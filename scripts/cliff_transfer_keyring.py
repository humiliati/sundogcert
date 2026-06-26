"""Secret-safe key discovery and provider probes for cliff-transfer runs.

The operator keeps model API keys outside the repo under reversed filenames:

  C:/Users/<user>/Dev/syek.ianepo.txt     -> openai
  C:/Users/<user>/Dev/syek.ciporhtna.txt  -> anthropic
  C:/Users/<user>/Dev/syek.corg.txt       -> groq
  C:/Users/<user>/Dev/syek.lartsim.txt    -> mistral

This module never prints key values. It reports only presence/shape and can run
a no-generation list-models probe to check that the credentials are usable.

Run:
  python scripts/cliff_transfer_keyring.py --list
  python scripts/cliff_transfer_keyring.py --probe
  python scripts/cliff_transfer_keyring.py --probe --json
  python -m pytest scripts/test_cliff_transfer_keyring.py -q
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Mapping

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

KEYRING_VERSION = "H1_CLIFF_TRANSFER_KEYRING_V1"


@dataclass(frozen=True)
class ProviderConfig:
    provider: str
    env_var: str
    filename: str
    list_models_url: str
    auth_header: str
    auth_scheme: str
    extra_headers: tuple[tuple[str, str], ...] = ()

    def headers(self, key: str) -> dict[str, str]:
        value = key if self.auth_scheme == "raw" else f"{self.auth_scheme} {key}"
        headers = {
            self.auth_header: value,
            "Accept": "application/json",
            "User-Agent": "sundogcert-cliff-transfer-keyring/1",
        }
        headers.update(dict(self.extra_headers))
        return headers


PROVIDERS: dict[str, ProviderConfig] = {
    "openai": ProviderConfig(
        provider="openai",
        env_var="OPENAI_API_KEY",
        filename="syek.ianepo.txt",
        list_models_url="https://api.openai.com/v1/models",
        auth_header="Authorization",
        auth_scheme="Bearer",
    ),
    "anthropic": ProviderConfig(
        provider="anthropic",
        env_var="ANTHROPIC_API_KEY",
        filename="syek.ciporhtna.txt",
        list_models_url="https://api.anthropic.com/v1/models",
        auth_header="x-api-key",
        auth_scheme="raw",
        extra_headers=(("anthropic-version", "2023-06-01"),),
    ),
    "groq": ProviderConfig(
        provider="groq",
        env_var="GROQ_API_KEY",
        filename="syek.corg.txt",
        list_models_url="https://api.groq.com/openai/v1/models",
        auth_header="Authorization",
        auth_scheme="Bearer",
    ),
    "mistral": ProviderConfig(
        provider="mistral",
        env_var="MISTRAL_API_KEY",
        filename="syek.lartsim.txt",
        list_models_url="https://api.mistral.ai/v1/models",
        auth_header="Authorization",
        auth_scheme="Bearer",
    ),
}


@dataclass(frozen=True)
class KeyStatus:
    provider: str
    source: str
    exists: bool
    present: bool
    char_count: int
    line_count: int
    source_kind: str

    def to_dict(self) -> dict:
        return {
            "provider": self.provider,
            "source": self.source,
            "exists": self.exists,
            "present": self.present,
            "char_count": self.char_count,
            "line_count": self.line_count,
            "source_kind": self.source_kind,
        }


@dataclass(frozen=True)
class ProbeResult:
    provider: str
    ok: bool
    http_status: int | None
    model_count: int | None
    source_kind: str
    error_type: str | None = None

    def to_dict(self) -> dict:
        return {
            "provider": self.provider,
            "ok": self.ok,
            "http_status": self.http_status,
            "model_count": self.model_count,
            "source_kind": self.source_kind,
            "error_type": self.error_type,
        }


def default_key_dir() -> Path:
    return Path(os.environ.get("SUNDOG_MODEL_KEY_DIR", Path.home() / "Dev"))


def _candidate_key_line(text: str) -> str:
    candidates = [
        line.strip()
        for line in text.splitlines()
        if line.strip() and not line.strip().startswith("#")
    ]
    if not candidates:
        return ""
    # Some local key files are "provider-name\nactual-key". Pick the longest
    # non-comment candidate so labels do not get mistaken for credentials.
    return max(candidates, key=len)


def _read_key_file(path: Path) -> tuple[str, int, int]:
    if not path.exists():
        return "", 0, 0
    text = path.read_text(encoding="utf-8").strip()
    return _candidate_key_line(text), len(text), len(text.splitlines()) if text else 0


def load_provider_key(
    provider: str,
    *,
    key_dir: Path | None = None,
    environ: Mapping[str, str] | None = None,
) -> tuple[str, str]:
    config = PROVIDERS[provider]
    env = environ if environ is not None else os.environ
    env_key = env.get(config.env_var, "").strip()
    if env_key:
        return env_key, "env"

    root = key_dir or default_key_dir()
    key, _, _ = _read_key_file(root / config.filename)
    if key:
        return key, "file"
    return "", "missing"


def key_status(
    provider: str,
    *,
    key_dir: Path | None = None,
    environ: Mapping[str, str] | None = None,
) -> KeyStatus:
    config = PROVIDERS[provider]
    env = environ if environ is not None else os.environ
    env_key = env.get(config.env_var, "").strip()
    if env_key:
        return KeyStatus(
            provider=provider,
            source=config.env_var,
            exists=True,
            present=True,
            char_count=len(env_key),
            line_count=1,
            source_kind="env",
        )

    root = key_dir or default_key_dir()
    path = root / config.filename
    key, char_count, line_count = _read_key_file(path)
    return KeyStatus(
        provider=provider,
        source=str(path),
        exists=path.exists(),
        present=bool(key),
        char_count=char_count,
        line_count=line_count,
        source_kind="file" if path.exists() else "missing",
    )


def list_key_statuses(
    *,
    key_dir: Path | None = None,
    environ: Mapping[str, str] | None = None,
) -> tuple[KeyStatus, ...]:
    return tuple(key_status(provider, key_dir=key_dir, environ=environ) for provider in PROVIDERS)


def _model_count(payload: object) -> int | None:
    if isinstance(payload, dict):
        data = payload.get("data")
        if isinstance(data, list):
            return len(data)
        models = payload.get("models")
        if isinstance(models, list):
            return len(models)
    if isinstance(payload, list):
        return len(payload)
    return None


OpenFn = Callable[[urllib.request.Request, int], object]


def _default_open(req: urllib.request.Request, timeout: int) -> object:
    return urllib.request.urlopen(req, timeout=timeout)


def probe_provider(
    provider: str,
    *,
    key_dir: Path | None = None,
    environ: Mapping[str, str] | None = None,
    timeout: int = 20,
    opener: OpenFn = _default_open,
) -> ProbeResult:
    config = PROVIDERS[provider]
    key, source_kind = load_provider_key(provider, key_dir=key_dir, environ=environ)
    if not key:
        return ProbeResult(provider, False, None, None, source_kind, "missing-key")

    req = urllib.request.Request(
        config.list_models_url,
        headers=config.headers(key),
        method="GET",
    )
    try:
        with opener(req, timeout) as response:  # type: ignore[attr-defined]
            status = int(response.status)
            body = response.read()
        payload = json.loads(body.decode("utf-8")) if body else {}
        return ProbeResult(provider, 200 <= status < 300, status, _model_count(payload), source_kind)
    except urllib.error.HTTPError as exc:
        return ProbeResult(provider, False, int(exc.code), None, source_kind, "http-error")
    except urllib.error.URLError:
        return ProbeResult(provider, False, None, None, source_kind, "url-error")
    except TimeoutError:
        return ProbeResult(provider, False, None, None, source_kind, "timeout")
    except json.JSONDecodeError:
        return ProbeResult(provider, False, None, None, source_kind, "bad-json")


def probe_all(
    *,
    key_dir: Path | None = None,
    environ: Mapping[str, str] | None = None,
    timeout: int = 20,
) -> tuple[ProbeResult, ...]:
    return tuple(
        probe_provider(provider, key_dir=key_dir, environ=environ, timeout=timeout)
        for provider in PROVIDERS
    )


def format_statuses(statuses: tuple[KeyStatus, ...]) -> str:
    lines = [f"CLIFF-TRANSFER KEYRING {KEYRING_VERSION}"]
    for status in statuses:
        shape = f"chars={status.char_count} lines={status.line_count}" if status.present else "absent"
        lines.append(
            f"  {status.provider:9s} present={str(status.present):5s} "
            f"source={status.source_kind:7s} {shape}"
        )
    return "\n".join(lines)


def format_probes(results: tuple[ProbeResult, ...]) -> str:
    lines = [f"CLIFF-TRANSFER PROVIDER PROBE {KEYRING_VERSION}"]
    for result in results:
        detail = (
            f"status={result.http_status} models={result.model_count}"
            if result.ok
            else f"status={result.http_status} error={result.error_type}"
        )
        lines.append(
            f"  {result.provider:9s} ok={str(result.ok):5s} source={result.source_kind:7s} {detail}"
        )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> dict:
    parser = argparse.ArgumentParser(description="Secret-safe keyring for cliff-transfer model providers.")
    parser.add_argument("--key-dir", type=Path, default=default_key_dir())
    parser.add_argument("--list", action="store_true", help="list key presence without network")
    parser.add_argument("--probe", action="store_true", help="run no-generation list-models probes")
    parser.add_argument("--json", action="store_true", help="emit JSON")
    parser.add_argument("--timeout", type=int, default=20)
    args = parser.parse_args(argv)

    do_probe = args.probe
    if do_probe:
        probes = probe_all(key_dir=args.key_dir, timeout=args.timeout)
        result = {
            "keyring_version": KEYRING_VERSION,
            "mode": "probe",
            "providers": [probe.to_dict() for probe in probes],
        }
        print(json.dumps(result, indent=2, sort_keys=True) if args.json else format_probes(probes))
        return result

    statuses = list_key_statuses(key_dir=args.key_dir)
    result = {
        "keyring_version": KEYRING_VERSION,
        "mode": "list",
        "providers": [status.to_dict() for status in statuses],
    }
    print(json.dumps(result, indent=2, sort_keys=True) if args.json else format_statuses(statuses))
    return result


if __name__ == "__main__":
    main()
