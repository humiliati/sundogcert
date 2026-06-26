"""Frozen tests for the cliff-transfer keyring.

Run:
  python -m pytest scripts/test_cliff_transfer_keyring.py -q
"""

import json
from pathlib import Path

import cliff_transfer_keyring as keyring


class FakeResponse:
    status = 200

    def __init__(self, payload):
        self.payload = payload

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        return False

    def read(self):
        return json.dumps(self.payload).encode("utf-8")


def test_lists_reversed_key_files_without_revealing_values(tmp_path: Path):
    (tmp_path / "syek.ianepo.txt").write_text("sk-openai-secret\n", encoding="utf-8")
    (tmp_path / "syek.ciporhtna.txt").write_text("sk-ant-secret\n", encoding="utf-8")

    statuses = keyring.list_key_statuses(key_dir=tmp_path, environ={})
    rendered = keyring.format_statuses(statuses)

    by_provider = {status.provider: status for status in statuses}
    assert by_provider["openai"].present is True
    assert by_provider["anthropic"].present is True
    assert by_provider["groq"].present is False
    assert "sk-openai-secret" not in rendered
    assert "sk-ant-secret" not in rendered


def test_environment_key_wins_over_file(tmp_path: Path):
    (tmp_path / "syek.ianepo.txt").write_text("file-key\n", encoding="utf-8")

    status = keyring.key_status("openai", key_dir=tmp_path, environ={"OPENAI_API_KEY": "env-key"})
    value, source = keyring.load_provider_key(
        "openai", key_dir=tmp_path, environ={"OPENAI_API_KEY": "env-key"}
    )

    assert status.source_kind == "env"
    assert status.char_count == len("env-key")
    assert value == "env-key"
    assert source == "env"


def test_longest_noncomment_line_is_loaded_to_skip_labels(tmp_path: Path):
    (tmp_path / "syek.lartsim.txt").write_text(
        "# comment\n\nmistral\nmistral-key-longer\n", encoding="utf-8"
    )

    value, source = keyring.load_provider_key("mistral", key_dir=tmp_path, environ={})

    assert value == "mistral-key-longer"
    assert source == "file"


def test_probe_uses_provider_auth_shape_without_printing_key(tmp_path: Path):
    (tmp_path / "syek.corg.txt").write_text("groq-secret\n", encoding="utf-8")
    seen = {}

    def fake_open(req, timeout):
        seen["url"] = req.full_url
        seen["auth"] = req.headers["Authorization"]
        seen["timeout"] = timeout
        return FakeResponse({"data": [{"id": "a"}, {"id": "b"}]})

    result = keyring.probe_provider("groq", key_dir=tmp_path, environ={}, timeout=3, opener=fake_open)
    rendered = keyring.format_probes((result,))

    assert result.ok is True
    assert result.model_count == 2
    assert seen["url"].endswith("/models")
    assert seen["auth"] == "Bearer groq-secret"
    assert seen["timeout"] == 3
    assert "groq-secret" not in rendered


def test_missing_key_probe_fails_closed(tmp_path: Path):
    result = keyring.probe_provider("anthropic", key_dir=tmp_path, environ={})

    assert result.ok is False
    assert result.error_type == "missing-key"
