#!/usr/bin/env python
"""S3-A6 Step 1 — upstream gate checker. Ticket doc (FROZEN): upstream/UPSTREAM_TICKETS_2026-06-11.md.

Functions (fixture-tested in scripts/test_upstream_gate_check.py, no network):
  - parse_axiom_audit(text): #print-axioms output -> True iff only {propext, Classical.choice,
    Quot.sound} appear for every audited decl.
  - lint_no_sundogcert_import(src): True iff no `import Sundogcert` line.
  - parse_lint_exit(exit_code), parse_env_linter(log): the pinned T1 lint commands' verdicts.
  - staleness_verdict(state): compares a live sweep dict against the FROZEN expectations; returns
    per-target GO/STALE/DRIFT verdicts (DRIFT = the world moved vs the ticket doc; re-freeze).

`--live` runs the real sweep via the gh CLI (mathlib PR #38014; ArkLib issues; the BCIKS20 retarget
file SHA + sorry count) and prints the verdict table.
Run: python scripts/upstream_gate_check.py --live   |   python scripts/test_upstream_gate_check.py
"""
import argparse
import json
import re
import subprocess
import sys

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

FROZEN = {
    "pr38014_state": "open",
    "arklib_issues_stale": [222, 224, 225, 233],
    "bciks20_path": "ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean",
    "bciks20_sha": "90959c93f71d65ccf03afd186ad7f7777fb96f3d",
    "bciks20_sorries": 2,
}


def parse_axiom_audit(text):
    """True iff every `'<decl>' depends on axioms: [...]` line lists only allowed axioms."""
    found = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text)
    if not found:
        return False
    for group in found:
        axs = {a.strip().strip("'") for a in group.split(",") if a.strip()}
        if not axs <= ALLOWED_AXIOMS:
            return False
    return True


def lint_no_sundogcert_import(src):
    return not re.search(r"^\s*import\s+Sundogcert", src, re.MULTILINE)


def parse_lint_exit(exit_code):
    return exit_code == 0


def parse_env_linter(log):
    """True iff the build log carries no linter errors/warnings (mathlib env linters fail loudly)."""
    return not re.search(r"(error:|warning:.*linter)", log, re.IGNORECASE)


def staleness_verdict(state):
    """state: dict from a live sweep. Returns {target: verdict} with DRIFT when the world has moved
    relative to the FROZEN ticket-doc expectations (a DRIFT requires re-freezing, never silent)."""
    v = {}
    v["pr38014"] = ("GO" if state["pr38014_state"] == FROZEN["pr38014_state"]
                    else f"DRIFT({state['pr38014_state']})")
    for n in FROZEN["arklib_issues_stale"]:
        v[f"arklib#{n}"] = ("STALE-as-frozen" if state.get(f"issue{n}_state") == "open"
                            else f"DRIFT({state.get(f'issue{n}_state')})")
    if state.get("bciks20_sha") != FROZEN["bciks20_sha"]:
        v["bciks20"] = f"DRIFT(sha {str(state.get('bciks20_sha'))[:8]})"
    elif state.get("bciks20_sorries") != FROZEN["bciks20_sorries"]:
        v["bciks20"] = f"DRIFT(sorries {state.get('bciks20_sorries')})"
    else:
        v["bciks20"] = "GO"
    return v


def _gh(args):
    r = subprocess.run(["gh", "api"] + args, capture_output=True, text=True, encoding="utf-8")
    if r.returncode != 0:
        raise RuntimeError(f"gh api failed: {r.stderr[:200]}")
    return r.stdout


def live_sweep():
    state = {}
    pr = json.loads(_gh(["repos/leanprover-community/mathlib4/pulls/38014"]))
    state["pr38014_state"] = pr["state"]
    state["pr38014_updated"] = pr["updated_at"]
    for n in FROZEN["arklib_issues_stale"]:
        iss = json.loads(_gh([f"repos/Verified-zkEVM/ArkLib/issues/{n}"]))
        state[f"issue{n}_state"] = iss["state"]
    commits = json.loads(_gh([f"repos/Verified-zkEVM/ArkLib/commits?path={FROZEN['bciks20_path']}"
                              "&per_page=1"]))
    state["bciks20_sha"] = commits[0]["sha"]
    raw = _gh(["-H", "Accept: application/vnd.github.raw",
               f"repos/Verified-zkEVM/ArkLib/contents/{FROZEN['bciks20_path']}"])
    state["bciks20_sorries"] = len(re.findall(r"\bsorry\b", raw))
    return state


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--live", action="store_true")
    args = ap.parse_args()
    if not args.live:
        print("fixture mode: run scripts/test_upstream_gate_check.py; use --live for the sweep")
        return 0
    state = live_sweep()
    v = staleness_verdict(state)
    print("S3-A6 upstream staleness sweep (live):")
    for k, verdict in v.items():
        print(f"  {k:14s} {verdict}")
    drift = any(s.startswith("DRIFT") for s in v.values())
    print("DRIFT DETECTED — re-freeze the ticket doc before proceeding" if drift
          else "all targets as frozen — proceed per tickets")
    return 1 if drift else 0


if __name__ == "__main__":
    sys.exit(main())
