#!/usr/bin/env python
"""Frozen fixture test for scripts/upstream_gate_check.py (S3-A6 Step 1). No network.
Run: python scripts/test_upstream_gate_check.py"""
import sys

sys.path.insert(0, "scripts")
import upstream_gate_check as g

fail = 0


def check(name, cond, detail=""):
    global fail
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")
    if not cond:
        fail += 1


print("axiom-audit parser:")
ok_txt = "'cauchy_no_mean' depends on axioms: [propext, Classical.choice, Quot.sound]\n" \
         "'cauchy_charFun_tendsto_zero' depends on axioms: [propext, Quot.sound]"
bad_txt = "'thm' depends on axioms: [propext, Classical.choice, Quot.sound, sorryAx]"
check("clean audit accepted", g.parse_axiom_audit(ok_txt))
check("sorryAx rejected", not g.parse_axiom_audit(bad_txt))
check("empty audit rejected", not g.parse_axiom_audit("no axioms here"))

print("import lint:")
check("clean file passes", g.lint_no_sundogcert_import("import Mathlib.Probability.Moments\n"))
check("Sundogcert import caught",
      not g.lint_no_sundogcert_import("import Mathlib\nimport Sundogcert.ShadowDecayCauchy\n"))

print("lint/build parsers:")
check("lint exit 0 = pass", g.parse_lint_exit(0) and not g.parse_lint_exit(1))
check("env-linter warning caught",
      not g.parse_env_linter("warning: style linter docBlame fired") and
      g.parse_env_linter("Build completed successfully (2903 jobs)"))

print("staleness verdicts (fixtures pin the FROZEN 2026-06-12 expectations):")
asfrozen = {"pr38014_state": "open", "issue222_state": "open", "issue224_state": "open",
            "issue225_state": "open", "issue233_state": "open",
            "bciks20_sha": g.FROZEN["bciks20_sha"], "bciks20_sorries": 2}
v = g.staleness_verdict(asfrozen)
check("as-frozen world -> all GO/STALE-as-frozen",
      v["pr38014"] == "GO" and v["bciks20"] == "GO" and
      all(v[f"arklib#{n}"] == "STALE-as-frozen" for n in (222, 224, 225, 233)))
moved = dict(asfrozen, pr38014_state="closed")
check("PR close -> DRIFT", g.staleness_verdict(moved)["pr38014"].startswith("DRIFT"))
moved = dict(asfrozen, bciks20_sorries=0)
check("sorries vanish -> DRIFT (retarget stale)",
      g.staleness_verdict(moved)["bciks20"].startswith("DRIFT"))
moved = dict(asfrozen, bciks20_sha="deadbeef")
check("file moved -> DRIFT", g.staleness_verdict(moved)["bciks20"].startswith("DRIFT"))

print(f"\n{'ALL PASS' if fail == 0 else str(fail) + ' FAILED'} — S3-A6 gate-check frozen test")
sys.exit(1 if fail else 0)
