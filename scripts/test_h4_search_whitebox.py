"""Frozen analysis-pin for the H-IV search white-box probe.

Pins the coordinate map, both admissions, and the recall/redundancy metrics on hand-built
branches BEFORE any real search touches it (prereg §4): high-score WRONG near-duplicates +
a low-score CORRECT distinct branch. The real run changes only the source of the branches.

  python -m pytest scripts/test_h4_search_whitebox.py -q
"""

import numpy as np

import h4_search_whitebox as wb


def test_score_misses_winner_structural_keeps_it():
    tm = wb.task_metrics(wb.synthetic_branches())
    assert tm["top_score_correct"] == 0          # the top-score branch is wrong
    assert tm["score_recall"] == 0               # count-by-score prunes the low-score winner
    assert tm["struct_recall"] == 1              # structural admission retains it
    assert tm["struct_is_cap"]                   # admitted set is a genuine cap


def test_structural_is_more_diverse():
    tm = wb.task_metrics(wb.synthetic_branches())
    assert tm["struct_redundancy"] < tm["score_redundancy"]


def test_quantize_to_f3_is_in_space():
    rng = np.random.default_rng(1)
    embs = rng.normal(size=(8, 6))
    coords = wb.quantize_to_f3(embs, dim=3)
    assert len(coords) == 8
    assert all(len(c) == 3 and all(x in (0, 1, 2) for x in c) for c in coords)


def test_matched_admitted_size():
    # the count-by-score budget is matched to the structural admitted-cap size.
    branches = wb.synthetic_branches()
    struct_idx, _ = wb.struct_admit(branches)
    score_idx = wb.score_admit(branches, len(struct_idx))
    assert len(score_idx) == len(struct_idx)


# --------------------------------------------- reasoning regime (scale re-run) ----

def test_word_boundary_answer_match():
    # the reasoning regime matches the integer answer as a standalone number, so "8" does
    # NOT match inside "128" (the prior substring match would have).
    assert wb._is_correct("the total is 28 pencils", "28", word_boundary=True)
    assert not wb._is_correct("that gives 128 in the end", "8", word_boundary=True)
    assert not wb._is_correct("the answer is 280", "28", word_boundary=True)
    # the short regime keeps the substring behavior (back-compat).
    assert wb._is_correct("the answer is 280", "28", word_boundary=False)


def test_reasoning_tasks_wellformed():
    assert len(wb.REASONING_TASKS) == 8
    for prompt, answer in wb.REASONING_TASKS:
        assert answer.isdigit() and int(answer) >= 10      # distinctive multi-digit answers
        assert prompt.strip().endswith("A:")               # generation prompt
    assert wb.MAX_NEW_REASONING > wb.MAX_NEW_SHORT          # longer branches than the short leg


# ----------------------------------- slot-map fair test: small-budget recall@k (V3) ----

def test_smallbudget_struct_beats_score_all_maps():
    # the diversity-constrained struct@2 reaches the correct distinct slot where
    # count-by-score@2 stays in the wrong near-duplicate cluster; recall@1 ties.
    tm = wb.task_metrics_v3(wb.synthetic_branches_v3())
    assert tm["top_score_correct"] == 0 and tm["any_correct"] == 1     # a collapse task
    for m in wb.MAPS:
        r = tm["maps"][m]
        assert r["struct_is_cap"]
        assert r["score_recall@1"] == r["struct_recall@1"]             # k=1 sanity floor (tie)
        assert r["score_recall@2"] == 0                                # greedy wastes its 2nd slot
        assert r["struct_recall@2"] == 1                               # diversity reaches the winner


def test_f33_cap_is_line_free():
    assert wb.is_cap(wb.F33_CAP)                                       # the answer-bucket cap
    assert len(wb.F33_CAP) >= 8


def test_answer_coords_bucket_by_conclusion():
    branches = wb.synthetic_branches_v3()
    coords = wb.coords_for(branches, "answer")
    # same concluded integer -> same slot; distinct conclusion -> distinct slot.
    assert coords[0] == coords[1]                                      # both "99"
    assert coords[2] != coords[0]                                      # "42" distinct


def test_whitened_map_valid_and_centers():
    # whitening centers + standardizes before PCA->tercile; assert it runs and returns valid
    # F_3^3 coords, and that on an anisotropic cluster (shared offset) it separates points the
    # raw map collapses (the de-anisotropizing the prereg specifies).
    embs = [b["emb"] for b in wb.synthetic_branches_v3()]
    wc = wb.quantize_to_f3(embs, mode="whitened")
    assert len(wc) == len(embs)
    assert all(len(c) == 3 and all(x in (0, 1, 2) for x in c) for c in wc)
    import numpy as _np
    shared = _np.array([10.0, 10, 10, 10, 10, 10])         # large common (anisotropic) offset
    aniso = [shared + 0.01 * _np.arange(6), shared + 0.02 * _np.arange(6),
             shared - 0.01 * _np.arange(6), shared - 0.02 * _np.arange(6)]
    assert len(set(wb.quantize_to_f3(aniso, mode="whitened"))) >= \
        len(set(wb.quantize_to_f3(aniso, mode="embedding")))   # whitening separates >= raw
