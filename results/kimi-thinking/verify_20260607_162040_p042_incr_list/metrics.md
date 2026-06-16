# Verification Metrics

| Metric | Value |
|--------|-------|
| Problem | p042_incr_list |
| Total VCs | 4 |
| Proved Manually | 4 |
| Proved Automatically | 0 |
| Time to Complete | ~2 hours |
| Key Lemmas Added | 2 (`Zlength_map_incr`, `Znth_map_incr`) |
| Lines of Manual Proof | ~90 lines |

## VC Breakdown

| VC | Status | Approach |
|----|--------|----------|
| safety_wit_3 | Proved | Used `list_incr_int_range` hypothesis with `lia` bounds |
| entail_wit_1 | Proved | `Exists nil` + array lemmas + `reflexivity`/`lia` |
| entail_wit_2 | Proved | `sublist_split`, `sublist_single`, `map_app` |
| return_wit_1 | Proved | `seg_to_full` + `undef_seg_empty` + `Znth_map_incr` lemma |
