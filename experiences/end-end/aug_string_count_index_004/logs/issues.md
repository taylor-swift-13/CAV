# Issues

## 2026-06-05 resolved symbolic-execution blocker

- Gate: `symexec`
- Phenomenon: the first run on `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_041101v_aug_string_count_index_004.c` failed with `Error: Lack of assertions in some paths for the loop!` at the single `while (1)` loop.
- Localization: the loop had no invariant connecting `i`, `count`, and the processed string prefix.
- Fix action: added a prefix/suffix loop invariant with `count == aug_string_count_index_004_spec(l1)`, `Zlength(l1) == i`, bounds `0 <= count <= i`, preserved `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, and a post-loop assertion fixing `i == n` and `count == aug_string_count_index_004_spec(l)`.
- Why this fixed it: the generated VC now had the processed-prefix semantic summary needed to advance one character per loop iteration and to derive the final postcondition on loop exit.
- Result: rerunning `symexec` succeeded and regenerated fresh `goal/proof_auto/proof_manual/goal_check` files in `/home/yangfp/CAV/C/CAV/output/verify_20260605_041101v_aug_string_count_index_004/coq/generated/`.

## 2026-06-05 resolved compile replay blocker

- Gate: `coqc goal.v`
- Phenomenon: the first full compile replay failed with `Required library char_array_strategy_goal matches several files in path` because both `QCP_demos_LLM` and `QCP_demos_human` provide `char_array_strategy_goal.vo` and `char_array_strategy_proof.vo`.
- Localization: `/home/yangfp/CAV/C/CAV/output/verify_20260605_041101v_aug_string_count_index_004/coq/generated/aug_string_count_index_004_goal.v`, import lines `Require Import char_array_strategy_goal.` and `Require Import char_array_strategy_proof.`
- Fix action: added workspace-local wrappers `/home/yangfp/CAV/C/CAV/output/verify_20260605_041101v_aug_string_count_index_004/original/char_array_strategy_goal.v` and `.../char_array_strategy_proof.v` that re-export the `SimpleC.EE.QCP_demos_LLM` strategy modules, then compiled those wrappers before the generated files.
- Why this fixed it: `-Q "$ORIG" ""` now gives those short names a unique resolution without modifying shared examples or generated files.
- Result: the full replay `goal.v -> proof_auto.v -> proof_manual.v -> goal_check.v` completed successfully.

## 2026-06-05 resolved manual-proof blockers

- Gate: `coqc proof_manual.v`
- Phenomenon: the generated manual proof file initially contained four `Admitted` obligations: `proof_of_aug_string_count_index_004_entail_wit_1`, `_entail_wit_2_1`, `_entail_wit_2_2`, and `_entail_wit_3`.
- Localization: `/home/yangfp/CAV/C/CAV/output/verify_20260605_041101v_aug_string_count_index_004/coq/generated/aug_string_count_index_004_proof_manual.v`.
- Fix action: replaced the placeholders with explicit proofs plus helper lemma `aug_string_count_index_004_spec_app_single`, then repaired two follow-up issues:
  `Found no subterm matching "Zlength (?M ++ ?N)" in H7` in `entail_wit_3` by using shape-directed `match goal` proof instead of a hard-coded hypothesis name.
  `Syntax error: [ltac_use_default] expected after [tactic]` by closing a `match goal` block with `end.` inside the local assertion proof.
- Why this fixed it: the obligations were pure prefix-extension and exit-shape lemmas; once the proof stopped depending on unstable generated hypothesis names, the VC matched the standard string-count proof pattern.
- Result: `proof_manual.v` and `goal_check.v` compile cleanly, and `proof_manual.v` contains no `Admitted`, `admit`, `Abort`, or new `Axiom`.

Final Result: Success
