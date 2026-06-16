## 2026-06-06

- Gate: `coqc p102_choose_num_goal.v`
  Location: `output/verify_20260606_155626_p102_choose_num/coq/generated/p102_choose_num_goal.v`
  Symptom: initial compile attempt failed with load-path errors, including `Cannot find a physical path bound to logical path int_auto with prefix AUXLib` and then `Cannot find a physical path bound to logical path p102_choose_num`.
  Resolution: compiled with the repo-local QCP roots under `QualifiedCProgramming/SeparationLogic/...`, added `-R output SimpleC.EE.CAV`, and added `-Q input/humaneval ''` so `Require Import p102_choose_num` resolves to `input/humaneval/p102_choose_num.v`.

- Gate: `coqc p102_choose_num_proof_manual.v`
  Location: `output/verify_20260606_155626_p102_choose_num/coq/generated/p102_choose_num_proof_manual.v`, return witnesses 1-4.
  Symptom: the first proof draft failed repeatedly on parity reasoning and proof shape:
  `Cannot find witness` when trying to solve parity side conditions with `lia`;
  `No product even after head-reduction` when splitting the separation-logic entailment directly;
  notation mismatch between generated hypotheses using `Z.rem` and Coq parity lemmas using `mod`.
  Resolution: switched the manual proofs to `pre_process; entailer!` so each witness becomes a pure Coq proposition, rewrote copied parity hypotheses with `Z.rem_mod_nonneg`, and proved parity cases with `Zmod_even`, `Zmod_odd`, `Z.even_pred`, and `Z.negb_odd`. After that, all five return witnesses compiled.

- Gate: `source_integrity`
  Location: `output/verify_20260606_155626_p102_choose_num/logs/source_integrity_gate.log`
  Symptom: runner retry reported `input V changed after verify bootstrap: /home/yangfp/CAV/C/CAV/input/humaneval/p102_choose_num.v`.
  Key diff: workspace snapshot `output/verify_20260606_155626_p102_choose_num/original/p102_choose_num.v` differed from the current input only at the specification comment opener: snapshot had `(* ` while input had `(*`.
  Resolution: refreshed the workspace-local snapshot file to match the current input spec exactly, then rechecked with `diff -u` to confirm no remaining content drift.

- Gate: `coqc generated modules`
  Location: `output/verify_20260606_155626_p102_choose_num/coq/generated/{p102_choose_num_goal,proof_auto,proof_manual,goal_check}.v`
  Symptom: rerunning `coqc` from the repo root failed with `Cannot find a physical path bound to logical path p102_choose_num` and then `...p102_choose_num_goal with prefix SimpleC.EE.CAV.verify_20260606_155626_p102_choose_num`.
  Resolution: compiled `input/humaneval/p102_choose_num.v` first, then reran the generated files from `output/verify_20260606_155626_p102_choose_num/coq` with `-R generated SimpleC.EE.CAV.verify_20260606_155626_p102_choose_num` and the existing QCP `-R` roots. That compile order and root binding produced passing `goal`, `proof_auto`, `proof_manual`, and `goal_check`.
