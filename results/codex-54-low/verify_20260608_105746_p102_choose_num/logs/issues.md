1. `goal.v` initial compile failed with `Cannot find a physical path bound to logical path p102_choose_num`.
Resolution: compile the QCP audit with `-Q SeparationLogic/_cav_original/verify_20260608_105746_p102_choose_num ''` so the mirrored bare import is visible to `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.

2. `p102_choose_num_proof_manual.v` required five manual return witnesses and several compile/proof iterations.
Key failures: parity proofs initially used `Z.modulo` facts where the generated branch hypotheses use `Z.rem`-style `%`, and some branch subgoals were vacuous after `repeat split`.
Resolution: prove parity contradictions through `Z.rem_mod_nonneg`, `Z.even_spec`, and direct branch-specific rewrites; simplify vacuous maximality subgoals; rerun `coqc` until `proof_manual.v` and `goal_check.v` both compiled.
