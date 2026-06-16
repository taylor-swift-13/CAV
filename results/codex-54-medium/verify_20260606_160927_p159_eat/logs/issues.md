## 2026-06-06

Issue: initial `coqc` load-path binding was wrong for this repo layout.

- Gate: `coqc p159_eat_goal.v`
- Symptom: `Cannot find a physical path bound to logical path int_auto with prefix AUXLib` and then `Cannot find a physical path bound to logical path p159_eat`.
- Location: [p159_eat_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260606_160927_p159_eat/coq/generated/p159_eat_goal.v:10)
- Resolution: use repo-local physical roots under `QualifiedCProgramming/SeparationLogic/...`, compile [p159_eat.v](/home/yangfp/CAV/C/CAV/input/humaneval/p159_eat.v:1) first, and bind the generated directory with `-Q output/verify_20260606_160927_p159_eat/coq/generated SimpleC.EE.CAV.verify_20260606_160927_p159_eat`.

Issue: manual proof scripts needed witness-shape-specific tactics instead of the initial generic script.

- Gate: `coqc p159_eat_proof_manual.v`
- Symptom 1: `proof_of_p159_eat_safety_wit_6` left two pure arithmetic goals open after `entailer!`.
- Symptom 2: return-witness scripts failed on comma-separated `Exists`, then on unfinished bullets while building `IntArray.full`.
- Location: [p159_eat_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260606_160927_p159_eat/coq/generated/p159_eat_proof_manual.v:22)
- Resolution:
  - For `safety_wit_6`, `safety_wit_10`, and `safety_wit_12`, keep `pre_process; entailer!` and solve all resulting pure goals with `all: unfold problem_159_pre in H3; lia.`
  - For `return_wit_1` and `return_wit_2`, use one `Exists` per witness, build the spatial result with `unfold IntArray.full, store_array; simpl; entailer!.`, then discharge the remaining pure goal with `entailer!; unfold problem_159_spec; ...`.
