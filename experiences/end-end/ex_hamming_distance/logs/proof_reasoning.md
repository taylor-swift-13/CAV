2026-06-05 08:xx proof setup

Phenomenon: [coq/generated/ex_hamming_distance_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080838v_ex_hamming_distance/coq/generated/ex_hamming_distance_proof_manual.v) contains five nontrivial manual lemmas: `safety_wit_5`, `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, and `return_wit_1`.

Location: generated goals in [coq/generated/ex_hamming_distance_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080838v_ex_hamming_distance/coq/generated/ex_hamming_distance_goal.v).

Repair plan: first replay-compile `original/<name>.v`, `goal.v`, and `proof_auto.v` so `coqtop` can inspect the actual witness states. After that, replace the `Admitted` bodies in `proof_manual.v` with small structural proofs plus helper lemmas only if the step/return witnesses need list-prefix normalization.

Why this plan: the obligations are all consequences of the prefix-count invariant, so the likely proof work is arithmetic and one-step unfolding of `ex_hamming_distance_spec`, not a return to annotation unless the VCs show missing semantic facts.

2026-06-05 08:xx replay compile repair 1

Phenomenon: compiling [coq/generated/ex_hamming_distance_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080838v_ex_hamming_distance/coq/generated/ex_hamming_distance_goal.v) failed before any theorem proof with `Required library char_array_strategy_goal matches several files in path`.

Location: short-name imports `Require Import char_array_strategy_goal.` and `Require Import char_array_strategy_proof.` at the top of `goal.v`.

Repair action: add workspace-local sibling wrappers in `coq/generated/` for both short names, exporting the `QCP_demos_LLM` strategy modules. This follows the compile guidance for duplicate-path strategy imports during generated-file replay.

Key wrapper shape:
```coq
From SimpleC.EE.QCP_demos_LLM Require Export char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.char_array_strategy_proof.
```

Why this change: the VC files themselves must remain unchanged, but replay needs a unique local resolution for those short module names. Generated-directory wrappers satisfy bare and `-R "$GEN"` compilation modes without modifying shared examples or the generated goal text.
