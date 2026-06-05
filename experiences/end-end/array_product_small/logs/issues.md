2026-06-05 issue 1

Phenomenon: The first replay compile failed at `/home/yangfp/CAV/C/CAV/output/verify_20260605_004203v_array_product_small/coq/generated/array_product_small_goal.v` with `Error: Required library int_array_strategy_goal matches several files in path`.

Location: `array_product_small_goal.v`, line 21 `Require Import int_array_strategy_goal.`

Repair action: Added workspace-local wrapper modules in `/home/yangfp/CAV/C/CAV/output/verify_20260605_004203v_array_product_small/original/` for `int_array_strategy_*`, `uint_array_strategy_*`, `undef_uint_array_strategy_*`, and `array_shape_strategy_*`, each re-exporting the `QCP_demos_LLM` version. Recompiled those wrappers before replaying `goal/proof_auto/proof_manual/goal_check`.

Key snippet:

```coq
From SimpleC.EE.QCP_demos_LLM Require Export int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof.
```

Why this worked: the generated files import short strategy module names, and the wrapper files make those names resolve uniquely through `-Q "$ORIG" ""` without modifying generated Coq or shared library trees.

2026-06-05 issue 2

Phenomenon: The first regenerated proof attempt was still seeing the old witness shape after `symexec`; `coqtop` on `array_product_small_safety_wit_3` still exposed stale quantified variables `a, n` even though the new `array_product_small_goal.v` no longer did.

Location: stale compiled artifacts under `/home/yangfp/CAV/C/CAV/output/verify_20260605_004203v_array_product_small/coq/generated/`.

Repair action: Deleted generated `.vo/.glob/.aux/.vok/.vos` artifacts, deleted stale compiled files under `original/`, then recompiled wrappers, `original/array_product_small.v`, `goal.v`, and `proof_auto.v` before recompiling `proof_manual.v`.

Key symptom:

```text
goal.v source: forall (a_pre: Z) (n_pre: Z) ...
coq proof state: a, ret, n, i : Z
```

Why this worked: after the second `symexec`, the `.v` files changed but old compiled modules were still available on the load path. Cleaning the compiled artifacts forced Coq to check the manual proof against the current VC rather than a stale one.
