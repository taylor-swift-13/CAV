2026-06-05

Phenomenon: initial `symexec` on `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_004036v_array_none_zero.c` failed at the loop with `Error: Lack of assertions in some paths for the loop!`.

Location: annotated C file `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_004036v_array_none_zero.c`, `for (i = 0; i < n; i++)`.

Repair action: added a loop invariant describing the loop-head state:

```c
0 <= i && i <= n &&
a == a@pre &&
n == n@pre &&
(forall (k: Z), (0 <= k && k < i) => l[k] != 0) &&
IntArray::full(a, n, l)
```

Why this fixed it: `symexec` needed both a loop assertion and the resource/pure facts required to re-enter the body and later discharge return obligations.

2026-06-05

Phenomenon: after the first invariant draft, `symexec` failed at `a[i]` with `Cannot derive the precondition of Memory Read.`.

Location: annotated C file `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_004036v_array_none_zero.c`, loop-body read `a[i]`.

Repair action: strengthened the invariant to retain `IntArray::full(a, n, l)`.

Why this fixed it: the array-read rule needs the full-array ownership fact at the loop head; the pure prefix property alone is insufficient.

2026-06-05

Phenomenon: the first generated return witnesses quantified both current parameters and `@pre` parameters without any bridge equalities, producing obligations of the shape `IntArray.full a n l |-- IntArray.full a_pre n_pre l`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_004036v_array_none_zero/coq/generated/array_none_zero_goal.v`, `array_none_zero_return_wit_1` and `array_none_zero_return_wit_2`.

Repair action: added `a == a@pre` and `n == n@pre` to the loop invariant, then regenerated all Coq files with a fresh `symexec`.

Why this fixed it: `a` and `n` are unchanged parameters, so those equalities belong in the annotation layer. After regeneration, the return witnesses were expressed directly in terms of `a_pre` and `n_pre`.

2026-06-05

Phenomenon: replay compilation of `array_none_zero_goal.v` failed with duplicate short-name strategy imports such as `Required library int_array_strategy_goal matches several files in path`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_004036v_array_none_zero/coq/generated/array_none_zero_goal.v`, short imports for `int_array`, `uint_array`, `undef_uint_array`, and `array_shape` strategies.

Repair action: added workspace-local wrappers under `/home/yangfp/CAV/C/CAV/output/verify_20260605_004036v_array_none_zero/original/`:

```coq
From SimpleC.EE.QCP_demos_LLM Require Export int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof.
```

and the analogous wrappers for `uint_array`, `undef_uint_array`, and `array_shape`.

Why this fixed it: the generated files keep their original short imports, while `-Q "$ORIG" ""` makes the workspace wrappers the unique resolution target during replay.

2026-06-05

Phenomenon: manual proof replay failed twice during `proof_of_array_none_zero_return_wit_2`: first because the script assumed a nonexistent contradiction branch after `entailer!`, then because assertion-level `Exists` was used where the remaining goal was a pure Coq existential.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_004036v_array_none_zero/coq/generated/array_none_zero_proof_manual.v`, theorem `proof_of_array_none_zero_return_wit_2`.

Repair action: inspected the post-`entailer!` proof state with `coqtop`, simplified the script to the actual remaining goal

```coq
0 = 0 -> exists i_0 : Z, 0 <= i_0 < n_pre /\ Znth i_0 l 0 = 0
```

and proved it with pure Coq `exists i_3`.

Why this fixed it: the remaining obligation had already left separation-logic entailment mode, so it required ordinary Coq proof steps, not QCP assertion-level constructors.
