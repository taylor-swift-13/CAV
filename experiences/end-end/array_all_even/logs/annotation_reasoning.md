2026-06-04 20:16: Initial annotation pass

Phenomenon: `array_all_even` is a single-loop read-only array scan with an early return on the first odd element. The base contract states a universal property for return `1` and an existential counterexample for return `0`, but the loop body had no invariant to preserve the processed-prefix semantics needed at the loop head and at normal loop exit.

Location: [annotated/verify_20260604_201124v_array_all_even.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260604_201124v_array_all_even.c:17), `for (i = 0; i < n; ++i)` in function `array_all_even`.

Repair action: Added a loop invariant with three parts: `0 <= i && i <= n` for loop-head bounds, `(forall (k: Z), (0 <= k && k < i) => l[k] % 2 == 0)` to summarize the already-processed prefix, and `IntArray::full(a, n, l)` to keep the read-only array ownership/value relation available across iterations.

Key annotation snippet:

```c
/*@ Inv
      0 <= i && i <= n &&
      (forall (k: Z), (0 <= k && k < i) => l[k] % 2 == 0) &&
      IntArray::full(a, n, l)
*/
```

Why this change: At the loop head, `i` denotes the next unchecked index, so the natural closed form is "all elements in the processed prefix `[0, i)` are even". This invariant initializes at `i == 0`, is preserved when the branch `a[i] % 2 != 0` is not taken, and at loop exit together with `i >= n` it directly yields the universal postcondition for return `1`. The early-return branch should obtain the existential postcondition from the guard witness `i`.

2026-06-04 20:25: Invariant strengthening for unchanged parameters

Phenomenon: After the first proof pass, `array_all_even_return_wit_1` still had spatial goal `IntArray.full a n l |-- IntArray.full a_pre (Zlength l) l`. The proof state showed no facts connecting current `a`, `n` back to `a_pre`, `n_pre`, so the return witnesses were missing exactly the parameter-stability information described in the invariant guidance.

Location: return witness generated from [annotated/verify_20260604_201124v_array_all_even.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260604_201124v_array_all_even.c:17), loop invariant for `for (i = 0; i < n; ++i)`.

Repair action: Strengthened the loop invariant with `a == a@pre` and `n == n@pre`.

Key annotation delta:

```c
a == a@pre &&
n == n@pre &&
```

Why this change: the function never writes either parameter, but generated return witnesses must recover the postcondition in terms of pre-state names. This is a classic "parameter unchanged relation polluted return witness" issue; the correct fix is to preserve those equalities in the invariant and rerun `symexec`, not to force the equalities later inside `proof_manual.v`.
2026-06-04 20:49: The retry blocker is no longer a semantic VC issue. Even the canonical `symexec` command from `experiences/general/SYMEXEC/README.md §1` regenerated `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_goal.v` with short unqualified strategy imports (`Require Import int_array_strategy_goal.` through `array_shape_strategy_proof.` at lines 20-27), and plain audit `coqc` then failed before any theorem because those short names are ambiguous across `QualifiedCProgramming/SeparationLogic/examples/QCP_demos_LLM/` and `.../QCP_demos_human/`.

定位：the proof obligations themselves are still the same two manual lemmas in `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_proof_manual.v`, so changing the loop invariant would not affect this failure. The only remaining verify-scope lever that survives the runner freshness check is to influence the generated Coq header from the annotated C.

修复动作：prepend verification-only `Import Coq` annotations in `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_201124v_array_all_even.c` for the canonical qualified strategy modules under `SimpleC.EE.QCP_demos_LLM` (`common_strategy_goal/proof`, `int_array_strategy_goal/proof`, `uint_array_strategy_goal/proof`, `undef_uint_array_strategy_goal/proof`, `array_shape_strategy_goal/proof`). The expectation is that regenerated files will load the qualified libraries first, after which the generator’s existing short `Require Import int_array_strategy_goal.` lines can resolve to already-loaded modules instead of triggering duplicate path search.

关键片段：

```c
/*@ Import Coq From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal */
```

为什么这样改：the annotation changes only verification metadata, not the function contract or executable C. Unlike manually editing `*_goal.v`, this survives the runner’s resymexec freshness audit because the generated header change originates from the annotated source itself.

2026-06-04 21:05: Retry round 4 re-evaluated the previous helper-import experiment against the new general symexec guidance `experiences/general/SYMEXEC/README.md §19`. The generated `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_goal.v` currently differs from clean verified examples by containing both the qualified strategy-import block and an extra trailing short block:

```coq
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
...
```

定位：those extra short imports are consistent with the ten verification-only helper lines now present at the top of `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_201124v_array_all_even.c`, for example:

```c
/*@ Import Coq From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal */
```

修复动作：remove all ten `Import Coq From SimpleC.EE.QCP_demos_LLM Require Import ...` lines from the annotated C, keep the loop invariant and contract unchanged, then rerun canonical `symexec`.

为什么这样改：the new guidance explicitly warns that temporary annotation-side helper imports can let `symexec` succeed but poison audit replay by baking extra `Require Import <helper>.` lines into `goal.v`. Here the helper imports are not needed to express the invariant at all, so the correct fix is to revert to helper-free annotations and regenerate fresh Coq files rather than trying to compensate in proof scripts or workspace-local deps.
## retry-after-attempt-5 @ 2026-06-04 21:08:00 +0800

Phenomenon: `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_goal.v` still begins its strategy section with short imports such as `Require Import int_array_strategy_goal.`, and compiling that file from `QualifiedCProgramming/SeparationLogic` with the documented base `-R examples SimpleC.EE` arguments fails immediately with `Required library int_array_strategy_goal matches several files in path` because both `QCP_demos_LLM` and `QCP_demos_human` export the same leaf name.

Localization: the executable function and loop invariant are already sufficient for VC generation and the only manual obligations left are the two existing entailment witnesses. Stable array examples such as `experiences/end-end/array_count_even/original/array_count_even.c` carry a verification-only self-import line `/*@ Import Coq Require Import array_count_even */`, and their generated `*_goal.v` files use the qualified `From SimpleC.EE.QCP_demos_LLM Require Import ...` block instead of short unqualified imports.

Repair action: add the analogous verification-only line `/*@ Import Coq Require Import array_all_even */` above the target function in `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_201124v_array_all_even.c`, leaving the original contract text and executable implementation untouched, then delete the generated quartet and rerun canonical `symexec`. The reason for this edit is to make symexec treat the workspace-local `original/array_all_even.v` as the intended Coq companion module so the regenerated header can follow the same qualified import pattern as the passing end-to-end examples.

Result of the experiment: negative. Fresh `symexec` did add `Require Import array_all_even.` to regenerated files, but `array_all_even_goal.v` still emitted the same short strategy block:

```coq
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
...
```

and compiling with the documented base load path from `QualifiedCProgramming/SeparationLogic` still failed at the first short import with the same duplicate-library error against `examples/QCP_demos_LLM` and `examples/QCP_demos_human`. This disproves the hypothesis that adding the standard self-import line is sufficient to switch symexec back to the qualified `From SimpleC.EE.QCP_demos_LLM Require Import ...` header used by passing end-to-end examples.

Rollback action: remove the self-import line from the annotated C again and regenerate once more, because keeping an annotation that does not improve replay only perturbs the generated witness header. After rollback, restore the two manual witness proofs so the workspace remains proof-complete aside from the unchanged goal-header replay blocker.
