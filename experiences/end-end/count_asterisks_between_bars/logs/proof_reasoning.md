2026-06-05 proof iteration 1

Phenomenon: after the annotation repair and fresh `symexec`, the manual proof file `/home/yangfp/CAV/C/CAV/output/verify_20260605_054012v_count_asterisks_between_bars/coq/generated/count_asterisks_between_bars_proof_manual.v` contains exactly the semantic bridge lemmas `entail_wit_1`, `entail_wit_2_1` through `entail_wit_2_5`, `entail_wit_3`, and `return_wit_1`. The increment safety witness disappeared once `0 <= count <= i` was added to the invariant.

Location: generated manual proof obligations for `count_asterisks_between_bars`.

Repair plan: prove the witnesses via small helper lemmas instead of trying to force each witness directly.

Key expected helper structure:

1. Prefix/suffix head decomposition at the loop index:
   from `l = app(prefix, suffix)` and `Zlength(prefix) = i` and `Znth i (app(l, 0::nil)) 0 = x` with `x <> 0`, derive `exists suffix', suffix = x :: suffix'`.
2. One-step recurrence facts for the spec helper:
   `count_asterisks_between_bars_go inside (x :: suffix')`
   specialized to `x = 124`, `x = 42` with `inside = 0`, and `x = 42` with `inside <> 0`.
3. Loop-exit empty-suffix consequence:
   from `Zlength(prefix) = n`, `Zlength(l) = n`, and `l = app(prefix, suffix)`, derive `suffix = nil`, then simplify `count_asterisks_between_bars_go inside nil`.

Why this plan: all remaining VCs are pure list/arithmetic/spec equalities. The invariant is already aligned with the control points, so going back to annotation again would only be justified by a concrete mismatch. At this stage the cheapest path is to keep the witnesses short and push the repetitive list reasoning into explicit helper lemmas.

2026-06-05 proof iteration 2

Phenomenon: the first compile replay did not reach the manual witnesses. `coqc` failed on `/home/yangfp/CAV/C/CAV/output/verify_20260605_054012v_count_asterisks_between_bars/coq/generated/count_asterisks_between_bars_goal.v:21` with `Required library char_array_strategy_goal matches several files in path`, because both `QCP_demos_LLM` and `QCP_demos_human` export the same short strategy module names.

Location: generated imports `Require Import char_array_strategy_goal.` and `Require Import char_array_strategy_proof.` in the current workspace.

Repair action: added local wrapper modules in both `original/` and `coq/generated/`:

```coq
From SimpleC.EE.QCP_demos_LLM Require Export char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.char_array_strategy_proof.
```

Why this change: `-Q "$ORIG" ""` makes the `original/` wrappers the unique short-name resolution for the normal replay command, while the sibling wrappers in `coq/generated/` cover the bare-file replay mode described in the compile experience. This is a replay-path repair, not a proof change.

2026-06-05 proof iteration 3

Phenomenon: after the replay-path fix, `coqc` advanced through the helper lemmas and branch witnesses, but `return_wit_1` remained underdetermined because the exit assertion had dropped `Zlength(l) == n`. The manual proof reduced to a bare equality `count = count_asterisks_between_bars_spec l` with no way to force `suffix = nil`.

Location: theorem `count_asterisks_between_bars_return_wit_1`.

Repair action: stopped proof work, returned to annotation, restored the missing length fact at the loop-exit `Assert`, reran `symexec`, then replayed the same manual proof file against the refreshed witnesses. The refreshed `return_wit_1` premise regained:

```coq
“ (Zlength (l)) = n ”
```

which made `suffix_nil_from_lengths` applicable again.

Why this change: this was an annotation information-loss bug, not a missing Coq tactic. Continuing to push proof automation without restoring the lost cutpoint fact would have been unsound.

2026-06-05 proof iteration 4

Phenomenon: after the final `symexec` replay, the branch witness theorem names and shapes stayed stable, and `entail_wit_3`/`return_wit_1` gained the extra length fact expected from the repaired exit assertion.

Repair action: restored the near-complete manual proof file, kept the branch-witness proofs unchanged, and replayed the final exit/return proofs:

```coq
rewrite H13.
cancel.
```

for the remaining `i` store entailment in `entail_wit_3`, and

```coq
assert (suffix = nil) as Hnil by (eapply suffix_nil_from_lengths; eauto).
subst suffix.
entailer!.
```

for `return_wit_1`.

Result: `proof_manual.v` compiled cleanly, and the full compile chain through `goal_check.v` passed.
