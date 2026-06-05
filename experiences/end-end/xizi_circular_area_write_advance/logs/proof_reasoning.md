## 2026-06-02 Round 1

Phenomenon: proof-only workspace has one manual obligation left in `/home/yangfp/CAV/OS/CAV/output/verify_20260602_185301v_xizi_circular_area_write_advance/coq/generated/xizi_circular_area_write_advance_proof_manual.v`, theorem `proof_of_xizi_circular_area_write_advance_return_wit_2`, while `goal.v` shows a straight-line scalar branch VC about `% area_length`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260602_185301v_xizi_circular_area_write_advance/coq/generated/xizi_circular_area_write_advance_goal.v`, definition `xizi_circular_area_write_advance_return_wit_2`.

Action: start with the proof README straight-line template and specialize it to modulo arithmetic: `pre_process; entailer!` should reduce the VC to pure goals of the form `(x < m -> x mod m = x)`, `(x = m -> x mod m = 0)`, and `(x > m -> x mod m = x - m)` under the branch assumptions `x <= m` and `0 < m`. The last implication is expected to be vacuous because the branch hypothesis contradicts `x > m`.

Key snippet:

```coq
“ ((writeidx_pre + data_length_pre ) <= area_length_pre) ”
&& “ (0 < area_length_pre) ”
|-- “ (((writeidx_pre + data_length_pre ) < area_length_pre) ->
        (((writeidx_pre + data_length_pre ) % ( area_length_pre ) ) =
         (writeidx_pre + data_length_pre ))) ”
```

Why this change: this witness is purely arithmetic with no spatial resource manipulation, so a minimal `Z.mod` proof is the correct first attempt and keeps the manual proof stable.

## 2026-06-02 Round 2

Phenomenon: compiling `/home/yangfp/CAV/OS/CAV/output/verify_20260602_185301v_xizi_circular_area_write_advance/coq/generated/xizi_circular_area_write_advance_proof_manual.v` failed at line 27 with `Unable to unify "? mod ? = ?" with "(writeidx_pre + data_length_pre) % area_length_pre = 0"`.

Location: theorem `proof_of_xizi_circular_area_write_advance_return_wit_2` in the same file; the first bullet after `entailer!` received an equality hypothesis instead of the expected strict-less-than hypothesis.

Action: inspect the post-`entailer!` proof state with `coqtop` using the workspace load-path, then reorder the bullets to match the actual subgoal sequence.

Key error:

```text
Hlt : writeidx_pre + data_length_pre = area_length_pre
Unable to unify "?M5717 mod ?M5718 = ?M5717" with
"(writeidx_pre + data_length_pre) % area_length_pre = 0".
```

Why this change: the theorem is still arithmetic, but QCP reordered the implication branches during entailment simplification, so the proof script has to follow the generated subgoal order exactly.

## 2026-06-02 Round 3

Phenomenon: after reordering the bullets, compilation still failed in `proof_of_xizi_circular_area_write_advance_return_wit_2` at the equality branch with `Found no subterm matching "? mod ?" in the current goal`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260602_185301v_xizi_circular_area_write_advance/coq/generated/xizi_circular_area_write_advance_proof_manual.v:28`.

Action: inspect the equality branch after `intros Heq` to determine whether `subst` normalized the goal into `area_length_pre mod area_length_pre = 0`, whether the arithmetic expression is under a different syntactic form, or whether `lia` can already close it after a targeted rewrite.

Key error:

```text
Error: Found no subterm matching "?M5723 mod ?M5723" in the current goal.
```

Why this change: this is now a syntactic normalization issue rather than a semantic one; the proof needs to match Coq’s actual post-substitution shape.

## 2026-06-02 Round 4

Phenomenon: replacing `subst` with `rewrite Heq` did not change the compile failure; Coq still reported no subterm matching `? mod ?` for `Z.mod_same`.

Location: equality branch of `proof_of_xizi_circular_area_write_advance_return_wit_2` in `xizi_circular_area_write_advance_proof_manual.v`.

Action: inspect the goal after `rewrite Heq` inside `coqtop` to identify the exact operator behind `%` and choose a proof step that matches that normalized term.

Key error:

```text
Error: Found no subterm matching "?M5723 mod ?M5723" in the current goal.
```

Why this change: at this point the blocker is not arithmetic validity but the concrete lemma shape expected by the generated `%` notation.

## 2026-06-02 Round 5

Phenomenon: even on the normalized goal `area_length_pre % area_length_pre = 0`, `apply Z.mod_same` failed with an explicit unification mismatch between the theorem head and the goal head.

Location: equality branch of `proof_of_xizi_circular_area_write_advance_return_wit_2`.

Action: query the loaded Coq environment for modulo lemmas matching the concrete `%` notation used in this workspace and switch to the exact theorem name/signature that unifies with the generated goal.

Key error:

```text
Unable to unify "?M5723 mod ?M5723 = 0" with
"area_length_pre % area_length_pre = 0".
```

Why this change: the remaining failure is a notation/constant mismatch, so the right fix is to target the precise modulo lemma available under the loaded imports.
