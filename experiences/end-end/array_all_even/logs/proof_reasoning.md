2026-06-04 20:18: First manual-proof pass

Phenomenon: `symexec` succeeded on the current annotated file and left exactly three manual theorems in [array_all_even_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_proof_manual.v:21): `array_all_even_entail_wit_2`, `array_all_even_return_wit_1`, and `array_all_even_return_wit_2`.

Location: Generated witness definitions in [array_all_even_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_goal.v:167), [array_all_even_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_goal.v:181), and [array_all_even_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_goal.v:198).

Repair action: Wrote the smallest proof skeleton matching each VC shape before running `coqc`.

Key theorem-to-tactic plan:

```coq
Lemma proof_of_array_all_even_entail_wit_2 : array_all_even_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  intros k Hk.
  ...
Qed.
```

Why this change: The loop-step entailment is a pure strengthening of the processed-prefix universal from `< i` to `< i + 1`, so a case split `k < i \/ k = i` should be enough once `((Znth i l 0) % 2) = 0` is in context. The return witnesses are assertion-level disjunctions: the normal return should go to the right disjunct and reuse the loop invariant with `i_3 = n_pre`, while the odd-element early return should go to the left disjunct with existential witness `i_3`.

2026-06-04 20:20: First compile failure and proof repair

Phenomenon: `coqc` reached [array_all_even_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_proof_manual.v:30) and failed in `proof_of_array_all_even_entail_wit_2` with `Unable to unify "i <= n" with "Znth k l 0 % 2 = 0"`. The local strategy fallback itself was acceptable; the failure was inside the manual proof script.

Location: theorem `proof_of_array_all_even_entail_wit_2`, branch `k < i`.

Repair action: Replaced the brittle `apply H2` with a `match goal` that selects the actual prefix-universal hypothesis by shape:

```coq
match goal with
| Hprefix : forall k : Z, 0 <= k < i -> Znth k l 0 % 2 = 0 |- _ =>
    apply Hprefix; lia
end.
```

Why this change: `pre_process; entailer!` does not preserve a stable hypothesis numbering across witnesses. Matching on the semantic shape of the needed fact is more robust than guessing whether the universal prefix fact is `H2`, `H3`, or another identifier after Coq simplification.

2026-06-04 20:22: Second compile failure and proof repair

Phenomenon: recompiling `proof_manual.v` then failed at [array_all_even_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_proof_manual.v:43) with `The variable i_2 was not found in the current environment.` The failure is again about proof-state naming after `entailer!`, not about the witness statement.

Location: theorem `proof_of_array_all_even_return_wit_1`, right-disjunct universal proof.

Repair action: Replaced the hard-coded quantified variable `i_2` with a fresh introduction `intros x Hx`, then reused the loop-prefix universal via a shape-based `match goal`.

Key proof fragment:

```coq
intros x Hx.
assert (x < i_3) by lia.
match goal with
| Hprefix : forall k : Z, 0 <= k < i_3 -> Znth k l 0 % 2 = 0 |- _ =>
    apply Hprefix; lia
end.
```

Why this change: after the assertion-level disjunction is chosen, `entailer!` leaves a standard Coq universal quantifier whose binder name is chosen by the tactic. Introducing it explicitly avoids depending on generator-specific names.

2026-06-04 20:26: After invariant repair, witness set simplified

Phenomenon: rerunning `symexec` after adding `a == a@pre` and `n == n@pre` simplified the generated VCs. The new [array_all_even_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_goal.v:161) expresses the loop-step theorem and the normal-return theorem entirely in terms of `a_pre`, `n_pre`, and `l`; the early-return theorem is no longer left in `proof_manual.v`.

Location: regenerated [array_all_even_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_proof_manual.v:21).

Repair action: replaced the regenerated `Admitted` placeholders with two direct proofs:

```coq
Proof.
  pre_process.
  Right.
  entailer!.
  intros i_2 Hi_2.
  ...
Qed.
```

Why this change: once parameter stability is preserved in the invariant, the return witness reduces to a pure universal fact over the full array length. That is exactly the information already stored in the prefix invariant at `i_3 = n_pre`, so no extra annotation or helper lemma is needed.
2026-06-04 20:36: Fresh `symexec` was rerun after the audit replay investigation to confirm whether the short strategy imports in `coq/generated/array_all_even_goal.v` were stale or canonical. The regenerated file still contained bare `Require Import int_array_strategy_goal.` / `..._proof.` lines at `array_all_even_goal.v:20-27`, so the duplicate-library issue is emitted by the current generator rather than introduced by a later manual edit. The rerun also reset `array_all_even_proof_manual.v` back to two `Admitted.` stubs for `proof_of_array_all_even_entail_wit_2` and `proof_of_array_all_even_return_wit_1`.

Repair action: restored the two manual proofs in `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_proof_manual.v` with the same tactic structure validated in the previous round:

```coq
pre_process.
entailer!.
intros k Hk.
...
```

and

```coq
pre_process.
Right.
entailer!.
intros i_2 Hi_2.
...
```

Why this is still the right proof: the fresh VC body after rerun matches the earlier proof shape exactly, with the same prefix-evenness hypothesis `forall k : Z, 0 <= k < i -> Znth k l 0 % 2 = 0` (or `i_3` in the return witness). No annotation rollback was needed because the invariant on `annotated/verify_20260604_201124v_array_all_even.c` still provides the required semantic bridge.
2026-06-04 20:52: After adding qualified `Import Coq` strategy annotations to the annotated C and rerunning `symexec`, `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_proof_manual.v` was regenerated with the same two manual obligations, but both lemmas reverted to `Proof. Admitted.` placeholders. This is expected freshness fallout from the rerun, not a change in VC semantics.

定位：the theorem statements are still `proof_of_array_all_even_entail_wit_2` and `proof_of_array_all_even_return_wit_1`, and their proof scripts from the previous successful round remain valid because the VC bodies are unchanged. The new blocker is still in `array_all_even_goal.v` import resolution under base compile flags, not in these theorem bodies.

修复动作：restore exactly the previous two witness proofs in `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_proof_manual.v`, then re-run the compile chain. This keeps the workspace proof-complete while isolating the remaining failure to `goal.v` load-path behavior.

关键 Coq 片段：

```coq
Lemma proof_of_array_all_even_entail_wit_2 : array_all_even_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  intros k Hk.
  destruct Hk as [Hk0 Hk1].
  assert (k < i \/ k = i) as Hcase by lia.
```

为什么这样改：restoring the existing proofs avoids introducing a new `proof_manual.v` gate failure while testing the unrelated strategy-import workaround. The manual proof file should remain fully discharged even if the overall retry still fails on `goal.v`.

2026-06-04 21:14: Retry round 4 found a workspace-local way to remove the remaining `goal.v` compile blocker without changing the VC body. A throwaway compile experiment showed that the current generated `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_goal.v` succeeds under the standard base `-R` flags as soon as short-name wrapper modules such as

```coq
From SimpleC.EE.QCP_demos_LLM Require Export int_array_strategy_goal.
```

are compiled on a root load path passed via `-Q "$ORIG" ""`.

定位：this does not change any theorem statement in `array_all_even_proof_manual.v`; it only affects how the short imports at the top of `array_all_even_goal.v` resolve during compile replay. The regenerated manual file still contains exactly two obligations, `proof_of_array_all_even_entail_wit_2` and `proof_of_array_all_even_return_wit_1`, both reset to `Admitted.` by the fresh `symexec` run.

修复动作：add eight wrapper modules plus an empty `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/original/array_all_even.v` so the documented compile chain can legitimately include `-Q "$ORIG" ""`, then restore the two existing witness proofs unchanged in `proof_manual.v`.

为什么这样改：the wrapper modules are compile-time aliases only; they preserve the same underlying strategy libraries but give the short `Require Import int_array_strategy_goal.` family a unique resolution path inside this workspace. That keeps the annotated C and generated VC semantics untouched while making the replay path deterministic.

2026-06-04 21:17: The first wrapper shape fixed `goal.v`, `proof_auto.v`, and `proof_manual.v`, but `goal_check.v` still failed with

```text
The field int_array_strategy1_correctness is missing in ... VC_Correctness.
```

定位：`/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_goal_check.v` uses

```coq
Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
```

so the short-name proof wrappers must expose the underlying correctness lemmas as fields of the wrapper module itself; a plain `Require Export` is not enough for `Include`.

修复动作：change the four proof-side wrappers in `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/original/` from `Require Export` to `Require Import` plus `Include SimpleC.EE.QCP_demos_LLM.<module>.`, for example:

```coq
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof.
```

为什么这样改：this preserves the short-name library expected by generated files while re-exposing the concrete strategy correctness lemmas under the wrapper’s own module path, which is exactly what `goal_check.v` includes.
## retry-after-attempt-5 @ 2026-06-04 21:15:00 +0800

Phenomenon: the self-import experiment forced `symexec` to regenerate `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_proof_manual.v` back to two placeholder stubs:

```coq
Lemma proof_of_array_all_even_entail_wit_2 : array_all_even_entail_wit_2.
Proof. Admitted.

Lemma proof_of_array_all_even_return_wit_1 : array_all_even_return_wit_1.
Proof. Admitted.
```

while the actual audit blocker was still upstream in `array_all_even_goal.v` line 20 on short strategy imports. The proof file therefore needed to be restored only after rolling annotation changes back to the helper-free version, so the workspace would remain proof-complete even if replay still failed at the goal header.

Repair action: after removing the failed `Import Coq Require Import array_all_even` experiment from the annotated C and rerunning canonical `symexec`, I rewrote the two manual lemmas back to the previously checked witness scripts:

```coq
Lemma proof_of_array_all_even_entail_wit_2 : array_all_even_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  intros k Hk.
  destruct Hk as [Hk0 Hk1].
  assert (k < i \/ k = i) as Hcase by lia.
  destruct Hcase as [Hlt | Heq].
  - match goal with
      | Hprefix : forall k : Z, 0 <= k < i -> Znth k l 0 % 2 = 0 |- _ =>
          apply Hprefix; lia
    end.
  - subst k; auto.
Qed.
```

and

```coq
Lemma proof_of_array_all_even_return_wit_1 : array_all_even_return_wit_1.
Proof.
  pre_process.
  Right.
  entailer!.
  intros i_2 Hi_2.
  match goal with
    | Hprefix : forall k : Z, 0 <= k < i_3 -> Znth k l 0 % 2 = 0 |- _ =>
        apply Hprefix; lia
  end.
Qed.
```

Why this is the right restoration: the regenerated VC body after rollback is the same witness family as before the failed self-import experiment, so the earlier proofs remain aligned. A fallback compile from `QualifiedCProgramming/SeparationLogic` with workspace-local short-name shims (`-Q "$DEPS" ""`, plus the standard `-Q "$ORIG" ""` and `-R "$GEN" "$LP"`) successfully replayed `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, confirming that the proofs themselves are sound and that the only remaining failure is the standard runner replay path that does not prepend those local short-name shims.

2026-06-04 21:33: Retry round 6 confirmed that the surviving proof blocker was not in `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_proof_manual.v` at all. The two manual lemmas were already complete and unchanged; the failure reproduced only when `array_all_even_goal.v` tried to resolve short strategy imports before any workspace-local wrapper libraries had been compiled.

定位：a direct replay from `QualifiedCProgramming/SeparationLogic` with the documented base flags plus `-Q "$ORIG" ""` failed first on `Require Import int_array_strategy_goal.` in `array_all_even_goal.v:20`. After compiling `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/original/int_array_strategy_goal.v`, the same replay advanced to the next import and failed on `int_array_strategy_proof`. That one-step progression proves the short-name wrappers in `original/` are the intended disambiguation mechanism and that only their compiled `.vo` artifacts were missing.

修复动作：compile the existing wrapper sources in `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/original/` first (`int_array_strategy_*`, `uint_array_strategy_*`, `undef_uint_array_strategy_*`, `array_shape_strategy_*`, plus the empty `array_all_even.v` marker), then rerun the normal compile chain for `/home/yangfp/CAV/C/CAV/output/verify_20260604_201124v_array_all_even/coq/generated/array_all_even_goal.v`, `array_all_even_proof_auto.v`, `array_all_even_proof_manual.v`, and `array_all_even_goal_check.v` with the standard base flags and `-Q "$ORIG" "" -R "$GEN" "$LP"`.

关键命令形状：

```text
coqc BASE -Q "$ORIG" "" "$ORIG/int_array_strategy_goal.v"
...
coqc BASE -Q "$ORIG" "" -R "$GEN" SimpleC.EE.CAV.verify_20260604_201124v_array_all_even "$GEN/array_all_even_goal_check.v"
```

为什么这样改：this keeps the generated VC and the two witness proofs untouched while restoring the deterministic replay path that earlier success rounds had already validated. The proof file itself needed no edits because the theorem bodies never changed; only the library resolution state had regressed after cleanup removed the wrapper `.vo` files.
