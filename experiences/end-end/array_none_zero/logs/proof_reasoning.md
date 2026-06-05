2026-06-05

Phenomenon: `symexec` succeeded and generated manual obligations in `/home/yangfp/CAV/C/CAV/output/verify_20260605_004036v_array_none_zero/coq/generated/array_none_zero_proof_manual.v` for `array_none_zero_entail_wit_2`, `array_none_zero_return_wit_1`, and `array_none_zero_return_wit_2`.

Location: generated Coq files `array_none_zero_goal.v` and `array_none_zero_proof_manual.v`.

First proof analysis: `array_none_zero_return_wit_1` and `array_none_zero_return_wit_2` quantify both `a_pre/n_pre` and current `a/n`, but the antecedents only contain `IntArray.full a n l` and no equalities relating current parameters to their `@pre` versions. This matches the known failure mode where an invariant omitted unchanged-parameter facts, so the return witness asks proof to reconstruct what annotation should have preserved.

Key VC fragment:

```coq
Definition array_none_zero_return_wit_1 :=
forall (a_pre: Z) (n_pre: Z) ... (a: Z) (n: Z) ...,
  ... && (IntArray.full a n l)
|--
  ... && (IntArray.full a_pre n_pre l).
```

Repair action: return to annotation and add `a == a@pre` and `n == n@pre` to the loop invariant, then rerun `symexec` to regenerate aligned witnesses before proving anything manually.

Why this change: these are unchanged function parameters. Proving the return witnesses without explicit parameter-equality facts would amount to proving a resource transport across unrelated addresses/lengths, which is not the intended VC and is likely impossible under the current annotation.

2026-06-05

Phenomenon: after regenerating VCs with parameter-equality facts in the invariant, the manual obligations simplify to:

- `array_none_zero_entail_wit_2`: extend the scanned-prefix property from `[0, i)` to `[0, i + 1)`.
- `array_none_zero_return_wit_1`: use loop exit `i_3 >= n_pre` plus invariant bound `i_3 <= n_pre` to conclude the universal postcondition for return value `1`.
- `array_none_zero_return_wit_2`: witness the existential postcondition for return value `0` with the current index `i_3`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_004036v_array_none_zero/coq/generated/array_none_zero_goal.v`.

Repair action: replace the three `Admitted` placeholders in `array_none_zero_proof_manual.v` with direct proofs using `pre_process`, `entailer!`, a small split on `k < i \/ k = i` for the prefix-extension lemma, and direct implication/existential reasoning for the return lemmas.

Key VC fragments:

```coq
forall k, 0 <= k /\ k < i + 1 -> Znth k l 0 <> 0
```

```coq
(1 = 1) -> forall i, 0 <= i /\ i < n_pre -> Znth i l 0 <> 0
```

```coq
(0 = 0) -> exists i_2, (0 <= i_2 /\ i_2 < n_pre) /\ Znth i_2 l 0 = 0
```

Why this change: these obligations are now pure logical consequences of the invariant and branch facts, so the shortest stable proof is preferable to introducing helper lemmas or additional annotation churn.

2026-06-05

Phenomenon: replay compilation of `array_none_zero_proof_manual.v` failed at line 57 with `Tactic failure: Cannot find witness.` while proving `proof_of_array_none_zero_return_wit_2`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_004036v_array_none_zero/coq/generated/array_none_zero_proof_manual.v`, theorem `proof_of_array_none_zero_return_wit_2`.

Observed proof state: after `pre_process; entailer!`, Coq had already discharged the vacuous implication `(0 = 1) -> ...` and left only

```coq
0 = 0 -> exists i_0 : Z, 0 <= i_0 < n_pre /\ Znth i_0 l 0 = 0
```

Repair action: remove the spurious first bullet and prove the remaining goal directly by introducing the trivial premise, choosing witness `i_3`, and discharging the range/value facts from the branch hypotheses.

Why this change: the failure came from a mismatch between the assumed subgoal ordering and the actual post-`entailer!` state. The goal is simpler than expected and needs a direct existential witness proof, not a contradiction branch.

2026-06-05

Phenomenon: the next replay failure in `proof_of_array_none_zero_return_wit_2` reported that `Exists i_3` produced an assertion-level entailment witness while Coq expected a pure proposition of shape `exists i_2 : Z, ...`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_004036v_array_none_zero/coq/generated/array_none_zero_proof_manual.v`, line 57.

Key error:

```text
The term "derivable1s_exp_r ... i_3 ..." has type "?P |-- EX x : _, ?Q x"
while it is expected to have type "exists i_2 : Z, ..."
```

Repair action: replace assertion-level `Exists` with pure Coq `exists`, then prove the conjunctive range/value goal using `lia` and the branch fact `Znth i_3 l 0 = 0`.

Why this change: `entailer!` had already reduced the separation-logic wrapper away. The remaining obligation lives in ordinary Coq logic, so the proof must use ordinary `exists`/`split`, not QCP entailment constructors.
