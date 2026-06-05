## 2026-06-05 06:02:18 +0800

- Symptom: `coq/generated/count_odds_interval_proof_manual.v` still contains `Admitted` for `proof_of_count_odds_interval_safety_wit_10` and `proof_of_count_odds_interval_safety_wit_11`, so `goal_check.v` cannot satisfy proof-only completion.
- Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_055555v_count_odds_interval/coq/generated/count_odds_interval_proof_manual.v`, theorems `count_odds_interval_safety_wit_10` and `count_odds_interval_safety_wit_11`.
- Repair action: start with the proof README §3 try-first skeleton for arithmetic entailments: `pre_process; entailer!; try lia.` on each witness.
- Key VC shape: both goals are pure safety bounds of the form `((((high_pre - low_pre) ÷ 2) + 1) <= INT_MAX) && (INT_MIN <= (((high_pre - low_pre) ÷ 2) + 1))` under parity facts plus `0 <= low_pre <= high_pre` and integer-valued locals from `# Int |->`.
- Why this change: these witnesses do not involve heap restructuring or existentials; the likely proof obligation is just integer-range arithmetic from the generated int-value bounds plus monotonicity of division by `2`.

## 2026-06-05 06:06:41 +0800

- Symptom: the first compile failed at `/home/yangfp/CAV/C/CAV/output/verify_20260605_055555v_count_odds_interval/coq/generated/count_odds_interval_proof_manual.v:26` with `Tactic failure: Cannot find witness.`
- Location: theorem `proof_of_count_odds_interval_safety_wit_10`. A `coqtop` replay showed that after `pre_process; entailer!` the remaining pure goals are exactly `-2147483648 <= (high_pre - low_pre) ÷ 2 + 1` and `(high_pre - low_pre) ÷ 2 + 1 <= 2147483647`, but the context only has `0 <= low_pre <= high_pre`.
- Repair action: follow `experiences/general/PROOF/9/overflow-from-int-stack.md` and the `upper_bound` example. Before `entailer!`, recover signed-int ranges from the live stack cells via `sep_apply store_int_range` twice, normalize `Int.min_signed`/`Int.max_signed` to numerals, and assert a local helper bound `0 <= (high_pre - low_pre) ÷ 2 <= high_pre - low_pre`.
- Key proof fragment to add:
```coq
sep_apply store_int_range.
sep_apply store_int_range.
change Int.min_signed with (-2147483648) in *.
change Int.max_signed with 2147483647 in *.
assert (Hq : 0 <= (high_pre - low_pre) ÷ 2 <= high_pre - low_pre)
  by (apply count_odds_interval_quot2_bounds; lia).
```
- Why this change: the VC is not a contract gap yet. The missing facts are standard machine-int range facts carried by `(&(\"high\")) # Int |-> high_pre` and `(&(\"low\")) # Int |-> low_pre`, and `lia` only becomes effective once the quotient is bounded explicitly.

## 2026-06-05 06:10:56 +0800

- Symptom: after adding `store_int_range` and the quotient lower/upper helper, `proof_of_count_odds_interval_safety_wit_10` now reaches `Qed` with one open goal instead of failing inside `entailer!`.
- Location: post-`entailer!` state of `proof_of_count_odds_interval_safety_wit_10` in `coq/generated/count_odds_interval_proof_manual.v`. The only remaining subgoal is:
```coq
(high_pre - low_pre) ÷ 2 + 1 <= 2147483647
```
with hypotheses `0 <= low_pre <= high_pre`, `-2147483648 <= high_pre <= 2147483647`, `-2147483648 <= low_pre <= 2147483647`, and `0 <= (high_pre - low_pre) ÷ 2 <= high_pre - low_pre`.
- Repair action: add a second local helper proving `x ÷ 2 + 1 <= 2147483647` from `0 <= x <= 2147483647`, assert `0 <= high_pre - low_pre <= 2147483647` before `entailer!`, and feed that helper to the proof so the final upper-bound goal is already in context when automation runs.
- Why this change: the lower bound is already discharged automatically. The remaining blocker is a pure quotient-plus-one arithmetic fact, and encoding it once as a local helper is more stable than trying to force `lia` through `Z.quot` syntax in each witness.

## 2026-06-05 06:13:07 +0800

- Symptom: the next compile moved the failure earlier to `/home/yangfp/CAV/C/CAV/output/verify_20260605_055555v_count_odds_interval/coq/generated/count_odds_interval_proof_manual.v:51`, where `assert (Hdiff : 0 <= high_pre - low_pre <= 2147483647) by lia.` reported `Cannot find witness`.
- Location: same theorem `proof_of_count_odds_interval_safety_wit_10`, before `entailer!`.
- Root cause from `coqtop`: after two `sep_apply store_int_range` calls, the int-range facts still sit inside the antecedent as
```coq
“ Int.min_signed <= high_pre <= Int.max_signed ” &&
“ Int.min_signed <= low_pre <= Int.max_signed ” ** TT
```
so `lia` cannot see them yet. Running `Intros.` at that point moves them into Coq hypotheses `H2` and `H3`.
- Repair action: insert `Intros.` immediately after the two `sep_apply store_int_range` calls in both witness proofs, then keep the existing `change ...`, `Hdiff`, `Hq`, and `Hq1` steps.
- Why this change: the arithmetic helpers were already sufficient in the inspected post-`entailer!` state. The remaining issue was proof-state plumbing, not a missing contract fact or missing arithmetic lemma.
