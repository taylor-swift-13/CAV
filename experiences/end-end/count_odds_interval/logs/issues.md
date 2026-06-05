## 2026-06-05 06:16:02 +0800

- Gate: `coqc count_odds_interval_proof_manual.v`
- Phenomenon: the first proof attempt with only `pre_process; entailer!; lia.` failed at `proof_of_count_odds_interval_safety_wit_10` with `Tactic failure: Cannot find witness.`
- Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_055555v_count_odds_interval/coq/generated/count_odds_interval_proof_manual.v:26`.
- Key error/proof state: after `entailer!`, the open pure obligations were `-2147483648 <= (high_pre - low_pre) ÷ 2 + 1` and `(high_pre - low_pre) ÷ 2 + 1 <= 2147483647`, while the visible context only had `0 <= low_pre <= high_pre`.
- Fix: recovered machine-int bounds from the live local stores using two `sep_apply store_int_range` calls, extracted them with `Intros.`, and added local helpers for `0 <= x ÷ 2 <= x` and `x ÷ 2 + 1 <= 2147483647`.
- Why this fixed it: the VC was proof-stage arithmetic over `Z.quot`, not a contract contradiction. The missing ingredients were local-int range extraction and an explicit quotient-plus-one bound.

- Gate: `coqc count_odds_interval_proof_manual.v`
- Phenomenon: the next proof revision still failed before `entailer!` when asserting `0 <= high_pre - low_pre <= 2147483647` by `lia`.
- Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_055555v_count_odds_interval/coq/generated/count_odds_interval_proof_manual.v:51`.
- Key proof state: after `sep_apply store_int_range`, the range facts were still embedded in the antecedent as `“ Int.min_signed <= high_pre <= Int.max_signed ” && “ Int.min_signed <= low_pre <= Int.max_signed ” ** TT`, so `lia` could not see them.
- Fix: inserted `Intros.` immediately after the two `sep_apply store_int_range` calls in both manual witnesses.
- Why this fixed it: `Intros.` moves those pure range facts into Coq hypotheses, making the subsequent arithmetic assertions and `entailer!` discharge stable.
