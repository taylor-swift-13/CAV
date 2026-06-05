2026-06-03 Round 1

Symptom: `output/verify_20260603_000130v_xizi_dataqueue_free_slots/coq/generated/xizi_dataqueue_free_slots_proof_manual.v` contains two unresolved lemmas, `proof_of_xizi_dataqueue_free_slots_safety_wit_4` and `proof_of_xizi_dataqueue_free_slots_return_wit_1`, both left as `Admitted`.

Location: `output/verify_20260603_000130v_xizi_dataqueue_free_slots/coq/generated/xizi_dataqueue_free_slots_goal.v`, definitions `xizi_dataqueue_free_slots_safety_wit_4` and `xizi_dataqueue_free_slots_return_wit_1`.

Planned fix: keep proof-only boundaries, inspect the exact Coq proof state with the current generated VC, and replace the two `Admitted` placeholders with minimal arithmetic proofs in `.../xizi_dataqueue_free_slots_proof_manual.v`.

Key VC shape: `safety_wit_4` asks for signed-int bounds on `(max_len_pre - 1) - (((rear_pre - front_pre) + max_len_pre) % max_len_pre)`. `return_wit_1` asks for nonnegativity, `< max_len_pre`, and the two branch equalities for the same expression under `front_pre <= rear_pre` and `rear_pre < front_pre`.

Why this approach: proof-only mode forbids changing contract/annotation/generated goals, so the only valid path is to discharge the existing arithmetic obligations directly and fail only if the VC is intrinsically unprovable.

2026-06-03 Round 2

Symptom: direct `lia` after `pre_process; entailer!` was unstable inside the generated witness proof, even though the same arithmetic statement proved immediately in a plain Coq goal.

Location: `.../xizi_dataqueue_free_slots_proof_manual.v`, witness proofs for `proof_of_xizi_dataqueue_free_slots_safety_wit_4` and `proof_of_xizi_dataqueue_free_slots_return_wit_1`.

Fix action: move the modulo arithmetic into standalone helper lemmas proved in plain Coq (`free_slots_range`, `free_slots_case_front_le_rear`, `free_slots_case_rear_lt_front`), then keep the witness proofs short: `pre_process; entailer!;` and apply the helper facts.

Key proof fragments:
- `Z.mod_pos_bound` gives `0 <= ((rear - front + max_len) mod max_len) < max_len` from `0 < max_len`.
- `Z.mod_add` + `Z.mod_small` handles the `front <= rear` branch by rewriting `(rear - front + max_len) mod max_len` to `rear - front`.
- `Z.mod_small` handles the `rear < front` branch because `0 <= rear - front + max_len < max_len`.

Why this change: helper lemmas isolate the arithmetic from the separation-logic entailment context and produce a shorter, more deterministic manual proof script.

2026-06-03 Round 3

Symptom: `coqc` failed at `.../xizi_dataqueue_free_slots_proof_manual.v:75` inside `proof_of_xizi_dataqueue_free_slots_safety_wit_4`, where the witness proof still used a single `lia` over the helper result.

Location: `.../xizi_dataqueue_free_slots_proof_manual.v`, safety witness proof after `entailer!`.

Fix action: destruct the helper result from `free_slots_range` into explicit lower/upper bounds and use those bounds directly, rather than depending on one-shot arithmetic reconstruction inside the generated witness proof.

Key details: `free_slots_range` already proves `0 <= free_slots_expr < max_len_pre`. The lower signed-int obligation follows from `0 <= free_slots_expr`; the upper signed-int obligation follows from `free_slots_expr < max_len_pre` plus `max_len_pre <= 1073741824 < INT_MAX`.

Why this change: the helper lemma is already sufficient; making the projection explicit removes tactic brittleness without changing the VC or proof strategy.

2026-06-03 Round 4

Symptom: `coqc` still failed at the safety witness after destructing `free_slots_range`; the remaining `lia` inside the generated witness proof was still fragile in that context.

Location: `.../xizi_dataqueue_free_slots_proof_manual.v`, `proof_of_xizi_dataqueue_free_slots_safety_wit_4`.

Fix action: add dedicated plain-Coq helper lemmas for the exact signed-int obligations (`free_slots_sint_lower`, `free_slots_sint_upper`) and for the return-range projections (`free_slots_nonneg`, `free_slots_below_max`), then use direct `apply` in the witness proofs.

Key proof fragment: the standalone helpers are proved outside the separation-logic witness context, so they can freely use `pose proof (free_slots_range ...)` and ordinary arithmetic; the witness scripts then only instantiate those already-proved facts.

Why this change: it removes the last arithmetic search step from the witness proof itself and keeps the manual proof deterministic.

2026-06-03 Round 5

Symptom: `coqc` still rejected `apply free_slots_sint_lower` in the safety witness with a unification mismatch around the normalized `INT_MIN` comparison, even though the displayed goal was the expected proposition.

Location: `.../xizi_dataqueue_free_slots_proof_manual.v`, safety witness bullets after `entailer!`.

Fix action: avoid `apply`-time unification on the generated goal; instead instantiate the helper lemma with `pose proof ... as Hbound` and finish the bullet with `exact Hbound`.

Key detail: this keeps the theorem statement identical but moves elaboration of the helper instantiation outside the fragile witness-goal matcher.

Why this change: the target proposition is already known to be correct; the remaining issue is proof-script robustness, not missing arithmetic facts.

2026-06-03 Round 6

Symptom: the safety witness still failed because the generated `%` operator expands to `Z.rem`, while my helper lemmas were stated over Coq `mod`; the propositions looked similar when printed but were not definitionally equal.

Location: `.../xizi_dataqueue_free_slots_proof_manual.v`, all helper lemmas over the free-slot expression.

Fix action: restate every helper lemma with the exact generated `%` expression (`Z.rem`) and, inside the helper proofs only, rewrite `Z.rem` to `mod` via `Z.rem_mod_nonneg` once the dividend nonnegativity is established.

Key proof fragment:
- `Locate "%"` in the proof context resolves to `Z.rem`.
- `Z.rem_bound_pos` gives the range fact directly for nonnegative dividend and positive divisor.
- `Z.rem_mod_nonneg` bridges `Z.rem` to `mod` when needed for `Z.mod_add` / `Z.mod_small`.

Why this change: once the helper statements use the same operator as the VC, the witness proof can consume them without any remaining unification mismatch.

2026-06-03 Round 7

Symptom: after switching helper statements to `%`, `coqc` failed to parse `% max_len_pre` because Coq read it as a scope key instead of remainder syntax.

Location: `.../xizi_dataqueue_free_slots_proof_manual.v`, helper lemma statements.

Fix action: rewrite every remainder occurrence to the generated parenthesized form `% ( max_len_pre )`, matching the syntax in `xizi_dataqueue_free_slots_goal.v`.

Key code fragment: `((rear_pre - front_pre + max_len_pre) % ( max_len_pre ))`

Why this change: it preserves the intended `Z.rem` operator while avoiding Coq’s scope-annotation parser ambiguity.
