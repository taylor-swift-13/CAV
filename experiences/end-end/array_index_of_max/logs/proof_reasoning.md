2026-06-05T00:00:00Z

Phenomenon: `symexec` generated three manual obligations in `coq/generated/array_index_of_max_proof_manual.v`: `entail_wit_2_1`, `entail_wit_2_2`, and `return_wit_1`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_002002v_array_index_of_max/coq/generated/array_index_of_max_goal.v`, definitions `array_index_of_max_entail_wit_2_1`, `array_index_of_max_entail_wit_2_2`, `array_index_of_max_return_wit_1`.

Repair action planned: first try the minimal proof shape from the proof guide. The two entailment witnesses should be discharged by `pre_process; entailer!`, then splitting the new prefix fact at `j < i` versus `j = i`. The return witness is checked separately because its goal mentions `IntArray.full a_pre n_pre l` while the hypotheses expose `IntArray.full a n l`; if compilation confirms that no equality bridge is available, this points back to missing parameter-preservation facts in the annotation rather than a pure Coq-side gap.

Why this approach: it separates proof-side arithmetic/list obligations from annotation-side state preservation. If the first failure is only the array-parameter mismatch in `return_wit_1`, the cheaper and more correct fix is to regenerate the VC with explicit `a == a@pre` and `n == n@pre` carried through the loop.

2026-06-05T00:00:00Z

Phenomenon: the first replay compile stopped at `array_index_of_max_proof_manual.v:26` with `Tactic failure: Cannot find witness`.

Location: `proof_of_array_index_of_max_entail_wit_2_1`, after `pre_process; entailer!`.

Repair action: inspected the proof state in `coqtop`. `entailer!` had already discharged the arithmetic frame and left exactly two pure goals:
`forall j_2, 0 <= j_2 < i -> Znth j_2 l 0 < Znth i l 0`
and
`forall j, 0 <= j < i + 1 -> Znth j l 0 <= Znth i l 0`.
The original script was solving the wrong goals and also reused the wrong hypothesis numbers. I am replacing it with the minimal direct argument:
for strictness, combine the old prefix bound `H5 : Znth j <= Znth idx` with branch fact `H : Znth i > Znth idx`;
for the extended prefix, split `j < i` versus `j = i`.

Key proof-state fragment:
`H : Znth i l 0 > Znth idx l 0`
`H5 : forall j, 0 <= j < i -> Znth j l 0 <= Znth idx l 0`
goal `forall j_2, 0 <= j_2 < i -> Znth j_2 l 0 < Znth i l 0`.

Why this change: the obligation is pure arithmetic over array values, so the stable fix is to prove exactly the remaining inequalities instead of fighting `entailer!` with extra bullets.

2026-06-05T00:00:00Z

Phenomenon: after fixing `entail_wit_2_1`, replay advanced to `proof_of_array_index_of_max_entail_wit_2_2` and failed with a unification error at line 41.

Location: `array_index_of_max_proof_manual.v`, lemma `proof_of_array_index_of_max_entail_wit_2_2`.

Repair action: reorder the bullets. The first remaining goal is the extended non-strict prefix fact
`forall j, 0 <= j < i + 1 -> Znth j l 0 <= Znth idx l 0`,
not the old strict fact. I am proving that goal by splitting `j < i` versus `j = i` and using the branch hypothesis `Znth i l 0 <= Znth idx l 0`; the second goal is then exactly the old invariant fact `H6`.

Key error fragment:
`Unable to unify "forall j_2, ... < Znth idx l 0" with "forall j, ... <= Znth idx l 0"`.

Why this change: this is a proof-state ordering issue, not a semantic blocker. Matching the bullets to the actual `entailer!` goal order is the minimal correction.

2026-06-05T00:00:00Z

Phenomenon: the next replay failed with `Wrong bullet +: No more goals` in `proof_of_array_index_of_max_entail_wit_2_2`.

Location: `array_index_of_max_proof_manual.v:46`.

Repair action: remove the stale second bullet. After the first branch proves the extended prefix fact, `entailer!` has already discharged the unchanged strict-prefix fact automatically, so there is no remaining subgoal for `apply H6`.

Key error fragment: `[Focus] Wrong bullet +: No more goals.`

Why this change: this confirms the proof is now over-specified rather than under-specified; the correct fix is to delete the extra branch instead of forcing a nonexistent goal.

2026-06-05T00:00:00Z

Phenomenon: after adding `a == a@pre` and `n == n@pre` to the loop invariant and rerunning `symexec`, the manual VC changed shape as expected: `entail_wit_2_1`, `entail_wit_2_2`, and `return_wit_1` are now stated only over `a_pre`, `n_pre`, `idx`, and `i`.

Location: regenerated `/home/yangfp/CAV/C/CAV/output/verify_20260605_002002v_array_index_of_max/coq/generated/array_index_of_max_goal.v`, definitions `array_index_of_max_entail_wit_2_1`, `array_index_of_max_entail_wit_2_2`, `array_index_of_max_return_wit_1`.

Repair action: replace the manual proof with the clean regenerated obligations:
- `entail_wit_2_1`: prove new max-at-`i` facts by combining the old prefix bound with the branch condition `Znth i l 0 > Znth idx l 0`;
- `entail_wit_2_2`: extend the processed prefix when the branch is not taken by splitting `j < i` versus `j = i`;
- `return_wit_1`: use `i >= n_pre` and `i <= n_pre` to obtain `i = n_pre`, then forward the prefix-max fact from range `< i` to range `< n_pre`.

Why this change: once the annotation carries parameter preservation, the remaining work is pure arithmetic over the processed prefix, which belongs in `proof_manual.v`.
