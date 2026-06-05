## 2026-06-03 19:07:16 +0800

Phenomenon: Fresh `symexec` generated three manual obligations in [xizi_id_first_nonfull_byte_proof_manual.v](/home/yangfp/CAV/OS/CAV/output/verify_20260603_190108v_xizi_id_first_nonfull_byte/coq/generated/xizi_id_first_nonfull_byte_proof_manual.v:1): `entail_wit_2`, `return_wit_1`, and `return_wit_2`.

Location:
- `xizi_id_first_nonfull_byte_entail_wit_2`
- `xizi_id_first_nonfull_byte_return_wit_1`
- `xizi_id_first_nonfull_byte_return_wit_2`

Repair action: Replaced the initial `Admitted` placeholders with minimal proof skeletons based on the generated VC shapes:
- `entail_wit_2`: prove the strengthened prefix fact for `i + 1` by splitting `j < i + 1` into `j < i` or `j = i`.
- `return_wit_1`: choose the `__return == -1` disjunct with assertion-level `Right`, then reuse the loop invariant fact with `i_3 >= n` and `i_3 <= n`.
- `return_wit_2`: choose the early-return disjunct with assertion-level `Left`; the generated premises already match the target modulo parameter identity that `pre_process` is expected to expose.

Key proof sketch:

```coq
pre_process.
entailer!.
intros j Hj.
destruct Hj as [Hj0 Hjlt].
assert (j < i \/ j = i) by lia.
```

Why this change: These VCs are all direct consequences of the prefix invariant and the branch condition. The cheapest stable path is to keep the proofs short and let `pre_process` plus entailment automation discharge the preserved heap/resource facts.

## 2026-06-03 19:07:16 +0800

Phenomenon: `coqc` failed in `proof_of_xizi_id_first_nonfull_byte_return_wit_1` before any meaningful pure reasoning; after `Right; entailer!`, the remaining goal still needed `IntArray.full id_map_pre n_pre l` while the context only exposed `IntArray.full id_map n l`.

Location: [xizi_id_first_nonfull_byte_proof_manual.v](/home/yangfp/CAV/OS/CAV/output/verify_20260603_190108v_xizi_id_first_nonfull_byte/coq/generated/xizi_id_first_nonfull_byte_proof_manual.v:40), theorem `proof_of_xizi_id_first_nonfull_byte_return_wit_1`.

Repair action: Stopped proof-side iteration and returned to the annotation layer to add `n == n@pre` and `id_map == id_map@pre` to the loop invariant, then plan to rerun `symexec`.

Key compiler fragment:

```text
Unable to unify ... with ... IntArray.full id_map_pre n_pre l
```

Why this change: This is not a missing tactic; it is witness pollution from omitted unchanged-parameter facts, which the verify guidance explicitly classifies as an annotation problem. Continuing to patch the proof here would cement the wrong VC shape.

## 2026-06-03 19:07:16 +0800

Phenomenon: After regenerating from the strengthened invariant, `proof_manual.v` shrank to two lemmas: `entail_wit_2` and `return_wit_1`. The earlier polluted `return_wit_2` obligation disappeared from manual proof.

Location: [xizi_id_first_nonfull_byte_proof_manual.v](/home/yangfp/CAV/OS/CAV/output/verify_20260603_190108v_xizi_id_first_nonfull_byte/coq/generated/xizi_id_first_nonfull_byte_proof_manual.v:1)

Repair action: Replaced the fresh `Admitted` placeholders with proof scripts tailored to the cleaned VCs:
- `entail_wit_2` extends the prefix property from `i` to `i + 1` by splitting `j < i + 1` into `j < i` or `j = i`.
- `return_wit_1` chooses the `__return == -1` disjunct and applies the loop prefix fact to any `i_2 < n_pre`.

Key proof snippets:

```coq
assert (j < i \/ j = i) as Hsplit by lia.
```

```coq
Right.
entailer!.
```

Why this change: Once the VC is expressed purely in pre-state terms, the remaining obligations match the intended loop invariant exactly. Short direct proofs are more stable than trying to reconstruct additional facts through automation.
