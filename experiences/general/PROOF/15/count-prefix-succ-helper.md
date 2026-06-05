# Read-only counting scan: prove the prefix-step lemma once

Symptom:

- A single-loop read-only array scan keeps an invariant like `count = spec(sublist 0 i l)`.
- The branch entailment or return witness then gets stuck on goals shaped like:
  - `spec(sublist 0 (i + 1) l) = ...`
  - `count + 1 = spec(sublist 0 (i + 1) l)`
  - `count = spec(sublist 0 (i + 1) l)`

Cause:

- The remaining VC is no longer about separation logic ownership. It is a pure list fact saying "the processed prefix grew by exactly one element".
- If you expand the recursive spec directly inside each witness, you end up redoing the same `sublist` normalization and `Znth` case split in multiple places.

Rule:

- Keep the invariant in prefix-summary form.
- In `proof_manual.v`, first prove one helper lemma that rewrites the next prefix into "old prefix + current element", then reuse it in both branch witnesses.

Minimal shape:

```coq
Lemma spec_prefix_succ :
  forall l i,
    0 <= i < Zlength l ->
    spec (sublist 0 (i + 1) l) =
    spec (sublist 0 i l) +
    step (Znth i l 0).
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite spec_app.
  rewrite (sublist_single 0 i l) by lia.
  simpl.
  destruct (step_dec (Znth i l 0)); lia.
Qed.
```

Then each branch witness should:

- `rewrite spec_prefix_succ by lia`
- rewrite the invariant equality for the old prefix summary
- discharge the final zero/nonzero case by `destruct ...; lia`

Return witness:

- First derive the exit index equality (`i = n` or equivalent).
- Rewrite by the invariant's prefix-summary equality.
- Only then use `sublist_self` to collapse `sublist 0 n l` to `l`.

Scope:

- Read-only array/string scans
- counting / boolean-accumulation loops
- any single-loop invariant of the form "accumulator = spec(processed prefix)"
