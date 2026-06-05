# C parity branches need `Z.rem` to bridge into `Z.even`

Symptom:

- The C loop branches on parity with conditions such as `x % 2 == 0` or `x % 2 != 0`.
- The generated QCP witnesses carry those branch facts as `Z.rem x 2 = 0` or `Z.rem x 2 <> 0`.
- The task-local Coq spec or safety predicate instead branches on `Z.even x`, so helper lemmas written against `Z.mod` do not match the VC shape.

Cause:

- QCP models the executable C `%` operator with `Z.rem`, not with Euclidean remainder `Z.mod`.
- If the proof starts from `Z.mod`-based parity lemmas, the main witness gets stuck before it can even unfold the spec-side `if Z.even x then ... else ...`.

Rule:

- For parity branches coming from executable C `%`, write the first bridge lemmas against `Z.rem`:
  - `Z.rem x 2 = 0 -> Z.even x = true`
  - `Z.rem x 2 <> 0 -> Z.even x = false`
- Use those lemmas immediately before unfolding one-step semantic or safety helpers that branch on `Z.even`.
- Do not start with `Z.mod` parity facts unless the VC already contains `Z.mod`; otherwise the helper shape does not align with generated witnesses.

Minimal shape:

```coq
Lemma rem2_zero_even_true :
  forall x, Z.rem x 2 = 0 -> Z.even x = true.

Lemma rem2_nonzero_even_false :
  forall x, Z.rem x 2 <> 0 -> Z.even x = false.

Lemma spec_even_step :
  forall x fuel,
    0 <= fuel ->
    x <> 1 ->
    Z.rem x 2 = 0 ->
    spec_safe x (fuel + 1) ->
    spec_safe (x / 2) fuel.

Lemma spec_odd_step :
  forall x fuel,
    0 <= fuel ->
    x <> 1 ->
    Z.rem x 2 <> 0 ->
    spec_safe x (fuel + 1) ->
    spec_safe (3 * x + 1) fuel.
```

Scope:

- `problem_kind = math`
- `data = scalar`
- `pattern = single_loop`
- Scalar arithmetic loops whose executable branch condition uses `%` but whose Coq-side recursion or safety predicate uses `Z.even`
