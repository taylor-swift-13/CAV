# Halving recursion specs need a fuel-irrelevance lemma, not repeated unfolding

Symptom:

- The task-local spec is defined through a fuelled recursion such as
  `spec_z n := spec_fuel n (Z.to_nat n)`.
- The loop VC for one iteration needs a step equation on `n ÷ 2`.
- A helper that unfolds `spec_fuel` one more recursive step often produces the wrong target shape, for example exposing `spec_fuel (n / 2) (...)` or even `(n / 2) / 2` where the witness only wants `spec_z (n ÷ 2)`.

Cause:

- The real proof obligation is not "unfold deeper". It is "any fuel that is large enough for the current nonnegative input computes the same result".
- Once the loop body has changed `n` to `n ÷ 2`, the witness naturally mixes the original definitional fuel `Z.to_nat n` with another sufficient fuel coming from the smaller argument.

Rule:

- First prove a local fuel-irrelevance lemma for nonnegative inputs:
  any two fuels both bounded below by `n` give the same `spec_fuel n`.
- Derive a `spec_fuel_enough` lemma and only then state the one-step equation for `spec_z`.
- Keep the induction conservative: explicit predicate in `well_founded_induction`, explicit comparison split on `Z.leb_spec`, and explicit premises instead of brittle `rewrite ... by ...`.

Minimal shape:

```coq
Lemma spec_fuel_irrelevant :
  forall n,
    0 <= n ->
    forall fuel1 fuel2,
      n <= Z.of_nat fuel1 ->
      n <= Z.of_nat fuel2 ->
      spec_fuel n fuel1 = spec_fuel n fuel2.

Lemma spec_fuel_enough :
  forall fuel n,
    0 <= n ->
    n <= Z.of_nat fuel ->
    spec_fuel n fuel = spec_z n.

Lemma spec_z_step :
  forall n,
    0 < n ->
    spec_z n = step_of n + spec_z (n ÷ 2).
```

Then the branch witness should use `spec_z_step` once and leave only quotient/range side conditions to `lia`, `Z.quot_pos`, or `Z.quot_le_upper_bound`.

Scope:

- Scalar single-loop proofs whose semantic spec is a fuelled recursion over a shrinking nonnegative integer
- Especially useful when the C VC mentions `Z.quot` (`÷`) but the spec definition is phrased through a fuel based on `Z.to_nat`
