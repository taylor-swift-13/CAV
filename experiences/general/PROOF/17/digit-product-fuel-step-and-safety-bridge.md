# Digit-product fuel specs need separate semantic-step and safety-step lemmas

Symptom:

- The task-local spec is defined through fuelled recursion, for example a semantic function
  `digit_product_acc_z n acc := digit_product_loop_fuel n acc (Z.to_nat n)`
  and a safety predicate
  `digit_product_safe_z n acc := digit_product_safe_fuel n acc (Z.to_nat n)`.
- After `symexec`, the preservation and return VCs already contain the right program-state facts, but the manual proof gets stuck on one-step obligations such as:
  `digit_product_acc_z (n ÷ 10) (acc * (n % 10)) = ...`
  and
  `digit_product_safe_z (n ÷ 10) (acc * (n % 10))`.
- Repeatedly unfolding the fuelled definitions inside the witness produces awkward targets with predecessor fuel or mixed `Z.div` / `Z.quot` forms instead of the exact helper predicates the VC wants.

Cause:

- The blocker is not missing annotation information. The blocker is that the VC needs a one-step bridge from the current residual state to the next residual state, while the definitions are packaged through `Z.to_nat n` fuel.
- The semantic equation and the signed-overflow side condition move together but are logically different obligations, so trying to solve both by ad-hoc unfolding in the main witness is brittle.

Rule:

- First prove local fuel-stability lemmas: once the fuel is at least `Z.to_nat n`, extra fuel does not change either the semantic recursion or the safety recursion.
- Then state two separate one-step bridge lemmas:
  one for the semantic accumulator equation, and one for the safety predicate plus current multiplication range.
- In the witness proofs, use those step lemmas once, then discharge the remaining quotient/remainder side conditions with basic arithmetic lemmas.

Minimal shape:

```coq
Lemma spec_loop_fuel_stable :
  forall fuel n acc extra,
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    spec_loop_fuel n acc (fuel + extra)%nat =
    spec_loop_fuel n acc fuel.

Lemma spec_safe_fuel_stable :
  forall fuel n acc extra,
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    spec_safe_fuel n acc (fuel + extra)%nat =
    spec_safe_fuel n acc fuel.

Lemma spec_acc_step :
  forall n acc,
    0 < n ->
    spec_acc_z n acc = spec_acc_z (n ÷ 10) (acc * (n % 10)).

Lemma spec_safe_step :
  forall n acc,
    0 < n ->
    spec_safe_z n acc ->
    (INT_MIN <= acc * (n % 10) <= INT_MAX) /\
    spec_safe_z (n ÷ 10) (acc * (n % 10)).
```

Scope:

- `problem_kind = product`
- `data = scalar`
- `pattern = single_loop`
- Scalar loops whose spec is a fuelled recursion over a shrinking nonnegative integer and whose preservation VC must carry both semantic equality and executable signed-overflow safety
