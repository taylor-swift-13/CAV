# P092 Any int

## Problem (HumanEval 92)

Create a function that takes 3 numbers.
Returns true if one of the numbers is equal to the sum of the other two, && all numbers are integers.
Returns false in any other cases.

Examples
p092_any_int(5, 2, 7) ➞ true

p092_any_int(3, 2, 2) ➞ false

p092_any_int(3, -2, 1) ➞ true

p092_any_int(3.6, -2.2, 2) ➞ false

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `he_external_round`

Coq model: define nearest-integer rounding with ties away from zero, matching the HumanEval statement when used for closest-integer tasks.

Contract shape:

```c
int he_external_round(double x)
/*@ Require emp
    Ensure he_round_spec(x, __return)
*/;
```

## Reference Implementation

```c
int he_external_round(double x);
bool p092_any_int(float a, float b, float c){
    if (he_external_round(a)!=a) return false;
    if (he_external_round(b)!=b) return false;
    if (he_external_round(c)!=c) return false;
    if (a+b==c || a+c==b || b+c==a) return true;
    return false;
}
```
