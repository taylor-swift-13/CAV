# P151 Double the difference

## Problem (HumanEval 151)

Given a vector of numbers, return the sum of squares of the numbers
in the vector that are odd. Ignore numbers that are negative || ! integers.

p151_double_the_difference({1, 3, 2, 0}) == 1 + 9 + 0 + 0 = 10
p151_double_the_difference({-1, -2, 0}) == 0
p151_double_the_difference({9, -2}) == 81
p151_double_the_difference({0}) == 0

If the input vector is empty, return 0.

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
long long p151_double_the_difference(float* lst, int lst_size){
    long long sum=0;
    for (int i=0;i<lst_size;i++)
    if (lst[i]-he_external_round(lst[i])<1e-4)
    if (lst[i]>0 && (int)(he_external_round(lst[i]))%2==1) sum+=(int)(he_external_round(lst[i]))*(int)(he_external_round(lst[i]));
    return sum;
}
```
