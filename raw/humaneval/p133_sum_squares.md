# P133 Sum squares

## Problem (HumanEval 133)

You are given a vector of numbers.
You need to return the sum of squared numbers in the given vector,
round each element in the vector to the upper int(Ceiling) first.
Examples:
For lst = {1,2,3} the output should be 14
For lst = {1,4,9} the output should be 98
For lst = {1,3,5,7} the output should be 84
For lst = {1.4,4.2,0} the output should be 29
For lst = {-2.4,1,1} the output should be 6

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `he_external_ceil`

Coq model: define the least integer greater than or equal to the input value.

Contract shape:

```c
int he_external_ceil(double x)
/*@ Require emp
    Ensure he_ceil_spec(x, __return)
*/;
```

## Reference Implementation

```c
int he_external_ceil(double x);
int p133_sum_squares(float* lst, int lst_size){
    int sum=0;
    for (int i=0;i<lst_size;i++)
        sum+=he_external_ceil(lst[i])*he_external_ceil(lst[i]);
    return sum;
}
```
