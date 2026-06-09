# P128 Prod signs

## Problem (HumanEval 128)

You are given a vector arr of integers && you need to return
sum of magnitudes of integers multiplied by product of all signs
of each number in the vector, represented by 1, -1 || 0.
Note: return -32768 for empty arr.

Example:
>>> p128_prod_signs({1, 2, 2, -4}) == -9
>>> p128_prod_signs({0, 1}) == 0
>>> p128_prod_signs({}) == -32768

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `abs`

Coq model:

```coq
Definition he_abs_spec (x r : Z) : Prop :=
  r = Z.abs x.
```

Contract shape:

```c
int abs(int x)
/*@ Require INT_MIN < x && x <= INT_MAX
    Ensure he_abs_spec(x, __return)
*/;
```

## Reference Implementation

```c
/*
You are given a vector arr of integers && you need to return
sum of magnitudes of integers multiplied by product of all signs
of each number in the vector, represented by 1, -1 || 0.
Note: return -32768 for empty arr.

Example:
>>> p128_prod_signs({1, 2, 2, -4}) == -9
>>> p128_prod_signs({0, 1}) == 0
>>> p128_prod_signs({}) == -32768
*/

int abs(int x)

{
    if (x < 0) return -x;
    else return x;
}

int p128_prod_signs(int* arr, int arr_size)

{
    if (arr_size == 0) return -32768;
    int i, sum = 0, prods = 1;

    for (i = 0; i < arr_size; i++)
    {
        int current = arr[i];
        int mag = abs(current);

        sum += mag;
        if (current == 0) prods = 0;
        if (current < 0) prods = -prods;
   }
   return sum * prods;
}
```
