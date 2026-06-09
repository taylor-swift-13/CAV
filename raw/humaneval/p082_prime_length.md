# P082 Prime length

## Problem (HumanEval 82)

Write a function that takes a string && returns true if the string
length is a prime number || false otherwise
Examples
p082_prime_length("Hello") == true
p082_prime_length("abcdcba") == true
p082_prime_length("kittens") == true
p082_prime_length("orange") == false

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `strlen`

Coq model: represent strings as a list `l : list Z` of nonzero byte values followed by a zero terminator in memory.

Contract shape:

```c
int strlen(char *s)
/*@ With l n
    Require 0 <= n && n < INT_MAX &&
            Zlength(l) == n &&
            (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
            CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/;
```

## Reference Implementation

```c
/*
Write a function that takes a string && returns true if the string
length is a prime number || false otherwise
Examples
p082_prime_length("Hello") == true
p082_prime_length("abcdcba") == true
p082_prime_length("kittens") == true
p082_prime_length("orange") == false
*/

int strlen(char *s)

;

int p082_prime_length(char *str)

{
    int i;
    int n = strlen(str);
    if (n < 2) return 0;

    for (i = 2; i * i <= n; i++) {
        if (n % i == 0) return 0;
    }
    return 1;
}
```
