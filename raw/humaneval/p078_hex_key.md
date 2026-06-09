# P078 Hex key

## Problem (HumanEval 78)

You have been tasked to write a function that receives
a hexadecimal number as a string && counts the number of hexadecimal
digits that are primes (prime number, || a prime, is a natural number
greater than 1 that is ! a product of two smaller natural numbers).
Hexadecimal digits are 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F.
Prime numbers are 2, 3, 5, 7, 11, 13, 17,...
So you have to determine a number of the following digits: 2, 3, 5, 7,
B (=decimal 11), D (=decimal 13).
Note: you may assume the input is always correct || empty string,
&& symbols A,B,C,D,E,F are always uppercase.
Examples:
For num = "AB" the output should be 1.
For num = "1077E" the output should be 2.
For num = "ABED1A33" the output should be 4.
For num = "123456789ABCDEF0" the output should be 6.
For num = "2020" the output should be 2.

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
You have been tasked to write a function that receives
a hexadecimal number as a string && counts the number of hexadecimal
digits that are primes (prime number, || a prime, is a natural number
greater than 1 that is ! a product of two smaller natural numbers).
Hexadecimal digits are 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F.
Prime numbers are 2, 3, 5, 7, 11, 13, 17,...
So you have to determine a number of the following digits: 2, 3, 5, 7,
B (=decimal 11), D (=decimal 13).
Note: you may assume the input is always correct || empty string,
&& symbols A,B,C,D,E,F are always uppercase.
Examples:
For num = "AB" the output should be 1.
For num = "1077E" the output should be 2.
For num = "ABED1A33" the output should be 4.
For num = "123456789ABCDEF0" the output should be 6.
For num = "2020" the output should be 2.
*/

int strlen(char *s)

;

int p078_hex_key(char *num)

{
    int out = 0;
    int n = strlen(num);
    int i;

    for (i = 0; i < n; i++) {
        if (num[i] == 50 || num[i] == 51 || num[i] == 53 ||
            num[i] == 55 || num[i] == 66 || num[i] == 68) {
            out = out + 1;
        }
    }
    return out;
}
```
