# P064 Vowels count

## Problem (HumanEval 64)

Write a function p064_vowels_count which takes a string representing a word as input && returns the number of vowels in the string. Vowels in this case are 'a', 'e', 'i', 'o', 'u'.
Here, 'y' is also a vowel, but only when it is at the end of the given word.
Example:
>>> p064_vowels_count("abcde")
2
>>> p064_vowels_count("ACEDY")
3

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
Write a function p064_vowels_count which takes a string representing a word as input && returns the number of vowels in the string. Vowels in this case are 'a', 'e', 'i', 'o', 'u'.
Here, 'y' is also a vowel, but only when it is at the end of the given word.
Example:
>>> p064_vowels_count("abcde")
2
>>> p064_vowels_count("ACEDY")
3
*/

int strlen(char *s)

;

int p064_vowels_count(char *s)

{
    int n = strlen(s);
    int count = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (s[i] == 97 || s[i] == 101 || s[i] == 105 ||
            s[i] == 111 || s[i] == 117 ||
            s[i] == 65 || s[i] == 69 || s[i] == 73 ||
            s[i] == 79 || s[i] == 85) {
            count = count + 1;
        }
    }
    if (n > 0 && (s[n - 1] == 121 || s[n - 1] == 89)) {
        count = count + 1;
    }
    return count;
}
```
