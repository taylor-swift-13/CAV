# P134 Check if last char is a letter

## Problem (HumanEval 134)

Create a function that returns true if the last character
of a given string is an alphabetical character && is !
a part of a word, && false otherwise.
Note: "word" is a group of characters separated by space.

Examples:
p134_check_if_last_char_is_a_letter("apple pie") ➞ false
p134_check_if_last_char_is_a_letter("apple pi e") ➞ true
p134_check_if_last_char_is_a_letter("apple pi e ") ➞ false
p134_check_if_last_char_is_a_letter("") ➞ false

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
Create a function that returns true if the last character
of a given string is an alphabetical character && is !
a part of a word, && false otherwise.
Note: "word" is a group of characters separated by space.

Examples:
p134_check_if_last_char_is_a_letter("apple pie") -> false
p134_check_if_last_char_is_a_letter("apple pi e") -> true
p134_check_if_last_char_is_a_letter("apple pi e ") -> false
p134_check_if_last_char_is_a_letter("") -> false
*/

int strlen(char *s)

;

int p134_check_if_last_char_is_a_letter(char *txt)

{
    int n = strlen(txt);
    if (n == 0) return 0;

    int chr = txt[n - 1];
    if (chr < 65) return 0;
    if (chr > 90 && chr < 97) return 0;
    if (chr > 122) return 0;

    if (n == 1) return 1;

    chr = txt[n - 2];
    if (chr == 32) return 1;
    return 0;
}
```
