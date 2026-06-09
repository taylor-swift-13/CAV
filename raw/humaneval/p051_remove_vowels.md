# P051 Remove vowels

## Problem (HumanEval 51)

p051_remove_vowels is a function that takes string && returns string without vowels.
>>> p051_remove_vowels("")
""
>>> p051_remove_vowels("abcdef\nghijklm")
"bcdf\nghjklm"
>>> p051_remove_vowels("abcdef")
"bcdf"
>>> p051_remove_vowels("aaaaa")
""
>>> p051_remove_vowels("aaBAA")
"B"
>>> p051_remove_vowels("zbcd")
"zbcd"

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `malloc_char_array`

Allocates a fresh writable character array with unspecified contents.

Contract shape:

```c
char *malloc_char_array(int n)
/*@ Require n > 0 && n < INT_MAX
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/;
```

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
p051_remove_vowels is a function that takes string && returns string without vowels.
>>> p051_remove_vowels("")
""
>>> p051_remove_vowels("abcdef
ghijklm")
"bcdf
ghjklm"
>>> p051_remove_vowels("abcdef")
"bcdf"
>>> p051_remove_vowels("aaaaa")
""
>>> p051_remove_vowels("aaBAA")
"B"
>>> p051_remove_vowels("zbcd")
"zbcd"
*/

char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *p051_remove_vowels(char *text)

{
    int i;
    int j = 0;
    int n = strlen(text);
    char *out = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        int c = text[i];
        if (c == 65 || c == 69 || c == 73 || c == 79 || c == 85 ||
            c == 97 || c == 101 || c == 105 || c == 111 || c == 117) {
        } else {
            out[j] = c;
            j = j + 1;
        }
    }
    out[j] = 0;
    return out;
}
```
