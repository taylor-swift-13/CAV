# P054 Same chars

## Problem (HumanEval 54)

Check if two words have the same characters.
>>> p054_same_chars("eabcdzzzz", "dddzzzzzzzddeddabc")
true
>>> p054_same_chars("abcd", "dddddddabc")
true
>>> p054_same_chars("dddddddabc", "abcd")
true
>>> p054_same_chars("eabcd", "dddddddabc")
false
>>> p054_same_chars("abcd", "dddddddabce")
false
>>> p054_same_chars("eabcdzzzz", "dddzzzzzzzddddabc")
false

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

### `strchr`

Coq model: define a relation over the input character list, searched byte `c`, and result pointer. The result is `0` iff `c` does not occur before the terminator; otherwise it points to an occurrence of `c` inside the owned string.

Contract shape:

```c
char *strchr(char *s, int c)
/*@ With l n
    Require 0 <= n && n < INT_MAX &&
            Zlength(l) == n &&
            CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure CharArray::full(s, n + 1, app(l, cons(0, nil))) &&
           strchr_spec(s, l, c, __return)
*/;
```

## Reference Implementation

```c
/*
Check if two words have the same characters.
>>> p054_same_chars("eabcdzzzz", "dddzzzzzzzddeddabc")
true
>>> p054_same_chars("abcd", "dddddddabc")
true
>>> p054_same_chars("dddddddabc", "abcd")
true
>>> p054_same_chars("eabcd", "dddddddabc")
false
>>> p054_same_chars("abcd", "dddddddabce")
false
>>> p054_same_chars("eabcdzzzz", "dddzzzzzzzddddabc")
false
*/

int strlen(char *s)

;

char *strchr(char *s, int c)

;

int p054_same_chars(char *s0, char *s1)

{
    int len0 = strlen(s0);
    int len1 = strlen(s1);
    int i;

    for (i = 0; i < len0; i++)
    {
        int chr = s0[i];
        char *found = strchr(s1, chr);
        if (found == 0) {
            return 0;
        }
    }

    for (i = 0; i < len1; i++)
    {
        int chr = s1[i];
        char *found = strchr(s0, chr);
        if (found == 0) {
            return 0;
        }
    }
    return 1;
}
```
