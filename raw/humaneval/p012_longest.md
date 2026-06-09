# P012 Longest

## Problem (HumanEval 12)

Out of vector of strings, return the p012_longest one. Return the first one in case of multiple
strings of the same length. Return None in case the input vector is empty.
>>> p012_longest({})

>>> p012_longest({"a", "b", "c"})
"a"
>>> p012_longest({"a", "bb", "ccc"})
"ccc"

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
const char* p012_longest(const char** strings, int strings_size){
    const char* out = "";
    int best = -1;
    for (int i=0;i<strings_size;i++)
    {
        int len = (int)strlen(strings[i]);
        if (len > best) {
            best = len;
            out = strings[i];
        }
    }
    return out;
}
```
