# P029 Filter by prefix

## Problem (HumanEval 29)

Filter an input vector of strings only for ones that start with a given prefix.
>>> p029_filter_by_prefix({}, "a")
{}
>>> p029_filter_by_prefix({"abc", "bcd", "cde", "vector"}, "a")
{"abc", "vector"}

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
typedef struct {
    char** data;
    int size;
} StrArray;

StrArray p029_filter_by_prefix(char** strings, int strings_size, const char* prefix){
    StrArray out;
    int plen = (int)strlen(prefix);
    out.size = 0;
    out.data = (char**)malloc((size_t)strings_size * sizeof(char*));
    if (out.data == NULL) return out;
    for (int i=0;i<strings_size;i++)
        if (strncmp(strings[i], prefix, (size_t)plen)==0) out.data[out.size++] = strings[i];
    return out;
}
```
