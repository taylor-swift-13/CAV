# P014 All prefixes

## Problem (HumanEval 14)

Return vector of all prefixes from shortest to longest of the input string
>>> p014_all_prefixes("abc")
{"a", "ab", "abc"}

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

StrArray p014_all_prefixes(const char* str){
    StrArray out;
    int n = (int)strlen(str);
    out.size = n;
    out.data = (char**)malloc((size_t)n * sizeof(char*));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    for (int i=0;i<n;i++)
    {
        out.data[i] = (char*)malloc((size_t)i + 2);
        if (out.data[i] == NULL) return out;
        memcpy(out.data[i], str, (size_t)i + 1);
        out.data[i][i+1] = '\0';
    }
    return out;
}
```
