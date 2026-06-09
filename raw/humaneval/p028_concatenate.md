# P028 Concatenate

## Problem (HumanEval 28)

Concatenate vector of strings into a single string
>>> p028_concatenate({})
""
>>> p028_concatenate({"a", "b", "c"})
"abc"

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
char* p028_concatenate(char** strings, int strings_size){
    int total = 1;
    char* out;
    int k = 0;
    for (int i=0;i<strings_size;i++) total += (int)strlen(strings[i]);
    out = (char*)malloc((size_t)total);
    if (out == NULL) return NULL;
    for (int i=0;i<strings_size;i++) {
        int len = (int)strlen(strings[i]);
        memcpy(out + k, strings[i], (size_t)len);
        k += len;
    }
    out[k] = '\0';
    return out;
}
```
