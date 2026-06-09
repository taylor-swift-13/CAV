# P149 Sorted list sum

## Problem (HumanEval 149)

Write a function that accepts a vector of strings as a parameter,
deletes the strings that have odd lengths from it,
&& returns the resulted vector with a sorted order,
The vector is always a vector of strings && never a vector of numbers,
&& it may contain duplicates.
The order of the vector should be ascending by length of each word, && you
should return the vector sorted by that rule.
If two words have the same length, sort the vector alphabetically.
The function should return a vector of strings in sorted order.
You may assume that all words will have the same length.
For example:
assert vector_sort({"aa", "a", "aaa"}) => {"aa"}
assert vector_sort({"ab", "a", "aaa", "cd"}) => {"ab", "cd"}

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

static int cmp_word(const void* a, const void* b) {
    const char* x = *(const char**)a;
    const char* y = *(const char**)b;
    int lx = (int)strlen(x);
    int ly = (int)strlen(y);
    if (lx != ly) return lx - ly;
    return strcmp(x, y);
}

StrArray p149_sorted_list_sum(char** lst, int lst_size){
    StrArray out;
    out.size = 0;
    out.data = (char**)malloc((size_t)lst_size * sizeof(char*));
    if (out.data == NULL) return out;
    for (int i=0;i<lst_size;i++)
    if ((int)strlen(lst[i])%2==0) out.data[out.size++] = lst[i];
    qsort(out.data, (size_t)out.size, sizeof(char*), cmp_word);
    return out;
}
```
