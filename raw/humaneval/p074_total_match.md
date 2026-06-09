# P074 Total match

## Problem (HumanEval 74)

Write a function that accepts two vectors of strings && returns the vector that has
total number of chars in the all strings of the vector less than the other vector.

if the two vectors have the same number of chars, return the first vector.

Examples
p074_total_match({}, {}) ➞ {}
p074_total_match({"hi", "admin"}, {"hI", "Hi"}) ➞ {"hI", "Hi"}
p074_total_match({"hi", "admin"}, {"hi", "hi", "admin", "project"}) ➞ {"hi", "admin"}
p074_total_match({"hi", "admin"}, {"hI", "hi", "hi"}) ➞ {"hI", "hi", "hi"}
p074_total_match({"4"}, {"1", "2", "3", "4", "5"}) ➞ {"4"}

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
    const char** data;
    int size;
} StrArray;

StrArray p074_total_match(const char** lst1, int lst1_size, const char** lst2, int lst2_size){
    int num1,num2,i;
    StrArray out;
    num1=0;num2=0;
    for (i=0;i<lst1_size;i++)
        num1+=(int)strlen(lst1[i]);
    for (i=0;i<lst2_size;i++)
        num2+=(int)strlen(lst2[i]);
    if (num1>num2) {
        out.data = lst2;
        out.size = lst2_size;
        return out;
    }
    out.data = lst1;
    out.size = lst1_size;
    return out;
}
```
