# P112 Reverse delete

## Problem (HumanEval 112)

Task
We are given two strings s && c, you have to deleted all the characters in s that are equal to any character in c
then check if the result string is palindrome.
A string is called palindrome if it reads the same backward as forward.
You should return a vector containing the result string && "True"/"False" for the check.
Example
For s = "abcde", c = "ae", the result should be ("bcd","False")
For s = "abcdef", c = "b"  the result should be ("acdef","False")
For s = "abcdedcba", c = "ab", the result should be ("cdedc","True")

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
typedef struct {
    char** data;
    int size;
} StrArray;

StrArray p112_reverse_delete(const char* s,const char* c){
    StrArray out;
    int n = (int)strlen(s);
    int k = 0;
    char* filtered = (char*)malloc((size_t)n + 1);
    int pal = 1;
    out.size = 2;
    out.data = (char**)malloc(2 * sizeof(char*));
    if (filtered == NULL || out.data == NULL) {
        free(filtered);
        free(out.data);
        out.size = 0;
        out.data = NULL;
        return out;
    }

    for (int i=0;i<n;i++) {
        if (strchr(c, s[i]) == NULL) {
            filtered[k++] = s[i];
        }
    }
    filtered[k] = '\0';

    for (int i=0;i<k/2;i++) {
        if (filtered[i] != filtered[k-1-i]) {
            pal = 0;
            break;
        }
    }

    out.data[0] = filtered;
    out.data[1] = (char*)malloc(pal ? 5 : 6);
    if (out.data[1] == NULL) {
        free(filtered);
        free(out.data);
        out.size = 0;
        out.data = NULL;
        return out;
    }
    if (pal) memcpy(out.data[1], "True", 5);
    else memcpy(out.data[1], "False", 6);
    return out;
}
```
