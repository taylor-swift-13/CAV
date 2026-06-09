# P101 Words string

## Problem (HumanEval 101)

You will be given a string of words separated by commas || spaces. Your task is
to split the string into words && return a vector of the words.

For example:
p101_words_string("Hi, my name is John") == {"Hi", "my", "name", "is", "John"}
p101_words_string("One, two, three, four, five, six") == {"One", 'two", 'three", "four", "five", 'six"}

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

StrArray p101_words_string(const char* s){
    StrArray out;
    int cap = 8;
    int start = -1;
    int n = (int)strlen(s);
    out.size = 0;
    out.data = (char**)malloc((size_t)cap * sizeof(char*));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    for (int i=0;i<=n;i++) {
        char ch = (i < n) ? s[i] : ' ';
        if (ch==' ' || ch==',') {
            if (start >= 0) {
                int len = i - start;
                char* w = (char*)malloc((size_t)len + 1);
                if (w == NULL) return out;
                memcpy(w, s + start, (size_t)len);
                w[len] = '\0';
                if (out.size == cap) {
                    int new_cap = cap * 2;
                    char** tmp = (char**)realloc(out.data, (size_t)new_cap * sizeof(char*));
                    if (tmp == NULL) return out;
                    out.data = tmp;
                    cap = new_cap;
                }
                out.data[out.size++] = w;
                start = -1;
            }
        } else if (start < 0) {
            start = i;
        }
    }
    return out;
}
```
