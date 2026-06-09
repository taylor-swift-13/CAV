# P117 Select words

## Problem (HumanEval 117)

Given a string s && a natural number n, you have been tasked to implement
a function that returns a vector of all words from string s that contain exactly
n consonants, in order these words appear in the string s.
If the string s is empty then the function should return an empty vector.
Note: you may assume the input string contains only letters && spaces.
Examples:
p117_select_words("Mary had a little lamb", 4) ==> {"little"}
p117_select_words("Mary had a little lamb", 3) ==> {"Mary", "lamb"}
p117_select_words('simple white space", 2) ==> {}
p117_select_words("Hello world", 4) ==> {"world"}
p117_select_words("Uncle sam", 3) ==> {"Uncle"}

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

StrArray p117_select_words(const char* s,int n){
    const char* vowels="aeiouAEIOU";
    int len = (int)strlen(s);
    int cap = 8;
    int start = -1;
    StrArray out;
    int numc=0;
    out.size = 0;
    out.data = (char**)malloc((size_t)cap * sizeof(char*));
    if (out.data == NULL) return out;
    for (int i=0;i<=len;i++)
        if (i==len || s[i]==' ')
        {
            if (start >= 0 && numc==n) {
                int wlen = i - start;
                char* w = (char*)malloc((size_t)wlen + 1);
                if (w == NULL) return out;
                memcpy(w, s + start, (size_t)wlen);
                w[wlen] = '\0';
                if (out.size == cap) {
                    int new_cap = cap * 2;
                    char** tmp = (char**)realloc(out.data, (size_t)new_cap * sizeof(char*));
                    if (tmp == NULL) return out;
                    out.data = tmp;
                    cap = new_cap;
                }
                out.data[out.size++] = w;
            }
            start = -1;
            numc=0;
        }
        else
        {
            if (start < 0) start = i;
            if ((s[i]>=65 && s[i]<=90) || (s[i]>=97 && s[i]<=122))
            if (strchr(vowels,s[i])==NULL)
                numc+=1;
        }
    return out;
}
```
