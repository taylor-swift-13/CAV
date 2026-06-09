# P158 Find max

## Problem (HumanEval 158)

Write a function that accepts a vector of strings.
The vector contains different words. Return the word with maximum number
of unique characters. If multiple strings have maximum number of unique
characters, return the one which comes first in lexicographical order.

p158_find_max({"name", "of", 'string"}) == 'string"
p158_find_max({"name", "enam", "game"}) == "enam"
p158_find_max({"aaaaaaa", "bb" ,"cc"}) == "aaaaaaa"

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
const char* p158_find_max(char** words, int words_size){
    const char* max="";
    int maxu=0;
    for (int i=0;i<words_size;i++)
    {
        int seen[256] = {0};
        int unique = 0;
        for (size_t j=0;j<strlen(words[i]);j++)
            if (!seen[(unsigned char)words[i][j]]) {
                seen[(unsigned char)words[i][j]] = 1;
                unique += 1;
            }
        if (unique>maxu || (unique==maxu && strcmp(words[i], max) < 0))
        {
            max=words[i];
            maxu=unique;
        }
    }
    return max;
}
```
