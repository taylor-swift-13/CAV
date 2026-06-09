# P143 Words in sentence

## Problem (HumanEval 143)

You are given a string representing a sentence,
the sentence contains some words separated by a space,
&& you have to return a string that contains the words from the original sentence,
whose lengths are prime numbers,
the order of the words in the new string should be the same as the original one.

Example 1:
    Input: sentence = "This is a test"
    Output: "is"

Example 2:
    Input: sentence = "lets go for swimming"
    Output: "go for"

Constraints:
    * 1 <= len(sentence) <= 100
    * sentence contains only letters

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `malloc_char_array`

Allocates a fresh writable character array with unspecified contents.

Contract shape:

```c
char *malloc_char_array(int n)
/*@ Require n > 0 && n < INT_MAX
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/;
```

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
/*
You are given a string representing a sentence,
the sentence contains some words separated by a space,
and you have to return a string that contains the words from the original sentence,
whose lengths are prime numbers,
the order of the words in the new string should be the same as the original one.

Example 1:
    Input: sentence = "This is a test"
    Output: "is"

Example 2:
    Input: sentence = "lets go for swimming"
    Output: "go for"

Constraints:
    * 1 <= len(sentence) <= 100
    * sentence contains only letters
*/

char *malloc_char_array(int n)

;

int strlen(char *s)

;

int is_prime_len(int len)

{
    int j;
    int composite = 0;
    if (len < 2) {
        return 0;
    }

    for (j = 2; j < len; j++) {
        if (len % j == 0) {
            composite = 1;
        }
    }

    if (composite == 1) {
        return 0;
    }
    return 1;
}

char *p143_words_in_sentence(char *sentence)

{
    int n = strlen(sentence);
    char *out = malloc_char_array(n + 2);
    int out_len = 0;
    int i = 0;

    while (i < n) {

        while (i < n && sentence[i] == 32) {
            i = i + 1;
        }

        if (i < n) {
            int start = i;

            while (i < n && sentence[i] != 32) {
                i = i + 1;
            }

            int word_len = i - start;
            int prime = is_prime_len(word_len);
            if (prime == 1) {
                int k;
                if (out_len > 0) {
                    out[out_len] = 32;
                    out_len = out_len + 1;
                }

                for (k = 0; k < word_len; k++) {
                    out[out_len] = sentence[start + k];
                    out_len = out_len + 1;
                }
            }
        }
    }

    out[out_len] = 0;
    return out;
}
```
