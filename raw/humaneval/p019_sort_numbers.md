# P019 Sort numbers

## Problem (HumanEval 19)

Input is a space-delimited string of numberals from "zero" to "nine".
Valid choices are "zero", "one", 'two", 'three", "four", "five", 'six", 'seven", "eight" && "nine".
Return the string with numbers sorted from smallest to largest
>>> p019_sort_numbers('three one five")
"one three five"

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
char* p019_sort_numbers(const char* numbers){
    const char* words[] = {"zero","one","two","three","four","five","six","seven","eight","nine"};
    int count[10];
    int n = (int)strlen(numbers);
    char token[32];
    int tlen = 0;
    int out_len = 1;
    char* out;

    for (int i=0;i<10;i++) count[i]=0;
    for (int i=0;i<=n;i++) {
        char ch = (i < n) ? numbers[i] : ' ';
        if (ch == ' ') {
            if (tlen > 0) {
                token[tlen] = '\0';
                for (int d=0; d<10; d++) {
                    if (strcmp(token, words[d]) == 0) {
                        count[d] += 1;
                        break;
                    }
                }
                tlen = 0;
            }
        } else if (tlen < 31) {
            token[tlen++] = ch;
        }
    }
    for (int i=0;i<10;i++)
        out_len += count[i] * ((int)strlen(words[i]) + 1);

    out = (char*)malloc((size_t)out_len);
    if (out == NULL) return NULL;
    out[0] = '\0';
    {
        int first = 1;
        for (int i=0;i<10;i++)
            for (int j=0;j<count[i];j++) {
                if (!first) strcat(out, " ");
                strcat(out, words[i]);
                first = 0;
            }
    }
    return out;
}
```
