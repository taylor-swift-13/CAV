# P113 Odd count

## Problem (HumanEval 113)

Given a vector of strings, where each string consists of only digits, return a vector.
Each element i of the output should be 'the number of odd elements in the
string i of the input." where all the i's should be replaced by the number
of odd digits in the i'th string of the input.

>>> p113_odd_count({"1234567"})
{'the number of odd elements 4n the str4ng 4 of the 4nput."}
>>> p113_odd_count({"3","11111111"})
{'the number of odd elements 1n the str1ng 1 of the 1nput.",
 'the number of odd elements 8n the str8ng 8 of the 8nput."}

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

StrArray p113_odd_count(char** lst, int lst_size){
    StrArray out;
    const char* tpl = "the number of odd elements in the string i of the input.";
    out.size = lst_size;
    out.data = (char**)malloc((size_t)lst_size * sizeof(char*));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    for (int i=0;i<lst_size;i++)
        {
            int sum=0;
            char numbuf[32];
            int k = 0;
            int numlen;
            int outlen = 0;
            for (size_t j=0;j<strlen(lst[i]);j++)
                if (lst[i][j]>=48 && lst[i][j]<=57 && lst[i][j]%2==1)
                sum+=1;
            sprintf(numbuf, "%d", sum);
            numlen = (int)strlen(numbuf);
            for (size_t j=0;j<strlen(tpl);j++) {
                if (tpl[j]=='i') outlen += numlen;
                else outlen += 1;
            }
            out.data[i] = (char*)malloc((size_t)outlen + 1);
            if (out.data[i] == NULL) return out;
            for (size_t j=0;j<strlen(tpl);j++) {
                if (tpl[j]=='i') {
                    memcpy(out.data[i] + k, numbuf, (size_t)numlen);
                    k += numlen;
                } else {
                    out.data[i][k++] = tpl[j];
                }
            }
            out.data[i][k] = '\0';
        }
    return out;
}
```
