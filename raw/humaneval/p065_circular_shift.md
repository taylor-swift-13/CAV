# P065 Circular shift

## Problem (HumanEval 65)

Circular shift the digits of the integer x, shift the digits right by shift
&& return the result as a string.
If shift > number of digits, return digits reversed.
>>> p065_circular_shift(12, 1)
"21"
>>> p065_circular_shift(12, 2)
"12"

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

## Reference Implementation

```c
/*
Circular shift the digits of the integer x, shift the digits right by shift
&& return the result as a string.
If shift > number of digits, return digits reversed.
>>> p065_circular_shift(12, 1)
"21"
>>> p065_circular_shift(12, 2)
"12"
*/

char *malloc_char_array(int n)

;

char* p065_circular_shift(int x, int shift)

{
    char *buf = malloc_char_array(64);
    int n = 0;
    int tmp = 0;
    int i = 0;
    int fill = 0;

    if (x == 0) {
        buf[0] = 48;
        buf[1] = 0;
        n = 1;

    } else {
        tmp = x;

        while (tmp > 0) {
            n = n + 1;
            tmp = tmp / 10;
        }


        for (i = 0; i <= n; i++) {
            buf[i] = 0;
        }

        tmp = x;
        fill = n;

        while (tmp > 0) {
            fill = fill - 1;

            buf[fill] = 48 + (tmp % 10);
            tmp = tmp / 10;
        }

    }

    char *out = malloc_char_array(n + 1);

    if (n < shift) {

        for (i = 0; i < n; i++) {
            out[i] = buf[n - 1 - i];
        }
    } else {

        for (i = 0; i < n; i++) {
            int src = n - shift + i;
            if (src >= n) {
                src = src - n;
            }

            out[i] = buf[src];
        }
    }

    out[n] = 0;
    return out;
}
```
