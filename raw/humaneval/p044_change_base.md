# P044 Change base

## Problem (HumanEval 44)

Change numerical base of input number x to base.
return string representation after the conversion.
base numbers are less than 10.
>>> p044_change_base(8, 3)
"22"
>>> p044_change_base(8, 2)
"1000"
>>> p044_change_base(7, 2)
"111"

## Reference Implementation

```c
/*
Change numerical base of input number x to base.
return string representation after the conversion.
base numbers are less than 10.
>>> p044_change_base(8, 3)
"22"
>>> p044_change_base(8, 2)
"1000"
>>> p044_change_base(7, 2)
"111"
*/

char *malloc_char_array(int n)

;

char* p044_change_base(int x, int base)

{
    if (x == 0) {
        char *out0 = malloc_char_array(2);
        out0[0] = 48;
        out0[1] = 0;
        return out0;
    } else {
        int digits = 0;
        int t = x;
        int total = 0;
        char *out = 0;
        int i = 0;

        while (t > 0) {
            digits = digits + 1;
            t = t / base;
        }

        total = digits;
        out = malloc_char_array(total + 1);

        for (i = 0; i <= total; i++) {
            out[i] = 0;
        }


        while (x > 0) {
            digits = digits - 1;

            out[digits] = 48 + (x % base);
            x = x / base;
        }
        return out;
    }
}
```
