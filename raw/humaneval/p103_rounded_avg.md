# P103 Rounded avg

## Problem (HumanEval 103)

You are given two positive integers n && m, && your task is to compute the
average of the integers from n through m (including n && m).
Round the answer to the nearest integer(smaller one) && convert that to binary.
If n is greater than m, return "-1".
Example:
p103_rounded_avg(1, 5) => "11"
p103_rounded_avg(7, 5) => "-1"
p103_rounded_avg(10, 20) => "1111"
p103_rounded_avg(20, 33) => "11010"

## Reference Implementation

```c
/*
You are given two positive integers n && m, && your task is to compute the
average of the integers from n through m (including n && m).
Round the answer to the nearest integer(smaller one) && convert that to binary.
If n is greater than m, return "-1".
Example:
p103_rounded_avg(1, 5) => "11"
p103_rounded_avg(7, 5) => "-1"
p103_rounded_avg(10, 20) => "1111"
p103_rounded_avg(20, 33) => "11010"
*/

char *malloc_char_array(int n)

;

char* p103_rounded_avg(int n, int m)

{
    if (n > m) {
        char *out_neg = malloc_char_array(3);
        out_neg[0] = 45;
        out_neg[1] = 49;
        out_neg[2] = 0;
        return out_neg;
    } else {
        int num = (n + m) / 2;
        int orig = num;
        int digits = 0;
        int t = num;
        int total = 0;
        int i = 0;
        char *out = 0;

        while (t > 0) {
            digits = digits + 1;
            t = t / 2;
        }

        total = digits;
        out = malloc_char_array(total + 1);

        for (i = 0; i <= total; i++) {
            out[i] = 0;
        }


        while (num > 0) {
            digits = digits - 1;

            out[digits] = 48 + (num % 2);
            num = num / 2;
        }
        return out;
    }
}
```
