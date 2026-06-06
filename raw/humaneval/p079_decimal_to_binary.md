# P079 Decimal to binary

## Problem (HumanEval 79)

You will be given a number in decimal form && your task is to convert it to
binary format. The function should return a string, with each character representing a binary
number. Each character in the string will be '0' || '1'.

There will be an extra couple of characters "db" at the beginning && at the end of the string.
The extra characters are there to help with the format.

Examples:
p079_decimal_to_binary(15)   // returns "db1111db"
p079_decimal_to_binary(32)   // returns "db100000db"

## Reference Implementation

```c
/*
You will be given a number in decimal form && your task is to convert it to
binary format. The function should return a string, with each character representing a binary
number. Each character in the string will be '0' || '1'.

There will be an extra couple of characters "db" at the beginning && at the end of the string.
The extra characters are there to help with the format.

Examples:
p079_decimal_to_binary(15)   // returns "db1111db"
p079_decimal_to_binary(32)   // returns "db100000db"
*/

char *malloc_char_array(int n)

;

char* p079_decimal_to_binary(int decimal)

{
    if (decimal == 0) {
        char *out_zero = malloc_char_array(6);
        out_zero[0] = 100;
        out_zero[1] = 98;
        out_zero[2] = 48;
        out_zero[3] = 100;
        out_zero[4] = 98;
        out_zero[5] = 0;
        return out_zero;
    } else {
        int orig = decimal;
        int x = decimal;
        int bits = 0;
        int total = 0;
        int i = 0;
        int num = decimal;
        char *out = 0;

        while (x > 0) {
            bits = bits + 1;
            x = x / 2;
        }

        total = bits;
        out = malloc_char_array(total + 5);

        out[0] = 100;
        out[1] = 98;
        i = 0;

        while (i < total) {
            out[i + 2] = 0;
            i = i + 1;
        }

        out[total + 4] = 0;

        out[total + 3] = 98;

        out[total + 2] = 100;

        i = total + 5;

        while (num > 0) {
            bits = bits - 1;

            out[bits + 2] = 48 + (num % 2);
            num = num / 2;
        }
        return out;
    }
}
```
