# P156 Int to mini romank

## Problem (HumanEval 156)

Given a positive integer, obtain its roman numeral equivalent as a string,
&& return it in lowercase.
Restrictions: 1 <= num <= 1000

Examples:
>>> int_to_mini_roman(19) == "xix"
>>> int_to_mini_roman(152) == "clii"
>>> int_to_mini_roman(426) == "cdxxvi"

## Reference Implementation

```c
/*
Given a positive integer, obtain its roman numeral equivalent as a string,
and return it in lowercase.
Restrictions: 1 <= num <= 1000

Examples:
>>> int_to_mini_roman(19) == "xix"
>>> int_to_mini_roman(152) == "clii"
>>> int_to_mini_roman(426) == "cdxxvi"
*/

char *malloc_char_array(int n)

;

int append_roman_digit(char *out, int pos, int one, int ten, int five, int digit)

{
    if (digit == 0) {
        return pos;
    } else if (digit == 1) {
        out[pos] = one;
        return pos + 1;
    } else if (digit == 2) {
        out[pos] = one;
        out[pos + 1] = one;
        return pos + 2;
    } else if (digit == 3) {
        out[pos] = one;
        out[pos + 1] = one;
        out[pos + 2] = one;
        return pos + 3;
    } else if (digit == 4) {
        out[pos] = one;
        out[pos + 1] = five;
        return pos + 2;
    } else if (digit == 5) {
        out[pos] = five;
        return pos + 1;
    } else if (digit == 6) {
        out[pos] = five;
        out[pos + 1] = one;
        return pos + 2;
    } else if (digit == 7) {
        out[pos] = five;
        out[pos + 1] = one;
        out[pos + 2] = one;
        return pos + 3;
    } else if (digit == 8) {
        out[pos] = five;
        out[pos + 1] = one;
        out[pos + 2] = one;
        out[pos + 3] = one;
        return pos + 4;
    } else {
        out[pos] = one;
        out[pos + 1] = ten;
        return pos + 2;
    }
}

int append_roman_thousand(char *out, int number)

{
    if (number == 1000) {
        out[0] = 109;
        return 1;
    } else {
        return 0;
    }
}

char* p156_int_to_mini_romank(int number)

{
    int original = number;
    int k = 0;
    int h = 0;
    int t = 0;
    int o = 0;
    char *out = malloc_char_array(64);

    k = append_roman_thousand(out, number) ;

    h = (number / 100) % 10;
    k = append_roman_digit(out, k, 99, 109, 100, h)
        ;

    t = (number / 10) % 10;
    k = append_roman_digit(out, k, 120, 99, 108, t)
        ;

    o = number % 10;
    k = append_roman_digit(out, k, 105, 120, 118, o)
        ;

    out[k] = 0;
    return out;
}
```
