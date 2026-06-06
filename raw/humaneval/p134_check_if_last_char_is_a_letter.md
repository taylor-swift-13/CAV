# P134 Check if last char is a letter

## Problem (HumanEval 134)

Create a function that returns true if the last character
of a given string is an alphabetical character && is !
a part of a word, && false otherwise.
Note: "word" is a group of characters separated by space.

Examples:
p134_check_if_last_char_is_a_letter("apple pie") ➞ false
p134_check_if_last_char_is_a_letter("apple pi e") ➞ true
p134_check_if_last_char_is_a_letter("apple pi e ") ➞ false
p134_check_if_last_char_is_a_letter("") ➞ false

## Reference Implementation

```c
/*
Create a function that returns true if the last character
of a given string is an alphabetical character && is !
a part of a word, && false otherwise.
Note: "word" is a group of characters separated by space.

Examples:
p134_check_if_last_char_is_a_letter("apple pie") -> false
p134_check_if_last_char_is_a_letter("apple pi e") -> true
p134_check_if_last_char_is_a_letter("apple pi e ") -> false
p134_check_if_last_char_is_a_letter("") -> false
*/

int strlen(char *s)

;

int p134_check_if_last_char_is_a_letter(char *txt)

{
    int n = strlen(txt);
    if (n == 0) return 0;

    int chr = txt[n - 1];
    if (chr < 65) return 0;
    if (chr > 90 && chr < 97) return 0;
    if (chr > 122) return 0;

    if (n == 1) return 1;

    chr = txt[n - 2];
    if (chr == 32) return 1;
    return 0;
}
```
