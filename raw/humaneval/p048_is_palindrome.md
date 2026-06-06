# P048 Is palindrome

## Problem (HumanEval 48)

Checks if given string is a palindrome
>>> p048_is_palindrome("")
true
>>> p048_is_palindrome("aba")
true
>>> p048_is_palindrome("aaaaa")
true
>>> p048_is_palindrome("zbcd")
false

## Reference Implementation

```c
/*
Checks if given string is a palindrome
>>> p048_is_palindrome("")
true
>>> p048_is_palindrome("aba")
true
>>> p048_is_palindrome("aaaaa")
true
>>> p048_is_palindrome("zbcd")
false
*/

int strlen(char *s)

;

int p048_is_palindrome(char *text)

{
    int i = 0;
    int j = strlen(text);

    if (j == 0) {
        return 1;
    }

    j = j - 1;

    while (i < j) {
        if (text[i] != text[j]) {
            return 0;
        }
        i = i + 1;
        j = j - 1;
    }
    return 1;
}
```
