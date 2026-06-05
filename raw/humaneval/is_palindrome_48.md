# Is Palindrome 48

## Problem (HumanEval 48)

Checks if given string is a palindrome
>>> is_palindrome_48("")
true
>>> is_palindrome_48("aba")
true
>>> is_palindrome_48("aaaaa")
true
>>> is_palindrome_48("zbcd")
false

## Reference Implementation

```c
bool is_palindrome_48(const char* text){
    size_t i = 0;
    size_t j = strlen(text);

    if (j == 0) {
        return true;
    }

    j -= 1;
    while (i < j) {
        if (text[i] != text[j]) {
            return false;
        }
        i += 1;
        j -= 1;
    }
    return true;
}
```
