# Same Chars 54

## Problem (HumanEval 54)

Check if two words have the same characters.
>>> same_chars_54("eabcdzzzz", "dddzzzzzzzddeddabc")
true
>>> same_chars_54("abcd", "dddddddabc")
true
>>> same_chars_54("dddddddabc", "abcd")
true
>>> same_chars_54("eabcd", "dddddddabc")
false
>>> same_chars_54("abcd", "dddddddabce")
false
>>> same_chars_54("eabcdzzzz", "dddzzzzzzzddddabc")
false

## Reference Implementation

```c
bool same_chars_54(const char* s0, const char* s1){
    size_t i;
    for (i = 0; s0[i] != '\0'; i++) {
        if (strchr(s1, s0[i]) == NULL) {
            return false;
        }
    }
    for (i = 0; s1[i] != '\0'; i++) {
        if (strchr(s0, s1[i]) == NULL) {
            return false;
        }
    }
    return true;
}
```
