# Is Happy 80

## Problem (HumanEval 80)

You are given a string s.
Your task is to check if the string is happy || !.
A string is happy if its length is at least 3 && every 3 consecutive letters are distinct
For example:
is_happy_80("a") => false
is_happy_80("aa") => false
is_happy_80("abcd") => true
is_happy_80("aabb") => false
is_happy_80("adb") => true
is_happy_80("xyy") => false

## Reference Implementation

```c
bool is_happy_80(const char* s){
    size_t n = strlen(s);
    if (n<3) return false;
    for (size_t i=2;i<n;i++)
    if (s[i]==s[i-1] || s[i]==s[i-2]) return false;
    return true;
}
```
