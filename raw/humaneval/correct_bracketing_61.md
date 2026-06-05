# Correct Bracketing 61

## Problem (HumanEval 61)

brackets is a string of '(' && ')'.
return true if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing_61("(")
false
>>> correct_bracketing_61("()")
true
>>> correct_bracketing_61("(()())")
true
>>> correct_bracketing_61(")(()")
false

## Reference Implementation

```c
bool correct_bracketing_61(const char* brackets){
    int level=0;
    for (size_t i=0;i<strlen(brackets);i++)
    {
        if (brackets[i]=='(') level+=1;
        if (brackets[i]==')') level-=1;
        if (level<0) return false;
    }
    if (level!=0) return false;
    return true;
}
```
