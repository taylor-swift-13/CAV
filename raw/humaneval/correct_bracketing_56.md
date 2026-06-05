# Correct Bracketing 56

## Problem (HumanEval 56)

brackets is a string of '<' && '>'.
return true if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing_56("<")
false
>>> correct_bracketing_56("<>")
true
>>> correct_bracketing_56("<<><>>")
true
>>> correct_bracketing_56("><<>")
false

## Reference Implementation

```c
bool correct_bracketing_56(const char* brackets){
    int level=0;
    for (size_t i=0;i<strlen(brackets);i++)
    {
        if (brackets[i]=='<') level+=1;
        if (brackets[i]=='>') level-=1;
        if (level<0) return false;
    }
    if (level!=0) return false;
    return true;
}
```
