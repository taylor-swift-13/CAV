# Is Nested 132

## Problem (HumanEval 132)

Create a function that takes a string as input which contains only square brackets.
The function should return true if && only if there is a valid subsequence of brackets
where at least one bracket in the subsequence is nested.

is_nested_132("[[]]") ➞ true
is_nested_132("[]]]]]]][[[[[]") ➞ false
is_nested_132("[][]") ➞ false
is_nested_132("[]") ➞ false
is_nested_132("[[][]]") ➞ true
is_nested_132("[[]][[") ➞ true

## Reference Implementation

```c
bool is_nested_132(const char* str){
    int count=0,maxcount=0;
    for (size_t i=0; i<strlen(str); i++)
    {
        if (str[i]=='[') count+=1;
        if (str[i]==']') count-=1;
        if (count<0) count=0;
        if (count>maxcount) maxcount=count;
        if (count<=maxcount-2) return  true;
    }
    return false;
}
```
