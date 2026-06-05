# Longest

## Problem (HumanEval 12)

Out of vector of strings, return the longest one. Return the first one in case of multiple
strings of the same length. Return None in case the input vector is empty.
>>> longest({})

>>> longest({"a", "b", "c"})
"a"
>>> longest({"a", "bb", "ccc"})
"ccc"

## Reference Implementation

```c
const char* longest(const char** strings, int strings_size){
    const char* out = "";
    int best = -1;
    for (int i=0;i<strings_size;i++)
    {
        int len = (int)strlen(strings[i]);
        if (len > best) {
            best = len;
            out = strings[i];
        }
    }
    return out;
}
```
