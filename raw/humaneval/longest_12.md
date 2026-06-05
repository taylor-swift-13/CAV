# Longest 12

## Problem (HumanEval 12)

Out of vector of strings, return the longest_12 one. Return the first one in case of multiple
strings of the same length. Return None in case the input vector is empty.
>>> longest_12({})

>>> longest_12({"a", "b", "c"})
"a"
>>> longest_12({"a", "bb", "ccc"})
"ccc"

## Reference Implementation

```c
const char* longest_12(const char** strings, int strings_size){
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
