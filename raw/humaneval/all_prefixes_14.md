# All Prefixes 14

## Problem (HumanEval 14)

Return vector of all prefixes from shortest to longest of the input string
>>> all_prefixes_14("abc")
{"a", "ab", "abc"}

## Reference Implementation

```c
typedef struct {
    char** data;
    int size;
} StrArray;

StrArray all_prefixes_14(const char* str){
    StrArray out;
    int n = (int)strlen(str);
    out.size = n;
    out.data = (char**)malloc((size_t)n * sizeof(char*));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    for (int i=0;i<n;i++)
    {
        out.data[i] = (char*)malloc((size_t)i + 2);
        if (out.data[i] == NULL) return out;
        memcpy(out.data[i], str, (size_t)i + 1);
        out.data[i][i+1] = '\0';
    }
    return out;
}
```
