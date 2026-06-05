# String Sequence 15

## Problem (HumanEval 15)

Return a string containing space-delimited numbers starting from 0 upto n inclusive.
>>> string_sequence_15(0)
"0"
>>> string_sequence_15(5)
"0 1 2 3 4 5"

## Reference Implementation

```c
char* string_sequence_15(int n){
    int total = 2;
    char tmp[32];
    char* out;
    int k = 0;
    for (int i=1;i<=n;i++) {
        sprintf(tmp, "%d", i);
        total += 1 + (int)strlen(tmp);
    }
    out = (char*)malloc((size_t)total);
    if (out == NULL) return NULL;
    out[k++]='0';
    for (int i=1;i<=n;i++) {
        int len;
        out[k++]=' ';
        sprintf(tmp, "%d", i);
        len = (int)strlen(tmp);
        memcpy(out + k, tmp, (size_t)len);
        k += len;
    }
    out[k]='\0';
    return out;
}
```
