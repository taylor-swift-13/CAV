# Count Distinct Characters 16

## Problem (HumanEval 16)

Given a string, find out how many distinct characters (regardless of case) does it consist of
>>> count_distinct_characters_16("xyzXYZ")
3
>>> count_distinct_characters_16("Jerry")
4

## Reference Implementation

```c
int count_distinct_characters_16(const char* str){
    bool seen[256] = {false};
    int count = 0;
    for (size_t i = 0; i < strlen(str); i++) {
        unsigned char c = (unsigned char)tolower((unsigned char)str[i]);
        if (!seen[c]) {
            seen[c] = true;
            count += 1;
        }
    }
    return count;
}
```
