# Count Upper 98

## Problem (HumanEval 98)

Given a string s, count the number of uppercase vowels in even indices.

For example:
count_upper_98("aBCdEf") returns 1
count_upper_98("abcdefg") returns 0
count_upper_98("dBBE") returns 0

## Reference Implementation

```c
static int is_upper_vowel(char ch) {
    return ch == 'A' || ch == 'E' || ch == 'I' || ch == 'O' || ch == 'U';
}

int count_upper_98(const char* s){
    int count=0;
    size_t i;
    for (i = 0; s[i] != '\0'; i += 2) {
        if (is_upper_vowel(s[i])) {
            count += 1;
        }
    }
    return count;
}
```
