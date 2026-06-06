# P086 Anti shuffle

## Problem (HumanEval 86)

Write a function that takes a string && returns an ordered version of it.
Ordered version of string, is a string where all words (separated by space)
are replaced by a new word where all the characters arranged in
ascending order based on ascii value.
Note: You should keep the order of words && blank spaces in the sentence.

For example:
p086_anti_shuffle("Hi") returns "Hi"
p086_anti_shuffle("hello") returns "ehllo"
p086_anti_shuffle("Hello World!!!") returns "Hello !!!Wdlor"

## Reference Implementation

```c
/*
Write a function that takes a string && returns an ordered version of it.
Ordered version of string, is a string where all words (separated by space)
are replaced by a new word where all the characters arranged in
ascending order based on ascii value.
Note: You should keep the order of words && blank spaces in the sentence.

For example:
p086_anti_shuffle("Hi") returns "Hi"
p086_anti_shuffle("hello") returns "ehllo"
p086_anti_shuffle("Hello World!!!") returns "Hello !!!Wdlor"
*/

int strlen(char *s)

;

char *malloc_char_array(int n)

;

void free_char_array(char *p, int init_size, int size)

;

void sort_char_array(char *p, int n)

;

void copy_char_array(char *dst, int off, char *src, int len, int cap)

;

char* p086_anti_shuffle(char *s)

{
    int n = strlen(s);
    int cap = n + 1;
    char *out = malloc_char_array(cap);
    char *cur = malloc_char_array(cap);
    int out_len = 0;
    int cur_len = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (s[i] != 32) {
            cur[cur_len] = s[i];
            cur_len = cur_len + 1;
        } else {
            sort_char_array(cur, cur_len);
            copy_char_array(out, out_len, cur, cur_len, cap);
            out_len = out_len + cur_len;
            cur_len = 0;
            out[out_len] = 32;
            out_len = out_len + 1;
        }
    }

    sort_char_array(cur, cur_len);
    copy_char_array(out, out_len, cur, cur_len, cap);
    out_len = out_len + cur_len;
    free_char_array(cur, cur_len, cap);
    cur_len = 0;

    out[out_len] = 0;

    return out;
}
```
