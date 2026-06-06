# P118 Get closest vowel

## Problem (HumanEval 118)

You are given a word. Your task is to find the closest vowel that stands between
two consonants from the right side of the word (case sensitive).

Vowels in the beginning && ending doesn't count. Return empty string if you didn't
find any vowel met the above condition.

You may assume that the given string contains English letter only.

Example:
p118_get_closest_vowel("yogurt") ==> "u"
p118_get_closest_vowel("FULL") ==> "U"
p118_get_closest_vowel("quick") ==> ""
p118_get_closest_vowel("ab") ==> ""

## Reference Implementation

```c
/*
You are given a word. Your task is to find the closest vowel that stands between
two consonants from the right side of the word (case sensitive).

Vowels in the beginning && ending doesn't count. Return empty string if you didn't
find any vowel met the above condition.

You may assume that the given string contains English letter only.

Example:
p118_get_closest_vowel("yogurt") ==> "u"
p118_get_closest_vowel("FULL") ==> "U"
p118_get_closest_vowel("quick") ==> ""
p118_get_closest_vowel("ab") ==> ""
*/

char *malloc_char_array(int n)

;

int strlen(char *s)

;

int is_vowel_code(int ch)

{
    if (ch == 65) return 1;
    if (ch == 69) return 1;
    if (ch == 73) return 1;
    if (ch == 79) return 1;
    if (ch == 85) return 1;
    if (ch == 97) return 1;
    if (ch == 101) return 1;
    if (ch == 105) return 1;
    if (ch == 111) return 1;
    if (ch == 117) return 1;
    return 0;
}

char *p118_get_closest_vowel(char *word)

{
    int i;
    int cur;
    int right;
    int left;
    int cur_vowel;
    int right_vowel;
    int left_vowel;
    int n = strlen(word);
    cur = 0;
    right = 0;
    left = 0;
    cur_vowel = 0;
    right_vowel = 0;
    left_vowel = 0;

    if (n < 3) {
        char *out = malloc_char_array(1);
        out[0] = 0;
        return out;
    }

    i = n - 2;

    while (i >= 1) {
        cur = word[i];
        right = word[i + 1];
        left = word[i - 1];
        cur_vowel = is_vowel_code(cur);
        if (cur_vowel == 1) {
            right_vowel = is_vowel_code(right);
            if (right_vowel == 0) {
                left_vowel = is_vowel_code(left);
                if (left_vowel == 0) {

                    char *out = malloc_char_array(2);
                    out[0] = cur;
                    out[1] = 0;
                    return out;
                }
            }
        }

        i -= 1;
    }

    char *out = malloc_char_array(1);
    out[0] = 0;
    return out;
}
```
