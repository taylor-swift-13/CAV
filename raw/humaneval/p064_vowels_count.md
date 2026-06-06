# P064 Vowels count

## Problem (HumanEval 64)

Write a function p064_vowels_count which takes a string representing a word as input && returns the number of vowels in the string. Vowels in this case are 'a', 'e', 'i', 'o', 'u'.
Here, 'y' is also a vowel, but only when it is at the end of the given word.
Example:
>>> p064_vowels_count("abcde")
2
>>> p064_vowels_count("ACEDY")
3

## Reference Implementation

```c
/*
Write a function p064_vowels_count which takes a string representing a word as input && returns the number of vowels in the string. Vowels in this case are 'a', 'e', 'i', 'o', 'u'.
Here, 'y' is also a vowel, but only when it is at the end of the given word.
Example:
>>> p064_vowels_count("abcde")
2
>>> p064_vowels_count("ACEDY")
3
*/

int strlen(char *s)

;

int p064_vowels_count(char *s)

{
    int n = strlen(s);
    int count = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (s[i] == 97 || s[i] == 101 || s[i] == 105 ||
            s[i] == 111 || s[i] == 117 ||
            s[i] == 65 || s[i] == 69 || s[i] == 73 ||
            s[i] == 79 || s[i] == 85) {
            count = count + 1;
        }
    }
    if (n > 0 && (s[n - 1] == 121 || s[n - 1] == 89)) {
        count = count + 1;
    }
    return count;
}
```
