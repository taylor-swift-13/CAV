# P051 Remove vowels

## Problem (HumanEval 51)

p051_remove_vowels is a function that takes string && returns string without vowels.
>>> p051_remove_vowels("")
""
>>> p051_remove_vowels("abcdef\nghijklm")
"bcdf\nghjklm"
>>> p051_remove_vowels("abcdef")
"bcdf"
>>> p051_remove_vowels("aaaaa")
""
>>> p051_remove_vowels("aaBAA")
"B"
>>> p051_remove_vowels("zbcd")
"zbcd"

## Reference Implementation

```c
/*
p051_remove_vowels is a function that takes string && returns string without vowels.
>>> p051_remove_vowels("")
""
>>> p051_remove_vowels("abcdef
ghijklm")
"bcdf
ghjklm"
>>> p051_remove_vowels("abcdef")
"bcdf"
>>> p051_remove_vowels("aaaaa")
""
>>> p051_remove_vowels("aaBAA")
"B"
>>> p051_remove_vowels("zbcd")
"zbcd"
*/

char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *p051_remove_vowels(char *text)

{
    int i;
    int j = 0;
    int n = strlen(text);
    char *out = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        int c = text[i];
        if (c == 65 || c == 69 || c == 73 || c == 79 || c == 85 ||
            c == 97 || c == 101 || c == 105 || c == 111 || c == 117) {
        } else {
            out[j] = c;
            j = j + 1;
        }
    }
    out[j] = 0;
    return out;
}
```
