# Remove Vowels 51

## Problem (HumanEval 51)

remove_vowels_51 is a function that takes string && returns string without vowels.
>>> remove_vowels_51("")
""
>>> remove_vowels_51("abcdef\nghijklm")
"bcdf\nghjklm"
>>> remove_vowels_51("abcdef")
"bcdf"
>>> remove_vowels_51("aaaaa")
""
>>> remove_vowels_51("aaBAA")
"B"
>>> remove_vowels_51("zbcd")
"zbcd"

## Reference Implementation

```c
char* remove_vowels_51(const char* text){
    const char* vowels = "AEIOUaeiou";
    size_t i;
    size_t j = 0;
    size_t n = strlen(text);
    char* out = (char*)malloc(n + 1);

    if (out == NULL) {
        return NULL;
    }

    for (i = 0; i < n; i++) {
        if (strchr(vowels, text[i]) == NULL) {
            out[j++] = text[i];
        }
    }
    out[j] = '\0';
    return out;

}
```
