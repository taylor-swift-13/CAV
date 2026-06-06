# P093 Encode

## Problem (HumanEval 93)

Write a function that takes a message, && encodes in such a
way that it swaps case of all letters, replaces all vowels in
the message with the letter that appears 2 places ahead of that
vowel in the english alphabet.
Assume only letters.

Examples:
>>> p093_encode('test")
"TGST"
>>> p093_encode("This is a message")
'tHKS KS C MGSSCGG"

## Reference Implementation

```c
/*
Write a function that takes a message, && encodes in such a
way that it swaps case of all letters, replaces all vowels in
the message with the letter that appears 2 places ahead of that
vowel in the english alphabet.
Assume only letters.

Examples:
>>> p093_encode('test")
"TGST"
>>> p093_encode("This is a message")
'tHKS KS C MGSSCGG"
*/

char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *p093_encode(char *message)

{
    int n = strlen(message);
    char *out = malloc_char_array(n + 1);
    int i;

    for (i = 0; i < n; i++) {
        int w = message[i];
        if (w >= 97 && w <= 122) {
            w = w - 32;
        } else if (w >= 65 && w <= 90) {
            w = w + 32;
        }
        if (w == 65 || w == 69 || w == 73 || w == 79 || w == 85 ||
            w == 97 || w == 101 || w == 105 || w == 111 || w == 117) {
            w = w + 2;
        }
        out[i] = w;
    }
    out[n] = 0;
    return out;
}
```
