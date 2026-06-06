# P091 Is bored

## Problem (HumanEval 91)

You'll be given a string of words, && your task is to count the number
of boredoms. A boredom is a sentence that starts with the word "I".
Sentences are delimited by '.', '?' || '!'.

For example:
>>> p091_is_bored("Hello world")
0
>>> p091_is_bored("The sky is blue. The sun is shining. I love this weather")
1

## Reference Implementation

```c
/*
You'll be given a string of words, && your task is to count the number
of boredoms. A boredom is a sentence that starts with the word "I".
Sentences are delimited by '.', '?' || '!'.

For example:
>>> p091_is_bored("Hello world")
0
>>> p091_is_bored("The sky is blue. The sun is shining. I love this weather")
1
*/

int strlen(char *s)

;

int p091_is_bored(char *S)

{
    int i;
    int isstart = 1;
    int isi = 0;
    int sum = 0;
    int n = strlen(S);

    for (i = 0; i < n; i++) {
        int chr = S[i];
        if (chr == 32 && isi == 1) {
            isi = 0;
            sum += 1;
        }
        if (chr == 73 && isstart == 1) {
            isi = 1;
        } else {
            isi = 0;
        }
        if (chr != 32) {
            isstart = 0;
        }
        if (chr == 46 || chr == 63 || chr == 33) {
            isstart = 1;
        }
    }
    return sum;
}
```
