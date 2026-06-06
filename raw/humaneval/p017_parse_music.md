# P017 Parse music

## Problem (HumanEval 17)

Input to this function is a string representing musical notes in a special ASCII format.
Your task is to parse this string && return vector of integers corresponding to how many beats does each
! last.

Here is a legend:
"o" - whole note, lasts four beats
"o|" - half note, lasts two beats
".|" - quater note, lasts one beat

>>> p017_parse_music("o o| .| o| o| .| .| .| .| o o")
{4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4}

## Reference Implementation

```c
/*
Input to this function is a string representing musical notes in a special ASCII format.
Your task is to parse this string && return vector of integers corresponding to how many beats does each
! last.

Here is a legend:
"o" - whole note, lasts four beats
"o|" - half note, lasts two beats
".|" - quater note, lasts one beat

>>> p017_parse_music("o o| .| o| o| .| .| .| .| o o")
{4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4}
*/

typedef struct {
    int *data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

int strlen(char *s)

;

IntArray *p017_parse_music(char *music_string)

{
    IntArray *out = malloc_int_array_struct();
    int n = strlen(music_string);
    out->size = 0;
    out->data = malloc_int_array(n + 1);
    int *data = out->data;
    int state = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (music_string[i] == 32) {
            if (state == 1) {
                data[out->size] = 4;
                out->size = out->size + 1;
            } else if (state == 2) {
                data[out->size] = 2;
                out->size = out->size + 1;
            } else if (state == 4) {
                data[out->size] = 1;
                out->size = out->size + 1;
            }
            state = 0;
        } else {
            if (state == 0 && music_string[i] == 111) {
                state = 1;
            } else if (state == 0 && music_string[i] == 46) {
                state = 3;
            } else if (state == 1 && music_string[i] == 124) {
                state = 2;
            } else if (state == 3 && music_string[i] == 124) {
                state = 4;
            } else {
                state = 5;
            }
        }

    }

    if (state == 1) {
        data[out->size] = 4;
        out->size = out->size + 1;
    } else if (state == 2) {
        data[out->size] = 2;
        out->size = out->size + 1;
    } else if (state == 4) {
        data[out->size] = 1;
        out->size = out->size + 1;
    }

    return out;
}
```
