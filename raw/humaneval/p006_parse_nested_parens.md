# P006 Parse nested parens

## Problem (HumanEval 6)

Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
For each of the group, output the deepest level of nesting of parentheses.
E.g. (()()) has maximum two levels of nesting while ((())) has three.

>>> p006_parse_nested_parens("(()()) ((())) () ((())()())")
{2, 3, 1, 3}

## Reference Implementation

```c
/*
Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
For each of the group, output the deepest level of nesting of parentheses.
E.g. (()()) has maximum two levels of nesting while ((())) has three.

>>> p006_parse_nested_parens("(()()) ((())) () ((())()())")
{2, 3, 1, 3}
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

IntArray *p006_parse_nested_parens(char *paren_string)

{
    IntArray *out = malloc_int_array_struct();
    int n = strlen(paren_string);
    out->size = 0;
    out->data = malloc_int_array(n);
    int *data = out->data;
    int level = 0;
    int max_level = 0;
    int in_group = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (paren_string[i] == 32) {
            if (in_group) {
                data[out->size] = max_level;
                out->size = out->size + 1;
                level = 0;
                max_level = 0;
                in_group = 0;
            }
        } else {
            in_group = 1;
            if (paren_string[i] == 40) {
                level = level + 1;
                if (level > max_level) {
                    max_level = level;
                }
            } else {
                if (level > 0) {
                    level = level - 1;
                }
            }
        }

    }

    if (in_group) {
        data[out->size] = max_level;
        out->size = out->size + 1;
    }

    return out;
}
```
