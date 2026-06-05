# aug_string_count_ptr_004

## Problem

Return the number of `e` characters in `s` using a pointer-walk style C implementation.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `string_count_char`
- Variant kind: `fixed-character-count-pointer-walk`
- Constants: `{"char": "e", "i": 4, "implementation_strategy": "pointer-walk"}`

## Signature

- Return: `int`
- Params: `s:string`

## Requirements

- Implement exactly the named function.
- Use only the language standard library.
- Do not read stdin or write stdout.
- Inputs satisfy the stated encoding constraints.
- This is an augment item: it is a same-problem implementation variant or a small semantic variant of the recorded parent problem.

## Reference Implementation

```c
int aug_string_count_ptr_004(const char *s) {
    int count = 0;
    const char *p = s;
    while (*p != '\0') {
        if (*p == 'e') count++;
        p++;
    }
    return count;
}
```
