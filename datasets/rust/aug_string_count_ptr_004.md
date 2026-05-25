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

```rust
pub fn aug_string_count_ptr_004(s: &str) -> i32 {
    let bytes = s.as_bytes();
    let mut count = 0;
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'e' { count += 1; }
        i += 1;
    }
    count
}
```
