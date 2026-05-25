# aug_string_count_index_004

## Problem

Return the number of `e` characters in `s`.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `string_count_char`
- Variant kind: `fixed-character-count-index-scan`
- Constants: `{"char": "e", "i": 4, "implementation_strategy": "index-scan"}`

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

```java
class AugStringCountIndex004 {
    public static int aug_string_count_index_004(String s) {
        int count = 0;
        for (int i = 0; i < s.length(); i++) if (s.charAt(i) == 'e') count++;
        return count;
    }
}
```
