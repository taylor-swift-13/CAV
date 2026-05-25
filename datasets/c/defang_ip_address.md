# defang_ip_address

## Problem

Return the defanged form of an IPv4 address by replacing each `.` with `[.]`.

## Requirements

- Input is an IPv4 address string.
- Replace every period with the three-character sequence `[.]`.
- All other characters are copied unchanged.
- Return the transformed string.

## Source

- Source: LeetCode problem `defanging-an-ip-address`.
- URL: https://leetcode.com/problems/defanging-an-ip-address/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
char *defang_ip_address(const char *address) {
    int n = 0, dots = 0;
    while (address[n] != '\0') { if (address[n] == '.') dots++; n++; }
    char *out = (char *)malloc((unsigned long)n + (unsigned long)dots * 2 + 1);
    int pos = 0;
    for (int i = 0; i < n; i++) { if (address[i] == '.') { out[pos++] = '['; out[pos++] = '.'; out[pos++] = ']'; } else out[pos++] = address[i]; }
    out[pos] = '\0';
    return out;
}
```
