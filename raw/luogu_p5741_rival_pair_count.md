# Luogu P5741 Rival Pair Count

## Problem

Given semicolon-separated student score triples, count pairs whose three subject differences are all at most 5 and total-score difference is at most 10.

## Requirements

- Each record is `name:chinese,math,english`.
- Names are ignored for the count.
- There are at most 128 records.

## Source

- Source: Luogu problem `P5741`.
- URL: https://www.luogu.com.cn/problem/P5741
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5741_rival_pair_count(const char *students) {
    int s[128][3], n = 0, i = 0;
    while (students[i] != '\0') {
        while (students[i] != ':' && students[i] != '\0') i++;
        if (students[i] == ':') i++;
        for (int k = 0; k < 3; k++) { int v = 0; while (students[i] >= '0' && students[i] <= '9') { v = v * 10 + (students[i] - '0'); i++; } s[n][k] = v; if (students[i] == ',') i++; }
        n++; if (students[i] == ';') i++;
    }
    int ans = 0;
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) {
        int ok = 1, suma = 0, sumb = 0;
        for (int k = 0; k < 3; k++) { int d = s[a][k] - s[b][k]; if (d < 0) d = -d; if (d > 5) ok = 0; suma += s[a][k]; sumb += s[b][k]; }
        int td = suma - sumb; if (td < 0) td = -td; if (ok && td <= 10) ans++;
    }
    return ans;
}
```
