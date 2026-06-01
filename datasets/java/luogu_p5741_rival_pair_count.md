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

```java
class LuoguP5741RivalPairCount {
    public static int luogu_p5741_rival_pair_count(String students) {
        String[] rows = students.split(";"); int n = rows.length; int[][] s = new int[n][3];
        for (int i = 0; i < n; i++) { String[] parts = rows[i].substring(rows[i].indexOf(':') + 1).split(","); for (int k = 0; k < 3; k++) s[i][k] = Integer.parseInt(parts[k]); }
        int ans = 0;
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) { boolean ok = true; int suma = 0, sumb = 0; for (int k = 0; k < 3; k++) { if (Math.abs(s[a][k] - s[b][k]) > 5) ok = false; suma += s[a][k]; sumb += s[b][k]; } if (ok && Math.abs(suma - sumb) <= 10) ans++; }
        return ans;
    }
}
```
