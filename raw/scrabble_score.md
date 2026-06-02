# scrabble_score

## Problem

Return the Scrabble score of an ASCII word. Letter case is ignored.

## Requirements

- Implement exactly the named function shown in the reference implementation.
- Use only the language standard library.
- The function must be deterministic and must not read stdin or write stdout.
- Inputs satisfy the stated problem preconditions; behavior outside those preconditions is intentionally unspecified.

## Source

- Source: Exercism practice exercise `scrabble-score`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/scrabble-score
- License note: prompt rewrite and implementations are local; upstream inspiration is Exercism MIT licensed.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int scrabble_score(const char *word) {
    int score = 0;
    for (int i = 0; word[i] != '\0'; i++) {
        char c = word[i];
        if (c >= 'a' && c <= 'z') c = (char)(c - 'a' + 'A');
        if (c=='A'||c=='E'||c=='I'||c=='O'||c=='U'||c=='L'||c=='N'||c=='R'||c=='S'||c=='T') score += 1;
        else if (c=='D'||c=='G') score += 2;
        else if (c=='B'||c=='C'||c=='M'||c=='P') score += 3;
        else if (c=='F'||c=='H'||c=='V'||c=='W'||c=='Y') score += 4;
        else if (c=='K') score += 5;
        else if (c=='J'||c=='X') score += 8;
        else if (c=='Q'||c=='Z') score += 10;
    }
    return score;
}
```
