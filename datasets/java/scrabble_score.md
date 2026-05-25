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

```java
class ScrabbleScore {
    public static int scrabble_score(String word) {
        int score = 0;
        for (int i = 0; i < word.length(); i++) {
            char c = Character.toUpperCase(word.charAt(i));
            if ("AEIOULNRST".indexOf(c) >= 0) score += 1;
            else if ("DG".indexOf(c) >= 0) score += 2;
            else if ("BCMP".indexOf(c) >= 0) score += 3;
            else if ("FHVWY".indexOf(c) >= 0) score += 4;
            else if (c == 'K') score += 5;
            else if ("JX".indexOf(c) >= 0) score += 8;
            else if ("QZ".indexOf(c) >= 0) score += 10;
        }
        return score;
    }
}
```
