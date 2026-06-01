# Exercism Scrabble Score

## Problem

Return the Scrabble score of an ASCII word.

## Requirements

- Letters are scored case-insensitively.
- Nonletters score zero.

## Source

- Source: Exercism problem `scrabble-score`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/scrabble-score
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExScrabbleScore {
    public static int ex_scrabble_score(String word) {
        int[] score = {1,3,3,2,1,4,2,4,1,8,5,1,3,1,1,3,10,1,1,1,1,4,4,8,4,10}; int ans = 0; for (int i = 0; i < word.length(); i++) { char ch = Character.toLowerCase(word.charAt(i)); if (ch >= 'a' && ch <= 'z') ans += score[ch - 'a']; } return ans;
    }
}
```
