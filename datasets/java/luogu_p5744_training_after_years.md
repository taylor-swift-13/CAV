# Luogu P5744 Training After Years

## Problem

After `years` yearly updates, return `age + score` where age increases by 1 each year and score increases by 20 percent capped at 600.

## Requirements

- `years >= 0`.
- Use truncating integer arithmetic after each yearly score update.

## Source

- Source: Luogu problem `P5744`.
- URL: https://www.luogu.com.cn/problem/P5744
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP5744TrainingAfterYears {
    public static int luogu_p5744_training_after_years(int age, int score, int years) {
        for (int i = 0; i < years; i++) { age++; score = score * 120 / 100; if (score > 600) score = 600; }
        return age + score;
    }
}
```
