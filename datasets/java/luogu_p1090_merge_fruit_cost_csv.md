# Luogu P1090 Merge Fruit Cost CSV

## Problem

Return the minimum total cost of repeatedly merging the two smallest piles.

## Requirements

- `piles` is a nonempty comma-separated list of positive integers.
- This is the Huffman-style greedy objective from Luogu P1090.

## Source

- Source: Luogu problem `P1090`.
- URL: https://www.luogu.com.cn/problem/P1090
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP1090MergeFruitCostCsv {
    public static int luogu_p1090_merge_fruit_cost_csv(String piles) {
        java.util.PriorityQueue<Integer> pq = new java.util.PriorityQueue<Integer>(); for (String p : piles.split(",")) pq.add(Integer.parseInt(p)); int cost = 0; while (pq.size() > 1) { int merged = pq.poll() + pq.poll(); cost += merged; pq.add(merged); } return cost;
    }
}
```
