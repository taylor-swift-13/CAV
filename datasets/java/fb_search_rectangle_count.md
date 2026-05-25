# fb_search_rectangle_count

## Problem

Count positive integer side pairs `(a,b)` whose rectangle diagonal fits inside a circle with the given `radius`.

## Requirements

- `1 <= radius <= 20`.
- Use inclusive loops over side lengths from `1` to `2*radius`.

## Source

- Source: FormalBenchHF base program `CountRectangles.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbSearchRectangleCount {
    public static int fb_search_rectangle_count(int radius) {
        int count = 0, limit = 2 * radius, d2 = limit * limit;
        for (int a = 1; a <= limit; a++) for (int b = 1; b <= limit; b++) if (a * a + b * b <= d2) count++;
        return count;
    }
}
```
