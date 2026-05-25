# fb_search_max_box_volume

## Problem

Return the largest product `l*b*h` over positive `l` and `b` with `h = s-l-b`.

## Requirements

- `1 <= s <= 100`.
- Use the loops exactly as described.

## Source

- Source: FormalBenchHF base program `MaxVolume.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbSearchMaxBoxVolume {
    public static int fb_search_max_box_volume(int s) {
        int best = 0;
        for (int l = 1; l <= s; l++) for (int b = 1; b <= s - l + 1; b++) { int h = s - l - b; int volume = l * b * h; if (volume > best) best = volume; }
        return best;
    }
}
```
