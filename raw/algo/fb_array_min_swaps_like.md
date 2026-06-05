# fb_array_min_swaps_like

## Problem

Run the two-pointer FormalBench scan and return how many equal aligned pairs it counts.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `FindMinSwaps.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_array_min_swaps_like(int arr[], int n) {
    int count = 0, i = 0, j = 1;
    while (i < n && j < n) {
        if (arr[i] == arr[j]) { i++; j++; count++; }
        else if (arr[i] > arr[j]) i++;
        else j++;
    }
    return count;
}
```
