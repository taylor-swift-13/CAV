# 26-bucket letter-histogram contracts must restrict every scanned byte to the indexed alphabet (2026-06-05)

Symptom:

- the implementation normalizes each scanned character and then updates a fixed-size frequency table with an index such as `base[ch - 97]++` or `cur[ch - 97]++`;
- the natural-language task sounds like plain string processing, so it is tempting to specify only tokenization, case-folding, and the final anagram/counting semantics;
- but any non-letter byte would make the executable C compute an out-of-range array index before the high-level spec gets a chance to reject it.

Cause:

- for this implementation shape, safety depends on a **semantic character-domain invariant**, not just on NUL termination or separator structure;
- if the contract allows punctuation, digits, empty tokens, or arbitrary bytes, the C code can perform `ch - 'a'` outside `0..25`, so the spec becomes unsound even if the mathematical counting relation is correct.

Rule:

- define the precondition around the executable indexing domain first;
- require every subject byte and every candidate-word byte that reaches the histogram loop to be ASCII alphabetic;
- if the parser uses separators such as `';'`, separate the stream grammar from the per-word character domain: separators may appear only at token boundaries, and each token body must satisfy the alphabetic predicate;
- keep the postcondition focused on the semantic result and unchanged read-only strings.

Minimal shape:

```c
/*@ Extern Coq (task_pre : list Z -> list Z -> Prop) */
/*@ Extern Coq (task_spec : list Z -> list Z -> Z) */

/*@ Require
      0 <= ns && 0 <= nc &&
      Zlength(ls) == ns &&
      Zlength(lc) == nc &&
      (forall (i: Z), (0 <= i && i < ns) => ls[i] != 0) &&
      (forall (i: Z), (0 <= i && i < nc) => lc[i] != 0) &&
      task_pre(ls, lc) &&
      CharArray::full((char *)subject, ns + 1, app(ls, cons(0, nil))) *
      CharArray::full((char *)candidates, nc + 1, app(lc, cons(0, nil)))
    Ensure
      __return == task_spec(ls, lc) &&
      CharArray::full((char *)subject, ns + 1, app(ls, cons(0, nil))) *
      CharArray::full((char *)candidates, nc + 1, app(lc, cons(0, nil)))
*/
```

Here `task_pre` should encode both:

- the candidate-stream grammar;
- the fact that every character later used as `lower_ascii(ch) - 97` is an ASCII letter.

Scope:

- `problem_kind = count`
- `data = string`
- `pattern = nested_loop`
- especially anagram / frequency-table tasks that compare lowercase histograms over a fixed 26-letter alphabet
