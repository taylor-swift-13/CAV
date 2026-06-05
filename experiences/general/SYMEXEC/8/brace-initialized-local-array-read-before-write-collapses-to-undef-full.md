# Local brace-initialized arrays that are read before write at arbitrary indices collapse to `IntArray::undef_full`

Symptom:

- the C code allocates a fixed local array with a concrete brace initializer, for example `int seen[26] = {0};`;
- later code reads `seen[k]` before writing `seen[k]`, where `k` is data-dependent and can range over the whole array;
- fresh `symexec` may succeed only after pushing the loop entry into a manual witness, but the first surviving VC then has the shape:

```coq
IntArray.undef_full &("seen") 26
|-- EX ls, all_zero ls && IntArray.full &("seen") 26 ls
```

- repeated proof retries, post-initializer `Assert` variants, and `Search` in the loaded environment never produce a converse from undefined ownership to existential concrete contents.

Typical executable shape:

```c
int seen[26] = {0};

...
int k = c - 97;
if (seen[k]) {
    return 0;
}
seen[k] = 1;
```

Cause:

- in the current QCP frontend/library model, the brace initializer can be erased before the manual VC, leaving only `IntArray.undef_full(seen, N)`;
- for arbitrary-index read-before-write code, weaker contiguous patterns such as `IntArray::seg_shape(...) * IntArray::undef_seg(...)` do not fit honestly, because the next read may target any slot, not just an initialized prefix/suffix;
- if the environment also lacks a base converse like `x # Int |->_ |-- EX v, x # Int |-> v`, no workspace-local proof lemma can reconstruct the needed concrete array contents.

Rule:

1. Confirm the live post-`pre_process` VC really starts from `IntArray.undef_full` and asks for a concrete `IntArray.full`.
2. If the code reads arbitrary indices before first write, do not keep retrying loop invariants, post-initializer assertions, or manual helper lemmas inside the same verify workspace.
3. Treat this as a modeling boundary and escalate immediately:
   - either strengthen the frontend/library so the brace initializer survives as concrete contents;
   - or rewrite the executable implementation in Contract/source stage to an initialization/storage shape the verifier already models precisely.

What not to do:

- do not fake the missing contents with `assume`, `Axiom`, or `Admitted`;
- do not pretend a contiguous initialized segment invariant covers an access pattern that can read any array slot;
- do not keep burning retries on `proof_manual.v` once the single-cell / array-level converse has been checked and is absent.

Scope:

- `problem_kind = compare`
- `data = string`
- `pattern = single_loop`
- more generally, any fixed local bitmap / table initialized by brace syntax and then probed at arbitrary data-dependent indices before those indices are guaranteed to have been written
