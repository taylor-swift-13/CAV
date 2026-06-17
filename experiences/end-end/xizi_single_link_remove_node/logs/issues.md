# Issues

No open issues.

Notes:

- `run_verify.py` was not run.
- The contract verifies the target-present removal path. The raw C also has a target-absent no-op path; verifying that path needs an additional absence predicate or a disjunctive contract.
- A plain `xizi_sllseg(target, target, l)` is not safe to left-collapse to `l = nil`; it can describe an early cycle. Use `xizi_sll_to_target` for this removal pattern.
