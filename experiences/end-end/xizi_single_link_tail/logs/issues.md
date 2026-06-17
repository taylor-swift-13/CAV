# Issues

No open issues.

Notes:

- `run_verify.py` was not run.
- The postcondition preserves the list as `xizi_sllseg(old_head,tail,l1) * tail->node_next == 0`, which is more useful for a returned tail pointer than a shape-only `xizi_sll(old_head,l)` post.
