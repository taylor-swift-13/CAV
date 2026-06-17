# Proof Reasoning

Proof structure:

- safety witness for `next == linklist_node` uses `xizi_sll_not_target_same_nonzero`;
- invariant initialization and preservation use `xizi_sll_not_target_not_zero`;
- loop preservation extends the visited prefix with `xizi_sllseg_len1` and `xizi_sllseg_sllseg`;
- exit uses `xizi_sll_not_target_zero` to reduce the remaining suffix to `nil`;
- return uses `xizi_sll_len1` for the final tail node and `xizi_sllseg_sll` to rebuild `xizi_sll(linklist,l)`.

No array model, no admitted proof, no `run_verify.py`.
