# Proof Reasoning

Generated obligations:

- `entail_wit_1`: initialize the invariant by unfolding non-null `xizi_sll(linklist_pre,l)` with `xizi_sll_not_zero`.
- `entail_wit_2`: move the current node into the visited prefix with `xizi_sllseg_len1` and `xizi_sllseg_sllseg`, after unfolding the non-null suffix with `xizi_sll_not_zero`.
- `return_wit_1`: at loop exit `next == 0`, use `xizi_sll_zero` to get `l2 = nil`, then expose the final tail field cell.

The proof follows the same segment-extension pattern as `AppendSingleLinkList`, but the postcondition stops at the returned tail node instead of rebuilding an appended chain.

The final audit re-ran `symexec`, restored checked proof files, compiled deps/goal/proofs/goal_check, and found no proof obligation markers.
