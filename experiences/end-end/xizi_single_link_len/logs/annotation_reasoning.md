2026-06-03 annotation round 1

Phenomenon:
The input contract already fixes the intended semantics with `xizi_single_link_wf` and `xizi_single_link_len_spec`, but the loop in [verify_20260603_193124v_xizi_single_link_len.c](/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c) has no invariant. Without an invariant, `symexec` cannot justify the repeated read `next[node]` or connect the loop counter to `xizi_single_link_len_spec`.

Location:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c`, theorem source will come from the `while (node != -1)` control point.

Repair action:
Add a loop invariant with two ghost components:
`seen : list Z` records how many links have already been traversed, and `fuel : nat` is the remaining well-founded budget from `xizi_single_link_valid_nat`.
The invariant keeps:
`length == Zlength(seen)`,
`length + Z.of_nat(fuel) == n`,
`xizi_single_link_valid_nat fuel seen node l`,
and
`length + xizi_single_link_len_nat fuel node l == xizi_single_link_len_spec(head@pre, l)`.
It also explicitly preserves `head`, `next`, and `n` as unchanged parameters and keeps `IntArray::full(next, n, l)`.

Key C/Coq fragment:
The proof-critical bridge is:
`xizi_single_link_valid_nat fuel seen node l`
combined with `node != -1`, which should expose
`0 <= node < Z.of_nat (length l)` and the recursive tail fact on `xizi_next_at node l`.

Why this change:
The loop follows a path in an array-encoded linked list. A plain arithmetic invariant like `length + remaining == spec` is too weak because it does not justify that the current `node` is in range before `next[node]` is read. Carrying the recursive validity predicate is the minimal way to retain both safety and progress from the original contract.

2026-06-03 annotation round 2

Phenomenon:
The first `symexec` run failed at `/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c:40` with `Use of undeclared identifier 'Z'` because the annotation parser rejected `Z.of_nat(fuel)`.

Location:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c`, loop invariant line containing `length + Z.of_nat(fuel) == n`.

Repair action:
Remove the parser-unsupported coercion and keep an explicit source-level bound `length <= n` instead. The remaining invariant still carries the recursive validity predicate and the suffix-length equation:
`xizi_single_link_valid_nat fuel seen node l`
and
`length + xizi_single_link_len_nat fuel node l == xizi_single_link_len_spec(head@pre, l)`.

Key error snippet:
`fatal error: Use of undeclared identifier 'Z'`

Why this change:
The front-end parser must accept the annotation before any Coq proof can start. Keeping the bound as a plain integer fact preserves the C overflow/safety intent while avoiding unsupported surface syntax.

2026-06-03 annotation round 3

Phenomenon:
The second `symexec` run still stopped at the loop head, now with `Expected C expression` after the invariant carrying `fuel : nat` and calls to `xizi_single_link_valid_nat` / `xizi_single_link_len_nat`.

Location:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c:29-38`, entire loop invariant.

Repair action:
Drop the nat-indexed imported symbols from the surface annotation and rewrite the invariant using only parser-safe Z-valued facts:
either the traversal is finished and `node == -1` with `length == xizi_single_link_len_spec(head@pre, l)`,
or the traversal is at a valid current node with
`0 <= node && node < n`,
`xizi_single_link_wf(node, l)`,
and
`length + 1 + xizi_single_link_len_spec(node, l) == xizi_single_link_len_spec(head@pre, l)`.

Key error snippet:
`fatal error: Expected C expression`

Why this change:
At this stage the bottleneck is annotation parsing, not proof strength. The rewritten invariant stays close to the recursive meaning of the spec while using only symbols that already appear in the contract surface language.

2026-06-03 annotation round 4

Phenomenon:
The third `symexec` run still failed at the loop head with `Expected C expression`, which indicates the front end still rejected the large parenthesized case split in the invariant.

Location:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c:29-41`, invariant branch `(node == -1 && ...) || (...)`.

Repair action:
Rewrite the same information as flat implication facts:
`(node == -1) => length == spec`,
`(node != -1) => 0 <= node && node < n`,
`(node != -1) => xizi_single_link_wf(node, l)`,
and
`(node != -1) => length + 1 + xizi_single_link_len_spec(node, l) == xizi_single_link_len_spec(head@pre, l)`.

Key error snippet:
`fatal error: Expected C expression`

Why this change:
The assertion guidance explicitly favors multiple single-purpose implications over one large case formula. This keeps the same semantic split while better matching the front-end grammar.

2026-06-03 annotation round 5

Phenomenon:
The fourth `symexec` run still failed with the same parser error at the loop head, so the remaining suspect is not just the disjunction shape but the use of imported Coq formulas inside the invariant surface syntax.

Location:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c`, current loop invariant.

Repair action:
Temporarily reduce the invariant to a parser-trivial core with only source-level integer facts and the unchanged array resource:
`head == head@pre`, `next == next@pre`, `n == n@pre`, `0 <= length`, `length <= n`, and `IntArray::full(next, n, l)`.

Key error snippet:
`fatal error: Expected C expression`

Why this change:
This is a controlled parser-isolation step. If the reduced invariant parses, the grammar problem is specifically with the imported Coq terms, and I can then decide whether the task is blocked at the verify boundary rather than continuing to guess unsupported annotation forms.

2026-06-03 annotation round 6

Phenomenon:
The reduced invariant still failed to parse. Comparing with the existing annotated case `annotated/verify_20260603_190108v_xizi_id_first_nonfull_byte.c`, the loop-head annotation form there is plain `Inv`, not `Inv Assert`.

Location:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c`, current `while` annotation header.

Repair action:
Switch the loop annotation header from `Inv Assert` to `Inv` to match the verified local pattern already accepted by this front end.

Key code snippet:
working local example:
`/*@ Inv
      0 <= i && i <= n &&
      ...
*/`

Why this change:
At the loop head we need the exact grammar that `symexec` accepts. Reusing the accepted local form is lower-risk than continuing to infer undocumented variants.

2026-06-03 annotation round 7

Phenomenon:
Even after switching to plain `Inv`, the loop annotation still fails before VC generation. The remaining uncertainty is whether a specific clause such as `IntArray::full(...)`, `next == next@pre`, or even the local identifier `length` is what the parser rejects.

Location:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c`, current loop invariant.

Repair action:
Reduce the invariant one step further to a single pure clause `0 <= length` as a parser-isolation test.

Why this change:
This is the shortest path to identify whether the failure is tied to the invariant body generally or to a specific formula class inside it.

2026-06-03 annotation round 8

Phenomenon:
The one-clause invariant parsed successfully. `symexec` then failed at `/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c:29:8` with `Cannot derive the precondition of Memory Read`, which is exactly the missing `next[node]` range fact.

Location:
Loop body statement `node = next[node];`.

Repair action:
Restore a semantic invariant in the accepted plain-`Inv` form. The strengthened invariant carries:
`(node == -1) => length == xizi_single_link_len_spec(head@pre, l)`,
`(node != -1) => 0 <= node && node < n`,
`(node != -1) => xizi_single_link_wf(node, l)`,
and
`(node != -1) => length + 1 + xizi_single_link_len_spec(node, l) == xizi_single_link_len_spec(head@pre, l)`,
along with unchanged parameters and `IntArray::full`.

Key error snippet:
`fatal error: Cannot derive the precondition of Memory Read`

Why this change:
The parser problem is resolved. The remaining task is now proper verification: keep enough semantic information in the invariant so the current node is provably readable and the final counter still matches the imported spec.

2026-06-03 annotation round 9

Phenomenon:
Reintroducing the semantic facts with implication syntax brought back the front-end parse error. The failure is now more likely tied to the `=>` surface form than to the imported symbols alone.

Location:
Loop invariant in `/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c`.

Repair action:
Rewrite the semantic split as a plain disjunction:
left branch for the finished state `node == -1`,
right branch for the active traversal state with node range, `xizi_single_link_wf(node, l)`, and the recursive count equation.

Why this change:
The repository already uses `||` in accepted contracts. This keeps the same two-state meaning while avoiding the implication form that appears to be rejected here.

2026-06-03 annotation round 10

Phenomenon:
The disjunctive invariant still failed to parse. Since the minimal invariant was accepted, the remaining surface-level suspects are the `@pre` equalities and the use of `head@pre` inside the loop invariant rather than the recursive spec terms themselves.

Location:
Loop invariant in `/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c`.

Repair action:
Drop the explicit `@pre` parameter equalities and rewrite the recursive equations against `head` directly, relying on the fact that `head`, `next`, and `n` are not assigned in the function body.

Why this change:
This is the last low-cost annotation variant that stays within the given contract while still trying to recover a strong enough invariant for `symexec`.

2026-06-03 annotation round 11

Phenomenon:
With the `@pre` equalities removed, the semantic invariant finally parsed, but `symexec` stopped at the loop head with:
`The number of now assertions and loop inv pre assertions does not match.`
This points to the disjunction itself creating incompatible case splits for the loop interface.

Location:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c:38:4`, loop invariant entry.

Repair action:
Replace the disjunction by flat implication-style facts while keeping the same meaning and still avoiding explicit `@pre` equalities:
`(node == -1) => ...`
and separate `(node != -1) => ...` clauses.

Key error snippet:
`The number of now assertions and loop inv pre assertions does not match`

Why this change:
The parser and imported symbols are no longer the blocker. The issue is now the loop-interface case structure, and flattening it is the narrowest fix.
