# Issues

Resolved:

- Using `*` between `xizi_sll(...)` and a field assertion in the function contract caused a QCP type-unification parse error. The field assertion must be combined in the same style as existing QCP field contracts, using `&&`.
- Manual `which implies` assertions for unfolding `xizi_sll` conflicted with enabled strategy rules. Removing them let strategy-driven symbolic execution generate stable VCs.
- The initial invariant needed `xizi_sllseg(p,p,nil)`. This required a local strategy rule plus matching Coq strategy proof.
- The first return VC lost the parameter roots until the invariant explicitly retained `linklist == linklist@pre` and `linklist_node == linklist_node@pre`.

Boundary:

- This case proves shape append over `xizi_sll(linklist, l)`, where `linklist` is the chain root/head node. It does not claim payload semantics because XiZi `SysSingleLinklistType` has no payload field.
