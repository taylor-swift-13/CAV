# Scanner Return Bridge Must Pin The Unread Suffix Head

Symptom: in a byte-wise scanner or state-machine loop, a branch-local `Assert` before `return` keeps the semantic summary

```c
go(stk, l2) == spec(l)
```

and records facts about the current byte `c`, but the generated return witness is still false or too weak to prove. A common shape is a mismatch/early-reject branch that only preserves `c == 41/93/125` (or another class fact) and `go(...) == spec(l)`, after which Coq can build a counterexample where `l2` does not actually start with `c`.

Cause: the control-flow fact "the current byte is `c`" does not by itself tell the proof that the unread suffix passed to the semantic interpreter also starts with `c`. If the bridge drops that head-of-suffix fact, the return VC can no longer justify one-step reduction of `go`.

Rule: when the return semantics depend on the current scanned byte being the next unread element, preserve that relation explicitly in the bridge assertion:

```c
/*@ Assert exists l1 l2 l2_tail ...,
      ...
      l2 == cons(c, l2_tail) &&
      l == app(l1, l2) &&
      go(stk, l2) == spec(l) &&
      ...
*/
```

Do this for mismatch/empty-stack early returns as well as any other branch where the proof needs to unfold `go` by one step on the current character.

Minimal pattern:

```text
loop invariant carries l == app(l1, l2) and go(stk, l2) == spec(l)
  -> branch reads current byte c
  -> return-site Assert keeps l2 == cons(c, l2_tail)
  -> return witness unfolds go on that exact head byte
```

Scope: single-pass scanners and parser-like state machines over strings/arrays, especially when branch-local returns are justified by one-step semantic reduction on the unread suffix.
