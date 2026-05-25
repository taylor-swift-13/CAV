# Lemma Experience

This file records reusable lessons for encoding helper lemmas as Java/JML
artifacts OpenJML can check — never as unchecked axioms. It does not record loop
invariants (see `INV.md`), assertion use (`ASSERTION.md`), or anti-cheating
policy (`AUDIT.md`).

常见入口 / symptom index:

- 允许的 lemma 形式 -> see 1
- lemma 的硬规则 -> see 2
- 何时引入 lemma -> see 3
- spec 里调用的方法要 pure + deterministic -> see 4
- bodyless lemma = 假设 -> see 5
- model method / model field / ghost -> see 6, 7, 8

## 1. 允许的 lemma 形式

- `pure` helper methods with full JML contracts and executable bodies.
- Small boolean predicates implemented as Java methods and specified with JML.
- Model methods only when their semantics are explicit and do not hide an
  unproved property.

## 2. lemma 硬规则

- A lemma helper must be verified by OpenJML together with the target file.
- Do not use `native`, empty bodies, or impossible preconditions to bypass proof.
- Do not move the core algorithm into a helper with a weaker specification.
- Keep helper methods deterministic and side-effect free.

## 3. 何时用 lemma

- Reusable arithmetic facts.
- Reusable array segment predicates.
- Sortedness or prefix facts used in more than one assertion or invariant.

## 4. spec 里调用的方法必须 pure 且确定 (MethodsInSpecifications.html)

Methods called from specifications must be pure (no change to Java state visible
at the start of the call) and deterministic (no randomness, clocks, environment,
or I/O). If a helper is used in `requires`/`ensures`/invariants/assertions/
quantifiers, give it a contract strong enough for callers — OpenJML reasons from
the helper's specification, not from arbitrary inlining.

## 5. bodyless lemma 是假设，不可接受 (Lemmas.html)

Prefer a proved lemma over an assumption. A model lemma with a body `{}` is
checked; the same declaration ending in `;` is assumed and is not acceptable for
this workflow. Calling a lemma in JML instantiates its pre/postcondition at
specific values — useful when a solver needs one connecting fact. A lemma body
may be a sequence of checked `assert` statements that guide the solver.

## 6. model method 用作 spec 时要 spec_pure + 显式 contract (ModelMethods.html)

Model methods are specification-only. When used in specifications they should be
`spec_pure` and carry explicit contracts. Model methods with no implementation or
insufficient contract behave like uninterpreted functions; use them only when the
needed facts come from invariants, preconditions, or postconditions.

## 7. model field 在小例子里通常没必要 (ModelFields.html)

Model fields describe abstract state connected to concrete state via
representation clauses in richer designs. They are usually unnecessary for small
algorithmic examples; prefer direct executable helpers unless an abstraction is
clearly needed.

## 8. ghost 只用来记证明相关状态，谨慎使用 (Ghost.html)

Ghost variables and `set` statements are specification-only state. Use them
sparingly to record proof-relevant values, and never to hide unproved facts.
