# Lean scratch

Claude-generated Lean version of the core of λFS from Arntzenius & Willsey,
*Finite Functional Programming* (`finite-functional-programming.pdf`). I
(Michael) haven't checked these definitions fully yet, so take with a grain of
salt. There is no "core theorem"; the main result is the semantics itself. So
there may well be gaps between this mechanization and the paper, and no
mechanical way to check they agree besides reading the definitions, which I
haven't yet done to my own satisfaction.

Remainder of this file written by Claude.

Lean 4 (v4.34.0, via elan), no Mathlib.

Build with `lake build`; the `#guard_msgs` checks in `FFP/Examples.lean`
run as part of the build.

## Scope

Formalised: figures 1–6 — the pointed sets and their constructions, the
typing rules, the semantics of types and contexts, and the denotational
semantics of expressions and terms, as a runnable Lean function checked
against the paper's own examples. Because the semantics must produce point
preserving maps and finitely supported ones, and must consume those
properties of subterms to establish its own, defining it amounts to proving
the semantic finite support and point preservation that §7 lists as not yet
done. Not formalised: everything else §7 raises as future work — recursion,
interleaved Δ/Ω contexts, free grounding order, destructuring `&` pairs, and
finite-map patterns — together with all metatheory (weakening, substitution,
soundness or adequacy of the semantics), for which the paper gives no proofs
to follow. There is also no concrete syntax: terms are written directly as
typing derivations, against primitives supplied as semantic values rather
than as constants of the language.

## Entry points

- **fig. 1**, pointed sets and their constructions —
  `Pointed.lean`: `PSet`, `PMap`, `FinMap`; and `PSet.amp`, `tensor`,
  `lolli`, `fmap`, `maybe`, `nat`, `bool`.

- **figs. 2 and 4**, syntax and typing rules —
  `Syntax.lean`: `Expr` and `Term`, one constructor per rule. Intrinsically
  typed, so the two figures coincide: a `Term Γ Δ Ω P` *is* a derivation of
  `Γ / Δ / Ω ⊢ t : P`.

- **§5**, splitting and grounding of contexts —
  `Syntax.lean`: `Cover` for `Δ₁ ∪ Δ₂`, `Merge` for `Ω₁, Ω₂`, and `Ins` for
  `⇒e`'s insertion. Explicit here because the paper treats contexts as sets.

- **fig. 3**, sugar and primitives —
  `Sugar.lean`: `Term.true`, `false`, `and`, `let_`, `when`.
  `Prims.lean`: `Prim.or`, `exists`, `sum`, `plus`, `times`, `eq`.

- **fig. 5**, semantics of types and contexts —
  `Syntax.lean`: `Ty.sem`, `PTy.sem`, `Env`, `PEnv`.
  `Semantics.lean`: `PSet.smashCtx`, the n-ary smash product `⟦Δ⟧`.

- **fig. 6**, semantics of expressions and terms —
  `Semantics.lean`: `Expr.sem` and `Term.sem`. The set comprehensions each
  equation is built from are the combinators in `Combinators.lean`.

- **p. 14**, the typing of the semantics —
  `Semantics.lean`: `Term.semP`, packaging `Term.sem` as the point
  preserving map `⟦Γ⟧ → ⟦Δ⟧ ⊸ ⟦Ω⟧ ⇒ ⟦P⟧`.

- **§3**, example programs —
  `Examples.lean`: `costars`, `hitchcockAlone`, `filmCount`, `intersect`
  and `union`, evaluated against a small `stars` table.

Some of these exist for fidelity to the paper rather than because anything
calls them, and should not be mistaken for dead code: `Term.semP` (and the
`PSet.smashCtx` it needs) is the statement that gives `TermSem.pres` its
purpose, and `Prim.plus`, `Prim.times` and `Term.false` complete figure 3
though no example uses them.

## Representation choices

Finitely supported maps are functions carrying a list that bounds their
support; point preserving maps are functions carrying a proof that they send
`nil` to `nil`. Pointed sets are carriers with an `IsNil` predicate rather
than quotient types. See `why_classical.md` for how the support property is
phrased and why that phrasing is what keeps the development free of
`Classical.choice`.

## Separate note: two definitions of finitely supported map

`FinSupp/` is standalone (its own lake library, nothing shared with `FFP`):
`Defs.lean` defines a pointed set strictly — one distinguished element, so
nil-ness is just equality — and two finitely supported map types, `FinMapProp`
(carrying a proof that the support is finite) and `FinMapWit` (carrying a list
witness, quotiented so all witnesses are equal). `Convert.lean` relates them:
`Wit → Prop` is constructive; the reverse is classical, and the two are then
isomorphic. Constructively the reverse fails for two reasons, each identified
exactly — the phrasing of finiteness is equivalent to excluded middle (a
disproof), and escaping the `Prop` is equivalent to subsingleton choice
(unprovable without `Classical.choice`, unrefutable with it). Over `Nat` keys
`FinMapWit` computes its support; `FinMapProp`'s version is `noncomputable`.
`Examples.lean` has a worked example and the axiom audit.
