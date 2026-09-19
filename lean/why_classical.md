# Axioms used by the λFS formalisation

`#print axioms FFP.Term.sem` reports:

```
'FFP.Term.sem' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, and **no `Classical.choice`**. The semantics of λFS is
constructive: not merely computable with proofs erased, but built without
excluded middle anywhere. This note records how, since the route there was
not obvious and two plausible formulations of finite support fail.

## Summary

| Axiom | Where it comes from | Essential? |
|---|---|---|
| `propext` | the `List` membership API and `simp`/`rw` | incidental |
| `Quot.sound` | the same — `List` is not a quotient, but its lemma proofs use `Quot` | incidental |
| `Classical.choice` | nowhere | — |

`propext` and `Quot.sound` are not used deliberately. They arrive through
`List.mem_map`, `List.mem_flatMap`, `List.mem_append`, `List.eraseDups` and
`simp`/`rw` in `FFP/Prims.lean`. Several declarations avoid even those:

```
'FFP.FinMap.comp'              does not depend on any axioms
'FFP.FinMap.single'            does not depend on any axioms
'FFP.Cover.anyNil'             does not depend on any axioms
'FFP.Merge.join_split'         does not depend on any axioms
'FFP.Ins.insert_extract'       does not depend on any axioms
'FFP.Prim.sum' / '.plus' / '.times'   do not depend on any axioms
```

## Everything turns on how `supp_ok` is phrased

```lean
structure FinMap (A : Type) (P : PSet) where
  fn : A → P.carrier
  supp : List A
  supp_ok : ∀ a, a ∈ supp ∨ P.IsNil (fn a)
```

`PSet.IsNil` is an arbitrary `Prop`-valued predicate — deliberately, since `⊗`
is a quotient and the semantics only ever asks "is this nil?", never decides
equality of pointed values. With no decidability to lean on, the phrasing of
`supp_ok` determines how much classical reasoning the development needs.
Three phrasings are classically equivalent:

1. `¬ IsNil (fn a) → a ∈ supp`
2. `a ∉ supp → IsNil (fn a)`
3. `a ∈ supp ∨ IsNil (fn a)` ← what we use

Constructively (3) is strictly the strongest, and it is the only one that
works. A `Prop`-valued `Or` cannot be *decided*, but it can be *eliminated*
into a `Prop` goal, so every construction that needs to know "is this key
listed, or is its value nil?" gets to ask, and the answer arrives as data.

The weaker phrasings each force `Classical.em` somewhere. Measured, with
everything else held fixed:

| combinator | phrasing (1) | phrasing (2) | phrasing (3) |
|---|---|---|---|
| `amp` (`&i`) | choice | — | — |
| `curry` (`⇒i`) | choice | — | — |
| `uncurry` (`⇒e`) | — | choice | — |
| `bind` (`⊸e`, `⊗i`, `⊗e`, `maybe e`) | — | choice | — |
| `ofRel` | choice | — | — |

Under (1) the hypothesis is a negation and the conclusion a positive
membership, so `amp` needs De Morgan and `curry`/`ofRel` need `¬∀ → ∃¬`.
Under (2) that reverses: those three become easy, but `uncurry` and `bind`
must case-split on `ω ∈ T.supp` — the value is nil for two different reasons
and they have to know which. Only (3) satisfies both ends at once.

## `curry` (rule `⇒i`) needs an argument

Under (3) the other combinators are routine: they consult `supp_ok` at the
key in hand and follow whichever disjunct comes back. `curry` is harder,
because its obligation at `ω`,

```
ω ∈ T.supp.map Prod.snd  ∨  ∀ x, IsNil (T.fn (x, ω))
```

has a second disjunct quantifying over all of `X`, while `T`'s own
disjunction speaks about one pair at a time. Reading `ω ∈ …` as something to
be *decided* makes this look impossible: it amounts to asking whether the
fibre of `T.supp` over `ω` is empty, and `Env Ω` has no `DecidableEq` — λFS
has a function type `A → B`, and nothing stops `⇒i` binding a finitely
supported variable of function type. Currying a flat table into a nested one
is a group-by on the outer column, and a group-by ordinarily needs key
equality.

But no key comparison is needed, because the membership can be *constructed*
rather than decided. `curry_aux` sweeps `T.supp` and, for each first
component `x'` it finds there, probes `T` at `(x', ω)` — substituting our own
`ω` instead of testing the listed one against it. Then:

* if any probe answers "listed", that gives `(x', ω) ∈ T.supp` and hence
  `ω ∈ T.supp.map Prod.snd` outright — the left disjunct, with a witness;
* if every probe answers "nil", the unbounded `∀ x` collapses onto that
  finite sweep. For arbitrary `x`, `T.supp_ok (x, ω)` either reports nil
  directly, or places `(x, ω)` in `T.supp` — in which case `x` is one of the
  `x'` already swept, and the sweep already showed it nil.

The quantifier is unbounded, but `supp_ok` guarantees that everything outside
the finite list is nil, so only the listed keys can witness anything. That is
what makes the finite sweep sufficient.

Both halves matter. The sweep borrows only `x'` from the list, never
comparing it to anything, so no `DecidableEq` is needed; and `supp_ok` being
a disjunction (3) is what lets each probe be *asked* at all.

## The runnable part

Since no classical axiom is used anywhere, this is no longer a question about
proof erasure — but the data/proof split is still worth recording. `supp_ok`
and `PMap.pres` are `Prop` fields, erased during compilation:

```
$ grep -c Classical .lake/build/ir/FFP/*.c
Combinators.c:0   Examples.c:0   Pointed.c:0   Prims.c:0
Semantics.c:0     Sugar.c:0      Syntax.c:0
```

The complementary check is that Lean rejects a definition whose executable
content really does use choice, so compiling at all is evidence of erasure:
`def pick (h : ∃ n : Nat, n > 3) : Nat := Classical.choose h` fails with
"failed to compile definition, consider marking it as 'noncomputable'".

`Term.sem` is a plain `def` that compiles, `#eval` runs it, and the
`#guard_msgs` checks in `FFP/Examples.lean` run as part of `lake build`.
Note that `curry_aux` is a `theorem`: the finite sweep is reasoning only, so
it costs nothing at runtime — `curry` still computes its support as
`T.supp.map Prod.snd`.

## Decidability instances are a separate matter

`FFP/Prims.lean` and `FFP/Examples.lean` ask for `[DecidableEq A]` on the
*key* type of a finite map (`Prim.eq`, `Prim.sum`, `FinMap.ofList`,
`FinMap.ofRel`, `FinMap.toList`, …). That is not classical reasoning but
genuine computational content: deduplicating support lists, building
singleton relations, deciding table membership. It is required only by the
primitives and the example readers, never by the semantics in
`FFP/Semantics.lean` — which, as above, needs no decidability at all.
