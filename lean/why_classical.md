# Why the λFS formalisation uses classical axioms

`#print axioms FFP.Term.sem` reports:

```
'FFP.Term.sem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the three standard axioms of Lean's `Init` — not `sorryAx`, so
nothing is assumed about λFS itself. This note says where each one enters,
whether it affects evaluation (it does not), and which uses are essential.

## Summary

| Axiom | Where it comes from | Essential? |
|---|---|---|
| `propext` | the `List` membership API and `simp`/`rw` | incidental |
| `Quot.sound` | the same — `List` is not a quotient, but its lemma proofs use `Quot` | incidental |
| `Classical.choice` | four explicit sites, listed below | two of four are essential |

Nothing here affects what the semantics computes. Every classical step
discharges a `Prop`-valued proof obligation — the `supp_ok` field of `FinMap`
or the `pres` field of `PMap`. Lean erases `Prop` at compile time, so the
support lists and denotations that `#eval` prints are produced by ordinary
computation. The `#guard_msgs` checks in `FFP/Examples.lean` run as part of
`lake build` and confirm this.

## The root cause: `supp_ok` is stated negatively

```lean
structure FinMap (A : Type) (P : PSet) where
  fn : A → P.carrier
  supp : List A
  supp_ok : ∀ a, ¬ P.IsNil (fn a) → a ∈ supp
```

`PSet.IsNil` is an arbitrary `Prop`-valued predicate — deliberately, since
`⊗` is a quotient and the semantics only ever needs to ask "is this nil?",
never to decide equality of pointed values. Because `IsNil` carries no
decidability, `supp_ok`'s hypothesis `¬ P.IsNil (fn a)` is a *negation*, and
its conclusion `a ∈ supp` is a *positive* statement needing a witness. Getting
a witness out of a negation is precisely what intuitionistic logic forbids, so
constructing finite maps repeatedly needs excluded middle.

## The four explicit sites

### 1. `FFP/Pointed.lean:96` — `FinMap.isNil_of_not_mem`

```lean
theorem FinMap.isNil_of_not_mem (f : FinMap A P) (h : a ∉ f.supp) : P.IsNil (f.fn a) :=
  Classical.byContradiction fun hn => h (f.supp_ok a hn)
```

Double negation elimination: `supp_ok` gives `¬IsNil → a ∈ supp`, and
contraposing it yields `a ∉ supp → ¬¬IsNil`, one `¬` too many.

This lemma is **dead code** — nothing in the development references it.

### 2. `FFP/Combinators.lean:43` — `FinMap.amp` (rule `&i`)

The support of `⟨t, u⟩` is `T.supp ++ U.supp`, and `IsNil` for `P & Q` is a
conjunction, so the obligation is

```
¬ (IsNil (T.fn a) ∧ IsNil (U.fn a))  →  a ∈ T.supp ++ U.supp
```

To pick which side of the append to land in, we must know which conjunct
fails; but `¬(p ∧ q) → ¬p ∨ ¬q` is exactly De Morgan's law, which is not
intuitionistically valid. Hence `Classical.em`.

### 3. `FFP/Combinators.lean:53` — `FinMap.curry` (rule `⇒i`)

The obligation is

```
¬ (∀ x, IsNil (T.fn (x, ω)))  →  ω ∈ T.supp.map Prod.snd
```

`Classical.not_forall` turns the negated universal into an existential,
producing the `x` whose pair `(x, ω)` witnesses the membership. `¬∀ → ∃¬`
is again not constructive.

### 4. `FFP/Prims.lean:95` — `FinMap.ofRel`

The same `¬∀ → ∃¬` step, for the finite relation built from a list of pairs.

## Two of these are avoidable; two are not

I tested this rather than guessing: reformulating `supp_ok` in the logically
equivalent *positive* direction,

```lean
supp_ok : ∀ a, a ∉ supp → P.IsNil (fn a)   -- "outside the list, the value is nil"
```

turns the hypothesis into the negation and the conclusion into the `Prop` we
want, which reverses the direction of inference. Under that formulation, with
the combinators rewritten accordingly:

```
'FFP.FinMap.amp'       depends on axioms: [propext]                              -- was + Classical.choice
'FFP.FinMap.curry'     depends on axioms: [propext, Quot.sound]                  -- was + Classical.choice
'FFP.FinMap.isNil_of_not_mem'  does not depend on any axioms                     -- was + Classical.choice
'FFP.FinMap.uncurry'   depends on axioms: [propext, Classical.choice, Quot.sound]
'FFP.FinMap.bind'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

So sites 1–4 above are all incidental — artifacts of how `supp_ok` was
phrased. `ofRel` goes the same way as `curry`.

But `uncurry` (rule `⇒e`) and `bind` (the left-to-right grounding shared by
`⊸e`, `⊗i`, `⊗e`, `maybe e`) then acquire an *essential* use of excluded
middle, which the negative formulation had hidden inside `supp_ok`. In
`uncurry`, the denotation at `ω'` is

```
(T.fn ω).fn x      where (x, ω) = i.extract ω'
```

and this is nil for two genuinely different reasons:

* if `ω ∉ T.supp`, then `T.fn ω` is the nil finite map, so every value is nil;
* if `ω ∈ T.supp`, then `x ∉ (T.fn ω).supp` follows from `ω' ∉ supp`, and the
  inner map's own `supp_ok` applies.

Proving the goal requires knowing *which* case holds, i.e. deciding
`ω ∈ T.supp`. That is not decidable here: `Env Ω` is a tuple of semantic
values, and λFS has a function type `A → B`, so `Env Ω` can contain functions
and has no `DecidableEq`. The case split is unavoidable.

The case split would also disappear if support lists were required to be
*exact* rather than over-approximating — but exactness is itself only
expressible given a decidable `IsNil`, which would rule out the quotient
structure of `⊗`. So the choice is real, not an accident of presentation.

## Where `propext` and `Quot.sound` come from

Neither is used deliberately. They arrive through Lean's `List` API —
`List.mem_map`, `List.mem_flatMap`, `List.mem_append`, `List.eraseDups` — and
through `simp`/`rw` calls in `FFP/Prims.lean`. Several definitions avoid them
entirely and are reported axiom-free:

```
'FFP.FinMap.comp'          does not depend on any axioms
'FFP.FinMap.single'        does not depend on any axioms
'FFP.Cover.anyNil'         does not depend on any axioms
'FFP.Merge.join_split'     does not depend on any axioms
'FFP.Ins.insert_extract'   does not depend on any axioms
'FFP.Prim.sum'             does not depend on any axioms
'FFP.Prim.plus'            does not depend on any axioms
'FFP.Prim.times'           does not depend on any axioms
```

## Decidability instances are a separate matter

`FFP/Prims.lean` and `FFP/Examples.lean` ask for `[DecidableEq A]` on the
*key* type of a finite map (`Prim.eq`, `Prim.sum`, `FinMap.ofList`,
`FinMap.toList`, …). That is not classical reasoning: it is genuine
computational content, used to deduplicate support lists and to build
singleton relations. It is required only by the primitives and the example
readers, never by the semantics in `FFP/Semantics.lean`.
