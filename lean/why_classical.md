# Why the λFS formalisation uses classical axioms

`#print axioms FFP.Term.sem` reports:

```
'FFP.Term.sem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the three standard axioms of Lean's `Init` — not `sorryAx`, so
nothing is assumed about λFS itself. This note says where each enters, why
none of them affect what the semantics *computes*, and why exactly one use of
`Classical.choice` remains.

## Summary

| Axiom | Where it comes from | Essential? |
|---|---|---|
| `propext` | the `List` membership API and `simp`/`rw` | incidental |
| `Quot.sound` | the same — `List` is not a quotient, but its lemma proofs use `Quot` | incidental |
| `Classical.choice` | one site: `FinMap.curry`, i.e. the rule `⇒i` | essential, short of restricting the language |

## The shape of `supp_ok`

```lean
structure FinMap (A : Type) (P : PSet) where
  fn : A → P.carrier
  supp : List A
  supp_ok : ∀ a, a ∈ supp ∨ P.IsNil (fn a)
```

`PSet.IsNil` is an arbitrary `Prop`-valued predicate — deliberately, since `⊗`
is a quotient and the semantics only ever needs to ask "is this nil?", never to
decide equality of pointed values. So `IsNil` carries no decidability, and the
phrasing of `supp_ok` decides how much classical reasoning the development
needs. Three phrasings are classically equivalent:

1. `¬ IsNil (fn a) → a ∈ supp`
2. `a ∉ supp → IsNil (fn a)`
3. `a ∈ supp ∨ IsNil (fn a)` ← what we use

Constructively (3) is strictly the strongest, and it is the right choice. A
`Prop`-valued `Or` cannot be *decided*, but it can be *eliminated* into a
`Prop` goal. Every construction that needs to know "is this key listed, or is
its value nil?" therefore gets to ask, and the answer arrives as data rather
than via excluded middle.

Both weaker phrasings force classical steps. (1) makes the hypothesis a
negation and the conclusion a positive membership, so `amp` needs De Morgan
(`¬(p ∧ q) → ¬p ∨ ¬q`) and `curry`/`ofRel` need `¬∀ → ∃¬`. (2) reverses that,
fixing those three but pushing an essential `Classical.em` into `uncurry` and
`bind` instead. Measured, with everything else held fixed:

| combinator | phrasing (1) | phrasing (2) | phrasing (3) |
|---|---|---|---|
| `amp` (`&i`) | choice | — | — |
| `curry` (`⇒i`) | choice | — | **choice** |
| `uncurry` (`⇒e`) | — | choice | — |
| `bind` (`⊸e`, `⊗i`, `⊗e`, `maybe e`) | — | choice | — |
| `ofRel` | choice | — | — |
| `isNil_of_not_mem` | choice | — | — |

Phrasing (3) leaves exactly one.

## The one that remains: `curry`, i.e. rule `⇒i`

Its obligation at `ω` is

```
ω ∈ T.supp.map Prod.snd  ∨  ∀ x, IsNil (T.fn (x, ω))
```

The disjunction `T` supplies speaks about **one** pair `(x, ω)` at a time.
Settling the outer disjunct means knowing whether *some* `x` has
`(x, ω) ∈ T.supp` — whether a whole fibre of `T.supp` over `ω` is empty. That
is an unbounded search over `X`, or equivalently a search of `T.supp` for an
entry whose second component equals `ω`, which needs `DecidableEq (Env Ω)`.
Both escapes were checked:

```
'FFP.FinMap.curryClassical'  depends on axioms: [propext, Classical.choice, Quot.sound]
'FFP.FinMap.curryDecidable'  depends on axioms: [propext, Quot.sound]   -- given [DecidableEq (Env Ω)]
```

`Env Ω` has no `DecidableEq` because λFS has a function type `A → B` and
nothing stops `⇒i` from binding a finitely supported variable of function
type. Getting to zero classical uses would mean restricting finite-map key
spaces to a first-order fragment — a change to the language, not to the
formalisation, and one the paper does not make.

The contrast with `uncurry` is structural and worth stating. `uncurry`'s index
`ω'` determines *both* `ω` and `x`, so it can consult `T`'s disjunction at one
exact point. `curry` projects a coordinate away and must then ask whether a
fibre is empty. Deciding emptiness of a fibre is precisely the
non-constructive step — which is apt, given that the paper's thesis is that
knowing a function's support is what buys you `exists`.

## The runnable part does not depend on any of this

`supp_ok` and `PMap.pres` are `Prop` fields. Lean erases `Prop` during
compilation, so no proof — classical or otherwise — is present in the code
that runs. Three independent confirmations:

**1. Nothing classical survives compilation.** Counting references to
`Classical` in the generated C for every module:

```
.lake/build/ir/FFP/Combinators.c:0      .lake/build/ir/FFP/Prims.c:0
.lake/build/ir/FFP/Examples.c:0         .lake/build/ir/FFP/Semantics.c:0
.lake/build/ir/FFP/Pointed.c:0          .lake/build/ir/FFP/Sugar.c:0
.lake/build/ir/FFP/Syntax.c:0
```

`FinMap.curry` compiles to ordinary list-mapping code; its `supp` is
`T.supp.map Prod.snd`, computed by `List.mapTR_loop`, and the `Classical.em`
appears nowhere.

**2. Lean would have refused otherwise.** `Classical.choice` is
`noncomputable`, and Lean rejects any definition whose *executable* content
depends on it:

```
error: failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'Classical.choose', which is 'noncomputable'
```

`FinMap.curry` and `Term.sem` are plain `def`s that compile, so their data
content is choice-free by construction — the axiom is confined to the proof.

**3. It runs.** `#eval` uses compiled code, and the `#guard_msgs` checks in
`FFP/Examples.lean` run as part of `lake build`:

```
#eval (Examples.costars.run Examples.γ₀).supp.length      -- 161
#eval FinMap.toList (Examples.stewartAndNovak.run Examples.γ₀)  -- ["Vertigo"]
```

So the split is exactly as one would want: the support lists, the finite maps
and the denotations are computed constructively, and `Classical.choice` is
used only to prove that one of those computed lists really does bound its
support.

## Where `propext` and `Quot.sound` come from

Neither is deliberate. They arrive through Lean's `List` API —
`List.mem_map`, `List.mem_flatMap`, `List.mem_append`, `List.eraseDups` — and
through `simp`/`rw` in `FFP/Prims.lean`. Several declarations avoid them and
are reported axiom-free:

```
'FFP.FinMap.comp'              does not depend on any axioms
'FFP.FinMap.single'            does not depend on any axioms
'FFP.FinMap.isNil_of_not_mem'  does not depend on any axioms
'FFP.Cover.anyNil'             does not depend on any axioms
'FFP.Merge.join_split'         does not depend on any axioms
'FFP.Ins.insert_extract'       does not depend on any axioms
'FFP.Prim.sum'                 does not depend on any axioms
'FFP.Prim.plus'                does not depend on any axioms
'FFP.Prim.times'               does not depend on any axioms
```

## Decidability instances are a separate matter

`FFP/Prims.lean` and `FFP/Examples.lean` ask for `[DecidableEq A]` on the
*key* type of a finite map (`Prim.eq`, `Prim.sum`, `FinMap.ofList`,
`FinMap.ofRel`, `FinMap.toList`, …). That is not classical reasoning but
genuine computational content: deduplicating support lists, building singleton
relations, deciding table membership. It is required only by the primitives
and the example readers, never by the semantics in `FFP/Semantics.lean`.
