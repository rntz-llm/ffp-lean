/-
# The set comprehensions of figure 6, as finite-map combinators

Figure 6 writes each term denotation as a set comprehension of input/output
pairs `ω ↦ y`.  Each combinator below is one of those comprehensions: its `fn`
is the function `ω ↦ y`, its `supp` is a list enumerating (a superset of) the
inputs the comprehension ranges over, and `supp_ok` shows the list really
bounds the support.  The `_isNil` lemmas are what point preservation of the
semantics rests on: nil inputs produce nil outputs.

Because `FinMap.supp_ok` is a disjunction, every case analysis these proofs
need — "is this key listed, or is its value nil?" — comes from the data
itself.  Only `curry` needs more; see the note there and `why_classical.md`.
-/
import FFP.Syntax

namespace FFP
namespace FinMap

variable {P Q R : PSet}

/-- `{() ↦ y}`: the singleton map on the empty context. -/
def single (y : P.carrier) : FinMap (Env []) P where
  fn _ := y
  supp := [()]
  supp_ok a := .inl (by cases a; exact .head _)

/-- `{}`: the empty map. -/
def empty (A : Type) : FinMap A P := (PSet.fmap A P).nil

/-- `{a ↦ g a x : a ↦ x ∈ T}`, for a `g` that sends nil to nil. -/
def comp {A : Type} (T : FinMap A P) (g : A → P.carrier → Q.carrier)
    (hg : ∀ a p, P.IsNil p → Q.IsNil (g a p)) : FinMap A Q where
  fn a := g a (T.fn a)
  supp := T.supp
  supp_ok a := (T.supp_ok a).imp id (hg a _)

theorem comp_isNil {A : Type} {T : FinMap A P} {g hg} (hT : ∀ a, P.IsNil (T.fn a)) :
    ∀ a, Q.IsNil ((comp T g hg).fn a) := fun a => hg a _ (hT a)

/-- &i: `{a ↦ ⟨x, y⟩ : a ↦ x ∈ T, a ↦ y ∈ U}`. -/
def amp {A : Type} (T : FinMap A P) (U : FinMap A Q) : FinMap A (PSet.amp P Q) where
  fn a := (T.fn a, U.fn a)
  supp := T.supp ++ U.supp
  supp_ok a := match T.supp_ok a with
    | .inl h => .inl (List.mem_append.2 (.inl h))
    | .inr hp => match U.supp_ok a with
      | .inl h => .inl (List.mem_append.2 (.inr h))
      | .inr hq => .inr ⟨hp, hq⟩

/-- Auxiliary to `curry`.  Walking the list `l`, probe `T` at `(x', ω)` for
each first component `x'` drawn from `l`, keeping *our own* `ω`.  Either some
probe reports membership — which is already a witness that `ω` is in the
curried support — or every probe reports nil. -/
private theorem curry_aux {X : Type} (T : FinMap (X × Env Ω) P) (ω : Env Ω) :
    ∀ l : List (X × Env Ω),
      ω ∈ T.supp.map Prod.snd ∨ ∀ x, x ∈ l.map Prod.fst → P.IsNil (T.fn (x, ω))
  | [] => .inr fun _ hx => absurd hx (by simp)
  | (x', _) :: l => match T.supp_ok (x', ω) with
    | .inl h => .inl (List.mem_map.2 ⟨(x', ω), h, rfl⟩)
    | .inr hnil => (curry_aux T ω l).imp id fun ih x hx =>
        match List.mem_cons.1 hx with
        | .inl h => by rw [h]; exact hnil
        | .inr hx' => ih x hx'

/-- ⇒i: `{ω ↦ {x ↦ y : (ω,x) ↦ y ∈ T} : ∃ x y. (ω,x) ↦ y ∈ T}`.

Constructive, though it takes a little work.  The obligation at `ω` is
`ω ∈ T.supp.map Prod.snd ∨ ∀ x, IsNil (T.fn (x, ω))`, and the second disjunct
quantifies over the whole of `X`.  One might expect to need excluded middle to
choose a side — deciding whether the fibre of `T.supp` over `ω` is empty —
but no comparison of keys is required.

Instead, `curry_aux` sweeps `T.supp` and probes `T` at `(x', ω)` for each
first component `x'` in the list, substituting our own `ω` rather than
testing the listed one against it.  A probe that answers "listed" hands us
`(x', ω) ∈ T.supp`, hence `ω ∈ T.supp.map Prod.snd` directly.  If every probe
answers "nil", the unbounded `∀ x` collapses onto that finite sweep: for an
arbitrary `x`, `T.supp_ok (x, ω)` either gives nil outright, or puts
`(x, ω)` in `T.supp` — so `x` is one of the `x'` already swept. -/
def curry {X : Type} (T : FinMap (X × Env Ω) P) : FinMap (Env Ω) (PSet.fmap X P) where
  fn ω := ⟨fun x => T.fn (x, ω), T.supp.map Prod.fst,
           fun x => (T.supp_ok (x, ω)).imp (fun h => List.mem_map.2 ⟨(x, ω), h, rfl⟩) id⟩
  supp := T.supp.map Prod.snd
  supp_ok ω := (curry_aux T ω T.supp).imp id fun hall x =>
    (T.supp_ok (x, ω)).elim
      (fun hmem => hall x (List.mem_map.2 ⟨(x, ω), hmem, rfl⟩)) id

/-- ⇒e: `{(ω,x) ↦ y : ω ↦ f ∈ T, x ↦ y ∈ f}`, with `x` inserted into `Ω` by `i`.
Unlike `curry` this is constructive: the index `ω'` determines both `ω` and
`x`, so `T`'s own disjunction can be consulted at that one point. -/
def uncurry (i : Ins A Ω Ω') (T : FinMap (Env Ω) (PSet.fmap A.sem P)) :
    FinMap (Env Ω') P where
  fn ω' := (T.fn (i.extract ω').2).fn (i.extract ω').1
  supp := T.supp.flatMap fun ω => (T.fn ω).supp.map fun x => i.insert x ω
  supp_ok ω' := match T.supp_ok (i.extract ω').2 with
    | .inr hnil => .inr (hnil _)
    | .inl hmem => match (T.fn (i.extract ω').2).supp_ok (i.extract ω').1 with
      | .inl hx => .inl (List.mem_flatMap.2 ⟨_, hmem,
          List.mem_map.2 ⟨_, hx, i.insert_extract ω'⟩⟩)
      | .inr hnil => .inr hnil

/-- Left-to-right grounding, the shape shared by ⊸e, ⊗i, ⊗e and maybe e:
`{(ω₁,ω₂) ↦ k x y : ω₁ ↦ x ∈ T, ω₂ ↦ y ∈ U ω₁}`.  The right-hand map `U` may
depend on `ω₁` (it is `⟦u⟧ (γ, ω₁) …`, with `Ω₁` grounded).  `hk` says the
combining function `k` yields nil as soon as either input is nil, which is
what keeps the support finite. -/
def bind (m : Merge Ω₁ Ω₂ Ω) (T : FinMap (Env Ω₁) P) (U : Env Ω₁ → FinMap (Env Ω₂) Q)
    (k : P.carrier → Q.carrier → R.carrier)
    (hk : ∀ ω₁ ω₂, P.IsNil (T.fn ω₁) ∨ Q.IsNil ((U ω₁).fn ω₂) →
      R.IsNil (k (T.fn ω₁) ((U ω₁).fn ω₂))) : FinMap (Env Ω) R where
  fn ω := k (T.fn (m.split ω).1) ((U (m.split ω).1).fn (m.split ω).2)
  supp := T.supp.flatMap fun ω₁ => (U ω₁).supp.map fun ω₂ => m.join ω₁ ω₂
  supp_ok ω := match T.supp_ok (m.split ω).1 with
    | .inr hp => .inr (hk _ _ (.inl hp))
    | .inl hmem => match (U (m.split ω).1).supp_ok (m.split ω).2 with
      | .inl h₂ => .inl (List.mem_flatMap.2 ⟨_, hmem,
          List.mem_map.2 ⟨_, h₂, m.join_split ω⟩⟩)
      | .inr hq => .inr (hk _ _ (.inr hq))

theorem bind_isNil {m : Merge Ω₁ Ω₂ Ω} {T : FinMap (Env Ω₁) P}
    {U : Env Ω₁ → FinMap (Env Ω₂) Q} {k : P.carrier → Q.carrier → R.carrier} {hk}
    (h : ∀ ω, P.IsNil (T.fn (m.split ω).1) ∨
              Q.IsNil ((U (m.split ω).1).fn (m.split ω).2)) :
    ∀ ω, R.IsNil ((bind m T U k hk).fn ω) := fun ω => hk _ _ (h ω)

/-- maybe e: `{(ω₁,ω₂) ↦ y : ω₁ ↦ just x ∈ T, ω₂ ↦ y ∈ U ω₁ x}`. -/
def letJust {X : Type} (m : Merge Ω₁ Ω₂ Ω) (T : FinMap (Env Ω₁) (PSet.maybe X))
    (U : Env Ω₁ → X → FinMap (Env Ω₂) P) : FinMap (Env Ω) P :=
  bind m T (fun ω₁ => (T.fn ω₁).elim (empty _) (U ω₁)) (fun _ y => y) fun ω₁ _ h =>
    h.elim (fun hn => by rw [show T.fn ω₁ = none from hn]; exact P.nil_isNil) id

theorem letJust_isNil_left {X : Type} {m : Merge Ω₁ Ω₂ Ω}
    {T : FinMap (Env Ω₁) (PSet.maybe X)} {U : Env Ω₁ → X → FinMap (Env Ω₂) P}
    (hT : ∀ ω₁, T.fn ω₁ = none) : ∀ ω, P.IsNil ((letJust m T U).fn ω) :=
  bind_isNil fun _ => .inl (hT _)

theorem letJust_isNil_right {X : Type} {m : Merge Ω₁ Ω₂ Ω}
    {T : FinMap (Env Ω₁) (PSet.maybe X)} {U : Env Ω₁ → X → FinMap (Env Ω₂) P}
    (hU : ∀ ω₁ x ω₂, P.IsNil ((U ω₁ x).fn ω₂)) :
    ∀ ω, P.IsNil ((letJust m T U).fn ω) :=
  bind_isNil fun ω => .inr <| by
    show P.IsNil (((T.fn (m.split ω).1).elim (empty _) (U _)).fn (m.split ω).2)
    cases T.fn (m.split ω).1 with
    | none => exact P.nil_isNil
    | some x => exact hU _ x _

end FinMap
end FFP
