/-
# The set comprehensions of figure 6, as finite-map combinators

Figure 6 writes each term denotation as a set comprehension of input/output
pairs `ω ↦ y`.  Each combinator below is one of those comprehensions: its `fn`
is the function `ω ↦ y`, its `supp` is a list enumerating (a superset of) the
inputs the comprehension ranges over, and `supp_ok` shows the list really
bounds the support.  The `_isNil_` lemmas are what point preservation of the
semantics rests on: nil inputs produce nil outputs.
-/
import FFP.Syntax

namespace FFP
namespace FinMap

variable {P Q R : PSet}

/-- `{() ↦ y}`: the singleton map on the empty context. -/
def single (y : P.carrier) : FinMap (Env []) P where
  fn _ := y
  supp := [()]
  supp_ok a _ := by cases a; exact .head _

/-- `{}`: the empty map. -/
def empty (A : Type) : FinMap A P := (PSet.fmap A P).nil

/-- `{a ↦ g a x : a ↦ x ∈ T}`, for a `g` that yields nil on nil. -/
def comp {A : Type} (T : FinMap A P) (g : A → P.carrier → Q.carrier)
    (hg : ∀ a p, ¬ Q.IsNil (g a p) → ¬ P.IsNil p) : FinMap A Q where
  fn a := g a (T.fn a)
  supp := T.supp
  supp_ok a h := T.supp_ok a (hg a _ h)

theorem comp_isNil {A : Type} {T : FinMap A P} {g hg} (hT : ∀ a, P.IsNil (T.fn a))
    (hg' : ∀ a p, P.IsNil p → Q.IsNil (g a p)) : ∀ a, Q.IsNil ((comp T g hg).fn a) :=
  fun a => hg' a _ (hT a)

/-- &i: `{a ↦ ⟨x, y⟩ : a ↦ x ∈ T, a ↦ y ∈ U}`. -/
def amp {A : Type} (T : FinMap A P) (U : FinMap A Q) : FinMap A (PSet.amp P Q) where
  fn a := (T.fn a, U.fn a)
  supp := T.supp ++ U.supp
  supp_ok a h := List.mem_append.2 <|
    (Classical.em (P.IsNil (T.fn a))).elim
      (fun hp => .inr (U.supp_ok a fun hq => h ⟨hp, hq⟩))
      (fun hp => .inl (T.supp_ok a hp))

/-- ⇒i: `{ω ↦ {x ↦ y : (ω,x) ↦ y ∈ T} : ∃ x y. (ω,x) ↦ y ∈ T}`. -/
def curry {X : Type} (T : FinMap (X × Env Ω) P) : FinMap (Env Ω) (PSet.fmap X P) where
  fn ω := ⟨fun x => T.fn (x, ω), T.supp.map Prod.fst,
           fun x hx => List.mem_map.2 ⟨(x, ω), T.supp_ok _ hx, rfl⟩⟩
  supp := T.supp.map Prod.snd
  supp_ok ω hω :=
    have ⟨x, hx⟩ := Classical.not_forall.1 hω
    List.mem_map.2 ⟨(x, ω), T.supp_ok _ hx, rfl⟩

/-- ⇒e: `{(ω,x) ↦ y : ω ↦ f ∈ T, x ↦ y ∈ f}`, with `x` inserted into `Ω` by `i`. -/
def uncurry (i : Ins A Ω Ω') (T : FinMap (Env Ω) (PSet.fmap A.sem P)) :
    FinMap (Env Ω') P where
  fn ω' := (T.fn (i.extract ω').2).fn (i.extract ω').1
  supp := T.supp.flatMap fun ω => (T.fn ω).supp.map fun x => i.insert x ω
  supp_ok ω' h := List.mem_flatMap.2 ⟨_, T.supp_ok _ fun hn => h (hn _),
    List.mem_map.2 ⟨_, (T.fn _).supp_ok _ h, i.insert_extract ω'⟩⟩

/-- Left-to-right grounding, the shape shared by ⊸e, ⊗i, ⊗e and maybe e:
`{(ω₁,ω₂) ↦ k x y : ω₁ ↦ x ∈ T, ω₂ ↦ y ∈ U ω₁}`.  The right-hand map `U` may
depend on `ω₁` (it is `⟦u⟧ (γ, ω₁) …`, with `Ω₁` grounded).  `hk` says the
combining function `k` cannot produce a non-nil output unless both inputs are
non-nil, which is what keeps the support finite. -/
def bind (m : Merge Ω₁ Ω₂ Ω) (T : FinMap (Env Ω₁) P) (U : Env Ω₁ → FinMap (Env Ω₂) Q)
    (k : P.carrier → Q.carrier → R.carrier)
    (hk : ∀ ω₁ ω₂, ¬ R.IsNil (k (T.fn ω₁) ((U ω₁).fn ω₂)) →
      ¬ P.IsNil (T.fn ω₁) ∧ ¬ Q.IsNil ((U ω₁).fn ω₂)) : FinMap (Env Ω) R where
  fn ω := k (T.fn (m.split ω).1) ((U (m.split ω).1).fn (m.split ω).2)
  supp := T.supp.flatMap fun ω₁ => (U ω₁).supp.map fun ω₂ => m.join ω₁ ω₂
  supp_ok ω h := List.mem_flatMap.2 ⟨_, T.supp_ok _ (hk _ _ h).1,
    List.mem_map.2 ⟨_, (U _).supp_ok _ (hk _ _ h).2, m.join_split ω⟩⟩

theorem bind_isNil_left {m : Merge Ω₁ Ω₂ Ω} {T : FinMap (Env Ω₁) P}
    {U : Env Ω₁ → FinMap (Env Ω₂) Q} {k : P.carrier → Q.carrier → R.carrier} {hk}
    (hT : ∀ ω₁, P.IsNil (T.fn ω₁))
    (hk' : ∀ ω₁ ω₂, P.IsNil (T.fn ω₁) → R.IsNil (k (T.fn ω₁) ((U ω₁).fn ω₂))) :
    ∀ ω, R.IsNil ((bind m T U k hk).fn ω) :=
  fun _ => hk' _ _ (hT _)

theorem bind_isNil_right {m : Merge Ω₁ Ω₂ Ω} {T : FinMap (Env Ω₁) P}
    {U : Env Ω₁ → FinMap (Env Ω₂) Q} {k : P.carrier → Q.carrier → R.carrier} {hk}
    (hU : ∀ ω₁ ω₂, Q.IsNil ((U ω₁).fn ω₂))
    (hk' : ∀ p q, Q.IsNil q → R.IsNil (k p q)) :
    ∀ ω, R.IsNil ((bind m T U k hk).fn ω) :=
  fun _ => hk' _ _ (hU _ _)

/-- maybe e: `{(ω₁,ω₂) ↦ y : ω₁ ↦ just x ∈ T, ω₂ ↦ y ∈ U ω₁ x}`. -/
def letJust {X : Type} (m : Merge Ω₁ Ω₂ Ω) (T : FinMap (Env Ω₁) (PSet.maybe X))
    (U : Env Ω₁ → X → FinMap (Env Ω₂) P) : FinMap (Env Ω) P :=
  bind m T (fun ω₁ => (T.fn ω₁).elim (empty _) (U ω₁)) (fun _ y => y) fun ω₁ _ h =>
    ⟨fun hn => h (by
        have hn' : T.fn ω₁ = none := hn
        rw [hn']; exact P.nil_isNil),
     h⟩

theorem letJust_isNil_left {X : Type} {m : Merge Ω₁ Ω₂ Ω} {T : FinMap (Env Ω₁) (PSet.maybe X)}
    {U : Env Ω₁ → X → FinMap (Env Ω₂) P} (hT : ∀ ω₁, T.fn ω₁ = none) :
    ∀ ω, P.IsNil ((letJust m T U).fn ω) := fun ω => by
  show P.IsNil (((T.fn (m.split ω).1).elim (empty _) (U _)).fn (m.split ω).2)
  rw [hT]; exact P.nil_isNil

theorem letJust_isNil_right {X : Type} {m : Merge Ω₁ Ω₂ Ω} {T : FinMap (Env Ω₁) (PSet.maybe X)}
    {U : Env Ω₁ → X → FinMap (Env Ω₂) P} (hU : ∀ ω₁ x ω₂, P.IsNil ((U ω₁ x).fn ω₂)) :
    ∀ ω, P.IsNil ((letJust m T U).fn ω) := fun ω => by
  show P.IsNil (((T.fn (m.split ω).1).elim (empty _) (U _)).fn (m.split ω).2)
  cases T.fn (m.split ω).1 with
  | none => exact P.nil_isNil
  | some x => exact hU _ x _

end FinMap
end FFP
