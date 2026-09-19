/-
# Semantics of expressions and terms (figure 6)

`⟦Γ ⊢ e : A⟧ ∈ ⟦Γ⟧ → ⟦A⟧` and `⟦Γ/Δ/Ω ⊢ t : P⟧ ∈ ⟦Γ⟧ → ⟦Δ⟧ ⊸ ⟦Ω⟧ ⇒ ⟦P⟧`.

Each term denotation is a `FinMap` built from the comprehension combinators
of `FFP.Combinators`.  Because ⊸i must produce a *point preserving* map, and
⊸e / ⇒e must *use* point preservation and finite support of their subterms'
values to bound their own support, the semantics is defined simultaneously
with a proof that it is nil whenever the relevant environment `δ` is nil
(`TermSem.pres`).  This is the "semantic finite support and point
preservation" that §7 of the paper lists as not yet proven.
-/
import FFP.Combinators

namespace FFP

/-- The n-ary smash product `⟦Δ⟧ = ⨂_{x:P ∈ Δ} ⟦P⟧` (figure 5): the tuples of
`PEnv Δ` plus an explicit `nil`, with a tuple counting as nil when any of its
components is.  (For `Δ = ·` this has the two elements `nil` and `()`.) -/
def PSet.smashCtx (Δ : PCtx) : PSet where
  carrier := Option (PEnv Δ)
  IsNil
    | none => True
    | some δ => PEnv.AnyNil Δ δ
  nil := none
  nil_isNil := trivial

/-- The denotation of `Γ/Δ/Ω ⊢ t : P` at a fixed `γ` and tuple `δ`: a finite
map `⟦Ω⟧ ⇒ ⟦P⟧`, together with the fact that it is the nil map whenever `δ`
is nil, which is what makes `δ ↦ map` point preserving. -/
structure TermSem (Δ : PCtx) (δ : PEnv Δ) (Ω : Ctx) (P : PTy) where
  map : FinMap (Env Ω) P.sem
  pres : PEnv.AnyNil Δ δ → ∀ ω, P.sem.IsNil (map.fn ω)

mutual
  /-- `⟦Γ ⊢ e : A⟧ γ`. -/
  def Expr.sem : Expr Γ A → Env Γ → A.sem
    -- ⟦t⟧γ = ⟦t⟧ γ () ()
    | .ui t, γ => (t.sem γ ()).map.fn ()
    | .var v, γ => v.lookup γ
    | .unit, _ => ()
    | .lam e, γ => fun a => e.sem (a, γ)
    | .app e₁ e₂, γ => (e₁.sem γ) (e₂.sem γ)
    | .pair e₁ e₂, γ => (e₁.sem γ, e₂.sem γ)
    | .fst e, γ => (e.sem γ).1
    | .snd e, γ => (e.sem γ).2
    | .case e₁ e₂ e₃, γ =>
      match e₁.sem γ with
      | some x => e₂.sem (x, γ)
      | none => e₃.sem γ

  /-- `⟦Γ/Δ/Ω ⊢ t : P⟧ γ δ`, one case per rule of figure 4. -/
  def Term.sem : Term Γ Δ Ω P → (γ : Env Γ) → (δ : PEnv Δ) → TermSem Δ δ Ω P
    -- ⟦Γ/·/· ⊢ e : P⟧ γ δ = {() ↦ ⟦e⟧γ : δ ≠ nil}; the tuple () is never nil.
    | .ue e, γ, _ => ⟨.single (e.sem γ), fun h => False.elim h⟩
    -- ⟦Γ/x:P/· ⊢ x : P⟧ γ x = {() ↦ x}
    | .var, _, δ => ⟨.single δ.1, fun h _ => Or.elim h id False.elim⟩
    -- ⟦nil⟧ γ δ = {}
    | .nil, _, _ => ⟨.empty _, fun _ _ => P.sem.nil_isNil⟩
    -- ⟦λx.t : P ⊸ Q⟧ γ δ = {() ↦ λx. ⟦t⟧ γ (δ, x)}
    | .lamL t, γ, δ =>
      ⟨.single ⟨fun p => (t.sem γ (p, δ)).map.fn (),
                fun p hp => (t.sem γ (p, δ)).pres (.inl hp) ()⟩,
       fun h _ p => (t.sem γ (p, δ)).pres (.inr h) ()⟩
    -- ⟦λx.t : A ⇒ P⟧ γ δ = {ω ↦ {x ↦ y : (ω,x) ↦ y ∈ ⟦t⟧γδ} : ∃ x y. (ω,x) ↦ y ∈ ⟦t⟧γδ}
    | .lamF t, γ, δ =>
      let T := t.sem γ δ
      ⟨.curry T.map, fun h ω x => T.pres h (x, ω)⟩
    -- ⟦t u⟧ γ δ = {(ω₁,ω₂) ↦ x y : ω₁ ↦ x ∈ ⟦t⟧ γ (π_Δ₁ δ), ω₂ ↦ y ∈ ⟦u⟧ (γ,ω₁) (π_Δ₂ δ)}
    | .appL c m t u, γ, δ =>
      let T := t.sem γ (c.proj₁ δ)
      let U := fun ω₁ => u.sem (Env.append ω₁ γ) (c.proj₂ δ)
      ⟨.bind m T.map (fun ω₁ => (U ω₁).map) (fun f y => f.fn y)
          (fun ω₁ _ h => h.elim (fun hf => hf _) (fun hy => (T.map.fn ω₁).pres _ hy)),
       fun h => FinMap.bind_isNil fun _ => match c.anyNil δ h with
         | .inl h₁ => .inl (T.pres h₁ _)
         | .inr h₂ => .inr ((U _).pres h₂ _)⟩
    -- ⟦t x⟧ γ δ = {(ω,x) ↦ y : ω ↦ f ∈ ⟦t⟧γδ, x ↦ y ∈ f}
    | .appV i t, γ, δ =>
      let T := t.sem γ δ
      ⟨.uncurry i T.map, fun h _ => T.pres h _ _⟩
    -- ⟦t e⟧ γ δ = {ω ↦ f (⟦e⟧(γ,ω)) : ω ↦ f ∈ ⟦t⟧γδ}
    | .appE t e, γ, δ =>
      let T := t.sem γ δ
      ⟨.comp T.map (fun ω f => f.fn (e.sem (Env.append ω γ))) (fun _ _ hf => hf _),
       fun h ω => T.pres h ω _⟩
    -- ⟦⟨t,u⟩⟧ γ δ = {ω ↦ ⟨x,y⟩ : ω ↦ x ∈ ⟦t⟧γδ, ω ↦ y ∈ ⟦u⟧γδ}
    | .amp t u, γ, δ =>
      let T := t.sem γ δ
      let U := u.sem γ δ
      ⟨.amp T.map U.map, fun h ω => ⟨T.pres h ω, U.pres h ω⟩⟩
    -- ⟦πᵢ t⟧ γ δ = {ω ↦ πᵢ x : ω ↦ x ∈ ⟦t⟧γδ}
    | .proj₁ t, γ, δ =>
      let T := t.sem γ δ
      ⟨.comp T.map (fun _ x => x.1) (fun _ _ hx => hx.1), fun h ω => (T.pres h ω).1⟩
    | .proj₂ t, γ, δ =>
      let T := t.sem γ δ
      ⟨.comp T.map (fun _ x => x.2) (fun _ _ hx => hx.2), fun h ω => (T.pres h ω).2⟩
    -- ⟦(t,u)⟧ γ δ = {(ω₁,ω₂) ↦ (x,y) : ω₁ ↦ x ∈ ⟦t⟧ γ (π_Δ₁ δ), ω₂ ↦ y ∈ ⟦u⟧ (γ,ω₁) (π_Δ₂ δ)}
    | .tensor c m t u, γ, δ =>
      let T := t.sem γ (c.proj₁ δ)
      let U := fun ω₁ => u.sem (Env.append ω₁ γ) (c.proj₂ δ)
      ⟨.bind m T.map (fun ω₁ => (U ω₁).map) Prod.mk (fun _ _ h => h),
       fun h => FinMap.bind_isNil fun _ => match c.anyNil δ h with
         | .inl h₁ => .inl (T.pres h₁ _)
         | .inr h₂ => .inr ((U _).pres h₂ _)⟩
    -- ⟦let (x,y) = t in u⟧ γ δ
    --   = {(ω₁,ω₂) ↦ z : ω₁ ↦ (x,y) ∈ ⟦t⟧ γ (π_Δ₁ δ), ω₂ ↦ z ∈ ⟦u⟧ (γ,ω₁) (π_Δ₂ δ, x, y)}
    | .letTensor c m t u, γ, δ =>
      let T := t.sem γ (c.proj₁ δ)
      let U := fun ω₁ =>
        u.sem (Env.append ω₁ γ) ((T.map.fn ω₁).2, (T.map.fn ω₁).1, c.proj₂ δ)
      ⟨.bind m T.map (fun ω₁ => (U ω₁).map) (fun _ z => z)
          (fun ω₁ ω₂ h => h.elim
            (fun hxy => (U ω₁).pres (hxy.elim (fun hx => .inr (.inl hx)) .inl) ω₂) id),
       fun h => FinMap.bind_isNil fun _ => match c.anyNil δ h with
         | .inl h₁ => .inl (T.pres h₁ _)
         | .inr h₂ => .inr ((U _).pres (.inr (.inr h₂)) _)⟩
    -- ⟦Γ/·/· ⊢ just e : maybe A⟧ γ δ = {() ↦ just (⟦e⟧γ) : δ ≠ nil}
    | .just e, γ, _ => ⟨.single (some (e.sem γ)), fun h => False.elim h⟩
    -- ⟦let just x = t in u⟧ γ δ
    --   = {(ω₁,ω₂) ↦ y : ω₁ ↦ just x ∈ ⟦t⟧ γ (π_Δ₁ δ), ω₂ ↦ y ∈ ⟦u⟧ (γ,ω₁,x) (π_Δ₂ δ)}
    | .letJust c m t u, γ, δ =>
      let T := t.sem γ (c.proj₁ δ)
      let U := fun ω₁ x => u.sem (x, Env.append ω₁ γ) (c.proj₂ δ)
      ⟨.letJust m T.map (fun ω₁ x => (U ω₁ x).map),
       fun h => match c.anyNil δ h with
         | .inl h₁ => FinMap.letJust_isNil_left (T.pres h₁)
         | .inr h₂ => FinMap.letJust_isNil_right fun ω₁ x ω₂ => (U ω₁ x).pres h₂ ω₂⟩
end

/-- `⟦Γ/Δ/Ω ⊢ t : P⟧ γ ∈ ⟦Δ⟧ ⊸ ⟦Ω⟧ ⇒ ⟦P⟧`: the point preserving map out of the
n-ary smash product, sending its explicit `nil` to the empty map. -/
def Term.semP (t : Term Γ Δ Ω P) (γ : Env Γ) :
    PMap (PSet.smashCtx Δ) (PSet.fmap (Env Ω) P.sem) where
  fn
    | none => (PSet.fmap _ _).nil
    | some δ => (t.sem γ δ).map
  pres
    | none, _ => (PSet.fmap _ _).nil_isNil
    | some δ, h => (t.sem γ δ).pres h

end FFP
