/-
# Renaming of unrestricted variables, and the syntax sugar of figure 3

`Γ` is a cartesian context, so weakening it is admissible; we need it to
desugar `t and u ⟶ let just _ = t in u`, whose continuation `u` must be
weakened by the unused `_ : 1`.  We implement the general renaming of `Γ`
by de Bruijn index maps; `Δ` and `Ω` are untouched.
-/
import FFP.Syntax

namespace FFP

/-- A renaming of unrestricted contexts. -/
def Ren (Γ Γ' : Ctx) := ∀ {A : Ty}, Var Γ A → Var Γ' A

namespace Ren

def weak : Ren Γ (A :: Γ) := fun v => .there v

def lift (ρ : Ren Γ Γ') : Ren (A :: Γ) (A :: Γ') := fun
  | .here => .here
  | .there v => .there (ρ v)

/-- Extend a renaming under the finitely supported variables `Ω` that jumped
into the unrestricted context (`Γ, Ω`). -/
def liftMany : (Ω : Ctx) → Ren Γ Γ' → Ren (Ω ++ Γ) (Ω ++ Γ')
  | [], ρ => ρ
  | _ :: Ω, ρ => Ren.lift (liftMany Ω ρ)

end Ren

mutual
  def Expr.rename (ρ : Ren Γ Γ') : Expr Γ A → Expr Γ' A
    | .ui t => .ui (t.rename ρ)
    | .var v => .var (ρ v)
    | .unit => .unit
    | .lam e => .lam (e.rename ρ.lift)
    | .app e₁ e₂ => .app (e₁.rename ρ) (e₂.rename ρ)
    | .pair e₁ e₂ => .pair (e₁.rename ρ) (e₂.rename ρ)
    | .fst e => .fst (e.rename ρ)
    | .snd e => .snd (e.rename ρ)
    | .case e₁ e₂ e₃ => .case (e₁.rename ρ) (e₂.rename ρ.lift) (e₃.rename ρ)

  def Term.rename (ρ : Ren Γ Γ') : Term Γ Δ Ω P → Term Γ' Δ Ω P
    | .ue e => .ue (e.rename ρ)
    | .var => .var
    | .nil => .nil
    | .lamL t => .lamL (t.rename ρ)
    | .lamF t => .lamF (t.rename ρ)
    | .appL c m t u => .appL c m (t.rename ρ) (u.rename (ρ.liftMany _))
    | .appV i t => .appV i (t.rename ρ)
    | .appE t e => .appE (t.rename ρ) (e.rename (ρ.liftMany _))
    | .amp t u => .amp (t.rename ρ) (u.rename ρ)
    | .proj₁ t => .proj₁ (t.rename ρ)
    | .proj₂ t => .proj₂ (t.rename ρ)
    | .tensor c m t u => .tensor c m (t.rename ρ) (u.rename (ρ.liftMany _))
    | .letTensor c m t u => .letTensor c m (t.rename ρ) (u.rename (ρ.liftMany _))
    | .just e => .just (e.rename ρ)
    | .letJust c m t u => .letJust c m (t.rename ρ) (u.rename (Ren.lift (ρ.liftMany _)))
end

/-! ## Trivial context splits -/

def Cover.allLeft : (Δ : PCtx) → Cover Δ [] Δ
  | [] => .nil
  | _ :: Δ => .left (allLeft Δ)

def Cover.allRight : (Δ : PCtx) → Cover [] Δ Δ
  | [] => .nil
  | _ :: Δ => .right (allRight Δ)

def Merge.allLeft : (Ω : Ctx) → Merge Ω [] Ω
  | [] => .nil
  | _ :: Ω => .left (allLeft Ω)

def Merge.allRight : (Ω : Ctx) → Merge [] Ω Ω
  | [] => .nil
  | _ :: Ω => .right (allRight Ω)

/-! ## Syntax sugar (figure 3) -/

namespace Term

/-- `true ⟶ just ()` -/
def true : Term Γ [] [] .bool := .just .unit

/-- `false ⟶ nil` -/
def false : Term Γ Δ Ω .bool := .nil

/-- `t and u ⟶ let just _ = t in u`, generalised to `bool ⊗ P ⊸ P`. -/
def and (c : Cover Δ₁ Δ₂ Δ) (m : Merge Ω₁ Ω₂ Ω)
    (t : Term Γ Δ₁ Ω₁ .bool) (u : Term (Ω₁ ++ Γ) Δ₂ Ω₂ P) : Term Γ Δ Ω P :=
  .letJust c m t (u.rename Ren.weak)

/-- `let x = t in u ⟶ let (x, y) = (t, true) in (y and u)`; `x : P` is bound
relevantly (it is the head of `u`'s `Δ`). -/
def let_ (c : Cover Δ₁ Δ₂ Δ) (m : Merge Ω₁ Ω₂ Ω)
    (t : Term Γ Δ₁ Ω₁ P) (u : Term (Ω₁ ++ Γ) (P :: Δ₂) Ω₂ Q) : Term Γ Δ Ω Q :=
  .letTensor c m (.tensor (.allLeft Δ₁) (.allLeft Ω₁) t .true)
    (Term.and (.left (.allRight _)) (.allRight Ω₂) .var u)

/-- `t when u ⟶ let x = t in (u and x)`, of type `P ⊗ bool ⊸ P`. -/
def when (c : Cover Δ₁ Δ₂ Δ) (m : Merge Ω₁ Ω₂ Ω)
    (t : Term Γ Δ₁ Ω₁ P) (u : Term (Ω₁ ++ Γ) Δ₂ Ω₂ .bool) : Term Γ Δ Ω P :=
  let_ c m t (Term.and (.right (.allLeft Δ₂)) (.allLeft Ω₂) u .var)

end Term
end FFP
