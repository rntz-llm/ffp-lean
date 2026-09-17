/-
# Types, contexts and typing derivations of λFS

Figures 2, 4 and 5 of "Finite Functional Programming".

We define *intrinsically typed* terms: an inhabitant of `Term Γ Δ Ω P` is a
typing derivation of `Γ / Δ / Ω ⊢ t : P`, and an inhabitant of `Expr Γ A` is
a derivation of `Γ ⊢ e : A`.  Variables are de Bruijn indices into the
relevant context.

## Contexts

The paper treats contexts as sets of named hypotheses, with `Δ₁ ∪ Δ₂` a
genuine union (a relevant variable may occur on both sides) and `Ω₁, Ω₂` a
concatenation of disjoint contexts, both up to the implicit exchange of
hypotheses.  With de Bruijn indices we make this explicit:

* `Cover Δ₁ Δ₂ Δ` witnesses `Δ = Δ₁ ∪ Δ₂`: every hypothesis of `Δ` is sent
  to the left premise, the right premise, or both.
* `Merge Ω₁ Ω₂ Ω` witnesses `Ω = Ω₁, Ω₂` up to exchange: every hypothesis
  of `Ω` is sent to exactly one premise.
* `Ins A Ω Ω'` witnesses `Ω' = Ω, x:A` up to exchange, i.e. `Ω'` is `Ω` with
  a hypothesis `x:A` inserted somewhere.

Contexts are lists with the most recently bound variable at the head, so the
paper's `Γ, x:A` is `A :: Γ` and `Γ, Ω₁` is `Ω₁ ++ Γ`.
-/
import FFP.Pointed

namespace FFP

/-! ## Types (figure 2) -/

mutual
  /-- Set types `A, B`. We add one base type of strings, so that examples
  have some atoms (people, films, …) to talk about. -/
  inductive Ty : Type
    | pt : PTy → Ty          -- the underlying set of a pointed type
    | arrow : Ty → Ty → Ty   -- A → B
    | prod : Ty → Ty → Ty    -- A × B
    | unit : Ty              -- 1
    | str : Ty               -- strings (base type for examples)
  /-- Pointed types `P, Q`. -/
  inductive PTy : Type
    | amp : PTy → PTy → PTy      -- P & Q
    | tensor : PTy → PTy → PTy   -- P ⊗ Q
    | lolli : PTy → PTy → PTy    -- P ⊸ Q
    | fmap : Ty → PTy → PTy      -- A ⇒ P
    | maybe : Ty → PTy           -- maybe A
    | nat : PTy                  -- N₀
end

/-- `bool = maybe 1` (figure 3). -/
abbrev PTy.bool : PTy := .maybe .unit

/-! ## Semantics of types (figure 5) -/

mutual
  /-- `⟦A⟧ ∈ Set`. -/
  def Ty.sem : Ty → Type
    | .pt P => P.sem.carrier
    | .arrow A B => A.sem → B.sem
    | .prod A B => A.sem × B.sem
    | .unit => Unit
    | .str => String
  /-- `⟦P⟧ ∈ Set∗`. -/
  def PTy.sem : PTy → PSet
    | .amp P Q => PSet.amp P.sem Q.sem
    | .tensor P Q => PSet.tensor P.sem Q.sem
    | .lolli P Q => PSet.lolli P.sem Q.sem
    | .fmap A P => PSet.fmap A.sem P.sem
    | .maybe A => PSet.maybe A.sem
    | .nat => PSet.nat
end

/-! ## Contexts and environments -/

abbrev Ctx := List Ty
abbrev PCtx := List PTy

/-- `⟦Γ⟧ = ∏ ⟦A⟧`, likewise `⟦Ω⟧`. -/
def Env : Ctx → Type
  | [] => Unit
  | A :: Γ => A.sem × Env Γ

/-- The underlying tuples of `⟦Δ⟧ = ⨂ ⟦P⟧`.  The n-ary smash product is
these tuples plus an explicit `nil`, quotiented so that a tuple with a `nil`
component is `nil`; see `PSet.smashCtx` in `FFP.Semantics`.  We carry the
predicate `AnyNil` around instead of the quotient. -/
def PEnv : PCtx → Type
  | [] => Unit
  | P :: Δ => P.sem.carrier × PEnv Δ

/-- A tuple in `⟦Δ⟧` is nil iff some component is nil. -/
def PEnv.AnyNil : (Δ : PCtx) → PEnv Δ → Prop
  | [], _ => False
  | P :: Δ, δ => P.sem.IsNil δ.1 ∨ AnyNil Δ δ.2

/-- De Bruijn variables: `Var Γ A` is a position in `Γ` holding type `A`. -/
inductive Var {α : Type} : List α → α → Type
  | here : Var (a :: l) a
  | there : Var l a → Var (b :: l) a

def Var.lookup : {Γ : Ctx} → Var Γ A → Env Γ → A.sem
  | _ :: _, .here, γ => γ.1
  | _ :: _, .there v, γ => v.lookup γ.2

/-- `⟦Ω₁⟧ × ⟦Γ⟧ → ⟦Ω₁ ++ Γ⟧`: build the environment for `Γ, Ω₁`. -/
def Env.append : {Ω : Ctx} → Env Ω → Env Γ → Env (Ω ++ Γ)
  | [], _, γ => γ
  | _ :: _, ω, γ => (ω.1, Env.append ω.2 γ)

/-- `Merge Ω₁ Ω₂ Ω`: `Ω` is an interleaving of `Ω₁` and `Ω₂`. -/
inductive Merge : Ctx → Ctx → Ctx → Type
  | nil : Merge [] [] []
  | left : Merge Ω₁ Ω₂ Ω → Merge (A :: Ω₁) Ω₂ (A :: Ω)
  | right : Merge Ω₁ Ω₂ Ω → Merge Ω₁ (A :: Ω₂) (A :: Ω)

def Merge.split : Merge Ω₁ Ω₂ Ω → Env Ω → Env Ω₁ × Env Ω₂
  | .nil, _ => ((), ())
  | .left m, ω => let p := m.split ω.2; ((ω.1, p.1), p.2)
  | .right m, ω => let p := m.split ω.2; (p.1, (ω.1, p.2))

def Merge.join : Merge Ω₁ Ω₂ Ω → Env Ω₁ → Env Ω₂ → Env Ω
  | .nil, _, _ => ()
  | .left m, ω₁, ω₂ => (ω₁.1, m.join ω₁.2 ω₂)
  | .right m, ω₁, ω₂ => (ω₂.1, m.join ω₁ ω₂.2)

theorem Merge.join_split : (m : Merge Ω₁ Ω₂ Ω) → (ω : Env Ω) →
    m.join (m.split ω).1 (m.split ω).2 = ω
  | .nil, () => rfl
  | .left m, (a, ω) => congrArg (a, ·) (m.join_split ω)
  | .right m, (a, ω) => congrArg (a, ·) (m.join_split ω)

/-- `Ins A Ω Ω'`: `Ω'` is `Ω` with a hypothesis of type `A` inserted. -/
inductive Ins (A : Ty) : Ctx → Ctx → Type
  | here : Ins A Ω (A :: Ω)
  | there : Ins A Ω Ω' → Ins A (B :: Ω) (B :: Ω')

def Ins.extract : Ins A Ω Ω' → Env Ω' → A.sem × Env Ω
  | .here, ω => ω
  | .there i, ω => let p := i.extract ω.2; (p.1, (ω.1, p.2))

def Ins.insert : Ins A Ω Ω' → A.sem → Env Ω → Env Ω'
  | .here, a, ω => (a, ω)
  | .there i, a, ω => (ω.1, i.insert a ω.2)

theorem Ins.insert_extract : (i : Ins A Ω Ω') → (ω : Env Ω') →
    i.insert (i.extract ω).1 (i.extract ω).2 = ω
  | .here, _ => rfl
  | .there i, (b, ω) => congrArg (b, ·) (i.insert_extract ω)

/-- `Cover Δ₁ Δ₂ Δ`: `Δ = Δ₁ ∪ Δ₂`, each hypothesis going left, right or both. -/
inductive Cover : PCtx → PCtx → PCtx → Type
  | nil : Cover [] [] []
  | left : Cover Δ₁ Δ₂ Δ → Cover (P :: Δ₁) Δ₂ (P :: Δ)
  | right : Cover Δ₁ Δ₂ Δ → Cover Δ₁ (P :: Δ₂) (P :: Δ)
  | both : Cover Δ₁ Δ₂ Δ → Cover (P :: Δ₁) (P :: Δ₂) (P :: Δ)

/-- `π_{Δ₁} : ⟦Δ⟧ → ⟦Δ₁⟧`. -/
def Cover.proj₁ : Cover Δ₁ Δ₂ Δ → PEnv Δ → PEnv Δ₁
  | .nil, _ => ()
  | .left c, δ => (δ.1, c.proj₁ δ.2)
  | .right c, δ => c.proj₁ δ.2
  | .both c, δ => (δ.1, c.proj₁ δ.2)

/-- `π_{Δ₂} : ⟦Δ⟧ → ⟦Δ₂⟧`. -/
def Cover.proj₂ : Cover Δ₁ Δ₂ Δ → PEnv Δ → PEnv Δ₂
  | .nil, _ => ()
  | .left c, δ => c.proj₂ δ.2
  | .right c, δ => (δ.1, c.proj₂ δ.2)
  | .both c, δ => (δ.1, c.proj₂ δ.2)

/-- Relevance: since `Δ₁ ∪ Δ₂` covers `Δ`, a nil hypothesis in `Δ` is nil in
at least one of the two projections. -/
theorem Cover.anyNil : (c : Cover Δ₁ Δ₂ Δ) → (δ : PEnv Δ) → PEnv.AnyNil Δ δ →
    PEnv.AnyNil Δ₁ (c.proj₁ δ) ∨ PEnv.AnyNil Δ₂ (c.proj₂ δ)
  | .nil, _, h => h.elim
  | .left c, δ, h => match h with
    | .inl hp => .inl (.inl hp)
    | .inr hδ => (c.anyNil δ.2 hδ).imp .inr id
  | .right c, δ, h => match h with
    | .inl hp => .inr (.inl hp)
    | .inr hδ => (c.anyNil δ.2 hδ).imp id .inr
  | .both c, δ, h => match h with
    | .inl hp => .inl (.inl hp)
    | .inr hδ => (c.anyNil δ.2 hδ).imp .inr .inr

/-! ## Typing derivations (figure 4)

Constructor names follow the rule names in the paper. -/

mutual
  /-- `Γ ⊢ e : A`. -/
  inductive Expr : Ctx → Ty → Type
    /-- ui: a closed pointed term is an expression. -/
    | ui : Term Γ [] [] P → Expr Γ (.pt P)
    | var : Var Γ A → Expr Γ A
    | unit : Expr Γ .unit
    | lam : Expr (A :: Γ) B → Expr Γ (.arrow A B)
    | app : Expr Γ (.arrow A B) → Expr Γ A → Expr Γ B
    | pair : Expr Γ A → Expr Γ B → Expr Γ (.prod A B)
    | fst : Expr Γ (.prod A B) → Expr Γ A
    | snd : Expr Γ (.prod A B) → Expr Γ B
    | case : Expr Γ (.pt (.maybe A)) → Expr (A :: Γ) B → Expr Γ B → Expr Γ B
  /-- `Γ / Δ / Ω ⊢ t : P`. -/
  inductive Term : Ctx → PCtx → Ctx → PTy → Type
    /-- ue: an expression of pointed type is a term using no relevant or
    finitely supported hypotheses. -/
    | ue : Expr Γ (.pt P) → Term Γ [] [] P
    /-- var: `Γ / x:P / · ⊢ x : P`. -/
    | var : Term Γ [P] [] P
    | nil : Term Γ Δ Ω P
    /-- ⊸i: `Γ / Δ, x:P / · ⊢ t : Q` gives `λx.t : P ⊸ Q`. -/
    | lamL : Term Γ (P :: Δ) [] Q → Term Γ Δ [] (.lolli P Q)
    /-- ⇒i: `Γ / Δ / Ω, x:A ⊢ t : P` gives `λx.t : A ⇒ P`. -/
    | lamF : Term Γ Δ (A :: Ω) P → Term Γ Δ Ω (.fmap A P)
    /-- ⊸e: `t u` with `Γ/Δ₁/Ω₁ ⊢ t : P ⊸ Q` and `Γ,Ω₁/Δ₂/Ω₂ ⊢ u : P`. -/
    | appL : Cover Δ₁ Δ₂ Δ → Merge Ω₁ Ω₂ Ω →
        Term Γ Δ₁ Ω₁ (.lolli P Q) → Term (Ω₁ ++ Γ) Δ₂ Ω₂ P → Term Γ Δ Ω Q
    /-- ⇒e: `t x` grounds a fresh finitely supported variable `x : A`. -/
    | appV : Ins A Ω Ω' → Term Γ Δ Ω (.fmap A P) → Term Γ Δ Ω' P
    /-- ⇒e₂: `t e` looks up an arbitrary expression, which may use `Ω`. -/
    | appE : Term Γ Δ Ω (.fmap A P) → Expr (Ω ++ Γ) A → Term Γ Δ Ω P
    /-- &i: both components share `Δ` and `Ω`. -/
    | amp : Term Γ Δ Ω P → Term Γ Δ Ω Q → Term Γ Δ Ω (.amp P Q)
    | proj₁ : Term Γ Δ Ω (.amp P Q) → Term Γ Δ Ω P
    | proj₂ : Term Γ Δ Ω (.amp P Q) → Term Γ Δ Ω Q
    /-- ⊗i: `(t, u)`, grounding left to right. -/
    | tensor : Cover Δ₁ Δ₂ Δ → Merge Ω₁ Ω₂ Ω →
        Term Γ Δ₁ Ω₁ P → Term (Ω₁ ++ Γ) Δ₂ Ω₂ Q → Term Γ Δ Ω (.tensor P Q)
    /-- ⊗e: `let (x, y) = t in u`, binding `x:P, y:Q` relevantly in `u`. -/
    | letTensor : Cover Δ₁ Δ₂ Δ → Merge Ω₁ Ω₂ Ω →
        Term Γ Δ₁ Ω₁ (.tensor P Q) → Term (Ω₁ ++ Γ) (Q :: P :: Δ₂) Ω₂ R → Term Γ Δ Ω R
    /-- maybe i: `just e`. -/
    | just : Expr Γ A → Term Γ [] [] (.maybe A)
    /-- maybe e: `let just x = t in u`, binding `x:A` unrestrictedly in `u`. -/
    | letJust : Cover Δ₁ Δ₂ Δ → Merge Ω₁ Ω₂ Ω →
        Term Γ Δ₁ Ω₁ (.maybe A) → Term (A :: (Ω₁ ++ Γ)) Δ₂ Ω₂ P → Term Γ Δ Ω P
end

end FFP
