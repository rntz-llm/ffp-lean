/-
# Running the semantics on the paper's examples (§3)

We write typing derivations for `costars`, `hitchcockAlone`, `filmCount`,
`intersect` and `union` against a signature `Γ₀` holding figure 3's
primitives and a small `stars` table, then `#eval` their denotations.
-/
import FFP.Semantics
import FFP.Sugar
import FFP.Prims

namespace FFP

/-- Run a closed term: `⟦t⟧ = ⟦t⟧ γ () ()`. -/
def Term.run (t : Term Γ [] [] P) (γ : Env Γ) : P.sem.carrier := (t.sem γ ()).map.fn ()

/-! ### De Bruijn indices -/
def v0 : Var (a :: l) a := .here
def v1 : Var (b :: a :: l) a := .there v0
def v2 : Var (c :: b :: a :: l) a := .there v1
def v3 : Var (d :: c :: b :: a :: l) a := .there v2
def v4 : Var (e :: d :: c :: b :: a :: l) a := .there v3
def v5 : Var (f :: e :: d :: c :: b :: a :: l) a := .there v4
def v6 : Var (g :: f :: e :: d :: c :: b :: a :: l) a := .there v5

namespace Examples

/-! ## The signature

    Γ₀ = sum : (str ⇒ N₀) ⊸ N₀, exists : (str ⇒ bool) ⊸ bool, or : bool & bool ⊸ bool,
         one : N₀, stars : str ⇒ str ⇒ bool, hitchcock : str, (=) : str → str ⇒ bool,
         stewart : str ⇒ bool, novak : str ⇒ bool
-/

abbrev bool := PTy.bool
abbrev str := Ty.str
abbrev setTy : PTy := .fmap str bool

-- Type class resolution does not unfold `Ty.sem`, so point it at the base types.
instance : DecidableEq Ty.str.sem := inferInstanceAs (DecidableEq String)
instance {n : Nat} : OfNat (Ty.pt .nat).sem n := inferInstanceAs (OfNat Nat n)

def Γ₀ : Ctx :=
  [ .pt (.lolli (.fmap str .nat) .nat)   -- 0: sum
  , .pt (.lolli setTy bool)              -- 1: exists
  , .pt (.lolli (.amp bool bool) bool)   -- 2: or
  , .pt .nat                             -- 3: one
  , .pt (.fmap str setTy)                -- 4: stars
  , str                                  -- 5: hitchcock
  , .arrow str (.pt setTy)               -- 6: (=)
  , .pt setTy                            -- 7: stewart : films starring James Stewart
  , .pt setTy ]                          -- 8: novak : films starring Kim Novak

def starsTable : FinMap String (PSet.fmap String PSet.bool) := FinMap.ofRel
  [ ("Psycho", "Anthony Perkins"), ("Psycho", "Janet Leigh")
  , ("Vertigo", "James Stewart"), ("Vertigo", "Kim Novak")
  , ("Rear Window", "James Stewart"), ("Rear Window", "Grace Kelly")
  , ("Rope", "James Stewart") ]

def γ₀ : Env Γ₀ :=
  ( Prim.sum String, Prim.«exists» String, Prim.or, 1, starsTable, "Hitchcock", Prim.eq String
  , FinMap.ofList ["Vertigo", "Rear Window", "Rope"], FinMap.ofList ["Vertigo", "Picnic"], () )

/-- `costars x y = exists (λfilm. stars film x and stars film y) : person ⇒ person ⇒ bool` -/
def costars : Term Γ₀ [] [] (.fmap str setTy) :=
  .lamF <| .lamF <|                                        -- Ω = y, x
    .appL .nil (.right (.right .nil)) (.ue (.var v1)) <|   -- exists (…), grounding nothing itself
      .lamF <|                                             -- Ω = film, y, x
        Term.and .nil (.left (.right (.left .nil)))        -- Ω₁ = film, x   Ω₂ = y
          (.appV (.there .here) (.appV .here (.ue (.var v4))))   -- stars film x
          (.appV .here (.appE (.ue (.var v6)) (.var v0)))        -- stars film y, with film ∈ Γ,Ω₁

/-- `hitchcockAlone x = (hitchcock = x) : person ⇒ bool` -/
def hitchcockAlone : Term Γ₀ [] [] setTy :=
  .lamF <| .appV .here <| .ue (.app (.var v6) (.var v5))

/-- `filmCount actor = sum (λfilm. 1 when stars film actor) : person ⇒ N₀` -/
def filmCount : Term Γ₀ [] [] (.fmap str .nat) :=
  .lamF <|                                                 -- Ω = actor
    .appL .nil (.right .nil) (.ue (.var v0)) <|            -- sum (…)
      .lamF <|                                             -- Ω = film, actor
        Term.when .nil (.right (.right .nil))
          (.ue (.var v3))                                  -- 1
          (.appV (.there .here) (.appV .here (.ue (.var v4))))   -- stars film actor

/-- `intersect f g x = f x and g x : (A ⇒ bool) ⊸ (A ⇒ bool) ⊸ (A ⇒ bool)` -/
def intersect : Term Γ₀ [] [] (.lolli setTy (.lolli setTy setTy)) :=
  .lamL <| .lamL <|                                        -- Δ = g, f
    .lamF <|                                               -- Ω = x
      Term.and (.right (.left .nil)) (.left .nil)          -- Δ₁ = f, Δ₂ = g;  Ω₁ = x, Ω₂ = ·
        (.appV .here .var)                                 -- f x
        (.appE .var (.var v0))                             -- g x, with x ∈ Γ,Ω₁

/-- `union fg x = π₁ fg x or π₂ fg x : (A ⇒ bool) & (A ⇒ bool) ⊸ (A ⇒ bool)` -/
def union : Term Γ₀ [] [] (.lolli (.amp setTy setTy) setTy) :=
  .lamL <| .lamF <|                                        -- Δ = fg, Ω = x
    .appL (.right .nil) (.right .nil) (.ue (.var v2)) <|   -- or ⟨…, …⟩
      .amp (.appV .here (.proj₁ .var)) (.appV .here (.proj₂ .var))

/-- `intersect stewart novak` -/
def stewartAndNovak : Term Γ₀ [] [] setTy :=
  .appL .nil .nil (.appL .nil .nil intersect (.ue (.var (.there v6)))) (.ue (.var (.there (.there v6))))

/-- `union ⟨stewart, novak⟩` -/
def stewartOrNovak : Term Γ₀ [] [] setTy :=
  .appL .nil .nil union (.amp (.ue (.var (.there v6))) (.ue (.var (.there (.there v6)))))

/-! ## Running them -/

/--
info: [("Anthony Perkins", "Anthony Perkins"),
 ("Anthony Perkins", "Janet Leigh"),
 ("Janet Leigh", "Anthony Perkins"),
 ("Janet Leigh", "Janet Leigh"),
 ("James Stewart", "James Stewart"),
 ("James Stewart", "Kim Novak"),
 ("James Stewart", "Grace Kelly"),
 ("Kim Novak", "James Stewart"),
 ("Kim Novak", "Kim Novak"),
 ("Grace Kelly", "James Stewart"),
 ("Grace Kelly", "Grace Kelly")]
-/
#guard_msgs in
#eval FinMap.toPairs (costars.run γ₀)

/-- info: ["Hitchcock"] -/
#guard_msgs in
#eval FinMap.toList (hitchcockAlone.run γ₀)

/-- info: [("Anthony Perkins", 1), ("Janet Leigh", 1), ("James Stewart", 3), ("Kim Novak", 1), ("Grace Kelly", 1)] -/
#guard_msgs in
#eval FinMap.toCounts (filmCount.run γ₀)

/-- info: ["Vertigo"] -/
#guard_msgs in
#eval FinMap.toList (stewartAndNovak.run γ₀)

/-- info: ["Vertigo", "Rear Window", "Rope", "Picnic"] -/
#guard_msgs in
#eval FinMap.toList (stewartOrNovak.run γ₀)

-- The support list is an over-approximation (it is built without deciding
-- equality on values), but it is finite: every actor in the table shows up.
/-- info: ["Anthony Perkins", "Janet Leigh", "James Stewart", "Kim Novak", "Grace Kelly"] -/
#guard_msgs in
#eval (costars.run γ₀).supp.eraseDups

end Examples
end FFP
