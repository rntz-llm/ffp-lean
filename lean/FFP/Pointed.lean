/-
# Pointed sets, point preserving maps, and finite maps

The semantic universe of λFS (Arntzenius & Willsey, "Finite Functional
Programming", §2 and figure 1).

A pointed set is a set with a designated element `nil`.  The paper's smash
product `P ⊗ Q` is a *quotient* (any pair with a `nil` component is `nil`),
and so is the n-ary smash product used to interpret pointed contexts.  Rather
than build quotient types, we represent a pointed set by a carrier together
with the *predicate* `IsNil` picking out the equivalence class of `nil`.
Nothing in the semantics ever needs to decide equality of pointed values;
what it needs is exactly "is this value nil?", both to state finite support
(`supp f = {x | ¬ IsNil (f x)}`) and point preservation (`IsNil p → IsNil (f p)`).

Everything here is computable: proofs are erased at runtime, and a finite
map carries its support as an explicit list.
-/

namespace FFP

/-- A pointed set: a carrier, the class of values that count as `nil`, and a
canonical representative of that class. -/
structure PSet where
  carrier : Type
  IsNil : carrier → Prop
  nil : carrier
  nil_isNil : IsNil nil

/-- Point preserving maps `P ⊸ Q`: functions that send `nil` to `nil`. -/
structure PMap (P Q : PSet) where
  fn : P.carrier → Q.carrier
  pres : ∀ p, P.IsNil p → Q.IsNil (fn p)

/-- Finitely supported maps `A ⇒ P`: a function equipped with a proof of
finite support, namely a list containing every input with a non-`nil` output.
(The list may over-approximate the support; it is finite either way.) -/
structure FinMap (A : Type) (P : PSet) where
  fn : A → P.carrier
  supp : List A
  supp_ok : ∀ a, ¬ P.IsNil (fn a) → a ∈ supp

namespace PSet

/-- Direct product `P & Q`: nil when *both* components are nil. -/
abbrev amp (P Q : PSet) : PSet where
  carrier := P.carrier × Q.carrier
  IsNil x := P.IsNil x.1 ∧ Q.IsNil x.2
  nil := (P.nil, Q.nil)
  nil_isNil := ⟨P.nil_isNil, Q.nil_isNil⟩

/-- Smash product `P ⊗ Q`: nil when *either* component is nil. -/
abbrev tensor (P Q : PSet) : PSet where
  carrier := P.carrier × Q.carrier
  IsNil x := P.IsNil x.1 ∨ Q.IsNil x.2
  nil := (P.nil, Q.nil)
  nil_isNil := Or.inl P.nil_isNil

/-- Point preserving maps `P ⊸ Q`, pointed by the constantly-nil map. -/
abbrev lolli (P Q : PSet) : PSet where
  carrier := PMap P Q
  IsNil f := ∀ p, Q.IsNil (f.fn p)
  nil := ⟨fun _ => Q.nil, fun _ _ => Q.nil_isNil⟩
  nil_isNil _ := Q.nil_isNil

/-- Finite maps `A ⇒ P`, pointed by the map with empty support. -/
abbrev fmap (A : Type) (P : PSet) : PSet where
  carrier := FinMap A P
  IsNil f := ∀ a, P.IsNil (f.fn a)
  nil := ⟨fun _ => P.nil, [], fun _ h => absurd P.nil_isNil h⟩
  nil_isNil _ := P.nil_isNil

/-- `maybe A`: the free pointed set on `A`, pointed by `none`. -/
abbrev maybe (A : Type) : PSet where
  carrier := Option A
  IsNil o := o = none
  nil := none
  nil_isNil := rfl

/-- `N₀`: the naturals pointed by `0`. -/
abbrev nat : PSet where
  carrier := Nat
  IsNil n := n = 0
  nil := 0
  nil_isNil := rfl

/-- `bool` is sugar for `maybe 1` (figure 3): `true = just ()`, `false = nil`. -/
abbrev bool : PSet := maybe Unit

end PSet

/-- A finite map's support list is a superset of its true support, so a value
that lies outside the list is nil. -/
theorem FinMap.isNil_of_not_mem {A : Type} {P : PSet} (f : FinMap A P) {a : A}
    (h : a ∉ f.supp) : P.IsNil (f.fn a) :=
  Classical.byContradiction fun hn => h (f.supp_ok a hn)

end FFP
