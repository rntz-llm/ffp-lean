/-
Pointed sets and two definitions of finitely supported map.

Independent of `FFP`: a pointed set here has *one* distinguished element,
unlike `FFP.PSet`, whose `IsNil` predicate admits many.
-/

namespace FinSupp

/-- A set with a distinguished element.  "Is `x` nil?" is `x = nil`. -/
structure PSet where
  carrier : Type
  nil : carrier

variable {A : Type} {P : PSet}

/-- `l` covers the support: everything non-nil is listed. -/
def Covers (f : A → P.carrier) (l : List A) : Prop := ∀ a, f a ≠ P.nil → a ∈ l

/-- `l` splits the domain: every input is nil-valued or listed.  Constructively
stronger than `Covers`. -/
def Splits (f : A → P.carrier) (l : List A) : Prop := ∀ a, f a = P.nil ∨ a ∈ l

theorem Covers.of_splits {f : A → P.carrier} {l} (h : Splits f l) : Covers f l :=
  fun a ha => (h a).resolve_left ha

/-- **Definition 1**: the support is finite, as a proposition. -/
structure FinMapProp (A : Type) (P : PSet) where
  fn : A → P.carrier
  finite : ∃ l, Covers fn l

/-- Proof irrelevance: a subsingleton over `fn`. -/
theorem FinMapProp.ext {F G : FinMapProp A P} (h : F.fn = G.fn) : F = G := by
  cases F; cases G; cases h; rfl

/-! ## Truncation -/

def trivialSetoid (α : Type) : Setoid α where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

/-- `α` quotiented so that all its elements are equal. -/
def Trunc (α : Type) : Type := Quotient (trivialSetoid α)

namespace Trunc

def mk {α : Type} (a : α) : Trunc α := Quotient.mk (trivialSetoid α) a

theorem eq {α : Type} (x y : Trunc α) : x = y :=
  Quotient.inductionOn₂ x y fun _ _ => Quotient.sound trivial

instance {α : Type} : Subsingleton (Trunc α) := ⟨eq⟩

/-- Eliminate, provided the result does not depend on which element we have. -/
def lift {α : Type} {β : Sort u} (g : α → β) (h : ∀ a b, g a = g b) (x : Trunc α) : β :=
  Quotient.lift g (fun a b _ => h a b) x

theorem ind {α : Type} {motive : Trunc α → Prop} (h : ∀ a, motive (mk a)) (x : Trunc α) :
    motive x := Quotient.ind h x

end Trunc

/-- A list bounding the support, with the disjunctive proof asked of it. -/
structure Witness (f : A → P.carrier) where
  supp : List A
  ok : ∀ a, f a = P.nil ∨ a ∈ supp

theorem nonempty_witness_iff {f : A → P.carrier} :
    Nonempty (Witness f) ↔ ∃ l, Splits f l :=
  ⟨fun ⟨w⟩ => ⟨w.supp, w.ok⟩, fun ⟨l, h⟩ => ⟨⟨l, h⟩⟩⟩

/-- **Definition 2**: a witness of finite support, quotiented so all witnesses
are equal. -/
structure FinMapWit (A : Type) (P : PSet) where
  fn : A → P.carrier
  wit : Trunc (Witness fn)

/-- The quotient has one element: also a subsingleton over `fn`. -/
theorem FinMapWit.ext {F G : FinMapWit A P} (h : F.fn = G.fn) : F = G := by
  cases F; cases G; cases h; exact congrArg _ (Trunc.eq _ _)

abbrev PSet.nat : PSet := ⟨Nat, 0⟩

/-- A type with a list of all its elements. -/
structure Listable (A : Type) where
  elems : List A
  complete : ∀ a, a ∈ elems

end FinSupp
