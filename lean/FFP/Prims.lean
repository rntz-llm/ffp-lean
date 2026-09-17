/-
# Primitive functions (figure 3), as semantic values

λFS has no primitive constants of its own: figure 3's `or`, `exists`, `sum`,
`+`, `×`, `=` are assumed in the unrestricted context `Γ`.  Here we build
their denotations, so that closed programs can be run against an
environment `γ` supplying them.  Every one is a point preserving map (or, for
`=`, an ordinary function into finite maps), and the proof is part of the
value.
-/
import FFP.Syntax

namespace FFP
namespace Prim

/-- `or : bool & bool ⊸ bool` -/
def or : PMap (PSet.amp PSet.bool PSet.bool) PSet.bool where
  fn x := match x.1, x.2 with
    | none, none => none
    | _, _ => some ()
  pres x h := by
    obtain ⟨h₁, h₂⟩ := h
    show (match x.1, x.2 with | none, none => none | _, _ => some ()) = none
    rw [show x.1 = none from h₁, show x.2 = none from h₂]

/-- `exists : (A ⇒ bool) ⊸ bool`: is the support non-empty? -/
def «exists» (A : Type) : PMap (PSet.fmap A PSet.bool) PSet.bool where
  fn f := if f.supp.any fun a => (f.fn a).isSome then some () else none
  pres f hf := by
    have h : (f.supp.any fun a => (f.fn a).isSome) = false := by
      apply Bool.eq_false_iff.2
      intro h
      obtain ⟨a, _, ha⟩ := List.any_eq_true.1 h
      rw [show f.fn a = none from hf a] at ha
      exact Bool.noConfusion ha
    show (if f.supp.any (fun a => (f.fn a).isSome) then some () else none) = none
    rw [h]; rfl

theorem foldl_add_zero {A : Type} (g : A → Nat) (hg : ∀ a, g a = 0) :
    ∀ (l : List A) (acc : Nat), l.foldl (fun acc a => acc + g a) acc = acc
  | [], _ => rfl
  | a :: l, acc => by rw [List.foldl_cons, hg a, Nat.add_zero]; exact foldl_add_zero g hg l acc

/-- `sum : (A ⇒ N₀) ⊸ N₀`: add up the values over the support.  Decidable
equality on `A` is needed to remove duplicates from the support list. -/
def sum (A : Type) [DecidableEq A] : PMap (PSet.fmap A PSet.nat) PSet.nat where
  fn f := f.supp.eraseDups.foldl (fun acc a => acc + f.fn a) 0
  pres f hf := foldl_add_zero (fun a => f.fn a) hf _ 0

/-- `(+) : N₀ & N₀ ⊸ N₀` -/
def plus : PMap (PSet.amp PSet.nat PSet.nat) PSet.nat where
  fn x := x.1 + x.2
  pres x h := by
    obtain ⟨h₁, h₂⟩ := h
    show x.1 + x.2 = 0
    rw [show x.1 = 0 from h₁, show x.2 = 0 from h₂]

/-- `(×) : N₀ ⊗ N₀ ⊸ N₀` -/
def times : PMap (PSet.tensor PSet.nat PSet.nat) PSet.nat where
  fn x := x.1 * x.2
  pres x h := by
    show x.1 * x.2 = 0
    rcases h with h | h
    · rw [show x.1 = 0 from h, Nat.zero_mul]
    · rw [show x.2 = 0 from h, Nat.mul_zero]

/-- `(=) : A → (A ⇒ bool)`: the singleton relation, supported on `[a]`. -/
def eq (A : Type) [DecidableEq A] (a : A) : FinMap A PSet.bool where
  fn b := if a = b then some () else none
  supp := [a]
  supp_ok b h :=
    if hab : a = b then List.mem_singleton.2 hab.symm
    else absurd (by simp [hab]) h

end Prim

/-! ## Tables: finite maps from data -/

namespace FinMap

/-- A finite set `A ⇒ bool` from a list of elements. -/
def ofList {A : Type} [DecidableEq A] (l : List A) : FinMap A PSet.bool where
  fn a := if a ∈ l then some () else none
  supp := l
  supp_ok a h := if ha : a ∈ l then ha else absurd (by simp [ha]) h

/-- A finite relation `A ⇒ B ⇒ bool` from a list of pairs. -/
def ofRel {A B : Type} [DecidableEq A] [DecidableEq B] (l : List (A × B)) :
    FinMap A (PSet.fmap B PSet.bool) where
  fn a := ⟨fun b => if (a, b) ∈ l then some () else none, l.map Prod.snd,
           fun b h => if hab : (a, b) ∈ l then List.mem_map.2 ⟨(a, b), hab, rfl⟩
                      else absurd (by simp [hab]) h⟩
  supp := l.map Prod.fst
  supp_ok a h :=
    have ⟨b, hb⟩ := Classical.not_forall.1 h
    if hab : (a, b) ∈ l then List.mem_map.2 ⟨(a, b), hab, rfl⟩
    else absurd (by simp [hab]) hb

/-- The entries of a finite map with a decidably non-nil value. -/
def entries {A : Type} [DecidableEq A] {P : PSet} (f : FinMap A P)
    (nonNil : P.carrier → Bool) : List (A × P.carrier) :=
  f.supp.eraseDups.filterMap fun a => if nonNil (f.fn a) then some (a, f.fn a) else none

/-- The elements of a finite set `A ⇒ bool`. -/
def toList {A : Type} [DecidableEq A] (f : FinMap A PSet.bool) : List A :=
  (f.entries Option.isSome).map Prod.fst

/-- The pairs of a finite relation `A ⇒ B ⇒ bool`. -/
def toPairs {A B : Type} [DecidableEq A] [DecidableEq B]
    (f : FinMap A (PSet.fmap B PSet.bool)) : List (A × B) :=
  f.supp.eraseDups.flatMap fun a => (f.fn a).toList.map fun b => (a, b)

/-- The entries of a finite bag `A ⇒ N₀`. -/
def toCounts {A : Type} [DecidableEq A] (f : FinMap A PSet.nat) : List (A × Nat) :=
  f.entries fun n => n != 0

end FinMap
end FFP
