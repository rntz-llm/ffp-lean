/-
# Pointed sets and finitely supported maps: two definitions, and the gap between them

This file is self-contained and independent of the `FFP` development: it
imports nothing from it and shares no definitions with it.  In particular the
`PSet` below is a genuine **pointed set** — a set with *one* distinguished
element — not `FFP.PSet`, which carries an `IsNil` *predicate* and so lets
many values count as nil.

Two definitions of "finitely supported map from `A` into a pointed set `P`":

1. `FinMap₁`: a function `fn : A → P.carrier` together with a *proof* that its
   support `{a | fn a ≠ nil}` is finite.
2. `FinMap₂`: a function together with a *witness* that its support is finite —
   a list, plus a proof that every input is either sent to nil or listed —
   where the witness type has been quotiented so that all witnesses are equal.

The question this file answers: can we convert between them, constructively or
otherwise?  In one word each: `₂ → ₁` yes, constructively; `₁ → ₂` yes, but
only classically, and the two obstructions to doing it constructively can both
be pinned down exactly.

## Results

* `FinMap₂.toFinMap₁` — definition 2 to definition 1, constructively
  (§ "Axiom audit" checks that it uses no axioms at all).
* `Strengthening.em` / `strengthening_of_em` — the first obstruction,
  the *phrasing* of finiteness, is **equivalent to excluded middle**.
  This half is a genuine disproof: a constructive conversion would prove `em`.
* `Untruncation.subsingletonChoice` and friends — the second obstruction,
  escaping a `Prop` into a `Type`, is **equivalent to subsingleton choice**
  (equivalently: to the principle that `Nonempty α` can be upgraded to a
  quotient-style truncation `Trunc α`).  This half cannot be refuted inside
  Lean — `Classical.choice` proves it — but the equivalence localises exactly
  what is missing.
* `FinMap₁.toFinMap₂` — the classical conversion, and `toFinMap₂_toFinMap₁` /
  `toFinMap₁_toFinMap₂`: classically the two definitions are isomorphic, and
  since both are subsingletons over the underlying function, the isomorphism
  is the only one there is.
* `FinMap₁.toFinMap₂_of_listable` — a constructive conversion whenever the key
  type comes with a list of all its elements.
* `FinMap₂.support` — with `Nat` keys and a boolean nil-test, definition 2
  lets you *compute* the exact support as data, constructively; the same
  function built from definition 1 is `noncomputable`.  That is the sharpest
  internal statement of the difference between the two definitions.
-/

namespace FinSupp

/-! ## Pointed sets -/

/-- A **pointed set**: a set (here, a type) together with a distinguished
element `nil`.  "Is `x` nil?" means exactly `x = nil`. -/
structure PSet where
  /-- The underlying set. -/
  carrier : Type
  /-- The distinguished element. -/
  nil : carrier

/-- `Option A`, pointed at `none`. -/
def PSet.option (A : Type) : PSet := ⟨Option A, none⟩

/-- `Nat`, pointed at `0`. -/
def PSet.nat : PSet := ⟨Nat, 0⟩

/-- `Prop`, pointed at `True`.  Used to extract excluded middle below. -/
def PSet.prop : PSet := ⟨Prop, True⟩

/-! ## Support, and three readings of "the support is finite"

The support of `f : A → P.carrier` is the set of inputs with non-nil output.
A list `l` can relate to it in three ways.  Classically the three are
equivalent; constructively they are not, and the differences matter. -/

variable {A : Type} {P : PSet}

/-- The support of `f`: the inputs whose output is not nil. -/
def Support (f : A → P.carrier) (a : A) : Prop := f a ≠ P.nil

/-- `l` **covers** the support: everything non-nil is listed.  This is the
literal reading of "the support is finite" (it is contained in a finite list),
and it is what `FinMap₁` uses. -/
def Covers (f : A → P.carrier) (l : List A) : Prop := ∀ a, Support f a → a ∈ l

/-- `l` **splits** `A`: every input is either sent to nil or listed.  This is
the witness condition asked of `FinMap₂`, stated as a disjunction. -/
def Splits (f : A → P.carrier) (l : List A) : Prop := ∀ a, f a = P.nil ∨ a ∈ l

/-- `l` **enumerates** the support exactly. -/
def Enumerates (f : A → P.carrier) (l : List A) : Prop := ∀ a, a ∈ l ↔ Support f a

theorem Covers.of_splits {f : A → P.carrier} {l} (h : Splits f l) : Covers f l :=
  fun a ha => (h a).resolve_left ha

theorem Covers.of_enumerates {f : A → P.carrier} {l} (h : Enumerates f l) : Covers f l :=
  fun a ha => (h a).mpr ha

/-- Enumerating the support is stronger than splitting only in that it forbids
junk in the list; the disjunction still needs a decision at each input. -/
theorem Splits.of_enumerates_of_dec {f : A → P.carrier} {l}
    (h : Enumerates f l) (dec : ∀ a, f a = P.nil ∨ Support f a) : Splits f l :=
  fun a => (dec a).imp id (h a).mpr

/-! ## Definition 1: a function plus a proof that its support is finite -/

/-- **Finitely supported map, version 1.**  A function into a pointed set,
carrying a `Prop` asserting that its support is finite. -/
structure FinMap₁ (A : Type) (P : PSet) where
  /-- The underlying function. -/
  fn : A → P.carrier
  /-- The support is contained in some finite list. -/
  finite : ∃ l, Covers fn l

/-- Two version-1 maps with the same underlying function are equal: the second
field is a `Prop`, so proof irrelevance does the rest. -/
theorem FinMap₁.ext {F G : FinMap₁ A P} (h : F.fn = G.fn) : F = G := by
  cases F; cases G; cases h; rfl

/-! ## Definition 2: a function plus a quotiented witness

First, the truncation: a quotient of a type by the total relation, so that all
of its elements become equal. -/

/-- The relation that relates everything. -/
def trivialSetoid (α : Type) : Setoid α where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

/-- `Trunc α` is `α` quotiented so that all its elements are equal. -/
def Trunc (α : Type) : Type := Quotient (trivialSetoid α)

namespace Trunc

/-- Include an element into the truncation. -/
def mk {α : Type} (a : α) : Trunc α := Quotient.mk (trivialSetoid α) a

/-- All elements of `Trunc α` are equal — that is what the quotient is for. -/
theorem eq {α : Type} (x y : Trunc α) : x = y :=
  Quotient.inductionOn₂ x y fun _ _ => Quotient.sound trivial

instance {α : Type} : Subsingleton (Trunc α) := ⟨eq⟩

/-- Eliminate a truncation into any sort, provided the result does not depend
on which element we have. -/
def lift {α : Type} {β : Sort u} (g : α → β) (h : ∀ a b, g a = g b) (x : Trunc α) : β :=
  Quotient.lift g (fun a b _ => h a b) x

@[simp] theorem lift_mk {α : Type} {β : Sort u} (g : α → β) (h : ∀ a b, g a = g b) (a : α) :
    lift g h (mk a) = g a := rfl

/-- Induction: to prove a `Prop` about a truncation, prove it about elements. -/
theorem ind {α : Type} {motive : Trunc α → Prop} (h : ∀ a, motive (mk a)) (x : Trunc α) :
    motive x := Quotient.ind h x

/-- A truncation yields mere existence, constructively.  (The converse is the
crux of this file: see `TruncLift`.) -/
theorem nonempty {α : Type} (x : Trunc α) : Nonempty α :=
  lift (fun a => ⟨a⟩) (fun _ _ => rfl) x

end Trunc

/-- A **witness** that `f` has finite support: a list, together with a proof
that every input is either sent to nil or is in the list. -/
structure Witness (f : A → P.carrier) where
  /-- The list bounding the support (it may contain junk). -/
  supp : List A
  /-- Every input is nil-valued or listed. -/
  ok : ∀ a, f a = P.nil ∨ a ∈ supp

theorem Witness.splits {f : A → P.carrier} (w : Witness f) : Splits f w.supp := w.ok

/-- Mere existence of a witness is exactly the disjunctive phrasing. -/
theorem nonempty_witness_iff {f : A → P.carrier} :
    Nonempty (Witness f) ↔ ∃ l, Splits f l :=
  ⟨fun ⟨w⟩ => ⟨w.supp, w.ok⟩, fun ⟨l, h⟩ => ⟨⟨l, h⟩⟩⟩

/-- **Finitely supported map, version 2.**  A function into a pointed set,
equipped with a witness of finite support, quotiented so that all witnesses
are equal. -/
structure FinMap₂ (A : Type) (P : PSet) where
  /-- The underlying function. -/
  fn : A → P.carrier
  /-- A witness of finite support, up to the identification of all witnesses. -/
  wit : Trunc (Witness fn)

/-- Two version-2 maps with the same underlying function are equal: the second
field lives in a quotient with a single element. -/
theorem FinMap₂.ext {F G : FinMap₂ A P} (h : F.fn = G.fn) : F = G := by
  cases F; cases G; cases h; exact congrArg _ (Trunc.eq _ _)

/-! ## Definition 2 → definition 1, constructively

The truncation may be eliminated into a `Prop`, because any two proofs of a
`Prop` are equal.  So this direction is free. -/

/-- Every version-2 map is a version-1 map.  No axioms. -/
def FinMap₂.toFinMap₁ (F : FinMap₂ A P) : FinMap₁ A P where
  fn := F.fn
  finite := F.wit.lift (fun w => ⟨w.supp, Covers.of_splits w.ok⟩) (fun _ _ => rfl)

theorem FinMap₂.toFinMap₁_fn (F : FinMap₂ A P) : F.toFinMap₁.fn = F.fn := rfl

/-- The conversion is injective — indeed both types are subsingletons over the
underlying function, so `toFinMap₁` is an embedding and the only question is
whether it is surjective. -/
theorem FinMap₂.toFinMap₁_injective {F G : FinMap₂ A P}
    (h : F.toFinMap₁ = G.toFinMap₁) : F = G :=
  FinMap₂.ext (congrArg FinMap₁.fn h)

/-! ## Obstruction 1: the phrasing of finiteness is exactly excluded middle

Definition 1 says "everything non-nil is in `l`"; definition 2's witness says
"everything is nil or in `l`".  Getting from the first to the second means
deciding, at each input, which of the two disjuncts holds — and that is not a
figure of speech: the principle that this is always possible *is* excluded
middle. -/

/-- The principle "a list covering the support can be turned into a list
splitting the domain". -/
def Strengthening : Prop :=
  ∀ (A : Type) (P : PSet) (f : A → P.carrier), (∃ l, Covers f l) → (∃ l, Splits f l)

/-- Excluded middle gives the strengthening, with the same list. -/
theorem strengthening_of_em (em : ∀ q : Prop, q ∨ ¬q) : Strengthening := by
  rintro A P f ⟨l, hl⟩
  exact ⟨l, fun a => (em (f a = P.nil)).imp id (fun hne => hl a hne)⟩

/-- Every member of a list of naturals is at most the list's maximum. -/
theorem le_foldr_max : ∀ (l : List Nat) (m : Nat), m ∈ l → m ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro m hm; cases hm
  | cons a t ih =>
    intro m hm
    cases hm with
    | head => simp only [List.foldr_cons]; omega
    | tail _ h => have := ih m h; simp only [List.foldr_cons]; omega

/-- Every finite list of naturals misses a natural. -/
theorem exists_not_mem (l : List Nat) : ∃ n, n ∉ l :=
  ⟨l.foldr max 0 + 1, fun hm => by have := le_foldr_max l _ hm; omega⟩

/-- … and conversely the strengthening gives double negation elimination.

The pointed set is `Prop` pointed at `True`, the map is the constant `q` on
`Nat` keys.  Under `¬¬q` the *empty* list covers the support vacuously, so
definition 1's hypothesis holds; but a list splitting `ℕ` must miss some `n`,
and at that `n` the disjunction has to report `q = True` outright. -/
theorem Strengthening.dne (h : Strengthening) (q : Prop) (hq : ¬¬q) : q := by
  have ne_true : q ≠ True → ¬q := fun hne hqq => hne (propext ⟨fun _ => trivial, fun _ => hqq⟩)
  have covers : ∃ l : List Nat, Covers (P := PSet.prop) (fun _ => q) l :=
    ⟨[], fun _ ha => absurd (ne_true ha) hq⟩
  obtain ⟨l, hl⟩ := h Nat PSet.prop (fun _ => q) covers
  obtain ⟨n, hn⟩ := exists_not_mem l
  have : q = True := (hl n).resolve_right hn
  rw [this]; trivial

/-- Hence the strengthening implies excluded middle: it is not constructive. -/
theorem Strengthening.em (h : Strengthening) (q : Prop) : q ∨ ¬q :=
  h.dne _ fun hn => hn (Or.inr fun hq => hn (Or.inl hq))

/-! ## Obstruction 2: escaping the `Prop` is exactly subsingleton choice

Suppose obstruction 1 out of the way — suppose we are handed definition 1 in
its disjunctive phrasing, `∃ l, Splits f l`, which is literally
`Nonempty (Witness f)`.  Definition 2 still asks for an element of
`Trunc (Witness f)`, which is a `Type`.  Lean's elimination rules do not let a
`Prop` be taken apart to build a `Type`, however subsingleton-ish the target,
so this is not a matter of finding a cleverer proof.

Three principles, all in `Type 1`, turn out to be equivalent; the file proves
the cycle `Untruncation → SubsingletonChoice → TruncLift → Untruncation`. -/

/-- The conversion we want, with obstruction 1 already assumed away. -/
def Untruncation : Type 1 :=
  ∀ (A : Type) (P : PSet) (f : A → P.carrier), (∃ l, Splits f l) → Trunc (Witness f)

/-- Choice for subsingletons: a nonempty type with at most one element has an
element.  Provable from `Classical.choice`, not otherwise. -/
def SubsingletonChoice : Type 1 := ∀ α : Type, Subsingleton α → Nonempty α → α

/-- Propositional truncation upgrades to quotient truncation. -/
def TruncLift : Type 1 := ∀ α : Type, Nonempty α → Trunc α

/-- A witness for the everywhere-non-nil map on `α` has a nonempty list,
provided `α` is nonempty: if the list were empty every element of `α` would be
sent to nil, and it is not. -/
theorem Witness.supp_ne_nil {α : Type} (hne : Nonempty α)
    (w : Witness (P := PSet.option Unit) (fun _ : α => some ())) : w.supp ≠ [] := by
  intro hnil
  refine hne.elim fun a => ?_
  rcases w.ok a with h | h
  · simp [PSet.option] at h
  · rw [hnil] at h; cases h

/-- **The conversion implies subsingleton choice.**  Given a subsingleton `α`
with an element, map `α` into `Option Unit` by the constant `some ()`: its
support is all of `α`, and a one-element list covers it because `α` is a
subsingleton.  Definition 2's witness must then list an element of `α`, and
`α` being a subsingleton is exactly what lets us read it back out of the
quotient. -/
def Untruncation.subsingletonChoice (conv : Untruncation) : SubsingletonChoice := by
  intro α hss hne
  have hsplit : ∃ l, Splits (P := PSet.option Unit) (fun _ : α => some ()) l :=
    hne.elim fun a₀ => ⟨[a₀], fun a => Or.inr (by rw [Subsingleton.elim a a₀]; simp)⟩
  exact (conv α (PSet.option Unit) (fun _ => some ()) hsplit).lift
    (fun w => w.supp.head (Witness.supp_ne_nil hne w))
    (fun _ _ => Subsingleton.elim _ _)

/-- Subsingleton choice gives the truncation lift: `Trunc α` is a subsingleton
and is nonempty as soon as `α` is. -/
def SubsingletonChoice.truncLift (sc : SubsingletonChoice) : TruncLift :=
  fun α hne => sc (Trunc α) inferInstance (hne.elim fun a => ⟨Trunc.mk a⟩)

/-- The truncation lift gives the conversion: `∃ l, Splits f l` is
`Nonempty (Witness f)`. -/
def TruncLift.untruncation (tl : TruncLift) : Untruncation :=
  fun _ _ f h => tl (Witness f) (nonempty_witness_iff.mpr h)

/-- Closing the cycle: subsingleton choice also follows from the truncation
lift, and every one of the three principles implies the other two. -/
def SubsingletonChoice.untruncation (sc : SubsingletonChoice) : Untruncation :=
  sc.truncLift.untruncation

/-- `Classical.choice` proves all of them — which is why none of them can be
*refuted* here.  Only their constructive unprovability is at stake, and that
is a statement about Lean, not a statement in Lean. -/
noncomputable def classicalSubsingletonChoice : SubsingletonChoice :=
  fun _ _ hne => Classical.choice hne

/-! ## The classical conversion

With `Classical.choice` both obstructions fall: `Classical.em` supplies the
disjunction at each input, and `Classical.choice` turns the resulting
`Nonempty (Witness f)` into an actual witness, which `Trunc.mk` then hides
again.  (In Lean `Classical.em` is itself derived from `Classical.choice` via
Diaconescu, so the axiom audit below lists only `Classical.choice`.) -/

/-- Classically, a list covering the support also splits the domain. -/
theorem Splits.of_covers {f : A → P.carrier} {l} (h : Covers f l) : Splits f l :=
  fun a => (Classical.em (f a = P.nil)).imp id (fun hne => h a hne)

/-- **Definition 1 → definition 2, classically.** -/
noncomputable def FinMap₁.toFinMap₂ (F : FinMap₁ A P) : FinMap₂ A P where
  fn := F.fn
  wit := Trunc.mk (Classical.choice
    (nonempty_witness_iff.mpr (F.finite.elim fun l hl => ⟨l, Splits.of_covers hl⟩)))

theorem FinMap₁.toFinMap₂_fn (F : FinMap₁ A P) : F.toFinMap₂.fn = F.fn := rfl

/-- The two conversions are mutually inverse, so classically the definitions
are isomorphic.  Both `FinMap₁ A P` and `FinMap₂ A P` are subsingletons over
the underlying function (`FinMap₁.ext`, `FinMap₂.ext`), so this is the only
isomorphism commuting with `fn` — there is no choice of identification. -/
theorem FinMap₁.toFinMap₂_toFinMap₁ (F : FinMap₁ A P) : F.toFinMap₂.toFinMap₁ = F :=
  FinMap₁.ext rfl

theorem FinMap₂.toFinMap₁_toFinMap₂ (F : FinMap₂ A P) : F.toFinMap₁.toFinMap₂ = F :=
  FinMap₂.ext rfl

/-! ## When the conversion *is* constructive

The obstructions are about the key type, not about the function.  If `A` comes
with a list of all its elements then every map into a pointed set is finitely
supported, constructively, and definition 1's hypothesis is not even needed. -/

/-- A type together with a list of all its elements. -/
structure Listable (A : Type) where
  /-- The list of all elements. -/
  elems : List A
  /-- … and it really does contain them all. -/
  complete : ∀ a, a ∈ elems

/-- Over a listable key type, every function has a witness, with no
hypothesis and no axioms. -/
def Listable.witness (L : Listable A) (f : A → P.carrier) : Witness f where
  supp := L.elems
  ok a := Or.inr (L.complete a)

/-- Hence a constructive version of the conversion, for listable key types. -/
def FinMap₁.toFinMap₂_of_listable (L : Listable A) (F : FinMap₁ A P) : FinMap₂ A P where
  fn := F.fn
  wit := Trunc.mk (L.witness F.fn)

theorem FinMap₁.toFinMap₂_of_listable_fn (L : Listable A) (F : FinMap₁ A P) :
    (F.toFinMap₂_of_listable L).fn = F.fn := rfl

/-! ## What definition 2 buys: the support as computable data

The quotient means a version-2 map carries no *particular* list — but it does
carry every list-derived quantity that is the same for all witnesses.  The
exact support is one such quantity: over `Nat` keys, with a boolean nil-test,
sweeping `0 … max(witness list)` and keeping the non-nil keys gives the same
list whichever witness we start from.  So definition 2 lets us *compute* the
support, constructively.

The corresponding function on definition 1 (`FinMap₁.support`) has to route
through `Classical.choice` and is `noncomputable`.  This is the sharpest
statement of the difference available inside Lean: same list, same
specification, but one of the two `#eval`s runs. -/

section Support

/-- The boolean nil-test does test nil-ness. -/
theorem keep_iff (isNil : P.carrier → Bool) (hIsNil : ∀ x, isNil x = true ↔ x = P.nil)
    (f : Nat → P.carrier) (n : Nat) : (!isNil (f n)) = true ↔ f n ≠ P.nil := by
  cases h : isNil (f n) with
  | true => simp [(hIsNil _).mp h]
  | false =>
    have hne : f n ≠ P.nil := fun he => by rw [(hIsNil _).mpr he] at h; cases h
    simp [hne]

/-- The non-nil keys below `N`. -/
def upTo (isNil : P.carrier → Bool) (f : Nat → P.carrier) (N : Nat) : List Nat :=
  (List.range N).filter (fun n => !isNil (f n))

theorem mem_upTo (isNil : P.carrier → Bool) (hIsNil : ∀ x, isNil x = true ↔ x = P.nil)
    (f : Nat → P.carrier) (N n : Nat) : n ∈ upTo isNil f N ↔ n < N ∧ f n ≠ P.nil := by
  simp only [upTo, List.mem_filter, List.mem_range, keep_iff isNil hIsNil f]

/-- Sweeping further than a bound on the support changes nothing. -/
theorem upTo_eq_of_le (isNil : P.carrier → Bool) (hIsNil : ∀ x, isNil x = true ↔ x = P.nil)
    (f : Nat → P.carrier) {N : Nat} (hN : ∀ n, f n ≠ P.nil → n < N) :
    ∀ M, N ≤ M → upTo isNil f M = upTo isNil f N := by
  intro M
  induction M with
  | zero => intro h; have : N = 0 := Nat.le_zero.mp h; subst this; rfl
  | succ M ih =>
    intro hle
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · rw [heq]
    · have hNM : N ≤ M := by omega
      have hdrop : (!isNil (f M)) = false := by
        cases h : isNil (f M) with
        | true => rfl
        | false =>
          have hne : f M ≠ P.nil := (keep_iff isNil hIsNil f M).mp (by rw [h]; rfl)
          exact absurd (hN M hne) (by omega)
      have hstep : upTo isNil f (M + 1) = upTo isNil f M := by
        simp only [upTo, List.range_succ, List.filter_append, List.filter_cons, hdrop]
        simp
      rw [hstep, ih hNM]

/-- A witness bounds the support: everything non-nil is listed, hence at most
the list's maximum. -/
def bound (f : Nat → P.carrier) (w : Witness f) : Nat := w.supp.foldr max 0 + 1

theorem lt_bound (f : Nat → P.carrier) (w : Witness f) (n : Nat) (hn : f n ≠ P.nil) :
    n < bound f w :=
  Nat.lt_succ_of_le (le_foldr_max _ _ ((w.ok n).resolve_left hn))

/-- The sweep is witness-independent — which is exactly what lets it pass
through the quotient. -/
theorem upTo_bound_eq (isNil : P.carrier → Bool) (hIsNil : ∀ x, isNil x = true ↔ x = P.nil)
    (f : Nat → P.carrier) (w w' : Witness f) :
    upTo isNil f (bound f w) = upTo isNil f (bound f w') := by
  rcases Nat.le_total (bound f w) (bound f w') with h | h
  · exact (upTo_eq_of_le isNil hIsNil f (lt_bound f w) _ h).symm
  · exact upTo_eq_of_le isNil hIsNil f (lt_bound f w') _ h

end Support

/-- **The exact support of a version-2 map, computed.**  Constructive: the
only elimination of the quotient is into a value that all witnesses agree on. -/
def FinMap₂.support (F : FinMap₂ Nat P) (isNil : P.carrier → Bool)
    (hIsNil : ∀ x, isNil x = true ↔ x = P.nil) : List Nat :=
  F.wit.lift (fun w => upTo isNil F.fn (bound F.fn w)) (upTo_bound_eq isNil hIsNil F.fn)

theorem FinMap₂.mem_support (F : FinMap₂ Nat P) (isNil : P.carrier → Bool)
    (hIsNil : ∀ x, isNil x = true ↔ x = P.nil) (n : Nat) :
    n ∈ F.support isNil hIsNil ↔ F.fn n ≠ P.nil := by
  obtain ⟨fn, wit⟩ := F
  refine Trunc.ind (motive := fun w =>
    n ∈ (FinMap₂.mk fn w).support isNil hIsNil ↔ fn n ≠ P.nil) ?_ wit
  intro w
  show n ∈ upTo isNil fn (bound fn w) ↔ _
  rw [mem_upTo isNil hIsNil]
  exact ⟨fun h => h.2, fun h => ⟨lt_bound fn w n h, h⟩⟩

/-- The same list from a version-1 map.  Dropping `noncomputable` is a compile
error — the support is locked inside a `Prop` and only `Classical.choice` gets
it out. -/
noncomputable def FinMap₁.support (F : FinMap₁ Nat P) (isNil : P.carrier → Bool)
    (hIsNil : ∀ x, isNil x = true ↔ x = P.nil) : List Nat :=
  F.toFinMap₂.support isNil hIsNil

theorem FinMap₁.mem_support (F : FinMap₁ Nat P) (isNil : P.carrier → Bool)
    (hIsNil : ∀ x, isNil x = true ↔ x = P.nil) (n : Nat) :
    n ∈ F.support isNil hIsNil ↔ F.fn n ≠ P.nil :=
  FinMap₂.mem_support F.toFinMap₂ isNil hIsNil n

/-! ### It runs -/

/-- A map `ℕ → ℕ₀` that is non-nil at 3 and 5 only. -/
def demoFn : Nat → Nat := fun n => if n = 3 then 7 else if n = 5 then 2 else 0

/-- Witnessed by a deliberately sloppy list: junk keys and a gap. -/
def demo : FinMap₂ Nat PSet.nat where
  fn := demoFn
  wit := Trunc.mk
    { supp := [0, 1, 2, 3, 4, 5, 9]
      ok := fun a => by
        unfold demoFn
        by_cases h3 : a = 3
        · exact Or.inr (by subst h3; simp)
        · by_cases h5 : a = 5
          · exact Or.inr (by subst h5; simp)
          · exact Or.inl (by simp [h3, h5, PSet.nat]) }

/-- info: [3, 5] -/
#guard_msgs in
#eval demo.support (fun n : Nat => n == 0) (fun x : Nat => by simp [PSet.nat])

/-! ## Axiom audit

These `#guard_msgs` run as part of `lake build`, so the constructivity claims
above are checked, not asserted.  `propext` and `Quot.sound` arrive from the
`List` lemmas, `simp`, and the quotient itself; the interesting entry is
`Classical.choice`, which appears in exactly the places predicted. -/

/-- info: 'FinSupp.FinMap₂.toFinMap₁' does not depend on any axioms -/
#guard_msgs in #print axioms FinMap₂.toFinMap₁

/-- info: 'FinSupp.FinMap₁.toFinMap₂_of_listable' does not depend on any axioms -/
#guard_msgs in #print axioms FinMap₁.toFinMap₂_of_listable

/-- info: 'FinSupp.TruncLift.untruncation' does not depend on any axioms -/
#guard_msgs in #print axioms TruncLift.untruncation

/-- info: 'FinSupp.strengthening_of_em' does not depend on any axioms -/
#guard_msgs in #print axioms strengthening_of_em

/-- info: 'FinSupp.Untruncation.subsingletonChoice' depends on axioms: [propext] -/
#guard_msgs in #print axioms Untruncation.subsingletonChoice

/-- info: 'FinSupp.Strengthening.em' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Strengthening.em

/-- info: 'FinSupp.FinMap₂.support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FinMap₂.support

/-- info: 'FinSupp.FinMap₁.toFinMap₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FinMap₁.toFinMap₂

/-- info: 'FinSupp.FinMap₁.support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FinMap₁.support

/-! ## Conclusions

**Definition 2 → definition 1: yes, constructively.**  `FinMap₂.toFinMap₁`,
with no axioms at all.  A `Prop` is a legitimate target for eliminating a
quotient, because any two proofs of it are equal.

**Definition 1 → definition 2: yes classically** (`FinMap₁.toFinMap₂`), and
the conversions are then mutually inverse, so the two definitions describe the
same thing up to a unique isomorphism.

**Definition 1 → definition 2: no, constructively**, for two independent
reasons, each identified exactly:

1. *The phrasing of finiteness.*  Definition 1 says "every non-nil key is
   listed"; the witness says "every key is nil-valued or listed".  Passing
   from the first to the second, in general, **is** excluded middle:
   `Strengthening.em` derives `em` from it and `strengthening_of_em` derives
   it from `em`.  This is a disproof in the usual sense — a constructive
   conversion would constructively prove `em`.  It is also avoidable: phrase
   definition 1's `Prop` disjunctively in the first place (as `FFP.FinMap`
   does in the main development, for exactly this reason) and this obstruction
   disappears.

2. *Escaping the `Prop`.*  Even in the disjunctive phrasing, `∃ l, Splits f l`
   is a `Prop` and `Trunc (Witness f)` is a `Type`.  That step is equivalent
   to subsingleton choice (`Untruncation.subsingletonChoice`,
   `SubsingletonChoice.untruncation`), equivalently to `TruncLift`.  This one
   cannot be *dis*proved inside Lean: `Classical.choice` proves it, so Lean
   cannot refute it, and "constructively unprovable" is a statement about
   Lean's type theory (`Prop` does not eliminate into `Type` except for
   subsingleton-eliminating inductives, and `Nonempty` is not one), not a
   statement in it.  Note that this obstruction is strictly weaker than full
   choice: `Trunc` only ever hands back information that every witness agrees
   on, so it cannot decide anything, and no taboo follows from it.

**Where it is constructive.**  If the key type is listable, the conversion is
constructive and the finiteness hypothesis is not even used
(`FinMap₁.toFinMap₂_of_listable`).  The obstruction is about infinite key
types, where no list can be produced without knowing which keys matter.

**Why the difference is not academic.**  Definition 2 is genuinely stronger
computationally: `FinMap₂.support` computes the exact support as data (the
`#eval` above prints `[3, 5]`), because the sweep it performs is the same for
every witness and therefore survives the quotient.  The identical function on
definition 1 routes through `Classical.choice` and Lean refuses to compile it
without `noncomputable`.  So the quotient in definition 2 destroys the
*particular* list while keeping everything invariant about it — which is more
than a `Prop` keeps, and exactly the gap the two obstructions above measure. -/

end FinSupp
