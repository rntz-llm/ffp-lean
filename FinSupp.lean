/-
# Finitely supported maps into a pointed set: two definitions

Independent of the `FFP` development.  A pointed set here is a set with *one*
distinguished element, not `FFP.PSet`, whose `IsNil` predicate admits many.

* `FinMap₁`: a function plus a `Prop` saying its support is finite.
* `FinMap₂`: a function plus a witness — a list bounding the support —
  quotiented so all witnesses are equal.

Answers: `₂ → ₁` constructively; `₁ → ₂` only classically, and then the two are
isomorphic.  Constructively `₁ → ₂` fails for two independent reasons.
The phrasing gap, `Covers → Splits`, is *equivalent to excluded middle*, so
that half is disproved.  Escaping the `Prop` is *equivalent to subsingleton
choice*, which `Classical.choice` proves, so Lean can neither prove it
constructively nor refute it.  Both obstructions vanish for listable key types.
Definition 2 is also strictly more useful: it computes the support, and
definition 1 cannot.

Examples and the axiom audit are at the bottom.
-/

namespace FinSupp

/-- A pointed set: a set with a distinguished element.  "Is `x` nil?" is `x = nil`. -/
structure PSet where
  carrier : Type
  nil : carrier

def PSet.option (A : Type) : PSet := ⟨Option A, none⟩

/-- `Prop` pointed at `True`; used to extract excluded middle. -/
def PSet.prop : PSet := ⟨Prop, True⟩

variable {A : Type} {P : PSet}

/-- `l` covers the support: everything non-nil is listed. -/
def Covers (f : A → P.carrier) (l : List A) : Prop := ∀ a, f a ≠ P.nil → a ∈ l

/-- `l` splits the domain: every input is nil-valued or listed.  Constructively
stronger than `Covers`. -/
def Splits (f : A → P.carrier) (l : List A) : Prop := ∀ a, f a = P.nil ∨ a ∈ l

theorem Covers.of_splits {f : A → P.carrier} {l} (h : Splits f l) : Covers f l :=
  fun a ha => (h a).resolve_left ha

/-- **Definition 1.** -/
structure FinMap₁ (A : Type) (P : PSet) where
  fn : A → P.carrier
  finite : ∃ l, Covers fn l

/-- Proof irrelevance: version 1 is a subsingleton over `fn`. -/
theorem FinMap₁.ext {F G : FinMap₁ A P} (h : F.fn = G.fn) : F = G := by
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

/-- **Definition 2.** -/
structure FinMap₂ (A : Type) (P : PSet) where
  fn : A → P.carrier
  wit : Trunc (Witness fn)

/-- The quotient has one element: version 2 is a subsingleton over `fn` too. -/
theorem FinMap₂.ext {F G : FinMap₂ A P} (h : F.fn = G.fn) : F = G := by
  cases F; cases G; cases h; exact congrArg _ (Trunc.eq _ _)

/-! ## Definition 2 → 1, constructively

A quotient may always be eliminated into a `Prop`. -/

def FinMap₂.toFinMap₁ (F : FinMap₂ A P) : FinMap₁ A P where
  fn := F.fn
  finite := F.wit.lift (fun w => ⟨w.supp, Covers.of_splits w.ok⟩) (fun _ _ => rfl)

/-! ## Obstruction 1: the phrasing is exactly excluded middle -/

def Strengthening : Prop :=
  ∀ (A : Type) (P : PSet) (f : A → P.carrier), (∃ l, Covers f l) → (∃ l, Splits f l)

theorem strengthening_of_em (em : ∀ q : Prop, q ∨ ¬q) : Strengthening := by
  rintro A P f ⟨l, hl⟩
  exact ⟨l, fun a => (em (f a = P.nil)).imp id (fun hne => hl a hne)⟩

theorem le_foldr_max : ∀ (l : List Nat) (m : Nat), m ∈ l → m ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro m hm; cases hm
  | cons a t ih =>
    intro m hm
    cases hm with
    | head => simp only [List.foldr_cons]; omega
    | tail _ h => have := ih m h; simp only [List.foldr_cons]; omega

theorem exists_not_mem (l : List Nat) : ∃ n, n ∉ l :=
  ⟨l.foldr max 0 + 1, fun hm => by have := le_foldr_max l _ hm; omega⟩

/-- Conversely: on `Prop` pointed at `True`, the constant map `q` on `Nat` keys
is covered by `[]` as soon as `¬¬q`, but a splitting list misses some `n` and
must report `q = True` there. -/
theorem Strengthening.dne (h : Strengthening) (q : Prop) (hq : ¬¬q) : q := by
  have ne_true : q ≠ True → ¬q := fun hne hqq => hne (propext ⟨fun _ => trivial, fun _ => hqq⟩)
  have covers : ∃ l : List Nat, Covers (P := PSet.prop) (fun _ => q) l :=
    ⟨[], fun _ ha => absurd (ne_true ha) hq⟩
  obtain ⟨l, hl⟩ := h Nat PSet.prop (fun _ => q) covers
  obtain ⟨n, hn⟩ := exists_not_mem l
  have : q = True := (hl n).resolve_right hn
  rw [this]; trivial

theorem Strengthening.em (h : Strengthening) (q : Prop) : q ∨ ¬q :=
  h.dne _ fun hn => hn (Or.inr fun hq => hn (Or.inl hq))

/-! ## Obstruction 2: escaping the `Prop` is exactly subsingleton choice

Even granted the disjunctive phrasing, `∃ l, Splits f l` is a `Prop` and
`Trunc (Witness f)` a `Type`.  The cycle below shows that step is equivalent to
subsingleton choice; `Classical.choice` proves the latter, so none of these can
be refuted here. -/

def Untruncation : Type 1 :=
  ∀ (A : Type) (P : PSet) (f : A → P.carrier), (∃ l, Splits f l) → Trunc (Witness f)

def SubsingletonChoice : Type 1 := ∀ α : Type, Subsingleton α → Nonempty α → α

def TruncLift : Type 1 := ∀ α : Type, Nonempty α → Trunc α

theorem Witness.supp_ne_nil {α : Type} (hne : Nonempty α)
    (w : Witness (P := PSet.option Unit) (fun _ : α => some ())) : w.supp ≠ [] := by
  intro hnil
  refine hne.elim fun a => ?_
  rcases w.ok a with h | h
  · simp [PSet.option] at h
  · rw [hnil] at h; cases h

/-- The constant `some ()` on a subsingleton `α` has all of `α` as support, so a
witness must list an element of `α` — and `α` being a subsingleton is what lets
us read it back out of the quotient. -/
def Untruncation.subsingletonChoice (conv : Untruncation) : SubsingletonChoice := by
  intro α hss hne
  have hsplit : ∃ l, Splits (P := PSet.option Unit) (fun _ : α => some ()) l :=
    hne.elim fun a₀ => ⟨[a₀], fun a => Or.inr (by rw [Subsingleton.elim a a₀]; simp)⟩
  exact (conv α (PSet.option Unit) (fun _ => some ()) hsplit).lift
    (fun w => w.supp.head (Witness.supp_ne_nil hne w))
    (fun _ _ => Subsingleton.elim _ _)

def SubsingletonChoice.truncLift (sc : SubsingletonChoice) : TruncLift :=
  fun α hne => sc (Trunc α) inferInstance (hne.elim fun a => ⟨Trunc.mk a⟩)

def TruncLift.untruncation (tl : TruncLift) : Untruncation :=
  fun _ _ f h => tl (Witness f) (nonempty_witness_iff.mpr h)

/-! ## Definition 1 → 2, classically

`Classical.em` supplies the disjunction, `Classical.choice` the witness. -/

theorem Splits.of_covers {f : A → P.carrier} {l} (h : Covers f l) : Splits f l :=
  fun a => (Classical.em (f a = P.nil)).imp id (fun hne => h a hne)

noncomputable def FinMap₁.toFinMap₂ (F : FinMap₁ A P) : FinMap₂ A P where
  fn := F.fn
  wit := Trunc.mk (Classical.choice
    (nonempty_witness_iff.mpr (F.finite.elim fun l hl => ⟨l, Splits.of_covers hl⟩)))

/-- Mutually inverse, and by the two `ext` lemmas this is the only isomorphism
over `fn`. -/
theorem FinMap₁.toFinMap₂_toFinMap₁ (F : FinMap₁ A P) : F.toFinMap₂.toFinMap₁ = F :=
  FinMap₁.ext rfl

theorem FinMap₂.toFinMap₁_toFinMap₂ (F : FinMap₂ A P) : F.toFinMap₁.toFinMap₂ = F :=
  FinMap₂.ext rfl

/-! ## Listable key types: constructive, and no hypothesis needed -/

structure Listable (A : Type) where
  elems : List A
  complete : ∀ a, a ∈ elems

def Listable.witness (L : Listable A) (f : A → P.carrier) : Witness f where
  supp := L.elems
  ok a := Or.inr (L.complete a)

def FinMap₁.toFinMap₂_of_listable (L : Listable A) (F : FinMap₁ A P) : FinMap₂ A P where
  fn := F.fn
  wit := Trunc.mk (L.witness F.fn)

/-! ## Computing the support

Over `Nat` keys with a boolean nil-test, sweeping `0 … max(witness list)` gives
the same list for every witness, so it survives the quotient.  The same function
on definition 1 must go through `Classical.choice` and is `noncomputable`. -/

section Support

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

def bound (f : Nat → P.carrier) (w : Witness f) : Nat := w.supp.foldr max 0 + 1

theorem lt_bound (f : Nat → P.carrier) (w : Witness f) (n : Nat) (hn : f n ≠ P.nil) :
    n < bound f w :=
  Nat.lt_succ_of_le (le_foldr_max _ _ ((w.ok n).resolve_left hn))

theorem upTo_bound_eq (isNil : P.carrier → Bool) (hIsNil : ∀ x, isNil x = true ↔ x = P.nil)
    (f : Nat → P.carrier) (w w' : Witness f) :
    upTo isNil f (bound f w) = upTo isNil f (bound f w') := by
  rcases Nat.le_total (bound f w) (bound f w') with h | h
  · exact (upTo_eq_of_le isNil hIsNil f (lt_bound f w) _ h).symm
  · exact upTo_eq_of_le isNil hIsNil f (lt_bound f w') _ h

end Support

/-- The exact support of a version-2 map, computed. -/
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

/-- Same list, same spec, from definition 1.  Dropping `noncomputable` is a
compile error. -/
noncomputable def FinMap₁.support (F : FinMap₁ Nat P) (isNil : P.carrier → Bool)
    (hIsNil : ∀ x, isNil x = true ↔ x = P.nil) : List Nat :=
  F.toFinMap₂.support isNil hIsNil

theorem FinMap₁.mem_support (F : FinMap₁ Nat P) (isNil : P.carrier → Bool)
    (hIsNil : ∀ x, isNil x = true ↔ x = P.nil) (n : Nat) :
    n ∈ F.support isNil hIsNil ↔ F.fn n ≠ P.nil :=
  FinMap₂.mem_support F.toFinMap₂ isNil hIsNil n

/-! ## Example -/

def PSet.nat : PSet := ⟨Nat, 0⟩

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

Checked at build time.  `propext` and `Quot.sound` come from `List` lemmas,
`simp` and the quotient; `Classical.choice` appears exactly where predicted. -/

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

end FinSupp
