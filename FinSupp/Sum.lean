/-
Summing a finitely supported map into `(ℕ, +, 0)`.

With decidable key equality, definition 2's sum computes: deduplicate the
witness list (junk keys contribute 0, duplicates would be counted twice) and
add up.  Without it there is no sum at all — `Summation.wlem`.  Definition 1
has no sum either way: ℕ is not a subsingleton, so its `Prop` cannot be
eliminated into ℕ; `Classical.choice` supplies one, noncomputably.
-/
import FinSupp.Convert

namespace FinSupp

variable {A : Type}

def sumOver (f : A → Nat) : List A → Nat
  | [] => 0
  | a :: l => f a + sumOver f l

section
variable [DecidableEq A] (f : A → Nat)

def dedup : List A → List A
  | [] => []
  | a :: l => if a ∈ l then dedup l else a :: dedup l

theorem mem_dedup {x : A} : ∀ {l : List A}, x ∈ dedup l ↔ x ∈ l
  | [] => by simp [dedup]
  | a :: l => by
    by_cases h : a ∈ l <;> simp [dedup, h, @mem_dedup x l]
    rintro rfl; exact h

theorem nodup_dedup : ∀ l : List A, (dedup l).Nodup
  | [] => by simp [dedup]
  | a :: l => by
    by_cases h : a ∈ l
    · simpa [dedup, h] using nodup_dedup l
    · have : dedup (a :: l) = a :: dedup l := by simp [dedup, h]
      rw [this, List.nodup_cons]
      exact ⟨fun hm => h (mem_dedup.mp hm), nodup_dedup l⟩

theorem mem_erase_of_ne {x b : A} (hne : x ≠ b) : ∀ {l : List A}, x ∈ l → x ∈ l.erase b
  | c :: t, h => by
    by_cases hc : c = b
    · subst hc
      rw [List.erase_cons_head]
      exact (List.mem_cons.mp h).resolve_left hne
    · rw [show (c :: t).erase b = c :: t.erase b by simp [hc]]
      rcases List.mem_cons.mp h with rfl | h'
      · exact .head _
      · exact .tail _ (mem_erase_of_ne hne h')

theorem ne_of_mem_erase {x b : A} : ∀ {l : List A}, l.Nodup → x ∈ l.erase b → x ≠ b
  | c :: t, hn, h => by
    by_cases hc : c = b
    · subst hc
      rw [List.erase_cons_head] at h
      rintro rfl
      exact (List.nodup_cons.mp hn).1 h
    · rw [show (c :: t).erase b = c :: t.erase b by simp [hc]] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact hc
      · exact ne_of_mem_erase (List.nodup_cons.mp hn).2 h'

theorem sumOver_erase : ∀ {l : List A} {a : A}, a ∈ l →
    sumOver f l = f a + sumOver f (l.erase a)
  | b :: l, a, h => by
    by_cases hb : b = a
    · subst hb; simp [sumOver]
    · have ha : a ∈ l := by cases h with
        | head => exact absurd rfl hb
        | tail _ h => exact h
      have : (b :: l).erase a = b :: l.erase a := by simp [hb]
      rw [this]
      simp only [sumOver, sumOver_erase ha]
      omega

/-- Two duplicate-free lists sum alike when the elements of one that are
missing from the other are nil-valued. -/
theorem sumOver_eq : ∀ {l₂ l₁ : List A}, l₁.Nodup → l₂.Nodup →
    (∀ x ∈ l₁, x ∈ l₂) → (∀ x ∈ l₂, x ∉ l₁ → f x = 0) → sumOver f l₁ = sumOver f l₂
  | [], l₁, _, _, hsub, _ => by
    cases l₁ with
    | nil => rfl
    | cons a _ => exact absurd (hsub a (by simp)) (by simp)
  | b :: t, l₁, h₁, h₂, hsub, hz => by
    rw [List.nodup_cons] at h₂
    by_cases hb : b ∈ l₁
    · have hsub' : ∀ x ∈ l₁.erase b, x ∈ t := by
        intro x hx
        have hne : x ≠ b := ne_of_mem_erase h₁ hx
        exact ((List.mem_cons).mp (hsub x (List.mem_of_mem_erase hx))).resolve_left hne
      have hz' : ∀ x ∈ t, x ∉ l₁.erase b → f x = 0 := by
        intro x hx hnx
        refine hz x (List.mem_cons_of_mem _ hx) fun hxl => hnx ?_
        exact mem_erase_of_ne (fun he => h₂.1 (by rw [← he]; exact hx)) hxl
      rw [sumOver_erase f hb, sumOver_eq (l₁ := l₁.erase b) (h₁.erase b) h₂.2 hsub' hz']
      rfl
    · have hfb : f b = 0 := hz b (by simp) hb
      have hsub' : ∀ x ∈ l₁, x ∈ t := fun x hx =>
        ((List.mem_cons).mp (hsub x hx)).resolve_left (fun he => hb (he ▸ hx))
      rw [sumOver_eq (l₁ := l₁) h₁ h₂.2 hsub' (fun x hx hnx => hz x (List.mem_cons_of_mem _ hx) hnx)]
      simp [sumOver, hfb]

/-- Hence any two splitting lists agree after deduplication. -/
theorem sumOver_dedup_eq {l l' : List A} (s : ∀ a, f a = 0 ∨ a ∈ l)
    (s' : ∀ a, f a = 0 ∨ a ∈ l') : sumOver f (dedup l) = sumOver f (dedup l') := by
  have key : ∀ {m m' : List A}, (∀ a, f a = 0 ∨ a ∈ m) →
      sumOver f (dedup m) = sumOver f (dedup (m ++ m')) := by
    intro m m' hm
    refine sumOver_eq f (nodup_dedup _) (nodup_dedup _)
      (fun x hx => mem_dedup.mpr (List.mem_append_left _ (mem_dedup.mp hx))) ?_
    intro x _ hnx
    exact (hm x).resolve_right fun hxm => hnx (mem_dedup.mpr hxm)
  rw [key s (m' := l'), key s' (m' := l)]
  have swap : ∀ {m m' : List A} {x : A}, x ∈ dedup (m ++ m') → x ∈ dedup (m' ++ m) :=
    fun hx => mem_dedup.mpr (List.mem_append.mpr (List.mem_append.mp (mem_dedup.mp hx)).symm)
  exact sumOver_eq f (nodup_dedup _) (nodup_dedup _) (fun _ hx => swap hx)
    (fun _ hx hnx => absurd (swap hx) hnx)

end

/-- The sum of a version-2 map's outputs, computed. -/
def FinMapWit.sum [DecidableEq A] (F : FinMapWit A PSet.nat) : Nat :=
  F.wit.lift (fun w => sumOver F.fn (dedup w.supp))
    (fun w w' => sumOver_dedup_eq F.fn w.ok w'.ok)

/-- On a duplicate-free witness it is the plain list sum; that pins it down. -/
theorem FinMapWit.sum_eq [DecidableEq A] (F : FinMapWit A PSet.nat)
    (w : Witness (P := PSet.nat) F.fn) (hw : w.supp.Nodup) : F.sum = sumOver F.fn w.supp := by
  obtain ⟨fn, wit⟩ := F
  rw [show wit = Trunc.mk w from Trunc.eq _ _]
  exact sumOver_eq fn (nodup_dedup _) hw (fun _ h => mem_dedup.mp h)
    (fun _ hx hnx => absurd (mem_dedup.mpr hx) hnx)

/-! ## Without decidable key equality there is no sum

A summation operator need only agree with the list sum on duplicate-free
witnesses.  Even so it decides, for every `q`, whether `q` is refutable. -/

structure Summation where
  sum : ∀ A : Type, FinMapWit A PSet.nat → Nat
  spec : ∀ (A : Type) (f : A → Nat) (w : Witness (P := PSet.nat) f), w.supp.Nodup →
    sum A ⟨f, Trunc.mk w⟩ = sumOver f w.supp

/-- `Bool` with `true` and `false` identified exactly when `q` holds. -/
def collapse (q : Prop) : Type := Quot (fun x y : Bool => x = y ∨ q)

namespace collapse
variable {q : Prop}

def mk (b : Bool) : collapse q := Quot.mk _ b

theorem eq_of (hq : q) : (mk true : collapse q) = mk false := Quot.sound (Or.inr hq)

/-- `mk true ↦ True`, `mk false ↦ q`; well defined since `q` collapses them. -/
def probe (q : Prop) : collapse q → Prop :=
  Quot.lift (fun b => cond b True q) (by
    rintro x y (rfl | hq)
    · rfl
    · have hq' : q = True := propext ⟨fun _ => trivial, fun _ => hq⟩
      cases x <;> cases y <;> simp [hq'])

theorem of_eq (h : (mk true : collapse q) = mk false) : q := by
  have hq : True = q := congrArg (probe q) h
  rw [← hq]; trivial

theorem mem_pair (a : collapse q) : a ∈ [(mk true : collapse q), mk false] := by
  induction a using Quot.ind
  next b => cases b
            · exact .tail _ (.head _)
            · exact .head _

theorem eq_true_of (hq : q) (a : collapse q) : a = mk true := by
  induction a using Quot.ind
  next b => cases b
            · exact (eq_of hq).symm
            · rfl

end collapse

theorem Summation.wlem (S : Summation) (q : Prop) : ¬q ∨ ¬¬q := by
  let f : collapse q → Nat := fun _ => 1
  let w : Witness (P := PSet.nat) f :=
    ⟨[collapse.mk true, collapse.mk false], fun a => Or.inr (collapse.mem_pair a)⟩
  have h1 : q → S.sum _ ⟨f, Trunc.mk w⟩ = 1 := by
    intro hq
    let w₁ : Witness (P := PSet.nat) f :=
      ⟨[collapse.mk true], fun a => Or.inr (by simp [collapse.eq_true_of hq a])⟩
    rw [show Trunc.mk w = Trunc.mk w₁ from Trunc.eq _ _]
    exact S.spec _ f w₁ (List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩)
  have h2 : ¬q → S.sum _ ⟨f, Trunc.mk w⟩ = 2 := by
    intro hnq
    have hne : (collapse.mk true : collapse q) ≠ collapse.mk false :=
      fun h => hnq (collapse.of_eq h)
    rw [S.spec _ f w (List.nodup_cons.mpr
      ⟨by simpa using hne, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩)]
    rfl
  by_cases h : S.sum _ ⟨f, Trunc.mk w⟩ = 1
  · exact Or.inr fun hn => by have := h2 hn; omega
  · exact Or.inl fun hq => h (h1 hq)

/-- Definition 1's sum exists only classically. -/
noncomputable def FinMapProp.sum [DecidableEq A] (F : FinMapProp A PSet.nat) : Nat :=
  F.toWit.sum

theorem FinMapProp.sum_eq [DecidableEq A] (F : FinMapProp A PSet.nat)
    (w : Witness (P := PSet.nat) F.fn) (hw : w.supp.Nodup) : F.sum = sumOver F.fn w.supp :=
  FinMapWit.sum_eq F.toWit w hw

end FinSupp
