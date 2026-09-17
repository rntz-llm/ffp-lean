/-
Commutativity of addition, proved from scratch.

No Mathlib: this file uses only Lean 4's built-in prelude. The natural
numbers and their addition are defined here rather than imported, so the
proof does not lean on any pre-existing arithmetic lemmas.
-/

namespace Scratch

/-- Peano naturals. -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

/-- Addition by structural recursion on the second argument. -/
def add : MyNat → MyNat → MyNat
  | n, .zero   => n
  | n, .succ m => .succ (add n m)

theorem zero_add : ∀ n : MyNat, add .zero n = n
  | .zero   => rfl
  | .succ m => congrArg succ (zero_add m)

theorem succ_add : ∀ n m : MyNat, add (.succ n) m = .succ (add n m)
  | _, .zero   => rfl
  | n, .succ k => congrArg succ (succ_add n k)

/-- Commutativity of addition, by induction on the second argument. -/
theorem add_comm : ∀ n m : MyNat, add n m = add m n
  | n, .zero   => (zero_add n).symm
  | n, .succ k => (congrArg succ (add_comm n k)).trans (succ_add k n).symm

end MyNat
end Scratch
