/-
A worked example, and the axiom audit that checks the constructivity claims.
-/
import FinSupp.Convert

namespace FinSupp

def PSet.nat : PSet := ⟨Nat, 0⟩

def demoFn : Nat → Nat := fun n => if n = 3 then 7 else if n = 5 then 2 else 0

/-- Witnessed by a deliberately sloppy list: junk keys and a gap. -/
def demo : FinMapWit Nat PSet.nat where
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

`propext` and `Quot.sound` come from `List` lemmas, `simp` and the quotient;
`Classical.choice` appears exactly where predicted. -/

/-- info: 'FinSupp.FinMapWit.toProp' does not depend on any axioms -/
#guard_msgs in #print axioms FinMapWit.toProp

/-- info: 'FinSupp.FinMapProp.toWit_of_listable' does not depend on any axioms -/
#guard_msgs in #print axioms FinMapProp.toWit_of_listable

/-- info: 'FinSupp.TruncLift.untruncation' does not depend on any axioms -/
#guard_msgs in #print axioms TruncLift.untruncation

/-- info: 'FinSupp.strengthening_of_em' does not depend on any axioms -/
#guard_msgs in #print axioms strengthening_of_em

/-- info: 'FinSupp.Untruncation.subsingletonChoice' depends on axioms: [propext] -/
#guard_msgs in #print axioms Untruncation.subsingletonChoice

/-- info: 'FinSupp.Strengthening.em' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Strengthening.em

/-- info: 'FinSupp.FinMapWit.support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FinMapWit.support

/-- info: 'FinSupp.FinMapProp.toWit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FinMapProp.toWit

/-- info: 'FinSupp.FinMapProp.support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FinMapProp.support

end FinSupp
