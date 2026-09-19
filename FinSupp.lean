/-
# Finitely supported maps into a pointed set: two definitions

Standalone; shares nothing with the `FFP` development.

* `FinSupp.Defs`    — pointed sets, `FinMapProp` (a proof of finite support),
                      `FinMapWit` (a witness, quotiented so all are equal)
* `FinSupp.Convert` — how the two relate, and what separates them
* `FinSupp.Sum`     — summing a map into `(ℕ, +, 0)`
* `FinSupp.Examples`— a worked example, and the axiom audit

`Wit → Prop` is constructive.  `Prop → Wit` needs classical logic, for two
independent reasons: the phrasing gap is equivalent to excluded middle, and
escaping the `Prop` is equivalent to subsingleton choice.  Both vanish for
listable key types.  Only `FinMapWit` computes its support.

Summing a map into `(ℕ, +, 0)` needs decidable equality of *keys* — with it
`FinMapWit.sum` computes, without it `Summation.wlem` rules any sum out, and
`Summation.ofWLEM` builds one back from weak excluded middle, so for ℕ that is
the exact strength.  `FinMapWit.sum` never tests values for equality, so it
generalises to any commutative monoid; the converse does not, as it needs
`¬¬`-stable equality on values.
-/
import FinSupp.Defs
import FinSupp.Convert
import FinSupp.Sum
import FinSupp.Examples
