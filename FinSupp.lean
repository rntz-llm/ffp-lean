/-
# Finitely supported maps into a pointed set: two definitions

Standalone; shares nothing with the `FFP` development.

* `FinSupp.Defs`    — pointed sets, `FinMapProp` (a proof of finite support),
                      `FinMapWit` (a witness, quotiented so all are equal)
* `FinSupp.Convert` — how the two relate, and what separates them
* `FinSupp.Examples`— a worked example, and the axiom audit

`Wit → Prop` is constructive.  `Prop → Wit` needs classical logic, for two
independent reasons: the phrasing gap is equivalent to excluded middle, and
escaping the `Prop` is equivalent to subsingleton choice.  Both vanish for
listable key types.  Only `FinMapWit` computes its support.
-/
import FinSupp.Defs
import FinSupp.Convert
import FinSupp.Examples
