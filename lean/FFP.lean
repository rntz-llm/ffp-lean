/-
# Finite Functional Programming in Lean

A formalisation of the core of λFS from Arntzenius & Willsey, "Finite
Functional Programming, or, LAMBDA: The Ultimate Predicate":

* `FFP.Pointed`     — pointed sets, point preserving maps, finite maps (§2, fig. 1)
* `FFP.Syntax`      — types, contexts, intrinsically typed derivations (figs. 2, 4, 5)
* `FFP.Combinators` — the set comprehensions of figure 6 as finite-map combinators
* `FFP.Semantics`   — `⟦Γ ⊢ e : A⟧` and `⟦Γ/Δ/Ω ⊢ t : P⟧` (fig. 6)
* `FFP.Sugar`       — renaming of `Γ`, and figure 3's syntax sugar
* `FFP.Prims`       — figure 3's primitive functions as semantic values
* `FFP.Examples`    — the paper's example programs, evaluated
-/
import FFP.Pointed
import FFP.Syntax
import FFP.Combinators
import FFP.Semantics
import FFP.Sugar
import FFP.Prims
import FFP.Examples
