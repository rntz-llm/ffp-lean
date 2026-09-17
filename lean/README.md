# Lean scratch

Lean 4 (v4.34.0, via elan), no Mathlib.

Build with `lake build`; the `#guard_msgs` checks in `FFP/Examples.lean`
run as part of the build.

* `FFP/` — the core of λFS from Arntzenius & Willsey, *Finite Functional
  Programming* (see `FFP.lean` for a module map):
  intrinsically typed derivations for the typing rules of figure 4, and the
  denotational semantics of figure 6, as a runnable Lean function.  Finitely
  supported maps are functions carrying a list that bounds their support;
  point preserving maps are functions carrying a proof that they send `nil`
  to `nil`.  Defining the semantics requires establishing both properties for
  every rule, so the definition doubles as a proof of semantic finite support
  and point preservation.
