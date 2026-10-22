/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A1.ClosedConvex

public section

universe u

variable {H₁ : Type u} [TopologicalSpace H₁] [AddCommMonoid H₁] [Module ℝ H₁]

/- Assumption A1 (1). The closed-subset clause of the feasible-set assumption is formalized in
Lean by the canonical predicate `IsClosed C` for `C : Set H₁`. -/
#check IsClosed

/- Assumption A1 (2). The convex-subset clause of the feasible-set assumption is formalized in
Lean by the canonical predicate `Convex ℝ C` for `C : Set H₁`. -/
#check Convex

/- Assumption A1. The combined feasible-set hypothesis used later in the chapter is packaged by
the source-facing companion predicate `Set.ClosedConvex C`. -/
#check Set.ClosedConvex
