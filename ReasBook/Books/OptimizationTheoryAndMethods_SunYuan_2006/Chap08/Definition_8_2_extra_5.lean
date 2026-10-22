/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_1_extra_1

section Chapter08Definition82Extra5

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

-- Domain-style sampling:
-- * primary domain: convex analysis of constrained feasible sets
-- * sampled owner declarations:
--   `ConstrainedOptimizationProblem.feasibleSet`,
--   `ConvexOn`,
--   `Convex.affine_preimage`,
--   `ConcaveOn.convex_ge`
-- * owner abstraction: `ConstrainedOptimizationProblem` carries the primitive objective and
--   constraints, while convex programming is the bridge
--   `ConvexOn ℝ problem.feasibleSet problem.objective`
-- * primitive data: the objective, the constraint family, and the equality/inequality index sets
-- * derived API: `problem.feasibleSet`, its convexity under linear/concave hypotheses, and
--   `problem.IsConvexProgramming`
-- Layer triage:
-- * source-facing: `ConstrainedOptimizationProblem.IsConvexProgramming`
-- * core/canonical: `ConvexOn ℝ Ω f`
-- * bridge/view: `problem.IsConvexProgramming ↔ ConvexOn ℝ problem.feasibleSet problem.objective`

/- Chapter08 Definition 8.2-extra-5 (1): the source notion “minimize `f` over `Ω` as a convex
program” is the canonical convex-analysis owner `ConvexOn ℝ Ω f`. -/
#check (ConvexOn ℝ : Set Point → (Point → ℝ) → Prop)

namespace ConstrainedOptimizationProblem

/-- Chapter08 Definition 8.2-extra-5 (1), constrained-problem form: `problem` is a convex
programming problem when `problem.objective` is convex on `problem.feasibleSet`. -/
abbrev IsConvexProgramming (problem : _root_.ConstrainedOptimizationProblem n m E I) : Prop :=
  ConvexOn ℝ problem.feasibleSet problem.objective

/-- `problem.IsConvexProgramming` means that `problem.objective` is convex on
`problem.feasibleSet`. -/
theorem isConvexProgramming_iff
    (problem : _root_.ConstrainedOptimizationProblem n m E I) :
    problem.IsConvexProgramming ↔ ConvexOn ℝ problem.feasibleSet problem.objective :=
  Iff.rfl

/-- Chapter08 Definition 8.2-extra-5 (2): if each equality constraint of `problem` is affine and
each inequality constraint is concave, then the feasible set `problem.feasibleSet` is convex. -/
theorem convex_feasibleSet_of_eq_affine_of_ineq_concave
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (h_eq : ∀ i ∈ E, ∃ c : Point →ᵃ[ℝ] ℝ, problem.constraint i = c)
    (h_ineq : ∀ i ∈ I, ConcaveOn ℝ Set.univ (problem.constraint i)) :
    Convex ℝ problem.feasibleSet := by
  let eqSet : Fin m → Set Point := fun i ↦ problem.constraint i ⁻¹' ({0} : Set ℝ)
  let ineqSet : Fin m → Set Point := fun i ↦ {x | 0 ≤ problem.constraint i x}
  have h_eqSet : ∀ i, ∀ hi : i ∈ E, Convex ℝ (eqSet i) := by
    intro i hi
    rcases h_eq i hi with ⟨c, hc⟩
    simpa [eqSet, hc] using
      (convex_singleton (0 : ℝ)).affine_preimage c
  have h_ineqSet : ∀ i, ∀ hi : i ∈ I, Convex ℝ (ineqSet i) := by
    intro i hi
    simpa [ineqSet] using (h_ineq i hi).convex_ge (0 : ℝ)
  have h_eqInter : Convex ℝ (⋂ i ∈ E, eqSet i) :=
    convex_iInter₂ h_eqSet
  have h_ineqInter : Convex ℝ (⋂ i ∈ I, ineqSet i) :=
    convex_iInter₂ h_ineqSet
  have h_feasibleSet :
      problem.feasibleSet = (⋂ i ∈ E, eqSet i) ∩ ⋂ i ∈ I, ineqSet i := by
    ext x
    simp [ConstrainedOptimizationProblem.feasibleSet, eqSet, ineqSet]
  simpa [h_feasibleSet] using h_eqInter.inter h_ineqInter

/-- Chapter08 Definition 8.2-extra-5 (3): if the objective of `problem` is convex, each equality
constraint is affine, and each inequality constraint is concave, then `problem` is a convex
programming problem. -/
theorem isConvexProgramming_of_convexOn_of_eq_affine_of_ineq_concave
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (h_objective : ConvexOn ℝ Set.univ problem.objective)
    (h_eq : ∀ i ∈ E, ∃ c : Point →ᵃ[ℝ] ℝ, problem.constraint i = c)
    (h_ineq : ∀ i ∈ I, ConcaveOn ℝ Set.univ (problem.constraint i)) :
    problem.IsConvexProgramming := by
  change ConvexOn ℝ problem.feasibleSet problem.objective
  exact h_objective.subset (by simp) <|
    convex_feasibleSet_of_eq_affine_of_ineq_concave problem h_eq h_ineq

end ConstrainedOptimizationProblem

end Chapter08Definition82Extra5
