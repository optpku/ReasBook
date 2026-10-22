/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Definition_19_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Definition_19_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section SecondVariable

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- For fixed `x`, the Lagrangian fiber in the second variable is the negative Fenchel conjugate of
the slice `y ↦ F (x, y)`. -/
theorem lagrangian_eq_neg_conjugate_second_variable_slice
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) :
    ℒ[F] x = fun v ↦ -((fun y : K ↦ (F (x, y) : EReal))∗ v) :=
  sorry

-- Proof sketch: use `lagrangian_eq_neg_conjugate_second_variable_slice` and the standard
-- regularity of Fenchel conjugates; the concavity statement is recorded through convexity of the
-- negated fiber in the chapter's extended-real owner language.
/-- Proposition 19.17 (1): clause (i). For every `x`, the fiber `v ↦ ℒ[F] x v` is upper
semicontinuous and concave, expressed canonically as convexity of its negation.
-/
theorem lagrangian_upperSemicontinuous_and_concave_in_second_variable
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) :
    UpperSemicontinuous (ℒ[F] x) ∧
      IsConvex (fun v ↦ -(ℒ[F] x v)) :=
  sorry

end SecondVariable

section PrimalValue

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: apply the Fenchel--Moreau theorem to the slice `y ↦ F (x, y)` and then evaluate
-- the resulting identity at `0`.
/-- Proposition 19.17 (2): clause (ii), at the correct slice-local abstraction level. If the
second-variable slice `y ↦ F (x, y)` belongs to `Γ₀(K)`, then the supremum of the Lagrangian fiber
at `x` recovers the primal objective value `perturbationPrimalObjective F x = F (x, 0)`. -/
theorem lagrangian_sSup_eq_perturbationPrimalObjective_of_slice_mem_gammaZero
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H)
    (hx : (fun y : K ↦ F (x, y)) ∈ Γ₀(K)) :
    sSup (Set.range (ℒ[F] x)) = perturbationPrimalObjective F x := sorry

section Product

variable [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]

-- Proof sketch: derive `Γ₀(K)` for the fixed slice `y ↦ F (x, y)` from `hF : F ∈ Γ₀(H × K)`, then
-- apply the slice-local form of clause (ii).
/-- Companion source-global form of Proposition 19.17 (2): if `F ∈ Γ₀(H × K)`, then the fixed
slice theorem applies at every `x`. -/
theorem lagrangian_sSup_eq_perturbationPrimalObjective_of_mem_gammaZero
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) :
    sSup (Set.range (ℒ[F] x)) = perturbationPrimalObjective F x := sorry

end Product

end PrimalValue

section FirstVariable

variable {H : Type u} {K : Type v}
variable [AddCommGroup H] [Module ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

-- Proof sketch: for fixed `v`, the perturbation `(x, y) ↦ F (x, y) - ⟪y, v⟫` is convex whenever
-- `F` is convex, and Proposition 8.35 identifies the infimum over `y` with the canonical
-- extended-real convex marginal.
/-- Proposition 19.17 (3): clause (iii). If `F` is convex on `H × K`, then for every `v`, the
fiber `x ↦ ℒ[F] x v` is convex on `H`. -/
theorem lagrangian_convex_in_first_variable
    (F : H × K → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn F Set.univ) (v : K) :
    IsConvex (fun x : H ↦ ℒ[F] x v) := sorry

end FirstVariable

section DualValue

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

-- Proof sketch: unfold `lagrangian`, interchange the two suprema over `x` and `y`, and recognize
-- the resulting expression as the dual objective `perturbationDualObjective F v = F^*(0, v)`.
/-- Proposition 19.17 (4): clause (iv). For every `v`, the infimum of the Lagrangian fiber over
`H` is the negative dual objective value `- perturbationDualObjective F v = -F^*(0, v)`. -/
theorem lagrangian_sInf_eq_neg_perturbationDualObjective
    (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) :
    sInf (Set.range fun x ↦ ℒ[F] x v) = -perturbationDualObjective F v := sorry

end DualValue

end ERealFunction
