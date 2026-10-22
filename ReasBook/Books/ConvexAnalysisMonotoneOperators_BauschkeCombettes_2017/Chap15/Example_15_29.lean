/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_49
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-
Source/core/bridge triage:
- `source-facing`: Example 15.29 is the support-function saddle formula
  `inf_{x ∈ C} σ[D](Lx) = max_{v ∈ D} inf_{x ∈ C} ⟪Lx, v⟫`.
- `core/canonical`: the chapter owners are `innerInfimumOn`, `σ[C]`, and the composite Fenchel
  duality owners from Theorem 15.23.
- `bridge/view`: `innerInfimumOn_adjoint_eq_sInf_image` is the source-to-owner identification
  `inf_{x ∈ C} ⟪Lx, v⟫ = innerInfimumOn C (L.adjoint v)`, while the main theorem is the
  source-facing indicator/support-function specialization of the Chapter 15 owner theorem.
-/

-- Proof sketch: rewrite `innerInfimumOn C (L.adjoint v)` using
-- `innerInfimumOn_eq_sInf_image`, and then use the adjoint identity
-- `⟪x, L.adjoint v⟫ = ⟪L x, v⟫` to identify the image set.
/-- The dual inner infimum `innerInfimumOn C (L.adjoint v)` is exactly the infimum of the values
`⟪Lx, v⟫` over `x ∈ C`. -/
theorem innerInfimumOn_adjoint_eq_sInf_image
    (C : Set H) (L : H →L[ℝ] K) (v : K) :
    innerInfimumOn C (L.adjoint v) =
      sInf ((fun x : H ↦ (⟪L x, v⟫_ℝ : EReal)) '' C) := sorry

-- Proof sketch: apply Theorem 15.23 with `f = ι_C` and `g = σ[D]`, using Example 13.3(i) to
-- identify the conjugate of `ι_C` with `σ[C]` and Example 13.43(i) to identify the conjugate of
-- `σ[D]` with the indicator of the closed convex set `D`. The dual minimum over `D` is then the
-- negative of the maximal value of the owner functional
-- `v ↦ innerInfimumOn C (L.adjoint v)`, and the support-function formula rewrites the primal
-- infimum as `inf_{x ∈ C} sup_{v ∈ D} ⟪Lx, v⟫`.
/-- Example 15.29: if `C ⊆ H` and `D ⊆ K` are closed convex and
`0 ∈ sri (D - L '' C)`, then the primal value `inf_{x ∈ C} sup_{v ∈ D} ⟪Lx, v⟫` equals the
attained dual value `max_{v ∈ D} inf_{x ∈ C} ⟪Lx, v⟫`, written here as
`sInf ((fun x ↦ σ[D] (L x)) '' C)` and a maximizer of
`v ↦ innerInfimumOn C (L.adjoint v)` on `D`. -/
theorem exists_dualMaximizer_inf_inner_eq_inf_supportFunction_of_zero_mem_sri_sub_image
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (D - L '' C)) :
    ∃ v ∈ D, IsMaxOn (fun w : K ↦ innerInfimumOn C (L.adjoint w)) D v ∧
      sInf ((fun x : H ↦ σ[D] (L x)) '' C) = innerInfimumOn C (L.adjoint v) := sorry

end FenchelRockafellarDuality

end ERealFunction
