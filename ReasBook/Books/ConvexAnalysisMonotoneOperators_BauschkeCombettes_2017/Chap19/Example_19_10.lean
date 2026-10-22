/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_5

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section NonemptyBridge

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

-- Proof sketch: membership in `sri (L '' C - D)` implies membership in `L '' C - D`, so
-- `0 = L x - d` for some `x ∈ C` and `d ∈ D`; in particular `x` witnesses `C.Nonempty`.
private theorem nonempty_of_zero_mem_sri_image_sub_left
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (L '' C - D)) :
    C.Nonempty := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨Lx, hLx, _, _, _⟩
  rcases hLx with ⟨x, hx, _⟩
  exact ⟨x, hx⟩

end NonemptyBridge

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Example 19.10 is the constrained best-approximation problem on
  `C ∩ L ⁻¹' D`.
- `core/canonical`: the owner theorem is
  `argmin_proximalCompositeDual_nonempty_and_argmin_primal_eq_singleton_proximityOperator`.
- `bridge/view`: specialize the owner theorem to `φ = ι[C]` and `ψ = ι[D]`, then rewrite the
  resulting proximity operator as the metric projection `P[C, hC]` and the conjugate of `ι[D]`
  as the support function `σ[D]`.
-/

variable {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable {D : Set K} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
variable (z : H) (L : H →L[ℝ] K)
variable (hsri : (0 : K) ∈ sri (L '' C - D))

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex
    (nonempty_of_zero_mem_sri_image_sub_left C D L hsri) hC_closed hC_convex

local notation "P_C" => P[C, hC_cheb]

-- Proof sketch: apply Proposition 19.5 with `φ = ι_C`, `ψ = ι_D`, and `r = 0`. Rewrite the dual
-- objective by the indicator Moreau-envelope formula and the conjugate of an indicator as a
-- support function. Then identify the proximal point of `ι_C` with the metric projection onto
-- `C`, and use that minimizing `‖x - z‖` over the feasible set is equivalent to minimizing
-- `(1 / 2) ‖x - z‖²`.
/-- Example 19.10: if `C` and `D` are closed convex subsets of real Hilbert spaces and
`0 ∈ sri (L(C) - D)`, then the dual problem
`v ↦ (1 / 2) ‖z - L^* v‖² - (1 / 2) d_C(z - L^* v)² + σ[D] v` has a solution; moreover, for every
dual solution `v`, the unique minimizer of `‖x - z‖` over `x ∈ C` with `L x ∈ D` is
`P_C (z - L^* v)`. -/
theorem argmin_bestApproximationDual_nonempty_and_argminOn_norm_eq_singleton_projectionPoint :
    (Argmin
      (fun v : K ↦
        ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
          ((((1 / 2 : ℝ) * (Metric.infDist (z - L.adjoint v) C) ^ 2 : ℝ) : EReal))) +
            σ[D] v)).Nonempty ∧
      ∀ {v : K},
        v ∈
            Argmin
              (fun v : K ↦
                ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
                  ((((1 / 2 : ℝ) * (Metric.infDist (z - L.adjoint v) C) ^ 2 : ℝ) : EReal))) +
                    σ[D] v) →
        Argmin[C ∩ L ⁻¹' D] (fun x : H ↦ ‖x - z‖) =
          ({P_C (z - L.adjoint v)} : Set H) := sorry

end PrimalSolutionsViaDualSolutions

end ERealFunction
