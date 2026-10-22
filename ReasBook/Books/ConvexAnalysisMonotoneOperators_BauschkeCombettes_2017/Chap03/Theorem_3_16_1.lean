/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] in
/-- Helper for Theorem 3.16.1: a point of `C` whose norm distance realizes the subtype infimum is a
best approximation in the project API. -/
private theorem isBestApproximation_of_mem_and_norm_eq_iInf {C : Set 𝓗} {x p : 𝓗}
    (hpC : p ∈ C) (hpmin : ‖x - p‖ = ⨅ y : C, ‖x - y‖) : IsBestApproximation x C p := by
  constructor
  · exact hpC
  -- Rewrite the project distance to a set as the subtype infimum from mathlib's minimizer theorem.
  rw [Metric.infDist_eq_iInf]
  simpa [dist_eq_norm] using hpmin

/-- Helper for Theorem 3.16.1: the Hilbert-space projection theorem supplies at least one best
approximation in every nonempty closed convex set. -/
private theorem exists_isBestApproximation_of_nonempty_isClosed_convex {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ∀ x : 𝓗, ∃ p : 𝓗, IsBestApproximation x C p := by
  intro x
  -- Apply the complete-convex minimizer theorem and translate its conclusion to `IsBestApproximation`.
  rcases exists_norm_eq_iInf_of_complete_convex hC_nonempty hC_closed.isComplete hC_convex x with
    ⟨p, hpC, hpmin⟩
  refine ⟨p, ?_⟩
  exact isBestApproximation_of_mem_and_norm_eq_iInf hpC hpmin

omit [CompleteSpace 𝓗] in
/-- Helper for Theorem 3.16.1: convexity forces two best approximations to coincide. -/
private theorem eq_of_isBestApproximation_of_convex {C : Set 𝓗} (hC_convex : Convex ℝ C)
    {x p q : 𝓗}
    (hp : IsBestApproximation x C p) (hq : IsBestApproximation x C q) : p = q := by
  have hpmin : ‖x - p‖ = ⨅ y : C, ‖x - y‖ := by
    simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hp.2
  have hqmin : ‖x - q‖ = ⨅ y : C, ‖x - y‖ := by
    simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hq.2
  have hp_inner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mp hpmin q hq.1
  have hq_inner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hq.1).mp hqmin p hp.1
  have hq_inner' : 0 ≤ ⟪x - q, q - p⟫_ℝ := by
    rw [show q - p = -(p - q) by abel, inner_neg_right]
    exact neg_nonneg.mpr hq_inner
  have hp_expand :
      ⟪x - p, q - p⟫_ℝ = ⟪x - q, q - p⟫_ℝ + ‖q - p‖ ^ 2 := by
    calc
      ⟪x - p, q - p⟫_ℝ = ⟪(x - q) + (q - p), q - p⟫_ℝ := by
        congr 1
        abel
      _ = ⟪x - q, q - p⟫_ℝ + ⟪q - p, q - p⟫_ℝ := by rw [inner_add_left]
      _ = ⟪x - q, q - p⟫_ℝ + ‖q - p‖ ^ 2 := by rw [real_inner_self_eq_norm_sq, sq]
  have hpq_sq : ‖q - p‖ ^ 2 ≤ 0 := by
    rw [hp_expand] at hp_inner
    nlinarith
  have hpq_eq : q - p = 0 := by
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp <| le_antisymm hpq_sq (sq_nonneg ‖q - p‖)
  exact (sub_eq_zero.mp hpq_eq).symm

-- Proof sketch: combine the Hilbert projection theorem for existence with the convex minimizer
-- characterization for uniqueness.
/-- Theorem 3.16.1: every nonempty closed convex subset of a real Hilbert space is a Chebyshev
set, equivalently each point has a unique nearest point in the set. -/
theorem isChebyshev_of_nonempty_isClosed_convex {C : Set 𝓗} (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    IsChebyshev C := by
  intro x
  rcases exists_isBestApproximation_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex x with
    ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact (eq_of_isBestApproximation_of_convex hC_convex hp hq).symm

-- Proof sketch: specialize the Chebyshev conclusion of Theorem 3.16.1 at the given point.
/-- Every point in a real Hilbert space has a unique best approximation in a nonempty closed convex
set. -/
theorem existsUnique_bestApproximation_of_nonempty_isClosed_convex {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ∀ x : 𝓗, ∃! p : 𝓗, IsBestApproximation x C p := by
  exact isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
