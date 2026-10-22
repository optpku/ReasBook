/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_23

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace ERealFunction

section

variable {H : Type u} [NormedAddCommGroup H]
variable {C : Set H}

private theorem ereal_sq_norm_ne_top (z : H) : ((↑‖z‖ : EReal) ^ 2) ≠ ⊤ := by
  simpa [pow_two] using
    (show (↑‖z‖ : EReal) * (↑‖z‖ : EReal) ≠ ⊤ by
      rw [EReal.mul_ne_top]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [norm_nonneg])

private theorem ereal_sq_norm_ne_bot (z : H) : ((↑‖z‖ : EReal) ^ 2) ≠ ⊥ := by
  simpa [pow_two] using
    (show (↑‖z‖ : EReal) * (↑‖z‖ : EReal) ≠ ⊥ by
      rw [EReal.mul_ne_bot]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [norm_nonneg])

-- Proof sketch: when `C` is nonempty, points outside `C` contribute `⊤`, while points of `C`
-- contribute the quadratic term `‖x - y‖² / 2`; hence proximal points of `ι[C]` are exactly the
-- best approximation points of `x` in `C`.
/-- For the indicator of a nonempty set, proximal points are exactly the best approximation points
in that set. -/
@[simp] theorem isProxPoint_indicator_iff_isBestApproximation
    (hC_nonempty : C.Nonempty) (x p : H) :
    IsProxPoint (ι[C]) x p ↔ IsBestApproximation x C p := by
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff,
    isBestApproximation_iff_mem_and_dist_eq_infDist]
  constructor
  · intro hp
    rcases hC_nonempty with ⟨q, hqC⟩
    have hpC : p ∈ C := by
      by_contra hpC
      have hp_top : proximalObjective (ι[C]) x p = ⊤ := by
        rw [proximalObjective]
        simp [indicator, hpC]
        have hterm_ne_bot :
            (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - p‖ : EReal) ^ 2 ≠ ⊥ := by
          rw [EReal.mul_ne_bot]
          refine ⟨?_, ?_, ?_, ?_⟩
          · left
            simpa using (EReal.coe_ne_bot (2⁻¹ : ℝ))
          · right
            simpa using ereal_sq_norm_ne_bot (x - p)
          · left
            simpa using (EReal.coe_ne_top (2⁻¹ : ℝ))
          · left
            positivity
        exact EReal.top_add_of_ne_bot hterm_ne_bot
      have hpq := hp q
      rw [hp_top] at hpq
      have hq_ne_top : proximalObjective (ι[C]) x q ≠ ⊤ := by
        rw [proximalObjective]
        simp [indicator, hqC]
        have hmul :
            (((2⁻¹ : ℝ) * ‖x - q‖ ^ 2 : ℝ) : EReal) =
              (↑(2⁻¹ : ℝ) : EReal) * ↑(‖x - q‖ ^ 2 : ℝ) := by
          simpa using (EReal.coe_mul (2⁻¹ : ℝ) (‖x - q‖ ^ 2))
        have hne : (((2⁻¹ : ℝ) * ‖x - q‖ ^ 2 : ℝ) : EReal) ≠ ⊤ :=
          EReal.coe_ne_top ((2⁻¹ : ℝ) * ‖x - q‖ ^ 2)
        simpa [hmul] using hne
      exact hq_ne_top (top_le_iff.mp hpq)
    refine ⟨hpC, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hpC)⟩
    rw [Metric.le_infDist ⟨q, hqC⟩]
    intro y hy
    have hquad : (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
      exact_mod_cast (by simpa [proximalObjective, indicator, hpC, hy] using hp y :
        (((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal) ≤
          (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal))
    have hdist : dist x p ≤ dist x y := by
      have hnorm : ‖x - p‖ ≤ ‖x - y‖ := by
        have hsq : ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 :=
          by nlinarith [hquad]
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
      simpa [dist_eq_norm] using hnorm
    exact hdist
  · rintro ⟨hpC, hpdist⟩
    intro y
    by_cases hy : y ∈ C
    · have hdist : dist x p ≤ dist x y := by
        rw [hpdist]
        exact Metric.infDist_le_dist_of_mem hy
      have hquad : (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
        have hnorm : ‖x - p‖ ≤ ‖x - y‖ := by
          simpa [dist_eq_norm] using hdist
        have hsq : ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
        exact mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (1 / 2 : ℝ))
      have hquad' :
          (((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal) ≤
            (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
        exact_mod_cast hquad
      exact by
        simpa [proximalObjective, indicator, hpC, hy] using hquad'
    · have hy_top : proximalObjective (ι[C]) x y = ⊤ := by
        rw [proximalObjective]
        simp [indicator, hy]
        have hterm_ne_bot :
            (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - y‖ : EReal) ^ 2 ≠ ⊥ := by
          rw [EReal.mul_ne_bot]
          refine ⟨?_, ?_, ?_, ?_⟩
          · left
            simpa using (EReal.coe_ne_bot (2⁻¹ : ℝ))
          · right
            simpa using ereal_sq_norm_ne_bot (x - y)
          · left
            simpa using (EReal.coe_ne_top (2⁻¹ : ℝ))
          · left
            positivity
        exact EReal.top_add_of_ne_bot hterm_ne_bot
      rw [hy_top]
      exact le_top

-- Proof sketch: extensionality on points, then rewrite both sides by
-- `isProxPoint_indicator_iff_isBestApproximation` and `mem_setValuedProjector_iff`.
/-- For a nonempty set `C`, the proximal-point set of the indicator `ι[C]` agrees with the
set-valued projector onto `C`. -/
theorem proximalPoints_indicator_eq_setValuedProjector (hC_nonempty : C.Nonempty) (x : H) :
    proximalPoints (ι[C]) x = setValuedProjector C x := by
  ext p
  change IsProxPoint (ι[C]) x p ↔ p ∈ setValuedProjector C x
  rw [mem_setValuedProjector_iff, isProxPoint_indicator_iff_isBestApproximation hC_nonempty]

-- Proof sketch: unfold `HasUniqueProxPoint` and `IsChebyshev`, then rewrite the proximal-point
-- set by `proximalPoints_indicator_eq_setValuedProjector`.
/-- For a nonempty set `C`, the indicator of `C` has unique proximal points exactly when `C` is
Chebyshev. -/
theorem hasUniqueProxPoint_indicator_iff_isChebyshev (hC_nonempty : C.Nonempty) :
    HasUniqueProxPoint (ι[C]) ↔ IsChebyshev C := by
  constructor
  · intro hf x
    simpa [HasUniqueProxPoint, proximalPoints_indicator_eq_setValuedProjector hC_nonempty] using
      hf x
  · intro hC x
    simpa [HasUniqueProxPoint, proximalPoints_indicator_eq_setValuedProjector hC_nonempty] using
      (isChebyshev_iff_forall_existsUnique_mem_setValuedProjector C).mp hC x

private theorem nonempty_of_isChebyshev (hC : IsChebyshev C) : C.Nonempty := by
  rcases hC 0 with ⟨p, hp, _⟩
  exact ⟨p, hp.1⟩

-- Proof sketch: specialize `hasUniqueProxPoint_indicator_iff_isChebyshev` to the given Chebyshev
-- structure on `C`.
/-- A Chebyshev set has a unique proximal point for its indicator at every base point. -/
theorem hasUniqueProxPoint_indicator (hC : IsChebyshev C) :
    HasUniqueProxPoint (ι[C]) :=
  (hasUniqueProxPoint_indicator_iff_isChebyshev (nonempty_of_isChebyshev hC)).2 hC

-- Proof sketch: the Chebyshev projection point is a proximal point by
-- `isProxPoint_indicator_iff_isBestApproximation`; uniqueness of proximal points for `ι[C]`
-- then identifies it with `Prox_{ι[C]}`.
/-- For a Chebyshev set, the proximity operator of the indicator `ι[C]` agrees with the metric
projection `P_C`. -/
theorem proximityOperator_indicator_eq_projectionPoint (hC : IsChebyshev C) :
    proximityOperator (ι[C]) (hasUniqueProxPoint_indicator hC) = projectionPoint C hC := by
  funext x
  symm
  have hproj : projectionPoint C hC x ∈ proximalPoints (ι[C]) x := by
    rw [proximalPoints_indicator_eq_setValuedProjector (nonempty_of_isChebyshev hC)]
    exact projectionPoint_mem_setValuedProjector C hC x
  exact eq_proximityOperator_of_isProxPoint (ι[C]) (hasUniqueProxPoint_indicator hC) <|
    hproj

-- Proof sketch: rewrite the proximal-point set of `ι[C]` as the set-valued projector onto `C`,
-- then use uniqueness in the Chebyshev set `C` to identify that projector with the singleton
-- containing `projectionPoint C hC x`.
/-- For a Chebyshev set, the proximal points of its indicator form the singleton consisting of the
metric projection. -/
theorem proximalPoints_indicator_eq_singleton_projectionPoint (hC : IsChebyshev C) (x : H) :
    proximalPoints (ι[C]) x = ({projectionPoint C hC x} : Set H) := by
  rw [proximalPoints_indicator_eq_setValuedProjector (nonempty_of_isChebyshev hC)]
  ext p
  constructor
  · intro hp
    rw [Set.mem_singleton_iff]
    exact eq_projectionPoint_of_isBestApproximation C hC <|
      mem_setValuedProjector_iff.mp hp
  · intro hp
    rw [Set.mem_singleton_iff] at hp
    rw [hp]
    exact projectionPoint_mem_setValuedProjector C hC x

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}

-- Proof sketch: closed convex subsets of a complete real Hilbert space are Chebyshev by
-- `isChebyshev_of_nonempty_isClosed_convex`; apply `hasUniqueProxPoint_indicator`.
/-- A nonempty closed convex set has a unique proximal point for its indicator at every base
point. -/
theorem hasUniqueProxPoint_indicator_of_nonempty_isClosed_convex
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    HasUniqueProxPoint (ι[C]) :=
  hasUniqueProxPoint_indicator <|
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

-- Proof sketch: instantiate `proximityOperator_indicator_eq_projectionPoint` with the Chebyshev
-- structure coming from `isChebyshev_of_nonempty_isClosed_convex`.
/-- Example 12.25: for a nonempty closed convex subset `C` of a real Hilbert space, the
proximity operator of the indicator `ι_C` is the metric projection `P_C`. -/
theorem proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    proximityOperator (ι[C])
        (hasUniqueProxPoint_indicator_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex) =
      projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) := by
  let hC_chebyshev : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  simpa [hC_chebyshev] using
    proximityOperator_indicator_eq_projectionPoint hC_chebyshev

-- Proof sketch: instantiate `proximalPoints_indicator_eq_singleton_projectionPoint` with the
-- Chebyshev structure coming from `isChebyshev_of_nonempty_isClosed_convex`.
/-- For a nonempty closed convex subset `C` of a real Hilbert space, the proximal
points of the indicator `ι_C` at `x` form the singleton consisting of the metric projection of `x`
onto `C`. -/
theorem proximalPoints_indicator_eq_singleton_projectionPoint_of_nonempty_isClosed_convex
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (x : H) :
    proximalPoints (ι[C]) x =
      ({projectionPoint C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x} : Set H) :=
  by
    let hC_chebyshev : IsChebyshev C :=
      isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
    simpa [hC_chebyshev] using proximalPoints_indicator_eq_singleton_projectionPoint hC_chebyshev x

end

end ERealFunction
