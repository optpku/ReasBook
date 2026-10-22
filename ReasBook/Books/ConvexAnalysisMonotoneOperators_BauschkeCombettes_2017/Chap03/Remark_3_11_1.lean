/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [MetricSpace X]

/-- Helper for Remark 3.11.1: if a closure point admits a best approximation in `C`, then that
best approximation must coincide with the point, so the point already lies in `C`. -/
private lemma mem_of_mem_closure_of_isBestApproximation {C : Set X} {x p : X}
    (hx : x ∈ closure C) (hp : IsBestApproximation x C p) : x ∈ C := by
  -- A closure point has zero distance to the set, so the chosen best approximation is at distance
  -- zero from the point.
  have hxp_dist : dist x p = 0 := by
    rw [hp.2, Metric.infDist_zero_of_mem_closure hx]
  -- Zero distance identifies the point with its best approximation.
  have hxp : x = p := dist_eq_zero.mp hxp_dist
  simpa [hxp] using hp.1

/-- Helper for Remark 3.11.1: proximinality forces `closure C ⊆ C`. -/
private lemma closure_subset_of_isProximinalIn {C : Set X} (hC : IsProximinalIn C) :
    closure C ⊆ C := by
  intro x hx
  -- Choose a best approximation for the closure point and apply the zero-distance argument.
  obtain ⟨p, hp, hbest⟩ := hC x
  exact mem_of_mem_closure_of_isBestApproximation hx ⟨hp, hbest⟩

-- Proof sketch: if `x ∈ closure C`, then `Metric.infDist x C = 0`; a best approximation
-- `p ∈ C` must therefore satisfy `dist x p = 0`, hence `x = p ∈ C`.
/-- Remark 3.11.1: a proximinal set in a metric space is closed. -/
theorem isClosed_of_isProximinalIn {C : Set X} (hC : IsProximinalIn C) : IsClosed C := by
  -- The source proof reduces closedness to the invariant `closure C ⊆ C`.
  exact (closure_subset_iff_isClosed).mp
    (closure_subset_of_isProximinalIn hC)

/-- Every Chebyshev set in a metric space is closed. -/
theorem isClosed_of_isChebyshev {C : Set X} (hC : IsChebyshev C) : IsClosed C := by
  -- Forget uniqueness and reuse the proximal case proved above.
  exact isClosed_of_isProximinalIn fun x ↦ ExistsUnique.exists (hC x)
