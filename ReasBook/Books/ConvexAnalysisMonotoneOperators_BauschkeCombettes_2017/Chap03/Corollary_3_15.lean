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

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
  [FiniteDimensional ℝ 𝓗]

-- Proof sketch: for the forward implication, use the defining best-approximation condition to show
-- that every point in the closure of `C` already belongs to `C`. For the reverse implication, fix
-- `x`, choose a minimizing sequence in the nonempty closed set `C`, use compactness of closed
-- bounded sets in finite dimensions to extract a convergent subsequence with limit in `C`, and
-- show that the limit realizes `Metric.infDist x C`.
/-- Corollary 3.15: in a finite-dimensional real Hilbert space, a nonempty set is proximal if and
only if it is closed. -/
theorem proximinal_iff_isClosed_of_nonempty {C : Set 𝓗} (hC : C.Nonempty) :
    IsProximinalIn C ↔ IsClosed C := by
  constructor
  · intro hprox
    rw [isProximinalIn_iff_forall_exists_bestApproximation] at hprox
    -- The governing invariant in the forward direction is `closure C ⊆ C`.
    refine (closure_subset_iff_isClosed).mp ?_
    intro x hx
    -- Realize the distance to `C` at the closure point `x`.
    obtain ⟨p, hpC, hpdist⟩ := hprox x
    -- A closure point has distance zero to `C`, so the realizing point must equal `x`.
    rw [Metric.infDist_zero_of_mem_closure hx] at hpdist
    have hxp : x = p := dist_eq_zero.mp hpdist
    simpa [hxp] using hpC
  · intro hclosed
    rw [isProximinalIn_iff_forall_exists_bestApproximation]
    intro x
    -- In finite dimensions, the proper-space attainment theorem realizes `infDist` on closed
    -- nonempty sets.
    obtain ⟨p, hpC, hpdist⟩ := hclosed.exists_infDist_eq_dist hC x
    exact ⟨p, hpC, hpdist.symm⟩

/-- Compatibility form of `proximinal_iff_isClosed_of_nonempty`. -/
theorem proximal_iff_isClosed_of_nonempty {C : Set 𝓗} (hC : C.Nonempty) :
    IsProximal C ↔ IsClosed C :=
  proximinal_iff_isClosed_of_nonempty hC
