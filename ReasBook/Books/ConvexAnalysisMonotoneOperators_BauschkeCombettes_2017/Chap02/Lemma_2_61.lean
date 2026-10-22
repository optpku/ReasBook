/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u v

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

-- Proof sketch: a Fréchet derivative gives the usual little-o control of
-- `T (x + h) - T x - A h` as `h → 0` within `C`. Because `C` is a neighborhood of `x`, every
-- direction from `x` stays inside `C` along a short positive segment, so substituting `h = α • y`
-- and dividing by `α > 0` yields the one-sided directional limit defining the Gâteaux derivative
-- with the same operator `A`.
/-- Lemma 2.61 (1): if `C` is a neighborhood of `x` and `A` is the Fréchet derivative of `T` at
`x` within `C`, then for every direction `y` the one-sided directional difference quotient tends to
`A y`; equivalently, `T` is Gâteaux differentiable there and the two derivatives coincide. -/
theorem HasFDerivWithinAt.tendsto_directionalDifferenceQuotient
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasFDerivWithinAt T A C x) (hC : C ∈ 𝓝 x) :
    ∀ y : H,
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) := by
  simpa using
    (hT.hasGateauxDerivativeWithinAt hC).tendsto_directionalDifferenceQuotient

-- Proof sketch: a Fréchet derivative within `C` implies continuity within `C` at `x` by the
-- standard calculus theorem. Since `C` is a neighborhood of `x`, continuity within `C` upgrades to
-- ordinary continuity at `x`.
/-- Lemma 2.61 (2): if `C` is a neighborhood of `x` and `T` is Fréchet differentiable at `x`
within `C`, then `T` is continuous at `x`. -/
theorem HasFDerivWithinAt.continuousAt_of_mem_nhds
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasFDerivWithinAt T A C x) (hC : C ∈ 𝓝 x) :
    ContinuousAt T x := by
  -- Fréchet differentiability gives continuity within `C`, and the neighborhood hypothesis
  -- upgrades that local continuity to ordinary continuity at `x`.
  simpa using hT.continuousWithinAt.continuousAt hC
