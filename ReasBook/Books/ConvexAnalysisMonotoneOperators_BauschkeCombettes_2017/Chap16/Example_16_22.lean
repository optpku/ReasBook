/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_39
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace ERealFunction

local notation "L2pos" => lp (fun _ : ℕ+ ↦ ℝ) 2

/-- The one-variable coordinate function `t ↦ n * t^(2n)` from Example 16.22. -/
def positiveNatWeightedEvenPowerCoordinate (n : ℕ+) : ℝ → ℝ :=
  fun t ↦ (n : ℝ) * t ^ (2 * (n : ℕ))

-- Proof sketch: unfold `positiveNatWeightedEvenPowerCoordinate`.
/-- Evaluating the `n`th coordinate function recovers the explicit formula `n * t^(2n)`. -/
@[simp] theorem positiveNatWeightedEvenPowerCoordinate_apply (n : ℕ+) (t : ℝ) :
    positiveNatWeightedEvenPowerCoordinate n t = (n : ℝ) * t ^ (2 * (n : ℕ)) :=
  rfl

/-- The coordinate function from Example 16.22 vanishes at `0`. -/
@[simp] theorem positiveNatWeightedEvenPowerCoordinate_zero (n : ℕ+) :
    positiveNatWeightedEvenPowerCoordinate n 0 = 0 := by
  simp [positiveNatWeightedEvenPowerCoordinate]

-- Proof sketch: `n : ℝ` is nonnegative and `t^(2n)` is nonnegative because the exponent is even.
/-- The coordinate function `t ↦ n * t^(2n)` is pointwise nonnegative. -/
theorem positiveNatWeightedEvenPowerCoordinate_nonneg (n : ℕ+) (t : ℝ) :
    0 ≤ positiveNatWeightedEvenPowerCoordinate n t := sorry

/-- Viewing the coordinate function through `toEReal` preserves the value at `0`. -/
@[simp] theorem positiveNatWeightedEvenPowerCoordinate_toEReal_zero (n : ℕ+) :
    (((positiveNatWeightedEvenPowerCoordinate n).toEReal) 0 : EReal) = 0 := by
  simp [positiveNatWeightedEvenPowerCoordinate]

-- Proof sketch: rewrite through `Function.toEReal_apply` and use real-valued nonnegativity.
/-- The `toEReal` lift of the coordinate function attains its minimum at `0`. -/
theorem positiveNatWeightedEvenPowerCoordinate_toEReal_nonneg (n : ℕ+) (t : ℝ) :
    (((positiveNatWeightedEvenPowerCoordinate n).toEReal) 0 : EReal) ≤
      (positiveNatWeightedEvenPowerCoordinate n).toEReal t := sorry

-- Proof sketch: the exponent `2n` is even, so `t ↦ n * t^(2n)` is convex, lower semicontinuous,
-- finite everywhere, and minimized at `0`.
/-- Each coordinate function from Example 16.22 belongs to `Γ₀(ℝ)`. -/
theorem positiveNatWeightedEvenPowerCoordinate_mem_gammaZero (n : ℕ+) :
    (positiveNatWeightedEvenPowerCoordinate n).toEReal ∈ Γ₀(ℝ) := sorry

/-- The function from Example 16.22 on `ℓ²(ℕ+, ℝ)`, given by
`f(ξ) = ∑ₙ n * ξₙ^(2n)`, realized through the canonical inner-product series owner from
Example 9.13 specialized to the standard unit vectors of `ℓ²(ℕ+, ℝ)`. -/
noncomputable def positiveNatWeightedEvenPowerSeries : L2pos → Set.Ioi (⊥ : EReal) :=
  innerProductSeriesFunction
    (fun n ↦ lp.single 2 n (1 : ℝ))
    (fun n ↦ (positiveNatWeightedEvenPowerCoordinate n).toEReal)
    positiveNatWeightedEvenPowerCoordinate_toEReal_zero
    positiveNatWeightedEvenPowerCoordinate_toEReal_nonneg

-- Proof sketch: unfold the canonical inner-product series specialization and simplify
-- `⟪ξ, lp.single 2 n 1⟫_ℝ = ξ n`.
/-- Coercing the Example 16.22 function to `EReal` recovers the explicit weighted coordinate
family sum. -/
@[simp] theorem positiveNatWeightedEvenPowerSeries_apply (x : L2pos) :
    (positiveNatWeightedEvenPowerSeries x : EReal) =
      familySum
        (fun (n : ℕ+) (ξ : L2pos) ↦
          (((n : ℝ) * (ξ n) ^ (2 * (n : ℕ)) : ℝ) : EReal)) x := sorry

-- Proof sketch: apply Example 9.13 to the coordinate family `t ↦ n * t^(2n)`. Each coordinate
-- function is finite everywhere, lower semicontinuous, convex, vanishes at `0`, and is minimized
-- at `0` because the exponent `2n` is even.
/-- The weighted even-power series from Example 16.22 belongs to `Γ₀(ℓ²(ℕ+, ℝ))`. -/
theorem positiveNatWeightedEvenPowerSeries_mem_gammaZero :
    positiveNatWeightedEvenPowerSeries ∈ Γ₀(L2pos) := by
  simpa [positiveNatWeightedEvenPowerSeries] using
    innerProductSeriesFunction_mem_gammaZero
      (fun n ↦ lp.single 2 n (1 : ℝ))
      (fun n ↦ (positiveNatWeightedEvenPowerCoordinate n).toEReal)
      (fun n ↦ positiveNatWeightedEvenPowerCoordinate_mem_gammaZero n)
      positiveNatWeightedEvenPowerCoordinate_toEReal_zero
      positiveNatWeightedEvenPowerCoordinate_toEReal_nonneg

-- Proof sketch: for `x ∈ ℓ²(ℕ+, ℝ)`, the coordinates satisfy `x n → 0`. Since `n^(1 / n) → 1`,
-- eventually `x n ^ 2 ≤ 1 / (n^(3 / n))`, hence `n * x n^(2n) ≤ 1 / n^2`. Comparison with the
-- convergent `p`-series shows that every value is finite.
/-- The effective domain of the Example 16.22 series is all of `ℓ²(ℕ+, ℝ)`. -/
theorem positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ :
    effectiveDomain positiveNatWeightedEvenPowerSeries = Set.univ := sorry

-- Proof sketch: membership in `Γ₀(ℓ²(ℕ+, ℝ))` gives lower semicontinuity and convexity on the
-- effective domain. Since the previous theorem identifies that domain with `univ`, Corollary 8.39
-- yields continuity of the finite real representative at every point.
/-- The real-valued representative of the Example 16.22 series is continuous on all of
`ℓ²(ℕ+, ℝ)`. -/
theorem positiveNatWeightedEvenPowerSeries_continuous :
    Continuous fun x : L2pos ↦ ((positiveNatWeightedEvenPowerSeries x : EReal).toReal) := sorry

-- Proof sketch: by the domain theorem, every point lies in `effectiveDomain
-- positiveNatWeightedEvenPowerSeries`. The continuity theorem above gives continuity on the
-- effective domain, so Proposition 16.17(ii) yields a nonempty subdifferential at each point.
/-- The Example 16.22 series is subdifferentiable at every point of `ℓ²(ℕ+, ℝ)`. -/
theorem positiveNatWeightedEvenPowerSeries_subdifferentiableAt (x : L2pos) :
    SubdifferentiableAt positiveNatWeightedEvenPowerSeries x := sorry

-- Proof sketch: the standard basis vector `eₙ` has exactly one nonzero coordinate, equal to `1`
-- at index `n`. Hence every off-diagonal term in the family sum vanishes and the remaining term is
-- `n * 1^(2n) = n`.
/-- The Example 16.22 series takes the value `n` on the `n`th standard unit vector. -/
theorem positiveNatWeightedEvenPowerSeries_apply_basisVector (n : ℕ+) :
    (positiveNatWeightedEvenPowerSeries (lp.single 2 n (1 : ℝ)) : EReal) = ((n : ℝ) : EReal) :=
  sorry

-- Proof sketch: the helper theorems above identify the series as an everywhere finite continuous
-- convex function on `ℓ²(ℕ+, ℝ)`. The basis-vector formula gives `f(eₙ) = n`, so `f` is unbounded
-- on the bounded set of standard unit vectors. Proposition 16.20 therefore rules out
-- supercoercivity of the Fenchel conjugate.
/-- Example 16.22: for the series `f(ξ) = ∑ₙ n * ξₙ^(2n)` on `ℓ²(ℕ+, ℝ)`, the Fenchel conjugate
`f*` is not supercoercive. -/
theorem positiveNatWeightedEvenPowerSeries_conjugate_not_supercoercive :
    ¬ Supercoercive positiveNatWeightedEvenPowerSeries.asEReal∗ := sorry

end ERealFunction

end
