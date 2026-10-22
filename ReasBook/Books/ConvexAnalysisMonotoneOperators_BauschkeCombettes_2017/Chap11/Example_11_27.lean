/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_32_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

section

/-- The real-valued weighted quadratic coordinate function used in the Hilbert-basis series
example. The weights are primitive nonnegative data, so no separate proof witness enters the
owner. -/
def weightedSquareCoordinate (ω : ℕ → NNReal) (n : ℕ) : ℝ → ℝ :=
  fun t ↦ (ω n : ℝ) * t ^ 2

/-- The weighted quadratic coordinate function vanishes at the origin. -/
@[simp] theorem weightedSquareCoordinate_zero (ω : ℕ → NNReal) (n : ℕ) :
    weightedSquareCoordinate ω n 0 = 0 := by
  simp [weightedSquareCoordinate]

/-- Viewing the weighted quadratic coordinate through `toEReal` preserves the value at `0`. -/
@[simp] theorem weightedSquareCoordinate_toEReal_zero (ω : ℕ → NNReal) (n : ℕ) :
    (((weightedSquareCoordinate ω n).toEReal) 0 : EReal) = 0 := by
  simp [weightedSquareCoordinate]

/-- The weighted quadratic coordinate function is pointwise nonnegative. -/
-- Proof sketch: rewrite the explicit formula and use the nonnegativity built into `ωₙ : NNReal`
-- together with `0 ≤ t²`.
theorem weightedSquareCoordinate_nonneg (ω : ℕ → NNReal) (n : ℕ) (t : ℝ) :
    0 ≤ weightedSquareCoordinate ω n t := sorry

/-- The `toEReal` lift of the weighted quadratic coordinate function attains its minimum at `0`. -/
-- Proof sketch: rewrite both sides through `Function.toEReal_apply` and use the real-valued
-- nonnegativity of `t ↦ ωₙ t²`.
theorem weightedSquareCoordinate_toEReal_nonneg (ω : ℕ → NNReal) (n : ℕ) (t : ℝ) :
    (((weightedSquareCoordinate ω n).toEReal) 0 : EReal) ≤
      (weightedSquareCoordinate ω n).toEReal t :=
  sorry

/-- A weighted square belongs to `Γ₀(ℝ)` after passage to the canonical
`Function.toEReal` bridge. -/
-- Proof sketch: identify `t ↦ ωₙ t²` with a nonnegative scalar multiple of the squared norm on
-- `ℝ`, combine convexity and lower semicontinuity of the quadratic function, and observe that the
-- value at `0` is finite.
theorem weightedSquareCoordinate_mem_gammaZero (ω : ℕ → NNReal) (n : ℕ) :
    (weightedSquareCoordinate ω n).toEReal ∈ Γ₀(ℝ) := sorry

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The weighted squared-coordinate series from Example 11.27, realized through the canonical
nonnegative inner-product series owner from Example 9.13. -/
noncomputable def weightedHilbertBasisSquareSeries (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) :
    H → Set.Ioi (⊥ : EReal) :=
  innerProductSeriesFunction b (fun n ↦ (weightedSquareCoordinate ω n).toEReal)
    (weightedSquareCoordinate_toEReal_zero ω)
    (weightedSquareCoordinate_toEReal_nonneg ω)

/-- Coercing the weighted Hilbert-basis square series back to `EReal` recovers the coordinate
family sum. -/
@[simp] theorem weightedHilbertBasisSquareSeries_apply (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (x : H) :
    (weightedHilbertBasisSquareSeries ω b x : EReal) =
      familySum (fun n y ↦ ((weightedSquareCoordinate ω n).toEReal ⟪y, b n⟫_ℝ : EReal)) x := by
  simp [weightedHilbertBasisSquareSeries, innerProductSeriesFunction_apply]

/-- The weighted Hilbert-basis square series belongs to `Γ₀(H)`. -/
-- Proof sketch: specialize Example 9.13 to the coordinate family `t ↦ ωₙ t²`, using the
-- coordinate-level `Γ₀(ℝ)` result together with the facts that the family vanishes at `0` and is
-- pointwise minimized there.
theorem weightedHilbertBasisSquareSeries_mem_gammaZero (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) :
    weightedHilbertBasisSquareSeries ω b ∈ Γ₀(H) := by
  simpa [weightedHilbertBasisSquareSeries] using
    innerProductSeriesFunction_mem_gammaZero b
      (fun n ↦ (weightedSquareCoordinate ω n).toEReal)
      (fun n ↦ weightedSquareCoordinate_mem_gammaZero ω n)
      (weightedSquareCoordinate_toEReal_zero ω)
      (weightedSquareCoordinate_toEReal_nonneg ω)

/-- The weighted Hilbert-basis square series is finite everywhere, hence real-valued in the
textbook sense. -/
-- Proof sketch: use Parseval to bound the weighted coordinate sum by
-- `(sSup (Set.range ω)) * ‖x‖²`; a uniform upper bound on the weights then keeps every value
-- finite.
theorem weightedHilbertBasisSquareSeries_effectiveDomain_eq_univ (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_bdd : BddAbove (Set.range ω)) :
    effectiveDomain (weightedHilbertBasisSquareSeries ω b) = Set.univ := sorry

/-- The real-valued representative of the weighted Hilbert-basis square series is continuous on the
whole Hilbert space. -/
-- Proof sketch: first place the series in `Γ₀(H)`, then use the previous theorem to identify the
-- effective domain with `univ`, and finally apply the Chapter 8 continuity criterion for convex
-- functions on the interior of their effective domain.
theorem weightedHilbertBasisSquareSeries_continuous (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_bdd : BddAbove (Set.range ω)) :
    Continuous fun x : H ↦ ((weightedHilbertBasisSquareSeries ω b x : EReal)).toReal :=
  sorry

/-- Positive weights make the weighted Hilbert-basis square series strictly convex. -/
-- Proof sketch: for distinct `x` and `y`, choose a basis coordinate on which they differ; the
-- corresponding weighted square term is then strictly convex, while all remaining terms are merely
-- convex, so the summed Jensen inequality is strict.
theorem weightedHilbertBasisSquareSeries_strictlyConvex (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_pos : ∀ n, 0 < ω n) :
    StrictlyConvex (weightedHilbertBasisSquareSeries ω b) := sorry

/-- The weighted Hilbert-basis square series vanishes at the origin. -/
-- Proof sketch: each coordinate of `0` is `0`, so every coordinate term vanishes and the whole
-- family sum is `0`.
theorem weightedHilbertBasisSquareSeries_zero (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) :
    (weightedHilbertBasisSquareSeries ω b 0 : EReal) = 0 := by
  simpa [weightedHilbertBasisSquareSeries] using
    innerProductSeriesFunction_zero b (fun n ↦ (weightedSquareCoordinate ω n).toEReal)
      (weightedSquareCoordinate_toEReal_zero ω)
      (weightedSquareCoordinate_toEReal_nonneg ω)

/-- Positive weights force the origin to be the unique minimizer of the weighted Hilbert-basis
square series. -/
-- Proof sketch: every term in the defining series is nonnegative, so the origin gives the minimal
-- value `0`; if `x ≠ 0`, some basis coordinate is nonzero, and the positivity of the
-- corresponding weight makes the value strictly positive.
theorem weightedHilbertBasisSquareSeries_argmin_eq_singleton (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_pos : ∀ n, 0 < ω n) :
    Argmin (weightedHilbertBasisSquareSeries ω b).asEReal =
      ({(0 : H)} : Set H) := sorry

/-- The weighted Hilbert-basis square series takes the value `ωₙ` on the `n`th basis vector. -/
-- Proof sketch: all basis coordinates of `b n` vanish except the `n`th one, whose squared norm is
-- `1`.
theorem weightedHilbertBasisSquareSeries_apply_basis (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) :
    (weightedHilbertBasisSquareSeries ω b (b n) : EReal) = (ω n : ℝ) := sorry

private noncomputable def weightedHilbertBasisSquareSeriesPositiveEscapeSequence
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) : ℕ → H :=
  fun n ↦ (Real.sqrt (ω n : ℝ))⁻¹ • b n

-- Along the positive-weight escape sequence `yₙ = bₙ / √ωₙ`, the weighted series has the
-- constant value `1`.
private theorem weightedHilbertBasisSquareSeries_apply_positiveEscapeSequence (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_pos : ∀ n, 0 < ω n) (n : ℕ) :
    (weightedHilbertBasisSquareSeries ω b
        (weightedHilbertBasisSquareSeriesPositiveEscapeSequence ω b n) : EReal) = 1 := sorry

/-- The weighted Hilbert-basis square series is not coercive. -/
-- Proof sketch: if some weight vanishes, the whole ray through the corresponding basis vector has
-- constant value `0`, so coercivity already fails. Otherwise every weight is positive, and the
-- positive-weight escape sequence `yₙ = bₙ / √ωₙ` has norm tending to `+∞` because `ωₙ → 0`
-- while the function value stays identically equal to `1`.
theorem weightedHilbertBasisSquareSeries_not_coercive (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_tendsto : Tendsto (fun n ↦ (ω n : ℝ)) atTop (𝓝 0)) :
    ¬ Coercive (weightedHilbertBasisSquareSeries ω b).asEReal := sorry

omit [CompleteSpace H] in
/-- A Hilbert basis does not converge strongly to the origin. -/
-- Proof sketch: apply the orthonormal-sequence result from Example 2.32.1 to the orthonormal
-- family underlying the Hilbert basis.
theorem hilbertBasis_not_tendsto_zero_strongly (b : HilbertBasis ℕ ℝ H) :
    ¬ Tendsto b atTop (𝓝 (0 : H)) := sorry

/-- Example 11.27: if `ωₙ → 0`, then the Hilbert basis itself is a minimizing sequence for the
weighted squared-coordinate series, and it converges weakly to `0`. -/
-- Proof sketch: the coordinate computation gives `f (b n) = ωₙ`, so `ωₙ → 0 = f 0` shows that
-- `b` is a minimizing sequence. Weak convergence follows from the orthonormal-sequence theorem
-- from Example 2.32.1 applied to the basis family.
theorem weightedHilbertBasisSquareSeries_basis_isMinimizingSequence_and_tendsto_weakly
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H)
    (hω_tendsto : Tendsto (fun n ↦ (ω n : ℝ)) atTop (𝓝 0)) :
    IsMinimizingSequence (weightedHilbertBasisSquareSeries ω b).asEReal b ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (b n)) atTop (𝓝 (0 : WeakSpace ℝ H)) := sorry

/- The minimizing Hilbert-basis sequence from Example 11.27 does not converge strongly to `0`;
this is exactly `hilbertBasis_not_tendsto_zero_strongly`. -/
recall hilbertBasis_not_tendsto_zero_strongly

end

end ERealFunction
