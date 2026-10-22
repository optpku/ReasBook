/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_2.Rate

noncomputable section

open Filter

universe u

section ConvergenceRates

variable {E : Type u} [NormedAddCommGroup E]

/-- A scalar sequence `q` is a nonnegative majorant for the norm-error sequence of `x`
relative to `xStar` when each term of `q` is nonnegative and bounds `‖x k - xStar‖`. -/
def IsNonnegErrorMajorant (x : ℕ → E) (xStar : E) (q : ℕ → ℝ) : Prop :=
  (∀ k : ℕ, 0 ≤ q k) ∧ ∀ k : ℕ, ‖x k - xStar‖ ≤ q k

/-- Unfolding formula for `IsNonnegErrorMajorant`. -/
theorem isNonnegErrorMajorant_iff (x : ℕ → E) (xStar : E) (q : ℕ → ℝ) :
    IsNonnegErrorMajorant x xStar q ↔
      (∀ k : ℕ, 0 ≤ q k) ∧ (∀ k : ℕ, ‖x k - xStar‖ ≤ q k) :=
  Iff.rfl

/-- A nonnegative scalar error majorant tending to `0` forces the underlying sequence
to converge to the same limit. -/
theorem tendsto_of_isNonnegErrorMajorant_tendsto_zero
    {x : ℕ → E} {xStar : E} {q : ℕ → ℝ}
    (hq : IsNonnegErrorMajorant x xStar q)
    (hq0 : Tendsto q atTop (nhds 0)) :
    Tendsto x atTop (nhds xStar) := by
  rcases hq with ⟨_, hqBound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact
    squeeze_zero'
      (Eventually.of_forall fun k ↦ norm_nonneg _)
      (Eventually.of_forall hqBound)
      hq0

/-- An `R`-rate is monotone under a nonnegative scalar error majorant. -/
theorem rRate_le_of_isNonnegErrorMajorant
    {p : RRateOrder} {x : ℕ → E} {xStar : E} {q : ℕ → ℝ}
    (hq : IsNonnegErrorMajorant x xStar q)
    (hq0 : Tendsto q atTop (nhds 0)) :
    R[p] x xStar ≤ R[p] (fun k ↦ q k) 0 := by
  rcases hq with ⟨hqNonneg, hqBound⟩
  rw [rRate_eq_limsup, rRate_eq_limsup]
  have hu :
      Filter.IsCoboundedUnder
        (fun a b : ℝ ↦ a ≤ b)
        atTop
        (fun k ↦ Real.rpow (‖x k - xStar‖) (rRateExponent p k)) := by
    change
      ∃ b : ℝ,
        ∀ a : ℝ,
          (∀ᶠ k in atTop, Real.rpow (‖x k - xStar‖) (rRateExponent p k) ≤ a) → b ≤ a
    refine ⟨0, ?_⟩
    intro a ha
    rcases ha.exists with ⟨k, hk⟩
    exact le_trans (Real.rpow_nonneg (norm_nonneg _) _) hk
  have hv :
      Filter.IsBoundedUnder
        (fun a b : ℝ ↦ a ≤ b)
        atTop
        (fun k ↦ Real.rpow (‖(q k : ℝ) - 0‖) (rRateExponent p k)) := by
    change
      ∃ b : ℝ,
        ∀ᶠ k in atTop, Real.rpow (‖(q k : ℝ) - 0‖) (rRateExponent p k) ≤ b
    refine ⟨1, ?_⟩
    have hqLtOne : ∀ᶠ k in atTop, q k < 1 :=
      hq0.eventually (Iio_mem_nhds zero_lt_one)
    have hqNonnegEvent : ∀ᶠ k in atTop, 0 ≤ q k := Eventually.of_forall hqNonneg
    filter_upwards [hqLtOne, hqNonnegEvent] with k hk hqkNonneg
    have hNormLeOne : ‖(q k : ℝ) - 0‖ ≤ 1 := by
      simpa [abs_of_nonneg hqkNonneg] using hk.le
    exact Real.rpow_le_one (norm_nonneg _) hNormLeOne (rRateExponent_nonneg p k)
  refine Filter.limsup_le_limsup (Eventually.of_forall ?_) hu hv
  intro k
  have hqNorm : ‖(q k : ℝ) - 0‖ = q k := by
    simpa using (abs_of_nonneg (hqNonneg k))
  calc
    Real.rpow (‖x k - xStar‖) (rRateExponent p k)
        ≤ Real.rpow (q k) (rRateExponent p k) := by
          exact Real.rpow_le_rpow (norm_nonneg _) (hqBound k) (rRateExponent_nonneg p k)
    _ = Real.rpow (‖(q k : ℝ) - 0‖) (rRateExponent p k) := by
          rw [hqNorm]

/-- A `Q`-linear scalar witness already tends to `0` by definition. -/
theorem HasQLinearConvergenceTo.tendsto_zero
    {q : ℕ → ℝ} (hq : HasQLinearConvergenceTo q 0) :
    Tendsto q atTop (nhds 0) := by
  rcases hq with ⟨_, _, hqOrder⟩
  exact hqOrder.tendsto

/-- A `Q`-quadratic scalar witness already tends to `0` by definition. -/
theorem HasQQuadraticConvergenceTo.tendsto_zero
    {q : ℕ → ℝ} (hq : HasQQuadraticConvergenceTo q 0) :
    Tendsto q atTop (nhds 0) := by
  rcases hq with ⟨_, hqOrder⟩
  exact hqOrder.tendsto

end ConvergenceRates
