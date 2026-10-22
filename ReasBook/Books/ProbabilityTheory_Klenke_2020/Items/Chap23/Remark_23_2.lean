/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

noncomputable section

namespace ProbabilityTheory

/-- The finite-value branch of the Bernoulli Cramér rate function, namely
`((1 + x) log (1 + x) + (1 - x) log (1 - x)) / 2`. -/
def bernoulliCramerRateFunction (x : ℝ) : ℝ :=
  ((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) / 2

/-- Helper for Remark 23.2: the Bernoulli Cramér rate function is continuous on all of `ℝ`. -/
lemma continuousBernoulliCramerRateFunction :
    Continuous bernoulliCramerRateFunction := by
  -- Each affine-log summand is continuous by composing
  -- `Real.continuous_mul_log` with an affine map.
  have hPlus : Continuous fun x : ℝ ↦ (1 + x) * Real.log (1 + x) := by
    simpa using Real.continuous_mul_log.comp (continuous_const.add continuous_id)
  have hMinus : Continuous fun x : ℝ ↦ (1 - x) * Real.log (1 - x) := by
    simpa using Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  -- Summing the two terms and dividing by `2` preserves continuity.
  simpa [bernoulliCramerRateFunction] using (hPlus.add hMinus).div_const (2 : ℝ)

/-- Helper for Remark 23.2: the half-affine coordinate `x ↦ (1 + x) / 2` is strictly increasing on
`[-1, 1]`. -/
lemma halfAffineStrictMonoOn :
    StrictMonoOn (fun x : ℝ ↦ (1 + x) / 2) (Icc (-1 : ℝ) 1) := by
  -- This affine change of variables preserves the strict order on `ℝ`.
  intro x hx y hy hxy
  linarith

/-- Helper for Remark 23.2: the Bernoulli Cramér rate function is `log 2 - binEntropy` after the
half-affine change of variables. -/
lemma bernoulliCramerRateFunction_eq_logTwo_sub_binEntropy (x : ℝ) :
    bernoulliCramerRateFunction x = Real.log 2 - Real.binEntropy ((1 + x) / 2) := by
  let p : ℝ := (1 + x) / 2
  have hPlus : 1 + x = 2 * p := by
    dsimp [p]
    ring
  have hMinus : 1 - x = 2 * (1 - p) := by
    dsimp [p]
    ring
  have hTwo : Real.negMulLog 2 = -2 * Real.log 2 := by
    simp [Real.negMulLog]
  -- Rewrite the explicit formula through `Real.negMulLog_mul`, which is stable at the endpoints.
  calc
    bernoulliCramerRateFunction x
        = ((2 * p) * Real.log (2 * p) + (2 * (1 - p)) * Real.log (2 * (1 - p))) / 2 := by
            rw [bernoulliCramerRateFunction, hPlus, hMinus]
    _ = (-Real.negMulLog (2 * p) + -Real.negMulLog (2 * (1 - p))) / 2 := by
          simp [Real.negMulLog]
    _ = (-(p * Real.negMulLog 2 + 2 * Real.negMulLog p) -
          ((1 - p) * Real.negMulLog 2 + 2 * Real.negMulLog (1 - p))) / 2 := by
          rw [Real.negMulLog_mul 2 p, Real.negMulLog_mul 2 (1 - p)]
          ring
    _ = Real.log 2 - (Real.negMulLog p + Real.negMulLog (1 - p)) := by
          rw [hTwo]
          ring
    _ = Real.log 2 - Real.binEntropy p := by
          rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    _ = Real.log 2 - Real.binEntropy ((1 + x) / 2) := by
          rfl

/-- Helper for Remark 23.2: pulling back binary entropy along `x ↦ (1 + x) / 2` stays strictly
concave on `[-1, 1]`. -/
lemma strictConcaveOn_binEntropy_halfAffine :
    StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) (fun x : ℝ ↦ Real.binEntropy ((1 + x) / 2)) := by
  refine ⟨convex_Icc (-1 : ℝ) 1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : (1 + x) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : (1 + y) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have hxy' : (1 + x) / 2 ≠ (1 + y) / 2 := by
    intro hHalf
    apply hxy
    linarith
  have hAffine :
      a * ((1 + x) / 2) + b * ((1 + y) / 2) = (1 + (a * x + b * y)) / 2 := by
    have hSum : a * (1 + x) + b * (1 + y) = 1 + (a * x + b * y) := by
      nlinarith [hab]
    calc
      a * ((1 + x) / 2) + b * ((1 + y) / 2) = (a * (1 + x) + b * (1 + y)) / 2 := by ring
      _ = (1 + (a * x + b * y)) / 2 := by rw [hSum]
  -- Apply strict concavity of `Real.binEntropy` after identifying the affine coordinate.
  simpa [smul_eq_mul, hAffine] using Real.strictConcave_binEntropy.2 hx' hy' hxy' ha hb hab

-- Proof sketch: combine mathlib's canonical continuity theorem `Real.continuous_mul_log` with the
-- affine maps `x ↦ 1 + x` and `x ↦ 1 - x`; on `[-1,1]` both arguments stay in `[0,2]`, so the sum
-- and scalar multiple remain continuous.
/-- With the convention `0 log 0 = 0`, the restriction of the Bernoulli Cramér rate function to
`[-1,1]` is continuous. -/
theorem bernoulliCramerRateFunction_continuousOn :
    ContinuousOn bernoulliCramerRateFunction (Icc (-1 : ℝ) 1) := by
  -- Restrict the global continuity companion to the interval from the remark.
  exact continuousBernoulliCramerRateFunction.continuousOn

-- Proof sketch: substitute `x = -1` into the explicit formula; the `0 log 0` term vanishes and
-- the remaining term is `(2 * log 2) / 2`.
/-- The Bernoulli Cramér rate function takes the endpoint value `log 2` at `-1`. -/
theorem bernoulliCramerRateFunction_neg_one :
    bernoulliCramerRateFunction (-1) = Real.log 2 := by
  -- Evaluate the entropy normal form at the left endpoint, where the entropy parameter is `0`.
  simpa using bernoulliCramerRateFunction_eq_logTwo_sub_binEntropy (-1)

-- Proof sketch: substitute `x = 1` into the explicit formula; again the `0 log 0` term vanishes
-- and the remaining term is `(2 * log 2) / 2`.
/-- The Bernoulli Cramér rate function takes the endpoint value `log 2` at `1`. -/
theorem bernoulliCramerRateFunction_one :
    bernoulliCramerRateFunction 1 = Real.log 2 := by
  -- Evaluate the entropy normal form at the right endpoint, where the entropy parameter is `1`.
  simpa using bernoulliCramerRateFunction_eq_logTwo_sub_binEntropy 1

-- Proof sketch: combine the canonical strict convexity of `x ↦ x * Real.log x` on `Ici 0` given by
-- `Real.strictConvexOn_mul_log` with the affine maps `x ↦ 1 + x` and `x ↦ 1 - x`, then use the
-- endpoint continuity to extend strict convexity to the closed interval.
/-- Remark 23.2: the Bernoulli Cramér rate function is strictly convex on `[-1,1]`. -/
theorem bernoulliCramerRateFunction_strictConvexOn :
    StrictConvexOn ℝ (Icc (-1 : ℝ) 1) bernoulliCramerRateFunction := by
  -- Route correction: rewrite the rate function through binary entropy and use strict concavity.
  have hConvex :
      StrictConvexOn ℝ (Icc (-1 : ℝ) 1)
        ((fun x : ℝ ↦ -Real.binEntropy ((1 + x) / 2)) + fun _ ↦ Real.log 2) := by
    exact strictConcaveOn_binEntropy_halfAffine.neg.add_const (Real.log 2)
  -- The rewritten normal form agrees with the original rate function on the whole interval.
  refine hConvex.congr ?_
  intro x hx
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (bernoulliCramerRateFunction_eq_logTwo_sub_binEntropy x).symm

-- Proof sketch: evaluate the explicit formula at `x = 0`; both logarithmic terms are
-- `1 * log 1 = 0`.
/-- The Bernoulli Cramér rate function vanishes at the origin. -/
theorem bernoulliCramerRateFunction_zero :
    bernoulliCramerRateFunction 0 = 0 := by
  have hHalf : ((1 : ℝ) + 0) / 2 = (2 : ℝ)⁻¹ := by
    norm_num
  -- Evaluate the entropy normal form at the symmetric point `p = 1 / 2`.
  rw [bernoulliCramerRateFunction_eq_logTwo_sub_binEntropy 0, hHalf, Real.binEntropy_two_inv]
  ring

-- Proof sketch: the derivative of the explicit formula is nonnegative on `[0,1]`, so the
-- function is monotone increasing there.
/-- The Bernoulli Cramér rate function is monotone increasing on `[0,1]`. -/
theorem bernoulliCramerRateFunction_monotoneOn_nonneg :
    MonotoneOn bernoulliCramerRateFunction (Icc (0 : ℝ) 1) := by
  have hBinEntropyAnti : StrictAntiOn Real.binEntropy (Icc (1 / 2 : ℝ) 1) := by
    simpa using Real.binEntropy_strictAntiOn
  have hHalfMono : StrictMonoOn (fun x : ℝ ↦ (1 + x) / 2) (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact halfAffineStrictMonoOn ⟨by linarith [hx.1], hx.2⟩ ⟨by linarith [hy.1], hy.2⟩ hxy
  have hHalfMaps : MapsTo (fun x : ℝ ↦ (1 + x) / 2) (Icc (0 : ℝ) 1) (Icc (1 / 2 : ℝ) 1) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hEntropyAnti :
      StrictAntiOn (fun x : ℝ ↦ Real.binEntropy ((1 + x) / 2)) (Icc (0 : ℝ) 1) := by
    exact hBinEntropyAnti.comp_strictMonoOn hHalfMono hHalfMaps
  -- Route correction: the entropy normal form turns decreasing entropy on `[1/2, 1]`
  -- into increasing rate on `[0, 1]`.
  intro x hx y hy hxy
  rw [bernoulliCramerRateFunction_eq_logTwo_sub_binEntropy x,
    bernoulliCramerRateFunction_eq_logTwo_sub_binEntropy y]
  have hEntropyLe := hEntropyAnti.antitoneOn hx hy hxy
  linarith

-- Proof sketch: the derivative of the explicit formula is nonpositive on `[-1,0]`, so the
-- function is monotone decreasing there.
/-- The Bernoulli Cramér rate function is monotone decreasing on `[-1,0]`. -/
theorem bernoulliCramerRateFunction_antitoneOn_nonpos :
    AntitoneOn bernoulliCramerRateFunction (Icc (-1 : ℝ) 0) := by
  have hBinEntropyMono : StrictMonoOn Real.binEntropy (Icc (0 : ℝ) (1 / 2 : ℝ)) := by
    simpa using Real.binEntropy_strictMonoOn
  have hHalfMono : StrictMonoOn (fun x : ℝ ↦ (1 + x) / 2) (Icc (-1 : ℝ) 0) := by
    intro x hx y hy hxy
    exact halfAffineStrictMonoOn ⟨hx.1, by linarith [hx.2]⟩ ⟨hy.1, by linarith [hy.2]⟩ hxy
  have hHalfMaps : MapsTo (fun x : ℝ ↦ (1 + x) / 2) (Icc (-1 : ℝ) 0) (Icc (0 : ℝ) (1 / 2 : ℝ)) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hEntropyMono :
      StrictMonoOn (fun x : ℝ ↦ Real.binEntropy ((1 + x) / 2)) (Icc (-1 : ℝ) 0) := by
    exact hBinEntropyMono.comp hHalfMono hHalfMaps
  -- Route correction: the entropy normal form turns increasing entropy on `[-1, 0]`
  -- into decreasing rate on `[-1, 0]`.
  intro x hx y hy hxy
  rw [bernoulliCramerRateFunction_eq_logTwo_sub_binEntropy x,
    bernoulliCramerRateFunction_eq_logTwo_sub_binEntropy y]
  have hEntropyLe := hEntropyMono.monotoneOn hx hy hxy
  linarith

end ProbabilityTheory
