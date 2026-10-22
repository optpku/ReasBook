/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology ComplexConjugate

section

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

namespace IsConvolutionSemigroup

variable {ν : NNReal → ProbabilityMeasure E} [hν : IsConvolutionSemigroup ν]

/-- Helper for Exercise 14.4.2: reindexing a `ℕ+`-sequence along `Nat.succPNat` preserves its
`atTop` limit. -/
private theorem tendsto_pnat_atTop_iff_succPNat {β : Type*} [TopologicalSpace β]
    {f : ℕ+ → β} {l : Filter β} :
    Tendsto f atTop l ↔ Tendsto (fun n : ℕ ↦ f (Nat.succPNat n)) atTop l := by
  constructor
  · intro hf
    -- Proof comment: compose the `ℕ+`-indexed limit with the order isomorphism `ℕ ≃o ℕ+`.
    simpa [OrderIso.pnatIsoNat_symm_apply] using hf.comp OrderIso.pnatIsoNat.symm.tendsto_atTop
  · intro hf
    -- Proof comment: compose the shifted sequence with `PNat.natPred` to recover the original
    -- `ℕ+`-indexing.
    have hcomp := hf.comp OrderIso.pnatIsoNat.tendsto_atTop
    convert hcomp using 1
    ext n
    simp [OrderIso.pnatIsoNat_apply]

/-- Helper for Exercise 14.4.2: along a convolution semigroup on `ℝ^d`, a positive-integer time
multiple `n • s` corresponds to the `n`fold convolution power of `ν s`. -/
private theorem semigroupPosNsmul_eq_pow
    {F : Type*} [AddCommMonoid F] [MeasurableSpace F] [MeasurableAdd₂ F]
    {σ : NNReal → ProbabilityMeasure F} [hσ : IsConvolutionSemigroup σ]
    (s : NNReal) (n : ℕ+) :
    σ ((n : ℕ) • s) = σ s ^ (n : ℕ) := by
  refine PNat.recOn n ?_ ?_
  · -- Proof comment: at `n = 1`, the statement is just the definition of the first convolution
    -- power.
    simp
  · intro k hk
    -- Proof comment: one more time step adds one more factor through the semigroup law.
    change σ (((k : ℕ) + 1) • s) = σ s ^ ((k : ℕ) + 1)
    rw [succ_nsmul, hσ.convolution_eq, hk, pow_succ]

/-- Helper for Exercise 14.4.2: for every positive integer `n`, the time slice `ν (t / n)` is an
`n`th convolution root of the fixed law `ν t`. -/
private theorem pow_div_eq
    {F : Type*} [AddCommMonoid F] [MeasurableSpace F] [MeasurableAdd₂ F]
    {σ : NNReal → ProbabilityMeasure F} [hσ : IsConvolutionSemigroup σ]
    (t : NNReal) (n : ℕ+) :
    σ (t / (n : NNReal)) ^ (n : ℕ) = σ t := by
  -- Proof comment: rewrite the `n`fold power as the semigroup law at time `n • (t / n)` and then
  -- simplify the scalar arithmetic.
  rw [← semigroupPosNsmul_eq_pow (σ := σ) (s := t / (n : NNReal)) n]
  rw [show ((n : ℕ) • (t / (n : NNReal))) = t by
    rw [nsmul_eq_mul]
    field_simp [show (n : NNReal) ≠ 0 by exact_mod_cast n.ne_zero]]

/-- Helper for Exercise 14.4.2: semigroup slices at times `t / (m * n)` are exact `m`th
convolution roots of the slice at time `t / n`. -/
private theorem pow_div_mul_eq_div
    {F : Type*} [AddCommMonoid F] [MeasurableSpace F] [MeasurableAdd₂ F]
    {σ : NNReal → ProbabilityMeasure F} [hσ : IsConvolutionSemigroup σ]
    (t : NNReal) (m n : ℕ+) :
    σ (t / ((m : NNReal) * (n : NNReal))) ^ (m : ℕ) = σ (t / (n : NNReal)) := by
  -- Proof comment: apply the exact-root identity to the slice `σ (t / n)` and normalize the
  -- double division to the denominator product `m * n`.
  simpa [div_div, mul_comm, mul_left_comm, mul_assoc] using
    (pow_div_eq (σ := σ) (t := t / (n : NNReal)) (n := m))

/-- Helper for Exercise 14.4.2: pushing forward a convolution of probability laws through a
continuous linear functional preserves the convolution product. -/
private theorem map_conv_continuousLinearMap
    (μ₁ μ₂ : ProbabilityMeasure E) (L : StrongDual ℝ E) :
    ProbabilityMeasure.map (μ₁ * μ₂) L.continuous.measurable.aemeasurable =
      ProbabilityMeasure.map μ₁ L.continuous.measurable.aemeasurable *
        ProbabilityMeasure.map μ₂ L.continuous.measurable.aemeasurable := by
  -- Proof comment: after coercing to measures, this is the standard pushforward-of-convolution
  -- identity for continuous linear maps.
  apply ProbabilityMeasure.toMeasure_injective
  simpa [ProbabilityMeasure.map] using
    (Measure.map_conv_continuousLinearMap
      (μ := (μ₁ : Measure E))
      (ν := (μ₂ : Measure E))
      (L := L))

/-- Helper for Exercise 14.4.2: convolution powers commute with pushforward along a continuous
linear functional, for positive exponents. -/
private theorem map_posPow_continuousLinearMap
    (μ : ProbabilityMeasure E) (L : StrongDual ℝ E) (n : ℕ+) :
    (ProbabilityMeasure.map μ L.continuous.measurable.aemeasurable) ^ (n : ℕ) =
      ProbabilityMeasure.map (μ ^ (n : ℕ)) L.continuous.measurable.aemeasurable := by
  refine PNat.recOn n (by simp) ?_
  intro k hk
  -- Proof comment: the inductive step rewrites the next convolution power via `pow_succ` and
  -- then pushes the extra convolution factor through the linear map.
  change
    (ProbabilityMeasure.map μ L.continuous.measurable.aemeasurable) ^ ((k : ℕ) + 1) =
      ProbabilityMeasure.map (μ ^ ((k : ℕ) + 1)) L.continuous.measurable.aemeasurable
  rw [pow_succ, pow_succ, hk, ← map_conv_continuousLinearMap]

/-- Helper for Exercise 14.4.2: projecting exact convolution roots along a continuous linear
functional preserves the exact power identity. -/
private theorem projectedRootPow_eq
    {ρs : ℕ+ → ProbabilityMeasure E} {ρ : ProbabilityMeasure E}
    (hpow : ∀ n : ℕ+, ρs n ^ (n : ℕ) = ρ)
    (L : StrongDual ℝ E) (n : ℕ+) :
    (ProbabilityMeasure.map (ρs n) L.continuous.measurable.aemeasurable) ^ (n : ℕ) =
      ProbabilityMeasure.map ρ L.continuous.measurable.aemeasurable := by
  -- Proof comment: first commute the `n`fold convolution power with the projection, then replace
  -- the powered root by the fixed target law.
  rw [map_posPow_continuousLinearMap, hpow]

/-- Helper for Exercise 14.4.2: projecting a convolution semigroup through a continuous linear
functional yields another convolution semigroup. -/
private theorem map_isConvolutionSemigroup_continuousLinearMap
    (ν₀ : NNReal → ProbabilityMeasure E) [IsConvolutionSemigroup ν₀]
    (L : StrongDual ℝ E) :
    IsConvolutionSemigroup
      (fun s : NNReal ↦ ProbabilityMeasure.map (ν₀ s) L.continuous.measurable.aemeasurable) where
  convolution_eq s t := by
    -- Proof comment: push the ambient semigroup identity through the linear map and use the
    -- convolution-pushforward compatibility.
    rw [IsConvolutionSemigroup.convolution_eq (ν := ν₀) s t]
    exact map_conv_continuousLinearMap (μ₁ := ν₀ s) (μ₂ := ν₀ t) (L := L)

/-- Helper for Exercise 14.4.2: evaluating the semigroup slice root identity at a fixed
frequency turns it into an exact power identity for characteristic-function values. -/
private theorem charFun_posPow_eq_pow
    (μ : ProbabilityMeasure ℝ) (u : ℝ) (n : ℕ+) :
    charFun (((μ ^ (n : ℕ)) : ProbabilityMeasure ℝ) : Measure ℝ) u =
      charFun ((μ : ProbabilityMeasure ℝ) : Measure ℝ) u ^ (n : ℕ) := by
  refine PNat.recOn n ?_ ?_
  · -- Proof comment: for the first power there is nothing to prove.
    simp
  · intro k hk
    -- Proof comment: the next convolution power adds one more factor, and characteristic
    -- functions multiply across convolutions.
    change charFun ((((μ ^ (k : ℕ)) * μ : ProbabilityMeasure ℝ) : Measure ℝ)) u =
        charFun ((μ : ProbabilityMeasure ℝ) : Measure ℝ) u ^ ((k : ℕ) + 1)
    simpa [pow_succ, hk] using
      (MeasureTheory.charFun_conv
        (μ := (((μ ^ (k : ℕ)) : ProbabilityMeasure ℝ) : Measure ℝ))
        (ν := ((μ : ProbabilityMeasure ℝ) : Measure ℝ))
        u)

/-- Helper for Exercise 14.4.2: evaluating the semigroup slice root identity at a fixed
frequency turns it into an exact power identity for characteristic-function values. -/
private theorem sliceCharFunPow_eq
    {σ : NNReal → ProbabilityMeasure ℝ} [hσ : IsConvolutionSemigroup σ]
    (t : NNReal) (u : ℝ) (n : ℕ+) :
    charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u ^ (n : ℕ) =
      charFun ((σ t : ProbabilityMeasure ℝ) : Measure ℝ) u := by
  -- Proof comment: first rewrite the powered slice law on the measure side, then evaluate the
  -- characteristic function of that convolution power.
  calc
    charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u ^ (n : ℕ)
        = charFun ((((σ (t / (n : NNReal))) ^ (n : ℕ)) : ProbabilityMeasure ℝ) : Measure ℝ) u := by
            symm
            exact charFun_posPow_eq_pow (σ (t / (n : NNReal))) u n
    _ = charFun ((σ t : ProbabilityMeasure ℝ) : Measure ℝ) u := by
          simp [pow_div_eq (σ := σ) (t := t) (n := n)]

/-- Helper for Exercise 14.4.2: eventual exact convolution roots give eventual whole-function
power identities for characteristic functions. -/
private theorem exactRootCharPow_eventuallyEq
    {μ : ProbabilityMeasure ℝ} {ρs : ℕ → ProbabilityMeasure ℝ}
    (hpowρ : ∀ᶠ n : ℕ in atTop, ρs n ^ n = μ) :
    ∀ᶠ n : ℕ in atTop,
      (fun s : ℝ ↦ charFun (ρs n : Measure ℝ) s ^ n) = charFun (μ : Measure ℝ) := by
  filter_upwards [eventually_gt_atTop 0, hpowρ] with n hnpos hn
  funext s
  have hchar :
      charFun (ρs n : Measure ℝ) s ^ n =
        charFun (((ρs n ^ n : ProbabilityMeasure ℝ) : Measure ℝ)) s := by
    -- Proof comment: for positive indices, the `ℕ`-power identity is the existing `ℕ+` formula
    -- after rewriting `n` as `Nat.toPNat' n`.
    simpa [PNat.toPNat'_coe hnpos] using
      (charFun_posPow_eq_pow (μ := ρs n) s (Nat.toPNat' n)).symm
  rw [hchar, hn]

/-- Helper for Exercise 14.4.2: eventual exact convolution roots make the powered characteristic
functions eventually constant at the target characteristic function. -/
private theorem exactRootCharPow_tendsto
    {μ : ProbabilityMeasure ℝ} {ρs : ℕ → ProbabilityMeasure ℝ}
    (hpowρ : ∀ᶠ n : ℕ in atTop, ρs n ^ n = μ) :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ ↦ charFun (ρs n : Measure ℝ) t ^ n) atTop
        (𝓝 (charFun (μ : Measure ℝ) t)) := by
  intro t
  have hEventuallyEq := exactRootCharPow_eventuallyEq (μ := μ) (ρs := ρs) hpowρ
  have hEventually :
      (fun n : ℕ ↦ charFun (ρs n : Measure ℝ) t ^ n) =ᶠ[atTop]
        fun _ : ℕ ↦ charFun (μ : Measure ℝ) t := by
    filter_upwards [hEventuallyEq] with n hn
    -- Proof comment: evaluate the eventual whole-function identity at the fixed frequency `t`.
    simpa using congrArg (fun f : ℝ → ℂ ↦ f t) hn
  -- Proof comment: once the sequence is eventually constant, its limit is immediate.
  exact Tendsto.congr' hEventually.symm tendsto_const_nhds

/-- Helper for Exercise 14.4.2: a positive lower bound on `r^n` bounds the logarithmic defect
`n * (1 - r)`. -/
private theorem natMulOneSub_le_negLog_of_pow_ge {r c : ℝ} {n : ℕ}
    (hr_nonneg : 0 ≤ r) (hc_pos : 0 < c) (hc_le : c ≤ r ^ n) :
    (n : ℝ) * (1 - r) ≤ -Real.log c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hc_le_one : c ≤ 1 := by simpa using hc_le
    have hlog_nonpos : Real.log c ≤ 0 := Real.log_nonpos hc_pos.le hc_le_one
    -- Proof comment: when `n = 0`, the left-hand side vanishes.
    have hneg_nonneg : 0 ≤ -Real.log c := by linarith
    simpa using hneg_nonneg
  · have hr_pow_pos : 0 < r ^ n := lt_of_lt_of_le hc_pos hc_le
    have hr_ne_zero : r ≠ 0 := by
      intro hr_zero
      rw [hr_zero, zero_pow hn.ne'] at hr_pow_pos
      exact lt_irrefl _ hr_pow_pos
    have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_ne_zero)
    have hlog_le :
        Real.log c ≤ (n : ℝ) * (r - 1) := by
      calc
        Real.log c ≤ Real.log (r ^ n) := Real.log_le_log hc_pos hc_le
        _ = (n : ℝ) * Real.log r := by
          rw [← Real.rpow_natCast, Real.log_rpow hr_pos]
        _ ≤ (n : ℝ) * (r - 1) := by
          exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr_pos) (by positivity)
    -- Proof comment: compare `log c` with `n * log r`, then use `log r ≤ r - 1`.
    linarith

/-- Helper for Exercise 14.4.2: every real probability characteristic function satisfies the
doubling-defect bound `1 - Re φ(2t) ≤ 4 (1 - Re φ(t))`. -/
private theorem oneSubReCharFun_double_le_four_mul {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (t : ℝ) :
    1 - Complex.re (charFun μ (2 * t)) ≤ 4 * (1 - Complex.re (charFun μ t)) := by
  have hint₂ : Integrable (BoundedContinuousFunction.innerProbChar (2 * t)) μ :=
    BoundedContinuousFunction.integrable μ _
  have hint₁ : Integrable (BoundedContinuousFunction.innerProbChar t) μ :=
    BoundedContinuousFunction.integrable μ _
  have hcos₂ : Integrable (fun x ↦ Real.cos (inner ℝ x (2 * t))) μ := by
    convert hint₂.re using 1
    funext x
    rw [BoundedContinuousFunction.innerProbChar_apply]
    simpa [mul_comm] using (Complex.exp_ofReal_mul_I_re (inner ℝ x (2 * t))).symm
  have hcos₁ : Integrable (fun x ↦ Real.cos (inner ℝ x t)) μ := by
    convert hint₁.re using 1
    funext x
    rw [BoundedContinuousFunction.innerProbChar_apply]
    simpa [mul_comm] using (Complex.exp_ofReal_mul_I_re (inner ℝ x t)).symm
  have hre₂ :
      Complex.re (charFun μ (2 * t)) = ∫ x, Real.cos (inner ℝ x (2 * t)) ∂μ := by
    rw [charFun_eq_integral_innerProbChar]
    calc
      Complex.re (∫ x, BoundedContinuousFunction.innerProbChar (2 * t) x ∂μ)
        = ∫ x, Complex.re (BoundedContinuousFunction.innerProbChar (2 * t) x) ∂μ := by
            simpa using (integral_re hint₂).symm
      _ = ∫ x, Real.cos (inner ℝ x (2 * t)) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [BoundedContinuousFunction.innerProbChar_apply]
            simpa [mul_comm] using Complex.exp_ofReal_mul_I_re (inner ℝ x (2 * t))
  have hre₁ : Complex.re (charFun μ t) = ∫ x, Real.cos (inner ℝ x t) ∂μ := by
    rw [charFun_eq_integral_innerProbChar]
    calc
      Complex.re (∫ x, BoundedContinuousFunction.innerProbChar t x ∂μ)
        = ∫ x, Complex.re (BoundedContinuousFunction.innerProbChar t x) ∂μ := by
            simpa using (integral_re hint₁).symm
      _ = ∫ x, Real.cos (inner ℝ x t) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [BoundedContinuousFunction.innerProbChar_apply]
            simpa [mul_comm] using Complex.exp_ofReal_mul_I_re (inner ℝ x t)
  have hleft :
      1 - Complex.re (charFun μ (2 * t)) =
        ∫ x, 1 - Real.cos (inner ℝ x (2 * t)) ∂μ := by
    -- Proof comment: rewrite the defect as the integral of the pointwise cosine defect.
    calc
      1 - Complex.re (charFun μ (2 * t))
        = ∫ x, (1 : ℝ) ∂μ - ∫ x, Real.cos (inner ℝ x (2 * t)) ∂μ := by rw [hre₂]; simp
      _ = ∫ x, 1 - Real.cos (inner ℝ x (2 * t)) ∂μ := by
        rw [← integral_sub (integrable_const 1) hcos₂]
  have hright :
      1 - Complex.re (charFun μ t) =
        ∫ x, 1 - Real.cos (inner ℝ x t) ∂μ := by
    -- Proof comment: the same rewrite at frequency `t` gives the right-hand comparison target.
    calc
      1 - Complex.re (charFun μ t)
        = ∫ x, (1 : ℝ) ∂μ - ∫ x, Real.cos (inner ℝ x t) ∂μ := by rw [hre₁]; simp
      _ = ∫ x, 1 - Real.cos (inner ℝ x t) ∂μ := by
        rw [← integral_sub (integrable_const 1) hcos₁]
  have hpoint :
      ∀ x, 1 - Real.cos (inner ℝ x (2 * t)) ≤ 4 * (1 - Real.cos (inner ℝ x t)) := by
    intro x
    have hinner_eq : inner ℝ x (2 * t) = 2 * inner ℝ x t := by
      rw [show (2 * t : ℝ) = (2 : ℝ) • t by simp, real_inner_smul_right]
    rw [hinner_eq, Real.cos_two_mul]
    nlinarith [sq_nonneg (Real.cos (inner ℝ x t) - 1)]
  rw [hleft]
  calc
    ∫ x, 1 - Real.cos (inner ℝ x (2 * t)) ∂μ
      ≤ ∫ x, 4 * (1 - Real.cos (inner ℝ x t)) ∂μ := by
          refine integral_mono ((integrable_const 1).sub hcos₂)
            (((integrable_const 1).sub hcos₁).const_mul 4) hpoint
    _ = 4 * ∫ x, 1 - Real.cos (inner ℝ x t) ∂μ := by rw [integral_const_mul]
    _ = 4 * (1 - Complex.re (charFun μ t)) := by rw [← hright]

/-- Helper for Exercise 14.4.2: the doubled-frequency defect inequality also controls the squared
modulus defect of a real characteristic function. -/
private theorem oneSubNormSqCharFun_double_le_four_mul
    (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    1 - ‖charFun ((μ : ProbabilityMeasure ℝ) : Measure ℝ) (2 * t)‖ ^ 2 ≤
      4 * (1 - ‖charFun ((μ : ProbabilityMeasure ℝ) : Measure ℝ) t‖ ^ 2) := by
  let ν : ProbabilityMeasure ℝ :=
    μ.map ((measurable_const.mul measurable_id).aemeasurable :
      AEMeasurable (fun x : ℝ ↦ (-1 : ℝ) * x) (μ : Measure ℝ))
  have hν :
      ∀ s : ℝ, charFun (ν : Measure ℝ) s = conj (charFun (μ : Measure ℝ) s) := by
    intro s
    -- Proof comment: reflecting the law replaces `s` by `-s`, which conjugates the
    -- characteristic function.
    calc
      charFun (ν : Measure ℝ) s = charFun (μ : Measure ℝ) ((-1 : ℝ) * s) := by
        simpa [ν] using (MeasureTheory.charFun_map_mul (μ := (μ : Measure ℝ)) (-1) s)
      _ = charFun (μ : Measure ℝ) (-s) := by simp
      _ = conj (charFun (μ : Measure ℝ) s) := MeasureTheory.charFun_neg s
  have hraw :
      1 - Complex.re (charFun (((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ)) (2 * t)) ≤
        4 * (1 - Complex.re (charFun (((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ)) t)) := by
    -- Proof comment: apply the real-line doubled-frequency estimate to the convolution with the
    -- reflected law.
    simpa using
      (oneSubReCharFun_double_le_four_mul
        (μ := (((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ))) t)
  have htwo :
      charFun (((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ)) (2 * t) =
        charFun (μ : Measure ℝ) (2 * t) * conj (charFun (μ : Measure ℝ) (2 * t)) := by
    calc
      charFun (((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ)) (2 * t)
          = charFun (μ : Measure ℝ) (2 * t) * charFun (ν : Measure ℝ) (2 * t) := by
              simpa using
                (MeasureTheory.charFun_conv
                  (μ := (μ : Measure ℝ))
                  (ν := (ν : Measure ℝ))
                  (2 * t))
      _ = charFun (μ : Measure ℝ) (2 * t) * conj (charFun (μ : Measure ℝ) (2 * t)) := by
            rw [hν]
  have hone :
      charFun (((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ)) t =
        charFun (μ : Measure ℝ) t * conj (charFun (μ : Measure ℝ) t) := by
    calc
      charFun (((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ)) t
          = charFun (μ : Measure ℝ) t * charFun (ν : Measure ℝ) t := by
              simpa using
                (MeasureTheory.charFun_conv
                  (μ := (μ : Measure ℝ))
                  (ν := (ν : Measure ℝ))
                  t)
      _ = charFun (μ : Measure ℝ) t * conj (charFun (μ : Measure ℝ) t) := by
            rw [hν]
  -- Proof comment: after rewriting the reflected convolution characteristic function, its real
  -- part becomes the squared modulus.
  rw [htwo, hone] at hraw
  have htwoRe :
      Complex.re
          (charFun (μ : Measure ℝ) (2 * t) * conj (charFun (μ : Measure ℝ) (2 * t))) =
        ‖charFun (μ : Measure ℝ) (2 * t)‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have honeRe :
      Complex.re (charFun (μ : Measure ℝ) t * conj (charFun (μ : Measure ℝ) t)) =
        ‖charFun (μ : Measure ℝ) t‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [htwoRe, honeRe] at hraw
  exact hraw

/-- Helper for Exercise 14.4.2: an eventual bound on `n * (1 - rₙ)` keeps the powers `rₙ^n`
uniformly away from `0`. -/
private theorem eventuallyPosLowerBoundOfEventuallyNatMulOneSubLe
    {r : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (1 - r n) ≤ C) :
    ∃ c > 0, ∀ᶠ n in atTop, c ≤ r n ^ n := by
  have hmodel :
      Tendsto (fun n : ℕ ↦ (1 - C / n) ^ n) atTop (𝓝 (Real.exp (-C))) := by
    -- Proof comment: compare with the explicit exponential model `(1 - C / n)^n → e^{-C}`.
    simpa [sub_eq_add_neg, neg_div] using Real.tendsto_one_add_div_pow_exp (-C)
  have hmodelEventually :
      ∀ᶠ n : ℕ in atTop, Real.exp (-C) / 2 < (1 - C / n) ^ n := by
    have hhalf_lt : Real.exp (-C) / 2 < Real.exp (-C) := by
      have hexp_pos : 0 < Real.exp (-C) := Real.exp_pos (-C)
      nlinarith
    exact hmodel.eventually (Ioi_mem_nhds hhalf_lt)
  have hlarge :
      ∀ᶠ n : ℕ in atTop, C < n := by
    exact tendsto_natCast_atTop_atTop.eventually_gt_atTop C
  refine ⟨Real.exp (-C) / 2, by positivity, ?_⟩
  filter_upwards [hbound, hmodelEventually, hlarge] with n hn hmodeln hnlarge
  have hn_nat_pos : 0 < n := by
    by_contra hnzero
    have hnzero' : n = 0 := Nat.eq_zero_of_not_pos hnzero
    subst hnzero'
    exact (not_lt.mpr hC) (by simpa using hnlarge)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn_nat_pos
  have hdefect : 1 - r n ≤ C / n := by
    rw [le_div_iff₀ hnpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hn
  have hbase_le : 1 - C / n ≤ r n := by
    linarith
  have hbase_nonneg : 0 ≤ 1 - C / n := by
    have hdiv_lt : C / n < 1 := by
      rw [div_lt_iff₀ hnpos]
      linarith
    linarith
  have hpow_le : (1 - C / n) ^ n ≤ r n ^ n := by
    exact pow_le_pow_left₀ hbase_nonneg hbase_le n
  -- Proof comment: the explicit exponential model transfers to `rₙ^n` by monotonicity.
  exact le_trans (le_of_lt hmodeln) hpow_le

/-- Helper for Exercise 14.4.2: exact semigroup slices have a uniform local modulus-defect bound
near the origin. -/
private theorem sliceCharFunLocalModulusDefectBoundNat
    {σ : NNReal → ProbabilityMeasure ℝ} [hσ : IsConvolutionSemigroup σ]
    (t : NNReal) :
    ∃ ε > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Set.Icc (-ε) ε,
        (n : ℝ) *
          (1 -
            ‖charFun
                ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) s‖ ^ 2) ≤ C := by
  let μ : ProbabilityMeasure ℝ := σ t
  let ρs : ℕ → ProbabilityMeasure ℝ := fun n ↦ σ (t / (Nat.toPNat' n : NNReal))
  have hpowρ : ∀ᶠ n : ℕ in atTop, ρs n ^ n = μ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hroot :
        σ (t / (Nat.toPNat' n : NNReal)) ^ n = σ t := by
      simpa [PNat.toPNat'_coe hn] using
        (pow_div_eq (σ := σ) (t := t) (n := Nat.toPNat' n))
    -- Proof comment: for positive natural indices, the semigroup slice is an exact `n`th
    -- convolution root of `σ t`.
    simpa [ρs, μ] using hroot
  have hcont0 :
      ContinuousAt (fun s : ℝ ↦ charFun (μ : Measure ℝ) s) 0 :=
    (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).continuousAt
  have hnear :
      {s : ℝ | charFun (μ : Measure ℝ) s ∈ Metric.ball (1 : ℂ) (1 / 2)} ∈ 𝓝 (0 : ℝ) := by
    -- Proof comment: continuity of `charFun (σ t)` at `0` gives a small interval where the target
    -- values stay close to `1`.
    have hnearBall :
        ∀ᶠ s : ℝ in 𝓝 (0 : ℝ),
          charFun (μ : Measure ℝ) s ∈ Metric.ball (charFun (μ : Measure ℝ) 0) (1 / 2) :=
      hcont0 (Metric.ball_mem_nhds (charFun (μ : Measure ℝ) 0)
        (show (0 : ℝ) < 1 / 2 by norm_num))
    simpa [μ, MeasureTheory.charFun_zero] using hnearBall
  rcases Metric.mem_nhds_iff.mp hnear with ⟨δ, hδpos, hδsubset⟩
  let ε : ℝ := δ / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < δ := by
    dsimp [ε]
    linarith
  have hsmall :
      ∀ s ∈ Set.Icc (-ε) ε, (1 / 2 : ℝ) < ‖charFun (μ : Measure ℝ) s‖ := by
    intro s hs
    have hsabs : |s| ≤ ε := abs_le.mpr ⟨hs.1, hs.2⟩
    have hsball : s ∈ Metric.ball (0 : ℝ) δ := by
      show dist s 0 < δ
      simpa [Real.dist_eq] using lt_of_le_of_lt hsabs hεlt
    have hclose : ‖charFun (μ : Measure ℝ) s - 1‖ < (1 / 2 : ℝ) := by
      have hsballφ : charFun (μ : Measure ℝ) s ∈ Metric.ball (1 : ℂ) (1 / 2) := hδsubset hsball
      simpa [Metric.mem_ball, dist_eq_norm] using hsballφ
    have hone_le : (1 : ℝ) ≤ ‖1 - charFun (μ : Measure ℝ) s‖ + ‖charFun (μ : Measure ℝ) s‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_add_le (1 - charFun (μ : Measure ℝ) s) (charFun (μ : Measure ℝ) s))
    have hclose' : ‖1 - charFun (μ : Measure ℝ) s‖ < (1 / 2 : ℝ) := by
      simpa [norm_sub_rev] using hclose
    nlinarith
  have hpowEq := exactRootCharPow_eventuallyEq (μ := μ) (ρs := ρs) hpowρ
  refine ⟨ε, hεpos, -Real.log (1 / 16 : ℝ), ?_, ?_⟩
  · exact neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  · filter_upwards [hpowEq] with n hn
    intro s hs
    have hμlower : (1 / 2 : ℝ) < ‖charFun (μ : Measure ℝ) s‖ := hsmall s hs
    have hpowValue :
        charFun (ρs n : Measure ℝ) s ^ n = charFun (μ : Measure ℝ) s := by
      simpa using congrArg (fun f : ℝ → ℂ ↦ f s) hn
    have hnormSq_le_one : ‖charFun (ρs n : Measure ℝ) s‖ ^ 2 ≤ 1 := by
      have hnorm_le_one :
          ‖charFun (ρs n : Measure ℝ) s‖ ≤ 1 :=
        MeasureTheory.norm_charFun_le_one (μ := (ρs n : Measure ℝ)) s
      have hnorm_nonneg : 0 ≤ ‖charFun (ρs n : Measure ℝ) s‖ := norm_nonneg _
      have hmul :
          ‖charFun (ρs n : Measure ℝ) s‖ * ‖charFun (ρs n : Measure ℝ) s‖ ≤ 1 * 1 :=
        mul_le_mul hnorm_le_one hnorm_le_one hnorm_nonneg (by positivity)
      simpa [pow_two] using hmul
    have hpowSq_ge : (1 / 16 : ℝ) ≤ (‖charFun (ρs n : Measure ℝ) s‖ ^ 2) ^ n := by
      have hsq :
          (1 / 16 : ℝ) < ‖charFun (ρs n : Measure ℝ) s ^ n‖ ^ 2 := by
        rw [hpowValue]
        have hquarter : (1 / 4 : ℝ) < ‖charFun (μ : Measure ℝ) s‖ ^ 2 := by
          nlinarith [sq_nonneg (‖charFun (μ : Measure ℝ) s‖ - 1 / 2)]
        linarith
      calc
        (1 / 16 : ℝ) ≤ ‖charFun (ρs n : Measure ℝ) s ^ n‖ ^ 2 := le_of_lt hsq
        _ = (‖charFun (ρs n : Measure ℝ) s‖ ^ 2) ^ n := by
            calc
              ‖charFun (ρs n : Measure ℝ) s ^ n‖ ^ 2 =
                  (‖charFun (ρs n : Measure ℝ) s‖ ^ n) ^ 2 := by
                    rw [norm_pow]
              _ = ‖charFun (ρs n : Measure ℝ) s‖ ^ (n * 2) := by rw [pow_mul]
              _ = ‖charFun (ρs n : Measure ℝ) s‖ ^ (2 * n) := by rw [Nat.mul_comm]
              _ = (‖charFun (ρs n : Measure ℝ) s‖ ^ 2) ^ n := by rw [pow_mul]
    -- Proof comment: the exact power identity turns the target lower bound into a logarithmic
    -- defect estimate for the exact roots.
    exact natMulOneSub_le_negLog_of_pow_ge
      (by positivity) (by norm_num) hpowSq_ge

/-- Helper for Exercise 14.4.2: the fixed-time target characteristic function of a convolution
semigroup on `ℝ` never vanishes. -/
private theorem sliceTargetCharFun_nonzero
    {σ : NNReal → ProbabilityMeasure ℝ} [hσ : IsConvolutionSemigroup σ]
    (t : NNReal) :
    ∀ u : ℝ, charFun ((σ t : ProbabilityMeasure ℝ) : Measure ℝ) u ≠ 0 := by
  rcases sliceCharFunLocalModulusDefectBoundNat (σ := σ) t with
    ⟨ε, hεpos, C, hCpos, hlocal⟩
  let μ : ProbabilityMeasure ℝ := σ t
  let ρs : ℕ → ProbabilityMeasure ℝ := fun n ↦ σ (t / (Nat.toPNat' n : NNReal))
  have hpowρ : ∀ᶠ n : ℕ in atTop, ρs n ^ n = μ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hroot :
        σ (t / (Nat.toPNat' n : NNReal)) ^ n = σ t := by
      simpa [PNat.toPNat'_coe hn] using
        (pow_div_eq (σ := σ) (t := t) (n := Nat.toPNat' n))
    -- Proof comment: for positive natural indices, `ρs n` is the exact `n`th semigroup slice
    -- root of `μ = σ t`.
    simpa [ρs, μ] using hroot
  intro u
  have hdyadic :
      ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
        ∀ s ∈ Set.Icc (-((2 ^ k : ℝ) * ε)) ((2 ^ k : ℝ) * ε),
          (n : ℝ) *
            (1 -
              ‖charFun
                  ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) s‖ ^ 2)
            ≤ (4 ^ k : ℝ) * C := by
    intro k
    induction k with
    | zero =>
        -- Proof comment: the base dyadic interval is exactly the local defect estimate.
        filter_upwards [hlocal] with n hn s hs
        simpa using hn s (by simpa using hs)
    | succ k ih =>
        filter_upwards [ih] with n hn s hs
        let v : ℝ := s / 2
        have hs_two : 2 * v = s := by
          dsimp [v]
          ring_nf
        have hpow2 : ((2 ^ (k + 1) : ℝ) * ε) = 2 * ((2 ^ k : ℝ) * ε) := by
          simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
        have hv :
            v ∈ Set.Icc (-((2 ^ k : ℝ) * ε)) ((2 ^ k : ℝ) * ε) := by
          rw [hpow2] at hs
          constructor
          · have hsleft := hs.1
            dsimp [v]
            nlinarith
          · have hsright := hs.2
            dsimp [v]
            nlinarith
        have hdbl :
            1 -
                ‖charFun
                    ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) s‖ ^ 2
              ≤
                4 *
                  (1 -
                    ‖charFun
                        ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ)
                        v‖ ^ 2) := by
          -- Proof comment: apply the doubled-frequency squared-modulus inequality to the `n`th
          -- semigroup slice.
          simpa [v, hs_two] using
            (oneSubNormSqCharFun_double_le_four_mul
              (μ := σ (t / (Nat.toPNat' n : NNReal))) v)
        calc
          (n : ℝ) *
              (1 -
                ‖charFun
                    ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) s‖ ^ 2)
              ≤
                (n : ℝ) *
                  (4 *
                    (1 -
                      ‖charFun
                          ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ)
                          v‖ ^ 2)) := by
                    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
                    gcongr
          _ =
              4 *
                ((n : ℝ) *
                  (1 -
                    ‖charFun
                        ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ)
                        v‖ ^ 2)) := by ring
          _ ≤ 4 * ((4 ^ k : ℝ) * C) := by
                have hvBound := hn v hv
                nlinarith
          _ = (4 ^ (k + 1) : ℝ) * C := by
                simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (|u| / ε) (show (1 : ℝ) < 2 by norm_num)
  have huk : |u| ≤ (2 ^ k : ℝ) * ε := by
    have hk' : |u| / ε < (2 ^ k : ℝ) := by simpa using hk
    have := (div_lt_iff₀ hεpos).mp hk'
    exact le_of_lt (by simpa [mul_comm] using this)
  have huIcc : u ∈ Set.Icc (-((2 ^ k : ℝ) * ε)) ((2 ^ k : ℝ) * ε) := by
    simpa [abs_le] using huk
  have hbound_u :
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) *
          (1 -
            ‖charFun
                ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u‖ ^ 2)
          ≤ (4 ^ k : ℝ) * C := by
    filter_upwards [hdyadic k] with n hn
    exact hn u huIcc
  obtain ⟨c, hcpos, hcbound⟩ :=
    eventuallyPosLowerBoundOfEventuallyNatMulOneSubLe
      (C := (4 ^ k : ℝ) * C)
      (by positivity)
      hbound_u
  have hpowNormSq :
      Tendsto
        (fun n : ℕ ↦
          (‖charFun
              ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u‖ ^ 2) ^ n)
        atTop
        (𝓝 (‖charFun (μ : Measure ℝ) u‖ ^ 2)) := by
    have hnorm :
        Tendsto
          (fun n : ℕ ↦
            ‖charFun
                ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u ^ n‖)
          atTop
          (𝓝 ‖charFun (μ : Measure ℝ) u‖) :=
      Tendsto.norm (exactRootCharPow_tendsto (μ := μ) (ρs := ρs) hpowρ u)
    have hsq :
        Tendsto
          (fun n : ℕ ↦
            ‖charFun
                ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u ^ n‖ ^ 2)
          atTop
          (𝓝 (‖charFun (μ : Measure ℝ) u‖ ^ 2)) :=
      hnorm.pow 2
    have hrewrite :
        ∀ n : ℕ,
          ‖charFun
              ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u ^ n‖ ^ 2 =
            (‖charFun
                ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u‖ ^ 2) ^ n := by
      intro n
      calc
        ‖charFun
              ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u ^ n‖ ^ 2 =
            (‖charFun
                ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u‖ ^ n) ^ 2 := by
                  rw [norm_pow]
        _ =
            ‖charFun
                ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u‖ ^
              (n * 2) := by
                rw [pow_mul]
        _ =
            ‖charFun
                ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u‖ ^
              (2 * n) := by
                rw [Nat.mul_comm]
        _ =
            (‖charFun
                ((σ (t / (Nat.toPNat' n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u‖ ^ 2) ^ n := by
                rw [pow_mul]
    exact hsq.congr' (Eventually.of_forall hrewrite)
  have hlimit_lower : c ≤ ‖charFun (μ : Measure ℝ) u‖ ^ 2 := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hpowNormSq hcbound
  have hnormsq_pos : 0 < ‖charFun (μ : Measure ℝ) u‖ ^ 2 := lt_of_lt_of_le hcpos hlimit_lower
  -- Proof comment: a strictly positive norm square rules out a zero of the target
  -- characteristic function.
  exact fun hzero ↦ by simpa [μ, hzero] using hnormsq_pos

/-- Helper for Exercise 14.4.2: on the closed unit disk, the squared distance to `1` is
controlled by the real-part defect. -/
private theorem sqNormSubOne_le_two_mul_one_sub_re {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖z - 1‖ ^ 2 ≤ 2 * (1 - Complex.re z) := by
  have hzsq : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz, norm_nonneg z]
  -- Proof comment: expand `‖z - 1‖²` through `normSq` and use the closed-unit-disk bound
  -- `‖z‖² ≤ 1`.
  calc
    ‖z - 1‖ ^ 2 = Complex.normSq (z - 1) := by rw [← Complex.normSq_eq_norm_sq]
    _ = Complex.normSq z + 1 - 2 * Complex.re z := by
      rw [Complex.normSq_sub]
      simp
    _ ≤ 1 + 1 - 2 * Complex.re z := by
      nlinarith
    _ = 2 * (1 - Complex.re z) := by ring

/-- Helper for Exercise 14.4.2: a Nat-indexed closed-unit-disk sequence whose shifted exact-root
exponential limit is nonzero must converge to `1`. -/
private theorem unitDiskExpLimit_tendstoOne_shifted
    {z : ℕ → ℂ} {c : ℂ}
    (hz : ∀ n : ℕ, ‖z n‖ ≤ 1) (hc : c ≠ 0)
    (hexp :
      Tendsto (fun n : ℕ ↦ Complex.exp (((n + 1 : ℕ) : ℂ) * (z n - 1))) atTop (𝓝 c)) :
    Tendsto z atTop (𝓝 1) := by
  have hlogNorm :
      Tendsto (fun n : ℕ ↦ Real.log ‖Complex.exp (((n + 1 : ℕ) : ℂ) * (z n - 1))‖)
        atTop (𝓝 (Real.log ‖c‖)) := by
    -- Proof comment: the exponential limit stays away from `0`, so norms and then logs preserve
    -- the limit.
    exact (Real.continuousAt_log (norm_ne_zero_iff.mpr hc)).tendsto.comp hexp.norm
  have hscaledRe :
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) * (Complex.re (z n) - 1)) atTop
        (𝓝 (Real.log ‖c‖)) := by
    -- Proof comment: `‖exp w‖ = exp (Re w)` turns the logarithmic norm limit into a limit for
    -- the scaled real-part defect.
    simpa [Complex.norm_exp, Complex.mul_re, Complex.sub_re] using hlogNorm
  have hinv :
      Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
    -- Proof comment: the reciprocal of the shifted index still tends to `0`.
    exact tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hReSubMul :
      Tendsto
        (fun n : ℕ ↦
          (((n + 1 : ℕ) : ℝ) * (Complex.re (z n) - 1)) * (((n + 1 : ℕ) : ℝ)⁻¹))
        atTop
        (𝓝 0) := by
    -- Proof comment: multiplying the scaled defect by `1 / (n + 1)` recovers the unscaled
    -- real-part defect.
    simpa using hscaledRe.mul hinv
  have hReSubEventually :
      (fun n : ℕ ↦
        (((n + 1 : ℕ) : ℝ) * (Complex.re (z n) - 1)) * (((n + 1 : ℕ) : ℝ)⁻¹)) =ᶠ[atTop]
        fun n ↦ Complex.re (z n) - 1 := by
    filter_upwards with n
    have hn0 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    -- Proof comment: for every index, the compensating factor `(n + 1) * (n + 1)⁻¹` equals `1`.
    calc
      (((n + 1 : ℕ) : ℝ) * (Complex.re (z n) - 1)) * (((n + 1 : ℕ) : ℝ)⁻¹)
          = ((((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ)⁻¹)) * (Complex.re (z n) - 1)) := by ring
      _ = Complex.re (z n) - 1 := by rw [mul_inv_cancel₀ hn0, one_mul]
  have hReSub : Tendsto (fun n : ℕ ↦ Complex.re (z n) - 1) atTop (𝓝 0) :=
    hReSubMul.congr' hReSubEventually
  have hRe : Tendsto (fun n : ℕ ↦ Complex.re (z n)) atTop (𝓝 1) := by
    -- Proof comment: add back the constant `1` after controlling the real-part defect.
    simpa using hReSub.const_add (1 : ℝ)
  have hsq :
      Tendsto (fun n : ℕ ↦ ‖z n - 1‖ ^ 2) atTop (𝓝 0) := by
    have honeSub : Tendsto (fun n : ℕ ↦ (1 : ℝ) - Complex.re (z n)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hRe
    have hupper :
        Tendsto (fun n : ℕ ↦ 2 * (1 - Complex.re (z n))) atTop (𝓝 0) := by
      -- Proof comment: once the real parts converge to `1`, the closed-unit-disk upper bound
      -- for `‖z n - 1‖²` tends to `0`.
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2)).mul honeSub
    -- Proof comment: squeeze the squared norm between `0` and the real-part defect.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · filter_upwards with n
      exact sq_nonneg ‖z n - 1‖
    · filter_upwards with n
      exact sqNormSubOne_le_two_mul_one_sub_re (hz n)
  have hnormSub : Tendsto (fun n : ℕ ↦ ‖z n - 1‖) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      -- Proof comment: the norm is always nonnegative, so every negative lower bound is
      -- eventually satisfied.
      filter_upwards with n
      exact lt_of_lt_of_le ha (norm_nonneg _)
    · intro a ha
      have hsqUpper : ∀ᶠ n : ℕ in atTop, ‖z n - 1‖ ^ 2 < a ^ 2 :=
        (tendsto_order.1 hsq).2 (a ^ 2) (by positivity)
      -- Proof comment: once the squares are eventually smaller than `a²`, positivity upgrades the
      -- estimate to `‖z n - 1‖ < a`.
      filter_upwards [hsqUpper] with n hn
      nlinarith [hn, norm_nonneg (z n - 1), ha]
  -- Proof comment: convergence of `‖z n - 1‖` to `0` is exactly convergence of `z n` to `1`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa using hnormSub

/-- Helper for Exercise 14.4.2: a `ℕ+`-indexed closed-unit-disk sequence whose exact-root
exponential limit is nonzero must converge to `1`. -/
private theorem unitDiskExpLimit_tendstoOne
    {z : ℕ+ → ℂ} {c : ℂ}
    (hz : ∀ n : ℕ+, ‖z n‖ ≤ 1) (hc : c ≠ 0)
    (hexp : Tendsto (fun n : ℕ+ ↦ Complex.exp ((n : ℂ) * (z n - 1))) atTop (𝓝 c)) :
    Tendsto z atTop (𝓝 1) := by
  have hNatExp :
      Tendsto
        (fun n : ℕ ↦ Complex.exp (((Nat.succPNat n : ℕ+) : ℂ) * (z (Nat.succPNat n) - 1)))
        atTop
        (𝓝 c) := by
    -- Proof comment: reindex the `ℕ+`-sequence along `Nat.succPNat` so the shifted Nat lemma
    -- applies.
    simpa [Nat.succPNat_coe] using (tendsto_pnat_atTop_iff_succPNat.1 hexp)
  have hNat :
      Tendsto (fun n : ℕ ↦ z (Nat.succPNat n)) atTop (𝓝 (1 : ℂ)) :=
    unitDiskExpLimit_tendstoOne_shifted
      (z := fun n : ℕ ↦ z (Nat.succPNat n))
      (c := c)
      (fun n ↦ hz (Nat.succPNat n))
      hc
      hNatExp
  -- Proof comment: transfer the Nat-indexed convergence back to the original `ℕ+` sequence.
  exact (tendsto_pnat_atTop_iff_succPNat).2 hNat

/-- Helper for Exercise 14.4.2: the zero-free target characteristic-function path on
`Set.uIcc 0 u` admits a continuous logarithmic lift normalized to vanish at `0`. -/
private theorem sliceCharFunSegmentLogLiftOn_uIcc
    {σ : NNReal → ProbabilityMeasure ℝ} [hσ : IsConvolutionSemigroup σ]
    (t : NNReal) (u : ℝ) :
    ∃ ψ : C(Set.uIcc (0 : ℝ) u, ℂ),
      ψ ⟨0, by simp⟩ = 0 ∧
      ∀ x, Complex.exp (ψ x) = charFun ((σ t : ProbabilityMeasure ℝ) : Measure ℝ) x := by
  let A : Set ℝ := Set.uIcc (0 : ℝ) u
  letI : ContractibleSpace A := (convex_uIcc (0 : ℝ) u).contractibleSpace ⟨0, by simp [A]⟩
  letI : LocPathConnectedSpace A := (convex_uIcc (0 : ℝ) u).locPathConnectedSpace
  let χLift : C(A, {z : ℂ // z ≠ 0}) :=
    ⟨fun x ↦ ⟨charFun ((σ t : ProbabilityMeasure ℝ) : Measure ℝ) x,
        sliceTargetCharFun_nonzero (σ := σ) t x⟩, by
      -- Proof comment: restriction to the interval lands in `ℂ \ {0}` by the zero-free target
      -- characteristic function.
      refine Continuous.subtype_mk ?_ ?_
      simpa using
        (MeasureTheory.continuous_charFun
          (μ := ((σ t : ProbabilityMeasure ℝ) : Measure ℝ))).comp continuous_subtype_val⟩
  rcases Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts χLift ⟨0, by simp [A]⟩ 0
      (by simpa [χLift, MeasureTheory.charFun_zero]) with ⟨ψ, hψ, _⟩
  refine ⟨ψ, hψ.1, ?_⟩
  intro x
  -- Proof comment: forgetting the subtype in the lifted identity gives the desired exponential
  -- representation on the whole interval.
  have hψx := congrArg (fun f : A → {z : ℂ // z ≠ 0} ↦ f x) hψ.2
  simpa [χLift, Function.comp] using congrArg Subtype.val hψx

/-- Helper for Exercise 14.4.2: dividing a semigroup slice characteristic function by the lifted
target exponential produces an `n`th root of unity at every interval point. -/
private theorem sliceCharFunQuotientPow_eq_one_on_uIcc
    {σ : NNReal → ProbabilityMeasure ℝ} [hσ : IsConvolutionSemigroup σ]
    (t : NNReal) (u : ℝ) {n : ℕ+}
    {ψ : C(Set.uIcc (0 : ℝ) u, ℂ)}
    (hexp : ∀ x, Complex.exp (ψ x) = charFun ((σ t : ProbabilityMeasure ℝ) : Measure ℝ) x)
    (x : Set.uIcc (0 : ℝ) u) :
    ((charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) x) /
        Complex.exp (ψ x / (n : ℂ))) ^ (n : ℕ) = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  calc
    ((charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) x) /
          Complex.exp (ψ x / (n : ℂ))) ^ (n : ℕ)
        =
          charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) x ^ (n : ℕ) /
            Complex.exp (ψ x / (n : ℂ)) ^ (n : ℕ) := by
              rw [div_pow]
    _ =
        charFun ((σ t : ProbabilityMeasure ℝ) : Measure ℝ) x /
          Complex.exp ((n : ℂ) * (ψ x / (n : ℂ))) := by
            rw [sliceCharFunPow_eq (σ := σ) (t := t) (u := x) (n := n), ← Complex.exp_nat_mul]
    _ = charFun ((σ t : ProbabilityMeasure ℝ) : Measure ℝ) x / Complex.exp (ψ x) := by
          congr 2
          field_simp [hn0]
    _ = Complex.exp (ψ x) / Complex.exp (ψ x) := by rw [hexp x]
    _ = 1 := by field_simp

/-- Helper for Exercise 14.4.2: on `Set.uIcc 0 u`, each semigroup slice characteristic function
agrees with the normalized exponential of the target logarithm lift. -/
private theorem sliceCharFunSegmentRepresentationOn_uIcc
    {σ : NNReal → ProbabilityMeasure ℝ} [hσ : IsConvolutionSemigroup σ]
    (t : NNReal) (u : ℝ)
    {ψ : C(Set.uIcc (0 : ℝ) u, ℂ)}
    (hψ0 : ψ ⟨0, by simp⟩ = 0)
    (hexp : ∀ x, Complex.exp (ψ x) = charFun ((σ t : ProbabilityMeasure ℝ) : Measure ℝ) x) :
    ∀ n : ℕ+, ∀ x : Set.uIcc (0 : ℝ) u,
      charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) x =
        Complex.exp (ψ x / (n : ℂ)) := by
  intro n x
  let A : Set ℝ := Set.uIcc (0 : ℝ) u
  letI : ContractibleSpace A := (convex_uIcc (0 : ℝ) u).contractibleSpace ⟨0, by simp [A]⟩
  let T : Set ℂ := Set.range fun ζ : rootsOfUnity (n : ℕ) ℂ => ((ζ : Units ℂ) : ℂ)
  let q : A → ℂ := fun y ↦
    charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) y /
      Complex.exp (ψ y / (n : ℂ))
  have hqcont : Continuous q := by
    have hnum : Continuous fun y : A ↦
        charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) y := by
      simpa using
        (MeasureTheory.continuous_charFun
          (μ := ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ))).comp
            continuous_subtype_val
    have hden : Continuous fun y : A ↦ Complex.exp (ψ y / (n : ℂ)) := by
      -- Proof comment: the denominator is the exponential of the continuous logarithm lift
      -- divided by the constant index `n`.
      simpa using Complex.continuous_exp.comp (ψ.continuous.div_const (n : ℂ))
    exact hnum.div hden fun y ↦ Complex.exp_ne_zero _
  have hqmaps : Set.MapsTo q (Set.univ : Set A) T := by
    intro y hy
    refine ⟨rootsOfUnity.mkOfPowEq (q y)
      (sliceCharFunQuotientPow_eq_one_on_uIcc
        (σ := σ) (t := t) (u := u) (n := n) (ψ := ψ) hexp y), ?_⟩
    simp [T, q, rootsOfUnity.coe_mkOfPowEq]
  have hTdiscrete :
      IsDiscrete T := (Set.finite_range
        fun ζ : rootsOfUnity (n : ℕ) ℂ => ((ζ : Units ℂ) : ℂ)).isDiscrete
  have hconst : q x = q ⟨0, by simp [A]⟩ := by
    -- Proof comment: the interval subtype is contractible, hence preconnected, so a continuous
    -- map into a finite discrete set must be constant on `Set.univ`.
    exact isPreconnected_univ.constant_of_mapsTo hTdiscrete hqcont.continuousOn hqmaps
      (by simp) (by simp)
  have hqzero : q ⟨0, by simp [A]⟩ = 1 := by
    -- Proof comment: at the left endpoint, both the characteristic function and the lifted
    -- exponential equal `1`.
    simp [q, hψ0, MeasureTheory.charFun_zero]
  have hqone : q x = 1 := hconst.trans hqzero
  have hden_ne : Complex.exp (ψ x / (n : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  -- Proof comment: clearing the nonzero denominator identifies the slice with the normalized
  -- exponential model.
  have hmul :
      charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) x =
        1 * Complex.exp (ψ x / (n : ℂ)) := by
    exact (div_eq_iff hden_ne).mp (by simpa [q] using hqone)
  calc
    charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) x =
        1 * Complex.exp (ψ x / (n : ℂ)) := hmul
    _ = Complex.exp (ψ x / (n : ℂ)) := by simp

/-- Helper for Exercise 14.4.2: on the compact segment `Set.uIcc 0 u`, the nonvanishing target
characteristic function admits a continuous logarithmic lift whose normalized exponentials agree
eventually with the semigroup slice characteristic functions. -/
private theorem sliceCharFun_eventually_eq_exp_logLift
    {σ : NNReal → ProbabilityMeasure ℝ} [hσ : IsConvolutionSemigroup σ]
    (t : NNReal) (u : ℝ) :
    ∃ ψ : C(Set.uIcc (0 : ℝ) u, ℂ),
      ψ ⟨0, by simp⟩ = 0 ∧
      (∀ x, Complex.exp (ψ x) = charFun ((σ t : ProbabilityMeasure ℝ) : Measure ℝ) x) ∧
      ∀ᶠ n : ℕ+ in atTop,
        ∀ x : Set.uIcc (0 : ℝ) u,
          charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) x =
            Complex.exp (ψ x / (n : ℂ)) := by
  -- Route correction: the old scalar endgame asked directly for the exponential limit at the
  -- endpoint `u`. The remaining structural step is more precise: build the logarithm lift as a
  -- continuous map on the interval subtype, then package the exact root representation as an
  -- eventual statement only at the very end.
  rcases sliceCharFunSegmentLogLiftOn_uIcc (σ := σ) t u with ⟨ψ, hψ0, hexp⟩
  refine ⟨ψ, hψ0, hexp, ?_⟩
  -- Proof comment: the stronger interval identity already holds for every positive integer, so the
  -- eventual statement is immediate.
  exact Filter.Eventually.of_forall
    (sliceCharFunSegmentRepresentationOn_uIcc (σ := σ) t u hψ0 hexp)

/-- Helper for Exercise 14.4.2: for a one-dimensional convolution semigroup, the semigroup slices
`σ (t / n)` have characteristic functions converging pointwise to `1`. -/
private theorem oneDimensionalSemigroupSliceCharFun_tendsto_one
    {σ : NNReal → ProbabilityMeasure ℝ} [hσ : IsConvolutionSemigroup σ] (t : NNReal) :
    ∀ u : ℝ,
      Tendsto
        (fun n : ℕ+ ↦ charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u)
        atTop
        (𝓝 1) := by
  -- Route correction: instead of first proving a linearized exponential limit at the endpoint,
  -- work with a theorem-local logarithm lift on the whole interval `Set.uIcc 0 u`. Once the slice
  -- characteristic functions are identified with `exp (ψ(·) / n)` on that interval, the endpoint
  -- limit follows directly from continuity of `exp` at `0`.
  intro u
  rcases sliceCharFun_eventually_eq_exp_logLift (σ := σ) t u with ⟨ψ, hψ0, hexp, hsegment⟩
  let endpoint : Set.uIcc (0 : ℝ) u := ⟨u, by simp⟩
  have hsegmentEndpoint :
      (fun n : ℕ+ ↦ charFun ((σ (t / (n : NNReal)) : ProbabilityMeasure ℝ) : Measure ℝ) u) =ᶠ[atTop]
        fun n : ℕ+ ↦ Complex.exp (ψ endpoint / (n : ℂ)) := by
    filter_upwards [hsegment] with n hn
    simpa [endpoint] using hn endpoint
  have hdivNat :
      Tendsto (fun n : ℕ ↦ ψ endpoint / (((n + 1 : ℕ) : ℂ))) atTop (𝓝 0) := by
    have hinvReal :
        Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
      exact tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hinv :
        Tendsto (fun n : ℕ ↦ Complex.ofReal (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
      exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hinvReal
    -- Proof comment: the endpoint value is constant, so dividing by the diverging index tends to
    -- zero.
    simpa [div_eq_mul_inv, Complex.ofReal_inv] using tendsto_const_nhds.mul hinv
  have hdiv :
      Tendsto (fun n : ℕ+ ↦ ψ endpoint / (n : ℂ)) atTop (𝓝 0) := by
    refine (tendsto_pnat_atTop_iff_succPNat).2 ?_
    simpa [Nat.succPNat_coe] using hdivNat
  have hexpLimit :
      Tendsto (fun n : ℕ+ ↦ Complex.exp (ψ endpoint / (n : ℂ))) atTop (𝓝 1) := by
    simpa using Filter.Tendsto.cexp hdiv
  -- Proof comment: evaluate the interval identity at the endpoint and then use continuity of
  -- `Complex.exp` at `0`.
  exact Tendsto.congr' hsegmentEndpoint.symm hexpLimit

/-- Helper for Exercise 14.4.2: after projecting the semigroup slices along a continuous linear
functional, the resulting dual characteristic functions converge pointwise to `1`. -/
private theorem projectedDivCharFunDual_tendsto_one
    (ν₀ : NNReal → ProbabilityMeasure E) [IsConvolutionSemigroup ν₀]
    (t : NNReal) (L : StrongDual ℝ E) :
    Tendsto
      (fun n : ℕ+ ↦ charFunDual (((ν₀ (t / (n : NNReal)) : ProbabilityMeasure E) : Measure E)) L)
      atTop
      (𝓝 1) := by
  -- Proof comment: once the projected slice family is registered as a one-dimensional
  -- convolution semigroup, this is an immediate rewrite to the scalar slice theorem.
  let σL : NNReal → ProbabilityMeasure ℝ :=
    fun s ↦ ProbabilityMeasure.map (ν₀ s) L.continuous.measurable.aemeasurable
  letI : IsConvolutionSemigroup σL :=
    map_isConvolutionSemigroup_continuousLinearMap (ν₀ := ν₀) L
  have hscalar :=
    oneDimensionalSemigroupSliceCharFun_tendsto_one (σ := σL) t (1 : ℝ)
  -- Proof comment: rewrite the projected characteristic function at frequency `1` back to the
  -- ambient dual characteristic function.
  simpa [σL, MeasureTheory.charFunDual_eq_charFun_map_one] using hscalar

/-- Helper for Exercise 14.4.2: the semigroup slices `ν (t / n)` converge weakly to
`diracProba 0`. -/
private theorem divPnat_tendsto_diracZero
    (ν₀ : NNReal → ProbabilityMeasure E) [IsConvolutionSemigroup ν₀] (t : NNReal) :
    Tendsto (fun n : ℕ+ ↦ ν₀ (t / (n : NNReal))) atTop (𝓝 (diracProba (0 : E))) := by
  -- Proof comment: after the scalar slice theorem and the projected dual-characteristic-function
  -- rewrite are in place, Lévy's continuity theorem closes this exactly as in the earlier generic
  -- root-based proof.
  apply (tendsto_pnat_atTop_iff_succPNat).2
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
  intro x
  have hdual :
      Tendsto
        (fun n : ℕ ↦
          charFunDual
            (((ν₀ (t / (Nat.succPNat n : NNReal)) : ProbabilityMeasure E) : Measure E))
            (InnerProductSpace.toDualMap ℝ E x))
        atTop
        (𝓝 1) := by
    -- Proof comment: reindex the `ℕ+`-limit from the projected slice theorem to a standard
    -- `ℕ`-sequence.
    exact
      (tendsto_pnat_atTop_iff_succPNat).1
        (projectedDivCharFunDual_tendsto_one
          (ν₀ := ν₀) t (InnerProductSpace.toDualMap ℝ E x))
  have hdirac :
      charFunDual
        (((diracProba (0 : E) : ProbabilityMeasure E) : Measure E))
        (InnerProductSpace.toDualMap ℝ E x) = 1 := by
    simpa [MeasureTheory.diracProba] using
      (MeasureTheory.charFunDual_dirac
        (x := (0 : E))
        (L := InnerProductSpace.toDualMap ℝ E x))
  -- Proof comment: convert the dual characteristic-function limit back to the ordinary
  -- characteristic function and identify the Dirac target.
  simpa [MeasureTheory.charFun_eq_charFunDual_toDualMap, hdirac] using hdual

/-- Exercise 14.4.2: for every fixed `t ≥ 0`, the subdivided marginals `ν (t / n)` of a
convolution semigroup on the chapter's `ℝ^d` model converge weakly to the Dirac probability
measure at `0` as `n → ∞` through positive integers. -/
-- Proof sketch: write `ν t` as an `n`-fold convolution power of `ν (t / n)` using the semigroup
-- law on `ℝ^d`, then apply the standard infinitesimality criterion for convolution roots of a
-- fixed probability measure in this finite-dimensional real-vector-space setting to conclude weak
-- convergence to `δ₀`.
theorem tendsto_div_pNat_diracProba_zero (t : NNReal) :
    Tendsto (fun n : ℕ+ ↦ ν (t / (n : NNReal))) atTop (𝓝 (diracProba (0 : Fin d → ℝ))) := by
  -- Proof comment: the proof has been refactored to work directly with the semigroup slices
  -- `ν (t / n)`, so the final step is the specialized weak-convergence lemma above.
  exact divPnat_tendsto_diracZero (ν₀ := ν) t

end IsConvolutionSemigroup

end
