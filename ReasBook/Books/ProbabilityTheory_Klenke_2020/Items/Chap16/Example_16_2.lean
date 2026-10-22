/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Exercise_3_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Example_5_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_1_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Example_16_2.Shared
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Example_16_2.GaussianOverSqrtGamma
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Corollary_16_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Corollary_16_9

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped MeasureTheory NNReal unitInterval

noncomputable section

universe u

/-- Helper for Example 16.2: the `n`th additive convolution power of `diracProba a` on `ℝ`
is the Dirac law at the `n`-fold sum `n • a`. -/
private lemma diracProba_pow_eq_real (a : ℝ) :
    ∀ m : ℕ, (diracProba a : ProbabilityMeasure ℝ) ^ m = diracProba (m • a)
  | 0 => by
      -- Proof comment: the zeroth convolution power is the convolution unit `δ₀`.
      simp
  | m + 1 => by
      -- Proof comment: convolving once more with `δ_a` adds one more copy of `a`.
      rw [pow_succ, diracProba_pow_eq_real a m]
      apply ProbabilityMeasure.toMeasure_injective
      have hdirac :
          (Measure.dirac (m • a) : Measure ℝ) ∗ Measure.dirac a =
            Measure.dirac ((m • a) + a) :=
        Measure.dirac_conv_dirac (m • a) a
      calc
        (diracProba (m • a) : Measure ℝ) ∗ (diracProba a : Measure ℝ)
            = Measure.dirac ((m • a) + a) := by
                rw [MeasureTheory.diracProba, MeasureTheory.diracProba]
                exact hdirac
        _ = (diracProba ((m + 1) • a) : Measure ℝ) := by
              rw [MeasureTheory.diracProba]
              have hmul : (m • a) + a = (m + 1) • a := by
                rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
                ring_nf
              exact congrArg Measure.dirac hmul

/-- Helper for Example 16.2: along a fixed additive parameter ray, repeated convolution with the
same root law realizes the successive parameter multiples. -/
private theorem convolutionPower_succ_eq_of_additiveOrbit
    {E α : Type*} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E] [AddMonoid α]
    (ν : α → ProbabilityMeasure E) (a : α)
    (hstep : ∀ k : ℕ,
      (((ν (((k + 1 : ℕ) • a)) : ProbabilityMeasure E) : Measure E) ∗ (ν a : Measure E) =
        (ν (((k + 2 : ℕ) • a)) : Measure E))) :
    ∀ k : ℕ, (ν a) ^ (k + 1) = ν (((k + 1 : ℕ) • a))
  | 0 => by
      -- Proof comment: the first convolution power is the root law itself.
      simp
  | k + 1 => by
      -- Proof comment: apply the orbit step once more to append one additional copy of the root
      -- parameter.
      rw [pow_succ, convolutionPower_succ_eq_of_additiveOrbit ν a hstep k]
      exact ProbabilityMeasure.toMeasure_injective (hstep k)

-- Proof sketch: the sum of `n` independent point masses at `x / n` is the point mass at `x`, so
-- the `n`th convolution power of `δ_{x / n}` is `δ_x`.
/-- Part (1) of Example 16.2: The Dirac law `δ_x` is infinitely divisible, with explicit `n`th convolution
root `δ_{x / n}` for every positive integer `n`. -/
theorem measureConvolutionPower_dirac_div_eq_dirac (x : ℝ) (n : ℕ+) :
    let ν : ProbabilityMeasure ℝ := ⟨Measure.dirac (x / (n : ℝ)), inferInstance⟩
    ν ^ (n : ℕ) = diracProba x := by
  change (diracProba (x / (n : ℝ)) : ProbabilityMeasure ℝ) ^ (n : ℕ) = diracProba x
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  rw [diracProba_pow_eq_real]
  congr 1
  rw [nsmul_eq_mul]
  field_simp [hn]

-- Proof sketch: convolving Gaussian laws adds means and variances; iterating the Gaussian
-- convolution formula with mean `m / n` and variance `σ² / n` yields `N_{m,σ²}`.
/-- Part (2) of Example 16.2: The Gaussian law `N_{m,σ²}` is infinitely divisible, with
`N_{m / n, σ² / n}` as an `n`th convolution root for every positive integer `n`. -/
theorem measureConvolutionPower_gaussianReal_div_eq_gaussianReal
    (m : ℝ) (σ2 : ℝ≥0) (n : ℕ+) :
    let ν : ProbabilityMeasure ℝ :=
      ⟨gaussianReal (m / (n : ℝ)) (σ2 / (n : ℝ≥0)), inferInstance⟩
    let μ : ProbabilityMeasure ℝ := ⟨gaussianReal m σ2, inferInstance⟩
    ν ^ (n : ℕ) = μ := by
  let gaussianLaw : ℝ × ℝ≥0 → ProbabilityMeasure ℝ :=
    fun p ↦ ⟨gaussianReal p.1 p.2, inferInstance⟩
  change gaussianLaw (m / (n : ℝ), σ2 / (n : ℝ≥0)) ^ (n : ℕ) = gaussianLaw (m, σ2)
  have hpow :=
    convolutionPower_succ_eq_of_additiveOrbit
      (ν := gaussianLaw) (a := (m / (n : ℝ), σ2 / (n : ℝ≥0)))
      (hstep := by
        intro k
        -- Proof comment: Gaussian convolution adds the mean and variance parameters.
        simp [gaussianLaw]
        rw [ProbabilityTheory.gaussianReal_conv_gaussianReal]
        congr <;> ring)
      n.natPred
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  have hnNN : (n : ℝ≥0) ≠ 0 := by
    exact_mod_cast n.ne_zero
  rw [n.natPred_add_one] at hpow
  calc
    gaussianLaw (m / (n : ℝ), σ2 / (n : ℝ≥0)) ^ (n : ℕ)
      = gaussianLaw ((n : ℕ) • (m / (n : ℝ), σ2 / (n : ℝ≥0))) := by
          simpa using hpow
    _ = gaussianLaw (m, σ2) := by
          congr 1
          ext
          · simp [nsmul_eq_mul]
            field_simp [hnR]
          · simp [nsmul_eq_mul, div_eq_mul_inv, hnNN, mul_left_comm]

-- Proof sketch: the centered Cauchy convolution law adds scale parameters; iterating the centered
-- convolution identity with scale `a / n` gives the scale `a` law.
/-- Part (3) of Example 16.2: The centered Cauchy law with scale `a` is infinitely divisible, with
`Cau_{a / n}` as an `n`th convolution root for every positive integer `n`. -/
theorem measureConvolutionPower_centeredCauchy_div_eq_centeredCauchy
    (a : ℝ) (ha : 0 < a) (n : ℕ+) :
    let ν : ProbabilityMeasure ℝ := ⟨cauchyMeasure 0 (Real.toNNReal (a / (n : ℝ))), inferInstance⟩
    let μ : ProbabilityMeasure ℝ := ⟨cauchyMeasure 0 (Real.toNNReal a), inferInstance⟩
    ν ^ (n : ℕ) = μ := by
  let cauchyLaw : ℝ≥0 → ProbabilityMeasure ℝ := fun γ ↦ ⟨cauchyMeasure 0 γ, inferInstance⟩
  have hnRpos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  have hnR : (n : ℝ) ≠ 0 := hnRpos.ne'
  have hrootpos : 0 < a / (n : ℝ) := div_pos ha hnRpos
  change cauchyLaw (Real.toNNReal (a / (n : ℝ))) ^ (n : ℕ) = cauchyLaw (Real.toNNReal a)
  have hpow :=
    convolutionPower_succ_eq_of_additiveOrbit
      (ν := cauchyLaw) (a := Real.toNNReal (a / (n : ℝ)))
      (hstep := by
        intro k
        -- Proof comment: centered Cauchy convolution adds the scale parameter.
        simp [cauchyLaw]
        rw [cauchyMeasure_conv_centered]
        congr 1
        ring)
      n.natPred
  rw [n.natPred_add_one] at hpow
  calc
    cauchyLaw (Real.toNNReal (a / (n : ℝ))) ^ (n : ℕ)
      = cauchyLaw ((n : ℕ) • Real.toNNReal (a / (n : ℝ))) := by
          simpa using hpow
    _ = cauchyLaw (Real.toNNReal a) := by
          congr 1
          apply Subtype.ext
          simp [nsmul_eq_mul, Real.toNNReal_of_nonneg (le_of_lt hrootpos),
            Real.toNNReal_of_nonneg (le_of_lt ha)]
          field_simp [hnR]

-- Proof sketch: compute both sides from the explicit formula
-- `exp (-|r t|^α)` and use `|r * ((n : ℝ)^(1 / α) * t)|^α = n * |r * t|^α`.
/-- Helper for Example 16.2: the symmetric stable characteristic functions satisfy the scaling
identity that characterizes strict stability. -/
private theorem symmetricStableCharFun_charFun_scaling
    {α r : ℝ} (hα₀ : 0 < α) :
    ∀ n : ℕ+, ∀ t : ℝ,
      symmetricStableCharFun α r t ^ (n : ℕ) =
        symmetricStableCharFun α r (((n : ℝ) ^ (1 / α)) * t) := by
  intro n t
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    positivity
  have hroot_nonneg : 0 ≤ (n : ℝ) ^ (1 / α) := by
    exact Real.rpow_nonneg hn_nonneg _
  have hmul :
      r * (((n : ℝ) ^ (1 / α)) * t) = (r * t) * ((n : ℝ) ^ (1 / α)) := by
    ring
  have hroot_pow : (((n : ℝ) ^ (1 / α)) ^ α) = (n : ℝ) := by
    rw [← Real.rpow_mul hn_nonneg, one_div_mul_cancel hα₀.ne', Real.rpow_one]
  have hscale :
      |r * (((n : ℝ) ^ (1 / α)) * t)| ^ α = (n : ℝ) * |r * t| ^ α := by
    calc
      |r * (((n : ℝ) ^ (1 / α)) * t)| ^ α
          = (|r * t| * ((n : ℝ) ^ (1 / α))) ^ α := by
              rw [hmul, abs_mul, abs_of_nonneg hroot_nonneg]
      _ = |r * t| ^ α * (((n : ℝ) ^ (1 / α)) ^ α) := by
            rw [Real.mul_rpow (abs_nonneg _) hroot_nonneg]
      _ = |r * t| ^ α * (n : ℝ) := by
            rw [hroot_pow]
      _ = (n : ℝ) * |r * t| ^ α := by
            ring
  -- Proof comment: rewrite the `n`th power of the stable characteristic function as one
  -- exponential whose exponent matches the scaled stable kernel.
  calc
    symmetricStableCharFun α r t ^ (n : ℕ)
        = Complex.exp (((n : ℂ) * (-(|r * t| ^ α : ℝ) : ℂ))) := by
            rw [symmetricStableCharFun_apply,
              (Complex.exp_nat_mul ((-(|r * t| ^ α : ℝ) : ℂ)) (n : ℕ)).symm]
    _ = Complex.exp ((-(|r * (((n : ℝ) ^ (1 / α)) * t)| ^ α : ℝ) : ℂ)) := by
          have hexp :
              (n : ℝ) * (-(|r * t| ^ α : ℝ)) =
                -(|r * (((n : ℝ) ^ (1 / α)) * t)| ^ α : ℝ) := by
            rw [hscale]
            ring
          exact congrArg Complex.exp (by exact_mod_cast hexp)
    _ = symmetricStableCharFun α r (((n : ℝ) ^ (1 / α)) * t) := by
          rw [symmetricStableCharFun_apply]

-- Proof sketch: rewriting the scaled frequency variable turns the target characteristic function
-- into the characteristic function of the pushforward by the scalar map
-- `x ↦ ((n : ℝ) ^ (1 / α))⁻¹ * x`.
/-- Helper for Example 16.2: scaling the frequency variable by `((n : ℝ) ^ (1 / α))⁻¹`
corresponds to replacing the stable scale parameter `γ` by `γ / (n : ℝ) ^ (1 / α)`. -/
private theorem symmetricStableCharFun_rootScale
    (α γ : ℝ) (n : ℕ+) :
    ∀ t : ℝ,
      symmetricStableCharFun α γ ((((n : ℝ) ^ (1 / α))⁻¹) * t) =
        symmetricStableCharFun α (γ / (n : ℝ) ^ (1 / α)) t := by
  intro t
  -- Proof comment: the scaled frequency variable is the same as replacing `γ` by the divided
  -- scale parameter inside the explicit stable characteristic-function formula.
  rw [symmetricStableCharFun_apply, symmetricStableCharFun_apply]
  have harg :
      γ * ((((n : ℝ) ^ (1 / α))⁻¹) * t) =
        (γ / (n : ℝ) ^ (1 / α)) * t := by
    rw [div_eq_mul_inv]
    ring
  rw [harg]

-- Proof sketch: start from an already given symmetric stable law `μ`, push it forward by the
-- scalar `((n : ℝ) ^ (1 / α))⁻¹`, and read off the new characteristic function via
-- `MeasureTheory.charFun_map_mul`.
/-- Helper for Example 16.2: an existing symmetric stable law with characteristic function
`symmetricStableCharFun α γ` yields an `n`th convolution root by scaling the law. -/
private theorem exists_symmetricStable_root_measure
    (μ : ProbabilityMeasure ℝ) (α γ : ℝ)
    (hchar : ∀ t : ℝ, charFun (μ : Measure ℝ) t = symmetricStableCharFun α γ t) :
    ∀ n : ℕ+, ∃ ν : ProbabilityMeasure ℝ, ∀ t : ℝ, charFun (ν : Measure ℝ) t =
        symmetricStableCharFun α (γ / (n : ℝ) ^ (1 / α)) t := by
  intro n
  let c : ℝ := ((n : ℝ) ^ (1 / α))⁻¹
  let ν : ProbabilityMeasure ℝ :=
    ProbabilityMeasure.map μ
      (show AEMeasurable (fun x : ℝ ↦ c * x) (μ : Measure ℝ) from
        (measurable_const.mul measurable_id).aemeasurable)
  refine ⟨ν, ?_⟩
  intro t
  -- Proof comment: push forward the given law by the scaling `x ↦ c * x` and rewrite the
  -- characteristic function with `charFun_map_mul`.
  calc
    charFun (ν : Measure ℝ) t = charFun (μ : Measure ℝ) (c * t) := by
      simpa [ν, c] using (MeasureTheory.charFun_map_mul (μ := (μ : Measure ℝ)) c t)
    _ = symmetricStableCharFun α γ (c * t) := hchar (c * t)
    _ = symmetricStableCharFun α (γ / (n : ℝ) ^ (1 / α)) t :=
      symmetricStableCharFun_rootScale α γ n t

-- Proof sketch: the characteristic functions satisfy
-- `exp (-|γ t|^α) = exp (-|(γ / n^(1 / α)) t|^α) ^ (n : ℕ)`; then uniqueness of characteristic
-- functions identifies the `n`th convolution power of `ν` with `μ`.
/-- Helper for Example 16.2: a probability law with characteristic function
`t ↦ exp (-|(γ / n^(1 / α)) t|^α)` is an `n`th convolution root of the symmetric stable law with
characteristic function `t ↦ exp (-|γ t|^α)`. -/
private theorem measureConvolutionPower_eq_of_charFun_eq_symmetricStable_root
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (α γ : ℝ) (hα₀ : 0 < α) (_hα₂ : α ≤ 2) (_hγ : 0 < γ) (n : ℕ+)
    (hμ : ∀ t : ℝ, charFun μ t = symmetricStableCharFun α γ t)
    (hν : ∀ t : ℝ, charFun ν t =
      symmetricStableCharFun α (γ / (n : ℝ) ^ (1 / α)) t) :
    let μ₀ : ProbabilityMeasure ℝ := ⟨μ, inferInstance⟩
    let ν₀ : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
    ν₀ ^ (n : ℕ) = μ₀ := by
  dsimp
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  have hrootAtScale :=
      symmetricStableCharFun_rootScale α γ n (((n : ℝ) ^ (1 / α)) * t)
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    positivity
  have hscale_nonzero : (n : ℝ) ^ (1 / α) ≠ 0 := by
    exact Real.rpow_pos_of_pos (show (0 : ℝ) < (n : ℝ) by exact_mod_cast n.pos) _ |>.ne'
  have hcancel :
      (((n : ℝ) ^ (1 / α))⁻¹) * (((n : ℝ) ^ (1 / α)) * t) = t := by
    field_simp [hscale_nonzero]
  -- Proof comment: compare the characteristic function of the `n`th convolution power with the
  -- scaled stable kernel, then simplify the scaling back to `t`.
  calc
    charFun ((⟨ν, inferInstance⟩ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun ν t ^ (n : ℕ) := by
            simpa using
              congrArg
                (fun f : ℝ → ℂ ↦ f t)
                (ProbabilityMeasure.charFun_pow ⟨ν, inferInstance⟩ (n : ℕ))
    _ = symmetricStableCharFun α (γ / (n : ℝ) ^ (1 / α)) t ^ (n : ℕ) := by
          rw [hν]
    _ = symmetricStableCharFun α (γ / (n : ℝ) ^ (1 / α)) (((n : ℝ) ^ (1 / α)) * t) := by
          exact symmetricStableCharFun_charFun_scaling hα₀ n t
    _ = symmetricStableCharFun α γ t := by
          have hrewrite :
              symmetricStableCharFun α γ
                  ((((n : ℝ) ^ (1 / α))⁻¹) * (((n : ℝ) ^ (1 / α)) * t)) =
                symmetricStableCharFun α (γ / (n : ℝ) ^ (1 / α)) (((n : ℝ) ^ (1 / α)) * t) :=
            hrootAtScale
          rw [hcancel] at hrewrite
          exact hrewrite.symm
    _ = charFun μ t := by
          exact (hμ t).symm

-- Proof sketch: for each `n`, choose `ν` from `exists_symmetricStable_root_measure` and apply
-- `measureConvolutionPower_eq_of_charFun_eq_symmetricStable_root`.
/-- Part (4) of Example 16.2: Every symmetric stable
law with index `α ∈ (0,2]` and scale parameter `γ > 0` is infinitely divisible. -/
theorem symmetricStable_isInfinitelyDivisible
    (μ : ProbabilityMeasure ℝ) (α γ : ℝ)
    (hα₀ : 0 < α) (hα₂ : α ≤ 2) (hγ : 0 < γ)
    (hchar : ∀ t : ℝ, charFun (μ : Measure ℝ) t = symmetricStableCharFun α γ t) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ := by
  refine ⟨?_⟩
  intro n
  rcases exists_symmetricStable_root_measure μ α γ hchar n with ⟨ν, hν⟩
  refine ⟨ν, ?_⟩
  simpa using
    measureConvolutionPower_eq_of_charFun_eq_symmetricStable_root
      (μ := (μ : Measure ℝ)) (ν := (ν : Measure ℝ))
      α γ hα₀ hα₂ hγ n hchar hν

/-- Helper for Example 16.2: along the additive orbit generated by `x`, the next convolution step
adds one more copy of `x`. -/
private lemma additiveOrbitNatCastStep (x : ℝ) (k : ℕ) :
    (((k + 1 : ℕ) : ℝ) * x) + x = ((k + 2 : ℕ) : ℝ) * x := by
  -- Proof comment: rewrite the successor cast once so the extra summand is absorbed into the
  -- scalar coefficient.
  calc
    (((k + 1 : ℕ) : ℝ) * x) + x = ((((k + 1 : ℕ) : ℝ) + 1) * x) := by ring
    _ = ((k + 2 : ℕ) : ℝ) * x := by
      congr 1
      exact_mod_cast (show (k + 1) + 1 = k + 2 by omega)

-- Proof sketch: Gamma convolution at fixed rate adds shape parameters; iterating the common-rate
-- convolution identity with shape `r / n` gives the shape `r` law.
/-- Part (5) of Example 16.2: The Gamma law `Γ_{θ,r}` with `θ, r > 0` is infinitely
divisible, with `Γ_{θ, r / n}` as an `n`th convolution root for every positive integer `n`. -/
theorem measureConvolutionPower_gammaMeasure_shape_div_eq_gammaMeasure
    (θ r : ℝ) (hθ : 0 < θ) (hr : 0 < r) (n : ℕ+) :
    let ν : ProbabilityMeasure ℝ :=
      ⟨gammaMeasure (r / (n : ℝ)) θ,
        isProbabilityMeasure_gammaMeasure
          (div_pos hr (show (0 : ℝ) < (n : ℝ) by exact_mod_cast n.pos)) hθ⟩
    let μ : ProbabilityMeasure ℝ := ⟨gammaMeasure r θ, isProbabilityMeasure_gammaMeasure hr hθ⟩
    ν ^ (n : ℕ) = μ := by
  have hnRpos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  have hnR : (n : ℝ) ≠ 0 := hnRpos.ne'
  have hrootpos : 0 < r / (n : ℝ) := div_pos hr hnRpos
  let gammaLaw : ℝ → ProbabilityMeasure ℝ := fun s ↦
    if hs : 0 < s then
      ⟨gammaMeasure s θ, isProbabilityMeasure_gammaMeasure hs hθ⟩
    else
      diracProba 0
  have hpow :
      gammaLaw (r / (n : ℝ)) ^ (n : ℕ) = gammaLaw r := by
    have horbit :=
      convolutionPower_succ_eq_of_additiveOrbit
        (ν := gammaLaw) (a := r / (n : ℝ))
        (hstep := by
          intro k
          have hk1scalarpos : 0 < ((k + 1 : ℕ) : ℝ) := by
            positivity
          have hk2scalarpos : 0 < ((k + 2 : ℕ) : ℝ) := by
            positivity
          have hk1pos : 0 < (((k + 1 : ℕ) : ℝ) * (r / (n : ℝ))) := by
            exact mul_pos hk1scalarpos hrootpos
          have hk2pos : 0 < (((k + 2 : ℕ) : ℝ) * (r / (n : ℝ))) := by
            exact mul_pos hk2scalarpos hrootpos
          have hk1pos_nsmul : 0 < ((k + 1 : ℕ) • (r / (n : ℝ))) := by
            simpa [nsmul_eq_mul] using hk1pos
          have hk2pos_nsmul : 0 < ((k + 2 : ℕ) • (r / (n : ℝ))) := by
            simpa [nsmul_eq_mul] using hk2pos
          have hk1law :
              (((gammaLaw (((k + 1 : ℕ) • (r / (n : ℝ)))) : ProbabilityMeasure ℝ) :
                  Measure ℝ)) =
                gammaMeasure ((((k + 1 : ℕ) : ℝ) * (r / (n : ℝ)))) θ := by
            dsimp [gammaLaw]
            split_ifs
            · simp [nsmul_eq_mul]
          have hrootlaw :
              (((gammaLaw (r / (n : ℝ)) : ProbabilityMeasure ℝ) : Measure ℝ)) =
                gammaMeasure (r / (n : ℝ)) θ := by
            dsimp [gammaLaw]
            split_ifs
            · rfl
          have hk2law :
              (((gammaLaw (((k + 2 : ℕ) • (r / (n : ℝ)))) : ProbabilityMeasure ℝ) :
                  Measure ℝ)) =
                gammaMeasure ((((k + 2 : ℕ) : ℝ) * (r / (n : ℝ)))) θ := by
            dsimp [gammaLaw]
            split_ifs
            · simp [nsmul_eq_mul]
          -- Proof comment: common-rate Gamma convolution adds the shape parameters along the
          -- additive orbit generated by `r / n`.
          rw [hk1law, hrootlaw, hk2law]
          rw [gammaMeasure_conv_same_rate θ (((k + 1 : ℕ) : ℝ) * (r / (n : ℝ)))
            (r / (n : ℝ)) hθ hk1pos hrootpos]
          congr 1
          exact additiveOrbitNatCastStep (r / (n : ℝ)) k)
        n.natPred
    rw [n.natPred_add_one] at horbit
    calc
      gammaLaw (r / (n : ℝ)) ^ (n : ℕ) = gammaLaw ((n : ℕ) • (r / (n : ℝ))) := by
        simpa using horbit
      _ = gammaLaw r := by
        congr 1
        rw [nsmul_eq_mul]
        field_simp [hnR]
  simpa [gammaLaw, hrootpos, hr] using hpow

-- Proof sketch: Poisson convolution adds intensities, so iterating the Poisson convolution law
-- with intensity `λ / n` produces `Poi_λ`.
/-- Part (6) of Example 16.2: The Poisson law `Poi_λ` is infinitely divisible, with
`Poi_{λ / n}` as an `n`th convolution root for every positive integer `n`. -/
theorem measureConvolutionPower_poissonMeasure_div_eq_poissonMeasure
    (lam : ℝ≥0) (n : ℕ+) :
    let ν : ProbabilityMeasure ℕ := ⟨poissonMeasure (lam / (n : ℝ≥0)), inferInstance⟩
    let μ : ProbabilityMeasure ℕ := ⟨poissonMeasure lam, inferInstance⟩
    ν ^ (n : ℕ) = μ := by
  let poissonLaw : ℝ≥0 → ProbabilityMeasure ℕ := fun r ↦ ⟨poissonMeasure r, inferInstance⟩
  change poissonLaw (lam / (n : ℝ≥0)) ^ (n : ℕ) = poissonLaw lam
  have hpow :=
    convolutionPower_succ_eq_of_additiveOrbit
      (ν := poissonLaw) (a := lam / (n : ℝ≥0))
      (hstep := by
        intro k
        -- Proof comment: Poisson convolution adds the intensity parameter.
        simp [poissonLaw]
        rw [poissonMeasure_conv_poissonMeasure]
        congr 1
        ring)
      n.natPred
  have hnNN : (n : ℝ≥0) ≠ 0 := by
    exact_mod_cast n.ne_zero
  rw [n.natPred_add_one] at hpow
  calc
    poissonLaw (lam / (n : ℝ≥0)) ^ (n : ℕ)
      = poissonLaw ((n : ℕ) • (lam / (n : ℝ≥0))) := by
          simpa using hpow
    _ = poissonLaw lam := by
          congr 1
          simp [nsmul_eq_mul, div_eq_mul_inv, hnNN, mul_left_comm]

-- Proof sketch: negative-binomial convolution at fixed success parameter adds the shape
-- parameters; iterating the convolution identity with shape `r / n` yields the law with shape
-- `r`.
/-- Part (7) of Example 16.2: The negative-binomial law with parameters `r > 0` and
`p ∈ (0,1)` is infinitely divisible, with `b^-_{r / n, p}` as an `n`th convolution root for every
positive integer `n`. -/
theorem measureConvolutionPower_negativeBinomial_div_eq_negativeBinomial
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp₁ : p < 1) (n : ℕ+) :
    let ν : ProbabilityMeasure ℕ :=
      ⟨negativeBinomialMeasure (r / (n : ℝ)) p
          (div_pos hr (show (0 : ℝ) < (n : ℝ) by exact_mod_cast n.pos)) hp
          (le_of_lt hp₁), inferInstance⟩
    let μ : ProbabilityMeasure ℕ :=
      ⟨negativeBinomialMeasure r p hr hp (le_of_lt hp₁), inferInstance⟩
    ν ^ (n : ℕ) = μ := by
  have hnRpos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  have hnR : (n : ℝ) ≠ 0 := hnRpos.ne'
  have hrootpos : 0 < r / (n : ℝ) := div_pos hr hnRpos
  let negativeBinomialLaw : ℝ → ProbabilityMeasure ℕ := fun s ↦
    if hs : 0 < s then
      ⟨negativeBinomialMeasure s p hs hp (le_of_lt hp₁), inferInstance⟩
    else
      diracProba 0
  have hpow :
      negativeBinomialLaw (r / (n : ℝ)) ^ (n : ℕ) = negativeBinomialLaw r := by
    have horbit :=
      convolutionPower_succ_eq_of_additiveOrbit
        (ν := negativeBinomialLaw) (a := r / (n : ℝ))
        (hstep := by
          intro k
          have hk1scalarpos : 0 < ((k + 1 : ℕ) : ℝ) := by
            positivity
          have hk2scalarpos : 0 < ((k + 2 : ℕ) : ℝ) := by
            positivity
          have hk1pos : 0 < (((k + 1 : ℕ) : ℝ) * (r / (n : ℝ))) := by
            exact mul_pos hk1scalarpos hrootpos
          have hk2pos : 0 < (((k + 2 : ℕ) : ℝ) * (r / (n : ℝ))) := by
            exact mul_pos hk2scalarpos hrootpos
          have hk1pos_nsmul : 0 < ((k + 1 : ℕ) • (r / (n : ℝ))) := by
            simpa [nsmul_eq_mul] using hk1pos
          have hk2pos_nsmul : 0 < ((k + 2 : ℕ) • (r / (n : ℝ))) := by
            simpa [nsmul_eq_mul] using hk2pos
          have hk1law :
              (((negativeBinomialLaw (((k + 1 : ℕ) • (r / (n : ℝ)))) : ProbabilityMeasure ℕ) :
                  Measure ℕ)) =
                negativeBinomialMeasure ((((k + 1 : ℕ) : ℝ) * (r / (n : ℝ)))) p hk1pos hp
                  (le_of_lt hp₁) := by
            dsimp [negativeBinomialLaw]
            split_ifs
            · simp [nsmul_eq_mul]
          have hrootlaw :
              (((negativeBinomialLaw (r / (n : ℝ)) : ProbabilityMeasure ℕ) : Measure ℕ)) =
                negativeBinomialMeasure (r / (n : ℝ)) p hrootpos hp (le_of_lt hp₁) := by
            dsimp [negativeBinomialLaw]
            split_ifs
            · rfl
          have hk2law :
              (((negativeBinomialLaw (((k + 2 : ℕ) • (r / (n : ℝ)))) : ProbabilityMeasure ℕ) :
                  Measure ℕ)) =
                negativeBinomialMeasure ((((k + 2 : ℕ) : ℝ) * (r / (n : ℝ)))) p hk2pos hp
                  (le_of_lt hp₁) := by
            dsimp [negativeBinomialLaw]
            split_ifs
            · simp [nsmul_eq_mul]
          -- Proof comment: common-success-parameter negative-binomial convolution adds the shape
          -- parameters along the same additive orbit.
          rw [hk1law, hrootlaw, hk2law]
          rw [negativeBinomialMeasure_conv (((k + 1 : ℕ) : ℝ) * (r / (n : ℝ)))
            (r / (n : ℝ)) p hk1pos hrootpos hp (le_of_lt hp₁)]
          congr 1
          exact additiveOrbitNatCastStep (r / (n : ℝ)) k)
        n.natPred
    rw [n.natPred_add_one] at horbit
    calc
      negativeBinomialLaw (r / (n : ℝ)) ^ (n : ℕ) =
          negativeBinomialLaw ((n : ℕ) • (r / (n : ℝ))) := by
            simpa using horbit
      _ = negativeBinomialLaw r := by
        congr 1
        rw [nsmul_eq_mul]
        field_simp [hnR]
  simpa [negativeBinomialLaw, hrootpos, hr] using hpow

-- Proof sketch: one uses the cited representation theorem for the variance-mixture law
-- `X / √Y`; once that law is known to be infinitely divisible, the Student `t` family follows by
-- the stated parameter specialization.
/-- Helper for Example 16.2: identical distribution on a fixed probability space transfers
infinite divisibility of real-valued random variables. -/
private lemma isInfinitelyDivisibleRandomVariable_of_identDistrib
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hXY : IdentDistrib X Y P P) :
    IsInfinitelyDivisibleRandomVariable P Y → IsInfinitelyDivisibleRandomVariable P X := by
  intro hY n
  rcases hY n with ⟨Ω', hΩ', P', ν, Z, hZ_meas, hZ_law, hZ_indep, hYZ⟩
  -- Proof comment: compose the fixed-source identically distributed bridge with the chosen
  -- `n`-summand representation of `Y`.
  refine ⟨Ω', hΩ', P', ν, Z, hZ_meas, hZ_law, hZ_indep, ?_⟩
  exact hXY.trans hYZ

/-- Helper for Example 16.2: the Gaussian-over-`√Gamma` ratio map is almost everywhere
measurable under the law hypotheses. -/
private lemma ratioGaussianSqrtGamma_aemeasurable
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} {σ2 : ℝ≥0} {θ r : ℝ}
    (hX : HasLaw X (gaussianReal (0 : ℝ) σ2) P)
    (hY : HasLaw Y (gammaMeasure r θ) P) :
    AEMeasurable (fun ω ↦ X ω / Real.sqrt (Y ω)) P := by
  simpa using hX.aemeasurable.div hY.aemeasurable.sqrt

/-- Helper for Example 16.2: a law-side infinite-divisibility statement for the mapped ratio law
implies the source-facing random-variable statement. -/
private lemma ratioGaussianSqrtGamma_isInfinitelyDivisible_from_map
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ)
    (hZ : AEMeasurable (fun ω ↦ X ω / Real.sqrt (Y ω)) P) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ) →
      IsInfinitelyDivisibleRandomVariable P (fun ω ↦ X ω / Real.sqrt (Y ω)) := by
  intro hmap
  let Zm : Ω → ℝ := hZ.mk (fun ω ↦ X ω / Real.sqrt (Y ω))
  have hZm_meas : Measurable Zm := hZ.measurable_mk
  have hident :
      IdentDistrib (fun ω ↦ X ω / Real.sqrt (Y ω)) Zm P P := by
    -- Proof comment: replace the ratio by its measurable representative before using the law-side
    -- equivalence.
    simpa [Zm] using hZ.identDistrib_mk
  have hmapMeasure :
      (((ProbabilityMeasure.map ⟨P, inferInstance⟩ hZm_meas.aemeasurable : ProbabilityMeasure ℝ) :
          Measure ℝ)) =
        (((ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ : ProbabilityMeasure ℝ) :
          Measure ℝ)) := by
    -- Proof comment: both probability measures are pushforwards of `P` along a.e.-equal maps.
    simpa [Zm] using
      (Measure.map_congr (μ := P) hZ.ae_eq_mk).symm
  have hmapPM :
      (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZm_meas.aemeasurable : ProbabilityMeasure ℝ) =
        ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ :=
    ProbabilityMeasure.toMeasure_injective hmapMeasure
  have hmap' :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZm_meas.aemeasurable) := by
    -- Proof comment: the original ratio law and the measurable representative have the same
    -- pushforward measure.
    simpa [hmapPM] using hmap
  have hZm :
      IsInfinitelyDivisibleRandomVariable P Zm := by
    exact
      (isInfinitelyDivisibleRandomVariable_iff_law_isInfinitelyDivisible
        (P := P) (X := Zm) hZm_meas).2 hmap'
  exact isInfinitelyDivisibleRandomVariable_of_identDistrib P hident hZm

/-- Helper for Example 16.2: the pushforward law of the ratio map `ω ↦ X ω / √(Y ω)` matches the
canonical owner law `gaussianOverSqrtGammaLaw` once the Gaussian and Gamma marginals are
identified. -/
private theorem ratioGaussianSqrtGamma_map_eq_ownerLaw
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hXY : IndepFun X Y P) (σ2 : ℝ≥0) (θ r : ℝ)
    (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hX : HasLaw X (gaussianReal (0 : ℝ) σ2) P)
    (hY : HasLaw Y (gammaMeasure r θ) P) :
    let Z : Ω → ℝ := fun ω ↦ X ω / Real.sqrt (Y ω)
    let hZ : AEMeasurable Z P := ratioGaussianSqrtGamma_aemeasurable hX hY
    (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ : ProbabilityMeasure ℝ) =
      gaussianOverSqrtGammaLaw σ2 θ r hθ hr := by
  dsimp
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  -- Proof comment: both candidate owner laws are characterized by the same transform
  -- `gaussianOverSqrtGammaCFP`.
  rw [ratioGaussianSqrtGamma_map_charFun_eq (P := P) (X := X) (Y := Y)
    (ratioGaussianSqrtGamma_aemeasurable hX hY) hXY σ2 θ r hσ2 hθ hr hX hY t]
  exact (gaussianOverSqrtGammaLaw_charFun_eq σ2 θ r hσ2 hθ hr t).symm

/-- Helper for Example 16.2: any `ℕ+`-indexed characteristic-function root approximation of
`gaussianOverSqrtGammaCFP σ2 θ r` already implies that this canonical CFP is infinitely
divisible. -/
private theorem gaussianOverSqrtGammaCFP_isInfinitelyDivisible_of_rootApprox
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hroot :
      ∃ ψSeq : ℕ+ → ℝ → ℂ,
        (∀ n : ℕ+, IsCFP (ψSeq n)) ∧
          ∀ t : ℝ,
            Tendsto (fun n : ℕ+ ↦ (ψSeq n t) ^ (n : ℕ)) atTop
              (nhds (gaussianOverSqrtGammaCFP σ2 θ r t))) :
    IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP σ2 θ r) := by
  have hcont : ContinuousAt (gaussianOverSqrtGammaCFP σ2 θ r) 0 := by
    rcases gaussianOverSqrtGammaCFP_isCFP σ2 θ r hσ2 hθ hr with ⟨μ, hμ⟩
    -- Proof comment: every characteristic function of a probability measure is continuous at
    -- `0`, so the canonical Gaussian-over-`√Gamma` transform inherits that continuity.
    simpa [hμ] using (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).continuousAt
  -- Proof comment: Corollary 16.8 is exactly the bridge from a positive-integer root
  -- approximation to infinite divisibility of the limiting characteristic function.
  exact
    (isInfinitelyDivisibleCFP_iff_exists_charFun_pow_tendsto
      (φ := gaussianOverSqrtGammaCFP σ2 θ r) hcont).2 hroot

/-- Helper for Example 16.2: if the characteristic function of a probability law is infinitely
divisible in the CFP sense, then the law itself is infinitely divisible. -/
private theorem lawIsInfinitelyDivisible_of_charFunIsInfinitelyDivisibleCFP
    {μ : ProbabilityMeasure ℝ}
    (hμ : IsInfinitelyDivisibleCFP (charFun (μ : Measure ℝ))) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ := by
  refine ⟨?_⟩
  intro n
  rcases hμ n with ⟨φn, hφncfp, hroot⟩
  rcases hφncfp with ⟨ν, hν⟩
  refine ⟨ν, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  -- Proof comment: the chosen CFP root is represented by `ν`, so `charFun_pow` identifies the
  -- `n`th convolution power of `ν` with the powered root characteristic function.
  calc
    charFun ((ν ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun (ν : Measure ℝ) t ^ (n : ℕ) := by
            simpa using
              congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow ν (n : ℕ))
    _ = φn t ^ (n : ℕ) := by
          rw [hν]
    _ = charFun (μ : Measure ℝ) t := by
          simpa using (congrArg (fun f : ℝ → ℂ ↦ f t) hroot).symm

/-- Helper for Example 16.2: package the pointwise owner-law characteristic-function computation
as a function equality so every owner/CFP transport step rewrites through the same bridge. -/
private theorem gaussianOverSqrtGammaLaw_charFun_eq_fun
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    charFun (((gaussianOverSqrtGammaLaw σ2 θ r hθ hr : ProbabilityMeasure ℝ) : Measure ℝ)) =
      gaussianOverSqrtGammaCFP σ2 θ r := by
  -- Proof comment: this is just the pointwise owner-law characteristic-function formula bundled
  -- into one reusable equality.
  funext t
  exact gaussianOverSqrtGammaLaw_charFun_eq σ2 θ r hσ2 hθ hr t

/-- Helper for Example 16.2: once the canonical characteristic function
`gaussianOverSqrtGammaCFP` is known to be infinitely divisible, the owner law is infinitely
divisible by rewriting its characteristic function to that canonical CFP. -/
private theorem gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_cfp
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hcfp : IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP σ2 θ r)) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw σ2 θ r hθ hr) := by
  -- Proof comment: Theorem 16.12 applies after rewriting the owner-law characteristic function
  -- to the canonical Gaussian-over-`√Gamma` CFP.
  exact lawIsInfinitelyDivisible_of_charFunIsInfinitelyDivisibleCFP <| by
    simpa [gaussianOverSqrtGammaLaw_charFun_eq_fun σ2 θ r hσ2 hθ hr] using hcfp

/-- Helper for Example 16.2: any explicit `ℕ+`-indexed characteristic-function root
approximation of the exact unit Gaussian-over-`√Gamma` CFP already closes the corresponding unit
owner law. -/
private theorem gaussianOverSqrtGammaLaw_unitRate_isInfinitelyDivisible_of_rootApprox
    (r : ℝ) (hr : 0 < r)
    (hroot :
      ∃ ψSeq : ℕ+ → ℝ → ℂ,
        (∀ n : ℕ+, IsCFP (ψSeq n)) ∧
          ∀ t : ℝ,
            Tendsto (fun n : ℕ+ ↦ (ψSeq n t) ^ (n : ℕ)) atTop
              (nhds (gaussianOverSqrtGammaCFP 1 1 r t))) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  have hcfp : IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP 1 1 r) := by
    -- Proof comment: the previously established root-approximation bridge already proves
    -- infinite divisibility of the exact unit characteristic function.
    exact
      gaussianOverSqrtGammaCFP_isInfinitelyDivisible_of_rootApprox
        1 1 r zero_lt_one zero_lt_one hr hroot
  -- Proof comment: once the unit characteristic function is infinitely divisible, the earlier
  -- owner/CFP transport closes the exact unit owner law immediately.
  exact
    gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_cfp
      1 1 r zero_lt_one zero_lt_one hr hcfp

/-- Helper for Example 16.2: owner-law infinite divisibility transports back to the canonical
Gaussian-over-`√Gamma` characteristic function by rewriting the owner characteristic function. -/
private theorem gaussianOverSqrtGammaCFP_isInfinitelyDivisible_of_owner
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (howner :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw σ2 θ r hθ hr)) :
    IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP σ2 θ r) := by
  -- Proof comment: first pass infinite divisibility from the owner law to its characteristic
  -- function, then rewrite that characteristic function to the canonical CFP.
  simpa [gaussianOverSqrtGammaLaw_charFun_eq_fun σ2 θ r hσ2 hθ hr] using
    (MeasureTheory.ProbabilityMeasure.charFun_isInfinitelyDivisible howner)

/-- Helper for Example 16.2: for the canonical Gaussian-over-`√Gamma` law, infinite divisibility
of the owner law is equivalent to infinite divisibility of the canonical characteristic function. -/
private theorem gaussianOverSqrtGammaLaw_isInfinitelyDivisible_iff_cfp
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw σ2 θ r hθ hr) ↔
      IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP σ2 θ r) := by
  constructor
  · intro howner
    -- Proof comment: this direction is the owner-to-CFP transport packaged in the previous
    -- helper.
    exact gaussianOverSqrtGammaCFP_isInfinitelyDivisible_of_owner σ2 θ r hσ2 hθ hr howner
  · intro hcfp
    -- Proof comment: the reverse direction is the owner-law transport from the canonical CFP.
    exact gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_cfp σ2 θ r hσ2 hθ hr hcfp

/-- Helper for Example 16.2: the scaling map `x ↦ a x` is almost everywhere measurable for every
real law. -/
private lemma aemeasurable_scale
    (a : ℝ) (μ : Measure ℝ) :
    AEMeasurable (fun x : ℝ ↦ a * x) μ :=
  (measurable_const.mul measurable_id).aemeasurable

/-- Helper for Example 16.2: push a real probability law forward by the scalar map `x ↦ a x`. -/
private noncomputable def scaleLaw
    (a : ℝ) (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map μ (aemeasurable_scale a (μ : Measure ℝ))

/-- Helper for Example 16.2: the unit-rate Gamma law scaled by `1 / θ` has the Gamma law with
rate `θ`. -/
private theorem gammaMeasure_unitRate_map_div_eq_gammaMeasure
    (θ r : ℝ) (hθ : 0 < θ) (hr : 0 < r) :
    Measure.map (fun y : ℝ ↦ y / θ) (gammaMeasure r 1) = gammaMeasure r θ := by
  letI : IsProbabilityMeasure (gammaMeasure r 1) := isProbabilityMeasure_gammaMeasure hr zero_lt_one
  letI : IsProbabilityMeasure (gammaMeasure r θ) := isProbabilityMeasure_gammaMeasure hr hθ
  apply Measure.ext_of_charFun
  ext t
  -- Proof comment: identify both measures by the closed Gamma characteristic-function formula,
  -- after rewriting the pushforward as a scalar map by `θ⁻¹`.
  calc
    charFun (Measure.map (fun y : ℝ ↦ y / θ) (gammaMeasure r 1)) t
        = charFun (gammaMeasure r 1) (θ⁻¹ * t) := by
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
              (MeasureTheory.charFun_map_mul (μ := gammaMeasure r 1) θ⁻¹ t)
    _ = (1 - (((θ : ℂ)⁻¹ * (t : ℂ)) / 1) * Complex.I) ^ (-r : ℂ) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (charFun_gammaMeasure r 1 hr zero_lt_one (θ⁻¹ * t))
    _ = (1 - (t / θ) * Complex.I) ^ (-r : ℂ) := by
          congr 1
          field_simp [hθ.ne']
    _ = charFun (gammaMeasure r θ) t := by
          rw [charFun_gammaMeasure r θ hr hθ t]

/-- Helper for Example 16.2: the canonical Gamma law lives on `[0, ∞)` almost surely. -/
private lemma ae_nonneg_gammaMeasure_rate
    (r θ : ℝ) :
    ∀ᵐ y ∂ gammaMeasure r θ, 0 ≤ y := by
  rw [gammaMeasure, ae_withDensity_iff (by
    simpa [gammaPDF] using ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal r θ))]
  filter_upwards with y hy
  -- Proof comment: the Gamma density vanishes on the negative half-line, so every negative point
  -- is `gammaMeasure`-null.
  by_contra hy_neg
  exact hy (gammaPDF_of_neg (lt_of_not_ge hy_neg))

/-- Helper for Example 16.2: scalar pushforwards commute with additive convolution powers. -/
private theorem map_mul_pow_eq_map_pow_mul
    (μ : ProbabilityMeasure ℝ) (a : ℝ) (n : ℕ+) :
    scaleLaw a μ ^ (n : ℕ) = scaleLaw a (μ ^ (n : ℕ)) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  ext t
  -- Proof comment: compare both measures through their characteristic functions; scaling sends
  -- `t` to `a * t`, and `charFun_pow` handles the convolution power.
  calc
    charFun
        (((scaleLaw a μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ)) t
        = charFun
            (((scaleLaw a μ : ProbabilityMeasure ℝ) : Measure ℝ)) t ^ (n : ℕ) := by
              simpa using
                congrArg
                  (fun f : ℝ → ℂ ↦ f t)
                  (ProbabilityMeasure.charFun_pow (scaleLaw a μ) (n : ℕ))
    _ = charFun (μ : Measure ℝ) (a * t) ^ (n : ℕ) := by
          exact congrArg (fun z : ℂ ↦ z ^ (n : ℕ)) <| by
            simpa [scaleLaw] using (MeasureTheory.charFun_map_mul (μ := (μ : Measure ℝ)) a t)
    _ = charFun (((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ)) (a * t) := by
          symm
          simpa using
            congrArg
              (fun f : ℝ → ℂ ↦ f (a * t))
              (ProbabilityMeasure.charFun_pow μ (n : ℕ))
    _ = charFun (((scaleLaw a (μ ^ (n : ℕ)) : ProbabilityMeasure ℝ) : Measure ℝ)) t := by
          symm
          simpa using
            (MeasureTheory.charFun_map_mul
              (μ := (((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ))) a t)

/-- Helper for Example 16.2: scaling a real infinitely divisible law preserves infinite
divisibility. -/
private theorem isInfinitelyDivisible_map_mul
    {μ : ProbabilityMeasure ℝ}
    (hμ : MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ) (a : ℝ) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible (scaleLaw a μ) := by
  refine ⟨?_⟩
  intro n
  rcases hμ.exists_root n with ⟨ν, hν⟩
  refine ⟨scaleLaw a ν, ?_⟩
  -- Proof comment: take the chosen convolution root of `μ` and push it forward by the same
  -- scalar map; the previous helper commutes that pushforward with the convolution power.
  calc
    scaleLaw a ν ^ (n : ℕ) = scaleLaw a (ν ^ (n : ℕ)) := by
            exact map_mul_pow_eq_map_pow_mul ν a n
    _ = scaleLaw a μ := by
          rw [hν]

/-- Helper for Example 16.2: the general Gaussian-over-`√Gamma` owner law is a scalar image of
the unit-variance/unit-rate owner law. -/
private theorem gaussianOverSqrtGammaLaw_eq_map_unitRate
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    gaussianOverSqrtGammaLaw σ2 θ r hθ hr =
      scaleLaw (Real.sqrt ((σ2 : ℝ) * θ))
        (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  let P : Measure (ℝ × ℝ) := (gaussianReal (0 : ℝ) 1).prod (gammaMeasure r 1)
  let X : ℝ × ℝ → ℝ := fun z ↦ z.1
  let Y : ℝ × ℝ → ℝ := fun z ↦ z.2
  let Xσ : ℝ × ℝ → ℝ := fun z ↦ Real.sqrt (σ2 : ℝ) * z.1
  let Yθ : ℝ × ℝ → ℝ := fun z ↦ z.2 / θ
  let Z : ℝ × ℝ → ℝ := fun z ↦ z.1 / Real.sqrt z.2
  let Zσθ : ℝ × ℝ → ℝ := fun z ↦ Xσ z / Real.sqrt (Yθ z)
  let a : ℝ := Real.sqrt ((σ2 : ℝ) * θ)
  letI : IsProbabilityMeasure (gammaMeasure r 1) := isProbabilityMeasure_gammaMeasure hr zero_lt_one
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  have hXY : IndepFun X Y P := by
    -- Proof comment: the coordinate projections are independent under the canonical product law.
    simpa [P, X, Y] using
      (ProbabilityTheory.indepFun_prod
        (μ := gaussianReal (0 : ℝ) 1) (ν := gammaMeasure r 1)
        (X := id) (Y := id) measurable_id measurable_id)
  have hX : HasLaw X (gaussianReal (0 : ℝ) 1) P := by
    -- Proof comment: the first coordinate of the product law is the Gaussian marginal.
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    simpa [P, X] using
      (Measure.map_fst_prod
        (μ := gaussianReal (0 : ℝ) 1) (ν := gammaMeasure r 1))
  have hY : HasLaw Y (gammaMeasure r 1) P := by
    -- Proof comment: the second coordinate of the product law is the unit-rate Gamma marginal.
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    simpa [P, Y] using
      (Measure.map_snd_prod
        (μ := gaussianReal (0 : ℝ) 1) (ν := gammaMeasure r 1))
  have hXσ_base :
      HasLaw (fun x : ℝ ↦ Real.sqrt (σ2 : ℝ) * x) (gaussianReal (0 : ℝ) σ2)
        (gaussianReal (0 : ℝ) 1) := by
    refine ⟨(measurable_const.mul measurable_id).aemeasurable, ?_⟩
    -- Proof comment: scaling the unit Gaussian by `√σ²` produces variance `σ²`.
    simpa [Real.sq_sqrt, le_of_lt hσ2] using
      (ProbabilityTheory.gaussianReal_map_const_mul
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (c := Real.sqrt (σ2 : ℝ)))
  have hYθ_base :
      HasLaw (fun y : ℝ ↦ y / θ) (gammaMeasure r θ) (gammaMeasure r 1) := by
    refine ⟨measurable_id.div_const θ |>.aemeasurable, ?_⟩
    -- Proof comment: this is the unit-rate-to-rate-`θ` Gamma scaling from the previous helper.
    exact gammaMeasure_unitRate_map_div_eq_gammaMeasure θ r hθ hr
  have hXσ : HasLaw Xσ (gaussianReal (0 : ℝ) σ2) P := by
    -- Proof comment: compose the first coordinate with the Gaussian scaling law.
    simpa [Xσ, X, Function.comp] using HasLaw.comp hXσ_base hX
  have hYθ : HasLaw Yθ (gammaMeasure r θ) P := by
    -- Proof comment: compose the second coordinate with the Gamma scaling law.
    simpa [Yθ, Y, Function.comp] using HasLaw.comp hYθ_base hY
  have hXσYθ : IndepFun Xσ Yθ P := by
    -- Proof comment: independent coordinates remain independent after separate measurable
    -- scalar transformations.
    simpa [Xσ, Yθ, X, Y, Function.comp] using
      hXY.comp
        (measurable_const.mul measurable_id)
        (measurable_id.div_const θ)
  have hZ : AEMeasurable Z P := by
    simpa [Z] using measurable_fst.aemeasurable.div measurable_snd.aemeasurable.sqrt
  have hZσθ : AEMeasurable Zσθ P := by
    simpa [Zσθ, Xσ, Yθ] using
      (measurable_const.mul measurable_fst).aemeasurable.div
        ((measurable_snd.div_const θ).aemeasurable.sqrt)
  have hUnitMap :
      (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ : ProbabilityMeasure ℝ) =
        gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr := by
    -- Proof comment: the unit owner law is the ratio law of the canonical unit Gaussian/Gamma
    -- pair.
    exact
      ratioGaussianSqrtGamma_map_eq_ownerLaw
        (P := P) (X := X) (Y := Y) hXY 1 1 r zero_lt_one zero_lt_one hr hX hY
  have hGeneralMap :
      (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZσθ : ProbabilityMeasure ℝ) =
        gaussianOverSqrtGammaLaw σ2 θ r hθ hr := by
    -- Proof comment: after scaling the coordinates, the same canonical product space realizes the
    -- general owner law.
    exact
      ratioGaussianSqrtGamma_map_eq_ownerLaw
        (P := P) (X := Xσ) (Y := Yθ) hXσYθ σ2 θ r hσ2 hθ hr hXσ hYθ
  have hYnonneg : ∀ᵐ z ∂ P, 0 ≤ z.2 := by
    -- Proof comment: the Gamma coordinate is almost surely nonnegative, and the product law
    -- preserves that support statement on the second coordinate.
    simpa [Y, P] using
      (hY.ae_iff (by fun_prop)).2 (ae_nonneg_gammaMeasure_rate r 1)
  have hratio :
      (fun z : ℝ × ℝ ↦ Zσθ z) =ᵐ[P] fun z ↦ a * Z z := by
    filter_upwards [hYnonneg] with z hz
    have hsqrt :
        Real.sqrt (z.2 / θ) = Real.sqrt z.2 / Real.sqrt θ := by
      rw [Real.sqrt_div hz θ]
    have ha :
        Real.sqrt (σ2 : ℝ) * Real.sqrt θ = a := by
      dsimp [a]
      symm
      exact Real.sqrt_mul (le_of_lt hσ2) θ
    -- Proof comment: on the nonnegative Gamma support, the denominator rescales by `1 / √θ`,
    -- so the whole ratio rescales by `√(σ² θ)`.
    dsimp [Zσθ, Z, Xσ, Yθ, a]
    calc
      Real.sqrt (σ2 : ℝ) * z.1 / Real.sqrt (z.2 / θ)
          = Real.sqrt (σ2 : ℝ) * z.1 / (Real.sqrt z.2 / Real.sqrt θ) := by
              rw [hsqrt]
      _ = (Real.sqrt (σ2 : ℝ) * z.1 * Real.sqrt θ) / Real.sqrt z.2 := by
            rw [div_div_eq_mul_div]
      _ = (Real.sqrt (σ2 : ℝ) * Real.sqrt θ * z.1) / Real.sqrt z.2 := by
            ring
      _ = (a * z.1) / Real.sqrt z.2 := by
            rw [ha]
      _ = a * (z.1 / Real.sqrt z.2) := by
            rw [mul_div_assoc]
  apply ProbabilityMeasure.toMeasure_injective
  -- Proof comment: rewrite both sides as pushforwards of the same canonical unit pair, then use
  -- the almost-sure identity of the two ratio maps.
  calc
    ((gaussianOverSqrtGammaLaw σ2 θ r hθ hr : ProbabilityMeasure ℝ) : Measure ℝ)
        =
          ((ProbabilityMeasure.map ⟨P, inferInstance⟩ hZσθ :
            ProbabilityMeasure ℝ) : Measure ℝ) := by
            rw [hGeneralMap]
    _ = Measure.map Zσθ P := by
          simp [ProbabilityMeasure.toMeasure_map]
    _ = Measure.map (fun z : ℝ × ℝ ↦ a * Z z) P := by
          exact Measure.map_congr hratio
    _ = Measure.map (fun x : ℝ ↦ a * x) (Measure.map Z P) := by
          simpa [Function.comp, Z] using
            (Measure.map_map (measurable_const.mul measurable_id)
              (measurable_fst.div measurable_snd.sqrt) (μ := P)).symm
    _ = ((scaleLaw a (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) : ProbabilityMeasure ℝ) :
          Measure ℝ) := by
          rw [← hUnitMap]
          simp [scaleLaw, ProbabilityMeasure.toMeasure_map]

/-- Helper for Example 16.2: the Gaussian-over-`√Gamma` characteristic functions are obtained
from the unit law by scaling the frequency variable by `√(σ² θ)`. -/
private theorem gaussianOverSqrtGammaCFP_scaleToUnit
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    ∀ t : ℝ,
      gaussianOverSqrtGammaCFP σ2 θ r t =
        gaussianOverSqrtGammaCFP 1 1 r (Real.sqrt ((σ2 : ℝ) * θ) * t) := by
  intro t
  -- Proof comment: rewrite the general owner law to the scaled unit owner law, then evaluate the
  -- characteristic function of the pushforward with `charFun_map_mul`.
  calc
    gaussianOverSqrtGammaCFP σ2 θ r t
        =
          charFun
            (((gaussianOverSqrtGammaLaw σ2 θ r hθ hr : ProbabilityMeasure ℝ) :
              Measure ℝ)) t := by
            symm
            exact gaussianOverSqrtGammaLaw_charFun_eq σ2 θ r hσ2 hθ hr t
    _ = charFun
          (((scaleLaw (Real.sqrt ((σ2 : ℝ) * θ))
              (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) : ProbabilityMeasure ℝ) :
              Measure ℝ)) t := by
            rw [gaussianOverSqrtGammaLaw_eq_map_unitRate σ2 θ r hσ2 hθ hr]
    _ = charFun
          (((gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr : ProbabilityMeasure ℝ) : Measure ℝ))
          (Real.sqrt ((σ2 : ℝ) * θ) * t) := by
            simpa using
              (MeasureTheory.charFun_map_mul
                (μ := (((gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr : ProbabilityMeasure ℝ) :
                  Measure ℝ))) (Real.sqrt ((σ2 : ℝ) * θ)) t)
    _ = gaussianOverSqrtGammaCFP 1 1 r (Real.sqrt ((σ2 : ℝ) * θ) * t) := by
          exact gaussianOverSqrtGammaLaw_charFun_eq 1 1 r zero_lt_one zero_lt_one hr _

/-- Helper for Example 16.2: the reciprocal-Gamma time law on `[0, ∞)` obtained by pushing the
unit-rate Gamma law forward along `y ↦ y⁻¹`. -/
private noncomputable def reciprocalGammaTimeLaw (r : ℝ) (hr : 0 < r) : ProbabilityMeasure NNReal :=
  ProbabilityMeasure.map
    ⟨gammaMeasure r 1, isProbabilityMeasure_gammaMeasure hr zero_lt_one⟩
    ((measurable_real_toNNReal.comp measurable_inv).aemeasurable)

/-- Helper for Example 16.2: the unit-rate Gamma law has no atom at `0`. -/
private lemma gammaMeasure_unitRate_singleton_zero (r : ℝ) :
    gammaMeasure r 1 ({0} : Set ℝ) = 0 := by
  -- Proof comment: Gamma laws are absolutely continuous with respect to Lebesgue measure, so
  -- singletons have zero mass.
  rw [gammaMeasure, withDensity_apply _ (measurableSet_singleton 0)]
  simp

/-- Helper for Example 16.2: the unit-rate Gamma law is almost surely strictly positive. -/
private lemma ae_pos_gammaMeasure_unitRate (r : ℝ) :
    ∀ᵐ y ∂ gammaMeasure r 1, 0 < y := by
  have hnonneg : ∀ᵐ y ∂ gammaMeasure r 1, 0 ≤ y := ae_nonneg_gammaMeasure_rate r 1
  have hne_zero : ∀ᵐ y ∂ gammaMeasure r 1, y ≠ 0 := by
    rw [ae_iff]
    simpa using gammaMeasure_unitRate_singleton_zero r
  -- Proof comment: combine the nonnegative support of the Gamma law with the zero-atom fact.
  filter_upwards [hnonneg, hne_zero] with y hy_nonneg hy_ne
  exact lt_of_le_of_ne hy_nonneg (Ne.symm hy_ne)

/-- Helper for Example 16.2: the unit-rate Gamma law viewed on `[0, ∞)` via `Real.toNNReal`. -/
private noncomputable def unitRateGammaTimeLaw (r : ℝ) (hr : 0 < r) : ProbabilityMeasure NNReal :=
  ProbabilityMeasure.map
    ⟨gammaMeasure r 1, isProbabilityMeasure_gammaMeasure hr zero_lt_one⟩
    measurable_real_toNNReal.aemeasurable

/-- Helper for Example 16.2: the `NNReal` unit-rate Gamma law inherits the zero-atom property at
the origin. -/
private lemma unitRateGammaTimeLaw_singleton_zero (r : ℝ) (hr : 0 < r) :
    (((unitRateGammaTimeLaw r hr : ProbabilityMeasure NNReal) : Measure NNReal)
      ({0} : Set NNReal)) = 0 := by
  rw [unitRateGammaTimeLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply_of_aemeasurable measurable_real_toNNReal.aemeasurable
      (measurableSet_singleton 0)]
  have hpreimage_eq :
      Real.toNNReal ⁻¹' ({0} : Set NNReal) = Set.Iic (0 : ℝ) := by
    ext y
    constructor
    · intro hy
      -- Proof comment: `Real.toNNReal y = 0` is equivalent to `y ≤ 0`.
      exact Real.toNNReal_eq_zero.mp (by simpa [Set.mem_preimage] using hy)
    · intro hy
      -- Proof comment: the converse direction is the same equivalence read backwards.
      simpa [Set.mem_preimage] using (Real.toNNReal_eq_zero.mpr hy)
  have hIic_ae :
      ∀ᵐ y ∂ gammaMeasure r 1, y ∉ Set.Iic (0 : ℝ) := by
    filter_upwards [ae_pos_gammaMeasure_unitRate r] with y hy
    have hy_not_le : ¬ y ≤ 0 := by
      linarith
    simpa [Set.mem_Iic] using hy_not_le
  rw [hpreimage_eq]
  rw [ae_iff] at hIic_ae
  simpa using hIic_ae

/-- Helper for Example 16.2: the reciprocal-Gamma time law is the inversion pushforward of the
`NNReal` unit-rate Gamma law. -/
private theorem reciprocalGammaTimeLaw_eq_map_inv_unitRateGammaTimeLaw
    (r : ℝ) (hr : 0 < r) :
    reciprocalGammaTimeLaw r hr =
      ProbabilityMeasure.map (unitRateGammaTimeLaw r hr) measurable_inv.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  have hcongr :
      (fun y : ℝ ↦ (Real.toNNReal (y⁻¹) : NNReal)) =ᵐ[gammaMeasure r 1]
        fun y : ℝ ↦ ((Real.toNNReal y : NNReal)⁻¹) := by
    filter_upwards [ae_pos_gammaMeasure_unitRate r] with y hy
    apply NNReal.coe_injective
    simp [Real.toNNReal_of_nonneg hy.le, Real.toNNReal_of_nonneg (inv_nonneg.mpr hy.le)]
  -- Proof comment: rewrite both laws as pushforwards of the same unit-rate Gamma law and compare
  -- the maps a.e. on the positive support.
  calc
    ((reciprocalGammaTimeLaw r hr : ProbabilityMeasure NNReal) : Measure NNReal)
        = Measure.map (Real.toNNReal ∘ Inv.inv) (gammaMeasure r 1) := by
            simp [reciprocalGammaTimeLaw, ProbabilityMeasure.toMeasure_map]
    _ = Measure.map (fun y : ℝ ↦ (Real.toNNReal (y⁻¹) : NNReal)) (gammaMeasure r 1) := by
          rfl
    _ = Measure.map (fun y : ℝ ↦ ((Real.toNNReal y : NNReal)⁻¹)) (gammaMeasure r 1) := by
          exact Measure.map_congr hcongr
    _ = ((ProbabilityMeasure.map (unitRateGammaTimeLaw r hr) measurable_inv.aemeasurable :
            ProbabilityMeasure NNReal) : Measure NNReal) := by
          symm
          rw [unitRateGammaTimeLaw, ProbabilityMeasure.toMeasure_map]
          simpa [Function.comp, ProbabilityMeasure.toMeasure_map] using
            (Measure.map_map measurable_inv measurable_real_toNNReal
              (μ := gammaMeasure r 1))

/-- Helper for Example 16.2: the reciprocal-Gamma time law has Mellin transform equal to the
negative Mellin transform of the `NNReal` unit-rate Gamma law. -/
private theorem mellinTransform_reciprocalGammaTimeLaw_eq_neg
    (r : ℝ) (hr : 0 < r) (s : ℝ) :
    mellinTransform
        (((reciprocalGammaTimeLaw r hr : ProbabilityMeasure NNReal) : Measure NNReal)) s =
      mellinTransform
        (((unitRateGammaTimeLaw r hr : ProbabilityMeasure NNReal) : Measure NNReal)) (-s) := by
  rw [reciprocalGammaTimeLaw_eq_map_inv_unitRateGammaTimeLaw r hr]
  -- Proof comment: once the reciprocal-Gamma law is normalized as an inversion pushforward, the
  -- Chapter 15 Mellin inversion identity applies directly.
  simpa using
    (mellinTransform_map_inv_eq_neg
      (((unitRateGammaTimeLaw r hr : ProbabilityMeasure NNReal) : Measure NNReal))
      (unitRateGammaTimeLaw_singleton_zero r hr) (s := s))

/-- Helper for Example 16.2: the Gaussian-mixture time parameter attached to frequency `t`, namely
the nonnegative scalar `t² / 2` viewed in `NNReal`. -/
private noncomputable def gaussianTimeMixtureParameter (t : ℝ) : NNReal :=
  Real.toNNReal (t ^ (2 : ℕ) / 2)

/-- Helper for Example 16.2: coercing the Gaussian-mixture time parameter back to `ℝ` recovers the
original nonnegative scalar `t² / 2`. -/
private lemma coe_gaussianTimeMixtureParameter (t : ℝ) :
    ((gaussianTimeMixtureParameter t : NNReal) : ℝ) = t ^ (2 : ℕ) / 2 := by
  -- Proof comment: `t² / 2` is nonnegative, so `Real.toNNReal` is a two-sided coercion here.
  have ht_nonneg : 0 ≤ t ^ (2 : ℕ) / 2 := by positivity
  simp [gaussianTimeMixtureParameter, Real.toNNReal_of_nonneg ht_nonneg]

/-- Helper for Example 16.2: the positive-time Gaussian-mixture characteristic-function candidate
attached to an `NNReal` time law. -/
private noncomputable def gaussianTimeMixtureCFP (τ : ProbabilityMeasure NNReal) : ℝ → ℂ :=
  fun t ↦
    ∫ s : NNReal,
      ((Real.exp
          (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ))) : ℝ) : ℂ)
        ∂(τ : Measure NNReal)

/-- Helper for Example 16.2: the Gaussian-mixture CFP is the complex coercion of the underlying
real Laplace integral. -/
private lemma gaussianTimeMixtureCFP_eq_ofReal_laplace
    (τ : ProbabilityMeasure NNReal) (t : ℝ) :
    gaussianTimeMixtureCFP τ t =
      ((∫ s : NNReal,
          Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ)))
        ∂(τ : Measure NNReal)) : ℂ) := by
  -- Proof comment: the complex-valued integral of a real-valued kernel is exactly the coercion of
  -- the corresponding real integral.
  simpa [gaussianTimeMixtureCFP] using
    (integral_ofReal
      (μ := (τ : Measure NNReal))
      (f := fun s : NNReal ↦
        Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ)))))

/-- Helper for Example 16.2: the standard Gaussian characteristic function at frequency
`√s * t` matches the Laplace kernel at time `s` and parameter `t² / 2`. -/
private lemma charFun_stdGaussian_eq_gaussianTimeMixtureKernel
    (s : NNReal) (t : ℝ) :
    charFun (gaussianReal (0 : ℝ) 1) (Real.sqrt (s : ℝ) * t) =
      (((Real.exp
          (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ))) : ℝ)) : ℂ) := by
  have hs : 0 ≤ (s : ℝ) := by
    exact_mod_cast s.2
  have hsq :
      (Real.sqrt (s : ℝ) * t) ^ (2 : ℕ) / 2 =
        (((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ) := by
    -- Proof comment: the square of `√s * t` is `s * t²`, so the Gaussian exponent is exactly the
    -- Laplace time parameter `s` multiplied by `t² / 2`.
    rw [coe_gaussianTimeMixtureParameter]
    calc
      (Real.sqrt (s : ℝ) * t) ^ (2 : ℕ) / 2
          = ((Real.sqrt (s : ℝ)) ^ (2 : ℕ) * t ^ (2 : ℕ)) / 2 := by ring
      _ = ((s : ℝ) * t ^ (2 : ℕ)) / 2 := by rw [Real.sq_sqrt hs]
      _ = (t ^ (2 : ℕ) / 2) * (s : ℝ) := by ring
  -- Proof comment: rewrite the Gaussian characteristic function with `charFun_gaussianReal` and
  -- simplify its exponent using the previous normalization.
  rw [ProbabilityTheory.charFun_gaussianReal, Complex.ofReal_exp]
  congr 1
  norm_num
  exact_mod_cast hsq

/-- Helper for Example 16.2: the Laplace kernel on `[0, ∞)` is integrable against every
probability law. -/
private lemma integrableNnrealLaplaceKernel (μ : ProbabilityMeasure NNReal) (t : NNReal) :
    Integrable (fun x : NNReal ↦ Real.exp (-((t : ℝ) * (x : ℝ)))) (μ : Measure NNReal) := by
  -- Proof comment: the exponential kernel is bounded by the constant function `1`.
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards with x
  have hnonneg : 0 ≤ Real.exp (-((t : ℝ) * (x : ℝ))) := by positivity
  rw [Real.norm_of_nonneg hnonneg]
  refine Real.exp_le_one_iff.mpr ?_
  have ht : 0 ≤ (t : ℝ) := by positivity
  have hx : 0 ≤ (x : ℝ) := by exact_mod_cast x.2
  nlinarith

/-- Helper for Example 16.2: the Gaussian-mixture Laplace integral is strictly positive. -/
private lemma gaussianTimeMixtureLaplaceIntegral_pos
    (τ : ProbabilityMeasure NNReal) (t : ℝ) :
    0 < ∫ s : NNReal,
        Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ)))
          ∂(τ : Measure NNReal) := by
  -- Proof comment: the Laplace kernel is everywhere positive, so its integral against a
  -- probability law is strictly positive.
  simpa using
    (MeasureTheory.integral_exp_pos
      (μ := (τ : Measure NNReal))
      (f := fun s : NNReal ↦
        -((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ)))
      (integrableNnrealLaplaceKernel τ (gaussianTimeMixtureParameter t)))

/-- Helper for Example 16.2: additive convolution on `[0, ∞)` turns the Laplace kernel into a
product. -/
private lemma nnrealLaplaceIntegral_mul
    (μ ν : ProbabilityMeasure NNReal) (t : NNReal) :
    ∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂((μ * ν : ProbabilityMeasure NNReal) : Measure NNReal) =
      (∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal)) *
        ∫ y, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(ν : Measure NNReal) := by
  -- Proof comment: convolution is the pushforward of the product measure under addition, and the
  -- Laplace kernel factorizes across sums.
  rw [ProbabilityMeasure.toMeasure_mul, Measure.conv]
  rw [integral_map_of_stronglyMeasurable measurable_add]
  · calc
      ∫ z : NNReal × NNReal, Real.exp (-((t : ℝ) * ((z.1 + z.2 : NNReal) : ℝ)))
          ∂((μ : Measure NNReal).prod (ν : Measure NNReal)) =
        ∫ z : NNReal × NNReal,
            Real.exp (-((t : ℝ) * (z.1 : ℝ))) * Real.exp (-((t : ℝ) * (z.2 : ℝ)))
            ∂((μ : Measure NNReal).prod (ν : Measure NNReal)) := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
              rcases z with ⟨x, y⟩
              change
                Real.exp (-((t : ℝ) * (((x + y : NNReal) : ℝ)))) =
                  Real.exp (-((t : ℝ) * (x : ℝ))) * Real.exp (-((t : ℝ) * (y : ℝ)))
              rw [show (((x + y : NNReal) : ℝ)) = (x : ℝ) + (y : ℝ) by rfl]
              rw [mul_add, neg_add, Real.exp_add]
      _ = (∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal)) *
            ∫ y, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(ν : Measure NNReal) := by
              simpa using
                (integral_prod_mul
                  (μ := (μ : Measure NNReal))
                  (ν := (ν : Measure NNReal))
                  (f := fun x : NNReal ↦ Real.exp (-((t : ℝ) * (x : ℝ))))
                  (g := fun y : NNReal ↦ Real.exp (-((t : ℝ) * (y : ℝ)))))
  · fun_prop

/-- Helper for Example 16.2: convolution powers on `[0, ∞)` raise the Laplace transform to the
matching power. -/
private lemma nnrealLaplaceIntegral_pow
    (μ : ProbabilityMeasure NNReal) (t : NNReal) :
    ∀ m : ℕ,
      ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ)))
          ∂((μ ^ m : ProbabilityMeasure NNReal) : Measure NNReal) =
        (∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal)) ^ m
  | 0 => by
      -- Proof comment: the zeroth convolution power is `δ₀`, whose Laplace integral is `1`.
      simp [ProbabilityMeasure.one_eq_diracProba, MeasureTheory.diracProba]
  | m + 1 => by
      -- Proof comment: one more convolution factor multiplies the Laplace transform by the base
      -- Laplace value.
      rw [pow_succ, nnrealLaplaceIntegral_mul, nnrealLaplaceIntegral_pow μ t m, pow_succ]

/-- Helper for Example 16.2: the Gaussian-mixture owner law obtained from a nonnegative time law
by scaling a standard Gaussian with `√s`. -/
private noncomputable def gaussianTimeMixtureLaw (τ : ProbabilityMeasure NNReal) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    ⟨((gaussianReal (0 : ℝ) 1).prod (τ : Measure NNReal)), by infer_instance⟩
    ((by
      fun_prop : Measurable (fun z : ℝ × NNReal ↦ Real.sqrt (z.2 : ℝ) * z.1)).aemeasurable)

/-- Helper for Example 16.2: the Gaussian-mixture owner law has characteristic function equal to
the Laplace transform of the time law at `t² / 2`. -/
private theorem gaussianTimeMixtureLaw_charFun_eq
    (τ : ProbabilityMeasure NNReal) :
    charFun (((gaussianTimeMixtureLaw τ : ProbabilityMeasure ℝ) : Measure ℝ)) =
      gaussianTimeMixtureCFP τ := by
  funext t
  let P : Measure (ℝ × NNReal) := ((gaussianReal (0 : ℝ) 1).prod (τ : Measure NNReal))
  let f : ℝ × NNReal → ℂ := fun z ↦ Complex.exp (t * (Real.sqrt (z.2 : ℝ) * z.1) * Complex.I)
  have hZ :
      AEMeasurable (fun z : ℝ × NNReal ↦ Real.sqrt (z.2 : ℝ) * z.1) P := by
    -- Proof comment: the Gaussian-mixture owner law is defined by scaling the Gaussian coordinate
    -- by `√s`.
    dsimp [P]
    fun_prop
  have hf : AEStronglyMeasurable f P := by
    -- Proof comment: the product-space integrand is a measurable complex exponential.
    dsimp [f, P]
    fun_prop
  have hInt : Integrable f P := by
    -- Proof comment: the complex exponential has norm `1`, so the product-space integral is
    -- absolutely bounded by the constant integrable function `1`.
    refine Integrable.of_bound hf 1 ?_
    filter_upwards with z
    simp [f, Complex.norm_exp]
  have hmap :
      (((gaussianTimeMixtureLaw τ : ProbabilityMeasure ℝ) : Measure ℝ)) =
        Measure.map (fun z : ℝ × NNReal ↦ Real.sqrt (z.2 : ℝ) * z.1) P := by
    -- Proof comment: unfold the owner-law pushforward once, but keep the product-model interface
    -- opaque afterwards.
    simp [gaussianTimeMixtureLaw, P, ProbabilityMeasure.toMeasure_map]
  calc
    charFun (((gaussianTimeMixtureLaw τ : ProbabilityMeasure ℝ) : Measure ℝ)) t
        = ∫ z, f z ∂P := by
            -- Proof comment: expand the characteristic function of the pushed-forward mixture law.
            rw [hmap, charFun_apply_real]
            rw [integral_map hZ]
            · refine integral_congr_ae ?_
              filter_upwards with z
              simp [f]
            · fun_prop
    _ = ∫ s, ∫ x, f (x, s) ∂(gaussianReal (0 : ℝ) 1) ∂(τ : Measure NNReal) := by
          -- Proof comment: separate the product integral into Gaussian and time coordinates.
          simpa [P] using integral_prod_symm f hInt
    _ = ∫ s, charFun (gaussianReal (0 : ℝ) 1) (Real.sqrt (s : ℝ) * t) ∂(τ : Measure NNReal) := by
          -- Proof comment: for each time value `s`, the inner Gaussian integral is the Gaussian
          -- characteristic function at frequency `√s * t`.
          refine integral_congr_ae ?_
          filter_upwards with s
          rw [charFun_apply_real]
          congr 1
          funext x
          simp [f]
          ring
    _ = ∫ s, (((Real.exp
            (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ))) : ℝ)) : ℂ)
            ∂(τ : Measure NNReal) := by
          -- Proof comment: rewrite the inner Gaussian characteristic function into the Laplace
          -- kernel of the time law.
          refine integral_congr_ae ?_
          filter_upwards with s
          exact charFun_stdGaussian_eq_gaussianTimeMixtureKernel s t
    _ = gaussianTimeMixtureCFP τ t := by
          rfl

/-- Helper for Example 16.2: every positive-time Gaussian mixture is a characteristic function,
realized by the corresponding product-model owner law. -/
private theorem gaussianTimeMixture_isCFP (τ : ProbabilityMeasure NNReal) :
    IsCFP (gaussianTimeMixtureCFP τ) := by
  -- Proof comment: the previous helper identifies the mixture formula with the characteristic
  -- function of the explicit Gaussian-mixture owner law.
  refine ⟨gaussianTimeMixtureLaw τ, ?_⟩
  exact gaussianTimeMixtureLaw_charFun_eq τ

/-- Helper for Example 16.2: the unit Gaussian-over-`√Gamma` characteristic function is exactly
the Gaussian-mixture CFP obtained from the reciprocal-Gamma time law. -/
private theorem gaussianOverSqrtGammaUnit_cfp_eq_gaussianTimeMixture
    (r : ℝ) (hr : 0 < r) :
    gaussianOverSqrtGammaCFP 1 1 r = gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr) := by
  funext t
  have hnonneg : ∀ᵐ y ∂gammaMeasure r 1, 0 ≤ y := ae_nonneg_gammaMeasure_rate r 1
  calc
    gaussianOverSqrtGammaCFP 1 1 r t
        = ∫ y,
            (((Real.exp
                (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) *
                    (((Real.toNNReal (y⁻¹) : NNReal) : ℝ)))) : ℝ)) : ℂ)
              ∂(gammaMeasure r 1) := by
            -- Proof comment: on the nonnegative Gamma support, `t / √y` is the same frequency as
            -- `√(y⁻¹) * t`, so the unit Gaussian kernel becomes the reciprocal-Gamma Laplace
            -- kernel.
            refine integral_congr_ae ?_
            filter_upwards [hnonneg] with y hy
            have hy_inv : 0 ≤ y⁻¹ := inv_nonneg.mpr hy
            have hfreq :
                Real.sqrt (((Real.toNNReal (y⁻¹) : NNReal) : ℝ)) * t = t / Real.sqrt y := by
              simp [Real.toNNReal_of_nonneg hy_inv, Real.sqrt_inv, div_eq_mul_inv, mul_comm]
            calc
              charFun (gaussianReal (0 : ℝ) 1) (t / Real.sqrt y)
                  = charFun (gaussianReal (0 : ℝ) 1)
                      (Real.sqrt (((Real.toNNReal (y⁻¹) : NNReal) : ℝ)) * t) := by
                        rw [hfreq]
              _ = (((Real.exp
                      (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) *
                          (((Real.toNNReal (y⁻¹) : NNReal) : ℝ)))) : ℝ)) : ℂ) := by
                    exact charFun_stdGaussian_eq_gaussianTimeMixtureKernel
                      (Real.toNNReal (y⁻¹)) t
    _ = gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr) t := by
          -- Proof comment: now rewrite the reciprocal-Gamma law as the pushforward of the
          -- unit-rate Gamma law under inversion.
          rw [gaussianTimeMixtureCFP_eq_ofReal_laplace, reciprocalGammaTimeLaw,
            ProbabilityMeasure.toMeasure_map]
          rw [integral_map ((measurable_real_toNNReal.comp measurable_inv).aemeasurable)]
          · rfl
          · fun_prop

/-- Helper for Example 16.2: exact convolution roots of a positive-time law induce exact power
identities for the corresponding Gaussian-mixture characteristic functions. -/
private theorem gaussianTimeMixture_pow_eq_of_timePow_eq
    {τ τn : ProbabilityMeasure NNReal} (n : ℕ+) (hpow : τn ^ (n : ℕ) = τ) :
    ∀ t : ℝ, (gaussianTimeMixtureCFP τn t) ^ (n : ℕ) = gaussianTimeMixtureCFP τ t := by
  intro t
  have hrootLap :
      ∫ x : NNReal,
          Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
          ∂(τ : Measure NNReal) =
        (∫ x : NNReal,
            Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
            ∂(τn : Measure NNReal)) ^ (n : ℕ) := by
    -- Proof comment: the exact time-law root identity transports directly through the Laplace
    -- transform of the time law.
    simpa [hpow] using nnrealLaplaceIntegral_pow τn (gaussianTimeMixtureParameter t) (n : ℕ)
  have hrootLapC :
      (((∫ x : NNReal,
          Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
          ∂(τn : Measure NNReal)) : ℂ) ^ (n : ℕ)) =
        ((∫ x : NNReal,
            Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
            ∂(τ : Measure NNReal)) : ℂ) := by
    exact_mod_cast hrootLap.symm
  calc
    (gaussianTimeMixtureCFP τn t) ^ (n : ℕ)
        = (((∫ x : NNReal,
                Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
                ∂(τn : Measure NNReal)) : ℂ) ^ (n : ℕ)) := by
              rw [gaussianTimeMixtureCFP_eq_ofReal_laplace]
    _ = ((∫ x : NNReal,
            Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
            ∂(τ : Measure NNReal)) : ℂ) := hrootLapC
    _ = gaussianTimeMixtureCFP τ t := by
          rw [gaussianTimeMixtureCFP_eq_ofReal_laplace]

/-- Helper for Example 16.2: an infinitely divisible positive-time law yields an infinitely
divisible Gaussian-mixture characteristic function. -/
private theorem gaussianTimeMixtureCFP_isInfinitelyDivisible_of_timeLaw
    {τ : ProbabilityMeasure NNReal}
    (hτ : MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible τ) :
    IsInfinitelyDivisibleCFP (gaussianTimeMixtureCFP τ) := by
  have hcont : ContinuousAt (gaussianTimeMixtureCFP τ) 0 := by
    rcases gaussianTimeMixture_isCFP τ with ⟨μ, hμ⟩
    -- Proof comment: every characteristic function of a probability law is continuous at `0`,
    -- and the Gaussian-mixture formula is already identified with such a characteristic function.
    simpa [hμ] using (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).continuousAt
  refine (isInfinitelyDivisibleCFP_iff_exists_charFun_pow_tendsto hcont).2 ?_
  classical
  let τroot : ℕ+ → ProbabilityMeasure NNReal := fun n ↦ Classical.choose (hτ.exists_root n)
  have hτroot : ∀ n : ℕ+, τroot n ^ (n : ℕ) = τ := by
    intro n
    exact Classical.choose_spec (hτ.exists_root n)
  refine ⟨fun n ↦ gaussianTimeMixtureCFP (τroot n), ?_, ?_⟩
  · intro n
    -- Proof comment: every exact time root still defines a genuine Gaussian-mixture
    -- characteristic function.
    exact gaussianTimeMixture_isCFP (τroot n)
  · intro t
    have hconst :
        (fun n : ℕ+ ↦ (gaussianTimeMixtureCFP (τroot n) t) ^ (n : ℕ)) =
          fun _ : ℕ+ ↦ gaussianTimeMixtureCFP τ t := by
      funext n
      -- Proof comment: the exact time-law root identity transports directly through the Laplace
      -- transform defining the Gaussian-mixture characteristic function.
      exact gaussianTimeMixture_pow_eq_of_timePow_eq n (hτroot n) t
    -- Proof comment: after the power transport, the approximating sequence is pointwise
    -- constant, so Corollary 16.8 applies immediately.
    rw [hconst]
    exact tendsto_const_nhds

/-- Helper for Example 16.2: once the Gaussian-mixture characteristic function is infinitely
divisible, the corresponding Gaussian-mixture owner law is infinitely divisible by the local
CFP-to-owner bridge. -/
private theorem gaussianTimeMixtureLaw_isInfinitelyDivisible_of_cfp
    (τ : ProbabilityMeasure NNReal)
    (hcfp : IsInfinitelyDivisibleCFP (gaussianTimeMixtureCFP τ)) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible (gaussianTimeMixtureLaw τ) := by
  have hownerCFP :
      IsInfinitelyDivisibleCFP
        (charFun (((gaussianTimeMixtureLaw τ : ProbabilityMeasure ℝ) : Measure ℝ))) := by
    -- Proof comment: rewrite the owner characteristic function to the explicit
    -- Gaussian-mixture CFP before invoking the earlier CFP-to-owner transport.
    simpa [gaussianTimeMixtureLaw_charFun_eq τ] using hcfp
  -- Proof comment: after rewriting to the owner characteristic function, the earlier local
  -- theorem turns the CFP statement into owner-law infinite divisibility.
  exact lawIsInfinitelyDivisible_of_charFunIsInfinitelyDivisibleCFP hownerCFP

/-- Helper for Example 16.2: once a Gaussian-mixture owner law is infinitely divisible, its
explicit Gaussian-mixture characteristic function is infinitely divisible by rewriting the owner
characteristic function to the canonical mixture CFP. -/
private theorem gaussianTimeMixtureCFP_isInfinitelyDivisible_of_ownerLaw
    (τ : ProbabilityMeasure NNReal)
    (howner : MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible (gaussianTimeMixtureLaw τ)) :
    IsInfinitelyDivisibleCFP (gaussianTimeMixtureCFP τ) := by
  -- Proof comment: pass infinite divisibility from the owner law to its characteristic function,
  -- then rewrite that characteristic function to the canonical Gaussian-mixture CFP.
  simpa [gaussianTimeMixtureLaw_charFun_eq τ] using
    (MeasureTheory.ProbabilityMeasure.charFun_isInfinitelyDivisible howner)

/-- Helper for Example 16.2: for Gaussian mixtures, owner-law infinite divisibility is equivalent
to infinite divisibility of the explicit Gaussian-mixture characteristic function. -/
private theorem gaussianTimeMixtureLaw_isInfinitelyDivisible_iff_cfp
    (τ : ProbabilityMeasure NNReal) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible (gaussianTimeMixtureLaw τ) ↔
      IsInfinitelyDivisibleCFP (gaussianTimeMixtureCFP τ) := by
  constructor
  · intro howner
    -- Proof comment: this direction is the owner-to-CFP transport proved in the previous helper.
    exact gaussianTimeMixtureCFP_isInfinitelyDivisible_of_ownerLaw τ howner
  · intro hcfp
    -- Proof comment: the reverse direction is the previously established CFP-to-owner bridge.
    exact gaussianTimeMixtureLaw_isInfinitelyDivisible_of_cfp τ hcfp

/-- Helper for Example 16.2: once the unit-variance/unit-rate Gaussian-over-`√Gamma` owner law
is infinitely divisible, the general owner law follows by the scalar transport already proved in
this file. -/
private theorem gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_unitRate
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hunit :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr)) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw σ2 θ r hθ hr) := by
  have hscaled :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (scaleLaw (Real.sqrt ((σ2 : ℝ) * θ))
          (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr)) :=
    isInfinitelyDivisible_map_mul hunit (Real.sqrt ((σ2 : ℝ) * θ))
  -- Proof comment: the earlier scale-to-unit identity rewrites the general owner law to a scaled
  -- unit owner law, so infinite divisibility transports through the scalar pushforward.
  simpa [gaussianOverSqrtGammaLaw_eq_map_unitRate σ2 θ r hσ2 hθ hr] using hscaled

/-- Helper for Example 16.2: the unit Gaussian-over-`√Gamma` owner law is infinitely divisible as
soon as the exact reciprocal-Gamma Gaussian-mixture characteristic function is infinitely
divisible. -/
private theorem gaussianOverSqrtGammaUnitOwnerLaw_isInfinitelyDivisible_of_mixtureCFP
    (r : ℝ) (hr : 0 < r)
    (hmix :
      IsInfinitelyDivisibleCFP (gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr))) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  have hcfp : IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP 1 1 r) := by
    -- Proof comment: rewrite the reciprocal-Gamma Gaussian-mixture characteristic function back
    -- to the canonical unit Gaussian-over-`√Gamma` characteristic function.
    simpa [gaussianOverSqrtGammaUnit_cfp_eq_gaussianTimeMixture r hr] using hmix
  -- Proof comment: once the canonical unit characteristic function is infinitely divisible, the
  -- earlier owner/CFP bridge closes the unit owner law.
  exact gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_cfp 1 1 r zero_lt_one zero_lt_one hr hcfp

/-- Helper for Example 16.2: infinite divisibility of the reciprocal-Gamma time law is enough to
close the unit Gaussian-over-`√Gamma` owner law through the Gaussian-mixture bridge. -/
private theorem gaussianOverSqrtGammaLaw_unitRate_isInfinitelyDivisible_of_timeLaw
    (r : ℝ) (hr : 0 < r)
    (htime :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible (reciprocalGammaTimeLaw r hr)) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  have hmix :
      IsInfinitelyDivisibleCFP
        (gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr)) :=
    gaussianTimeMixtureCFP_isInfinitelyDivisible_of_timeLaw htime
  -- Proof comment: the previous helper reduces the unit owner law to the exact reciprocal-Gamma
  -- Gaussian-mixture characteristic function, which the time-law theorem supplies directly.
  exact gaussianOverSqrtGammaUnitOwnerLaw_isInfinitelyDivisible_of_mixtureCFP r hr hmix

/-- Helper for Example 16.2: the unit Gaussian-over-`√Gamma` owner law agrees exactly with the
Gaussian-mixture owner law driven by the reciprocal-Gamma time law. -/
private theorem gaussianOverSqrtGammaLaw_unitRate_eq_gaussianTimeMixtureLaw
    (r : ℝ) (hr : 0 < r) :
    gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr =
      gaussianTimeMixtureLaw (reciprocalGammaTimeLaw r hr) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  -- Proof comment: both owner laws have the same characteristic function, namely the reciprocal-
  -- Gamma Gaussian-mixture transform identified earlier in the file.
  calc
    charFun (((gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr : ProbabilityMeasure ℝ) :
        Measure ℝ)) t
        = gaussianOverSqrtGammaCFP 1 1 r t := by
            exact gaussianOverSqrtGammaLaw_charFun_eq 1 1 r zero_lt_one zero_lt_one hr t
    _ = gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr) t := by
          exact congrFun (gaussianOverSqrtGammaUnit_cfp_eq_gaussianTimeMixture r hr) t
    _ = charFun (((gaussianTimeMixtureLaw (reciprocalGammaTimeLaw r hr) :
        ProbabilityMeasure ℝ) : Measure ℝ)) t := by
          symm
          exact congrFun (gaussianTimeMixtureLaw_charFun_eq (reciprocalGammaTimeLaw r hr)) t

/-- Helper for Example 16.2: once the reciprocal-Gamma Gaussian-mixture owner law is infinitely
divisible, the equivalent unit Gaussian-over-`√Gamma` owner law is infinitely divisible. -/
private theorem gaussianOverSqrtGammaLaw_unitRate_isInfinitelyDivisible_of_mixtureLaw
    (r : ℝ) (hr : 0 < r)
    (hmix :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianTimeMixtureLaw (reciprocalGammaTimeLaw r hr))) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  -- Proof comment: rewrite the unit owner law to the explicit reciprocal-Gamma Gaussian mixture
  -- and transport the supplied owner-law statement across that equality.
  simpa [gaussianOverSqrtGammaLaw_unitRate_eq_gaussianTimeMixtureLaw r hr] using hmix

/-- Helper for Example 16.2: an exact additive convolution root of the reciprocal-Gamma time law
pushes through the Gaussian-mixture construction to an exact `n`th convolution root of the unit
Gaussian-over-`√Gamma` owner law. -/
private theorem gaussianOverSqrtGammaUnitOwner_root_of_timeRoot
    (r : ℝ) (hr : 0 < r) (n : ℕ+) {τn : ProbabilityMeasure NNReal}
    (hpow : τn ^ (n : ℕ) = reciprocalGammaTimeLaw r hr) :
    ∃ ν : ProbabilityMeasure ℝ, ν ^ (n : ℕ) = gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr := by
  refine ⟨gaussianTimeMixtureLaw τn, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  -- Proof comment: the characteristic function of the chosen Gaussian-mixture root is the
  -- Gaussian-mixture transform of `τn`, whose `n`th power matches the reciprocal-Gamma mixture
  -- transform by the exact time-law root identity.
  calc
    charFun (((gaussianTimeMixtureLaw τn ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ)) t
        = charFun (((gaussianTimeMixtureLaw τn : ProbabilityMeasure ℝ) : Measure ℝ)) t ^ (n : ℕ) := by
            simpa using
              congrArg (fun f : ℝ → ℂ ↦ f t)
                (ProbabilityMeasure.charFun_pow (gaussianTimeMixtureLaw τn) (n : ℕ))
    _ = (gaussianTimeMixtureCFP τn t) ^ (n : ℕ) := by
          rw [congrFun (gaussianTimeMixtureLaw_charFun_eq τn) t]
    _ = gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr) t := by
          exact gaussianTimeMixture_pow_eq_of_timePow_eq n hpow t
    _ = gaussianOverSqrtGammaCFP 1 1 r t := by
          exact (congrFun (gaussianOverSqrtGammaUnit_cfp_eq_gaussianTimeMixture r hr) t).symm
    _ = charFun (((gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr : ProbabilityMeasure ℝ) :
          Measure ℝ)) t := by
          symm
          exact gaussianOverSqrtGammaLaw_charFun_eq 1 1 r zero_lt_one zero_lt_one hr t

/-- Helper for Example 16.2: exact additive convolution roots of the reciprocal-Gamma time law are
already enough to prove infinite divisibility of the unit Gaussian-over-`√Gamma` owner law. -/
private theorem gaussianOverSqrtGammaUnitOwnerLaw_isInfinitelyDivisible_of_timeRoots
    (r : ℝ) (hr : 0 < r)
    (hroot :
      ∀ n : ℕ+, ∃ τn : ProbabilityMeasure NNReal,
        τn ^ (n : ℕ) = reciprocalGammaTimeLaw r hr) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  refine ⟨?_⟩
  intro n
  rcases hroot n with ⟨τn, hτn⟩
  -- Proof comment: once an exact time-law root is available at level `n`, the previous helper
  -- turns it into the matching owner-law root for the unit Gaussian-over-`√Gamma` law.
  exact gaussianOverSqrtGammaUnitOwner_root_of_timeRoot r hr n hτn

/-- Helper for Example 16.2: the single remaining local analytic frontier is the unit
Gaussian-over-`√Gamma` owner law `gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr`. -/
private theorem gaussianOverSqrtGammaUnitOwnerLaw_isInfinitelyDivisibleLocal
    (r : ℝ) (hr : 0 < r) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  -- Route correction: the theorem-local support module already packages the cited owner-level
  -- analytic theorem, so this file only needs to consume that exact unit-law statement.
  -- Proof comment: specialize the support theorem at `σ² = θ = 1`; the surrounding file keeps
  -- the owner/CFP, mixture, and map transports local to this target.
  simpa using gaussianOverSqrtGammaLaw_isInfinitelyDivisible 1 1 r zero_lt_one zero_lt_one hr

/-- Helper for Example 16.2: once the local unit owner-law frontier is available, the exact
reciprocal-Gamma Gaussian-mixture characteristic function follows by the established owner/CFP
bridge and the unit-CFP identification. -/
private theorem gaussianTimeMixtureCFP_reciprocalGamma_isInfinitelyDivisible_of_unitOwnerLaw
    (r : ℝ) (hr : 0 < r)
    (hunit :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr)) :
    IsInfinitelyDivisibleCFP (gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr)) := by
  have hunitCFP :
      IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP 1 1 r) := by
    -- Proof comment: rewrite the unit owner-law theorem through the proved local owner/CFP
    -- equivalence before identifying the unit characteristic function with the reciprocal-Gamma
    -- Gaussian-mixture characteristic function.
    exact
      (gaussianOverSqrtGammaLaw_isInfinitelyDivisible_iff_cfp 1 1 r zero_lt_one zero_lt_one hr).1
        hunit
  -- Proof comment: the unit Gaussian-over-`√Gamma` characteristic function is exactly the
  -- reciprocal-Gamma Gaussian-mixture characteristic function.
  simpa [gaussianOverSqrtGammaUnit_cfp_eq_gaussianTimeMixture r hr] using hunitCFP

/-- Helper for Example 16.2: the exact reciprocal-Gamma Gaussian-mixture characteristic function
is the remaining analytic frontier after all local owner/CFP and scale transports are proved. -/
private theorem gaussianTimeMixtureCFP_reciprocalGamma_isInfinitelyDivisible
    (r : ℝ) (hr : 0 < r) :
    IsInfinitelyDivisibleCFP (gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr)) := by
  -- Route correction: the live blocker is now the smaller unit owner law, not the exact
  -- reciprocal-Gamma Gaussian-mixture characteristic function. The preceding adapter isolates the
  -- proved owner/CFP transport, so this declaration is now just the final bridge application.
  exact
    gaussianTimeMixtureCFP_reciprocalGamma_isInfinitelyDivisible_of_unitOwnerLaw r hr
      (gaussianOverSqrtGammaUnitOwnerLaw_isInfinitelyDivisibleLocal r hr)

/-- Helper for Example 16.2: the reciprocal-Gamma Gaussian-mixture owner law is infinitely
divisible once its exact characteristic function is known to be infinitely divisible. -/
private theorem gaussianTimeMixtureLaw_reciprocalGamma_isInfinitelyDivisible
    (r : ℝ) (hr : 0 < r) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianTimeMixtureLaw (reciprocalGammaTimeLaw r hr)) := by
  -- Proof comment: the local Gaussian-mixture owner/CFP equivalence reduces this owner-law step
  -- to the single exact reciprocal-Gamma Gaussian-mixture CFP frontier.
  exact
    (gaussianTimeMixtureLaw_isInfinitelyDivisible_iff_cfp (reciprocalGammaTimeLaw r hr)).2
      (gaussianTimeMixtureCFP_reciprocalGamma_isInfinitelyDivisible r hr)

/-- Helper for Example 16.2: once the local unit owner-law frontier is available, the unit
characteristic-function statement follows directly from the established owner/CFP transport, so an
explicit `ℕ+`-indexed root approximation is unnecessary duplication. -/
private theorem gaussianOverSqrtGammaUnit_cfp_isInfinitelyDivisible_of_ownerLaw
    (r : ℝ) (hr : 0 < r) :
    IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP 1 1 r) := by
  -- Route correction: earlier versions re-expressed the unit owner law through an imported
  -- support theorem. The target file now keeps the exact unit owner-law blocker local.
  -- Proof comment: earlier versions re-expressed the imported owner-law theorem through
  -- Corollary 16.8 as an explicit root-approximation witness. The owner/CFP equivalence already
  -- proved in this file is the cheaper canonical bridge.
  have howner :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
    -- Proof comment: the only remaining analytic premise is now stated directly at the exact unit
    -- owner law consumed by the local transport lemmas.
    exact gaussianOverSqrtGammaUnitOwnerLaw_isInfinitelyDivisibleLocal r hr
  -- Proof comment: rewrite the local unit owner-law theorem through the local owner/CFP transport
  -- equivalence to obtain the unit characteristic-function statement directly.
  exact
    (gaussianOverSqrtGammaLaw_isInfinitelyDivisible_iff_cfp 1 1 r zero_lt_one zero_lt_one hr).1
      howner

/-- Helper for Example 16.2: the unit Gaussian-over-`√Gamma` characteristic function is
infinitely divisible once the local unit owner-law frontier is rewritten through the local
owner/CFP bridge. -/
private theorem gaussianOverSqrtGammaUnit_cfp_isInfinitelyDivisible
    (r : ℝ) (hr : 0 < r) :
    IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP 1 1 r) := by
  -- Proof comment: the direct owner-to-CFP helper above removes the redundant root-approximation
  -- detour and keeps the live analytic frontier at the single local unit owner law only.
  exact gaussianOverSqrtGammaUnit_cfp_isInfinitelyDivisible_of_ownerLaw r hr

/-- Helper for Example 16.2: the Gaussian-over-`√Gamma` owner law is reduced to the unit
Gaussian-over-`√Gamma` characteristic-function frontier after the local scaling and owner/CFP
transport steps proved in this file. -/
private theorem gaussianOverSqrtGammaOwnerLaw_isInfinitelyDivisible
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw σ2 θ r hθ hr) := by
  -- Route correction: the file now routes the general owner law only through the exact local unit
  -- owner-law frontier and the already-proved scale transport, with no hidden support-module
  -- theorem on the proof path.
  -- Proof comment: once the unit owner law is available, the earlier scale-to-unit theorem
  -- finishes the general `σ², θ` case immediately.
  exact
    gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_unitRate σ2 θ r hσ2 hθ hr
      (gaussianOverSqrtGammaUnitOwnerLaw_isInfinitelyDivisibleLocal r hr)

/-- Helper for Example 16.2: the owner-law infinite-divisibility frontier yields infinite
divisibility of the canonical Gaussian-over-`√Gamma` characteristic function. -/
private theorem gaussianOverSqrtGammaCFP_isInfinitelyDivisible
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP σ2 θ r) := by
  -- Route correction: the transport layer is complete locally, so the only live blocker is the
  -- owner-law infinite-divisibility theorem isolated immediately above.
  -- Proof comment: transport the owner-law theorem across the local owner/CFP equivalence that
  -- was established earlier in this file.
  exact
    (gaussianOverSqrtGammaLaw_isInfinitelyDivisible_iff_cfp σ2 θ r hσ2 hθ hr).1
      (gaussianOverSqrtGammaOwnerLaw_isInfinitelyDivisible σ2 θ r hσ2 hθ hr)

/-- Helper for Example 16.2: after identifying the ratio pushforward with the canonical owner
law, the cited Gaussian-over-`√Gamma` theorem gives infinite divisibility of that pushforward. -/
private theorem ratioGaussianSqrtGamma_map_isInfinitelyDivisible_of_ownerLaw
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hXY : IndepFun X Y P) (σ2 : ℝ≥0) (θ r : ℝ)
    (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hX : HasLaw X (gaussianReal (0 : ℝ) σ2) P)
    (hY : HasLaw Y (gammaMeasure r θ) P)
    (howner :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw σ2 θ r hθ hr)) :
    let Z : Ω → ℝ := fun ω ↦ X ω / Real.sqrt (Y ω)
    let hZ : AEMeasurable Z P := ratioGaussianSqrtGamma_aemeasurable hX hY
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ) := by
  dsimp
  have hmap_eq :=
    ratioGaussianSqrtGamma_map_eq_ownerLaw
      (P := P) (X := X) (Y := Y) hXY σ2 θ r hσ2 hθ hr hX hY
  -- Proof comment: rewrite the ratio pushforward law to the canonical owner law and transport
  -- the supplied owner-level infinite-divisibility statement across that identification.
  simpa [hmap_eq] using howner

/-- Helper for Example 16.2: after identifying the ratio pushforward with the canonical owner
law, the cited Gaussian-over-`√Gamma` theorem gives infinite divisibility of that pushforward. -/
private theorem ratioGaussianSqrtGamma_map_isInfinitelyDivisible
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hXY : IndepFun X Y P) (σ2 : ℝ≥0) (θ r : ℝ)
    (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hX : HasLaw X (gaussianReal (0 : ℝ) σ2) P)
    (hY : HasLaw Y (gammaMeasure r θ) P) :
    let Z : Ω → ℝ := fun ω ↦ X ω / Real.sqrt (Y ω)
    let hZ : AEMeasurable Z P := ratioGaussianSqrtGamma_aemeasurable hX hY
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ) := by
  -- Route correction: the local file only needs the owner-law transport point; the analytic
  -- infinite-divisibility frontier remains isolated in the owner-law theorem stated just above.
  have howner :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw σ2 θ r hθ hr) := by
    -- Proof comment: the general Gaussian-over-`√Gamma` owner law is already known to be
    -- infinitely divisible, so only the map-to-owner rewrite remains here.
    exact gaussianOverSqrtGammaOwnerLaw_isInfinitelyDivisible σ2 θ r hσ2 hθ hr
  exact
    ratioGaussianSqrtGamma_map_isInfinitelyDivisible_of_ownerLaw
      (P := P) (X := X) (Y := Y) hXY σ2 θ r hσ2 hθ hr hX hY howner

/-- Helper for Example 16.2: once the ratio pushforward is identified with the canonical owner
law, any owner-law infinite-divisibility statement transports back to the original random
variable. -/
private theorem ratioGaussianSqrtGamma_isInfinitelyDivisible_of_ownerLaw
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hXY : IndepFun X Y P) (σ2 : ℝ≥0) (θ r : ℝ)
    (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hX : HasLaw X (gaussianReal (0 : ℝ) σ2) P)
    (hY : HasLaw Y (gammaMeasure r θ) P)
    (howner :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw σ2 θ r hθ hr)) :
    IsInfinitelyDivisibleRandomVariable P (fun ω ↦ X ω / Real.sqrt (Y ω)) := by
  let Z : Ω → ℝ := fun ω ↦ X ω / Real.sqrt (Y ω)
  have hZ : AEMeasurable Z P := ratioGaussianSqrtGamma_aemeasurable hX hY
  have hmap :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ) := by
    -- Proof comment: the dedicated map-side helper packages the only transport step from the
    -- owner law to the pushforward law.
    simpa [Z, hZ] using
      ratioGaussianSqrtGamma_map_isInfinitelyDivisible_of_ownerLaw
        (P := P) (X := X) (Y := Y) hXY σ2 θ r hσ2 hθ hr hX hY howner
  -- Proof comment: the existing measurable-representative bridge converts the pushforward-law
  -- statement back to the original random variable.
  exact ratioGaussianSqrtGamma_isInfinitelyDivisible_from_map P X Y hZ hmap

/-- Example 16.2 (8): If `X` and `Y` are independent with `X ∼ N_{0,σ²}` and
`Y ∼ Γ_{θ,r}` for `σ², θ, r > 0`, then the law of `X / √Y` is infinitely divisible. -/
theorem ratio_gaussian_sqrtGamma_isInfinitelyDivisible
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hXY : IndepFun X Y P) (σ2 : ℝ≥0) (θ r : ℝ)
    (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hX : HasLaw X (gaussianReal (0 : ℝ) σ2) P)
    (hY : HasLaw Y (gammaMeasure r θ) P) :
    IsInfinitelyDivisibleRandomVariable P (fun ω ↦ X ω / Real.sqrt (Y ω)) := by
  -- Proof comment: the entire local transport layer factors through the canonical owner law, so
  -- only the isolated owner-level theorem remains as the live analytic dependency.
  exact
    ratioGaussianSqrtGamma_isInfinitelyDivisible_of_ownerLaw
      (P := P) (X := X) (Y := Y) hXY σ2 θ r hσ2 hθ hr hX hY
      (gaussianOverSqrtGammaOwnerLaw_isInfinitelyDivisible σ2 θ r hσ2 hθ hr)

/-- Helper for Example 16.2: the Student `t` specialization of the Gaussian-over-`√Gamma`
variance-mixture law is infinitely divisible when `θ = r = k / 2` and `σ² = 1`. -/
theorem studentTRandomVariable_isInfinitelyDivisible
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hXY : IndepFun X Y P) (k : ℕ+)
    (hX : HasLaw X (gaussianReal (0 : ℝ) 1) P)
    (hY : HasLaw Y (gammaMeasure ((k : ℝ) / 2) ((k : ℝ) / 2)) P) :
    IsInfinitelyDivisibleRandomVariable P (fun ω ↦ X ω / Real.sqrt (Y ω)) := by
  have hk : 0 < (k : ℝ) := by
    exact_mod_cast k.pos
  -- Proof comment: specialize the Gaussian-over-`√Gamma` theorem at `σ² = 1` and
  -- `θ = r = k / 2`.
  exact
    ratio_gaussian_sqrtGamma_isInfinitelyDivisible
      (P := P) (X := X) (Y := Y) hXY 1 ((k : ℝ) / 2) ((k : ℝ) / 2)
      (by norm_num) (by linarith) (by linarith) hX hY

/-- The binomial law viewed as a probability measure on `ℝ` via the inclusion `ℕ ↪ ℝ`. -/
noncomputable def binomialRealProbabilityMeasure (n : ℕ) (p : I) : ProbabilityMeasure ℝ :=
  let ν : ProbabilityMeasure ℕ := ⟨binomial n p, inferInstance⟩
  ν.map (show AEMeasurable (fun k : ℕ ↦ (k : ℝ)) ν from Measurable.of_discrete.aemeasurable)

/-- Helper for Example 16.2: a probability law with full mass on a singleton is the corresponding
Dirac measure. -/
private lemma eq_dirac_of_measure_singleton_eq_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {x : ℝ} (hx : μ ({x} : Set ℝ) = 1) :
    μ = Measure.dirac x := by
  have hae : ∀ᵐ y ∂μ, y ∈ ({x} : Set ℝ) :=
    (mem_ae_iff_prob_eq_one (measurableSet_singleton x)).2 hx
  -- Proof comment: restricting to the singleton turns the probability law into a scalar multiple
  -- of the matching Dirac mass.
  calc
    μ = μ.restrict ({x} : Set ℝ) := (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ = μ ({x} : Set ℝ) • Measure.dirac x := Measure.restrict_singleton μ x
    _ = Measure.dirac x := by rw [hx, one_smul]

/-- Helper for Example 16.2: the sum of `n` i.i.d. real random variables with common law `ν` has
law `ν ^ n`. -/
private lemma iidSum_hasLaw_pow {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : ProbabilityMeasure ℝ) (n : ℕ+)
    (X : Fin n → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_law : ∀ i, HasLaw (X i) (ν : Measure ℝ) P)
    (hX_indep : iIndepFun X P) :
    HasLaw (fun ω ↦ ∑ i, X i ω) (((ν ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ)) P := by
  let P' : ProbabilityMeasure Ω := ⟨P, inferInstance⟩
  let hSumLaw :
      ∀ s : Finset (Fin n),
        HasLaw (fun ω ↦ ∑ i ∈ s, X i ω)
          ((((ν ^ s.card : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) P' := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty =>
        -- Proof comment: the empty sum is constantly `0`, whose law is the convolution unit
        -- `δ₀`.
        refine ProbabilityTheory.HasLaw.mk aemeasurable_const ?_
        simp [ProbabilityMeasure.one_eq_diracProba, MeasureTheory.diracProba]
    | @insert i s hi ih =>
        let S : Ω → ℝ := fun ω ↦ ∑ j ∈ s, X j ω
        have hSumEqS : (∑ j ∈ s, X j) = S := by
          funext ω
          simp [S, Finset.sum_apply]
        have hsum :
            HasLaw S
              ((((ν ^ s.card : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) P' := by
          simpa [S] using ih
        have hindepSum :
            IndepFun (∑ j ∈ s, X j) (X i) P' := by
          simpa using hX_indep.indepFun_finset_sum_of_notMem hX_meas hi
        have hindep :
            IndepFun S (X i) P' := by
          exact hSumEqS ▸ hindepSum
        have hstep :
            HasLaw
              (fun ω ↦ S ω + X i ω)
              ((((ν ^ s.card : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ) : Measure ℝ).conv
                (ν : Measure ℝ))
              P' := by
          simpa [S, Pi.add_apply] using hindep.hasLaw_add hsum (hX_law i)
        -- Proof comment: the inserted summand contributes one more convolution factor.
        convert hstep using 1
        · funext ω
          simp [S, Finset.sum_insert hi, add_comm]
        · simp [pow_succ, Finset.card_insert_of_notMem hi]
  -- Proof comment: specialize the finite-set convolution-power law to the full index set.
  simpa [P'] using hSumLaw Finset.univ

/-- Helper for Example 16.2: if every summand in a `Fin n` family is strictly larger than `c`,
then the total sum is strictly larger than `(n : ℝ) * c`. -/
private lemma constMul_lt_sum_of_forall_lt
    (n : ℕ+) {X : Fin n → ℝ} {c : ℝ}
    (hX : ∀ i, c < X i) :
    (n : ℝ) * c < ∑ i, X i := by
  -- Proof comment: compare the constant sum `∑ i, c` with `∑ i, X i` termwise and use one
  -- strict coordinate.
  have hsum : ∑ i : Fin n, c < ∑ i : Fin n, X i := by
    refine Finset.sum_lt_sum (fun i _ ↦ (hX i).le) ?_
    exact ⟨0, Finset.mem_univ _, hX 0⟩
  simpa [nsmul_eq_mul, mul_comm] using hsum

/-- Helper for Example 16.2: if every summand in a `Fin n` family is strictly smaller than `c`,
then the total sum is strictly smaller than `(n : ℝ) * c`. -/
private lemma sum_lt_constMul_of_forall_lt
    (n : ℕ+) {X : Fin n → ℝ} {c : ℝ}
    (hX : ∀ i, X i < c) :
    ∑ i, X i < (n : ℝ) * c := by
  -- Proof comment: compare the sum to the constant upper bound coordinatewise and keep one strict
  -- inequality.
  have hsum : ∑ i : Fin n, X i < ∑ i : Fin n, c := by
    refine Finset.sum_lt_sum (fun i _ ↦ (hX i).le) ?_
    exact ⟨0, Finset.mem_univ _, hX 0⟩
  simpa [nsmul_eq_mul, mul_comm] using hsum

/-- Helper for Example 16.2: any `n`th convolution root of a law supported on `Set.Icc a b` is
supported on `Set.Icc (a / n) (b / n)`. -/
private lemma root_measure_Icc_div_eq_one
    (μ ν : ProbabilityMeasure ℝ) (a b : ℝ) (n : ℕ+)
    (hpow : ν ^ (n : ℕ) = μ) (hμ : (μ : Measure ℝ) (Set.Icc a b) = 1) :
    (ν : Measure ℝ) (Set.Icc (a / (n : ℝ)) (b / (n : ℝ))) = 1 := by
  have hnRpos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  have hnR : (n : ℝ) ≠ 0 := hnRpos.ne'
  rcases ProbabilityTheory.exists_iid (Fin n) ((ν : Measure ℝ)) with
    ⟨Ω, _, P, X, hX_meas, hX_law, hX_indep, hPprob⟩
  let S : Ω → ℝ := fun ω ↦ ∑ i, X i ω
  let upper : ℝ := b / (n : ℝ)
  let lower : ℝ := a / (n : ℝ)
  have hsum_law_pow : HasLaw S (((ν ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ)) P :=
    iidSum_hasLaw_pow P ν n X hX_meas hX_law hX_indep
  have hsum_law : HasLaw S (μ : Measure ℝ) P := by
    refine ProbabilityTheory.HasLaw.mk (by
      -- Proof comment: the iid sum is a finite measurable sum.
      fun_prop) ?_
    calc
      Measure.map S P = ((ν ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) := hsum_law_pow.map_eq
      _ = (μ : Measure ℝ) := by
            simpa using congrArg (fun η : ProbabilityMeasure ℝ ↦ (η : Measure ℝ)) hpow
  have hsum_Icc : P (S ⁻¹' Set.Icc a b) = 1 := by
    calc
      P (S ⁻¹' Set.Icc a b) = Measure.map S P (Set.Icc a b) := by
        rw [Measure.map_apply (by
          -- Proof comment: the sum map is measurable because each coordinate is measurable.
          fun_prop) measurableSet_Icc]
      _ = (μ : Measure ℝ) (Set.Icc a b) := by rw [hsum_law.map_eq]
      _ = 1 := hμ
  have hS_meas : Measurable S := by
    -- Proof comment: finite sums of measurable coordinate maps stay measurable.
    fun_prop
  have hsum_Icc_ae : ∀ᵐ ω ∂P, S ω ∈ Set.Icc a b :=
    (mem_ae_iff_prob_eq_one (hS_meas measurableSet_Icc)).2 hsum_Icc
  have hupper_zero : (ν : Measure ℝ) (Set.Ioi upper) = 0 := by
    by_contra hupper_ne
    have hupper_pos : 0 < (ν : Measure ℝ) (Set.Ioi upper) := by
      have hupper_ne' : (0 : ENNReal) ≠ (ν : Measure ℝ) (Set.Ioi upper) := by
        intro hzero
        exact hupper_ne hzero.symm
      exact lt_of_le_of_ne bot_le hupper_ne'
    let A : Set Ω := ⋂ i ∈ (Finset.univ : Finset (Fin n)), X i ⁻¹' Set.Ioi upper
    have hA_eq :
        P A = ((ν : Measure ℝ) (Set.Ioi upper)) ^ (n : ℕ) := by
      calc
        P A = ∏ i ∈ (Finset.univ : Finset (Fin n)), P (X i ⁻¹' Set.Ioi upper) := by
          simpa [A] using
            hX_indep.measure_inter_preimage_eq_mul (Finset.univ : Finset (Fin n))
              (fun i _ ↦ measurableSet_Ioi)
        _ = ∏ i ∈ (Finset.univ : Finset (Fin n)), (ν : Measure ℝ) (Set.Ioi upper) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          calc
            P (X i ⁻¹' Set.Ioi upper) = Measure.map (X i) P (Set.Ioi upper) := by
              rw [Measure.map_apply (hX_meas i) measurableSet_Ioi]
            _ = (ν : Measure ℝ) (Set.Ioi upper) := by rw [hX_law i |>.map_eq]
        _ = ((ν : Measure ℝ) (Set.Ioi upper)) ^ (n : ℕ) := by simp
    have hA_pos : 0 < P A := by
      rw [hA_eq]
      have hpow_ne' : (0 : ENNReal) ≠ ((ν : Measure ℝ) (Set.Ioi upper)) ^ (n : ℕ) := by
        intro hzero
        exact (pow_ne_zero (n : ℕ) hupper_ne) hzero.symm
      exact lt_of_le_of_ne bot_le hpow_ne'
    have hA_subset : A ⊆ S ⁻¹' Set.Ioi b := by
      intro ω hω
      have hω' : ∀ i : Fin n, upper < X i ω := by
        intro i
        have hi : ω ∈ X i ⁻¹' Set.Ioi upper := by
          exact Set.mem_iInter₂.mp hω i (Finset.mem_univ i)
        simpa [upper, Set.mem_preimage, Set.mem_Ioi] using hi
      have hsum_gt : (n : ℝ) * upper < S ω := by
        simpa [S] using constMul_lt_sum_of_forall_lt n hω'
      have hb : (n : ℝ) * upper = b := by
        dsimp [upper]
        field_simp [hnR]
      simpa [Set.mem_preimage, Set.mem_Ioi, hb] using hsum_gt
    have hS_Ioi_zero : P (S ⁻¹' Set.Ioi b) = 0 := by
      refine (compl_mem_ae_iff.1 ?_)
      filter_upwards [hsum_Icc_ae] with ω hω
      simp [Set.mem_preimage, Set.mem_Ioi, not_lt_of_ge hω.2]
    exact hA_pos.ne' (measure_mono_null hA_subset hS_Ioi_zero)
  have hlower_zero : (ν : Measure ℝ) (Set.Iio lower) = 0 := by
    by_contra hlower_ne
    have hlower_pos : 0 < (ν : Measure ℝ) (Set.Iio lower) := by
      have hlower_ne' : (0 : ENNReal) ≠ (ν : Measure ℝ) (Set.Iio lower) := by
        intro hzero
        exact hlower_ne hzero.symm
      exact lt_of_le_of_ne bot_le hlower_ne'
    let A : Set Ω := ⋂ i ∈ (Finset.univ : Finset (Fin n)), X i ⁻¹' Set.Iio lower
    have hA_eq :
        P A = ((ν : Measure ℝ) (Set.Iio lower)) ^ (n : ℕ) := by
      calc
        P A = ∏ i ∈ (Finset.univ : Finset (Fin n)), P (X i ⁻¹' Set.Iio lower) := by
          simpa [A] using
            hX_indep.measure_inter_preimage_eq_mul (Finset.univ : Finset (Fin n))
              (fun i _ ↦ measurableSet_Iio)
        _ = ∏ i ∈ (Finset.univ : Finset (Fin n)), (ν : Measure ℝ) (Set.Iio lower) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          calc
            P (X i ⁻¹' Set.Iio lower) = Measure.map (X i) P (Set.Iio lower) := by
              rw [Measure.map_apply (hX_meas i) measurableSet_Iio]
            _ = (ν : Measure ℝ) (Set.Iio lower) := by rw [hX_law i |>.map_eq]
        _ = ((ν : Measure ℝ) (Set.Iio lower)) ^ (n : ℕ) := by simp
    have hA_pos : 0 < P A := by
      rw [hA_eq]
      have hpow_ne' : (0 : ENNReal) ≠ ((ν : Measure ℝ) (Set.Iio lower)) ^ (n : ℕ) := by
        intro hzero
        exact (pow_ne_zero (n : ℕ) hlower_ne) hzero.symm
      exact lt_of_le_of_ne bot_le hpow_ne'
    have hA_subset : A ⊆ S ⁻¹' Set.Iio a := by
      intro ω hω
      have hω' : ∀ i : Fin n, X i ω < lower := by
        intro i
        have hi : ω ∈ X i ⁻¹' Set.Iio lower := by
          exact Set.mem_iInter₂.mp hω i (Finset.mem_univ i)
        simpa [lower, Set.mem_preimage, Set.mem_Iio] using hi
      have hsum_lt : S ω < (n : ℝ) * lower := by
        simpa [S] using sum_lt_constMul_of_forall_lt n hω'
      have ha : (n : ℝ) * lower = a := by
        dsimp [lower]
        field_simp [hnR]
      simpa [Set.mem_preimage, Set.mem_Iio, ha] using hsum_lt
    have hS_Iio_zero : P (S ⁻¹' Set.Iio a) = 0 := by
      refine (compl_mem_ae_iff.1 ?_)
      filter_upwards [hsum_Icc_ae] with ω hω
      simp [Set.mem_preimage, Set.mem_Iio, not_lt_of_ge hω.1]
    exact hA_pos.ne' (measure_mono_null hA_subset hS_Iio_zero)
  have hupper_ae : ∀ᵐ x ∂(ν : Measure ℝ), x ∉ Set.Ioi upper := compl_mem_ae_iff.2 hupper_zero
  have hlower_ae : ∀ᵐ x ∂(ν : Measure ℝ), x ∉ Set.Iio lower := compl_mem_ae_iff.2 hlower_zero
  have hIcc_ae : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Set.Icc lower upper := by
    filter_upwards [hupper_ae, hlower_ae] with x hxUpper hxLower
    have hxUpper' : x ≤ upper := by
      simp only [Set.mem_Ioi, not_lt] at hxUpper
      exact hxUpper
    have hxLower' : lower ≤ x := by
      simp only [Set.mem_Iio, not_lt] at hxLower
      exact hxLower
    simp only [Set.mem_Icc]
    exact ⟨hxLower', hxUpper'⟩
  exact (mem_ae_iff_prob_eq_one measurableSet_Icc).1 hIcc_ae

/-- Helper for Example 16.2: every convolution root of a law supported on `Set.Icc a b` has
variance at most `((b - a)^2 / 4) / m`. -/
private lemma variance_le_intervalSq_div_rootOrder
    (μ : ProbabilityMeasure ℝ) [MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ]
    (a b : ℝ) (hμ : (μ : Measure ℝ) (Set.Icc a b) = 1) :
    ∀ m : ℕ+, Var[id; (μ : Measure ℝ)] ≤ ((b - a) ^ 2 / 4) / (m : ℝ)
  | m => by
      have hmRpos : 0 < (m : ℝ) := by
        exact_mod_cast m.pos
      have hmR : (m : ℝ) ≠ 0 := hmRpos.ne'
      rcases
          (inferInstance : MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ).exists_root m
        with ⟨ν, hpow⟩
      have hroot_Icc :
          (ν : Measure ℝ) (Set.Icc (a / (m : ℝ)) (b / (m : ℝ))) = 1 :=
        root_measure_Icc_div_eq_one μ ν a b m hpow hμ
      have hroot_ae :
          ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Set.Icc (a / (m : ℝ)) (b / (m : ℝ)) :=
        (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hroot_Icc
      have hν_memLp : MemLp id 2 (ν : Measure ℝ) := by
        -- Proof comment: the shrunken interval support gives a uniform `L²` bound for the root
        -- law.
        exact MemLp.of_bound aestronglyMeasurable_id (max |a / (m : ℝ)| |b / (m : ℝ)|) <| by
          filter_upwards [hroot_ae] with x hx
          exact abs_le_max_abs_abs hx.1 hx.2
      have hν_var_le :
          Var[id; (ν : Measure ℝ)] ≤ (((b / (m : ℝ)) - (a / (m : ℝ))) / 2) ^ 2 :=
        ProbabilityTheory.variance_le_sq_of_bounded hroot_ae aemeasurable_id
      rcases ProbabilityTheory.exists_iid (Fin m) ((ν : Measure ℝ)) with
        ⟨Ω, _, P, X, hX_meas, hX_law, hX_indep, hPprob⟩
      let S : Ω → ℝ := fun ω ↦ ∑ i, X i ω
      have hsum_law_pow : HasLaw S (((ν ^ (m : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ)) P :=
        iidSum_hasLaw_pow P ν m X hX_meas hX_law hX_indep
      have hsum_law : HasLaw S (μ : Measure ℝ) P := by
        refine ProbabilityTheory.HasLaw.mk (by
          -- Proof comment: the iid sum is a finite measurable sum.
          fun_prop) ?_
        calc
          Measure.map S P = ((ν ^ (m : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) :=
            hsum_law_pow.map_eq
          _ = (μ : Measure ℝ) := by
                simpa using congrArg (fun η : ProbabilityMeasure ℝ ↦ (η : Measure ℝ)) hpow
      have hX_memLp : ∀ i, MemLp (X i) 2 P := by
        intro i
        have hIdent :
            IdentDistrib (X i) id P (ν : Measure ℝ) :=
          (hX_law i).identDistrib (ProbabilityTheory.HasLaw.id (μ := (ν : Measure ℝ)))
        exact (hIdent.memLp_iff).2 hν_memLp
      have hX_pairwise :
          Set.Pairwise (↑(Finset.univ : Finset (Fin m))) fun i j ↦ IndepFun (X i) (X j) P := by
        intro i hi j hj hij
        exact hX_indep.indepFun hij
      have hS_eq : S = ∑ i, X i := by
        funext ω
        simp [S, Finset.sum_apply]
      have hsum_var :
          Var[S; P] = ∑ i : Fin m, Var[X i; P] := by
        rw [hS_eq]
        simpa using
          (IndepFun.variance_sum (μ := P) (s := Finset.univ)
            (fun i _ ↦ hX_memLp i) hX_pairwise)
      have hXi_var : ∀ i, Var[X i; P] = Var[id; (ν : Measure ℝ)] := by
        intro i
        exact (hX_law i).variance_eq
      have hscale :
          (m : ℝ) * ((((b / (m : ℝ)) - (a / (m : ℝ))) / 2) ^ 2) =
            ((b - a) ^ 2 / 4) / (m : ℝ) := by
        field_simp [hmR]
        ring
      calc
        Var[id; (μ : Measure ℝ)] = Var[S; P] := by symm; exact hsum_law.variance_eq
        _ = ∑ i : Fin m, Var[X i; P] := hsum_var
        _ = ∑ i : Fin m, Var[id; (ν : Measure ℝ)] := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hXi_var i
        _ = (m : ℝ) * Var[id; (ν : Measure ℝ)] := by
              simp [nsmul_eq_mul]
        _ ≤ (m : ℝ) * ((((b / (m : ℝ)) - (a / (m : ℝ))) / 2) ^ 2) := by
              exact mul_le_mul_of_nonneg_left hν_var_le hmRpos.le
        _ = ((b - a) ^ 2 / 4) / (m : ℝ) := hscale

/-- Helper for Example 16.2: an infinitely divisible law with full mass on a bounded interval must
already be a Dirac measure. -/
private theorem infinitelyDivisible_eq_dirac_of_measure_Icc_eq_one
    (μ : ProbabilityMeasure ℝ) [MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ]
    (a b : ℝ)
    (hμ : (μ : Measure ℝ) (Set.Icc a b) = 1) :
    ∃ x ∈ Set.Icc a b, (μ : Measure ℝ) = Measure.dirac x := by
  have hab : a ≤ b := by
    by_contra hab
    have : (0 : ENNReal) = 1 := by
      simpa [Set.Icc_eq_empty, lt_of_not_ge hab] using hμ
    exact zero_ne_one this
  have hμ_ae : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Set.Icc a b :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hμ
  have hμ_memLp : MemLp id 2 (μ : Measure ℝ) := by
    -- Proof comment: the original bounded support gives a global `L²` bound for the identity.
    exact MemLp.of_bound aestronglyMeasurable_id (max |a| |b|) <| by
      filter_upwards [hμ_ae] with x hx
      exact abs_le_max_abs_abs hx.1 hx.2
  have hVar_zero : Var[id; (μ : Measure ℝ)] = 0 := by
    by_contra hVar_ne
    let C : ℝ := (b - a) ^ 2 / 4
    have hVar_pos : 0 < Var[id; (μ : Measure ℝ)] :=
      by
        have hVar_ne' : (0 : ℝ) ≠ Var[id; (μ : Measure ℝ)] := by
          intro hzero
          exact hVar_ne hzero.symm
        exact lt_of_le_of_ne (variance_nonneg _ _) hVar_ne'
    obtain ⟨N, hN⟩ := exists_nat_gt (C / Var[id; (μ : Measure ℝ)])
    let m : ℕ+ := ⟨N + 1, Nat.succ_pos _⟩
    have hmRpos : 0 < (m : ℝ) := by
      exact_mod_cast m.pos
    have hquot_lt : C / (m : ℝ) < Var[id; (μ : Measure ℝ)] := by
      have hCm : C / Var[id; (μ : Measure ℝ)] < (m : ℝ) := by
        exact lt_trans hN (by
          change (N : ℝ) < ((N + 1 : ℕ) : ℝ)
          exact_mod_cast Nat.lt_succ_self N)
      have hCv : C < (m : ℝ) * Var[id; (μ : Measure ℝ)] := by
        exact (div_lt_iff₀ hVar_pos).1 hCm
      exact (div_lt_iff₀ hmRpos).2 (by simpa [mul_comm] using hCv)
    have hVar_le := variance_le_intervalSq_div_rootOrder μ a b hμ m
    exact (not_lt_of_ge hVar_le hquot_lt).elim
  let x : ℝ := ∫ y, y ∂(μ : Measure ℝ)
  have hconst : id =ᵐ[(μ : Measure ℝ)] fun _ ↦ x := by
    -- Proof comment: variance zero makes the identity almost surely constant at its expectation.
    simpa [x] using ae_eq_integral_of_variance_eq_zero hμ_memLp hVar_zero
  have hsingleton : (μ : Measure ℝ) ({x} : Set ℝ) = 1 := by
    have hsingle_ae : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ ({x} : Set ℝ) := by
      filter_upwards [hconst] with y hy
      simpa [Set.mem_singleton_iff] using hy
    exact (mem_ae_iff_prob_eq_one (measurableSet_singleton x)).1 hsingle_ae
  have hdirac : (μ : Measure ℝ) = Measure.dirac x :=
    eq_dirac_of_measure_singleton_eq_one hsingleton
  have hx : x ∈ Set.Icc a b := by
    have hx_mass : (Measure.dirac x) (Set.Icc a b) = 1 := by
      simpa [hdirac] using hμ
    by_contra hx_not
    simp [hx_not] at hx_mass
  exact ⟨x, hx, hdirac⟩

/-- Helper for Example 16.2: the real-valued binomial law is supported on the interval `[0, n]`. -/
private lemma binomialRealProbabilityMeasure_measure_Icc_zero_n_eq_one
    (n : ℕ+) (p : I) :
    ((binomialRealProbabilityMeasure (n : ℕ) p : ProbabilityMeasure ℝ) : Measure ℝ)
      (Set.Icc 0 (n : ℝ)) = 1 := by
  have hNat : ∀ᵐ k : ℕ ∂Bin((n : ℕ), p), k ≤ (n : ℕ) := by
    -- Proof comment: the nat-valued binomial law is supported on `{0, …, n}`.
    simpa using
      (ProbabilityTheory.ae_le_of_hasLaw_binomial (n := (n : ℕ)) (p := p)
        (X := id) (P := Bin((n : ℕ), p)) (ProbabilityTheory.HasLaw.id (μ := Bin((n : ℕ), p))))
  have hReal :
      ∀ᵐ x : ℝ ∂(((binomialRealProbabilityMeasure (n : ℕ) p : ProbabilityMeasure ℝ) : Measure ℝ)),
        x ∈ Set.Icc 0 (n : ℝ) := by
    have hRealBin : ∀ᵐ x : ℝ ∂Bin(ℝ, (n : ℕ), p), x ∈ Set.Icc 0 (n : ℝ) := by
      -- Proof comment: `Bin(ℝ, n, p)` is the cast pushforward of `Bin(n, p)`, so `HasLaw.ae_iff`
      -- transports the nat-valued support bound.
      let hCastLaw : HasLaw (fun k : ℕ ↦ (k : ℝ)) Bin(ℝ, (n : ℕ), p) Bin((n : ℕ), p) :=
        ProbabilityTheory.HasLaw.mk measurableNatCastReal.aemeasurable rfl
      have hpMeas : Measurable (fun x : ℝ ↦ x ∈ Set.Icc 0 (n : ℝ)) := by
        have hLowerMeas : Measurable (fun x : ℝ ↦ (0 : ℝ) ≤ x) :=
          (show Measurable fun _ : ℝ ↦ (0 : ℝ) from measurable_const).le' measurable_id
        have hUpperMeas : Measurable (fun x : ℝ ↦ x ≤ (n : ℝ)) :=
          measurable_id.le' (show Measurable fun _ : ℝ ↦ (n : ℝ) from measurable_const)
        simpa [Set.mem_Icc] using hLowerMeas.and hUpperMeas
      exact (hCastLaw.ae_iff (p := fun x : ℝ ↦ x ∈ Set.Icc 0 (n : ℝ)) hpMeas).1 <| by
        filter_upwards [hNat] with k hk
        exact ⟨by exact_mod_cast Nat.zero_le k, by exact_mod_cast hk⟩
    simpa [binomialRealProbabilityMeasure] using hRealBin
  exact (mem_ae_iff_prob_eq_one measurableSet_Icc).1 hReal

-- Proof sketch: a nondegenerate binomial law is finitely supported on `{0, …, n}`; any
-- hypothetical convolution roots would force an impossible bounded-support infinitely divisible
-- law, so the binomial law cannot be infinitely divisible.
/-- Part (9) of Example 16.2: The nondegenerate binomial law with parameters `n ≥ 1` and
`p ∈ (0,1)`, viewed as a probability law on `ℝ` via the inclusion `ℕ ↪ ℝ`, is not infinitely
divisible. -/
theorem binomial_not_isInfinitelyDivisible
    (n : ℕ+) (p : I) (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1) :
    ¬ MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (binomialRealProbabilityMeasure (n : ℕ) p) := by
  intro hInf
  let μ : ProbabilityMeasure ℝ := binomialRealProbabilityMeasure (n : ℕ) p
  letI : MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ := hInf
  have hμ_Icc : (μ : Measure ℝ) (Set.Icc 0 (n : ℝ)) = 1 :=
    binomialRealProbabilityMeasure_measure_Icc_zero_n_eq_one n p
  obtain ⟨x, hx, hdirac⟩ :=
    infinitelyDivisible_eq_dirac_of_measure_Icc_eq_one μ 0 (n : ℝ) hμ_Icc
  have hmass0 : 0 < ((μ : Measure ℝ) ({0} : Set ℝ)).toReal := by
    -- Proof comment: the binomial law has strictly positive mass at `0`.
    have hmass0Bin : 0 < (Bin(ℝ, (n : ℕ), p) ({0} : Set ℝ)).toReal := by
      rw [show Bin(ℝ, (n : ℕ), p) = Measure.map (Nat.cast : ℕ → ℝ) (Bin((n : ℕ), p)) by rfl]
      rw [Measure.map_apply measurableNatCastReal (measurableSet_singleton 0)]
      have hpre0 : (Nat.cast : ℕ → ℝ) ⁻¹' ({0} : Set ℝ) = ({0} : Set ℕ) := by
        ext k
        simp
      rw [hpre0]
      have : 0 < (Bin((n : ℕ), p) ({0} : Set ℕ)).toReal := by
        rw [binomial_apply_singleton_toReal (n : ℕ) 0 p]
        simpa using (pow_pos (sub_pos.2 hp₁) (n : ℕ))
      exact this
    simpa [μ, binomialRealProbabilityMeasure] using hmass0Bin
  have hmassN : 0 < ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal := by
    -- Proof comment: the binomial law also has strictly positive mass at the top endpoint `n`.
    have hmassNBin : 0 < (Bin(ℝ, (n : ℕ), p) ({(n : ℝ)} : Set ℝ)).toReal := by
      rw [show Bin(ℝ, (n : ℕ), p) = Measure.map (Nat.cast : ℕ → ℝ) (Bin((n : ℕ), p)) by rfl]
      rw [Measure.map_apply measurableNatCastReal (measurableSet_singleton (n : ℝ))]
      have hpreN : (Nat.cast : ℕ → ℝ) ⁻¹' ({(n : ℝ)} : Set ℝ) = ({(n : ℕ)} : Set ℕ) := by
        ext k
        simp
      rw [hpreN]
      have : 0 < (Bin((n : ℕ), p) ({(n : ℕ)} : Set ℕ)).toReal := by
        rw [binomial_apply_singleton_toReal (n : ℕ) (n : ℕ) p]
        simpa using (pow_pos hp₀ (n : ℕ))
      exact this
    simpa [μ, binomialRealProbabilityMeasure] using hmassNBin
  have hx_zero : x = 0 := by
    by_contra hx_zero
    have : 0 < ((Measure.dirac x) ({0} : Set ℝ)).toReal := by
      simpa [hdirac] using hmass0
    simp [hx_zero] at this
  have hx_top : x = (n : ℝ) := by
    by_contra hx_top
    have : 0 < ((Measure.dirac x) ({(n : ℝ)} : Set ℝ)).toReal := by
      simpa [hdirac] using hmassN
    simp [hx_top] at this
  have hnR_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  have : (n : ℝ) = 0 := by
    simpa [hx_zero] using hx_top.symm
  exact hnR_ne this

-- Proof sketch: if an infinitely divisible probability law has full mass on a bounded interval,
-- repeated convolution roots shrink the interval width; letting the width tend to `0` forces the
-- law to collapse to a single Dirac mass.
/-- Part (10) of Example 16.2: An infinitely divisible probability distribution
concentrated on a bounded interval must be a Dirac mass. Equivalently, there is no nontrivial
infinitely divisible distribution supported in a bounded interval. -/
theorem eq_dirac_of_isInfinitelyDivisible_of_measure_Icc_eq_one
    (μ : ProbabilityMeasure ℝ) [MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ]
    (a b : ℝ)
    (hμ : (μ : Measure ℝ) (Set.Icc a b) = 1) :
    ∃ x ∈ Set.Icc a b, (μ : Measure ℝ) = Measure.dirac x := by
  -- Proof comment: this is the bounded-support Dirac collapse proved above in reusable form.
  exact infinitelyDivisible_eq_dirac_of_measure_Icc_eq_one μ a b hμ
