/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.ContinuousExpLift
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Lemma_16_24
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_5

open Filter MeasureTheory ProbabilityTheory MeasureTheory.ProbabilityMeasure
open scoped Topology MeasureTheory NNReal

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- Helper for Theorem 16.17: a Lévy--Khintchin representation never vanishes under the complex
exponential, so the represented characteristic function is zero-free. -/
private lemma charFun_ne_zero_of_hasLevyKhinchinRepresentation
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∀ t : ℝ, charFun (μ : Measure ℝ) t ≠ 0 := by
  intro t
  rw [hτ.charFun_eq_exp t]
  exact Complex.exp_ne_zero _

/-- Helper for Theorem 16.17: every Lévy--Khintchin exponent vanishes at the origin. -/
private lemma levyKhinchinExponent_zero (τ : LevyKhinchinTriple) :
    levyKhinchinExponent τ 0 = 0 := by
  -- Proof comment: the quadratic, linear, and jump terms all vanish at frequency `0`.
  simp [levyKhinchinExponent, levyKhinchinExponentWithCentering]

/-- Helper for Theorem 16.17: the local canonical jump kernel used to prove continuity of the
Lévy--Khintchin exponent. -/
private def levyKhinchinCanonicalKernelLocal (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
      (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)

/-- Helper for Theorem 16.17: the smooth sine-centered jump kernel used in the compact-average
reconstruction. -/
private def levyKhinchinSineKernelLocal (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
      (((t * Real.sin x : ℝ) : ℂ) * Complex.I)

/-- Helper for Theorem 16.17: the local canonical jump kernel is measurable. -/
private lemma measurable_levyKhinchinCanonicalKernelLocal (t : ℝ) :
    Measurable (levyKhinchinCanonicalKernelLocal t) := by
  -- Proof comment: measurability follows from the measurable exponential term and the measurable
  -- canonical centering correction.
  have hExp :
      Measurable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hCenter :
      Measurable
        (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) := by
    exact
      (Complex.measurable_ofReal.comp
        (measurable_const.mul measurable_levyKhinchinCanonicalCentering)).mul_const Complex.I
  exact (hExp.sub measurable_const).sub hCenter

/-- Helper for Theorem 16.17: the local canonical jump kernel is pointwise continuous in the
frequency variable. -/
private lemma continuous_levyKhinchinCanonicalKernelLocal (x : ℝ) :
    Continuous (fun t : ℝ ↦ levyKhinchinCanonicalKernelLocal t x) := by
  -- Proof comment: for fixed `x`, the kernel is an explicit combination of continuous scalar and
  -- exponential functions of `t`.
  continuity

/-- Helper for Theorem 16.17: inside the unit ball the canonical truncated second moment is just
`x²`. -/
private lemma sqMinOne_eq_sq_of_abs_lt_one_local {x : ℝ} (hx : |x| < 1) :
    min (x ^ (2 : ℕ)) 1 = x ^ (2 : ℕ) := by
  -- Proof comment: inside the unit ball the truncation `min (x^2) 1` does not cut anything off.
  refine min_eq_left ?_
  exact le_of_lt ((sq_lt_one_iff_abs_lt_one x).2 hx)

/-- Helper for Theorem 16.17: outside the unit ball the canonical truncated second moment is `1`.
-/
private lemma sqMinOne_eq_one_of_one_le_abs_local {x : ℝ} (hx : 1 ≤ |x|) :
    min (x ^ (2 : ℕ)) 1 = 1 := by
  -- Proof comment: once `|x| ≥ 1`, the truncation saturates at `1`.
  refine min_eq_right ?_
  have hxSq : 1 ≤ |x| * |x| := by
    nlinarith
  simpa [pow_two, sq_abs] using hxSq

/-- Helper for Theorem 16.17: the quadratic term `|t * x|²` factors as `|t|² x²`. -/
private lemma abs_mul_sq_local (t x : ℝ) :
    |t * x| ^ (2 : ℕ) = |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by
  -- Proof comment: take absolute values first, then expand the square of the product.
  rw [abs_mul, mul_pow, sq_abs, sq_abs]

/-- Helper for Theorem 16.17: when `|t * x| > 1`, the crude bound `2 + |t * x|` is still
controlled by `3 |t * x|²`. -/
private lemma two_add_abs_mul_le_three_abs_mul_sq_local {t x : ℝ} (hlarge : 1 < |t * x|) :
    2 + |t * x| ≤ 3 * |t * x| ^ (2 : ℕ) := by
  -- Proof comment: if `|t * x| > 1`, then both `2` and `|t * x|` are bounded by multiples of
  -- `|t * x|²`.
  nlinarith [le_of_lt hlarge, sq_nonneg (|t * x|)]

/-- Helper for Theorem 16.17: the oscillatory term `exp (i t x) - 1` is uniformly bounded by
`2`. -/
private lemma norm_exp_sub_one_mul_I_le_two_local (t x : ℝ) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 2 := by
  -- Proof comment: `exp (i y)` lies on the unit circle, so subtracting `1` has norm at most `2`.
  calc
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 1 + 1 := by
          rw [Complex.norm_exp_ofReal_mul_I]
          simp
    _ = 2 := by norm_num

/-- Helper for Theorem 16.17: the oscillatory remainder is bounded by `2 + |t * x|`. -/
private lemma norm_exp_sub_one_sub_id_mul_I_le_two_add_abs_mul_local (t x : ℝ) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
        (((t * x : ℝ) : ℂ) * Complex.I)‖ ≤
      2 + |t * x| := by
  -- Proof comment: use the triangle inequality and the basic bounds for `exp (i y) - 1` and
  -- `‖y I‖`.
  calc
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
        (((t * x : ℝ) : ℂ) * Complex.I)‖
        ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ +
            ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ := norm_sub_le _ _
    _ ≤ 2 + |t * x| := by
      gcongr
      · exact norm_exp_sub_one_mul_I_le_two_local t x
      · simp [Complex.norm_I, Real.norm_eq_abs]

/-- Helper for Theorem 16.17: the local canonical jump kernel satisfies the standard quadratic
domination bound. -/
private lemma norm_levyKhinchinCanonicalKernelLocal_le (t x : ℝ) :
    ‖levyKhinchinCanonicalKernelLocal t x‖ ≤
      max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
  by_cases hx : |x| < 1
  · by_cases htx : |t * x| ≤ 1
    · -- Proof comment: on the small-jump branch, the quadratic Taylor remainder bound controls
      -- the oscillatory kernel by `|t x|²`.
      let z : ℂ := (((t * x : ℝ) : ℂ) * Complex.I)
      have hquad :
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - (((t * x : ℝ) : ℂ) * Complex.I)‖ ≤
            |t * x| ^ (2 : ℕ) := by
        have hz : ‖z‖ ≤ 1 := by
          simpa [z, Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs] using htx
        simpa [z, Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs] using
          (Complex.norm_exp_sub_one_sub_id_le hz)
      calc
        ‖levyKhinchinCanonicalKernelLocal t x‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                (((t * x : ℝ) : ℂ) * Complex.I)‖ := by
                  simp [levyKhinchinCanonicalKernelLocal, levyKhinchinCanonicalCentering, hx]
        _ ≤ |t * x| ^ (2 : ℕ) := hquad
        _ = |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := abs_mul_sq_local t x
        _ ≤ 3 * |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by
              nlinarith [sq_nonneg (|t|), sq_nonneg x]
        _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 * x ^ (2 : ℕ) := by
              gcongr
              exact le_max_left _ _
        _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
              rw [sqMinOne_eq_sq_of_abs_lt_one_local hx]
    · -- Proof comment: once `|t x| > 1`, the coarse linear bound still yields quadratic control
      -- on the unit-ball branch.
      have hlarge : 1 < |t * x| := lt_of_not_ge htx
      calc
        ‖levyKhinchinCanonicalKernelLocal t x‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                (((t * x : ℝ) : ℂ) * Complex.I)‖ := by
                  simp [levyKhinchinCanonicalKernelLocal, levyKhinchinCanonicalCentering, hx]
        _ ≤ 2 + |t * x| := norm_exp_sub_one_sub_id_mul_I_le_two_add_abs_mul_local t x
        _ ≤ 3 * |t * x| ^ (2 : ℕ) := two_add_abs_mul_le_three_abs_mul_sq_local hlarge
        _ = 3 * (|t| ^ (2 : ℕ) * x ^ (2 : ℕ)) := by rw [abs_mul_sq_local]
        _ = 3 * |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by ring
        _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 * x ^ (2 : ℕ) := by
              gcongr
              exact le_max_left _ _
        _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
              rw [sqMinOne_eq_sq_of_abs_lt_one_local hx]
  · -- Proof comment: outside the unit ball, the linear correction vanishes and the uniform bound
    -- `2` is enough because `min (x², 1) = 1`.
    have hxLarge : 1 ≤ |x| := le_of_not_gt hx
    calc
      ‖levyKhinchinCanonicalKernelLocal t x‖
          = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ := by
              simp [levyKhinchinCanonicalKernelLocal, levyKhinchinCanonicalCentering, hx]
      _ ≤ 2 := norm_exp_sub_one_mul_I_le_two_local t x
      _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 := le_max_right _ _
      _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
            rw [sqMinOne_eq_one_of_one_le_abs_local hxLarge, mul_one]

/-- Helper for Theorem 16.17: the local canonical jump kernel is integrable against every
canonical Lévy measure. -/
private lemma integrable_levyKhinchinCanonicalKernelLocal {ν : Measure ℝ}
    (hν : IsCanonicalMeasure ν) (t : ℝ) :
    Integrable (levyKhinchinCanonicalKernelLocal t) ν := by
  have hbound :
      Integrable (fun x : ℝ ↦ max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1) ν := by
    -- Proof comment: the dominating function is a constant multiple of the canonical integrand.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hν.integrable_sq_min_one.const_mul (max (3 * |t| ^ (2 : ℕ)) 2)
  refine Integrable.mono' hbound
      (measurable_levyKhinchinCanonicalKernelLocal t).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦
    norm_levyKhinchinCanonicalKernelLocal_le t x

/-- Helper for Theorem 16.17: canonical Lévy--Khintchin exponents are continuous. -/
private lemma continuousLevyKhinchinExponentLocal
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) :
    Continuous (levyKhinchinExponent τ) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t₀
  let M : ℝ := max (3 * (|t₀| + 1) ^ (2 : ℕ)) 2
  have hτMeasure : IsCanonicalMeasure τ.ν := hτ.isCanonicalMeasure
  have hboundInt :
      Integrable (fun x : ℝ ↦ M * min (x ^ (2 : ℕ)) 1) τ.ν := by
    -- Proof comment: on a unit neighborhood of `t₀`, one fixed quadratic bound controls all
    -- nearby jump kernels.
    simpa [M, mul_comm, mul_left_comm, mul_assoc] using
      hτMeasure.integrable_sq_min_one.const_mul M
  have hkernel :
      ContinuousAt (fun t : ℝ ↦ ∫ x : ℝ, levyKhinchinCanonicalKernelLocal t x ∂τ.ν) t₀ := by
    have hmeas :
        ∀ᶠ t : ℝ in 𝓝 t₀,
          AEStronglyMeasurable (levyKhinchinCanonicalKernelLocal t) τ.ν := by
      exact Filter.Eventually.of_forall fun t ↦
        (measurable_levyKhinchinCanonicalKernelLocal t).aestronglyMeasurable
    have hbound :
        ∀ᶠ t : ℝ in 𝓝 t₀, ∀ᵐ x ∂τ.ν,
          ‖levyKhinchinCanonicalKernelLocal t x‖ ≤ M * min (x ^ (2 : ℕ)) 1 := by
      filter_upwards [Metric.ball_mem_nhds t₀ zero_lt_one] with t ht
      have ht_dist : |t - t₀| < 1 := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using ht
      have ht_abs : |t| ≤ |t₀| + 1 := by
        have htriangle : abs (|t| - |t₀|) ≤ |t - t₀| := abs_abs_sub_abs_le_abs_sub _ _
        rcases abs_le.mp htriangle with ⟨hneg, hpos⟩
        linarith
      have hM :
          max (3 * |t| ^ (2 : ℕ)) 2 ≤ M := by
        dsimp [M]
        have hsq : |t| ^ (2 : ℕ) ≤ (|t₀| + 1) ^ (2 : ℕ) := by
          nlinarith [ht_abs, abs_nonneg t, show 0 ≤ |t₀| + 1 by positivity]
        exact max_le_max (by gcongr) le_rfl
      filter_upwards with x
      exact (norm_levyKhinchinCanonicalKernelLocal_le t x).trans <|
        mul_le_mul_of_nonneg_right hM (by positivity)
    have hlim :
        ∀ᵐ x ∂τ.ν,
          Tendsto (fun t : ℝ ↦ levyKhinchinCanonicalKernelLocal t x) (𝓝 t₀)
            (𝓝 (levyKhinchinCanonicalKernelLocal t₀ x)) := by
      filter_upwards with x
      exact (continuous_levyKhinchinCanonicalKernelLocal x).continuousAt.tendsto
    have htendsto :
        Tendsto (fun t : ℝ ↦ ∫ x : ℝ, levyKhinchinCanonicalKernelLocal t x ∂τ.ν)
          (𝓝 t₀) (𝓝 (∫ x : ℝ, levyKhinchinCanonicalKernelLocal t₀ x ∂τ.ν)) := by
      exact
        tendsto_integral_filter_of_dominated_convergence
          (fun x ↦ M * min (x ^ (2 : ℕ)) 1) hmeas hbound hboundInt hlim
    simpa [ContinuousAt] using htendsto
  have hpoly :
      ContinuousAt
        (fun t : ℝ ↦
          (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * t : ℝ) : ℂ) * Complex.I)) t₀ := by
    -- Proof comment: the Gaussian and drift contributions are explicit polynomial functions of
    -- the frequency variable.
    have hQuad :
        Continuous
          (fun t : ℝ ↦ (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ))) := by
      continuity
    have hDrift :
        Continuous
          (fun t : ℝ ↦ (((τ.b * t : ℝ) : ℂ) * Complex.I)) := by
      continuity
    exact hQuad.continuousAt.add hDrift.continuousAt
  -- Proof comment: continuity of the full exponent is the sum of the explicit polynomial part and
  -- the dominated-convergence continuity of the jump integral.
  have hsum :
      ContinuousAt
        (fun t : ℝ ↦
          (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * t : ℝ) : ℂ) * Complex.I) +
            ∫ x : ℝ, levyKhinchinCanonicalKernelLocal t x ∂τ.ν) t₀ := by
    exact hpoly.add hkernel
  change ContinuousAt
      (fun t : ℝ ↦ levyKhinchinExponentWithCentering
        τ.sigma2 τ.b τ.ν levyKhinchinCanonicalCentering t) t₀
  convert hsum using 1

/-- Helper for Theorem 16.17: once continuity is supplied, two Lévy--Khintchin representations of
the same law have the same exponent. -/
private lemma levyKhinchinExponent_eq_of_sameRepresentation_of_continuous
    {μ : ProbabilityMeasure ℝ} {τ₁ τ₂ : LevyKhinchinTriple}
    (hτ₁ : HasLevyKhinchinRepresentation μ τ₁)
    (hτ₂ : HasLevyKhinchinRepresentation μ τ₂)
    (hcont₁ : Continuous (levyKhinchinExponent τ₁))
    (hcont₂ : Continuous (levyKhinchinExponent τ₂)) :
    ∀ t : ℝ, levyKhinchinExponent τ₁ t = levyKhinchinExponent τ₂ t := by
  let Ψ₁ : C(ℝ, ℂ) := ⟨levyKhinchinExponent τ₁, hcont₁⟩
  let Ψ₂ : C(ℝ, ℂ) := ⟨levyKhinchinExponent τ₂, hcont₂⟩
  obtain ⟨Ψ, hΨ, huniq⟩ :=
    existsUniqueContinuousExpLift
      (MeasureTheory.continuous_charFun : Continuous (charFun (μ : Measure ℝ)))
      (charFun_ne_zero_of_hasLevyKhinchinRepresentation hτ₁)
      (by simpa using (MeasureTheory.charFun_zero (μ := (μ : Measure ℝ))))
  have hΨ₁ :
      Ψ₁ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ₁ t) = charFun (μ : Measure ℝ) t := by
    constructor
    · -- Proof comment: the first exponent uses the standard normalization at `0`.
      simpa [Ψ₁] using levyKhinchinExponent_zero τ₁
    · intro t
      -- Proof comment: the first representation identifies `charFun μ` with `exp ∘ Ψ₁`.
      simpa [Ψ₁] using (hτ₁.charFun_eq_exp t).symm
  have hΨ₂ :
      Ψ₂ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ₂ t) = charFun (μ : Measure ℝ) t := by
    constructor
    · -- Proof comment: the second exponent uses the same normalization at `0`.
      simpa [Ψ₂] using levyKhinchinExponent_zero τ₂
    · intro t
      -- Proof comment: the second representation produces the same characteristic function.
      simpa [Ψ₂] using (hτ₂.charFun_eq_exp t).symm
  have hEq₁ : Ψ₁ = Ψ := huniq Ψ₁ hΨ₁
  have hEq₂ : Ψ₂ = Ψ := huniq Ψ₂ hΨ₂
  intro t
  -- Proof comment: evaluate the common continuous lift at frequency `t`.
  exact congrArg (fun f : C(ℝ, ℂ) ↦ f t) (hEq₁.trans hEq₂.symm)

/-- Helper for Theorem 16.17: the theorem-local canonical jump kernel used in the Gaussian
recovery argument. -/
private def levyKhinchinCanonicalKernel (t : ℝ) : ℝ → ℂ :=
  levyKhinchinCanonicalKernelLocal t

/-- Helper for Theorem 16.17: the theorem-local canonical jump kernel is measurable. -/
private lemma measurable_levyKhinchinCanonicalKernel (t : ℝ) :
    Measurable (levyKhinchinCanonicalKernel t) := by
  simpa [levyKhinchinCanonicalKernel] using
    measurable_levyKhinchinCanonicalKernelLocal t

/-- Helper for Theorem 16.17: the theorem-local canonical jump kernel satisfies the standard
quadratic domination bound. -/
private lemma norm_levyKhinchinCanonicalKernel_bound (t x : ℝ) :
    ‖levyKhinchinCanonicalKernel t x‖ ≤
      max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
  simpa [levyKhinchinCanonicalKernel] using
    norm_levyKhinchinCanonicalKernelLocal_le t x

/-- Helper for Theorem 16.17: the theorem-local canonical jump kernel is integrable against every
canonical Lévy measure. -/
private lemma integrable_levyKhinchinCanonicalKernel_local {ν : Measure ℝ}
    (hν : IsCanonicalMeasure ν) (t : ℝ) :
    Integrable (levyKhinchinCanonicalKernel t) ν := by
  simpa [levyKhinchinCanonicalKernel] using
    integrable_levyKhinchinCanonicalKernelLocal hν t

/-- Helper for Theorem 16.17: the Gaussian recovery kernel. -/
private def gaussianRecoveryKernel (x : ℝ) : ℝ :=
  1 - Real.exp (-(x ^ (2 : ℕ) / 2))

/-- Helper for Theorem 16.17: the Gaussian recovery kernel is measurable. -/
private lemma measurable_gaussianRecoveryKernel :
    Measurable gaussianRecoveryKernel := by
  -- Proof comment: the Gaussian recovery kernel is built from measurable polynomial and
  -- exponential pieces.
  have hArg : Measurable (fun x : ℝ ↦ -(x ^ (2 : ℕ) / 2 : ℝ)) := by
    fun_prop
  simpa [gaussianRecoveryKernel] using
    measurable_const.sub (Real.measurable_exp.comp hArg)

/-- Helper for Theorem 16.17: the Gaussian recovery kernel vanishes at the origin. -/
private lemma gaussianRecoveryKernel_zero :
    gaussianRecoveryKernel 0 = 0 := by
  -- Proof comment: at the origin, the Gaussian damping factor is `exp 0 = 1`.
  simp [gaussianRecoveryKernel]

/-- Helper for Theorem 16.17: the Gaussian recovery kernel is nonnegative. -/
private lemma gaussianRecoveryKernel_nonneg (x : ℝ) :
    0 ≤ gaussianRecoveryKernel x := by
  -- Proof comment: the exponential term lies in `(0, 1]`, so subtracting it from `1` is
  -- nonnegative.
  refine sub_nonneg.mpr ?_
  refine Real.exp_le_one_iff.mpr ?_
  have hsq_nonneg : 0 ≤ x ^ (2 : ℕ) / 2 := by positivity
  linarith

/-- Helper for Theorem 16.17: the Gaussian recovery kernel is bounded above by `1`. -/
private lemma gaussianRecoveryKernel_le_one (x : ℝ) :
    gaussianRecoveryKernel x ≤ 1 := by
  -- Proof comment: the exponential term is nonnegative, so removing it cannot exceed `1`.
  dsimp [gaussianRecoveryKernel]
  have hExp : 0 ≤ Real.exp (-(x ^ (2 : ℕ) / 2)) := (Real.exp_pos _).le
  linarith

/-- Helper for Theorem 16.17: the Gaussian recovery kernel is controlled by `x²`. -/
private lemma gaussianRecoveryKernel_le_sq (x : ℝ) :
    gaussianRecoveryKernel x ≤ x ^ (2 : ℕ) := by
  -- Proof comment: the elementary inequality `1 - y ≤ exp (-y)` gives the quadratic bound.
  have hStep : gaussianRecoveryKernel x ≤ x ^ (2 : ℕ) / 2 := by
    have hExp : 1 - (x ^ (2 : ℕ) / 2) ≤ Real.exp (-(x ^ (2 : ℕ) / 2)) := by
      simpa using Real.one_sub_le_exp_neg (x ^ (2 : ℕ) / 2)
    dsimp [gaussianRecoveryKernel]
    linarith
  have hHalf_le : x ^ (2 : ℕ) / 2 ≤ x ^ (2 : ℕ) := by
    nlinarith [sq_nonneg x]
  exact le_trans hStep hHalf_le

/-- Helper for Theorem 16.17: the Gaussian recovery kernel is dominated by the canonical
integrand `x ↦ min (x², 1)`. -/
private lemma gaussianRecoveryKernel_le_sqMinOne (x : ℝ) :
    gaussianRecoveryKernel x ≤ min (x ^ (2 : ℕ)) 1 := by
  -- Proof comment: the kernel is simultaneously bounded by `x²` and by `1`.
  exact le_min (gaussianRecoveryKernel_le_sq x) (gaussianRecoveryKernel_le_one x)

/-- Helper for Theorem 16.17: the Gaussian recovery kernel is strictly positive away from `0`. -/
private lemma gaussianRecoveryKernel_ne_zero {x : ℝ} (hx : x ≠ 0) :
    gaussianRecoveryKernel x ≠ 0 := by
  -- Proof comment: `exp y = 1` forces `y = 0`, so the kernel only vanishes at the origin.
  intro hKernel
  have hExp : Real.exp (-(x ^ (2 : ℕ) / 2)) = 1 := by
    dsimp [gaussianRecoveryKernel] at hKernel
    linarith
  have hArg : -(x ^ (2 : ℕ) / 2) = 0 := (Real.exp_eq_one_iff _).mp hExp
  have hSq : x ^ (2 : ℕ) = 0 := by
    nlinarith
  exact hx (eq_zero_of_pow_eq_zero hSq)

/-- Helper for Theorem 16.17: every canonical Lévy measure integrates the Gaussian recovery
kernel. -/
private lemma integrable_gaussianRecoveryKernel {ν : Measure ℝ}
    (hν : IsCanonicalMeasure ν) :
    Integrable gaussianRecoveryKernel ν := by
  -- Proof comment: the Gaussian recovery kernel is dominated by the canonical integrand
  -- `min (x², 1)`.
  refine hν.integrable_sq_min_one.mono' measurable_gaussianRecoveryKernel.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    have hnonneg : 0 ≤ gaussianRecoveryKernel x := gaussianRecoveryKernel_nonneg x
    rw [Real.norm_of_nonneg hnonneg]
    exact gaussianRecoveryKernel_le_sqMinOne x

/-- Helper for Theorem 16.17: the Gaussian-smoothed auxiliary measure is finite. -/
private theorem gaussianRecoveryAuxFiniteMeasure_isFinite
    (α : NNReal) (ν : Measure ℝ)
    (h_int : Integrable gaussianRecoveryKernel ν) :
    IsFiniteMeasure
      ((α : ENNReal) • Measure.dirac 0 +
        ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) := by
  -- Proof comment: both the Dirac atom and the Gaussian-damped Lévy part are finite.
  have hDirac :
      IsFiniteMeasure (((α : ENNReal) • Measure.dirac (0 : ℝ) : Measure ℝ)) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, Measure.dirac_apply_of_mem (by simp)]
    simp [smul_eq_mul]
  have hTilt :
      IsFiniteMeasure
        (ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) := by
    simpa using
      (MeasureTheory.isFiniteMeasure_withDensity_ofReal (μ := ν) h_int.hasFiniteIntegral)
  letI : IsFiniteMeasure (((α : ENNReal) • Measure.dirac (0 : ℝ) : Measure ℝ)) := hDirac
  letI :
      IsFiniteMeasure
        (ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) := hTilt
  simpa using
    (inferInstance :
      IsFiniteMeasure
        ((((α : ENNReal) • Measure.dirac (0 : ℝ) : Measure ℝ) +
          ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x)))))

/-- Helper for Theorem 16.17: the Gaussian-smoothed auxiliary finite measure
`α δ₀ + (1 - exp (-(x² / 2))) ν(dx)`. -/
private noncomputable def gaussianRecoveryAuxFiniteMeasure
    (α : NNReal) (ν : Measure ℝ) (h_int : Integrable gaussianRecoveryKernel ν) :
    FiniteMeasure ℝ :=
  ⟨(α : ENNReal) • Measure.dirac 0 +
      ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x)),
    gaussianRecoveryAuxFiniteMeasure_isFinite α ν h_int⟩

/-- Helper for Theorem 16.17: the Gaussian-damped Lévy part contributes no atom at `0`. -/
private lemma gaussianRecoveryAuxFiniteMeasure_apply_zero
    (α : NNReal) {ν : Measure ℝ}
    (h_int : Integrable gaussianRecoveryKernel ν) :
    (((gaussianRecoveryAuxFiniteMeasure α ν h_int : FiniteMeasure ℝ) : Measure ℝ) {0}) = α := by
  -- Proof comment: the Gaussian recovery kernel vanishes at `0`, so only the Dirac atom remains.
  have hTiltZero :
      (ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) {0} = 0 := by
    rw [withDensity_apply _ (measurableSet_singleton 0)]
    simp [gaussianRecoveryKernel_zero]
  change ((((α : ENNReal) • Measure.dirac (0 : ℝ) : Measure ℝ) +
      ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) {0}) = α
  rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (by simp), hTiltZero,
    add_zero]
  simp [smul_eq_mul]

/-- Helper for Theorem 16.17: the Gaussian recovery kernel is almost everywhere nonzero under a
measure with no atom at `0`. -/
private lemma gaussianRecoveryKernel_ae_ne_zero
    {ν : Measure ℝ} (hν0 : ν ({0} : Set ℝ) = 0) :
    ∀ᵐ x ∂ν, gaussianRecoveryKernel x ≠ 0 := by
  -- Proof comment: the Gaussian recovery kernel only vanishes at the origin.
  have hzero : ∀ᵐ x ∂ν, x ≠ 0 := by
    simp [ae_iff, hν0]
  filter_upwards [hzero] with x hx
  exact gaussianRecoveryKernel_ne_zero hx

/-- Helper for Theorem 16.17: the ENNReal Gaussian recovery density is finite everywhere. -/
private lemma gaussianRecoveryKernel_ae_ne_top {ν : Measure ℝ} :
    ∀ᵐ x ∂ν, (ENNReal.ofReal (gaussianRecoveryKernel x)) ≠ ⊤ := by
  -- Proof comment: `ENNReal.ofReal` is finite on every real input.
  filter_upwards with x
  simp

/-- Helper for Theorem 16.17: on the punctured restriction `η.restrict ({0}ᶜ)`, the Gaussian
recovery kernel never vanishes. -/
private lemma gaussianRecoveryKernel_ae_ne_zero_restrict_compl_singleton
    (η : Measure ℝ) :
    ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), gaussianRecoveryKernel x ≠ 0 := by
  rw [ae_restrict_iff' ((measurableSet_singleton (0 : ℝ)).compl)]
  filter_upwards with x hx
  -- Proof comment: removing the origin removes the only zero of the Gaussian recovery kernel.
  exact gaussianRecoveryKernel_ne_zero (by simpa using hx)

/-- Helper for Theorem 16.17: the pure oscillatory Fourier kernel is integrable against every
finite measure. -/
private lemma integrable_fourierKernel_of_isFiniteMeasure
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) ν := by
  -- Proof comment: the oscillatory factor has norm `1`, so finiteness of the measure gives
  -- integrability immediately.
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    simpa [mul_assoc] using (le_of_eq (Complex.norm_exp_ofReal_mul_I (t * x)))

/-- Helper for Theorem 16.17: inverting the Gaussian recovery density on the punctured restriction
recovers the original punctured measure. -/
private lemma withDensity_gaussianRecoveryKernel_inv_same_restrict_compl_singleton
    (η : Measure ℝ) :
    (((η.restrict ({0}ᶜ : Set ℝ)).withDensity
        (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).withDensity
      (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹)) =
      η.restrict ({0}ᶜ : Set ℝ) := by
  let f : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x)
  have hf_meas : Measurable f := measurable_gaussianRecoveryKernel.ennreal_ofReal
  have hf_ne_zero :
      ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), f x ≠ 0 :=
    by
      filter_upwards [gaussianRecoveryKernel_ae_ne_zero_restrict_compl_singleton η] with x hx
      have hpos : 0 < gaussianRecoveryKernel x :=
        lt_of_le_of_ne (gaussianRecoveryKernel_nonneg x) (by simpa [eq_comm] using hx)
      simpa [f, ENNReal.ofReal_eq_zero, not_le_of_gt hpos]
  have hf_ne_top :
      ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), f x ≠ (⊤ : ENNReal) :=
    by
      simpa [f] using
        gaussianRecoveryKernel_ae_ne_top (ν := η.restrict ({0}ᶜ : Set ℝ))
  -- Proof comment: the Gaussian auxiliary measure is built by weighting the punctured jump measure
  -- with this density, so a second `withDensity` by its inverse removes the tilt.
  simpa [f] using MeasureTheory.withDensity_inv_same hf_meas hf_ne_zero hf_ne_top

/-- Helper for Theorem 16.17: recover the punctured jump measure of a Gaussian auxiliary finite
measure by inverting the Gaussian recovery density away from `0`. -/
private noncomputable def gaussianRecoveredJumpMeasure_local (η : FiniteMeasure ℝ) : Measure ℝ :=
  (((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)).withDensity
    (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹))

/-- Helper for Theorem 16.17: restricting the Gaussian auxiliary finite measure away from `0`
removes the Dirac atom and leaves only the tilted jump part. -/
private lemma gaussianRecoveryAuxFiniteMeasure_restrict_compl_singleton_local
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) :
    let α : NNReal := ⟨τ.sigma2 / 2, by
      exact div_nonneg hτ.sigma2_nonneg (by positivity)⟩
    (((gaussianRecoveryAuxFiniteMeasure α τ.ν
        (integrable_gaussianRecoveryKernel hτ.isCanonicalMeasure) : FiniteMeasure ℝ) :
          Measure ℝ).restrict ({0}ᶜ : Set ℝ)) =
      (τ.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
        (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x)) := by
  let α : NNReal := ⟨τ.sigma2 / 2, by
    exact div_nonneg hτ.sigma2_nonneg (by positivity)⟩
  -- Proof comment: the auxiliary measure is `α δ₀` plus the tilted jump measure, so puncturing
  -- the origin deletes only the Dirac contribution.
  change
    ((((α : ENNReal) • Measure.dirac (0 : ℝ) +
        τ.ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).restrict
        ({0}ᶜ : Set ℝ))) =
      (τ.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
        (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))
  rw [Measure.restrict_add, Measure.restrict_smul,
    restrict_dirac' ((measurableSet_singleton (0 : ℝ)).compl), if_neg (by simp), smul_zero,
    zero_add, MeasureTheory.restrict_withDensity ((measurableSet_singleton (0 : ℝ)).compl)]

/-- Helper for Theorem 16.17: recovering the jump measure from the Gaussian auxiliary package
returns the original Lévy measure. -/
private lemma gaussianRecoveredJumpMeasure_aux_eq_local
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) :
    let α : NNReal := ⟨τ.sigma2 / 2, by
      exact div_nonneg hτ.sigma2_nonneg (by positivity)⟩
    gaussianRecoveredJumpMeasure_local
        (gaussianRecoveryAuxFiniteMeasure α τ.ν
          (integrable_gaussianRecoveryKernel hτ.isCanonicalMeasure)) =
      τ.ν := by
  let α : NNReal := ⟨τ.sigma2 / 2, by
    exact div_nonneg hτ.sigma2_nonneg (by positivity)⟩
  -- Proof comment: first identify the punctured auxiliary measure with the tilted jump measure,
  -- then cancel the density and finally add back the zero atom, which vanishes canonically.
  calc
    gaussianRecoveredJumpMeasure_local
        (gaussianRecoveryAuxFiniteMeasure α τ.ν
          (integrable_gaussianRecoveryKernel hτ.isCanonicalMeasure))
        =
      (((τ.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
          (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).withDensity
        (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹)) := by
          rw [gaussianRecoveredJumpMeasure_local,
            gaussianRecoveryAuxFiniteMeasure_restrict_compl_singleton_local hτ]
    _ = τ.ν.restrict ({0}ᶜ : Set ℝ) := by
          exact withDensity_gaussianRecoveryKernel_inv_same_restrict_compl_singleton τ.ν
    _ = τ.ν.restrict ({0} : Set ℝ) + τ.ν.restrict ({0}ᶜ : Set ℝ) := by
          rw [Measure.restrict_singleton, hτ.isCanonicalMeasure.measure_singleton_zero, zero_smul,
            zero_add]
    _ = τ.ν := by
          simpa using
            (Measure.restrict_add_restrict_compl (μ := τ.ν) (measurableSet_singleton (0 : ℝ)))

/-- Helper for Theorem 16.17: the Gaussian-smoothed auxiliary finite measure has characteristic
function `α + ∫ e^{itx} gaussianRecoveryKernel(x) ν(dx)`. -/
private lemma gaussianRecoveryAuxFiniteMeasure_charFun
    (α : NNReal) {ν : Measure ℝ}
    (h_int : Integrable gaussianRecoveryKernel ν) (t : ℝ) :
    charFun (((gaussianRecoveryAuxFiniteMeasure α ν h_int : FiniteMeasure ℝ) : Measure ℝ)) t =
      (α : ℂ) +
        ∫ x : ℝ,
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂ν := by
  let μdirac : Measure ℝ := ((α : ENNReal) • Measure.dirac 0 : Measure ℝ)
  let μtilt : Measure ℝ :=
    ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))
  have hDiracFinite : IsFiniteMeasure μdirac := by
    refine ⟨?_⟩
    change (((α : ENNReal) • Measure.dirac (0 : ℝ)) Set.univ) < ⊤
    rw [Measure.smul_apply, Measure.dirac_apply_of_mem (by simp)]
    simp [smul_eq_mul]
  have hTiltFinite : IsFiniteMeasure μtilt := by
    dsimp [μtilt]
    simpa using
      (MeasureTheory.isFiniteMeasure_withDensity_ofReal (μ := ν) h_int.hasFiniteIntegral)
  letI : IsFiniteMeasure μdirac := hDiracFinite
  letI : IsFiniteMeasure μtilt := hTiltFinite
  have hDiracInt :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) μdirac :=
    integrable_fourierKernel_of_isFiniteMeasure μdirac t
  have hTiltInt :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) μtilt :=
    integrable_fourierKernel_of_isFiniteMeasure μtilt t
  have hDirac :
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μdirac = α := by
    change
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂((α : ENNReal) • Measure.dirac 0) =
        α
    rw [integral_smul_measure, integral_dirac]
    have hsmul :
        ((α : ℝ) • Complex.exp ((((t * (0 : ℝ) : ℝ) : ℂ) * Complex.I))) = (α : ℂ) := by
      simp
    exact hsmul
  have hTilt :
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μtilt =
        ∫ x : ℝ,
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂ν := by
    dsimp [μtilt]
    rw [integral_withDensity_eq_integral_toReal_smul measurable_gaussianRecoveryKernel.ennreal_ofReal
      (by
        filter_upwards [gaussianRecoveryKernel_ae_ne_top (ν := ν)] with x hx
        exact lt_of_le_of_ne le_top hx)]
    refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
    have hnonneg : 0 ≤ gaussianRecoveryKernel x := gaussianRecoveryKernel_nonneg x
    calc
      (ENNReal.ofReal (gaussianRecoveryKernel x)).toReal •
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
          = ((gaussianRecoveryKernel x : ℂ)) *
              Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
                simp [hnonneg, smul_eq_mul]
      _ = Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * ((gaussianRecoveryKernel x : ℂ)) := by
            ring
      _ = Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x := by
            simp
  -- Proof comment: split the auxiliary measure into the Dirac atom at `0` and the weighted jump
  -- part, then rewrite both integrals explicitly.
  rw [charFun_apply_real]
  calc
    ∫ x : ℝ,
        Complex.exp (((t : ℂ) * x) * Complex.I) ∂
          ((gaussianRecoveryAuxFiniteMeasure α ν h_int : FiniteMeasure ℝ) : Measure ℝ) =
        ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μdirac +
          ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μtilt := by
            rw [gaussianRecoveryAuxFiniteMeasure]
            simpa [μdirac, μtilt, mul_assoc] using integral_add_measure hDiracInt hTiltInt
    _ = (α : ℂ) +
          ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂ν := by
            rw [hDirac, hTilt]

/-- Helper for Theorem 16.17: the identity map is complex-integrable under the standard Gaussian
law. -/
private lemma integrable_complexId_gaussianReal_zero_one :
    Integrable (fun s : ℝ ↦ (s : ℂ)) (gaussianReal 0 1) := by
  have hmem : MemLp id 2 (gaussianReal 0 1) := by
    -- Proof comment: the standard Gaussian has finite second moment, so the identity belongs to
    -- `L²`.
    simpa using
      (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2 (by simp))
  have hint : Integrable (fun s : ℝ ↦ s) (gaussianReal 0 1) := by
    -- Proof comment: on the probability measure `gaussianReal 0 1`, `L²` control implies `L¹`
    -- integrability.
    exact hmem.integrable (by norm_num)
  -- Proof comment: complexification preserves integrability of the real-valued identity map.
  simpa using hint.ofReal

/-- Helper for Theorem 16.17: the centered standard Gaussian has vanishing complex first
moment. -/
private lemma integral_complexId_gaussianReal_zero_one :
    ∫ s : ℝ, (s : ℂ) ∂gaussianReal 0 1 = 0 := by
  -- Proof comment: convert the complex integral to the real one and use the centered Gaussian
  -- mean formula.
  rw [integral_complex_ofReal]
  rw [ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))]
  simp

/-- Helper for Theorem 16.17: the standard Gaussian has second moment `1`. -/
private lemma integral_sq_gaussianReal_zero_one :
    ∫ s : ℝ, s ^ (2 : ℕ) ∂gaussianReal 0 1 = 1 := by
  have hmem : MemLp id 2 (gaussianReal 0 1) := by
    -- Proof comment: use the standard Gaussian `L²` package to access the variance identity.
    simpa using
      (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2 (by simp))
  have hvariance :
      Var[id; gaussianReal 0 1] =
        ∫ s : ℝ, s ^ (2 : ℕ) ∂gaussianReal 0 1 - (∫ s : ℝ, s ∂gaussianReal 0 1) ^ (2 : ℕ) := by
    -- Proof comment: rewrite the Gaussian variance into second moment minus squared mean.
    simpa using (variance_eq_sub (μ := gaussianReal 0 1) (X := id) hmem)
  -- Proof comment: the standard Gaussian has variance `1` and mean `0`.
  rw [ProbabilityTheory.variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))] at hvariance
  simpa [ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))] using
    hvariance.symm

/-- Helper for Theorem 16.17: the real identity map is integrable under the standard Gaussian. -/
private lemma integrable_id_gaussianReal_zero_one :
    Integrable (fun s : ℝ ↦ s) (gaussianReal 0 1) := by
  have hmem : MemLp id 2 (gaussianReal 0 1) := by
    -- Proof comment: the standard Gaussian identity map lies in `L²`.
    simpa using
      (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2 (by simp))
  -- Proof comment: on a probability space, `L²` membership implies Bochner integrability.
  exact hmem.integrable (by norm_num)

/-- Helper for Theorem 16.17: the square function is integrable under the standard Gaussian. -/
private lemma integrable_sq_gaussianReal_zero_one :
    Integrable (fun s : ℝ ↦ s ^ (2 : ℕ)) (gaussianReal 0 1) := by
  have hmem : MemLp id 2 (gaussianReal 0 1) := by
    -- Proof comment: the standard Gaussian identity map lies in `L²`.
    simpa using
      (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2 (by simp))
  -- Proof comment: `L²` membership of the identity is exactly integrability of the square.
  simpa using hmem.integrable_sq

/-- Helper for Theorem 16.17: the shifted square remains integrable under the standard Gaussian. -/
private lemma integrable_shiftedSq_gaussianReal_zero_one (t : ℝ) :
    Integrable (fun s : ℝ ↦ (t + s) ^ (2 : ℕ)) (gaussianReal 0 1) := by
  have hpoly :
      Integrable (fun s : ℝ ↦ t ^ (2 : ℕ) + (2 * t) * s + s ^ (2 : ℕ)) (gaussianReal 0 1) := by
    -- Proof comment: expand the shifted square into constant, linear, and quadratic pieces.
    have hConst : Integrable (fun _ : ℝ ↦ t ^ (2 : ℕ)) (gaussianReal 0 1) := integrable_const _
    have hLinear : Integrable (fun s : ℝ ↦ (2 * t) * s) (gaussianReal 0 1) :=
      integrable_id_gaussianReal_zero_one.const_mul (2 * t)
    simpa [add_assoc] using (hConst.add hLinear).add integrable_sq_gaussianReal_zero_one
  -- Proof comment: rewrite `(t + s)²` into the polynomial normal form above.
  refine hpoly.congr ?_
  filter_upwards with s
  ring

/-- Helper for Theorem 16.17: the shifted square has Gaussian expectation `t² + 1`. -/
private lemma integral_shiftedSq_gaussianReal_zero_one (t : ℝ) :
    ∫ s : ℝ, (t + s) ^ (2 : ℕ) ∂gaussianReal 0 1 = t ^ (2 : ℕ) + 1 := by
  have hlin :
      Integrable (fun s : ℝ ↦ t ^ (2 : ℕ) + (2 * t) * s) (gaussianReal 0 1) := by
    -- Proof comment: the linearized part of the shifted square is integrable by previous lemmas.
    exact (integrable_const (t ^ (2 : ℕ))).add
      (integrable_id_gaussianReal_zero_one.const_mul (2 * t))
  calc
    ∫ s : ℝ, (t + s) ^ (2 : ℕ) ∂gaussianReal 0 1
        = ∫ s : ℝ, (t ^ (2 : ℕ) + (2 * t) * s + s ^ (2 : ℕ)) ∂gaussianReal 0 1 := by
            refine integral_congr_ae ?_
            filter_upwards with s
            ring
    _ =
        ∫ s : ℝ, (t ^ (2 : ℕ) + (2 * t) * s) ∂gaussianReal 0 1 +
          ∫ s : ℝ, s ^ (2 : ℕ) ∂gaussianReal 0 1 := by
            rw [integral_add hlin integrable_sq_gaussianReal_zero_one]
    _ =
        (∫ s : ℝ, (t ^ (2 : ℕ) : ℝ) ∂gaussianReal 0 1 +
            ∫ s : ℝ, (2 * t) * s ∂gaussianReal 0 1) +
          ∫ s : ℝ, s ^ (2 : ℕ) ∂gaussianReal 0 1 := by
            rw [integral_add (integrable_const (t ^ (2 : ℕ)))
              (integrable_id_gaussianReal_zero_one.const_mul (2 * t))]
    _ = t ^ (2 : ℕ) + (2 * t) * ∫ s : ℝ, s ∂gaussianReal 0 1 + 1 := by
          rw [integral_const, integral_const_mul, integral_sq_gaussianReal_zero_one]
          simp
    _ = t ^ (2 : ℕ) + 1 := by
          rw [ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))]
          ring

/-- Helper for Theorem 16.17: the shifted canonical-kernel weight is controlled by one
Gaussian-integrable quadratic factor. -/
private lemma max_shiftedKernelWeight_le_separableQuadratic (t s : ℝ) :
    max (3 * |t + s| ^ (2 : ℕ)) 2 ≤
      (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1) := by
  have hquad :
      3 * |t + s| ^ (2 : ℕ) ≤ (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1) := by
    have hsq :
        |t + s| ^ (2 : ℕ) ≤ 2 * (|t| ^ (2 : ℕ) + s ^ (2 : ℕ)) := by
      calc
        |t + s| ^ (2 : ℕ) ≤ (|t| + |s|) ^ (2 : ℕ) := by
          gcongr
          exact abs_add_le _ _
        _ ≤ 2 * (|t| ^ (2 : ℕ) + |s| ^ (2 : ℕ)) := by
          nlinarith [sq_nonneg (|t| - |s|)]
        _ = 2 * (|t| ^ (2 : ℕ) + s ^ (2 : ℕ)) := by
          simp [sq_abs]
    have hprod :
        |t| ^ (2 : ℕ) + s ^ (2 : ℕ) ≤ (|t| ^ (2 : ℕ) + 1) * (s ^ (2 : ℕ) + 1) := by
      nlinarith
    calc
      3 * |t + s| ^ (2 : ℕ) ≤ 3 * (2 * (|t| ^ (2 : ℕ) + s ^ (2 : ℕ))) := by
        gcongr
      _ = 6 * (|t| ^ (2 : ℕ) + s ^ (2 : ℕ)) := by ring
      _ ≤ 6 * ((|t| ^ (2 : ℕ) + 1) * (s ^ (2 : ℕ) + 1)) := by
        gcongr
      _ = (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1) := by ring
  have hconst :
      2 ≤ (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1) := by
    calc
      2 ≤ 6 := by norm_num
      _ ≤ 6 * (s ^ (2 : ℕ) + 1) := by nlinarith
      _ ≤ (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1) := by
        nlinarith [sq_nonneg t, sq_nonneg s]
  exact max_le_iff.2 ⟨hquad, hconst⟩

/-- Helper for Theorem 16.17: the Gaussian-shifted canonical jump kernel is integrable on the
product space needed for Fubini. -/
private lemma integrable_shiftedCanonicalKernel_prod
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) (t : ℝ) :
    Integrable
      (fun z : ℝ × ℝ ↦ levyKhinchinCanonicalKernel (t + z.1) z.2)
      (((gaussianReal 0 1) : Measure ℝ).prod τ.ν) := by
  have hWeight :
      Integrable
        (fun s : ℝ ↦ (6 * |t| ^ (2 : ℕ) + 6) * (s ^ (2 : ℕ) + 1))
        (gaussianReal 0 1) := by
    -- Proof comment: the separable quadratic weight is a constant multiple of a second-moment
    -- integrand for the standard Gaussian.
    exact
      ((integrable_sq_gaussianReal_zero_one.add (integrable_const (1 : ℝ)))).const_mul
        (6 * |t| ^ (2 : ℕ) + 6)
  have hDom :
      Integrable
        (fun z : ℝ × ℝ ↦
          ((6 * |t| ^ (2 : ℕ) + 6) * (z.1 ^ (2 : ℕ) + 1)) * min (z.2 ^ (2 : ℕ)) 1)
        (((gaussianReal 0 1) : Measure ℝ).prod τ.ν) := by
    -- Proof comment: the product dominating function separates into the Gaussian and canonical
    -- factors, so Fubini applies directly.
    exact hWeight.smul_prod hτ.isCanonicalMeasure.integrable_sq_min_one
  have hMeas :
      Measurable (fun z : ℝ × ℝ ↦ levyKhinchinCanonicalKernel (t + z.1) z.2) := by
    -- Proof comment: the shifted kernel is measurable because both coordinate maps are.
    have hExp :
        Measurable
          (fun z : ℝ × ℝ ↦
            Complex.exp ((((t + z.1) * z.2 : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    have hCenter :
        Measurable
          (fun z : ℝ × ℝ ↦
            ((((t + z.1) * levyKhinchinCanonicalCentering z.2 : ℝ) : ℂ) * Complex.I)) := by
      exact
        (Complex.measurable_ofReal.comp
          ((measurable_const.add measurable_fst).mul
            (measurable_levyKhinchinCanonicalCentering.comp measurable_snd))).mul_const Complex.I
    simpa [levyKhinchinCanonicalKernel, levyKhinchinCanonicalKernelLocal] using
      (hExp.sub measurable_const).sub hCenter
  refine Integrable.mono' hDom hMeas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun z ↦ by
    -- Proof comment: the pointwise kernel bound reduces to the separable quadratic estimate.
    exact
      (norm_levyKhinchinCanonicalKernel_bound (t + z.1) z.2).trans <|
        mul_le_mul_of_nonneg_right
          (max_shiftedKernelWeight_le_separableQuadratic t z.1) (by positivity)

/-- Helper for Theorem 16.17: averaging the centered jump kernel against the standard Gaussian
replaces the oscillatory factor by the Gaussian damping factor and kills the linear correction. -/
private lemma integral_gaussianRecovery_shiftedCanonicalKernel
    (t x : ℝ) :
    ∫ s : ℝ, levyKhinchinCanonicalKernel (t + s) x ∂gaussianReal 0 1 =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) -
        1 - (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) := by
  let c : ℝ := levyKhinchinCanonicalCentering x
  have hOscInt :
      Integrable
        (fun s : ℝ ↦ Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I))
        (gaussianReal 0 1) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun s ↦ by
      simpa using (le_of_eq (Complex.norm_exp_ofReal_mul_I ((t + s) * x)))
  have hLinearInt :
      Integrable
        (fun s : ℝ ↦ ((((t + s) * c : ℝ) : ℂ) * Complex.I))
        (gaussianReal 0 1) := by
    have hConst :
        Integrable (fun _ : ℝ ↦ (((t * c : ℝ) : ℂ) * Complex.I)) (gaussianReal 0 1) :=
      integrable_const _
    have hId :
        Integrable (fun s : ℝ ↦ (s : ℂ) * (((c : ℂ)) * Complex.I)) (gaussianReal 0 1) :=
      integrable_complexId_gaussianReal_zero_one.mul_const (((c : ℂ)) * Complex.I)
    refine (hConst.add hId).congr ?_
    filter_upwards with s
    simp [c]
    ring
  have hOscAvg :
      ∫ s : ℝ, Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) := by
    have hBase :
        Integrable
          (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I))
          (gaussianReal 0 1) := by
      refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
      exact Filter.Eventually.of_forall fun s ↦ by
        simpa using (le_of_eq (Complex.norm_exp_ofReal_mul_I (s * x)))
    calc
      ∫ s : ℝ, Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
          ∫ s : ℝ,
            Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 := by
                refine integral_congr_ae <| Filter.Eventually.of_forall fun s ↦ ?_
                have hsplit :
                    ((((t + s) * x : ℝ) : ℂ) * Complex.I) =
                      ((((t * x : ℝ) : ℂ) + (((s * x : ℝ) : ℂ))) * Complex.I) := by
                  calc
                    ((((t + s) * x : ℝ) : ℂ) * Complex.I)
                        = ((((t * x : ℝ) + s * x : ℝ) : ℂ) * Complex.I) := by
                            congr 1
                            ring
                    _ = ((((t * x : ℝ) : ℂ) + (((s * x : ℝ) : ℂ))) * Complex.I) := by
                          norm_num
                calc
                  Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I)
                      = Complex.exp
                          ((((t * x : ℝ) : ℂ) + (((s * x : ℝ) : ℂ))) * Complex.I) := by
                              rw [hsplit]
                  _ =
                      Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I) +
                        (((s * x : ℝ) : ℂ) * Complex.I)) := by
                          rw [add_mul]
                  _ =
                      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                        Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by
                          rw [Complex.exp_add]
                  _ =
                      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                        Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by rfl
      _ = Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            ∫ s : ℝ, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 := by
              simpa using
                (integral_const_mul (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I))
                  (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I))
                  (μ := gaussianReal 0 1))
      _ = Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) := by
              have hGaussianChar :
                  ∫ s : ℝ, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
                    Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) := by
                simpa [MeasureTheory.charFun_apply_real, mul_comm] using
                  (ProbabilityTheory.charFun_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) x)
              rw [hGaussianChar]
  have hLinearAvg :
      ∫ s : ℝ, ((((t + s) * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
        (((t * c : ℝ) : ℂ) * Complex.I) := by
    calc
      ∫ s : ℝ, ((((t + s) * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
          ∫ s : ℝ,
            ((((t * c : ℝ) : ℂ) * Complex.I) + (s : ℂ) * (((c : ℂ)) * Complex.I))
              ∂gaussianReal 0 1 := by
                refine integral_congr_ae <| Filter.Eventually.of_forall fun s ↦ ?_
                simp [c]
                ring
      _ =
          ∫ s : ℝ, (((t * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 +
            ∫ s : ℝ, (s : ℂ) * (((c : ℂ)) * Complex.I) ∂gaussianReal 0 1 := by
              rw [integral_add (integrable_const _)
                (integrable_complexId_gaussianReal_zero_one.mul_const (((c : ℂ)) * Complex.I))]
      _ = (((t * c : ℝ) : ℂ) * Complex.I) := by
            have hMulConst :
                ∫ s : ℝ, (s : ℂ) * (((c : ℂ)) * Complex.I) ∂gaussianReal 0 1 =
                  (∫ s : ℝ, (s : ℂ) ∂gaussianReal 0 1) * (((c : ℂ)) * Complex.I) := by
              simpa using
                (integral_mul_const (((c : ℂ)) * Complex.I) (fun s : ℝ ↦ (s : ℂ))
                  (μ := gaussianReal 0 1))
            rw [integral_const, hMulConst, integral_complexId_gaussianReal_zero_one]
            simp
  -- Proof comment: split the shifted kernel into oscillatory, constant, and linear parts.
  change
    ∫ s : ℝ,
        (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1 -
          ((((t + s) * c : ℝ) : ℂ) * Complex.I)) ∂gaussianReal 0 1 =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) -
        1 - (((t * c : ℝ) : ℂ) * Complex.I)
  have hSplitIntegral :
      ∫ s : ℝ,
          (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1 -
            ((((t + s) * c : ℝ) : ℂ) * Complex.I)) ∂gaussianReal 0 1 =
        ∫ s : ℝ, (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1) ∂gaussianReal 0 1 -
          ∫ s : ℝ, ((((t + s) * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 := by
    simpa [sub_eq_add_neg, add_assoc] using
      (integral_sub (hOscInt.sub (integrable_const (1 : ℂ))) hLinearInt)
  rw [hSplitIntegral, integral_sub hOscInt (integrable_const (1 : ℂ))]
  rw [hOscAvg, integral_const, hLinearAvg]
  simp [c]

/-- Helper for Theorem 16.17: Gaussian averaging of the quadratic Lévy term adds the unit
variance contribution. -/
private lemma integral_shiftedLevyQuadratic_gaussianReal_zero_one (σ2 t : ℝ) :
    ∫ s : ℝ, (((-(σ2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) ∂gaussianReal 0 1 =
      (((-(σ2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) := by
  -- Proof comment: pull out the scalar coefficient and use the Gaussian second-moment identity.
  rw [integral_complex_ofReal, integral_const_mul, integral_shiftedSq_gaussianReal_zero_one]

/-- Helper for Theorem 16.17: Gaussian averaging kills the centered linear correction term. -/
private lemma integral_shiftedLinearComplex_gaussianReal_zero_one (c t : ℝ) :
    ∫ s : ℝ, ((((t + s) * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
      (((t * c : ℝ) : ℂ) * Complex.I) := by
  -- Proof comment: split the shifted linear term into a constant part and the centered Gaussian
  -- first moment, which vanishes.
  calc
    ∫ s : ℝ, ((((t + s) * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
        ∫ s : ℝ,
          ((((t * c : ℝ) : ℂ) * Complex.I) + (s : ℂ) * (((c : ℂ)) * Complex.I))
            ∂gaussianReal 0 1 := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun s ↦ ?_
              simp
              ring
    _ =
        ∫ s : ℝ, (((t * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 +
          ∫ s : ℝ, (s : ℂ) * (((c : ℂ)) * Complex.I) ∂gaussianReal 0 1 := by
            rw [integral_add (integrable_const _)
              (integrable_complexId_gaussianReal_zero_one.mul_const (((c : ℂ)) * Complex.I))]
    _ = (((t * c : ℝ) : ℂ) * Complex.I) := by
          have hMulConst :
              ∫ s : ℝ, (s : ℂ) * (((c : ℂ)) * Complex.I) ∂gaussianReal 0 1 =
                (∫ s : ℝ, (s : ℂ) ∂gaussianReal 0 1) * (((c : ℂ)) * Complex.I) := by
            simpa using
              (integral_mul_const (((c : ℂ)) * Complex.I) (fun s : ℝ ↦ (s : ℂ))
                (μ := gaussianReal 0 1))
          calc
            ∫ s : ℝ, (((t * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 +
                ∫ s : ℝ, (s : ℂ) * (((c : ℂ)) * Complex.I) ∂gaussianReal 0 1
                =
              (((t * c : ℝ) : ℂ) * Complex.I) +
                (∫ s : ℝ, (s : ℂ) ∂gaussianReal 0 1) * (((c : ℂ)) * Complex.I) := by
                  rw [integral_const, hMulConst]
                  simp [probReal_univ]
            _ = (((t * c : ℝ) : ℂ) * Complex.I) := by
                  rw [integral_complexId_gaussianReal_zero_one]
                  simp

/-- Helper for Theorem 16.17: Gaussian averaging rewrites the Lévy--Khinchin exponent in a fixed
normal form. -/
private lemma averageLevyKhinchinExponent_eq_normalForm_local
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) (t : ℝ) :
    ∫ s : ℝ, levyKhinchinExponent τ (t + s) ∂gaussianReal 0 1 =
      (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) +
        (((τ.b * t : ℝ) : ℂ) * Complex.I) +
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν := by
  have hKernelProd := integrable_shiftedCanonicalKernel_prod hτ t
  have hKernelSectionInt :
      Integrable
        (fun s : ℝ ↦ ∫ x : ℝ, levyKhinchinCanonicalKernel (t + s) x ∂τ.ν)
        (gaussianReal 0 1) :=
    hKernelProd.integral_prod_left
  have hKernelSwap :
      ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernel (t + s) x ∂τ.ν ∂gaussianReal 0 1 =
        ∫ x : ℝ, ∫ s : ℝ, levyKhinchinCanonicalKernel (t + s) x ∂gaussianReal 0 1 ∂τ.ν := by
    -- Proof comment: Fubini moves the Gaussian averaging inside the Lévy measure integral once
    -- the product kernel is shown integrable.
    simpa [Function.uncurry] using
      (integral_integral_swap
        (μ := gaussianReal 0 1) (ν := τ.ν)
        (f := fun s x ↦ levyKhinchinCanonicalKernel (t + s) x)
        hKernelProd)
  have hKernelAvg :
      ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernel (t + s) x ∂τ.ν ∂gaussianReal 0 1 =
        ∫ x : ℝ,
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
            (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν := by
    -- Proof comment: the previously isolated Gaussian kernel average fixes one canonical spelling
    -- for the jump term and avoids reopening `levyKhinchinExponentWithCentering`.
    rw [hKernelSwap]
    refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
    exact integral_gaussianRecovery_shiftedCanonicalKernel t x
  have hQuadInt :
      Integrable
        (fun s : ℝ ↦ (((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)))
        (gaussianReal 0 1) := by
    simpa [mul_assoc] using
      (((integrable_shiftedSq_gaussianReal_zero_one t).ofReal).const_mul
        (((( -(τ.sigma2 / 2) : ℝ) : ℂ))))
  have hLinearInt :
      Integrable
        (fun s : ℝ ↦ (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I))
        (gaussianReal 0 1) := by
    have hConst :
        Integrable (fun _ : ℝ ↦ (((τ.b * t : ℝ) : ℂ) * Complex.I)) (gaussianReal 0 1) :=
      integrable_const _
    have hId :
        Integrable (fun s : ℝ ↦ (s : ℂ) * (((τ.b : ℂ)) * Complex.I)) (gaussianReal 0 1) :=
      by
        simpa [mul_comm] using
          integrable_complexId_gaussianReal_zero_one.const_mul (((τ.b : ℂ)) * Complex.I)
    refine (hConst.add hId).congr ?_
    filter_upwards with s
    simp
    ring
  -- Proof comment: average the quadratic, linear, and jump contributions separately, then
  -- reassemble the exponent in the fixed normal form used below.
  change
    ∫ s : ℝ,
        (((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) +
          (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I) +
            ∫ x : ℝ, levyKhinchinCanonicalKernel (t + s) x ∂τ.ν
        ∂gaussianReal 0 1 =
      (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) +
        (((τ.b * t : ℝ) : ℂ) * Complex.I) +
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν
  have hSplit₁ :
      ∫ s : ℝ,
          ((((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I) +
            ∫ x : ℝ, levyKhinchinCanonicalKernel (t + s) x ∂τ.ν) ∂gaussianReal 0 1 =
        ∫ s : ℝ,
            ((((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) +
              (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I)) ∂gaussianReal 0 1 +
          ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernel (t + s) x ∂τ.ν ∂gaussianReal 0 1 := by
    simpa [add_assoc] using
      (integral_add (hQuadInt.add hLinearInt) hKernelSectionInt)
  have hSplit₂ :
      ∫ s : ℝ,
          ((((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I)) ∂gaussianReal 0 1 =
        ∫ s : ℝ, (((-(τ.sigma2 / 2) * (t + s) ^ (2 : ℕ) : ℝ) : ℂ)) ∂gaussianReal 0 1 +
          ∫ s : ℝ, (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 := by
    exact integral_add hQuadInt hLinearInt
  have hLinearAvg' :
      ∫ s : ℝ, (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
        (((τ.b * t : ℝ) : ℂ) * Complex.I) := by
    simpa [mul_comm] using integral_shiftedLinearComplex_gaussianReal_zero_one τ.b t
  rw [hSplit₁, hSplit₂]
  rw [integral_shiftedLevyQuadratic_gaussianReal_zero_one]
  calc
    (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) +
          ∫ s : ℝ, (((τ.b * (t + s) : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 +
          ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernel (t + s) x ∂τ.ν ∂gaussianReal 0 1
        =
      (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) +
          (((τ.b * t : ℝ) : ℂ) * Complex.I) +
          ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernel (t + s) x ∂τ.ν ∂gaussianReal 0 1 := by
            simpa [add_assoc] using
              congrArg
                (fun z : ℂ ↦
                  (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) + z +
                    ∫ s : ℝ, ∫ x : ℝ, levyKhinchinCanonicalKernel (t + s) x ∂τ.ν
                      ∂gaussianReal 0 1)
                hLinearAvg'
    _ =
      (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) +
        (((τ.b * t : ℝ) : ℂ) * Complex.I) +
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν := by
            rw [hKernelAvg]

/-- Helper for Theorem 16.17: subtracting the Gaussian-smoothed jump kernel leaves exactly the
recovery kernel term. -/
private lemma canonicalKernel_sub_gaussianSmoothed_eq_recoveryKernel_local
    (t x : ℝ) :
    levyKhinchinCanonicalKernel t x -
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
          (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x := by
  -- Proof comment: this is the one-line algebraic bridge between the canonical jump kernel and
  -- the Gaussian-damped kernel.
  simp [levyKhinchinCanonicalKernel, levyKhinchinCanonicalKernelLocal, gaussianRecoveryKernel]
  ring_nf

/-- Helper for Theorem 16.17: Gaussian smoothing converts the Lévy--Khintchin exponent into the
characteristic function of the auxiliary finite measure. -/
private lemma gaussianSmoothedExponent_eq_auxCharFun
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) (t : ℝ) :
    let α : NNReal := ⟨τ.sigma2 / 2, by
      exact div_nonneg hτ.sigma2_nonneg (by positivity)⟩
    charFun (((gaussianRecoveryAuxFiniteMeasure α τ.ν
      (integrable_gaussianRecoveryKernel hτ.isCanonicalMeasure) : FiniteMeasure ℝ) :
        Measure ℝ)) t =
      levyKhinchinExponent τ t -
        ∫ s : ℝ, levyKhinchinExponent τ (t + s) ∂gaussianReal 0 1 := by
  let α : NNReal := ⟨τ.sigma2 / 2, by
    exact div_nonneg hτ.sigma2_nonneg (by positivity)⟩
  have hAverage := averageLevyKhinchinExponent_eq_normalForm_local hτ t
  have hKernelInt :
      Integrable (levyKhinchinCanonicalKernel t) τ.ν :=
    integrable_levyKhinchinCanonicalKernel_local hτ.isCanonicalMeasure t
  have hRecoveryInt :
      Integrable
        (fun x : ℝ ↦
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x)
        τ.ν := by
    have hExpMeas :
        Measurable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) := by
      exact
        Complex.continuous_exp.measurable.comp <|
          (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const
            Complex.I
    have hKernelMeas : Measurable (fun x : ℝ ↦ (gaussianRecoveryKernel x : ℂ)) := by
      exact Complex.measurable_ofReal.comp measurable_gaussianRecoveryKernel
    refine (integrable_gaussianRecoveryKernel hτ.isCanonicalMeasure).mono'
      (hExpMeas.mul hKernelMeas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hnormExp : ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ = 1 := by
        simpa using (Complex.norm_exp_ofReal_mul_I (t * x))
      have hnonneg : 0 ≤ gaussianRecoveryKernel x := gaussianRecoveryKernel_nonneg x
      calc
        ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ * ‖gaussianRecoveryKernel x‖ := by
                simp
        _ ≤ gaussianRecoveryKernel x := by
              rw [hnormExp]
              simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hAvgKernelInt :
      Integrable
        (fun x : ℝ ↦
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
            (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I))
        τ.ν := by
    refine (hKernelInt.sub hRecoveryInt).congr ?_
    filter_upwards with x
    simp [levyKhinchinCanonicalKernel, levyKhinchinCanonicalKernelLocal, gaussianRecoveryKernel]
    ring_nf
  have hKernelDiff :
      ∫ x : ℝ, levyKhinchinCanonicalKernel t x ∂τ.ν -
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν =
        ∫ x : ℝ,
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂τ.ν := by
    -- Proof comment: subtract the fixed averaged jump normal form from the original kernel and
    -- rewrite the pointwise difference by the recovery-kernel adapter.
    rw [← integral_sub hKernelInt hAvgKernelInt]
    refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
    exact canonicalKernel_sub_gaussianSmoothed_eq_recoveryKernel_local t x
  have hAverageExpanded :
      ∫ s : ℝ,
          levyKhinchinExponentWithCentering τ.sigma2 τ.b τ.ν levyKhinchinCanonicalCentering
            (t + s) ∂gaussianReal 0 1 =
        (((-(τ.sigma2 / 2) * (t ^ (2 : ℕ) + 1) : ℝ) : ℂ)) +
          (((τ.b * t : ℝ) : ℂ) * Complex.I) +
            ∫ x : ℝ,
              (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                  Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
                (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν := by
    simpa [levyKhinchinExponent] using hAverage
  have hKernelDiffExpanded :
      ∫ x : ℝ,
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν -
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((-(x ^ (2 : ℕ) / 2) : ℝ) : ℂ)) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν =
        ∫ x : ℝ,
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂τ.ν := by
    simpa [levyKhinchinCanonicalKernel, levyKhinchinCanonicalKernelLocal] using hKernelDiff
  -- Proof comment: the auxiliary finite-measure characteristic function equals the Gaussian atom
  -- plus the recovery-kernel integral, and the averaged normal form turns that expression into the
  -- desired exponent difference.
  calc
    charFun (((gaussianRecoveryAuxFiniteMeasure α τ.ν
      (integrable_gaussianRecoveryKernel hτ.isCanonicalMeasure) : FiniteMeasure ℝ) :
        Measure ℝ)) t =
        (α : ℂ) +
          ∫ x : ℝ,
            Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x ∂τ.ν := by
              exact
                gaussianRecoveryAuxFiniteMeasure_charFun α
                  (integrable_gaussianRecoveryKernel hτ.isCanonicalMeasure) t
    _ = levyKhinchinExponent τ t -
          ∫ s : ℝ, levyKhinchinExponent τ (t + s) ∂gaussianReal 0 1 := by
            rw [levyKhinchinExponent, levyKhinchinExponentWithCentering, hAverageExpanded,
              ← hKernelDiffExpanded]
            have hAlpha : (α : ℂ) = (((τ.sigma2 / 2 : ℝ) : ℂ)) := by
              rfl
            rw [hAlpha]
            simp [mul_comm, mul_left_comm, mul_assoc]
            ring_nf

/-- Helper for Theorem 16.17: equality of the Lévy--Khintchin exponents identifies the
Gaussian-smoothed auxiliary finite measures. -/
private lemma gaussianRecoveryAuxFiniteMeasure_eq_of_exponentEq
    {τ₁ τ₂ : LevyKhinchinTriple}
    (hτ₁ : IsCanonicalTriple τ₁) (hτ₂ : IsCanonicalTriple τ₂)
    (hExp : ∀ t : ℝ, levyKhinchinExponent τ₁ t = levyKhinchinExponent τ₂ t) :
    let α₁ : NNReal := ⟨τ₁.sigma2 / 2, by
      exact div_nonneg hτ₁.sigma2_nonneg (by positivity)⟩
    let α₂ : NNReal := ⟨τ₂.sigma2 / 2, by
      exact div_nonneg hτ₂.sigma2_nonneg (by positivity)⟩
    gaussianRecoveryAuxFiniteMeasure α₁ τ₁.ν
        (integrable_gaussianRecoveryKernel hτ₁.isCanonicalMeasure) =
      gaussianRecoveryAuxFiniteMeasure α₂ τ₂.ν
        (integrable_gaussianRecoveryKernel hτ₂.isCanonicalMeasure) := by
  let α₁ : NNReal := ⟨τ₁.sigma2 / 2, by
    exact div_nonneg hτ₁.sigma2_nonneg (by positivity)⟩
  let α₂ : NNReal := ⟨τ₂.sigma2 / 2, by
    exact div_nonneg hτ₂.sigma2_nonneg (by positivity)⟩
  apply FiniteMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  have hDiff :
      levyKhinchinExponent τ₁ t -
          ∫ s : ℝ, levyKhinchinExponent τ₁ (t + s) ∂gaussianReal 0 1 =
        levyKhinchinExponent τ₂ t -
          ∫ s : ℝ, levyKhinchinExponent τ₂ (t + s) ∂gaussianReal 0 1 := by
    rw [hExp t]
    congr 1
    refine integral_congr_ae <| Filter.Eventually.of_forall fun s ↦ ?_
    exact hExp (t + s)
  -- Proof comment: after rewriting both sides by the Gaussian smoothing identity, pointwise
  -- equality of exponents gives equality of the auxiliary characteristic functions.
  calc
    charFun (((gaussianRecoveryAuxFiniteMeasure α₁ τ₁.ν
      (integrable_gaussianRecoveryKernel hτ₁.isCanonicalMeasure) : FiniteMeasure ℝ) :
        Measure ℝ)) t =
        levyKhinchinExponent τ₁ t -
          ∫ s : ℝ, levyKhinchinExponent τ₁ (t + s) ∂gaussianReal 0 1 := by
            exact gaussianSmoothedExponent_eq_auxCharFun hτ₁ t
    _ =
        levyKhinchinExponent τ₂ t -
          ∫ s : ℝ, levyKhinchinExponent τ₂ (t + s) ∂gaussianReal 0 1 := hDiff
    _ =
        charFun (((gaussianRecoveryAuxFiniteMeasure α₂ τ₂.ν
          (integrable_gaussianRecoveryKernel hτ₂.isCanonicalMeasure) : FiniteMeasure ℝ) :
            Measure ℝ)) t := by
              exact (gaussianSmoothedExponent_eq_auxCharFun hτ₂ t).symm

/-- Helper for Theorem 16.17: same-law Lévy--Khintchin representations have the same Gaussian
coefficient and Lévy measure. -/
private lemma sigma2_levyMeasure_eq_of_sameRepresentation
    {μ : ProbabilityMeasure ℝ} {τ₁ τ₂ : LevyKhinchinTriple}
    (hτ₁ : HasLevyKhinchinRepresentation μ τ₁)
    (hτ₂ : HasLevyKhinchinRepresentation μ τ₂) :
    τ₁.sigma2 = τ₂.sigma2 ∧ τ₁.ν = τ₂.ν := by
  have hExp :
      ∀ t : ℝ, levyKhinchinExponent τ₁ t = levyKhinchinExponent τ₂ t :=
    levyKhinchinExponent_eq_of_sameRepresentation_of_continuous
      hτ₁
      hτ₂
      (continuousLevyKhinchinExponentLocal hτ₁.isCanonicalTriple)
      (continuousLevyKhinchinExponentLocal hτ₂.isCanonicalTriple)
  let α₁ : NNReal := ⟨τ₁.sigma2 / 2, by
    exact div_nonneg hτ₁.isCanonicalTriple.sigma2_nonneg (by positivity)⟩
  let α₂ : NNReal := ⟨τ₂.sigma2 / 2, by
    exact div_nonneg hτ₂.isCanonicalTriple.sigma2_nonneg (by positivity)⟩
  have hAuxEq :
      gaussianRecoveryAuxFiniteMeasure α₁ τ₁.ν
          (integrable_gaussianRecoveryKernel hτ₁.isCanonicalTriple.isCanonicalMeasure) =
        gaussianRecoveryAuxFiniteMeasure α₂ τ₂.ν
          (integrable_gaussianRecoveryKernel hτ₂.isCanonicalTriple.isCanonicalMeasure) := by
    simpa [α₁, α₂] using
      gaussianRecoveryAuxFiniteMeasure_eq_of_exponentEq
        hτ₁.isCanonicalTriple hτ₂.isCanonicalTriple hExp
  have hAlpha :
      (α₁ : ENNReal) = α₂ := by
    have hZero :=
      congrArg
        (fun ν : FiniteMeasure ℝ ↦ ((ν : Measure ℝ) ({0} : Set ℝ)))
        hAuxEq
    simpa [gaussianRecoveryAuxFiniteMeasure_apply_zero] using hZero
  have hAlphaNN : α₁ = α₂ := ENNReal.coe_inj.mp hAlpha
  have hSigmaHalf : τ₁.sigma2 / 2 = τ₂.sigma2 / 2 := by
    simpa [α₁, α₂] using congrArg (fun a : NNReal ↦ (a : ℝ)) hAlphaNN
  have hSigma : τ₁.sigma2 = τ₂.sigma2 := by
    linarith
  have hTiltRestrict :
      ((τ₁.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
          (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) =
        ((τ₂.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
          (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))) := by
    have hRestrict :=
      congrArg
        (fun ν : FiniteMeasure ℝ ↦ ((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ)))
        hAuxEq
    change
      ((((α₁ : ENNReal) • Measure.dirac 0 +
          τ₁.ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).restrict
          ({0}ᶜ : Set ℝ))) =
        ((((α₂ : ENNReal) • Measure.dirac 0 +
          τ₂.ν.withDensity (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).restrict
          ({0}ᶜ : Set ℝ))) at hRestrict
    rw [Measure.restrict_add, Measure.restrict_smul,
      restrict_dirac' ((measurableSet_singleton (0 : ℝ)).compl), if_neg (by simp),
      smul_zero, zero_add, MeasureTheory.restrict_withDensity
        ((measurableSet_singleton (0 : ℝ)).compl),
      Measure.restrict_add, Measure.restrict_smul,
      restrict_dirac' ((measurableSet_singleton (0 : ℝ)).compl), if_neg (by simp),
      smul_zero, zero_add, MeasureTheory.restrict_withDensity
        ((measurableSet_singleton (0 : ℝ)).compl)] at hRestrict
    exact hRestrict
  have hNuRestrict :
      τ₁.ν.restrict ({0}ᶜ : Set ℝ) = τ₂.ν.restrict ({0}ᶜ : Set ℝ) := by
    have hInv :=
      congrArg
        (fun η : Measure ℝ ↦
          η.withDensity (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹))
        hTiltRestrict
    -- Proof comment: on `{0}ᶜ`, the Gaussian recovery density is strictly positive, so a second
    -- `withDensity` by its inverse removes the tilt and recovers the punctured jump measure.
    calc
      τ₁.ν.restrict ({0}ᶜ : Set ℝ) =
          (((τ₁.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
              (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).withDensity
            (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹)) := by
              symm
              exact
                withDensity_gaussianRecoveryKernel_inv_same_restrict_compl_singleton τ₁.ν
      _ =
          (((τ₂.ν.restrict ({0}ᶜ : Set ℝ)).withDensity
              (fun x ↦ ENNReal.ofReal (gaussianRecoveryKernel x))).withDensity
            (fun x ↦ (ENNReal.ofReal (gaussianRecoveryKernel x))⁻¹)) := hInv
      _ = τ₂.ν.restrict ({0}ᶜ : Set ℝ) := by
            exact
              withDensity_gaussianRecoveryKernel_inv_same_restrict_compl_singleton τ₂.ν
  have hNu : τ₁.ν = τ₂.ν := by
    have hZeroRestrict :
        τ₁.ν.restrict ({0} : Set ℝ) = τ₂.ν.restrict ({0} : Set ℝ) := by
      rw [Measure.restrict_singleton, hτ₁.isCanonicalTriple.isCanonicalMeasure.measure_singleton_zero,
        zero_smul, Measure.restrict_singleton,
        hτ₂.isCanonicalTriple.isCanonicalMeasure.measure_singleton_zero, zero_smul]
    rw [← Measure.restrict_add_restrict_compl (μ := τ₁.ν) (measurableSet_singleton (0 : ℝ)),
      ← Measure.restrict_add_restrict_compl (μ := τ₂.ν) (measurableSet_singleton (0 : ℝ)),
      hZeroRestrict]
    exact congrArg (fun η : Measure ℝ ↦ τ₂.ν.restrict ({0} : Set ℝ) + η) hNuRestrict
  exact ⟨hSigma, hNu⟩

/-- Helper for Theorem 16.17: the canonical triple in a Lévy--Khintchin representation is unique.
-/
private lemma levyTriple_eq_of_same_representation
    {μ : ProbabilityMeasure ℝ} {τ₁ τ₂ : LevyKhinchinTriple}
    (hτ₁ : HasLevyKhinchinRepresentation μ τ₁)
    (hτ₂ : HasLevyKhinchinRepresentation μ τ₂) :
    τ₁ = τ₂ := by
  obtain ⟨hSigma, hNu⟩ := sigma2_levyMeasure_eq_of_sameRepresentation hτ₁ hτ₂
  have hExp :
      ∀ t : ℝ, levyKhinchinExponent τ₁ t = levyKhinchinExponent τ₂ t :=
    levyKhinchinExponent_eq_of_sameRepresentation_of_continuous
      hτ₁
      hτ₂
      (continuousLevyKhinchinExponentLocal hτ₁.isCanonicalTriple)
      (continuousLevyKhinchinExponentLocal hτ₂.isCanonicalTriple)
  have hB :
      τ₁.b = τ₂.b := by
    have hDrift :
        (((τ₁.b : ℂ)) * Complex.I) = (((τ₂.b : ℂ)) * Complex.I) := by
      simpa [levyKhinchinExponent, levyKhinchinExponentWithCentering, hSigma, hNu] using hExp 1
    have hIm := congrArg Complex.im hDrift
    simpa using hIm
  -- Proof comment: once the Gaussian coefficient, Lévy measure, and drift all agree, the two
  -- representing triples coincide componentwise.
  cases τ₁
  cases τ₂
  simp_all

/-- Helper for Theorem 16.17: package exact positive-integer convolution roots of an infinitely
divisible law into a single `ℕ+`-indexed family. -/
private theorem existsExactRootFamily_of_isInfinitelyDivisible_local
    {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    ∃ μroot : ℕ+ → ProbabilityMeasure ℝ, ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ := by
  -- Proof comment: choose one exact `n`th convolution root for each positive integer and package
  -- those choices into a single family.
  refine ⟨fun n ↦ Classical.choose (hμ.exists_root n), ?_⟩
  intro n
  exact Classical.choose_spec (hμ.exists_root n)

/-- Helper for Theorem 16.17: an exact positive-integer root family yields the expected
compound-Poisson approximation. -/
private theorem exactRootCompoundPoissonApproximation
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ) :
    Tendsto
      (fun n : ℕ ↦
        compoundPoissonMeasure
          (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
            FiniteMeasure ℝ)))
      atTop
      (𝓝 μ) := by
  let φs : ℕ → ℝ → ℂ := fun n t ↦ charFun (μroot (Nat.toPNat' n) : Measure ℝ) t
  have hφs : ∀ n : ℕ, IsCFP (φs n) := by
    intro n
    -- Proof comment: each exact root already appears as a characteristic function.
    refine ⟨μroot (Nat.toPNat' n), ?_⟩
    funext t
    rfl
  have hpow :
      ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (φs n t) ^ n) atTop (𝓝 (charFun (μ : Measure ℝ) t)) := by
    intro t
    have hrootChar :
        ∀ n : ℕ+, (charFun (μroot n : Measure ℝ) t) ^ (n : ℕ) = charFun (μ : Measure ℝ) t := by
      intro n
      calc
        (charFun (μroot n : Measure ℝ) t) ^ (n : ℕ)
            = charFun ((μroot n ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t := by
                simpa using
                  (congrArg (fun f : ℝ → ℂ ↦ f t)
                    (ProbabilityMeasure.charFun_pow (μroot n) (n : ℕ))).symm
        _ = charFun (μ : Measure ℝ) t := by
              simpa using
                congrArg (fun ν : ProbabilityMeasure ℝ ↦ charFun (ν : Measure ℝ) t) (hroot n)
    have hpowP :
        Tendsto
          (fun n : ℕ+ ↦ (charFun (μroot n : Measure ℝ) t) ^ (n : ℕ))
          atTop
          (𝓝 (charFun (μ : Measure ℝ) t)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      exact Filter.Eventually.of_forall fun n ↦ by
        simpa using (hrootChar n).symm
    have hshiftPNat :
        Tendsto
          (fun n : ℕ ↦ (charFun (μroot (Nat.succPNat n) : Measure ℝ) t) ^
            ((Nat.succPNat n : ℕ+) : ℕ))
          atTop
          (𝓝 (charFun (μ : Measure ℝ) t)) := by
      -- Proof comment: reindex the positive integers by `Nat.succPNat`.
      simpa [OrderIso.pnatIsoNat_symm_apply] using
        hpowP.comp OrderIso.pnatIsoNat.symm.tendsto_atTop
    have hshiftNat :
        Tendsto (fun n : ℕ ↦ (φs (n + 1) t) ^ (n + 1)) atTop
          (𝓝 (charFun (μ : Measure ℝ) t)) := by
      -- Proof comment: after shifting by one, `Nat.toPNat'` agrees with `Nat.succPNat`.
      simpa [φs, PNat.toPNat'_coe (Nat.succ_pos _), Nat.succPNat_coe] using hshiftPNat
    -- Proof comment: a finite shift does not change the `atTop` limit.
    exact (Filter.tendsto_add_atTop_iff_nat 1).1 hshiftNat
  have hchar0 : ContinuousAt (charFun (μ : Measure ℝ)) 0 := by
    simpa using
      (MeasureTheory.continuous_charFun : Continuous (charFun (μ : Measure ℝ))).continuousAt
  rcases
      (cfp_power_limit_iff_linearized_limit hφs).1
        ⟨charFun (μ : Measure ℝ), hpow, hchar0⟩ with
    ⟨ψ, hlin, _hψ0⟩
  have hcharEq :
      charFun (μ : Measure ℝ) = fun t : ℝ ↦ Complex.exp (ψ t) :=
    cfp_power_limit_eq_cexp_linearized_limit hφs hpow hchar0 hlin
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦
    compoundPoissonMeasure
      (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
        FiniteMeasure ℝ))
  have hμsChar :
      ∀ t : ℝ,
        Tendsto (fun n : ℕ ↦ charFun (μs n : Measure ℝ) t) atTop
          (𝓝 (charFun (μ : Measure ℝ) t)) := by
    intro t
    have htarget : charFun (μ : Measure ℝ) t = Complex.exp (ψ t) := by
      simpa using congrArg (fun f : ℝ → ℂ ↦ f t) hcharEq
    have hlinShift :
        Tendsto
          (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) * (φs (n + 1) t - 1))
          atTop
          (𝓝 (ψ t)) :=
      (Filter.tendsto_add_atTop_iff_nat 1).2 (hlin t)
    have hExpCont : ContinuousAt Complex.exp (ψ t) := by
      simpa using Complex.continuous_exp.continuousAt
    rw [htarget]
    refine Tendsto.congr' ?_ (hExpCont.tendsto.comp hlinShift)
    exact Filter.Eventually.of_forall fun n ↦ by
      -- Proof comment: the compound-Poisson characteristic function is the centered exponential
      -- attached to the `(n + 1)`st root.
      simpa [μs, φs, PNat.toPNat'_coe (Nat.succ_pos _), Nat.succPNat_coe] using
        (charFun_compoundPoissonMeasure_natSmulProbability
          (μroot (Nat.succPNat n)) (n + 1) t).symm
  -- Proof comment: characteristic functions determine weak convergence of probability laws.
  exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 hμsChar

/-- Helper for Theorem 16.17: pushing a punctured finite measure forward along `Subtype.val`
preserves the fact that there is no atom at `0`. -/
private lemma map_puncturedFiniteMeasure_apply_singleton_zero
    (ν : FiniteMeasure {x : ℝ // x ≠ 0}) :
    (((ν.map Subtype.val : FiniteMeasure ℝ) : Measure ℝ) ({0} : Set ℝ)) = 0 := by
  change (Measure.map Subtype.val (ν : Measure {x : ℝ // x ≠ 0})) ({0} : Set ℝ) = 0
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton 0)]
  have hpreimage :
      (Subtype.val : {x : ℝ // x ≠ 0} → ℝ) ⁻¹' ({0} : Set ℝ) =
        (∅ : Set {x : ℝ // x ≠ 0}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false]
    constructor
    · intro hx
      exact x.2 hx
    · intro hFalse
      exact False.elim hFalse
  simp [hpreimage]

/-- Helper for Theorem 16.17: the canonical centering cutoff is uniformly bounded by `1`. -/
private lemma norm_levyKhinchinCanonicalCentering_le_one_local (x : ℝ) :
    ‖levyKhinchinCanonicalCentering x‖ ≤ 1 := by
  -- Proof comment: on the unit ball the cutoff equals `x`, while off the unit ball it vanishes.
  by_cases hx : |x| < 1
  · simpa [levyKhinchinCanonicalCentering, hx, Real.norm_eq_abs] using le_of_lt hx
  · simp [levyKhinchinCanonicalCentering, hx]

/-- Helper for Theorem 16.17: a finite measure with no atom at `0` already satisfies the
canonical Lévy-measure condition. -/
private lemma isCanonicalMeasure_of_isFiniteMeasure_of_measure_singleton_zero_local
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν0 : ν ({0} : Set ℝ) = 0) :
    IsCanonicalMeasure ν := by
  refine ⟨hν0, ?_⟩
  -- Proof comment: the canonical integrand is bounded by `1`, so finiteness of `ν` gives
  -- integrability immediately.
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    have hnonneg : 0 ≤ min (x ^ (2 : ℕ)) 1 := by positivity
    have hle : min (x ^ (2 : ℕ)) 1 ≤ 1 := min_le_right _ _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

/-- Helper for Theorem 16.17: the complex cutoff correction is integrable against every finite
measure. -/
private lemma integrable_complexCenteringCorrection_of_isFiniteMeasure_local
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable
      (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ν := by
  -- Proof comment: the cutoff has norm at most `1`, so the complex correction is bounded by
  -- `|t|`.
  refine (integrable_const ‖t‖).mono'
    (((Complex.measurable_ofReal.comp
      (measurable_const.mul measurable_levyKhinchinCanonicalCentering)).mul_const
        Complex.I).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    calc
      ‖(((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)‖
          = ‖t * levyKhinchinCanonicalCentering x‖ := by simp
      _ = ‖t‖ * ‖levyKhinchinCanonicalCentering x‖ := by simp [norm_mul]
      _ ≤ ‖t‖ * 1 := by
            exact mul_le_mul_of_nonneg_left
              (norm_levyKhinchinCanonicalCentering_le_one_local x) (norm_nonneg t)
      _ = ‖t‖ := by ring

/-- Helper for Theorem 16.17: the compound-Poisson kernel `x ↦ exp(i t x) - 1` is integrable
against every finite measure. -/
private lemma integrable_compoundPoissonKernel_of_isFiniteMeasure_local
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν := by
  -- Proof comment: the oscillatory factor has norm `1`, so subtracting `1` leaves a uniform
  -- bound by `2`.
  refine (integrable_const (2 : ℝ)).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    calc
      ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖
          ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by
            rw [Complex.norm_exp_ofReal_mul_I]
            simp
      _ = 2 := by norm_num

/-- Helper for Theorem 16.17: the integrated complex cutoff correction equals the linear drift
term `i t ∫ x 𝟙_{|x|<1} ν(dx)`. -/
private lemma integral_complexCenteringCorrection_eq_local
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν =
      ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I) := by
  -- Proof comment: first move the constant `I` outside the integral, then rewrite the remaining
  -- complex integral as the complexification of the real one.
  calc
    ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν
        = (∫ x : ℝ, ((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) ∂ν) * Complex.I := by
            simpa using
              (integral_mul_const (μ := ν) Complex.I
                (fun x : ℝ ↦ ((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ)))
    _ = ((((∫ x : ℝ, t * levyKhinchinCanonicalCentering x ∂ν : ℝ)) : ℂ)) * Complex.I := by
          rw [integral_complex_ofReal]
    _ = ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ)) : ℂ)) * Complex.I := by
          rw [integral_const_mul]

/-- Helper for Theorem 16.17: the complex `sin` correction is integrable against every finite
measure. -/
private lemma integrable_complexSinCorrection_of_isFiniteMeasure_local
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ ↦ (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ν := by
  -- Proof comment: `sin` is uniformly bounded by `1`, so the complex `sin` correction is again
  -- bounded by `|t|`.
  refine (integrable_const ‖t‖).mono'
    (((Complex.measurable_ofReal.comp
      (measurable_const.mul Real.measurable_sin)).mul_const Complex.I).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    calc
      ‖(((t * Real.sin x : ℝ) : ℂ) * Complex.I)‖
          = ‖((t * Real.sin x : ℝ) : ℂ)‖ * ‖Complex.I‖ := by
              rw [norm_mul]
      _ = ‖t * Real.sin x‖ := by rw [Complex.norm_real, Complex.norm_I, mul_one]
      _ = |t * Real.sin x| := by rw [Real.norm_eq_abs]
      _ = |t| * |Real.sin x| := by rw [abs_mul]
      _ = ‖t‖ * ‖Real.sin x‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖t‖ * 1 := by
            gcongr
            simpa [Real.norm_eq_abs] using Real.abs_sin_le_one x
      _ = ‖t‖ := by ring

/-- Helper for Theorem 16.17: the integrated complex `sin` correction equals the linear drift
term `i t ∫ sin(x) ν(dx)`. -/
private lemma integral_complexSinCorrection_eq_local
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    ∫ x : ℝ, (((t * Real.sin x : ℝ) : ℂ) * Complex.I) ∂ν =
      ((((t * ∫ x : ℝ, Real.sin x ∂ν : ℝ) : ℂ)) * Complex.I) := by
  -- Proof comment: pull the constant factor `I` through the integral, then rewrite the remaining
  -- complex integral as the complexification of the real `sin` integral.
  calc
    ∫ x : ℝ, (((t * Real.sin x : ℝ) : ℂ) * Complex.I) ∂ν
        = (∫ x : ℝ, ((t * Real.sin x : ℝ) : ℂ) ∂ν) * Complex.I := by
            simpa using
              (integral_mul_const (μ := ν) Complex.I
                (fun x : ℝ ↦ ((t * Real.sin x : ℝ) : ℂ)))
    _ = ((((∫ x : ℝ, t * Real.sin x ∂ν : ℝ)) : ℂ)) * Complex.I := by
          rw [integral_complex_ofReal]
    _ = ((((t * ∫ x : ℝ, Real.sin x ∂ν : ℝ)) : ℂ)) * Complex.I := by
          rw [integral_const_mul]

/-- Helper for Theorem 16.17: a finite jump intensity with no atom at `0` already gives the
canonical compound-Poisson representation. -/
private lemma compoundPoisson_hasLevyKhinchinRepresentation
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν0 : ν ({0} : Set ℝ) = 0) :
    HasLevyKhinchinRepresentation
      (compoundPoissonMeasure ν)
      { sigma2 := 0
        b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν
        ν := ν } := by
  constructor
  · -- Proof comment: finite jump intensities with no atom at `0` are canonical, and the
    -- Gaussian coefficient vanishes.
    refine ⟨by simp, isCanonicalMeasure_of_isFiniteMeasure_of_measure_singleton_zero_local ν hν0⟩
  · intro t
    have hkernel :
        Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
      integrable_compoundPoissonKernel_of_isFiniteMeasure_local ν t
    have hcorr :
        Integrable
          (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ν :=
      integrable_complexCenteringCorrection_of_isFiniteMeasure_local ν t
    have hsplit :
        ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂ν =
          ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
            ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν := by
      -- Proof comment: split the centered jump kernel into the raw compound-Poisson kernel minus
      -- the centering correction.
      rw [integral_sub hkernel hcorr]
    have hexponent :
        levyKhinchinExponent
            { sigma2 := 0
              b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν
              ν := ν } t =
          ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν := by
      -- Proof comment: the explicit drift term cancels the integrated centering correction.
      calc
        levyKhinchinExponent
            { sigma2 := 0
              b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν
              ν := ν } t
            =
          ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I) +
            ∫ x : ℝ,
              (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂ν := by
              simp [levyKhinchinExponent, levyKhinchinExponentWithCentering,
                mul_assoc, mul_left_comm, mul_comm]
        _ = ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I) +
              (∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
                ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν) := by
              rw [hsplit]
        _ = ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν := by
              rw [integral_complexCenteringCorrection_eq_local]
              simpa using
                (mul_comm (((∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) (t : ℂ))
    -- Proof comment: the compound-Poisson characteristic function is the exponential of the raw
    -- jump integral, which matches the simplified Lévy--Khintchin exponent above.
    rw [charFun_compoundPoissonMeasure]
    simpa [hexponent]

/-- Helper for Theorem 16.17: the exact-root compound-Poisson approximation can be written with
the punctured jump intensity only. -/
private noncomputable def exactRootApproxIntensity
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    FiniteMeasure ℝ :=
  (puncturedIntensity
      (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
        FiniteMeasure ℝ))).map Subtype.val

/-- Helper for Theorem 16.17: deleting the zero atom does not change the exact-root
compound-Poisson approximant law. -/
private theorem exactRootApproxLaw_eq_fullCompoundPoisson_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    compoundPoissonMeasure (exactRootApproxIntensity μroot n) =
      compoundPoissonMeasure
        (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
          FiniteMeasure ℝ)) := by
  let νFinite : FiniteMeasure ℝ :=
    (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
      FiniteMeasure ℝ))
  -- Proof comment: puncturing the scaled root law removes only the irrelevant atom at `0`, so
  -- the resulting compound-Poisson law is unchanged.
  simpa [exactRootApproxIntensity, νFinite] using
    (compoundPoissonMeasure_ignoreZeroAtom νFinite)

/-- Helper for Theorem 16.17: after puncturing the exact-root intensities, the exact-root
compound-Poisson approximants still converge weakly to `μ`. -/
private theorem exactRootApproxLaw_tendsto_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ) :
    Tendsto
      (fun n : ℕ ↦ compoundPoissonMeasure (exactRootApproxIntensity μroot n))
      atTop
      (𝓝 μ) := by
  -- Proof comment: the punctured and unpunctured exact-root compound-Poisson approximants agree
  -- pointwise, so the previously proved full-intensity convergence theorem applies verbatim.
  refine Tendsto.congr' ?_ (exactRootCompoundPoissonApproximation μroot hroot)
  exact Filter.Eventually.of_forall fun n ↦ by
    simpa using (exactRootApproxLaw_eq_fullCompoundPoisson_local μroot n).symm

/-- Helper for Theorem 16.17: the punctured exact-root approximation carries its canonical
compound-Poisson Lévy--Khintchin triple. -/
private noncomputable def exactRootApproxTriple
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    LevyKhinchinTriple :=
  { sigma2 := 0
    b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂(exactRootApproxIntensity μroot n : Measure ℝ)
    ν := (exactRootApproxIntensity μroot n : Measure ℝ) }

/-- Helper for Theorem 16.17: each punctured exact-root intensity yields the expected
compound-Poisson representation. -/
private lemma exactRootApproxTriple_hasLevyKhinchinRepresentation
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    HasLevyKhinchinRepresentation
      (compoundPoissonMeasure (exactRootApproxIntensity μroot n))
      (exactRootApproxTriple μroot n) := by
  let νPunctured : FiniteMeasure {x : ℝ // x ≠ 0} :=
    puncturedIntensity
      (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
        FiniteMeasure ℝ))
  -- Proof comment: after deleting the irrelevant atom at `0`, the remaining finite jump
  -- intensity is already a canonical compound-Poisson Lévy measure.
  simpa [exactRootApproxTriple, exactRootApproxIntensity, νPunctured] using
    compoundPoisson_hasLevyKhinchinRepresentation
      ((νPunctured.map Subtype.val : FiniteMeasure ℝ) : Measure ℝ)
      (map_puncturedFiniteMeasure_apply_singleton_zero νPunctured)

/-- Helper for Theorem 16.17: the Gaussian-smoothed auxiliary finite measure attached to the
`n`th exact-root approximant triple. -/
private noncomputable def exactRootApproxAuxFiniteMeasure
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) : FiniteMeasure ℝ :=
  gaussianRecoveryAuxFiniteMeasure 0
    (exactRootApproxTriple μroot n).ν
    (integrable_gaussianRecoveryKernel
      (exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).isCanonicalTriple.isCanonicalMeasure)

/-- Helper for Theorem 16.17: the exact-root auxiliary finite measure is already the
Gaussian-smoothed characteristic-function package for the `n`th approximant exponent. -/
private lemma exactRootApproxAuxFiniteMeasure_charFun_eq_smoothedExponent_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t =
      levyKhinchinExponent (exactRootApproxTriple μroot n) t -
        ∫ s : ℝ, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
          ∂gaussianReal 0 1 := by
  -- Proof comment: specialize the general Gaussian-smoothing identity to the finite exact-root
  -- approximant triple, whose Gaussian coefficient is already `0`.
  simpa [exactRootApproxAuxFiniteMeasure, exactRootApproxTriple] using
    gaussianSmoothedExponent_eq_auxCharFun
      (exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).isCanonicalTriple t

/-- Helper for Theorem 16.17: evaluating the exact-root auxiliary characteristic function at
frequency `0` reads off the Gaussian-recovery mass integral. -/
private lemma exactRootApproxAuxFiniteMeasure_charFun_zero_eq_integral_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) 0 =
      ((∫ x : ℝ, gaussianRecoveryKernel x ∂(exactRootApproxTriple μroot n).ν : ℝ) : ℂ) := by
  have hcanon :
      IsCanonicalMeasure ((exactRootApproxTriple μroot n).ν) := by
    letI := (exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).isCanonicalTriple
    exact inferInstance
  have hchar :=
    gaussianRecoveryAuxFiniteMeasure_charFun
      (α := 0)
      (ν := (exactRootApproxTriple μroot n).ν)
      (integrable_gaussianRecoveryKernel hcanon)
      0
  -- Proof comment: specialize the Gaussian-smoothing characteristic-function identity at
  -- frequency `0`, where the oscillatory kernel is identically `1`.
  calc
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) 0
        =
          (0 : ℂ) +
            ∫ x : ℝ,
              Complex.exp (((0 * x : ℝ) : ℂ) * Complex.I) * gaussianRecoveryKernel x
                ∂(exactRootApproxTriple μroot n).ν := by
                  simpa [exactRootApproxAuxFiniteMeasure] using hchar
    _ = ∫ x : ℝ, ((gaussianRecoveryKernel x : ℝ) : ℂ) ∂(exactRootApproxTriple μroot n).ν := by
          simp
    _ = ((∫ x : ℝ, gaussianRecoveryKernel x ∂(exactRootApproxTriple μroot n).ν : ℝ) : ℂ) := by
          rw [integral_complex_ofReal]

/-- Helper for Theorem 16.17: the zero-frequency value of the exact-root auxiliary
characteristic function is a nonnegative real mass. -/
private lemma exactRootApproxAuxFiniteMeasure_charFun_zero_re_nonneg_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    0 ≤ Complex.re (charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) :
      Measure ℝ) 0) := by
  -- Proof comment: the auxiliary mass is the integral of the nonnegative Gaussian-recovery
  -- kernel against the finite exact-root Lévy measure.
  rw [exactRootApproxAuxFiniteMeasure_charFun_zero_eq_integral_local]
  simp only [Complex.ofReal_re]
  exact integral_nonneg fun x ↦ gaussianRecoveryKernel_nonneg x

/-- Helper for Theorem 16.17: for a fixed complex number `w`, the scaled exponential increment
`n (exp (w / n) - 1)` converges to `w`. -/
private lemma natSuccMulExpDivSubOne_norm_le_local (w : ℂ) (n : ℕ)
    (hsmall : ‖w / ((n + 1 : ℕ) : ℂ)‖ ≤ 1) :
    ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w‖ ≤
      ‖w‖ ^ (2 : ℕ) / (n + 1 : ℝ) := by
  have hn0C : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hn0R : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hrew :
      ((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w =
        ((n + 1 : ℕ) : ℂ) *
          (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1 - w / ((n + 1 : ℕ) : ℂ)) := by
    -- Proof comment: factor the target difference so that the quadratic Taylor remainder estimate
    -- applies directly to `w / (n + 1)`.
    field_simp [hn0C]
  calc
    ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w‖
        =
      ‖((n + 1 : ℕ) : ℂ) *
          (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1 - w / ((n + 1 : ℕ) : ℂ))‖ := by
            rw [hrew]
    _ ≤ ‖((n + 1 : ℕ) : ℂ)‖ * ‖w / ((n + 1 : ℕ) : ℂ)‖ ^ (2 : ℕ) := by
          -- Proof comment: once the argument is small, `exp z - 1 - z` is bounded by `‖z‖²`.
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (Complex.norm_exp_sub_one_sub_id_le hsmall) (norm_nonneg _)
    _ = (n + 1 : ℝ) * (‖w‖ / (n + 1 : ℝ)) ^ (2 : ℕ) := by
          rw [Complex.norm_natCast, norm_div, Complex.norm_natCast]
          norm_num
    _ = ‖w‖ ^ (2 : ℕ) / (n + 1 : ℝ) := by
          field_simp [hn0R]

/-- Helper for Theorem 16.17: for a fixed complex number `w`, the scaled exponential increment
`n (exp (w / n) - 1)` converges to `w`. -/
private lemma natSucc_mul_expDiv_sub_one_tendsto_local (w : ℂ) :
    Tendsto
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1))
      atTop
      (𝓝 w) := by
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w‖ ≤
          ‖w‖ ^ (2 : ℕ) / (n + 1 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (Nat.ceil ‖w‖)] with n hn
    have hsmallNum : ‖w‖ / (n + 1 : ℝ) ≤ 1 := by
      have hwle : ‖w‖ ≤ (n + 1 : ℝ) := by
        calc
          ‖w‖ ≤ (Nat.ceil ‖w‖ : ℝ) := Nat.le_ceil _
          _ ≤ n := by exact_mod_cast hn
          _ ≤ n + 1 := by linarith
      exact
        (div_le_iff₀ (show (0 : ℝ) < n + 1 by positivity)).2
          (by simpa [one_mul] using hwle)
    have hsmall :
        ‖w / ((n + 1 : ℕ) : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast]
      simpa using hsmallNum
    exact natSuccMulExpDivSubOne_norm_le_local w n hsmall
  have hzero :
      Tendsto (fun n : ℕ ↦ ‖w‖ ^ (2 : ℕ) / (n + 1 : ℝ)) atTop (𝓝 0) := by
    have hden :
        Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
      simpa [Nat.cast_add] using
        tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have hinv :
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ‖w‖ ^ (2 : ℕ)) atTop (𝓝 (‖w‖ ^ (2 : ℕ)))).mul
        hinv
  have hdiff :
      Tendsto
        (fun n : ℕ ↦
          ((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w)
        atTop
        (𝓝 0) := by
    have hnorm :
        Tendsto
          (fun n : ℕ ↦
            ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w‖)
          atTop
          (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
        hbound hzero
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  -- Proof comment: the scaled remainder tends to zero, so adding back the constant term `w`
  -- yields the claimed limit.
  simpa [sub_eq_add_neg, add_assoc] using
    (hdiff.add (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ w) atTop (𝓝 w)))

/-- Helper for Theorem 16.17: the scalar exact-root linearization converges uniformly on every
bounded complex ball. -/
private lemma natSucc_mul_expDiv_sub_one_tendstoUniformlyOn_ball_local (R : ℝ) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun w : ℂ ↦
        ((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1))
      (fun w : ℂ ↦ w) atTop (Metric.ball (0 : ℂ) R) := by
  by_cases hR : 0 < R
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hzero :
        Tendsto (fun n : ℕ ↦ R ^ (2 : ℕ) / (n + 1 : ℝ)) atTop (𝓝 0) := by
      have hden :
          Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
        simpa [Nat.cast_add] using
          tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
      have hinv :
          Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hden
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ R ^ (2 : ℕ)) atTop (𝓝 (R ^ (2 : ℕ)))).mul
          hinv
    have hsmallEventually :
        ∀ᶠ n : ℕ in atTop, R ^ (2 : ℕ) / (n + 1 : ℝ) < ε := by
      exact hzero (Iio_mem_nhds hε)
    filter_upwards [Filter.eventually_ge_atTop (Nat.ceil R), hsmallEventually] with n hnR hnε w hw
    have hwR : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hsmallNum : ‖w‖ / (n + 1 : ℝ) ≤ 1 := by
      have hRle : R ≤ (n + 1 : ℝ) := by
        calc
          R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil _
          _ ≤ n := by exact_mod_cast hnR
          _ ≤ n + 1 := by linarith
      exact
        (div_le_iff₀ (show (0 : ℝ) < n + 1 by positivity)).2
          (by simpa [one_mul] using le_trans (le_of_lt hwR) hRle)
    have hsmall :
        ‖w / ((n + 1 : ℕ) : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast]
      simpa using hsmallNum
    have hbound := natSuccMulExpDivSubOne_norm_le_local w n hsmall
    have hboundR :
        ‖w‖ ^ (2 : ℕ) / (n + 1 : ℝ) ≤ R ^ (2 : ℕ) / (n + 1 : ℝ) := by
      have hwRle : ‖w‖ ≤ R := le_of_lt hwR
      have hsq : ‖w‖ ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hR.le] using hwRle
      exact div_le_div_of_nonneg_right hsq (by positivity)
    have hdist :
        dist w (((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1)) =
          ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1) - w‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    exact
      lt_of_le_of_lt
        (hdist ▸ hbound.trans hboundR)
        hnε
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [] with n w hw
    exfalso
    have hposR : 0 < R := by
      exact lt_of_le_of_lt (by simpa using norm_nonneg w) hw
    exact hR hposR

/-- Helper for Theorem 16.17: exact positive-integer roots linearize to the chosen continuous
exponential lift. -/
private lemma exactRootLinearizedLimit_eq_expLift_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    ∀ t : ℝ,
      Tendsto
        (fun n : ℕ ↦
          ((n + 1 : ℕ) : ℂ) * (charFun (μroot (Nat.succPNat n) : Measure ℝ) t - 1))
        atTop
        (𝓝 (Ψ t)) := by
  intro t
  have hcfp :
      ∀ m : ℕ+, IsCFP (fun s : ℝ ↦ charFun (μroot m : Measure ℝ) s) := by
    intro m
    simpa using ProbabilityMeasure.isCFP_charFun (μroot m)
  have hpow :
      ∀ m : ℕ+, ∀ s : ℝ,
        (charFun (μroot m : Measure ℝ) s) ^ (m : ℕ) = charFun (μ : Measure ℝ) s := by
    intro m s
    calc
      (charFun (μroot m : Measure ℝ) s) ^ (m : ℕ)
          = charFun ((μroot m ^ (m : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) s := by
              simpa using
                (congrArg (fun f : ℝ → ℂ ↦ f s)
                  (ProbabilityMeasure.charFun_pow (μroot m) (m : ℕ))).symm
      _ = charFun (μ : Measure ℝ) s := by
            simpa using
              congrArg (fun ν : ProbabilityMeasure ℝ ↦ charFun (ν : Measure ℝ) s) (hroot m)
  refine Tendsto.congr' ?_ (natSucc_mul_expDiv_sub_one_tendsto_local (Ψ t))
  exact Filter.Eventually.of_forall fun n ↦ by
    have hrootChar :
        charFun (μroot (Nat.succPNat n) : Measure ℝ) t =
          Complex.exp (Ψ t / (((n + 1 : ℕ) : ℂ))) := by
      simpa [Nat.succPNat_coe] using
        exactRoot_eq_expDivLift
          (φ := charFun (μ : Measure ℝ))
          (φs := fun m s ↦ charFun (μroot m : Measure ℝ) s)
          hcfp hpow hΨ0 hΨexp (Nat.succPNat n) t
    simpa [hrootChar]

/-- Helper for Theorem 16.17: the exact-root compound-Poisson approximant exponent already has
the fixed `Ψ`-normal form `((n + 1) * (exp (Ψ / (n + 1)) - 1))`. -/
private lemma exactRootApproxExponent_eq_expLiftIncrement_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (n : ℕ) (t : ℝ) :
    levyKhinchinExponent (exactRootApproxTriple μroot n) t =
      ((n + 1 : ℕ) : ℂ) * (Complex.exp (Ψ t / (((n + 1 : ℕ) : ℂ))) - 1) := by
  let μn : ProbabilityMeasure ℝ := compoundPoissonMeasure (exactRootApproxIntensity μroot n)
  let Λ : C(ℝ, ℂ) :=
    ⟨fun s : ℝ ↦ ((n + 1 : ℕ) : ℂ) * (charFun (μroot (Nat.succPNat n) : Measure ℝ) s - 1), by
      -- Proof comment: the root characteristic function is continuous, so the linearized lift is
      -- continuous as well.
      simpa using
        ((MeasureTheory.continuous_charFun : Continuous
          (charFun (μroot (Nat.succPNat n) : Measure ℝ))).sub continuous_const).const_mul
          ((n + 1 : ℕ) : ℂ)⟩
  obtain ⟨Lift, hLift, hLiftUnique⟩ :=
    existsUniqueContinuousExpLift
      (MeasureTheory.continuous_charFun : Continuous (charFun (μn : Measure ℝ)))
      (by
        intro s
        rw [(exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).charFun_eq_exp s]
        exact Complex.exp_ne_zero _)
      (by simpa [μn] using (MeasureTheory.charFun_zero (μ := (μn : Measure ℝ))))
  have hExponentLift :
      (⟨levyKhinchinExponent (exactRootApproxTriple μroot n),
          continuousLevyKhinchinExponentLocal
            (exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).isCanonicalTriple⟩ :
        C(ℝ, ℂ)) = Lift := by
    apply hLiftUnique
    constructor
    · -- Proof comment: the exact-root approximant exponent keeps the standard normalization.
      simpa using levyKhinchinExponent_zero (exactRootApproxTriple μroot n)
    · intro s
      -- Proof comment: the approximant triple represents `μn` by construction.
      simpa [μn] using
        ((exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).charFun_eq_exp s).symm
  have hLinearizedLift : Λ = Lift := by
    apply hLiftUnique
    constructor
    · -- Proof comment: the explicit linearized lift also vanishes at the origin.
      simp [Λ]
    · intro s
      let νFinite : FiniteMeasure ℝ :=
        (((((n + 1 : ℕ) : NNReal) • (μroot (Nat.succPNat n)).toFiniteMeasure) :
          FiniteMeasure ℝ))
      have hμnEq :
          μn = compoundPoissonMeasure νFinite := by
        -- Proof comment: removing the zero atom from the jump intensity does not change the
        -- compound-Poisson law.
        simpa [μn, exactRootApproxIntensity, νFinite] using
          (compoundPoissonMeasure_ignoreZeroAtom νFinite)
      calc
        Complex.exp (Λ s)
            = charFun (compoundPoissonMeasure νFinite : Measure ℝ) s := by
                simpa [Λ, νFinite] using
                  (charFun_compoundPoissonMeasure_natSmulProbability
                    (μroot (Nat.succPNat n)) (n + 1) s).symm
        _ = charFun (μn : Measure ℝ) s := by simpa [hμnEq]
  have hRootChar :
      charFun (μroot (Nat.succPNat n) : Measure ℝ) t =
        Complex.exp (Ψ t / (((n + 1 : ℕ) : ℂ))) := by
    have hcfp :
        ∀ m : ℕ+, IsCFP (fun s : ℝ ↦ charFun (μroot m : Measure ℝ) s) := by
      intro m
      simpa using ProbabilityMeasure.isCFP_charFun (μroot m)
    have hpow :
        ∀ m : ℕ+, ∀ s : ℝ,
          (charFun (μroot m : Measure ℝ) s) ^ (m : ℕ) = charFun (μ : Measure ℝ) s := by
      intro m s
      calc
        (charFun (μroot m : Measure ℝ) s) ^ (m : ℕ)
            = charFun ((μroot m ^ (m : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) s := by
                simpa using
                  (congrArg (fun f : ℝ → ℂ ↦ f s)
                    (ProbabilityMeasure.charFun_pow (μroot m) (m : ℕ))).symm
        _ = charFun (μ : Measure ℝ) s := by
              simpa using
                congrArg (fun ν : ProbabilityMeasure ℝ ↦ charFun (ν : Measure ℝ) s) (hroot m)
    -- Proof comment: the exact-root lift theorem rewrites the root characteristic function into
    -- the fixed logarithmic-lift spelling `exp (Ψ / (n + 1))`.
    simpa [Nat.succPNat_coe] using
      exactRoot_eq_expDivLift
        (φ := charFun (μ : Measure ℝ))
        (φs := fun m s ↦ charFun (μroot m : Measure ℝ) s)
        hcfp hpow hΨ0 hΨexp (Nat.succPNat n) t
  have hLiftEq :
      levyKhinchinExponent (exactRootApproxTriple μroot n) t =
        ((n + 1 : ℕ) : ℂ) * (charFun (μroot (Nat.succPNat n) : Measure ℝ) t - 1) := by
    -- Proof comment: both formulas are the unique normalized continuous lifts of the same
    -- exact-root approximant characteristic function.
    exact congrArg (fun f : C(ℝ, ℂ) ↦ f t) (hExponentLift.trans hLinearizedLift.symm)
  calc
    levyKhinchinExponent (exactRootApproxTriple μroot n) t
        = ((n + 1 : ℕ) : ℂ) * (charFun (μroot (Nat.succPNat n) : Measure ℝ) t - 1) := hLiftEq
    _ = ((n + 1 : ℕ) : ℂ) * (Complex.exp (Ψ t / (((n + 1 : ℕ) : ℂ))) - 1) := by
          rw [hRootChar]

/-- Helper for Theorem 16.17: the exact-root compound-Poisson approximant exponents converge to
the retained logarithmic lift `Ψ`. -/
private lemma compoundPoissonApproxExponent_tendsto_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    ∀ t : ℝ,
      Tendsto
        (fun n : ℕ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) t)
        atTop
        (𝓝 (Ψ t)) := by
  intro t
  refine Tendsto.congr' ?_ (natSucc_mul_expDiv_sub_one_tendsto_local (Ψ t))
  exact Filter.Eventually.of_forall fun n ↦ by
    -- Proof comment: the exact-root approximant exponent is already in the fixed
    -- `exp (Ψ / (n + 1))` normal form.
    simpa [exactRootApproxExponent_eq_expLiftIncrement_local
      (μroot := μroot) (μ := μ) hroot (Ψ := Ψ) hΨ0 hΨexp n t]

/-- Helper for Theorem 16.17: the exact-root compound-Poisson approximant exponents converge
uniformly on every compact interval to the retained lift `Ψ`. -/
private lemma exactRootApproxExponent_tendstoUniformlyOn_interval_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (a b : ℝ) :
    TendstoUniformlyOn
      (fun n t ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) t)
      (fun t ↦ Ψ t) atTop (Set.Icc a b) := by
  rcases
      (isCompact_Icc.image Ψ.continuous).isBounded.subset_ball (0 : ℂ) with
    ⟨R, hR⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hball :
      ∀ᶠ n : ℕ in atTop,
        ∀ w ∈ Metric.ball (0 : ℂ) R,
          dist w (((n + 1 : ℕ) : ℂ) * (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1)) < ε := by
    exact
      (Metric.tendstoUniformlyOn_iff.1
        (natSucc_mul_expDiv_sub_one_tendstoUniformlyOn_ball_local R)) ε hε
  filter_upwards [hball] with n hn t ht
  have hΨt : Ψ t ∈ Metric.ball (0 : ℂ) R := hR ⟨t, ht, rfl⟩
  -- Proof comment: on the interval, the exact-root exponent is exactly the scalar linearization
  -- evaluated at the bounded lift value `Ψ t`.
  simpa [exactRootApproxExponent_eq_expLiftIncrement_local
    (μroot := μroot) (μ := μ) hroot (Ψ := Ψ) hΨ0 hΨexp n t] using hn (Ψ t) hΨt

/-- Helper for Theorem 16.17: the exact-root exponent is already the raw finite-jump Fourier
integral against the punctured intensity. -/
private lemma exactRootApproxExponent_eq_rawKernelIntegral_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    levyKhinchinExponent (exactRootApproxTriple μroot n) t =
      ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1)
        ∂(exactRootApproxTriple μroot n).ν := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  letI : IsFiniteMeasure ν := by
    change IsFiniteMeasure (((exactRootApproxIntensity μroot n : FiniteMeasure ℝ) : Measure ℝ))
    infer_instance
  have hkernel :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
    integrable_compoundPoissonKernel_of_isFiniteMeasure_local ν t
  have hcorr :
      Integrable
        (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ν :=
    integrable_complexCenteringCorrection_of_isFiniteMeasure_local ν t
  have hsplit :
      ∫ x : ℝ,
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂ν =
        ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
          ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν := by
    -- Proof comment: split the exact-root kernel into its raw oscillatory part and the centering
    -- correction so the chosen drift can cancel it.
    rw [integral_sub hkernel hcorr]
  -- Proof comment: the exact-root triple has `σ² = 0`, and its drift is precisely the integral
  -- of the centering cutoff against the punctured intensity.
  calc
    levyKhinchinExponent (exactRootApproxTriple μroot n) t
        =
          ((((∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) * t : ℝ) : ℂ) * Complex.I) +
            ∫ x : ℝ,
              (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂ν := by
            simp [exactRootApproxTriple, ν, levyKhinchinExponent, levyKhinchinExponentWithCentering,
              mul_comm]
    _ =
          ((((∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) * t : ℝ) : ℂ) * Complex.I) +
            (∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
              ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν) := by
            rw [hsplit]
    _ =
          ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I) +
            (∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
              ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I)) := by
            rw [integral_complexCenteringCorrection_eq_local]
            congr 1
            ring
    _ = ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν := by
          ring

/-- Helper for Theorem 16.17: each exact-root exponent splits into the sin-centered jump kernel
plus one explicit linear residual term. -/
private lemma exactRootApproxExponent_eq_sinCenteredKernelIntegral_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    levyKhinchinExponent (exactRootApproxTriple μroot n) t =
      ((((t * ∫ x : ℝ, Real.sin x ∂(exactRootApproxTriple μroot n).ν : ℝ) : ℂ)) * Complex.I) +
        ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
          (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ∂(exactRootApproxTriple μroot n).ν := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  letI : IsFiniteMeasure ν := by
    change IsFiniteMeasure (((exactRootApproxIntensity μroot n : FiniteMeasure ℝ) : Measure ℝ))
    infer_instance
  have hkernel :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
    integrable_compoundPoissonKernel_of_isFiniteMeasure_local ν t
  have hsin :
      Integrable (fun x : ℝ ↦ (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ν :=
    integrable_complexSinCorrection_of_isFiniteMeasure_local ν t
  have hsplit :
      ∫ x : ℝ,
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ∂ν =
        ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
          ∫ x : ℝ, (((t * Real.sin x : ℝ) : ℂ) * Complex.I) ∂ν := by
    -- Proof comment: split the raw exact-root kernel into the sin-centered kernel plus the
    -- bounded linear correction.
    rw [integral_sub hkernel hsin]
  calc
    levyKhinchinExponent (exactRootApproxTriple μroot n) t
        = ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν := by
            simpa [ν] using exactRootApproxExponent_eq_rawKernelIntegral_local μroot n t
    _ =
        ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ∂ν +
          ∫ x : ℝ, (((t * Real.sin x : ℝ) : ℂ) * Complex.I) ∂ν := by
            rw [hsplit]
            ring
    _ =
        ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ∂ν +
          ((((t * ∫ x : ℝ, Real.sin x ∂ν : ℝ) : ℂ)) * Complex.I) := by
            rw [integral_complexSinCorrection_eq_local]
    _ =
        ((((t * ∫ x : ℝ, Real.sin x ∂ν : ℝ) : ℂ)) * Complex.I) +
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              (((t * Real.sin x : ℝ) : ℂ) * Complex.I)) ∂ν := by
            ring

/-- Helper for Theorem 16.17: the shifted exact-root exponent is Gaussian-integrable because the
raw finite-jump Fourier kernel stays uniformly bounded by `2`. -/
private lemma integrable_exactRootApproxExponent_shift_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    Integrable
      (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
      (gaussianReal 0 1) := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  letI : IsFiniteMeasure ν := by
    change IsFiniteMeasure (((exactRootApproxIntensity μroot n : FiniteMeasure ℝ) : Measure ℝ))
    infer_instance
  have hconst :
      Integrable (fun _ : ℝ ↦ ∫ x : ℝ, (2 : ℝ) ∂ν) (gaussianReal 0 1) :=
    integrable_const _
  refine hconst.mono' ?_ ?_
  · -- Proof comment: continuity of the exact-root exponent makes the shifted Gaussian integrand
    -- strongly measurable.
    exact
      ((continuousLevyKhinchinExponentLocal
        (exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).isCanonicalTriple).comp
        (continuous_const.add continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun s ↦ by
      have hkernel :
          Integrable (fun x : ℝ ↦ Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
        integrable_compoundPoissonKernel_of_isFiniteMeasure_local ν (t + s)
      calc
        ‖levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)‖
            =
              ‖∫ x : ℝ, (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν‖ := by
                rw [exactRootApproxExponent_eq_rawKernelIntegral_local]
        _ ≤ ∫ x : ℝ, ‖Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1‖ ∂ν := by
              simpa using
                (norm_integral_le_integral_norm
                  (f := fun x : ℝ ↦ Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1))
        _ ≤ ∫ x : ℝ, (2 : ℝ) ∂ν := by
              exact
                integral_mono_ae hkernel.norm (integrable_const (2 : ℝ))
                  (Filter.Eventually.of_forall fun x ↦
                    norm_exp_sub_one_mul_I_le_two_local (t + s) x)

/-- Helper for Theorem 16.17: truncating the Gaussian average to `[-R, R]` leaves exactly the
complementary Gaussian tail of the exact-root exponent. -/
private lemma exactRootApproxAuxSmoothedTail_eq_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (R t : ℝ) :
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t -
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ∫ s in Set.Icc (-R) R, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1) =
      - ∫ s in (Set.Icc (-R) R)ᶜ,
          levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) ∂gaussianReal 0 1 := by
  let S : Set ℝ := Set.Icc (-R) R
  have hS : MeasurableSet S := by
    simp [S]
  have hInt := integrable_exactRootApproxExponent_shift_local μroot n t
  -- Proof comment: split the full Gaussian average into its compact window and the complementary
  -- tail.
  calc
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t -
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ∫ s in Set.Icc (-R) R, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1)
        =
          - (∫ s : ℝ, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
              ∂gaussianReal 0 1 -
            ∫ s in S, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
              ∂gaussianReal 0 1) := by
            rw [exactRootApproxAuxFiniteMeasure_charFun_eq_smoothedExponent_local]
            ring
    _ =
          - ∫ s in Sᶜ, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1 := by
            rw [MeasureTheory.setIntegral_compl (μ := gaussianReal 0 1) (s := S) (f := fun s : ℝ ↦
              levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) hS hInt]

/-- Helper for Theorem 16.17: the Gaussian tail error can already be rewritten using the raw
finite-jump Fourier kernel of the exact-root approximant. -/
private lemma exactRootApproxAuxSmoothedTail_eq_rawKernelTail_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (R t : ℝ) :
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t -
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ∫ s in Set.Icc (-R) R, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1) =
      - ∫ s in (Set.Icc (-R) R)ᶜ,
          ∫ x : ℝ, (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1)
            ∂(exactRootApproxTriple μroot n).ν ∂gaussianReal 0 1 := by
  let S : Set ℝ := Set.Icc (-R) R
  -- Proof comment: after the tail split, each exponent value is rewritten by the raw oscillatory
  -- integral for the exact-root triple.
  calc
    charFun ((exactRootApproxAuxFiniteMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t -
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ∫ s in Set.Icc (-R) R, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1)
        =
          - ∫ s in Sᶜ, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1 :=
      exactRootApproxAuxSmoothedTail_eq_local μroot n R t
    _ =
          - ∫ s in Sᶜ,
              ∫ x : ℝ, (Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) - 1)
                ∂(exactRootApproxTriple μroot n).ν ∂gaussianReal 0 1 := by
            congr 1
            refine integral_congr_ae <| Filter.Eventually.of_forall fun s ↦ ?_
            simpa using
              (exactRootApproxExponent_eq_rawKernelIntegral_local
                (μroot := μroot) (n := n) (t := t + s))

/-- Helper for Theorem 16.17: on every compact Gaussian truncation window, the exact-root
smoothed exponents converge to the corresponding truncated Gaussian average of `Ψ`. -/
private lemma exactRootApproxAuxSmoothedTrunc_tendsto_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (R t : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ∫ s in Set.Icc (-R) R,
            levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) ∂gaussianReal 0 1)
      atTop
      (𝓝
        (Ψ t - ∫ s in Set.Icc (-R) R, Ψ (t + s) ∂gaussianReal 0 1)) := by
  let S : Set ℝ := Set.Icc (-R) R
  have hUniform :
      ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ s ∈ S,
            dist (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) (Ψ (t + s)) <
              ε := by
    intro ε hε
    have hInterval :=
      (Metric.tendstoUniformlyOn_iff.1
        (exactRootApproxExponent_tendstoUniformlyOn_interval_local
          μroot hroot hΨ0 hΨexp (t - R) (t + R))) ε hε
    filter_upwards [hInterval] with n hn s hs
    have hts : t + s ∈ Set.Icc (t - R) (t + R) := by
      constructor <;> linarith [hs.1, hs.2]
    simpa [dist_comm] using hn (t + s) hts
  have hIntegrableApprox :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
          S (gaussianReal 0 1) := by
    intro n
    have hcont :
        Continuous (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) := by
      -- Proof comment: the exact-root exponent is continuous, and the truncation window only
      -- shifts the frequency by the fixed base point `t`.
      exact
        (continuousLevyKhinchinExponentLocal
          (exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).isCanonicalTriple).comp
          (continuous_const.add continuous_id)
    simpa [S] using hcont.integrableOn_Icc (μ := gaussianReal 0 1) (a := -R) (b := R)
  have hIntegrableLimit :
      IntegrableOn (fun s : ℝ ↦ Ψ (t + s)) S (gaussianReal 0 1) := by
    have hcont : Continuous (fun s : ℝ ↦ Ψ (t + s)) :=
      Ψ.continuous.comp (continuous_const.add continuous_id)
    simpa [S] using hcont.integrableOn_Icc (μ := gaussianReal 0 1) (a := -R) (b := R)
  have hMeasureReal_le_one :
      (gaussianReal 0 1 : Measure ℝ).real S ≤ 1 := by
    have hRealUniv : (gaussianReal 0 1 : Measure ℝ).real Set.univ = 1 := by
      rw [Measure.real_def]
      simp
    calc
      (gaussianReal 0 1 : Measure ℝ).real S ≤ (gaussianReal 0 1 : Measure ℝ).real Set.univ := by
        exact measureReal_mono (Set.subset_univ S)
      _ = 1 := hRealUniv
  have hIntegral :
      Tendsto
        (fun n : ℕ ↦
          ∫ s in S, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
            ∂gaussianReal 0 1)
        atTop
        (𝓝 (∫ s in S, Ψ (t + s) ∂gaussianReal 0 1)) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    have hHalf : 0 < ε / 2 := by positivity
    filter_upwards [hUniform (ε / 2) hHalf] with n hn
    have hDistEq :
        dist
            (∫ s in S, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
              ∂gaussianReal 0 1)
            (∫ s in S, Ψ (t + s) ∂gaussianReal 0 1) =
          ‖∫ s in S,
              (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) - Ψ (t + s))
              ∂gaussianReal 0 1‖ := by
      -- Proof comment: compare the two truncated Gaussian averages by integrating their pointwise
      -- difference over the fixed window.
      rw [dist_eq_norm, ← integral_sub (hIntegrableApprox n) hIntegrableLimit]
    have hNormLe :
        ‖∫ s in S,
            (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) - Ψ (t + s))
            ∂gaussianReal 0 1‖ ≤
          (ε / 2) * (gaussianReal 0 1 : Measure ℝ).real S := by
      refine norm_setIntegral_le_of_norm_le_const ?_ ?_
      · simpa [S] using measure_lt_top (μ := (gaussianReal 0 1 : Measure ℝ)) S
      · intro s hs
        simpa [dist_eq_norm] using le_of_lt (hn s hs)
    have hHalfMulLt :
        (ε / 2) * (gaussianReal 0 1 : Measure ℝ).real S < ε := by
      have hHalfNonneg : 0 ≤ ε / 2 := by linarith
      have hHalfMulLe : (ε / 2) * (gaussianReal 0 1 : Measure ℝ).real S ≤ ε / 2 := by
        calc
          (ε / 2) * (gaussianReal 0 1 : Measure ℝ).real S ≤ (ε / 2) * 1 := by
            exact mul_le_mul_of_nonneg_left hMeasureReal_le_one hHalfNonneg
          _ = ε / 2 := by ring
      have hHalfLt : ε / 2 < ε := by linarith
      exact lt_of_le_of_lt hHalfMulLe hHalfLt
    exact lt_of_le_of_lt (hDistEq ▸ hNormLe) hHalfMulLt
  -- Proof comment: the exact-root exponent at `t` converges directly to `Ψ t`, and the
  -- truncated Gaussian averages converge separately on the fixed compact window.
  exact
    (compoundPoissonApproxExponent_tendsto_local μroot hroot hΨ0 hΨexp t).sub hIntegral

/-- Helper for Theorem 16.17: the compact-average kernel appearing in the uniqueness and
existence argument. -/
private def compactAverageKernel (x : ℝ) : ℝ :=
  1 - Real.sinc x

/-- Helper for Theorem 16.17: the compact-average kernel is measurable. -/
private lemma measurable_compactAverageKernel :
    Measurable compactAverageKernel := by
  -- Proof comment: the kernel is the difference between the constant function `1` and `sinc`.
  simpa [compactAverageKernel] using measurable_const.sub Real.measurable_sinc

/-- Helper for Theorem 16.17: the compact-average kernel is continuous. -/
private lemma continuous_compactAverageKernel :
    Continuous compactAverageKernel := by
  -- Proof comment: continuity follows immediately from continuity of `Real.sinc`.
  simpa [compactAverageKernel] using continuous_const.sub Real.continuous_sinc

/-- Helper for Theorem 16.17: the compact-average kernel vanishes at the origin. -/
private lemma compactAverageKernel_zero :
    compactAverageKernel 0 = 0 := by
  -- Proof comment: `sinc 0 = 1`, so the compact-average correction disappears at `0`.
  simp [compactAverageKernel]

/-- Helper for Theorem 16.17: the compact-average kernel is nonnegative. -/
private lemma compactAverageKernel_nonneg (x : ℝ) :
    0 ≤ compactAverageKernel x := by
  -- Proof comment: `sinc x ≤ 1` everywhere, so subtracting it from `1` stays nonnegative.
  dsimp [compactAverageKernel]
  linarith [Real.sinc_le_one x]

/-- Helper for Theorem 16.17: away from `0`, the compact-average kernel is strictly positive. -/
private lemma compactAverageKernel_pos_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    0 < compactAverageKernel x := by
  have hxAbs : 0 < |x| := abs_pos.mpr hx
  have hsincAbsLtOne : |Real.sinc x| < 1 := by
    rw [Real.sinc_of_ne_zero hx, abs_div]
    exact (div_lt_iff₀ hxAbs).2 (by simpa using Real.abs_sin_lt_abs hx)
  have hsincLtOne : Real.sinc x < 1 := lt_of_le_of_lt (le_abs_self _) hsincAbsLtOne
  -- Proof comment: strict inequality `|sinc x| < 1` away from `0` upgrades the nonnegative
  -- kernel to a strictly positive one.
  dsimp [compactAverageKernel]
  linarith

/-- Helper for Theorem 16.17: the compact-average kernel is bounded above by `2`. -/
private lemma compactAverageKernel_le_two (x : ℝ) :
    compactAverageKernel x ≤ 2 := by
  -- Proof comment: `sinc x ≥ -1`, so `1 - sinc x` is at most `2`.
  dsimp [compactAverageKernel]
  linarith [Real.neg_one_le_sinc x]

/-- Helper for Theorem 16.17: on the punctured restriction `η.restrict ({0}ᶜ)`, the
compact-average kernel never vanishes. -/
private lemma compactAverageKernel_ae_ne_zero_restrict_compl_singleton
    (η : Measure ℝ) :
    ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), compactAverageKernel x ≠ 0 := by
  rw [ae_restrict_iff' ((measurableSet_singleton (0 : ℝ)).compl)]
  filter_upwards with x hx
  -- Proof comment: removing the origin removes the only zero of `compactAverageKernel`.
  exact ne_of_gt (compactAverageKernel_pos_of_ne_zero (by simpa using hx))

/-- Helper for Theorem 16.17: the ENNReal compact-average density is finite everywhere. -/
private lemma compactAverageKernel_ae_ne_top {ν : Measure ℝ} :
    ∀ᵐ x ∂ν, (ENNReal.ofReal (compactAverageKernel x)) ≠ ⊤ := by
  -- Proof comment: `ENNReal.ofReal` is finite on every real input.
  filter_upwards with x
  simp

/-- Helper for Theorem 16.17: inverting the compact-average density on the punctured restriction
recovers the original punctured measure. -/
private lemma withDensity_compactAverageKernel_inv_same_restrict_compl_singleton
    (η : Measure ℝ) :
    (((η.restrict ({0}ᶜ : Set ℝ)).withDensity
        (fun x ↦ ENNReal.ofReal (compactAverageKernel x))).withDensity
      (fun x ↦ (ENNReal.ofReal (compactAverageKernel x))⁻¹)) =
      η.restrict ({0}ᶜ : Set ℝ) := by
  let f : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (compactAverageKernel x)
  have hf_meas : Measurable f := measurable_compactAverageKernel.ennreal_ofReal
  have hf_ne_zero :
      ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), f x ≠ 0 := by
    filter_upwards [compactAverageKernel_ae_ne_zero_restrict_compl_singleton η] with x hx
    have hpos : 0 < compactAverageKernel x :=
      lt_of_le_of_ne (compactAverageKernel_nonneg x) (by simpa [eq_comm] using hx)
    simpa [f, ENNReal.ofReal_eq_zero, not_le_of_gt hpos]
  have hf_ne_top :
      ∀ᵐ x ∂η.restrict ({0}ᶜ : Set ℝ), f x ≠ (⊤ : ENNReal) := by
    simpa [f] using compactAverageKernel_ae_ne_top (ν := η.restrict ({0}ᶜ : Set ℝ))
  -- Proof comment: weighting by the compact-average kernel and then by its inverse cancels on
  -- the punctured restriction where the density never vanishes.
  simpa [f] using MeasureTheory.withDensity_inv_same hf_meas hf_ne_zero hf_ne_top

/-- Helper for Theorem 16.17: recover the punctured jump measure of a compact-average auxiliary
finite measure by inverting the compact-average density away from `0`. -/
private noncomputable def compactAverageRecoveredJumpMeasure_local
    (η : FiniteMeasure ℝ) : Measure ℝ :=
  (((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)).withDensity
    (fun x ↦ (ENNReal.ofReal (compactAverageKernel x))⁻¹))

/-- Helper for Theorem 16.17: weighting the recovered compact-average jump measure by the kernel
restores the punctured auxiliary measure. -/
private lemma compactAverageRecoveredJumpMeasure_weighted_eq_restrict_compl_local
    (η : FiniteMeasure ℝ) :
    (compactAverageRecoveredJumpMeasure_local η).withDensity
      (fun x ↦ ENNReal.ofReal (compactAverageKernel x)) =
      ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) := by
  let μ : Measure ℝ := ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ))
  let f : ℝ → ENNReal := fun x ↦ (ENNReal.ofReal (compactAverageKernel x))⁻¹
  let g : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (compactAverageKernel x)
  have hf : Measurable f := measurable_compactAverageKernel.ennreal_ofReal.inv
  have hg : Measurable g := measurable_compactAverageKernel.ennreal_ofReal
  have hfg :
      f * g =ᵐ[μ] 1 := by
    filter_upwards [compactAverageKernel_ae_ne_zero_restrict_compl_singleton (η : Measure ℝ),
      compactAverageKernel_ae_ne_top (ν := μ)] with x hx0 hxtop
    have hpos : 0 < compactAverageKernel x :=
      lt_of_le_of_ne (compactAverageKernel_nonneg x) (by simpa [eq_comm] using hx0)
    have hx0' : ENNReal.ofReal (compactAverageKernel x) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le_of_gt hpos]
    change
      ((ENNReal.ofReal (compactAverageKernel x))⁻¹ *
        ENNReal.ofReal (compactAverageKernel x) = 1)
    exact ENNReal.inv_mul_cancel hx0' hxtop
  -- Proof comment: on `{0}ᶜ`, the compact-average kernel is strictly positive and finite, so
  -- applying `withDensity` by the inverse density and then by the original density is the identity.
  calc
    (compactAverageRecoveredJumpMeasure_local η).withDensity
        (fun x ↦ ENNReal.ofReal (compactAverageKernel x))
        = (μ.withDensity f).withDensity g := by
            rfl
    _ = μ.withDensity (f * g) := by
          symm
          exact MeasureTheory.withDensity_mul (μ := μ) hf hg
    _ = μ.withDensity 1 := by
          exact MeasureTheory.withDensity_congr_ae hfg
    _ = μ := by
          rw [MeasureTheory.withDensity_one]

/-- Helper for Theorem 16.17: the compact-average auxiliary finite measure splits into its atom
at `0` and the weighted punctured recovered jump measure. -/
private lemma compactAverageRecoveredJumpMeasure_decomposition_local
    (η : FiniteMeasure ℝ) :
    (η : Measure ℝ) =
      ((η : Measure ℝ) ({0} : Set ℝ)) • Measure.dirac 0 +
        (compactAverageRecoveredJumpMeasure_local η).withDensity
          (fun x ↦ ENNReal.ofReal (compactAverageKernel x)) := by
  -- Proof comment: split `η` into its singleton and punctured restrictions, then rewrite the
  -- punctured part through the recovered compact-average jump measure.
  calc
    (η : Measure ℝ)
        = ((η : Measure ℝ).restrict ({0} : Set ℝ)) +
            ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) := by
              symm
              simpa using
                (Measure.restrict_add_restrict_compl
                  (μ := (η : Measure ℝ)) (measurableSet_singleton (0 : ℝ)))
    _ = ((η : Measure ℝ) ({0} : Set ℝ)) • Measure.dirac 0 +
          ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) := by
            rw [Measure.restrict_singleton]
    _ = ((η : Measure ℝ) ({0} : Set ℝ)) • Measure.dirac 0 +
          (compactAverageRecoveredJumpMeasure_local η).withDensity
            (fun x ↦ ENNReal.ofReal (compactAverageKernel x)) := by
            rw [compactAverageRecoveredJumpMeasure_weighted_eq_restrict_compl_local]

/-- Helper for Theorem 16.17: the compact-average correction of a continuous lift is again
continuous. -/
private lemma continuous_compactAverageExpLift_local
    (Ψ : C(ℝ, ℂ)) :
    Continuous fun t : ℝ ↦
      Ψ t - ((1 / 2 : ℂ) * ∫ s in (-1 : ℝ)..1, Ψ (t + s)) := by
  have hIntegral :
      Continuous fun t : ℝ ↦ ∫ s in (-1 : ℝ)..1, Ψ (t + s) := by
    -- Proof comment: the integrand `(t,s) ↦ Ψ (t + s)` is jointly continuous, so the compact
    -- interval integral depends continuously on the parameter `t`.
    have hUncurry : Continuous (Function.uncurry fun t s : ℝ ↦ Ψ (t + s)) := by
      simpa [Function.uncurry] using Ψ.continuous.comp (continuous_fst.add continuous_snd)
    simpa [Function.uncurry] using
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) (f := fun t s : ℝ ↦ Ψ (t + s)) hUncurry (-1 : ℝ) 1)
  -- Proof comment: subtract the continuous compact-average correction from the original lift.
  simpa using Ψ.continuous.sub (hIntegral.const_mul (1 / 2 : ℂ))

/-- Helper for Theorem 16.17: compact averaging preserves continuity of the retained logarithmic
lift. -/
private noncomputable def compactAverageExpLift (Ψ : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t : ℝ ↦ Ψ t - ((1 / 2 : ℂ) * ∫ s in (-1 : ℝ)..1, Ψ (t + s)),
    continuous_compactAverageExpLift_local Ψ⟩

/-- Helper for Theorem 16.17: the chosen continuous exponential lift has nonpositive real part,
because it exponentiates to a characteristic function. -/
private lemma continuousExpLift_re_nonpos_local
    {μ : ProbabilityMeasure ℝ} {Ψ : C(ℝ, ℂ)}
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    ∀ t : ℝ, Complex.re (Ψ t) ≤ 0 := by
  intro t
  have hnormExp : Real.exp (Complex.re (Ψ t)) = ‖charFun (μ : Measure ℝ) t‖ := by
    simpa [Complex.norm_exp] using congrArg norm (hΨexp t)
  have hnormLe : Real.exp (Complex.re (Ψ t)) ≤ 1 := by
    rw [hnormExp]
    exact MeasureTheory.norm_charFun_le_one (μ := (μ : Measure ℝ)) t
  exact Real.exp_le_one_iff.mp hnormLe

/-- Helper for Theorem 16.17: compact averaging commutes with the exact-root exponent limit on
every fixed frequency. -/
private lemma exactRootApproxCompactAverageExponent_tendsto_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    ∀ t : ℝ,
      Tendsto
        (fun n : ℕ ↦
          levyKhinchinExponent (exactRootApproxTriple μroot n) t -
            ((1 / 2 : ℂ) *
              ∫ s in (-1 : ℝ)..1, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)))
        atTop
        (𝓝 ((compactAverageExpLift Ψ) t)) := by
  intro t
  have hUniform :
      ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ s ∈ Set.Icc (-1 : ℝ) 1,
            dist (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) (Ψ (t + s)) <
              ε := by
    intro ε hε
    have hInterval :=
      (Metric.tendstoUniformlyOn_iff.1
        (exactRootApproxExponent_tendstoUniformlyOn_interval_local
          μroot hroot hΨ0 hΨexp (t - 1) (t + 1))) ε hε
    filter_upwards [hInterval] with n hn s hs
    have hts : t + s ∈ Set.Icc (t - 1) (t + 1) := by
      constructor <;> linarith [hs.1, hs.2]
    simpa [dist_comm] using hn (t + s) hts
  have hIntegrableApprox :
      ∀ n : ℕ,
        IntervalIntegrable
          (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
          volume (-1) 1 := by
    intro n
    have hcont :
        Continuous (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) := by
      -- Proof comment: the exact-root exponent is continuous, and the compact-average window
      -- only shifts the frequency variable by the fixed base point `t`.
      exact
        (continuousLevyKhinchinExponentLocal
          (exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).isCanonicalTriple).comp
          (continuous_const.add continuous_id)
    exact hcont.intervalIntegrable (-1) 1
  have hIntegrableLimit :
      IntervalIntegrable (fun s : ℝ ↦ Ψ (t + s)) volume (-1) 1 := by
    have hcont : Continuous (fun s : ℝ ↦ Ψ (t + s)) :=
      Ψ.continuous.comp (continuous_const.add continuous_id)
    exact hcont.intervalIntegrable (-1) 1
  have hIntegral :
      Tendsto
        (fun n : ℕ ↦
          ∫ s in (-1 : ℝ)..1, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
        atTop
        (𝓝 (∫ s in (-1 : ℝ)..1, Ψ (t + s))) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    have hQuarter : 0 < ε / 4 := by positivity
    filter_upwards [hUniform (ε / 4) hQuarter] with n hn
    have hDistEq :
        dist
            (∫ s in (-1 : ℝ)..1,
              levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
            (∫ s in (-1 : ℝ)..1, Ψ (t + s)) =
          ‖∫ s in (-1 : ℝ)..1,
              (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) - Ψ (t + s))‖ := by
      -- Proof comment: compare the two interval integrals by integrating the pointwise
      -- difference on the fixed window `[-1, 1]`.
      rw [dist_eq_norm, ← intervalIntegral.integral_sub (hIntegrableApprox n) hIntegrableLimit]
    have hNormLe :
        ‖∫ s in (-1 : ℝ)..1,
            (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) - Ψ (t + s))‖ ≤
          (ε / 4) * |(1 : ℝ) - (-1 : ℝ)| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro s hs
      have hsIoc : s ∈ Set.Ioc (-1 : ℝ) 1 := by
        simpa [Set.uIoc, min_eq_left (show (-1 : ℝ) ≤ 1 by norm_num),
          max_eq_right (show (-1 : ℝ) ≤ 1 by norm_num)] using hs
      have hs' : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hsIoc.1, hsIoc.2⟩
      simpa [dist_eq_norm] using le_of_lt (hn s hs')
    have hQuarterMulLt : (ε / 4) * |(1 : ℝ) - (-1 : ℝ)| < ε := by
      norm_num
      linarith
    exact lt_of_le_of_lt (hDistEq ▸ hNormLe) hQuarterMulLt
  have hScaledIntegral :
      Tendsto
        (fun n : ℕ ↦
          ((1 / 2 : ℂ)) *
            ∫ s in (-1 : ℝ)..1, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
        atTop
        (𝓝 (((1 / 2 : ℂ)) * ∫ s in (-1 : ℝ)..1, Ψ (t + s))) := by
    exact
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 / 2 : ℂ)) atTop (𝓝 (1 / 2 : ℂ))).mul
        hIntegral
  -- Proof comment: the exact-root exponent already converges pointwise to `Ψ t`, and the
  -- compact-average correction converges separately on the fixed interval `[-1, 1]`.
  simpa [compactAverageExpLift] using
    (compoundPoissonApproxExponent_tendsto_local μroot hroot hΨ0 hΨexp t).sub hScaledIntegral

/-- Helper for Theorem 16.17: on the non-Dirac branch, compact averaging leaves strictly positive
mass at the origin. -/
private lemma compactAverageLiftZero_pos_of_notDirac_local
    {μ : ProbabilityMeasure ℝ} {Ψ : C(ℝ, ℂ)}
    (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (hDirac : ¬ ∃ b : ℝ, μ = diracProba b) :
    0 < Complex.re ((compactAverageExpLift Ψ) 0) := by
  let f : ℝ → ℝ := fun s ↦ -Complex.re (Ψ s)
  have hReNonpos : ∀ s : ℝ, Complex.re (Ψ s) ≤ 0 :=
    continuousExpLift_re_nonpos_local hΨexp
  have hfNonneg : ∀ s : ℝ, 0 ≤ f s := by
    intro s
    dsimp [f]
    linarith [hReNonpos s]
  have hfCont : Continuous f := by
    -- Proof comment: `f` is the negative real part of the continuous logarithmic lift.
    simpa [f] using (Complex.continuous_re.comp Ψ.continuous).neg
  have hΨInt : IntervalIntegrable (fun s : ℝ ↦ Ψ s) volume (-1) 1 :=
    Ψ.continuous.intervalIntegrable (-1) 1
  have hfInt : IntervalIntegrable f volume (-1) 1 :=
    hfCont.intervalIntegrable (-1) 1
  have hReFormula :
      Complex.re ((compactAverageExpLift Ψ) 0) =
        (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, f s := by
    -- Proof comment: at `0`, compact averaging is exactly half the interval integral of
    -- `-Re (Ψ s)` because the lift is normalized by `Ψ 0 = 0`.
    have hReFormulaSet :
        Complex.re ((compactAverageExpLift Ψ) 0) =
          (1 / 2 : ℝ) * ∫ s in Set.Ioc (-1 : ℝ) 1, f s := by
      have hReInt :
          (∫ s in Set.Ioc (-1 : ℝ) 1, Ψ s).re =
            ∫ s in Set.Ioc (-1 : ℝ) 1, Complex.re (Ψ s) := by
        simpa using (integral_re hΨInt.1).symm
      rw [compactAverageExpLift]
      simp only [ContinuousMap.coe_mk]
      rw [hΨ0]
      simp only [zero_sub, Complex.neg_re, Complex.mul_re]
      have hZeroShift :
          (∫ x in Set.Ioc (-1 : ℝ) 1, Ψ (0 + x)) = ∫ x in Set.Ioc (-1 : ℝ) 1, Ψ x := by
        simp [zero_add]
      rw [intervalIntegral.integral_of_le (by norm_num), hZeroShift, hReInt]
      simp [f]
      rw [integral_neg]
      ring
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact hReFormulaSet
  have hReNonneg : 0 ≤ Complex.re ((compactAverageExpLift Ψ) 0) := by
    rw [hReFormula]
    refine mul_nonneg (by norm_num) ?_
    exact intervalIntegral.integral_nonneg (by norm_num) fun s _ ↦ hfNonneg s
  by_contra hNotPos
  have hReZero : Complex.re ((compactAverageExpLift Ψ) 0) = 0 := by
    linarith
  have hIntZero : ∫ s in (-1 : ℝ)..1, f s = 0 := by
    rw [hReFormula] at hReZero
    linarith
  have hfZeroOnIoo : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, f s = 0 := by
    intro s hs
    by_contra hsNe
    have hsPos : 0 < f s := lt_of_le_of_ne (hfNonneg s) (Ne.symm hsNe)
    have hsCont : ContinuousAt f s := hfCont.continuousAt
    have hsHalfPos : 0 < f s / 2 := by positivity
    rcases Metric.continuousAt_iff.mp hsCont (f s / 2) hsHalfPos with ⟨δ, hδPos, hδ⟩
    let r : ℝ := min (δ / 2) (min ((s + 1) / 2) ((1 - s) / 2))
    have hrPos : 0 < r := by
      dsimp [r]
      have hsLeftPos : 0 < (s + 1) / 2 := by linarith [hs.1]
      have hsRightPos : 0 < (1 - s) / 2 := by linarith [hs.2]
      refine lt_min ?_ (lt_min hsLeftPos hsRightPos)
      linarith
    have hrLeDelta : r ≤ δ := by
      dsimp [r]
      have hMin : min (δ / 2) (min ((s + 1) / 2) ((1 - s) / 2)) ≤ δ / 2 := min_le_left _ _
      linarith
    have hrLeLeft : r ≤ (s + 1) / 2 := by
      dsimp [r]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hrLeRight : r ≤ (1 - s) / 2 := by
      dsimp [r]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hPosOnSmall : ∀ y ∈ Set.Ioo (s - r) (s + r), 0 < f y := by
      intro y hy
      have hyAbs : |y - s| < r := by
        refine abs_lt.mpr ?_
        constructor <;> linarith [hy.1, hy.2]
      have hyDist : dist y s < δ := by
        simpa [Real.dist_eq, abs_sub_comm] using lt_of_lt_of_le hyAbs hrLeDelta
      have hyClose : |f y - f s| < f s / 2 := by
        simpa [Real.dist_eq] using hδ hyDist
      rcases abs_lt.mp hyClose with ⟨hyLeft, _hyRight⟩
      have hyLower : f s / 2 < f y := by
        linarith
      exact lt_trans hsHalfPos hyLower
    have hSupportSubset :
        Set.Ioo (s - r) (s + r) ⊆ Function.support f ∩ Set.Ioc (-1 : ℝ) 1 := by
      intro y hy
      refine ⟨Function.mem_support.2 (hPosOnSmall y hy).ne', ?_⟩
      constructor
      · linarith [hy.1, hrLeLeft]
      · linarith [hy.2, hrLeRight]
    have hSupportPos : 0 < volume (Function.support f ∩ Set.Ioc (-1 : ℝ) 1) := by
      have hSmallPos : 0 < volume (Set.Ioo (s - r) (s + r)) := by
        rw [Real.volume_Ioo, ENNReal.ofReal_pos]
        linarith
      exact lt_of_lt_of_le hSmallPos (measure_mono hSupportSubset)
    have hIntegralPos : 0 < ∫ x in (-1 : ℝ)..1, f x := by
      rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall hfNonneg) hfInt]
      exact ⟨by norm_num, hSupportPos⟩
    exact hIntegralPos.ne' hIntZero
  let t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 2)
  have htAntitone : Antitone fun k ↦ |t k| := by
    intro m n hmn
    -- Proof comment: the reciprocal sequence `1 / (k + 2)` is decreasing and positive.
    simp only [t]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have hRecip :
        1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / (((m + 1 : ℕ) : ℝ) + 1) :=
      Nat.one_div_le_one_div (Nat.succ_le_succ hmn)
    convert hRecip using 1 <;> norm_num [Nat.cast_add, add_assoc]
  have htZero : Tendsto (fun k ↦ |t k|) atTop (𝓝 0) := by
    -- Proof comment: the reciprocal sequence tends to `0` because its denominator tends to
    -- `+∞`.
    have habs : (fun k ↦ |t k|) = fun k : ℕ ↦ (((k : ℝ) + 2) : ℝ)⁻¹ := by
      funext k
      have hk : 0 ≤ (k : ℝ) + 2 := by positivity
      simp [t, abs_of_nonneg (inv_nonneg.mpr hk)]
    rw [habs]
    have hDen : Tendsto (fun k : ℕ ↦ (k : ℝ) + 2) atTop atTop := by
      simpa using tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hDen
  have htNonzero : ∀ k, t k ≠ 0 := by
    intro k
    have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
    simp [t, hk]
  have hCharUnit : ∀ k, ‖charFun (μ : Measure ℝ) (t k)‖ = 1 := by
    intro k
    have htkPos : 0 < t k := by
      dsimp [t]
      positivity
    have htkLtOne : t k < 1 := by
      dsimp [t]
      have hkPos : 0 < (k : ℝ) + 1 := by positivity
      have hk : 1 < (k : ℝ) + 2 := by linarith
      simpa [one_div] using inv_lt_one_of_one_lt₀ hk
    have htkMem : t k ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor
      · linarith
      · exact htkLtOne
    have hNegReZero : -Complex.re (Ψ (t k)) = 0 := by
      simpa [f] using hfZeroOnIoo (t k) htkMem
    have hReZero : Complex.re (Ψ (t k)) = 0 := by
      linarith
    have hNormExp : ‖Complex.exp (Ψ (t k))‖ = 1 := by
      simpa [Complex.norm_exp, hReZero]
    simpa [hΨexp (t k)] using hNormExp
  obtain ⟨b, hbMeasure⟩ :=
    Measure.eq_dirac_of_charFun_norm_eq_one_along_zero
      (μ := (μ : Measure ℝ)) htAntitone htZero htNonzero hCharUnit
  apply hDirac
  refine ⟨b, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  simpa [MeasureTheory.diracProba] using hbMeasure

local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-- Helper for Theorem 16.17: read the unique coordinate of `ℝ¹` measurably. -/
private lemma measurable_euclidean1ToReal_local :
    Measurable (euclidean1ToReal : E1 → ℝ) := by
  -- Proof comment: `euclidean1ToReal` is evaluation at the sole coordinate of `ℝ¹`.
  simpa [euclidean1ToReal] using
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 1 ↦ ℝ) (0 : Fin 1)).measurable

/-- Helper for Theorem 16.17: continuity at `0` on `ℝ` gives the one-dimensional
`PartiallyContinuousAtZero` condition after transport to `ℝ¹`. -/
private lemma partiallyContinuousAtZero_comp_euclidean1ToReal_local
    {φ : ℝ → ℂ} (hφ0 : ContinuousAt φ 0) :
    PartiallyContinuousAtZero (d := 1) (fun x : E1 ↦ φ (euclidean1ToReal x)) := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  -- Proof comment: in dimension one the unique coordinate axis is exactly the original real
  -- line.
  simpa [euclidean1ToReal, realToEuclidean1] using hφ0

/-- Helper for Theorem 16.17: mapping a one-dimensional Euclidean law back to `ℝ` recovers the
real characteristic function by evaluating at `realToEuclidean1`. -/
private lemma charFun_map_euclidean1ToReal_local
    (μ : ProbabilityMeasure E1) (t : ℝ) :
    charFun
      (μ.map measurable_euclidean1ToReal_local.aemeasurable : Measure ℝ) t =
      charFun (μ : Measure E1) (realToEuclidean1 t) := by
  -- Proof comment: rewrite the pushforward characteristic function via `integral_map`, then
  -- identify the one-dimensional inner product with scalar multiplication by `t`.
  change
    charFun (Measure.map euclidean1ToReal (μ : Measure E1)) t =
      charFun (μ : Measure E1) (realToEuclidean1 t)
  rw [MeasureTheory.charFun_apply_real, MeasureTheory.charFun_apply,
    MeasureTheory.integral_map measurable_euclidean1ToReal_local.aemeasurable (by fun_prop)]
  congr with x
  congr 1
  have hinner :
      inner ℝ x (realToEuclidean1 t) = t * euclidean1ToReal x := by
    simpa [euclidean1ToReal, realToEuclidean1] using
      (EuclideanSpace.inner_single_right (i := (0 : Fin 1)) t x)
  exact congrArg (fun z : ℂ ↦ z * Complex.I) (by exact_mod_cast hinner.symm)

/-- Helper for Theorem 16.17: normalizing a nonzero finite measure scales its characteristic
function by the reciprocal total mass. -/
private lemma charFun_normalize_eq_invMass_local
    (η : FiniteMeasure ℝ) (hη : η ≠ 0) (t : ℝ) :
    charFun (η.normalize : Measure ℝ) t =
      (((η.mass⁻¹ : NNReal) : ℂ)) * charFun ((η : FiniteMeasure ℝ) : Measure ℝ) t := by
  -- Proof comment: rewrite the normalized measure as the reciprocal-mass scalar multiple of the
  -- original finite measure and then move the scalar through the Fourier integral.
  rw [η.toMeasure_normalize_eq_of_nonzero hη, MeasureTheory.charFun_apply_real,
    MeasureTheory.charFun_apply_real]
  change
    ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂
        ((((η.mass⁻¹ : NNReal) : ENNReal) • (η : Measure ℝ))) =
      (((η.mass⁻¹ : NNReal) : ℂ)) *
        ∫ x : ℝ, Complex.exp (((t : ℂ) * x) * Complex.I) ∂(η : Measure ℝ)
  rw [integral_smul_measure]
  rfl

/-- Helper for Theorem 16.17: the characteristic function of a finite measure at `0` is its total
mass. -/
private lemma charFun_finiteMeasure_zero_eq_mass_local (η : FiniteMeasure ℝ) :
    charFun ((η : FiniteMeasure ℝ) : Measure ℝ) 0 = (η.mass : ℂ) := by
  -- Proof comment: `charFun μ 0` is the total mass of `μ`, and for a finite measure that mass is
  -- exactly `η.mass`.
  rw [MeasureTheory.charFun_zero, Measure.real_def]
  change ((((η : Measure ℝ) Set.univ).toReal : ℂ) =
    ((((η : Measure ℝ) Set.univ).toNNReal : ℝ≥0) : ℂ))
  simp [ENNReal.coe_toNNReal_eq_toReal]

/-- Helper for Theorem 16.17: scaling a probability law by a finite mass scales its
characteristic function by the same complex scalar. -/
private lemma charFun_mass_smul_probability_local
    (m : NNReal) (ρ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (((m • ρ.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ)) t =
      (m : ℂ) * charFun (ρ : Measure ℝ) t := by
  -- Proof comment: identify the scaled finite measure with the scalar multiple of the underlying
  -- probability measure and then move the scalar through the Fourier integral.
  rw [MeasureTheory.charFun_apply_real]
  simpa [FiniteMeasure.toMeasure_smul, Algebra.smul_def, MeasureTheory.charFun_apply_real] using
    (integral_smul_measure
      (μ := ((ρ.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ))
      (c := m)
      (f := fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)))

/-- Helper for Theorem 16.17: when finite measures converge after normalization, keep both the
limiting probability law and the reconstructed finite measure in one package. -/
private lemma exists_auxFiniteMeasure_with_normalizedLimit_of_tendsto_charFun_local
    {ηs : ℕ → FiniteMeasure ℝ} {Φ : ℝ → ℂ} {m : NNReal}
    (hmass : Tendsto (fun n : ℕ ↦ (ηs n).mass) atTop (𝓝 m))
    (hm : m ≠ 0)
    (hchar : ∀ t : ℝ,
      Tendsto (fun n : ℕ ↦ charFun ((ηs n : FiniteMeasure ℝ) : Measure ℝ) t) atTop
        (𝓝 (Φ t)))
    (hcont : ContinuousAt (fun t : ℝ ↦ (((m⁻¹ : NNReal) : ℂ)) * Φ t) 0) :
    ∃ ρ : ProbabilityMeasure ℝ, ∃ η : FiniteMeasure ℝ,
      η = m • ρ.toFiniteMeasure ∧
      (∀ t : ℝ, charFun ((η : FiniteMeasure ℝ) : Measure ℝ) t = Φ t) ∧
      Tendsto (fun n : ℕ ↦ (ηs n).normalize) atTop (𝓝 ρ) := by
  let Ps : ℕ → ProbabilityMeasure E1 := fun n ↦ pushRealToEuclidean1 ((ηs n).normalize)
  have hmassInv :
      Tendsto (fun n : ℕ ↦ (ηs n).mass⁻¹) atTop (𝓝 m⁻¹) :=
    Tendsto.inv₀ hmass hm
  have hmassInvC :
      Tendsto (fun n : ℕ ↦ (((ηs n).mass⁻¹ : NNReal) : ℂ)) atTop
        (𝓝 (((m⁻¹ : NNReal) : ℂ))) := by
    exact
      (Complex.continuous_ofReal.continuousAt.tendsto.comp <|
        (NNReal.continuous_coe.continuousAt.tendsto.comp hmassInv))
  have hηne :
      ∀ᶠ n : ℕ in atTop, ηs n ≠ 0 := by
    filter_upwards [hmass (Ioi_mem_nhds (show (0 : NNReal) < m by
      exact pos_iff_ne_zero.mpr hm))] with n hn
    exact fun hzero ↦ by
      simpa [hzero] using hn
  have hcharE1 :
      ∀ x : E1,
        Tendsto (fun n ↦ charFun (Ps n : Measure E1) x) atTop
          (𝓝 ((((m⁻¹ : NNReal) : ℂ)) * Φ (euclidean1ToReal x))) := by
    intro x
    have hnormEq :
        ∀ᶠ n : ℕ in atTop,
          charFun (Ps n : Measure E1) x =
            (((((ηs n).mass)⁻¹ : NNReal) : ℂ)) *
              charFun ((ηs n : FiniteMeasure ℝ) : Measure ℝ) (euclidean1ToReal x) := by
      filter_upwards [hηne] with n hn
      rw [show Ps n = pushRealToEuclidean1 ((ηs n).normalize) by rfl]
      rw [charFun_map_realToEuclidean1]
      simpa using charFun_normalize_eq_invMass_local (ηs n) hn (euclidean1ToReal x)
    refine (hmassInvC.mul (hchar (euclidean1ToReal x))).congr' ?_
    filter_upwards [hnormEq] with n hn
    exact hn.symm
  have hφ0 :
      PartiallyContinuousAtZero (d := 1)
        (fun x : E1 ↦ (((m⁻¹ : NNReal) : ℂ)) * Φ (euclidean1ToReal x)) := by
    exact partiallyContinuousAtZero_comp_euclidean1ToReal_local hcont
  rcases exists_probabilityMeasure_of_tendsto_charFun (d := 1) Ps hcharE1 hφ0 with
    ⟨ρE1, hρE1char, hPsTendsto⟩
  let ρ : ProbabilityMeasure ℝ := ρE1.map measurable_euclidean1ToReal_local.aemeasurable
  have hρchar :
      ∀ t : ℝ, charFun (ρ : Measure ℝ) t = (((m⁻¹ : NNReal) : ℂ)) * Φ t := by
    intro t
    rw [charFun_map_euclidean1ToReal_local]
    simpa [realToEuclidean1, euclidean1ToReal] using hρE1char (realToEuclidean1 t)
  have hnormChar :
      ∀ t : ℝ,
        Tendsto (fun n : ℕ ↦ charFun ((ηs n).normalize : Measure ℝ) t) atTop
          (𝓝 (charFun (ρ : Measure ℝ) t)) := by
    intro t
    have hnormEq :
        ∀ᶠ n : ℕ in atTop,
          charFun ((ηs n).normalize : Measure ℝ) t =
            (((((ηs n).mass)⁻¹ : NNReal) : ℂ)) *
              charFun ((ηs n : FiniteMeasure ℝ) : Measure ℝ) t := by
      filter_upwards [hηne] with n hn
      exact charFun_normalize_eq_invMass_local (ηs n) hn t
    have hnormScaled :
        Tendsto
          (fun n : ℕ ↦ charFun ((ηs n).normalize : Measure ℝ) t)
          atTop
          (𝓝 ((((m⁻¹ : NNReal) : ℂ)) * Φ t)) := by
      refine (hmassInvC.mul (hchar t)).congr' ?_
      filter_upwards [hnormEq] with n hn
      exact hn.symm
    simpa [hρchar t] using hnormScaled
  have hnormTendsto :
      Tendsto (fun n : ℕ ↦ (ηs n).normalize) atTop (𝓝 ρ) := by
    exact ProbabilityMeasure.tendsto_of_tendsto_charFun hnormChar
  let η : FiniteMeasure ℝ := m • ρ.toFiniteMeasure
  refine ⟨ρ, η, rfl, ?_, hnormTendsto⟩
  intro t
  rw [charFun_mass_smul_probability_local]
  rw [hρchar]
  simp [hm]

/-- Helper for Theorem 16.17: once the auxiliary finite measures have convergent masses and their
normalized characteristic functions satisfy Lévy's continuity theorem, they assemble into one
limiting finite measure realizing the target auxiliary characteristic function. -/
private lemma exists_auxFiniteMeasure_of_tendsto_charFun_local
    {ηs : ℕ → FiniteMeasure ℝ} {Φ : ℝ → ℂ} {m : NNReal}
    (hmass : Tendsto (fun n : ℕ ↦ (ηs n).mass) atTop (𝓝 m))
    (hm : m ≠ 0)
    (hchar : ∀ t : ℝ,
      Tendsto (fun n : ℕ ↦ charFun ((ηs n : FiniteMeasure ℝ) : Measure ℝ) t) atTop
        (𝓝 (Φ t)))
    (hcont : ContinuousAt (fun t : ℝ ↦ (((m⁻¹ : NNReal) : ℂ)) * Φ t) 0) :
    ∃ η : FiniteMeasure ℝ, ∀ t : ℝ, charFun ((η : FiniteMeasure ℝ) : Measure ℝ) t = Φ t := by
  obtain ⟨ρ, η, _hηeq, hηchar, _hnormTendsto⟩ :=
    exists_auxFiniteMeasure_with_normalizedLimit_of_tendsto_charFun_local
      hmass hm hchar hcont
  exact ⟨η, hηchar⟩

/-- Helper for Theorem 16.17: the compact-average kernel is integrable against every finite
measure because it is bounded by `2`. -/
private lemma integrable_compactAverageKernel_of_isFiniteMeasure_local
    (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable compactAverageKernel ν := by
  -- Proof comment: the compact-average kernel is measurable and uniformly bounded by `2`.
  refine (integrable_const (2 : ℝ)).mono' measurable_compactAverageKernel.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    have hnonneg : 0 ≤ compactAverageKernel x := compactAverageKernel_nonneg x
    rw [Real.norm_of_nonneg hnonneg]
    exact compactAverageKernel_le_two x

/-- Helper for Theorem 16.17: the compact-average weighted exact-root jump measure is finite. -/
private theorem exactRootApproxCompactAverageMeasure_isFinite
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    IsFiniteMeasure
      ((exactRootApproxTriple μroot n).ν.withDensity
        (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  letI : IsFiniteMeasure ν := by
    change IsFiniteMeasure (((exactRootApproxIntensity μroot n : FiniteMeasure ℝ) : Measure ℝ))
    infer_instance
  -- Proof comment: bounded compact-average weighting preserves finiteness of the exact-root
  -- jump intensity.
  simpa [ν] using
    (MeasureTheory.isFiniteMeasure_withDensity_ofReal
      (μ := ν)
      (integrable_compactAverageKernel_of_isFiniteMeasure_local ν).hasFiniteIntegral)

/-- Helper for Theorem 16.17: the compact-average weighted exact-root jump measure. -/
private noncomputable def exactRootApproxCompactAverageMeasure
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) : FiniteMeasure ℝ :=
  ⟨(exactRootApproxTriple μroot n).ν.withDensity
      (fun x ↦ ENNReal.ofReal (compactAverageKernel x)),
    exactRootApproxCompactAverageMeasure_isFinite μroot n⟩

/-- Helper for Theorem 16.17: the compact-average exact-root auxiliary measure has no atom at
`0` because the compact-average weight vanishes there. -/
private lemma exactRootApproxCompactAverageMeasure_apply_zero_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    (((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ)
      ({0} : Set ℝ)) = 0 := by
  -- Proof comment: the exact-root auxiliary measure is defined by `withDensity` using
  -- `compactAverageKernel`, and that density is zero at the origin.
  change
    (((exactRootApproxTriple μroot n).ν.withDensity
      (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) ({0} : Set ℝ)) = 0
  rw [withDensity_apply _ (measurableSet_singleton 0)]
  simp [compactAverageKernel_zero]

/-- Helper for Theorem 16.17: exposing the compact-average `withDensity` factor turns the
auxiliary characteristic function back into the original Fourier kernel multiplied by
`compactAverageKernel`. -/
private lemma compactAverageWeightedFourierIntegral_eq_local
    {ν : Measure ℝ} (t : ℝ) :
    ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
        ∂ν.withDensity (fun x ↦ ENNReal.ofReal (compactAverageKernel x)) =
      ∫ x : ℝ,
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * compactAverageKernel x ∂ν := by
  -- Proof comment: `withDensity` contributes exactly the real scalar
  -- `compactAverageKernel x`, since the compact-average kernel is nonnegative everywhere.
  rw [integral_withDensity_eq_integral_toReal_smul measurable_compactAverageKernel.ennreal_ofReal
    (by
      filter_upwards [compactAverageKernel_ae_ne_top (ν := ν)] with x hx
      exact lt_of_le_of_ne le_top hx)]
  refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
  have htoReal :
      ENNReal.toReal (ENNReal.ofReal (compactAverageKernel x)) = compactAverageKernel x := by
    simp [compactAverageKernel_nonneg x]
  calc
    ENNReal.toReal (ENNReal.ofReal (compactAverageKernel x)) •
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) =
      (((compactAverageKernel x : ℝ) : ℂ)) *
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
          simpa [Algebra.smul_def, htoReal]
    _ =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (((compactAverageKernel x : ℝ) : ℂ)) := by
        ring

/-- Helper for Theorem 16.17: averaging the pure oscillatory factor over `[-1,1]` produces
`2 sinc(x)`. -/
private lemma intervalIntegralExpMulCompactAverageBridge_local (x : ℝ) :
    ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) =
      2 * (Real.sinc x : ℂ) := by
  calc
    ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)
        = ∫ s in (-1 : ℝ)..1, charFun (Measure.dirac x) s := by
            refine intervalIntegral.integral_congr fun s _ ↦ ?_
            rw [MeasureTheory.charFun_dirac]
            rw [show inner ℝ x s = x * s by simpa using (RCLike.inner_apply' (𝕜 := ℝ) x s)]
            congr 1
            ring
    _ = 2 * (Real.sinc x : ℂ) := by
          simpa using
            (MeasureTheory.integral_charFun_Icc (μ := Measure.dirac x) (r := (1 : ℝ)) zero_lt_one)

/-- Helper for Theorem 16.17: `compactAverageKernel` is the half-interval average of
`1 - cos (s * x)` over `[-1, 1]`. -/
private lemma compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_bridge_local (x : ℝ) :
    compactAverageKernel x = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
  have hExpInt :
      IntervalIntegrable
        (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) volume (-1 : ℝ) 1 := by
    have hExpCont :
        Continuous (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
      continuity
    exact hExpCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hReInt :
      ∫ s in (-1 : ℝ)..1, Complex.re (Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) =
        Complex.re (∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
    simpa using
      (Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
        (a := (-1 : ℝ)) (b := (1 : ℝ))
        (f := fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) hExpInt)
  have hCosInt :
      ∫ s in (-1 : ℝ)..1, Real.cos (s * x) = 2 * Real.sinc x := by
    calc
      ∫ s in (-1 : ℝ)..1, Real.cos (s * x)
          = ∫ s in (-1 : ℝ)..1, Complex.re (Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
              refine intervalIntegral.integral_congr fun s _ ↦ ?_
              simpa using (Complex.exp_ofReal_mul_I_re (s * x)).symm
      _ = Complex.re
            (∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := hReInt
      _ = 2 * Real.sinc x := by
            rw [intervalIntegralExpMulCompactAverageBridge_local]
            simp
  have hCosCont :
      IntervalIntegrable (fun s : ℝ ↦ Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    have hCosCont' : Continuous (fun s : ℝ ↦ Real.cos (s * x)) := by
      simpa using (Real.continuous_cos.comp (continuous_id.mul continuous_const))
    exact hCosCont'.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hSub :
      ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) =
        (∫ s in (-1 : ℝ)..1, (1 : ℝ)) - ∫ s in (-1 : ℝ)..1, Real.cos (s * x) := by
    rw [intervalIntegral.integral_sub (μ := volume) intervalIntegrable_const hCosCont]
  have hConstIntEval : ∫ s in (-1 : ℝ)..1, (1 : ℝ) = 2 := by
    norm_num [intervalIntegral.integral_const]
  calc
    compactAverageKernel x = 1 - Real.sinc x := by
      simp [compactAverageKernel]
    _ = (1 / 2 : ℝ) * (2 - 2 * Real.sinc x) := by ring
    _ = (1 / 2 : ℝ) *
          ((∫ s in (-1 : ℝ)..1, (1 : ℝ)) - ∫ s in (-1 : ℝ)..1, Real.cos (s * x)) := by
            rw [hConstIntEval, hCosInt]
    _ = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
          rw [← hSub]

/-- Helper for Theorem 16.17: the cosine defect is quadratically bounded above. -/
private lemma one_sub_cos_le_sq_div_two_bridge_local (y : ℝ) :
    1 - Real.cos y ≤ y ^ (2 : ℕ) / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos (x := y)]

/-- Helper for Theorem 16.17: on `[-1,1]`, the cosine defect is quadratically bounded below by a
uniform multiple of `y²`. -/
private lemma two_div_pi_sq_mul_sq_le_one_sub_cos_bridge_local {y : ℝ} (hy : |y| ≤ 1) :
    (2 / Real.pi ^ (2 : ℕ)) * y ^ (2 : ℕ) ≤ 1 - Real.cos y := by
  have hpi : |y| ≤ Real.pi := by
    linarith [hy, Real.pi_gt_three]
  have hcos := Real.cos_le_one_sub_mul_cos_sq (x := y) hpi
  linarith [hcos]

/-- Helper for Theorem 16.17: near `0`, the compact-average kernel is at most a constant multiple
of `x²`. -/
private lemma compactAverageKernel_le_half_sq_bridge_local {x : ℝ} (_hx : |x| ≤ 1) :
    compactAverageKernel x ≤ x ^ (2 : ℕ) / 2 := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hConstInt :
      IntervalIntegrable (fun _ : ℝ ↦ x ^ (2 : ℕ) / 2) volume (-1 : ℝ) 1 := intervalIntegrable_const
  have hMono :
      ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) ≤
        ∫ s in (-1 : ℝ)..1, (x ^ (2 : ℕ) / 2 : ℝ) := by
    refine intervalIntegral.integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
      (f := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (g := fun _ : ℝ ↦ x ^ (2 : ℕ) / 2)
      (hab := by norm_num) hDefectInt hConstInt ?_
    intro s hs
    have hsBounds : -1 ≤ s ∧ s ≤ 1 := by
      simpa using hs
    have hsAbs : |s| ≤ 1 := abs_le.mpr hsBounds
    have hDefect := one_sub_cos_le_sq_div_two_bridge_local (s * x)
    have hSq :
        (s * x) ^ (2 : ℕ) / 2 ≤ x ^ (2 : ℕ) / 2 := by
      have hsSq : s ^ (2 : ℕ) ≤ 1 := by
        nlinarith [sq_nonneg s, hsAbs]
      calc
        (s * x) ^ (2 : ℕ) / 2 = (s ^ (2 : ℕ) * x ^ (2 : ℕ)) / 2 := by ring
        _ ≤ (1 * x ^ (2 : ℕ)) / 2 := by
              nlinarith [hsSq, sq_nonneg x]
        _ = x ^ (2 : ℕ) / 2 := by ring
    exact hDefect.trans hSq
  calc
    compactAverageKernel x
        = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
            rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_bridge_local]
    _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (x ^ (2 : ℕ) / 2 : ℝ) := by
          gcongr
    _ = x ^ (2 : ℕ) / 2 := by
          rw [intervalIntegral.integral_const]
          norm_num
          ring

/-- Helper for Theorem 16.17: near `0`, the compact-average kernel is bounded below by a fixed
positive multiple of `x²`. -/
private lemma two_div_pi_sq_mul_sq_quarter_le_compactAverageKernel_bridge_local {x : ℝ}
    (hx : |x| ≤ 1) :
    x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hLowerInt :
      IntervalIntegrable
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) volume (-1 : ℝ) 1 := by
    have hLowerCont : Continuous (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) := by
      continuity
    exact hLowerCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hMono :
      ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) ≤
        ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
    refine intervalIntegral.integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
      (f := fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ))
      (g := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (hab := by norm_num) hLowerInt hDefectInt ?_
    intro s hs
    have hsBounds : -1 ≤ s ∧ s ≤ 1 := by
      simpa using hs
    have hsAbs : |s| ≤ 1 := abs_le.mpr hsBounds
    have hsxAbs : |s * x| ≤ 1 := by
      calc
        |s * x| = |s| * |x| := by rw [abs_mul]
        _ ≤ 1 * 1 := by
              gcongr
        _ = 1 := by ring
    simpa using two_div_pi_sq_mul_sq_le_one_sub_cos_bridge_local (y := s * x) hsxAbs
  have hSqHalf : (1 / 2 : ℝ) ≤ ∫ s in (-1 : ℝ)..1, s ^ (2 : ℕ) := by
    rw [integral_pow]
    norm_num
  let c : ℝ := (1 / 2 : ℝ) * ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ))
  have hcNonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hFactor := mul_le_mul_of_nonneg_left hSqHalf hcNonneg
  have hLowerBound :
      x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ)) ≤
        (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
    dsimp [c] at hFactor ⊢
    convert hFactor using 1
    · ring
    · rw [show (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) =
          fun s : ℝ ↦ ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ)) * s ^ (2 : ℕ) by
            funext s
            ring]
      rw [intervalIntegral.integral_const_mul]
      ring
  calc
    x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ))
        ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) :=
          hLowerBound
    _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
          gcongr
    _ = compactAverageKernel x := by
          rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_bridge_local]

/-- Helper for Theorem 16.17: on the shell `1 ≤ |x| ≤ 2`, the compact-average kernel has a
uniform positive lower bound. -/
private lemma one_div_twelve_pi_sq_le_compactAverageKernel_of_one_le_abs_le_two_bridge_local
    {x : ℝ} (hx1 : 1 ≤ |x|) (hx2 : |x| ≤ 2) :
    1 / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hLowerInt :
      IntervalIntegrable
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) volume (-1 / 2 : ℝ)
        (1 / 2 : ℝ) := by
    have hLowerCont : Continuous
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) := by
      continuity
    exact hLowerCont.intervalIntegrable (μ := volume) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  have hSmallDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)] fun s : ℝ ↦ 1 - Real.cos (s * x) := by
    exact Filter.Eventually.of_forall fun s ↦ sub_nonneg.mpr (Real.cos_le_one _)
  have hWindowMono :
      ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) ≤
        ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
    exact intervalIntegral.integral_mono_interval
      (μ := volume)
      (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (c := (-1 : ℝ)) (d := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) hNonneg hDefectInt
  have hMono :
      ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) ≤
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) := by
    refine intervalIntegral.integral_mono_on (μ := volume)
      (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (f := fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ))
      (g := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (hab := by norm_num) hLowerInt hSmallDefectInt ?_
    intro s hs
    have hsBounds : -(1 / 2 : ℝ) ≤ s ∧ s ≤ 1 / 2 := by
      rcases hs with ⟨hsLeft, hsRight⟩
      constructor <;> linarith
    have hsAbs : |s| ≤ 1 / 2 := abs_le.mpr hsBounds
    have hsxAbs : |s * x| ≤ 1 := by
      calc
        |s * x| = |s| * |x| := by rw [abs_mul]
        _ ≤ (1 / 2 : ℝ) * 2 := by
              gcongr
        _ = 1 := by ring
    simpa using two_div_pi_sq_mul_sq_le_one_sub_cos_bridge_local (y := s * x) hsxAbs
  have hLowerEval :
      x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ)) ≤
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
    have hEval :
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) =
          x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ)) := by
      rw [show (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) =
          fun s : ℝ ↦ ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ)) * s ^ (2 : ℕ) by
            funext s
            ring]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring_nf
    exact le_of_eq hEval.symm
  have hShell :
      x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
    calc
      x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ))
          = (1 / 2 : ℝ) * (x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ))) := by
              field_simp [Real.pi_ne_zero]
              ring
      _ ≤ (1 / 2 : ℝ) *
              ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_left hLowerEval (by norm_num : 0 ≤ (1 / 2 : ℝ))
      _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) := by
            gcongr
      _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
            gcongr
      _ = compactAverageKernel x := by
            rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_bridge_local]
  have hxSqOne : 1 ≤ x ^ (2 : ℕ) := by
    have hxSqAbs : 1 ≤ |x| ^ (2 : ℕ) := by
      nlinarith [hx1, abs_nonneg x]
    simpa [sq_abs] using hxSqAbs
  have hOneToSq :
      1 / (12 * Real.pi ^ (2 : ℕ)) ≤ x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ)) := by
    exact div_le_div_of_nonneg_right hxSqOne (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
  exact hOneToSq.trans hShell

/-- Helper for Theorem 16.17: the compact-average kernel globally dominates the canonical
integrand up to one fixed scalar factor. -/
private lemma compactAverageInverseWeightBound_bridge_local (x : ℝ) :
    min (x ^ (2 : ℕ)) 1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
  by_cases hx1 : |x| ≤ 1
  · have hLower :=
      two_div_pi_sq_mul_sq_quarter_le_compactAverageKernel_bridge_local (x := x) hx1
    have hSq :
        x ^ (2 : ℕ) ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
      have hScaled := mul_le_mul_of_nonneg_left hLower (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
      calc
        x ^ (2 : ℕ) ≤ 6 * x ^ (2 : ℕ) := by
              nlinarith [sq_nonneg x]
        _ = (12 * Real.pi ^ (2 : ℕ)) * (x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ))) := by
              field_simp [Real.pi_ne_zero]
              ring
        _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := hScaled
    exact (min_le_left _ _).trans hSq
  · have hxgt : 1 < |x| := lt_of_not_ge hx1
    by_cases hx2 : |x| ≤ 2
    · have hShell :
          1 / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x :=
        one_div_twelve_pi_sq_le_compactAverageKernel_of_one_le_abs_le_two_bridge_local
          (le_of_lt hxgt) hx2
      have hOne :
          1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
        have hScaled := mul_le_mul_of_nonneg_left hShell (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
        calc
          1 = (12 * Real.pi ^ (2 : ℕ)) * (1 / (12 * Real.pi ^ (2 : ℕ))) := by
                field_simp [Real.pi_ne_zero]
          _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := hScaled
      exact (min_le_right _ _).trans hOne
    · have hx2' : 2 < |x| := lt_of_not_ge hx2
      have hsincHalf : |Real.sinc x| ≤ 1 / (2 : ℝ) := by
        by_cases hxzero : x = 0
        · exfalso
          have hNot : ¬ 1 < |x| := by simpa [hxzero]
          exact hNot hxgt
        · rw [Real.sinc, if_neg hxzero]
          have hsinLe : |Real.sin x| ≤ 1 := by
            exact abs_le.2 ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
          have hInv : 1 / |x| ≤ 1 / (2 : ℝ) := by
            exact one_div_le_one_div_of_le (by positivity) (le_of_lt hx2')
          calc
            |Real.sin x / x| = |Real.sin x| / |x| := by rw [abs_div]
            _ ≤ 1 / |x| := by gcongr
            _ ≤ 1 / (2 : ℝ) := hInv
      have hKernelHalf : (1 / 2 : ℝ) ≤ compactAverageKernel x := by
        have hsincLeHalf : Real.sinc x ≤ 1 / (2 : ℝ) := le_trans (le_abs_self _) hsincHalf
        calc
          (1 / 2 : ℝ) ≤ 1 - Real.sinc x := by linarith
          _ = compactAverageKernel x := by simp [compactAverageKernel]
      have hOne :
          1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
        calc
          1 ≤ 6 * Real.pi ^ (2 : ℕ) := by
                nlinarith [Real.pi_gt_three]
          _ = (12 * Real.pi ^ (2 : ℕ)) * (1 / 2 : ℝ) := by ring
          _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
                gcongr
      exact (min_le_right _ _).trans hOne

/-- Helper for Theorem 16.17: the theorem-local quotient kernel used to reconstruct the smooth
sine-centered Lévy kernel from the compact-average auxiliary measure. -/
private def compactAverageReconstructionKernel_local (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    if hx : x = 0 then
      -((3 * t ^ (2 : ℕ) : ℝ) : ℂ)
    else
      levyKhinchinSineKernelLocal t x / compactAverageKernel x

/-- Helper for Theorem 16.17: the compact-average reconstruction kernel is measurable. -/
private lemma measurable_compactAverageReconstructionKernel_local (t : ℝ) :
    Measurable (compactAverageReconstructionKernel_local t) := by
  classical
  have hQuot :
      Measurable
        (fun x : ℝ ↦ levyKhinchinSineKernelLocal t x / ((compactAverageKernel x : ℝ) : ℂ)) := by
    -- Proof comment: away from the filled value at `0`, the reconstruction kernel is a quotient
    -- of the measurable sine-centered kernel by the measurable compact-average weight.
    have hNum : Measurable (levyKhinchinSineKernelLocal t) := by
      unfold levyKhinchinSineKernelLocal
      fun_prop
    have hDen :
        Measurable (fun x : ℝ ↦ ((compactAverageKernel x : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp measurable_compactAverageKernel
    simpa using hNum.div hDen
  -- Proof comment: the only special value is the explicit fill-in at `0`, so measurability is a
  -- single `if`-combination over the measurable singleton.
  let s : Set ℝ := {x : ℝ | x = 0}
  have hs : MeasurableSet s := by
    simpa [s] using measurableSet_singleton (0 : ℝ)
  simpa [compactAverageReconstructionKernel_local, s] using
    measurable_const.piecewise hs hQuot

/-- Helper for Theorem 16.17: the scaled compact-average kernel differs from its quadratic limit
by at most a linear error near `0`. -/
private lemma abs_compactAverageKernel_div_sq_sub_oneSix_le_local
    {x : ℝ} (hx : x ≠ 0) (hsmall : |x| ≤ 1) :
    |compactAverageKernel x / x ^ (2 : ℕ) - 1 / 6| ≤ |x| * (5 / 96) := by
  have hSin := Real.sin_bound hsmall
  have hxpow2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
  have hxpow3 : x ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hx
  have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
  calc
    |compactAverageKernel x / x ^ (2 : ℕ) - 1 / 6|
        = |-(Real.sin x - (x - x ^ (3 : ℕ) / 6)) / x ^ (3 : ℕ)| := by
            rw [compactAverageKernel, Real.sinc_of_ne_zero hx]
            congr 1
            field_simp [hxpow2, hxpow3]
            ring
    _ = |Real.sin x - (x - x ^ (3 : ℕ) / 6)| / |x| ^ (3 : ℕ) := by
          rw [abs_div, abs_neg, abs_pow]
    _ ≤ (|x| ^ (4 : ℕ) * (5 / 96)) / |x| ^ (3 : ℕ) := by
          exact div_le_div_of_nonneg_right hSin (by positivity)
    _ = |x| * (5 / 96) := by
          field_simp [hxabs]

/-- Helper for Theorem 16.17: after dividing by `x²`, the compact-average kernel tends to `1/6`
at the origin. -/
private lemma tendsto_compactAverageKernel_div_sq_at_zero_local :
    Tendsto (fun x : ℝ ↦ compactAverageKernel x / x ^ (2 : ℕ)) (𝓝[≠] 0) (𝓝 (1 / 6)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let A : ℝ := 5 / 96
  let δ : ℝ := min 1 (ε / (A + 1))
  have hδpos : 0 < δ := by
    dsimp [δ, A]
    refine lt_min (by norm_num) ?_
    positivity
  refine ⟨δ, hδpos, ?_⟩
  intro x hx hxDist
  have hsmall : |x| ≤ 1 := by
    have hxlt : |x| < δ := by
      simpa [Real.dist_eq, abs_sub_comm, δ] using hxDist
    exact le_of_lt (lt_of_lt_of_le hxlt (min_le_left _ _))
  have hNear :
      |compactAverageKernel x / x ^ (2 : ℕ) - 1 / 6| ≤ A * |x| := by
    simpa [A, mul_comm] using
      abs_compactAverageKernel_div_sq_sub_oneSix_le_local hx hsmall
  have hxlt : |x| < ε / (A + 1) := by
    have hxlt' : |x| < δ := by
      simpa [Real.dist_eq, abs_sub_comm, δ] using hxDist
    exact lt_of_lt_of_le hxlt' (min_le_right _ _)
  have hMul :
      (A + 1) * |x| < ε := by
    have hApos : 0 < A + 1 := by
      dsimp [A]
      positivity
    simpa [mul_comm] using (lt_div_iff₀ hApos).mp hxlt
  have hAle :
      A * |x| ≤ (A + 1) * |x| := by
    have hxnonneg : 0 ≤ |x| := abs_nonneg x
    have hA : A ≤ A + 1 := by
      dsimp [A]
      linarith
    exact mul_le_mul_of_nonneg_right hA hxnonneg
  calc
    dist (compactAverageKernel x / x ^ (2 : ℕ)) (1 / 6)
        = |compactAverageKernel x / x ^ (2 : ℕ) - 1 / 6| := by
            simp [Real.dist_eq]
    _ ≤ A * |x| := hNear
    _ < ε := lt_of_le_of_lt hAle hMul

/-- Helper for Theorem 16.17: the scaled cosine remainder has the expected quadratic limit at
the origin. -/
private lemma abs_cos_sub_one_div_sq_add_half_sq_le_local
    {t x : ℝ} (hx : x ≠ 0) (hsmall : |t * x| ≤ 1) :
    |(Real.cos (t * x) - 1) / x ^ (2 : ℕ) + t ^ (2 : ℕ) / 2| ≤
      (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
  have hCos := Real.cos_bound hsmall
  have hxpow2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
  have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
  calc
    |(Real.cos (t * x) - 1) / x ^ (2 : ℕ) + t ^ (2 : ℕ) / 2|
        = |(Real.cos (t * x) - (1 - (t * x) ^ (2 : ℕ) / 2)) / x ^ (2 : ℕ)| := by
            congr 1
            field_simp [hxpow2]
            ring
    _ = |Real.cos (t * x) - (1 - (t * x) ^ (2 : ℕ) / 2)| / |x| ^ (2 : ℕ) := by
          rw [abs_div, abs_pow]
    _ ≤ (|t * x| ^ (4 : ℕ) * (5 / 96)) / |x| ^ (2 : ℕ) := by
          exact div_le_div_of_nonneg_right hCos (by positivity)
    _ = (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
          rw [abs_mul, mul_pow]
          field_simp [hxabs]

/-- Helper for Theorem 16.17: the real part of the scaled canonical kernel tends to
`-t² / 2` at the origin. -/
private lemma tendsto_cos_sub_one_div_sq_at_zero_local (t : ℝ) :
    Tendsto (fun x : ℝ ↦ (Real.cos (t * x) - 1) / x ^ (2 : ℕ)) (𝓝[≠] 0)
      (𝓝 (-(t ^ (2 : ℕ) / 2))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let A : ℝ := |t| ^ (4 : ℕ) * (5 / 96)
  let δ : ℝ := min 1 (min ((|t| + 1)⁻¹) (ε / (A + 1)))
  have hδpos : 0 < δ := by
    dsimp [δ]
    refine lt_min (by norm_num) ?_
    refine lt_min ?_ ?_
    · have : 0 < |t| + 1 := by positivity
      exact inv_pos.mpr this
    · positivity
  refine ⟨δ, hδpos, ?_⟩
  intro x hx hxDist
  have hxlt : |x| < δ := by
    simpa [Real.dist_eq, abs_sub_comm, δ] using hxDist
  have hsmallX : |x| ≤ 1 := le_of_lt (lt_of_lt_of_le hxlt (min_le_left _ _))
  have hδinv : δ ≤ (|t| + 1)⁻¹ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have htxLt : |t * x| < 1 := by
    have hxInv : |x| < (|t| + 1)⁻¹ := lt_of_lt_of_le hxlt hδinv
    by_cases ht : t = 0
    · simp [ht]
    · calc
        |t * x| = |t| * |x| := by rw [abs_mul]
        _ < |t| * ((|t| + 1)⁻¹) := by
              exact mul_lt_mul_of_pos_left hxInv (abs_pos.mpr ht)
        _ = |t| / (|t| + 1) := by
              rw [div_eq_mul_inv]
        _ < 1 := by
              have hpos : 0 < |t| + 1 := by positivity
              have hlt : |t| < |t| + 1 := by linarith
              exact (div_lt_one hpos).2 hlt
  have hNear :
      |(Real.cos (t * x) - 1) / x ^ (2 : ℕ) + t ^ (2 : ℕ) / 2| ≤
        A * |x| ^ (2 : ℕ) :=
    abs_cos_sub_one_div_sq_add_half_sq_le_local hx (le_of_lt htxLt)
  have hNear' :
      |(Real.cos (t * x) - 1) / x ^ (2 : ℕ) + t ^ (2 : ℕ) / 2| ≤ A * |x| := by
    refine hNear.trans ?_
    have hPow : |x| ^ (2 : ℕ) ≤ |x| := by
      simpa using
        (pow_le_pow_of_le_one (abs_nonneg x) hsmallX (by decide : (1 : ℕ) ≤ 2))
    gcongr
  have hxlt' : |x| < ε / (A + 1) := by
    exact lt_of_lt_of_le hxlt (by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _))
  have hMul :
      (A + 1) * |x| < ε := by
    have hApos : 0 < A + 1 := by positivity
    simpa [mul_comm] using (lt_div_iff₀ hApos).mp hxlt'
  have hAle :
      A * |x| ≤ (A + 1) * |x| := by
    have hxnonneg : 0 ≤ |x| := abs_nonneg x
    have hA : A ≤ A + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hA hxnonneg
  calc
    dist ((Real.cos (t * x) - 1) / x ^ (2 : ℕ)) (-(t ^ (2 : ℕ) / 2))
        = |(Real.cos (t * x) - 1) / x ^ (2 : ℕ) + t ^ (2 : ℕ) / 2| := by
            simp [Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ ≤ A * |x| := hNear'
    _ < ε := lt_of_le_of_lt hAle hMul

/-- Helper for Theorem 16.17: the scaled sine remainder is at most linear near the origin. -/
private lemma abs_sin_sub_linear_div_sq_le_local
    {t x : ℝ} (hx : x ≠ 0) (hsmall : |t * x| ≤ 1) :
    |(Real.sin (t * x) - t * x) / x ^ (2 : ℕ)| ≤
      |t| ^ (3 : ℕ) * |x| / 6 + (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
  have hSin := Real.sin_bound hsmall
  have hxpow2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
  have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hErr :
      |(Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)) / x ^ (2 : ℕ)| ≤
        (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
    calc
      |(Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)) / x ^ (2 : ℕ)|
          = |Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)| / |x| ^ (2 : ℕ) := by
              rw [abs_div, abs_pow]
    _ ≤ (|t * x| ^ (4 : ℕ) * (5 / 96)) / |x| ^ (2 : ℕ) := by
            exact div_le_div_of_nonneg_right hSin (by positivity)
      _ = (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
            rw [abs_mul, mul_pow]
            field_simp [hxabs]
  have hDecomp :
      (Real.sin (t * x) - t * x) / x ^ (2 : ℕ) =
        (Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)) / x ^ (2 : ℕ) -
          t ^ (3 : ℕ) * x / 6 := by
    field_simp [hxpow2]
    ring
  calc
    |(Real.sin (t * x) - t * x) / x ^ (2 : ℕ)|
        ≤
          |(Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)) / x ^ (2 : ℕ)| +
            |t ^ (3 : ℕ) * x / 6| := by
              rw [hDecomp]
              simpa [sub_eq_add_neg] using
                (abs_sub_le
                  ((Real.sin (t * x) - ((t * x) - (t * x) ^ (3 : ℕ) / 6)) / x ^ (2 : ℕ))
                  0 (t ^ (3 : ℕ) * x / 6))
    _ ≤ (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) + |t ^ (3 : ℕ) * x / 6| := by
          gcongr
    _ = |t| ^ (3 : ℕ) * |x| / 6 + (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) := by
          rw [abs_div, abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (6 : ℝ))]
          ring

/-- Helper for Theorem 16.17: the imaginary part of the scaled canonical kernel tends to `0` at
the origin. -/
private lemma tendsto_sin_sub_linear_div_sq_at_zero_local (t : ℝ) :
    Tendsto (fun x : ℝ ↦ (Real.sin (t * x) - t * x) / x ^ (2 : ℕ)) (𝓝[≠] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let B : ℝ := |t| ^ (3 : ℕ) / 6 + |t| ^ (4 : ℕ) * (5 / 96)
  let δ : ℝ := min 1 (min ((|t| + 1)⁻¹) (ε / (B + 1)))
  have hδpos : 0 < δ := by
    dsimp [δ]
    refine lt_min (by norm_num) ?_
    refine lt_min ?_ ?_
    · have : 0 < |t| + 1 := by positivity
      exact inv_pos.mpr this
    · positivity
  refine ⟨δ, hδpos, ?_⟩
  intro x hx hxDist
  have hxlt : |x| < δ := by
    simpa [Real.dist_eq, abs_sub_comm, δ] using hxDist
  have hsmallX : |x| ≤ 1 := le_of_lt (lt_of_lt_of_le hxlt (min_le_left _ _))
  have hδinv : δ ≤ (|t| + 1)⁻¹ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have htxLt : |t * x| < 1 := by
    have hxInv : |x| < (|t| + 1)⁻¹ := lt_of_lt_of_le hxlt hδinv
    by_cases ht : t = 0
    · simp [ht]
    · calc
        |t * x| = |t| * |x| := by rw [abs_mul]
        _ < |t| * ((|t| + 1)⁻¹) := by
              exact mul_lt_mul_of_pos_left hxInv (abs_pos.mpr ht)
        _ = |t| / (|t| + 1) := by
              rw [div_eq_mul_inv]
        _ < 1 := by
              have hpos : 0 < |t| + 1 := by positivity
              have hlt : |t| < |t| + 1 := by linarith
              exact (div_lt_one hpos).2 hlt
  have hNear :
      |(Real.sin (t * x) - t * x) / x ^ (2 : ℕ)| ≤
        |t| ^ (3 : ℕ) * |x| / 6 + (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) :=
    abs_sin_sub_linear_div_sq_le_local hx (le_of_lt htxLt)
  have hNear' :
      |(Real.sin (t * x) - t * x) / x ^ (2 : ℕ)| ≤ B * |x| := by
    refine hNear.trans ?_
    have hPow : |x| ^ (2 : ℕ) ≤ |x| := by
      simpa using
        (pow_le_pow_of_le_one (abs_nonneg x) hsmallX (by decide : (1 : ℕ) ≤ 2))
    have hSecond :
        (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ) ≤
          (|t| ^ (4 : ℕ) * (5 / 96)) * |x| := by
      gcongr
    calc
      |t| ^ (3 : ℕ) * |x| / 6 + (|t| ^ (4 : ℕ) * (5 / 96)) * |x| ^ (2 : ℕ)
          ≤ |t| ^ (3 : ℕ) * |x| / 6 + (|t| ^ (4 : ℕ) * (5 / 96)) * |x| := by
              exact add_le_add le_rfl hSecond
      _ = B * |x| := by
            dsimp [B]
            ring
  have hxlt' : |x| < ε / (B + 1) := by
    exact lt_of_lt_of_le hxlt (by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _))
  have hMul :
      (B + 1) * |x| < ε := by
    have hBpos : 0 < B + 1 := by positivity
    simpa [mul_comm] using (lt_div_iff₀ hBpos).mp hxlt'
  have hBle :
      B * |x| ≤ (B + 1) * |x| := by
    have hxnonneg : 0 ≤ |x| := abs_nonneg x
    have hB : B ≤ B + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hB hxnonneg
  calc
    dist ((Real.sin (t * x) - t * x) / x ^ (2 : ℕ)) 0
        = |(Real.sin (t * x) - t * x) / x ^ (2 : ℕ)| := by
            rw [Real.dist_eq]
            simp
    _ ≤ B * |x| := hNear'
    _ < ε := lt_of_le_of_lt hBle hMul

/-- Helper for Theorem 16.17: the smooth centering `Real.sin` differs from the canonical cutoff by
at most `min (x^2) 1`. -/
private lemma norm_sin_sub_levyKhinchinCanonicalCentering_le_sqMinOne_local (x : ℝ) :
    ‖Real.sin x - levyKhinchinCanonicalCentering x‖ ≤ min (x ^ (2 : ℕ)) 1 := by
  by_cases hx : |x| < 1
  · by_cases hx0 : x = 0
    · subst hx0
      simp [levyKhinchinCanonicalCentering]
    · have hsmall : |(1 : ℝ) * x| ≤ 1 := by
        simpa using le_of_lt hx
      have hTaylor :=
        abs_sin_sub_linear_div_sq_le_local (t := (1 : ℝ)) hx0 hsmall
      have hDivLeOne : |(Real.sin x - x) / x ^ (2 : ℕ)| ≤ 1 := by
        have hTaylor' : |(Real.sin x - x) / x ^ (2 : ℕ)| ≤
            |x| / 6 + (5 / 96 : ℝ) * |x| ^ (2 : ℕ) := by
          simpa using hTaylor
        have hAux :
            |x| / 6 + (5 / 96 : ℝ) * |x| ^ (2 : ℕ) ≤ 1 := by
          have hxle : |x| ≤ 1 := le_of_lt hx
          nlinarith [abs_nonneg x, hxle]
        exact hTaylor'.trans hAux
      have hxSqPos : 0 < x ^ (2 : ℕ) := by
        nlinarith [sq_pos_iff.mpr hx0]
      have hDiv' : |Real.sin x - x| / x ^ (2 : ℕ) ≤ 1 := by
        simpa [abs_div, abs_of_pos hxSqPos, abs_pow] using hDivLeOne
      have hAbs : |Real.sin x - x| ≤ x ^ (2 : ℕ) := by
        simpa using (div_le_iff₀ hxSqPos).mp hDiv'
      simpa [levyKhinchinCanonicalCentering, hx, Real.norm_eq_abs,
        sqMinOne_eq_sq_of_abs_lt_one_local hx, abs_sub_comm] using hAbs
  · have hx' : 1 ≤ |x| := le_of_not_gt hx
    simpa [levyKhinchinCanonicalCentering, hx, Real.norm_eq_abs,
      sqMinOne_eq_one_of_one_le_abs_local hx', abs_sub_comm] using Real.abs_sin_le_one x

/-- Helper for Theorem 16.17: the sine-to-canonical centering correction is integrable against
every canonical Lévy measure. -/
private lemma integrable_sin_sub_levyKhinchinCanonicalCentering_local
    {ν : Measure ℝ} (hν : IsCanonicalMeasure ν) :
    Integrable (fun x : ℝ ↦ Real.sin x - levyKhinchinCanonicalCentering x) ν := by
  have hMeas :
      AEStronglyMeasurable (fun x : ℝ ↦ Real.sin x - levyKhinchinCanonicalCentering x) ν := by
    have hMeasurable :
        Measurable (fun x : ℝ ↦ Real.sin x - levyKhinchinCanonicalCentering x) := by
      exact (Real.continuous_sin.measurable).sub measurable_levyKhinchinCanonicalCentering
    exact hMeasurable.aestronglyMeasurable
  refine hν.integrable_sq_min_one.mono' hMeas ?_
  exact Filter.Eventually.of_forall fun x ↦
    norm_sin_sub_levyKhinchinCanonicalCentering_le_sqMinOne_local x

/-- Helper for Theorem 16.17: the compact-average reconstruction kernel is uniformly bounded by a
`t`-dependent constant. -/
private lemma norm_compactAverageReconstructionKernel_local_le (t x : ℝ) :
    ‖compactAverageReconstructionKernel_local t x‖ ≤
      (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) + 3 * t ^ (2 : ℕ) := by
  by_cases hx : x = 0
  · subst hx
    have hMainNonneg :
        0 ≤ (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) := by
      positivity
    simpa [compactAverageReconstructionKernel_local] using
      (le_add_of_nonneg_left hMainNonneg : 3 * t ^ (2 : ℕ) ≤
        (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) + 3 * t ^ (2 : ℕ))
  · have hKernelPos : 0 < compactAverageKernel x := compactAverageKernel_pos_of_ne_zero hx
    have hEq :
        levyKhinchinSineKernelLocal t x =
          levyKhinchinCanonicalKernelLocal t x +
            ((((t * (levyKhinchinCanonicalCentering x - Real.sin x) : ℝ) : ℂ)) * Complex.I) := by
      simp [levyKhinchinSineKernelLocal, levyKhinchinCanonicalKernelLocal]
      ring
    have hCorr :
        ‖((((t * (levyKhinchinCanonicalCentering x - Real.sin x) : ℝ) : ℂ)) * Complex.I)‖ ≤
          |t| * min (x ^ (2 : ℕ)) 1 := by
      calc
        ‖((((t * (levyKhinchinCanonicalCentering x - Real.sin x) : ℝ) : ℂ)) * Complex.I)‖
            = |t * (levyKhinchinCanonicalCentering x - Real.sin x)| := by
              rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        _ = |t| * |levyKhinchinCanonicalCentering x - Real.sin x| := by
              rw [abs_mul]
        _ = |t| * |Real.sin x - levyKhinchinCanonicalCentering x| := by
              rw [abs_sub_comm]
        _ ≤ |t| * min (x ^ (2 : ℕ)) 1 := by
              exact mul_le_mul_of_nonneg_left
                (norm_sin_sub_levyKhinchinCanonicalCentering_le_sqMinOne_local x)
                (abs_nonneg t)
    have hNum :
        ‖levyKhinchinSineKernelLocal t x‖ ≤
          (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) *
            ((12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x) := by
      calc
        ‖levyKhinchinSineKernelLocal t x‖
            = ‖levyKhinchinCanonicalKernelLocal t x +
                ((((t * (levyKhinchinCanonicalCentering x - Real.sin x) : ℝ) : ℂ)) *
                  Complex.I)‖ := by
                  rw [hEq]
        _ ≤ ‖levyKhinchinCanonicalKernelLocal t x‖ +
              ‖((((t * (levyKhinchinCanonicalCentering x - Real.sin x) : ℝ) : ℂ)) *
                Complex.I)‖ := norm_add_le _ _
        _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 + |t| * min (x ^ (2 : ℕ)) 1 := by
              exact add_le_add (norm_levyKhinchinCanonicalKernelLocal_le t x) hCorr
        _ = (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * min (x ^ (2 : ℕ)) 1 := by ring
        _ ≤ (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) *
              ((12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x) := by
              gcongr
              exact compactAverageInverseWeightBound_bridge_local x
    have hQuot :
        ‖levyKhinchinSineKernelLocal t x‖ / compactAverageKernel x ≤
          (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) := by
      exact (div_le_iff₀ hKernelPos).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hNum)
    have hFillNonneg : 0 ≤ 3 * t ^ (2 : ℕ) := by
      positivity
    calc
      ‖compactAverageReconstructionKernel_local t x‖
          = ‖levyKhinchinSineKernelLocal t x‖ / compactAverageKernel x := by
              simp [compactAverageReconstructionKernel_local, hx, Complex.norm_real,
                Real.norm_eq_abs, abs_of_pos hKernelPos]
      _ ≤ (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) := hQuot
      _ ≤ (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) + 3 * t ^ (2 : ℕ) :=
            le_add_of_nonneg_right hFillNonneg

/-- Helper for Theorem 16.17: the quotient kernel used to reconstruct the canonical kernel has the
correct filled value at `0`. -/
private lemma tendsto_compactAverageReconstructionQuotient_at_zero_local (t : ℝ) :
    Tendsto (fun x : ℝ ↦ levyKhinchinSineKernelLocal t x / ((compactAverageKernel x : ℝ) : ℂ))
      (𝓝[≠] 0)
      (𝓝 (-((3 * t ^ (2 : ℕ) : ℝ) : ℂ))) := by
  let num : ℝ → ℂ := fun x ↦
    (((Real.cos (t * x) - 1) / x ^ (2 : ℕ) : ℝ) : ℂ) +
      ((((Real.sin (t * x) - t * Real.sin x) / x ^ (2 : ℕ) : ℝ) : ℂ) * Complex.I)
  have hNum :
      Tendsto num (𝓝[≠] 0) (𝓝 (-((t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
    have hRe :
        Tendsto (fun x : ℝ ↦ ((Real.cos (t * x) - 1) / x ^ (2 : ℕ) : ℂ))
          (𝓝[≠] 0) (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
      convert
        (Complex.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_cos_sub_one_div_sq_at_zero_local t)) using 1
      · ext x
        simp
      · simp
    have hImReal :
        Tendsto
          (fun x : ℝ ↦ (Real.sin (t * x) - t * Real.sin x) / x ^ (2 : ℕ))
          (𝓝[≠] 0) (𝓝 0) := by
      have hMain := tendsto_sin_sub_linear_div_sq_at_zero_local t
      have hBase :
          Tendsto (fun x : ℝ ↦ -((Real.sin x - x) / x ^ (2 : ℕ))) (𝓝[≠] 0) (𝓝 0) := by
        simpa using (tendsto_sin_sub_linear_div_sq_at_zero_local (1 : ℝ)).neg
      have hCorrectionBase :
          Tendsto (fun x : ℝ ↦ (x - Real.sin x) / x ^ (2 : ℕ)) (𝓝[≠] 0) (𝓝 0) := by
        refine hBase.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        have hxpow2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
        field_simp [hxpow2]
        ring
      have hCorrection :
          Tendsto (fun x : ℝ ↦ t * ((x - Real.sin x) / x ^ (2 : ℕ)))
            (𝓝[≠] 0) (𝓝 0) := by
        simpa using tendsto_const_nhds.mul hCorrectionBase
      have hSum :
          Tendsto
            (fun x : ℝ ↦
              (Real.sin (t * x) - t * x) / x ^ (2 : ℕ) +
                t * ((x - Real.sin x) / x ^ (2 : ℕ)))
            (𝓝[≠] 0) (𝓝 0) := by
        simpa using hMain.add hCorrection
      refine hSum.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxpow2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
      field_simp [hxpow2]
      ring
    have hIm :
        Tendsto
          (fun x : ℝ ↦ (((Real.sin (t * x) - t * Real.sin x) / x ^ (2 : ℕ) : ℝ) : ℂ) *
            Complex.I)
          (𝓝[≠] 0) (𝓝 (0 * Complex.I)) := by
      exact ((Complex.continuous_ofReal.continuousAt.tendsto.comp hImReal).mul tendsto_const_nhds)
    simpa [num] using hRe.add hIm
  have hDen :
      Tendsto (fun x : ℝ ↦ ((compactAverageKernel x / x ^ (2 : ℕ) : ℝ) : ℂ))
        (𝓝[≠] 0) (𝓝 (((1 / 6 : ℝ) : ℂ))) := by
    exact
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_compactAverageKernel_div_sq_at_zero_local)
  have hScaled :
      Tendsto (fun x : ℝ ↦ num x / ((compactAverageKernel x / x ^ (2 : ℕ) : ℝ) : ℂ))
        (𝓝[≠] 0) (𝓝 ((-((t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) / (((1 / 6 : ℝ) : ℂ)))) := by
    exact hNum.div hDen (by norm_num)
  have hQuot :
      Tendsto (fun x : ℝ ↦ levyKhinchinSineKernelLocal t x / ((compactAverageKernel x : ℝ) : ℂ))
        (𝓝[≠] 0) (𝓝 ((-((t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) / (((1 / 6 : ℝ) : ℂ)))) := by
    refine hScaled.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with x hx hxBall
    have hxpow2 : ((x : ℂ) ^ (2 : ℕ)) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 hx
    have hKernelNe : ((compactAverageKernel x : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (compactAverageKernel_pos_of_ne_zero hx)
    have hNumEq :
        num x * (x : ℂ) ^ (2 : ℕ) = levyKhinchinSineKernelLocal t x := by
      have hx0 : x ≠ 0 := by simpa using hx
      dsimp [num, levyKhinchinSineKernelLocal]
      rw [Complex.exp_ofReal_mul_I]
      simp [div_eq_mul_inv]
      field_simp [hx0]
      ring_nf
    have hDenEq :
        ((compactAverageKernel x / x ^ (2 : ℕ) : ℝ) : ℂ) =
          ((compactAverageKernel x : ℝ) : ℂ) / (x : ℂ) ^ (2 : ℕ) := by
      norm_num [div_eq_mul_inv]
    calc
      num x / ((compactAverageKernel x / x ^ (2 : ℕ) : ℝ) : ℂ)
          = num x / (((compactAverageKernel x : ℝ) : ℂ) / (x : ℂ) ^ (2 : ℕ)) := by
              rw [hDenEq]
      _ = num x * (x : ℂ) ^ (2 : ℕ) / ((compactAverageKernel x : ℝ) : ℂ) := by
            field_simp [hxpow2, hKernelNe]
      _ = levyKhinchinSineKernelLocal t x / ((compactAverageKernel x : ℝ) : ℂ) := by
            rw [hNumEq]
  have hQuot' :
      Tendsto (fun x : ℝ ↦ levyKhinchinSineKernelLocal t x / ((compactAverageKernel x : ℝ) : ℂ))
        (𝓝[≠] 0) (𝓝 (-(↑t ^ (2 : ℕ) / 2 * 6))) := by
    simpa [div_eq_mul_inv] using hQuot
  have hQuot'' :
      Tendsto (fun x : ℝ ↦ levyKhinchinSineKernelLocal t x / ((compactAverageKernel x : ℝ) : ℂ))
        (𝓝[≠] 0) (𝓝 (-(((t ^ (2 : ℕ)) * 3 : ℝ) : ℂ))) := by
    convert hQuot' using 1
    congr 1
    calc
      -(((t ^ (2 : ℕ)) * 3 : ℝ) : ℂ) = -(↑t ^ (2 : ℕ) * 3) := by simp
      _ = -(↑t ^ (2 : ℕ) * ((1 / 2 : ℂ) * 6)) := by norm_num
      _ = -(↑t ^ (2 : ℕ) / 2 * 6) := by ring_nf
  simpa [mul_comm] using hQuot''

/-- Helper for Theorem 16.17: the compact-average reconstruction kernel is continuous. -/
private lemma continuous_compactAverageReconstructionKernel_local (t : ℝ) :
    Continuous (compactAverageReconstructionKernel_local t) := by
  refine continuous_iff_continuousAt.2 ?_
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [Metric.continuousAt_iff]
    intro ε hε
    rcases (Metric.tendsto_nhdsWithin_nhds.mp
        (tendsto_compactAverageReconstructionQuotient_at_zero_local t)) ε hε with
      ⟨δ, hδpos, hδ⟩
    refine ⟨δ, hδpos, ?_⟩
    intro y hyDist
    by_cases hy : y = 0
    · subst hy
      simpa [compactAverageReconstructionKernel_local] using hε
    · simpa [compactAverageReconstructionKernel_local, hy] using hδ hy hyDist
  · have hQuot :
      ContinuousAt (fun y : ℝ ↦ levyKhinchinSineKernelLocal t y / compactAverageKernel y) x :=
      by
        have hNum :
            ContinuousAt
              (fun y : ℝ ↦
                Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) - 1 -
                  (((t * Real.sin y : ℝ) : ℂ) * Complex.I)) x := by
          fun_prop
        have hNum' : ContinuousAt (fun y : ℝ ↦ levyKhinchinSineKernelLocal t y) x := by
          simpa [levyKhinchinSineKernelLocal] using hNum
        have hDen :
            ContinuousAt (fun y : ℝ ↦ ((compactAverageKernel y : ℝ) : ℂ)) x := by
          exact
            Complex.continuous_ofReal.continuousAt.comp
              continuous_compactAverageKernel.continuousAt
        have hDenNe : (((compactAverageKernel x : ℝ) : ℂ)) ≠ 0 := by
          exact_mod_cast (compactAverageKernel_pos_of_ne_zero hx).ne'
        exact ContinuousAt.div hNum' hDen hDenNe
    have hAway : ∀ᶠ y in 𝓝 x, y ≠ 0 := by
      filter_upwards [Metric.ball_mem_nhds x (half_pos (abs_pos.mpr hx))] with y hy
      have hyDist : |y - x| < |x| / 2 := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hy
      intro hy0
      subst hy0
      have hxabs : 0 < |x| := abs_pos.mpr hx
      have : |x| < |x| / 2 := by simpa using hyDist
      nlinarith
    exact hQuot.congr_of_eventuallyEq <|
      hAway.mono fun y hy ↦ by simp [compactAverageReconstructionKernel_local, hy]

/-- Helper for Theorem 16.17: every finite measure integrates the compact-average reconstruction
kernel because the kernel is measurable and uniformly bounded. -/
private lemma integrable_compactAverageReconstructionKernel_of_isFiniteMeasure_local
    (t : ℝ) (η : Measure ℝ) [IsFiniteMeasure η] :
    Integrable (compactAverageReconstructionKernel_local t) η := by
  let C : ℝ := (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) + 3 * t ^ (2 : ℕ)
  have hBound : Integrable (fun _ : ℝ ↦ C) η := integrable_const C
  -- Proof comment: a measurable complex-valued function dominated by one real constant is
  -- integrable against every finite measure.
  refine hBound.mono' (measurable_compactAverageReconstructionKernel_local t).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    have hCNonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    simpa [C, Real.norm_eq_abs, abs_of_nonneg hCNonneg] using
      norm_compactAverageReconstructionKernel_local_le t x

/-- Helper for Theorem 16.17: multiplying the reconstruction quotient kernel by
`compactAverageKernel` recovers the smooth sine-centered Lévy kernel pointwise. -/
private lemma compactAverageReconstructionKernel_mul_kernel_local
    (t x : ℝ) :
    ((compactAverageKernel x : ℝ) : ℂ) * compactAverageReconstructionKernel_local t x =
      levyKhinchinSineKernelLocal t x := by
  by_cases hx : x = 0
  · subst hx
    -- Proof comment: at the origin both sides vanish because the canonical kernel and the
    -- compact-average weight are zero there.
    simp [compactAverageReconstructionKernel_local, compactAverageKernel_zero,
      levyKhinchinSineKernelLocal]
  · have hkernelNe : ((compactAverageKernel x : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (compactAverageKernel_pos_of_ne_zero hx)
    -- Proof comment: away from `0`, the quotient definition is exact and cancellation is legal.
    simp [compactAverageReconstructionKernel_local, hx]
    field_simp [hkernelNe]

/-- Helper for Theorem 16.17: integrating the reconstruction quotient kernel against the
compact-average exact-root auxiliary measure rewrites to the sine-centered kernel integral against
the exact-root Lévy measure. -/
private lemma integral_compactAverageReconstructionKernel_exactRootApprox_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
      ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) =
      ∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂(exactRootApproxTriple μroot n).ν := by
  -- Proof comment: unfold the `withDensity` definition of the exact-root auxiliary measure and
  -- absorb the compact-average weight into the quotient kernel.
  change
    ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
      ((exactRootApproxTriple μroot n).ν.withDensity
        (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) =
      ∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂(exactRootApproxTriple μroot n).ν
  rw [integral_withDensity_eq_integral_toReal_smul
    measurable_compactAverageKernel.ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
  have hnonneg : 0 ≤ compactAverageKernel x := compactAverageKernel_nonneg x
  calc
    (ENNReal.ofReal (compactAverageKernel x)).toReal • compactAverageReconstructionKernel_local t x
        = ((compactAverageKernel x : ℝ) : ℂ) * compactAverageReconstructionKernel_local t x := by
            simp [hnonneg, smul_eq_mul]
    _ = levyKhinchinSineKernelLocal t x :=
          compactAverageReconstructionKernel_mul_kernel_local t x

/-- Helper for Theorem 16.17: recovering the jump measure from the exact-root compact-average
auxiliary measure returns the original exact-root jump intensity. -/
private lemma compactAverageRecoveredJumpMeasure_exactRootApprox_eq_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) :
    compactAverageRecoveredJumpMeasure_local (exactRootApproxCompactAverageMeasure μroot n) =
      (exactRootApproxTriple μroot n).ν := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  have hν : IsCanonicalMeasure ν :=
    (exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).isCanonicalTriple.isCanonicalMeasure
  -- Proof comment: puncturing the exact-root compact-average auxiliary measure leaves precisely
  -- the compact-average weighted jump intensity, and the inverse density then removes that weight.
  calc
    compactAverageRecoveredJumpMeasure_local (exactRootApproxCompactAverageMeasure μroot n)
        =
      (((ν.restrict ({0}ᶜ : Set ℝ)).withDensity
          (fun x ↦ ENNReal.ofReal (compactAverageKernel x))).withDensity
        (fun x ↦ (ENNReal.ofReal (compactAverageKernel x))⁻¹)) := by
          rw [compactAverageRecoveredJumpMeasure_local, exactRootApproxCompactAverageMeasure]
          exact congrArg
            (fun μ : Measure ℝ ↦
              μ.withDensity (fun x ↦ (ENNReal.ofReal (compactAverageKernel x))⁻¹))
            (MeasureTheory.restrict_withDensity ((measurableSet_singleton (0 : ℝ)).compl)
              (μ := ν) (f := fun x ↦ ENNReal.ofReal (compactAverageKernel x)))
    _ = ν.restrict ({0}ᶜ : Set ℝ) := by
          exact withDensity_compactAverageKernel_inv_same_restrict_compl_singleton ν
    _ = ν.restrict ({0} : Set ℝ) + ν.restrict ({0}ᶜ : Set ℝ) := by
          rw [Measure.restrict_singleton, hν.measure_singleton_zero, zero_smul, zero_add]
    _ = ν := by
          simpa using
            (Measure.restrict_add_restrict_compl (μ := ν) (measurableSet_singleton (0 : ℝ)))

/-- Helper for Theorem 16.17: integrating the reconstruction kernel against the weighted
recovered jump measure rewrites to the sine-centered Lévy kernel integral. -/
private lemma integral_compactAverageReconstructionKernel_recovered_local
    (η : FiniteMeasure ℝ) (t : ℝ) :
    ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
      ((compactAverageRecoveredJumpMeasure_local η).withDensity
        (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) =
      ∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂(compactAverageRecoveredJumpMeasure_local η) :=
    by
  -- Proof comment: push the compact-average density back through the integral so the quotient
  -- kernel collapses to the sine-centered Lévy kernel pointwise.
  rw [integral_withDensity_eq_integral_toReal_smul
    measurable_compactAverageKernel.ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
  have hnonneg : 0 ≤ compactAverageKernel x := compactAverageKernel_nonneg x
  calc
    (ENNReal.ofReal (compactAverageKernel x)).toReal • compactAverageReconstructionKernel_local t x
        = ((compactAverageKernel x : ℝ) : ℂ) * compactAverageReconstructionKernel_local t x := by
            simp [hnonneg, smul_eq_mul]
    _ = levyKhinchinSineKernelLocal t x :=
          compactAverageReconstructionKernel_mul_kernel_local t x

/-- Helper for Theorem 16.17: the drift adjustment needed to rewrite the exact-root exponent with
the smooth centering `Real.sin`. -/
private noncomputable def exactRootApproxReconstructionDrift_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) : ℝ :=
  (exactRootApproxTriple μroot n).b +
    ∫ x : ℝ, (Real.sin x - levyKhinchinCanonicalCentering x) ∂(exactRootApproxTriple μroot n).ν

/-- Helper for Theorem 16.17: the jump measure recovered from a compact-average auxiliary finite
measure is canonical. -/
private lemma isCanonicalMeasure_compactAverageRecoveredJumpMeasure_local
    (η : FiniteMeasure ℝ) :
    IsCanonicalMeasure (compactAverageRecoveredJumpMeasure_local η) := by
  -- Proof comment: rewrite the recovered measure through the inverse compact-average density on
  -- `η.restrict ({0}ᶜ)`, then use `compactAverageInverseWeightBound_local` to dominate
  -- `x ↦ min (x^2) 1 / compactAverageKernel x` by one global constant.
  refine ⟨?_, ?_⟩
  · -- Proof comment: the recovered measure is supported on `{0}ᶜ`, so the singleton at `0`
    -- receives zero mass.
    rw [compactAverageRecoveredJumpMeasure_local, withDensity_apply _ (measurableSet_singleton 0)]
    simp
  · let μ : Measure ℝ := (η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)
    let C : ℝ := 12 * Real.pi ^ (2 : ℕ)
    have hInvLtTop :
        ∀ᵐ x ∂μ, (ENNReal.ofReal (compactAverageKernel x))⁻¹ < ⊤ := by
      filter_upwards [compactAverageKernel_ae_ne_zero_restrict_compl_singleton (η : Measure ℝ)] with x hx
      have hKernelPos : 0 < compactAverageKernel x := by
        exact lt_of_le_of_ne (compactAverageKernel_nonneg x) (by simpa [eq_comm] using hx)
      have hx0 : ENNReal.ofReal (compactAverageKernel x) ≠ 0 := by
        exact ne_of_gt (ENNReal.ofReal_pos.mpr hKernelPos)
      simpa [hx0]
    rw [compactAverageRecoveredJumpMeasure_local]
    rw [integrable_withDensity_iff measurable_compactAverageKernel.ennreal_ofReal.inv hInvLtTop]
    letI : IsFiniteMeasure μ := by
      dsimp [μ]
      infer_instance
    have hMeas :
        AEStronglyMeasurable
          (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1 * ((ENNReal.ofReal (compactAverageKernel x))⁻¹).toReal)
          μ := by
      exact
        (((measurable_id.pow_const 2).min measurable_const).mul
          ((measurable_compactAverageKernel.ennreal_ofReal.inv).ennreal_toReal)).aestronglyMeasurable
    refine (integrable_const C).mono' hMeas ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      by_cases hx : x = 0
      · subst hx
        have hC : 0 ≤ C := by
          dsimp [C]
          positivity
        simpa [C, compactAverageKernel] using hC
      · have hKernelPos : 0 < compactAverageKernel x := by
          exact compactAverageKernel_pos_of_ne_zero hx
        have hMinNonneg : 0 ≤ min (x ^ (2 : ℕ)) 1 := by positivity
        have hToRealInv :
            ((ENNReal.ofReal (compactAverageKernel x))⁻¹).toReal =
              (compactAverageKernel x)⁻¹ := by
          rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal]
          simp [compactAverageKernel_nonneg x]
        have hBound :
            min (x ^ (2 : ℕ)) 1 / compactAverageKernel x ≤ C := by
          exact
            (div_le_iff₀ hKernelPos).2
              (by
                simpa [C, mul_comm, mul_left_comm, mul_assoc] using
                  compactAverageInverseWeightBound_bridge_local x)
        have hInvNonneg : 0 ≤ (compactAverageKernel x)⁻¹ := by positivity
        simpa [C, Real.norm_eq_abs, abs_of_nonneg hMinNonneg, abs_of_nonneg hInvNonneg,
          abs_of_pos hKernelPos, hToRealInv, div_eq_mul_inv, mul_comm, mul_left_comm,
          mul_assoc] using hBound

/-- Helper for Theorem 16.17: the recovered compact-average auxiliary finite measure determines
the zero-drift Gaussian-plus-jump part of the sine-centered Lévy--Khinchin exponent. -/
private lemma compactAverageRecoveredZeroDriftExponent_local
    (η : FiniteMeasure ℝ) (t : ℝ) :
    let σ2 : ℝ := 6 * (((η : Measure ℝ) ({0} : Set ℝ)).toReal)
    let ν := compactAverageRecoveredJumpMeasure_local η
    levyKhinchinExponentWithCentering σ2 0 ν Real.sin t =
      ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(η : Measure ℝ) := by
  -- Proof comment: split `η` into its atom at `0` plus the weighted recovered jump measure,
  -- identify the atom contribution with the Gaussian quadratic term, and rewrite the weighted
  -- contribution through `integral_compactAverageReconstructionKernel_recovered_local`.
  dsimp
  let atomMass : ENNReal := ((η : Measure ℝ) ({0} : Set ℝ))
  let ν := compactAverageRecoveredJumpMeasure_local η
  have hIntAtom :
      Integrable (compactAverageReconstructionKernel_local t) (atomMass • Measure.dirac 0) := by
    letI : IsFiniteMeasure (atomMass • Measure.dirac (0 : ℝ)) := by
      refine ⟨?_⟩
      simp [atomMass]
    exact
      integrable_compactAverageReconstructionKernel_of_isFiniteMeasure_local
        t (atomMass • Measure.dirac 0)
  have hIntWeighted :
      Integrable (compactAverageReconstructionKernel_local t)
        (ν.withDensity (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) := by
    rw [compactAverageRecoveredJumpMeasure_weighted_eq_restrict_compl_local]
    letI : IsFiniteMeasure ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) := by
      infer_instance
    exact
      integrable_compactAverageReconstructionKernel_of_isFiniteMeasure_local
        t ((η : Measure ℝ).restrict ({0}ᶜ : Set ℝ))
  have hAtomEval :
      ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(atomMass • Measure.dirac 0) =
        (((-(6 * atomMass.toReal / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) := by
    -- Proof comment: the filled value at `0` turns the atom contribution into the Gaussian
    -- quadratic term.
    rw [integral_smul_measure, integral_dirac]
    simp [atomMass, compactAverageReconstructionKernel_local]
    change ((atomMass.toReal : ℂ) * (3 * ↑t ^ (2 : ℕ))) =
      6 * ↑(atomMass.toReal) / 2 * ↑t ^ (2 : ℕ)
    ring
  calc
    levyKhinchinExponentWithCentering (6 * atomMass.toReal) 0 ν Real.sin t =
        (((-(6 * atomMass.toReal / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          ∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂ν := by
            simp [levyKhinchinExponentWithCentering, levyKhinchinSineKernelLocal, atomMass, ν]
    _ =
        ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(atomMass • Measure.dirac 0) +
          ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
            (ν.withDensity (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) := by
            rw [hAtomEval, integral_compactAverageReconstructionKernel_recovered_local]
    _ =
        ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
          (atomMass • Measure.dirac 0 +
            ν.withDensity (fun x ↦ ENNReal.ofReal (compactAverageKernel x))) := by
            rw [integral_add_measure hIntAtom hIntWeighted]
    _ = ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(η : Measure ℝ) := by
            rw [compactAverageRecoveredJumpMeasure_decomposition_local η]

/-- Helper for Theorem 16.17: adding a drift coefficient to a fixed Gaussian/jump pair
contributes exactly the linear imaginary phase term in the sine-centered Lévy--Khintchin
exponent. -/
private lemma levyKhinchinExponentWithSineCentering_add_drift_eq_local
    (σ2 b : ℝ) (ν : Measure ℝ) (t : ℝ) :
    levyKhinchinExponentWithCentering σ2 b ν Real.sin t =
      levyKhinchinExponentWithCentering σ2 0 ν Real.sin t +
        ((((b * t : ℝ) : ℂ)) * Complex.I) := by
  -- Proof comment: the Gaussian and jump terms stay fixed, so only the explicit drift line
  -- changes.
  simp [levyKhinchinExponentWithCentering]
  ring

/-- Helper for Theorem 16.17: each exact-root exponent splits into its compact-average
reconstruction integral plus the explicit drift line from the centering constant. -/
private lemma exactRootApproxExponent_eq_reconstructionIntegral_add_drift_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    levyKhinchinExponent (exactRootApproxTriple μroot n) t =
      (∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
          ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ)) +
        ((((exactRootApproxReconstructionDrift_local μroot n * t : ℝ) : ℂ) * Complex.I)) := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  have hν : IsCanonicalMeasure ν :=
    (exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).isCanonicalTriple.isCanonicalMeasure
  have hDiffInt :
      Integrable (fun x : ℝ ↦ Real.sin x - levyKhinchinCanonicalCentering x) ν :=
    integrable_sin_sub_levyKhinchinCanonicalCentering_local hν
  have hChange :
      levyKhinchinExponent (exactRootApproxTriple μroot n) t =
        levyKhinchinExponentWithCentering
          0 (exactRootApproxReconstructionDrift_local μroot n) ν Real.sin t := by
    have hChangeFn :=
      levyKhinchinExponentWithCentering_changeCentering
        0 (exactRootApproxTriple μroot n).b ν hν Real.sin hDiffInt
    have hChangeAt := congrArg (fun f : ℝ → ℂ ↦ f t) hChangeFn
    simpa [exactRootApproxReconstructionDrift_local, ν, levyKhinchinExponent] using hChangeAt.symm
  have hZeroDrift :
      levyKhinchinExponentWithCentering 0 0 ν Real.sin t =
        ∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂ν := by
    -- Proof comment: when the Gaussian and drift terms vanish, the exponent is exactly the
    -- sine-centered jump-kernel integral.
    simp [levyKhinchinExponentWithCentering, levyKhinchinSineKernelLocal, ν]
  -- Proof comment: peel off the explicit linear drift, then transport the zero-drift integral
  -- through the compact-average auxiliary measure.
  calc
    levyKhinchinExponent (exactRootApproxTriple μroot n) t =
        levyKhinchinExponentWithCentering 0 0 ν Real.sin t +
          ((((exactRootApproxReconstructionDrift_local μroot n * t : ℝ) : ℂ) * Complex.I)) := by
            rw [hChange]
            rw [levyKhinchinExponentWithSineCentering_add_drift_eq_local]
    _ =
        (∫ x : ℝ, levyKhinchinSineKernelLocal t x ∂ν) +
          ((((exactRootApproxReconstructionDrift_local μroot n * t : ℝ) : ℂ) * Complex.I)) := by
            rw [hZeroDrift]
    _ =
        (∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
            ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ)) +
          ((((exactRootApproxReconstructionDrift_local μroot n * t : ℝ) : ℂ) * Complex.I)) := by
            rw [integral_compactAverageReconstructionKernel_exactRootApprox_local]

/-- Helper for Theorem 16.17: the shifted oscillatory phase is integrable on the compact averaging
window times any finite jump measure. -/
private lemma integrable_compactAverageShiftFourier_prod_local
    {ν : Measure ℝ} [IsFiniteMeasure ν] (t : ℝ) :
    Integrable
      (Function.uncurry fun s x : ℝ ↦
        Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)))
      ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν) := by
  -- Proof comment: the integrand is continuous on the product, and its norm is identically `1`,
  -- so integrability follows by domination from the constant function over the finite product
  -- measure.
  have hCont :
      Continuous fun p : ℝ × ℝ ↦
        Complex.exp (((((t + p.1) * p.2 : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hAEMeas :
      AEStronglyMeasurable
        (Function.uncurry fun s x : ℝ ↦
          Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)))
        ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν) := by
    simpa [Function.uncurry] using hCont.aestronglyMeasurable
  letI : IsFiniteMeasure (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    refine ⟨?_⟩
    simp [Set.uIoc, Real.volume_Ioc]
  letI : IsFiniteMeasure ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν) := by
    infer_instance
  refine Integrable.mono'
      (integrable_const
        (μ := ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν))
        (1 : ℝ))
      hAEMeas ?_
  exact Filter.Eventually.of_forall fun p ↦ by
    simpa [Function.uncurry] using
      (le_of_eq (Complex.norm_exp_ofReal_mul_I ((t + p.1) * p.2)))

/-- Helper for Theorem 16.17: extract the scalar factor and swap the compact-average Fourier
integrals in the exact `(s, x)` spelling used downstream. -/
private lemma shiftedFourierCompactAverageBridge_local
    {ν : Measure ℝ} [IsFiniteMeasure ν] (t : ℝ)
    (hShiftProdIntegrable :
      Integrable
        (Function.uncurry fun s x : ℝ ↦
          Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)))
        ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν)) :
    ∫ x : ℝ,
        ((1 / 2 : ℂ) *
          ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) ∂ν =
      ((1 / 2 : ℂ) *
        ∫ s in (-1 : ℝ)..1,
          ∫ x : ℝ, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) ∂ν) := by
  -- Proof comment: first pull the constant `1 / 2` through the outer integral, then apply the
  -- interval-integral Fubini theorem in the exact `(s, x)` binder order used downstream.
  let F : ℝ → ℝ → ℂ := fun s x ↦ Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))
  let G : ℝ → ℂ := fun x ↦ ∫ s in (-1 : ℝ)..1, F s x
  have hConst :
      ∫ x : ℝ, ((1 / 2 : ℂ) * G x) ∂ν =
        (1 / 2 : ℂ) * ∫ x : ℝ, G x ∂ν := by
    simpa using
      (integral_const_mul (μ := ν) (r := (1 / 2 : ℂ)) (f := G))
  calc
    ∫ x : ℝ,
        ((1 / 2 : ℂ) *
          ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) ∂ν =
        ∫ x : ℝ, ((1 / 2 : ℂ) * G x) ∂ν := by
            simp [F, G]
    _ = (1 / 2 : ℂ) * ∫ x : ℝ, G x ∂ν := hConst
    _ = ((1 / 2 : ℂ) * ∫ s in (-1 : ℝ)..1, ∫ x : ℝ, F s x ∂ν) := by
          congr 1
          simpa [G, F] using
            (MeasureTheory.intervalIntegral_integral_swap
              (μ := ν)
              (a := (-1 : ℝ))
              (b := (1 : ℝ))
              (f := F)
              (by simpa [F] using hShiftProdIntegrable)).symm
    _ =
        ((1 / 2 : ℂ) *
          ∫ s in (-1 : ℝ)..1,
            ∫ x : ℝ, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) ∂ν) := by
              simp [F]

/-- Helper for Theorem 16.17: averaging the pure oscillatory factor over `[-1,1]` produces
`2 sinc(x)`. -/
private lemma compactAverageUnitWindowIntegral_eq_sinc_local (x : ℝ) :
    ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) =
      2 * (Real.sinc x : ℂ) := by
  -- Proof comment: specialize `integral_charFun_Icc` to the Dirac mass at `x`, then rewrite the
  -- characteristic function of that Dirac law.
  calc
    ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)
        = ∫ s in (-1 : ℝ)..1, charFun (Measure.dirac x) s := by
            refine intervalIntegral.integral_congr fun s _ ↦ ?_
            rw [MeasureTheory.charFun_dirac]
            rw [show inner ℝ x s = x * s by simpa using (RCLike.inner_apply' (𝕜 := ℝ) x s)]
            congr 1
            ring
    _ = 2 * (Real.sinc x : ℂ) := by
          simpa using
            (MeasureTheory.integral_charFun_Icc (μ := Measure.dirac x) (r := (1 : ℝ))
              zero_lt_one)

/-- Helper for Theorem 16.17: the compact-average exact-root auxiliary measure has
characteristic function equal to the compact-averaged exact-root exponent. -/
private lemma exactRootApproxCompactAverageMeasure_charFun_eq_local
    (μroot : ℕ+ → ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t =
      levyKhinchinExponent (exactRootApproxTriple μroot n) t -
        ((1 / 2 : ℂ) *
          ∫ s in (-1 : ℝ)..1, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) := by
  let ν : Measure ℝ := (exactRootApproxTriple μroot n).ν
  letI : IsFiniteMeasure ν := by
    change IsFiniteMeasure (((exactRootApproxIntensity μroot n : FiniteMeasure ℝ) : Measure ℝ))
    infer_instance
  have hFourier :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) ν :=
    integrable_fourierKernel_of_isFiniteMeasure ν t
  have hRaw :
      Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
    integrable_compoundPoissonKernel_of_isFiniteMeasure_local ν t
  letI : IsFiniteMeasure (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    refine ⟨?_⟩
    simpa [Set.uIoc, min_eq_left (show (-1 : ℝ) ≤ 1 by norm_num),
      max_eq_right (show (-1 : ℝ) ≤ 1 by norm_num), Real.volume_Ioc] using
      (show volume (Set.Ioc (-1 : ℝ) 1) < ⊤ by norm_num [Real.volume_Ioc])
  have hShiftProdIntegrable :
      Integrable
        (Function.uncurry fun s x : ℝ ↦
          Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)))
        ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν) := by
    exact integrable_compactAverageShiftFourier_prod_local (ν := ν) t
  have hShiftIntervalCont :
      Continuous fun x : ℝ ↦
        ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) := by
    have hUncurry :
        Continuous (Function.uncurry fun x s : ℝ ↦
          Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) := by
      fun_prop
    simpa [Function.uncurry] using
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume)
        (f := fun x s : ℝ ↦ Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)))
        hUncurry (-1 : ℝ) 1)
  have hShiftIntervalIntegrable :
      Integrable
        (fun x : ℝ ↦
          ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) ν := by
    refine (integrable_const (2 : ℝ)).mono' hShiftIntervalCont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hNorm :
          ‖∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))‖ ≤
            (1 : ℝ) * |(1 : ℝ) - (-1 : ℝ)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro s hs
        simpa using (le_of_eq (Complex.norm_exp_ofReal_mul_I ((t + s) * x)))
      have hNorm' :
          ‖∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))‖ ≤ 2 := by
        calc
          ‖∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))‖ ≤
              (1 : ℝ) * |(1 : ℝ) - (-1 : ℝ)| := hNorm
          _ = 2 := by norm_num
      simpa using hNorm'
  have hShiftFactor :
      ∀ x : ℝ,
        ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by
    intro x
    calc
      ∫ s in (-1 : ℝ)..1, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) =
          ∫ s in (-1 : ℝ)..1,
            Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by
              -- Proof comment: split the shifted phase into the fixed `t` part and the averaging
              -- variable `s` part before pulling the constant factor outside the interval
              -- integral.
              refine intervalIntegral.integral_congr fun s _ ↦ ?_
              have hArg :
                  (((((t + s) * x : ℝ) : ℂ) * Complex.I)) =
                    ((((t * x : ℝ) : ℂ) + (((s * x : ℝ) : ℂ))) * Complex.I) := by
                    calc
                      (((((t + s) * x : ℝ) : ℂ) * Complex.I)) =
                          ((((t * x + s * x : ℝ) : ℂ)) * Complex.I) := by
                            congr 1
                            ring
                      _ = ((((t * x : ℝ) : ℂ) + (((s * x : ℝ) : ℂ))) * Complex.I) := by
                            simp
              rw [hArg, add_mul, Complex.exp_add]
      _ =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by
              exact
                intervalIntegral.integral_const_mul
                  (a := (-1 : ℝ))
                  (b := (1 : ℝ))
                  (r := Complex.exp (((t * x : ℝ) : ℂ) * Complex.I))
                  (f := fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I))
  have hPointwise :
      ∀ x : ℝ,
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * compactAverageKernel x =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
            ((1 / 2 : ℂ) *
              ∫ s in (-1 : ℝ)..1,
                Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) := by
    intro x
    calc
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * compactAverageKernel x =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (1 - Real.sinc x) := by
            simp [compactAverageKernel]
      _ =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (Real.sinc x : ℂ)) := by
              ring
      _ =
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
            ((1 / 2 : ℂ) *
              ∫ s in (-1 : ℝ)..1,
                Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) := by
              -- Proof comment: the compact-average kernel is exactly the half-interval average of
              -- the shifted oscillatory phase.
              rw [hShiftFactor x, intervalIntegralExpMulCompactAverageBridge_local]
              ring
  have hExpEq :
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂ν =
        levyKhinchinExponent (exactRootApproxTriple μroot n) t +
          ∫ x : ℝ, (1 : ℂ) ∂ν := by
    -- Proof comment: rewrite the Fourier phase as the raw exact-root kernel plus the constant
    -- `1` contribution.
    calc
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂ν =
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) + (1 : ℂ) ∂ν := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
              ring
      _ =
          ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν +
            ∫ x : ℝ, (1 : ℂ) ∂ν := by
              rw [integral_add hRaw (integrable_const (1 : ℂ))]
      _ =
          levyKhinchinExponent (exactRootApproxTriple μroot n) t +
            ∫ x : ℝ, (1 : ℂ) ∂ν := by
              rw [exactRootApproxExponent_eq_rawKernelIntegral_local]
  have hExpEqShift :
      ∀ s : ℝ,
        ∫ x : ℝ, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) ∂ν =
          levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) +
            ∫ x : ℝ, (1 : ℂ) ∂ν := by
    intro s
    have hRawShift :
        Integrable (fun x : ℝ ↦ Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) - 1) ν :=
      integrable_compoundPoissonKernel_of_isFiniteMeasure_local ν (t + s)
    calc
      ∫ x : ℝ, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) ∂ν =
          ∫ x : ℝ,
            (Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) - 1) + (1 : ℂ) ∂ν := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
              ring
      _ =
          ∫ x : ℝ, (Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) - 1) ∂ν +
            ∫ x : ℝ, (1 : ℂ) ∂ν := by
              rw [integral_add hRawShift (integrable_const (1 : ℂ))]
      _ =
          levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) +
            ∫ x : ℝ, (1 : ℂ) ∂ν := by
              rw [exactRootApproxExponent_eq_rawKernelIntegral_local]
  have hApproxIntervalIntegrable :
      IntervalIntegrable
        (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s))
        volume (-1 : ℝ) 1 := by
    have hCont :
        Continuous (fun s : ℝ ↦ levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) := by
      exact
        (continuousLevyKhinchinExponentLocal
          (exactRootApproxTriple_hasLevyKhinchinRepresentation μroot n).isCanonicalTriple).comp
          (continuous_const.add continuous_id)
    exact hCont.intervalIntegrable (μ := volume) (-1 : ℝ) 1
  -- Proof comment: rewrite the weighted characteristic function using the compact-average
  -- kernel, swap the interval and measure integrals, and cancel the constant mass term.
  calc
    charFun ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) t =
        ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * compactAverageKernel x ∂ν := by
          rw [MeasureTheory.charFun_apply_real]
          simpa [ν, exactRootApproxCompactAverageMeasure] using
            compactAverageWeightedFourierIntegral_eq_local (ν := ν) t
    _ =
        ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂ν -
          ∫ x : ℝ,
            ((1 / 2 : ℂ) *
              ∫ s in (-1 : ℝ)..1,
                Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I))) ∂ν := by
          refine (integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ hPointwise x).trans ?_
          rw [integral_sub hFourier (hShiftIntervalIntegrable.const_mul (1 / 2 : ℂ))]
    _ =
        ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂ν -
          ((1 / 2 : ℂ) *
            ∫ s in (-1 : ℝ)..1,
              ∫ x : ℝ, Complex.exp (((((t + s) * x : ℝ) : ℂ) * Complex.I)) ∂ν) := by
          -- Route correction: replace the earlier pair of alpha-renaming adapters by one exact
          -- bridge that keeps the `(s, x)` binder spelling fixed through scalar extraction and
          -- the Fubini swap.
          congr 1
          rw [shiftedFourierCompactAverageBridge_local (ν := ν) t hShiftProdIntegrable]
    _ =
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t +
            ∫ x : ℝ, (1 : ℂ) ∂ν) -
          ((1 / 2 : ℂ) *
            ∫ s in (-1 : ℝ)..1,
              (levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s) +
                ∫ x : ℝ, (1 : ℂ) ∂ν)) := by
          rw [hExpEq]
          congr 1
          exact congrArg
            (fun z : ℂ ↦ ((1 / 2 : ℂ) * z))
            (intervalIntegral.integral_congr fun s _ ↦ by
              rw [hExpEqShift s])
    _ =
        (levyKhinchinExponent (exactRootApproxTriple μroot n) t +
            ∫ x : ℝ, (1 : ℂ) ∂ν) -
          ((1 / 2 : ℂ) *
            ((∫ s in (-1 : ℝ)..1,
                levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) +
              ∫ s in (-1 : ℝ)..1, (∫ x : ℝ, (1 : ℂ) ∂ν))) := by
          rw [intervalIntegral.integral_add hApproxIntervalIntegrable intervalIntegrable_const]
    _ =
        levyKhinchinExponent (exactRootApproxTriple μroot n) t -
          ((1 / 2 : ℂ) *
            ∫ s in (-1 : ℝ)..1,
              levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)) := by
          have hrealOne : (ν.real Set.univ : ℂ) = ν.real Set.univ • (1 : ℂ) := by
            simp
          have hConstInt : ∫ x : ℝ, (1 : ℂ) ∂ν = (ν.real Set.univ : ℂ) := by
            rw [integral_const]
            exact hrealOne.symm
          set A : ℂ :=
            ∫ s in (-1 : ℝ)..1, levyKhinchinExponent (exactRootApproxTriple μroot n) (t + s)
          rw [intervalIntegral.integral_const, hConstInt]
          have hLength :
              ((1 - -1 : ℝ) • (ν.real Set.univ : ℂ)) = (2 : ℂ) * (ν.real Set.univ : ℂ) := by
            norm_num [smul_eq_mul]
          calc
            levyKhinchinExponent (exactRootApproxTriple μroot n) t + (ν.real Set.univ : ℂ) -
                ((1 / 2 : ℂ) * (A + ((1 - -1 : ℝ) • (ν.real Set.univ : ℂ)))) =
              levyKhinchinExponent (exactRootApproxTriple μroot n) t + (ν.real Set.univ : ℂ) -
                ((1 / 2 : ℂ) * (A + (2 : ℂ) * (ν.real Set.univ : ℂ))) := by
                  rw [hLength]
            _ =
              levyKhinchinExponent (exactRootApproxTriple μroot n) t - ((1 / 2 : ℂ) * A) := by
                ring

/-- Helper for Theorem 16.17: evaluating the compact-average exact-root auxiliary characteristic
function at `0` identifies the complex mass limit needed for the finite-measure existence step. -/
private lemma exactRootApproxCompactAverageMass_tendsto_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    Tendsto
      (fun n : ℕ ↦ (((exactRootApproxCompactAverageMeasure μroot n).mass : NNReal) : ℂ))
      atTop
      (𝓝 ((compactAverageExpLift Ψ) 0)) := by
  have hChar :
      Tendsto
        (fun n : ℕ ↦
          charFun ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ) 0)
        atTop
        (𝓝 ((compactAverageExpLift Ψ) 0)) := by
    refine
      (exactRootApproxCompactAverageExponent_tendsto_local
        (μ := μ) μroot hroot hΨ0 hΨexp 0).congr' ?_
    filter_upwards [] with n
    symm
    exact exactRootApproxCompactAverageMeasure_charFun_eq_local μroot n 0
  -- Proof comment: at zero frequency, the characteristic function of a finite measure is its
  -- total mass.
  refine hChar.congr' ?_
  filter_upwards [] with n
  rw [charFun_finiteMeasure_zero_eq_mass_local]

/-- Helper for Theorem 16.17: the compact-averaged lift takes a real value at `0` because it is
the limit of finite-measure masses. -/
private lemma compactAverageExpLift_zero_im_eq_zero_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    Complex.im ((compactAverageExpLift Ψ) 0) = 0 := by
  have him :
      Tendsto
        (fun n : ℕ ↦
          Complex.im ((((exactRootApproxCompactAverageMeasure μroot n).mass : NNReal) : ℂ)))
        atTop
        (𝓝 (Complex.im ((compactAverageExpLift Ψ) 0))) :=
    (Complex.continuous_im.continuousAt.tendsto.comp <|
      exactRootApproxCompactAverageMass_tendsto_local (μ := μ) μroot hroot hΨ0 hΨexp)
  have hzero :
      Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (Complex.im ((compactAverageExpLift Ψ) 0))) := by
    simpa using him
  exact tendsto_nhds_unique hzero tendsto_const_nhds

/-- Helper for Theorem 16.17: the compact-average auxiliary masses converge in `NNReal` to the
real part of the zero-frequency compact-average lift. -/
private lemma exactRootApproxCompactAverageMass_tendsto_nnreal_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t) :
    Tendsto
      (fun n : ℕ ↦ (exactRootApproxCompactAverageMeasure μroot n).mass)
      atTop
      (𝓝 (Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0)))) := by
  have hRe :
      Tendsto
        (fun n : ℕ ↦ ((exactRootApproxCompactAverageMeasure μroot n).mass : ℝ))
        atTop
        (𝓝 (Complex.re ((compactAverageExpLift Ψ) 0))) := by
    -- Proof comment: take real parts of the existing complex mass limit.
    simpa using
      (Complex.continuous_re.continuousAt.tendsto.comp
        (exactRootApproxCompactAverageMass_tendsto_local
          (μ := μ) μroot hroot hΨ0 hΨexp))
  -- Proof comment: applying `NNReal.ofReal` to the real-valued mass limit rewrites the source
  -- sequence back to the original `NNReal` masses.
  refine ((continuous_real_toNNReal.tendsto _).comp hRe).congr' ?_
  filter_upwards [] with n
  simp

/-- Helper for Theorem 16.17: on the non-Dirac branch, the compact-average characteristic-function
surface is realized by an auxiliary finite measure together with its normalized weak limit. -/
private lemma exists_compactAverageAuxFiniteMeasure_with_normalizedLimit_of_exactRoots_nonDirac_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (hDirac : ¬ ∃ b : ℝ, μ = diracProba b) :
    ∃ ρ : ProbabilityMeasure ℝ, ∃ η : FiniteMeasure ℝ,
      η = (Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0))) • ρ.toFiniteMeasure ∧
      (∀ t : ℝ, charFun ((η : FiniteMeasure ℝ) : Measure ℝ) t = (compactAverageExpLift Ψ) t) ∧
      Tendsto (fun n : ℕ ↦ (exactRootApproxCompactAverageMeasure μroot n).normalize) atTop
        (𝓝 ρ) := by
  let m : NNReal := Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0))
  have hmass :
      Tendsto
        (fun n : ℕ ↦ (exactRootApproxCompactAverageMeasure μroot n).mass)
        atTop
        (𝓝 m) := by
    simpa [m] using
      exactRootApproxCompactAverageMass_tendsto_nnreal_local
        (μ := μ) μroot hroot hΨ0 hΨexp
  have hmPos : 0 < m := by
    -- Proof comment: compact averaging preserves strictly positive zero-frequency mass away from
    -- Dirac laws.
    dsimp [m]
    exact Real.toNNReal_pos.mpr
      (compactAverageLiftZero_pos_of_notDirac_local hΨ0 hΨexp hDirac)
  have hchar :
      ∀ t : ℝ,
        Tendsto
          (fun n : ℕ ↦
            charFun ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) :
              Measure ℝ) t)
          atTop
          (𝓝 ((compactAverageExpLift Ψ) t)) := by
    intro t
    refine
      (exactRootApproxCompactAverageExponent_tendsto_local
        (μ := μ) μroot hroot hΨ0 hΨexp t).congr' ?_
    filter_upwards [] with n
    symm
    exact exactRootApproxCompactAverageMeasure_charFun_eq_local μroot n t
  have hcont :
      ContinuousAt
        (fun t : ℝ ↦ (((m⁻¹ : NNReal) : ℂ)) * (compactAverageExpLift Ψ t))
        0 := by
    -- Proof comment: scaling the continuous compact-average lift by the fixed inverse mass keeps
    -- continuity at the origin.
    simpa using
      ((continuous_const.mul (compactAverageExpLift Ψ).continuous).continuousAt : ContinuousAt
        (fun t : ℝ ↦ (((m⁻¹ : NNReal) : ℂ)) * (compactAverageExpLift Ψ t)) 0)
  exact
    exists_auxFiniteMeasure_with_normalizedLimit_of_tendsto_charFun_local
      (ηs := fun n ↦ exactRootApproxCompactAverageMeasure μroot n)
      (Φ := fun t ↦ (compactAverageExpLift Ψ) t)
      (m := m)
      hmass
      (ne_of_gt hmPos)
      hchar
      hcont

/-- Helper for Theorem 16.17: averaging the pure oscillatory factor over `[-1,1]` produces
`2 sinc(x)`. -/
private lemma intervalIntegral_exp_mul_compactAverage_local (x : ℝ) :
    ∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) =
      2 * (Real.sinc x : ℂ) := by
  -- Proof comment: reuse the earlier oscillatory averaging identity in the exact same form.
  simpa using compactAverageUnitWindowIntegral_eq_sinc_local x

/-- Helper for Theorem 16.17: `compactAverageKernel` is the half-interval average of
`1 - cos (s * x)` over `[-1, 1]`. -/
private lemma compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_local (x : ℝ) :
    compactAverageKernel x = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
  -- Route correction: instead of rebuilding the compact-average identity from `sinc` algebra, take
  -- real parts of the already proved complex oscillatory integral.
  have hExpInt :
      IntervalIntegrable
        (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the oscillatory phase factor is continuous on the compact interval.
    have hExpCont :
        Continuous (fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
      continuity
    exact hExpCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hReInt :
      ∫ s in (-1 : ℝ)..1, Complex.re (Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) =
        Complex.re (∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
    simpa using
      (Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
        (a := (-1 : ℝ)) (b := (1 : ℝ))
        (f := fun s : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) hExpInt)
  have hCosInt :
      ∫ s in (-1 : ℝ)..1, Real.cos (s * x) = 2 * Real.sinc x := by
    calc
      ∫ s in (-1 : ℝ)..1, Real.cos (s * x)
          = ∫ s in (-1 : ℝ)..1, Complex.re (Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := by
              refine intervalIntegral.integral_congr fun s _ ↦ ?_
              simpa using (Complex.exp_ofReal_mul_I_re (s * x)).symm
      _ = Complex.re
            (∫ s in (-1 : ℝ)..1, Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)) := hReInt
      _ = 2 * Real.sinc x := by
            rw [intervalIntegral_exp_mul_compactAverage_local]
            simp
  have hCosCont :
      IntervalIntegrable (fun s : ℝ ↦ Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the real cosine integrand is continuous on the averaging window.
    have hCosCont' : Continuous (fun s : ℝ ↦ Real.cos (s * x)) := by
      simpa using (Real.continuous_cos.comp (continuous_id.mul continuous_const))
    exact hCosCont'.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hSub :
      ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) =
        (∫ s in (-1 : ℝ)..1, (1 : ℝ)) - ∫ s in (-1 : ℝ)..1, Real.cos (s * x) := by
    rw [intervalIntegral.integral_sub (μ := volume) intervalIntegrable_const hCosCont]
  have hConstIntEval : ∫ s in (-1 : ℝ)..1, (1 : ℝ) = 2 := by
    norm_num [intervalIntegral.integral_const]
  calc
    compactAverageKernel x = 1 - Real.sinc x := by
      simp [compactAverageKernel]
    _ = (1 / 2 : ℝ) * (2 - 2 * Real.sinc x) := by ring
    _ = (1 / 2 : ℝ) *
          ((∫ s in (-1 : ℝ)..1, (1 : ℝ)) - ∫ s in (-1 : ℝ)..1, Real.cos (s * x)) := by
            rw [hConstIntEval, hCosInt]
    _ = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
          rw [← hSub]

/-- Helper for Theorem 16.17: the cosine defect is quadratically bounded above. -/
private lemma one_sub_cos_le_sq_div_two_local (y : ℝ) :
    1 - Real.cos y ≤ y ^ (2 : ℕ) / 2 := by
  -- Proof comment: rearrange the standard quadratic lower bound for `cos`.
  linarith [Real.one_sub_sq_div_two_le_cos (x := y)]

/-- Helper for Theorem 16.17: on `[-1,1]`, the cosine defect is quadratically bounded below by a
uniform multiple of `y²`. -/
private lemma two_div_pi_sq_mul_sq_le_one_sub_cos_local {y : ℝ} (hy : |y| ≤ 1) :
    (2 / Real.pi ^ (2 : ℕ)) * y ^ (2 : ℕ) ≤ 1 - Real.cos y := by
  -- Proof comment: on `[-1, 1]`, Jordan's cosine defect bound is available directly from
  -- `Real.cos_le_one_sub_mul_cos_sq`.
  have hpi : |y| ≤ Real.pi := by
    linarith [hy, Real.pi_gt_three]
  have hcos := Real.cos_le_one_sub_mul_cos_sq (x := y) hpi
  linarith [hcos]

/-- Helper for Theorem 16.17: near `0`, the compact-average kernel is at most a constant multiple
of `x²`. -/
private lemma compactAverageKernel_le_half_sq_local {x : ℝ} (_hx : |x| ≤ 1) :
    compactAverageKernel x ≤ x ^ (2 : ℕ) / 2 := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the compact-average defect is continuous, hence interval-integrable.
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hConstInt :
      IntervalIntegrable (fun _ : ℝ ↦ x ^ (2 : ℕ) / 2) volume (-1 : ℝ) 1 := intervalIntegrable_const
  have hMono :
      ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) ≤
        ∫ s in (-1 : ℝ)..1, (x ^ (2 : ℕ) / 2 : ℝ) := by
    -- Proof comment: on `[-1,1]`, the cosine defect is bounded by `((s x)^2) / 2`, and the
    -- factor `s²` is at most `1`.
    refine intervalIntegral.integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
      (f := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (g := fun _ : ℝ ↦ x ^ (2 : ℕ) / 2)
      (hab := by norm_num) hDefectInt hConstInt ?_
    intro s hs
    have hsBounds : -1 ≤ s ∧ s ≤ 1 := by
      simpa using hs
    have hsAbs : |s| ≤ 1 := abs_le.mpr hsBounds
    have hDefect := one_sub_cos_le_sq_div_two_local (s * x)
    have hSq :
        (s * x) ^ (2 : ℕ) / 2 ≤ x ^ (2 : ℕ) / 2 := by
      have hsSq : s ^ (2 : ℕ) ≤ 1 := by
        nlinarith [sq_nonneg s, hsAbs]
      calc
        (s * x) ^ (2 : ℕ) / 2 = (s ^ (2 : ℕ) * x ^ (2 : ℕ)) / 2 := by ring
        _ ≤ (1 * x ^ (2 : ℕ)) / 2 := by
              nlinarith [hsSq, sq_nonneg x]
        _ = x ^ (2 : ℕ) / 2 := by ring
    exact hDefect.trans hSq
  calc
    compactAverageKernel x
        = (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
            rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_local]
    _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (x ^ (2 : ℕ) / 2 : ℝ) := by
          gcongr
    _ = x ^ (2 : ℕ) / 2 := by
          rw [intervalIntegral.integral_const]
          norm_num
          ring

/-- Helper for Theorem 16.17: near `0`, the compact-average kernel is bounded below by a fixed
positive multiple of `x²`. -/
private lemma two_div_pi_sq_mul_sq_quarter_le_compactAverageKernel_local {x : ℝ}
    (hx : |x| ≤ 1) :
    x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the compact-average defect is continuous on `[-1,1]`.
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hLowerInt :
      IntervalIntegrable
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the quadratic lower comparison kernel is polynomial, hence continuous.
    have hLowerCont : Continuous (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) := by
      continuity
    exact hLowerCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hMono :
      ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) ≤
        ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
    -- Proof comment: the lower cosine defect estimate applies because `|s * x| ≤ 1` on the
    -- averaging window whenever `|x| ≤ 1`.
    refine intervalIntegral.integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
      (f := fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ))
      (g := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (hab := by norm_num) hLowerInt hDefectInt ?_
    intro s hs
    have hsBounds : -1 ≤ s ∧ s ≤ 1 := by
      simpa using hs
    have hsAbs : |s| ≤ 1 := abs_le.mpr hsBounds
    have hsxAbs : |s * x| ≤ 1 := by
      calc
        |s * x| = |s| * |x| := by rw [abs_mul]
        _ ≤ 1 * 1 := by
              gcongr
        _ = 1 := by ring
    simpa using two_div_pi_sq_mul_sq_le_one_sub_cos_local (y := s * x) hsxAbs
  have hSqHalf : (1 / 2 : ℝ) ≤ ∫ s in (-1 : ℝ)..1, s ^ (2 : ℕ) := by
    rw [integral_pow]
    norm_num
  let c : ℝ := (1 / 2 : ℝ) * ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ))
  have hcNonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hFactor := mul_le_mul_of_nonneg_left hSqHalf hcNonneg
  have hLowerBound :
      x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ)) ≤
        (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
    -- Proof comment: `∫_{-1}^1 s² ds ≥ 1 / 2`, and pulling out the constant comparison kernel
    -- converts this into the required lower scalar bound.
    dsimp [c] at hFactor ⊢
    convert hFactor using 1
    · ring
    · rw [show (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) =
          fun s : ℝ ↦ ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ)) * s ^ (2 : ℕ) by
            funext s
            ring]
      rw [intervalIntegral.integral_const_mul]
      ring
  calc
    x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ))
        ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) :=
          hLowerBound
    _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
          gcongr
    _ = compactAverageKernel x := by
          rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_local]

/-- Helper for Theorem 16.17: on the shell `1 ≤ |x| ≤ 2`, the compact-average kernel has a
uniform positive lower bound. -/
private lemma one_div_twelve_pi_sq_le_compactAverageKernel_of_one_le_abs_le_two_local {x : ℝ}
    (hx1 : 1 ≤ |x|) (hx2 : |x| ≤ 2) :
    1 / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
  have hDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 : ℝ) 1 := by
    -- Proof comment: the compact-average defect is continuous on the full averaging window.
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 : ℝ)) (b := (1 : ℝ))
  have hLowerInt :
      IntervalIntegrable
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) volume (-1 / 2 : ℝ)
        (1 / 2 : ℝ) := by
    -- Proof comment: the quadratic comparison kernel on the inner shell is polynomial.
    have hLowerCont : Continuous
        (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) := by
      continuity
    exact hLowerCont.intervalIntegrable (μ := volume) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  have hSmallDefectInt :
      IntervalIntegrable (fun s : ℝ ↦ 1 - Real.cos (s * x)) volume (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
    -- Proof comment: the same defect integrand is continuous on the inner shell window.
    have hDefectCont : Continuous (fun s : ℝ ↦ 1 - Real.cos (s * x)) := by
      simpa using
        (continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
    exact hDefectCont.intervalIntegrable (μ := volume) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)] fun s : ℝ ↦ 1 - Real.cos (s * x) := by
    exact Filter.Eventually.of_forall fun s ↦ sub_nonneg.mpr (Real.cos_le_one _)
  have hWindowMono :
      ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) ≤
        ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
    exact intervalIntegral.integral_mono_interval
      (μ := volume)
      (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (c := (-1 : ℝ)) (d := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) hNonneg hDefectInt
  have hMono :
      ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) ≤
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) := by
    -- Proof comment: on `[-1/2, 1/2]` and for `|x| ≤ 2`, the argument `|s * x|` stays within
    -- `[-1, 1]`, so the uniform lower cosine-defect estimate applies pointwise.
    refine intervalIntegral.integral_mono_on (μ := volume)
      (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (f := fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ))
      (g := fun s : ℝ ↦ 1 - Real.cos (s * x))
      (hab := by norm_num) hLowerInt hSmallDefectInt ?_
    intro s hs
    have hsBounds : -(1 / 2 : ℝ) ≤ s ∧ s ≤ 1 / 2 := by
      rcases hs with ⟨hsLeft, hsRight⟩
      constructor <;> linarith
    have hsAbs : |s| ≤ 1 / 2 := abs_le.mpr hsBounds
    have hsxAbs : |s * x| ≤ 1 := by
      calc
        |s * x| = |s| * |x| := by rw [abs_mul]
        _ ≤ (1 / 2 : ℝ) * 2 := by
              gcongr
        _ = 1 := by ring
    simpa using two_div_pi_sq_mul_sq_le_one_sub_cos_local (y := s * x) hsxAbs
  have hLowerEval :
      x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ)) ≤
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
    -- Proof comment: evaluating the inner quadratic comparison integral gives an explicit
    -- multiple of `x²`.
    have hEval :
        ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) =
          x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ)) := by
      rw [show (fun s : ℝ ↦ (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ)) =
          fun s : ℝ ↦ ((2 / Real.pi ^ (2 : ℕ)) * x ^ (2 : ℕ)) * s ^ (2 : ℕ) by
            funext s
            ring]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring_nf
    exact le_of_eq hEval.symm
  have hShell :
      x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x := by
    calc
      x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ))
          = (1 / 2 : ℝ) * (x ^ (2 : ℕ) / (6 * Real.pi ^ (2 : ℕ))) := by
              field_simp [Real.pi_ne_zero]
              ring
      _ ≤ (1 / 2 : ℝ) *
              ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (2 / Real.pi ^ (2 : ℕ)) * (s * x) ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_left hLowerEval (by norm_num : 0 ≤ (1 / 2 : ℝ))
      _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (1 - Real.cos (s * x)) := by
            gcongr
      _ ≤ (1 / 2 : ℝ) * ∫ s in (-1 : ℝ)..1, (1 - Real.cos (s * x)) := by
            gcongr
      _ = compactAverageKernel x := by
            rw [compactAverageKernel_eq_half_intervalIntegral_one_sub_cos_local]
  have hxSqOne : 1 ≤ x ^ (2 : ℕ) := by
    have hxSqAbs : 1 ≤ |x| ^ (2 : ℕ) := by
      nlinarith [hx1, abs_nonneg x]
    simpa [sq_abs] using hxSqAbs
  have hOneToSq :
      1 / (12 * Real.pi ^ (2 : ℕ)) ≤ x ^ (2 : ℕ) / (12 * Real.pi ^ (2 : ℕ)) := by
    exact div_le_div_of_nonneg_right hxSqOne (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
  exact hOneToSq.trans hShell

/-- Helper for Theorem 16.17: the compact-average kernel globally dominates the canonical
integrand up to one fixed scalar factor. -/
private lemma compactAverageInverseWeightBound_local (x : ℝ) :
    min (x ^ (2 : ℕ)) 1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
  by_cases hx1 : |x| ≤ 1
  · have hLower :=
      two_div_pi_sq_mul_sq_quarter_le_compactAverageKernel_local (x := x) hx1
    have hSq :
        x ^ (2 : ℕ) ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
      have hScaled := mul_le_mul_of_nonneg_left hLower (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
      calc
        x ^ (2 : ℕ) ≤ 6 * x ^ (2 : ℕ) := by
              nlinarith [sq_nonneg x]
        _ = (12 * Real.pi ^ (2 : ℕ)) * (x ^ (2 : ℕ) / (2 * Real.pi ^ (2 : ℕ))) := by
              field_simp [Real.pi_ne_zero]
              ring
        _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := hScaled
    exact (min_le_left _ _).trans hSq
  · have hxgt : 1 < |x| := lt_of_not_ge hx1
    by_cases hx2 : |x| ≤ 2
    · have hShell :
          1 / (12 * Real.pi ^ (2 : ℕ)) ≤ compactAverageKernel x :=
        one_div_twelve_pi_sq_le_compactAverageKernel_of_one_le_abs_le_two_local
          (le_of_lt hxgt) hx2
      have hOne :
          1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
        have hScaled := mul_le_mul_of_nonneg_left hShell
          (by positivity : 0 ≤ 12 * Real.pi ^ (2 : ℕ))
        calc
          1 = (12 * Real.pi ^ (2 : ℕ)) * (1 / (12 * Real.pi ^ (2 : ℕ))) := by
                field_simp [Real.pi_ne_zero]
          _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := hScaled
      exact (min_le_right _ _).trans hOne
    · have hx2' : 2 < |x| := lt_of_not_ge hx2
      have hsincHalf : |Real.sinc x| ≤ 1 / (2 : ℝ) := by
        have hx0 : x ≠ 0 := by
          intro hx0
          rw [hx0] at hx2'
          norm_num at hx2'
        rw [Real.sinc_of_ne_zero hx0, abs_div]
        have hSin : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
        have hxAbsPos : 0 < |x| := abs_pos.mpr hx0
        have hDiv : |Real.sin x| / |x| ≤ 1 / |x| := by
          exact div_le_div_of_nonneg_right hSin hxAbsPos.le
        have hInv : 1 / |x| ≤ 1 / (2 : ℝ) := by
          exact one_div_le_one_div_of_le (by positivity) (le_of_lt hx2')
        exact hDiv.trans hInv
      have hKernelHalf : (1 / 2 : ℝ) ≤ compactAverageKernel x := by
        have hsincLeHalf : Real.sinc x ≤ 1 / (2 : ℝ) := le_trans (le_abs_self _) hsincHalf
        dsimp [compactAverageKernel]
        linarith
      have hOne :
          1 ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
        calc
          1 ≤ 6 * Real.pi ^ (2 : ℕ) := by
                nlinarith [Real.pi_gt_three]
          _ = (12 * Real.pi ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
                ring
          _ ≤ (12 * Real.pi ^ (2 : ℕ)) * compactAverageKernel x := by
                gcongr
      exact (min_le_right _ _).trans hOne
/-- Helper for Theorem 16.17: a Dirac law is represented by the zero-jump, zero-Gaussian
canonical triple with drift equal to the atom location. -/
private lemma hasLevyKhinchinRepresentation_dirac_local (b : ℝ) :
    HasLevyKhinchinRepresentation (diracProba b)
      { sigma2 := 0, b := b, ν := (0 : Measure ℝ) } := by
  constructor
  · -- Proof comment: the zero measure is canonical and the Gaussian coefficient is already `0`.
    infer_instance
  · intro t
    have hInner : inner ℝ b t = b * t := by
      simpa using (RCLike.inner_apply' (𝕜 := ℝ) b t)
    -- Proof comment: with vanishing Gaussian and jump terms, the exponent is exactly the phase of
    -- the Dirac mass at `b`.
    simpa [MeasureTheory.diracProba, MeasureTheory.charFun_dirac, hInner,
      levyKhinchinExponent, levyKhinchinExponentWithCentering, mul_assoc, mul_left_comm, mul_comm]
-- Route correction: the old forward implication depended on the later theorem
-- `Theorem_16_28`, whose existence lemma is still unresolved in this workspace. The new route
-- keeps the uniqueness block above and rebuilds existence locally from exact-root
-- compound-Poisson approximants plus the Gaussian-recovery machinery already present in this file.
/-- Helper for Theorem 16.17: an infinitely divisible law has a continuous logarithmic lift of
its characteristic function normalized by `Ψ 0 = 0`. -/
private lemma continuousExpLift_of_isInfinitelyDivisible_local
    {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    ∃ Ψ : C(ℝ, ℂ), Ψ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t := by
  -- Proof comment: infinite divisibility implies the characteristic function is zero-free, so
  -- the standard covering-space lift of `Complex.exp` applies.
  obtain ⟨Ψ, hΨ, _huniq⟩ :=
    existsUniqueContinuousExpLift
      (MeasureTheory.continuous_charFun : Continuous (charFun (μ : Measure ℝ)))
      (charFun_ne_zero_of_isInfinitelyDivisible hμ)
      (by simpa using (MeasureTheory.charFun_zero (μ := (μ : Measure ℝ))))
  exact ⟨Ψ, hΨ.1, hΨ.2⟩

/-- Helper for Theorem 16.17: a nonzero finite measure is its total mass times the normalized
probability law. -/
private lemma integral_eq_mass_mul_integral_normalize_local
    (η : FiniteMeasure ℝ) (hη : η ≠ 0) (f : ℝ → ℂ) :
    ∫ x : ℝ, f x ∂((η : FiniteMeasure ℝ) : Measure ℝ) =
      ((η.mass : NNReal) : ℂ) * ∫ x : ℝ, f x ∂(η.normalize : Measure ℝ) := by
  have hmass : η.mass ≠ 0 := (FiniteMeasure.mass_nonzero_iff η).2 hη
  have hNormalize :
      ∫ x : ℝ, f x ∂(η.normalize : Measure ℝ) =
        (((η.mass⁻¹ : NNReal) : ℂ)) * ∫ x : ℝ, f x ∂(η : Measure ℝ) := by
    rw [η.toMeasure_normalize_eq_of_nonzero hη]
    change
      ∫ x : ℝ, f x ∂((((η.mass⁻¹ : NNReal) : ENNReal) • (η : Measure ℝ))) =
        (((η.mass⁻¹ : NNReal) : ℂ)) * ∫ x : ℝ, f x ∂(η : Measure ℝ)
    rw [integral_smul_measure]
    rfl
  have hmassC : (((η.mass : NNReal) : ℂ) * (((η.mass⁻¹ : NNReal) : ℂ))) = 1 := by
    have hmassCne : (((η.mass : NNReal) : ℂ)) ≠ 0 := by
      exact_mod_cast hmass
    simpa using (mul_inv_cancel₀ hmassCne)
  calc
    ∫ x : ℝ, f x ∂(η : Measure ℝ)
        = 1 * ∫ x : ℝ, f x ∂(η : Measure ℝ) := by ring
    _ = (((η.mass : NNReal) : ℂ) * (((η.mass)⁻¹ : NNReal) : ℂ)) *
          ∫ x : ℝ, f x ∂(η : Measure ℝ) := by rw [hmassC]
    _ = ((η.mass : NNReal) : ℂ) *
          ((((η.mass)⁻¹ : NNReal) : ℂ) * ∫ x : ℝ, f x ∂(η : Measure ℝ)) := by ring
    _ = ((η.mass : NNReal) : ℂ) * ∫ x : ℝ, f x ∂(η.normalize : Measure ℝ) := by
          rw [hNormalize]

/-- Helper for Theorem 16.17: scaling a probability law by a finite mass scales every complex
integral by the same scalar. -/
private lemma integral_mass_smul_probability_local
    (m : NNReal) (ρ : ProbabilityMeasure ℝ) (f : ℝ → ℂ) :
    ∫ x : ℝ, f x ∂(((m • ρ.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ)) =
      (m : ℂ) * ∫ x : ℝ, f x ∂(ρ : Measure ℝ) := by
  simpa [FiniteMeasure.toMeasure_smul, Algebra.smul_def] using
    (integral_smul_measure
      (μ := ((ρ.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ))
      (c := m) (f := f))

/-- Helper for Theorem 16.17: bounded-continuous weak convergence of the normalized compact-average
auxiliary laws transports the reconstruction-kernel integrals to the limiting finite measure. -/
private lemma tendsto_integral_compactAverageReconstructionKernel_exactRootApprox_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (hMassPos : 0 < Complex.re ((compactAverageExpLift Ψ) 0))
    {ρ : ProbabilityMeasure ℝ} {η : FiniteMeasure ℝ}
    (hηeq : η = (Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0))) • ρ.toFiniteMeasure)
    (hnormTendsto : Tendsto (fun n : ℕ ↦ (exactRootApproxCompactAverageMeasure μroot n).normalize)
      atTop (𝓝 ρ))
    (t : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
          ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ))
      atTop
      (𝓝 (∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(η : Measure ℝ))) := by
  let C : ℝ := (max (3 * |t| ^ (2 : ℕ)) 2 + |t|) * (12 * Real.pi ^ (2 : ℕ)) + 3 * t ^ (2 : ℕ)
  let f_t : BoundedContinuousFunction ℝ ℂ :=
    BoundedContinuousFunction.mkOfBound
      ⟨compactAverageReconstructionKernel_local t,
        continuous_compactAverageReconstructionKernel_local t⟩
      (2 * C)
      (fun x y ↦ by
        calc
          dist (compactAverageReconstructionKernel_local t x)
              (compactAverageReconstructionKernel_local t y)
              ≤ ‖compactAverageReconstructionKernel_local t x‖ +
                  ‖compactAverageReconstructionKernel_local t y‖ := by
                    simpa [dist_eq_norm, sub_eq_add_neg] using
                      (norm_sub_le
                        (compactAverageReconstructionKernel_local t x)
                        (compactAverageReconstructionKernel_local t y))
          _ ≤ C + C := by
                gcongr <;> simpa [C] using norm_compactAverageReconstructionKernel_local_le t _
          _ = 2 * C := by ring)
  let m : NNReal := Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0))
  have hmPos : 0 < m := Real.toNNReal_pos.mpr hMassPos
  have hNormIntegral :
      Tendsto
        (fun n : ℕ ↦
          ∫ x : ℝ, f_t x ∂((exactRootApproxCompactAverageMeasure μroot n).normalize : Measure ℝ))
        atTop
        (𝓝 (∫ x : ℝ, f_t x ∂(ρ : Measure ℝ))) := by
    exact
      (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1
        hnormTendsto f_t
  have hMassTendsto :
      Tendsto
        (fun n : ℕ ↦ (((exactRootApproxCompactAverageMeasure μroot n).mass : NNReal) : ℂ))
        atTop
        (𝓝 (m : ℂ)) := by
    exact
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (NNReal.continuous_coe.continuousAt.tendsto.comp
          (exactRootApproxCompactAverageMass_tendsto_nnreal_local
            (μ := μ) μroot hroot hΨ0 hΨexp)))
  have hApproxEventuallyNonzero :
      ∀ᶠ n : ℕ in atTop, exactRootApproxCompactAverageMeasure μroot n ≠ 0 := by
    filter_upwards
      [(exactRootApproxCompactAverageMass_tendsto_nnreal_local
        (μ := μ) μroot hroot hΨ0 hΨexp) (Ioi_mem_nhds hmPos)] with n hn
    exact (FiniteMeasure.mass_nonzero_iff (exactRootApproxCompactAverageMeasure μroot n)).1
      (ne_of_gt hn)
  have hApproxEq :
      (fun n : ℕ ↦
        ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
          ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ)) =ᶠ[atTop]
      (fun n : ℕ ↦
        (((exactRootApproxCompactAverageMeasure μroot n).mass : NNReal) : ℂ) *
          ∫ x : ℝ, f_t x ∂((exactRootApproxCompactAverageMeasure μroot n).normalize : Measure ℝ)) := by
    filter_upwards [hApproxEventuallyNonzero] with n hn
    simpa [f_t] using
      (integral_eq_mass_mul_integral_normalize_local
        (exactRootApproxCompactAverageMeasure μroot n) hn
        (fun x : ℝ ↦ compactAverageReconstructionKernel_local t x))
  have hLimitEq :
      ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(η : Measure ℝ) =
        (m : ℂ) * ∫ x : ℝ, f_t x ∂(ρ : Measure ℝ) := by
    rw [hηeq]
    simpa [m, f_t] using
      (integral_mass_smul_probability_local
        m ρ (fun x : ℝ ↦ compactAverageReconstructionKernel_local t x))
  have hScaled :
      Tendsto
        (fun n : ℕ ↦
          (((exactRootApproxCompactAverageMeasure μroot n).mass : NNReal) : ℂ) *
            ∫ x : ℝ, f_t x ∂((exactRootApproxCompactAverageMeasure μroot n).normalize : Measure ℝ))
        atTop
        (𝓝 ((m : ℂ) * ∫ x : ℝ, f_t x ∂(ρ : Measure ℝ))) := by
    exact hMassTendsto.mul hNormIntegral
  have hIntegral :
      Tendsto
        (fun n : ℕ ↦
          ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
            ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ))
        atTop
        (𝓝 ((m : ℂ) * ∫ x : ℝ, f_t x ∂(ρ : Measure ℝ))) := by
    exact hScaled.congr' hApproxEq.symm
  simpa [hLimitEq] using hIntegral

/-- Helper for Theorem 16.17: after recovering the zero-drift Gaussian and jump fields from the
compact-average auxiliary measure, the remaining residual is exactly one linear imaginary drift. -/
private lemma compactAverageResidual_eq_linearDrift_local
    {μ : ProbabilityMeasure ℝ}
    (μroot : ℕ+ → ProbabilityMeasure ℝ)
    (hroot : ∀ n : ℕ+, μroot n ^ (n : ℕ) = μ)
    {Ψ : C(ℝ, ℂ)} (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = charFun (μ : Measure ℝ) t)
    (hMassPos : 0 < Complex.re ((compactAverageExpLift Ψ) 0))
    {ρ : ProbabilityMeasure ℝ} {η : FiniteMeasure ℝ}
    (hηeq : η = (Real.toNNReal (Complex.re ((compactAverageExpLift Ψ) 0))) • ρ.toFiniteMeasure)
    (hnormTendsto : Tendsto (fun n : ℕ ↦ (exactRootApproxCompactAverageMeasure μroot n).normalize)
      atTop (𝓝 ρ)) :
    let σ2 : ℝ := 6 * (((η : Measure ℝ) ({0} : Set ℝ)).toReal)
    let ν := compactAverageRecoveredJumpMeasure_local η
    ∃ b : ℝ, ∀ t : ℝ, Ψ t = levyKhinchinExponentWithCentering σ2 b ν Real.sin t := by
  dsimp
  let σ2 : ℝ := 6 * (((η : Measure ℝ) ({0} : Set ℝ)).toReal)
  let ν : Measure ℝ := compactAverageRecoveredJumpMeasure_local η
  let R : ℝ → ℂ := fun t ↦ Ψ t - levyKhinchinExponentWithCentering σ2 0 ν Real.sin t
  let residualSeq : ℕ → ℝ → ℂ := fun n t ↦
    ((((exactRootApproxReconstructionDrift_local μroot n * t : ℝ) : ℂ) * Complex.I))
  have hIntegralLimit :
      ∀ t : ℝ,
        Tendsto
          (fun n : ℕ ↦
            ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
              ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ))
          atTop
          (𝓝 (levyKhinchinExponentWithCentering σ2 0 ν Real.sin t)) := by
    intro t
    have h :=
      tendsto_integral_compactAverageReconstructionKernel_exactRootApprox_local
        (μ := μ) μroot hroot hΨ0 hΨexp hMassPos hηeq hnormTendsto t
    have hEta :
        ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂(η : Measure ℝ) =
          levyKhinchinExponentWithCentering σ2 0 ν Real.sin t := by
      symm
      simpa [σ2, ν] using compactAverageRecoveredZeroDriftExponent_local η t
    simpa [hEta] using h
  have hResidualLimit :
      ∀ t : ℝ, Tendsto (fun n : ℕ ↦ residualSeq n t) atTop (𝓝 (R t)) := by
    intro t
    have hRaw :
        Tendsto
          (fun n : ℕ ↦
            levyKhinchinExponent (exactRootApproxTriple μroot n) t -
              ∫ x : ℝ, compactAverageReconstructionKernel_local t x ∂
                ((exactRootApproxCompactAverageMeasure μroot n : FiniteMeasure ℝ) : Measure ℝ))
          atTop
          (𝓝 (R t)) := by
      simpa [R] using
        (compoundPoissonApproxExponent_tendsto_local
          (μ := μ) μroot hroot hΨ0 hΨexp t).sub (hIntegralLimit t)
    refine hRaw.congr' ?_
    filter_upwards [] with n
    rw [exactRootApproxExponent_eq_reconstructionIntegral_add_drift_local]
    simp [residualSeq]
  have hResidualLinear :
      ∀ t : ℝ, R t = (t : ℂ) * R 1 := by
    intro t
    have hLeft : Tendsto (fun n : ℕ ↦ residualSeq n t) atTop (𝓝 (R t)) := hResidualLimit t
    have hRight :
        Tendsto (fun n : ℕ ↦ (t : ℂ) * residualSeq n 1) atTop (𝓝 ((t : ℂ) * R 1)) := by
      exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (t : ℂ)) atTop (𝓝 (t : ℂ))).mul
        (hResidualLimit 1)
    have hSeqEq :
        (fun n : ℕ ↦ residualSeq n t) =ᶠ[atTop] fun n : ℕ ↦ (t : ℂ) * residualSeq n 1 := by
      filter_upwards [] with n
      simp [residualSeq]
      ring
    have hRight' :
        Tendsto (fun n : ℕ ↦ residualSeq n t) atTop (𝓝 ((t : ℂ) * R 1)) := by
      exact hRight.congr' hSeqEq.symm
    exact tendsto_nhds_unique hLeft hRight'
  have hReZero :
      Complex.re (R 1) = 0 := by
    have hRe :
        Tendsto (fun n : ℕ ↦ Complex.re (residualSeq n 1)) atTop
          (𝓝 (Complex.re (R 1))) := by
      exact (Complex.continuous_re.continuousAt.tendsto.comp (hResidualLimit 1))
    have hZero :
        Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (Complex.re (R 1))) := by
      refine hRe.congr' ?_
      filter_upwards [] with n
      simp [residualSeq]
    exact tendsto_nhds_unique hZero tendsto_const_nhds
  let b : ℝ := Complex.im (R 1)
  have hRone :
      R 1 = ((b : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [b, hReZero]
  refine ⟨b, ?_⟩
  intro t
  have hResidualFormula :
      R t = ((((b * t : ℝ) : ℂ)) * Complex.I) := by
    calc
      R t = (t : ℂ) * R 1 := hResidualLinear t
      _ = (t : ℂ) * ((b : ℂ) * Complex.I) := by rw [hRone]
      _ = ((((b * t : ℝ) : ℂ)) * Complex.I) := by
            simp [mul_assoc, mul_comm, mul_left_comm]
  have hAdd :
      Ψ t = levyKhinchinExponentWithCentering σ2 0 ν Real.sin t +
        ((((b * t : ℝ) : ℂ)) * Complex.I) := by
    have hAdd' :
        Ψ t = ((((b * t : ℝ) : ℂ)) * Complex.I) +
          levyKhinchinExponentWithCentering σ2 0 ν Real.sin t := by
      exact sub_eq_iff_eq_add.mp (by simpa [R] using hResidualFormula)
    simpa [add_comm] using hAdd'
  rw [levyKhinchinExponentWithSineCentering_add_drift_eq_local]
  exact hAdd

/-- Helper for Theorem 16.17: local forward existence frontier for infinitely divisible laws. -/
private lemma levyKhinchinTriple_exists_of_isInfinitelyDivisible_local
    {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    ∃ τ : LevyKhinchinTriple, HasLevyKhinchinRepresentation μ τ := by
  obtain ⟨μroot, hroot⟩ := existsExactRootFamily_of_isInfinitelyDivisible_local hμ
  obtain ⟨Ψ, hΨ0, hΨexp⟩ := continuousExpLift_of_isInfinitelyDivisible_local hμ
  by_cases hDirac : ∃ b : ℝ, μ = diracProba b
  · rcases hDirac with ⟨b, rfl⟩
    -- Proof comment: the Dirac branch is explicit, so the canonical triple is `(0, b, 0)`.
    exact ⟨{ sigma2 := 0, b := b, ν := (0 : Measure ℝ) },
      hasLevyKhinchinRepresentation_dirac_local b⟩
  · have hMassPos :
        0 < Complex.re ((compactAverageExpLift Ψ) 0) :=
      compactAverageLiftZero_pos_of_notDirac_local hΨ0 hΨexp hDirac
    obtain ⟨ρ, η, hηeq, hηchar, hnormTendsto⟩ :=
      exists_compactAverageAuxFiniteMeasure_with_normalizedLimit_of_exactRoots_nonDirac_local
        (μ := μ) μroot hroot hΨ0 hΨexp hDirac
    let _ := hMassPos
    let _ := ρ
    let _ := η
    let _ := hηeq
    let _ := hηchar
    let _ := hnormTendsto
    -- Proof comment: the non-Dirac branch now has the exact-root compact-average auxiliary
    -- finite measure `η` together with its normalized weak limit. Recover the zero-drift
    -- Gaussian/jump fields from `η` with the smooth `Real.sin` centering, then convert back to
    -- the canonical cutoff via `changeCentering`.
    let σ2 : ℝ := 6 * (((η : Measure ℝ) ({0} : Set ℝ)).toReal)
    let ν : Measure ℝ := compactAverageRecoveredJumpMeasure_local η
    have hν : IsCanonicalMeasure ν := by
      simpa [ν] using isCanonicalMeasure_compactAverageRecoveredJumpMeasure_local η
    have hDiffInt :
        Integrable (fun x : ℝ ↦ Real.sin x - levyKhinchinCanonicalCentering x) ν :=
      integrable_sin_sub_levyKhinchinCanonicalCentering_local hν
    obtain ⟨bSin, hbSin⟩ :=
      compactAverageResidual_eq_linearDrift_local
        (μ := μ) μroot hroot hΨ0 hΨexp hMassPos hηeq hnormTendsto
    let b : ℝ := bSin - ∫ x : ℝ, (Real.sin x - levyKhinchinCanonicalCentering x) ∂ν
    refine ⟨{ sigma2 := σ2, b := b, ν := ν }, ?_⟩
    constructor
    · refine ⟨?_, ?_⟩
      · dsimp [σ2]
        positivity
      · simpa [ν] using hν
    · intro t
      have hChangeFn :=
        levyKhinchinExponentWithCentering_changeCentering σ2 b ν hν Real.sin hDiffInt
      have hChangeAt := congrArg (fun f : ℝ → ℂ ↦ f t) hChangeFn
      rw [← hΨexp t, hbSin t]
      exact congrArg Complex.exp (by simpa [b, levyKhinchinExponent, ν] using hChangeAt)

/-- Helper for Theorem 16.17: the canonical cover sets from Definition 16.16 are measurable. -/
private lemma measurableSet_canonicalMeasureCoverSet_local (n : ℕ) :
    MeasurableSet (IsCanonicalMeasure.canonicalMeasureCoverSet n : Set ℝ) := by
  -- Proof comment: the cover set is a strict superlevel set of the measurable truncation
  -- integrand.
  refine measurableSet_lt measurable_const ?_
  fun_prop

/-- Helper for Theorem 16.17: restricting a canonical Lévy measure to one cover set gives a
finite measure. -/
private lemma isFiniteMeasure_restrict_canonicalMeasureCoverSet_local
    {ν : Measure ℝ} (hν : IsCanonicalMeasure ν) (n : ℕ) :
    IsFiniteMeasure (ν.restrict (IsCanonicalMeasure.canonicalMeasureCoverSet n)) := by
  refine ⟨?_⟩
  -- Proof comment: each cover set is a positive level set of the integrable canonical kernel.
  have hlevel :
      ν {x : ℝ | ((n + 1 : ℝ)⁻¹) < min (x ^ (2 : ℕ)) 1} < ⊤ :=
    IsCanonicalMeasure.canonicalMeasure_levelSet_lt_top hν (by positivity)
  simpa [IsCanonicalMeasure.canonicalMeasureCoverSet] using hlevel

/-- Helper for Theorem 16.17: restricting a canonical Lévy measure to one canonical cover set
preserves canonicality. -/
private lemma isCanonicalMeasure_restrict_canonicalMeasureCoverSet_local
    {ν : Measure ℝ} (hν : IsCanonicalMeasure ν) (n : ℕ) :
    IsCanonicalMeasure (ν.restrict (IsCanonicalMeasure.canonicalMeasureCoverSet n)) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the restricted singleton is contained in `{0}`, which already has zero mass.
    rw [Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    exact measure_mono_null (by intro x hx; simpa using hx.1) hν.measure_singleton_zero
  · -- Proof comment: the canonical truncated second moment remains integrable after restriction.
    exact hν.integrable_sq_min_one.restrict

/-- Helper for Theorem 16.17: each canonical cover truncation of a canonical triple is again a
canonical triple. -/
private lemma isCanonicalTriple_restrict_canonicalMeasureCoverSet_local
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) (n : ℕ) :
    IsCanonicalTriple
      { sigma2 := τ.sigma2
        b := τ.b
        ν := τ.ν.restrict (IsCanonicalMeasure.canonicalMeasureCoverSet n) } := by
  refine ⟨hτ.sigma2_nonneg, ?_⟩
  exact isCanonicalMeasure_restrict_canonicalMeasureCoverSet_local hτ.isCanonicalMeasure n

/-- Helper for Theorem 16.17: the canonical truncation cover sets increase with the index. -/
private lemma mem_canonicalMeasureCoverSet_mono_local {x : ℝ} {m n : ℕ}
    (hmn : m ≤ n) :
    x ∈ IsCanonicalMeasure.canonicalMeasureCoverSet m →
      x ∈ IsCanonicalMeasure.canonicalMeasureCoverSet n := by
  -- Proof comment: the defining threshold `(n + 1)⁻¹` decreases as `n` grows.
  dsimp [IsCanonicalMeasure.canonicalMeasureCoverSet]
  intro hx
  refine lt_of_le_of_lt ?_ hx
  have hsucc : (m + 1 : ℝ) ≤ n + 1 := by
    exact_mod_cast Nat.succ_le_succ hmn
  simpa [one_div] using one_div_le_one_div_of_le (by positivity) hsucc

/-- Helper for Theorem 16.17: the Gaussian law `N(m, σ²)` is represented by the canonical triple
`(σ², m, 0)`. -/
private lemma gaussian_hasLevyKhinchinRepresentation_local (m : ℝ) (σ2 : NNReal) :
    HasLevyKhinchinRepresentation
      (⟨gaussianReal m σ2, inferInstance⟩ : ProbabilityMeasure ℝ)
      { sigma2 := (σ2 : ℝ), b := m, ν := (0 : Measure ℝ) } := by
  constructor
  · -- Proof comment: the Gaussian coefficient is nonnegative and the zero jump measure is
    -- canonical.
    refine ⟨by exact_mod_cast σ2.2, by infer_instance⟩
  · intro t
    -- Proof comment: with zero jump measure, the Lévy--Khinchin exponent is exactly the Gaussian
    -- characteristic exponent.
    calc
      charFun (⟨gaussianReal m σ2, inferInstance⟩ : ProbabilityMeasure ℝ) t
          = Complex.exp (t * m * Complex.I - ((σ2 : ℝ) * t ^ (2 : ℕ) / 2 : ℝ)) := by
              simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
                (ProbabilityTheory.charFun_gaussianReal (μ := m) (v := σ2) t)
      _ =
          Complex.exp
            (levyKhinchinExponent { sigma2 := (σ2 : ℝ), b := m, ν := (0 : Measure ℝ) } t) := by
              congr 1
              simp [levyKhinchinExponent, levyKhinchinExponentWithCentering, sub_eq_add_neg,
                mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
              ring

/-- Helper for Theorem 16.17: convolution preserves infinite divisibility. -/
private lemma isInfinitelyDivisible_mul_local
    {μ ν : ProbabilityMeasure ℝ}
    (hμ : IsInfinitelyDivisible μ) (hν : IsInfinitelyDivisible ν) :
    IsInfinitelyDivisible (μ * ν) := by
  refine ⟨fun n ↦ ?_⟩
  rcases hμ.exists_root n with ⟨μroot, hμroot⟩
  rcases hν.exists_root n with ⟨νroot, hνroot⟩
  refine ⟨μroot * νroot, ?_⟩
  -- Proof comment: characteristic functions turn convolution into multiplication, so the
  -- convolution of the two roots is an `n`th root of `μ * ν`.
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_charFun ?_
  funext t
  calc
    charFun (((μroot * νroot) ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun (μroot * νroot) t ^ (n : ℕ) := by
            simpa using
              congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow (μroot * νroot) (n : ℕ))
    _ = (charFun (μroot : Measure ℝ) t) ^ (n : ℕ) * (charFun (νroot : Measure ℝ) t) ^ (n : ℕ) := by
          rw [ProbabilityMeasure.toMeasure_mul, MeasureTheory.charFun_conv, mul_pow]
    _ = charFun (μ : Measure ℝ) t * charFun (ν : Measure ℝ) t := by
          rw [← hμroot, ← hνroot]
          simp only [ProbabilityMeasure.charFun_pow]
    _ = charFun (((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ)) t := by
          rw [ProbabilityMeasure.toMeasure_mul, MeasureTheory.charFun_conv]

/-- Helper for Theorem 16.17: along an additive orbit, repeated convolution with the root law
recovers the successive parameter multiples. -/
private theorem convolutionPower_succ_eq_of_additiveOrbit_local
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
      -- Proof comment: add one more convolution factor and use the additive-orbit recursion.
      rw [pow_succ, convolutionPower_succ_eq_of_additiveOrbit_local ν a hstep k]
      exact ProbabilityMeasure.toMeasure_injective (hstep k)

/-- Helper for Theorem 16.17: every real Gaussian law is infinitely divisible. -/
private lemma gaussianReal_infinitelyDivisible_local (m : ℝ) (σ2 : NNReal) :
    IsInfinitelyDivisible
      (⟨gaussianReal m σ2, inferInstance⟩ : ProbabilityMeasure ℝ) := by
  refine ⟨fun n ↦ ?_⟩
  let gaussianLaw : ℝ × NNReal → ProbabilityMeasure ℝ :=
    fun p ↦ ⟨gaussianReal p.1 p.2, inferInstance⟩
  refine ⟨gaussianLaw (m / (n : ℝ), σ2 / (n : NNReal)), ?_⟩
  -- Proof comment: rebuild the Gaussian root formula directly from the additive-orbit
  -- convolution identity.
  change gaussianLaw (m / (n : ℝ), σ2 / (n : NNReal)) ^ (n : ℕ) = gaussianLaw (m, σ2)
  have hpow :=
    convolutionPower_succ_eq_of_additiveOrbit_local
      (ν := gaussianLaw) (a := (m / (n : ℝ), σ2 / (n : NNReal)))
      (hstep := by
        intro k
        -- Proof comment: Gaussian convolution adds the mean and variance parameters.
        simp [gaussianLaw]
        rw [ProbabilityTheory.gaussianReal_conv_gaussianReal]
        congr <;> ring)
      n.natPred
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  have hnNN : (n : NNReal) ≠ 0 := by
    exact_mod_cast n.ne_zero
  rw [n.natPred_add_one] at hpow
  calc
    gaussianLaw (m / (n : ℝ), σ2 / (n : NNReal)) ^ (n : ℕ)
        = gaussianLaw ((n : ℕ) • (m / (n : ℝ), σ2 / (n : NNReal))) := by
            simpa using hpow
    _ = gaussianLaw (m, σ2) := by
          congr 1
          ext
          · -- Proof comment: summing the root means recovers the original mean.
            simp [nsmul_eq_mul]
            field_simp [hnR]
          · -- Proof comment: summing the root variances recovers the original variance.
            simp [nsmul_eq_mul, div_eq_mul_inv, hnNN, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 16.17: the explicit finite-jump law attached to a canonical
Lévy--Khinchin triple. -/
private def finiteCanonicalLaw_local (τ : LevyKhinchinTriple) [IsFiniteMeasure τ.ν]
    (hσ : 0 ≤ τ.sigma2) :
    ProbabilityMeasure ℝ :=
  let γ : ProbabilityMeasure ℝ :=
    ⟨gaussianReal
      (τ.b - ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂τ.ν)
      ⟨τ.sigma2, hσ⟩, inferInstance⟩
  γ * compoundPoissonMeasure τ.ν

/-- Helper for Theorem 16.17: the explicit finite-jump law realizes the given canonical triple in
the Lévy--Khinchin formula. -/
private theorem finiteCanonicalLaw_hasLevyKhinchinRepresentation_local
    {τ : LevyKhinchinTriple} [IsFiniteMeasure τ.ν] (hτ : IsCanonicalTriple τ) :
    HasLevyKhinchinRepresentation
      (finiteCanonicalLaw_local τ hτ.sigma2_nonneg) τ := by
  let σ2NN : NNReal := ⟨τ.sigma2, hτ.sigma2_nonneg⟩
  let gaussianDrift : ℝ := τ.b - ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂τ.ν
  let γ : ProbabilityMeasure ℝ := ⟨gaussianReal gaussianDrift σ2NN, inferInstance⟩
  let π : ProbabilityMeasure ℝ := compoundPoissonMeasure τ.ν
  have hγ :
      HasLevyKhinchinRepresentation γ
        { sigma2 := σ2NN, b := gaussianDrift, ν := 0 } := by
    -- Proof comment: the Gaussian factor carries the quadratic coefficient and the residual
    -- drift.
    simpa [γ] using gaussian_hasLevyKhinchinRepresentation_local gaussianDrift σ2NN
  have hπ :
      HasLevyKhinchinRepresentation π
        { sigma2 := 0
          b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂τ.ν
          ν := τ.ν } := by
    -- Proof comment: the finite jump intensity is represented by the canonical compound-Poisson
    -- law.
    simpa [π] using
      compoundPoisson_hasLevyKhinchinRepresentation
        τ.ν hτ.isCanonicalMeasure.measure_singleton_zero
  constructor
  · exact hτ
  · intro t
    have hsumExp :
        levyKhinchinExponent { sigma2 := σ2NN, b := gaussianDrift, ν := 0 } t +
            levyKhinchinExponent
              { sigma2 := 0
                b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂τ.ν
                ν := τ.ν } t =
          levyKhinchinExponent τ t := by
      -- Proof comment: the Gaussian and jump exponents add back to the target exponent of `τ`.
      simp [levyKhinchinExponent, levyKhinchinExponentWithCentering, σ2NN, gaussianDrift,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
      ring
    -- Proof comment: convolution multiplies characteristic functions, so the exponents add.
    simpa [finiteCanonicalLaw_local, γ, π, ProbabilityMeasure.toMeasure_mul,
      MeasureTheory.charFun_conv] using
      (show charFun (γ * π) t = Complex.exp (levyKhinchinExponent τ t) by
        rw [ProbabilityMeasure.toMeasure_mul, MeasureTheory.charFun_conv, hγ.charFun_eq_exp,
          hπ.charFun_eq_exp, ← Complex.exp_add, hsumExp])

/-- Helper for Theorem 16.17: the explicit finite-jump law is infinitely divisible because it is
the convolution of a Gaussian law and a compound-Poisson law. -/
private theorem finiteCanonicalLaw_isInfinitelyDivisible_local
    {τ : LevyKhinchinTriple} [IsFiniteMeasure τ.ν] (hτ : IsCanonicalTriple τ) :
    IsInfinitelyDivisible (finiteCanonicalLaw_local τ hτ.sigma2_nonneg) := by
  let σ2NN : NNReal := ⟨τ.sigma2, hτ.sigma2_nonneg⟩
  let gaussianDrift : ℝ := τ.b - ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂τ.ν
  let γ : ProbabilityMeasure ℝ := ⟨gaussianReal gaussianDrift σ2NN, inferInstance⟩
  let π : ProbabilityMeasure ℝ := compoundPoissonMeasure τ.ν
  have hγInfDiv : IsInfinitelyDivisible γ := by
    -- Proof comment: Gaussian laws have explicit convolution roots.
    simpa [γ] using gaussianReal_infinitelyDivisible_local gaussianDrift σ2NN
  have hπInfDiv : IsInfinitelyDivisible π := by
    -- Proof comment: compound-Poisson laws are already known to be infinitely divisible.
    simpa [π] using compoundPoissonMeasure_infinitelyDivisible τ.ν
  -- Proof comment: the explicit finite law is the convolution of those two infinitely divisible
  -- factors.
  simpa [finiteCanonicalLaw_local, γ, π] using isInfinitelyDivisible_mul_local hγInfDiv hπInfDiv

/-- Helper for Theorem 16.17: a Lévy--Khinchin representation with finite jump measure is
automatically infinitely divisible. -/
private theorem isInfinitelyDivisible_of_hasLevyKhinchinRepresentation_of_isFiniteMeasure_local
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} [IsFiniteMeasure τ.ν]
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    IsInfinitelyDivisible μ := by
  have hmodel :
      HasLevyKhinchinRepresentation
        (finiteCanonicalLaw_local τ hτ.isCanonicalTriple.sigma2_nonneg) τ :=
    finiteCanonicalLaw_hasLevyKhinchinRepresentation_local hτ.isCanonicalTriple
  have hmodelEq :
      finiteCanonicalLaw_local τ hτ.isCanonicalTriple.sigma2_nonneg = μ := by
    -- Proof comment: the explicit finite law and `μ` have the same characteristic function
    -- because they realize the same exponent.
    apply ProbabilityMeasure.toMeasure_injective
    refine Measure.ext_of_charFun ?_
    funext t
    rw [hmodel.charFun_eq_exp, hτ.charFun_eq_exp]
  have hmodelInfDiv :
      IsInfinitelyDivisible (finiteCanonicalLaw_local τ hτ.isCanonicalTriple.sigma2_nonneg) :=
    finiteCanonicalLaw_isInfinitelyDivisible_local hτ.isCanonicalTriple
  exact hmodelEq ▸ hmodelInfDiv

/-- Helper for Theorem 16.17: the Lévy--Khinchin exponents of the finite canonical truncations
converge pointwise back to the full exponent. -/
private lemma truncatedLevyKhinchinExponent_tendsto_local
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) :
    ∀ t : ℝ,
      Tendsto
        (fun n : ℕ ↦
          levyKhinchinExponent
            { sigma2 := τ.sigma2
              b := τ.b
              ν := τ.ν.restrict (IsCanonicalMeasure.canonicalMeasureCoverSet n) } t)
        atTop
        (𝓝 (levyKhinchinExponent τ t)) := by
  intro t
  let cover : ℕ → Set ℝ := IsCanonicalMeasure.canonicalMeasureCoverSet
  let F : ℕ → ℝ → ℂ :=
    fun n ↦ Set.indicator (cover n) (levyKhinchinCanonicalKernel t)
  let bound : ℝ → ℝ := fun x ↦ max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1
  have hmeas :
      ∀ n : ℕ, AEStronglyMeasurable (F n) τ.ν := by
    intro n
    -- Proof comment: each truncated kernel is a measurable indicator of the measurable cover set.
    simpa [F] using
      ((measurable_levyKhinchinCanonicalKernel t).indicator
        (measurableSet_canonicalMeasureCoverSet_local n)).aestronglyMeasurable
  have hboundInt : Integrable bound τ.ν := by
    -- Proof comment: the dominating function is a constant multiple of the canonical integrand.
    simpa [bound, mul_comm, mul_left_comm, mul_assoc] using
      hτ.isCanonicalMeasure.integrable_sq_min_one.const_mul (max (3 * |t| ^ (2 : ℕ)) 2)
  have hbound :
      ∀ n : ℕ, ∀ᵐ x ∂τ.ν, ‖F n x‖ ≤ bound x := by
    intro n
    filter_upwards with x
    by_cases hx : x ∈ cover n
    · -- Proof comment: on the active branch, the indicator reveals the original kernel bound.
      simpa [F, cover, hx, bound] using norm_levyKhinchinCanonicalKernel_bound t x
    · -- Proof comment: off the cover set, the indicator vanishes, so the domination is trivial.
      have hbound_nonneg : 0 ≤ bound x := by
        dsimp [bound]
        have hmax_nonneg : 0 ≤ max (3 * |t| ^ (2 : ℕ)) 2 := by
          exact le_trans (by norm_num) (le_max_right _ _)
        have hmin_nonneg : 0 ≤ min (x ^ (2 : ℕ)) 1 := by
          positivity
        exact mul_nonneg hmax_nonneg hmin_nonneg
      simpa [F, cover, hx] using hbound_nonneg
  have hzeroAE : ∀ᵐ x ∂τ.ν, x ≠ 0 := by
    -- Proof comment: canonical Lévy measures have no atom at `0`.
    rw [ae_iff]
    simp [hτ.isCanonicalMeasure.measure_singleton_zero]
  have hlim :
      ∀ᵐ x ∂τ.ν, Tendsto (fun n : ℕ ↦ F n x) atTop (𝓝 (levyKhinchinCanonicalKernel t x)) := by
    filter_upwards [hzeroAE] with x hx0
    obtain ⟨N, hN⟩ := IsCanonicalMeasure.mem_canonicalMeasureCover_of_ne_zero hx0
    have hEventually :
        (fun n : ℕ ↦ F n x) =ᶠ[atTop] fun _ : ℕ ↦ levyKhinchinCanonicalKernel t x := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hxmem : x ∈ cover n := mem_canonicalMeasureCoverSet_mono_local hn hN
      simp [F, cover, hxmem]
    -- Proof comment: every nonzero point belongs to all sufficiently far-out cover sets, so the
    -- truncated kernel is eventually constant there.
    exact Tendsto.congr' hEventually.symm tendsto_const_nhds
  have hIntegralTendsto :
      Tendsto (fun n : ℕ ↦ ∫ x : ℝ, F n x ∂τ.ν) atTop
        (𝓝 (∫ x : ℝ, levyKhinchinCanonicalKernel t x ∂τ.ν)) := by
    -- Proof comment: dominated convergence upgrades the pointwise stabilization to convergence of
    -- the jump integrals.
    simpa [F, bound] using
      (MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := τ.ν)
        (f := levyKhinchinCanonicalKernel t)
        (bound := bound)
        hmeas hboundInt hbound hlim)
  have hRestrictIntegral :
      ∀ n : ℕ,
        ∫ x : ℝ, levyKhinchinCanonicalKernel t x ∂(τ.ν.restrict (cover n)) =
          ∫ x : ℝ, F n x ∂τ.ν := by
    intro n
    -- Proof comment: rewrite the restricted integral as the indicator integral over `τ.ν`.
    rw [show ∫ x : ℝ, levyKhinchinCanonicalKernel t x ∂(τ.ν.restrict (cover n)) =
        ∫ x in cover n, levyKhinchinCanonicalKernel t x ∂τ.ν by rfl]
    rw [← MeasureTheory.integral_indicator (measurableSet_canonicalMeasureCoverSet_local n)]
  have hIntegralTendstoRestrict :
      Tendsto
        (fun n : ℕ ↦ ∫ x : ℝ, levyKhinchinCanonicalKernel t x ∂(τ.ν.restrict (cover n)))
        atTop
        (𝓝 (∫ x : ℝ, levyKhinchinCanonicalKernel t x ∂τ.ν)) := by
    simpa [hRestrictIntegral] using hIntegralTendsto
  have hConst :
      Tendsto
        (fun _ : ℕ ↦
          (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * t : ℝ) : ℂ) * Complex.I))
        atTop
        (𝓝 ((((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          (((τ.b * t : ℝ) : ℂ) * Complex.I))) :=
    tendsto_const_nhds
  -- Proof comment: the Gaussian and drift terms stay fixed under truncation, so only the jump
  -- integral uses dominated convergence.
  have hsumTendsto :
      Tendsto
        (fun n : ℕ ↦
          (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * t : ℝ) : ℂ) * Complex.I) +
            ∫ x : ℝ, levyKhinchinCanonicalKernel t x ∂(τ.ν.restrict (cover n)))
        atTop
        (𝓝
          ((((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * t : ℝ) : ℂ) * Complex.I) +
            ∫ x : ℝ, levyKhinchinCanonicalKernel t x ∂τ.ν)) :=
    hConst.add hIntegralTendstoRestrict
  simpa [levyKhinchinExponent, levyKhinchinExponentWithCentering, levyKhinchinCanonicalKernel,
    levyKhinchinCanonicalKernelLocal, cover] using hsumTendsto

/-- Helper for Theorem 16.17: the finite canonical laws of the canonical cover truncations
converge weakly back to the original represented law. -/
private theorem truncatedFiniteCanonicalLaw_tendsto_local
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    Tendsto
      (fun n : ℕ ↦
        let truncTriple : LevyKhinchinTriple :=
          { sigma2 := τ.sigma2
            b := τ.b
            ν := τ.ν.restrict (IsCanonicalMeasure.canonicalMeasureCoverSet n) }
        letI : IsFiniteMeasure truncTriple.ν :=
          isFiniteMeasure_restrict_canonicalMeasureCoverSet_local
            hτ.isCanonicalTriple.isCanonicalMeasure n
        finiteCanonicalLaw_local truncTriple hτ.isCanonicalTriple.sigma2_nonneg)
      atTop
      (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 ?_
  intro t
  have hExp :
      Tendsto
        (fun n : ℕ ↦
          Complex.exp
            (levyKhinchinExponent
              { sigma2 := τ.sigma2
                b := τ.b
                ν := τ.ν.restrict (IsCanonicalMeasure.canonicalMeasureCoverSet n) } t))
        atTop
        (𝓝 (Complex.exp (levyKhinchinExponent τ t))) :=
    (Complex.continuous_exp.continuousAt.tendsto.comp
      (truncatedLevyKhinchinExponent_tendsto_local hτ.isCanonicalTriple t))
  convert hExp using 1
  · ext n
    let truncTriple : LevyKhinchinTriple :=
      { sigma2 := τ.sigma2
        b := τ.b
        ν := τ.ν.restrict (IsCanonicalMeasure.canonicalMeasureCoverSet n) }
    letI : IsFiniteMeasure truncTriple.ν :=
      isFiniteMeasure_restrict_canonicalMeasureCoverSet_local
        hτ.isCanonicalTriple.isCanonicalMeasure n
    have htrunc :
        HasLevyKhinchinRepresentation
          (finiteCanonicalLaw_local truncTriple hτ.isCanonicalTriple.sigma2_nonneg) truncTriple :=
      finiteCanonicalLaw_hasLevyKhinchinRepresentation_local
        (isCanonicalTriple_restrict_canonicalMeasureCoverSet_local hτ.isCanonicalTriple n)
    simpa [truncTriple] using htrunc.charFun_eq_exp t
  · rw [hτ.charFun_eq_exp]

/-- Helper for Theorem 16.17: every Lévy--Khintchin representation comes from an infinitely
divisible law. -/
private lemma hasLevyKhinchinRepresentation_isInfinitelyDivisible_local
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    IsInfinitelyDivisible μ := by
  -- Proof comment: use finite canonical cover truncations and weak-limit stability, so the
  -- infinite-jump branch reduces to the finite converse proved just above.
  refine MeasureTheory.ProbabilityMeasure.isInfinitelyDivisible_of_tendsto ?_
    (truncatedFiniteCanonicalLaw_tendsto_local hτ)
  intro n
  let truncTriple : LevyKhinchinTriple :=
    { sigma2 := τ.sigma2
      b := τ.b
      ν := τ.ν.restrict (IsCanonicalMeasure.canonicalMeasureCoverSet n) }
  letI : IsFiniteMeasure truncTriple.ν :=
    isFiniteMeasure_restrict_canonicalMeasureCoverSet_local
      hτ.isCanonicalTriple.isCanonicalMeasure n
  have htrunc :
      HasLevyKhinchinRepresentation
        (finiteCanonicalLaw_local truncTriple hτ.isCanonicalTriple.sigma2_nonneg) truncTriple :=
    finiteCanonicalLaw_hasLevyKhinchinRepresentation_local
      (isCanonicalTriple_restrict_canonicalMeasureCoverSet_local hτ.isCanonicalTriple n)
  simpa [truncTriple] using
    isInfinitelyDivisible_of_hasLevyKhinchinRepresentation_of_isFiniteMeasure_local htrunc

-- Proof sketch: the forward implication now routes through the theorem-local exact-root
-- approximation frontier, and the reverse implication is the converse theorem already extracted
-- in Remark 16.18.
/-- Theorem 16.17: a probability measure on `ℝ` is infinitely divisible if and only if its
characteristic function admits a unique Lévy--Khinchin representation by a canonical triple
`(σ², b, ν)`; equivalently, `charFun μ = exp ∘ levyKhinchinExponent τ`. Here `ν` is the Lévy
measure, `σ²` the Gaussian coefficient, and `b` the centering constant. -/
theorem isInfinitelyDivisible_iff_exists_unique_levyKhinchin_triple
    (μ : ProbabilityMeasure ℝ) :
    IsInfinitelyDivisible μ ↔
      ∃! τ : LevyKhinchinTriple, HasLevyKhinchinRepresentation μ τ := by
  constructor
  · intro hμ
    obtain ⟨τ, hτ⟩ := levyKhinchinTriple_exists_of_isInfinitelyDivisible_local hμ
    refine ⟨τ, hτ, ?_⟩
    intro τ' hτ'
    exact levyTriple_eq_of_same_representation (μ := μ) hτ' hτ
  · rintro ⟨τ, hτ, _huniq⟩
    exact hasLevyKhinchinRepresentation_isInfinitelyDivisible_local hτ

end MeasureTheory.ProbabilityMeasure
