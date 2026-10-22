/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Topology ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: for every `λ ≥ 0`, the integrand `ω ↦ exp (-(λ * X ω))` is bounded by `1` on the
-- almost-everywhere set where `0 ≤ X ω`, hence it is integrable on a probability space. This gives
-- `Ici 0 ⊆ integrableExpSet (-X) P`, so every `λ > 0` belongs to the interior.
/-- A nonnegative random variable has Laplace transform defined on the open right half-line. -/
theorem Ioi_subset_interior_integrableExpSet_neg_of_nonneg
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) :
    Ioi (0 : ℝ) ⊆ interior (integrableExpSet (-X) P) := by
  have h_nonneg_mem : Ici (0 : ℝ) ⊆ integrableExpSet (-X) P := by
    intro s hs
    refine Integrable.mono'
      (integrable_const (1 : ℝ))
      ((hX_meas.neg.const_mul s).exp.aestronglyMeasurable) ?_
    filter_upwards [hX_nonneg] with ω hω
    have hsX : 0 ≤ s * X ω := mul_nonneg hs hω
    have hle : Real.exp (-(s * X ω)) ≤ 1 := by
      simpa using Real.exp_le_one_iff.mpr (by linarith : -(s * X ω) ≤ 0)
    simpa [Pi.neg_apply, neg_mul, mul_comm, mul_left_comm, mul_assoc,
      abs_of_nonneg (Real.exp_pos _).le] using hle
  intro t ht
  exact (interior_mono h_nonneg_mem) (by simpa [interior_Ici] using ht)

-- Proof sketch: rewrite the Laplace transform as the moment-generating function `mgf (-X) P`,
-- place `λ` in `interior (integrableExpSet (-X) P)` using the preceding lemma, and then apply the
-- canonical identity `ProbabilityTheory.iteratedDeriv_mgf`.
/-- For Example 6.29, a nonnegative random variable `X` has Laplace transform
`λ ↦ P[fun ω ↦ exp (-(λ * X ω))] = mgf (-X) P λ` has `n`th derivative
`P[fun ω ↦ (-(X ω)) ^ n * exp (-(λ * X ω))]` for every `λ > 0`. -/
theorem iteratedDeriv_laplaceTransform_eq
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv n (mgf (-X) P) t =
      P[fun ω ↦ (-(X ω)) ^ n * Real.exp (-(t * X ω))] := by
  have ht_mem : t ∈ interior (integrableExpSet (-X) P) :=
    Ioi_subset_interior_integrableExpSet_neg_of_nonneg hX_meas hX_nonneg ht
  simpa [Pi.neg_apply, neg_mul, mul_comm, mul_left_comm, mul_assoc] using
    iteratedDeriv_mgf ht_mem n

-- Proof sketch: once `λ > 0` is known to lie in the interior of `integrableExpSet (-X) P`, the
-- Laplace transform is analytic there by `ProbabilityTheory.analyticOn_mgf`; analyticity on an
-- open neighborhood implies `C^∞` regularity on `Set.Ioi 0`.
/-- The Laplace transform of a nonnegative random variable is infinitely differentiable on
`(0, ∞)`. -/
theorem laplaceTransform_contDiffOn
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) :
    ContDiffOn ℝ ⊤ (mgf (-X) P) (Ioi (0 : ℝ)) := by
  refine (analyticOn_mgf.mono ?_).contDiffOn_of_completeSpace
  exact Ioi_subset_interior_integrableExpSet_neg_of_nonneg hX_meas hX_nonneg

-- Proof sketch: specialize the preceding `n`th-derivative formula to `n = 1` and factor the minus
-- sign outside the expectation.
/-- The first derivative of the Laplace transform is `-P[X * exp (-λ X)]`. -/
theorem deriv_laplaceTransform_eq
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) {t : ℝ} (ht : 0 < t) :
    deriv (mgf (-X) P) t =
      -(P[fun ω ↦ X ω * Real.exp (-(t * X ω))]) := by
  have ht_mem : t ∈ interior (integrableExpSet (-X) P) :=
    Ioi_subset_interior_integrableExpSet_neg_of_nonneg hX_meas hX_nonneg ht
  simpa [Pi.neg_apply, neg_mul, mul_comm, mul_left_comm, mul_assoc, integral_neg] using
    deriv_mgf ht_mem

-- Proof sketch: specialize the general `n`th-derivative formula to `n = 2` and use
-- `(-(X ω)) ^ 2 = (X ω) ^ 2`.
/-- The second derivative of the Laplace transform is `P[X^2 * exp (-λ X)]`. -/
theorem second_iteratedDeriv_laplaceTransform_eq
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (mgf (-X) P) t =
      P[fun ω ↦ (X ω) ^ 2 * Real.exp (-(t * X ω))] := by
  have ht_mem : t ∈ interior (integrableExpSet (-X) P) :=
    Ioi_subset_interior_integrableExpSet_neg_of_nonneg hX_meas hX_nonneg ht
  simpa [Pi.neg_apply, neg_mul, mul_comm, mul_left_comm, mul_assoc] using
    iteratedDeriv_mgf ht_mem 2

/-- Helper for Example 6.29: the nonnegative Laplace-moment kernel
`t ↦ ∫ X^n * exp (-t X) dP` written in `ENNReal`. -/
noncomputable def laplaceMomentKernel (P : Measure Ω) (X : Ω → ℝ) (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((X ω) ^ n * Real.exp (-(t * X ω))) ∂P

/-- Helper for Example 6.29: after multiplying the `n`th derivative by `(-1)^n`, the Laplace
transform derivative formula becomes the nonnegative Laplace-moment kernel. -/
lemma signedIteratedDeriv_eq_laplaceMomentKernel
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (((-1 : ℝ) ^ n) * iteratedDeriv n (mgf (-X) P) t) =
      laplaceMomentKernel P X n t := by
  have ht_mem : t ∈ interior (integrableExpSet (-X) P) :=
    Ioi_subset_interior_integrableExpSet_neg_of_nonneg hX_meas hX_nonneg ht
  have h_int_raw :
      Integrable (fun ω ↦ (-(X ω)) ^ n * Real.exp (-(t * X ω))) P := by
    -- The standard exponential-moment lemma gives integrability for the unsigned derivative kernel.
    simpa [Pi.neg_apply, neg_mul, mul_comm, mul_left_comm, mul_assoc] using
      ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet
        (X := -X) (μ := P) ht_mem n
  have h_sign :
      ∀ ω,
        ((-1 : ℝ) ^ n) * ((-(X ω)) ^ n * Real.exp (-(t * X ω))) =
          (X ω) ^ n * Real.exp (-(t * X ω)) := by
    intro ω
    have hpow :
        ((-1 : ℝ) ^ n) * (-(X ω)) ^ n = (X ω) ^ n := by
      have hnegpow : (-(X ω)) ^ n = (-1 : ℝ) ^ n * (X ω) ^ n := by
        simpa using (neg_pow (X ω) n)
      have hsq : ((-1 : ℝ) ^ n) * (-1 : ℝ) ^ n = (1 : ℝ) := by
        rw [← pow_add]
        simp
      calc
        ((-1 : ℝ) ^ n) * (-(X ω)) ^ n = ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n * (X ω) ^ n) := by
            rw [hnegpow]
        _ = (((-1 : ℝ) ^ n) * (-1 : ℝ) ^ n) * (X ω) ^ n := by ring
        _ = (X ω) ^ n := by rw [hsq, one_mul]
    calc
      ((-1 : ℝ) ^ n) * ((-(X ω)) ^ n * Real.exp (-(t * X ω))) =
          (((-1 : ℝ) ^ n) * (-(X ω)) ^ n) * Real.exp (-(t * X ω)) := by ring
      _ = (X ω) ^ n * Real.exp (-(t * X ω)) := by rw [hpow]
  have h_int :
      Integrable (fun ω ↦ (X ω) ^ n * Real.exp (-(t * X ω))) P := by
    -- The sign correction converts the derivative kernel into a nonnegative integrand.
    have h_signed :
        Integrable
          (fun ω ↦ ((-1 : ℝ) ^ n) * ((-(X ω)) ^ n * Real.exp (-(t * X ω)))) P :=
      h_int_raw.const_mul ((-1 : ℝ) ^ n)
    convert h_signed using 1
    ext ω
    exact (h_sign ω).symm
  have h_nonneg :
      0 ≤ᵐ[P] fun ω ↦ (X ω) ^ n * Real.exp (-(t * X ω)) := by
    -- Nonnegativity comes from `X ≥ 0` almost everywhere and positivity of the exponential.
    filter_upwards [hX_nonneg] with ω hω
    exact mul_nonneg (pow_nonneg hω _) (Real.exp_pos _).le
  -- Rewrite the derivative as an integral and then transport it to a lower integral in `ENNReal`.
  rw [iteratedDeriv_laplaceTransform_eq hX_meas hX_nonneg n ht]
  calc
    ENNReal.ofReal
        (((-1 : ℝ) ^ n) *
          ∫ ω, (-(X ω)) ^ n * Real.exp (-(t * X ω)) ∂P) =
      ENNReal.ofReal
        (∫ ω, ((-1 : ℝ) ^ n) * ((-(X ω)) ^ n * Real.exp (-(t * X ω))) ∂P) := by
          rw [← integral_const_mul]
    _ = ENNReal.ofReal (∫ ω, (X ω) ^ n * Real.exp (-(t * X ω)) ∂P) := by
          congr 1
          apply integral_congr_ae
          exact Eventually.of_forall h_sign
    _ = laplaceMomentKernel P X n t := by
          rw [laplaceMomentKernel, MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]

/-- Helper for Example 6.29: the Laplace-moment kernel decreases as the Laplace parameter grows. -/
lemma antitone_laplaceMomentKernel
    {P : Measure Ω} {X : Ω → ℝ}
    (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) (n : ℕ) :
    Antitone (laplaceMomentKernel P X n) := by
  intro s t hst
  -- Compare the kernels pointwise and lift the inequality through the lower integral.
  refine lintegral_mono_ae ?_
  filter_upwards [hX_nonneg] with ω hω
  have hmul : s * X ω ≤ t * X ω := mul_le_mul_of_nonneg_right hst hω
  have hexp : Real.exp (-(t * X ω)) ≤ Real.exp (-(s * X ω)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hpow : 0 ≤ (X ω) ^ n := pow_nonneg hω _
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp hpow)

/-- Helper for Example 6.29: for nonnegative `t`, the Laplace-moment kernel is bounded above by
the plain `n`th moment. -/
lemma laplaceMomentKernel_le_moment
    {P : Measure Ω} {X : Ω → ℝ}
    (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    laplaceMomentKernel P X n t ≤ ∫⁻ ω, ENNReal.ofReal ((X ω) ^ n) ∂P := by
  -- The exponential factor is at most `1` on the almost-everywhere nonnegative set.
  refine lintegral_mono_ae ?_
  filter_upwards [hX_nonneg] with ω hω
  have htx : 0 ≤ t * X ω := mul_nonneg ht hω
  have hexp : Real.exp (-(t * X ω)) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (by linarith : -(t * X ω) ≤ 0)
  have hpow : 0 ≤ (X ω) ^ n := pow_nonneg hω _
  exact ENNReal.ofReal_le_ofReal (by
    simpa using mul_le_mul_of_nonneg_left hexp hpow)

/-- Helper for Example 6.29: along the explicit sequence `((k : ℝ) + 1)⁻¹`, the Laplace-moment
kernel converges upward to the full `n`th moment. -/
lemma tendsto_laplaceMomentKernel_invNat
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) (n : ℕ) :
    Tendsto
      (fun k : ℕ ↦ laplaceMomentKernel P X n (((k : ℝ) + 1)⁻¹))
      atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal ((X ω) ^ n) ∂P)) := by
  let u : ℕ → ℝ := fun k ↦ ((k : ℝ) + 1)⁻¹
  have hu_tendsto : Tendsto u atTop (𝓝 0) := by
    have hu_tendsto' :
        Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [u, one_div] using hu_tendsto'
  -- Apply monotone convergence to the increasing sequence of truncated kernels.
  refine MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
  · intro k
    -- Each kernel term is measurable because it is built from measurable powers and exponentials.
    simpa [laplaceMomentKernel, u, neg_mul, mul_comm, mul_left_comm, mul_assoc] using
      ((((hX_meas.pow_const n).mul ((hX_meas.const_mul (-(u k))).exp)).aemeasurable).ennreal_ofReal)
  · -- For each sample path with `X ω ≥ 0`, shrinking `u k` increases the exponential factor.
    filter_upwards [hX_nonneg] with ω hω
    intro i j hij
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hij
    have hu_le : u j ≤ u i := by
      dsimp [u]
      simpa [one_div] using one_div_le_one_div_of_le (by positivity) hij'
    have hmul : u j * X ω ≤ u i * X ω := mul_le_mul_of_nonneg_right hu_le hω
    have hexp : Real.exp (-(u i * X ω)) ≤ Real.exp (-(u j * X ω)) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hpow : 0 ≤ (X ω) ^ n := pow_nonneg hω _
    simpa [laplaceMomentKernel, u] using
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp hpow)
  · -- Pointwise, the exponential term tends to `1`, so the kernel tends to the full moment.
    filter_upwards [hX_nonneg] with ω hω
    have hmul :
        Tendsto (fun k : ℕ ↦ u k * X ω) atTop (𝓝 (0 : ℝ)) := by
      simpa using hu_tendsto.mul_const (X ω)
    have hexp :
        Tendsto (fun k : ℕ ↦ Real.exp (-(u k * X ω))) atTop (𝓝 (Real.exp 0)) := by
      simpa using Real.continuous_exp.continuousAt.tendsto.comp (Filter.Tendsto.neg hmul)
    have hreal :
        Tendsto
          (fun k : ℕ ↦ (X ω) ^ n * Real.exp (-(u k * X ω)))
          atTop
          (𝓝 ((X ω) ^ n * 1)) := by
      simpa using hexp.const_mul ((X ω) ^ n)
    simpa [u, laplaceMomentKernel] using
      (ENNReal.continuous_ofReal.tendsto ((X ω) ^ n * 1)).comp hreal

/-- Helper for Example 6.29: the `sSup` value coming from the antitone right-limit description is
exactly the full `n`th moment. -/
lemma sSup_image_laplaceMomentKernel_eq
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) (n : ℕ) :
    sSup (laplaceMomentKernel P X n '' Ioi (0 : ℝ)) =
      ∫⁻ ω, ENNReal.ofReal ((X ω) ^ n) ∂P := by
  have h_upper :
      sSup (laplaceMomentKernel P X n '' Ioi (0 : ℝ)) ≤
        ∫⁻ ω, ENNReal.ofReal ((X ω) ^ n) ∂P := by
    -- Every positive-parameter kernel value is bounded by the untruncated moment.
    refine sSup_le ?_
    rintro _ ⟨t, ht, rfl⟩
    exact laplaceMomentKernel_le_moment hX_nonneg n ht.le
  have h_seq :
      Tendsto
        (fun k : ℕ ↦ laplaceMomentKernel P X n (((k : ℝ) + 1)⁻¹))
        atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal ((X ω) ^ n) ∂P)) :=
    tendsto_laplaceMomentKernel_invNat hX_meas hX_nonneg n
  have h_lower :
      ∫⁻ ω, ENNReal.ofReal ((X ω) ^ n) ∂P ≤
        sSup (laplaceMomentKernel P X n '' Ioi (0 : ℝ)) := by
    -- The approximating sequence lies in the image, so its limit also lies below the supremum.
    have h_event :
        ∀ᶠ k : ℕ in atTop,
          laplaceMomentKernel P X n (((k : ℝ) + 1)⁻¹) ∈
            Iic (sSup (laplaceMomentKernel P X n '' Ioi (0 : ℝ))) := by
      filter_upwards with k
      have hk :
          laplaceMomentKernel P X n (((k : ℝ) + 1)⁻¹) ∈
            laplaceMomentKernel P X n '' Ioi (0 : ℝ) := by
        have hk_pos : 0 < (((k : ℝ) + 1)⁻¹ : ℝ) := by
          exact inv_pos.2 (by positivity)
        exact ⟨((k : ℝ) + 1)⁻¹, hk_pos, rfl⟩
      exact le_sSup hk
    exact isClosed_Iic.mem_of_tendsto h_seq h_event
  exact le_antisymm h_upper h_lower

-- Proof sketch: rewrite `(-1)^n * F^(n)(λ)` using the derivative formula above as the truncated
-- moment `∫ X^n exp (-λX) dP`, then apply monotone convergence as `λ ↓ 0`.
/-- Example 6.29: the right limit of the signed `n`th derivative of the Laplace transform recovers
the `n`th
nonnegative moment in `ENNReal`. -/
theorem tendsto_ofReal_signed_iteratedDeriv_laplaceTransform_right_zero
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) (n : ℕ) :
    Tendsto
      (fun t : ℝ ↦ ENNReal.ofReal (((-1 : ℝ) ^ n) * iteratedDeriv n (mgf (-X) P) t))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫⁻ ω, ENNReal.ofReal ((X ω) ^ n) ∂P)) := by
  -- Route correction: rewrite the derivative into a single antitone ENNReal kernel first, then
  -- identify the right-limit value through an explicit monotone approximation sequence.
  have h_kernel_tendsto :
      Tendsto (laplaceMomentKernel P X n) (𝓝[>] (0 : ℝ))
        (𝓝 (sSup (laplaceMomentKernel P X n '' Ioi (0 : ℝ)))) :=
    (antitone_laplaceMomentKernel hX_nonneg n).tendsto_nhdsGT 0
  have hsSup :
      sSup (laplaceMomentKernel P X n '' Ioi (0 : ℝ)) =
        ∫⁻ ω, ENNReal.ofReal ((X ω) ^ n) ∂P :=
    sSup_image_laplaceMomentKernel_eq hX_meas hX_nonneg n
  have h_eventually_eq :
      (fun t : ℝ ↦ ENNReal.ofReal (((-1 : ℝ) ^ n) * iteratedDeriv n (mgf (-X) P) t)) =ᶠ[𝓝[>] 0]
        laplaceMomentKernel P X n := by
    -- On the right-neighborhood of `0`, every parameter is positive, so the normalization lemma
    -- applies pointwise.
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact signedIteratedDeriv_eq_laplaceMomentKernel hX_meas hX_nonneg n ht.1
  exact hsSup ▸ Filter.Tendsto.congr' h_eventually_eq.symm h_kernel_tendsto
