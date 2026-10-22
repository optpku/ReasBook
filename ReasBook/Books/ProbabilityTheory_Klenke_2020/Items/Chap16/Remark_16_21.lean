/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- Helper for Remark 16.21: equality in the characteristic-function norm bound forces the real
Fourier kernel to be almost surely constant. -/
private lemma ae_innerProbChar_eq_charFun_of_norm_eq_one
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (u : ℝ)
    (hu : ‖charFun μ u‖ = 1) :
    ∀ᵐ x ∂μ, BoundedContinuousFunction.innerProbChar u x = charFun μ u := by
  have hnorm : ∀ᵐ x ∂μ, ‖BoundedContinuousFunction.innerProbChar u x‖ ≤ (1 : ℝ) := by
    -- The real Fourier kernel always has unit norm.
    filter_upwards [] with x
    simp [BoundedContinuousFunction.innerProbChar_apply]
  rcases ae_eq_const_or_norm_integral_lt_of_norm_le_const
      (μ := μ) (f := BoundedContinuousFunction.innerProbChar u) (C := (1 : ℝ)) hnorm with
      hconst | hlt
  · -- In the equality case, the average is exactly the characteristic function.
    simpa [average_eq_integral, charFun_eq_integral_innerProbChar] using hconst
  · -- The strict inequality branch contradicts `‖charFun μ u‖ = 1`.
    have hnormIntegral : ‖∫ x, BoundedContinuousFunction.innerProbChar u x ∂μ‖ = 1 := by
      rw [← charFun_eq_integral_innerProbChar, hu]
    have hge :
        μ.real Set.univ * (1 : ℝ) ≤ ‖∫ x, BoundedContinuousFunction.innerProbChar u x ∂μ‖ := by
      rw [hnormIntegral]
      simp
    exact False.elim (not_lt_of_ge hge hlt)

/-- Helper for Remark 16.21: equal complex phases on the real line differ by an integral multiple
of `2π`. -/
private lemma exists_int_sub_mul_eq_of_exp_eq_exp {x y u : ℝ}
    (hxy : Complex.exp (x * u * Complex.I) = Complex.exp (y * u * Complex.I)) :
    ∃ z : ℤ, (x - y) * u = (2 * Real.pi : ℝ) * z := by
  obtain ⟨z, hz⟩ := Complex.exp_eq_exp_iff_exists_int.mp hxy
  -- Comparing imaginary parts recovers the real phase gap.
  have hzIm := congrArg Complex.im hz
  have hphase : x * u = y * u + (2 * Real.pi : ℝ) * z := by
    simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hzIm
  refine ⟨z, ?_⟩
  calc
    (x - y) * u = x * u - y * u := by ring
    _ = (y * u + (2 * Real.pi : ℝ) * z) - y * u := by rw [hphase]
    _ = (2 * Real.pi : ℝ) * z := by ring

/-- Helper for Remark 16.21: on `ℝ`, the real inner product is ordinary multiplication. -/
private lemma realInner_eq_mul (x y : ℝ) : inner ℝ x y = x * y := by
  have h := real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y
  simp [Real.norm_eq_abs] at h
  nlinarith

/-- Helper for Remark 16.21: a nonzero real cannot have phase `1` along a nonzero frequency
sequence with `|t n| → 0`. -/
private lemma eq_zero_of_exp_mul_I_eq_one_along_zero
    {t : ℕ → ℝ}
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    {b : ℝ}
    (hb : ∀ n, Complex.exp (b * t n * Complex.I) = 1) :
    b = 0 := by
  by_contra hb0
  have hb_abs_pos : 0 < |b| := abs_pos.mpr hb0
  have hsmall : ∀ᶠ n in atTop, |t n| < (2 * Real.pi) / |b| :=
    ht_zero (Iio_mem_nhds <| by positivity)
  rcases mem_atTop_sets.mp hsmall with ⟨N, hN⟩
  obtain ⟨z, hz⟩ := exists_int_sub_mul_eq_of_exp_eq_exp
    (x := b) (y := 0) (u := t N) (by simpa using hb N)
  have hz_zero : z = 0 := by
    by_contra hz_ne
    have hz_cast : (1 : ℝ) ≤ |(z : ℝ)| := by
      exact_mod_cast Int.one_le_abs hz_ne
    have hz_lower : (2 * Real.pi : ℝ) ≤ |((2 * Real.pi : ℝ) * z)| := by
      calc
        (2 * Real.pi : ℝ) = (2 * Real.pi : ℝ) * 1 := by ring
        _ ≤ (2 * Real.pi : ℝ) * |(z : ℝ)| := by
          exact mul_le_mul_of_nonneg_left hz_cast Real.two_pi_pos.le
        _ = |((2 * Real.pi : ℝ) * z)| := by
          rw [abs_mul, abs_of_pos Real.two_pi_pos]
    have hz_upper : |((2 * Real.pi : ℝ) * z)| < 2 * Real.pi := by
      have hsmallN : |t N| < (2 * Real.pi) / |b| := hN N le_rfl
      calc
        |((2 * Real.pi : ℝ) * z)| = |(b - 0) * t N| := by rw [← hz]
        _ = |b * t N| := by simp
        _ = |b| * |t N| := by rw [abs_mul]
        _ < |b| * ((2 * Real.pi) / |b|) := mul_lt_mul_of_pos_left hsmallN hb_abs_pos
        _ = 2 * Real.pi := by
          field_simp [hb_abs_pos.ne']
    exact (not_lt_of_ge hz_lower hz_upper).elim
  have hbt : b * t N = 0 := by
    simpa [hz_zero] using hz
  have htN_zero : t N = 0 := (mul_eq_zero.mp hbt).resolve_left hb0
  exact ht_nonzero N htN_zero

/-- Helper for Remark 16.21: a probability law with full mass on a singleton is the corresponding
Dirac measure. -/
private lemma eq_diracMeasure_of_measure_singleton_eq_one {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {x : ℝ} (hx : μ ({x} : Set ℝ) = 1) :
    μ = Measure.dirac x := by
  have hae : ∀ᵐ y ∂μ, y ∈ ({x} : Set ℝ) :=
    (mem_ae_iff_prob_eq_one (measurableSet_singleton x)).2 hx
  -- Restricting to the singleton turns the law into the corresponding Dirac mass.
  calc
    μ = μ.restrict ({x} : Set ℝ) := (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ = μ ({x} : Set ℝ) • Measure.dirac x := Measure.restrict_singleton μ x
    _ = Measure.dirac x := by rw [hx, one_smul]

/-- Helper for Remark 16.21: if the characteristic function has modulus `1` along a nonzero
sequence of frequencies tending to `0`, then the law is a Dirac mass. -/
private lemma eq_diracMeasure_of_charFun_norm_eq_one_along_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {t : ℕ → ℝ}
    (_ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_unit : ∀ n, ‖charFun μ (t n)‖ = 1) :
    ∃ b : ℝ, μ = Measure.dirac b := by
  classical
  let S : Set ℝ := {x | ∀ n, BoundedContinuousFunction.innerProbChar (t n) x = charFun μ (t n)}
  have hSae : ∀ᵐ x ∂μ, x ∈ S := by
    -- Intersect the a.e. constancy statements for the whole frequency sequence.
    change ∀ᵐ x ∂μ, ∀ n : ℕ, BoundedContinuousFunction.innerProbChar (t n) x = charFun μ (t n)
    exact ae_all_iff.2 fun n ↦ ae_innerProbChar_eq_charFun_of_norm_eq_one (u := t n) (hφ_unit n)
  have hSmeas : MeasurableSet S := by
    -- The common phase-agreement set is a countable intersection of closed equalizer sets.
    have hS_eq : S = ⋂ n : ℕ, {x | BoundedContinuousFunction.innerProbChar (t n) x =
        charFun μ (t n)} := by
      ext x
      simp [S]
    rw [hS_eq]
    refine MeasurableSet.iInter fun n : ℕ ↦ ?_
    exact (isClosed_eq (BoundedContinuousFunction.innerProbChar (t n)).continuous
      continuous_const).measurableSet
  have hSprob : μ S = 1 := (mem_ae_iff_prob_eq_one hSmeas).mp hSae
  have hSnonempty : S.Nonempty := by
    by_contra hEmpty
    rw [Set.not_nonempty_iff_eq_empty] at hEmpty
    simp [hEmpty] at hSprob
  obtain ⟨b, hbS⟩ := hSnonempty
  have hsingleton_ae : ∀ᵐ x ∂μ, x ∈ ({b} : Set ℝ) := by
    -- Any two points in the phase-agreement set must coincide by the small-frequency rigidity.
    refine hSae.mono fun x hxS ↦ ?_
    apply Set.mem_singleton_iff.mpr
    have hxb : x - b = 0 := by
      apply eq_zero_of_exp_mul_I_eq_one_along_zero (t := t) ht_zero ht_nonzero
      intro n
      have hxy : Complex.exp (x * t n * Complex.I) = Complex.exp (b * t n * Complex.I) := by
        simpa [BoundedContinuousFunction.innerProbChar_apply, realInner_eq_mul, mul_assoc,
          mul_left_comm, mul_comm] using (hxS n).trans (hbS n).symm
      obtain ⟨z, hz⟩ := exists_int_sub_mul_eq_of_exp_eq_exp (x := x) (y := b) (u := t n) hxy
      have hzC : ((((x - b) * t n : ℝ) : ℂ)) = (2 * Real.pi : ℂ) * z := by
        exact_mod_cast hz
      have hphaseOne : Complex.exp (((((x - b) * t n : ℝ) : ℂ) * Complex.I)) = 1 := by
        calc
          Complex.exp (((((x - b) * t n : ℝ) : ℂ) * Complex.I))
              = Complex.exp (((2 * Real.pi : ℂ) * z) * Complex.I) := by rw [hzC]
          _ = Complex.exp ((z : ℂ) * (2 * Real.pi * Complex.I)) := by
                congr 1
                ring
          _ = 1 := by exact Complex.exp_int_mul_two_pi_mul_I z
      have hphaseOne' : Complex.exp (((x - b : ℂ) * (t n : ℂ)) * Complex.I) = 1 := by
        simpa using hphaseOne
      simpa [mul_assoc] using hphaseOne'
    exact sub_eq_zero.mp hxb
  have hbprob : μ ({b} : Set ℝ) = 1 :=
    (mem_ae_iff_prob_eq_one (measurableSet_singleton b)).mp hsingleton_ae
  exact ⟨b, eq_diracMeasure_of_measure_singleton_eq_one hbprob⟩

/-- Helper for Remark 16.21: if a positive convolution power is a Dirac law, then the original
law is already a Dirac law. -/
private lemma eq_diracProba_of_pow_eq_diracProba
    {μ : ProbabilityMeasure ℝ} {n : ℕ+} {x : ℝ}
    (hpow : μ ^ (n : ℕ) = diracProba x) :
    ∃ y : ℝ, μ = diracProba y := by
  let t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have ht_antitone : Antitone fun k ↦ |t k| := by
    intro m n hmn
    -- The reciprocal sequence `1 / (n + 1)` decreases and stays nonnegative.
    simp only [t]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
      (Nat.one_div_le_one_div (α := ℝ) hmn)
  have ht_zero : Tendsto (fun k ↦ |t k|) atTop (𝓝 0) := by
    -- The reciprocal sequence tends to `0`.
    have habs : (fun k ↦ |t k|) = fun k : ℕ ↦ 1 / ((k : ℝ) + 1) := by
      funext k
      have hk : 0 ≤ (k : ℝ) + 1 := by positivity
      dsimp [t]
      rw [abs_of_nonneg (one_div_nonneg.mpr hk)]
    rw [habs]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have ht_nonzero : ∀ k, t k ≠ 0 := by
    intro k
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp [t, hk]
  have hφ_unit : ∀ k, ‖charFun (μ : Measure ℝ) (t k)‖ = 1 := by
    intro k
    have hchar :
        charFun ((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) (t k) =
          charFun (Measure.dirac x) (t k) := by
      simp [hpow, MeasureTheory.diracProba]
    have hnorm : ‖charFun (μ : Measure ℝ) (t k) ^ (n : ℕ)‖ = 1 := by
      simpa [MeasureTheory.ProbabilityMeasure.charFun_pow, MeasureTheory.charFun_dirac] using
        congrArg norm hchar
    have hpow_one : ‖charFun (μ : Measure ℝ) (t k)‖ ^ (n : ℕ) = 1 := by
      simpa [norm_pow] using hnorm
    have hnonneg : 0 ≤ ‖charFun (μ : Measure ℝ) (t k)‖ := norm_nonneg _
    exact (pow_eq_one_iff_of_nonneg hnonneg n.ne_zero).1 hpow_one
  obtain ⟨y, hy⟩ :=
    eq_diracMeasure_of_charFun_norm_eq_one_along_zero ht_antitone ht_zero ht_nonzero hφ_unit
  refine ⟨y, ?_⟩
  -- Upgrade the measure-level conclusion to the owner probability measure.
  apply ProbabilityMeasure.toMeasure_injective
  simpa [MeasureTheory.diracProba] using hy

/-- Helper for Remark 16.21: the broad-stability scale factors are strictly positive. -/
private lemma scalePosOfBroadStable
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSense μ)
    {a d : ℕ+ → ℝ} (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable) :
    ∀ n : ℕ+, 0 < a n := by
  intro n
  rcases hμ with ⟨hnotDirac, _⟩
  by_contra hna
  have hzero : a n = 0 := le_antisymm (not_lt.mp hna) (ha_nonneg n)
  have hdiracPow : μ ^ (n : ℕ) = diracProba (d n) := by
    -- Zero slope collapses the affine pushforward to a Dirac mass.
    rw [hscale n, hzero]
    apply ProbabilityMeasure.toMeasure_injective
    ext s hs
    simp [hs]
  rcases eq_diracProba_of_pow_eq_diracProba hdiracPow with ⟨x, hx⟩
  exact hnotDirac x hx

/-- Helper for Remark 16.21: affine pushforwards commute with positive convolution powers, with
the translation term accumulating linearly. -/
private lemma map_affine_pow_eq_map_pow_affine
    (μ : ProbabilityMeasure ℝ) (a c : ℝ) (n : ℕ+) :
    (map μ (measurable_affineMap a c).aemeasurable) ^ (n : ℕ) =
      map (μ ^ (n : ℕ)) (measurable_affineMap a ((n : ℝ) * c)).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_charFun ?_
  ext t
  have hmap :
      charFun ((map μ (measurable_affineMap a c).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ)
          t =
        charFun (μ : Measure ℝ) (a * t) *
          Complex.exp ((((c * t : ℝ) : ℂ) * Complex.I)) := by
    -- Decompose the affine map into a scaling followed by a translation.
    rw [ProbabilityMeasure.toMeasure_map]
    have hcomp :
        Measure.map (fun x : ℝ ↦ a * x + c) (μ : Measure ℝ) =
          Measure.map (fun x : ℝ ↦ x + c) (Measure.map (fun x : ℝ ↦ a * x) (μ : Measure ℝ)) := by
      rw [show (fun x : ℝ ↦ a * x + c) = (fun x : ℝ ↦ x + c) ∘ fun x : ℝ ↦ a * x from rfl,
        ← Measure.map_map]
      all_goals fun_prop
    rw [hcomp, MeasureTheory.charFun_map_add_const]
    simpa [realInner_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.charFun_map_mul (μ := (μ : Measure ℝ)) a t)
  have htarget :
      charFun
          ((map (μ ^ (n : ℕ)) (measurable_affineMap a ((n : ℝ) * c)).aemeasurable :
              ProbabilityMeasure ℝ) : Measure ℝ) t =
        charFun (μ : Measure ℝ) (a * t) ^ (n : ℕ) *
          Complex.exp ((((((n : ℝ) * c) * t : ℝ) : ℂ) * Complex.I)) := by
    -- Rewrite the target affine image in the same characteristic-function coordinates.
    rw [ProbabilityMeasure.toMeasure_map]
    rw [show (fun x : ℝ ↦ a * x + (n : ℝ) * c) =
        (fun x : ℝ ↦ x + (n : ℝ) * c) ∘ fun x : ℝ ↦ a * x from rfl, ← Measure.map_map]
    · rw [MeasureTheory.charFun_map_add_const, MeasureTheory.charFun_map_mul,
        ProbabilityMeasure.charFun_pow]
      simp [realInner_eq_mul, mul_left_comm, mul_comm]
    all_goals fun_prop
  -- Both sides reduce to the same characteristic-function formula.
  calc
    charFun (((map μ (measurable_affineMap a c).aemeasurable) ^ (n : ℕ) :
        ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun
            ((map μ (measurable_affineMap a c).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ)
            t ^ (n : ℕ) := by
              simpa using
                congrArg (fun f : ℝ → ℂ ↦ f t)
                  (ProbabilityMeasure.charFun_pow
                    (map μ (measurable_affineMap a c).aemeasurable) (n : ℕ))
    _ = (charFun (μ : Measure ℝ) (a * t) *
          Complex.exp ((((c * t : ℝ) : ℂ) * Complex.I))) ^ (n : ℕ) := by
            rw [hmap]
    _ = charFun (μ : Measure ℝ) (a * t) ^ (n : ℕ) *
          Complex.exp (((((n : ℝ) * (c * t) : ℝ) : ℂ) * Complex.I)) := by
            rw [mul_pow, (Complex.exp_nat_mul ((((c * t : ℝ) : ℂ) * Complex.I)) (n : ℕ)).symm]
            congr 1
            norm_num
            ring
    _ = charFun (μ : Measure ℝ) (a * t) ^ (n : ℕ) *
          Complex.exp ((((((n : ℝ) * c) * t : ℝ) : ℂ) * Complex.I)) := by
            congr 2
            ring
    _ = charFun
          ((map (μ ^ (n : ℕ)) (measurable_affineMap a ((n : ℝ) * c)).aemeasurable :
              ProbabilityMeasure ℝ) : Measure ℝ) t := by
            rw [htarget]

/-- Helper for Remark 16.21: inverting one affine broad-stability identity produces an explicit
`n`th convolution root of the original law. -/
private lemma affineRootPow_eq_self_of_affinePow
    {μ : ProbabilityMeasure ℝ} {n : ℕ+} {a d : ℝ} (ha : 0 < a)
    (hpow : μ ^ (n : ℕ) = map μ (measurable_affineMap a d).aemeasurable) :
    let ν : ProbabilityMeasure ℝ :=
      map μ (measurable_affineMap a⁻¹ (-(a⁻¹ * d) / (n : ℝ))).aemeasurable
    ν ^ (n : ℕ) = μ := by
  let ν : ProbabilityMeasure ℝ :=
    map μ (measurable_affineMap a⁻¹ (-(a⁻¹ * d) / (n : ℝ))).aemeasurable
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  -- Transport the convolution power through the inverse affine map.
  calc
    ν ^ (n : ℕ)
        = map (μ ^ (n : ℕ))
            (measurable_affineMap a⁻¹ ((n : ℝ) * (-(a⁻¹ * d) / (n : ℝ)))).aemeasurable := by
              simpa [ν] using
                map_affine_pow_eq_map_pow_affine μ a⁻¹ (-(a⁻¹ * d) / (n : ℝ)) n
    _ = map (map μ (measurable_affineMap a d).aemeasurable)
          (measurable_affineMap a⁻¹ ((n : ℝ) * (-(a⁻¹ * d) / (n : ℝ)))).aemeasurable := by
            rw [hpow]
    _ = μ := by
          apply ProbabilityMeasure.toMeasure_injective
          -- Compose the affine map with its inverse normalization and simplify to `id`.
          rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
          rw [Measure.map_map
            (measurable_affineMap a⁻¹ ((n : ℝ) * (-(a⁻¹ * d) / (n : ℝ))))
            (measurable_affineMap a d)]
          have hcomp :
              ((fun x : ℝ ↦ a⁻¹ * x + (n : ℝ) * (-(a⁻¹ * d) / (n : ℝ))) ∘
                fun x : ℝ ↦ a * x + d) = fun x : ℝ ↦ x := by
            funext x
            simp [Function.comp, div_eq_mul_inv]
            field_simp [ha_ne, hn_ne]
            ring
          rw [hcomp]
          exact Measure.map_id (μ := (μ : Measure ℝ))

-- Proof sketch: extract the affine realizations of the convolution powers from
-- `IsStableInBroadSense.exists_scale_shift`; for each `n`, invert the corresponding affine map to
-- produce an `n`th convolution root of `μ`.
/-- Remark 16.21: if `μ` is stable in the broad sense, then it is infinitely divisible. -/
theorem isInfinitelyDivisible_of_isStableInBroadSense
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSense μ) :
    IsInfinitelyDivisible μ := by
  rcases hμ.exists_scale_shift with ⟨a, d, ha_nonneg, hscale⟩
  have ha_pos : ∀ n : ℕ+, 0 < a n := scalePosOfBroadStable hμ ha_nonneg hscale
  refine ⟨?_⟩
  intro n
  let ν : ProbabilityMeasure ℝ :=
    map μ (measurable_affineMap (a n)⁻¹ (-( (a n)⁻¹ * d n) / (n : ℝ))).aemeasurable
  refine ⟨ν, ?_⟩
  -- The inverse affine normalization furnishes the desired convolution root.
  simpa [ν] using
    affineRootPow_eq_self_of_affinePow (n := n) (a := a n) (d := d n) (ha_pos n) (hscale n)

end MeasureTheory.ProbabilityMeasure
