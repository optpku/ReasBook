/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

open MeasureTheory ProbabilityTheory Filter

universe u

namespace MeasureTheory.Measure

section AlongZero

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]
variable {t : ℕ → ℝ}

/-- Helper for Exercise 15.2.4: equality in the norm bound forces the real Fourier kernel to be
almost surely constant. -/
private lemma ae_innerProbChar_eq_charFun_of_norm_eq_one (u : ℝ)
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
    have hge : μ.real Set.univ * (1 : ℝ) ≤ ‖∫ x, BoundedContinuousFunction.innerProbChar u x ∂μ‖ := by
      rw [hnormIntegral]
      simp
    exact False.elim (not_lt_of_ge hge hlt)

/-- Helper for Exercise 15.2.4: equal complex phases on the real line differ by an integral
multiple of `2π`. -/
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

/-- Helper for Exercise 15.2.4: on `ℝ`, the real inner product is ordinary multiplication. -/
private lemma realInner_eq_mul (x y : ℝ) : inner ℝ x y = x * y := by
  -- Normalize the real inner product through the scalar-field formula.
  have hInnerOne : inner ℝ x (1 : ℝ) = x := by
    have hInnerOne' : inner ℝ x (1 : ℝ) = 1 * (starRingEnd ℝ) x := RCLike.inner_apply x (1 : ℝ)
    simpa using hInnerOne'
  calc
    inner ℝ x y = inner ℝ x (y • (1 : ℝ)) := by simp
    _ = y * inner ℝ x (1 : ℝ) := by rw [real_inner_smul_right]
    _ = y * x := by rw [hInnerOne]
    _ = x * y := by ring

/-- Helper for Exercise 15.2.4: equal real phases yield phase `1` for their difference. -/
private lemma expSubMulI_eq_one_of_exp_eq_exp {x y u : ℝ}
    (hxy : Complex.exp (x * u * Complex.I) = Complex.exp (y * u * Complex.I)) :
    Complex.exp ((((x - y : ℝ) : ℂ) * u) * Complex.I) = 1 := by
  obtain ⟨z, hz⟩ := exists_int_sub_mul_eq_of_exp_eq_exp (x := x) (y := y) (u := u) hxy
  have hzC : ((((x - y) * u : ℝ) : ℂ)) = (2 * Real.pi : ℂ) * z := by
    exact_mod_cast hz
  -- Package the real-to-complex cast normalization once before applying the periodicity lemma.
  calc
    Complex.exp ((((x - y : ℝ) : ℂ) * u) * Complex.I) =
        Complex.exp ((((x - y) * u : ℝ) : ℂ) * Complex.I) := by
          congr 1
          push_cast
          ring
    _ =
        Complex.exp (((2 * Real.pi : ℂ) * z) * Complex.I) := by
          rw [hzC]
    _ = Complex.exp ((z : ℂ) * (2 * Real.pi * Complex.I)) := by
          congr 1
          ring
    _ = 1 := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.exp_int_mul_two_pi_mul_I z

/-- Helper for Exercise 15.2.4: a nonzero real cannot have phase `1` along a nonzero frequency
sequence with `|t n| → 0`. -/
private lemma eq_zero_of_exp_mul_I_eq_one_along_zero
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

/-- Helper for Exercise 15.2.4: a probability law with full mass on a singleton is the
corresponding Dirac measure. -/
private lemma eq_dirac_of_measure_singleton_eq_one {b : ℝ}
    (hb : μ ({b} : Set ℝ) = 1) :
    μ = Measure.dirac b := by
  have hae : ∀ᵐ x ∂μ, x ∈ ({b} : Set ℝ) :=
    (mem_ae_iff_prob_eq_one (measurableSet_singleton b)).2 hb
  -- Restricting to the singleton turns the law into a scalar multiple of the Dirac mass.
  calc
    μ = μ.restrict ({b} : Set ℝ) := (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ = μ ({b} : Set ℝ) • Measure.dirac b := Measure.restrict_singleton μ b
    _ = Measure.dirac b := by rw [hb, one_smul]

-- Proof sketch: use the doubling estimate for `1 - Re φ(2 t)` together with the hypothesis
-- `‖φ (t n)‖ = 1` to show that the law `μ` has the characteristic function of a Dirac measure.
/-- Law-level owner form of Exercise 15.2.4 (1): if a real probability law has characteristic
function of modulus `1` along a nonzero sequence of frequencies with `|t_n| ↓ 0`, then the law is
a Dirac mass. -/
theorem eq_dirac_of_charFun_norm_eq_one_along_zero
    (ht_antitone : Antitone fun n ↦ |t n|)
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
    -- Any two points in the phase-agreement set have zero difference by the small-frequency
    -- rigidity lemma.
    refine hSae.mono fun x hxS ↦ ?_
    apply Set.mem_singleton_iff.mpr
    have hxb : x - b = 0 := by
      -- Route correction: hide the real/complex phase-gap normalization in one helper lemma.
      apply eq_zero_of_exp_mul_I_eq_one_along_zero (t := t) ht_zero ht_nonzero
      intro n
      -- Convert the common phase identity to the scalar multiplication form expected below.
      have hxy : Complex.exp (x * t n * Complex.I) = Complex.exp (b * t n * Complex.I) := by
        simpa [BoundedContinuousFunction.innerProbChar_apply, realInner_eq_mul, mul_assoc,
          mul_left_comm, mul_comm]
          using (hxS n).trans (hbS n).symm
      exact expSubMulI_eq_one_of_exp_eq_exp (x := x) (y := b) (u := t n) hxy
    exact sub_eq_zero.mp hxb
  have hbprob : μ ({b} : Set ℝ) = 1 :=
    (mem_ae_iff_prob_eq_one (measurableSet_singleton b)).mp hsingleton_ae
  exact ⟨b, eq_dirac_of_measure_singleton_eq_one hbprob⟩

-- Proof sketch: apply the first law-level statement, then the additional hypothesis
-- `φ (t n) = 1` forces the Dirac characteristic function to be identically `1`, hence its atom is
-- located at `0`.
/-- Law-level owner form of Exercise 15.2.4 (2): if in addition the characteristic function is
equal to `1` along that same nonzero sequence, then the law is `δ₀`. -/
theorem eq_dirac_zero_of_charFun_eq_one_along_zero
    (ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_one : ∀ n, charFun μ (t n) = 1) :
    μ = Measure.dirac 0 := by
  have hφ_unit : ∀ n, ‖charFun μ (t n)‖ = 1 := by
    intro n
    simp [hφ_one n]
  obtain ⟨b, hb⟩ :=
    eq_dirac_of_charFun_norm_eq_one_along_zero ht_antitone ht_zero ht_nonzero hφ_unit
  have hb_zero : b = 0 := by
    -- Rewriting the law as a Dirac measure reduces the extra hypothesis to a phase-rigidity
    -- statement for the atom location.
    apply eq_zero_of_exp_mul_I_eq_one_along_zero (t := t) ht_zero ht_nonzero
    intro n
    have hdirac : charFun (Measure.dirac b) (t n) = 1 := by
      simpa [hb] using hφ_one n
    rw [charFun_dirac] at hdirac
    simpa [realInner_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hdirac
  simpa [hb_zero] using hb

end AlongZero

end MeasureTheory.Measure

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

section AlongZero

variable (t : ℕ → ℝ)

-- Proof sketch: use the doubling estimate for `1 - Re φ(2 t)` together with the hypothesis
-- `‖φ (t n)‖ = 1` to show that the pushforward law `P.map X` is a Dirac measure, then conclude
-- that `X` is almost surely constant from `HasLaw.ae_iff`.
/-- Exercise 15.2.4 (1): if the characteristic function of a real random variable has modulus
`1` along a nonzero sequence of frequencies with `|t_n| ↓ 0`, then the random variable is almost
surely constant. -/
theorem ae_eq_const_of_charFun_norm_eq_one_along_zero
    (hX : Measurable X)
    (ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_unit : ∀ n, ‖charFun (P.map X) (t n)‖ = 1) :
    ∃ b : ℝ, X =ᵐ[P] fun _ ↦ b := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  obtain ⟨b, hb⟩ :=
    Measure.eq_dirac_of_charFun_norm_eq_one_along_zero ht_antitone ht_zero ht_nonzero hφ_unit
  refine ⟨b, ?_⟩
  let hX_law : HasLaw X (Measure.dirac b) P := ⟨hX.aemeasurable, hb⟩
  exact (hX_law.ae_iff (measurable_id.eq measurable_const)).2 (by simp)

-- Proof sketch: apply the law-level `δ₀` statement to the pushforward law `P.map X`, then use
-- `HasLaw.ae_iff` to transport the almost-everywhere identity under the Dirac law back to `P`.
/-- Exercise 15.2.4 (2): if in addition the characteristic function is equal to `1` along that
same nonzero sequence with `|t_n| ↓ 0`, then the random variable vanishes almost surely. -/
theorem ae_eq_zero_of_charFun_eq_one_along_zero
    (hX : Measurable X)
    (ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_one : ∀ n, charFun (P.map X) (t n) = 1) :
    X =ᵐ[P] fun _ ↦ 0 := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  let hX_law : HasLaw X (Measure.dirac 0) P :=
    ⟨hX.aemeasurable,
      Measure.eq_dirac_zero_of_charFun_eq_one_along_zero
        ht_antitone ht_zero ht_nonzero hφ_one⟩
  exact (hX_law.ae_iff (measurable_id.eq measurable_const)).2 (by simp)

end AlongZero
