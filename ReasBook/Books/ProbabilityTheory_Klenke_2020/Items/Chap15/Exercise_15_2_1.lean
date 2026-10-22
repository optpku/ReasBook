/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory BoundedContinuousFunction

variable {d : ℕ}

/-- The phase-one set for the characteristic-function kernel at frequency `t`; equivalently, the
points `x` with `⟪x, t⟫ ∈ 2πℤ`. -/
def charFunPeriodSet (t : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | Complex.exp (inner ℝ x t * Complex.I) = 1}

/-- Membership in `charFunPeriodSet t` means that the owner Fourier kernel `innerProbChar t`
takes the value `1`. -/
@[simp]
theorem mem_charFunPeriodSet_iff_innerProbChar_eq_one {t x : EuclideanSpace ℝ (Fin d)} :
    x ∈ charFunPeriodSet t ↔ innerProbChar t x = 1 := by
  simp [charFunPeriodSet, innerProbChar_apply]

-- Proof sketch: apply `Complex.exp_eq_one_iff` to the purely imaginary number
-- `inner ℝ x t * Complex.I`, then compare real and imaginary parts.
/-- Membership in `charFunPeriodSet t` is equivalent to the phase `⟪x, t⟫` being an integral
multiple of `2π`. -/
theorem mem_charFunPeriodSet_iff_exists_int {t x : EuclideanSpace ℝ (Fin d)} :
    x ∈ charFunPeriodSet t ↔ ∃ z : ℤ, inner ℝ x t = (2 * Real.pi : ℝ) * z := by
  constructor
  · intro hx
    -- Convert the phase equation to the standard `2π i ℤ` normal form.
    change Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) = 1 at hx
    obtain ⟨z, hz⟩ := Complex.exp_eq_one_iff.mp hx
    refine ⟨z, ?_⟩
    -- Comparing imaginary parts recovers the real phase condition.
    have hzIm := congrArg Complex.im hz
    simpa [mul_assoc, mul_left_comm, mul_comm] using hzIm
  · rintro ⟨z, hz⟩
    -- Rewrite the phase as an integral multiple of `2π i`.
    change Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) = 1
    rw [hz]
    have hz' : ((((2 * Real.pi : ℝ) * z : ℝ) : ℂ) * Complex.I) =
        (z : ℂ) * (2 * Real.pi * Complex.I) := by
      simp [mul_left_comm, mul_comm]
    rw [hz']
    exact Complex.exp_int_mul_two_pi_mul_I z

-- Proof sketch: decompose `x` into its component orthogonal to `t` plus its projection onto the
-- line spanned by `t`. For `t ≠ 0`, the scalar coordinate along `t` is an integer multiple of
-- `2π / ‖t‖²` exactly when `x ∈ charFunPeriodSet t`.
/-- For `t ≠ 0`, the period set `charFunPeriodSet t` is the union of affine hyperplanes
orthogonal to `t`, translated by integer multiples of `((2π) / ‖t‖²) t`. -/
theorem charFunPeriodSet_eq_orthogonal_translate_set {t : EuclideanSpace ℝ (Fin d)} (ht : t ≠ 0) :
    charFunPeriodSet t =
      {x | ∃ y : EuclideanSpace ℝ (Fin d), ∃ z : ℤ,
        inner ℝ y t = 0 ∧ x = y + z • (((2 * Real.pi) / ‖t‖ ^ 2) • t)} := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := mem_charFunPeriodSet_iff_exists_int.mp hx
    have hnormsq : ‖t‖ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
    let y : EuclideanSpace ℝ (Fin d) := x - ((inner ℝ x t) / ‖t‖ ^ 2) • t
    -- Remove the component of `x` in the `t`-direction.
    have hy : inner ℝ y t = 0 := by
      dsimp [y]
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp [hnormsq]
      ring
    refine ⟨y, z, hy, ?_⟩
    have hproj : ((inner ℝ x t) / ‖t‖ ^ 2) • t = z • (((2 * Real.pi) / ‖t‖ ^ 2) • t) := by
      -- Rewrite the axial component as an integer multiple of the basic period vector.
      rw [hz]
      calc
        ((((2 * Real.pi : ℝ) * z) / ‖t‖ ^ 2) : ℝ) • t
            = (((z : ℝ) * ((2 * Real.pi : ℝ) / ‖t‖ ^ 2)) : ℝ) • t := by
                congr 1
                -- This is the scalar identity `(2π * z) / ‖t‖² = z * (2π / ‖t‖²)`.
                field_simp [hnormsq]
        _ = (z : ℝ) • (((2 * Real.pi : ℝ) / ‖t‖ ^ 2) • t) := by
              rw [smul_smul]
        _ = z • (((2 * Real.pi) / ‖t‖ ^ 2) • t) := by
              rw [Int.cast_smul_eq_zsmul ℝ]
    -- Reassemble `x` from its orthogonal and axial parts.
    have hxdecomp : x = y + ((inner ℝ x t) / ‖t‖ ^ 2) • t := by
      dsimp [y]
      abel
    calc
      x = y + ((inner ℝ x t) / ‖t‖ ^ 2) • t := hxdecomp
      _ = y + z • (((2 * Real.pi) / ‖t‖ ^ 2) • t) := by rw [hproj]
  · rintro ⟨y, z, hy, rfl⟩
    have hnormsq : ‖t‖ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
    -- Evaluate the phase on the orthogonal-plus-periodic decomposition.
    rw [mem_charFunPeriodSet_iff_exists_int]
    refine ⟨z, ?_⟩
    calc
      inner ℝ (y + z • (((2 * Real.pi) / ‖t‖ ^ 2) • t)) t
          = inner ℝ y t + inner ℝ (z • (((2 * Real.pi) / ‖t‖ ^ 2) • t)) t := by
              rw [inner_add_left]
      _ = inner ℝ (z • (((2 * Real.pi) / ‖t‖ ^ 2) • t)) t := by rw [hy, zero_add]
      _ = inner ℝ ((z : ℝ) • (((2 * Real.pi) / ‖t‖ ^ 2) • t)) t := by
              rw [Int.cast_smul_eq_zsmul ℝ]
      _ = (z : ℝ) * (((2 * Real.pi) / ‖t‖ ^ 2) * (‖t‖ ^ 2)) := by
              rw [real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      _ = (2 * Real.pi : ℝ) * z := by
            field_simp [hnormsq]

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]

/-- Helper for Exercise 15.2.1: if `charFun μ t = 1`, then the phase kernel `innerProbChar t`
is equal to `1` almost everywhere. -/
lemma ae_innerProbChar_eq_one_of_charFun_eq_one {t : EuclideanSpace ℝ (Fin d)}
    (hφ : charFun μ t = 1) :
    ∀ᵐ x ∂μ, innerProbChar t x = 1 := by
  have hnorm : ∀ᵐ x ∂μ, ‖innerProbChar t x‖ ≤ (1 : ℝ) := by
    -- The characteristic-function kernel always has unit norm.
    filter_upwards [] with x
    simp [innerProbChar_apply]
  rcases ae_eq_const_or_norm_integral_lt_of_norm_le_const
      (μ := μ) (f := innerProbChar t) (C := (1 : ℝ)) hnorm with hconst | hlt
  · -- In the equality case, identify the average with `charFun μ t = 1`.
    have havg : ⨍ x, innerProbChar t x ∂μ = (1 : ℂ) := by
      rw [average_eq_integral, ← charFun_eq_integral_innerProbChar, hφ]
    simpa [havg] using hconst
  · -- The strict inequality branch contradicts `‖charFun μ t‖ = ‖1‖`.
    have hnormIntegral : ‖∫ x, innerProbChar t x ∂μ‖ = (1 : ℝ) := by
      rw [← charFun_eq_integral_innerProbChar, hφ]
      norm_num
    have hge : μ.real Set.univ * (1 : ℝ) ≤ ‖∫ x, innerProbChar t x ∂μ‖ := by
      rw [hnormIntegral]
      simp
    exact False.elim (not_lt_of_ge hge hlt)

-- Proof sketch: rewrite `charFun μ t = 1` as equality in the triangle inequality
-- for the unit-modulus integrand `x ↦ exp (i \langle x, t \rangle)`, deduce that this integrand
-- is `1` almost everywhere, and translate that condition to `x ∈ charFunPeriodSet t`.
/-- Support statement for Exercise 15.2.1: if the characteristic function of a probability law on
`ℝ^d` takes the value `1` at frequency `t`, then the law is supported on
`H_t = charFunPeriodSet t`. -/
theorem measure_charFunPeriodSet_eq_one_of_charFun_eq_one {t : EuclideanSpace ℝ (Fin d)}
    (hφ : charFun μ t = 1) :
    μ (charFunPeriodSet t) = 1 := by
  have hae : ∀ᵐ x ∂μ, x ∈ charFunPeriodSet t := by
    -- The almost-everywhere phase constraint is exactly membership in `H_t`.
    filter_upwards [ae_innerProbChar_eq_one_of_charFun_eq_one hφ] with x hx
    exact mem_charFunPeriodSet_iff_innerProbChar_eq_one.mpr hx
  have hmeas : MeasurableSet (charFunPeriodSet t) := by
    -- `H_t` is the preimage of the closed singleton `{1}` under a continuous phase map.
    change MeasurableSet {x | innerProbChar t x = (1 : ℂ)}
    exact (isClosed_eq (innerProbChar t).continuous continuous_const).measurableSet
  exact (mem_ae_iff_prob_eq_one hmeas).mp hae

-- Proof sketch: use the support statement above to see that `exp (i \langle x, t \rangle) = 1`
-- for `μ`-almost every `x`, then factor the integrand defining `charFun μ (t + s)`
-- as `exp (i \langle x, s \rangle) * exp (i \langle x, t \rangle)` and simplify almost
-- everywhere.
/-- Helper for Exercise 15.2.1: if the characteristic function equals `1` at frequency `t`, then
it is periodic in the direction `t`, so `φ(t + s) = φ(s)` for every `s`. -/
theorem charFun_periodic_of_charFun_eq_one {t : EuclideanSpace ℝ (Fin d)}
    (hφ : charFun μ t = 1) :
    Function.Periodic (charFun μ) t := by
  intro s
  rw [charFun_eq_integral_innerProbChar, charFun_eq_integral_innerProbChar]
  refine integral_congr_ae ?_
  filter_upwards [ae_innerProbChar_eq_one_of_charFun_eq_one hφ] with x hx
  have hxt : Complex.exp (inner ℝ x t * Complex.I) = 1 := by
    simpa [innerProbChar_apply] using hx
  have hphase :
      (((inner ℝ x (s + t) : ℝ) : ℂ) * Complex.I) =
        (((inner ℝ x s : ℝ) : ℂ) * Complex.I) + (((inner ℝ x t : ℝ) : ℂ) * Complex.I) := by
    simp [inner_add_right, add_mul]
  -- Factor the kernel at frequency `s + t`, then use the a.e. phase-one condition.
  calc
    innerProbChar (s + t) x =
        Complex.exp
          ((((inner ℝ x s : ℝ) : ℂ) * Complex.I) + (((inner ℝ x t : ℝ) : ℂ) * Complex.I)) := by
          rw [innerProbChar_apply, hphase]
    _ = Complex.exp (inner ℝ x s * Complex.I) * Complex.exp (inner ℝ x t * Complex.I) := by
          rw [Complex.exp_add]
    _ = Complex.exp (inner ℝ x s * Complex.I) := by rw [hxt, mul_one]
    _ = innerProbChar s x := by rw [innerProbChar_apply]

/-- Exercise 15.2.1 (2): if the characteristic function equals `1` at frequency `t`, then it is
periodic in the direction `t`, so `φ(t + s) = φ(s)` for every `s`. -/
theorem charFun_add_eq_of_charFun_eq_one {t : EuclideanSpace ℝ (Fin d)}
    (hφ : charFun μ t = 1) (s : EuclideanSpace ℝ (Fin d)) :
    charFun μ (t + s) = charFun μ s := by
  simpa [add_comm] using charFun_periodic_of_charFun_eq_one hφ s
