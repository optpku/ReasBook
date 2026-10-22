/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
variable {X Y : Ω → EuclideanSpace ℝ (Fin d)}

-- Proof sketch: apply `MeasureTheory.norm_charFun_le_one` to the pushforward law `P.map X`,
-- using `Measure.isProbabilityMeasure_map hX.aemeasurable`.
/-- Lemma 15.11 (1): (i) The characteristic function of a measurable `ℝ^d`-valued random variable
has modulus at most `1` at every frequency. -/
theorem norm_charFun_map_le_one (hX : Measurable X) (t : EuclideanSpace ℝ (Fin d)) :
    ‖charFun (P.map X) t‖ ≤ 1 := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  simpa using (show ‖charFun (P.map X) t‖ ≤ 1 from norm_charFun_le_one t)

-- Proof sketch: apply `MeasureTheory.charFun_zero` to `P.map X` and use that a measurable
-- pushforward of a probability measure is again a probability measure.
/-- Lemma 15.11 (2): (i) The characteristic function of a measurable `ℝ^d`-valued random variable
takes the value `1` at the origin. -/
theorem charFun_map_zero (hX : Measurable X) :
    charFun (P.map X) 0 = 1 := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  simp

-- Proof sketch: first use `MeasureTheory.charFun_map_smul_comp` for the scaling `a • X`, then
-- apply `MeasureTheory.charFun_map_add_const` to the translated law.
section Affine

omit [IsProbabilityMeasure P]

/-- Lemma 15.11 (3): (ii) Affine changes of variables transform the characteristic function by
scaling the frequency and multiplying by the exponential translation factor. -/
theorem charFun_map_affine_eq [IsFiniteMeasure P] (hX : Measurable X) (a : ℝ)
    (b t : EuclideanSpace ℝ (Fin d)) :
    charFun (P.map (fun ω ↦ a • X ω + b)) t =
      charFun (P.map X) (a • t) * Complex.exp (inner ℝ b t * Complex.I) := by
  have hmap :
      P.map (fun ω ↦ a • X ω + b) = (P.map (fun ω ↦ a • X ω)).map (· + b) := by
    rw [show (fun ω ↦ a • X ω + b) = (· + b) ∘ fun ω ↦ a • X ω from rfl, ← Measure.map_map]
    all_goals fun_prop
  rw [hmap, charFun_map_add_const]
  simpa using
    (show charFun (P.map (fun ω ↦ a • X ω)) t = charFun (P.map X) (a • t) from
      charFun_map_smul_comp hX.aemeasurable a t)

end Affine

section FiniteMeasure

omit [IsProbabilityMeasure P]

variable [IsFiniteMeasure P]

-- Proof sketch: compare the characteristic functions of `P.map X` and `P.map (fun ω ↦ -X ω)`,
-- rewrite the second one using `MeasureTheory.charFun_neg`, and use
-- `MeasureTheory.Measure.ext_of_charFun`; equality with the complex conjugate is equivalent to
-- vanishing imaginary part.
/-- Lemma 15.11 (4): (iii) The law of `X` agrees with the law of `-X` exactly when the
characteristic function of `X` is real-valued. -/
theorem map_eq_map_neg_iff_charFun_real (hX : Measurable X) :
    P.map X = P.map (fun ω ↦ -X ω) ↔
      ∀ t : EuclideanSpace ℝ (Fin d), Complex.im (charFun (P.map X) t) = 0 := by
  have hmap_neg (t : EuclideanSpace ℝ (Fin d)) :
      charFun (P.map (fun ω ↦ -X ω)) t = charFun (P.map X) (-t) := by
    simpa using
      (show charFun (P.map (fun ω ↦ (-1 : ℝ) • X ω)) t = charFun (P.map X) ((-1 : ℝ) • t) from
        charFun_map_smul_comp hX.aemeasurable (-1) t)
  constructor
  · intro hμ t
    have hconj : conj (charFun (P.map X) t) = charFun (P.map X) t := by
      calc
        conj (charFun (P.map X) t) = charFun (P.map X) (-t) := by
          exact (charFun_neg t).symm
        _ = charFun (P.map (fun ω ↦ -X ω)) t := by
          symm
          exact hmap_neg t
        _ = charFun (P.map X) t := by rw [hμ]
    exact Complex.conj_eq_iff_im.mp hconj
  · intro hreal
    apply Measure.ext_of_charFun
    ext t
    calc
      charFun (P.map X) t = conj (charFun (P.map X) t) := by
        exact (Complex.conj_eq_iff_im.mpr (hreal t)).symm
      _ = charFun (P.map X) (-t) := by
        exact (charFun_neg t).symm
      _ = charFun (P.map (fun ω ↦ -X ω)) t := by
        symm
        exact hmap_neg t

-- Proof sketch: apply `ProbabilityTheory.IndepFun.charFun_map_fun_add_eq_mul` to the measurable
-- random variables `X` and `Y`.
/-- Lemma 15.11 (5): (iv) The characteristic function of the sum of two independent measurable
`ℝ^d`-valued random variables is the product of their characteristic functions. -/
theorem charFun_map_add_eq_mul (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    charFun (P.map (fun ω ↦ X ω + Y ω)) = charFun (P.map X) * charFun (P.map Y) := by
  simpa using hXY.charFun_map_fun_add_eq_mul hX.aemeasurable hY.aemeasurable

end FiniteMeasure

-- Proof sketch: rewrite `1 - Complex.re (MeasureTheory.charFun (P.map X) (2 • t))` as the
-- expectation of `1 - cos ⟪2 t, X⟫`, which is pointwise nonnegative.
/-- Lemma 15.11 (6): (v) The doubled-frequency real-part defect `1 - Re φ_X(2 t)` is nonnegative
for every frequency `t`. -/
theorem one_sub_re_charFun_two_smul_nonneg (hX : Measurable X)
    (t : EuclideanSpace ℝ (Fin d)) :
    0 ≤ 1 - Complex.re (charFun (P.map X) ((2 : ℝ) • t)) := by
  exact sub_nonneg.mpr <|
    (Complex.re_le_norm _).trans (norm_charFun_map_le_one hX ((2 : ℝ) • t))

-- Proof sketch: use the pointwise trigonometric inequality
-- `1 - cos (2 u) = 2 * (1 - (cos u)^2) ≤ 4 * (1 - cos u)` with `u = ⟪t, X⟫`, then take
-- expectations.
/-- Lemma 15.11 (7): (v) The real part of the characteristic function satisfies the doubling
estimate `1 - Re φ_X(2 t) ≤ 4 (1 - Re φ_X(t))`. -/
theorem one_sub_re_charFun_two_smul_le_four_mul (hX : Measurable X)
    (t : EuclideanSpace ℝ (Fin d)) :
    1 - Complex.re (charFun (P.map X) ((2 : ℝ) • t)) ≤
      4 * (1 - Complex.re (charFun (P.map X) t)) := by
  let μ := P.map X
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hint₂ : Integrable (BoundedContinuousFunction.innerProbChar ((2 : ℝ) • t)) μ :=
    BoundedContinuousFunction.integrable μ _
  have hint₁ : Integrable (BoundedContinuousFunction.innerProbChar t) μ :=
    BoundedContinuousFunction.integrable μ _
  have hcos₂ : Integrable (fun x ↦ Real.cos (inner ℝ x ((2 : ℝ) • t))) μ := by
    simpa [BoundedContinuousFunction.innerProbChar_apply, Complex.exp_ofReal_mul_I_re] using
      hint₂.re
  have hcos₁ : Integrable (fun x ↦ Real.cos (inner ℝ x t)) μ := by
    simpa [BoundedContinuousFunction.innerProbChar_apply, Complex.exp_ofReal_mul_I_re] using
      hint₁.re
  have hre₂ :
      Complex.re (charFun μ ((2 : ℝ) • t)) = ∫ x, Real.cos (inner ℝ x ((2 : ℝ) • t)) ∂μ := by
    rw [charFun_eq_integral_innerProbChar]
    simpa [BoundedContinuousFunction.innerProbChar_apply, Complex.exp_ofReal_mul_I_re] using
      (integral_re hint₂).symm
  have hre₁ : Complex.re (charFun μ t) = ∫ x, Real.cos (inner ℝ x t) ∂μ := by
    rw [charFun_eq_integral_innerProbChar]
    simpa [BoundedContinuousFunction.innerProbChar_apply, Complex.exp_ofReal_mul_I_re] using
      (integral_re hint₁).symm
  have hleft :
      1 - Complex.re (charFun μ ((2 : ℝ) • t)) =
        ∫ x, 1 - Real.cos (inner ℝ x ((2 : ℝ) • t)) ∂μ := by
    calc
      1 - Complex.re (charFun μ ((2 : ℝ) • t))
        = ∫ x, (1 : ℝ) ∂μ - ∫ x, Real.cos (inner ℝ x ((2 : ℝ) • t)) ∂μ := by rw [hre₂]; simp
      _ = ∫ x, 1 - Real.cos (inner ℝ x ((2 : ℝ) • t)) ∂μ := by
        rw [← integral_sub (integrable_const 1) hcos₂]
  have hright :
      1 - Complex.re (charFun μ t) = ∫ x, 1 - Real.cos (inner ℝ x t) ∂μ := by
    calc
      1 - Complex.re (charFun μ t)
        = ∫ x, (1 : ℝ) ∂μ - ∫ x, Real.cos (inner ℝ x t) ∂μ := by rw [hre₁]; simp
      _ = ∫ x, 1 - Real.cos (inner ℝ x t) ∂μ := by rw [← integral_sub (integrable_const 1) hcos₁]
  have hpoint :
      ∀ x, 1 - Real.cos (inner ℝ x ((2 : ℝ) • t)) ≤ 4 * (1 - Real.cos (inner ℝ x t)) := by
    intro x
    rw [inner_smul_right, Real.cos_two_mul]
    nlinarith [sq_nonneg (Real.cos (inner ℝ x t) - 1)]
  rw [hleft]
  calc
    ∫ x, 1 - Real.cos (inner ℝ x ((2 : ℝ) • t)) ∂μ
      ≤ ∫ x, 4 * (1 - Real.cos (inner ℝ x t)) ∂μ := by
        refine integral_mono ((integrable_const 1).sub hcos₂) (((integrable_const 1).sub hcos₁).const_mul 4) hpoint
    _ = 4 * ∫ x, 1 - Real.cos (inner ℝ x t) ∂μ := by rw [integral_const_mul]
    _ = 4 * (1 - Complex.re (charFun μ t)) := by rw [← hright]
