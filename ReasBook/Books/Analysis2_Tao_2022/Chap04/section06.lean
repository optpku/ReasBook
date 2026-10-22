/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap04
section Section06

/-- Definition 4.6.1 (Complex numbers): the set of complex numbers is
`{a + b i | a, b ∈ ℝ}`, where `i` is a symbol satisfying `i^2 = -1`.
In Lean, this is identified with the existing type `ℂ`. -/
abbrev complexNumbers : Type := ℂ

/-- Every complex number can be written in the form `a + b i` with `a b : ℝ`. -/
theorem complexNumbers_exists_real_imag (z : ℂ) :
    ∃ a b : ℝ, z = (a : ℂ) + (b : ℂ) * Complex.I := by
  refine ⟨z.re, z.im, ?_⟩
  simpa using (Complex.re_add_im z).symm

/-- Helper for Lemma 4.6.2: every complex number admits a real-imaginary pair
representation `z = a + bi`. -/
lemma helperForLemma_4_6_2_canonicalDecompositionExists (z : ℂ) :
    ∃ p : ℝ × ℝ, z = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
  refine ⟨(z.re, z.im), ?_⟩
  simpa using (Complex.re_add_im z).symm

/-- Helper for Lemma 4.6.2: any representation `z = a + bi` must use
`a = Re(z)` and `b = Im(z)`. -/
lemma helperForLemma_4_6_2_coordinatesFromRepresentation {z : ℂ} {p : ℝ × ℝ}
    (h : z = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :
    p.1 = z.re ∧ p.2 = z.im := by
  have hRe : z.re = p.1 := by
    exact (congrArg Complex.re h).trans (by simp)
  have hIm : z.im = p.2 := by
    exact (congrArg Complex.im h).trans (by simp)
  exact ⟨hRe.symm, hIm.symm⟩

/-- Helper for Lemma 4.6.2: the pair `(Re z, Im z)` is the unique coefficient
pair in a decomposition `z = a + bi`. -/
lemma helperForLemma_4_6_2_uniqueDecompositionPair (z : ℂ) (p : ℝ × ℝ)
    (h : z = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :
    p = (z.re, z.im) := by
  rcases helperForLemma_4_6_2_coordinatesFromRepresentation h with ⟨h1, h2⟩
  exact Prod.ext h1 h2

/-- Helper for Lemma 4.6.2: the imaginary unit squares to `-1`. -/
lemma helperForLemma_4_6_2_iSquared :
    Complex.I ^ 2 = (-1 : ℂ) := by
  simpa using Complex.I_sq

/-- Helper for Lemma 4.6.2: negation agrees with multiplication by `-1`. -/
lemma helperForLemma_4_6_2_negEqualsNegOneMul (z : ℂ) :
    -z = ((-1 : ℂ) * z) := by
  simpa using (neg_one_mul z).symm

/-- Lemma 4.6.2: every `z : ℂ` has a unique decomposition `z = a + b i` with
`a, b : ℝ`; moreover `i^2 = -1` and `-z = (-1)z` for all `z : ℂ`. -/
theorem complex_unique_decomposition_i_sq_and_neg_mul :
    (∀ z : ℂ, ∃! p : ℝ × ℝ, z = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∧
    Complex.I ^ 2 = (-1 : ℂ) ∧
    (∀ z : ℂ, -z = ((-1 : ℂ) * z)) := by
  constructor
  · intro z
    rcases helperForLemma_4_6_2_canonicalDecompositionExists z with ⟨p, hp⟩
    refine ⟨p, hp, ?_⟩
    intro q hq
    have hp' : p = (z.re, z.im) :=
      helperForLemma_4_6_2_uniqueDecompositionPair z p hp
    have hq' : q = (z.re, z.im) :=
      helperForLemma_4_6_2_uniqueDecompositionPair z q hq
    exact hq'.trans hp'.symm
  constructor
  · exact helperForLemma_4_6_2_iSquared
  · intro z
    exact helperForLemma_4_6_2_negEqualsNegOneMul z

/-- Definition 4.6.2 (Complex numbers): (i) a complex number is an ordered pair
`(a, b)` with `a, b ∈ ℝ`; (ii) equality is componentwise, i.e. `(a, b) = (c, d)`
iff `a = c` and `b = d`; (iii) the set of all such complex numbers is
`ℝ × ℝ`. -/
abbrev complexNumbersAsPairs : Type := ℝ × ℝ

/-- Componentwise addition on ordered pairs of real numbers. -/
abbrev complexPairAdd (z w : complexNumbersAsPairs) : complexNumbersAsPairs :=
  (z.1 + w.1, z.2 + w.2)

/-- Componentwise negation on ordered pairs of real numbers. -/
abbrev complexPairNeg (z : complexNumbersAsPairs) : complexNumbersAsPairs :=
  (-z.1, -z.2)

/-- The zero ordered pair `(0, 0)` in `ℝ × ℝ`. -/
abbrev complexPairZero : complexNumbersAsPairs := (0, 0)

/-- Definition 4.6.3 (Complex addition, negation, and zero): let `ℂ` be the set
of ordered pairs of real numbers. For `z = (a, b)` and `w = (c, d)`, define
`z + w := (a + c, b + d)`, `-z := (-a, -b)`, and `0_C := (0, 0)`. -/
def complexPairAddNegZeroData :
    (complexNumbersAsPairs → complexNumbersAsPairs → complexNumbersAsPairs) ×
      (complexNumbersAsPairs → complexNumbersAsPairs) × complexNumbersAsPairs :=
  (complexPairAdd, complexPairNeg, complexPairZero)

/-- Lemma 4.6.1 (Addition on `ℂ` satisfies the abelian group axioms): for all
`z₁ z₂ z₃ : ℂ`, (i) `z₁ + z₂ = z₂ + z₁`, (ii) `(z₁ + z₂) + z₃ = z₁ + (z₂ + z₃)`,
(iii) `z₁ + 0 = 0 + z₁ = z₁`, and (iv) `z₁ + (-z₁) = (-z₁) + z₁ = 0`.
In particular, `(ℂ, +)` is an abelian group with identity element `0`. -/
theorem complex_addition_abelian_group_axioms :
    (∀ z₁ z₂ : ℂ, z₁ + z₂ = z₂ + z₁) ∧
    (∀ z₁ z₂ z₃ : ℂ, (z₁ + z₂) + z₃ = z₁ + (z₂ + z₃)) ∧
    (∀ z₁ : ℂ, z₁ + 0 = z₁ ∧ 0 + z₁ = z₁) ∧
    (∀ z₁ : ℂ, z₁ + (-z₁) = 0 ∧ (-z₁) + z₁ = 0) := by
  constructor
  · intro z₁ z₂
    simpa using add_comm z₁ z₂
  constructor
  · intro z₁ z₂ z₃
    simpa using add_assoc z₁ z₂ z₃
  constructor
  · intro z₁
    constructor
    · simpa using add_zero z₁
    · simpa using zero_add z₁
  · intro z₁
    constructor
    · simpa using add_right_neg z₁
    · simpa using add_left_neg z₁

/-- Definition 4.6.4 (Complex multiplication): for complex numbers viewed as
ordered pairs z = (a, b) and w = (c, d), their product is
zw = (ac - bd, ad + bc), and the complex multiplicative identity is
1_C = (1, 0). -/
def complexPairMulOneData :
    (complexNumbersAsPairs → complexNumbersAsPairs → complexNumbersAsPairs) ×
      complexNumbersAsPairs :=
  (fun z w => (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1), (1, 0))

/-- Definition 4.6.5 (Embedding of real numbers into complex numbers): define
`ι : ℝ → ℂ` by identifying `x : ℝ` with `(x, 0)` in `ℂ`. -/
def realToComplexEmbedding : ℝ → ℂ :=
  fun x => (x : ℂ)

/-- The embedding of real numbers into complex numbers preserves equality,
addition, negation, and multiplication. -/
theorem realToComplexEmbedding_respects_operations :
    (∀ x y : ℝ, x = y ↔ realToComplexEmbedding x = realToComplexEmbedding y) ∧
    (∀ x₁ x₂ : ℝ,
      realToComplexEmbedding (x₁ + x₂) =
        realToComplexEmbedding x₁ + realToComplexEmbedding x₂) ∧
    (∀ x : ℝ, realToComplexEmbedding (-x) = -realToComplexEmbedding x) ∧
    (∀ x₁ x₂ : ℝ,
      realToComplexEmbedding (x₁ * x₂) =
        realToComplexEmbedding x₁ * realToComplexEmbedding x₂) := by
  constructor
  · intro x y
    simpa [realToComplexEmbedding]
  constructor
  · intro x₁ x₂
    simpa [realToComplexEmbedding]
  constructor
  · intro x
    simpa [realToComplexEmbedding]
  · intro x₁ x₂
    simpa [realToComplexEmbedding]

/-- Definition 4.6.6 (Imaginary unit): the imaginary unit is the complex number
`i ∈ ℂ` defined by `i := (0, 1)`. -/
def imaginaryUnit : ℂ :=
  ⟨0, 1⟩

/-- A complex number is real when its imaginary part vanishes. -/
def IsRealComplex (z : ℂ) : Prop :=
  z.im = 0

/-- A complex number is purely imaginary when its real part vanishes. -/
def IsPurelyImaginaryComplex (z : ℂ) : Prop :=
  z.re = 0

/-- Definition 4.6.7 (Real and imaginary parts; complex conjugate): for `z : ℂ`,
`z = Re(z) + i Im(z)`, a number is real iff `Im(z) = 0`, a number is purely
imaginary iff `Re(z) = 0`, and the complex conjugate is
`conj z = Re(z) - i Im(z)`. -/
theorem complex_real_imaginary_parts_and_conjugate (z : ℂ) :
    z = (z.re : ℂ) + Complex.I * (z.im : ℂ) ∧
    (IsRealComplex z ↔ z.im = 0) ∧
    (IsPurelyImaginaryComplex z ↔ z.re = 0) ∧
    star z = (z.re : ℂ) - Complex.I * (z.im : ℂ) := by
  constructor
  · simpa [mul_comm] using (Complex.re_add_im z).symm
  constructor
  · simp [IsRealComplex]
  constructor
  · simp [IsPurelyImaginaryComplex]
  · simpa [sub_eq_add_neg, mul_comm] using (Complex.re_add_im (star z)).symm

/-- Helper for Proposition 4.6.2: `Re(z)` equals `(z + \bar z)/2` written with
`star`. -/
lemma helperForProposition_4_6_2_re_eq_add_star (z : ℂ) :
    (z.re : ℂ) = (z + star z) / (2 : ℂ) := by
  simpa using (Complex.re_eq_add_conj z)

/-- Helper for Proposition 4.6.2: `Im(z)` equals `(z - \bar z)/(2i)` written
with `star`. -/
lemma helperForProposition_4_6_2_im_eq_sub_star (z : ℂ) :
    (z.im : ℂ) = (z - star z) / ((2 : ℂ) * Complex.I) := by
  simpa using (Complex.im_eq_sub_conj z)

/-- Proposition 4.6.2: for every complex number `z ∈ ℂ`,
`Re(z) = (z + \overline{z}) / 2` and `Im(z) = (z - \overline{z}) / (2i)`. -/
theorem complex_re_and_im_eq_conjugate_formulas (z : ℂ) :
    ((z.re : ℂ) = (z + star z) / (2 : ℂ)) ∧
    ((z.im : ℂ) = (z - star z) / ((2 : ℂ) * Complex.I)) := by
  constructor
  · exact helperForProposition_4_6_2_re_eq_add_star z
  · exact helperForProposition_4_6_2_im_eq_sub_star z

/-- Helper for Lemma 4.6.3: complex conjugation preserves addition,
negation, and multiplication. -/
lemma helperForLemma_4_6_3_conj_add_neg_mul (z w : ℂ) :
    star (z + w) = star z + star w ∧
    star (-z) = -star z ∧
    star (z * w) = star z * star w := by
  constructor
  · simpa using (starRingEnd ℂ).map_add z w
  constructor
  · simpa using (starRingEnd ℂ).map_neg z
  · simpa using (starRingEnd ℂ).map_mul z w

/-- Helper for Lemma 4.6.3: complex conjugation is involutive. -/
lemma helperForLemma_4_6_3_conj_involutive (z : ℂ) :
    star (star z) = z := by
  simpa using (star_star z)

/-- Helper for Lemma 4.6.3: complex conjugation is injective. -/
lemma helperForLemma_4_6_3_conj_eq_iff_eq (z w : ℂ) :
    star z = star w ↔ z = w := by
  simpa using (star_injective.eq_iff (a := z) (b := w))

/-- Helper for Lemma 4.6.3: fixed points of conjugation are exactly the real
complex numbers. -/
lemma helperForLemma_4_6_3_conj_fixed_iff_isReal (z : ℂ) :
    star z = z ↔ IsRealComplex z := by
  simpa [IsRealComplex] using (Complex.conj_eq_iff_im (z := z))

/-- Lemma 4.6.3 (Complex conjugation is an involution): for `z w : ℂ`,
complex conjugation satisfies
`
  \overline{z + w} = \bar z + \bar w,
  \overline{-z} = -\bar z,
  \overline{z w} = \bar z \, \bar w,
  \overline{\bar z} = z,
`
and moreover `\bar z = \bar w` iff `z = w`, while `\bar z = z` iff `z` is real. -/

theorem complex_conjugation_involution (z w : ℂ) :
    star (z + w) = star z + star w ∧
    star (-z) = -star z ∧
    star (z * w) = star z * star w ∧
    star (star z) = z ∧
    (star z = star w ↔ z = w) ∧
    (star z = z ↔ IsRealComplex z) := by
  rcases helperForLemma_4_6_3_conj_add_neg_mul z w with ⟨hAdd, hNeg, hMul⟩
  constructor
  · exact hAdd
  constructor
  · exact hNeg
  constructor
  · exact hMul
  constructor
  · exact helperForLemma_4_6_3_conj_involutive z
  constructor
  · exact helperForLemma_4_6_3_conj_eq_iff_eq z w
  · exact helperForLemma_4_6_3_conj_fixed_iff_isReal z

/-- Definition 4.6.8 (Complex absolute value): for `z = a + bi` with
`a b : ℝ`, the complex absolute value is the nonnegative real number
`|z| = sqrt (a^2 + b^2) = (a^2 + b^2)^(1/2)`. In Lean this is represented by
the complex norm `‖z‖`. -/
noncomputable abbrev complexAbsoluteValue (z : ℂ) : ℝ :=
  ‖z‖

/-- Lemma 4.6.4: for every `z ∈ ℂ`, the complex absolute value `|z|` is a
non-negative real number. -/
theorem complexAbsoluteValue_nonnegative (z : ℂ) :
    0 ≤ complexAbsoluteValue z := by
  simpa [complexAbsoluteValue] using norm_nonneg z

/-- Lemma 4.6.5: for every `z ∈ ℂ`, we have `|z| = 0` if and only if `z = 0`. -/
theorem complexAbsoluteValue_eq_zero_iff (z : ℂ) :
    complexAbsoluteValue z = 0 ↔ z = 0 := by
  simpa [complexAbsoluteValue] using (norm_eq_zero : ‖z‖ = 0 ↔ z = 0)

/-- Helper for Lemma 4.6.6: `z * conjugate(z)` is the real scalar
`Complex.normSq z`, viewed in `ℂ`. -/
lemma helperForLemma_4_6_6_mulConj_eq_normSqCast (z : ℂ) :
    z * star z = (Complex.normSq z : ℂ) := by
  simpa using (Complex.mul_conj z)

/-- Helper for Lemma 4.6.6: the real part of `z * conjugate(z)` is
`Complex.normSq z`. -/
lemma helperForLemma_4_6_6_mulConj_re_eq_normSq (z : ℂ) :
    (z * star z).re = Complex.normSq z := by
  simpa using congrArg Complex.re (helperForLemma_4_6_6_mulConj_eq_normSqCast z)

/-- Helper for Lemma 4.6.6: `(z * conjugate(z)).re` equals `|z|^2`. -/
lemma helperForLemma_4_6_6_mulConj_re_eq_absSq (z : ℂ) :
    (z * star z).re = (complexAbsoluteValue z) ^ 2 := by
  calc
    (z * star z).re = Complex.normSq z :=
      helperForLemma_4_6_6_mulConj_re_eq_normSq z
    _ = (complexAbsoluteValue z) ^ 2 := by
      simpa [complexAbsoluteValue] using (Complex.normSq_eq_norm_sq z)

/-- Helper for Lemma 4.6.6: `√(|z|^2) = |z|`. -/
lemma helperForLemma_4_6_6_sqrt_absSq_eq_absValue (z : ℂ) :
    Real.sqrt ((complexAbsoluteValue z) ^ 2) = complexAbsoluteValue z := by
  calc
    Real.sqrt ((complexAbsoluteValue z) ^ 2) = |complexAbsoluteValue z| := by
      simpa using (Real.sqrt_sq_eq_abs (complexAbsoluteValue z))
    _ = complexAbsoluteValue z := by
      exact abs_of_nonneg (complexAbsoluteValue_nonnegative z)

/-- Lemma 4.6.6: for every `z ∈ ℂ`, we have `z * \overline{z} = |z|^2`.
In particular, `|z| = sqrt (z * \overline{z})`, interpreted in Lean as
`|z| = sqrt ((z * \overline{z}).re)`. -/
theorem complex_mul_conj_eq_abs_sq_and_abs_eq_sqrt (z : ℂ) :
    z * star z = ((complexAbsoluteValue z) ^ 2 : ℂ) ∧
    complexAbsoluteValue z = Real.sqrt ((z * star z).re) := by
  constructor
  · calc
      z * star z = (Complex.normSq z : ℂ) :=
        helperForLemma_4_6_6_mulConj_eq_normSqCast z
      _ = ((complexAbsoluteValue z) ^ 2 : ℂ) := by
        simpa [complexAbsoluteValue] using
          congrArg (fun x : ℝ => (x : ℂ)) (Complex.normSq_eq_norm_sq z)
  · calc
      complexAbsoluteValue z = Real.sqrt ((complexAbsoluteValue z) ^ 2) :=
        (helperForLemma_4_6_6_sqrt_absSq_eq_absValue z).symm
      _ = Real.sqrt ((z * star z).re) := by
        rw [helperForLemma_4_6_6_mulConj_re_eq_absSq z]

/-- Lemma 4.6.7: for all `z, w ∈ ℂ`, the complex absolute value is
multiplicative: `|zw| = |z| |w|`. -/
lemma complexAbsoluteValue_mul (z w : ℂ) :
    complexAbsoluteValue (z * w) = complexAbsoluteValue z * complexAbsoluteValue w := by
  simpa [complexAbsoluteValue] using (norm_mul z w)

/-- Lemma 4.6.8: for every `z ∈ ℂ`, the complex absolute value is invariant
under complex conjugation: `|\overline{z}| = |z|`. -/
lemma complexAbsoluteValue_conj (z : ℂ) :
    complexAbsoluteValue (star z) = complexAbsoluteValue z := by
  simpa [complexAbsoluteValue] using (norm_star z)

/-- Proposition 4.6.3: if `z, w ∈ ℂ` and `w ≠ 0`, then
`|z / w| = |z| / |w|`. -/
theorem complexAbsoluteValue_div_of_ne_zero (z w : ℂ) :
    w ≠ 0 → complexAbsoluteValue (z / w) = complexAbsoluteValue z / complexAbsoluteValue w := by
  intro _
  simpa [complexAbsoluteValue] using (norm_div z w)

/-- Definition 4.6.9 (Complex reciprocal and quotient): for `z : ℂ`, the
reciprocal is undefined at `0` and is `|z|^{-2} \overline{z}` otherwise; for
`z w : ℂ`, the quotient `z / w` is defined when `w ≠ 0` by `z * w^{-1}`. -/
noncomputable def complexReciprocalQuotientPartialData :
    (ℂ → Option ℂ) × (ℂ → ℂ → Option ℂ) :=
  let reciprocal : ℂ → Option ℂ :=
    fun z =>
      if z = 0 then
        none
      else
        some (((((complexAbsoluteValue z) ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * star z)
  (reciprocal, fun z w => (reciprocal w).map (fun wInv => z * wInv))

/-- Partial complex reciprocal: undefined at `0`, and otherwise given by
`|z|^{-2} \overline{z}`. -/
noncomputable def complexReciprocalPartial (z : ℂ) : Option ℂ :=
  complexReciprocalQuotientPartialData.1 z

/-- Partial complex quotient: for `z w : ℂ`, this is defined by mapping
`w` to its partial reciprocal and multiplying by `z`. -/
noncomputable def complexQuotientPartial (z w : ℂ) : Option ℂ :=
  complexReciprocalQuotientPartialData.2 z w

/-- Definition 4.6.10 (Complex exponential): for each `z ∈ ℂ`, the complex
exponential is defined by the power series
`exp(z) = ∑' n : ℕ, z^n / n!`. -/
noncomputable def complexExponential (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / (Nat.factorial n : ℂ)

/-- Theorem 4.6.1: for all `z, w ∈ ℂ`, one has
`exp(z + w) = exp(z) exp(w)`. -/
theorem complex_exp_add (z w : ℂ) :
    Complex.exp (z + w) = Complex.exp z * Complex.exp w := by
  simpa using (Complex.exp_add z w)

/-- Proposition 4.6.1: for every `z ∈ ℂ`, the complex exponential commutes with
complex conjugation, i.e. `exp(conj z) = conj (exp z)`. -/
theorem complex_exp_conj (z : ℂ) :
    Complex.exp (star z) = star (Complex.exp z) := by
  simpa using (Complex.exp_conj z)

/-- Helper for Lemma 4.6.9: the absolute value of the real part is bounded by
the complex absolute value. -/
lemma helperForLemma_4_6_9_absRe_le_complexAbs (z : ℂ) :
    |z.re| ≤ complexAbsoluteValue z := by
  simpa [complexAbsoluteValue] using (Complex.abs_re_le_norm z)

/-- Helper for Lemma 4.6.9: the real part is bounded below by the negated
complex absolute value. -/
lemma helperForLemma_4_6_9_negComplexAbs_le_re (z : ℂ) :
    -complexAbsoluteValue z ≤ z.re := by
  exact (abs_le.mp (helperForLemma_4_6_9_absRe_le_complexAbs z)).1

/-- Helper for Lemma 4.6.9: the real part is bounded above by the complex
absolute value. -/
lemma helperForLemma_4_6_9_re_le_complexAbs (z : ℂ) :
    z.re ≤ complexAbsoluteValue z := by
  exact (abs_le.mp (helperForLemma_4_6_9_absRe_le_complexAbs z)).2

/-- Lemma 4.6.9: for every complex number `z`, its real part is bounded by its
complex absolute value: `-|z| ≤ Re(z) ≤ |z|`. -/
theorem realPart_le_complexAbsoluteValue (z : ℂ) :
    -complexAbsoluteValue z ≤ z.re ∧ z.re ≤ complexAbsoluteValue z := by
  constructor
  · exact helperForLemma_4_6_9_negComplexAbs_le_re z
  · exact helperForLemma_4_6_9_re_le_complexAbs z

/-- Helper for Lemma 4.6.10: the absolute value of the imaginary part is bounded
by the complex absolute value. -/
lemma helperForLemma_4_6_10_absIm_le_complexAbs (z : ℂ) :
    |z.im| ≤ complexAbsoluteValue z := by
  simpa [complexAbsoluteValue] using (Complex.abs_im_le_norm z)

/-- Helper for Lemma 4.6.10: the imaginary part is bounded below by the negated
complex absolute value. -/
lemma helperForLemma_4_6_10_negComplexAbs_le_im (z : ℂ) :
    -complexAbsoluteValue z ≤ z.im := by
  exact (abs_le.mp (helperForLemma_4_6_10_absIm_le_complexAbs z)).1

/-- Helper for Lemma 4.6.10: the imaginary part is bounded above by the complex
absolute value. -/
lemma helperForLemma_4_6_10_im_le_complexAbs (z : ℂ) :
    z.im ≤ complexAbsoluteValue z := by
  exact (abs_le.mp (helperForLemma_4_6_10_absIm_le_complexAbs z)).2

/-- Lemma 4.6.10: for every `z ∈ ℂ`, the imaginary part is bounded by the complex
absolute value: `-|z| ≤ Im(z) ≤ |z|`. -/
lemma imagPart_le_complexAbsoluteValue (z : ℂ) :
    -complexAbsoluteValue z ≤ z.im ∧ z.im ≤ complexAbsoluteValue z := by
  constructor
  · exact helperForLemma_4_6_10_negComplexAbs_le_im z
  · exact helperForLemma_4_6_10_im_le_complexAbs z

/-- Lemma 4.6.11: for every `z ∈ ℂ`, the complex absolute value is bounded by
the sum of the absolute values of its real and imaginary parts:
`|z| ≤ |Re(z)| + |Im(z)|`. -/
lemma complexAbsoluteValue_le_abs_re_add_abs_im (z : ℂ) :
    complexAbsoluteValue z ≤ |z.re| + |z.im| := by
  simpa [complexAbsoluteValue] using (Complex.norm_le_abs_re_add_abs_im z)

/-- Lemma 4.6.12: for all `z, w ∈ ℂ`, the complex absolute value satisfies the
triangle inequality `|z + w| ≤ |z| + |w|`. -/
lemma complexAbsoluteValue_add_le (z w : ℂ) :
    complexAbsoluteValue (z + w) ≤ complexAbsoluteValue z + complexAbsoluteValue w := by
  simpa [complexAbsoluteValue] using (norm_add_le z w)

/-- Helper for Proposition 4.6.4: equality in the triangle inequality for complex
norm is equivalent to the two numbers lying on the same real ray. -/
lemma helperForProposition_4_6_4_normEq_iff_sameRay (z w : ℂ) :
    complexAbsoluteValue (z + w) = complexAbsoluteValue z + complexAbsoluteValue w ↔
      SameRay ℝ z w := by
  simpa [complexAbsoluteValue] using (sameRay_iff_norm_add (x := z) (y := w)).symm

/-- Helper for Proposition 4.6.4: two nonzero complex numbers on the same real
ray differ by multiplication by a positive real scalar. -/
lemma helperForProposition_4_6_4_sameRay_to_existsPosMul (z w : ℂ)
    (hz : z ≠ 0) (hw : w ≠ 0) (hzw : SameRay ℝ z w) :
    ∃ c : ℝ, 0 < c ∧ z = (c : ℂ) * w := by
  rcases hzw.exists_pos_right hz hw with ⟨c, hc, hcw⟩
  refine ⟨c, hc, ?_⟩
  simpa [Algebra.smul_def] using hcw

/-- Helper for Proposition 4.6.4: if one complex number is a positive real
multiple of another, then equality holds in the triangle inequality. -/
lemma helperForProposition_4_6_4_existsPosMul_to_normEq (z w : ℂ) :
    (∃ c : ℝ, 0 < c ∧ z = (c : ℂ) * w) →
      complexAbsoluteValue (z + w) = complexAbsoluteValue z + complexAbsoluteValue w := by
  intro h
  rcases h with ⟨c, hc, hz⟩
  have hz' : z = c • w := by
    simpa [Algebra.smul_def] using hz
  have hRay : SameRay ℝ z w := by
    rw [hz']
    exact SameRay.sameRay_pos_smul_left w hc
  exact (helperForProposition_4_6_4_normEq_iff_sameRay z w).2 hRay

/-- Proposition 4.6.4: for nonzero complex numbers `z` and `w`,
`|z + w| = |z| + |w|` if and only if there exists a real number `c > 0`
such that `z = c w`. -/
theorem complexAbsoluteValue_add_eq_add_iff_exists_pos_real_mul (z w : ℂ)
    (hz : z ≠ 0) (hw : w ≠ 0) :
    complexAbsoluteValue (z + w) = complexAbsoluteValue z + complexAbsoluteValue w ↔
      ∃ c : ℝ, 0 < c ∧ z = (c : ℂ) * w := by
  constructor
  · intro hEq
    have hRay : SameRay ℝ z w :=
      (helperForProposition_4_6_4_normEq_iff_sameRay z w).1 hEq
    exact helperForProposition_4_6_4_sameRay_to_existsPosMul z w hz hw hRay
  · intro hMul
    exact helperForProposition_4_6_4_existsPosMul_to_normEq z w hMul

/-- Helper for Proposition 4.6.5: if `i` is positive and positivity is closed
under multiplication, then `-1` is positive. -/
lemma helperForProposition_4_6_5_posNegOne_from_posI
    (Pos : ℂ → Prop)
    (hMulPos : ∀ z w : ℂ, Pos z → Pos w → Pos (z * w))
    (hPosI : Pos Complex.I) :
    Pos (-(1 : ℂ)) := by
  have hPosISq : Pos (Complex.I * Complex.I) :=
    hMulPos Complex.I Complex.I hPosI hPosI
  simpa [Complex.I_sq] using hPosISq

/-- Helper for Proposition 4.6.5: if `i` is negative, negation sends negatives
to positives, and positivity is multiplicatively closed, then `-1` is positive. -/
lemma helperForProposition_4_6_5_posNegOne_from_negI
    (Pos Neg : ℂ → Prop)
    (hNegToPos : ∀ z : ℂ, Neg z → Pos (-z))
    (hMulPos : ∀ z w : ℂ, Pos z → Pos w → Pos (z * w))
    (hNegI : Neg Complex.I) :
    Pos (-(1 : ℂ)) := by
  have hPosNegI : Pos (-Complex.I) := hNegToPos Complex.I hNegI
  have hPosNegISq : Pos ((-Complex.I) * (-Complex.I)) :=
    hMulPos (-Complex.I) (-Complex.I) hPosNegI hPosNegI
  simpa [Complex.I_sq] using hPosNegISq

/-- Helper for Proposition 4.6.5: trichotomy at `i`, together with the
negation rule `Neg z → Pos (-z)` and multiplicative closure of positivity,
forces `-1` to be positive. -/
lemma helperForProposition_4_6_5_posNegOne
    (Pos Neg : ℂ → Prop)
    (hTrichotomy : ∀ z : ℂ, Pos z ∨ Neg z ∨ z = 0)
    (hNegToPos : ∀ z : ℂ, Neg z → Pos (-z))
    (hMulPos : ∀ z w : ℂ, Pos z → Pos w → Pos (z * w)) :
    Pos (-(1 : ℂ)) := by
  rcases hTrichotomy Complex.I with hPosI | hNegI | hIeqZero
  · exact helperForProposition_4_6_5_posNegOne_from_posI Pos hMulPos hPosI
  · exact helperForProposition_4_6_5_posNegOne_from_negI Pos Neg hNegToPos hMulPos hNegI
  · exact False.elim (Complex.I_ne_zero hIeqZero)

/-- Helper for Proposition 4.6.5: if `-1` is positive, positivity is closed
under multiplication, and positives negate to negatives, then exclusivity of
positive/negative classes yields a contradiction. -/
lemma helperForProposition_4_6_5_contradiction_from_posNegOne
    (Pos Neg : ℂ → Prop)
    (hPosNegExclusive : ∀ z : ℂ, ¬ (Pos z ∧ Neg z))
    (hPosToNeg : ∀ z : ℂ, Pos z → Neg (-z))
    (hMulPos : ∀ z w : ℂ, Pos z → Pos w → Pos (z * w))
    (hPosNegOne : Pos (-(1 : ℂ))) :
    False := by
  have hPosOneMul : Pos ((-(1 : ℂ)) * (-(1 : ℂ))) :=
    hMulPos (-(1 : ℂ)) (-(1 : ℂ)) hPosNegOne hPosNegOne
  have hPosOne : Pos (1 : ℂ) := by
    simpa using hPosOneMul
  have hNegNegOne : Neg (-(1 : ℂ)) := by
    simpa using hPosToNeg (1 : ℂ) hPosOne
  exact hPosNegExclusive (-(1 : ℂ)) ⟨hPosNegOne, hNegNegOne⟩

/-- Proposition 4.6.5: there does not exist a partition of `ℂ` into positive,
negative, and zero classes such that for every `z, w : ℂ`: (i) exactly one of
`Pos z`, `Neg z`, or `z = 0` holds, (ii) positivity/negativity are exchanged by
negation, (iii) positive numbers are closed under addition, and
(iv) positive numbers are closed under multiplication. -/
theorem no_complex_positive_negative_zero_partition :
    ¬ ∃ Pos Neg : ℂ → Prop,
      (∀ z : ℂ,
        (Pos z ∨ Neg z ∨ z = 0) ∧
          ¬ (Pos z ∧ Neg z) ∧ ¬ (Pos z ∧ z = 0) ∧ ¬ (Neg z ∧ z = 0)) ∧
      (∀ z : ℂ, Pos z → Neg (-z)) ∧
      (∀ z : ℂ, Neg z → Pos (-z)) ∧
      (∀ z w : ℂ, Pos z → Pos w → Pos (z + w)) ∧
      (∀ z w : ℂ, Pos z → Pos w → Pos (z * w)) := by
  intro hExists
  rcases hExists with ⟨Pos, Neg, hPartition, hPosToNeg, hNegToPos, hAddPos, hMulPos⟩
  have hTrichotomy : ∀ z : ℂ, Pos z ∨ Neg z ∨ z = 0 := by
    intro z
    exact (hPartition z).1
  have hPosNegExclusive : ∀ z : ℂ, ¬ (Pos z ∧ Neg z) := by
    intro z
    exact (hPartition z).2.1
  have hPosNegOne : Pos (-(1 : ℂ)) :=
    helperForProposition_4_6_5_posNegOne Pos Neg hTrichotomy hNegToPos hMulPos
  exact helperForProposition_4_6_5_contradiction_from_posNegOne
    Pos Neg hPosNegExclusive hPosToNeg hMulPos hPosNegOne

/-- Lemma 4.6.13: with `d(z,w) = |z - w|` on `ℂ`, this gives the usual metric on
`ℂ`; moreover, a sequence `z_n` converges to `z` in this metric iff both real
and imaginary parts converge, i.e. `Re(z_n) → Re(z)` and `Im(z_n) → Im(z)`. -/
lemma complex_tendsto_iff_re_im_tendsto (zSeq : ℕ → ℂ) (z : ℂ) :
    let d : ℂ → ℂ → ℝ := fun z₁ z₂ => ‖z₁ - z₂‖;
      ((∀ z₁ z₂ : ℂ, 0 ≤ d z₁ z₂) ∧
        (∀ z₁ z₂ : ℂ, d z₁ z₂ = 0 ↔ z₁ = z₂) ∧
        (∀ z₁ z₂ : ℂ, d z₁ z₂ = d z₂ z₁) ∧
        (∀ z₁ z₂ z₃ : ℂ, d z₁ z₃ ≤ d z₁ z₂ + d z₂ z₃)) ∧
        ((∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, d (zSeq n) z < ε) ↔
          Filter.Tendsto (fun n => (zSeq n).re) Filter.atTop (nhds z.re) ∧
            Filter.Tendsto (fun n => (zSeq n).im) Filter.atTop (nhds z.im)) := by
  dsimp
  constructor
  · constructor
    · intro z₁ z₂
      exact norm_nonneg (z₁ - z₂)
    · constructor
      · intro z₁ z₂
        constructor
        · intro h
          exact sub_eq_zero.mp (norm_eq_zero.mp h)
        · intro h
          simp [h]
      · constructor
        · intro z₁ z₂
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (norm_sub_rev z₁ z₂)
        · intro z₁ z₂ z₃
          simpa [dist_eq_norm] using (dist_triangle z₁ z₂ z₃)
  · constructor
    · intro h
      have hz : Filter.Tendsto zSeq Filter.atTop (nhds z) :=
        Metric.tendsto_atTop.2 (by simpa [dist_eq_norm] using h)
      constructor
      · exact (Complex.continuous_re.tendsto z).comp hz
      · exact (Complex.continuous_im.tendsto z).comp hz
    · intro h
      rcases h with ⟨hre, him⟩
      have hpair : Filter.Tendsto (fun n => ((zSeq n).re, (zSeq n).im))
          Filter.atTop (nhds (z.re, z.im)) := by
        simpa [nhds_prod_eq] using hre.prodMk him
      have hsymm : Filter.Tendsto (fun p : ℝ × ℝ => Complex.equivRealProdCLM.symm p)
          (nhds (z.re, z.im)) (nhds (Complex.equivRealProdCLM.symm (z.re, z.im))) :=
        (Complex.equivRealProdCLM.symm.continuous.tendsto (z.re, z.im))
      have hz : Filter.Tendsto (fun n => Complex.equivRealProdCLM.symm ((zSeq n).re, (zSeq n).im))
          Filter.atTop (nhds (Complex.equivRealProdCLM.symm (z.re, z.im))) :=
        hsymm.comp hpair
      have hz' : Filter.Tendsto zSeq Filter.atTop (nhds z) := by
        simpa [Complex.equivRealProdCLM_symm_apply, Complex.re_add_im] using hz
      simpa [dist_eq_norm] using Metric.tendsto_atTop.1 hz'

/-- Helper for Lemma 4.6.14: bundled arithmetic limit laws in `ℂ`
for sum, difference, scalar multiplication, and product. -/
lemma helperForLemma_4_6_14_arith_tendsto_bundle (zSeq wSeq : ℕ → ℂ) (z w c : ℂ)
    (hz : Filter.Tendsto zSeq Filter.atTop (nhds z))
    (hw : Filter.Tendsto wSeq Filter.atTop (nhds w)) :
    Filter.Tendsto (fun n => zSeq n + wSeq n) Filter.atTop (nhds (z + w)) ∧
    Filter.Tendsto (fun n => zSeq n - wSeq n) Filter.atTop (nhds (z - w)) ∧
    Filter.Tendsto (fun n => c * zSeq n) Filter.atTop (nhds (c * z)) ∧
    Filter.Tendsto (fun n => zSeq n * wSeq n) Filter.atTop (nhds (z * w)) := by
  constructor
  · exact hz.add hw
  constructor
  · exact hz.sub hw
  constructor
  · exact hz.const_mul c
  · exact hz.mul hw

/-- Helper for Lemma 4.6.14: conjugation preserves sequence limits in `ℂ`. -/
lemma helperForLemma_4_6_14_star_tendsto (zSeq : ℕ → ℂ) (z : ℂ)
    (hz : Filter.Tendsto zSeq Filter.atTop (nhds z)) :
    Filter.Tendsto (fun n => star (zSeq n)) Filter.atTop (nhds (star z)) := by
  simpa using hz.star

/-- Helper for Lemma 4.6.14: quotient limit law in `ℂ` under nonzero limit. -/
lemma helperForLemma_4_6_14_div_tendsto (zSeq wSeq : ℕ → ℂ) (z w : ℂ)
    (hz : Filter.Tendsto zSeq Filter.atTop (nhds z))
    (hw : Filter.Tendsto wSeq Filter.atTop (nhds w)) :
    (∀ n : ℕ, wSeq n ≠ 0) → w ≠ 0 →
      Filter.Tendsto (fun n => zSeq n / wSeq n) Filter.atTop (nhds (z / w)) := by
  intro _ hw0
  exact hz.div hw hw0

/-- Lemma 4.6.14 (Complex limit laws): if `zₙ → z` and `wₙ → w` in `ℂ`, then
`zₙ + wₙ → z + w`, `zₙ - wₙ → z - w`, `c zₙ → c z`, `zₙ wₙ → z w`, and
`conj zₙ → conj z`; moreover, if `wₙ ≠ 0` for all `n` and `w ≠ 0`, then
`zₙ / wₙ → z / w`. -/
lemma complex_limit_laws (zSeq wSeq : ℕ → ℂ) (z w c : ℂ)
    (hz : Filter.Tendsto zSeq Filter.atTop (nhds z))
    (hw : Filter.Tendsto wSeq Filter.atTop (nhds w)) :
    Filter.Tendsto (fun n => zSeq n + wSeq n) Filter.atTop (nhds (z + w)) ∧
    Filter.Tendsto (fun n => zSeq n - wSeq n) Filter.atTop (nhds (z - w)) ∧
    Filter.Tendsto (fun n => c * zSeq n) Filter.atTop (nhds (c * z)) ∧
    Filter.Tendsto (fun n => zSeq n * wSeq n) Filter.atTop (nhds (z * w)) ∧
    Filter.Tendsto (fun n => star (zSeq n)) Filter.atTop (nhds (star z)) ∧
    ((∀ n : ℕ, wSeq n ≠ 0) → w ≠ 0 →
      Filter.Tendsto (fun n => zSeq n / wSeq n) Filter.atTop (nhds (z / w))) := by
  rcases helperForLemma_4_6_14_arith_tendsto_bundle zSeq wSeq z w c hz hw with
    ⟨hAdd, hSub, hConstMul, hMul⟩
  constructor
  · exact hAdd
  constructor
  · exact hSub
  constructor
  · exact hConstMul
  constructor
  · exact hMul
  constructor
  · exact helperForLemma_4_6_14_star_tendsto zSeq z hz
  · exact helperForLemma_4_6_14_div_tendsto zSeq wSeq z w hz hw

end Section06
end Chap04
