/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.PNat.Equiv
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Equiv
open scoped InnerProductSpace

universe u

noncomputable section

/-- Lebesgue measure restricted to the unit interval `[0,1]`. -/
def unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The real Hilbert space `L²([0,1], λ)`. -/
abbrev L2UnitInterval :=
  ℝ →₂[unitIntervalMeasure] ℝ

/-- The source-facing coefficient space for real Fourier series on `[0,1]`: sine coefficients are
indexed by positive frequencies `n : ℕ+`, while cosine coefficients are indexed by `ℕ` and use
`b 0` for the normalized constant mode. -/
abbrev FourierCoefficients :=
  ℓ²(ℕ+, ℝ) × ℓ²(ℕ, ℝ)

/-- The sine function `Sₙ(x) = √2 sin (2π n x)` on the unit interval. -/
def fourierSineFun (n : ℕ) : ℝ → ℝ :=
  fun x ↦ Real.sqrt 2 * Real.sin (2 * Real.pi * n * x)

/-- The cosine function `Cₙ(x) = √2 cos (2π n x)` on the unit interval. -/
def fourierCosineFun (n : ℕ) : ℝ → ℝ :=
  fun x ↦ Real.sqrt 2 * Real.cos (2 * Real.pi * n * x)

/-- The normalized constant Fourier mode on `[0,1]`. -/
def fourierConstantFun : ℝ → ℝ :=
  fun _ ↦ 1

-- Proof sketch: the trigonometric function `fourierSineFun n` is continuous, hence strongly
-- measurable, and it is bounded on the compact interval `[0,1]`; finite measure then gives `L²`
-- integrability on `unitIntervalMeasure`.
/-- Companion: each sine Fourier mode belongs to `L²([0,1], λ)`. -/
theorem fourierSineFun_memLp (n : ℕ) :
    MemLp (fourierSineFun n) 2 unitIntervalMeasure := by
  -- The sine mode is continuous, hence strongly measurable on the interval measure.
  haveI : IsFiniteMeasure unitIntervalMeasure := by
    dsimp [unitIntervalMeasure]
    infer_instance
  have hcont : Continuous (fourierSineFun n) := by
    change Continuous (fun x : ℝ ↦ Real.sqrt 2 * Real.sin (2 * Real.pi * n * x))
    refine continuous_const.mul ?_
    refine Real.continuous_sin.comp ?_
    change Continuous (fun x : ℝ ↦ (2 * Real.pi * (n : ℝ)) * x)
    exact continuous_const.mul continuous_id
  -- Uniform boundedness by `√2` puts the function in every `Lᵖ` space over this finite measure.
  refine memLp_of_bounded
    (show ∀ᵐ x ∂unitIntervalMeasure,
        fourierSineFun n x ∈ Set.Icc (-Real.sqrt 2) (Real.sqrt 2) from ?_)
    hcont.aestronglyMeasurable 2
  filter_upwards [] with x
  have hsine := Real.sin_mem_Icc (2 * Real.pi * n * x)
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hleft : -Real.sqrt 2 ≤ Real.sqrt 2 * Real.sin (2 * Real.pi * n * x) := by
    nlinarith [hsine.1, hsqrt]
  have hright : Real.sqrt 2 * Real.sin (2 * Real.pi * n * x) ≤ Real.sqrt 2 := by
    nlinarith [hsine.2, hsqrt]
  exact ⟨by simpa [fourierSineFun] using hleft, by simpa [fourierSineFun] using hright⟩

-- Proof sketch: the trigonometric function `fourierCosineFun n` is continuous and bounded on the
-- compact interval `[0,1]`, so it is square-integrable for the restricted Lebesgue measure.
/-- Companion: each cosine Fourier mode belongs to `L²([0,1], λ)`. -/
theorem fourierCosineFun_memLp (n : ℕ) :
    MemLp (fourierCosineFun n) 2 unitIntervalMeasure := by
  -- The cosine mode is continuous, hence strongly measurable on the interval measure.
  haveI : IsFiniteMeasure unitIntervalMeasure := by
    dsimp [unitIntervalMeasure]
    infer_instance
  have hcont : Continuous (fourierCosineFun n) := by
    change Continuous (fun x : ℝ ↦ Real.sqrt 2 * Real.cos (2 * Real.pi * n * x))
    refine continuous_const.mul ?_
    refine Real.continuous_cos.comp ?_
    change Continuous (fun x : ℝ ↦ (2 * Real.pi * (n : ℝ)) * x)
    exact continuous_const.mul continuous_id
  -- Uniform boundedness by `√2` gives square integrability on `[0,1]`.
  refine memLp_of_bounded
    (show ∀ᵐ x ∂unitIntervalMeasure,
        fourierCosineFun n x ∈ Set.Icc (-Real.sqrt 2) (Real.sqrt 2) from ?_)
    hcont.aestronglyMeasurable 2
  filter_upwards [] with x
  have hcos := Real.cos_mem_Icc (2 * Real.pi * n * x)
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hleft : -Real.sqrt 2 ≤ Real.sqrt 2 * Real.cos (2 * Real.pi * n * x) := by
    nlinarith [hcos.1, hsqrt]
  have hright : Real.sqrt 2 * Real.cos (2 * Real.pi * n * x) ≤ Real.sqrt 2 := by
    nlinarith [hcos.2, hsqrt]
  exact ⟨by simpa [fourierCosineFun] using hleft, by simpa [fourierCosineFun] using hright⟩

-- Proof sketch: the constant function `1` is measurable and bounded on a finite-measure space,
-- so its square is integrable on `[0,1]`.
/-- Companion: the constant Fourier mode belongs to `L²([0,1], λ)`. -/
theorem fourierConstantFun_memLp :
    MemLp fourierConstantFun 2 unitIntervalMeasure := by
  haveI : IsFiniteMeasure unitIntervalMeasure := by
    dsimp [unitIntervalMeasure]
    infer_instance
  -- The constant mode is bounded by the single value `1`.
  refine memLp_of_bounded
    (show ∀ᵐ x ∂unitIntervalMeasure, fourierConstantFun x ∈ Set.Icc (1 : ℝ) 1 from ?_)
    continuous_const.aestronglyMeasurable 2
  filter_upwards [] with x
  exact ⟨le_rfl, le_rfl⟩

/-- The `L²` class of the sine mode `Sₙ`. -/
def fourierSine (n : ℕ) : L2UnitInterval :=
  (fourierSineFun_memLp n).toLp (fourierSineFun n)

/-- The `L²` class of the cosine mode `Cₙ`. -/
def fourierCosine (n : ℕ) : L2UnitInterval :=
  (fourierCosineFun_memLp n).toLp (fourierCosineFun n)

/-- The normalized constant mode in `L²([0,1], λ)`. -/
def fourierConstant : L2UnitInterval :=
  fourierConstantFun_memLp.toLp fourierConstantFun

/-- Companion: the textbook constant mode satisfies `C₀ = √2 · 1`. -/
theorem fourierCosine_zero_eq_smul_fourierConstant :
    fourierCosine 0 = Real.sqrt 2 • fourierConstant := by
  -- Both `L²` classes come from the same pointwise function on `[0,1]`.
  rw [fourierCosine, fourierConstant, ← fourierConstantFun_memLp.toLp_const_smul (Real.sqrt 2)]
  refine (MemLp.toLp_eq_toLp_iff (fourierCosineFun_memLp 0)
    (fourierConstantFun_memLp.const_smul (Real.sqrt 2))).2 ?_
  filter_upwards [] with x
  simp [fourierCosineFun, fourierConstantFun]

/-- Indices for the trigonometric family `C₀, Sₙ, Cₙ` with `n ≥ 1`. -/
inductive FourierTrigonometricIndex
  | constant
  | sine (n : ℕ)
  | cosine (n : ℕ)
deriving DecidableEq

/-- The textbook trigonometric family `C₀, Sₙ, Cₙ` in `L²([0,1], λ)`, indexed so that `sine n`
and `cosine n` correspond to the positive frequencies `n + 1`. -/
def fourierTrigonometricSystem : FourierTrigonometricIndex → L2UnitInterval
  | .constant => fourierCosine 0
  | .sine n => fourierSine (n + 1)
  | .cosine n => fourierCosine (n + 1)

/-- The normalized orthonormal trigonometric system `1, Sₙ, Cₙ` in `L²([0,1], λ)`, indexed so
that `sine n` and `cosine n` correspond to the positive frequencies `n + 1`. -/
def normalizedFourierTrigonometricSystem : FourierTrigonometricIndex → L2UnitInterval
  | .constant => fourierConstant
  | .sine n => fourierSine (n + 1)
  | .cosine n => fourierCosine (n + 1)

/-- The positive-frequency Fourier summand determined by sine coefficients `a` and cosine
coefficients `b`, where `b 0` is reserved for the constant term. -/
def fourierSeriesSummand (coeffs : FourierCoefficients) (n : ℕ+) : L2UnitInterval :=
  coeffs.1 n • fourierSine n + coeffs.2 n • fourierCosine n

/-- The real Fourier series on `[0,1]` attached to the coefficient vector
`coeffs = (a, b) : ℓ²(ℕ+, ℝ) × ℓ²(ℕ, ℝ)`, where `a n` is the coefficient of `Sₙ` for the
positive frequency `n : ℕ+`, and `b 0` is the coefficient of the normalized constant mode `1`
(equivalently, `(b 0 / Real.sqrt 2)` is the coefficient of `C₀`). -/
def fourierSeries (coeffs : FourierCoefficients) : L2UnitInterval :=
  coeffs.2 0 • fourierConstant + ∑' n : ℕ+, fourierSeriesSummand coeffs n

/-- Helper: the positive-frequency Fourier summand is additive in the
coefficient vector. -/
lemma fourierSeriesSummand_add (coeffs₁ coeffs₂ : FourierCoefficients) (n : ℕ+) :
    fourierSeriesSummand (coeffs₁ + coeffs₂) n =
      fourierSeriesSummand coeffs₁ n + fourierSeriesSummand coeffs₂ n := by
  -- Expanding the definition leaves only distributivity of scalar multiplication over addition.
  change
    ((coeffs₁.1 n + coeffs₂.1 n) • fourierSine n + (coeffs₁.2 n + coeffs₂.2 n) • fourierCosine n) =
      (coeffs₁.1 n • fourierSine n + coeffs₁.2 n • fourierCosine n) +
        (coeffs₂.1 n • fourierSine n + coeffs₂.2 n • fourierCosine n)
  rw [add_smul, add_smul]
  abel_nf

/-- Helper: the positive-frequency Fourier summand is homogeneous in the
coefficient vector. -/
lemma fourierSeriesSummand_smul (c : ℝ) (coeffs : FourierCoefficients) (n : ℕ+) :
    fourierSeriesSummand (c • coeffs) n = c • fourierSeriesSummand coeffs n := by
  -- Expanding the definition leaves only associativity of scalar multiplication.
  simp [fourierSeriesSummand, smul_add, smul_smul]

/-- Helper: the trigonometric index type is the disjoint union of the constant
mode, the sine modes, and the cosine modes. -/
theorem fourierIndexEquiv_left_inv :
    Function.LeftInverse
      (fun x : Unit ⊕ (ℕ ⊕ ℕ) ↦
        match x with
        | Sum.inl _ => FourierTrigonometricIndex.constant
        | Sum.inr (Sum.inl n) => FourierTrigonometricIndex.sine n
        | Sum.inr (Sum.inr n) => FourierTrigonometricIndex.cosine n)
      (fun i : FourierTrigonometricIndex ↦
        match i with
        | .constant => Sum.inl ()
        | .sine n => Sum.inr (Sum.inl n)
        | .cosine n => Sum.inr (Sum.inr n)) := by
  -- The inverse map is defined by cases on the three constructors.
  intro i
  cases i <;> rfl

/-- Helper: the disjoint-union coding of `FourierTrigonometricIndex` is
right-inverse to the constructor map. -/
theorem fourierIndexEquiv_right_inv :
    Function.RightInverse
      (fun x : Unit ⊕ (ℕ ⊕ ℕ) ↦
        match x with
        | Sum.inl _ => FourierTrigonometricIndex.constant
        | Sum.inr (Sum.inl n) => FourierTrigonometricIndex.sine n
        | Sum.inr (Sum.inr n) => FourierTrigonometricIndex.cosine n)
      (fun i : FourierTrigonometricIndex ↦
        match i with
        | .constant => Sum.inl ()
        | .sine n => Sum.inr (Sum.inl n)
        | .cosine n => Sum.inr (Sum.inr n)) := by
  -- The coding map is likewise definitionally compatible with the three constructors.
  intro i
  cases i with
  | inl u =>
      cases u
      rfl
  | inr v =>
      cases v <;> rfl

/-- Helper: an explicit equivalence between the trigonometric indices and a
three-way disjoint union. -/
def fourierIndexEquiv : FourierTrigonometricIndex ≃ Unit ⊕ (ℕ ⊕ ℕ) where
  toFun i :=
    match i with
    | .constant => Sum.inl ()
    | .sine n => Sum.inr (Sum.inl n)
    | .cosine n => Sum.inr (Sum.inr n)
  invFun x :=
    match x with
    | Sum.inl _ => FourierTrigonometricIndex.constant
    | Sum.inr (Sum.inl n) => FourierTrigonometricIndex.sine n
    | Sum.inr (Sum.inr n) => FourierTrigonometricIndex.cosine n
  left_inv := fourierIndexEquiv_left_inv
  right_inv := fourierIndexEquiv_right_inv

/-- Helper: restrict the cosine coefficients to positive frequencies. -/
theorem positiveCosineCoefficients_memℓp (coeffs : FourierCoefficients) :
    Memℓp (fun n : ℕ+ ↦ coeffs.2 n) 2 := by
  -- Positive cosine coefficients form a subseries of the square-summable cosine sequence.
  have hcos :
      Summable (fun n : ℕ ↦ ‖coeffs.2 n‖ ^ (2 : ℝ)) := by
    exact (lp.memℓp coeffs.2).summable (by norm_num)
  have hpos :
      Summable (fun n : ℕ+ ↦ ‖coeffs.2 n‖ ^ (2 : ℝ)) := by
    simpa [Function.comp] using hcos.comp_injective (fun m n h ↦ PNat.coe_injective h)
  exact memℓp_gen hpos

/-- Helper: the positive cosine coefficients as an `ℓ²` sequence on `ℕ+`. -/
def positiveCosineCoefficients (coeffs : FourierCoefficients) : ℓ²(ℕ+, ℝ) :=
  ⟨fun n ↦ coeffs.2 n, positiveCosineCoefficients_memℓp coeffs⟩

/-- Helper: integrating against `unitIntervalMeasure` is the same as interval
integration on `0..1`. -/
lemma integral_unitIntervalMeasure_eq_intervalIntegral {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (g : ℝ → E) :
    ∫ x, g x ∂unitIntervalMeasure = ∫ x in 0..1, g x := by
  -- Replace the `Icc` restriction by the a.e.-equal `Ioc` restriction used by interval integrals.
  have hrestrict : volume.restrict (Set.Ioc (0 : ℝ) 1) = volume.restrict (Set.Icc (0 : ℝ) 1) :=
    restrict_Ioc_eq_restrict_Icc
  rw [unitIntervalMeasure, ← hrestrict, intervalIntegral.integral_of_le zero_le_one]

/-- Helper: the real scalar inner product is ordinary multiplication. -/
lemma realScalarInner_eq_mul (x y : ℝ) : ⟪x, y⟫_ℝ = x * y := by
  -- This isolates the scalar-valued inner-product normal form used in the interval formulas.
  simpa using (RCLike.inner_apply' x y)

/-- Helper: pairing an explicit `L²` representative with an arbitrary
`L²([0,1], λ)` function is computed by an interval integral on `0..1`. -/
lemma inner_toLp_eq_intervalIntegral {g : ℝ → ℝ} (hg : MemLp g 2 unitIntervalMeasure)
    (f : L2UnitInterval) :
    ⟪hg.toLp g, f⟫_ℝ = ∫ x in 0..1, g x * f x := by
  -- Rewrite the `L²` inner product as an integral and then discard the quotient representative.
  rw [MeasureTheory.L2.inner_def]
  have htoLp : (fun x ↦ ⟪hg.toLp g x, f x⟫_ℝ) =ᵐ[unitIntervalMeasure] fun x ↦ g x * f x := by
    filter_upwards [hg.coeFn_toLp] with x hx
    simpa [hx, realScalarInner_eq_mul]
  rw [integral_congr_ae htoLp, integral_unitIntervalMeasure_eq_intervalIntegral]

/-- Helper: the inner product of two explicit `L²` representatives is computed
by the corresponding interval integral on `0..1`. -/
lemma inner_toLp_toLp_eq_intervalIntegral {f g : ℝ → ℝ}
    (hf : MemLp f 2 unitIntervalMeasure) (hg : MemLp g 2 unitIntervalMeasure) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x in 0..1, f x * g x := by
  -- Both `L²` classes can be replaced by their pointwise representatives inside the integral.
  rw [MeasureTheory.L2.inner_def]
  have htoLp :
      (fun x ↦ ⟪hf.toLp f x, hg.toLp g x⟫_ℝ) =ᵐ[unitIntervalMeasure] fun x ↦ f x * g x := by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    simpa [hfx, hgx, realScalarInner_eq_mul]
  rw [integral_congr_ae htoLp, integral_unitIntervalMeasure_eq_intervalIntegral]

/-- Helper: every nonzero integer Fourier sine mode has zero integral on
`[0,1]`. -/
lemma integral_sin_two_pi_int_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ x in 0..1, Real.sin (2 * Real.pi * k * x) = 0 := by
  have hc : (2 * Real.pi * (k : ℝ)) ≠ 0 := by
    refine mul_ne_zero ?_ (Int.cast_ne_zero.mpr hk)
    positivity
  -- Rescale the interval once so the endpoint values reduce to integer multiples of `2π`.
  have hmul :
      (2 * Real.pi * (k : ℝ)) * ∫ x in 0..1, Real.sin (x * (2 * Real.pi * (k : ℝ))) =
        ∫ x in 0..2 * Real.pi * (k : ℝ), Real.sin x := by
    simpa using
      (show
        (2 * Real.pi * (k : ℝ)) * ∫ x in (0 : ℝ)..1, Real.sin (x * (2 * Real.pi * (k : ℝ))) =
          ∫ x in (0 : ℝ)..2 * Real.pi * (k : ℝ), Real.sin x from
        mul_integral_comp_mul_right (fun x : ℝ ↦ Real.sin x))
  have hzero :
      (2 * Real.pi * (k : ℝ)) * ∫ x in 0..1, Real.sin (x * (2 * Real.pi * (k : ℝ))) = 0 := by
    rw [hmul, integral_sin]
    have hcos : Real.cos (2 * Real.pi * (k : ℝ)) = 1 := by
      convert Real.cos_int_mul_two_pi k using 1
      ring
    simp [Real.cos_zero, hcos]
  have hrew :
      ∫ x in 0..1, Real.sin (2 * Real.pi * k * x) =
        ∫ x in 0..1, Real.sin (x * (2 * Real.pi * (k : ℝ))) := by
    refine intervalIntegral.integral_congr_ae <| Filter.Eventually.of_forall ?_
    intro x hx
    congr 1
    ring
  rw [hrew]
  exact (mul_eq_zero.mp hzero).resolve_left hc

/-- Helper: every nonzero integer Fourier cosine mode has zero integral on
`[0,1]`. -/
lemma integral_cos_two_pi_int_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ x in 0..1, Real.cos (2 * Real.pi * k * x) = 0 := by
  have hc : (2 * Real.pi * (k : ℝ)) ≠ 0 := by
    refine mul_ne_zero ?_ (Int.cast_ne_zero.mpr hk)
    positivity
  -- Rescale the interval once so the endpoint values reduce to integer multiples of `2π`.
  have hmul :
      (2 * Real.pi * (k : ℝ)) * ∫ x in 0..1, Real.cos (x * (2 * Real.pi * (k : ℝ))) =
        ∫ x in 0..2 * Real.pi * (k : ℝ), Real.cos x := by
    simpa using
      (show
        (2 * Real.pi * (k : ℝ)) * ∫ x in (0 : ℝ)..1, Real.cos (x * (2 * Real.pi * (k : ℝ))) =
          ∫ x in (0 : ℝ)..2 * Real.pi * (k : ℝ), Real.cos x from
        mul_integral_comp_mul_right (fun x : ℝ ↦ Real.cos x))
  have hzero :
      (2 * Real.pi * (k : ℝ)) * ∫ x in 0..1, Real.cos (x * (2 * Real.pi * (k : ℝ))) = 0 := by
    rw [hmul, integral_cos]
    have hsin : Real.sin (2 * Real.pi * (k : ℝ)) = 0 := by
      simpa [two_mul, mul_assoc, mul_left_comm, mul_comm] using Real.sin_int_mul_pi (2 * k)
    simp [Real.sin_zero, hsin]
  have hrew :
      ∫ x in 0..1, Real.cos (2 * Real.pi * k * x) =
        ∫ x in 0..1, Real.cos (x * (2 * Real.pi * (k : ℝ))) := by
    refine intervalIntegral.integral_congr_ae <| Filter.Eventually.of_forall ?_
    intro x hx
    congr 1
    ring
  rw [hrew]
  exact (mul_eq_zero.mp hzero).resolve_left hc

/-- Helper: the constant mode has unit norm in `L²([0,1], λ)`. -/
lemma fourierConstant_inner_fourierConstant :
    ⟪fourierConstant, fourierConstant⟫_ℝ = 1 := by
  -- The constant mode is represented by the constant function `1` on `[0,1]`.
  rw [fourierConstant,
    inner_toLp_toLp_eq_intervalIntegral fourierConstantFun_memLp fourierConstantFun_memLp]
  simp [fourierConstantFun]

/-- Helper: the constant mode is orthogonal to every positive sine mode. -/
lemma fourierConstant_inner_fourierSine (n : ℕ) (hn : n ≠ 0) :
    ⟪fourierConstant, fourierSine n⟫_ℝ = 0 := by
  -- Rewrite the inner product as an interval integral and use the zero-average identity.
  rw [fourierConstant, fourierSine,
    inner_toLp_toLp_eq_intervalIntegral fourierConstantFun_memLp (fourierSineFun_memLp n)]
  simp [fourierConstantFun, fourierSineFun, intervalIntegral.integral_const_mul]
  exact integral_sin_two_pi_int_eq_zero (by exact_mod_cast hn)

/-- Helper: the constant mode is orthogonal to every positive cosine mode. -/
lemma fourierConstant_inner_fourierCosine (n : ℕ) (hn : n ≠ 0) :
    ⟪fourierConstant, fourierCosine n⟫_ℝ = 0 := by
  -- The nonconstant cosine modes also integrate to zero on `[0,1]`.
  rw [fourierConstant, fourierCosine,
    inner_toLp_toLp_eq_intervalIntegral fourierConstantFun_memLp (fourierCosineFun_memLp n)]
  simp [fourierConstantFun, fourierCosineFun, intervalIntegral.integral_const_mul]
  exact integral_cos_two_pi_int_eq_zero (by exact_mod_cast hn)

/-- Helper: positive sine modes have Kronecker-delta inner products. -/
lemma fourierSine_inner_fourierSine (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ⟪fourierSine m, fourierSine n⟫_ℝ = if m = n then 1 else 0 := by
  -- Rewrite the `L²` inner product as an interval integral of the pointwise sine product.
  rw [fourierSine, fourierSine,
    inner_toLp_toLp_eq_intervalIntegral (fourierSineFun_memLp m) (fourierSineFun_memLp n)]
  by_cases hmn : m = n
  · -- On the diagonal, the product-to-sum identity reduces the integrand to `1 - cos`.
    subst m
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hsumNat : 0 < n + n := add_pos hn' hn'
    have hsum : (((n + n : ℕ) : ℤ)) ≠ 0 := by
      exact_mod_cast hsumNat.ne'
    have hrewrite :
        ∫ x in 0..1, fourierSineFun n x * fourierSineFun n x =
          ∫ x in 0..1, (1 - Real.cos (2 * Real.pi * (n + n) * x)) := by
      refine intervalIntegral.integral_congr_ae <| Filter.Eventually.of_forall ?_
      intro x hx
      have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
      calc
        fourierSineFun n x * fourierSineFun n x
            = (Real.sqrt 2 * Real.sqrt 2) *
                (Real.sin (2 * Real.pi * n * x) * Real.sin (2 * Real.pi * n * x)) := by
                dsimp [fourierSineFun]
                ring
        _ = 2 * Real.sin (2 * Real.pi * n * x) * Real.sin (2 * Real.pi * n * x) := by
              rw [hsqrt]
              ring
        _ = Real.cos ((2 * Real.pi * n * x) - (2 * Real.pi * n * x)) -
              Real.cos ((2 * Real.pi * n * x) + (2 * Real.pi * n * x)) := by
                simpa using Real.two_mul_sin_mul_sin (2 * Real.pi * n * x) (2 * Real.pi * n * x)
        _ = 1 - Real.cos (2 * Real.pi * (n + n) * x) := by
              simp
              ring
    have hcosInt :
        IntervalIntegrable (fun x : ℝ ↦ Real.cos (2 * Real.pi * (n + n) * x)) volume 0 1 := by
      refine (Real.continuous_cos.comp ?_).intervalIntegrable 0 1
      exact continuous_const.mul continuous_id
    have hcosZero :
        ∫ x in 0..1, Real.cos (2 * Real.pi * (n + n) * x) = 0 := by
      simpa [Nat.cast_add] using integral_cos_two_pi_int_eq_zero hsum
    rw [hrewrite, intervalIntegral.integral_sub]
    · rw [hcosZero]
      norm_num
    · exact intervalIntegrable_const
    · exact hcosInt
  · -- Off the diagonal, the product-to-sum identity yields two nonzero cosine frequencies.
    have hsub : ((m : ℤ) - n) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hmn
    have hsum : ((m : ℤ) + n) ≠ 0 := by
      have hmz : (0 : ℤ) < m := by
        exact_mod_cast Nat.pos_of_ne_zero hm
      have hnz : (0 : ℤ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      linarith
    have hrewrite :
        ∫ x in 0..1, fourierSineFun m x * fourierSineFun n x =
          ∫ x in 0..1,
            (Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x) -
              Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x)) := by
      refine intervalIntegral.integral_congr_ae <| Filter.Eventually.of_forall ?_
      intro x hx
      have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
      calc
        fourierSineFun m x * fourierSineFun n x
            = (Real.sqrt 2 * Real.sqrt 2) *
                (Real.sin (2 * Real.pi * m * x) * Real.sin (2 * Real.pi * n * x)) := by
                dsimp [fourierSineFun]
                ring
        _ = 2 * Real.sin (2 * Real.pi * m * x) * Real.sin (2 * Real.pi * n * x) := by
              rw [hsqrt]
              ring
        _ = Real.cos ((2 * Real.pi * m * x) - (2 * Real.pi * n * x)) -
              Real.cos ((2 * Real.pi * m * x) + (2 * Real.pi * n * x)) := by
                simpa using Real.two_mul_sin_mul_sin (2 * Real.pi * m * x) (2 * Real.pi * n * x)
        _ = Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x) -
              Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x) := by
              congr 2
              · simp [Int.cast_sub, sub_eq_add_neg]
                ring
              · simp [Int.cast_add]
                ring
    have hcosSub :
        IntervalIntegrable
          (fun x : ℝ ↦ Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x)) volume 0 1 := by
      refine (Real.continuous_cos.comp ?_).intervalIntegrable 0 1
      exact continuous_const.mul continuous_id
    have hcosSum :
        IntervalIntegrable
          (fun x : ℝ ↦ Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x)) volume 0 1 := by
      refine (Real.continuous_cos.comp ?_).intervalIntegrable 0 1
      exact continuous_const.mul continuous_id
    have hcosSubZero :
        ∫ x in 0..1, Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x) = 0 := by
      exact integral_cos_two_pi_int_eq_zero hsub
    have hcosSumZero :
        ∫ x in 0..1, Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x) = 0 := by
      exact integral_cos_two_pi_int_eq_zero hsum
    rw [hrewrite, intervalIntegral.integral_sub]
    · rw [hcosSubZero, hcosSumZero]
      simpa [hmn]
    · exact hcosSub
    · exact hcosSum

/-- Helper: positive cosine modes have Kronecker-delta inner products. -/
lemma fourierCosine_inner_fourierCosine (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ⟪fourierCosine m, fourierCosine n⟫_ℝ = if m = n then 1 else 0 := by
  -- Rewrite the `L²` inner product as an interval integral of the pointwise cosine product.
  rw [fourierCosine, fourierCosine,
    inner_toLp_toLp_eq_intervalIntegral (fourierCosineFun_memLp m) (fourierCosineFun_memLp n)]
  by_cases hmn : m = n
  · -- On the diagonal, the product-to-sum identity reduces the integrand to `1 + cos`.
    subst m
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hsumNat : 0 < n + n := add_pos hn' hn'
    have hsum : (((n + n : ℕ) : ℤ)) ≠ 0 := by
      exact_mod_cast hsumNat.ne'
    have hrewrite :
        ∫ x in 0..1, fourierCosineFun n x * fourierCosineFun n x =
          ∫ x in 0..1, (1 + Real.cos (2 * Real.pi * (n + n) * x)) := by
      refine intervalIntegral.integral_congr_ae <| Filter.Eventually.of_forall ?_
      intro x hx
      have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
      calc
        fourierCosineFun n x * fourierCosineFun n x
            = (Real.sqrt 2 * Real.sqrt 2) *
                (Real.cos (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * n * x)) := by
                dsimp [fourierCosineFun]
                ring
        _ = 2 * Real.cos (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * n * x) := by
              rw [hsqrt]
              ring
        _ = Real.cos ((2 * Real.pi * n * x) - (2 * Real.pi * n * x)) +
              Real.cos ((2 * Real.pi * n * x) + (2 * Real.pi * n * x)) := by
                simpa using Real.two_mul_cos_mul_cos (2 * Real.pi * n * x) (2 * Real.pi * n * x)
        _ = 1 + Real.cos (2 * Real.pi * (n + n) * x) := by
              simp
              ring
    have hcosInt :
        IntervalIntegrable (fun x : ℝ ↦ Real.cos (2 * Real.pi * (n + n) * x)) volume 0 1 := by
      refine (Real.continuous_cos.comp ?_).intervalIntegrable 0 1
      exact continuous_const.mul continuous_id
    have hcosZero :
        ∫ x in 0..1, Real.cos (2 * Real.pi * (n + n) * x) = 0 := by
      simpa [Nat.cast_add] using integral_cos_two_pi_int_eq_zero hsum
    rw [hrewrite, intervalIntegral.integral_add]
    · rw [hcosZero]
      norm_num
    · exact intervalIntegrable_const
    · exact hcosInt
  · -- Off the diagonal, the product-to-sum identity yields two nonzero cosine frequencies.
    have hsub : ((m : ℤ) - n) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hmn
    have hsum : ((m : ℤ) + n) ≠ 0 := by
      have hmz : (0 : ℤ) < m := by
        exact_mod_cast Nat.pos_of_ne_zero hm
      have hnz : (0 : ℤ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      linarith
    have hrewrite :
        ∫ x in 0..1, fourierCosineFun m x * fourierCosineFun n x =
          ∫ x in 0..1,
            (Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x) +
              Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x)) := by
      refine intervalIntegral.integral_congr_ae <| Filter.Eventually.of_forall ?_
      intro x hx
      have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
      calc
        fourierCosineFun m x * fourierCosineFun n x
            = (Real.sqrt 2 * Real.sqrt 2) *
                (Real.cos (2 * Real.pi * m * x) * Real.cos (2 * Real.pi * n * x)) := by
                dsimp [fourierCosineFun]
                ring
        _ = 2 * Real.cos (2 * Real.pi * m * x) * Real.cos (2 * Real.pi * n * x) := by
              rw [hsqrt]
              ring
        _ = Real.cos ((2 * Real.pi * m * x) - (2 * Real.pi * n * x)) +
              Real.cos ((2 * Real.pi * m * x) + (2 * Real.pi * n * x)) := by
                simpa using Real.two_mul_cos_mul_cos (2 * Real.pi * m * x) (2 * Real.pi * n * x)
        _ = Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x) +
              Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x) := by
              congr 2
              · simp [Int.cast_sub, sub_eq_add_neg]
                ring
              · simp [Int.cast_add]
                ring
    have hcosSub :
        IntervalIntegrable
          (fun x : ℝ ↦ Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x)) volume 0 1 := by
      refine (Real.continuous_cos.comp ?_).intervalIntegrable 0 1
      exact continuous_const.mul continuous_id
    have hcosSum :
        IntervalIntegrable
          (fun x : ℝ ↦ Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x)) volume 0 1 := by
      refine (Real.continuous_cos.comp ?_).intervalIntegrable 0 1
      exact continuous_const.mul continuous_id
    have hcosSubZero :
        ∫ x in 0..1, Real.cos (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x) = 0 := by
      exact integral_cos_two_pi_int_eq_zero hsub
    have hcosSumZero :
        ∫ x in 0..1, Real.cos (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x) = 0 := by
      exact integral_cos_two_pi_int_eq_zero hsum
    rw [hrewrite, intervalIntegral.integral_add]
    · rw [hcosSubZero, hcosSumZero]
      simpa [hmn]
    · exact hcosSub
    · exact hcosSum

/-- Helper: positive sine and cosine modes are orthogonal. -/
lemma fourierSine_inner_fourierCosine (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ⟪fourierSine m, fourierCosine n⟫_ℝ = 0 := by
  -- Rewrite the mixed inner product as an interval integral and reduce it to sine averages.
  rw [fourierSine, fourierCosine,
    inner_toLp_toLp_eq_intervalIntegral (fourierSineFun_memLp m) (fourierCosineFun_memLp n)]
  by_cases hmn : m = n
  · -- On the diagonal, the mixed product reduces to a single nonzero sine frequency.
    subst m
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hsumNat : 0 < n + n := add_pos hn' hn'
    have hsum : (((n + n : ℕ) : ℤ)) ≠ 0 := by
      exact_mod_cast hsumNat.ne'
    have hrewrite :
        ∫ x in 0..1, fourierSineFun n x * fourierCosineFun n x =
          ∫ x in 0..1, Real.sin (2 * Real.pi * (n + n) * x) := by
      refine intervalIntegral.integral_congr_ae <| Filter.Eventually.of_forall ?_
      intro x hx
      have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
      calc
        fourierSineFun n x * fourierCosineFun n x
            = (Real.sqrt 2 * Real.sqrt 2) *
                (Real.sin (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * n * x)) := by
                dsimp [fourierSineFun, fourierCosineFun]
                ring
        _ = 2 * Real.sin (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * n * x) := by
              rw [hsqrt]
              ring
        _ = Real.sin ((2 * Real.pi * n * x) - (2 * Real.pi * n * x)) +
              Real.sin ((2 * Real.pi * n * x) + (2 * Real.pi * n * x)) := by
                simpa using Real.two_mul_sin_mul_cos (2 * Real.pi * n * x) (2 * Real.pi * n * x)
        _ = Real.sin (2 * Real.pi * (n + n) * x) := by
              simp
              ring
    rw [hrewrite]
    simpa [Nat.cast_add] using integral_sin_two_pi_int_eq_zero hsum
  · -- Off the diagonal, the product-to-sum identity yields two nonzero sine frequencies.
    have hsub : ((m : ℤ) - n) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hmn
    have hsum : ((m : ℤ) + n) ≠ 0 := by
      have hmz : (0 : ℤ) < m := by
        exact_mod_cast Nat.pos_of_ne_zero hm
      have hnz : (0 : ℤ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      linarith
    have hrewrite :
        ∫ x in 0..1, fourierSineFun m x * fourierCosineFun n x =
          ∫ x in 0..1,
            (Real.sin (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x) +
              Real.sin (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x)) := by
      refine intervalIntegral.integral_congr_ae <| Filter.Eventually.of_forall ?_
      intro x hx
      have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
      calc
        fourierSineFun m x * fourierCosineFun n x
            = (Real.sqrt 2 * Real.sqrt 2) *
                (Real.sin (2 * Real.pi * m * x) * Real.cos (2 * Real.pi * n * x)) := by
                dsimp [fourierSineFun, fourierCosineFun]
                ring
        _ = 2 * Real.sin (2 * Real.pi * m * x) * Real.cos (2 * Real.pi * n * x) := by
              rw [hsqrt]
              ring
        _ = Real.sin ((2 * Real.pi * m * x) - (2 * Real.pi * n * x)) +
              Real.sin ((2 * Real.pi * m * x) + (2 * Real.pi * n * x)) := by
                simpa using Real.two_mul_sin_mul_cos (2 * Real.pi * m * x) (2 * Real.pi * n * x)
        _ = Real.sin (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x) +
              Real.sin (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x) := by
              congr 2
              · simp [Int.cast_sub, sub_eq_add_neg]
                ring
              · simp [Int.cast_add]
                ring
    have hsinSub :
        IntervalIntegrable
          (fun x : ℝ ↦ Real.sin (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x)) volume 0 1 := by
      refine (Real.continuous_sin.comp ?_).intervalIntegrable 0 1
      exact continuous_const.mul continuous_id
    have hsinSum :
        IntervalIntegrable
          (fun x : ℝ ↦ Real.sin (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x)) volume 0 1 := by
      refine (Real.continuous_sin.comp ?_).intervalIntegrable 0 1
      exact continuous_const.mul continuous_id
    have hsinSubZero :
        ∫ x in 0..1, Real.sin (2 * Real.pi * (((m : ℤ) - n : ℤ) : ℝ) * x) = 0 := by
      exact integral_sin_two_pi_int_eq_zero hsub
    have hsinSumZero :
        ∫ x in 0..1, Real.sin (2 * Real.pi * (((m : ℤ) + n : ℤ) : ℝ) * x) = 0 := by
      exact integral_sin_two_pi_int_eq_zero hsum
    rw [hrewrite, intervalIntegral.integral_add]
    · rw [hsinSubZero, hsinSumZero]
      simp
    · exact hsinSub
    · exact hsinSum

/-- Helper: positive Fourier characters have the expected cosine real part. -/
lemma positiveFourierCharacter_re (n : ℕ) (x : ℝ) :
    RCLike.re (fourier (Int.ofNat (n + 1)) (x : AddCircle (1 : ℝ))) =
      Real.cos (2 * Real.pi * (n + 1) * x) := by
  -- The positive-frequency character is `cos + i sin`.
  rw [fourier_coe_apply]
  have h1 : 2 * ↑Real.pi * Complex.I * ↑(Int.ofNat (n + 1)) * ↑x / (1 : ℝ) =
      ↑(2 * Real.pi * (n + 1) * x) * Complex.I := by
    norm_num
    ring
  rw [h1]
  simpa using (Complex.exp_ofReal_mul_I_re (2 * Real.pi * (n + 1) * x))

/-- Helper: positive Fourier characters have the expected sine imaginary part. -/
lemma positiveFourierCharacter_im (n : ℕ) (x : ℝ) :
    RCLike.im (fourier (Int.ofNat (n + 1)) (x : AddCircle (1 : ℝ))) =
      Real.sin (2 * Real.pi * (n + 1) * x) := by
  -- The imaginary part is the sine mode.
  rw [fourier_coe_apply]
  have h1 : 2 * ↑Real.pi * Complex.I * ↑(Int.ofNat (n + 1)) * ↑x / (1 : ℝ) =
      ↑(2 * Real.pi * (n + 1) * x) * Complex.I := by
    norm_num
    ring
  rw [h1]
  simpa using (Complex.exp_ofReal_mul_I_im (2 * Real.pi * (n + 1) * x))

/-- Helper: negative Fourier characters keep the cosine real part. -/
lemma negativeFourierCharacter_re (n : ℕ) (x : ℝ) :
    RCLike.re (fourier (-(Int.ofNat (n + 1))) (x : AddCircle (1 : ℝ))) =
      Real.cos (2 * Real.pi * (n + 1) * x) := by
  -- Conjugation flips only the sine sign.
  rw [fourier_neg, fourier_coe_apply]
  have h1 : 2 * ↑Real.pi * Complex.I * ↑(Int.ofNat (n + 1)) * ↑x / (1 : ℝ) =
      ↑(2 * Real.pi * (n + 1) * x) * Complex.I := by
    norm_num
    ring
  rw [h1]
  simpa using (Complex.exp_ofReal_mul_I_re (2 * Real.pi * (n + 1) * x))

/-- Helper: negative Fourier characters negate the sine imaginary part. -/
lemma negativeFourierCharacter_im (n : ℕ) (x : ℝ) :
    RCLike.im (fourier (-(Int.ofNat (n + 1))) (x : AddCircle (1 : ℝ))) =
      -Real.sin (2 * Real.pi * (n + 1) * x) := by
  -- Conjugation reverses the imaginary part.
  rw [fourier_neg, fourier_coe_apply]
  have h1 : 2 * ↑Real.pi * Complex.I * ↑(Int.ofNat (n + 1)) * ↑x / (1 : ℝ) =
      ↑(2 * Real.pi * (n + 1) * x) * Complex.I := by
    norm_num
    ring
  rw [h1]
  simpa using congrArg Neg.neg (Complex.exp_ofReal_mul_I_im (2 * Real.pi * (n + 1) * x))

-- Route correction: the branchwise trigonometric orthogonality and the complex Fourier bridge
-- both still need a smaller normalization API to avoid elaboration blowups.
/-- Helper: the normalized real trigonometric modes have the expected
Kronecker-delta inner products. -/
lemma normalizedModesInner_eq_kronecker (i j : FourierTrigonometricIndex) :
    ⟪normalizedFourierTrigonometricSystem i, normalizedFourierTrigonometricSystem j⟫_ℝ =
      if i = j then 1 else 0 := by
  -- Evaluate the nine constant/sine/cosine cases using the branchwise orthogonality lemmas.
  cases i with
  | constant =>
      cases j with
      | constant =>
          simpa [normalizedFourierTrigonometricSystem] using fourierConstant_inner_fourierConstant
      | sine n =>
          simpa [normalizedFourierTrigonometricSystem] using
            fourierConstant_inner_fourierSine (n + 1) (Nat.succ_ne_zero n)
      | cosine n =>
          simpa [normalizedFourierTrigonometricSystem] using
            fourierConstant_inner_fourierCosine (n + 1) (Nat.succ_ne_zero n)
  | sine m =>
      cases j with
      | constant =>
          simpa [normalizedFourierTrigonometricSystem, inner_eq_zero_symm] using
            fourierConstant_inner_fourierSine (m + 1) (Nat.succ_ne_zero m)
      | sine n =>
          simpa [normalizedFourierTrigonometricSystem] using
            fourierSine_inner_fourierSine (m + 1) (n + 1) (Nat.succ_ne_zero m) (Nat.succ_ne_zero n)
      | cosine n =>
          simpa [normalizedFourierTrigonometricSystem] using
            fourierSine_inner_fourierCosine (m + 1) (n + 1) (Nat.succ_ne_zero m) (Nat.succ_ne_zero n)
  | cosine m =>
      cases j with
      | constant =>
          simpa [normalizedFourierTrigonometricSystem, inner_eq_zero_symm] using
            fourierConstant_inner_fourierCosine (m + 1) (Nat.succ_ne_zero m)
      | sine n =>
          simpa [normalizedFourierTrigonometricSystem, inner_eq_zero_symm] using
            fourierSine_inner_fourierCosine (n + 1) (m + 1) (Nat.succ_ne_zero n) (Nat.succ_ne_zero m)
      | cosine n =>
          simpa [normalizedFourierTrigonometricSystem] using
            fourierCosine_inner_fourierCosine (m + 1) (n + 1) (Nat.succ_ne_zero m) (Nat.succ_ne_zero n)

-- Proof sketch: compute the inner products by integrating products of sines and cosines on
-- `[0,1]`, then use the standard trigonometric orthogonality identities and the chosen
-- normalization constants.
/-- Companion: the normalized system `1, Sₙ, Cₙ` with `n ≥ 1` is orthonormal in
`L²([0,1], λ)`. -/
theorem normalizedFourierTrigonometricSystem_orthonormal :
    Orthonormal ℝ normalizedFourierTrigonometricSystem := by
  -- The Kronecker-delta inner-product formula is exactly the orthonormality criterion.
  rw [orthonormal_iff_ite]
  intro i j
  exact normalizedModesInner_eq_kronecker i j

/-- Helper for Exercise 7.3.1: orthogonality to the normalized trigonometric span forces the
constant, cosine, and sine interval integrals on `[0,1]` to vanish. -/
lemma orthogonalIntervalIntegrals_eq_zero (f : L2UnitInterval)
    (hf :
      f ∈ (Submodule.span ℝ (Set.range normalizedFourierTrigonometricSystem))ᗮ) :
    (∫ x in 0..1, f x = 0) ∧
      (∀ n : ℕ, ∫ x in 0..1, Real.cos (2 * Real.pi * (n + 1) * x) * f x = 0) ∧
      ∀ n : ℕ, ∫ x in 0..1, Real.sin (2 * Real.pi * (n + 1) * x) * f x = 0 := by
  -- Route correction: first collapse orthogonality to plain real interval integrals before
  -- touching the complex Fourier coefficient formulas.
  have horth :=
    ((Submodule.span ℝ (Set.range normalizedFourierTrigonometricSystem)).mem_orthogonal' f).1 hf
  have hsqrt2 : (Real.sqrt 2 : ℝ) ≠ 0 := by
    positivity
  have hconst : ∫ x in 0..1, f x = 0 := by
    -- The constant normalized mode is represented by the pointwise constant function `1`.
    have hconstInner : ⟪fourierConstant, f⟫_ℝ = 0 := by
      simpa [inner_eq_zero_symm] using
        horth _ (Submodule.subset_span ⟨FourierTrigonometricIndex.constant, rfl⟩)
    rw [fourierConstant,
      inner_toLp_eq_intervalIntegral fourierConstantFun_memLp f] at hconstInner
    simpa [fourierConstantFun] using hconstInner
  refine ⟨hconst, ?_, ?_⟩
  · intro n
    -- The cosine branch differs from the plain cosine integral only by the factor `√2`.
    have hcosInner : ⟪fourierCosine (n + 1), f⟫_ℝ = 0 := by
      simpa [inner_eq_zero_symm, normalizedFourierTrigonometricSystem] using
        horth _ (Submodule.subset_span ⟨FourierTrigonometricIndex.cosine n, rfl⟩)
    have hscaled :
        Real.sqrt 2 * ∫ x in 0..1, Real.cos (2 * Real.pi * (n + 1) * x) * f x = 0 := by
      rw [fourierCosine,
        inner_toLp_eq_intervalIntegral (fourierCosineFun_memLp (n + 1)) f] at hcosInner
      have hnormalized :
          ∫ x in 0..1, Real.sqrt 2 * (Real.cos (2 * Real.pi * (n + 1) * x) * f x) = 0 := by
        simpa [fourierCosineFun, mul_assoc, mul_left_comm, mul_comm] using hcosInner
      rw [intervalIntegral.integral_const_mul] at hnormalized
      simpa [mul_assoc, mul_left_comm, mul_comm] using hnormalized
    exact (mul_eq_zero.mp hscaled).resolve_left hsqrt2
  · intro n
    -- The sine branch is handled in the same way after factoring out the normalization constant.
    have hsinInner : ⟪fourierSine (n + 1), f⟫_ℝ = 0 := by
      simpa [inner_eq_zero_symm, normalizedFourierTrigonometricSystem] using
        horth _ (Submodule.subset_span ⟨FourierTrigonometricIndex.sine n, rfl⟩)
    have hscaled :
        Real.sqrt 2 * ∫ x in 0..1, Real.sin (2 * Real.pi * (n + 1) * x) * f x = 0 := by
      rw [fourierSine,
        inner_toLp_eq_intervalIntegral (fourierSineFun_memLp (n + 1)) f] at hsinInner
      have hnormalized :
          ∫ x in 0..1, Real.sqrt 2 * (Real.sin (2 * Real.pi * (n + 1) * x) * f x) = 0 := by
        simpa [fourierSineFun, mul_assoc, mul_left_comm, mul_comm] using hsinInner
      rw [intervalIntegral.integral_const_mul] at hnormalized
      simpa [mul_assoc, mul_left_comm, mul_comm] using hnormalized
    exact (mul_eq_zero.mp hscaled).resolve_left hsqrt2

/-- Helper for Exercise 7.3.1: the complexification of an `L²([0,1], λ)` function is square
integrable on `(0,1]`. -/
lemma complexify_memLp_Ioc (f : L2UnitInterval) :
    MemLp (fun x ↦ (f x : ℂ)) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  -- Rewrite the interval measure from `Icc` to the `Ioc` form used by `fourierCoeffOn`.
  simpa [unitIntervalMeasure, restrict_Ioc_eq_restrict_Icc] using
    ((Lp.memLp f).ofReal : MemLp (fun x ↦ (f x : ℂ)) 2 unitIntervalMeasure)

/-- Helper for Exercise 7.3.1: multiplying the complexified function by a Fourier character keeps
it integrable on `(0,1]`. -/
lemma fourierCharacterMul_complexify_integrable (f : L2UnitInterval) (n : ℤ) :
    Integrable (fun x : ℝ ↦ fourier n (x : AddCircle (1 : ℝ)) • (f x : ℂ))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  -- Fourier characters have pointwise norm `1`, so the product is dominated by the complexified
  -- representative itself on the finite interval measure.
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    infer_instance
  have hcomplex :
      Integrable (fun x ↦ (f x : ℂ)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    exact (complexify_memLp_Ioc f).integrable (by norm_num)
  refine Integrable.mono' hcomplex.norm
    ((((map_continuous (fourier n)).comp (AddCircle.continuous_mk' _)).aestronglyMeasurable).mul
      (complexify_memLp_Ioc f).aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hfourier : ‖fourier n (x : AddCircle (1 : ℝ))‖ = 1 := by
    simpa [fourier_coe_apply, Complex.norm_exp]
  rw [norm_smul, hfourier, one_mul]

/-- Helper for Exercise 7.3.1: the exact integrand from `fourierCoeffOn_eq_integral` is
integrable on `(0,1]`. -/
lemma fourierCoeffOnIntegrand_integrable (f : L2UnitInterval) (n : ℤ) :
    Integrable (fun x : ℝ ↦ fourier (-n) (x : AddCircle (1 : ℝ)) • (f x : ℂ))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  -- Route correction: match the `fourierCoeffOn_eq_integral` normal form exactly once.
  simpa using fourierCharacterMul_complexify_integrable f (-n)

/-- Helper for Exercise 7.3.1: the real part of a Fourier character times a real scalar keeps the
expected multiplicative shape. -/
lemma fourierCharacterSmulOfReal_re (m : ℤ) (x r : ℝ) :
    RCLike.re (fourier m (x : AddCircle (1 : ℝ)) • (r : ℂ)) =
      RCLike.re (fourier m (x : AddCircle (1 : ℝ))) * r := by
  -- The real-valued factor contributes no imaginary part, so `simp` exposes plain multiplication.
  simp [smul_eq_mul]

/-- Helper for Exercise 7.3.1: the imaginary part of a Fourier character times a real scalar keeps
the expected multiplicative shape. -/
lemma fourierCharacterSmulOfReal_im (m : ℤ) (x r : ℝ) :
    RCLike.im (fourier m (x : AddCircle (1 : ℝ)) • (r : ℂ)) =
      RCLike.im (fourier m (x : AddCircle (1 : ℝ))) * r := by
  -- The real scalar kills the cross term in the imaginary-part formula.
  simp [smul_eq_mul]

/-- Helper for Exercise 7.3.1: a positive Fourier coefficient of the complexified real function is
the complex number built from the cosine and sine interval integrals. -/
lemma fourierCoeffOn_complexify_pos_eq (f : L2UnitInterval) (n : ℕ) :
    fourierCoeffOn zero_lt_one (fun x ↦ (f x : ℂ)) (Int.ofNat (n + 1)) =
      Complex.mk
        (∫ x in 0..1, Real.cos (2 * Real.pi * (n + 1) * x) * f x)
        (-(∫ x in 0..1, Real.sin (2 * Real.pi * (n + 1) * x) * f x)) := by
  -- Route correction: rewrite the coefficient directly to the exact interval integrand, then
  -- read off the cosine and sine parts through `integral_re` and `integral_im`.
  have hInt := fourierCoeffOnIntegrand_integrable f (Int.ofNat (n + 1))
  have hcoeff :
      fourierCoeffOn zero_lt_one (fun x ↦ (f x : ℂ)) (Int.ofNat (n + 1)) =
        ∫ x in 0..1, fourier (-(Int.ofNat (n + 1))) (x : AddCircle (1 : ℝ)) • (f x : ℂ) := by
    -- The interval has length `1`, so the averaging factor disappears.
    rw [fourierCoeffOn_eq_integral (fun x ↦ (f x : ℂ)) (Int.ofNat (n + 1)) zero_lt_one]
    norm_num
  refine Complex.ext ?_ ?_
  · -- The real part is the cosine integral.
    rw [hcoeff]
    calc
      (∫ x in 0..1, fourier (-(Int.ofNat (n + 1))) (x : AddCircle (1 : ℝ)) • (f x : ℂ)).re
          = ∫ x in Set.Ioc (0 : ℝ) 1,
              RCLike.re (fourier (-(Int.ofNat (n + 1))) (x : AddCircle (1 : ℝ)) •
                (f x : ℂ)) ∂volume := by
                rw [intervalIntegral.integral_of_le zero_le_one]
                simpa using (integral_re hInt).symm
      _ = ∫ x in Set.Ioc (0 : ℝ) 1, Real.cos (2 * Real.pi * (n + 1) * x) * f x ∂volume := by
            refine integral_congr_ae ?_
            filter_upwards [] with x
            rw [fourierCharacterSmulOfReal_re, negativeFourierCharacter_re]
      _ = ∫ x in 0..1, Real.cos (2 * Real.pi * (n + 1) * x) * f x := by
            rw [intervalIntegral.integral_of_le zero_le_one]
  · -- The imaginary part is the negative sine integral.
    rw [hcoeff]
    calc
      (∫ x in 0..1, fourier (-(Int.ofNat (n + 1))) (x : AddCircle (1 : ℝ)) • (f x : ℂ)).im
          = ∫ x in Set.Ioc (0 : ℝ) 1,
              RCLike.im (fourier (-(Int.ofNat (n + 1))) (x : AddCircle (1 : ℝ)) •
                (f x : ℂ)) ∂volume := by
                rw [intervalIntegral.integral_of_le zero_le_one]
                simpa using (integral_im hInt).symm
      _ = ∫ x in Set.Ioc (0 : ℝ) 1, -(Real.sin (2 * Real.pi * (n + 1) * x) * f x) ∂volume := by
            refine integral_congr_ae ?_
            filter_upwards [] with x
            rw [fourierCharacterSmulOfReal_im, negativeFourierCharacter_im]
            ring
      _ = -(∫ x in Set.Ioc (0 : ℝ) 1, Real.sin (2 * Real.pi * (n + 1) * x) * f x ∂volume) := by
            rw [integral_neg]
      _ = -(∫ x in 0..1, Real.sin (2 * Real.pi * (n + 1) * x) * f x) := by
            rw [intervalIntegral.integral_of_le zero_le_one]

/-- Helper for Exercise 7.3.1: a negative Fourier coefficient of the complexified real function is
the complex number built from the cosine and sine interval integrals with the positive sine sign. -/
lemma fourierCoeffOn_complexify_neg_eq (f : L2UnitInterval) (n : ℕ) :
    fourierCoeffOn zero_lt_one (fun x ↦ (f x : ℂ)) (Int.negSucc n) =
      Complex.mk
        (∫ x in 0..1, Real.cos (2 * Real.pi * (n + 1) * x) * f x)
        (∫ x in 0..1, Real.sin (2 * Real.pi * (n + 1) * x) * f x) := by
  -- Route correction: the negative frequency turns `fourier (-n)` into the positive character, so
  -- the sine term picks up the positive sign.
  have hInt := fourierCoeffOnIntegrand_integrable f (Int.negSucc n)
  have hcoeff :
      fourierCoeffOn zero_lt_one (fun x ↦ (f x : ℂ)) (Int.negSucc n) =
        ∫ x in 0..1, fourier (Int.ofNat (n + 1)) (x : AddCircle (1 : ℝ)) • (f x : ℂ) := by
    -- Again the interval length is `1`, so no averaging factor remains.
    rw [fourierCoeffOn_eq_integral (fun x ↦ (f x : ℂ)) (Int.negSucc n) zero_lt_one]
    norm_num
  refine Complex.ext ?_ ?_
  · -- The real part is the cosine integral.
    rw [hcoeff]
    calc
      (∫ x in 0..1, fourier (Int.ofNat (n + 1)) (x : AddCircle (1 : ℝ)) • (f x : ℂ)).re
          = ∫ x in Set.Ioc (0 : ℝ) 1,
              RCLike.re (fourier (Int.ofNat (n + 1)) (x : AddCircle (1 : ℝ)) •
                (f x : ℂ)) ∂volume := by
                rw [intervalIntegral.integral_of_le zero_le_one]
                simpa using (integral_re hInt).symm
      _ = ∫ x in Set.Ioc (0 : ℝ) 1, Real.cos (2 * Real.pi * (n + 1) * x) * f x ∂volume := by
            refine integral_congr_ae ?_
            filter_upwards [] with x
            rw [fourierCharacterSmulOfReal_re, positiveFourierCharacter_re]
      _ = ∫ x in 0..1, Real.cos (2 * Real.pi * (n + 1) * x) * f x := by
            rw [intervalIntegral.integral_of_le zero_le_one]
  · -- The imaginary part is now the positive sine integral.
    rw [hcoeff]
    calc
      (∫ x in 0..1, fourier (Int.ofNat (n + 1)) (x : AddCircle (1 : ℝ)) • (f x : ℂ)).im
          = ∫ x in Set.Ioc (0 : ℝ) 1,
              RCLike.im (fourier (Int.ofNat (n + 1)) (x : AddCircle (1 : ℝ)) •
                (f x : ℂ)) ∂volume := by
                rw [intervalIntegral.integral_of_le zero_le_one]
                simpa using (integral_im hInt).symm
      _ = ∫ x in Set.Ioc (0 : ℝ) 1, Real.sin (2 * Real.pi * (n + 1) * x) * f x ∂volume := by
            refine integral_congr_ae ?_
            filter_upwards [] with x
            rw [fourierCharacterSmulOfReal_im, positiveFourierCharacter_im]
      _ = ∫ x in 0..1, Real.sin (2 * Real.pi * (n + 1) * x) * f x := by
            rw [intervalIntegral.integral_of_le zero_le_one]

/-- Helper: the interval Fourier coefficients of the complexification of a
vector orthogonal to the normalized trigonometric span all vanish. -/
lemma fourierCoeffOn_complexify_eq_zero_of_mem_orthogonal (f : L2UnitInterval)
    (hf :
      f ∈ (Submodule.span ℝ (Set.range normalizedFourierTrigonometricSystem))ᗮ) :
    ∀ n : ℤ, fourierCoeffOn zero_lt_one (fun x ↦ (f x : ℂ)) n = 0 := by
  -- Route correction: first extract the real interval vanishings, then read off each Fourier
  -- coefficient from the positive/negative branch formulas.
  have hintervals := orthogonalIntervalIntegrals_eq_zero f hf
  intro n
  cases n with
  | ofNat m =>
      cases m with
      | zero =>
          -- The zero-frequency coefficient is just the average of the function itself.
          change fourierCoeffOn zero_lt_one (fun x ↦ (f x : ℂ)) 0 = 0
          rw [fourierCoeffOn_eq_integral (fun x ↦ (f x : ℂ)) 0 zero_lt_one]
          norm_num
          calc
            ∫ x in 0..1, (f x : ℂ) = ((∫ x in 0..1, f x : ℝ) : ℂ) := by
              have hOfReal :
                  ∫ x in 0..1, ((fun x : ℝ ↦ f x) x : ℂ) =
                    ((∫ x in 0..1, (fun x : ℝ ↦ f x) x : ℝ) : ℂ) :=
                RCLike.intervalIntegral_ofReal
              simpa using hOfReal
            _ = 0 := by
              simpa using congrArg (fun t : ℝ ↦ (t : ℂ)) hintervals.1
      | succ k =>
          -- Positive frequencies vanish because both the cosine and sine integrals vanish.
          rw [fourierCoeffOn_complexify_pos_eq, hintervals.2.1 k, hintervals.2.2 k]
          apply Complex.ext <;> simp
  | negSucc k =>
      -- Negative frequencies use the analogous branch formula with the positive sine sign.
      rw [fourierCoeffOn_complexify_neg_eq, hintervals.2.1 k, hintervals.2.2 k]
      apply Complex.ext <;> simp

/-- Helper: the orthogonal complement of the normalized trigonometric span is
trivial. -/
lemma normalizedFourierTrigonometricSystem_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range normalizedFourierTrigonometricSystem))ᗮ = ⊥ := by
  -- Route correction: once every complex Fourier coefficient vanishes, Parseval on `(0,1]`
  -- forces the square integral to vanish, hence the original `L²` class is zero.
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hcoeff := fourierCoeffOn_complexify_eq_zero_of_mem_orthogonal f hf
  have henergy :=
    tsum_sq_fourierCoeffOn zero_lt_one (complexify_memLp_Ioc f)
  -- All Fourier coefficients are zero, so Parseval collapses the square integral to zero.
  simp [hcoeff] at henergy
  rw [intervalIntegral.integral_of_le zero_le_one] at henergy
  have hrealMemLpIoc : MemLp (fun x : ℝ ↦ f x) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    simpa [unitIntervalMeasure, restrict_Ioc_eq_restrict_Icc] using (Lp.memLp f)
  have hsqInt : Integrable (fun x : ℝ ↦ f x ^ 2) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hrealMemLpIoc.integrable_sq
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun x : ℝ ↦ f x ^ 2 := by
    -- Pointwise squares are nonnegative.
    filter_upwards [] with x
    positivity
  have hsqAeZero :
      (fun x : ℝ ↦ f x ^ 2) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] 0 := by
    -- Zero integral of a nonnegative function forces almost-everywhere vanishing.
    exact (integral_eq_zero_iff_of_nonneg_ae hnonneg hsqInt).1 henergy.symm
  have hrealAeZeroIoc : (fun x : ℝ ↦ f x) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] 0 := by
    -- Pointwise, a real square is zero exactly when the original value is zero.
    filter_upwards [hsqAeZero] with x hx
    exact eq_zero_of_pow_eq_zero hx
  have hrealAeZero : (fun x : ℝ ↦ f x) =ᵐ[unitIntervalMeasure] 0 := by
    -- Convert the `(0,1]` statement back to the textbook interval measure `[0,1]`.
    simpa [unitIntervalMeasure, restrict_Ioc_eq_restrict_Icc] using hrealAeZeroIoc
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hrealAeZero

-- Proof sketch: the closed linear span of the normalized trigonometric system contains the image
-- of all trigonometric polynomials, which are dense in `L²([0,1], λ)`.
/-- Companion: the normalized trigonometric system spans `L²([0,1], λ)` densely. -/
theorem normalizedFourierTrigonometricSystem_dense_span :
    (Submodule.span ℝ (Set.range normalizedFourierTrigonometricSystem)).topologicalClosure = ⊤ :=
  by
  -- Rewrite dense spanning as trivial orthogonal complement and reuse the previous lemma.
  rw [Submodule.topologicalClosure_eq_top_iff]
  exact normalizedFourierTrigonometricSystem_orthogonal_eq_bot

/-- The canonical Hilbert-basis owner for the normalized real trigonometric system on `[0,1]`. -/
def realFourierHilbertBasis : HilbertBasis FourierTrigonometricIndex ℝ L2UnitInterval :=
  HilbertBasis.mk normalizedFourierTrigonometricSystem_orthonormal
    (le_of_eq normalizedFourierTrigonometricSystem_dense_span.symm)

@[simp] theorem coe_realFourierHilbertBasis :
    ⇑realFourierHilbertBasis = normalizedFourierTrigonometricSystem := by
  simp [realFourierHilbertBasis]

/-- Companion: the Hilbert-basis Fourier coefficient of `f` is the inner product with the
corresponding normalized trigonometric mode. -/
theorem realFourierHilbertBasis_repr_apply
    (f : L2UnitInterval) (i : FourierTrigonometricIndex) :
    realFourierHilbertBasis.repr f i = ⟪normalizedFourierTrigonometricSystem i, f⟫_ℝ := by
  simpa [realFourierHilbertBasis] using
    HilbertBasis.repr_apply_apply realFourierHilbertBasis f i

/-- Companion: the normalized trigonometric expansion of an `L²([0,1], λ)` function converges to
that function in the Hilbert-space sense. -/
theorem hasSum_normalizedFourierExpansion (f : L2UnitInterval) :
    HasSum
      (fun i : FourierTrigonometricIndex ↦
        realFourierHilbertBasis.repr f i • normalizedFourierTrigonometricSystem i)
      f := by
  simpa [realFourierHilbertBasis] using HilbertBasis.hasSum_repr realFourierHilbertBasis f

/-- Helper: reindex a positive-frequency `ℓ²` family by `ℕ`. -/
theorem positiveFrequencyCoefficientsOnNat_memℓp (coeffs : ℓ²(ℕ+, ℝ)) :
    Memℓp (fun n : ℕ ↦ coeffs (Equiv.pnatEquivNat.symm n)) 2 := by
  -- The equivalence `ℕ ≃ ℕ+` preserves square summability of the positive-frequency branch.
  have hcoeff :
      Summable (fun n : ℕ+ ↦ ‖coeffs n‖ ^ (2 : ℝ)) := by
    exact (lp.memℓp coeffs).summable (by norm_num)
  exact memℓp_gen (by
    simpa [Function.comp] using hcoeff.comp_injective pnatEquivNat.symm.injective)

/-- Helper: view a positive-frequency `ℓ²` family as an `ℓ²` family on `ℕ`. -/
def positiveFrequencyCoefficientsOnNat (coeffs : ℓ²(ℕ+, ℝ)) : ℓ²(ℕ, ℝ) :=
  ⟨fun n ↦ coeffs (Equiv.pnatEquivNat.symm n), positiveFrequencyCoefficientsOnNat_memℓp coeffs⟩

/-- Helper: the positive-frequency sine modes are the sine branch of the
normalized Fourier basis. -/
theorem normalizedPositiveSineSystem_orthonormal :
    Orthonormal ℝ (fun n : ℕ ↦ fourierSine (n + 1)) := by
  -- Restricting the normalized trigonometric system to its sine branch preserves orthonormality.
  simpa [Function.comp, normalizedFourierTrigonometricSystem] using
    normalizedFourierTrigonometricSystem_orthonormal.comp
      (fun n : ℕ ↦ FourierTrigonometricIndex.sine n)
      (by
        intro m n hmn
        simpa using hmn)

/-- Helper: the positive-frequency cosine modes are the cosine branch of the
normalized Fourier basis. -/
theorem normalizedPositiveCosineSystem_orthonormal :
    Orthonormal ℝ (fun n : ℕ ↦ fourierCosine (n + 1)) := by
  -- Restricting the normalized trigonometric system to its cosine branch preserves orthonormality.
  simpa [Function.comp, normalizedFourierTrigonometricSystem] using
    normalizedFourierTrigonometricSystem_orthonormal.comp
      (fun n : ℕ ↦ FourierTrigonometricIndex.cosine n)
      (by
        intro m n hmn
        simpa using hmn)

-- Proof sketch: reindex the positive-frequency branches by `ℕ`, use orthogonality of the sine and
-- cosine branches separately, and then transfer the resulting summability statement back to `ℕ+`.
/-- Helper: the positive-frequency part of the Fourier series defining `h_{a,b}` is summable
in `L²([0,1], λ)`. -/
theorem fourierSeries_summable (coeffs : FourierCoefficients) :
    Summable (fourierSeriesSummand coeffs) := by
  -- Route correction: after moving the synthesis block below `realFourierHilbertBasis`,
  -- summability is proved by orthogonality of the sine/cosine branches rather than by
  -- forward-referencing later Hilbert-basis transport.
  let sineCoeffs : ℓ²(ℕ, ℝ) := positiveFrequencyCoefficientsOnNat coeffs.1
  let cosineCoeffs : ℓ²(ℕ, ℝ) := positiveFrequencyCoefficientsOnNat
    (positiveCosineCoefficients coeffs)
  -- Each orthonormal branch gives a summable synthesis series in `L²([0,1], λ)`.
  have hsine :
      Summable (fun n : ℕ ↦ sineCoeffs n • fourierSine (n + 1)) := by
    simpa [sineCoeffs, positiveFrequencyCoefficientsOnNat,
      LinearIsometry.toSpanSingleton_apply] using
      normalizedPositiveSineSystem_orthonormal.orthogonalFamily.summable_of_lp sineCoeffs
  have hcosine :
      Summable (fun n : ℕ ↦ cosineCoeffs n • fourierCosine (n + 1)) := by
    simpa [cosineCoeffs, positiveFrequencyCoefficientsOnNat, positiveCosineCoefficients,
      LinearIsometry.toSpanSingleton_apply] using
      normalizedPositiveCosineSystem_orthonormal.orthogonalFamily.summable_of_lp cosineCoeffs
  have hnat :
      Summable (fun n : ℕ ↦
        sineCoeffs n • fourierSine (n + 1) + cosineCoeffs n • fourierCosine (n + 1)) :=
    hsine.add hcosine
  have hreindexed :
      Summable (fourierSeriesSummand coeffs ∘ pnatEquivNat.symm) := by
    -- The reindexed summand is exactly the nat-indexed sum of the two orthogonal branches.
    simpa [Function.comp, fourierSeriesSummand, sineCoeffs, cosineCoeffs,
      positiveFrequencyCoefficientsOnNat, positiveCosineCoefficients] using hnat
  -- The map `ℕ ≃ ℕ+` has full range, so summability transfers back to the original indexing.
  exact (pnatEquivNat.symm.summable_iff).1 hreindexed

-- Mathlib recall: `hasSum_ite_eq` packages the constant mode, and
-- `tsum_zero_pnat_eq_tsum_nat` is the matching full-series reindexing lemma on `ℕ`.
/-- Part (2) of Exercise 7.3.1: for every square-summable coefficient vector `coeffs = (a, b)`, the full
Fourier series defining `h_{a,b}` converges in `L²([0,1], λ)`. Equivalently, the nat-indexed
series with zeroth term `b 0 • fourierConstant` and later terms given by the positive-frequency
summands in order has sum `fourierSeries coeffs`. -/
theorem fourierSeries_hasSum (coeffs : FourierCoefficients) :
    HasSum
      (fun n : ℕ ↦
        match n with
        | 0 => coeffs.2 0 • fourierConstant
        | n + 1 => fourierSeriesSummand coeffs (Equiv.pnatEquivNat.symm n))
      (fourierSeries coeffs) := by
  let f : ℕ → L2UnitInterval := fun n ↦
    match n with
    | 0 => coeffs.2 0 • fourierConstant
    | n + 1 => fourierSeriesSummand coeffs (Equiv.pnatEquivNat.symm n)
  let pos : ℕ → L2UnitInterval := fun n ↦ fourierSeriesSummand coeffs (Equiv.pnatEquivNat.symm n)
  -- Reindex the positive-frequency summand to `ℕ`.
  have hpos :
      HasSum pos (∑' n : ℕ+, fourierSeriesSummand coeffs n) := by
    simpa [pos, Function.comp] using
      (pnatEquivNat.symm.hasSum_iff).2 (fourierSeries_summable coeffs).hasSum
  -- Then add the zeroth term back in by the standard `nat_add` packaging.
  have hf :
      HasSum f
        (∑' n : ℕ+, fourierSeriesSummand coeffs n + coeffs.2 0 • fourierConstant) := by
    have hshift : HasSum (fun n : ℕ ↦ f (n + 1)) (∑' n : ℕ+, fourierSeriesSummand coeffs n) := by
      simpa [f, pos] using hpos
    simpa [f, add_comm, add_left_comm, add_assoc] using (hasSum_nat_add_iff 1).1 hshift
  -- The resulting sum is exactly the source-facing Fourier series.
  simpa [fourierSeries, add_comm, add_left_comm, add_assoc] using hf

/-- Helper: identify the cosine-side index set `Unit ⊕ ℕ` with `ℕ` by sending
the constant mode to `0` and the positive cosine modes to `n + 1`. -/
def constantCosineIndexEquiv : ℕ ≃ Unit ⊕ ℕ where
  toFun
    | 0 => Sum.inl ()
    | n + 1 => Sum.inr n
  invFun
    | Sum.inl _ => 0
    | Sum.inr n => n + 1
  left_inv n := by
    cases n <;> rfl
  right_inv x := by
    cases x with
    | inl u =>
        cases u
        rfl
    | inr n =>
        rfl

/-- Helper: the positive-frequency sine branch defines a summable `L²` series
on `ℕ+`. -/
theorem fourierSineSeries_summable (coeffs : FourierCoefficients) :
    Summable (fun n : ℕ+ ↦ coeffs.1 n • fourierSine n) := by
  let sineCoeffs : ℓ²(ℕ, ℝ) := positiveFrequencyCoefficientsOnNat coeffs.1
  -- Reindex the positive-frequency sine coefficients to `ℕ` and use orthogonality there once.
  have hsineNat :
      Summable (fun n : ℕ ↦ sineCoeffs n • fourierSine (n + 1)) := by
    simpa [sineCoeffs, positiveFrequencyCoefficientsOnNat,
      LinearIsometry.toSpanSingleton_apply] using
      normalizedPositiveSineSystem_orthonormal.orthogonalFamily.summable_of_lp sineCoeffs
  -- Transport the nat-indexed series back to the original positive-frequency indexing.
  exact (pnatEquivNat.symm.summable_iff).1 <| by
    simpa [sineCoeffs, positiveFrequencyCoefficientsOnNat, Function.comp] using hsineNat

/-- Helper: the positive-frequency cosine branch defines a summable `L²` series
on `ℕ+`. -/
theorem fourierCosineSeries_summable (coeffs : FourierCoefficients) :
    Summable (fun n : ℕ+ ↦ coeffs.2 n • fourierCosine n) := by
  let cosineCoeffs : ℓ²(ℕ, ℝ) :=
    positiveFrequencyCoefficientsOnNat (positiveCosineCoefficients coeffs)
  -- Reindex the positive cosine branch to `ℕ` and use orthogonality on that branch.
  have hcosineNat :
      Summable (fun n : ℕ ↦ cosineCoeffs n • fourierCosine (n + 1)) := by
    simpa [cosineCoeffs, positiveFrequencyCoefficientsOnNat, positiveCosineCoefficients,
      LinearIsometry.toSpanSingleton_apply] using
      normalizedPositiveCosineSystem_orthonormal.orthogonalFamily.summable_of_lp cosineCoeffs
  -- Transport the nat-indexed cosine series back to the original positive-frequency indexing.
  exact (pnatEquivNat.symm.summable_iff).1 <| by
    simpa [cosineCoeffs, positiveFrequencyCoefficientsOnNat, positiveCosineCoefficients,
      Function.comp] using hcosineNat

/-- Helper: the positive-frequency sine branch has the expected nat-indexed
reindexed sum. -/
theorem hasSum_fourierSineSeriesOnNat (coeffs : FourierCoefficients) :
    HasSum (fun n : ℕ ↦ coeffs.1 (Equiv.pnatEquivNat.symm n) • fourierSine (n + 1))
      (∑' n : ℕ+, coeffs.1 n • fourierSine n) := by
  -- Reindex the already summable positive-frequency sine series through `ℕ ≃ ℕ+`.
  simpa [Function.comp] using
    (pnatEquivNat.symm.hasSum_iff).2 (fourierSineSeries_summable coeffs).hasSum

/-- Helper: the positive-frequency cosine branch has the expected nat-indexed
reindexed sum. -/
theorem hasSum_fourierCosineSeriesOnNat (coeffs : FourierCoefficients) :
    HasSum (fun n : ℕ ↦ coeffs.2 (n + 1) • fourierCosine (n + 1))
      (∑' n : ℕ+, coeffs.2 n • fourierCosine n) := by
  -- Reindex the already summable positive-frequency cosine series through `ℕ ≃ ℕ+`.
  simpa [Function.comp] using
    (pnatEquivNat.symm.hasSum_iff).2 (fourierCosineSeries_summable coeffs).hasSum

/-- Helper: explicit constant/sine/cosine packaging of the source Fourier
coefficients on the three-branch sum type `Unit ⊕ (ℕ ⊕ ℕ)`. -/
def coefficientSumFamily (coeffs : FourierCoefficients) : Unit ⊕ (ℕ ⊕ ℕ) → ℝ
  | Sum.inl _ => coeffs.2 0
  | Sum.inr (Sum.inl n) => coeffs.1 (Equiv.pnatEquivNat.symm n)
  | Sum.inr (Sum.inr n) => coeffs.2 (n + 1)

/-- Helper: the branchwise synthesis term corresponding to the explicit
sum-type coefficient family. -/
def coefficientSynthesisFamily (coeffs : FourierCoefficients) : Unit ⊕ (ℕ ⊕ ℕ) → L2UnitInterval
  | Sum.inl _ => coeffs.2 0 • fourierConstant
  | Sum.inr (Sum.inl n) => coeffs.1 (Equiv.pnatEquivNat.symm n) • fourierSine (n + 1)
  | Sum.inr (Sum.inr n) => coeffs.2 (n + 1) • fourierCosine (n + 1)

/-- Helper: the explicit branch family of Fourier coefficients is
square-summable on `Unit ⊕ (ℕ ⊕ ℕ)`. -/
lemma fourierCoefficientSumFamily_memℓp (coeffs : FourierCoefficients) :
    Memℓp (coefficientSumFamily coeffs) 2 := by
  have hconst :
      Summable (fun u : Unit ↦ ‖coefficientSumFamily coeffs (Sum.inl u)‖ ^ (2 : ℝ)) := by
    -- The constant branch is a one-point summable family.
    simpa [coefficientSumFamily] using
      (hasSum_fintype (fun u : Unit ↦ ‖coefficientSumFamily coeffs (Sum.inl u)‖ ^ (2 : ℝ))).summable
  have hsine :
      Summable (fun n : ℕ ↦ ‖coefficientSumFamily coeffs (Sum.inr (Sum.inl n))‖ ^ (2 : ℝ)) := by
    -- The sine branch is exactly the reindexed positive-frequency `ℓ²` sequence.
    exact (positiveFrequencyCoefficientsOnNat_memℓp coeffs.1).summable (by norm_num)
  have hcos :
      Summable (fun n : ℕ ↦ ‖coefficientSumFamily coeffs (Sum.inr (Sum.inr n))‖ ^ (2 : ℝ)) := by
    -- The cosine branch is the nat-indexed version of the positive cosine coefficients.
    exact
      (positiveFrequencyCoefficientsOnNat_memℓp (positiveCosineCoefficients coeffs)).summable
        (by norm_num)
  have hright :
      Summable
        (fun i : ℕ ⊕ ℕ ↦ ‖coefficientSumFamily coeffs (Sum.inr i)‖ ^ (2 : ℝ)) := by
    -- Combine the sine and cosine branches on the right-hand sum.
    exact Summable.sum _ hsine hcos
  have hsum :
      Summable (fun i : Unit ⊕ (ℕ ⊕ ℕ) ↦ ‖coefficientSumFamily coeffs i‖ ^ (2 : ℝ)) := by
    -- Then add the constant branch back in.
    exact Summable.sum _ hconst hright
  exact memℓp_gen hsum

/-- Helper: the packaged coefficient family is square-summable on the
trigonometric Hilbert-basis index type. -/
theorem fourierCoefficientFamily_memℓp (coeffs : FourierCoefficients) :
    Memℓp
      (fun i : FourierTrigonometricIndex ↦
        match i with
        | .constant => coeffs.2 0
        | .sine n => coeffs.1 (Equiv.pnatEquivNat.symm n)
        | .cosine n => coeffs.2 (n + 1))
      2 := by
  -- Transport the square-summable branch family through the explicit index equivalence once.
  have hsum :
      Summable (fun i : Unit ⊕ (ℕ ⊕ ℕ) ↦ ‖coefficientSumFamily coeffs i‖ ^ (2 : ℝ)) := by
    exact (fourierCoefficientSumFamily_memℓp coeffs).summable (by norm_num)
  refine memℓp_gen ?_
  have hrewrite :
      (fun i : FourierTrigonometricIndex ↦
        ‖match i with
          | .constant => coeffs.2 0
          | .sine n => coeffs.1 (Equiv.pnatEquivNat.symm n)
          | .cosine n => coeffs.2 (n + 1)‖ ^ ENNReal.toReal 2) =
        fun i : FourierTrigonometricIndex ↦
          ‖coefficientSumFamily coeffs (fourierIndexEquiv i)‖ ^ ENNReal.toReal 2 := by
    funext i
    cases i <;> rfl
  rw [hrewrite]
  simpa [Function.comp] using (fourierIndexEquiv.summable_iff).2 hsum

/-- Helper: package the source-facing real Fourier coefficients into one
`ℓ²` coordinate family on the trigonometric Hilbert-basis index type. -/
def fourierCoefficientFamily (coeffs : FourierCoefficients) : ℓ²(FourierTrigonometricIndex, ℝ) :=
  ⟨fun i ↦
      match i with
      | .constant => coeffs.2 0
      | .sine n => coeffs.1 (Equiv.pnatEquivNat.symm n)
      | .cosine n => coeffs.2 (n + 1),
    fourierCoefficientFamily_memℓp coeffs⟩

@[simp] theorem fourierCoefficientFamily_constant (coeffs : FourierCoefficients) :
    fourierCoefficientFamily coeffs FourierTrigonometricIndex.constant = coeffs.2 0 :=
  rfl

@[simp] theorem fourierCoefficientFamily_sine (coeffs : FourierCoefficients) (n : ℕ) :
    fourierCoefficientFamily coeffs (FourierTrigonometricIndex.sine n) =
      coeffs.1 (Equiv.pnatEquivNat.symm n) :=
  rfl

@[simp] theorem fourierCoefficientFamily_cosine (coeffs : FourierCoefficients) (n : ℕ) :
    fourierCoefficientFamily coeffs (FourierTrigonometricIndex.cosine n) = coeffs.2 (n + 1) :=
  rfl

/-- Helper for Exercise 7.3.1: the constant branch of `coefficientSynthesisFamily` has the expected
one-point sum. -/
lemma coefficientSynthesisFamily_constant_hasSum (coeffs : FourierCoefficients) :
    HasSum (fun u : Unit ↦ coefficientSynthesisFamily coeffs (Sum.inl u))
      (coeffs.2 0 • fourierConstant) := by
  -- The constant branch is indexed by the one-point type `Unit`.
  simpa [coefficientSynthesisFamily] using
    (hasSum_fintype (fun u : Unit ↦ coefficientSynthesisFamily coeffs (Sum.inl u)))

/-- Helper for Exercise 7.3.1: the sine branch of `coefficientSynthesisFamily` is the nat-indexed
positive-frequency sine series. -/
lemma coefficientSynthesisFamily_sine_hasSum (coeffs : FourierCoefficients) :
    HasSum (fun n : ℕ ↦ coefficientSynthesisFamily coeffs (Sum.inr (Sum.inl n)))
      (∑' n : ℕ+, coeffs.1 n • fourierSine n) := by
  -- This is exactly the previously established nat reindexing of the sine series.
  simpa [coefficientSynthesisFamily] using hasSum_fourierSineSeriesOnNat coeffs

/-- Helper for Exercise 7.3.1: the cosine branch of `coefficientSynthesisFamily` is the nat-indexed
positive-frequency cosine series. -/
lemma coefficientSynthesisFamily_cosine_hasSum (coeffs : FourierCoefficients) :
    HasSum (fun n : ℕ ↦ coefficientSynthesisFamily coeffs (Sum.inr (Sum.inr n)))
      (∑' n : ℕ+, coeffs.2 n • fourierCosine n) := by
  -- This is exactly the previously established nat reindexing of the cosine series.
  simpa [coefficientSynthesisFamily] using hasSum_fourierCosineSeriesOnNat coeffs

/-- Helper for Exercise 7.3.1: combining the sine and cosine branches gives the right-hand
two-branch sum on `ℕ ⊕ ℕ`. -/
lemma coefficientSynthesisFamily_right_hasSum (coeffs : FourierCoefficients) :
    HasSum (fun i : ℕ ⊕ ℕ ↦ coefficientSynthesisFamily coeffs (Sum.inr i))
      ((∑' n : ℕ+, coeffs.1 n • fourierSine n) + ∑' n : ℕ+, coeffs.2 n • fourierCosine n) := by
  -- Assemble the two positive-frequency branches before adding back the constant mode.
  exact (coefficientSynthesisFamily_sine_hasSum coeffs).sum
    (coefficientSynthesisFamily_cosine_hasSum coeffs)

/-- Helper: the packaged coefficient family synthesizes back to the
source-facing real Fourier series. -/
lemma hasSum_coefficientSynthesisFamily (coeffs : FourierCoefficients) :
    HasSum (coefficientSynthesisFamily coeffs)
      (coeffs.2 0 • fourierConstant +
        ((∑' n : ℕ+, coeffs.1 n • fourierSine n) + ∑' n : ℕ+, coeffs.2 n • fourierCosine n)) := by
  -- Add the one-point constant branch to the already packaged sine/cosine branch sum.
  exact (coefficientSynthesisFamily_constant_hasSum coeffs).sum
    (coefficientSynthesisFamily_right_hasSum coeffs)

theorem hasSum_fourierCoefficientFamily (coeffs : FourierCoefficients) :
    HasSum
      (fun i : FourierTrigonometricIndex ↦
        fourierCoefficientFamily coeffs i • normalizedFourierTrigonometricSystem i)
      (fourierSeries coeffs) := by
  -- Keep the synthesis proof in explicit constant/sine/cosine branch form until the final transport.
  have hsineSummable : Summable (fun n : ℕ+ ↦ coeffs.1 n • fourierSine n) :=
    fourierSineSeries_summable coeffs
  have hcosSummable : Summable (fun n : ℕ+ ↦ coeffs.2 n • fourierCosine n) :=
    fourierCosineSeries_summable coeffs
  have hbranch :
      HasSum (coefficientSynthesisFamily coeffs) (fourierSeries coeffs) := by
    have hpack := hasSum_coefficientSynthesisFamily coeffs
    have htarget :
        coeffs.2 0 • fourierConstant +
            ((∑' n : ℕ+, coeffs.1 n • fourierSine n) + ∑' n : ℕ+, coeffs.2 n • fourierCosine n) =
          fourierSeries coeffs := by
      rw [fourierSeries]
      congr 1
      change
        (∑' n : ℕ+, coeffs.1 n • fourierSine n) + ∑' n : ℕ+, coeffs.2 n • fourierCosine n =
          ∑' n : ℕ+, (coeffs.1 n • fourierSine n + coeffs.2 n • fourierCosine n)
      exact (Summable.tsum_add hsineSummable hcosSummable).symm
    exact htarget ▸ hpack
  have htransport :
      HasSum
        (fun i : FourierTrigonometricIndex ↦ coefficientSynthesisFamily coeffs (fourierIndexEquiv i))
        (fourierSeries coeffs) := by
    simpa [Function.comp] using (fourierIndexEquiv.hasSum_iff).2 hbranch
  have hfamily :
      (fun i : FourierTrigonometricIndex ↦ coefficientSynthesisFamily coeffs (fourierIndexEquiv i)) =
        (fun i : FourierTrigonometricIndex ↦
          fourierCoefficientFamily coeffs i • normalizedFourierTrigonometricSystem i) := by
    funext i
    cases i <;> rfl
  rw [← hfamily]
  exact htransport

/-- Helper: rewrite the source-facing Fourier series as Hilbert-basis
synthesis of the packaged coordinate family. -/
theorem fourierSeries_eq_basisSymm (coeffs : FourierCoefficients) :
    fourierSeries coeffs = realFourierHilbertBasis.repr.symm (fourierCoefficientFamily coeffs) := by
  -- The Hilbert-basis synthesis of a coordinate family is uniquely determined by its sum.
  have hsynth :
      HasSum
        (fun i : FourierTrigonometricIndex ↦
          fourierCoefficientFamily coeffs i • realFourierHilbertBasis i)
        (fourierSeries coeffs) := by
    simpa [coe_realFourierHilbertBasis] using hasSum_fourierCoefficientFamily coeffs
  exact
    ((HilbertBasis.hasSum_repr_symm realFourierHilbertBasis (fourierCoefficientFamily coeffs)).unique
      hsynth).symm

/-- Helper: the sine branch of an `ℓ²` family on the trigonometric indices is
square-summable when reindexed by positive frequencies. -/
theorem sineCoordinateFamily_memℓp (coords : ℓ²(FourierTrigonometricIndex, ℝ)) :
    Memℓp (fun n : ℕ+ ↦ coords (.sine (Equiv.pnatEquivNat n))) 2 := by
  let sineEmbedding : ℕ+ → FourierTrigonometricIndex := fun n ↦ .sine (Equiv.pnatEquivNat n)
  -- Restrict the ambient `ℓ²` family to the injective sine branch.
  have hcoords : Summable (fun i : FourierTrigonometricIndex ↦ ‖coords i‖ ^ (2 : ℝ)) := by
    exact (lp.memℓp coords).summable (by norm_num)
  have hsine :
      Summable (fun n : ℕ+ ↦ ‖coords (sineEmbedding n)‖ ^ (2 : ℝ)) := by
    exact hcoords.comp_injective (fun m n h ↦ by simpa [sineEmbedding] using h)
  change Memℓp (fun n : ℕ+ ↦ coords (sineEmbedding n)) 2
  exact memℓp_gen hsine

/-- Helper: the constant mode together with the positive cosine branch forms a
square-summable cosine coefficient sequence on `ℕ`. -/
theorem constantCosineCoordinateFamily_memℓp (coords : ℓ²(FourierTrigonometricIndex, ℝ)) :
    Memℓp
      (fun n : ℕ ↦
        match n with
        | 0 => coords .constant
        | n + 1 => coords (.cosine n))
      2 := by
  let constantCosineEmbedding : ℕ → FourierTrigonometricIndex
    | 0 => .constant
    | n + 1 => .cosine n
  -- Restrict the ambient `ℓ²` family to the injective constant-plus-cosine branch.
  have hcoords : Summable (fun i : FourierTrigonometricIndex ↦ ‖coords i‖ ^ (2 : ℝ)) := by
    exact (lp.memℓp coords).summable (by norm_num)
  have hbranch :
      Summable (fun n : ℕ ↦ ‖coords (constantCosineEmbedding n)‖ ^ (2 : ℝ)) := by
    exact hcoords.comp_injective <| by
      intro m n h
      cases m <;> cases n <;> cases h <;> rfl
  have hfun :
      (fun n : ℕ ↦ coords (constantCosineEmbedding n)) =
        fun n : ℕ ↦
          match n with
          | 0 => coords .constant
          | n + 1 => coords (.cosine n) := by
    funext n
    cases n <;> rfl
  rw [← hfun]
  exact memℓp_gen hbranch

/-- Helper: recover the source-facing real Fourier coefficients of an
`L²([0,1], λ)` function from the coordinates of the real Fourier Hilbert basis. -/
def coefficientsOf (f : L2UnitInterval) : FourierCoefficients :=
  (⟨fun n ↦ realFourierHilbertBasis.repr f (.sine (Equiv.pnatEquivNat n)),
      sineCoordinateFamily_memℓp (realFourierHilbertBasis.repr f)⟩,
    ⟨fun n ↦
        match n with
        | 0 => realFourierHilbertBasis.repr f .constant
        | n + 1 => realFourierHilbertBasis.repr f (.cosine n),
      constantCosineCoordinateFamily_memℓp (realFourierHilbertBasis.repr f)⟩)

/-- Helper: the packaged coordinate family of `coefficientsOf f` is exactly the
Hilbert-basis coordinate family of `f`. -/
theorem fourierCoefficientFamily_coefficientsOf (f : L2UnitInterval) :
    fourierCoefficientFamily (coefficientsOf f) = realFourierHilbertBasis.repr f := by
  -- Each branch of the packaged source coefficients matches the corresponding Hilbert-basis branch.
  ext i <;> cases i <;> simp [coefficientsOf, fourierCoefficientFamily]

/-- Helper: synthesizing the recovered coefficient vector reproduces the
original `L²` function. -/
theorem coefficientsOf_spec (f : L2UnitInterval) :
    fourierSeries (coefficientsOf f) = f := by
  -- Once the coefficient family agrees with the Hilbert-basis coordinates, synthesis is immediate.
  calc
    fourierSeries (coefficientsOf f)
        = realFourierHilbertBasis.repr.symm (fourierCoefficientFamily (coefficientsOf f)) := by
            exact fourierSeries_eq_basisSymm (coefficientsOf f)
    _ = realFourierHilbertBasis.repr.symm (realFourierHilbertBasis.repr f) := by
          rw [fourierCoefficientFamily_coefficientsOf]
    _ = f := by
          simp

-- Proof sketch: first show existence of a Fourier expansion by density of step functions, then
-- prove uniqueness from orthogonality of the trigonometric system. Equivalently,
-- this is the source-facing coefficient statement obtained from the canonical Hilbert basis
-- `realFourierHilbertBasis`, with sine coefficients indexed by `ℕ+`.
/-- Helper: every real `L²` function on `[0,1]` has a unique Fourier expansion with
square-summable sine coefficients `a : ℓ²(ℕ+, ℝ)` and cosine coefficients `b : ℓ²(ℕ, ℝ)`, where
`b 0` is the coefficient of the normalized constant mode `1` (equivalently,
`(b 0 / Real.sqrt 2)` is the coefficient of `C₀`). -/
theorem existsUnique_fourierSeries_coefficients (f : L2UnitInterval) :
    ∃! coeffs : FourierCoefficients, fourierSeries coeffs = f := by
  refine ⟨coefficientsOf f, coefficientsOf_spec f, ?_⟩
  intro coeffs hcoeffs
  -- Apply the Hilbert-basis coordinate map once; the packaged coefficient family is then forced.
  have hfamily :
      fourierCoefficientFamily coeffs = realFourierHilbertBasis.repr f := by
    simpa [fourierSeries_eq_basisSymm] using congrArg realFourierHilbertBasis.repr hcoeffs
  have hfamily' :
      fourierCoefficientFamily coeffs = fourierCoefficientFamily (coefficientsOf f) := by
    rw [hfamily, fourierCoefficientFamily_coefficientsOf]
  -- Compare the sine branch and the two cosine branches to recover the source coefficient pair.
  apply Prod.ext
  · ext n
    have hbranch :=
      congrArg
        (fun g : ℓ²(FourierTrigonometricIndex, ℝ) ↦
          g (FourierTrigonometricIndex.sine (Equiv.pnatEquivNat n)))
        hfamily'
    simpa [fourierCoefficientFamily] using hbranch
  · ext n
    cases n with
    | zero =>
        have hbranch :=
          congrArg
            (fun g : ℓ²(FourierTrigonometricIndex, ℝ) ↦
              g FourierTrigonometricIndex.constant)
            hfamily'
        simpa [fourierCoefficientFamily] using hbranch
    | succ n =>
        have hbranch :=
          congrArg
            (fun g : ℓ²(FourierTrigonometricIndex, ℝ) ↦
              g (FourierTrigonometricIndex.cosine n))
            hfamily'
        simpa [fourierCoefficientFamily] using hbranch

/-- The linear Fourier-synthesis map from square-summable real coefficients to `L²([0,1], λ)`. -/
def fourierSeriesLinearMap : FourierCoefficients →ₗ[ℝ] L2UnitInterval where
  toFun := fourierSeries
  map_add' := by
    intro coeffs₁ coeffs₂
    -- Route correction: with summability now proved after the Hilbert-basis block, linearity
    -- reduces to pointwise additivity of the summands plus `tsum_add`.
    have hsum₁ : Summable (fourierSeriesSummand coeffs₁) := fourierSeries_summable coeffs₁
    have hsum₂ : Summable (fourierSeriesSummand coeffs₂) := fourierSeries_summable coeffs₂
    calc
      fourierSeries (coeffs₁ + coeffs₂)
          = ((coeffs₁ + coeffs₂).2 0) • fourierConstant
              + ∑' n : ℕ+, (fourierSeriesSummand coeffs₁ n + fourierSeriesSummand coeffs₂ n) := by
                  simp [fourierSeries, fourierSeriesSummand_add]
      _ = (coeffs₁.2 0 + coeffs₂.2 0) • fourierConstant
            + ∑' n : ℕ+, (fourierSeriesSummand coeffs₁ n + fourierSeriesSummand coeffs₂ n) := by
              rfl
      _ = (coeffs₁.2 0 • fourierConstant + ∑' n : ℕ+, fourierSeriesSummand coeffs₁ n) +
            (coeffs₂.2 0 • fourierConstant + ∑' n : ℕ+, fourierSeriesSummand coeffs₂ n) := by
              rw [Summable.tsum_add hsum₁ hsum₂]
              rw [add_smul]
              abel_nf
      _ = fourierSeries coeffs₁ + fourierSeries coeffs₂ := by
            simp [fourierSeries]
  map_smul' := by
    intro c coeffs
    -- After isolating homogeneity of each summand, `tsum_smul` finishes the synthesis-map proof.
    have hsum : Summable (fourierSeriesSummand coeffs) := fourierSeries_summable coeffs
    calc
      fourierSeries (c • coeffs)
          = (c * coeffs.2 0) • fourierConstant + ∑' n : ℕ+, c • fourierSeriesSummand coeffs n := by
              simp [fourierSeries, fourierSeriesSummand_smul, Pi.smul_apply]
      _ = c • (coeffs.2 0 • fourierConstant + ∑' n : ℕ+, fourierSeriesSummand coeffs n) := by
            rw [hsum.tsum_const_smul c]
            simp [smul_add, smul_smul]
      _ = c • fourierSeries coeffs := by
            simp [fourierSeries]

/-- The source-facing space `W` of real Fourier series on `[0,1]`. -/
def W : Submodule ℝ L2UnitInterval :=
  LinearMap.range fourierSeriesLinearMap

/-- Companion: every real Fourier series belongs to the space `W`. -/
theorem fourierSeries_mem_W (coeffs : FourierCoefficients) :
    fourierSeries coeffs ∈ W :=
  LinearMap.mem_range_self fourierSeriesLinearMap coeffs

/-- Companion: the Fourier-series subspace `W` exhausts `L²([0,1], λ)`. -/
theorem W_eq_top : W = ⊤ := by
  -- Every `L²` function has a Fourier expansion, so the synthesis-map range is all of `L²`.
  rw [Submodule.eq_top_iff']
  intro f
  rcases existsUnique_fourierSeries_coefficients f with ⟨coeffs, hcoeffs, _⟩
  exact ⟨coeffs, hcoeffs⟩

/-- Part (3) of Exercise 7.3.1: the vector space `W` of Fourier series is a closed linear subspace of
`L²([0,1], λ)`. -/
theorem W_isClosed : IsClosed (W : Set L2UnitInterval) := by
  simp [W_eq_top]

/-- Part (1) of Exercise 7.3.1: the functions `C₀, Sₙ, Cₙ` with `n ∈ ℕ+` form an orthogonal system in
`L²([0,1], λ)`. -/
theorem fourierTrigonometricSystem_pairwise_orthogonal :
    Pairwise fun i j : FourierTrigonometricIndex ↦
      ⟪fourierTrigonometricSystem i, fourierTrigonometricSystem j⟫_ℝ = 0 :=
  by
  intro i j hij
  -- The nonconstant modes already belong to the normalized orthonormal family.
  have horth := normalizedFourierTrigonometricSystem_orthonormal
  cases i with
  | constant =>
      cases j with
      | constant =>
          exact (hij rfl).elim
      | sine n =>
          -- Route correction: only the constant mode differs from the normalized family, by a scalar.
          have hzero : ⟪fourierConstant, fourierSine (n + 1)⟫_ℝ = 0 := by
            simpa [normalizedFourierTrigonometricSystem] using
              horth.inner_eq_zero
                (show FourierTrigonometricIndex.constant ≠ FourierTrigonometricIndex.sine n by simp)
          calc
            ⟪fourierTrigonometricSystem .constant, fourierTrigonometricSystem (.sine n)⟫_ℝ
                = ⟪Real.sqrt 2 • fourierConstant, fourierSine (n + 1)⟫_ℝ := by
                    simp [fourierTrigonometricSystem, fourierCosine_zero_eq_smul_fourierConstant]
            _ = Real.sqrt 2 * ⟪fourierConstant, fourierSine (n + 1)⟫_ℝ := by
                  rw [real_inner_smul_left]
            _ = 0 := by simp [hzero]
      | cosine n =>
          have hzero : ⟪fourierConstant, fourierCosine (n + 1)⟫_ℝ = 0 := by
            simpa [normalizedFourierTrigonometricSystem] using
              horth.inner_eq_zero
                (show FourierTrigonometricIndex.constant ≠ FourierTrigonometricIndex.cosine n by simp)
          calc
            ⟪fourierTrigonometricSystem .constant, fourierTrigonometricSystem (.cosine n)⟫_ℝ
                = ⟪Real.sqrt 2 • fourierConstant, fourierCosine (n + 1)⟫_ℝ := by
                    simp [fourierTrigonometricSystem, fourierCosine_zero_eq_smul_fourierConstant]
            _ = Real.sqrt 2 * ⟪fourierConstant, fourierCosine (n + 1)⟫_ℝ := by
                  rw [real_inner_smul_left]
            _ = 0 := by simp [hzero]
  | sine m =>
      cases j with
      | constant =>
          have hzero : ⟪fourierSine (m + 1), fourierConstant⟫_ℝ = 0 := by
            simpa [normalizedFourierTrigonometricSystem] using
              horth.inner_eq_zero
                (show FourierTrigonometricIndex.sine m ≠ FourierTrigonometricIndex.constant by simp)
          calc
            ⟪fourierTrigonometricSystem (.sine m), fourierTrigonometricSystem .constant⟫_ℝ
                = ⟪fourierSine (m + 1), Real.sqrt 2 • fourierConstant⟫_ℝ := by
                    simp [fourierTrigonometricSystem, fourierCosine_zero_eq_smul_fourierConstant]
            _ = Real.sqrt 2 * ⟪fourierSine (m + 1), fourierConstant⟫_ℝ := by
                  rw [real_inner_smul_right]
            _ = 0 := by simp [hzero]
      | sine n =>
          simpa [fourierTrigonometricSystem, normalizedFourierTrigonometricSystem] using
            horth.inner_eq_zero
              (show FourierTrigonometricIndex.sine m ≠ FourierTrigonometricIndex.sine n from hij)
      | cosine n =>
          simpa [fourierTrigonometricSystem, normalizedFourierTrigonometricSystem] using
            horth.inner_eq_zero
              (show FourierTrigonometricIndex.sine m ≠ FourierTrigonometricIndex.cosine n by simp)
  | cosine m =>
      cases j with
      | constant =>
          have hzero : ⟪fourierCosine (m + 1), fourierConstant⟫_ℝ = 0 := by
            simpa [normalizedFourierTrigonometricSystem] using
              horth.inner_eq_zero
                (show FourierTrigonometricIndex.cosine m ≠ FourierTrigonometricIndex.constant by simp)
          calc
            ⟪fourierTrigonometricSystem (.cosine m), fourierTrigonometricSystem .constant⟫_ℝ
                = ⟪fourierCosine (m + 1), Real.sqrt 2 • fourierConstant⟫_ℝ := by
                    simp [fourierTrigonometricSystem, fourierCosine_zero_eq_smul_fourierConstant]
            _ = Real.sqrt 2 * ⟪fourierCosine (m + 1), fourierConstant⟫_ℝ := by
                  rw [real_inner_smul_right]
            _ = 0 := by simp [hzero]
      | sine n =>
          simpa [fourierTrigonometricSystem, normalizedFourierTrigonometricSystem] using
            horth.inner_eq_zero
              (show FourierTrigonometricIndex.cosine m ≠ FourierTrigonometricIndex.sine n by simp)
      | cosine n =>
          simpa [fourierTrigonometricSystem, normalizedFourierTrigonometricSystem] using
            horth.inner_eq_zero
              (show FourierTrigonometricIndex.cosine m ≠ FourierTrigonometricIndex.cosine n from hij)

/-- Helper for Exercise 7.3.1: the constant branch of the coefficient norm-square family sums to
`b 0 ^ 2`. -/
lemma coefficientSumFamily_constant_normSq_hasSum (coeffs : FourierCoefficients) :
    HasSum (fun u : Unit ↦ ‖coefficientSumFamily coeffs (Sum.inl u)‖ ^ (2 : ℝ))
      (coeffs.2 0 ^ 2) := by
  -- The constant branch is a one-point family, and `‖x‖ ^ 2 = x ^ 2` over `ℝ`.
  simpa [coefficientSumFamily, Real.norm_eq_abs, sq_abs] using
    (hasSum_fintype (fun u : Unit ↦ ‖coefficientSumFamily coeffs (Sum.inl u)‖ ^ (2 : ℝ)))

/-- Helper for Exercise 7.3.1: the sine branch of the coefficient norm-square family is the
nat-indexed reindexing of the positive-frequency sine squares. -/
lemma coefficientSumFamily_sine_normSq_hasSum (coeffs : FourierCoefficients) :
    HasSum (fun n : ℕ ↦ ‖coefficientSumFamily coeffs (Sum.inr (Sum.inl n))‖ ^ (2 : ℝ))
      (∑' n : ℕ+, coeffs.1 n ^ 2) := by
  -- Transport the square-summable sine coefficients through `ℕ ≃ ℕ+` once.
  simpa [Function.comp, coefficientSumFamily, Real.norm_eq_abs, sq_abs] using
    (pnatEquivNat.symm.hasSum_iff).2 (((lp.memℓp coeffs.1).summable (by norm_num)).hasSum)

/-- Helper for Exercise 7.3.1: the cosine branch of the coefficient norm-square family is the
nat-indexed reindexing of the positive-frequency cosine squares. -/
lemma coefficientSumFamily_cosine_normSq_hasSum (coeffs : FourierCoefficients) :
    HasSum (fun n : ℕ ↦ ‖coefficientSumFamily coeffs (Sum.inr (Sum.inr n))‖ ^ (2 : ℝ))
      (∑' n : ℕ+, coeffs.2 n ^ 2) := by
  -- Use the already packaged positive cosine coefficient family on `ℕ+`.
  simpa [Function.comp, coefficientSumFamily, Real.norm_eq_abs, sq_abs] using
    (pnatEquivNat.symm.hasSum_iff).2
      (((positiveCosineCoefficients_memℓp coeffs).summable (by norm_num)).hasSum)

/-- Helper for Exercise 7.3.1: combining the sine and cosine coefficient norm-square branches gives
the full right-hand branch on `ℕ ⊕ ℕ`. -/
lemma coefficientSumFamily_right_normSq_hasSum (coeffs : FourierCoefficients) :
    HasSum (fun i : ℕ ⊕ ℕ ↦ ‖coefficientSumFamily coeffs (Sum.inr i)‖ ^ (2 : ℝ))
      ((∑' n : ℕ+, coeffs.1 n ^ 2) + ∑' n : ℕ+, coeffs.2 n ^ 2) := by
  -- Assemble the two positive-frequency scalar branches before adding the constant term.
  exact (coefficientSumFamily_sine_normSq_hasSum coeffs).sum
    (coefficientSumFamily_cosine_normSq_hasSum coeffs)

-- Proof sketch: expand `f` in the orthogonal trigonometric system, apply the Pythagorean theorem
-- in the Hilbert space `L²([0,1], λ)`, and identify the squared norm of the coefficient vector.
/-- Helper: compute the squared `ℓ²` norm of the packaged coefficient family. -/
theorem fourierCoefficientFamily_norm_sq (coeffs : FourierCoefficients) :
    ‖fourierCoefficientFamily coeffs‖ ^ 2 =
      coeffs.2 0 ^ 2 + ∑' n : ℕ+, (coeffs.1 n ^ 2 + coeffs.2 n ^ 2) := by
  -- Route correction: keep the square-sum in the explicit branch family until the final
  -- `fourierIndexEquiv` transport, then combine the positive-frequency branches once.
  have hbranch :
      HasSum (fun i : Unit ⊕ (ℕ ⊕ ℕ) ↦ ‖coefficientSumFamily coeffs i‖ ^ (2 : ℝ))
        (coeffs.2 0 ^ 2 + ((∑' n : ℕ+, coeffs.1 n ^ 2) + ∑' n : ℕ+, coeffs.2 n ^ 2)) := by
    exact (coefficientSumFamily_constant_normSq_hasSum coeffs).sum
      (coefficientSumFamily_right_normSq_hasSum coeffs)
  have htransport :
      HasSum
        (fun i : FourierTrigonometricIndex ↦ ‖coefficientSumFamily coeffs (fourierIndexEquiv i)‖ ^ (2 : ℝ))
        (coeffs.2 0 ^ 2 + ((∑' n : ℕ+, coeffs.1 n ^ 2) + ∑' n : ℕ+, coeffs.2 n ^ 2)) := by
    simpa [Function.comp] using (fourierIndexEquiv.hasSum_iff).2 hbranch
  have hfamily :
      (fun i : FourierTrigonometricIndex ↦ ‖coefficientSumFamily coeffs (fourierIndexEquiv i)‖ ^ (2 : ℝ)) =
        (fun i : FourierTrigonometricIndex ↦ ‖fourierCoefficientFamily coeffs i‖ ^ (2 : ℝ)) := by
    funext i
    cases i <;> rfl
  have hsine :
      Summable (fun n : ℕ+ ↦ coeffs.1 n ^ 2) := by
    simpa [Real.norm_eq_abs, sq_abs] using ((lp.memℓp coeffs.1).summable (by norm_num))
  have hcos :
      Summable (fun n : ℕ+ ↦ coeffs.2 n ^ 2) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      ((positiveCosineCoefficients_memℓp coeffs).summable (by norm_num))
  calc
    ‖fourierCoefficientFamily coeffs‖ ^ 2
        = ∑' i : FourierTrigonometricIndex, ‖fourierCoefficientFamily coeffs i‖ ^ (2 : ℝ) := by
            simpa using
              (lp.hasSum_norm (by norm_num) (fourierCoefficientFamily coeffs)).tsum_eq.symm
    _ = coeffs.2 0 ^ 2 + ((∑' n : ℕ+, coeffs.1 n ^ 2) + ∑' n : ℕ+, coeffs.2 n ^ 2) := by
          rw [← hfamily]
          exact htransport.tsum_eq
    _ = coeffs.2 0 ^ 2 + ∑' n : ℕ+, (coeffs.1 n ^ 2 + coeffs.2 n ^ 2) := by
          congr 1
          exact (Summable.tsum_add hsine hcos).symm

/-- Companion: Parseval's identity for the real Fourier expansion on `[0,1]`. -/
theorem fourierSeries_parseval {f : L2UnitInterval} {coeffs : FourierCoefficients}
    (hf : fourierSeries coeffs = f) :
    ‖f‖ ^ 2 = coeffs.2 0 ^ 2 + ∑' n : ℕ+, (coeffs.1 n ^ 2 + coeffs.2 n ^ 2) := by
  -- Route correction: Parseval is proved in the Hilbert-basis coordinate family, not from the
  -- product norm on `FourierCoefficients`.
  have hfamily :
      fourierCoefficientFamily coeffs = realFourierHilbertBasis.repr f := by
    simpa [fourierSeries_eq_basisSymm] using congrArg realFourierHilbertBasis.repr hf
  have hnorm : ‖realFourierHilbertBasis.repr f‖ = ‖f‖ := by
    simpa using realFourierHilbertBasis.repr.norm_map f
  calc
    ‖f‖ ^ 2 = ‖realFourierHilbertBasis.repr f‖ ^ 2 := by
      rw [← hnorm]
    _ = ‖fourierCoefficientFamily coeffs‖ ^ 2 := by
      rw [← hfamily]
    _ = coeffs.2 0 ^ 2 + ∑' n : ℕ+, (coeffs.1 n ^ 2 + coeffs.2 n ^ 2) :=
      fourierCoefficientFamily_norm_sq coeffs

/-- Exercise 7.3.1: for every `f ∈ L²([0,1], λ)`, there exists a unique coefficient vector
`coeffs = (a, b)` with `fourierSeries coeffs = f`, and these coefficients satisfy Parseval's
identity `‖f‖ ^ 2 = b 0 ^ 2 + ∑' n : ℕ+, (a n ^ 2 + b n ^ 2)`. -/
theorem existsUnique_fourierSeries_coefficients_parseval (f : L2UnitInterval) :
    ∃! coeffs : FourierCoefficients,
      fourierSeries coeffs = f ∧
        ‖f‖ ^ 2 = coeffs.2 0 ^ 2 + ∑' n : ℕ+, (coeffs.1 n ^ 2 + coeffs.2 n ^ 2) := by
  rcases existsUnique_fourierSeries_coefficients f with ⟨coeffs, hcoeffs, huniq⟩
  refine ⟨coeffs, ?_, ?_⟩
  · -- The previously constructed coefficient vector already satisfies Parseval.
    exact ⟨hcoeffs, fourierSeries_parseval hcoeffs⟩
  · intro other hother
    -- Uniqueness comes from the already-established uniqueness of the Fourier synthesis map.
    exact huniq other hother.1
