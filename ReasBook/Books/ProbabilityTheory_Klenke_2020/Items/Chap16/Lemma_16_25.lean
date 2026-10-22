/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Example_16_19
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Lemma_16_25.StableLevyCentering

open Filter MeasureTheory ProbabilityTheory MeasureTheory.ProbabilityMeasure
open scoped MeasureTheory NNReal

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- Helper for Lemma 16.25: a continuous zero-free characteristic function normalized by
`φ 0 = 1` admits a unique continuous logarithmic lift through `Complex.exp`. -/
private lemma existsUniqueContinuousExpLiftLocal {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφne : ∀ x : ℝ, φ x ≠ 0) (hφ0 : φ 0 = 1) :
    ∃! Ψ : C(ℝ, ℂ), Ψ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ t) = φ t := by
  let f : C(ℝ, {z : ℂ // z ≠ 0}) :=
    ⟨fun t ↦ ⟨φ t, hφne t⟩, hφc.subtype_mk _⟩
  have he :
      (fun z : ℂ ↦ (⟨Complex.exp z, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) 0 = f 0 := by
    ext
    simp [f, hφ0]
  rcases Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 he with
    ⟨Ψ, hΨ, hΨuniq⟩
  refine ⟨Ψ, ?_, ?_⟩
  · rcases hΨ with ⟨hΨ0, hΨexp⟩
    refine ⟨hΨ0, ?_⟩
    intro t
    simpa [f] using congrArg Subtype.val (congr_fun hΨexp t)
  · intro Ψ' hΨ'
    apply hΨuniq
    rcases hΨ' with ⟨hΨ'0, hΨ'exp⟩
    refine ⟨hΨ'0, ?_⟩
    funext t
    change (⟨Complex.exp (Ψ' t), (Ψ' t).exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) = f t
    apply Subtype.ext
    simpa [f] using hΨ'exp t

/-- Helper for Lemma 16.25: on `ℝ`, the inner product is ordinary multiplication. -/
private lemma realInner_eq_mul (x y : ℝ) : inner ℝ x y = x * y := by
  have h := real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y
  simp [Real.norm_eq_abs] at h
  nlinarith

/-- Helper for Lemma 16.25: vanishing Gaussian and Lévy terms force the represented law to be the
Dirac mass at the drift coefficient. -/
theorem eq_diracProba_of_zeroGaussian_zeroLevy
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (hσ : τ.sigma2 = 0) (hν : τ.ν = 0) :
    μ = diracProba τ.b := by
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_charFun ?_
  ext t
  -- Proof comment: with no Gaussian or jump term, the Lévy--Khintchin exponent is exactly the
  -- characteristic exponent of the point mass at `τ.b`.
  simpa [MeasureTheory.diracProba, MeasureTheory.charFun_dirac, realInner_eq_mul,
    levyKhinchinExponent, levyKhinchinExponentWithCentering, hσ, hν] using hτ.charFun_eq_exp t

/-- Helper for Lemma 16.25: when the Lévy measure vanishes, the convolution-power and affine-image
exponents are the same normalized continuous logarithmic lift of `charFun (μ ^ n)`. -/
theorem zeroLevyExponent_eq_of_broadStableScaling
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (hν : τ.ν = 0) :
    ∀ n : ℕ+, ∀ t : ℝ,
      (((-(((n : ℝ) * τ.sigma2) / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          ((((n : ℝ) * τ.b * t : ℝ) : ℂ) * Complex.I) =
        (((-(((a n) ^ (2 : ℕ) * τ.sigma2) / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          ((((a n * τ.b + d n) * t : ℝ) : ℂ) * Complex.I) := by
  intro n
  let Ψpow : C(ℝ, ℂ) :=
    ⟨fun t : ℝ ↦
      (((-(((n : ℝ) * τ.sigma2) / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
        ((((n : ℝ) * τ.b * t : ℝ) : ℂ) * Complex.I), by continuity⟩
  let Ψmap : C(ℝ, ℂ) :=
    ⟨fun t : ℝ ↦
      (((-(((a n) ^ (2 : ℕ) * τ.sigma2) / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
        ((((a n * τ.b + d n) * t : ℝ) : ℂ) * Complex.I), by continuity⟩
  let μpow : Measure ℝ := ((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ)
  have hpowExp :
      ∀ t : ℝ,
        Complex.exp (Ψpow t) = charFun μpow t := by
    intro t
    have hΨpow :
        Ψpow t = ((n : ℕ) : ℂ) * levyKhinchinExponent τ t := by
      -- Proof comment: with `τ.ν = 0`, the `n`th power exponent is exactly the scalar multiple
      -- `n ψ(t)`.
      simp [Ψpow, levyKhinchinExponent, levyKhinchinExponentWithCentering, hν]
      ring
    calc
      Complex.exp (Ψpow t)
          = Complex.exp (((n : ℕ) : ℂ) * levyKhinchinExponent τ t) := by rw [hΨpow]
      _ = Complex.exp (levyKhinchinExponent τ t) ^ (n : ℕ) := by
            rw [Complex.exp_nat_mul]
      _ = charFun (μ : Measure ℝ) t ^ (n : ℕ) := by rw [hτ.charFun_eq_exp]
      _ = charFun μpow t := by
            simpa using
              (congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow μ (n : ℕ))).symm
  have hmapExp :
      ∀ t : ℝ,
        Complex.exp (Ψmap t) = charFun μpow t := by
    intro t
    have hΨmap :
        Ψmap t =
          levyKhinchinExponent τ (a n * t) + ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
      -- Proof comment: when `τ.ν = 0`, the affine image changes only the Gaussian coefficient
      -- and adds the translated linear phase.
      simp [Ψmap, levyKhinchinExponent, levyKhinchinExponentWithCentering, hν]
      ring
    have hchar_map :
        charFun
            ((map μ (measurable_affineMap (a n) (d n)).aemeasurable : ProbabilityMeasure ℝ) :
              Measure ℝ) t =
          charFun (μ : Measure ℝ) (a n * t) *
            Complex.exp ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
      -- Proof comment: decompose the affine map into scaling followed by translation.
      rw [ProbabilityMeasure.toMeasure_map]
      have hcomp :
          Measure.map (fun x : ℝ ↦ a n * x + d n) (μ : Measure ℝ) =
            Measure.map (fun x : ℝ ↦ x + d n) (Measure.map (fun x : ℝ ↦ a n * x) (μ : Measure ℝ)) := by
        rw [show (fun x : ℝ ↦ a n * x + d n) =
            (fun x : ℝ ↦ x + d n) ∘ fun x : ℝ ↦ a n * x from rfl, ← Measure.map_map]
        all_goals fun_prop
      rw [hcomp, MeasureTheory.charFun_map_add_const]
      rw [MeasureTheory.charFun_map_mul]
      simp [realInner_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    calc
      Complex.exp (Ψmap t)
          = Complex.exp (levyKhinchinExponent τ (a n * t)) *
              Complex.exp ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
                rw [hΨmap, Complex.exp_add]
      _ = charFun (μ : Measure ℝ) (a n * t) *
            Complex.exp ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
              rw [hτ.charFun_eq_exp]
      _ = charFun
            ((map μ (measurable_affineMap (a n) (d n)).aemeasurable : ProbabilityMeasure ℝ) :
              Measure ℝ) t := by
              rw [hchar_map]
      _ = charFun μpow t := by
            simpa [μpow, hscale n]
  have hchar_nonzero : ∀ t : ℝ, charFun μpow t ≠ 0 := by
    intro t
    rw [← hpowExp t]
    exact Complex.exp_ne_zero _
  let φpow : ℝ → ℂ := fun t ↦ charFun μpow t
  obtain ⟨Ψ, hΨ, huniq⟩ :=
    existsUniqueContinuousExpLiftLocal
      (by
        simpa [φpow] using
          (MeasureTheory.continuous_charFun : Continuous (charFun μpow)))
      hchar_nonzero
      (by simpa [φpow] using MeasureTheory.charFun_zero μpow)
  have hpow_eq_Ψ : Ψpow = Ψ := by
    apply huniq
    constructor
    · -- Proof comment: the power-side polynomial lift is normalized at `0`.
      simp [Ψpow]
    · exact hpowExp
  have hmap_eq_Ψ : Ψmap = Ψ := by
    apply huniq
    constructor
    · -- Proof comment: the affine-side polynomial lift is normalized at `0`.
      simp [Ψmap]
    · exact hmapExp
  have hEq : Ψpow = Ψmap := hpow_eq_Ψ.trans hmap_eq_Ψ.symm
  intro t
  -- Proof comment: evaluate the equality of continuous lifts at the requested frequency.
  exact congrArg (fun f : C(ℝ, ℂ) ↦ f t) hEq

/-- Helper for Lemma 16.25: if a positive convolution power is a Dirac mass, then the original
law is already Dirac. -/
private lemma eq_diracProba_of_pow_eq_diracProbaLocal
    {μ : ProbabilityMeasure ℝ} {n : ℕ+} {x : ℝ}
    (hpow : μ ^ (n : ℕ) = diracProba x) :
    ∃ y : ℝ, μ = diracProba y := by
  let t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have ht_antitone : Antitone fun k ↦ |t k| := by
    intro m n hmn
    -- Proof comment: the reciprocal sequence is decreasing and nonnegative.
    simp only [t]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
      (Nat.one_div_le_one_div hmn : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1))
  have ht_zero : Tendsto (fun k ↦ |t k|) atTop (nhds 0) := by
    -- Proof comment: the reciprocal sequence tends to `0`.
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
    Measure.eq_dirac_of_charFun_norm_eq_one_along_zero ht_antitone ht_zero ht_nonzero hφ_unit
  -- Proof comment: upgrade the measure-level Dirac conclusion back to a probability measure.
  refine ⟨y, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  simpa [MeasureTheory.diracProba] using hy

/-- Helper for Lemma 16.25: every affine broad-stability scale is strictly positive. -/
private lemma scalePosOfBroadStableLocal
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
    -- Proof comment: a zero slope collapses the affine image to a Dirac mass.
    rw [hscale n, hzero]
    apply ProbabilityMeasure.toMeasure_injective
    ext s hs
    simp [hs]
  rcases eq_diracProba_of_pow_eq_diracProbaLocal hdiracPow with ⟨x, hx⟩
  exact hnotDirac x hx

/-- Helper for Lemma 16.25: rewrite a Lévy--Khintchin representation along an equality of laws. -/
private lemma hasLevyKhinchinRepresentation_congrLocal
    {μ ν : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hμν : μ = ν) (hτ : HasLevyKhinchinRepresentation μ τ) :
    HasLevyKhinchinRepresentation ν τ := by
  simpa [hμν] using hτ

/-- Helper for Lemma 16.25: a Lévy--Khintchin representation has zero-free characteristic
function. -/
private lemma charFun_ne_zero_of_hasLevyKhinchinRepresentationLocal
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∀ t : ℝ, charFun (μ : Measure ℝ) t ≠ 0 := by
  intro t
  rw [hτ.charFun_eq_exp t]
  exact Complex.exp_ne_zero _

/-- Helper for Lemma 16.25: every Lévy--Khintchin exponent vanishes at the origin. -/
private lemma levyKhinchinExponent_zeroLocal (τ : LevyKhinchinTriple) :
    levyKhinchinExponent τ 0 = 0 := by
  -- Proof comment: each term in the exponent contains a factor of `t`, so `t = 0` kills them.
  simp [levyKhinchinExponent, levyKhinchinExponentWithCentering]

/-- Helper for Lemma 16.25: the centered jump kernel at frequency `t`. -/
private def levyKhinchinCanonicalKernelLocal (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
      (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)

/-- Helper for Lemma 16.25: the local centered jump kernel is measurable. -/
private lemma measurable_levyKhinchinCanonicalKernelLocal (t : ℝ) :
    Measurable (levyKhinchinCanonicalKernelLocal t) := by
  -- Proof comment: the kernel is built from measurable algebraic operations and the complex
  -- exponential.
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

/-- Helper for Lemma 16.25: inside the unit ball, `min (x², 1)` is just `x²`. -/
private lemma sqMinOne_eq_sq_of_abs_lt_oneLocal {x : ℝ} (hx : |x| < 1) :
    min (x ^ (2 : ℕ)) 1 = x ^ (2 : ℕ) := by
  -- Proof comment: on `|x| < 1`, the truncation does not cut off the quadratic term.
  refine min_eq_left ?_
  exact le_of_lt ((sq_lt_one_iff_abs_lt_one x).2 hx)

/-- Helper for Lemma 16.25: outside the unit ball, `min (x², 1)` saturates at `1`. -/
private lemma sqMinOne_eq_one_of_one_le_absLocal {x : ℝ} (hx : 1 ≤ |x|) :
    min (x ^ (2 : ℕ)) 1 = 1 := by
  -- Proof comment: once `|x| ≥ 1`, the truncation is exactly the constant `1`.
  refine min_eq_right ?_
  have hxSq : 1 ≤ |x| * |x| := by
    nlinarith
  simpa [pow_two, sq_abs] using hxSq

/-- Helper for Lemma 16.25: `|t x|²` factors as `|t|² x²`. -/
private lemma abs_mul_sqLocal (t x : ℝ) :
    |t * x| ^ (2 : ℕ) = |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by
  -- Proof comment: absolute value commutes with multiplication, and squaring removes signs.
  rw [abs_mul, mul_pow, sq_abs, sq_abs]

/-- Helper for Lemma 16.25: on the large branch, `2 + |t x|` is controlled by `3 |t x|²`. -/
private lemma two_add_abs_mul_le_three_abs_mul_sqLocal {t x : ℝ} (hlarge : 1 < |t * x|) :
    2 + |t * x| ≤ 3 * |t * x| ^ (2 : ℕ) := by
  -- Proof comment: both summands are then bounded by a constant multiple of the square.
  nlinarith [le_of_lt hlarge, sq_nonneg (|t * x|)]

/-- Helper for Lemma 16.25: `exp (i t x) - 1` has norm at most `2`. -/
private lemma norm_exp_sub_one_mul_I_le_twoLocal (t x : ℝ) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 2 := by
  -- Proof comment: `exp (i y)` lies on the unit circle, so its distance to `1` is at most `2`.
  calc
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 1 + 1 := by
          rw [Complex.norm_exp_ofReal_mul_I]
          simp
    _ = 2 := by norm_num

/-- Helper for Lemma 16.25: the centered oscillatory remainder is bounded by `2 + |t x|`. -/
private lemma norm_exp_sub_one_sub_id_mul_I_le_two_add_abs_mulLocal (t x : ℝ) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - (((t * x : ℝ) : ℂ) * Complex.I)‖ ≤
      2 + |t * x| := by
  -- Proof comment: separate the nonlinear remainder into `exp (i t x) - 1` and the linear
  -- correction term.
  calc
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - (((t * x : ℝ) : ℂ) * Complex.I)‖
        ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ +
            ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ := norm_sub_le _ _
    _ ≤ 2 + |t * x| := by
      gcongr
      · exact norm_exp_sub_one_mul_I_le_twoLocal t x
      · simp [Complex.norm_I, Real.norm_eq_abs]

/-- Helper for Lemma 16.25: the local canonical kernel is dominated by the standard `min (x²,1)`
integrand. -/
private lemma norm_levyKhinchinCanonicalKernelLocal_le (t x : ℝ) :
    ‖levyKhinchinCanonicalKernelLocal t x‖ ≤
      max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
  by_cases hx : |x| < 1
  · by_cases htx : |t * x| ≤ 1
    · have hquad :
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - (((t * x : ℝ) : ℂ) * Complex.I)‖ ≤
            |t * x| ^ (2 : ℕ) := by
        simpa [Real.norm_eq_abs] using
          Complex.norm_exp_sub_one_sub_id_le (x := (((t * x : ℝ) : ℂ) * Complex.I)) (by
            simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs] using htx)
      calc
        ‖levyKhinchinCanonicalKernelLocal t x‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - (((t * x : ℝ) : ℂ) * Complex.I)‖ := by
                simp [levyKhinchinCanonicalKernelLocal, levyKhinchinCanonicalCentering, hx]
        _ ≤ |t * x| ^ (2 : ℕ) := hquad
        _ = |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := abs_mul_sqLocal t x
        _ ≤ 3 * |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by
              nlinarith [sq_nonneg (|t|), sq_nonneg x]
        _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 * x ^ (2 : ℕ) := by
              gcongr
              exact le_max_left _ _
        _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
              rw [sqMinOne_eq_sq_of_abs_lt_oneLocal hx]
    · have hlarge : 1 < |t * x| := lt_of_not_ge htx
      calc
        ‖levyKhinchinCanonicalKernelLocal t x‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - (((t * x : ℝ) : ℂ) * Complex.I)‖ := by
                simp [levyKhinchinCanonicalKernelLocal, levyKhinchinCanonicalCentering, hx]
        _ ≤ 2 + |t * x| := norm_exp_sub_one_sub_id_mul_I_le_two_add_abs_mulLocal t x
        _ ≤ 3 * |t * x| ^ (2 : ℕ) := two_add_abs_mul_le_three_abs_mul_sqLocal hlarge
        _ = 3 * (|t| ^ (2 : ℕ) * x ^ (2 : ℕ)) := by rw [abs_mul_sqLocal]
        _ = 3 * |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by ring
        _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 * x ^ (2 : ℕ) := by
              gcongr
              exact le_max_left _ _
        _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
              rw [sqMinOne_eq_sq_of_abs_lt_oneLocal hx]
  · have hxLarge : 1 ≤ |x| := le_of_not_gt hx
    calc
      ‖levyKhinchinCanonicalKernelLocal t x‖
          = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ := by
              simp [levyKhinchinCanonicalKernelLocal, levyKhinchinCanonicalCentering, hx]
      _ ≤ 2 := norm_exp_sub_one_mul_I_le_twoLocal t x
      _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 := le_max_right _ _
      _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
            rw [sqMinOne_eq_one_of_one_le_absLocal hxLarge, mul_one]

/-- Helper for Lemma 16.25: for fixed `x`, the local canonical kernel is continuous in `t`. -/
private lemma continuousLevyKhinchinCanonicalKernelLocal (x : ℝ) :
    Continuous (fun t : ℝ ↦ levyKhinchinCanonicalKernelLocal t x) := by
  -- Proof comment: for fixed `x`, the kernel is composed from continuous algebraic operations.
  continuity

/-- Helper for Lemma 16.25: canonical Lévy--Khintchin exponents are continuous. -/
private lemma continuousLevyKhinchinExponentLocal
    {τ : LevyKhinchinTriple} (hτ : IsCanonicalTriple τ) :
    Continuous (levyKhinchinExponent τ) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t₀
  let M : ℝ := max (3 * (|t₀| + 1) ^ (2 : ℕ)) 2
  have hboundInt :
      Integrable (fun x : ℝ ↦ M * min (x ^ (2 : ℕ)) 1) τ.ν := by
    -- Proof comment: on a unit neighborhood of `t₀`, the kernel bound only needs the fixed
    -- compact-radius constant `M`.
    simpa [M, mul_comm, mul_left_comm, mul_assoc] using
      hτ.isCanonicalMeasure.integrable_sq_min_one.const_mul M
  have hkernel :
      ContinuousAt (fun t : ℝ ↦ ∫ x : ℝ, levyKhinchinCanonicalKernelLocal t x ∂τ.ν) t₀ := by
    have hmeas :
        ∀ᶠ t : ℝ in nhds t₀, AEStronglyMeasurable (levyKhinchinCanonicalKernelLocal t) τ.ν := by
      exact Filter.Eventually.of_forall fun t ↦
        (measurable_levyKhinchinCanonicalKernelLocal t).aestronglyMeasurable
    have hbound :
        ∀ᶠ t : ℝ in nhds t₀, ∀ᵐ x ∂τ.ν,
          ‖levyKhinchinCanonicalKernelLocal t x‖ ≤ M * min (x ^ (2 : ℕ)) 1 := by
      filter_upwards [Metric.ball_mem_nhds t₀ zero_lt_one] with t ht
      have ht_dist : |t - t₀| < 1 := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using ht
      have ht_abs : |t| ≤ |t₀| + 1 := by
        have htriangle : abs (|t| - |t₀|) ≤ |t - t₀| := by
          simpa using (abs_abs_sub_abs_le_abs_sub t t₀)
        have htriangle_lt : abs (|t| - |t₀|) < 1 := lt_of_le_of_lt htriangle ht_dist
        have hright : |t| - |t₀| < 1 := (abs_lt.mp htriangle_lt).2
        linarith
      have hM :
          max (3 * |t| ^ (2 : ℕ)) 2 ≤ M := by
        dsimp [M]
        have hsq : |t| ^ (2 : ℕ) ≤ (|t₀| + 1) ^ (2 : ℕ) := by
          have hsq' := mul_self_le_mul_self (abs_nonneg t) ht_abs
          simpa [pow_two] using hsq'
        exact max_le_max (by gcongr) le_rfl
      filter_upwards with x
      exact (norm_levyKhinchinCanonicalKernelLocal_le t x).trans <|
        mul_le_mul_of_nonneg_right hM (by positivity)
    have hlim :
        ∀ᵐ x ∂τ.ν,
          Tendsto (fun t : ℝ ↦ levyKhinchinCanonicalKernelLocal t x) (nhds t₀)
            (nhds (levyKhinchinCanonicalKernelLocal t₀ x)) := by
      filter_upwards with x
      exact (continuousLevyKhinchinCanonicalKernelLocal x).continuousAt.tendsto
    have htendsto :
        Tendsto (fun t : ℝ ↦ ∫ x : ℝ, levyKhinchinCanonicalKernelLocal t x ∂τ.ν)
          (nhds t₀) (nhds (∫ x : ℝ, levyKhinchinCanonicalKernelLocal t₀ x ∂τ.ν)) := by
      exact
        (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (μ := τ.ν)
        (F := fun t x ↦ levyKhinchinCanonicalKernelLocal t x)
        (f := levyKhinchinCanonicalKernelLocal t₀)
        (bound := fun x ↦ M * min (x ^ (2 : ℕ)) 1)
        hmeas hbound hboundInt hlim)
    simpa [ContinuousAt] using htendsto
  have hpoly :
      ContinuousAt
        (fun t : ℝ ↦
          (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * t : ℝ) : ℂ) * Complex.I)) t₀ := by
    -- Proof comment: the Gaussian and drift terms are polynomial-exponential combinations in
    -- `t`, hence continuous.
    fun_prop
  -- Proof comment: continuity of the full exponent is the sum of the explicit polynomial part and
  -- the dominated-convergence continuity of the jump integral.
  have hsum :
      ContinuousAt
        ((fun t : ℝ ↦
            (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
              (((τ.b * t : ℝ) : ℂ) * Complex.I)) +
          fun t : ℝ ↦ ∫ x : ℝ, levyKhinchinCanonicalKernelLocal t x ∂τ.ν) t₀ := by
    exact hpoly.add hkernel
  change ContinuousAt
      ((fun t : ℝ ↦
          (((-(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
            (((τ.b * t : ℝ) : ℂ) * Complex.I)) +
        fun t : ℝ ↦
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν) t₀
  simpa [levyKhinchinCanonicalKernelLocal] using hsum

/-- Helper for Lemma 16.25: once continuity is known, two representations of the same law have
the same exponent. -/
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
    existsUniqueContinuousExpLiftLocal
      (MeasureTheory.continuous_charFun : Continuous (charFun (μ : Measure ℝ)))
      (charFun_ne_zero_of_hasLevyKhinchinRepresentationLocal hτ₁)
      (by simpa using (MeasureTheory.charFun_zero (μ := (μ : Measure ℝ))))
  have hΨ₁ :
      Ψ₁ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ₁ t) = charFun (μ : Measure ℝ) t := by
    constructor
    · -- Proof comment: the first exponent is normalized by vanishing at `0`.
      simpa [Ψ₁] using levyKhinchinExponent_zeroLocal τ₁
    · intro t
      -- Proof comment: the first representation identifies the characteristic function.
      simpa [Ψ₁] using (hτ₁.charFun_eq_exp t).symm
  have hΨ₂ :
      Ψ₂ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ₂ t) = charFun (μ : Measure ℝ) t := by
    constructor
    · -- Proof comment: the second exponent uses the same normalization at `0`.
      simpa [Ψ₂] using levyKhinchinExponent_zeroLocal τ₂
    · intro t
      -- Proof comment: the second representation produces the same characteristic function.
      simpa [Ψ₂] using (hτ₂.charFun_eq_exp t).symm
  have hEq₁ : Ψ₁ = Ψ := huniq Ψ₁ hΨ₁
  have hEq₂ : Ψ₂ = Ψ := huniq Ψ₂ hΨ₂
  intro t
  -- Proof comment: evaluate the common continuous lift at frequency `t`.
  exact congrArg (fun f : C(ℝ, ℂ) ↦ f t) (hEq₁.trans hEq₂.symm)

/-- Helper for Lemma 16.25: the power-side and affine-side canonical triples for `μ ^ n` have
the same exponent. -/
private lemma broadStablePowAffineExponent_eq
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (n : ℕ+) :
    ∀ t : ℝ,
      levyKhinchinExponent
        { sigma2 := (n : ℝ) * τ.sigma2
          b := (n : ℝ) * τ.b
          ν := (n : ℕ) • τ.ν } t =
        levyKhinchinExponent
          { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
            b := a n * τ.b + d n +
              a n * ∫ x : ℝ,
                ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
            ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } t := by
  have hpowRep :
      HasLevyKhinchinRepresentation (μ ^ (n : ℕ))
        { sigma2 := (n : ℝ) * τ.sigma2
          b := (n : ℝ) * τ.b
          ν := (n : ℕ) • τ.ν } :=
    pow_hasLevyKhinchinRepresentation μ τ n hτ
  have ha_pos : ∀ m : ℕ+, 0 < a m := scalePosOfBroadStableLocal hμ ha_nonneg hscale
  have hmapRep :
      HasLevyKhinchinRepresentation (μ ^ (n : ℕ))
        { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
          b := a n * τ.b + d n +
            a n * ∫ x : ℝ,
              ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } := by
    have hmapAffine :
        HasLevyKhinchinRepresentation
          (map μ (measurable_affineMap (a n) (d n)).aemeasurable)
          { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
            b := a n * τ.b + d n +
              a n * ∫ x : ℝ,
                ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
            ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } :=
      map_affine_hasLevyKhinchinRepresentation μ τ hτ (ha_pos n)
    -- Proof comment: rewrite the affine-image representation along the broad-stability identity
    -- so both exponents represent the common law `μ ^ n`.
    exact hasLevyKhinchinRepresentation_congrLocal (hscale n).symm hmapAffine
  exact levyKhinchinExponent_eq_of_sameRepresentation_of_continuous
    hpowRep
    hmapRep
    (continuousLevyKhinchinExponentLocal hpowRep.isCanonicalTriple)
    (continuousLevyKhinchinExponentLocal hmapRep.isCanonicalTriple)

/-- Helper for Lemma 16.25: broad stability gives the functional equation
`n ψ(t) = ψ(aₙ t) + i dₙ t` for the canonical exponent. -/
private lemma broadStableExponentScaling_eq
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+, μ ^ (n : ℕ) = μ.map (measurable_affineMap (a n) (d n)).aemeasurable) :
    ∀ n : ℕ+, ∀ t : ℝ,
      (n : ℂ) * levyKhinchinExponent τ t =
        levyKhinchinExponent τ (a n * t) + ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
  have ha_pos : ∀ m : ℕ+, 0 < a m := scalePosOfBroadStableLocal hμ ha_nonneg hscale
  intro n t
  have hEq := broadStablePowAffineExponent_eq hμ hτ ha_nonneg hscale n t
  rw [levyKhinchinExponent_nsmul] at hEq
  have hAffine :
      levyKhinchinExponent
        { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
          b := a n * τ.b + d n +
            a n * ∫ x : ℝ, ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } t =
        levyKhinchinExponent τ (a n * t) + ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
    calc
      levyKhinchinExponent
        { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
          b := a n * τ.b + d n +
            a n * ∫ x : ℝ, ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } t
          =
        levyKhinchinExponent
          { sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
            b := a n * τ.b +
              a n * ∫ x : ℝ, ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
            ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } t +
          ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                (levyKhinchinExponent_addDrift
                  ({ sigma2 := (a n) ^ (2 : ℕ) * τ.sigma2
                     b := a n * τ.b +
                       a n * ∫ x : ℝ,
                         ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
                     ν := Measure.map (fun x : ℝ ↦ a n * x) τ.ν } : LevyKhinchinTriple)
                  (d n) t)
      _ = levyKhinchinExponent τ (a n * t) + ((((d n * t : ℝ) : ℂ) * Complex.I)) := by
            rw [levyKhinchinExponent_map_mul τ (ha_pos n) hτ.isCanonicalTriple.isCanonicalMeasure]
  rw [hAffine] at hEq
  exact hEq

/-- First consequence of Lemma 16.25: for a broadly stable law whose `n`th convolution powers are
realized by the
affine scalings `x ↦ aₙ x + dₙ`, the Gaussian coefficient in the Lévy--Khintchin triple satisfies
`((aₙ)^2 - n) σ² = 0`. -/
theorem stableBroad_canonicalTriple_gaussianScaling
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable) :
    ∀ n : ℕ+, ((a n) ^ (2 : ℕ) - (n : ℝ)) * τ.sigma2 = 0 := by
  sorry

/-- Second consequence of Lemma 16.25: under the same broad-stability scaling relation, the Lévy
measure scales by
`n ν = ν ∘ m_{aₙ}^{-1}`. -/
theorem stableBroad_canonicalTriple_levyMeasureScaling
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable) :
    ∀ n : ℕ+, (n : ℕ) • τ.ν = Measure.map (fun x : ℝ ↦ a n * x) τ.ν := by
  sorry

/-- Third consequence of Lemma 16.25: if the Lévy measure in the canonical triple vanishes, then
the broad-stable
scale factors are the Gaussian ones `aₙ = n^(1/2)`. -/
theorem stableBroad_zeroLevyMeasure_scale_eq
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (hν : τ.ν = 0) :
    ∀ n : ℕ+, a n = (n : ℝ) ^ (1 / (2 : ℝ)) := by
  intro n
  have hσ_ne : τ.sigma2 ≠ 0 := by
    intro hσ
    have hdirac : μ = diracProba τ.b :=
      eq_diracProba_of_zeroGaussian_zeroLevy hτ hσ hν
    exact hμ.1 τ.b hdirac
  have hσ_pos : 0 < τ.sigma2 := by
    -- Proof comment: canonical Gaussian coefficients are nonnegative, so nonvanishing implies
    -- strict positivity.
    exact lt_of_le_of_ne hτ.isCanonicalTriple.sigma2_nonneg (by simpa using hσ_ne.symm)
  have hExpAtOne :=
    zeroLevyExponent_eq_of_broadStableScaling hτ hscale hν n 1
  have hreal := congrArg Complex.re hExpAtOne
  have hsigmaScale : ((a n) ^ (2 : ℕ) - (n : ℝ)) * τ.sigma2 = 0 := by
    -- Proof comment: taking real parts isolates the quadratic Gaussian coefficient.
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_eq_add_neg, add_zero, one_mul] at hreal
    linarith
  have hsq : (a n) ^ (2 : ℕ) = (n : ℝ) := by
    nlinarith [hsigmaScale, hσ_pos]
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hsq_sqrt : (a n) ^ (2 : ℕ) = (Real.sqrt (n : ℝ)) ^ (2 : ℕ) := by
    rw [pow_two, Real.sq_sqrt hn_nonneg]
    simpa [pow_two] using hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq_sqrt with ha_eq | ha_eq
  · -- Proof comment: nonnegativity of the affine scale picks the positive square-root branch.
    simpa [Real.sqrt_eq_rpow] using ha_eq
  · exfalso
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
      apply Real.sqrt_pos.2
      positivity
    linarith [ha_nonneg n, hsqrt_pos, ha_eq]

/-- Fourth consequence of Lemma 16.25: if the Lévy measure in the canonical triple vanishes, then
the centering
constants are exactly `b (n - n^(1/2))`. -/
theorem stableBroad_zeroLevyMeasure_centering_eq
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable)
    (hν : τ.ν = 0) :
    ∀ n : ℕ+, d n = τ.b * ((n : ℝ) - (n : ℝ) ^ (1 / (2 : ℝ))) := by
  intro n
  have hExpAtOne :=
    zeroLevyExponent_eq_of_broadStableScaling hτ hscale hν n 1
  have himag := congrArg Complex.im hExpAtOne
  have hscale_eq :
      a n = (n : ℝ) ^ (1 / (2 : ℝ)) :=
    stableBroad_zeroLevyMeasure_scale_eq hμ hτ ha_nonneg hscale hν n
  -- Proof comment: taking imaginary parts isolates the linear drift contribution.
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, add_zero, one_mul] at himag
  have himag' : (n : ℝ) * τ.b = (n : ℝ) ^ (1 / (2 : ℝ)) * τ.b + d n := by
    simpa [hscale_eq] using himag
  linarith

/-- Helper for Lemma 16.25: projecting the broad-stability comparison of canonical triples to the
drift field. -/
private lemma broadStablePowAffineExponent_eq_normalizedAtOne
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+, μ ^ (n : ℕ) = μ.map (measurable_affineMap (a n) (d n)).aemeasurable)
    (n : ℕ+) :
    levyKhinchinExponent
      { sigma2 := (n : ℝ) * τ.sigma2
        b := (n : ℝ) * τ.b
        ν := (n : ℕ) • τ.ν } 1 =
      levyKhinchinExponent
        { sigma2 := (n : ℝ) * τ.sigma2
          b := a n * τ.b + d n +
            a n * ∫ x : ℝ,
              ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := (n : ℕ) • τ.ν } 1 := by
  have hsigmaZero := stableBroad_canonicalTriple_gaussianScaling hμ hτ ha_nonneg hscale n
  have hsigma :
      (a n) ^ (2 : ℕ) * τ.sigma2 = (n : ℝ) * τ.sigma2 := by
    nlinarith
  have hnu := stableBroad_canonicalTriple_levyMeasureScaling hμ hτ ha_nonneg hscale n
  have hExp := broadStablePowAffineExponent_eq hμ hτ ha_nonneg hscale n 1
  -- Proof comment: rewrite the affine-side exponent so the Gaussian and Lévy-measure fields match
  -- the power-side normal form exactly.
  rw [hsigma, ← hnu] at hExp
  simpa using hExp

/-- Helper for Lemma 16.25: projecting the broad-stability comparison of canonical triples to the
drift field. -/
private lemma stableBroad_bField_eq
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} {a d : ℕ+ → ℝ}
    (hμ : IsStableInBroadSense μ)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (ha_nonneg : ∀ n : ℕ+, 0 ≤ a n)
    (hscale : ∀ n : ℕ+, μ ^ (n : ℕ) = μ.map (measurable_affineMap (a n) (d n)).aemeasurable)
    (n : ℕ+) :
    (n : ℝ) * τ.b =
      a n * τ.b + d n +
        a n * ∫ x : ℝ, ((if |x| < 1 / a n then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν := by
  -- Route correction: instead of reading imaginary parts off `n ψ(t) = ψ(aₙ t) + i dₙ t`,
  -- first normalize the exponent equality so the Gaussian and jump parts literally match.
  have hExpNormalized :=
    broadStablePowAffineExponent_eq_normalizedAtOne hμ hτ ha_nonneg hscale n
  have himagNormalized := congrArg Complex.im hExpNormalized
  -- Proof comment: once the non-drift fields coincide, taking imaginary parts leaves only the
  -- drift coefficients plus a common jump contribution that cancels automatically.
  simp only [levyKhinchinExponent, levyKhinchinExponentWithCentering, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul,
    mul_zero, add_zero, one_mul] at himagNormalized
  linarith

/-- Helper for Lemma 16.25: the canonical scale `n^(1 / α)` satisfies
`(n^(1 / α))^α = n` for `α > 0`. -/
private lemma stableScalePow_eq_natCast {α : ℝ} (hα0 : 0 < α) (n : ℕ+) :
    (((n : ℝ) ^ (1 / α)) ^ α) = (n : ℝ) := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  calc
    (((n : ℝ) ^ (1 / α)) ^ α) = (n : ℝ) ^ ((1 / α) * α) := by
      rw [Real.rpow_mul hn_nonneg]
    _ = (n : ℝ) ^ (1 : ℝ) := by
      congr 1
      field_simp [hα0.ne']
    _ = (n : ℝ) := by rw [Real.rpow_one]

/-- A stable law with an explicit index is stable in the broad sense. -/
private lemma isStableInBroadSense_of_stableWithIndexLocal
    {μ : ProbabilityMeasure ℝ} {α : ℝ}
    (hμ : IsStableInBroadSenseWithIndex μ α) : IsStableInBroadSense μ := by
  refine ⟨hμ.1, ?_⟩
  rcases hμ.2.2 with ⟨d, hd⟩
  refine ⟨(fun n : ℕ+ ↦ (n : ℝ) ^ (1 / α)), d, ?_, hd⟩
  intro n
  exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) _)

/-- Lemma 16.25 (5): if `α ∈ (0, 2)`, the canonical broad-stability scaling relation holds, and
`τ.ν = stableLevyMeasure α c⁻ c⁺`, then for admissible `c⁻, c⁺` and `α ≠ 1` the centering
constants satisfy the explicit formula from `(16.25)`. -/
theorem stableBroad_stableLevy_centering_eq_of_ne_one
    {μ : ProbabilityMeasure ℝ}
    {τ : LevyKhinchinTriple} {d : ℕ+ → ℝ} {α cMinus cPlus : ℝ}
    (hμ : IsStableInBroadSenseWithIndex μ α) (hτ : HasLevyKhinchinRepresentation μ τ)
    (hscale : ∀ n : ℕ+, μ ^ (n : ℕ) =
      μ.map (measurable_affineMap ((n : ℝ) ^ (1 / α)) (d n)).aemeasurable)
    (hcoeff : StableLevyCoefficients cMinus cPlus)
    (hν : τ.ν = stableLevyMeasure α cMinus cPlus) (hα : α ∈ Set.Ioo 0 2) (hα_ne : α ≠ 1)
    (n : ℕ+) :
    d n = (τ.b + (cPlus - cMinus) / (α - 1)) * ((n : ℝ) - (n : ℝ) ^ (1 / α)) := by
  have hμ_broad : IsStableInBroadSense μ :=
    isStableInBroadSense_of_stableWithIndexLocal hμ
  have ha_nonneg : ∀ n : ℕ+, 0 ≤ (n : ℝ) ^ (1 / α) := by
    intro m
    exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (m : ℝ) by exact_mod_cast m.pos) _)
  have hbField :=
    stableBroad_bField_eq hμ_broad hτ ha_nonneg hscale n
  have hα0 : 0 < α := hα.1
  have hn_one_le : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast PNat.one_le n
  have hInv_nonneg : 0 ≤ 1 / α := one_div_nonneg.mpr hα0.le
  have hs_one : 1 ≤ (n : ℝ) ^ (1 / α) := by
    exact Real.one_le_rpow hn_one_le hInv_nonneg
  have hcorrection :
      ((n : ℝ) ^ (1 / α)) *
          ∫ x : ℝ,
            ((if |x| < 1 / ((n : ℝ) ^ (1 / α)) then x else 0) -
                (if |x| < 1 then x else 0))
              ∂τ.ν =
        -((cPlus - cMinus) / (α - 1)) * ((n : ℝ) - (n : ℝ) ^ (1 / α)) := by
    rw [hν]
    have hcorr :=
      stableLevyCenteringCorrection_eq_of_ne_one
        (α := α) (cMinus := cMinus) (cPlus := cPlus)
        hcoeff (s := (n : ℝ) ^ (1 / α)) hs_one hα0 hα_ne
    rw [stableScalePow_eq_natCast hα0 n] at hcorr
    exact hcorr
  rw [hcorrection] at hbField
  linarith

/-- Final consequence of Lemma 16.25: in the same admissible stable-Lévy-measure setting, if
`α = 1` then the
centering constants satisfy the logarithmic formula from `(16.26)`. -/
theorem stableBroad_stableLevy_centering_eq_of_eq_one
    {μ : ProbabilityMeasure ℝ}
    {τ : LevyKhinchinTriple} {d : ℕ+ → ℝ} {α cMinus cPlus : ℝ}
    (hμ : IsStableInBroadSenseWithIndex μ α) (hτ : HasLevyKhinchinRepresentation μ τ)
    (hscale : ∀ n : ℕ+, μ ^ (n : ℕ) =
      μ.map (measurable_affineMap ((n : ℝ) ^ (1 / α)) (d n)).aemeasurable)
    (hcoeff : StableLevyCoefficients cMinus cPlus)
    (hν : τ.ν = stableLevyMeasure α cMinus cPlus) (hα_eq : α = 1) (n : ℕ+) :
    d n = (cPlus - cMinus) * (n : ℝ) * Real.log (n : ℝ) := by
  subst hα_eq
  have hμ_broad : IsStableInBroadSense μ :=
    isStableInBroadSense_of_stableWithIndexLocal hμ
  have ha_nonneg : ∀ m : ℕ+, 0 ≤ (m : ℝ) ^ (1 / (1 : ℝ)) := by
    intro m
    exact le_of_lt (Real.rpow_pos_of_pos (show 0 < (m : ℝ) by exact_mod_cast m.pos) _)
  have hbField :=
    stableBroad_bField_eq hμ_broad hτ ha_nonneg hscale n
  have hn_one_le : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast PNat.one_le n
  have hs_one : 1 ≤ (n : ℝ) ^ (1 / (1 : ℝ)) := by
    simpa using hn_one_le
  have hcorrection :
      ((n : ℝ) ^ (1 / (1 : ℝ))) *
          ∫ x : ℝ,
            ((if |x| < 1 / ((n : ℝ) ^ (1 / (1 : ℝ))) then x else 0) -
                (if |x| < 1 then x else 0))
              ∂τ.ν =
        -(cPlus - cMinus) * ((n : ℝ) ^ (1 / (1 : ℝ))) *
          Real.log ((n : ℝ) ^ (1 / (1 : ℝ))) := by
    rw [hν]
    exact stableLevyCenteringCorrection_eq_of_eq_one
      (cMinus := cMinus) (cPlus := cPlus) hcoeff (s := (n : ℝ) ^ (1 / (1 : ℝ))) hs_one
  rw [hcorrection] at hbField
  have hrpow_one : (n : ℝ) ^ (1 / (1 : ℝ)) = (n : ℝ) := by
    norm_num [Real.rpow_one]
  rw [hrpow_one] at hbField
  linarith

end MeasureTheory.ProbabilityMeasure
