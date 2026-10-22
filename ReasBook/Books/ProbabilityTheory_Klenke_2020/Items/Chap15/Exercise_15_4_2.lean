/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Exercise 15.4.2 is `source-facing`: the textbook content is the joint law of the splitting
transform `(B, Z) ↦ (B * Z, (1 - B) * Z)`.
The owner abstraction is therefore the joint `HasLaw` statement for that transformed pair; the
independence and one-coordinate laws below are derived API from this owner theorem. -/
section

variable (P : Measure Ω) {B Z : Ω → ℝ} {r s : ℝ}
variable (hr : 0 < r) (hs : 0 < s)
variable (hB : HasLaw B (betaMeasure r s) P)
variable (hZ : HasLaw Z (gammaMeasure (r + s) 1) P)
variable (hBZ : IndepFun B Z P)

include hr hs hB hZ hBZ

/-- Helper for Exercise 15.4.2: a Beta random variable is almost surely supported on `[0, 1]`. -/
private lemma ae_mem_Icc_of_hasLaw_beta :
    ∀ᵐ ω ∂P, 0 ≤ B ω ∧ B ω ≤ 1 := by
  have hbeta : ∀ᵐ x ∂ betaMeasure r s, 0 ≤ x ∧ x ≤ 1 := by
    rw [betaMeasure, ae_withDensity_iff (by
      simpa [betaPDF] using ENNReal.measurable_ofReal.comp (measurable_betaPDFReal r s))]
    filter_upwards with x hx
    -- Proof comment: outside `[0, 1]`, the Beta density vanishes, so any point with nonzero
    -- density must lie in the support interval.
    have hx_nonneg : 0 ≤ x := by
      by_contra hx_neg
      exact hx (betaPDF_eq_zero_of_nonpos (le_of_not_ge hx_neg))
    have hx_le_one : x ≤ 1 := by
      by_contra hx_gt
      exact hx (betaPDF_eq_zero_of_one_le (le_of_lt (not_le.mp hx_gt)))
    exact ⟨hx_nonneg, hx_le_one⟩
  -- Proof comment: transport the canonical support statement back along the `HasLaw` equality.
  exact (hB.ae_iff (by fun_prop)).2 hbeta

/-- Helper for Exercise 15.4.2: a Gamma random variable is almost surely nonnegative. -/
private lemma ae_nonneg_of_hasLaw_gamma :
    ∀ᵐ ω ∂P, 0 ≤ Z ω := by
  have hgamma : ∀ᵐ x ∂ gammaMeasure (r + s) 1, 0 ≤ x := by
    rw [gammaMeasure, ae_withDensity_iff (by
      simpa [gammaPDF] using ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal (r + s) 1))]
    filter_upwards with x hx
    -- Proof comment: the Gamma density is zero on the negative half-line, so nonzero-density
    -- points are automatically nonnegative.
    by_contra hx_neg
    exact hx (gammaPDF_of_neg (lt_of_not_ge hx_neg))
  -- Proof comment: transfer the support statement from the canonical Gamma law to `Z`.
  exact (hZ.ae_iff (by fun_prop)).2 hgamma

/-- Helper for Exercise 15.4.2: clamping the Beta/Gamma pair to its natural support preserves the
split coordinates almost everywhere, and the clamped coordinates satisfy the pointwise support
bounds needed for the moment route. -/
private lemma splitComponentsAeEq
    :
    let B0 : Ω → ℝ := fun ω ↦ min 1 (max 0 (B ω))
    let Z0 : Ω → ℝ := fun ω ↦ max 0 (Z ω)
    let X0 : Ω → ℝ := fun ω ↦ B0 ω * Z0 ω
    let Y0 : Ω → ℝ := fun ω ↦ (1 - B0 ω) * Z0 ω
    (∀ ω, 0 ≤ B0 ω ∧ B0 ω ≤ 1 ∧ 0 ≤ Z0 ω) ∧
      B0 =ᵐ[P] B ∧
      Z0 =ᵐ[P] Z ∧
      X0 =ᵐ[P] (fun ω ↦ B ω * Z ω) ∧
      Y0 =ᵐ[P] (fun ω ↦ (1 - B ω) * Z ω) := by
  let B0 : Ω → ℝ := fun ω ↦ min 1 (max 0 (B ω))
  let Z0 : Ω → ℝ := fun ω ↦ max 0 (Z ω)
  let X0 : Ω → ℝ := fun ω ↦ B0 ω * Z0 ω
  let Y0 : Ω → ℝ := fun ω ↦ (1 - B0 ω) * Z0 ω
  have hBounds : ∀ ω, 0 ≤ B0 ω ∧ B0 ω ≤ 1 ∧ 0 ≤ Z0 ω := by
    intro ω
    -- Proof comment: `min 1 (max 0 x)` is always in `[0, 1]`, and `max 0 z` is always
    -- nonnegative.
    refine ⟨?_, ?_, ?_⟩
    · exact le_min zero_le_one (le_max_left 0 (B ω))
    · exact min_le_left 1 (max 0 (B ω))
    · exact le_max_left 0 (Z ω)
  have hB_support : ∀ᵐ ω ∂P, 0 ≤ B ω ∧ B ω ≤ 1 :=
    ae_mem_Icc_of_hasLaw_beta (P := P) (B := B) (r := r) (s := s) hr hs hB hZ hBZ
  have hZ_support : ∀ᵐ ω ∂P, 0 ≤ Z ω :=
    ae_nonneg_of_hasLaw_gamma (P := P) (Z := Z) (r := r) (s := s) hr hs hB hZ hBZ
  have hB0_eq : B0 =ᵐ[P] B := by
    filter_upwards [hB_support] with ω hω
    rcases hω with ⟨hω_nonneg, hω_le_one⟩
    -- Proof comment: on the actual Beta support, the clamp is definitionally the identity.
    dsimp [B0]
    rw [max_eq_right hω_nonneg, min_eq_right hω_le_one]
  have hZ0_eq : Z0 =ᵐ[P] Z := by
    filter_upwards [hZ_support] with ω hω_nonneg
    -- Proof comment: on the Gamma support, the positive-part truncation is the identity.
    dsimp [Z0]
    rw [max_eq_right hω_nonneg]
  have hX0_eq : X0 =ᵐ[P] (fun ω ↦ B ω * Z ω) := by
    filter_upwards [hB0_eq, hZ0_eq] with ω hBω hZω
    -- Proof comment: once both clipped coordinates agree a.e. with the originals, the split
    -- product agrees as well.
    dsimp [X0]
    rw [hBω, hZω]
  have hY0_eq : Y0 =ᵐ[P] (fun ω ↦ (1 - B ω) * Z ω) := by
    filter_upwards [hB0_eq, hZ0_eq] with ω hBω hZω
    -- Proof comment: the same a.e. replacement carries over to the complementary split factor.
    dsimp [Y0]
    rw [hBω, hZω]
  exact ⟨hBounds, hB0_eq, hZ0_eq, hX0_eq, hY0_eq⟩

/-- Helper for Exercise 15.4.2: the unit-rate Gamma density integrates to `1` as a real-valued
integrand. -/
private lemma integral_gammaPDF_toReal_eq_one (a : ℝ) (ha : 0 < a) :
    ∫ x, (gammaPDF a 1 x).toReal = 1 := by
  -- Proof comment: convert the normalized `ENNReal` Gamma density to an ordinary real integral.
  rw [MeasureTheory.integral_toReal]
  · simp [lintegral_gammaPDF_eq_one ha zero_lt_one]
  · simpa [gammaPDF] using
      (ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a 1)).aemeasurable
  · exact Filter.Eventually.of_forall fun x ↦ by simp [gammaPDF]

/-- Helper for Exercise 15.4.2: multiplying the unit-rate Gamma density by `x ^ n` shifts the
shape parameter from `a` to `a + n`. -/
private lemma gammaMomentIntegrand_eq_ratio_mul_shiftedDensity
    (a : ℝ) (ha : 0 < a) (n : ℕ) (x : ℝ) :
    (gammaPDF a 1 x).toReal * x ^ n =
      (Real.Gamma (a + n) / Real.Gamma a) * (gammaPDF (a + n) 1 x).toReal := by
  rcases lt_or_ge x 0 with hx_neg | hx_nonneg
  · -- Proof comment: both Gamma densities vanish on the negative half-line.
    rw [gammaPDF_of_neg hx_neg, gammaPDF_of_neg hx_neg]
    simp
  · have han : 0 < a + n := by
      positivity
    have h_density :
        0 ≤ (1 ^ a / Real.Gamma a) * x ^ (a - 1) * Real.exp (-(1 * x)) := by
      have hnonneg := gammaPDFReal_nonneg ha zero_lt_one x
      rw [gammaPDFReal, if_pos hx_nonneg] at hnonneg
      simpa using hnonneg
    have h_shifted :
        0 ≤ (1 ^ (a + n) / Real.Gamma (a + n)) * x ^ (a + n - 1) * Real.exp (-(1 * x)) := by
      have hnonneg := gammaPDFReal_nonneg han zero_lt_one x
      rw [gammaPDFReal, if_pos hx_nonneg] at hnonneg
      simpa using hnonneg
    have hpow : x ^ (a - 1) * x ^ (n : ℝ) = x ^ (a + n - 1) := by
      rcases eq_or_lt_of_le hx_nonneg with rfl | hx_pos
      · by_cases hn : n = 0
        · subst hn
          simp
        · have hnpos : 0 < (n : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero hn
          have hn_one : 1 ≤ (n : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
          have hsum_pos : 0 < a + n - 1 := by
            linarith
          simp [hn, Real.zero_rpow (ne_of_gt hsum_pos)]
      · rw [← Real.rpow_add hx_pos]
        congr 1
        ring
    have hconst :
        (1 ^ a / Real.Gamma a) =
          (Real.Gamma (a + n) / Real.Gamma a) * (1 ^ (a + n) / Real.Gamma (a + n)) := by
      have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
      have hGan : Real.Gamma (a + n) ≠ 0 := (Real.Gamma_pos_of_pos han).ne'
      calc
        (1 ^ a / Real.Gamma a) = 1 / Real.Gamma a := by rw [Real.one_rpow]
        _ = (Real.Gamma (a + n) / Real.Gamma a) * (1 / Real.Gamma (a + n)) := by
              field_simp [hGa, hGan]
        _ = (Real.Gamma (a + n) / Real.Gamma a) * (1 ^ (a + n) / Real.Gamma (a + n)) := by
              rw [Real.one_rpow]
    -- Proof comment: on `[0, ∞)`, the extra factor `x ^ n` only shifts the Gamma shape.
    rw [gammaPDF_of_nonneg hx_nonneg, gammaPDF_of_nonneg hx_nonneg]
    rw [ENNReal.toReal_ofReal h_density, ENNReal.toReal_ofReal h_shifted]
    calc
      ((1 ^ a / Real.Gamma a) * x ^ (a - 1) * Real.exp (-(1 * x))) * x ^ n
          = (1 ^ a / Real.Gamma a) * (x ^ (a - 1) * x ^ (n : ℝ)) * Real.exp (-(1 * x)) := by
              have hpowNat : x ^ n = x ^ (n : ℝ) := by rw [Real.rpow_natCast]
              rw [hpowNat]
              ring
      _ = (1 ^ a / Real.Gamma a) * x ^ (a + n - 1) * Real.exp (-(1 * x)) := by
            rw [hpow]
      _ = ((Real.Gamma (a + n) / Real.Gamma a) * (1 ^ (a + n) / Real.Gamma (a + n))) *
            x ^ (a + n - 1) * Real.exp (-(1 * x)) := by
            rw [hconst]
      _ = (Real.Gamma (a + n) / Real.Gamma a) *
            ((1 ^ (a + n) / Real.Gamma (a + n)) * x ^ (a + n - 1) * Real.exp (-(1 * x))) := by
              ac_rfl

/-- Helper for Exercise 15.4.2: the Gamma recurrence unfolds `Γ (a + n)` into the finite product
`∏_{k < n} (a + k) * Γ a`. -/
private lemma gamma_add_nat_eq_prod_mul_gamma (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Real.Gamma (a + n) = (∏ k ∈ Finset.range n, (a + k)) * Real.Gamma a := by
  induction n with
  | zero =>
      -- Proof comment: the empty product leaves `Γ a` unchanged.
      simp
  | succ n ih =>
      have han : 0 < a + n := by
        positivity
      -- Proof comment: apply the Gamma recurrence once and then fold the induction product.
      calc
        Real.Gamma (a + ((n + 1 : ℕ) : ℝ)) = Real.Gamma ((a + n) + 1) := by
          congr 1
          norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
        _ = (a + n) * Real.Gamma (a + n) := by
              rw [Real.Gamma_add_one (by positivity : a + n ≠ 0)]
        _ = (a + n) * ((∏ k ∈ Finset.range n, (a + k)) * Real.Gamma a) := by
              rw [ih]
        _ = (∏ k ∈ Finset.range (n + 1), (a + k)) * Real.Gamma a := by
              rw [Finset.prod_range_succ]
              ring

/-- Helper for Exercise 15.4.2: the `n`th unit-rate Gamma moment is the finite rising-factorial
product `∏_{k < n} (a + k)`. -/
private lemma integral_pow_eq_prod_gammaMeasure (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∫ x, x ^ n ∂gammaMeasure a 1 = ∏ k ∈ Finset.range n, (a + k) := by
  have h_meas : Measurable (gammaPDF a 1) := by
    simpa [gammaPDF] using ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a 1)
  calc
    ∫ x, x ^ n ∂gammaMeasure a 1 = ∫ x, (gammaPDF a 1 x).toReal * x ^ n := by
      rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul h_meas]
      · simp only [smul_eq_mul]
      · exact Filter.Eventually.of_forall fun x : ℝ ↦ by simp [gammaPDF]
    _ = ∫ x, (Real.Gamma (a + n) / Real.Gamma a) * (gammaPDF (a + n) 1 x).toReal := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦
            gammaMomentIntegrand_eq_ratio_mul_shiftedDensity
              (P := P) (B := B) (Z := Z) (r := r) (s := s)
              (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
              a ha n x
    _ = Real.Gamma (a + n) / Real.Gamma a := by
          rw [integral_const_mul,
            integral_gammaPDF_toReal_eq_one
              (P := P) (B := B) (Z := Z) (r := r) (s := s)
              (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
              (a + n) (by positivity),
            mul_one]
    _ = ∏ k ∈ Finset.range n, (a + k) := by
          have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
          rw [gamma_add_nat_eq_prod_mul_gamma
            (P := P) (B := B) (Z := Z) (r := r) (s := s)
            (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
            a ha n, mul_div_assoc, div_self hGa, mul_one]

/-- Helper for Exercise 15.4.2: a unit-rate Gamma law has the textbook finite-product moment
formula. -/
private lemma gammaUnitRateMomentFormula {W : Ω → ℝ}
    (a : ℝ) (ha : 0 < a) (hW : HasLaw W (gammaMeasure a 1) P) (n : ℕ) :
    P[fun ω ↦ W ω ^ n] = ∏ k ∈ Finset.range n, (a + k) := by
  -- Proof comment: transport the canonical Gamma moment computation along the `HasLaw` equality.
  calc
    P[fun ω ↦ W ω ^ n] = ∫ x, x ^ n ∂gammaMeasure a 1 := by
      simpa [Function.comp_apply] using
        hW.integral_comp
          (f := fun x : ℝ ↦ x ^ n)
          ((continuous_id.pow n).aestronglyMeasurable)
    _ = ∏ k ∈ Finset.range n, (a + k) := integral_pow_eq_prod_gammaMeasure
      (P := P) (B := B) (Z := Z) (r := r) (s := s)
      (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
      a ha n

/-- Helper for Exercise 15.4.2: multiplying the Beta density by
`x ^ m * (1 - x) ^ n` shifts both shape parameters. -/
private lemma integral_betaPDF_toReal_eq_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x, (betaPDF a b x).toReal = 1 := by
  -- Proof comment: convert the normalized `ENNReal` Beta density to an ordinary real integral.
  rw [MeasureTheory.integral_toReal]
  · simp [lintegral_betaPDF_eq_one ha hb]
  · simpa [betaPDF] using
      (ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)).aemeasurable
  · exact Filter.Eventually.of_forall fun x ↦ by simp [betaPDF]

/-- Helper for Exercise 15.4.2: multiplying the Beta density by
`x ^ m * (1 - x) ^ n` shifts both shape parameters. -/
private lemma betaMixedMomentIntegrand_eq_ratio_mul_shiftedDensity
    (m n : ℕ) (x : ℝ) :
    (betaPDF r s x).toReal * (x ^ m * (1 - x) ^ n) =
      (beta (r + m) (s + n) / beta r s) * (betaPDF (r + m) (s + n) x).toReal := by
  rcases le_or_gt x 0 with hx_nonpos | hx_pos
  · -- Proof comment: both Beta densities vanish on the nonpositive half-line.
    rw [betaPDF_eq_zero_of_nonpos hx_nonpos, betaPDF_eq_zero_of_nonpos hx_nonpos]
    simp
  · rcases le_or_gt 1 x with hx_one | hx_lt
    · -- Proof comment: both Beta densities also vanish on `[1, ∞)`.
      rw [betaPDF_eq_zero_of_one_le hx_one, betaPDF_eq_zero_of_one_le hx_one]
      simp
    · have hrm : 0 < r + m := by positivity
      have hsn : 0 < s + n := by positivity
      have hmem : 0 < x ∧ x < 1 := ⟨hx_pos, hx_lt⟩
      have h_density :
          0 ≤ (1 / beta r s) * x ^ (r - 1) * (1 - x) ^ (s - 1) := by
        have hpos := (betaPDFReal_pos hx_pos hx_lt hr hs).le
        rw [betaPDFReal, if_pos hmem] at hpos
        exact hpos
      have h_shifted :
          0 ≤ (1 / beta (r + m) (s + n)) *
            x ^ (r + m - 1) * (1 - x) ^ (s + n - 1) := by
        have hpos := (betaPDFReal_pos hx_pos hx_lt hrm hsn).le
        rw [betaPDFReal, if_pos hmem] at hpos
        exact hpos
      have hconst :
          (1 / beta r s) =
            (beta (r + m) (s + n) / beta r s) * (1 / beta (r + m) (s + n)) := by
        field_simp [ne_of_gt (beta_pos hr hs), ne_of_gt (beta_pos hrm hsn)]
      have hpow_left : x ^ (r - 1) * x ^ (m : ℝ) = x ^ (r + m - 1) := by
        rw [← Real.rpow_add hx_pos]
        congr 1
        ring
      have hpow_right :
          (1 - x) ^ (s - 1) * (1 - x) ^ (n : ℝ) = (1 - x) ^ (s + n - 1) := by
        have hx_sub_pos : 0 < 1 - x := by linarith
        rw [← Real.rpow_add hx_sub_pos]
        congr 1
        ring
      -- Proof comment: on `(0, 1)`, the additional powers shift both Beta parameters.
      rw [betaPDF_of_pos_lt_one hx_pos hx_lt, betaPDF_of_pos_lt_one hx_pos hx_lt]
      rw [ENNReal.toReal_ofReal h_density, ENNReal.toReal_ofReal h_shifted]
      rw [← Real.rpow_natCast x m, ← Real.rpow_natCast (1 - x) n]
      calc
        ((1 / beta r s) * x ^ (r - 1) * (1 - x) ^ (s - 1)) *
            (x ^ (m : ℝ) * (1 - x) ^ (n : ℝ))
            = (1 / beta r s) * (x ^ (r - 1) * x ^ (m : ℝ)) *
                ((1 - x) ^ (s - 1) * (1 - x) ^ (n : ℝ)) := by
                  ac_rfl
        _ = (1 / beta r s) * x ^ (r + m - 1) * (1 - x) ^ (s + n - 1) := by
              rw [hpow_left, hpow_right]
        _ = ((beta (r + m) (s + n) / beta r s) * (1 / beta (r + m) (s + n))) *
              x ^ (r + m - 1) * (1 - x) ^ (s + n - 1) := by
                rw [hconst]
        _ = (beta (r + m) (s + n) / beta r s) *
              ((1 / beta (r + m) (s + n)) *
                x ^ (r + m - 1) * (1 - x) ^ (s + n - 1)) := by
                  ac_rfl

/-- Helper for Exercise 15.4.2: the mixed Beta moment integral equals the corresponding Beta
ratio after shifting both shape parameters. -/
private lemma integral_betaMixed_eq_beta_ratio_betaMeasure
    (m n : ℕ) :
    ∫ x, x ^ m * (1 - x) ^ n ∂betaMeasure r s =
      beta (r + m) (s + n) / beta r s := by
  have h_meas : Measurable (betaPDF r s) := by
    simpa [betaPDF] using ENNReal.measurable_ofReal.comp (measurable_betaPDFReal r s)
  calc
    ∫ x, x ^ m * (1 - x) ^ n ∂betaMeasure r s =
        ∫ x, (betaPDF r s x).toReal * (x ^ m * (1 - x) ^ n) := by
          rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul h_meas]
          · simp only [smul_eq_mul]
          · exact Filter.Eventually.of_forall fun x : ℝ ↦ by simp [betaPDF]
    _ = ∫ x, (beta (r + m) (s + n) / beta r s) * (betaPDF (r + m) (s + n) x).toReal := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦
            betaMixedMomentIntegrand_eq_ratio_mul_shiftedDensity
              (P := P) (B := B) (Z := Z) (r := r) (s := s)
              (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
              m n x
    _ = beta (r + m) (s + n) / beta r s := by
          rw [integral_const_mul,
            integral_betaPDF_toReal_eq_one
              (P := P) (B := B) (Z := Z) (r := r) (s := s)
              (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
              (r + m) (s + n) (by positivity) (by positivity),
            mul_one]

/-- Helper for Exercise 15.4.2: a Beta law has the textbook mixed-moment formula
`E[B^m (1 - B)^n] = beta (r + m) (s + n) / beta r s`. -/
private lemma betaMixedMomentFormula {W : Ω → ℝ}
    (hW : HasLaw W (betaMeasure r s) P) (m n : ℕ) :
    P[fun ω ↦ W ω ^ m * (1 - W ω) ^ n] = beta (r + m) (s + n) / beta r s := by
  -- Proof comment: transport the mixed Beta integral from the canonical law to the random
  -- variable `W`.
  calc
    P[fun ω ↦ W ω ^ m * (1 - W ω) ^ n] = ∫ x, x ^ m * (1 - x) ^ n ∂betaMeasure r s := by
      simpa [Function.comp_apply] using
        hW.integral_comp
          (f := fun x : ℝ ↦ x ^ m * (1 - x) ^ n)
          (((continuous_id.pow m).mul ((continuous_const.sub continuous_id).pow n)).aestronglyMeasurable)
    _ = beta (r + m) (s + n) / beta r s :=
      integral_betaMixed_eq_beta_ratio_betaMeasure
        (P := P) (B := B) (Z := Z) (r := r) (s := s)
        (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
        m n

/-- Helper for Exercise 15.4.2: the canonical coordinate under `gammaMeasure a 1` is almost
surely nonnegative. -/
private lemma ae_nonneg_gammaMeasure (a : ℝ) :
    ∀ᵐ x ∂ gammaMeasure a 1, 0 ≤ x := by
  rw [gammaMeasure, ae_withDensity_iff (by
    simpa [gammaPDF] using ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a 1))]
  filter_upwards with x hx
  -- Proof comment: the Gamma density vanishes on the negative half-line.
  by_contra hx_neg
  exact hx (gammaPDF_of_neg (lt_of_not_ge hx_neg))

/-- Helper for Exercise 15.4.2: the finite Gamma moment product is bounded by the endpoint power
`(a + n) ^ n`. -/
private lemma gammaMomentProduct_le_pow (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∏ k ∈ Finset.range n, (a + k) ≤ (a + n) ^ n := by
  have h_nonneg : ∀ k ∈ Finset.range n, 0 ≤ a + k := by
    intro k hk
    positivity
  have hbound : ∀ k ∈ Finset.range n, a + k ≤ a + n := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by
      exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hk)
    linarith
  -- Proof comment: every factor in the rising product is bounded by the endpoint `a + n`.
  have hprod_le :
      ∏ k ∈ Finset.range n, (a + k) ≤ ∏ k ∈ Finset.range n, (a + n) :=
    Finset.prod_le_prod h_nonneg hbound
  simpa [Finset.prod_eq_pow_card] using hprod_le

/-- Helper for Exercise 15.4.2: a nonnegative random variable with unit-rate Gamma law has
integrable powers of every order. -/
private lemma integrable_pow_gammaMeasure (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (gammaMeasure a 1) := by
  -- Proof comment: the explicit Gamma moment formula is strictly positive, so the integral cannot
  -- be the `0` placeholder produced by a non-integrable real integral.
  by_contra h_notInt
  have hMoment :
      ∫ x, x ^ n ∂gammaMeasure a 1 = ∏ k ∈ Finset.range n, (a + k) :=
    integral_pow_eq_prod_gammaMeasure
      (P := P) (B := B) (Z := Z) (r := r) (s := s)
      (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
      a ha n
  rw [integral_undef h_notInt] at hMoment
  have hPos : 0 < ∏ k ∈ Finset.range n, (a + k) := by
    refine Finset.prod_pos ?_
    intro k hk
    positivity
  exact (ne_of_gt hPos) hMoment.symm

/-- Helper for Exercise 15.4.2: a nonnegative random variable with unit-rate Gamma law has
integrable powers of every order. -/
private lemma integrable_pow_of_hasLaw_gammaUnit {W : Ω → ℝ}
    (a : ℝ) (ha : 0 < a) (hW : HasLaw W (gammaMeasure a 1) P)
    (hW_nonneg : ∀ ω, 0 ≤ W ω) (n : ℕ) :
    Integrable (fun ω ↦ W ω ^ n) P := by
  -- Route correction: prove the power is integrable once on the canonical Gamma space, then pull
  -- it back along `HasLaw` instead of redoing the integrability argument under the ambient measure.
  have hCanonical : Integrable (fun x : ℝ ↦ x ^ n) (gammaMeasure a 1) :=
    integrable_pow_gammaMeasure
      (P := P) (B := B) (Z := Z) (r := r) (s := s)
      (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
      a ha n
  have hCanonicalMap : Integrable (fun x : ℝ ↦ x ^ n) (P.map W) := by
    simpa [hW.map_eq] using hCanonical
  have hTransport :
      Integrable ((fun x : ℝ ↦ x ^ n) ∘ W) P := by
    exact
      (integrable_map_measure
        (f := W)
        (g := fun x : ℝ ↦ x ^ n)
        (μ := P)
        (by fun_prop)
        hW.aemeasurable).mp hCanonicalMap
  simpa [Function.comp] using hTransport

/-- Helper for Exercise 15.4.2: the Gamma moment constant and the Beta mixed-moment constant
collapse to the split Gamma moment product. -/
private lemma betaGammaConstant_eq_splitMomentProduct (m n : ℕ) :
    (∏ k ∈ Finset.range (m + n), (r + s + k)) * (beta (r + m) (s + n) / beta r s) =
      (∏ i ∈ Finset.range m, (r + i)) * (∏ j ∈ Finset.range n, (s + j)) := by
  have hΓr : Real.Gamma r ≠ 0 := (Real.Gamma_pos_of_pos hr).ne'
  have hΓs : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hs).ne'
  have hΓrs : Real.Gamma (r + s) ≠ 0 := (Real.Gamma_pos_of_pos (add_pos hr hs)).ne'
  have hΓrm : Real.Gamma (r + m) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity : 0 < r + m)).ne'
  have hΓsn : Real.Gamma (s + n) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity : 0 < s + n)).ne'
  have hΓsum : Real.Gamma (r + s + (m + n)) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by positivity : 0 < r + s + (m + n))).ne'
  have hProdSum :
      ∏ k ∈ Finset.range (m + n), (r + s + k) =
        Real.Gamma (r + s + (m + n)) / Real.Gamma (r + s) := by
    refine (eq_div_iff hΓrs).2 ?_
    simpa [mul_comm] using
      (gamma_add_nat_eq_prod_mul_gamma
        (P := P) (B := B) (Z := Z) (r := r) (s := s)
        (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
        (r + s) (add_pos hr hs) (m + n)).symm
  have hProdR :
      ∏ i ∈ Finset.range m, (r + i) = Real.Gamma (r + m) / Real.Gamma r := by
    refine (eq_div_iff hΓr).2 ?_
    simpa [mul_comm] using
      (gamma_add_nat_eq_prod_mul_gamma
        (P := P) (B := B) (Z := Z) (r := r) (s := s)
        (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
        r hr m).symm
  have hProdS :
      ∏ j ∈ Finset.range n, (s + j) = Real.Gamma (s + n) / Real.Gamma s := by
    refine (eq_div_iff hΓs).2 ?_
    simpa [mul_comm] using
      (gamma_add_nat_eq_prod_mul_gamma
        (P := P) (B := B) (Z := Z) (r := r) (s := s)
        (hr := hr) (hs := hs) (hB := hB) (hZ := hZ) (hBZ := hBZ)
        s hs n).symm
  -- Proof comment: rewrite every finite product as a Gamma ratio and cancel the common factors.
  rw [hProdSum, hProdR, hProdS, beta, beta]
  have hsum : r + m + (s + n) = r + s + (m + n) := by
    ring
  rw [hsum]
  field_simp [hΓr, hΓs, hΓrs, hΓrm, hΓsn, hΓsum]

-- The textbook notation `I_{1, a}` is interpreted as the Gamma law with shape `a` and unit rate,
-- namely `gammaMeasure a 1`. The source's `T_{1, r}` is treated as the same OCR-corrupted
-- notation.
-- Proof sketch: apply Exercise 15.4.1 to the change of variables `(b, z) ↦ (bz, (1 - b)z)` on
-- `(0,1) × (0,∞)`, identify the transported joint density with the product of the Gamma densities
-- of shapes `r` and `s`, and then use independence of `B` and `Z` to pass from the product law of
-- `(B, Z)` to the law of the transformed pair.
/-- Exercise 15.4.2: if `B` has Beta law `betaMeasure r s` and `Z` has Gamma law
`gammaMeasure (r + s) 1`, independently, then the pair `(B * Z, (1 - B) * Z)` has the product
Gamma law with shapes `r` and `s` and unit rate. -/
theorem beta_gamma_unit_rate_split_hasLaw_prod
    :
    HasLaw
      (fun ω ↦ (B ω * Z ω, (1 - B ω) * Z ω))
      ((gammaMeasure r 1).prod (gammaMeasure s 1)) P := by
  letI : IsProbabilityMeasure (betaMeasure r s) := isProbabilityMeasureBeta hr hs
  letI : IsProbabilityMeasure P := hB.isProbabilityMeasure
  letI : IsProbabilityMeasure (gammaMeasure r 1) := isProbabilityMeasure_gammaMeasure hr zero_lt_one
  letI : IsProbabilityMeasure (gammaMeasure s 1) := isProbabilityMeasure_gammaMeasure hs zero_lt_one
  let Bm : Ω → ℝ := hB.aemeasurable.mk B
  let Zm : Ω → ℝ := hZ.aemeasurable.mk Z
  let B0 : Ω → ℝ := fun ω ↦ min 1 (max 0 (Bm ω))
  let Z0 : Ω → ℝ := fun ω ↦ max 0 (Zm ω)
  let X0 : Ω → ℝ := fun ω ↦ B0 ω * Z0 ω
  let Y0 : Ω → ℝ := fun ω ↦ (1 - B0 ω) * Z0 ω
  -- Proof comment: first replace the original variables by measurable representatives so that the
  -- clipped split coordinates become measurable and compatible with Exercise 15.4.1.
  have hBm : HasLaw Bm (betaMeasure r s) P := by
    simpa [Bm] using hB.congr hB.aemeasurable.ae_eq_mk.symm
  have hZm : HasLaw Zm (gammaMeasure (r + s) 1) P := by
    simpa [Zm] using hZ.congr hZ.aemeasurable.ae_eq_mk.symm
  have hBmZm : IndepFun Bm Zm P := by
    simpa [Bm, Zm] using
      hBZ.congr hB.aemeasurable.ae_eq_mk hZ.aemeasurable.ae_eq_mk
  have hBm_eq : Bm =ᵐ[P] B := by
    simpa [Bm] using hB.aemeasurable.ae_eq_mk.symm
  have hZm_eq : Zm =ᵐ[P] Z := by
    simpa [Zm] using hZ.aemeasurable.ae_eq_mk.symm
  have hSplit :=
    splitComponentsAeEq
      (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
      (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm)
  rcases hSplit with ⟨hBounds, hB0_eq, hZ0_eq, hX0_eq, hY0_eq⟩
  have hB0_meas : Measurable B0 := by
    dsimp [B0]
    fun_prop
  have hZ0_meas : Measurable Z0 := by
    dsimp [Z0]
    fun_prop
  have hX0_meas : Measurable X0 := by
    dsimp [X0]
    fun_prop
  have hY0_meas : Measurable Y0 := by
    dsimp [Y0]
    fun_prop
  have hB0 : HasLaw B0 (betaMeasure r s) P := hBm.congr hB0_eq
  have hZ0 : HasLaw Z0 (gammaMeasure (r + s) 1) P := hZm.congr hZ0_eq
  have hB0Z0 : IndepFun B0 Z0 P := by
    -- Proof comment: clipping is a measurable coordinatewise transformation, so independence is
    -- preserved.
    change
      IndepFun
        ((fun b : ℝ ↦ min 1 (max 0 b)) ∘ Bm)
        ((fun z : ℝ ↦ max 0 z) ∘ Zm) P
    exact hBmZm.comp (by fun_prop) (by fun_prop)
  have hB0_nonneg : ∀ ω, 0 ≤ B0 ω := fun ω ↦ (hBounds ω).1
  have hB0_le_one : ∀ ω, B0 ω ≤ 1 := fun ω ↦ (hBounds ω).2.1
  have hZ0_nonneg : ∀ ω, 0 ≤ Z0 ω := fun ω ↦ (hBounds ω).2.2
  have hX0_nonneg : ∀ ω, 0 ≤ X0 ω := by
    intro ω
    dsimp [X0]
    exact mul_nonneg (hB0_nonneg ω) (hZ0_nonneg ω)
  have hY0_nonneg : ∀ ω, 0 ≤ Y0 ω := by
    intro ω
    dsimp [Y0]
    exact mul_nonneg (sub_nonneg.mpr (hB0_le_one ω)) (hZ0_nonneg ω)
  -- Proof comment: compute every mixed moment of the clipped split pair by separating the Beta
  -- and Gamma factors through independence of `B0` and `Z0`.
  have hMixedExplicit :
      ∀ m n : ℕ,
        Integrable (fun ω ↦ X0 ω ^ m * Y0 ω ^ n) P ∧
          ∫ ω, X0 ω ^ m * Y0 ω ^ n ∂P =
            (∏ i ∈ Finset.range m, (r + i)) * (∏ j ∈ Finset.range n, (s + j)) := by
    intro m n
    have hRewrite :
        (fun ω ↦ X0 ω ^ m * Y0 ω ^ n) =
          fun ω ↦ (B0 ω ^ m * (1 - B0 ω) ^ n) * Z0 ω ^ (m + n) := by
      funext ω
      dsimp [X0, Y0]
      calc
        (B0 ω * Z0 ω) ^ m * ((1 - B0 ω) * Z0 ω) ^ n
            = (B0 ω ^ m * Z0 ω ^ m) * ((1 - B0 ω) ^ n * Z0 ω ^ n) := by
                rw [mul_pow, mul_pow]
        _ = (B0 ω ^ m * (1 - B0 ω) ^ n) * (Z0 ω ^ m * Z0 ω ^ n) := by
              ring
        _ = (B0 ω ^ m * (1 - B0 ω) ^ n) * Z0 ω ^ (m + n) := by
              rw [← pow_add]
    have hFactor :
        ∫ ω, X0 ω ^ m * Y0 ω ^ n ∂P =
          (∫ ω, B0 ω ^ m * (1 - B0 ω) ^ n ∂P) * ∫ ω, Z0 ω ^ (m + n) ∂P := by
      calc
        ∫ ω, X0 ω ^ m * Y0 ω ^ n ∂P
            = ∫ ω, (B0 ω ^ m * (1 - B0 ω) ^ n) * Z0 ω ^ (m + n) ∂P := by
                rw [hRewrite]
        _ = (∫ ω, B0 ω ^ m * (1 - B0 ω) ^ n ∂P) * ∫ ω, Z0 ω ^ (m + n) ∂P := by
              simpa [Function.comp] using
                hB0Z0.integral_fun_comp_mul_comp
                  hB0_meas.aemeasurable
                  hZ0_meas.aemeasurable
                  (by
                    fun_prop :
                      AEStronglyMeasurable
                        (fun b : ℝ ↦ b ^ m * (1 - b) ^ n)
                        (P.map B0))
                  (by
                    fun_prop :
                      AEStronglyMeasurable
                        (fun z : ℝ ↦ z ^ (m + n))
                        (P.map Z0))
    have hEq :
        ∫ ω, X0 ω ^ m * Y0 ω ^ n ∂P =
          (∏ i ∈ Finset.range m, (r + i)) * (∏ j ∈ Finset.range n, (s + j)) := by
      calc
        ∫ ω, X0 ω ^ m * Y0 ω ^ n ∂P
            = (beta (r + m) (s + n) / beta r s) *
                (∏ k ∈ Finset.range (m + n), (r + s + k)) := by
                  rw [hFactor,
                    betaMixedMomentFormula
                      (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
                      (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm)
                      (W := B0) hB0 m n,
                    gammaUnitRateMomentFormula
                      (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
                      (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm)
                      (W := Z0) (r + s) (add_pos hr hs) hZ0 (m + n)]
        _ = (∏ i ∈ Finset.range m, (r + i)) * (∏ j ∈ Finset.range n, (s + j)) := by
              rw [mul_comm,
                betaGammaConstant_eq_splitMomentProduct
                  (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
                  (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm)]
    have hPos :
        0 <
          (∏ i ∈ Finset.range m, (r + i)) * (∏ j ∈ Finset.range n, (s + j)) := by
      apply mul_pos
      · refine Finset.prod_pos ?_
        intro i hi
        positivity
      · refine Finset.prod_pos ?_
        intro j hj
        positivity
    have hInt : Integrable (fun ω ↦ X0 ω ^ m * Y0 ω ^ n) P := by
      by_contra h_notInt
      rw [integral_undef h_notInt] at hEq
      exact (ne_of_gt hPos) hEq.symm
    exact ⟨hInt, hEq⟩
  have hMomentX :
      ∀ n : ℕ, moment X0 n P = ∏ i ∈ Finset.range n, (r + i) := by
    intro n
    simpa [moment] using (hMixedExplicit n 0).2
  have hMomentY :
      ∀ n : ℕ, moment Y0 n P = ∏ j ∈ Finset.range n, (s + j) := by
    intro n
    simpa [moment] using (hMixedExplicit 0 n).2
  have hXpow : ∀ n : ℕ, Integrable (fun ω ↦ X0 ω ^ n) P := by
    intro n
    by_contra h_notInt
    have hPos : 0 < ∏ i ∈ Finset.range n, (r + i) := by
      refine Finset.prod_pos ?_
      intro i hi
      positivity
    have hMoment := hMomentX n
    have hZero : ∫ x, (X0 ^ n) x ∂P = 0 := by
      simpa using integral_undef h_notInt
    rw [moment_def, hZero] at hMoment
    exact (ne_of_gt hPos) hMoment.symm
  have hYpow : ∀ n : ℕ, Integrable (fun ω ↦ Y0 ω ^ n) P := by
    intro n
    by_contra h_notInt
    have hPos : 0 < ∏ j ∈ Finset.range n, (s + j) := by
      refine Finset.prod_pos ?_
      intro j hj
      positivity
    have hMoment := hMomentY n
    have hZero : ∫ x, (Y0 ^ n) x ∂P = 0 := by
      simpa using integral_undef h_notInt
    rw [moment_def, hZero] at hMoment
    exact (ne_of_gt hPos) hMoment.symm
  -- Proof comment: the explicit Gamma-style moment formulas give the growth condition required by
  -- Exercise 15.4.1 for both clipped split marginals.
  have hX_growth : HasFiniteAbsoluteMomentRootLimsup P X0 := by
    refine ⟨hX0_meas, ?_, ?_⟩
    · intro n
      exact
        (integrable_absPow_iff_integrable_pow_of_nonneg
          (P := P) (Z := X0) hX0_nonneg n).2 (hXpow n)
    · refine Filter.isBoundedUnder_of_eventually_le (a := r + 1) ?_
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.mp hn)
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast hn
      have hMomentAbs :
          moment (fun ω ↦ |X0 ω|) n P = ∏ i ∈ Finset.range n, (r + i) := by
        rw [moment_abs_eq_moment_of_nonneg (P := P) (Z := X0) hX0_nonneg n]
        exact hMomentX n
      have hRootLe :
          Real.rpow (moment (fun ω ↦ |X0 ω|) n P) (1 / (n : ℝ)) ≤ r + n := by
        calc
          Real.rpow (moment (fun ω ↦ |X0 ω|) n P) (1 / (n : ℝ))
              ≤ Real.rpow ((r + n) ^ n) (1 / (n : ℝ)) := by
                rw [hMomentAbs]
                exact Real.rpow_le_rpow
                  (by positivity)
                  (gammaMomentProduct_le_pow
                    (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
                    (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm)
                    r hr n)
                  (by positivity)
          _ = r + n := by
                rw [one_div]
                exact Real.pow_rpow_inv_natCast (by positivity : 0 ≤ r + n)
                  (Nat.one_le_iff_ne_zero.mp hn)
      have hdiv : r / n ≤ r := div_le_self hr.le hn1
      calc
        ((n : ℝ)⁻¹) * Real.rpow (moment (fun ω ↦ |X0 ω|) n P) (1 / (n : ℝ))
            ≤ ((n : ℝ)⁻¹) * (r + n) := by
                exact mul_le_mul_of_nonneg_left hRootLe (by positivity)
        _ = r / n + 1 := by
              rw [mul_add, inv_mul_cancel₀ hn0, div_eq_mul_inv]
              ring
        _ ≤ r + 1 := by
              linarith
  have hY_growth : HasFiniteAbsoluteMomentRootLimsup P Y0 := by
    refine ⟨hY0_meas, ?_, ?_⟩
    · intro n
      exact
        (integrable_absPow_iff_integrable_pow_of_nonneg
          (P := P) (Z := Y0) hY0_nonneg n).2 (hYpow n)
    · refine Filter.isBoundedUnder_of_eventually_le (a := s + 1) ?_
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.mp hn)
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast hn
      have hMomentAbs :
          moment (fun ω ↦ |Y0 ω|) n P = ∏ j ∈ Finset.range n, (s + j) := by
        rw [moment_abs_eq_moment_of_nonneg (P := P) (Z := Y0) hY0_nonneg n]
        exact hMomentY n
      have hRootLe :
          Real.rpow (moment (fun ω ↦ |Y0 ω|) n P) (1 / (n : ℝ)) ≤ s + n := by
        calc
          Real.rpow (moment (fun ω ↦ |Y0 ω|) n P) (1 / (n : ℝ))
              ≤ Real.rpow ((s + n) ^ n) (1 / (n : ℝ)) := by
                rw [hMomentAbs]
                exact Real.rpow_le_rpow
                  (by positivity)
                  (gammaMomentProduct_le_pow
                    (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
                    (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm)
                    s hs n)
                  (by positivity)
          _ = s + n := by
                rw [one_div]
                exact Real.pow_rpow_inv_natCast (by positivity : 0 ≤ s + n)
                  (Nat.one_le_iff_ne_zero.mp hn)
      have hdiv : s / n ≤ s := div_le_self hs.le hn1
      calc
        ((n : ℝ)⁻¹) * Real.rpow (moment (fun ω ↦ |Y0 ω|) n P) (1 / (n : ℝ))
            ≤ ((n : ℝ)⁻¹) * (s + n) := by
                exact mul_le_mul_of_nonneg_left hRootLe (by positivity)
        _ = s / n + 1 := by
              rw [mul_add, inv_mul_cancel₀ hn0, div_eq_mul_inv]
              ring
        _ ≤ s + 1 := by
              linarith
  have hMixedFactorized :
      ∀ m n : ℕ,
        Integrable (fun ω ↦ X0 ω ^ m * Y0 ω ^ n) P ∧
          ∫ ω, X0 ω ^ m * Y0 ω ^ n ∂P = moment X0 m P * moment Y0 n P := by
    intro m n
    refine ⟨(hMixedExplicit m n).1, ?_⟩
    rw [hMomentX m, hMomentY n]
    exact (hMixedExplicit m n).2
  have hIndep0 : IndepFun X0 Y0 P := by
    -- Proof comment: Exercise 15.4.1 upgrades the explicit mixed-moment factorization to
    -- independence once the root-growth hypotheses are established.
    exact
      indepFun_of_mixed_moment_factorization_of_hasFiniteAbsoluteMomentRootLimsup
        P X0 Y0 hX_growth hY_growth hX0_nonneg hY0_nonneg hMixedFactorized
  -- Proof comment: identify each clipped marginal with the corresponding Gamma law by comparing
  -- its moments to the canonical nonnegative Gamma coordinate `x ↦ max 0 x`.
  have hMaxEq_r : (fun x : ℝ ↦ max 0 x) =ᵐ[gammaMeasure r 1] fun x ↦ x := by
    refine
      (ae_nonneg_gammaMeasure
        (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
        (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm) r).mono ?_
    intro x hx
    exact max_eq_right hx
  have hMaxEq_s : (fun x : ℝ ↦ max 0 x) =ᵐ[gammaMeasure s 1] fun x ↦ x := by
    refine
      (ae_nonneg_gammaMeasure
        (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
        (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm) s).mono ?_
    intro x hx
    exact max_eq_right hx
  have hMaxPow_r : ∀ n : ℕ, Integrable (fun x : ℝ ↦ (max 0 x) ^ n) (gammaMeasure r 1) := by
    intro n
    refine
      (integrable_pow_gammaMeasure
        (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
        (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm)
        r hr n).congr ?_
    filter_upwards [hMaxEq_r] with x hx
    simp [hx]
  have hMaxPow_s : ∀ n : ℕ, Integrable (fun x : ℝ ↦ (max 0 x) ^ n) (gammaMeasure s 1) := by
    intro n
    refine
      (integrable_pow_gammaMeasure
        (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
        (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm)
        s hs n).congr ?_
    filter_upwards [hMaxEq_s] with x hx
    simp [hx]
  have hMaxMoments_r :
      ∀ n : ℕ, Integrable (fun x : ℝ ↦ |max 0 x| ^ n) (gammaMeasure r 1) := by
    intro n
    exact
      (integrable_absPow_iff_integrable_pow_of_nonneg
        (P := gammaMeasure r 1) (Z := fun x : ℝ ↦ max 0 x)
        (fun x ↦ le_max_left 0 x) n).2 (hMaxPow_r n)
  have hMaxMoments_s :
      ∀ n : ℕ, Integrable (fun x : ℝ ↦ |max 0 x| ^ n) (gammaMeasure s 1) := by
    intro n
    exact
      (integrable_absPow_iff_integrable_pow_of_nonneg
        (P := gammaMeasure s 1) (Z := fun x : ℝ ↦ max 0 x)
        (fun x ↦ le_max_left 0 x) n).2 (hMaxPow_s n)
  have hMomentGamma_r :
      ∀ n : ℕ, moment (fun x : ℝ ↦ max 0 x) n (gammaMeasure r 1) =
        ∏ i ∈ Finset.range n, (r + i) := by
    intro n
    rw [moment]
    calc
      ∫ x, (max 0 x) ^ n ∂gammaMeasure r 1 = ∫ x, x ^ n ∂gammaMeasure r 1 := by
        refine integral_congr_ae ?_
        filter_upwards [hMaxEq_r] with x hx
        simp [hx]
      _ = ∏ i ∈ Finset.range n, (r + i) := by
            exact
              integral_pow_eq_prod_gammaMeasure
                (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
                (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm)
                r hr n
  have hMomentGamma_s :
      ∀ n : ℕ, moment (fun x : ℝ ↦ max 0 x) n (gammaMeasure s 1) =
        ∏ j ∈ Finset.range n, (s + j) := by
    intro n
    rw [moment]
    calc
      ∫ x, (max 0 x) ^ n ∂gammaMeasure s 1 = ∫ x, x ^ n ∂gammaMeasure s 1 := by
        refine integral_congr_ae ?_
        filter_upwards [hMaxEq_s] with x hx
        simp [hx]
      _ = ∏ j ∈ Finset.range n, (s + j) := by
            exact
              integral_pow_eq_prod_gammaMeasure
                (P := P) (B := Bm) (Z := Zm) (r := r) (s := s)
                (hr := hr) (hs := hs) (hB := hBm) (hZ := hZm) (hBZ := hBmZm)
                s hs n
  have hX_det : IsMomentDeterminate P X0 :=
    isMomentDeterminate_of_hasFiniteAbsoluteMomentRootLimsup P hX_growth
  have hY_det : IsMomentDeterminate P Y0 :=
    isMomentDeterminate_of_hasFiniteAbsoluteMomentRootLimsup P hY_growth
  have hXMap :
      P.map X0 = (gammaMeasure r 1).map (fun x : ℝ ↦ max 0 x) := by
    exact
      IsMomentDeterminate.map_eq hX_det
        (gammaMeasure r 1) (fun x : ℝ ↦ max 0 x)
        (by fun_prop) hMaxMoments_r (fun n ↦ by rw [hMomentX n, hMomentGamma_r n])
  have hYMap :
      P.map Y0 = (gammaMeasure s 1).map (fun x : ℝ ↦ max 0 x) := by
    exact
      IsMomentDeterminate.map_eq hY_det
        (gammaMeasure s 1) (fun x : ℝ ↦ max 0 x)
        (by fun_prop) hMaxMoments_s (fun n ↦ by rw [hMomentY n, hMomentGamma_s n])
  have hXLaw : HasLaw X0 (gammaMeasure r 1) P := by
    refine ⟨hX0_meas.aemeasurable, ?_⟩
    calc
      P.map X0 = (gammaMeasure r 1).map (fun x : ℝ ↦ max 0 x) := hXMap
      _ = (gammaMeasure r 1).map (fun x : ℝ ↦ x) := Measure.map_congr hMaxEq_r
      _ = gammaMeasure r 1 := by simpa using (Measure.map_id' (gammaMeasure r 1))
  have hYLaw : HasLaw Y0 (gammaMeasure s 1) P := by
    refine ⟨hY0_meas.aemeasurable, ?_⟩
    calc
      P.map Y0 = (gammaMeasure s 1).map (fun x : ℝ ↦ max 0 x) := hYMap
      _ = (gammaMeasure s 1).map (fun x : ℝ ↦ x) := Measure.map_congr hMaxEq_s
      _ = gammaMeasure s 1 := by simpa using (Measure.map_id' (gammaMeasure s 1))
  have hJoint0 :
      HasLaw (fun ω ↦ (X0 ω, Y0 ω))
        ((gammaMeasure r 1).prod (gammaMeasure s 1)) P := by
    -- Proof comment: once the clipped marginals are identified and independent, the standard
    -- map-to-product characterization yields the joint product law.
    refine ⟨hX0_meas.aemeasurable.prodMk hY0_meas.aemeasurable, ?_⟩
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX0_meas.aemeasurable hY0_meas.aemeasurable).1
        hIndep0, hXLaw.map_eq, hYLaw.map_eq]
  have hX_eq : X0 =ᵐ[P] (fun ω ↦ B ω * Z ω) := by
    refine hX0_eq.trans ?_
    filter_upwards [hBm_eq, hZm_eq] with ω hBω hZω
    simp [hBω, hZω]
  have hY_eq : Y0 =ᵐ[P] (fun ω ↦ (1 - B ω) * Z ω) := by
    refine hY0_eq.trans ?_
    filter_upwards [hBm_eq, hZm_eq] with ω hBω hZω
    simp [hBω, hZω]
  have hPair_eq :
      (fun ω ↦ (B ω * Z ω, (1 - B ω) * Z ω)) =ᵐ[P]
        fun ω ↦ (X0 ω, Y0 ω) := by
    filter_upwards [hX_eq.symm, hY_eq.symm] with ω hXω hYω
    simp [hXω, hYω]
  exact hJoint0.congr hPair_eq

-- Proof sketch: combine the main joint-law statement with
-- `indepFun_iff_map_prod_eq_prod_map_map`; the product target measure is exactly the criterion for
-- independence of the two coordinates.
/-- The Beta-Gamma splitting transform sends an independent Beta/Gamma pair to two independent
unit-rate Gamma random variables. -/
theorem beta_gamma_unit_rate_split_indepFun
    :
    IndepFun (fun ω ↦ B ω * Z ω) (fun ω ↦ (1 - B ω) * Z ω) P := by
  let F : Ω → ℝ × ℝ := fun ω ↦ (B ω * Z ω, (1 - B ω) * Z ω)
  letI : IsProbabilityMeasure (betaMeasure r s) := isProbabilityMeasureBeta hr hs
  letI : IsProbabilityMeasure P := hB.isProbabilityMeasure
  letI : IsProbabilityMeasure (gammaMeasure r 1) := isProbabilityMeasure_gammaMeasure hr zero_lt_one
  letI : IsProbabilityMeasure (gammaMeasure s 1) := isProbabilityMeasure_gammaMeasure hs zero_lt_one
  have hJoint : HasLaw F ((gammaMeasure r 1).prod (gammaMeasure s 1)) P :=
    beta_gamma_unit_rate_split_hasLaw_prod
      (P := P) (B := B) (Z := Z) (r := r) (s := s) hr hs hB hZ hBZ
  have hFstLaw :
      HasLaw Prod.fst (gammaMeasure r 1) ((gammaMeasure r 1).prod (gammaMeasure s 1)) :=
    (measurePreserving_fst (μ := gammaMeasure r 1) (ν := gammaMeasure s 1)).hasLaw
  have hSndLaw :
      HasLaw Prod.snd (gammaMeasure s 1) ((gammaMeasure r 1).prod (gammaMeasure s 1)) :=
    (measurePreserving_snd (μ := gammaMeasure r 1) (ν := gammaMeasure s 1)).hasLaw
  have hFst : HasLaw (Prod.fst ∘ F) (gammaMeasure r 1) P :=
    HasLaw.comp hFstLaw hJoint
  have hSnd : HasLaw (Prod.snd ∘ F) (gammaMeasure s 1) P :=
    HasLaw.comp hSndLaw hJoint
  have hEta : (fun ω ↦ ((Prod.fst ∘ F) ω, (Prod.snd ∘ F) ω)) = F := by
    -- Proof comment: the independence criterion is stated for the explicit pair map attached to
    -- the two coordinate functions, which is definitionally the same random vector `F`.
    funext ω
    exact Prod.eta (F ω)
  have hIndep : IndepFun (Prod.fst ∘ F) (Prod.snd ∘ F) P := by
    -- Proof comment: the joint law already identifies the pair map with the product of its two
    -- Gamma marginals, so the standard map-to-product criterion applies directly.
    refine (indepFun_iff_map_prod_eq_prod_map_map hFst.aemeasurable hSnd.aemeasurable).2 ?_
    rw [hEta, hJoint.map_eq, hFst.map_eq, hSnd.map_eq]
  simpa [F, Function.comp] using hIndep

-- Proof sketch: compose the joint-law statement with the first-coordinate projection and use that
-- the first marginal of a product measure is the first factor.
/-- The first coordinate in the Beta-Gamma splitting transform has Gamma law with shape `r` and
unit rate. -/
theorem beta_gamma_unit_rate_split_fst_hasLaw
    :
    HasLaw (fun ω ↦ B ω * Z ω) (gammaMeasure r 1) P := by
  let F : Ω → ℝ × ℝ := fun ω ↦ (B ω * Z ω, (1 - B ω) * Z ω)
  letI : IsProbabilityMeasure (gammaMeasure r 1) := isProbabilityMeasure_gammaMeasure hr zero_lt_one
  letI : IsProbabilityMeasure (gammaMeasure s 1) := isProbabilityMeasure_gammaMeasure hs zero_lt_one
  have hJoint : HasLaw F ((gammaMeasure r 1).prod (gammaMeasure s 1)) P :=
    beta_gamma_unit_rate_split_hasLaw_prod
      (P := P) (B := B) (Z := Z) (r := r) (s := s) hr hs hB hZ hBZ
  have hFstLaw :
      HasLaw Prod.fst (gammaMeasure r 1) ((gammaMeasure r 1).prod (gammaMeasure s 1)) :=
    (measurePreserving_fst (μ := gammaMeasure r 1) (ν := gammaMeasure s 1)).hasLaw
  -- Proof comment: compose the joint split law with the first projection of the target product
  -- measure.
  simpa [F, Function.comp] using (HasLaw.comp hFstLaw hJoint)

-- Proof sketch: compose the joint-law statement with the second-coordinate projection and use
-- that the second marginal of a product measure is the second factor.
/-- The second coordinate in the Beta-Gamma splitting transform has Gamma law with shape `s` and
unit rate. -/
theorem beta_gamma_unit_rate_split_snd_hasLaw
    :
    HasLaw (fun ω ↦ (1 - B ω) * Z ω) (gammaMeasure s 1) P := by
  let F : Ω → ℝ × ℝ := fun ω ↦ (B ω * Z ω, (1 - B ω) * Z ω)
  letI : IsProbabilityMeasure (gammaMeasure r 1) := isProbabilityMeasure_gammaMeasure hr zero_lt_one
  letI : IsProbabilityMeasure (gammaMeasure s 1) := isProbabilityMeasure_gammaMeasure hs zero_lt_one
  have hJoint : HasLaw F ((gammaMeasure r 1).prod (gammaMeasure s 1)) P :=
    beta_gamma_unit_rate_split_hasLaw_prod
      (P := P) (B := B) (Z := Z) (r := r) (s := s) hr hs hB hZ hBZ
  have hSndLaw :
      HasLaw Prod.snd (gammaMeasure s 1) ((gammaMeasure r 1).prod (gammaMeasure s 1)) :=
    (measurePreserving_snd (μ := gammaMeasure r 1) (ν := gammaMeasure s 1)).hasLaw
  -- Proof comment: compose the joint split law with the second projection of the target product
  -- measure.
  simpa [F, Function.comp] using (HasLaw.comp hSndLaw hJoint)

end
