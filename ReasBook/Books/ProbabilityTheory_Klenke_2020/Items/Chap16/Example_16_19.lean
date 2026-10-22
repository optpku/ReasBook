/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Lemma_16_24
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Remark_16_21

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory MeasureTheory.ProbabilityMeasure

noncomputable section

/- Primitive owner input for Example 16.19: the centered Cauchy characteristic function is
already formalized as `charFun_centeredCauchyMeasure`. -/
recall charFun_centeredCauchyMeasure

/-- Helper for Example 16.19: the stable Lévy density with index `α` and one-sided coefficients
`c⁻`, `c⁺`. -/
def stableLevyDensity (α cMinus cPlus : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then
    cMinus * (-x) ^ (-α - 1)
  else if 0 < x then
    cPlus * x ^ (-α - 1)
  else
    0

/-- Helper for Example 16.19: the stable Lévy measure with index `α` and one-sided coefficients
`c⁻`, `c⁺`. -/
noncomputable def stableLevyMeasure (α cMinus cPlus : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (stableLevyDensity α cMinus cPlus x))

/-- Helper for Example 16.19: admissible one-sided coefficients for a nontrivial stable Lévy
measure. -/
def StableLevyCoefficients (cMinus cPlus : ℝ) : Prop :=
  0 ≤ cMinus ∧ 0 ≤ cPlus ∧ 0 < cMinus + cPlus

/-- Helper for Example 16.19: the centered unit Cauchy law has characteristic function
`t ↦ exp (-|t|)`. -/
lemma centeredUnitCauchy_charFun_eq_exp_neg_abs (t : ℝ) :
    charFun ((⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) t =
      Complex.exp (-(|t| : ℝ)) := by
  -- Specialize the centered Cauchy characteristic-function formula at unit scale.
  simpa using (charFun_centeredCauchyMeasure 1 (by norm_num) t)

/-- Helper for Example 16.19: the centered unit Cauchy characteristic function matches the
canonical symmetric `α = 1` stable normal form. -/
lemma centeredUnitCauchy_charFun_eq_symmetricStableCharFun (t : ℝ) :
    charFun ((⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) t =
      symmetricStableCharFun 1 1 t := by
  -- Proof comment: rewrite the explicit Cauchy formula into the stable characteristic-function
  -- normal form used by the Chapter 15 owner API.
  rw [centeredUnitCauchy_charFun_eq_exp_neg_abs, symmetricStableCharFun_apply]
  congr 1
  simp

/-- Helper for Example 16.19: the Chapter 15 triangular-characteristic measure is normalized.
This is the mass-one identity needed for the direct Cauchy exponent computation. -/
lemma triangularCharacteristicMeasure_isProbabilityMeasure (a : ℝ) (ha : 0 < a) :
    IsProbabilityMeasure (triangularCharacteristicMeasure a) := by
  -- Proof comment: evaluate the characteristic function at frequency `0` and read off the total
  -- mass via `charFun_zero`.
  rw [MeasureTheory.isProbabilityMeasure_iff_real, ← Complex.ofReal_inj]
  simpa [MeasureTheory.charFun_zero] using charFun_triangularCharacteristicMeasure a ha 0

/-- Helper for Example 16.19: the centered unit Cauchy law is not a Dirac mass. -/
lemma centeredUnitCauchy_ne_dirac (x : ℝ) :
    (⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) ≠ diracProba x := by
  -- Proof comment: compare the value at frequency `1`; the Cauchy norm is `exp (-1) < 1`,
  -- while every Dirac characteristic function has norm `1`.
  intro hx
  have hchar :
      charFun ((diracProba x : ProbabilityMeasure ℝ) : Measure ℝ) 1 =
        symmetricStableCharFun 1 1 1 := by
    have hchar0 := centeredUnitCauchy_charFun_eq_symmetricStableCharFun 1
    rw [hx] at hchar0
    exact hchar0
  have hnorm := congrArg norm hchar
  have hleft : ‖charFun ((diracProba x : ProbabilityMeasure ℝ) : Measure ℝ) 1‖ = 1 := by
    simpa [MeasureTheory.diracProba, MeasureTheory.charFun_dirac, Complex.norm_exp]
  have hright : ‖symmetricStableCharFun 1 1 1‖ = Real.exp (-1 : ℝ) := by
    simp [symmetricStableCharFun_apply, Complex.norm_exp]
  rw [hleft, hright] at hnorm
  have hexp_ne : Real.exp (-1 : ℝ) ≠ 1 := by
    exact ne_of_lt (by simpa using (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)))
  exact hexp_ne hnorm.symm

/-- Helper for Example 16.19: the centered unit Cauchy characteristic function satisfies the
canonical strict-stability scaling law at index `1`. -/
lemma centeredUnitCauchy_charFun_scaling (n : ℕ+) (t : ℝ) :
    charFun ((⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) t ^ (n : ℕ) =
      charFun ((⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))
        (((n : ℝ) ^ (1 / (1 : ℝ))) * t) := by
  -- Proof comment: raise the explicit formula `exp (-|t|)` to the `n`th power and rewrite the
  -- exponent as the same formula evaluated at the canonical index-`1` scaling factor.
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    positivity
  have hroot : (n : ℝ) ^ (1 / (1 : ℝ)) = (n : ℝ) := by
    simp
  have habs : |(((n : ℝ) ^ (1 / (1 : ℝ))) * t)| = (n : ℝ) * |t| := by
    rw [hroot, abs_mul, abs_of_nonneg hn_nonneg]
  calc
    charFun ((⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) t ^ (n : ℕ)
        = Complex.exp (((n : ℂ) * (-(|t| : ℝ) : ℂ))) := by
            rw [centeredUnitCauchy_charFun_eq_exp_neg_abs,
              (Complex.exp_nat_mul (-(|t| : ℝ) : ℂ) (n : ℕ)).symm]
    _ = Complex.exp (((-((n : ℝ) * |t|) : ℝ) : ℂ)) := by
          congr 1
          exact_mod_cast (show (n : ℝ) * (-(|t| : ℝ)) = -((n : ℝ) * |t|) by ring)
    _ = Complex.exp (-(|(((n : ℝ) ^ (1 / (1 : ℝ))) * t)| : ℝ)) := by
          congr 1
          rw [habs]
          simp
    _ = charFun ((⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))
          (((n : ℝ) ^ (1 / (1 : ℝ))) * t) := by
            rw [centeredUnitCauchy_charFun_eq_exp_neg_abs]

/-- Helper for Example 16.19: the centered unit Cauchy law is strictly stable with index `1`. -/
lemma centeredUnitCauchy_isStableWithIndexOne :
    IsStableWithIndex (⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) 1 := by
  -- Route correction: avoid importing `Remark_15_26`, whose current owner chain still requests
  -- `Example_16_2.olean`, and prove the index-`1` scaling law directly from the explicit Cauchy
  -- characteristic function.
  let μ : ProbabilityMeasure ℝ := ⟨cauchyMeasure 0 1, inferInstance⟩
  refine ⟨?_, by norm_num, ?_⟩
  · intro x
    simpa [μ] using centeredUnitCauchy_ne_dirac x
  · intro n
    let ν : ProbabilityMeasure ℝ :=
      map μ (measurable_affineMap ((n : ℝ) ^ (1 / (1 : ℝ))) 0).aemeasurable
    have hνfin : IsFiniteMeasure (ν : Measure ℝ) := by
      refine ⟨?_⟩
      simp [ν]
    letI : IsFiniteMeasure (ν : Measure ℝ) := hνfin
    apply Subtype.ext
    exact Measure.ext_of_charFun
      (μ := (((μ ^ (n : ℕ)) : ProbabilityMeasure ℝ) : Measure ℝ))
      (ν := (ν : Measure ℝ)) <| by
        funext t
        have hpow :
            charFun (((μ ^ (n : ℕ)) : ProbabilityMeasure ℝ) : Measure ℝ) t =
              charFun μ t ^ (n : ℕ) := by
          simpa using
            congrArg (fun f : ℝ → ℂ ↦ f t) (MeasureTheory.ProbabilityMeasure.charFun_pow μ (n : ℕ))
        calc
          charFun (((μ ^ (n : ℕ)) : ProbabilityMeasure ℝ) : Measure ℝ) t
              = charFun μ t ^ (n : ℕ) := hpow
          _ = charFun μ (((n : ℝ) ^ (1 / (1 : ℝ))) * t) := by
                simpa [μ] using centeredUnitCauchy_charFun_scaling n t
          _ = charFun (ν : Measure ℝ) t := by
                simpa [ν, MeasureTheory.ProbabilityMeasure.measurable_affineMap, zero_add] using
                  (MeasureTheory.charFun_map_mul
                    (μ := (μ : Measure ℝ)) (((n : ℝ) ^ (1 / (1 : ℝ)))) t).symm

/-- Helper for Example 16.19: the centered unit Cauchy law is broadly stable with index `1`,
with zero centering sequence. -/
lemma centeredUnitCauchy_isStableInBroadSenseWithIndexOne :
    IsStableInBroadSenseWithIndex (⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) 1 := by
  -- Proof comment: strict stability is the broad-stability statement with the centering sequence
  -- identically zero.
  refine ⟨centeredUnitCauchy_isStableWithIndexOne.1,
    centeredUnitCauchy_isStableWithIndexOne.2.1, ?_⟩
  refine ⟨fun _ ↦ 0, ?_⟩
  intro n
  simpa using centeredUnitCauchy_isStableWithIndexOne.2.2 n

/-- Helper for Example 16.19: the centered unit Cauchy law is stable in the broad sense. -/
lemma centeredUnitCauchy_isStableInBroadSense :
    IsStableInBroadSense (⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) := by
  -- Proof comment: forget the index data and reuse the same affine scaling with zero centering.
  refine ⟨centeredUnitCauchy_isStableWithIndexOne.1, ?_⟩
  refine ⟨fun n ↦ (n : ℝ) ^ (1 / (1 : ℝ)), fun _ ↦ 0, ?_, ?_⟩
  · intro n
    positivity
  · intro n
    exact centeredUnitCauchy_isStableWithIndexOne.2.2 n

/-- Helper for Example 16.19: the centered unit Cauchy law is symmetric under `x ↦ -x`. -/
lemma centeredUnitCauchy_isNegInvariant :
    (((⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ)).IsNegInvariant := by
  -- Route correction: now that the Chapter 15 owner lemma is available on the trimmed import
  -- surface, reuse the canonical symmetry API instead of reproving evenness by hand.
  exact
    isNegInvariant_of_charFun_eq_symmetricStableCharFun
      (⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)
      centeredUnitCauchy_charFun_eq_symmetricStableCharFun

/-- Helper for Example 16.19: negating a canonical Lévy measure preserves canonicality. -/
lemma isCanonicalMeasure_map_neg {ν : Measure ℝ} (hν : IsCanonicalMeasure ν) :
    IsCanonicalMeasure (Measure.map (fun x : ℝ ↦ -x) ν) := by
  -- Proof comment: the map `x ↦ -x` fixes the origin and preserves `min (x^2) 1`, so both
  -- canonical-measure conditions are transported through the measurable equivalence.
  refine ⟨?_, ?_⟩
  · have hpre : (fun x : ℝ ↦ -x) ⁻¹' ({0} : Set ℝ) = ({0} : Set ℝ) := by
      ext x
      simp
    simpa [hpre, hν.measure_singleton_zero] using
      (Measure.map_apply
        (μ := ν)
        (f := fun x : ℝ ↦ -x)
        (s := ({0} : Set ℝ))
        (by fun_prop)
        (measurableSet_singleton (0 : ℝ)))
  · have hcomp :
        Integrable ((fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1) ∘ fun x : ℝ ↦ -x) ν := by
      simpa [Function.comp_def] using hν.integrable_sq_min_one
    simpa [Function.comp_def] using
      (integrable_map_equiv
        (μ := ν)
        (MeasurableEquiv.neg ℝ)
        (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1)).2 hcomp

/-- Helper for Example 16.19: negating a Lévy--Khintchin triple evaluates the exponent at `-t`. -/
lemma levyKhinchinExponent_map_neg (τ : LevyKhinchinTriple) (t : ℝ) :
    levyKhinchinExponent
      { sigma2 := τ.sigma2
        b := -τ.b
        ν := Measure.map (fun x : ℝ ↦ -x) τ.ν } t =
      levyKhinchinExponent τ (-t) := by
  -- Proof comment: push the Lévy integral through the negation equivalence and use that the
  -- canonical centering function is odd.
  have hmap :
      ∫ x : ℝ,
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I))
        ∂Measure.map (fun x : ℝ ↦ -x) τ.ν
        =
      ∫ x : ℝ,
          (Complex.exp (((t * (-x) : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * levyKhinchinCanonicalCentering (-x) : ℝ) : ℂ) * Complex.I))
        ∂τ.ν := by
    simpa using
      (integral_map_equiv
        (μ := τ.ν)
        (MeasurableEquiv.neg ℝ)
        (fun x : ℝ ↦
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)))
  rw [levyKhinchinExponent, levyKhinchinExponentWithCentering,
    levyKhinchinExponent, levyKhinchinExponentWithCentering, hmap]
  have hkernel :
      (fun x : ℝ ↦
        Complex.exp (((t * (-x) : ℝ) : ℂ) * Complex.I) - 1 -
          (((t * levyKhinchinCanonicalCentering (-x) : ℝ) : ℂ) * Complex.I)) =
        fun x : ℝ ↦
          Complex.exp ((((-t) * x : ℝ) : ℂ) * Complex.I) - 1 -
            ((((-t) * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) := by
    funext x
    by_cases hx : |x| < 1
    · have hnegx : |-x| < 1 := by simpa [abs_neg] using hx
      simp [levyKhinchinCanonicalCentering, hx, hnegx]
    · have hnegx : ¬ |-x| < 1 := by simpa [abs_neg] using hx
      simp [levyKhinchinCanonicalCentering, hx, hnegx]
  rw [hkernel]
  congr 1
  ring

/-- Helper for Example 16.19: symmetry of the law transports a Lévy--Khintchin representation to
the negated triple. -/
lemma negInvariant_hasLevyKhinchinRepresentation_neg
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hμneg : ((μ : Measure ℝ)).IsNegInvariant)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    HasLevyKhinchinRepresentation μ
      { sigma2 := τ.sigma2
        b := -τ.b
        ν := Measure.map (fun x : ℝ ↦ -x) τ.ν } := by
  -- Proof comment: use negation invariance to rewrite `charFun μ t` as `charFun μ (-t)`, then
  -- transport the exponent with `levyKhinchinExponent_map_neg`.
  constructor
  · refine ⟨hτ.isCanonicalTriple.sigma2_nonneg,
      isCanonicalMeasure_map_neg hτ.isCanonicalTriple.isCanonicalMeasure⟩
  · intro t
    calc
      charFun μ t = charFun ((μ : Measure ℝ).neg) t := by
        rw [hμneg.neg_eq_self]
      _ = charFun (μ : Measure ℝ) (-t) := by
        simpa [Measure.neg] using
          (MeasureTheory.charFun_map_mul (μ := (μ : Measure ℝ)) (-1) t)
      _ = Complex.exp (levyKhinchinExponent τ (-t)) := hτ.charFun_eq_exp (-t)
      _ = Complex.exp
            (levyKhinchinExponent
              { sigma2 := τ.sigma2
                b := -τ.b
                ν := Measure.map (fun x : ℝ ↦ -x) τ.ν } t) := by
            rw [levyKhinchinExponent_map_neg]

/-- Helper for Example 16.19: the symmetric `α = 1` stable Lévy density is the textbook
inverse-square kernel `(π x^2)⁻¹`. -/
lemma stableLevyDensityOneOverPi_eq_invSq (x : ℝ) :
    stableLevyDensity 1 (1 / Real.pi) (1 / Real.pi) x = 1 / (Real.pi * x ^ (2 : ℕ)) := by
  by_cases hx : x < 0
  · -- Proof comment: on the negative half-line, rewrite the `rpow` exponent `-2` as an inverse
    -- square and then identify `(-x)^2 = x^2`.
    have hx0 : x ≠ 0 := ne_of_lt hx
    have hinv : (-x)⁻¹ = -x⁻¹ := by
      field_simp [hx0]
    rw [stableLevyDensity, if_pos hx, show (-((1 : ℝ)) - 1) = -(2 : ℝ) by ring,
      Real.rpow_neg_eq_inv_rpow, hinv]
    field_simp [hx0, Real.pi_ne_zero]
    have hsq : x ^ 2 * (-(1 / x)) ^ 2 = 1 := by
      calc
        x ^ 2 * (-(1 / x)) ^ 2 = (x * (-(1 / x))) ^ 2 := by ring
        _ = 1 := by
          have hmul : x * (-(1 / x)) = -1 := by
            field_simp [hx0]
          rw [hmul]
          norm_num
    exact (by simpa [Real.rpow_natCast] using hsq : x ^ 2 * (-(1 / x)) ^ (2 : ℝ) = 1)
  · by_cases hx0 : x = 0
    · -- Proof comment: both the stable density and the inverse-square expression vanish at the
      -- origin because the owner density was defined with an explicit zero branch.
      simp [stableLevyDensity, hx, hx0]
    · -- Proof comment: on the positive half-line, the same inverse-square normalization applies.
      have hxpos : 0 < x := lt_of_le_of_ne (not_lt.mp hx) (by
        exact fun h => hx0 h.symm)
      rw [stableLevyDensity, if_neg hx, if_pos hxpos, show (-((1 : ℝ)) - 1) = -(2 : ℝ) by ring,
        Real.rpow_neg_eq_inv_rpow]
      field_simp [hx0, Real.pi_ne_zero]
      have hsq : x ^ 2 * (1 / x) ^ 2 = 1 := by
        calc
          x ^ 2 * (1 / x) ^ 2 = (x * (1 / x)) ^ 2 := by ring
          _ = 1 := by
            have hmul : x * (1 / x) = 1 := by
              field_simp [hx0]
            rw [hmul]
            norm_num
      exact (by simpa [Real.rpow_natCast] using hsq : x ^ 2 * (1 / x) ^ (2 : ℝ) = 1)

/-- Helper for Example 16.19: the inverse-square density is measurable on `ℝ`. -/
lemma measurable_inverseSquareDensity :
    Measurable (fun x : ℝ ↦ ENNReal.ofReal (1 / (Real.pi * x ^ (2 : ℕ)))) := by
  fun_prop

/-- Helper for Example 16.19: the target Lévy measure is Lebesgue measure with inverse-square
density. -/
lemma stableLevyMeasureOneOverPi_eq_withDensity_invSq :
    stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) =
      volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (1 / (Real.pi * x ^ (2 : ℕ)))) := by
  rw [stableLevyMeasure]
  congr 1
  funext x
  rw [stableLevyDensityOneOverPi_eq_invSq]

/-- Helper for Example 16.19: the inverse-square density sits in the real-valued normal form after
crossing the `ENNReal.ofReal`/`toReal` boundary. -/
lemma inverseSquareDensity_toReal (x : ℝ) :
    ((ENNReal.ofReal (1 / (Real.pi * x ^ (2 : ℕ)))).toReal : ℝ) =
      1 / (Real.pi * x ^ (2 : ℕ)) := by
  -- Proof comment: the inverse-square density is nonnegative, so `toReal (ofReal r)` collapses
  -- back to the original real expression.
  rw [ENNReal.toReal_ofReal]
  positivity

/-- Helper for Example 16.19: on the positive tail, the inverse-square density is dominated by the
standard integrable kernel `(1 + x^2)⁻¹`. -/
lemma inverseSquarePositiveTail_domination {x : ℝ} (hx : x ∈ Set.Ioi (1 : ℝ)) :
    |1 / (Real.pi * x ^ (2 : ℕ))| ≤ (2 / Real.pi) * (1 + x ^ (2 : ℕ))⁻¹ := by
  -- Proof comment: on `x > 1`, both denominators are positive, so clearing denominators reduces
  -- the estimate to `1 + x^2 ≤ 2 x^2`.
  have hxgt : 1 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hxgt)
  have hleft_nonneg : 0 ≤ 1 / (Real.pi * x ^ (2 : ℕ)) := by
    positivity
  rw [abs_of_nonneg hleft_nonneg]
  have hsq_bound : 1 + x ^ (2 : ℕ) ≤ 2 * x ^ (2 : ℕ) := by
    nlinarith [hxgt]
  have hineq :
      1 / (Real.pi * x ^ (2 : ℕ)) ≤ (2 / Real.pi) * (1 + x ^ (2 : ℕ))⁻¹ := by
    field_simp [hx0, Real.pi_ne_zero]
    nlinarith [Real.pi_pos, hsq_bound]
  exact hineq

/-- Helper for Example 16.19: the positive inverse-square tail is Lebesgue integrable. -/
lemma inverseSquarePositiveTail_integrable :
    Integrable
      (Set.indicator (Set.Ioi (1 : ℝ))
        (fun x : ℝ ↦ 1 / (Real.pi * x ^ (2 : ℕ)))) := by
  -- Proof comment: dominate the positive tail by the standard integrable kernel
  -- `(2 / π) * (1 + x²)⁻¹` on the same tail.
  have hbound :
      Integrable
        (Set.indicator (Set.Ioi (1 : ℝ))
          (fun x : ℝ ↦ (2 / Real.pi) * (1 + x ^ (2 : ℕ))⁻¹)) := by
    exact (integrable_inv_one_add_sq.const_mul (2 / Real.pi)).indicator measurableSet_Ioi
  have hmeas :
      Measurable
        (Set.indicator (Set.Ioi (1 : ℝ))
          (fun x : ℝ ↦ 1 / (Real.pi * x ^ (2 : ℕ)))) := by
    exact
      (show Measurable (fun x : ℝ ↦ 1 / (Real.pi * x ^ (2 : ℕ))) by fun_prop).indicator
        measurableSet_Ioi
  refine Integrable.mono' hbound hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  by_cases hx : x ∈ Set.Ioi (1 : ℝ)
  · have hdom := inverseSquarePositiveTail_domination hx
    have hrightNonneg : 0 ≤ (2 / Real.pi) * (1 + x ^ (2 : ℕ))⁻¹ := by
      positivity
    simpa [hx, Real.norm_eq_abs, abs_of_nonneg hrightNonneg] using hdom
  · simp [hx]

/-- Helper for Example 16.19: the negative inverse-square tail is Lebesgue integrable. -/
lemma inverseSquareNegativeTail_integrable :
    Integrable
      (Set.indicator (Set.Iio (-1 : ℝ))
        (fun x : ℝ ↦ 1 / (Real.pi * x ^ (2 : ℕ)))) := by
  -- Proof comment: reflect `Iio (-1)` to `Ioi 1` by the measurable equivalence `x ↦ -x`.
  have hcomp :
      Integrable
        ((Set.indicator (Set.Iio (-1 : ℝ))
          (fun x : ℝ ↦ 1 / (Real.pi * x ^ (2 : ℕ)))) ∘ fun x : ℝ ↦ -x)
        (volume : Measure ℝ) := by
    have hcompEq :
        ((Set.indicator (Set.Iio (-1 : ℝ))
          (fun x : ℝ ↦ 1 / (Real.pi * x ^ (2 : ℕ)))) ∘ fun x : ℝ ↦ -x) =
          Set.indicator (Set.Ioi (1 : ℝ))
            (fun x : ℝ ↦ 1 / (Real.pi * x ^ (2 : ℕ))) := by
      funext x
      by_cases hx : x ∈ Set.Ioi (1 : ℝ)
      · have hneg : -x ∈ Set.Iio (-1 : ℝ) := by simpa using hx
        simp [Function.comp_def, hx, hneg, pow_two, mul_comm, mul_left_comm, mul_assoc]
      · have hneg : -x ∉ Set.Iio (-1 : ℝ) := by simpa using hx
        simp [Function.comp_def, hx, hneg]
    rw [hcompEq]
    exact inverseSquarePositiveTail_integrable
  have hmap :
      Integrable
        (Set.indicator (Set.Iio (-1 : ℝ))
          (fun x : ℝ ↦ 1 / (Real.pi * x ^ (2 : ℕ))))
        (Measure.map (fun x : ℝ ↦ -x) (volume : Measure ℝ)) := by
    exact
      (integrable_map_equiv
        (μ := (volume : Measure ℝ))
        (MeasurableEquiv.neg ℝ)
        (Set.indicator (Set.Iio (-1 : ℝ))
          (fun x : ℝ ↦ 1 / (Real.pi * x ^ (2 : ℕ))))).2 hcomp
  simpa [Measure.map_neg_eq_self] using hmap

/-- Helper for Example 16.19: the compact core `[-1, 1] \ {0}` contributes only a bounded
constant indicator, hence is Lebesgue integrable. -/
lemma inverseSquareCompactCore_integrable :
    Integrable
      (Set.indicator (Set.Icc (-1 : ℝ) 1 \ ({0} : Set ℝ))
        (fun _ : ℝ ↦ (1 / Real.pi : ℝ))) := by
  -- Proof comment: the core set is measurable and sits inside the finite-volume interval
  -- `[-1, 1]`, so the bounded indicator is integrable.
  have hmeas : MeasurableSet (Set.Icc (-1 : ℝ) 1 \ ({0} : Set ℝ)) := by
    exact measurableSet_Icc.diff (measurableSet_singleton (0 : ℝ))
  have hfinite :
      volume (Set.Icc (-1 : ℝ) 1 \ ({0} : Set ℝ)) ≠ ⊤ := by
    exact ((measure_mono Set.diff_subset).trans_lt measure_Icc_lt_top).ne
  rw [integrable_indicator_iff hmeas]
  exact integrableOn_const hfinite

/-- Helper for Example 16.19: the truncated inverse-square kernel splits into the compact core
plus the positive and negative inverse-square tails. -/
lemma inverseSquareCanonicalIntegrand_eq_indicatorSum :
    (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1 * (1 / (Real.pi * x ^ (2 : ℕ)))) =
      fun x : ℝ ↦
        Set.indicator (Set.Icc (-1 : ℝ) 1 \ ({0} : Set ℝ))
          (fun _ : ℝ ↦ (1 / Real.pi : ℝ)) x +
        Set.indicator (Set.Ioi (1 : ℝ))
          (fun y : ℝ ↦ 1 / (Real.pi * y ^ (2 : ℕ))) x +
        Set.indicator (Set.Iio (-1 : ℝ))
          (fun y : ℝ ↦ 1 / (Real.pi * y ^ (2 : ℕ))) x := by
  -- Proof comment: inside `[-1, 1] \ {0}` the truncation cancels one factor `x²`, while outside
  -- that interval the truncation is `1` and the kernel is exactly one of the two tails.
  funext x
  by_cases hltNeg : x < -1
  · have hsq : 1 ≤ x ^ (2 : ℕ) := by
      nlinarith [hltNeg]
    have hmin : min (x ^ (2 : ℕ)) 1 = 1 := min_eq_right hsq
    have hcore : x ∉ Set.Icc (-1 : ℝ) 1 \ ({0} : Set ℝ) := by
      simp [Set.mem_diff, hltNeg, not_le.mpr hltNeg]
    have hpos' : ¬ 1 < x := by
      linarith
    have hpos : x ∉ Set.Ioi (1 : ℝ) := by
      simpa using hpos'
    have hnegIndicator :
        Set.indicator (Set.Iio (-1 : ℝ))
          (fun y : ℝ ↦ 1 / (Real.pi * y ^ (2 : ℕ))) x =
          1 / (Real.pi * x ^ (2 : ℕ)) :=
      Set.indicator_of_mem (show x ∈ Set.Iio (-1 : ℝ) from hltNeg) _
    rw [hmin]
    calc
      1 * (1 / (Real.pi * x ^ (2 : ℕ)))
          = 0 + 0 + 1 / (Real.pi * x ^ (2 : ℕ)) := by ring
      _ = Set.indicator (Set.Icc (-1 : ℝ) 1 \ ({0} : Set ℝ))
            (fun _ : ℝ ↦ (1 / Real.pi : ℝ)) x +
          Set.indicator (Set.Ioi (1 : ℝ))
            (fun y : ℝ ↦ 1 / (Real.pi * y ^ (2 : ℕ))) x +
          Set.indicator (Set.Iio (-1 : ℝ))
            (fun y : ℝ ↦ 1 / (Real.pi * y ^ (2 : ℕ))) x := by
            rw [Set.indicator_of_notMem hcore, Set.indicator_of_notMem hpos, hnegIndicator]
  · by_cases hgtPos : 1 < x
    · have hsq : 1 ≤ x ^ (2 : ℕ) := by
        nlinarith [hgtPos]
      have hmin : min (x ^ (2 : ℕ)) 1 = 1 := min_eq_right hsq
      have hcore : x ∉ Set.Icc (-1 : ℝ) 1 \ ({0} : Set ℝ) := by
        simp [Set.mem_diff, hgtPos, not_le.mpr hgtPos]
      have hneg' : ¬ x < -1 := by
        linarith
      have hneg : x ∉ Set.Iio (-1 : ℝ) := by
        simpa using hneg'
      have hposIndicator :
          Set.indicator (Set.Ioi (1 : ℝ))
            (fun y : ℝ ↦ 1 / (Real.pi * y ^ (2 : ℕ))) x =
            1 / (Real.pi * x ^ (2 : ℕ)) :=
        Set.indicator_of_mem (show x ∈ Set.Ioi (1 : ℝ) from hgtPos) _
      rw [hmin]
      calc
        1 * (1 / (Real.pi * x ^ (2 : ℕ)))
            = 0 + 1 / (Real.pi * x ^ (2 : ℕ)) + 0 := by ring
        _ = Set.indicator (Set.Icc (-1 : ℝ) 1 \ ({0} : Set ℝ))
              (fun _ : ℝ ↦ (1 / Real.pi : ℝ)) x +
            Set.indicator (Set.Ioi (1 : ℝ))
              (fun y : ℝ ↦ 1 / (Real.pi * y ^ (2 : ℕ))) x +
            Set.indicator (Set.Iio (-1 : ℝ))
              (fun y : ℝ ↦ 1 / (Real.pi * y ^ (2 : ℕ))) x := by
              rw [Set.indicator_of_notMem hcore, hposIndicator, Set.indicator_of_notMem hneg]
    · by_cases hx0 : x = 0
      · simp [hx0]
      · have hxlo : -1 ≤ x := le_of_not_gt hltNeg
        have hxhi : x ≤ 1 := le_of_not_gt hgtPos
        have hsq : x ^ (2 : ℕ) ≤ 1 := by
          nlinarith [hxlo, hxhi]
        have hmin : min (x ^ (2 : ℕ)) 1 = x ^ (2 : ℕ) := min_eq_left hsq
        have hsq0 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx0
        have hxcore : x ∈ Set.Icc (-1 : ℝ) 1 \ ({0} : Set ℝ) := by
          simp [Set.mem_diff, hxlo, hxhi, hx0]
        have hpos : x ∉ Set.Ioi (1 : ℝ) := by
          exact not_lt.mpr hxhi
        have hneg : x ∉ Set.Iio (-1 : ℝ) := by
          exact not_lt.mpr hxlo
        have hcoreIndicator :
            Set.indicator (Set.Icc (-1 : ℝ) 1 \ ({0} : Set ℝ))
              (fun _ : ℝ ↦ (1 / Real.pi : ℝ)) x =
              (1 / Real.pi : ℝ) :=
          Set.indicator_of_mem hxcore _
        rw [hmin]
        calc
          x ^ (2 : ℕ) * (1 / (Real.pi * x ^ (2 : ℕ))) = 1 / Real.pi := by
            field_simp [hsq0, Real.pi_ne_zero]
          _ = 1 / Real.pi + 0 + 0 := by ring
          _ = Set.indicator (Set.Icc (-1 : ℝ) 1 \ ({0} : Set ℝ))
                (fun _ : ℝ ↦ (1 / Real.pi : ℝ)) x +
              Set.indicator (Set.Ioi (1 : ℝ))
                (fun y : ℝ ↦ 1 / (Real.pi * y ^ (2 : ℕ))) x +
              Set.indicator (Set.Iio (-1 : ℝ))
                (fun y : ℝ ↦ 1 / (Real.pi * y ^ (2 : ℕ))) x := by
                rw [hcoreIndicator, Set.indicator_of_notMem hpos, Set.indicator_of_notMem hneg]

/-- Helper for Example 16.19: the truncated inverse-square kernel is integrable on Lebesgue
measure. -/
lemma inverseSquareCanonicalIntegrand_integrable :
    Integrable
      (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1 * (1 / (Real.pi * x ^ (2 : ℕ)))) := by
  -- Route correction: isolate the compact core as a separate bounded indicator before adding the
  -- positive and negative tails. This keeps the canonical-integrability proof in a stable normal
  -- form.
  -- Proof comment: after the exact indicator decomposition, integrability is just closure under
  -- finite sums of the compact core and the two tail integrals.
  rw [inverseSquareCanonicalIntegrand_eq_indicatorSum]
  exact
    (inverseSquareCompactCore_integrable.add inverseSquarePositiveTail_integrable).add
      inverseSquareNegativeTail_integrable

/-- Helper for Example 16.19: the triangular density also survives the
`ENNReal.ofReal`/`toReal` normalization unchanged. -/
lemma triangularCharacteristicDensity_toReal {a x : ℝ} (ha : 0 < a) :
    ((ENNReal.ofReal
        (((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ)))).toReal : ℝ) =
      (((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ))) := by
  -- Proof comment: the triangular density is nonnegative because `1 - cos (a x) ≥ 0`,
  -- `a > 0`, and `x^2 ≥ 0`.
  have hnonneg :
      0 ≤ (((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ))) := by
    have hcos : 0 ≤ 1 - Real.cos (a * x) := sub_nonneg.mpr (Real.cos_le_one (a * x))
    have hnum : 0 ≤ (1 / Real.pi) * (1 - Real.cos (a * x)) := by
      positivity
    have hden : 0 ≤ a * x ^ (2 : ℕ) := by
      positivity
    exact div_nonneg hnum hden
  rw [ENNReal.toReal_ofReal hnonneg]

/-- Helper for Example 16.19: the triangular-characteristic density integrates to `1`. -/
lemma triangularCharacteristicDensity_integral_one {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, (((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ))) = 1 := by
  -- Proof comment: rewrite the total mass of `triangularCharacteristicMeasure a` as the
  -- Lebesgue integral of its density and then use that the measure has total mass `1`.
  letI : IsProbabilityMeasure (triangularCharacteristicMeasure a) :=
    triangularCharacteristicMeasure_isProbabilityMeasure a ha
  have hDensityMeas :
      Measurable
        (fun x : ℝ ↦
          ENNReal.ofReal
            (((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ)))) := by
    fun_prop
  have hfinite :
      ∀ᵐ x ∂(volume : Measure ℝ),
        ENNReal.ofReal
            (((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ))) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ by simp
  calc
    ∫ x : ℝ, (((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ)))
        = ∫ x : ℝ,
            (((ENNReal.ofReal
                (((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ)))).toReal : ℝ)) := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [triangularCharacteristicDensity_toReal ha]
    _ = ∫ x : ℝ, (1 : ℝ) ∂ triangularCharacteristicMeasure a := by
          rw [triangularCharacteristicMeasure,
            integral_withDensity_eq_integral_toReal_smul
              (μ := volume)
              (f := fun x : ℝ ↦
                ENNReal.ofReal
                  (((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ))))
              hDensityMeas
              hfinite]
          simp
    _ = 1 := by
          simpa using (integral_const (μ := triangularCharacteristicMeasure a) (1 : ℝ))

/-- Helper for Example 16.19: the explicit target Lévy measure is canonical. -/
lemma stableLevyMeasureOneOverPi_isCanonicalMeasure :
    IsCanonicalMeasure (stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi)) := by
  -- Proof comment: rewrite the target measure as a Lebesgue `withDensity`, check that the
  -- density vanishes at `0`, and transport the already-proved truncated-kernel integrability
  -- through the standard `withDensity` integrability criterion.
  refine ⟨?_, ?_⟩
  · rw [stableLevyMeasureOneOverPi_eq_withDensity_invSq,
      withDensity_apply _ (measurableSet_singleton 0)]
    simp
  · rw [stableLevyMeasureOneOverPi_eq_withDensity_invSq]
    have hweighted :
        Integrable
          (fun x : ℝ ↦
            min (x ^ (2 : ℕ)) 1 *
              (((ENNReal.ofReal (1 / (Real.pi * x ^ (2 : ℕ)))).toReal : ℝ))) := by
      -- Proof comment: the weighted base-measure integrand is exactly the truncated
      -- inverse-square kernel proved integrable above.
      refine inverseSquareCanonicalIntegrand_integrable.congr ?_
      filter_upwards with x
      rw [inverseSquareDensity_toReal]
    exact
      (integrable_withDensity_iff
        (μ := volume)
        (f := fun x : ℝ ↦ ENNReal.ofReal (1 / (Real.pi * x ^ (2 : ℕ))))
        measurable_inverseSquareDensity
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)
        (g := fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1)).2 hweighted

/-- Helper for Example 16.19: integrating the Cauchy Lévy real-part kernel yields `|t|`. -/
lemma cosineDensityScaledMass_eq_abs (t : ℝ) :
    ∫ x : ℝ, (1 - Real.cos (t * x)) / (Real.pi * x ^ (2 : ℕ)) = |t| := by
  -- Route correction: specialize the exact mass-one density identity for
  -- `triangularCharacteristicMeasure |t|` instead of rebuilding a scaling argument.
  -- Proof comment: split `t = 0` and otherwise factor out `|t|` to match the normalized
  -- triangular density.
  by_cases ht : t = 0
  · simp [ht]
  · let a : ℝ := |t|
    have ha : 0 < a := abs_pos.mpr ht
    have hcos :
        ∀ x : ℝ, Real.cos (t * x) = Real.cos (a * x) := by
      intro x
      by_cases ht_nonneg : 0 ≤ t
      · simp [a, abs_of_nonneg ht_nonneg]
      · have ht_neg : t < 0 := lt_of_not_ge ht_nonneg
        simp [a, abs_of_neg ht_neg, Real.cos_neg, mul_comm, mul_left_comm, mul_assoc]
    have hfactor :
        ∀ x : ℝ,
          (1 - Real.cos (a * x)) / (Real.pi * x ^ (2 : ℕ)) =
            a * ((((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ)))) := by
      intro x
      by_cases hx : x = 0
      · simp [hx, ha.ne']
      · field_simp [hx, ha.ne', Real.pi_ne_zero]
    calc
      ∫ x : ℝ, (1 - Real.cos (t * x)) / (Real.pi * x ^ (2 : ℕ))
          = ∫ x : ℝ, (1 - Real.cos (a * x)) / (Real.pi * x ^ (2 : ℕ)) := by
              refine integral_congr_ae ?_
              filter_upwards with x
              rw [hcos x]
      _ = ∫ x : ℝ, a * ((((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ)))) := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [hfactor x]
      _ = a * ∫ x : ℝ, (((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ (2 : ℕ))) := by
            rw [integral_const_mul]
      _ = a := by
            rw [triangularCharacteristicDensity_integral_one ha]
            ring
      _ = |t| := rfl

/-- Helper for Example 16.19: the cosine part of the target Lévy kernel integrates to `-|t|`. -/
lemma stableLevyMeasureOneOverPi_cosinePart_eq_negAbs (t : ℝ) :
    ∫ x : ℝ, (Real.cos (t * x) - 1) ∂ stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) = -|t| := by
  -- Proof comment: rewrite the target measure as the inverse-square `withDensity` measure and
  -- then identify the weighted integrand with the negative of the already-normalized Cauchy
  -- density from `cosineDensityScaledMass_eq_abs`.
  rw [stableLevyMeasureOneOverPi_eq_withDensity_invSq,
    integral_withDensity_eq_integral_toReal_smul
      (μ := volume)
      (f := fun x : ℝ ↦ ENNReal.ofReal (1 / (Real.pi * x ^ (2 : ℕ))))
      measurable_inverseSquareDensity
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have hrewrite :
      (fun x : ℝ ↦
        (((ENNReal.ofReal (1 / (Real.pi * x ^ (2 : ℕ)))).toReal : ℝ)) •
          (Real.cos (t * x) - 1)) =
        fun x : ℝ ↦ -((1 - Real.cos (t * x)) / (Real.pi * x ^ (2 : ℕ))) := by
    funext x
    rw [inverseSquareDensity_toReal]
    simp [smul_eq_mul]
    ring
  rw [hrewrite, integral_neg]
  simpa using congrArg Neg.neg (cosineDensityScaledMass_eq_abs t)

/-- Helper for Example 16.19: the canonical centering cutoff is odd. -/
lemma levyKhinchinCanonicalCentering_neg (x : ℝ) :
    levyKhinchinCanonicalCentering (-x) = -levyKhinchinCanonicalCentering x := by
  -- Proof comment: the cutoff depends only on `|x| < 1`, and on that region it agrees with the
  -- identity map.
  by_cases hx : |x| < 1
  · simp [levyKhinchinCanonicalCentering, hx, abs_neg]
  · simp [levyKhinchinCanonicalCentering, hx, abs_neg]

/-- Helper for Example 16.19: symmetry forces the odd part of the target Lévy kernel to integrate
to zero. -/
lemma stableLevyMeasureOneOverPi_oddPart_eq_zero (t : ℝ) :
    ∫ x : ℝ, (Real.sin (t * x) - t * levyKhinchinCanonicalCentering x)
      ∂ stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) = 0 := by
  -- Proof comment: rewrite the inverse-square Lévy integral back to Lebesgue measure, observe
  -- that the resulting kernel is odd, and cancel it by reflection through `x ↦ -x`.
  let g : ℝ → ℝ :=
    fun x ↦
      (((ENNReal.ofReal (1 / (Real.pi * x ^ (2 : ℕ)))).toReal : ℝ)) *
        (Real.sin (t * x) - t * levyKhinchinCanonicalCentering x)
  have htarget :
      ∫ x : ℝ, (Real.sin (t * x) - t * levyKhinchinCanonicalCentering x)
        ∂ stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) =
        ∫ x : ℝ, g x := by
    rw [stableLevyMeasureOneOverPi_eq_withDensity_invSq,
      integral_withDensity_eq_integral_toReal_smul
        (μ := volume)
        (f := fun x : ℝ ↦ ENNReal.ofReal (1 / (Real.pi * x ^ (2 : ℕ))))
        measurable_inverseSquareDensity
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    rfl
  have hmap :
      ∫ x : ℝ, g x = ∫ x : ℝ, g (-x) := by
    simpa [g] using
      (integral_map_equiv
        (μ := (volume : Measure ℝ))
        (MeasurableEquiv.neg ℝ)
        g)
  have hodd : ∀ x : ℝ, g (-x) = -g x := by
    intro x
    dsimp [g]
    rw [inverseSquareDensity_toReal (-x), inverseSquareDensity_toReal x,
      levyKhinchinCanonicalCentering_neg]
    simp [Real.sin_neg, pow_two, mul_comm, mul_left_comm, mul_assoc]
    ring
  have hzeroAux : ∫ x : ℝ, g x = 0 := by
    have hselfNeg :
        ∫ x : ℝ, g x = -∫ x : ℝ, g x := by
      calc
        ∫ x : ℝ, g x = ∫ x : ℝ, g (-x) := hmap
        _ = ∫ x : ℝ, -g x := by
              refine integral_congr_ae ?_
              filter_upwards with x
              rw [hodd x]
        _ = -∫ x : ℝ, g x := by
              rw [integral_neg]
    linarith
  exact htarget.trans hzeroAux

/-- Helper for Example 16.19: the explicit target triple has Lévy--Khintchin exponent
`t ↦ -|t|`. -/
lemma centeredUnitCauchy_targetExponent_eq_negAbs (t : ℝ) :
    levyKhinchinExponent
      { sigma2 := 0
        b := 0
        ν := stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) } t =
      ((-|t| : ℝ) : ℂ) := by
  -- Proof comment: the real part of the exponent is the cosine integral already computed, and
  -- the imaginary part is the odd kernel that vanishes by symmetry.
  have hkernelInt :
      Integrable
        (fun x : ℝ ↦
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I))
        (stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi)) := by
  -- Proof comment: canonicality of the inverse-square Lévy measure gives integrability of the
  -- standard Lévy--Khintchin kernel.
    let hbase :=
      integrable_levyKhinchinCanonicalKernel
        (ν := stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi))
        stableLevyMeasureOneOverPi_isCanonicalMeasure t
    refine hbase.congr ?_
    filter_upwards with x
    rfl
  have hreal :
      Complex.re
        (levyKhinchinExponent
          { sigma2 := 0
            b := 0
            ν := stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) } t) = -|t| := by
    have hkernelInt' :
        Integrable
          (fun x : ℝ ↦
            Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
              (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I))
          (stableLevyMeasure 1 Real.pi⁻¹ Real.pi⁻¹) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hkernelInt
    rw [levyKhinchinExponent, levyKhinchinExponentWithCentering]
    simp
    change
      Complex.re
        (∫ x : ℝ,
          Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
            (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I) ∂
              stableLevyMeasure 1 Real.pi⁻¹ Real.pi⁻¹) = -|t|
    -- Proof comment: move the real part through the integral using the integrability bridge.
    have hnormalize :
        Complex.re
            (∫ x : ℝ,
              Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
                (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I) ∂
                  stableLevyMeasure 1 Real.pi⁻¹ Real.pi⁻¹) =
          ∫ x : ℝ,
            Complex.re
              (Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
                (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I)) ∂
              stableLevyMeasure 1 Real.pi⁻¹ Real.pi⁻¹ := by
      simpa using (integral_re hkernelInt').symm
    rw [hnormalize]
    have hpoint :
        (fun x : ℝ ↦
          Complex.re
            (Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
              (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I))) =
          fun x : ℝ ↦ Real.cos (t * x) - 1 := by
      funext x
      have hmul : ((t : ℂ) * x) = ((t * x : ℝ) : ℂ) := by simp
      have hcenter :
          ((t : ℂ) * levyKhinchinCanonicalCentering x) =
            ((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) := by
        simp
      have hexpRe :
          (Complex.exp (((t : ℂ) * x) * Complex.I)).re = Real.cos (t * x) := by
        rw [hmul]
        simpa using Complex.exp_ofReal_mul_I_re (t * x)
      have hmain :
          Complex.re
              (Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
                (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I)) =
            (Complex.exp (((t : ℂ) * x) * Complex.I)).re - 1 := by
        rw [hcenter]
        simp [sub_eq_add_neg, add_assoc]
      calc
        Complex.re
            (Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
              (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I)) =
          (Complex.exp (((t : ℂ) * x) * Complex.I)).re - 1 := hmain
        _ = Real.cos (t * x) - 1 := by rw [hexpRe]
    rw [hpoint]
    simpa using stableLevyMeasureOneOverPi_cosinePart_eq_negAbs t
  have himag :
      Complex.im
        (levyKhinchinExponent
          { sigma2 := 0
            b := 0
            ν := stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) } t) = 0 := by
    have hkernelInt' :
        Integrable
          (fun x : ℝ ↦
            Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
              (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I))
          (stableLevyMeasure 1 Real.pi⁻¹ Real.pi⁻¹) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hkernelInt
    rw [levyKhinchinExponent, levyKhinchinExponentWithCentering]
    simp
    change
      Complex.im
        (∫ x : ℝ,
          Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
            (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I) ∂
              stableLevyMeasure 1 Real.pi⁻¹ Real.pi⁻¹) = 0
    -- Proof comment: move the imaginary part through the integral before applying oddness.
    have hnormalize :
        Complex.im
            (∫ x : ℝ,
              Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
                (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I) ∂
                  stableLevyMeasure 1 Real.pi⁻¹ Real.pi⁻¹) =
          ∫ x : ℝ,
            Complex.im
              (Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
                (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I)) ∂
              stableLevyMeasure 1 Real.pi⁻¹ Real.pi⁻¹ := by
      simpa using (integral_im hkernelInt').symm
    rw [hnormalize]
    have hpoint :
        (fun x : ℝ ↦
          Complex.im
            (Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
              (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I))) =
          fun x : ℝ ↦ Real.sin (t * x) - t * levyKhinchinCanonicalCentering x := by
      funext x
      have hmul : ((t : ℂ) * x) = ((t * x : ℝ) : ℂ) := by simp
      have hcenter :
          ((t : ℂ) * levyKhinchinCanonicalCentering x) =
            ((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) := by
        simp
      have hexpIm :
          (Complex.exp (((t : ℂ) * x) * Complex.I)).im = Real.sin (t * x) := by
        rw [hmul]
        simpa using Complex.exp_ofReal_mul_I_im (t * x)
      have hmain :
          Complex.im
              (Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
                (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I)) =
            (Complex.exp (((t : ℂ) * x) * Complex.I)).im -
              t * levyKhinchinCanonicalCentering x := by
        rw [hcenter]
        simp [sub_eq_add_neg, add_assoc]
      calc
        Complex.im
            (Complex.exp (((t : ℂ) * x) * Complex.I) - 1 -
              (((t : ℂ) * levyKhinchinCanonicalCentering x) * Complex.I)) =
          (Complex.exp (((t : ℂ) * x) * Complex.I)).im -
            t * levyKhinchinCanonicalCentering x := hmain
        _ = Real.sin (t * x) - t * levyKhinchinCanonicalCentering x := by rw [hexpIm]
    rw [hpoint]
    simpa using stableLevyMeasureOneOverPi_oddPart_eq_zero t
  exact Complex.ext hreal himag

-- Proof sketch: combine the canonical centered-Cauchy characteristic-function formula with the
-- chapter owner `HasLevyKhinchinRepresentation`. For the centered unit Cauchy law, this
-- specializes to the symmetric `α = 1` stable Lévy measure with coefficients `c⁻ = c⁺ = 1 / π`.
/-- Example 16.19: the centered unit Cauchy law `Cau_1 = cauchyMeasure 0 1` has canonical triple
`(0, 0, stableLevyMeasure 1 (1 / π) (1 / π))`, equivalently `(0, 0, (π x^2)⁻¹ dx)`. -/
theorem centeredUnitCauchy_has_canonicalTriple :
    HasLevyKhinchinRepresentation
      (⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)
      { sigma2 := 0
        b := 0
        ν := stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) } := by
  -- Route correction: replace the failed arbitrary-triple classification route with a direct
  -- verification of the explicit target triple.
  constructor
  · -- Proof comment: the target triple is canonical because the Lévy measure has no atom at `0`
    -- and finite truncated second moment.
    refine ⟨by norm_num, stableLevyMeasureOneOverPi_isCanonicalMeasure⟩
  · intro t
    -- Proof comment: match the explicit target exponent with the already-proved centered Cauchy
    -- characteristic function `exp (-|t|)`.
    calc
      charFun ((⟨cauchyMeasure 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) t
          = Complex.exp (-(|t| : ℝ)) := centeredUnitCauchy_charFun_eq_exp_neg_abs t
      _ = Complex.exp
            (levyKhinchinExponent
              { sigma2 := 0
                b := 0
                ν := stableLevyMeasure 1 (1 / Real.pi) (1 / Real.pi) } t) := by
              simpa using
                congrArg Complex.exp (centeredUnitCauchy_targetExponent_eq_negAbs t).symm
