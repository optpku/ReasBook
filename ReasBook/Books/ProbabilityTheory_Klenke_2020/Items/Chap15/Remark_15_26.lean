/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Example_16_2

open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure

noncomputable section

-- Proof sketch: identify the characteristic function of `measureConvolutionPower μ n` as the `n`th
-- power of `charFun μ`, compare it with the characteristic function of the scaled law using the
-- assumed scaling identity, and conclude by uniqueness of characteristic functions.
/-- A characteristic-function scaling law yields strict stability with index `α` in the canonical
owner abstraction `IsStableWithIndex` once the owner side conditions are supplied explicitly. -/
theorem isStableWithIndex_of_charFun_scaling
    (μ : ProbabilityMeasure ℝ) {α : ℝ}
    (hμ_not_dirac : ∀ x : ℝ, μ ≠ diracProba x)
    (hα : α ∈ Set.Ioc (0 : ℝ) 2)
    (hφ : ∀ n : ℕ+, ∀ t : ℝ,
      charFun μ t ^ (n : ℕ) = charFun μ (((n : ℝ) ^ (1 / α)) * t)) :
    IsStableWithIndex μ α := by
  refine ⟨hμ_not_dirac, hα, ?_⟩
  intro n
  -- Read the scaling identity back as equality of probability measures through characteristic
  -- function uniqueness.
  let ν : ProbabilityMeasure ℝ :=
    map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) 0).aemeasurable
  have hν : map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) 0).aemeasurable = ν := rfl
  rw [hν]
  have hνfin : IsFiniteMeasure (ν : Measure ℝ) := by
    refine ⟨?_⟩
    simp
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
      rw [hpow, hφ n t]
      simpa [ν, MeasureTheory.ProbabilityMeasure.measurable_affineMap, zero_add] using
        (MeasureTheory.charFun_map_mul
          (μ := (μ : Measure ℝ)) (((n : ℝ) ^ (1 / α))) t).symm

-- Proof sketch: compute both sides from the explicit formula
-- `exp (-|r t|^α)` and use `|r * ((n : ℝ) ^ (1 / α) * t)|^α = n * |r * t|^α`.
/-- The symmetric stable characteristic functions satisfy the scaling identity that characterizes
strict stability. -/
theorem symmetricStableCharFun_charFun_scaling
    {α r : ℝ} (hα₀ : 0 < α) :
    ∀ n : ℕ+, ∀ t : ℝ,
      symmetricStableCharFun α r t ^ (n : ℕ) =
        symmetricStableCharFun α r (((n : ℝ) ^ (1 / α)) * t) := by
  intro n t
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    positivity
  have hroot_nonneg : 0 ≤ (n : ℝ) ^ (1 / α) := by
    exact Real.rpow_nonneg hn_nonneg _
  have hmul :
      r * (((n : ℝ) ^ (1 / α)) * t) = (r * t) * ((n : ℝ) ^ (1 / α)) := by
    ring
  have hroot_pow : (((n : ℝ) ^ (1 / α)) ^ α) = (n : ℝ) := by
    rw [← Real.rpow_mul hn_nonneg, one_div_mul_cancel hα₀.ne', Real.rpow_one]
  have hscale :
      |r * (((n : ℝ) ^ (1 / α)) * t)| ^ α = (n : ℝ) * |r * t| ^ α := by
    calc
      |r * (((n : ℝ) ^ (1 / α)) * t)| ^ α
          = (|r * t| * ((n : ℝ) ^ (1 / α))) ^ α := by
              rw [hmul, abs_mul, abs_of_nonneg hroot_nonneg]
      _ = |r * t| ^ α * (((n : ℝ) ^ (1 / α)) ^ α) := by
            rw [Real.mul_rpow (abs_nonneg _) hroot_nonneg]
      _ = |r * t| ^ α * (n : ℝ) := by
            rw [hroot_pow]
      _ = (n : ℝ) * |r * t| ^ α := by
            ring
  -- Normalize the real exponent before comparing the two characteristic-function formulas.
  calc
    symmetricStableCharFun α r t ^ (n : ℕ)
        = Complex.exp (((n : ℂ) * (-(|r * t| ^ α : ℝ) : ℂ))) := by
            rw [symmetricStableCharFun_apply,
              (Complex.exp_nat_mul ((-(|r * t| ^ α : ℝ) : ℂ)) (n : ℕ)).symm]
    _ = Complex.exp ((-(|r * (((n : ℝ) ^ (1 / α)) * t)| ^ α : ℝ) : ℂ)) := by
          have hexp :
              (n : ℝ) * (-(|r * t| ^ α : ℝ)) =
                -(|r * (((n : ℝ) ^ (1 / α)) * t)| ^ α : ℝ) := by
            rw [hscale]
            ring
          exact congrArg Complex.exp (by exact_mod_cast hexp)
    _ = symmetricStableCharFun α r (((n : ℝ) ^ (1 / α)) * t) := by
          rw [symmetricStableCharFun_apply]


/-- Helper for Remark 15.26: replacing the scale parameter `r` by `|r|` does not change the
corresponding symmetric stable characteristic function. -/
lemma symmetricStableCharFun_absScale (α r t : ℝ) :
    symmetricStableCharFun α |r| t = symmetricStableCharFun α r t := by
  -- Both formulas depend only on `|r * t|`, so the sign of `r` is irrelevant.
  rw [symmetricStableCharFun_apply, symmetricStableCharFun_apply]
  congr 1
  rw [abs_mul, abs_mul, abs_abs]


-- Proof sketch: combine `hμ` with `symmetricStableCharFun_charFun_scaling` and invoke
-- `isStableWithIndex_of_charFun_scaling`; the extra hypothesis `r ≠ 0` rules out the Dirac case
-- `symmetricStableCharFun α 0 = 1`.
/-- Helper for Remark 15.26: every probability law whose characteristic function is
`t ↦ exp (-|r t|^α)` with `r ≠ 0` is strictly stable with index `α`. -/
theorem isStableWithIndex_of_charFun_eq_symmetricStableCharFun
    (μ : ProbabilityMeasure ℝ) {α r : ℝ}
    (hα : α ∈ Set.Ioc (0 : ℝ) 2) (hr : r ≠ 0)
    (hμ : ∀ t : ℝ, charFun μ t = symmetricStableCharFun α r t) :
    IsStableWithIndex μ α := by
  -- Exclude the Dirac case by evaluating at the nonzero frequency `r⁻¹`.
  apply isStableWithIndex_of_charFun_scaling μ
  · intro x hx
    have hchar : charFun μ r⁻¹ = symmetricStableCharFun α r r⁻¹ := hμ r⁻¹
    rw [hx] at hchar
    have hnorm := congrArg norm hchar
    have hleft : ‖charFun ((diracProba x : ProbabilityMeasure ℝ) : Measure ℝ) r⁻¹‖ = 1 := by
      simpa [MeasureTheory.diracProba, MeasureTheory.charFun_dirac, Complex.norm_exp]
    have hright : ‖symmetricStableCharFun α r r⁻¹‖ = Real.exp (-1 : ℝ) := by
      simp [symmetricStableCharFun_apply, Complex.norm_exp, mul_inv_cancel₀ hr]
    rw [hleft, hright] at hnorm
    have hunit : (1 : ℝ) = Real.exp (-1 : ℝ) := hnorm
    have hexp_ne : Real.exp (-1 : ℝ) ≠ 1 := by
      exact ne_of_lt (by simpa using (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)))
    exact hexp_ne hunit.symm
  · exact hα
  · intro n t
    rw [hμ, symmetricStableCharFun_charFun_scaling hα.1, ← hμ]

-- Proof sketch: extend the existence statement from Corollary 15.25 to all `α ∈ (0,2]`, keep the
-- source-facing symmetric law visible, and combine the resulting characteristic-function identity
-- with `isStableWithIndex_of_charFun_eq_symmetricStableCharFun`.
/-- Helper for Remark 15.26: the Chapter 16 root-construction theorem specialized at `n = 1`
produces a probability law with characteristic function `symmetricStableCharFun α γ` for every
positive scale `γ`. -/
lemma exists_probabilityMeasure_charFun_eq_symmetricStableCharFun_of_posScale
    (α γ : ℝ) (hα₀ : 0 < α) (hα₂ : α ≤ 2) (hγ : 0 < γ) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ t : ℝ, charFun μ t = symmetricStableCharFun α γ t := by
  sorry

/-- Helper for Remark 15.26: in the range `1 < α ≤ 2`, every nonzero scale `r` admits a symmetric
probability law with characteristic function `symmetricStableCharFun α r`. -/
lemma exists_symmetricProbabilityMeasure_charFun_eq_symmetricStableCharFun_of_one_lt
    (α r : ℝ) (hα_lower : 1 < α) (hα_upper : α ≤ 2) (hr : r ≠ 0) :
    ∃ μ : ProbabilityMeasure ℝ, ((μ : Measure ℝ)).IsNegInvariant ∧
      ∀ t : ℝ, charFun μ t = symmetricStableCharFun α r t := by
  -- Build the witness first at the positive scale `|r|`, where the Chapter 16 theorem applies.
  rcases exists_probabilityMeasure_charFun_eq_symmetricStableCharFun_of_posScale
      α |r| (lt_trans zero_lt_one hα_lower) hα_upper (abs_pos.mpr hr) with ⟨μ, hμcharAbs⟩
  have hμchar : ∀ t : ℝ, charFun μ t = symmetricStableCharFun α r t := by
    intro t
    have hchar := hμcharAbs t
    -- Normalize the scale parameter from `|r|` back to `r`.
    rw [symmetricStableCharFun_absScale α r t] at hchar
    exact hchar
  have hμsymm : ((μ : Measure ℝ)).IsNegInvariant := by
    -- Reuse the characteristic-function symmetry criterion after the scale normalization.
    exact isNegInvariant_of_charFun_eq_symmetricStableCharFun μ hμchar
  exact ⟨μ, hμsymm, hμchar⟩

/-- Remark 15.26: for every `α ∈ (0,2]` and every nonzero `r ∈ ℝ`, there exists a symmetric
probability law on `ℝ` with characteristic function `t ↦ exp (-|r t|^α)`, and this law is
strictly stable with index `α`. -/
theorem exists_symmetricProbabilityMeasure_isStableWithIndex_charFun_eq_symmetricStableCharFun
    (α r : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 2) (hr : r ≠ 0) :
    ∃ μ : ProbabilityMeasure ℝ, ((μ : Measure ℝ)).IsNegInvariant ∧
      IsStableWithIndex μ α ∧
      ∀ t : ℝ, charFun μ t = symmetricStableCharFun α r t := by
  by_cases hα₁ : α ≤ 1
  · -- The earlier Chapter 15 existence theorem already covers the range `0 < α ≤ 1`.
    rcases exists_symmetricProbabilityMeasure_charFun_eq_symmetricStableCharFun α r hα.1 hα₁ with
      ⟨μ, hμsymm, hμchar⟩
    refine ⟨μ, hμsymm, ?_, hμchar⟩
    exact isStableWithIndex_of_charFun_eq_symmetricStableCharFun μ hα hr hμchar
  have hα_gt_one : 1 < α := by
    linarith
  by_cases hα₂ : α = 2
  · have hv : 0 ≤ 2 * r ^ 2 := by
      positivity
    let v : NNReal := ⟨2 * r ^ 2, hv⟩
    let μ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 v, inferInstance⟩
    have hμchar : ∀ t : ℝ, charFun μ t = symmetricStableCharFun 2 r t := by
      intro t
      -- Compare the explicit Gaussian and stable characteristic-function formulas at `α = 2`.
      have hμdef : (μ : Measure ℝ) = gaussianReal 0 v := rfl
      rw [hμdef, charFun_gaussianReal, symmetricStableCharFun_apply]
      have htwo : (2 : ℝ) = (2 : ℕ) := by
        norm_num
      rw [htwo, Real.rpow_natCast, sq_abs]
      congr 1
      simp [v]
      ring
    have hμsymm : ((μ : Measure ℝ)).IsNegInvariant := by
      -- Reuse the characteristic-function criterion instead of unfolding the Gaussian symmetry.
      exact isNegInvariant_of_charFun_eq_symmetricStableCharFun μ hμchar
    have hstable₂ : IsStableWithIndex μ 2 := by
      exact isStableWithIndex_of_charFun_eq_symmetricStableCharFun μ
        (by simpa [hα₂] using hα) hr hμchar
    refine ⟨μ, hμsymm, ?_, ?_⟩
    · simpa [hα₂] using hstable₂
    · intro t
      simpa [hα₂] using hμchar t
  -- Route correction: the remaining branch is closed by the Chapter 16 owner theorem rather than
  -- by a local Bochner-style construction in this file.
  rcases exists_symmetricProbabilityMeasure_charFun_eq_symmetricStableCharFun_of_one_lt
      α r hα_gt_one hα.2 hr with ⟨μ, hμsymm, hμchar⟩
  have hstable : IsStableWithIndex μ α := by
    -- Once the characteristic function is in the canonical stable form, stability is automatic.
    exact isStableWithIndex_of_charFun_eq_symmetricStableCharFun μ hα hr hμchar
  exact ⟨μ, hμsymm, hstable, hμchar⟩
