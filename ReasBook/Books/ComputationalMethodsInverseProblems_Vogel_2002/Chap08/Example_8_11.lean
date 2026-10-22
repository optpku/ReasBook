/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Real.Sign
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9

public section

noncomputable section

open scoped ENNReal Topology
open Set Filter

namespace VariationalRegularization

/-- Example 8.11 (1). For a one-dimensional jump on `[0, 1]`, splitting the pairing
against `deriv v` at `1 / 2` gives `(f0 - f1) * v (1 / 2)`. -/
theorem midpointJumpPairing_eq_jump_mul_midpoint
    (f0 f1 : ℝ) (v : ℝ → ℝ)
    (hderiv_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), DifferentiableAt ℝ v x)
    (hderiv_right : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1, DifferentiableAt ℝ v x)
    (hint_left : IntervalIntegrable (deriv v) MeasureTheory.volume 0 (1 / 2))
    (hint_right : IntervalIntegrable (deriv v) MeasureTheory.volume (1 / 2) 1)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    (∫ x in 0..(1 / 2 : ℝ), f0 * deriv v x) +
        ∫ x in (1 / 2 : ℝ)..1, f1 * deriv v x =
      (f0 - f1) * v (1 / 2) := by
  have hzero_half : (0 : ℝ) ≤ 1 / 2 := by
    norm_num
  have hhalf_one : (1 / 2 : ℝ) ≤ 1 := by
    norm_num
  -- Rewrite the left half-interval by converting the endpoint differentiability hypothesis
  -- into the `uIcc` form used by the fundamental theorem of calculus.
  have hleft :
      ∫ x in 0..(1 / 2 : ℝ), deriv v x = v (1 / 2) - v 0 := by
    refine intervalIntegral.integral_deriv_eq_sub ?_ hint_left
    intro x hx
    rw [Set.uIcc_of_le hzero_half] at hx
    exact hderiv_left x hx
  -- Apply the same FTC rewrite on the right half-interval.
  have hright :
      ∫ x in (1 / 2 : ℝ)..1, deriv v x = v 1 - v (1 / 2) := by
    refine intervalIntegral.integral_deriv_eq_sub ?_ hint_right
    intro x hx
    rw [Set.uIcc_of_le hhalf_one] at hx
    exact hderiv_right x hx
  -- Pull the constants out of the two interval integrals and replace each derivative integral
  -- with its endpoint expression.
  calc
    (∫ x in 0..(1 / 2 : ℝ), f0 * deriv v x) +
        ∫ x in (1 / 2 : ℝ)..1, f1 * deriv v x =
          f0 * (∫ x in 0..(1 / 2 : ℝ), deriv v x) +
            f1 * (∫ x in (1 / 2 : ℝ)..1, deriv v x) := by
              rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = f0 * (v (1 / 2) - v 0) + f1 * (v 1 - v (1 / 2)) := by
      rw [hleft, hright]
    -- The boundary conditions `v 0 = 0` and `v 1 = 0` leave only the jump size times the
    -- midpoint value.
    _ = (f0 - f1) * v (1 / 2) := by
      rw [hv0, hv1]
      ring

/-- Scalar form of Example 8.11 (2). -/
theorem jump_mul_le_abs_sub_of_abs_le_one
    (f0 f1 m : ℝ) (hm : |m| ≤ 1) :
    (f0 - f1) * m ≤ |f1 - f0| := by
  calc
    (f0 - f1) * m ≤ |(f0 - f1) * m| := le_abs_self _
    _ = |f0 - f1| * |m| := by rw [abs_mul]
    _ ≤ |f0 - f1| * 1 := by
      exact mul_le_mul_of_nonneg_left hm (abs_nonneg _)
    _ = |f0 - f1| := by simp
    _ = |f1 - f0| := by rw [abs_sub_comm]

/-- Example 8.11 (2). If `|v (1 / 2)| ≤ 1`, then the midpoint jump pairing is bounded
by `|f1 - f0|`. -/
theorem jump_mul_midpoint_le_abs_sub
    (f0 f1 : ℝ) (v : ℝ → ℝ) (hv_mid : |v (1 / 2 : ℝ)| ≤ 1) :
    (f0 - f1) * v (1 / 2 : ℝ) ≤ |f1 - f0| := by
  simpa using jump_mul_le_abs_sub_of_abs_le_one f0 f1 (v (1 / 2 : ℝ)) hv_mid

/-- Scalar form of Example 8.11 (3). -/
theorem jump_mul_eq_abs_sub_of_sign
    (f0 f1 : ℝ) :
    (f0 - f1) * Real.sign (f0 - f1) = |f1 - f0| := by
  have hsign : (f0 - f1) * Real.sign (f0 - f1) = |f0 - f1| := by
    rcases lt_trichotomy (f0 - f1) 0 with hneg | hzero | hpos
    · rw [Real.sign_of_neg hneg, abs_of_neg hneg, mul_neg_one]
    · rw [hzero, Real.sign_zero]
      simp
    · rw [Real.sign_of_pos hpos, abs_of_pos hpos, mul_one]
  rw [hsign, abs_sub_comm]

/-- Example 8.11 (3). The midpoint jump pairing attains `|f1 - f0|` when
`v (1 / 2) = Real.sign (f0 - f1)`. -/
theorem jump_mul_midpoint_eq_abs_sub_of_sign
    (f0 f1 : ℝ) (v : ℝ → ℝ)
    (hv_mid : v (1 / 2 : ℝ) = Real.sign (f0 - f1)) :
    (f0 - f1) * v (1 / 2 : ℝ) = |f1 - f0| := by
  rw [hv_mid]
  exact jump_mul_eq_abs_sub_of_sign f0 f1

/-- Example 8.11 (4). If the Chapter 8 admissible-divergence pairing of a midpoint jump datum is
given by `(f0 - f1) * midpointValue v`, every admissible `midpointValue v` has absolute value at
most `1`, and one admissible test field realizes the sign of `f0 - f1`, then
`VariationalRegularization.totalVariation` of that datum is the jump size `|f1 - f0|`. -/
theorem midpointJump_totalVariation_eq_abs_sub_of_pairingFormula
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (f0 f1 : ℝ)
    (midpointValue : AdmissibleTestField Ω → ℝ)
    (hpairing :
      ∀ v : AdmissibleTestField Ω,
        admissibleDivergencePairing f v = (f0 - f1) * midpointValue v)
    (hmidpoint_le_one : ∀ v : AdmissibleTestField Ω, |midpointValue v| ≤ 1)
    (v : AdmissibleTestField Ω)
    (hmidpoint_sign : midpointValue v = Real.sign (f0 - f1)) :
    totalVariation f = |f1 - f0| := by
  refine totalVariation_eq_of_pairing_upper_bound_and_attained f ?_ v ?_
  · intro w
    rw [hpairing w]
    exact_mod_cast jump_mul_le_abs_sub_of_abs_le_one f0 f1 (midpointValue w) (hmidpoint_le_one w)
  · rw [hpairing v, hmidpoint_sign]
    exact_mod_cast jump_mul_eq_abs_sub_of_sign f0 f1

/-- Canonical `eVariationOn` companion for the midpoint jump from Example 8.11. -/
theorem midpointJump_eVariationOn_eq_abs_sub (f0 f1 : ℝ) :
    eVariationOn (fun x : ℝ ↦ if x ≤ (1 / 2 : ℝ) then f0 else f1) (Set.Icc 0 1) =
      ENNReal.ofReal |f1 - f0| := by
  let f : ℝ → ℝ := fun x ↦ if x ≤ (1 / 2 : ℝ) then f0 else f1
  have hsplit :
      eVariationOn f (Set.Icc (0 : ℝ) (1 / 2)) + eVariationOn f (Set.Icc (1 / 2 : ℝ) 1) =
        eVariationOn f (Set.Icc (0 : ℝ) 1) := by
    simpa [Set.univ_inter] using
      (show eVariationOn f (Set.univ ∩ Set.Icc (0 : ℝ) (1 / 2)) +
          eVariationOn f (Set.univ ∩ Set.Icc (1 / 2 : ℝ) 1) =
            eVariationOn f (Set.univ ∩ Set.Icc (0 : ℝ) 1) from
        eVariationOn.Icc_add_Icc f (by norm_num) (by norm_num) (by simp))
  have hleft :
      eVariationOn f (Set.Icc (0 : ℝ) (1 / 2)) = 0 := by
    calc
      eVariationOn f (Set.Icc (0 : ℝ) (1 / 2))
          = eVariationOn (fun _ : ℝ ↦ f0) (Set.Icc (0 : ℝ) (1 / 2)) := by
              apply eVariationOn.congr
              intro x hx
              dsimp [f]
              rw [if_pos hx.2]
      _ = 0 := by
        refine eVariationOn.constant_on ?_
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rfl
  have hright_zero :
      eVariationOn f (Set.Ioc (1 / 2 : ℝ) 1) = 0 := by
    calc
      eVariationOn f (Set.Ioc (1 / 2 : ℝ) 1)
          = eVariationOn (fun _ : ℝ ↦ f1) (Set.Ioc (1 / 2 : ℝ) 1) := by
              apply eVariationOn.congr
              intro x hx
              dsimp [f]
              rw [if_neg (not_le.mpr hx.1)]
      _ = 0 := by
        refine eVariationOn.constant_on ?_
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rfl
  have hIccIci :
      Set.Icc (1 / 2 : ℝ) 1 ∩ Set.Ici (1 / 2 : ℝ) = Set.Icc (1 / 2 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, hx.1⟩
  have hIccIoi :
      Set.Icc (1 / 2 : ℝ) 1 ∩ Set.Ioi (1 / 2 : ℝ) = Set.Ioc (1 / 2 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2, hx.1.2⟩
    · intro hx
      exact ⟨⟨le_of_lt hx.1, hx.2⟩, hx.1⟩
  have hIoc_neBot :
      (𝓝[Set.Icc (1 / 2 : ℝ) 1 ∩ Set.Ioi (1 / 2 : ℝ)] (1 / 2 : ℝ)).NeBot := by
    rw [show Set.Icc (1 / 2 : ℝ) 1 ∩ Set.Ioi (1 / 2 : ℝ) =
        Set.Ioi (1 / 2 : ℝ) ∩ Set.Iic (1 : ℝ) by
          ext x
          constructor
          · intro hx
            exact ⟨hx.2, hx.1.2⟩
          · intro hx
            exact ⟨⟨le_of_lt hx.1, hx.2⟩, hx.1⟩]
    rw [nhdsWithin_inter_of_mem']
    · exact nhdsGT_neBot_of_exists_gt ⟨(1 : ℝ), by norm_num⟩
    · exact mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hright_tendsto :
      Tendsto f (𝓝[Set.Icc (1 / 2 : ℝ) 1 ∩ Set.Ioi (1 / 2 : ℝ)] (1 / 2 : ℝ)) (𝓝 f1) := by
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    dsimp [f]
    rw [if_neg (not_le.mpr hx.2)]
  have hright :
      eVariationOn f (Set.Icc (1 / 2 : ℝ) 1) = ENNReal.ofReal |f1 - f0| := by
    have hformula :
        eVariationOn f (Set.Icc (1 / 2 : ℝ) 1 ∩ Set.Ici (1 / 2 : ℝ)) =
          eVariationOn f (Set.Icc (1 / 2 : ℝ) 1 ∩ Set.Ioi (1 / 2 : ℝ)) +
            edist (f (1 / 2 : ℝ)) f1 :=
      eVariationOn.eVariationOn_on_inter_Ici_eq_Ioi_add_edist
        hIoc_neBot (by norm_num) hright_tendsto
    rw [hIccIci, hIccIoi] at hformula
    calc
      eVariationOn f (Set.Icc (1 / 2 : ℝ) 1)
          = eVariationOn f (Set.Ioc (1 / 2 : ℝ) 1) + edist (f (1 / 2 : ℝ)) f1 := hformula
      _ = 0 + edist (f (1 / 2 : ℝ)) f1 := by rw [hright_zero]
      _ = 0 + edist f0 f1 := by simp [f]
      _ = ENNReal.ofReal |f1 - f0| := by
        rw [zero_add, edist_dist, Real.dist_eq, abs_sub_comm]
  calc
    eVariationOn (fun x : ℝ ↦ if x ≤ (1 / 2 : ℝ) then f0 else f1) (Set.Icc 0 1)
        = eVariationOn f (Set.Icc (0 : ℝ) 1) := by rfl
    _ = eVariationOn f (Set.Icc (0 : ℝ) (1 / 2)) + eVariationOn f (Set.Icc (1 / 2 : ℝ) 1) :=
      hsplit.symm
    _ = 0 + ENNReal.ofReal |f1 - f0| := by rw [hleft, hright]
    _ = ENNReal.ofReal |f1 - f0| := by simp

/-- Real-valued `variationOnFromTo` companion for the midpoint jump from Example 8.11. -/
theorem midpointJump_variationOnFromTo_eq_abs_sub (f0 f1 : ℝ) :
    variationOnFromTo (fun x : ℝ ↦ if x ≤ (1 / 2 : ℝ) then f0 else f1) Set.univ 0 1 =
      |f1 - f0| := by
  rw [variationOnFromTo.eq_of_le
    (fun x : ℝ ↦ if x ≤ (1 / 2 : ℝ) then f0 else f1) Set.univ (by norm_num),
    Set.univ_inter, midpointJump_eVariationOn_eq_abs_sub]
  simp

end VariationalRegularization
