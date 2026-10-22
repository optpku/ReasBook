/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Exercise_13_2_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_39
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_45
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_49
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_43

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

universe u v

noncomputable section

open RealRandomVariableArray

/-- The symmetric Pareto density in textbook form. For `α = 1 / 2`, this becomes the inverse-cube
tail density `x ↦ |x|⁻³ 1_{|x| ≥ 1}`. -/
def symmetricParetoDensityReal (α x : ℝ) : ℝ :=
  if 1 ≤ |x| then (1 / (2 * α)) * |x| ^ (-1 - 1 / α) else 0

/-- The local symmetric Pareto density is already written in the textbook normal form. -/
theorem symmetricParetoDensityReal_eq (α x : ℝ) :
    symmetricParetoDensityReal α x =
      if 1 ≤ |x| then (1 / (2 * α)) * |x| ^ (-1 - 1 / α) else 0 :=
  rfl

/-- The symmetric Pareto law obtained from the density `symmetricParetoDensityReal α`. -/
def symmetricParetoMeasure (α : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (symmetricParetoDensityReal α x))

/-- A convenient explicit normalization for the inverse-cube-tail central limit theorem. -/
def inverseCubeTailCLTNormingSequence : ℕ → ℝ :=
  fun n ↦ Real.sqrt ((n + 2 : ℝ) * Real.log (n + 2 : ℝ))

/-- Helper for Exercise 15.5.3: the natural variance scale of the array truncated at
`inverseCubeTailCLTNormingSequence n`. -/
private def inverseCubeTailTruncationVarianceScale : ℕ → ℝ :=
  fun n ↦ Real.sqrt ((n : ℝ) * Real.log (((n + 2 : ℝ) * Real.log (n + 2 : ℝ))))

/-- Helper for Exercise 15.5.3: the rowwise truncation variance scale `B_{n+1}` is strictly
positive. -/
private lemma inverseCubeTailTruncationVarianceScale_pos (n : ℕ) :
    0 < inverseCubeTailTruncationVarianceScale (n + 1) := by
  -- Proof comment: rewrite `B_{n+1}` to its explicit `n + 3` logarithmic normalizer and use the
  -- positivity of that normalizer under the square root.
  rw [inverseCubeTailTruncationVarianceScale]
  have hshift : (((n + 1 : ℕ) : ℝ) + 2) = n + 3 := by
    norm_num [Nat.cast_add, add_assoc]
  rw [hshift]
  refine Real.sqrt_pos.2 ?_
  have hthree_pos : (0 : ℝ) < n + 3 := by positivity
  have hlog_lower :
      1 - (n + 3 : ℝ)⁻¹ ≤ Real.log (n + 3 : ℝ) :=
    Real.one_sub_inv_le_log_of_pos hthree_pos
  have hmul_lower :
      (n + 3 : ℝ) * (1 - (n + 3 : ℝ)⁻¹) ≤
        (n + 3 : ℝ) * Real.log (n + 3 : ℝ) := by
    exact mul_le_mul_of_nonneg_left hlog_lower (by positivity)
  have hbase :
      (1 : ℝ) < (n + 3 : ℝ) * (1 - (n + 3 : ℝ)⁻¹) := by
    have hneq : (n + 3 : ℝ) ≠ 0 := by linarith
    have hcalc : (n + 3 : ℝ) * (1 - (n + 3 : ℝ)⁻¹) = n + 2 := by
      field_simp [hneq]
      ring
    calc
      (1 : ℝ) < (n + 2 : ℝ) := by linarith
      _ = (n + 3 : ℝ) * (1 - (n + 3 : ℝ)⁻¹) := by
            symm
            exact hcalc
  have hlog_pos :
      0 < Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) :=
    Real.log_pos (lt_of_lt_of_le hbase hmul_lower)
  positivity

/-- Helper for Exercise 15.5.3: the logarithmic normalizer
`log (((n + 3) * log (n + 3)))` is positive. -/
private lemma inverseCubeTailLogNormalizer_pos (n : ℕ) :
    0 < Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) := by
  -- Proof comment: the same lower bound used for `B_{n+1} > 0` already shows that the
  -- logarithm is taken at an argument strictly larger than `1`.
  have hthree_pos : (0 : ℝ) < n + 3 := by positivity
  have hlog_lower :
      1 - (n + 3 : ℝ)⁻¹ ≤ Real.log (n + 3 : ℝ) :=
    Real.one_sub_inv_le_log_of_pos hthree_pos
  have hmul_lower :
      (n + 3 : ℝ) * (1 - (n + 3 : ℝ)⁻¹) ≤
        (n + 3 : ℝ) * Real.log (n + 3 : ℝ) := by
    exact mul_le_mul_of_nonneg_left hlog_lower (by positivity)
  have hbase :
      (1 : ℝ) < (n + 3 : ℝ) * (1 - (n + 3 : ℝ)⁻¹) := by
    have hneq : (n + 3 : ℝ) ≠ 0 := by linarith
    have hcalc : (n + 3 : ℝ) * (1 - (n + 3 : ℝ)⁻¹) = n + 2 := by
      field_simp [hneq]
      ring
    calc
      (1 : ℝ) < (n + 2 : ℝ) := by linarith
      _ = (n + 3 : ℝ) * (1 - (n + 3 : ℝ)⁻¹) := by
            symm
            exact hcalc
  exact Real.log_pos (lt_of_lt_of_le hbase hmul_lower)

/-- Helper for Exercise 15.5.3: the explicit norming sequence is always positive. -/
private lemma inverseCubeTailCLTNormingSequence_pos (n : ℕ) :
    0 < inverseCubeTailCLTNormingSequence n := by
  -- Proof comment: the radicand is positive because `n + 2 > 1`, hence `log (n + 2) > 0`.
  rw [inverseCubeTailCLTNormingSequence]
  refine Real.sqrt_pos.2 ?_
  have hn_nonneg : (0 : ℝ) ≤ n := by positivity
  have htwo_lt : (1 : ℝ) < n + 2 := by linarith
  have hlog_pos : 0 < Real.log (n + 2 : ℝ) := Real.log_pos htwo_lt
  positivity

/-- Helper for Exercise 15.5.3: the explicit cutoff always lies in the tail regime `R ≥ 1`
required by the inverse-cube-tail formulas. -/
private lemma inverseCubeTailCLTNormingSequence_one_le (n : ℕ) :
    1 ≤ inverseCubeTailCLTNormingSequence n := by
  -- Proof comment: `x log x` dominates `x - 1`, so at `x = n + 2` the radicand is at least
  -- `n + 1 ≥ 1`.
  rw [inverseCubeTailCLTNormingSequence]
  refine (Real.one_le_sqrt).2 ?_
  have hpos : 0 < (n + 2 : ℝ) := by positivity
  have hlog_lower :
      1 - (n + 2 : ℝ)⁻¹ ≤ Real.log (n + 2 : ℝ) :=
    Real.one_sub_inv_le_log_of_pos hpos
  have hmul_lower :
      (n + 2 : ℝ) * (1 - (n + 2 : ℝ)⁻¹) ≤
        (n + 2 : ℝ) * Real.log (n + 2 : ℝ) := by
    exact mul_le_mul_of_nonneg_left hlog_lower (by positivity)
  have hbase :
      (1 : ℝ) ≤ (n + 2 : ℝ) * (1 - (n + 2 : ℝ)⁻¹) := by
    have hstep : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hneq : (n + 2 : ℝ) ≠ 0 := by linarith [hpos]
    have hcalc : (n + 2 : ℝ) * (1 - (n + 2 : ℝ)⁻¹) = n + 1 := by
      field_simp [hneq]
      ring
    calc
      (1 : ℝ) ≤ (n + 1 : ℝ) := hstep
      _ = (n + 2 : ℝ) * (1 - (n + 2 : ℝ)⁻¹) := by
            symm
            exact hcalc
  exact hbase.trans hmul_lower

/-- Helper for Exercise 15.5.3: the union-bound rate for the rare jumps is `n / A_n^2`, which
tends to `0` for the explicit normalization `A_n = √((n + 2) log (n + 2))`. -/
lemma inverseCubeTail_largeJumpRate_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * ((inverseCubeTailCLTNormingSequence n)⁻¹ ^ (2 : ℕ)))
      atTop (𝓝 0) := by
  -- Proof comment: first rewrite the rate to the stable product
  -- `((n : ℝ) / (n + 2 : ℝ)) * (log (n + 2))⁻¹`.
  have hrewrite :
      (fun n : ℕ ↦ (n : ℝ) * ((inverseCubeTailCLTNormingSequence n)⁻¹ ^ (2 : ℕ))) =
        fun n : ℕ ↦ ((n : ℝ) / (n + 2 : ℝ)) * (Real.log (n + 2 : ℝ))⁻¹ := by
    funext n
    have hradicand_nonneg : 0 ≤ ((n + 2 : ℝ) * Real.log (n + 2 : ℝ)) := by
      have hn_nonneg : (0 : ℝ) ≤ n := by positivity
      have htwo_lt : (1 : ℝ) < n + 2 := by linarith
      have hlog_nonneg : 0 ≤ Real.log (n + 2 : ℝ) := le_of_lt (Real.log_pos htwo_lt)
      positivity
    calc
      (n : ℝ) * ((inverseCubeTailCLTNormingSequence n)⁻¹ ^ (2 : ℕ))
          = (n : ℝ) * (((n + 2 : ℝ) * Real.log (n + 2 : ℝ))⁻¹) := by
              rw [inverseCubeTailCLTNormingSequence, inv_pow]
              simp [Real.sq_sqrt hradicand_nonneg]
      _ = ((n : ℝ) / (n + 2 : ℝ)) * (Real.log (n + 2 : ℝ))⁻¹ := by
            rw [mul_inv_rev]
            simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hratio :
      Tendsto (fun n : ℕ ↦ ((n : ℝ) / (n + 2 : ℝ))) atTop (𝓝 1) := by
    simpa [Nat.cast_add, add_assoc] using tendsto_natCast_div_add_atTop (2 : ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ ↦ Real.log (n + 2 : ℝ)) atTop atTop := by
    have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop := by
      simpa using tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    simpa [Nat.cast_add, add_assoc] using
      Real.tendsto_log_atTop.comp hshift
  have hinv_log :
      Tendsto (fun n : ℕ ↦ (Real.log (n + 2 : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hlog_atTop
  -- Proof comment: the shifted prefactor tends to `1`, while the inverse logarithm tends to `0`.
  rw [hrewrite]
  simpa [one_mul] using hratio.mul hinv_log

/-- Helper for Exercise 15.5.3: the logarithmic correction
`log ((n + 2) log (n + 2)) / log (n + 2)` tends to `1`. -/
private lemma inverseCubeTail_logRatio_tendsto_one :
    Tendsto
      (fun n : ℕ ↦
        Real.log (((n + 2 : ℝ) * Real.log (n + 2 : ℝ))) / Real.log (n + 2 : ℝ))
      atTop (𝓝 1) := by
  have hlog_atTop :
      Tendsto (fun n : ℕ ↦ Real.log (n + 2 : ℝ)) atTop atTop := by
    have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop := by
      simpa using tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    simpa [Nat.cast_add, add_assoc] using
      Real.tendsto_log_atTop.comp hshift
  have hsmall :
      Tendsto
        (fun n : ℕ ↦ Real.log (Real.log (n + 2 : ℝ)) / Real.log (n + 2 : ℝ))
        atTop (𝓝 0) := by
    -- Proof comment: the extra logarithm is negligible compared with the base logarithmic scale.
    simpa [pow_one, one_mul, zero_add] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hlog_atTop
  have hrewrite :
      (fun n : ℕ ↦
        Real.log (((n + 2 : ℝ) * Real.log (n + 2 : ℝ))) / Real.log (n + 2 : ℝ)) =
        fun n : ℕ ↦
          1 + Real.log (Real.log (n + 2 : ℝ)) / Real.log (n + 2 : ℝ) := by
    funext n
    have htwo_ne : (n + 2 : ℝ) ≠ 0 := by positivity
    have hlog_pos : 0 < Real.log (n + 2 : ℝ) := by
      have hn_nonneg : (0 : ℝ) ≤ n := by positivity
      refine Real.log_pos ?_
      linarith
    have hlog_ne : Real.log (n + 2 : ℝ) ≠ 0 := hlog_pos.ne'
    rw [Real.log_mul htwo_ne hlog_ne]
    field_simp [hlog_ne]
  -- Proof comment: after the algebraic split, only the negligible `log(log)/log` term remains.
  rw [hrewrite]
  simpa using tendsto_const_nhds.add hsmall

/-- Helper for Exercise 15.5.3: the natural variance scale of the truncated array is asymptotic
to the explicit norming sequence. -/
lemma inverseCubeTail_truncationScaleRatio_tendsto_one :
    Tendsto
      (fun n ↦ inverseCubeTailTruncationVarianceScale n / inverseCubeTailCLTNormingSequence n)
      atTop (𝓝 1) := by
  have hratio :
      Tendsto (fun n : ℕ ↦ ((n : ℝ) / (n + 2 : ℝ))) atTop (𝓝 1) := by
    simpa [Nat.cast_add, add_assoc] using tendsto_natCast_div_add_atTop (2 : ℝ)
  have hinside :
      Tendsto
        (fun n : ℕ ↦
          ((n : ℝ) / (n + 2 : ℝ)) *
            (Real.log (((n + 2 : ℝ) * Real.log (n + 2 : ℝ))) / Real.log (n + 2 : ℝ)))
        atTop (𝓝 1) := by
    -- Proof comment: the inside factor is the product of the shifted prefactor and the
    -- logarithmic correction, and both tend to `1`.
    simpa [one_mul] using hratio.mul inverseCubeTail_logRatio_tendsto_one
  have hrewrite :
      (fun n : ℕ ↦
        inverseCubeTailTruncationVarianceScale n / inverseCubeTailCLTNormingSequence n) =
        fun n : ℕ ↦
          Real.sqrt
            (((n : ℝ) / (n + 2 : ℝ)) *
              (Real.log (((n + 2 : ℝ) * Real.log (n + 2 : ℝ))) / Real.log (n + 2 : ℝ))) := by
    funext n
    have hden_nonneg : 0 ≤ ((n + 2 : ℝ) * Real.log (n + 2 : ℝ)) := by
      have hn_nonneg : (0 : ℝ) ≤ n := by positivity
      have htwo_lt : (1 : ℝ) < n + 2 := by linarith
      have hlog_nonneg : 0 ≤ Real.log (n + 2 : ℝ) := le_of_lt (Real.log_pos htwo_lt)
      positivity
    rw [inverseCubeTailTruncationVarianceScale, inverseCubeTailCLTNormingSequence]
    rw [← Real.sqrt_div' _ hden_nonneg]
    congr 1
    rw [div_eq_mul_inv, mul_inv_rev]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- Proof comment: rewrite the ratio as `sqrt` of an inside term converging to `1`.
  rw [hrewrite]
  have hsqrt : Tendsto (fun x : ℝ ↦ Real.sqrt x) (𝓝 1) (𝓝 (Real.sqrt 1)) :=
    Real.continuous_sqrt.continuousAt.tendsto
  simpa using hsqrt.comp hinside

/-- Helper for Exercise 15.5.3: the truncation variance scale `B_n` tends to `+∞`. -/
private lemma inverseCubeTailTruncationVarianceScale_tendsto_atTop :
    Tendsto inverseCubeTailTruncationVarianceScale atTop atTop := by
  have hsqrtLower :
      Tendsto (fun n : ℕ ↦ Real.sqrt ((1 / 2 : ℝ) * (n + 2 : ℝ))) atTop atTop := by
    have hshift : Tendsto (fun n : ℕ ↦ (n + 2 : ℝ)) atTop atTop := by
      simpa [Nat.cast_add, add_assoc] using
        tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    have hscaled :
        Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) * (n + 2 : ℝ)) atTop atTop := by
      simpa [mul_comm] using hshift.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    exact Real.tendsto_sqrt_atTop.comp hscaled
  have hcltLower :
      ∀ᶠ n : ℕ in atTop,
        Real.sqrt ((1 / 2 : ℝ) * (n + 2 : ℝ)) ≤ inverseCubeTailCLTNormingSequence n := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    rw [inverseCubeTailCLTNormingSequence]
    refine Real.sqrt_le_sqrt ?_
    have hpos : (0 : ℝ) < n + 2 := by positivity
    have hlog_lower :
        1 - (n + 2 : ℝ)⁻¹ ≤ Real.log (n + 2 : ℝ) :=
      Real.one_sub_inv_le_log_of_pos hpos
    have hhalf_le :
        (1 / 2 : ℝ) ≤ 1 - (n + 2 : ℝ)⁻¹ := by
      have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hthree_le : (3 : ℝ) ≤ n + 2 := by linarith
      have hinv_le : (n + 2 : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹ := by
        rw [inv_le_inv₀ (by positivity : (0 : ℝ) < n + 2) (by norm_num : (0 : ℝ) < 3)]
        exact hthree_le
      linarith
    have hhalf_log : (1 / 2 : ℝ) ≤ Real.log (n + 2 : ℝ) :=
      le_trans hhalf_le hlog_lower
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hhalf_log (show 0 ≤ (n + 2 : ℝ) by positivity)
  have hratioEventually :
      ∀ᶠ n : ℕ in atTop,
        (1 / 2 : ℝ) < inverseCubeTailTruncationVarianceScale n / inverseCubeTailCLTNormingSequence n := by
    filter_upwards [inverseCubeTail_truncationScaleRatio_tendsto_one.eventually
      (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))] with n hn
    exact hn.1
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        (1 / 2 : ℝ) * Real.sqrt ((1 / 2 : ℝ) * (n + 2 : ℝ)) ≤
          inverseCubeTailTruncationVarianceScale n := by
    filter_upwards [hratioEventually, hcltLower] with n hratio hclt
    have hA_pos : 0 < inverseCubeTailCLTNormingSequence n :=
      inverseCubeTailCLTNormingSequence_pos n
    have hratioMul :
        (1 / 2 : ℝ) * inverseCubeTailCLTNormingSequence n <
          inverseCubeTailTruncationVarianceScale n := by
      have hmul := mul_lt_mul_of_pos_right hratio hA_pos
      have hA_ne : inverseCubeTailCLTNormingSequence n ≠ 0 := hA_pos.ne'
      simpa [div_eq_mul_inv, hA_ne, mul_assoc, mul_left_comm, mul_comm] using hmul
    calc
      (1 / 2 : ℝ) * Real.sqrt ((1 / 2 : ℝ) * (n + 2 : ℝ))
          ≤ (1 / 2 : ℝ) * inverseCubeTailCLTNormingSequence n := by
            gcongr
      _ ≤ inverseCubeTailTruncationVarianceScale n := hratioMul.le
  have hbase :
      Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) * Real.sqrt ((1 / 2 : ℝ) * (n + 2 : ℝ))) atTop atTop := by
    simpa [mul_comm] using hsqrtLower.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  -- Proof comment: the ratio `B_n / A_n` is eventually bounded below by `1 / 2`, while `A_n`
  -- already dominates a positive multiple of `√n`.
  exact tendsto_atTop_mono' atTop hlower hbase

/-- Helper for Exercise 15.5.3: the logarithmic normalization defect from replacing `B_n` by
`A_n` is negligible. -/
private lemma inverseCubeTail_scaleLogDefect_tendsto_zero :
    Tendsto
      (fun n ↦
        Real.log
            (inverseCubeTailCLTNormingSequence (n + 1) /
              inverseCubeTailTruncationVarianceScale (n + 1)) *
          (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹)
      atTop (𝓝 0) := by
  have hratio :
      Tendsto
        (fun n : ℕ ↦
          inverseCubeTailTruncationVarianceScale (n + 1) /
            inverseCubeTailCLTNormingSequence (n + 1))
        atTop (𝓝 1) := by
    simpa using inverseCubeTail_truncationScaleRatio_tendsto_one.comp (tendsto_add_atTop_nat 1)
  have hlogRatio :
      Tendsto
        (fun n : ℕ ↦
          Real.log
            (inverseCubeTailTruncationVarianceScale (n + 1) /
              inverseCubeTailCLTNormingSequence (n + 1)))
        atTop (𝓝 0) := by
    simpa using ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio)
  have hinnerAtTop :
      Tendsto (fun n : ℕ ↦ ((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) atTop atTop := by
    have hshift : Tendsto (fun n : ℕ ↦ (n + 3 : ℝ)) atTop atTop := by
      simpa [Nat.cast_add, add_assoc] using
        tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop
    have hlinear :
        Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) * (n + 3 : ℝ)) atTop atTop := by
      simpa [mul_comm] using hshift.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    have hlower :
        ∀ᶠ n : ℕ in atTop,
          (1 / 2 : ℝ) * (n + 3 : ℝ) ≤ (n + 3 : ℝ) * Real.log (n + 3 : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
      have hpos : (0 : ℝ) < n + 3 := by positivity
      have hlog_lower :
          1 - (n + 3 : ℝ)⁻¹ ≤ Real.log (n + 3 : ℝ) :=
        Real.one_sub_inv_le_log_of_pos hpos
      have hhalf_le :
          (1 / 2 : ℝ) ≤ 1 - (n + 3 : ℝ)⁻¹ := by
        have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have hfour_le : (4 : ℝ) ≤ n + 3 := by linarith
        have hinv_le : (n + 3 : ℝ)⁻¹ ≤ (4 : ℝ)⁻¹ := by
          rw [inv_le_inv₀ (by positivity : (0 : ℝ) < n + 3) (by norm_num : (0 : ℝ) < 4)]
          exact hfour_le
        linarith
      have hhalf_log : (1 / 2 : ℝ) ≤ Real.log (n + 3 : ℝ) :=
        le_trans hhalf_le hlog_lower
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hhalf_log (show 0 ≤ (n + 3 : ℝ) by positivity)
    exact tendsto_atTop_mono' atTop hlower hlinear
  have hlogNormalizerInv :
      Tendsto
        (fun n : ℕ ↦ (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹)
        atTop (𝓝 0) := by
    have hlogAtTop :
        Tendsto
          (fun n : ℕ ↦ Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))
          atTop atTop :=
      Real.tendsto_log_atTop.comp hinnerAtTop
    simpa [one_div] using tendsto_inv_atTop_zero.comp hlogAtTop
  have hprod :
      Tendsto
        (fun n : ℕ ↦
          (-Real.log
              (inverseCubeTailTruncationVarianceScale (n + 1) /
                inverseCubeTailCLTNormingSequence (n + 1))) *
            (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹)
        atTop (𝓝 0) := by
    simpa [zero_mul] using hlogRatio.neg.mul hlogNormalizerInv
  have heq :
      ∀ n : ℕ,
        Real.log
            (inverseCubeTailCLTNormingSequence (n + 1) /
              inverseCubeTailTruncationVarianceScale (n + 1)) *
          (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹ =
          (-Real.log
              (inverseCubeTailTruncationVarianceScale (n + 1) /
                inverseCubeTailCLTNormingSequence (n + 1))) *
            (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹ := by
    intro n
    have hA_ne : inverseCubeTailCLTNormingSequence (n + 1) ≠ 0 :=
      (inverseCubeTailCLTNormingSequence_pos (n + 1)).ne'
    have hB_ne : inverseCubeTailTruncationVarianceScale (n + 1) ≠ 0 :=
      (inverseCubeTailTruncationVarianceScale_pos n).ne'
    have hratioInv :
        inverseCubeTailCLTNormingSequence (n + 1) /
            inverseCubeTailTruncationVarianceScale (n + 1) =
          (inverseCubeTailTruncationVarianceScale (n + 1) /
            inverseCubeTailCLTNormingSequence (n + 1))⁻¹ := by
      field_simp [hA_ne, hB_ne]
    rw [hratioInv, Real.log_inv]
  -- Proof comment: `log (A_n / B_n)` is just `-log (B_n / A_n)`, and the remaining inverse
  -- logarithmic factor already tends to `0`.
  exact Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (heq n).symm) hprod

/-- Helper for Exercise 15.5.3: on the positive tail `(1, ∞)`, multiplying the inverse-cube-tail
density by `x^2` leaves the harmonic kernel `x⁻¹`. -/
private lemma inverseCubeTail_sqDensity_eq_invOnIoi :
    Set.EqOn
      (fun x : ℝ ↦ x ^ (2 : ℕ) *
        (ENNReal.ofReal (symmetricParetoDensityReal (1 / 2) x)).toReal)
      (fun x : ℝ ↦ x⁻¹)
      (Set.Ioi 1) := by
  intro x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hx1 : 1 ≤ |x| := by
    simpa [abs_of_pos hx0] using le_of_lt hx
  have hDensity :
      (ENNReal.ofReal (symmetricParetoDensityReal (1 / 2) x)).toReal = (x ^ (3 : ℕ))⁻¹ := by
    rw [symmetricParetoDensityReal_eq (1 / 2) x]
    have hx1' : 1 ≤ x := le_of_lt hx
    have hpow_nonneg : 0 ≤ x ^ (-1 - 2 : ℝ) := by positivity
    have hpow :
        x ^ (-1 - 2 : ℝ) = (x ^ (3 : ℕ))⁻¹ := by
      calc
        x ^ (-1 - 2 : ℝ) = x ^ (-(3 : ℝ)) := by norm_num
        _ = (x ^ (3 : ℝ))⁻¹ := by rw [Real.rpow_neg (le_of_lt hx0)]
        _ = (x ^ (3 : ℕ))⁻¹ := by simp
    simp [hx1', abs_of_pos hx0]
    rw [ENNReal.toReal_ofReal hpow_nonneg, hpow]
  have hx_ne : x ≠ 0 := ne_of_gt hx0
  calc
    x ^ (2 : ℕ) * (ENNReal.ofReal (symmetricParetoDensityReal (1 / 2) x)).toReal
        = x ^ (2 : ℕ) * (x ^ (3 : ℕ))⁻¹ := by rw [hDensity]
    _ = x⁻¹ := by
          field_simp [hx_ne]

/-- Helper for Exercise 15.5.3: the textbook inverse-cube-tail density is the symmetrized
one-sided Pareto density evaluated at `|x|`. -/
private lemma inverseCubeTailDensityReal_eq_half_paretoAbs (x : ℝ) :
    symmetricParetoDensityReal (1 / 2) x = (1 / 2 : ℝ) * paretoPDFReal 1 2 |x| := by
  by_cases habs : 1 ≤ |x|
  · rw [symmetricParetoDensityReal_eq (1 / 2) x, paretoPDFReal, if_pos habs, if_pos habs]
    -- Proof comment: on `|x| ≥ 1`, both formulas reduce to the same `|x|⁻³` kernel.
    simp
    ring_nf
  · rw [symmetricParetoDensityReal_eq (1 / 2) x, paretoPDFReal, if_neg habs, if_neg habs]
    -- Proof comment: away from the tail support, both densities vanish.
    simp

/-- Helper for Exercise 15.5.3: identify the `ENNReal` scalar `1 / 2` with the real half. -/
private lemma ennrealHalf_eq_ofRealHalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
  have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
  calc
    (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by rw [one_div]
    _ = (ENNReal.ofReal (2 : ℝ))⁻¹ := by rw [htwo]
    _ = ENNReal.ofReal ((2 : ℝ)⁻¹) := by rw [← ENNReal.ofReal_inv_of_pos zero_lt_two]
    _ = ENNReal.ofReal (1 / 2 : ℝ) := by norm_num

-- Route correction: the asymptotic prefix is now stable. The next block rebuilds the measure
-- interface directly from density identities before returning to the shell/Lindeberg suffix.

/-- Helper for Exercise 15.5.3: the inverse-cube-tail `ENNReal` density splits into the positive
shape-`2` Pareto density and its reflection. -/
private lemma inverseCubeTailDensity_toENNReal_eq_half_add_reflected (x : ℝ) :
    ENNReal.ofReal (symmetricParetoDensityReal (1 / 2) x) =
      (1 / 2 : ENNReal) * paretoPDF 1 2 x + (1 / 2 : ENNReal) * paretoPDF 1 2 (-x) := by
  by_cases habs : 1 ≤ |x|
  · by_cases hx : 0 ≤ x
    · have hx1 : 1 ≤ x := by rwa [abs_of_nonneg hx] at habs
      have hneglt : -x < 1 := by linarith
      -- Proof comment: on the positive half-line only the non-reflected Pareto branch survives.
      rw [symmetricParetoDensityReal_eq (1 / 2) x, abs_of_nonneg hx]
      rw [paretoPDF_of_le hx1, paretoPDF_of_lt hneglt]
      simp [hx1, ENNReal.ofReal_mul]
      simpa [mul_assoc] using
        (ENNReal.inv_mul_cancel_left
          (a := (2 : ENNReal))
          (b := ENNReal.ofReal (x ^ (-1 + -2)))
          two_ne_zero
          (by simp : (2 : ENNReal) ≠ ∞)).symm
    · have hxlt : x < 0 := lt_of_not_ge hx
      have hneg1 : 1 ≤ -x := by simpa [abs_of_neg hxlt] using habs
      have hxlt1 : x < 1 := by linarith
      -- Proof comment: on the negative half-line only the reflected Pareto branch survives.
      rw [symmetricParetoDensityReal_eq (1 / 2) x, abs_of_neg hxlt]
      rw [paretoPDF_of_lt hxlt1, paretoPDF_of_le hneg1]
      simp [hneg1, ENNReal.ofReal_mul]
      simpa [mul_assoc] using
        (ENNReal.inv_mul_cancel_left
          (a := (2 : ENNReal))
          (b := ENNReal.ofReal ((-x) ^ (-1 + -2)))
          two_ne_zero
          (by simp : (2 : ENNReal) ≠ ∞)).symm
  · have habs_lt : |x| < 1 := lt_of_not_ge habs
    have hxlt : x < 1 := lt_of_le_of_lt (le_abs_self x) habs_lt
    have hneglt : -x < 1 := lt_of_le_of_lt (neg_le_abs x) habs_lt
    -- Proof comment: away from `|x| ≥ 1`, both Pareto branches vanish.
    rw [symmetricParetoDensityReal_eq (1 / 2) x, paretoPDF_of_lt hxlt, paretoPDF_of_lt hneglt]
    simp [habs, ENNReal.ofReal_zero]

/-- Helper for Exercise 15.5.3: reflecting a measurable density across `x ↦ -x` rewrites the
restricted Lebesgue `lintegral` on measurable sets. -/
private lemma lintegral_preimage_neg_eq (f : ℝ → ℝ≥0∞) (hf : Measurable f) {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∫⁻ x in (fun x : ℝ ↦ -x) ⁻¹' s, f x ∂volume = ∫⁻ x in s, f (-x) ∂volume := by
  have hneg_meas : Measurable (fun x : ℝ ↦ -x) := by fun_prop
  have hmap :
      ∫⁻ y in s, f (-y) ∂volume = ∫⁻ x in (fun x : ℝ ↦ -x) ⁻¹' s, f x ∂volume := by
    -- Proof comment: `x ↦ -x` preserves Lebesgue measure, so we can push the integral through
    -- the measurable equivalence and rewrite the integrand by composition.
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    simpa [Function.comp] using
      (setLIntegral_map
        (μ := (volume : Measure ℝ))
        (g := fun x : ℝ ↦ -x)
        (f := fun y : ℝ ↦ f (-y))
        hs
        (hf.comp hneg_meas)
        hneg_meas)
  exact hmap.symm

/-- Helper for Exercise 15.5.3: the inverse-cube-tail law is the average of the one-sided
shape-`2` Pareto law `paretoMeasure 1 2` and its reflection. -/
private theorem inverseCubeTailMeasure_eq_symmetrized_paretoMeasure :
    symmetricParetoMeasure (1 / 2) =
      (1 / 2 : ENNReal) • paretoMeasure 1 2 +
        (1 / 2 : ENNReal) • (paretoMeasure 1 2).map (fun x ↦ -x) := by
  have hpareto_meas : Measurable (paretoPDF 1 2) := by
    simpa [paretoPDF] using (measurable_paretoPDFReal 1 2).ennreal_ofReal
  have hpareto_reflect_meas : Measurable (fun x : ℝ ↦ paretoPDF 1 2 (-x)) :=
    hpareto_meas.comp (by fun_prop)
  have hhalf_pareto_reflect_meas :
      Measurable (fun x : ℝ ↦ (1 / 2 : ENNReal) * paretoPDF 1 2 (-x)) := by
    fun_prop
  ext s hs
  -- Proof comment: rewrite every measure on the same measurable set through its defining density.
  rw [symmetricParetoMeasure, withDensity_apply _ hs]
  rw [show (fun x ↦ ENNReal.ofReal (symmetricParetoDensityReal (1 / 2) x)) =
      fun x ↦ (1 / 2 : ENNReal) * paretoPDF 1 2 x +
        (1 / 2 : ENNReal) * paretoPDF 1 2 (-x) by
      funext x
      exact inverseCubeTailDensity_toENNReal_eq_half_add_reflected x]
  have hadd :
      ∫⁻ x in s, (1 / 2 : ENNReal) * paretoPDF 1 2 x +
          (1 / 2 : ENNReal) * paretoPDF 1 2 (-x) ∂volume =
        ∫⁻ x in s, (1 / 2 : ENNReal) * paretoPDF 1 2 x ∂volume +
          ∫⁻ x in s, (1 / 2 : ENNReal) * paretoPDF 1 2 (-x) ∂volume := by
    simpa using
      (lintegral_add_right
        (μ := volume.restrict s)
        (f := fun x : ℝ ↦ (1 / 2 : ENNReal) * paretoPDF 1 2 x)
        (g := fun x : ℝ ↦ (1 / 2 : ENNReal) * paretoPDF 1 2 (-x))
        hhalf_pareto_reflect_meas)
  have hbase_apply :
      ((1 / 2 : ENNReal) • paretoMeasure 1 2) s =
        (1 / 2 : ENNReal) * ∫⁻ x in s, paretoPDF 1 2 x ∂volume := by
    rw [Measure.coe_smul, Pi.smul_apply, smul_eq_mul, paretoMeasure, withDensity_apply _ hs]
  have hmap_apply :
      ((1 / 2 : ENNReal) • (paretoMeasure 1 2).map (fun x : ℝ ↦ -x)) s =
        (1 / 2 : ENNReal) * ∫⁻ x in s, paretoPDF 1 2 (-x) ∂volume := by
    rw [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [Measure.map_apply (by fun_prop) hs, paretoMeasure]
    rw [withDensity_apply _ ((by fun_prop : Measurable (fun x : ℝ ↦ -x)) hs)]
    rw [lintegral_preimage_neg_eq (f := paretoPDF 1 2) hpareto_meas hs]
  calc
    ∫⁻ x in s, (1 / 2 : ENNReal) * paretoPDF 1 2 x +
        (1 / 2 : ENNReal) * paretoPDF 1 2 (-x) ∂volume
      = (1 / 2 : ENNReal) * ∫⁻ x in s, paretoPDF 1 2 x ∂volume +
          (1 / 2 : ENNReal) * ∫⁻ x in s, paretoPDF 1 2 (-x) ∂volume := by
            rw [hadd]
            rw [lintegral_const_mul _ hpareto_meas]
            rw [lintegral_const_mul _ hpareto_reflect_meas]
    _ = ((1 / 2 : ENNReal) • paretoMeasure 1 2) s +
          ((1 / 2 : ENNReal) • (paretoMeasure 1 2).map (fun x : ℝ ↦ -x)) s := by
            rw [hbase_apply, hmap_apply]
    _ = ((1 / 2 : ENNReal) • paretoMeasure 1 2 +
          (1 / 2 : ENNReal) • (paretoMeasure 1 2).map (fun x : ℝ ↦ -x)) s := by
            rw [Measure.add_apply]

/-- Helper for Exercise 15.5.3: the inverse-cube-tail law is a probability measure. -/
private theorem isProbabilityMeasure_inverseCubeTailMeasure :
    IsProbabilityMeasure (symmetricParetoMeasure (1 / 2)) where
  measure_univ := by
    letI : IsProbabilityMeasure (paretoMeasure 1 2) :=
      isProbabilityMeasure_paretoMeasure zero_lt_one zero_lt_two
    have hmap_univ :
        (paretoMeasure 1 2).map (fun x : ℝ ↦ -x) Set.univ = 1 := by
      -- Proof comment: reflection preserves the total mass of the one-sided Pareto law.
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
      simpa using (IsProbabilityMeasure.measure_univ : paretoMeasure 1 2 Set.univ = 1)
    -- Proof comment: the inverse-cube-tail law is the average of two probability measures.
    calc
      symmetricParetoMeasure (1 / 2) Set.univ
          = ((1 / 2 : ENNReal) • paretoMeasure 1 2 +
              (1 / 2 : ENNReal) • (paretoMeasure 1 2).map (fun x ↦ -x)) Set.univ := by
                rw [inverseCubeTailMeasure_eq_symmetrized_paretoMeasure]
      _ = (1 / 2 : ENNReal) * paretoMeasure 1 2 Set.univ +
            (1 / 2 : ENNReal) * ((paretoMeasure 1 2).map (fun x ↦ -x) Set.univ) := by
              simp [Measure.add_apply, smul_eq_mul]
      _ = (1 / 2 : ENNReal) * 1 + (1 / 2 : ENNReal) * 1 := by
            simp [hmap_univ]
      _ = 1 := by
            simpa using ENNReal.inv_two_add_inv_two

/-- Helper for Exercise 15.5.3: the square truncated to `[-R, R]` is integrable under the
one-sided shape-`2` Pareto law. -/
private lemma integrable_paretoShapeTwo_truncatedSquare (R : ℝ) :
    Integrable
      (Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)))
      (paretoMeasure 1 2) := by
  letI : IsProbabilityMeasure (paretoMeasure 1 2) :=
    isProbabilityMeasure_paretoMeasure zero_lt_one zero_lt_two
  have hmeas :
      Measurable (Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ))) := by
    exact (measurable_id.pow_const 2).indicator measurableSet_Icc
  -- Proof comment: on `[-R, R]` the truncated square is bounded by the constant `R²`.
  refine Integrable.of_bound hmeas.aestronglyMeasurable (R ^ (2 : ℕ)) ?_
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem hx, Real.norm_of_nonneg (by positivity)]
    nlinarith [hx.1, hx.2]
  · rw [Set.indicator_of_notMem hx]
    simpa using (show (0 : ℝ) ≤ R ^ (2 : ℕ) by positivity)

/-- Helper for Exercise 15.5.3: the square truncated to `[-R, R]` is integrable under the
inverse-cube-tail law. -/
private lemma integrable_inverseCubeTail_truncatedSquare (R : ℝ) :
    Integrable
      (Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)))
      (symmetricParetoMeasure (1 / 2)) := by
  letI : IsProbabilityMeasure (symmetricParetoMeasure (1 / 2)) :=
    isProbabilityMeasure_inverseCubeTailMeasure
  have hmeas :
      Measurable (Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ))) := by
    exact (measurable_id.pow_const 2).indicator measurableSet_Icc
  -- Proof comment: the same bounded-support argument works because the inverse-cube-tail law is
  -- also a probability measure.
  refine Integrable.of_bound hmeas.aestronglyMeasurable (R ^ (2 : ℕ)) ?_
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem hx, Real.norm_of_nonneg (by positivity)]
    nlinarith [hx.1, hx.2]
  · rw [Set.indicator_of_notMem hx]
    simpa using (show (0 : ℝ) ≤ R ^ (2 : ℕ) by positivity)

/-- Helper for Exercise 15.5.3: the one-sided Pareto law `paretoMeasure 1 2` has tail mass
`R⁻²` on `(R, ∞)`. -/
private lemma paretoMeasure_shapeTwo_Ioi (R : ℝ) (hR : 1 ≤ R) :
    paretoMeasure 1 2 (Set.Ioi R) = ENNReal.ofReal ((R⁻¹) ^ (2 : ℕ)) := by
  letI : IsProbabilityMeasure (paretoMeasure 1 2) :=
    isProbabilityMeasure_paretoMeasure zero_lt_one zero_lt_two
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [← ENNReal.ofReal_toReal (measure_lt_top (paretoMeasure 1 2) (Set.Ioi R)).ne]
  refine congrArg ENNReal.ofReal ?_
  rw [paretoMeasure, withDensity_apply _ measurableSet_Ioi]
  change (∫⁻ a in Set.Ioi R, ENNReal.ofReal (paretoPDFReal 1 2 a) ∂volume).toReal = (R⁻¹) ^ (2 : ℕ)
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi R)] fun x : ℝ ↦ paretoPDFReal 1 2 x := by
    exact Filter.Eventually.of_forall fun x ↦ paretoPDFReal_nonneg zero_le_one zero_le_two x
  have hmeasR : AEStronglyMeasurable (paretoPDFReal 1 2) (volume.restrict (Set.Ioi R)) :=
    (measurable_paretoPDFReal 1 2).aestronglyMeasurable
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeasR]
  have hkernel :
      ∫ x in Set.Ioi R, paretoPDFReal 1 2 x ∂volume =
        ∫ x in Set.Ioi R, (2 : ℝ) * x ^ (-(3 : ℝ)) ∂volume := by
    -- Proof comment: on `(R, ∞)` with `R ≥ 1`, the Pareto density is the explicit `2 x⁻³`
    -- kernel.
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have hx1 : 1 ≤ x := le_trans hR (le_of_lt hx)
    rw [paretoPDFReal, if_pos hx1]
    norm_num
  rw [hkernel, integral_const_mul, integral_Ioi_rpow_of_lt (a := -3) (by norm_num) hR0]
  calc
    (2 : ℝ) * (-R ^ ((-3 : ℝ) + 1) / ((-3 : ℝ) + 1)) = R ^ (-(2 : ℝ)) := by
      ring
    _ = (R⁻¹) ^ (2 : ℕ) := by
          rw [Real.rpow_neg (le_of_lt hR0)]
          have hpow : R ^ (2 : ℝ) = (R ^ (2 : ℕ) : ℝ) := by
            simpa using (Real.rpow_natCast R 2)
          rw [hpow, inv_pow]

/-- Helper for Exercise 15.5.3: the inverse-cube-tail law has exact tail mass `R⁻²` outside
`[-R, R]`. -/
lemma inverseCubeTail_tailMass (R : ℝ) (hR : 1 ≤ R) :
    symmetricParetoMeasure (1 / 2) {x : ℝ | R < |x|} = ENNReal.ofReal ((R⁻¹) ^ (2 : ℕ)) := by
  let s : Set ℝ := {x : ℝ | R < |x|}
  have hs : MeasurableSet s := by
    exact measurableSet_lt measurable_const measurable_abs
  have hbase :
      paretoMeasure 1 2 s = ENNReal.ofReal ((R⁻¹) ^ (2 : ℕ)) := by
    rw [paretoMeasure, withDensity_apply _ hs]
    -- Proof comment: the one-sided Pareto law charges only the positive half-line, so the shell
    -- event reduces to `(R, ∞)`.
    calc
      ∫⁻ x in s, paretoPDF 1 2 x ∂volume
          = ∫⁻ x, Set.indicator (Set.Ioi R) (paretoPDF 1 2) x ∂volume := by
            rw [← lintegral_indicator hs]
            refine lintegral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
            by_cases hsx : x ∈ s
            · by_cases hxR : x ∈ Set.Ioi R
              · simp [hsx, hxR]
              · have hx_nonpos : x ≤ 0 := by
                  by_contra hx_pos
                  have hx_pos' : 0 < x := lt_of_not_ge hx_pos
                  have hx_mem : x ∈ Set.Ioi R := by
                    simpa [s, Set.mem_Ioi, abs_of_pos hx_pos'] using hsx
                  exact hxR hx_mem
                have hxlt1 : x < 1 := lt_of_le_of_lt hx_nonpos zero_lt_one
                simp [hsx, hxR, paretoPDF_of_lt hxlt1]
            · have hxR : x ∉ Set.Ioi R := by
                intro hxR
                exact hsx <| by
                  have hxR' : R < x := hxR
                  have hx_pos : 0 < x := by linarith
                  simpa [s, Set.mem_Ioi, abs_of_pos hx_pos] using hxR'
              simp [hxR, hsx]
      _ = ∫⁻ x in Set.Ioi R, paretoPDF 1 2 x ∂volume := by
            rw [lintegral_indicator measurableSet_Ioi]
      _ = paretoMeasure 1 2 (Set.Ioi R) := by
            rw [paretoMeasure, withDensity_apply _ measurableSet_Ioi]
      _ = ENNReal.ofReal ((R⁻¹) ^ (2 : ℕ)) := paretoMeasure_shapeTwo_Ioi R hR
  have hmap :
      ((paretoMeasure 1 2).map (fun x ↦ -x)) s = paretoMeasure 1 2 s := by
    -- Proof comment: the shell event is invariant under reflection.
    rw [Measure.map_apply (by fun_prop) hs]
    congr 1
    ext x
    simp [s, abs_neg]
  -- Proof comment: both halves of the symmetrized measure contribute the same shell mass.
  calc
    symmetricParetoMeasure (1 / 2) s
        = ((1 / 2 : ENNReal) • paretoMeasure 1 2 +
            (1 / 2 : ENNReal) • (paretoMeasure 1 2).map (fun x ↦ -x)) s := by
              rw [inverseCubeTailMeasure_eq_symmetrized_paretoMeasure]
    _ = (1 / 2 : ENNReal) * paretoMeasure 1 2 s +
          (1 / 2 : ENNReal) * ((paretoMeasure 1 2).map (fun x ↦ -x) s) := by
            simp [Measure.add_apply, hs, smul_eq_mul]
    _ = (1 / 2 : ENNReal) * paretoMeasure 1 2 s + (1 / 2 : ENNReal) * paretoMeasure 1 2 s := by
          rw [hmap]
    _ = paretoMeasure 1 2 s := by
          have hhalf : (1 / 2 : ENNReal) + 1 / 2 = 1 := by
            simpa using ENNReal.inv_two_add_inv_two
          rw [← add_mul, hhalf, one_mul]
    _ = ENNReal.ofReal ((R⁻¹) ^ (2 : ℕ)) := hbase

/-- Helper for Exercise 15.5.3: the truncated second moment of `paretoMeasure 1 2` on `[-R, R]`
equals `2 log R`. -/
private lemma paretoMeasure_shapeTwo_truncatedSecondMoment (R : ℝ) (hR : 1 ≤ R) :
    ∫ x in Set.Icc (-R) R, x ^ (2 : ℕ) ∂paretoMeasure 1 2 = 2 * Real.log R := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hpareto_meas : Measurable (paretoPDF 1 2) := by
    simpa [paretoPDF] using (measurable_paretoPDFReal 1 2).ennreal_ofReal
  have hkernel :
      (fun x : ℝ ↦
        (paretoPDF 1 2 x).toReal •
          Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x) =
        Set.indicator (Set.Icc (1 : ℝ) R) (fun x : ℝ ↦ (2 : ℝ) * x⁻¹) := by
    -- Proof comment: on `[1, R]` the shape-`2` Pareto density is `2 * x⁻³`, so multiplying by
    -- `x²` leaves the harmonic kernel `2 / x`; away from that interval one side vanishes.
    funext x
    by_cases hx : x ∈ Set.Icc (1 : ℝ) R
    · have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
      have hx_ne : x ≠ 0 := ne_of_gt hx0
      have hsupport : x ∈ Set.Icc (-R) R := by
        constructor
        · linarith
        · exact hx.2
      rw [Set.indicator_of_mem hsupport, Set.indicator_of_mem hx, smul_eq_mul]
      rw [paretoPDF_of_le hx.1, ENNReal.toReal_ofReal]
      · have hxpow_base :
            x ^ (-(2 + 1 : ℝ)) * x ^ (2 : ℕ) = x⁻¹ := by
          rw [show x ^ (2 : ℕ) = x ^ (2 : ℝ) by exact (Real.rpow_natCast x 2).symm]
          calc
            x ^ (-(2 + 1 : ℝ)) * x ^ (2 : ℝ) = x ^ (-(1 : ℝ)) := by
              rw [← Real.rpow_add hx0]
              congr 1
              ring
            _ = x⁻¹ := by
              rw [Real.rpow_neg (le_of_lt hx0)]
              simp
        have hxpow : x ^ (-1 + -2 : ℝ) * x ^ (2 : ℕ) = x⁻¹ := by
          simpa using hxpow_base
        have hxpow' : x ^ (2 : ℕ) * x ^ (-1 + -2 : ℝ) = x⁻¹ := by
          calc
            x ^ (2 : ℕ) * x ^ (-1 + -2 : ℝ) = x ^ (-1 + -2 : ℝ) * x ^ (2 : ℕ) := by ring
            _ = x⁻¹ := hxpow
        simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t : ℝ ↦ 2 * t) hxpow'
      · positivity
    · have hx_split : x < 1 ∨ R < x := by
        by_cases hx1 : x < 1
        · exact Or.inl hx1
        · have hx1' : 1 ≤ x := le_of_not_gt hx1
          have hxR : ¬ x ≤ R := fun hxR ↦ hx ⟨hx1', hxR⟩
          exact Or.inr (lt_of_not_ge hxR)
      rcases hx_split with hx_lt1 | hRx
      · by_cases hsupport : x ∈ Set.Icc (-R) R
        · rw [Set.indicator_of_mem hsupport, Set.indicator_of_notMem hx, smul_eq_mul,
            paretoPDF_of_lt hx_lt1, ENNReal.toReal_zero]
          simp
        · rw [Set.indicator_of_notMem hsupport, Set.indicator_of_notMem hx]
          simp
      · have hsupport : x ∉ Set.Icc (-R) R := fun hsupport ↦ not_lt_of_ge hsupport.2 hRx
        rw [Set.indicator_of_notMem hsupport, Set.indicator_of_notMem hx]
        simp
  rw [← integral_indicator measurableSet_Icc]
  calc
    ∫ x, Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x ∂paretoMeasure 1 2
        = ∫ x,
            (paretoPDF 1 2 x).toReal •
              Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x ∂volume := by
            rw [paretoMeasure]
            simpa [smul_eq_mul] using
              (integral_withDensity_eq_integral_toReal_smul
                hpareto_meas
                (by
                  filter_upwards with x
                  simp [paretoPDF])
                (fun x : ℝ ↦ Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x))
    _ = ∫ x, Set.indicator (Set.Icc (1 : ℝ) R) (fun x : ℝ ↦ (2 : ℝ) * x⁻¹) x ∂volume := by
          rw [hkernel]
    _ = ∫ x in Set.Icc (1 : ℝ) R, (2 : ℝ) * x⁻¹ ∂volume := by
          rw [integral_indicator measurableSet_Icc]
    _ = ∫ x in Set.Ioc (1 : ℝ) R, (2 : ℝ) * x⁻¹ ∂volume := by
          rw [integral_Icc_eq_integral_Ioc]
    _ = ∫ x in (1 : ℝ)..R, (2 : ℝ) * x⁻¹ := by
          rw [← intervalIntegral.integral_of_le hR]
    _ = 2 * ∫ x in (1 : ℝ)..R, x⁻¹ := by
          rw [intervalIntegral.integral_const_mul]
    _ = 2 * Real.log R := by
          rw [integral_inv_of_pos zero_lt_one hR0]
          simp

/-- Helper for Exercise 15.5.3: the truncated second moment of the inverse-cube-tail law on
`[-R, R]` is exactly `2 log R`. -/
lemma inverseCubeTail_truncatedSecondMoment (R : ℝ) (hR : 1 ≤ R) :
    ∫ x in Set.Icc (-R) R, x ^ (2 : ℕ) ∂symmetricParetoMeasure (1 / 2) = 2 * Real.log R := by
  let μ : Measure ℝ := paretoMeasure 1 2
  let g : ℝ → ℝ := Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ))
  rw [← integral_indicator measurableSet_Icc]
  have hg_int : Integrable g μ := by
    simpa [g, μ] using integrable_paretoShapeTwo_truncatedSquare R
  have hbase : ∫ x, g x ∂μ = 2 * Real.log R := by
    calc
      ∫ x, g x ∂μ = ∫ x in Set.Icc (-R) R, x ^ (2 : ℕ) ∂μ := by
        simpa [g] using
          (integral_indicator (μ := μ) (f := fun x : ℝ ↦ x ^ (2 : ℕ)) measurableSet_Icc)
      _ = 2 * Real.log R := by simpa [μ] using paretoMeasure_shapeTwo_truncatedSecondMoment R hR
  have hg_comp :
      Integrable (g ∘ fun x : ℝ ↦ -x) μ := by
    -- Proof comment: the truncation interval is symmetric and `x ↦ x²` is even, so composing
    -- with reflection does not change the truncated square.
    have hg_even : (g ∘ fun x : ℝ ↦ -x) = g := by
      funext x
      dsimp [g]
      by_cases hx : x ∈ Set.Icc (-R) R
      · have hnegx : -x ∈ Set.Icc (-R) R := by
          constructor <;> linarith [hx.1, hx.2]
        simp [hx, hnegx, sq]
      · have hnegx : -x ∉ Set.Icc (-R) R := by
          intro hnegx
          apply hx
          constructor <;> linarith [hnegx.1, hnegx.2]
        simp [hx, hnegx]
    rw [hg_even]
    exact hg_int
  have hg_map_int : Integrable g (μ.map (fun x : ℝ ↦ -x)) := by
    exact (integrable_map_equiv (μ := μ) (MeasurableEquiv.neg ℝ) g).2 hg_comp
  have hg_map :
      ∫ x, g x ∂μ.map (fun x : ℝ ↦ -x) = ∫ x, g x ∂μ := by
    calc
      ∫ x, g x ∂μ.map (fun x : ℝ ↦ -x) = ∫ x, g (-x) ∂μ := by
            simpa [μ, g] using (integral_map_equiv (μ := μ) (MeasurableEquiv.neg ℝ) g)
      _ = ∫ x, g x ∂μ := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
            dsimp [g]
            by_cases hx : x ∈ Set.Icc (-R) R
            · have hnegx : -x ∈ Set.Icc (-R) R := by
                constructor <;> linarith [hx.1, hx.2]
              simp [hx, hnegx, sq]
            · have hnegx : -x ∉ Set.Icc (-R) R := by
                intro hnegx
                apply hx
                constructor <;> linarith [hnegx.1, hnegx.2]
              simp [hx, hnegx]
  -- Proof comment: rewrite the inverse-cube-tail law as the average of the one-sided Pareto law
  -- and its reflection, then use the evenness of the truncated square.
  calc
    ∫ x, Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x
        ∂symmetricParetoMeasure (1 / 2)
        = ∫ x, g x ∂symmetricParetoMeasure (1 / 2) := by
            rfl
    _
        = ∫ x, g x ∂((1 / 2 : ENNReal) • μ + (1 / 2 : ENNReal) • μ.map (fun x ↦ -x)) := by
            rw [inverseCubeTailMeasure_eq_symmetrized_paretoMeasure]
    _ = ∫ x, g x ∂((1 / 2 : ENNReal) • μ) + ∫ x, g x ∂((1 / 2 : ENNReal) • μ.map (fun x ↦ -x)) := by
          exact integral_add_measure
            (hg_int.smul_measure (by simp : (1 / 2 : ENNReal) ≠ ∞))
            (hg_map_int.smul_measure (by simp : (1 / 2 : ENNReal) ≠ ∞))
    _ = (1 / 2 : ℝ) * ∫ x, g x ∂μ + (1 / 2 : ℝ) * ∫ x, g x ∂μ.map (fun x ↦ -x) := by
          rw [integral_smul_measure, integral_smul_measure]
          simp
    _ = (1 / 2 : ℝ) * (2 * Real.log R) + (1 / 2 : ℝ) * (2 * Real.log R) := by
          rw [hg_map, hbase]
    _ = 2 * Real.log R := by ring

/-- Helper for Exercise 15.5.3: the inverse-cube-tail truncated second moment on the exact shell
`{x | r < |x| ∧ |x| ≤ R}` is the logarithmic gap `2 (log R - log r)`. -/
private lemma inverseCubeTail_shellSecondMoment (r R : ℝ) (hr : 1 ≤ r) (hR : r ≤ R) :
    ∫ x,
        Set.indicator {x : ℝ | r < |x| ∧ |x| ≤ R} (fun x ↦ x ^ (2 : ℕ)) x
          ∂symmetricParetoMeasure (1 / 2) =
      2 * (Real.log R - Real.log r) := by
  have hR_ge_one : 1 ≤ R := le_trans hr hR
  have hshell :
      Set.indicator {x : ℝ | r < |x| ∧ |x| ≤ R} (fun x ↦ x ^ (2 : ℕ)) =
        fun x : ℝ ↦
          Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x -
            Set.indicator (Set.Icc (-r) r) (fun x : ℝ ↦ x ^ (2 : ℕ)) x := by
    -- Proof comment: the shell is the difference between the large symmetric truncation and the
    -- nested smaller truncation because `r ≤ R`.
    funext x
    by_cases hRabs : |x| ≤ R
    · by_cases hrabs : |x| ≤ r
      · have hbig : x ∈ Set.Icc (-R) R := by
          simpa [Set.mem_Icc, abs_le] using hRabs
        have hsmall : x ∈ Set.Icc (-r) r := by
          simpa [Set.mem_Icc, abs_le] using hrabs
        have hshell_not : x ∉ {x : ℝ | r < |x| ∧ |x| ≤ R} := by
          simp [hrabs]
        simp [hshell_not, hbig, hsmall]
      · have hbig : x ∈ Set.Icc (-R) R := by
          simpa [Set.mem_Icc, abs_le] using hRabs
        have hsmall_not : x ∉ Set.Icc (-r) r := by
          simpa [Set.mem_Icc, abs_le] using hrabs
        have hshell : x ∈ {x : ℝ | r < |x| ∧ |x| ≤ R} := by
          simp [lt_of_not_ge hrabs, hRabs]
        simp [hshell, hbig, hsmall_not]
    · have hbig_not : x ∉ Set.Icc (-R) R := by
        simpa [Set.mem_Icc, abs_le] using hRabs
      have hsmall_not : x ∉ Set.Icc (-r) r := by
        intro hsmall
        apply hRabs
        exact le_trans (by simpa [Set.mem_Icc, abs_le] using hsmall) hR
      have hshell_not : x ∉ {x : ℝ | r < |x| ∧ |x| ≤ R} := by
        simp [hRabs]
      simp [hshell_not, hbig_not, hsmall_not]
  rw [hshell]
  -- Proof comment: once the shell is rewritten as a difference of nested truncations, the exact
  -- logarithmic formulas subtract directly.
  have hbig :
      ∫ x, Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x
          ∂symmetricParetoMeasure (1 / 2) = 2 * Real.log R := by
    calc
      ∫ x, Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x
          ∂symmetricParetoMeasure (1 / 2)
          = ∫ x in Set.Icc (-R) R, x ^ (2 : ℕ) ∂symmetricParetoMeasure (1 / 2) := by
              simpa using
                (integral_indicator
                  (μ := symmetricParetoMeasure (1 / 2))
                  (f := fun x : ℝ ↦ x ^ (2 : ℕ))
                  measurableSet_Icc)
      _ = 2 * Real.log R := inverseCubeTail_truncatedSecondMoment R hR_ge_one
  have hsmall :
      ∫ x, Set.indicator (Set.Icc (-r) r) (fun x : ℝ ↦ x ^ (2 : ℕ)) x
          ∂symmetricParetoMeasure (1 / 2) = 2 * Real.log r := by
    calc
      ∫ x, Set.indicator (Set.Icc (-r) r) (fun x : ℝ ↦ x ^ (2 : ℕ)) x
          ∂symmetricParetoMeasure (1 / 2)
          = ∫ x in Set.Icc (-r) r, x ^ (2 : ℕ) ∂symmetricParetoMeasure (1 / 2) := by
              simpa using
                (integral_indicator
                  (μ := symmetricParetoMeasure (1 / 2))
                  (f := fun x : ℝ ↦ x ^ (2 : ℕ))
                  measurableSet_Icc)
      _ = 2 * Real.log r := inverseCubeTail_truncatedSecondMoment r hr
  rw [integral_sub
    (integrable_inverseCubeTail_truncatedSquare R)
    (integrable_inverseCubeTail_truncatedSquare r),
    hbig, hsmall]
  ring

/-- A random variable with law `symmetricParetoMeasure (1 / 2)`, equivalently with density
`x ↦ |x|⁻³ 1_{ℝ \ [-1,1]}(x)`, has infinite second moment. -/
theorem secondMoment_eq_top_of_hasLaw_inverseCubeTail {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasLaw X (symmetricParetoMeasure (1 / 2)) P) :
    ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 : ℕ)) ∂P = ⊤ := by
  by_contra hfinite
  let M : ℝ := (∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 : ℕ)) ∂P).toReal
  have htrunc_eq (R : ℝ) (hR : 1 ≤ R) :
      ∫⁻ ω,
          ENNReal.ofReal
            (Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) (X ω)) ∂P =
        ENNReal.ofReal (2 * Real.log R) := by
    have hmeas :
        AEMeasurable
          (fun x : ℝ ↦
            ENNReal.ofReal (Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x))
          (symmetricParetoMeasure (1 / 2)) := by
      exact
        (((measurable_id.pow_const 2).indicator measurableSet_Icc).ennreal_ofReal).aemeasurable
    have hnonneg :
        0 ≤ᵐ[symmetricParetoMeasure (1 / 2)]
          fun x : ℝ ↦ Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x := by
      exact Filter.Eventually.of_forall fun x ↦ by
        by_cases hx : x ∈ Set.Icc (-R) R <;> simp [hx, sq_nonneg]
    -- Proof comment: first transport the truncated square through the law of `X`, then collapse
    -- the `ENNReal` truncation integral back to the explicit real integral.
    calc
      ∫⁻ ω,
          ENNReal.ofReal
            (Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) (X ω)) ∂P
          = ∫⁻ x,
              ENNReal.ofReal
                (Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x)
              ∂symmetricParetoMeasure (1 / 2) := by
                exact hX.lintegral_comp hmeas
      _ =
          ENNReal.ofReal
            (∫ x, Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x
              ∂symmetricParetoMeasure (1 / 2)) := by
              rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                (integrable_inverseCubeTail_truncatedSquare R) hnonneg]
      _ = ENNReal.ofReal (2 * Real.log R) := by
            have hbase :
                ∫ x, Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x
                    ∂symmetricParetoMeasure (1 / 2) = 2 * Real.log R := by
              calc
                ∫ x, Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) x
                    ∂symmetricParetoMeasure (1 / 2)
                    = ∫ x in Set.Icc (-R) R, x ^ (2 : ℕ) ∂symmetricParetoMeasure (1 / 2) := by
                        simpa using
                          (integral_indicator
                            (μ := symmetricParetoMeasure (1 / 2))
                            (f := fun x : ℝ ↦ x ^ (2 : ℕ))
                            measurableSet_Icc)
                _ = 2 * Real.log R := inverseCubeTail_truncatedSecondMoment R hR
            rw [hbase]
  have hlower (R : ℝ) (hR : 1 ≤ R) :
      ENNReal.ofReal (2 * Real.log R) ≤
        ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 : ℕ)) ∂P := by
    calc
      ENNReal.ofReal (2 * Real.log R)
          = ∫⁻ ω,
              ENNReal.ofReal
                (Set.indicator (Set.Icc (-R) R) (fun x : ℝ ↦ x ^ (2 : ℕ)) (X ω)) ∂P := by
                  rw [htrunc_eq R hR]
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 : ℕ)) ∂P := by
            refine lintegral_mono_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
            by_cases hx : X ω ∈ Set.Icc (-R) R
            · simp [hx, sq_nonneg]
            · simp [hx, sq_nonneg]
  have hbound (R : ℝ) (hR : 1 ≤ R) : 2 * Real.log R ≤ M := by
    exact (ENNReal.ofReal_le_iff_le_toReal hfinite).1 (hlower R hR)
  let R : ℝ := Real.exp (M + 1)
  have hR : 1 ≤ R := by
    have hR_lt : (1 : ℝ) < R := by
      dsimp [R, M]
      have hpos : 0 < (∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 : ℕ)) ∂P).toReal + 1 := by positivity
      simpa [Real.exp_zero] using Real.exp_lt_exp.mpr hpos
    linarith
  have hcontra : 2 * (M + 1) ≤ M := by
    simpa [R, M, Real.log_exp] using hbound R hR
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  linarith

/-- Helper for Exercise 15.5.3: replace each coordinate by a measurable representative without
changing its law. -/
private def inverseCubeTailCoordinateRepresentative
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    (n : ℕ) : Ω → ℝ :=
  (hX_law n).aemeasurable.mk (X (n + 1))

/-- Helper for Exercise 15.5.3: the measurable representative really is measurable. -/
private lemma measurable_inverseCubeTailCoordinateRepresentative
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    (n : ℕ) :
    Measurable (inverseCubeTailCoordinateRepresentative P X hX_law n) := by
  -- Proof comment: this is the canonical measurable representative attached to the a.e.-measurable
  -- coordinate from `HasLaw`.
  dsimp [inverseCubeTailCoordinateRepresentative]
  exact (hX_law n).aemeasurable.measurable_mk

/-- Helper for Exercise 15.5.3: the measurable representative agrees almost everywhere with the
original coordinate. -/
private lemma ae_eq_inverseCubeTailCoordinateRepresentative
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    (n : ℕ) :
    inverseCubeTailCoordinateRepresentative P X hX_law n =ᵐ[P] X (n + 1) := by
  -- Proof comment: `AEMeasurable.mk` is constructed precisely to be an a.e.-equal measurable
  -- version of the original coordinate.
  dsimp [inverseCubeTailCoordinateRepresentative]
  exact ((hX_law n).aemeasurable.ae_eq_mk).symm

/-- Helper for Exercise 15.5.3: the measurable representative still has the inverse-cube-tail
law. -/
private lemma hasLaw_inverseCubeTailCoordinateRepresentative
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    (n : ℕ) :
    HasLaw (inverseCubeTailCoordinateRepresentative P X hX_law n)
      (symmetricParetoMeasure (1 / 2)) P := by
  refine
    ⟨(measurable_inverseCubeTailCoordinateRepresentative P X hX_law n).aemeasurable, ?_⟩
  -- Proof comment: map the measurable representative and then rewrite back to the original
  -- coordinate through the a.e.-equality.
  calc
    Measure.map (inverseCubeTailCoordinateRepresentative P X hX_law n) P
        = Measure.map (X (n + 1)) P := by
            exact
              Measure.map_congr
                (ae_eq_inverseCubeTailCoordinateRepresentative P X hX_law n)
    _ = symmetricParetoMeasure (1 / 2) := (hX_law n).map_eq

/-- Helper for Exercise 15.5.3: the `n`-th row of the shifted truncated array has length
`n + 1`, cutoff `A_{n+1}`, and variance scale `B_{n+1}`. -/
private def inverseCubeTailTruncatedShiftedArray
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P) :
    RealRandomVariableArray Ω where
  rowLength n := n + 1
  entry n i ω :=
    (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
      Set.indicator
        {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
        (fun x ↦ x)
        (inverseCubeTailCoordinateRepresentative P X hX_law i.1 ω)
  measurable_entry n i :=
    measurable_const.mul <|
      ((measurable_id.indicator <|
        measurableSet_le measurable_abs measurable_const).comp
        (measurable_inverseCubeTailCoordinateRepresentative P X hX_law i.1))

/-- Helper for Exercise 15.5.3: the shifted truncated array entry is exactly the truncated
coordinate divided by `B_{n+1}`. -/
private theorem inverseCubeTailTruncatedShiftedArray_apply
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    (n : ℕ) (i : Fin (n + 1)) (ω : Ω) :
    inverseCubeTailTruncatedShiftedArray P X hX_law n i ω =
      (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
        Set.indicator
          {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
          (fun x ↦ x)
          (inverseCubeTailCoordinateRepresentative P X hX_law i.1 ω) := rfl

/-- Helper for Exercise 15.5.3: the shifted truncated row sum is the `range (n + 1)` sum of the
truncated measurable representatives. -/
private theorem inverseCubeTailTruncatedShiftedArray_rowSum_eq
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    (n : ℕ) (ω : Ω) :
    (inverseCubeTailTruncatedShiftedArray P X hX_law).rowSum n ω =
      (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
        ∑ k ∈ Finset.range (n + 1),
          Set.indicator
            {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
            (fun x ↦ x)
            (inverseCubeTailCoordinateRepresentative P X hX_law k ω) := by
  -- Proof comment: unfold the owner row sum, rewrite the `Fin (n + 1)` sum as a `range (n + 1)`
  -- sum, and then factor out the rowwise constant `B_{n+1}^{-1}`.
  have hsum :
      ∑ i : Fin (n + 1),
        (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
          Set.indicator
            {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
            (fun x ↦ x)
            (inverseCubeTailCoordinateRepresentative P X hX_law i.1 ω) =
        ∑ k ∈ Finset.range (n + 1),
          (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
            Set.indicator
              {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
              (fun x ↦ x)
              (inverseCubeTailCoordinateRepresentative P X hX_law k ω) := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (fun k : ℕ ↦
          (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
            Set.indicator
              {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
              (fun x ↦ x)
              (inverseCubeTailCoordinateRepresentative P X hX_law k ω))
        (n + 1))
  calc
    (inverseCubeTailTruncatedShiftedArray P X hX_law).rowSum n ω
        =
          ∑ i : Fin (n + 1),
            (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
              Set.indicator
                {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
                (fun x ↦ x)
                (inverseCubeTailCoordinateRepresentative P X hX_law i.1 ω) := by
            rw [RealRandomVariableArray.rowSum]
            simp [inverseCubeTailTruncatedShiftedArray]
            rfl
    _ =
        ∑ k ∈ Finset.range (n + 1),
          (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
            Set.indicator
              {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
              (fun x ↦ x)
              (inverseCubeTailCoordinateRepresentative P X hX_law k ω) := hsum
    _ =
        (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
          ∑ k ∈ Finset.range (n + 1),
            Set.indicator
              {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
              (fun x ↦ x)
              (inverseCubeTailCoordinateRepresentative P X hX_law k ω) := by
            rw [← Finset.mul_sum]

/-- Helper for Exercise 15.5.3: summing the truncated measurable representatives is almost
everywhere the same as summing the original truncated coordinates. -/
private theorem inverseCubeTailTruncatedShiftedArray_sum_ae_eq
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    (n : ℕ) :
    (fun ω ↦
      ∑ k ∈ Finset.range (n + 1),
        Set.indicator
          {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
          (fun x ↦ x)
          (inverseCubeTailCoordinateRepresentative P X hX_law k ω)) =ᵐ[P]
      (fun ω ↦
        ∑ k ∈ Finset.range (n + 1),
          Set.indicator
            {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
            (fun x ↦ x)
            (X (k + 1) ω)) := by
  let repTerm : ℕ → Ω → ℝ := fun k ω ↦
    Set.indicator
      {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
      (fun x ↦ x)
      (inverseCubeTailCoordinateRepresentative P X hX_law k ω)
  let rawTerm : ℕ → Ω → ℝ := fun k ω ↦
    Set.indicator
      {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
      (fun x ↦ x)
      (X (k + 1) ω)
  have hsum :
      ∀ m : ℕ,
        (fun ω ↦ ∑ k ∈ Finset.range m, repTerm k ω) =ᵐ[P]
          (fun ω ↦ ∑ k ∈ Finset.range m, rawTerm k ω) := by
    intro m
    induction m with
    | zero =>
        simp [repTerm, rawTerm]
    | succ m hm =>
        have htail : repTerm m =ᵐ[P] rawTerm m := by
          -- Proof comment: truncate after replacing the coordinate by its measurable
          -- representative; the truncation respects the a.e.-equality.
          filter_upwards [ae_eq_inverseCubeTailCoordinateRepresentative P X hX_law m] with ω hω
          simp [repTerm, rawTerm, hω]
        simpa [Finset.sum_range_succ, repTerm, rawTerm] using hm.add htail
  exact hsum (n + 1)

/-- Helper for Exercise 15.5.3: the shifted truncated row sum agrees almost everywhere with the
truncated normalized partial sum built from the original coordinates. -/
private theorem inverseCubeTailTruncatedShiftedArray_rowSum_ae_eq
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    (n : ℕ) :
    (inverseCubeTailTruncatedShiftedArray P X hX_law).rowSum n =ᵐ[P]
      (fun ω ↦
        (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
          ∑ k ∈ Finset.range (n + 1),
            Set.indicator
              {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
              (fun x ↦ x)
              (X (k + 1) ω)) := by
  -- Proof comment: first rewrite the owner row sum in terms of the measurable representatives,
  -- then replace those representatives by the original coordinates almost everywhere.
  filter_upwards [inverseCubeTailTruncatedShiftedArray_sum_ae_eq P X hX_law n] with ω hω
  rw [inverseCubeTailTruncatedShiftedArray_rowSum_eq]
  simp [hω]

/-- Helper for Exercise 15.5.3: the bounded odd truncation is integrable under the one-sided
shape-`2` Pareto law. -/
private lemma integrable_paretoShapeTwo_truncatedIdentity (R : ℝ) :
    Integrable
      (Set.indicator {x : ℝ | |x| ≤ R} (fun x ↦ x))
      (paretoMeasure 1 2) := by
  letI : IsProbabilityMeasure (paretoMeasure 1 2) :=
    isProbabilityMeasure_paretoMeasure zero_lt_one zero_lt_two
  have hmeas :
      Measurable (Set.indicator {x : ℝ | |x| ≤ R} (fun x : ℝ ↦ x)) := by
    exact measurable_id.indicator (measurableSet_le measurable_abs measurable_const)
  -- Proof comment: the truncation is bounded in absolute value by the deterministic cutoff `|R|`.
  refine Integrable.of_bound hmeas.aestronglyMeasurable |R| ?_
  filter_upwards with x
  by_cases hx : |x| ≤ R
  · have hR_nonneg : 0 ≤ R := le_trans (abs_nonneg x) hx
    simp [hx, abs_of_nonneg hR_nonneg]
  · simp [hx]

/-- Helper for Exercise 15.5.3: the bounded odd truncation is integrable under the symmetric
inverse-cube-tail law. -/
private lemma integrable_inverseCubeTail_truncatedIdentity (R : ℝ) :
    Integrable
      (Set.indicator {x : ℝ | |x| ≤ R} (fun x : ℝ ↦ x))
      (symmetricParetoMeasure (1 / 2)) := by
  letI : IsProbabilityMeasure (symmetricParetoMeasure (1 / 2)) :=
    isProbabilityMeasure_inverseCubeTailMeasure
  have hmeas :
      Measurable (Set.indicator {x : ℝ | |x| ≤ R} (fun x : ℝ ↦ x)) := by
    exact measurable_id.indicator (measurableSet_le measurable_abs measurable_const)
  -- Proof comment: the same bounded-support estimate works for the symmetric law because it is a
  -- probability measure.
  refine Integrable.of_bound hmeas.aestronglyMeasurable |R| ?_
  filter_upwards with x
  by_cases hx : |x| ≤ R
  · have hR_nonneg : 0 ≤ R := le_trans (abs_nonneg x) hx
    simp [hx, abs_of_nonneg hR_nonneg]
  · simp [hx]

/-- Helper for Exercise 15.5.3: the symmetric inverse-cube-tail law kills the bounded odd
truncation because the law is invariant under reflection. -/
private lemma inverseCubeTail_truncatedMean_zero (B R : ℝ) :
    ∫ x, B⁻¹ *
        Set.indicator {x : ℝ | |x| ≤ R} (fun x : ℝ ↦ x) x
      ∂symmetricParetoMeasure (1 / 2) = 0 := by
  let μ : Measure ℝ := paretoMeasure 1 2
  let g : ℝ → ℝ := fun x ↦ B⁻¹ * Set.indicator {x : ℝ | |x| ≤ R} (fun x ↦ x) x
  have hg_int : Integrable g μ := by
    simpa [g] using (integrable_paretoShapeTwo_truncatedIdentity R).const_mul B⁻¹
  have hg_comp : Integrable (g ∘ fun x : ℝ ↦ -x) μ := by
    have hodd : (g ∘ fun x : ℝ ↦ -x) = (fun x : ℝ ↦ -(g x)) := by
      funext x
      by_cases hx : |x| ≤ R
      · simp [g, hx, abs_neg, mul_comm, mul_left_comm, mul_assoc]
      · simp [g, hx, abs_neg, mul_comm, mul_left_comm, mul_assoc]
    rw [hodd]
    exact hg_int.neg
  have hg_map_int : Integrable g (μ.map (fun x : ℝ ↦ -x)) := by
    exact (integrable_map_equiv (μ := μ) (MeasurableEquiv.neg ℝ) g).2 hg_comp
  have hg_map :
      ∫ x, g x ∂μ.map (fun x : ℝ ↦ -x) = -∫ x, g x ∂μ := by
    calc
      ∫ x, g x ∂μ.map (fun x : ℝ ↦ -x) = ∫ x, g (-x) ∂μ := by
            simpa [μ, g] using (integral_map_equiv (μ := μ) (MeasurableEquiv.neg ℝ) g)
      _ = ∫ x, -(g x) ∂μ := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
            by_cases hx : |x| ≤ R
            · simp [g, hx, abs_neg, mul_comm, mul_left_comm, mul_assoc]
            · simp [g, hx, abs_neg, mul_comm, mul_left_comm, mul_assoc]
      _ = -∫ x, g x ∂μ := by rw [integral_neg]
  -- Proof comment: rewrite the symmetric law as the average of the one-sided Pareto law and its
  -- reflection, then cancel the two odd contributions.
  calc
    ∫ x, B⁻¹ * Set.indicator {x : ℝ | |x| ≤ R} (fun x : ℝ ↦ x) x
        ∂symmetricParetoMeasure (1 / 2)
        = ∫ x, g x ∂symmetricParetoMeasure (1 / 2) := by
            rfl
    _ = ∫ x, g x ∂((1 / 2 : ENNReal) • μ + (1 / 2 : ENNReal) • μ.map (fun x : ℝ ↦ -x)) := by
          rw [inverseCubeTailMeasure_eq_symmetrized_paretoMeasure]
    _ = ∫ x, g x ∂((1 / 2 : ENNReal) • μ) + ∫ x, g x ∂((1 / 2 : ENNReal) • μ.map (fun x ↦ -x)) := by
          exact integral_add_measure
            (hg_int.smul_measure (by simp : (1 / 2 : ENNReal) ≠ ∞))
            (hg_map_int.smul_measure (by simp : (1 / 2 : ENNReal) ≠ ∞))
    _ = (1 / 2 : ℝ) * ∫ x, g x ∂μ + (1 / 2 : ℝ) * ∫ x, g x ∂μ.map (fun x ↦ -x) := by
          rw [integral_smul_measure, integral_smul_measure]
          simp
    _ = (1 / 2 : ℝ) * ∫ x, g x ∂μ + (1 / 2 : ℝ) * (-(∫ x, g x ∂μ)) := by
          rw [hg_map]
    _ = 0 := by ring

/-- Helper for Exercise 15.5.3: each shifted truncated array entry is the inverse-cube-tail law
pushed forward by the textbook truncation-and-scale map. -/
private lemma hasLaw_inverseCubeTailTruncatedShiftedArray_entry
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    (n : ℕ) (i : Fin (n + 1)) :
    HasLaw
      ((inverseCubeTailTruncatedShiftedArray P X hX_law) n i)
      ((symmetricParetoMeasure (1 / 2)).map
        (fun x ↦
          (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
            Set.indicator
              {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
              (fun x ↦ x) x))
      P := by
  let g : ℝ → ℝ := fun x ↦
    (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
      Set.indicator
        {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
        (fun x ↦ x) x
  have hg_law : HasLaw g ((symmetricParetoMeasure (1 / 2)).map g) (symmetricParetoMeasure (1 / 2)) :=
    ⟨(measurable_const.mul
        (measurable_id.indicator (measurableSet_le measurable_abs measurable_const))).aemeasurable,
      rfl⟩
  -- Proof comment: compose the measurable representative law with the deterministic truncation map.
  simpa [g, inverseCubeTailTruncatedShiftedArray_apply, Function.comp] using
    hg_law.fun_comp (hasLaw_inverseCubeTailCoordinateRepresentative P X hX_law i.1)

/-- Helper for Exercise 15.5.3: squaring the truncation-and-scale map produces the deterministic
factor `B⁻²` times the truncated square kernel on `[-R, R]`. -/
private lemma scaledTruncationSquare_eq_truncatedSquare
    (B R x : ℝ) :
    (B⁻¹ *
        Set.indicator {y : ℝ | |y| ≤ R} (fun y ↦ y) x) ^ (2 : ℕ) =
      (B⁻¹) ^ (2 : ℕ) *
        Set.indicator (Set.Icc (-R) R) (fun y : ℝ ↦ y ^ (2 : ℕ)) x := by
  -- Proof comment: on the truncation set we keep `x` and square the scalar factor; off the set,
  -- both sides vanish.
  by_cases hx : |x| ≤ R
  · have hxIcc : x ∈ Set.Icc (-R) R := by
      simpa [Set.mem_Icc, abs_le] using hx
    simp [hx, hxIcc]
    ring
  · have hxIcc : x ∉ Set.Icc (-R) R := by
      simpa [Set.mem_Icc, abs_le] using hx
    simp [hx, hxIcc]

/-- Helper for Exercise 15.5.3: the tail-truncated square of the scaled truncation map is exactly
the shell square kernel between `ε B` and `R`. -/
private lemma scaledTruncationTailSquare_eq_shell
    {ε B R : ℝ} (hB : 0 < B) (x : ℝ) :
    Set.indicator
        {y : ℝ |
          ε <
            |B⁻¹ *
              Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) y|}
        (fun y : ℝ ↦
          (B⁻¹ *
            Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) y) ^ (2 : ℕ))
        x =
      (B⁻¹) ^ (2 : ℕ) *
        Set.indicator
          {y : ℝ | ε * B < |y| ∧ |y| ≤ R}
          (fun y : ℝ ↦ y ^ (2 : ℕ))
          x := by
  -- Proof comment: split according to whether the truncation keeps `x`. Outside `[-R, R]` the
  -- truncation map is zero, while on the support the tail event is exactly `ε * B < |x|`.
  by_cases hx : |x| ≤ R
  · have habs :
        |B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x| = |x| / B := by
      calc
        |B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x|
            = |B⁻¹ * x| := by simp [hx]
        _ = |B⁻¹| * |x| := by rw [abs_mul]
        _ = B⁻¹ * |x| := by simp [abs_inv, abs_of_pos hB]
        _ = |x| / B := by rw [div_eq_mul_inv, mul_comm]
    have htail :
        ε <
            |B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x| ↔
          ε * B < |x| := by
      rw [habs]
      exact (lt_div_iff₀ hB)
    have hsq :
        (B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x) ^ (2 : ℕ) =
          (B⁻¹) ^ (2 : ℕ) * x ^ (2 : ℕ) := by
      simp [hx]
      ring
    by_cases hcut : ε * B < |x|
    · -- Proof comment: on the nonempty shell both indicators are active, so only the scalar
      -- factorization of the square remains.
      have hleft :
          ε <
            |B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x| := htail.2 hcut
      have hright :
          x ∈ {y : ℝ | ε * B < |y| ∧ |y| ≤ R} := ⟨hcut, hx⟩
      calc
        Set.indicator
            {y : ℝ |
              ε <
                |B⁻¹ *
                  Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) y|}
            (fun y : ℝ ↦
              (B⁻¹ *
                Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) y) ^ (2 : ℕ))
            x
            =
              (B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x) ^ (2 : ℕ) := by
                change
                  (if ε < |B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x| then
                      (B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x) ^ (2 : ℕ)
                    else 0) =
                    (B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x) ^ (2 : ℕ)
                rw [if_pos hleft]
        _ = (B⁻¹) ^ (2 : ℕ) * x ^ (2 : ℕ) := hsq
        _ =
            (B⁻¹) ^ (2 : ℕ) *
              Set.indicator
                {y : ℝ | ε * B < |y| ∧ |y| ≤ R}
                (fun y : ℝ ↦ y ^ (2 : ℕ))
                x := by
                  rw [Set.indicator_of_mem hright]
    · -- Proof comment: if `x` lies below the shell cutoff, both indicators vanish.
      have hleft :
          ¬ ε <
            |B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x| := by
        intro hx_tail
        exact hcut (htail.1 hx_tail)
      have hright :
          x ∉ {y : ℝ | ε * B < |y| ∧ |y| ≤ R} := by
        intro hx_shell
        exact hcut hx_shell.1
      calc
        Set.indicator
            {y : ℝ |
              ε <
                |B⁻¹ *
                  Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) y|}
            (fun y : ℝ ↦
              (B⁻¹ *
                Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) y) ^ (2 : ℕ))
            x = 0 := by
              change
                (if ε < |B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x| then
                    (B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x) ^ (2 : ℕ)
                  else 0) = 0
              rw [if_neg hleft]
        _ =
            (B⁻¹) ^ (2 : ℕ) *
              Set.indicator
                {y : ℝ | ε * B < |y| ∧ |y| ≤ R}
                (fun y : ℝ ↦ y ^ (2 : ℕ))
                x := by
                  simp [Set.indicator, hright]
  · -- Proof comment: outside the truncation support the scaled truncation is identically `0`.
    simp [hx]

/-- Helper for Exercise 15.5.3: every entry of the shifted truncated array is bounded by the
deterministic ratio `A_{n+1} / B_{n+1}`. -/
private lemma inverseCubeTailTruncatedShiftedArray_entry_abs_le
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    (n : ℕ) (i : Fin (n + 1)) (ω : Ω) :
    |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω| ≤
      inverseCubeTailCLTNormingSequence (n + 1) /
        inverseCubeTailTruncationVarianceScale (n + 1) := by
  -- Proof comment: the truncation keeps the representative only inside `[-A_{n+1}, A_{n+1}]`,
  -- so after scaling by `B_{n+1}^{-1}` the entry is bounded by `A_{n+1} / B_{n+1}`.
  let B := inverseCubeTailTruncationVarianceScale (n + 1)
  let R := inverseCubeTailCLTNormingSequence (n + 1)
  let x := inverseCubeTailCoordinateRepresentative P X hX_law i.1 ω
  have hB_pos : 0 < B := by
    simpa [B] using inverseCubeTailTruncationVarianceScale_pos n
  have hR_nonneg : 0 ≤ R := by
    exact le_of_lt (inverseCubeTailCLTNormingSequence_pos (n + 1))
  by_cases hx : |x| ≤ R
  · calc
      |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω|
          = B⁻¹ * |x| := by
              simp [inverseCubeTailTruncatedShiftedArray_apply, B, R, x, hx, abs_mul, abs_inv,
                abs_of_pos hB_pos]
      _ ≤ B⁻¹ * R := by
            gcongr
      _ = R / B := by
            rw [div_eq_mul_inv, mul_comm]
  · calc
      |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω| = 0 := by
            simp [inverseCubeTailTruncatedShiftedArray_apply, B, R, x, hx]
      _ ≤ R / B := by
            have : 0 ≤ R / B := by positivity
            exact this

/-- Helper for Exercise 15.5.3: the measurable representatives preserve the rowwise independence
of the inverse-cube-tail coordinates after truncation and scaling. -/
private theorem inverseCubeTailTruncatedShiftedArray_isIndependent
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P) :
    RealRandomVariableArray.IsIndependent (inverseCubeTailTruncatedShiftedArray P X hX_law) P := by
  refine ⟨fun n ↦ ?_⟩
  have hrep_indep :
      iIndepFun (inverseCubeTailCoordinateRepresentative P X hX_law) P := by
    -- Proof comment: coordinatewise a.e.-equal measurable representatives preserve independence.
    exact hX_indep.congr (fun k ↦ (ae_eq_inverseCubeTailCoordinateRepresentative P X hX_law k).symm)
  let hrow : iIndepFun (fun i : Fin (n + 1) ↦ inverseCubeTailCoordinateRepresentative P X hX_law i.1) P :=
    hrep_indep.precomp Fin.val_injective
  let g : Fin (n + 1) → ℝ → ℝ := fun _ x ↦
    (inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
      Set.indicator
        {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
        (fun x ↦ x) x
  have hg : ∀ i, Measurable (g i) := by
    intro i
    exact measurable_const.mul
      (measurable_id.indicator (measurableSet_le measurable_abs measurable_const))
  -- Proof comment: each row is a measurable coordinatewise transform of an independent finite
  -- family.
  simpa [g, inverseCubeTailTruncatedShiftedArray_apply] using hrow.comp g hg

/-- Helper for Exercise 15.5.3: the shifted truncated array is centered because each truncated
entry keeps the odd inverse-cube-tail law and the symmetric truncation has mean `0`. -/
private lemma inverseCubeTailTruncatedShiftedArray_isCentered
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P) :
    (inverseCubeTailTruncatedShiftedArray P X hX_law).IsCentered P := by
  refine ⟨fun n i ↦ ?_⟩
  let A := inverseCubeTailTruncatedShiftedArray P X hX_law
  let B := inverseCubeTailTruncationVarianceScale (n + 1)
  let R := inverseCubeTailCLTNormingSequence (n + 1)
  let g : ℝ → ℝ := fun x ↦
    B⁻¹ * Set.indicator {x : ℝ | |x| ≤ R} (fun x ↦ x) x
  have hg_law : HasLaw g ((symmetricParetoMeasure (1 / 2)).map g) (symmetricParetoMeasure (1 / 2)) :=
    ⟨(measurable_const.mul
        (measurable_id.indicator (measurableSet_le measurable_abs measurable_const))).aemeasurable,
      rfl⟩
  have hIntegrable : Integrable (A n i) P := by
    -- Proof comment: every array entry is uniformly bounded by the deterministic ratio
    -- `A_{n+1} / B_{n+1}`, and probability spaces turn such bounds into integrability.
    refine Integrable.of_bound (A.measurable_entry n i).aestronglyMeasurable (R / B) ?_
    filter_upwards with ω
    simpa [A, B, R, Real.norm_eq_abs] using
      inverseCubeTailTruncatedShiftedArray_entry_abs_le P X hX_law n i ω
  have hMeanZero : P[A n i] = 0 := by
    -- Proof comment: transport the truncated entry law to the canonical truncation map under the
    -- inverse-cube-tail measure, then use the oddness-based mean-zero formula there.
    calc
      P[A n i] = ∫ x, x ∂((symmetricParetoMeasure (1 / 2)).map g) := by
        simpa [A, B, R, g] using
          (hasLaw_inverseCubeTailTruncatedShiftedArray_entry P X hX_law n i).integral_eq
      _ = ∫ x, g x ∂symmetricParetoMeasure (1 / 2) := by
        simpa [g] using hg_law.integral_eq.symm
      _ = 0 := by
        simpa [g, B, R] using inverseCubeTail_truncatedMean_zero B R
  exact ⟨hIntegrable, hMeanZero⟩

/-- Helper for Exercise 15.5.3: every row of the shifted truncated array has total variance `1`,
so this is the normed array used in the CLT package. -/
private lemma inverseCubeTailTruncatedShiftedArray_isNormed
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P) :
    (inverseCubeTailTruncatedShiftedArray P X hX_law).IsNormed P := by
  let A := inverseCubeTailTruncatedShiftedArray P X hX_law
  have hCentered := inverseCubeTailTruncatedShiftedArray_isCentered P X hX_law
  refine ⟨?_, ?_⟩
  · intro n i
    let B := inverseCubeTailTruncationVarianceScale (n + 1)
    let R := inverseCubeTailCLTNormingSequence (n + 1)
    -- Proof comment: the same deterministic entry bound gives the `L²` control required by the
    -- normed-array interface.
    refine MemLp.of_bound
      (p := (2 : ENNReal))
      (A.measurable_entry n i).aestronglyMeasurable
      (R / B) ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [A, B, R, Real.norm_eq_abs] using
        inverseCubeTailTruncatedShiftedArray_entry_abs_le P X hX_law n i ω
  · intro n
    let B := inverseCubeTailTruncationVarianceScale (n + 1)
    let R := inverseCubeTailCLTNormingSequence (n + 1)
    have hB_pos : 0 < B := by
      simpa [B] using inverseCubeTailTruncationVarianceScale_pos n
    have hB_ne : B ≠ 0 := ne_of_gt hB_pos
    have hR_one : 1 ≤ R := by
      simpa [R] using inverseCubeTailCLTNormingSequence_one_le (n + 1)
    have hlog_pos :
        0 < Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) :=
      inverseCubeTailLogNormalizer_pos n
    have hlog_ne :
        Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) ≠ 0 := hlog_pos.ne'
    have hvar_each : ∀ i : Fin (n + 1), Var[A n i; P] = 1 / (n + 1 : ℝ) := by
      intro i
      let g : ℝ → ℝ := fun x ↦
        B⁻¹ * Set.indicator {x : ℝ | |x| ≤ R} (fun x ↦ x) x
      letI : IsProbabilityMeasure (symmetricParetoMeasure (1 / 2)) :=
        isProbabilityMeasure_inverseCubeTailMeasure
      have hg_meas : Measurable g := by
        exact measurable_const.mul
          (measurable_id.indicator (measurableSet_le measurable_abs measurable_const))
      have hg_law :
          HasLaw g ((symmetricParetoMeasure (1 / 2)).map g) (symmetricParetoMeasure (1 / 2)) :=
        ⟨hg_meas.aemeasurable, rfl⟩
      letI : IsProbabilityMeasure ((symmetricParetoMeasure (1 / 2)).map g) :=
        Measure.isProbabilityMeasure_map hg_meas.aemeasurable
      have hMeanMap :
          ∫ x, x ∂((symmetricParetoMeasure (1 / 2)).map g) = 0 := by
        -- Proof comment: the mapped identity integral is exactly the truncated odd integral,
        -- which vanishes under the symmetric inverse-cube-tail law.
        calc
          ∫ x, x ∂((symmetricParetoMeasure (1 / 2)).map g)
              = ∫ x, g x ∂symmetricParetoMeasure (1 / 2) := by
                  simpa [g] using hg_law.integral_eq.symm
          _ = 0 := by
                simpa [g, B, R] using inverseCubeTail_truncatedMean_zero B R
      have hSecondMomentMap :
          ∫ x, x ^ (2 : ℕ) ∂((symmetricParetoMeasure (1 / 2)).map g) =
            (B⁻¹) ^ (2 : ℕ) * (2 * Real.log R) := by
        -- Proof comment: transport the squared entry through the law, normalize the deterministic
        -- factor `B⁻²`, and insert the explicit truncated second moment `2 log R`.
        calc
          ∫ x, x ^ (2 : ℕ) ∂((symmetricParetoMeasure (1 / 2)).map g)
              = ∫ x, (g x) ^ (2 : ℕ) ∂symmetricParetoMeasure (1 / 2) := by
                  simpa [Function.comp, g] using
                    (hg_law.integral_comp
                      ((measurable_id.pow_const 2).aestronglyMeasurable)).symm
          _ = ∫ x,
                (B⁻¹) ^ (2 : ℕ) *
                  Set.indicator (Set.Icc (-R) R) (fun y : ℝ ↦ y ^ (2 : ℕ)) x
                ∂symmetricParetoMeasure (1 / 2) := by
                  refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
                  simpa [g] using scaledTruncationSquare_eq_truncatedSquare B R x
          _ =
              (B⁻¹) ^ (2 : ℕ) *
                ∫ x,
                  Set.indicator (Set.Icc (-R) R) (fun y : ℝ ↦ y ^ (2 : ℕ)) x
                  ∂symmetricParetoMeasure (1 / 2) := by
                    rw [integral_const_mul]
          _ =
              (B⁻¹) ^ (2 : ℕ) *
                ∫ x in Set.Icc (-R) R, x ^ (2 : ℕ) ∂symmetricParetoMeasure (1 / 2) := by
                    rw [integral_indicator measurableSet_Icc]
          _ = (B⁻¹) ^ (2 : ℕ) * (2 * Real.log R) := by
                rw [inverseCubeTail_truncatedSecondMoment R hR_one]
      calc
        Var[A n i; P] = Var[id; ((symmetricParetoMeasure (1 / 2)).map g)] := by
          simpa [A, B, R, g] using
            (hasLaw_inverseCubeTailTruncatedShiftedArray_entry P X hX_law n i).variance_eq
        _ = ∫ x, x ^ (2 : ℕ) ∂((symmetricParetoMeasure (1 / 2)).map g) := by
          change Var[(fun x : ℝ ↦ x); ((symmetricParetoMeasure (1 / 2)).map g)] =
              ∫ x, x ^ (2 : ℕ) ∂((symmetricParetoMeasure (1 / 2)).map g)
          rw [variance_eq_integral measurable_id'.aemeasurable, hMeanMap]
          simp
        _ = (B⁻¹) ^ (2 : ℕ) * (2 * Real.log R) := hSecondMomentMap
        _ = 1 / (n + 1 : ℝ) := by
          have hshift : (((n + 1 : ℕ) : ℝ) + 2) = n + 3 := by
            norm_num [Nat.cast_add, add_assoc]
          have hR_log :
              2 * Real.log R =
                Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) := by
            dsimp [R]
            rw [inverseCubeTailCLTNormingSequence, hshift]
            have hrad_nonneg : 0 ≤ ((n + 3 : ℝ) * Real.log (n + 3 : ℝ)) := by
              have hlog_nonneg : 0 ≤ Real.log (n + 3 : ℝ) := by
                refine le_of_lt <| Real.log_pos ?_
                linarith
              positivity
            rw [Real.log_sqrt hrad_nonneg]
            ring
          have hB_sq :
              B ^ (2 : ℕ) =
                (n + 1 : ℝ) * Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) := by
            dsimp [B]
            rw [inverseCubeTailTruncationVarianceScale, hshift, sq]
            have hrad_nonneg :
                0 ≤ (n + 1 : ℝ) *
                  Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) := by
              have hlog_nonneg :
                  0 ≤ Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) := le_of_lt hlog_pos
              positivity
            simpa [pow_two] using (Real.sq_sqrt hrad_nonneg)
          have hrow_ne : (n + 1 : ℝ) ≠ 0 := by positivity
          rw [hR_log, inv_pow, hB_sq]
          field_simp [hrow_ne, hlog_ne]
    -- Proof comment: once each row entry has variance `1 / (n + 1)`, summing over `Fin (n + 1)`
    -- gives the required rowwise normalization.
    calc
      ∑ i : Fin (A.rowLength n), Var[A n i; P]
          = ∑ i : Fin (n + 1), 1 / (n + 1 : ℝ) := by
              refine Finset.sum_congr rfl fun i _ ↦ hvar_each i
    _ = 1 := by
            have hrow_ne : (n + 1 : ℝ) ≠ 0 := by positivity
            simp [hrow_ne, div_eq_mul_inv]

/-- Helper for Exercise 15.5.3: if the Lindeberg cutoff `ε B_{n+1}` lies above the truncation
cutoff `A_{n+1}`, then the whole rowwise truncated-second-moment sum vanishes. -/
private lemma inverseCubeTailTruncatedShiftedArray_rowTruncatedSecondMoment_eq_zero_of_cutoff
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (hcutoff :
      inverseCubeTailCLTNormingSequence (n + 1) <
        ε * inverseCubeTailTruncationVarianceScale (n + 1)) :
    ∑ i : Fin ((inverseCubeTailTruncatedShiftedArray P X hX_law).rowLength n),
        ∫ ω,
          Set.indicator
            {ω | ε < |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω|}
            (fun ω ↦ ((inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω) ^ (2 : ℕ))
            ω
          ∂P = 0 := by
  -- Proof comment: once `A_{n+1} / B_{n+1} < ε`, every row entry is uniformly below the
  -- Lindeberg cutoff, so each truncated second-moment integral vanishes.
  have hB_pos :
      0 < inverseCubeTailTruncationVarianceScale (n + 1) :=
    inverseCubeTailTruncationVarianceScale_pos n
  have hbound_lt :
      inverseCubeTailCLTNormingSequence (n + 1) /
          inverseCubeTailTruncationVarianceScale (n + 1) < ε := by
    rw [div_lt_iff₀ hB_pos]
    simpa [mul_comm] using hcutoff
  have hterm :
      ∀ i : Fin ((inverseCubeTailTruncatedShiftedArray P X hX_law).rowLength n),
        ∫ ω,
          Set.indicator
            {ω | ε < |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω|}
            (fun ω ↦ ((inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω) ^ (2 : ℕ))
            ω
          ∂P = 0 := by
    intro i
    have hpoint :
        ∀ ω, ¬ ε < |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω| := by
      intro ω
      exact not_lt_of_ge
        ((inverseCubeTailTruncatedShiftedArray_entry_abs_le P X hX_law n i ω).trans hbound_lt.le)
    have hzero :
        Set.indicator
            {ω | ε < |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω|}
            (fun ω ↦ ((inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω) ^ (2 : ℕ)) =
          fun _ : Ω ↦ (0 : ℝ) := by
      funext ω
      simp [hpoint ω]
    rw [hzero, integral_zero]
  simp [hterm]

/-- Helper for Exercise 15.5.3: the rowwise truncated second-moment sum of the shifted truncated
array is a constant multiple of one scalar integral under the inverse-cube-tail law. -/
private lemma inverseCubeTailTruncatedShiftedArray_rowTruncatedSecondMoment_eq_scalarIntegral
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    {ε : ℝ} (n : ℕ) :
    ∑ i : Fin ((inverseCubeTailTruncatedShiftedArray P X hX_law).rowLength n),
        ∫ ω,
          Set.indicator
            {ω | ε < |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω|}
            (fun ω ↦ ((inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω) ^ (2 : ℕ))
            ω
          ∂P =
      (n + 1 : ℝ) *
        ∫ x,
          Set.indicator
            {x : ℝ |
              ε <
                |(inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
                  Set.indicator
                    {z : ℝ | |z| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
                    (fun z ↦ z) x|}
            (fun x : ℝ ↦
              ((inverseCubeTailTruncationVarianceScale (n + 1))⁻¹ *
                  Set.indicator
                    {z : ℝ | |z| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
                    (fun z ↦ z) x) ^ (2 : ℕ))
            x
          ∂symmetricParetoMeasure (1 / 2) := by
  let B := inverseCubeTailTruncationVarianceScale (n + 1)
  let R := inverseCubeTailCLTNormingSequence (n + 1)
  let μ : Measure ℝ := symmetricParetoMeasure (1 / 2)
  let g : ℝ → ℝ := fun x ↦
    B⁻¹ * Set.indicator {x : ℝ | |x| ≤ R} (fun x ↦ x) x
  let h : ℝ → ℝ := fun x ↦
    Set.indicator {x : ℝ | ε < |x|} (fun x ↦ x ^ (2 : ℕ)) x
  have hg_meas : Measurable g := by
    exact measurable_const.mul
      (measurable_id.indicator (measurableSet_le measurable_abs measurable_const))
  have hh_meas : Measurable h := by
    exact (measurable_id.pow_const 2).indicator (measurableSet_lt measurable_const measurable_abs)
  have hg_law : HasLaw g (μ.map g) μ := ⟨hg_meas.aemeasurable, rfl⟩
  have hterm :
      ∀ i : Fin (n + 1),
        ∫ ω,
          Set.indicator
            {ω | ε < |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω|}
            (fun ω ↦ ((inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω) ^ (2 : ℕ))
            ω
          ∂P =
          ∫ x, h (g x) ∂μ := by
    intro i
    calc
      ∫ ω,
          Set.indicator
            {ω | ε < |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω|}
            (fun ω ↦ ((inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω) ^ (2 : ℕ))
            ω
          ∂P
          = ∫ x, h x ∂(μ.map g) := by
              simpa [Function.comp, μ, B, R, g, h] using
                (hasLaw_inverseCubeTailTruncatedShiftedArray_entry P X hX_law n i).integral_comp
                  hh_meas.aestronglyMeasurable
      _ = ∫ x, h (g x) ∂μ := by
            simpa [Function.comp, h] using
              (hg_law.integral_comp hh_meas.aestronglyMeasurable).symm
  -- Proof comment: every row entry has the same transported scalar law, so the finite row sum
  -- collapses to `(n + 1)` copies of the same scalar integral.
  change
    ∑ i : Fin (n + 1),
      ∫ ω,
        Set.indicator
          {ω | ε < |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω|}
          (fun ω ↦ ((inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω) ^ (2 : ℕ))
          ω
        ∂P =
      (n + 1 : ℝ) * ∫ x, h (g x) ∂μ
  calc
    ∑ i : Fin (n + 1),
        ∫ ω,
          Set.indicator
            {ω | ε < |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω|}
            (fun ω ↦ ((inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω) ^ (2 : ℕ))
            ω
          ∂P
        = ∑ i : Fin (n + 1), ∫ x, h (g x) ∂μ := by
            refine Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = (n + 1 : ℝ) * ∫ x, h (g x) ∂μ := by
          simp

private lemma inverseCubeTailTruncatedShiftedArray_rowTruncatedSecondMoment_eq_logRatio
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (hcutoff_one :
      1 ≤ ε * inverseCubeTailTruncationVarianceScale (n + 1))
    (hcutoff_le :
      ε * inverseCubeTailTruncationVarianceScale (n + 1) ≤
        inverseCubeTailCLTNormingSequence (n + 1)) :
    ∑ i : Fin ((inverseCubeTailTruncatedShiftedArray P X hX_law).rowLength n),
        ∫ ω,
          Set.indicator
            {ω | ε < |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω|}
            (fun ω ↦ ((inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω) ^ (2 : ℕ))
            ω
          ∂P =
      (2 * Real.log
          (inverseCubeTailCLTNormingSequence (n + 1) /
            (ε * inverseCubeTailTruncationVarianceScale (n + 1)))) *
        (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹ := by
  let B := inverseCubeTailTruncationVarianceScale (n + 1)
  let R := inverseCubeTailCLTNormingSequence (n + 1)
  let L := Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ)))
  let μ : Measure ℝ := symmetricParetoMeasure (1 / 2)
  have hB_pos : 0 < B := by
    simpa [B] using inverseCubeTailTruncationVarianceScale_pos n
  have hR_pos : 0 < R := by
    simpa [R] using inverseCubeTailCLTNormingSequence_pos (n + 1)
  have hεB_pos : 0 < ε * B := by positivity
  have hL_pos : 0 < L := by
    simpa [L] using inverseCubeTailLogNormalizer_pos n
  have hL_ne : L ≠ 0 := hL_pos.ne'
  have hrow_ne : (n + 1 : ℝ) ≠ 0 := by positivity
  have hshift : (((n + 1 : ℕ) : ℝ) + 2) = n + 3 := by
    norm_num [Nat.cast_add, add_assoc]
  have hB_sq :
      B ^ (2 : ℕ) = (n + 1 : ℝ) * L := by
    -- Proof comment: expand the variance scale and square the outer square root once.
    dsimp [B, L]
    rw [inverseCubeTailTruncationVarianceScale, hshift, sq]
    have hrad_nonneg :
        0 ≤
          (n + 1 : ℝ) *
            Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) := by
      have hlog_nonneg : 0 ≤ Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) :=
        le_of_lt (inverseCubeTailLogNormalizer_pos n)
      positivity
    simpa [pow_two] using (Real.sq_sqrt hrad_nonneg)
  have hprefactor :
      (n + 1 : ℝ) * (B⁻¹) ^ (2 : ℕ) = L⁻¹ := by
    -- Proof comment: the row multiplicity `(n + 1)` exactly cancels the variance normalization
    -- hidden inside `B²`.
    rw [inv_pow, hB_sq]
    field_simp [hrow_ne, hL_ne]
  have hshell :
      ∫ x,
          Set.indicator
            {x : ℝ |
              ε <
                |B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x|}
            (fun x : ℝ ↦
              (B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x) ^ (2 : ℕ))
            x
          ∂μ =
        (B⁻¹) ^ (2 : ℕ) * (2 * (Real.log R - Real.log (ε * B))) := by
    calc
      ∫ x,
          Set.indicator
            {x : ℝ |
              ε <
                |B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x|}
            (fun x : ℝ ↦
              (B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x) ^ (2 : ℕ))
            x
          ∂μ
          =
            ∫ x,
              (B⁻¹) ^ (2 : ℕ) *
                Set.indicator
                  {x : ℝ | ε * B < |x| ∧ |x| ≤ R}
                  (fun x : ℝ ↦ x ^ (2 : ℕ))
                  x
              ∂μ := by
                refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
                simpa [B, R] using scaledTruncationTailSquare_eq_shell hB_pos x
      _ =
          (B⁻¹) ^ (2 : ℕ) *
            ∫ x,
              Set.indicator
                {x : ℝ | ε * B < |x| ∧ |x| ≤ R}
                (fun x : ℝ ↦ x ^ (2 : ℕ))
                x
              ∂μ := by
                rw [integral_const_mul]
      _ = (B⁻¹) ^ (2 : ℕ) * (2 * (Real.log R - Real.log (ε * B))) := by
            have hshellMoment :
                ∫ x,
                    Set.indicator
                      {x : ℝ | ε * B < |x| ∧ |x| ≤ R}
                      (fun x : ℝ ↦ x ^ (2 : ℕ))
                      x
                    ∂μ =
                  2 * (Real.log R - Real.log (ε * B)) := by
              simpa [μ] using inverseCubeTail_shellSecondMoment (ε * B) R
                (by simpa [B] using hcutoff_one)
                (by simpa [R, B] using hcutoff_le)
            rw [hshellMoment]
  -- Proof comment: first collapse the rowwise owner sum to one scalar integral, then normalize
  -- that scalar integral into the logarithmic shell formula.
  calc
    ∑ i : Fin ((inverseCubeTailTruncatedShiftedArray P X hX_law).rowLength n),
        ∫ ω,
          Set.indicator
            {ω | ε < |(inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω|}
            (fun ω ↦ ((inverseCubeTailTruncatedShiftedArray P X hX_law) n i ω) ^ (2 : ℕ))
            ω
          ∂P
        =
          (n + 1 : ℝ) *
            ∫ x,
              Set.indicator
                {x : ℝ |
                  ε <
                    |B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x|}
                (fun x : ℝ ↦
                  (B⁻¹ * Set.indicator {z : ℝ | |z| ≤ R} (fun z ↦ z) x) ^ (2 : ℕ))
                x
              ∂μ := by
                simpa [μ, B, R] using
                  inverseCubeTailTruncatedShiftedArray_rowTruncatedSecondMoment_eq_scalarIntegral
                    P X hX_law (ε := ε) n
    _ = (n + 1 : ℝ) * ((B⁻¹) ^ (2 : ℕ) * (2 * (Real.log R - Real.log (ε * B)))) := by
          rw [hshell]
    _ = ((n + 1 : ℝ) * (B⁻¹) ^ (2 : ℕ)) * (2 * (Real.log R - Real.log (ε * B))) := by
          ring
    _ = L⁻¹ * (2 * (Real.log R - Real.log (ε * B))) := by
          rw [hprefactor]
    _ = (2 * Real.log (R / (ε * B))) * L⁻¹ := by
          rw [Real.log_div hR_pos.ne' hεB_pos.ne']
          ring
    _ =
        (2 * Real.log
            (inverseCubeTailCLTNormingSequence (n + 1) /
              (ε * inverseCubeTailTruncationVarianceScale (n + 1)))) *
          (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹ := by
            simp [B, R, L]

/-- Helper for Exercise 15.5.3: the shifted truncated array satisfies the Lindeberg condition
because the logarithmic shell defect is `o(1)`. -/
private lemma inverseCubeTailTruncatedShiftedArray_satisfiesLindebergCondition
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P) :
    (inverseCubeTailTruncatedShiftedArray P X hX_law).SatisfiesLindebergCondition P := by
  let A := inverseCubeTailTruncatedShiftedArray P X hX_law
  letI : A.IsIndependent P := inverseCubeTailTruncatedShiftedArray_isIndependent P X hX_indep hX_law
  letI : A.IsCentered P := inverseCubeTailTruncatedShiftedArray_isCentered P X hX_law
  letI : A.IsNormed P := inverseCubeTailTruncatedShiftedArray_isNormed P X hX_law
  refine (RealRandomVariableArray.satisfiesLindebergCondition_iff (A := A) (μ := P)).2 ?_
  intro ε hε
  let expr : ℕ → ℝ := fun n ↦
    (2 * Real.log
        (inverseCubeTailCLTNormingSequence (n + 1) /
          (ε * inverseCubeTailTruncationVarianceScale (n + 1)))) *
      (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹
  have hεScaleAtTop :
      Tendsto (fun n : ℕ ↦ ε * inverseCubeTailTruncationVarianceScale (n + 1)) atTop atTop := by
    have hshift :
        Tendsto (fun n : ℕ ↦ inverseCubeTailTruncationVarianceScale (n + 1)) atTop atTop := by
      simpa using inverseCubeTailTruncationVarianceScale_tendsto_atTop.comp (tendsto_add_atTop_nat 1)
    simpa [mul_comm] using hshift.const_mul_atTop hε
  have hcutoffOne :
      ∀ᶠ n : ℕ in atTop,
        1 ≤ ε * inverseCubeTailTruncationVarianceScale (n + 1) :=
    hεScaleAtTop.eventually_ge_atTop 1
  have hlogNormalizerInv :
      Tendsto
        (fun n : ℕ ↦ (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹)
        atTop (𝓝 0) := by
    have hinnerAtTop :
        Tendsto (fun n : ℕ ↦ ((n + 3 : ℝ) * Real.log (n + 3 : ℝ))) atTop atTop := by
      have hshift : Tendsto (fun n : ℕ ↦ (n + 3 : ℝ)) atTop atTop := by
        simpa [Nat.cast_add, add_assoc] using
          tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop
      have hlinear :
          Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) * (n + 3 : ℝ)) atTop atTop := by
        simpa [mul_comm] using hshift.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
      have hlower :
          ∀ᶠ n : ℕ in atTop,
            (1 / 2 : ℝ) * (n + 3 : ℝ) ≤ (n + 3 : ℝ) * Real.log (n + 3 : ℝ) := by
        filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
        have hpos : (0 : ℝ) < n + 3 := by positivity
        have hlog_lower :
            1 - (n + 3 : ℝ)⁻¹ ≤ Real.log (n + 3 : ℝ) :=
          Real.one_sub_inv_le_log_of_pos hpos
        have hhalf_le :
            (1 / 2 : ℝ) ≤ 1 - (n + 3 : ℝ)⁻¹ := by
          have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
          have hfour_le : (4 : ℝ) ≤ n + 3 := by linarith
          have hinv_le : (n + 3 : ℝ)⁻¹ ≤ (4 : ℝ)⁻¹ := by
            rw [inv_le_inv₀ (by positivity : (0 : ℝ) < n + 3) (by norm_num : (0 : ℝ) < 4)]
            exact hfour_le
          linarith
        have hhalf_log : (1 / 2 : ℝ) ≤ Real.log (n + 3 : ℝ) :=
          le_trans hhalf_le hlog_lower
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left hhalf_log (show 0 ≤ (n + 3 : ℝ) by positivity)
      exact tendsto_atTop_mono' atTop hlower hlinear
    have hlogAtTop :
        Tendsto
          (fun n : ℕ ↦ Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))
          atTop atTop :=
      Real.tendsto_log_atTop.comp hinnerAtTop
    simpa [one_div] using tendsto_inv_atTop_zero.comp hlogAtTop
  have hexpr :
      Tendsto expr atTop (𝓝 0) := by
    have hmain :
        Tendsto
          (fun n : ℕ ↦
            2 *
              (Real.log
                  (inverseCubeTailCLTNormingSequence (n + 1) /
                    inverseCubeTailTruncationVarianceScale (n + 1)) *
                (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹))
          atTop (𝓝 0) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        Tendsto.const_mul (2 : ℝ) inverseCubeTail_scaleLogDefect_tendsto_zero
    have hconst :
        Tendsto
          (fun n : ℕ ↦
            (-2 * Real.log ε) * (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹)
          atTop (𝓝 0) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        Tendsto.const_mul (-2 * Real.log ε) hlogNormalizerInv
    have heq :
        ∀ n : ℕ,
          expr n =
            2 *
                (Real.log
                    (inverseCubeTailCLTNormingSequence (n + 1) /
                      inverseCubeTailTruncationVarianceScale (n + 1)) *
                  (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹) +
              (-2 * Real.log ε) *
                (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹ := by
      intro n
      have hA_pos : 0 < inverseCubeTailCLTNormingSequence (n + 1) :=
        inverseCubeTailCLTNormingSequence_pos (n + 1)
      have hB_pos : 0 < inverseCubeTailTruncationVarianceScale (n + 1) :=
        inverseCubeTailTruncationVarianceScale_pos n
      dsimp [expr]
      have hsplit :
          inverseCubeTailCLTNormingSequence (n + 1) /
              (ε * inverseCubeTailTruncationVarianceScale (n + 1)) =
            (inverseCubeTailCLTNormingSequence (n + 1) /
                inverseCubeTailTruncationVarianceScale (n + 1)) /
              ε := by
        field_simp [hε.ne', hA_pos.ne', hB_pos.ne']
      rw [hsplit, Real.log_div (div_ne_zero hA_pos.ne' hB_pos.ne') hε.ne']
      ring
    -- Proof comment: split the logarithm into the scale defect `log (A_n / B_n)` and the fixed
    -- constant `-log ε`; both pieces die against the inverse logarithmic normalizer.
    have hsum :
        Tendsto
          (fun n : ℕ ↦
            2 *
                (Real.log
                    (inverseCubeTailCLTNormingSequence (n + 1) /
                      inverseCubeTailTruncationVarianceScale (n + 1)) *
                  (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹) +
              (-2 * Real.log ε) *
                (Real.log (((n + 3 : ℝ) * Real.log (n + 3 : ℝ))))⁻¹)
          atTop (𝓝 0) := by
      simpa using hmain.add hconst
    exact Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (heq n).symm) hsum
  have hpiece :
      Tendsto
        (fun n : ℕ ↦
          if hcutoff_le :
              ε * inverseCubeTailTruncationVarianceScale (n + 1) ≤
                inverseCubeTailCLTNormingSequence (n + 1)
          then expr n
          else 0)
        atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hExprNorm : Tendsto (fun n : ℕ ↦ ‖expr n‖) atTop (𝓝 0) := by
      simpa using hexpr.norm
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hExprNorm
    exact Eventually.of_forall fun n ↦ by
      by_cases hcutoff_le :
          ε * inverseCubeTailTruncationVarianceScale (n + 1) ≤
            inverseCubeTailCLTNormingSequence (n + 1)
      · simp [hcutoff_le]
      · simp [hcutoff_le]
  have heventuallyEq :
      (fun n : ℕ ↦
        ∑ i : Fin (A.rowLength n),
          ∫ ω,
            Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω
            ∂P) =ᶠ[atTop]
        (fun n : ℕ ↦
          if hcutoff_le :
              ε * inverseCubeTailTruncationVarianceScale (n + 1) ≤
                inverseCubeTailCLTNormingSequence (n + 1)
          then expr n
          else 0) := by
    filter_upwards [hcutoffOne] with n hcutoffOne
    by_cases hcutoff_le :
        ε * inverseCubeTailTruncationVarianceScale (n + 1) ≤
          inverseCubeTailCLTNormingSequence (n + 1)
    · have hrowEq :=
        inverseCubeTailTruncatedShiftedArray_rowTruncatedSecondMoment_eq_logRatio
          P X hX_law hε n hcutoffOne hcutoff_le
      simp [A, expr, hcutoff_le, hrowEq]
    · have hcutoff_lt :
          inverseCubeTailCLTNormingSequence (n + 1) <
            ε * inverseCubeTailTruncationVarianceScale (n + 1) := by
        exact lt_of_not_ge hcutoff_le
      have hrowEq :=
        inverseCubeTailTruncatedShiftedArray_rowTruncatedSecondMoment_eq_zero_of_cutoff
          P X hX_law hε n hcutoff_lt
      simp [A, expr, hcutoff_le, hrowEq]
  -- Proof comment: after the eventual `1 ≤ ε B_{n+1}` cutoff, the rowwise Lindeberg sum is
  -- exactly a shell formula in the nonempty branch and `0` in the empty branch.
  exact Tendsto.congr' heventuallyEq.symm hpiece

/-- Helper for Exercise 15.5.3: splitting a coordinate into its truncated and large-jump parts at
the cutoff `R` recovers the original value. -/
private lemma indicator_smallNorm_add_indicator_largeNorm_eq_self (R x : ℝ) :
    Set.indicator {y : ℝ | |y| ≤ R} (fun y ↦ y) x +
      Set.indicator {y : ℝ | R < |y|} (fun y ↦ y) x = x := by
  -- Proof comment: the two indicators form a disjoint partition according to whether `|x|` is at
  -- most `R` or strictly larger than `R`.
  by_cases hx : |x| ≤ R
  · simp [hx, not_lt_of_ge hx]
  · have hlarge : R < |x| := lt_of_not_ge hx
    simp [hx, hlarge]

/-- Helper for Exercise 15.5.3: the shifted partial sum splits into the truncated part and the
large-jump correction at the cutoff `A_{n+1}`. -/
private theorem shiftedPartialSum_eq_truncatedPart_add_largeJump
    {Ω : Type u} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range (n + 1), X (k + 1) ω) =
      (∑ k ∈ Finset.range (n + 1),
        Set.indicator
          {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
          (fun x ↦ x)
          (X (k + 1) ω)) +
      (∑ k ∈ Finset.range (n + 1),
        Set.indicator
          {x : ℝ | inverseCubeTailCLTNormingSequence (n + 1) < |x|}
          (fun x ↦ x)
          (X (k + 1) ω)) := by
  -- Proof comment: split each summand at the cutoff `A_{n+1}` and then distribute the sum over
  -- the resulting two pieces.
  calc
    (∑ k ∈ Finset.range (n + 1), X (k + 1) ω)
        =
          ∑ k ∈ Finset.range (n + 1),
            (Set.indicator
              {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
              (fun x ↦ x)
              (X (k + 1) ω) +
            Set.indicator
              {x : ℝ | inverseCubeTailCLTNormingSequence (n + 1) < |x|}
              (fun x ↦ x)
              (X (k + 1) ω)) := by
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            symm
            simpa using
              indicator_smallNorm_add_indicator_largeNorm_eq_self
                (inverseCubeTailCLTNormingSequence (n + 1)) (X (k + 1) ω)
    _ =
        (∑ k ∈ Finset.range (n + 1),
          Set.indicator
            {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
            (fun x ↦ x)
            (X (k + 1) ω)) +
        (∑ k ∈ Finset.range (n + 1),
          Set.indicator
            {x : ℝ | inverseCubeTailCLTNormingSequence (n + 1) < |x|}
            (fun x ↦ x)
            (X (k + 1) ω)) := by
            rw [Finset.sum_add_distrib]

/-- Helper for Exercise 15.5.3: the normalized large-jump correction vanishes in probability
because the event that any entry crosses the cutoff has probability at most
`(n + 1) / A_{n+1}^2`. -/
private theorem inverseCubeTail_largeJumpCorrection_tendstoInMeasure_zero
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P) :
    TendstoInMeasure P
      (fun n : ℕ ↦
        fun ω ↦
          (inverseCubeTailCLTNormingSequence (n + 1))⁻¹ *
            ∑ k ∈ Finset.range (n + 1),
              Set.indicator
                {x : ℝ | inverseCubeTailCLTNormingSequence (n + 1) < |x|}
                (fun x ↦ x)
                (X (k + 1) ω))
      atTop
      (fun _ ↦ (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let cutoff : ℕ → ℝ := fun n ↦ inverseCubeTailCLTNormingSequence (n + 1)
  let rareEvent : ℕ → ℕ → Set Ω := fun n k ↦ {ω | cutoff n < |X (k + 1) ω|}
  have hbound :
      ∀ n : ℕ,
        P {ω |
            ε ≤
              ‖(cutoff n)⁻¹ *
                ∑ k ∈ Finset.range (n + 1),
                  Set.indicator {x : ℝ | cutoff n < |x|} (fun x ↦ x) (X (k + 1) ω)‖} ≤
          ENNReal.ofReal (((n + 1 : ℝ) * ((cutoff n)⁻¹ ^ (2 : ℕ)))) := by
    intro n
    let jumpSum : Ω → ℝ := fun ω ↦
      (cutoff n)⁻¹ *
        ∑ k ∈ Finset.range (n + 1),
          Set.indicator {x : ℝ | cutoff n < |x|} (fun x ↦ x) (X (k + 1) ω)
    let s : Set Ω := {ω | ε ≤ ‖jumpSum ω‖}
    let t : Set Ω := ⋃ k ∈ Finset.range (n + 1), rareEvent n k
    have hsubset : s ⊆ t := by
      intro ω hω
      by_contra hωt
      have hzero_terms :
          ∀ k ∈ Finset.range (n + 1),
            Set.indicator {x : ℝ | cutoff n < |x|} (fun x ↦ x) (X (k + 1) ω) = 0 := by
        intro k hk
        have hk_not : ¬ cutoff n < |X (k + 1) ω| := by
          intro hk_mem
          exact hωt (by
            refine Set.mem_iUnion.2 ⟨k, ?_⟩
            exact Set.mem_iUnion.2 ⟨hk, hk_mem⟩)
        simp [hk_not]
      have hsum_zero :
          ∑ k ∈ Finset.range (n + 1),
            Set.indicator {x : ℝ | cutoff n < |x|} (fun x ↦ x) (X (k + 1) ω) = 0 := by
        refine Finset.sum_eq_zero fun k hk ↦ ?_
        exact hzero_terms k hk
      have hjump_zero : jumpSum ω = 0 := by
        simp [jumpSum, hsum_zero]
      have : ¬ ε ≤ ‖jumpSum ω‖ := by
        simpa [hjump_zero] using (show ¬ ε ≤ (0 : ℝ) by linarith)
      exact this hω
    calc
      P s ≤ P t := by
        exact measure_mono hsubset
      _ ≤ ∑ k ∈ Finset.range (n + 1), P (rareEvent n k) := by
        simpa [t] using measure_biUnion_finset_le (μ := P) (Finset.range (n + 1))
          (fun k ↦ rareEvent n k)
      _ = ∑ k ∈ Finset.range (n + 1),
            ENNReal.ofReal (((cutoff n)⁻¹) ^ (2 : ℕ)) := by
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          have hshell : MeasurableSet {x : ℝ | cutoff n < |x|} := by
            exact measurableSet_lt measurable_const measurable_abs
          calc
            P (rareEvent n k)
                = (Measure.map (X (k + 1)) P) {x : ℝ | cutoff n < |x|} := by
                    rw [show rareEvent n k = (X (k + 1)) ⁻¹' {x : ℝ | cutoff n < |x|}
                      by
                        ext ω
                        simp [rareEvent]]
                    exact (Measure.map_apply_of_aemeasurable (hX_law k).aemeasurable hshell).symm
            _ = symmetricParetoMeasure (1 / 2) {x : ℝ | cutoff n < |x|} := by
                  simpa using congrArg
                    (fun μ : Measure ℝ ↦ μ {x : ℝ | cutoff n < |x|}) (hX_law k).map_eq
            _ = ENNReal.ofReal (((cutoff n)⁻¹) ^ (2 : ℕ)) := by
                  simpa [cutoff] using
                    inverseCubeTail_tailMass (cutoff n)
                      (inverseCubeTailCLTNormingSequence_one_le (n + 1))
      _ = ENNReal.ofReal (((n + 1 : ℝ) * ((cutoff n)⁻¹ ^ (2 : ℕ)))) := by
            have hnonneg : 0 ≤ (((cutoff n)⁻¹) ^ (2 : ℕ) : ℝ) := by positivity
            calc
              ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (((cutoff n)⁻¹) ^ (2 : ℕ))
                  = (n + 1 : ENNReal) * ENNReal.ofReal (((cutoff n)⁻¹) ^ (2 : ℕ)) := by
                      simp
              _ = ENNReal.ofReal (((n + 1 : ℝ) * ((cutoff n)⁻¹ ^ (2 : ℕ)))) := by
                    have hnat : (n + 1 : ENNReal) = ENNReal.ofReal (n + 1 : ℝ) := by
                      simpa using (ENNReal.ofReal_natCast (n + 1)).symm
                    have hnat_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
                    rw [hnat]
                    simpa [mul_comm] using (ENNReal.ofReal_mul hnat_nonneg
                      (q := ((cutoff n)⁻¹ ^ (2 : ℕ)))).symm
  have hUpper_real :
      Tendsto
        (fun n : ℕ ↦ ((n + 1 : ℝ) * (inverseCubeTailCLTNormingSequence (n + 1) ^ (2 : ℕ))⁻¹))
        atTop
        (𝓝 0) := by
    convert inverseCubeTail_largeJumpRate_tendsto_zero.comp (tendsto_add_atTop_nat 1) using 1
    funext n
    simp [Function.comp, Nat.cast_add, Nat.cast_one]
  have hUpper :
      Tendsto
        (fun n : ℕ ↦
          ENNReal.ofReal
            (((n + 1 : ℝ) * (inverseCubeTailCLTNormingSequence (n + 1) ^ (2 : ℕ))⁻¹)))
        atTop
        (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hUpper_real
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper ?_
      (fun n ↦ by simpa [cutoff, inv_pow] using hbound n)
  intro n
  exact zero_le _

/-- Helper for Exercise 15.5.3: the centered normed truncated array has row-sum variance `1`. -/
private lemma inverseCubeTailTruncatedShiftedArray_rowSumVariance_eq_one
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P)
    (n : ℕ) :
    Var[(inverseCubeTailTruncatedShiftedArray P X hX_law).rowSum n; P] = 1 := by
  let A := inverseCubeTailTruncatedShiftedArray P X hX_law
  letI : A.IsIndependent P := inverseCubeTailTruncatedShiftedArray_isIndependent P X hX_indep hX_law
  letI : A.IsNormed P := inverseCubeTailTruncatedShiftedArray_isNormed P X hX_law
  have hPairwise : Pairwise fun i j : Fin (A.rowLength n) ↦ A n i ⟂ᵢ[P] A n j := by
    intro i j hij
    exact (RealRandomVariableArray.IsIndependent.rowwise (A := A) (μ := P) n).indepFun hij
  -- Proof comment: rowwise independence rewrites the row-sum variance into the sum of entry
  -- variances, and the normed-array normalization fixes that sum at `1`.
  calc
    Var[A.rowSum n; P] = ∑ i : Fin (A.rowLength n), Var[A n i; P] := by
      simpa [RealRandomVariableArray.rowSum] using
        ProbabilityTheory.IndepFun.variance_sum
          (μ := P) (X := fun i : Fin (A.rowLength n) ↦ A n i) (s := Finset.univ)
          (hs := fun i _ ↦ RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := P) n i)
          (by
            intro i _ j _ hij
            exact hPairwise hij)
    _ = 1 := RealRandomVariableArray.IsNormed.variance_sum_eq_one (A := A) (μ := P) n

/-- Helper for Exercise 15.5.3: the difference between the owner normalization `B_{n+1}` and the
target normalization `A_{n+1}` is negligible in probability on the truncated row sums. -/
private lemma inverseCubeTail_scaleSwap_tendstoInMeasure_zero
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P) :
    TendstoInMeasure P
      (fun n : ℕ ↦
        fun ω ↦
          ((inverseCubeTailTruncationVarianceScale (n + 1) /
                inverseCubeTailCLTNormingSequence (n + 1)) - 1) *
            (inverseCubeTailTruncatedShiftedArray P X hX_law).rowSum n ω)
      atTop
      (fun _ ↦ (0 : ℝ)) := by
  let A := inverseCubeTailTruncatedShiftedArray P X hX_law
  letI : A.IsIndependent P := inverseCubeTailTruncatedShiftedArray_isIndependent P X hX_indep hX_law
  letI : A.IsCentered P := inverseCubeTailTruncatedShiftedArray_isCentered P X hX_law
  letI : A.IsNormed P := inverseCubeTailTruncatedShiftedArray_isNormed P X hX_law
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let coeff : ℕ → ℝ := fun n ↦
    inverseCubeTailTruncationVarianceScale (n + 1) /
      inverseCubeTailCLTNormingSequence (n + 1) - 1
  let scaled : ℕ → Ω → ℝ := fun n ω ↦ A.rowSum n ω * coeff n
  have hcoeffZero : Tendsto coeff atTop (𝓝 0) := by
    simpa [coeff] using
      (inverseCubeTail_truncationScaleRatio_tendsto_one.comp (tendsto_add_atTop_nat 1)).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  have hcoeffBoundReal :
      Tendsto (fun n : ℕ ↦ (coeff n ^ (2 : ℕ)) / ε ^ (2 : ℕ)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n : ℕ ↦ coeff n ^ (2 : ℕ)) atTop (𝓝 0) := by
      simpa [pow_two] using hcoeffZero.mul hcoeffZero
    simpa using hsq.div_const (ε ^ (2 : ℕ))
  have hcoeffBound :
      Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((coeff n ^ (2 : ℕ)) / ε ^ (2 : ℕ))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hcoeffBoundReal
  have hbound :
      ∀ n : ℕ,
        P {ω | ε ≤ ‖scaled n ω - 0‖} ≤ ENNReal.ofReal ((coeff n ^ (2 : ℕ)) / ε ^ (2 : ℕ)) := by
    intro n
    have hrowMem :
        MemLp (A.rowSum n) 2 P := by
      refine memLp_two_of_variance_ne_zero (A.measurable_rowSum n).aestronglyMeasurable ?_
      rw [inverseCubeTailTruncatedShiftedArray_rowSumVariance_eq_one P X hX_indep hX_law n]
      norm_num
    have hscaledMem : MemLp (scaled n) 2 P := by
      simpa [scaled, coeff, mul_comm] using hrowMem.mul_const (coeff n)
    have hrowMean : P[A.rowSum n] = 0 := by
      have hrowExpand : A.rowSum n = fun ω ↦ ∑ i : Fin (A.rowLength n), A n i ω := by
        funext ω
        simp [RealRandomVariableArray.rowSum, Finset.sum_apply]
      rw [hrowExpand]
      rw [integral_finset_sum]
      · simp [RealRandomVariableArray.IsCentered.expectation_eq_zero (A := A) (μ := P)]
      · intro i hi
        exact RealRandomVariableArray.IsCentered.integrable (A := A) (μ := P) n i
    have hscaledMean : P[scaled n] = 0 := by
      calc
        ∫ ω, scaled n ω ∂P = (∫ ω, A.rowSum n ω ∂P) * coeff n := by
          rw [show scaled n = fun ω ↦ A.rowSum n ω * coeff n by rfl, integral_mul_const]
        _ = 0 := by simp [hrowMean]
    have hvarScaled :
        Var[scaled n; P] = coeff n ^ (2 : ℕ) := by
      calc
        Var[scaled n; P] = Var[A.rowSum n; P] * coeff n ^ (2 : ℕ) := by
          simpa [scaled, coeff, mul_comm] using
            (variance_mul_const (coeff n) (A.rowSum n) P)
        _ = coeff n ^ (2 : ℕ) := by
          rw [inverseCubeTailTruncatedShiftedArray_rowSumVariance_eq_one P X hX_indep hX_law n,
            one_mul]
    have hEvent :
        {ω | ε ≤ ‖scaled n ω - 0‖} = {ω | ε ≤ |scaled n ω - P[scaled n]|} := by
      ext ω
      simp [hscaledMean, Real.norm_eq_abs]
    -- Proof comment: Chebyshev reduces the perturbation event to the squared coefficient
    -- `((B_{n+1} / A_{n+1}) - 1)^2` because `Var[rowSum_n] = 1`.
    rw [hEvent]
    calc
      P {ω | ε ≤ |scaled n ω - P[scaled n]|} ≤ ENNReal.ofReal (Var[scaled n; P] / ε ^ (2 : ℕ)) :=
        meas_ge_le_variance_div_sq hscaledMem hε
      _ = ENNReal.ofReal ((coeff n ^ (2 : ℕ)) / ε ^ (2 : ℕ)) := by rw [hvarScaled]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcoeffBound ?_
    (fun n ↦ by simpa [scaled, coeff, mul_comm] using hbound n)
  intro n
  exact zero_le _

/-- Exercise 15.5.3: one explicit norming sequence for i.i.d. real random variables with density
`x ↦ |x|⁻³ 1_{ℝ \ [-1,1]}(x)` is `A_n = √((n + 2) log (n + 2))`; with this normalization, the
partial sums converge in distribution to the standard Gaussian law. -/
theorem tendstoInDistribution_sum_div_inverseCubeTailCLTNormingSequence
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (Y : Ω' → ℝ)
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P) :
    TendstoInDistribution
      (fun n ω ↦ (inverseCubeTailCLTNormingSequence n)⁻¹ *
        ∑ k ∈ Finset.range n, X (k + 1) ω)
      atTop Y (fun _ ↦ P) P' := by
  let A := inverseCubeTailTruncatedShiftedArray P X hX_law
  let gaussianProb : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  let target : ℕ → Ω → ℝ := fun n ω ↦
    (inverseCubeTailCLTNormingSequence n)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) ω
  let truncatedCore : ℕ → Ω → ℝ := fun n ω ↦
    (inverseCubeTailCLTNormingSequence (n + 1))⁻¹ *
      ∑ k ∈ Finset.range (n + 1),
        Set.indicator
          {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
          (fun x ↦ x)
          (X (k + 1) ω)
  let shiftedTarget : ℕ → Ω → ℝ := fun n ↦ target (n + 1)
  let largeJump : ℕ → Ω → ℝ := fun n ω ↦
    (inverseCubeTailCLTNormingSequence (n + 1))⁻¹ *
      ∑ k ∈ Finset.range (n + 1),
        Set.indicator
          {x : ℝ | inverseCubeTailCLTNormingSequence (n + 1) < |x|}
          (fun x ↦ x)
          (X (k + 1) ω)
  letI : A.IsIndependent P := inverseCubeTailTruncatedShiftedArray_isIndependent P X hX_indep hX_law
  letI : A.IsCentered P := inverseCubeTailTruncatedShiftedArray_isCentered P X hX_law
  letI : A.IsNormed P := inverseCubeTailTruncatedShiftedArray_isNormed P X hX_law
  have hA_lindeberg : A.SatisfiesLindebergCondition P :=
    inverseCubeTailTruncatedShiftedArray_satisfiesLindebergCondition P X hX_indep hX_law
  have hGaussianLaw :
      Tendsto (fun n ↦ A.rowSumLaw P n) atTop (𝓝 gaussianProb) := by
    exact
      ((RealRandomVariableArray.lindeberg_feller_central_limit_theorem
        (A := A) (μ := P)).1 hA_lindeberg).2
  have hRowSumDist :
      TendstoInDistribution (fun n ↦ A.rowSum n) atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    exact
      (tendstoInDistribution_iff_tendsto_limit_law
        (X := fun n ↦ A.rowSum n) (l := atTop) (μ := fun _ ↦ P)
        (Z := id) (μ' := gaussianReal 0 1) (ν := gaussianProb)
        (hX := fun n ↦ (A.measurable_rowSum n).aemeasurable) HasLaw.id).2
        hGaussianLaw
  have hTruncatedCoreEq :
      ∀ n : ℕ,
        truncatedCore n =ᵐ[P]
          (fun ω ↦
            A.rowSum n ω +
              ((inverseCubeTailTruncationVarianceScale (n + 1) /
                    inverseCubeTailCLTNormingSequence (n + 1)) - 1) *
                A.rowSum n ω) := by
    intro n
    let B := inverseCubeTailTruncationVarianceScale (n + 1)
    let C := inverseCubeTailCLTNormingSequence (n + 1)
    have hB_pos : 0 < B := by
      simpa [B] using inverseCubeTailTruncationVarianceScale_pos n
    have hC_pos : 0 < C := by
      simpa [C] using inverseCubeTailCLTNormingSequence_pos (n + 1)
    filter_upwards [inverseCubeTailTruncatedShiftedArray_rowSum_ae_eq P X hX_law n] with ω hω
    calc
      truncatedCore n ω = (B / C) * A.rowSum n ω := by
        rw [show truncatedCore n ω =
            C⁻¹ *
              ∑ k ∈ Finset.range (n + 1),
                Set.indicator
                  {x : ℝ | |x| ≤ inverseCubeTailCLTNormingSequence (n + 1)}
                  (fun x ↦ x)
                  (X (k + 1) ω) by rfl]
        rw [hω]
        field_simp [B, C, hB_pos.ne', hC_pos.ne']
        ring
      _ = A.rowSum n ω +
            ((inverseCubeTailTruncationVarianceScale (n + 1) /
                  inverseCubeTailCLTNormingSequence (n + 1)) - 1) *
              A.rowSum n ω := by
            simp [B, C]
            ring
  have hScaleSwap :
      TendstoInMeasure P
        (fun n : ℕ ↦
          fun ω ↦
            ((inverseCubeTailTruncationVarianceScale (n + 1) /
                  inverseCubeTailCLTNormingSequence (n + 1)) - 1) *
              A.rowSum n ω)
        atTop
        (fun _ ↦ (0 : ℝ)) :=
    inverseCubeTail_scaleSwap_tendstoInMeasure_zero P X hX_indep hX_law
  have hTruncatedCoreDist :
      TendstoInDistribution truncatedCore atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    have hPerturbed :
        TendstoInDistribution
          (fun n ↦
            fun ω ↦
              A.rowSum n ω +
                ((inverseCubeTailTruncationVarianceScale (n + 1) /
                      inverseCubeTailCLTNormingSequence (n + 1)) - 1) *
                  A.rowSum n ω)
          atTop
          (fun ω ↦ id ω + 0)
          (fun _ ↦ P)
          (gaussianReal 0 1) :=
      hRowSumDist.add_of_tendstoInMeasure_const hScaleSwap
        (fun n ↦ (measurable_const.mul (A.measurable_rowSum n)).aemeasurable)
    have hPerturbed' :
        TendstoInDistribution
          (fun n ↦
            fun ω ↦
              A.rowSum n ω +
                ((inverseCubeTailTruncationVarianceScale (n + 1) /
                      inverseCubeTailCLTNormingSequence (n + 1)) - 1) *
                  A.rowSum n ω)
          atTop
          id
          (fun _ ↦ P)
          (gaussianReal 0 1) := by
      simpa [Pi.add_def] using hPerturbed
    -- Proof comment: replace the owner row sum by the `A_{n+1}`-normalized truncated partial sum.
    exact
      TendstoInDistribution.congr
        (fun n ↦ (hTruncatedCoreEq n).symm)
        (Filter.Eventually.of_forall fun _ ↦ rfl)
        hPerturbed'
  have hLargeJumpMeas : ∀ n : ℕ, AEMeasurable (largeJump n) P := by
    intro n
    let jumpTerm : ℕ → Ω → ℝ := fun k ω ↦
      Set.indicator
        {x : ℝ | inverseCubeTailCLTNormingSequence (n + 1) < |x|}
        (fun x ↦ x)
        (X (k + 1) ω)
    have hjumpAe : ∀ k : ℕ, AEMeasurable (jumpTerm k) P := by
      intro k
      exact
        ((measurable_id.indicator
            (measurableSet_lt measurable_const measurable_abs)).aemeasurable).comp_aemeasurable
          (hX_law k).aemeasurable
    have hsumAe :
        AEMeasurable (∑ k ∈ Finset.range (n + 1), jumpTerm k) P := by
      exact Finset.aemeasurable_sum (Finset.range (n + 1)) fun k _ ↦ hjumpAe k
    simpa [largeJump, jumpTerm] using (hsumAe.aestronglyMeasurable.const_mul _).aemeasurable
  have hShiftedEq :
      ∀ n : ℕ, shiftedTarget n =ᵐ[P] fun ω ↦ truncatedCore n ω + largeJump n ω := by
    intro n
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    dsimp [shiftedTarget, target, truncatedCore, largeJump]
    rw [shiftedPartialSum_eq_truncatedPart_add_largeJump X n ω, mul_add]
  have hShiftedDist :
      TendstoInDistribution shiftedTarget atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    have hPerturbed :
        TendstoInDistribution
          (fun n ↦ fun ω ↦ truncatedCore n ω + largeJump n ω)
          atTop
          (fun ω ↦ id ω + 0)
          (fun _ ↦ P)
          (gaussianReal 0 1) :=
      hTruncatedCoreDist.add_of_tendstoInMeasure_const
        (inverseCubeTail_largeJumpCorrection_tendstoInMeasure_zero P X hX_law)
        hLargeJumpMeas
    have hPerturbed' :
        TendstoInDistribution
          (fun n ↦ fun ω ↦ truncatedCore n ω + largeJump n ω)
          atTop
          id
          (fun _ ↦ P)
          (gaussianReal 0 1) := by
      simpa [Pi.add_def] using hPerturbed
    -- Proof comment: add back the rare-jump correction and recover the shifted full normalized
    -- partial sums.
    exact
      TendstoInDistribution.congr
        (fun n ↦ (hShiftedEq n).symm)
        (Filter.Eventually.of_forall fun _ ↦ rfl)
        hPerturbed'
  have hTargetAemeas : ∀ n : ℕ, AEMeasurable (target n) P := by
    intro n
    let rawTerm : ℕ → Ω → ℝ := fun k ω ↦ X (k + 1) ω
    have hrawAe : ∀ k : ℕ, AEMeasurable (rawTerm k) P := by
      intro k
      simpa [rawTerm] using (hX_law k).aemeasurable
    have hsumAe : AEMeasurable (∑ k ∈ Finset.range n, rawTerm k) P := by
      exact Finset.aemeasurable_sum (Finset.range n) fun k _ ↦ hrawAe k
    simpa [target, rawTerm] using (hsumAe.aestronglyMeasurable.const_mul _).aemeasurable
  have hShiftedLaw :
      Tendsto
        (fun n ↦ ProbabilityMeasure.map ⟨P, inferInstance⟩ (hTargetAemeas (n + 1)))
        atTop
        (𝓝 gaussianProb) := by
    exact
      (tendstoInDistribution_iff_tendsto_limit_law
        (X := shiftedTarget) (l := atTop) (μ := fun _ ↦ P)
        (Z := id) (μ' := gaussianReal 0 1) (ν := gaussianProb)
        (hX := fun n ↦ hTargetAemeas (n + 1)) HasLaw.id).1 hShiftedDist
  have hTargetLaw :
      Tendsto (fun n ↦ ProbabilityMeasure.map ⟨P, inferInstance⟩ (hTargetAemeas n)) atTop
        (𝓝 gaussianProb) := by
    refine (Filter.tendsto_add_atTop_iff_nat 1).1 ?_
    simpa [Function.comp] using hShiftedLaw
  -- Proof comment: the final shift from `n + 1` back to `n` is harmless at `atTop`, so the
  -- original normalized partial sums have the same Gaussian limit law.
  exact
    (tendstoInDistribution_iff_tendsto_limit_law
      (X := target) (l := atTop) (μ := fun _ ↦ P)
      (Z := Y) (μ' := P') (ν := gaussianProb)
      (hX := hTargetAemeas) hY).2 hTargetLaw
