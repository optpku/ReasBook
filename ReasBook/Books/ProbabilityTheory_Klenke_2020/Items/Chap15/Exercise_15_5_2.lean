/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Example_15_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

open RealRandomVariableArray

/-- The three-point law of the rare jump variable `Z_{n+1}`: it is `0` with probability
`1 - (n + 1)⁻²` and takes the values `± (n + 1)` with probability `(2 (n + 1)²)⁻¹` each. -/
def rareJumpLaw (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) • Measure.dirac 0 +
    ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) • Measure.dirac (n + 1 : ℝ) +
      ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) • Measure.dirac (-(n + 1 : ℝ))

/-- The rare-jump law is the sum of the Dirac masses at `0` and `± (n + 1)` with the stated
weights. -/
theorem rareJumpLaw_def (n : ℕ) :
    rareJumpLaw n =
      ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) • Measure.dirac 0 +
        ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) • Measure.dirac (n + 1 : ℝ) +
          ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) •
            Measure.dirac (-(n + 1 : ℝ)) :=
  rfl

/-- Helper for Exercise 15.5.2: the rare-jump probability `(n + 1)⁻²` is at most `1`. -/
private lemma rareJumpWeight_le_one (n : ℕ) :
    1 / ((n + 1 : ℝ) ^ (2 : ℕ)) ≤ 1 := by
  -- Proof comment: `(n + 1)^2 ≥ 1`, so its reciprocal is bounded above by `1`.
  have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hsq_ge_one : (1 : ℝ) ≤ (n + 1 : ℝ) ^ (2 : ℕ) := by
    nlinarith
  have hsq_ne : ((n + 1 : ℝ) ^ (2 : ℕ)) ≠ 0 := by
    positivity
  have hdiv : 1 / ((n + 1 : ℝ) ^ (2 : ℕ)) ≤ 1 := by
    field_simp [hsq_ne]
    nlinarith
  simpa [one_div] using hdiv

/-- Helper for Exercise 15.5.2: the zero-atom weight in `rareJumpLaw n` is nonnegative. -/
private lemma rareJumpZeroWeight_nonneg (n : ℕ) :
    0 ≤ 1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ)) := by
  -- Proof comment: the zero mass is the complement of the rare-jump probability.
  exact sub_nonneg.mpr (rareJumpWeight_le_one n)

/-- Helper for Exercise 15.5.2: each side-atom weight in `rareJumpLaw n` is nonnegative. -/
private lemma rareJumpSideWeight_nonneg (n : ℕ) :
    0 ≤ 1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) := by
  -- Proof comment: the side weight is a positive reciprocal.
  positivity

/-- Helper for Exercise 15.5.2: every strongly measurable real function is integrable against the
three-point law `rareJumpLaw n`. -/
private lemma integrable_rareJumpLaw (n : ℕ) {f : ℝ → ℝ} (hf : StronglyMeasurable f) :
    Integrable f (rareJumpLaw n) := by
  -- Proof comment: each Dirac component is integrable, and finite sums preserve integrability.
  have h0 :
      Integrable f
        (ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) • Measure.dirac 0) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h1 :
      Integrable f
        (ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) • Measure.dirac (n + 1 : ℝ)) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h2 :
      Integrable f
        (ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) •
          Measure.dirac (-(n + 1 : ℝ))) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  simpa [rareJumpLaw] using
    (integrable_add_measure).2
      ⟨(integrable_add_measure).2 ⟨h0, h1⟩, h2⟩

/-- Helper for Exercise 15.5.2: integrating a real function against `rareJumpLaw n` reduces to
the corresponding three-point weighted average. -/
private lemma integral_rareJumpLaw (n : ℕ) {f : ℝ → ℝ} (hf : StronglyMeasurable f) :
    ∫ x, f x ∂rareJumpLaw n =
      (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) * f 0 +
        (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) * f (n + 1 : ℝ) +
          (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) * f (-(n + 1 : ℝ)) := by
  -- Proof comment: expand the measure into three scaled Dirac masses and evaluate each integral.
  have hzero_nonneg : 0 ≤ 1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ)) := rareJumpZeroWeight_nonneg n
  have hside_nonneg : 0 ≤ 1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) := rareJumpSideWeight_nonneg n
  have h0 :
      Integrable f
        (ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) • Measure.dirac 0) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h1 :
      Integrable f
        (ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) • Measure.dirac (n + 1 : ℝ)) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h2 :
      Integrable f
        (ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) •
          Measure.dirac (-(n + 1 : ℝ))) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h01 :
      Integrable f
        (ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) • Measure.dirac 0 +
          ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) •
            Measure.dirac (n + 1 : ℝ)) := by
    exact (integrable_add_measure).2 ⟨h0, h1⟩
  rw [rareJumpLaw, integral_add_measure h01 h2, integral_add_measure h0 h1,
    integral_smul_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac' f 0 hf, integral_dirac' f (n + 1 : ℝ) hf,
    integral_dirac' f (-(n + 1 : ℝ)) hf]
  change
    (ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ)))).toReal * f 0 +
        (ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))))).toReal * f (n + 1 : ℝ) +
          (ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))))).toReal * f (-(n + 1 : ℝ)) =
      (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) * f 0 +
        (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) * f (n + 1 : ℝ) +
          (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) * f (-(n + 1 : ℝ))
  rw [ENNReal.toReal_ofReal hzero_nonneg, ENNReal.toReal_ofReal hside_nonneg]

/-- Helper for Exercise 15.5.2: under `rareJumpLaw n`, the event `x ≠ 0` has mass `(n + 1)⁻²`. -/
theorem rareJumpLaw_nonzero_event (n : ℕ) :
    rareJumpLaw n {x : ℝ | x ≠ 0} =
      ENNReal.ofReal (1 / ((n + 1 : ℝ) ^ (2 : ℕ))) := by
  -- Proof comment: only the two atoms at `± (n + 1)` contribute to `{x | x ≠ 0}`.
  have hne : (n + 1 : ℝ) ≠ 0 := by
    positivity
  have hneg' : (-1 + -(n : ℝ)) ≠ 0 := by
    nlinarith
  have hside_nonneg : 0 ≤ 1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) := rareJumpSideWeight_nonneg n
  have hside_add :
      ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) +
          ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) =
        ENNReal.ofReal
          (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) + 1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) := by
    exact (ENNReal.ofReal_add hside_nonneg hside_nonneg).symm
  calc
    rareJumpLaw n {x : ℝ | x ≠ 0}
        = ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) +
            ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) := by
            simp [rareJumpLaw, hne, hneg']
    _ = ENNReal.ofReal (1 / ((n + 1 : ℝ) ^ (2 : ℕ))) := by
          rw [hside_add]
          have hsq_ne : ((n + 1 : ℝ) ^ (2 : ℕ)) ≠ 0 := by
            positivity
          congr 1
          field_simp [hsq_ne]
          ring

/-- Helper for Exercise 15.5.2: under `rareJumpLaw n`, the event `|x| = n + 1` has mass
`(n + 1)⁻²`. -/
theorem rareJumpLaw_abs_eq_event (n : ℕ) :
    rareJumpLaw n {x : ℝ | |x| = (n + 1 : ℝ)} =
      ENNReal.ofReal (1 / ((n + 1 : ℝ) ^ (2 : ℕ))) := by
  -- Proof comment: the atoms at `n + 1` and `-(n + 1)` both lie on the same absolute-value shell.
  have hpos : (0 : ℝ) < (n + 1 : ℝ) := by
    positivity
  have hzero_ne : (0 : ℝ) ≠ (n + 1 : ℝ) := by
    linarith
  have habs_pos : |(n + 1 : ℝ)| = (n + 1 : ℝ) := by
    rw [abs_of_nonneg hpos.le]
  have habs_neg : |(-(n + 1 : ℝ))| = (n + 1 : ℝ) := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  have hneg_eq : (-1 + -(n : ℝ)) = -(n + 1 : ℝ) := by
    ring
  have habs_neg' : |(-1 + -(n : ℝ))| = (n + 1 : ℝ) := by
    rw [hneg_eq, habs_neg]
  calc
    rareJumpLaw n {x : ℝ | |x| = (n + 1 : ℝ)}
        = ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) +
            ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) := by
            simp [rareJumpLaw, hzero_ne, habs_pos, habs_neg', add_assoc]
    _ = ENNReal.ofReal (1 / ((n + 1 : ℝ) ^ (2 : ℕ))) := by
          have hside_nonneg : 0 ≤ 1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) := rareJumpSideWeight_nonneg n
          rw [(ENNReal.ofReal_add hside_nonneg hside_nonneg).symm]
          have hsq_ne : ((n + 1 : ℝ) ^ (2 : ℕ)) ≠ 0 := by
            positivity
          congr 1
          field_simp [hsq_ne]
          ring

/-- Helper for Exercise 15.5.2: `rareJumpLaw n` is a probability measure. -/
private theorem rareJumpLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (rareJumpLaw n) := by
  -- Proof comment: the three Dirac masses carry the full probability mass `1`.
  refine ⟨?_⟩
  have hzero_nonneg : 0 ≤ 1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ)) := rareJumpZeroWeight_nonneg n
  have hside_nonneg : 0 ≤ 1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) := rareJumpSideWeight_nonneg n
  have hside_sum_nonneg :
      0 ≤ 1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) + 1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) := by
    nlinarith
  have hside_add :
      ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) +
          ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) =
        ENNReal.ofReal
          (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) + 1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) := by
    exact (ENNReal.ofReal_add hside_nonneg hside_nonneg).symm
  calc
    rareJumpLaw n Set.univ
        = ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) +
            ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) +
              ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) := by
            simp [rareJumpLaw, add_assoc]
    _ = ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) +
          ENNReal.ofReal
            (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) + 1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) := by
          rw [add_assoc, hside_add]
    _ =
        ENNReal.ofReal
          ((1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) +
            (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) + 1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))))) := by
          rw [← ENNReal.ofReal_add hzero_nonneg hside_sum_nonneg]
    _ = 1 := by
          have hsq_ne : ((n + 1 : ℝ) ^ (2 : ℕ)) ≠ 0 := by
            positivity
          have hweights :
              (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ)) +
                  (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))) +
                    1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ))))) = (1 : ℝ) := by
            field_simp [hsq_ne]
            ring
          rw [hweights]
          norm_num

/-- Helper for Exercise 15.5.2: the rare-jump law is centered, has variance `1`, and lies in
`L²`. -/
private theorem rareJumpLawMoments (n : ℕ) :
    MemLp id 2 (rareJumpLaw n) ∧ (∫ x, x ∂ rareJumpLaw n) = 0 ∧ Var[id; rareJumpLaw n] = 1 := by
  -- Proof comment: the law is symmetric at `± (n + 1)`, so the mean is `0`, the second moment is
  -- `1`, and square-integrability follows from the nonzero variance.
  haveI : IsProbabilityMeasure (rareJumpLaw n) := rareJumpLaw_isProbabilityMeasure n
  have hmean : (∫ x, x ∂ rareJumpLaw n) = 0 := by
    -- Proof comment: the two side atoms cancel because the law is symmetric.
    calc
      ∫ x, x ∂ rareJumpLaw n
          = (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) * (0 : ℝ) +
              (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) * (n + 1 : ℝ) +
                (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) * (-(n + 1 : ℝ)) := by
              simpa using integral_rareJumpLaw n stronglyMeasurable_id
      _ = 0 := by ring
  have hsecond : ∫ x, x ^ (2 : ℕ) ∂ rareJumpLaw n = 1 := by
    -- Proof comment: each side atom contributes half of `(n + 1)^2`, while the atom at `0`
    -- contributes nothing.
    calc
      ∫ x, x ^ (2 : ℕ) ∂ rareJumpLaw n
          = (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) * ((n + 1 : ℝ) ^ (2 : ℕ)) +
              (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) * ((n + 1 : ℝ) ^ (2 : ℕ)) := by
              rw [integral_rareJumpLaw n (f := fun x : ℝ ↦ x ^ (2 : ℕ)) (by fun_prop)]
              ring
      _ = 1 := by
            have hsq_ne : ((n + 1 : ℝ) ^ (2 : ℕ)) ≠ 0 := by
              positivity
            field_simp [hsq_ne]
            norm_num
  have hmemLp : MemLp id 2 (rareJumpLaw n) := by
    -- Proof comment: a finite sum of Dirac masses has integrable square.
    exact (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 <| by
      simpa using
        (integrable_rareJumpLaw n (f := fun x : ℝ ↦ x ^ (2 : ℕ)) (by fun_prop))
  have hvar : Var[id; rareJumpLaw n] = 1 := by
    -- Proof comment: rewrite the variance as `E[X^2] - E[X]^2` and substitute the two moments.
    calc
      Var[id; rareJumpLaw n]
          = ∫ x, x ^ (2 : ℕ) ∂ rareJumpLaw n - (∫ x, x ∂ rareJumpLaw n) ^ (2 : ℕ) := by
              simpa using (variance_eq_sub hmemLp)
      _ = 1 := by
            rw [hsecond, hmean]
            ring
  exact ⟨hmemLp, hmean, hvar⟩

/-- Helper for Exercise 15.5.2: if a real sequence is eventually zero, then its partial sums
stabilize. -/
private lemma partialSumCoordinateProcess_eventually_constant
    (ω : ℕ → ℝ) (hω : ∀ᶠ n in atTop, ω n = 0) :
    ∃ N : ℕ, (fun n ↦ partialSum coordinateProcess n ω) =ᶠ[atTop]
      fun _ ↦ partialSum coordinateProcess N ω := by
  -- Proof comment: every tail block vanishes once all coordinates past some index are zero.
  rcases Filter.eventually_atTop.1 hω with ⟨N, hN⟩
  refine ⟨N, Filter.eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩⟩
  have htail :
      ∑ i ∈ Finset.Ico N n, coordinateProcess i ω = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    exact hN i (Finset.mem_Ico.1 hi).1
  have hdiff := partialSum_sub_eq_sum_Ico coordinateProcess hn ω
  have hEq : partialSum coordinateProcess n ω - partialSum coordinateProcess N ω = 0 := by
    simpa [htail] using hdiff
  exact sub_eq_zero.mp hEq

/-- Helper for Exercise 15.5.2: once only finitely many rare jumps occur, the normalized rare-jump
partial sums tend to `0`. -/
private lemma normalizedRarePart_tendsto_zero_ae
    (ω : ℕ → ℝ) (hω : ∀ᶠ n in atTop, ω n = 0) :
    Tendsto
      (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum coordinateProcess n ω)
      atTop (𝓝 0) := by
  -- Proof comment: after the partial sums stabilize, only the scalar prefactor `(√n)⁻¹` varies.
  rcases partialSumCoordinateProcess_eventually_constant ω hω with ⟨N, hN⟩
  let c : ℝ := partialSum coordinateProcess N ω
  have hinv :
      Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) := by
    have hsqrt :
        Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa [one_div] using tendsto_inv_atTop_zero.comp hsqrt
  have hconst :
      Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹ * c) atTop (𝓝 0) := by
    simpa [c, zero_mul] using hinv.mul_const c
  have heq :
      (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum coordinateProcess n ω) =ᶠ[atTop]
        fun n ↦ (Real.sqrt (n : ℝ))⁻¹ * c := by
    filter_upwards [hN] with n hn
    simp [c, hn]
  exact Tendsto.congr' heq.symm hconst

/-- Helper for Exercise 15.5.2: partial sums commute with pointwise addition. -/
private lemma partialSum_add
    {Ω' : Type*} [MeasurableSpace Ω'] (Y Z : ℕ → Ω' → ℝ) (n : ℕ) (ω : Ω') :
    partialSum (fun k ω' ↦ Y k ω' + Z k ω') n ω =
      partialSum Y n ω + partialSum Z n ω := by
  -- Proof comment: finite sums distribute over pointwise addition.
  simp [partialSum, Finset.sum_add_distrib]

/-- Helper for Exercise 15.5.2: the normalized rare-jump partial sums vanish in measure because
only finitely many nonzero jumps occur almost surely. -/
private theorem normalizedRareJumpPartialSum_tendstoInMeasureZero
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hZ_meas : ∀ n, Measurable (Z n))
    (hZ_law : ∀ n, HasLaw (Z n) (rareJumpLaw n) P) :
    TendstoInMeasure P
      (fun n : ℕ => fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum Z n ω)
      atTop (fun _ ↦ (0 : ℝ)) := by
  let A : ℕ → Set Ω := fun n ↦ {ω | Z n ω ≠ 0}
  have hA_prob : ∀ n, P (A n) = ENNReal.ofReal (1 / ((n + 1 : ℝ) ^ (2 : ℕ))) := by
    -- Proof comment: push the event `{Z n ≠ 0}` forward through the law of `Z n`.
    intro n
    calc
      P (A n) = (Measure.map (Z n) P) {x : ℝ | x ≠ 0} := by
        rw [show A n = (Z n) ⁻¹' {x : ℝ | x ≠ 0} by
          ext ω
          simp [A]]
        exact (Measure.map_apply (hZ_meas n) ((measurableSet_singleton (0 : ℝ)).compl)).symm
      _ = rareJumpLaw n {x : ℝ | x ≠ 0} := by
        simpa using congrArg (fun μ : Measure ℝ => μ {x : ℝ | x ≠ 0}) (hZ_law n).map_eq
      _ = ENNReal.ofReal (1 / ((n + 1 : ℝ) ^ (2 : ℕ))) := rareJumpLaw_nonzero_event n
  have hsquare : Summable (fun n : ℕ ↦ ((n : ℝ) ^ (2 : ℕ))⁻¹) := by
    -- Proof comment: the comparison series is the standard `p`-series with exponent `2`.
    exact Real.summable_nat_pow_inv.mpr (by norm_num)
  have hrare_summable : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) := by
    -- Proof comment: shift the `p`-series by one to match the textbook indexing.
    simpa using
      (summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ) ^ (2 : ℕ))⁻¹) 1).2 hsquare
  have hA_tsum_ne_top : (∑' n, P (A n)) ≠ ⊤ := by
    -- Proof comment: the nonzero-event probabilities are exactly the summable rare-jump weights.
    rw [show (fun n ↦ P (A n)) = fun n : ℕ ↦ ENNReal.ofReal (1 / ((n + 1 : ℝ) ^ (2 : ℕ))) by
      funext n
      exact hA_prob n]
    exact ne_of_lt hrare_summable.tsum_ofReal_lt_top
  have hAe_eventually_zero : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, Z n ω = 0 := by
    -- Proof comment: first Borel-Cantelli gives only finitely many nonzero rare jumps almost
    -- surely.
    filter_upwards
      [MeasureTheory.ae_eventually_notMem (μ := P) (s := A) hA_tsum_ne_top] with ω hω
    filter_upwards [hω] with n hn
    simpa [A] using hn
  have hRare_ae :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum Z n ω) atTop (𝓝 0) := by
    -- Proof comment: once the rare jumps vanish eventually, the normalized partial sums are the
    -- fixed terminal sum divided by `√n`.
    filter_upwards [hAe_eventually_zero] with ω hω
    simpa [partialSum, coordinateProcess] using
      normalizedRarePart_tendsto_zero_ae (fun k ↦ Z k ω) hω
  refine tendstoInMeasure_of_tendsto_ae ?_ hRare_ae
  intro n
  exact ((partialSum_measurable Z hZ_meas n).const_mul _).aestronglyMeasurable

section RareJumpPerturbedArray

variable (Y Z : ℕ → Ω → ℝ)
variable (hY_meas : ∀ n, Measurable (Y n)) (hZ_meas : ∀ n, Measurable (Z n))

/- Exercise 15.5.2 is `source-facing`: it studies the perturbed normalized sums
`n^{-1/2} ∑_{k < n} (Y_k + Z_k)`. The chapter's `core/canonical` owner for rowwise CLT and
Lindeberg data is `RealRandomVariableArray Ω`; the array below is the `bridge/view` packaging of
those source sums as row sums of an owner object. -/
/-- The `n`-th row consists of the first `n` perturbed summands `Y_k + Z_k`, each scaled by
`(√n)⁻¹`, so its row sum is the normalized textbook sum `n^{-1/2} ∑_{k < n} (Y_k + Z_k)`. -/
def rareJumpPerturbedStandardizedArray : RealRandomVariableArray Ω where
  rowLength n := n
  entry n i ω := (Y i.1 ω + Z i.1 ω) / Real.sqrt (n : ℝ)
  measurable_entry n i := by
    simpa using ((hY_meas i.1).add (hZ_meas i.1)).div_const (Real.sqrt (n : ℝ))

/-- The entries of the rare-jump perturbed standardized array are the scaled perturbed summands. -/
theorem rareJumpPerturbedStandardizedArray_apply (n : ℕ) (i : Fin n) (ω : Ω) :
    rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas n i ω =
      (Y i.1 ω + Z i.1 ω) / Real.sqrt (n : ℝ) :=
  rfl

/-- The entries of the rare-jump perturbed standardized array are measurable. -/
theorem measurable_rareJumpPerturbedStandardizedArray_entry (n : ℕ) (i : Fin n) :
    Measurable (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas n i) :=
  (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).measurable_entry n i

/-- Helper for Exercise 15.5.2: the `n`-th row sum is the normalized partial sum of the perturbed
sequence. -/
theorem rareJumpPerturbed_rowSum_eq_normalized_partialSum
    (n : ℕ) (ω : Ω) :
    (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).rowSum n ω =
      (Real.sqrt (n : ℝ))⁻¹ *
        partialSum (fun k ω' ↦ Y k ω' + Z k ω') n ω := by
  -- Proof comment: unfold the row-sum owner definition and rewrite the `Fin n` sum as `range n`.
  calc
    (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).rowSum n ω
      = ∑ i : Fin n, (Y i.1 ω + Z i.1 ω) * (Real.sqrt (n : ℝ))⁻¹ := by
          rw [RealRandomVariableArray.rowSum]
          simp [rareJumpPerturbedStandardizedArray, div_eq_mul_inv]
          rfl
    _ = ∑ x ∈ Finset.range n, (Y x ω + Z x ω) * (Real.sqrt (n : ℝ))⁻¹ := by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (fun x : ℕ ↦ (Y x ω + Z x ω) * (Real.sqrt (n : ℝ))⁻¹) n)
    _ = (Real.sqrt (n : ℝ))⁻¹ * ∑ x ∈ Finset.range n, (Y x ω + Z x ω) := by
          symm
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x hx ↦ ?_
          rw [mul_comm]
    _ = (Real.sqrt (n : ℝ))⁻¹ *
          partialSum (fun k ω' ↦ Y k ω' + Z k ω') n ω := by
          rfl

end RareJumpPerturbedArray

-- Proof sketch: the source hypotheses require not only that `Y` is i.i.d., but also that the
-- perturbation sequence `Z` is independent and independent of the whole sequence `Y`. The
-- rare-jump law `rareJumpLaw n` gives `∑ n, P[Z n ≠ 0] < ∞`, so Borel--Cantelli yields only
-- finitely many nonzero jumps almost surely. Hence the perturbation is asymptotically negligible
-- after dividing by `√n`, the row sums still converge weakly to the standard Gaussian law by the
-- iid CLT for `Y` and Slutsky, and the exceptional summands still violate the chapter-owner
-- Lindeberg condition.
/-- Helper for Exercise 15.5.2: the normalized perturbed row sums converge in law to
`𝒩(0, 1)`. -/
private theorem rareJumpPerturbed_rowSumLaw_tendstoGaussian
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : ℕ → Ω → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hZ_meas : ∀ n, Measurable (Z n))
    (hY_iid : IsIID Y P)
    (hY_mean : P[Y 0] = 0)
    (hY_var : Var[Y 0; P] = 1)
    (hZ_law : ∀ n, HasLaw (Z n) (rareJumpLaw n) P) :
    Tendsto
      (fun n ↦ (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).rowSumLaw P n)
      atTop
      (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) := by
  let A := rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas
  let coreSum : ℕ → Ω → ℝ := fun n ω ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum Y n ω
  let rareSum : ℕ → Ω → ℝ := fun n ω ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum Z n ω
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) P P := fun n ↦ hY_iid.identDistrib n 0
  have hY_indep : iIndepFun Y P := hY_iid.iIndepFun
  have hY_second : P[(Y 0) ^ (2 : ℕ)] = 1 := by
    calc
      P[(Y 0) ^ (2 : ℕ)] = Var[Y 0; P] := by
        symm
        rw [variance_eq_integral (hY_meas 0).aemeasurable, hY_mean]
        simp
      _ = 1 := hY_var
  have hCore :
      TendstoInDistribution coreSum atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    simpa [coreSum, partialSum] using
      (tendstoInDistribution_inv_sqrt_mul_sum
        (P := P) (P' := gaussianReal 0 1) (X := Y) (Y := id)
        HasLaw.id hY_mean hY_second hY_indep hY_ident)
  have hRare_tendsto :
      TendstoInMeasure P rareSum atTop (fun _ ↦ (0 : ℝ)) := by
    simpa [rareSum] using
      normalizedRareJumpPartialSum_tendstoInMeasureZero
        (P := P) (Z := Z) hZ_meas hZ_law
  have hRowEq :
      (fun n ↦ A.rowSum n) = fun n ω ↦ coreSum n ω + rareSum n ω := by
    funext n ω
    rw [rareJumpPerturbed_rowSum_eq_normalized_partialSum]
    rw [partialSum_add, mul_add]
  have hRowSumDist :
      TendstoInDistribution (fun n ↦ A.rowSum n) atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    rw [hRowEq]
    simpa [coreSum, rareSum] using
      hCore.add_of_tendstoInMeasure_const
        hRare_tendsto
        (fun n ↦ ((partialSum_measurable Z hZ_meas n).const_mul _).aemeasurable)
  exact
    (tendstoInDistribution_iff_tendsto_limit_law
      (X := fun n ↦ A.rowSum n) (l := atTop) (μ := fun _ ↦ P)
      (Z := id) (μ' := gaussianReal 0 1) (ν := ⟨gaussianReal 0 1, inferInstance⟩)
      (hX := fun n ↦ (A.measurable_rowSum n).aemeasurable) HasLaw.id).1 hRowSumDist

/-- Helper for Exercise 15.5.2: the normalized perturbed row sums have variance `2` from row
`8` onward. -/
private theorem rareJumpPerturbed_rowSumVariance_eq_two
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : ℕ → Ω → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hZ_meas : ∀ n, Measurable (Z n))
    (hY_iid : IsIID Y P)
    (hZ_indep : iIndepFun Z P)
    (hYZ_indep : IndepFun (fun ω ↦ fun n : ℕ ↦ Y n ω) (fun ω ↦ fun n : ℕ ↦ Z n ω) P)
    (hY_var : Var[Y 0; P] = 1)
    (hZ_law : ∀ n, HasLaw (Z n) (rareJumpLaw n) P)
    {n : ℕ} (hn8 : 8 ≤ n) :
    Var[(rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).rowSum n; P] = 2 := by
  let A := rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas
  let coreSum : ℕ → Ω → ℝ := fun m ω ↦ (Real.sqrt (m : ℝ))⁻¹ * partialSum Y m ω
  let rareSum : ℕ → Ω → ℝ := fun m ω ↦ (Real.sqrt (m : ℝ))⁻¹ * partialSum Z m ω
  have hY_ident : ∀ m, IdentDistrib (Y m) (Y 0) P P := fun m ↦ hY_iid.identDistrib m 0
  have hY_indep : iIndepFun Y P := hY_iid.iIndepFun
  have hY0_memLp_two : MemLp (Y 0) 2 P := by
    refine memLp_two_of_variance_ne_zero (hY_meas 0).aestronglyMeasurable ?_
    linarith
  have hcoreVar : ∀ {m : ℕ}, 0 < m → Var[coreSum m; P] = 1 := by
    intro m hm
    have hrow :
        (iid_standardized_array Y hY_meas).rowSum (m - 1) = coreSum m := by
      funext ω
      have hpredNat : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
      have hpredCast : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        exact_mod_cast hpredNat
      have hsqrt : Real.sqrt (((m - 1 : ℕ) : ℝ) + 1) = Real.sqrt (m : ℝ) := by
        rw [hpredCast]
      calc
        (iid_standardized_array Y hY_meas).rowSum (m - 1) ω
            = ∑ x ∈ Finset.range (m - 1 + 1), Y x ω * (Real.sqrt (m : ℝ))⁻¹ := by
                rw [RealRandomVariableArray.rowSum]
                simp [iid_standardized_array, div_eq_mul_inv, hsqrt]
                simpa using
                  (Fin.sum_univ_eq_sum_range
                    (fun x : ℕ ↦ Y x ω * (Real.sqrt (m : ℝ))⁻¹) (m - 1 + 1))
        _ = ∑ x ∈ Finset.range m, Y x ω * (Real.sqrt (m : ℝ))⁻¹ := by
              simp [hpredNat]
        _ = (Real.sqrt (m : ℝ))⁻¹ * ∑ x ∈ Finset.range m, Y x ω := by
              symm
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x hx ↦ ?_
              rw [mul_comm]
        _ = coreSum m ω := rfl
    rw [← hrow]
    simpa [hY_var] using
      iidStandardizedArray_rowSumVariance
        (Y := Y) (hY_meas := hY_meas) (P := P)
        hY_indep hY_ident hY0_memLp_two (m - 1)
  have hrareVar : ∀ {m : ℕ}, 0 < m → Var[rareSum m; P] = 1 := by
    intro m hm
    let W : Fin m → Ω → ℝ := fun i ω ↦ Z i.1 ω / Real.sqrt (m : ℝ)
    have hW_indep : iIndepFun W P := by
      let hrow : iIndepFun (fun i : Fin m ↦ Z i.1) P := hZ_indep.precomp Fin.val_injective
      simpa [W] using
        hrow.comp (fun _ x ↦ x / Real.sqrt (m : ℝ))
          (fun _ ↦ measurable_id.div_const (Real.sqrt (m : ℝ)))
    have hW_mem : ∀ i : Fin m, MemLp (W i) 2 P := by
      intro i
      have hZi_mem : MemLp (Z i.1) 2 P := by
        simpa using
          (((hZ_law i.1).identDistrib HasLaw.id).memLp_iff.2 (rareJumpLawMoments i.1).1)
      simpa [W, div_eq_mul_inv] using hZi_mem.mul_const ((Real.sqrt (m : ℝ))⁻¹)
    have hW_pairwise :
        Set.Pairwise (↑(Finset.univ : Finset (Fin m))) (fun i j ↦ W i ⟂ᵢ[P] W j) := by
      intro i _ j _ hij
      exact hW_indep.indepFun hij
    have hsum' : Var[∑ i, W i; P] = ∑ i : Fin m, Var[W i; P] := by
      simpa using
        ProbabilityTheory.IndepFun.variance_sum
          (μ := P) (X := W) (s := Finset.univ) (hs := fun i _ ↦ hW_mem i) hW_pairwise
    have hvar_each : ∀ i : Fin m, Var[W i; P] = 1 / (m : ℝ) := by
      intro i
      have hZi_var : Var[Z i.1; P] = 1 := by
        rw [(hZ_law i.1).variance_eq]
        exact (rareJumpLawMoments i.1).2.2
      have hsqrt_sq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = m := by
        have hm_nonneg : 0 ≤ (m : ℝ) := by
          positivity
        nlinarith [Real.sq_sqrt hm_nonneg]
      have hinv_sq : (Real.sqrt (m : ℝ))⁻¹ ^ (2 : ℕ) = 1 / (m : ℝ) := by
        rw [inv_pow, pow_two, hsqrt_sq]
        simp [one_div]
      calc
        Var[W i; P] = Var[Z i.1; P] * (Real.sqrt (m : ℝ))⁻¹ ^ (2 : ℕ) := by
          simpa [W, div_eq_mul_inv] using
            (variance_mul_const ((Real.sqrt (m : ℝ))⁻¹) (Z i.1) P)
        _ = 1 / (m : ℝ) := by
              rw [hZi_var, hinv_sq]
              ring
    have hrow :
        (fun ω ↦ ∑ i : Fin m, W i ω) = rareSum m := by
      funext ω
      calc
        ∑ i : Fin m, W i ω
            = ∑ x ∈ Finset.range m, Z x ω * (Real.sqrt (m : ℝ))⁻¹ := by
                simpa [W, div_eq_mul_inv] using
                  (Fin.sum_univ_eq_sum_range
                    (fun x : ℕ ↦ Z x ω * (Real.sqrt (m : ℝ))⁻¹) m)
        _ = (Real.sqrt (m : ℝ))⁻¹ * ∑ x ∈ Finset.range m, Z x ω := by
              symm
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x hx ↦ ?_
              rw [mul_comm]
        _ = rareSum m ω := rfl
    have hsum_fn : (fun ω ↦ ∑ i : Fin m, W i ω) = ∑ i : Fin m, W i := by
      funext ω
      simp [Finset.sum_apply]
    rw [← hrow]
    calc
      Var[(fun ω ↦ ∑ i : Fin m, W i ω); P] = Var[∑ i : Fin m, W i; P] := by
        rw [hsum_fn]
      _ = ∑ i : Fin m, Var[W i; P] := hsum'
      _ = ∑ i : Fin m, 1 / (m : ℝ) := by
            refine Finset.sum_congr rfl fun i hi ↦ hvar_each i
      _ = 1 := by
          have hm' : (m : ℝ) ≠ 0 := by
            exact_mod_cast hm.ne'
          simp [hm', div_eq_mul_inv]
  have hcoreRare_indep : ∀ {m : ℕ}, 0 < m → coreSum m ⟂ᵢ[P] rareSum m := by
    intro m hm
    let φ : (ℕ → ℝ) → ℝ := fun f ↦ (Real.sqrt (m : ℝ))⁻¹ * partialSum coordinateProcess m f
    have hφ : Measurable φ := by
      simpa [φ, coordinateProcess] using
        ((partialSum_measurable coordinateProcess (fun k ↦ measurable_pi_apply k) m).const_mul _)
    simpa [coreSum, rareSum, φ, coordinateProcess] using hYZ_indep.comp hφ hφ
  have hn : 0 < n := by
    omega
  have hrow :
      A.rowSum n = fun ω ↦ coreSum n ω + rareSum n ω := by
    funext ω
    rw [rareJumpPerturbed_rowSum_eq_normalized_partialSum]
    rw [partialSum_add, mul_add]
  have hcore_mem : MemLp (coreSum n) 2 P := by
    refine memLp_two_of_variance_ne_zero
      (((partialSum_measurable Y hY_meas n).const_mul _).aestronglyMeasurable) ?_
    rw [hcoreVar hn]
    norm_num
  have hrare_mem : MemLp (rareSum n) 2 P := by
    refine memLp_two_of_variance_ne_zero
      (((partialSum_measurable Z hZ_meas n).const_mul _).aestronglyMeasurable) ?_
    rw [hrareVar hn]
    norm_num
  rw [hrow]
  calc
    Var[(fun ω ↦ coreSum n ω + rareSum n ω); P]
        = Var[coreSum n; P] + Var[rareSum n; P] := by
            exact (hcoreRare_indep hn).variance_add hcore_mem hrare_mem
    _ = 2 := by
          rw [hcoreVar hn, hrareVar hn]
          norm_num

/-- Helper for Exercise 15.5.2: every standardized perturbed entry belongs to `L²`. -/
private theorem rareJumpPerturbedEntry_memLpTwo
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : ℕ → Ω → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_iid : IsIID Y P)
    (hY_var : Var[Y 0; P] = 1)
    (hZ_law : ∀ n, HasLaw (Z n) (rareJumpLaw n) P)
    (n k : ℕ) :
    MemLp (fun ω ↦ ((Y k ω + Z k ω) / Real.sqrt (n : ℝ))) 2 P := by
  have hY0_memLp_two : MemLp (Y 0) 2 P := by
    -- Proof comment: the variance normalization on `Y₀` gives the needed `L²` control.
    refine memLp_two_of_variance_ne_zero (hY_meas 0).aestronglyMeasurable ?_
    linarith
  have hYk_memLp_two : MemLp (Y k) 2 P := by
    -- Proof comment: i.i.d. transfers `L²` from the first coordinate to every `Y_k`.
    simpa using ((hY_iid.identDistrib k 0).memLp_iff.2 hY0_memLp_two)
  have hZk_memLp_two : MemLp (Z k) 2 P := by
    -- Proof comment: transport the rare-jump `L²` moment along the `HasLaw` hypothesis.
    simpa using
      (((hZ_law k).identDistrib HasLaw.id).memLp_iff.2 (rareJumpLawMoments k).1)
  -- Proof comment: sums and deterministic scalings preserve membership in `L²`.
  simpa [div_eq_mul_inv] using
    (hYk_memLp_two.add hZk_memLp_two).mul_const ((Real.sqrt (n : ℝ))⁻¹)

/-- Helper for Exercise 15.5.2: the support event `{|Y_k| < 2} ∩ {|Z_k| = k + 1}` has
probability at least `(3 / 4) * (k + 1)⁻²`. -/
private theorem rareJumpPerturbedSupportEventProbLowerBound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : ℕ → Ω → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hZ_meas : ∀ n, Measurable (Z n))
    (hY_iid : IsIID Y P)
    (hYZ_indep : IndepFun (fun ω ↦ fun n : ℕ ↦ Y n ω) (fun ω ↦ fun n : ℕ ↦ Z n ω) P)
    (hY_mean : P[Y 0] = 0)
    (hY_var : Var[Y 0; P] = 1)
    (hZ_law : ∀ n, HasLaw (Z n) (rareJumpLaw n) P)
    (k : ℕ) :
    ENNReal.ofReal ((3 / 4 : ℝ) * (1 / ((k + 1 : ℝ) ^ (2 : ℕ)))) ≤
      P ((Y k) ⁻¹' Set.Ioo (-2) 2 ∩ (Z k) ⁻¹' {x : ℝ | |x| = (k + 1 : ℝ)}) := by
  let C : Set Ω := (Y k) ⁻¹' Set.Ioo (-2) 2
  let D : Set Ω := (Z k) ⁻¹' {x : ℝ | |x| = (k + 1 : ℝ)}
  let B : Set Ω := C ∩ D
  have hY_ident : ∀ m, IdentDistrib (Y m) (Y 0) P P := fun m ↦ hY_iid.identDistrib m 0
  have hY0_memLp_two : MemLp (Y 0) 2 P := by
    -- Proof comment: the variance hypothesis makes the reference coordinate square integrable.
    refine memLp_two_of_variance_ne_zero (hY_meas 0).aestronglyMeasurable ?_
    linarith
  have hY_mean_all : ∀ m, P[Y m] = 0 := by
    -- Proof comment: the i.i.d. family shares the same mean across coordinates.
    intro m
    rw [(hY_ident m).integral_eq, hY_mean]
  have hY_var_all : ∀ m, Var[Y m; P] = 1 := by
    -- Proof comment: the i.i.d. family also shares the same variance.
    intro m
    rw [(hY_ident m).variance_eq, hY_var]
  have hC_meas : MeasurableSet C := by
    -- Proof comment: the interval event is measurable because `Y_k` is measurable.
    dsimp [C]
    measurability
  have htail : P Cᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
    have hYi_mem : MemLp (Y k) 2 P := by
      simpa using ((hY_ident k).memLp_iff.2 hY0_memLp_two)
    have htail' : P {ω | (2 : ℝ) ≤ |Y k ω|} ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
      -- Proof comment: Chebyshev controls the complement of `|Y_k| < 2`.
      calc
        P {ω | (2 : ℝ) ≤ |Y k ω|} = P {ω | (2 : ℝ) ≤ |Y k ω - P[Y k]|} := by
          simp [hY_mean_all k]
        _ ≤ ENNReal.ofReal (Var[Y k; P] / (2 : ℝ) ^ (2 : ℕ)) := by
          exact meas_ge_le_variance_div_sq hYi_mem (by norm_num)
        _ = ENNReal.ofReal (1 / 4 : ℝ) := by
          rw [hY_var_all k]
          norm_num
    have hcompl : Cᶜ = {ω | (2 : ℝ) ≤ |Y k ω|} := by
      -- Proof comment: rewrite the interval complement into the absolute-value tail event.
      ext ω
      constructor
      · intro hω
        by_contra hω'
        apply hω
        have habs_lt : |Y k ω| < 2 := lt_of_not_ge hω'
        simpa [C, abs_lt] using habs_lt
      · intro hω
        intro hCω
        have habs_lt : |Y k ω| < 2 := by
          simpa [C, abs_lt] using hCω
        exact not_lt_of_ge hω habs_lt
    simpa [hcompl] using htail'
  have hC_prob : ENNReal.ofReal (3 / 4 : ℝ) ≤ P C := by
    -- Proof comment: complement control turns into a lower bound for `P(C)`.
    have hprobC : P C = 1 - P Cᶜ := by
      simpa using (prob_compl_eq_one_sub (μ := P) (s := Cᶜ) hC_meas.compl)
    have htail_real : P.real Cᶜ ≤ 1 / 4 := by
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      simpa using htail
    have hprobC_real : P.real C = 1 - P.real Cᶜ := by
      simpa [measureReal_def,
        ENNReal.toReal_sub_of_le (by simpa using prob_le_one (μ := P) (s := Cᶜ))] using
        congrArg ENNReal.toReal hprobC
    have hC_real : 3 / 4 ≤ P.real C := by
      rw [hprobC_real]
      nlinarith
    exact (ENNReal.ofReal_le_iff_le_toReal (by simp)).2 hC_real
  have hD_prob : P D = ENNReal.ofReal (1 / ((k + 1 : ℝ) ^ (2 : ℕ))) := by
    -- Proof comment: the `HasLaw` hypothesis identifies the absolute-value shell probability.
    calc
      P D = (Measure.map (Z k) P) {x : ℝ | |x| = (k + 1 : ℝ)} := by
        rw [show D = (Z k) ⁻¹' {x : ℝ | |x| = (k + 1 : ℝ)} by rfl]
        exact (Measure.map_apply (hZ_meas k) (by measurability)).symm
      _ = rareJumpLaw k {x : ℝ | |x| = (k + 1 : ℝ)} := by
        simpa using
          congrArg (fun μ : Measure ℝ => μ {x : ℝ | |x| = (k + 1 : ℝ)}) (hZ_law k).map_eq
      _ = ENNReal.ofReal (1 / ((k + 1 : ℝ) ^ (2 : ℕ))) := rareJumpLaw_abs_eq_event k
  have hcoord_indep : Y k ⟂ᵢ[P] Z k := by
    -- Proof comment: independence of the full coordinate processes specializes to one index.
    simpa using hYZ_indep.comp (measurable_pi_apply k) (measurable_pi_apply k)
  have hB_prob :
      ENNReal.ofReal ((3 / 4 : ℝ) * (1 / ((k + 1 : ℝ) ^ (2 : ℕ)))) ≤ P B := by
    -- Proof comment: multiply the one-coordinate lower bounds through independence.
    have hD_le : ENNReal.ofReal (1 / ((k + 1 : ℝ) ^ (2 : ℕ))) ≤ P D := by
      rw [hD_prob]
    have hmul :
        ENNReal.ofReal (3 / 4 : ℝ) * ENNReal.ofReal (1 / ((k + 1 : ℝ) ^ (2 : ℕ))) ≤
          P C * P D := by
      exact mul_le_mul' hC_prob hD_le
    have hinter : P B = P C * P D := by
      simpa [B, C, D] using
        hcoord_indep.measure_inter_preimage_eq_mul
          (Set.Ioo (-2) 2) {x : ℝ | |x| = (k + 1 : ℝ)} measurableSet_Ioo (by measurability)
    have hofReal_mul :
        ENNReal.ofReal ((3 / 4 : ℝ) * (1 / ((k + 1 : ℝ) ^ (2 : ℕ)))) =
          ENNReal.ofReal (3 / 4 : ℝ) * ENNReal.ofReal (1 / ((k + 1 : ℝ) ^ (2 : ℕ))) := by
      rw [ENNReal.ofReal_mul]
      positivity
    have hmul' :
        ENNReal.ofReal ((3 / 4 : ℝ) * (1 / ((k + 1 : ℝ) ^ (2 : ℕ)))) ≤ P C * P D := by
      calc
        ENNReal.ofReal ((3 / 4 : ℝ) * (1 / ((k + 1 : ℝ) ^ (2 : ℕ))))
            = ENNReal.ofReal (3 / 4 : ℝ) * ENNReal.ofReal (1 / ((k + 1 : ℝ) ^ (2 : ℕ))) := by
                rw [hofReal_mul]
        _ ≤ P C * P D := hmul
    rw [hinter]
    exact hmul'
  simpa [B, C, D] using hB_prob

/-- Helper for Exercise 15.5.2: on the support event `{|Y_k| < 2} ∩ {|Z_k| = k + 1}`, the
truncated square of the standardized perturbed entry is bounded below by `((k + 1)^2) / (4 n)`. -/
private theorem rareJumpPerturbedSupportEventIndicatorLowerBound
    (Y Z : ℕ → Ω → ℝ)
    {n k : ℕ} (hn8 : 8 ≤ n) (hk : k ∈ Finset.Icc (n / 2) (n - 1))
    {ω : Ω}
    (hω :
      ω ∈ (Y k) ⁻¹' Set.Ioo (-2) 2 ∩ (Z k) ⁻¹' {x : ℝ | |x| = (k + 1 : ℝ)}) :
    ((k + 1 : ℝ) ^ (2 : ℕ)) / (4 * n) ≤
      Set.indicator
        {ω | (1 / 32 : ℝ) < ((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ)}
        (fun ω ↦ ((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ)) ω := by
  have hYopen : -2 < Y k ω ∧ Y k ω < 2 := by
    -- Proof comment: unpack the `|Y_k| < 2` component of the support event.
    simpa [abs_lt] using hω.1
  have hYabs : |Y k ω| < 2 := by
    simpa [abs_lt] using hYopen
  have hZabs : |Z k ω| = (k + 1 : ℝ) := by
    -- Proof comment: the second component of the support event fixes the absolute jump size.
    simpa using hω.2
  have hk_half_nat : n / 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk_small : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
  have hk_bound : (n : ℝ) ≤ 2 * (k + 1 : ℝ) := by
    have hk_bound_nat : n ≤ 2 * (k + 1) := by
      omega
    exact_mod_cast hk_bound_nat
  have hk_four : (4 : ℝ) ≤ k := by
    have hk_four_nat : 4 ≤ k := by
      have hhalf_four : 4 ≤ n / 2 := by
        omega
      omega
    exact_mod_cast hk_four_nat
  have hn' : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have htriangle : |Z k ω| ≤ |Y k ω + Z k ω| + |Y k ω| := by
    -- Proof comment: isolate the large `Z_k` jump from the perturbation `Y_k` via the triangle inequality.
    simpa [abs_neg, add_comm, add_left_comm, add_assoc] using
      (abs_add_le (Y k ω + Z k ω) (-Y k ω))
  have habs : ((k + 1 : ℝ) / 2) < |Y k ω + Z k ω| := by
    -- Proof comment: the large jump dominates because the perturbation is bounded by `2`.
    nlinarith [htriangle, hYabs, hZabs, hk_four]
  have hc_lt :
      ((k + 1 : ℝ) ^ (2 : ℕ)) / (4 * n) <
        ((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ) := by
    have habs_sq : (((k + 1 : ℝ) / 2) ^ (2 : ℕ)) < |Y k ω + Z k ω| ^ (2 : ℕ) := by
      nlinarith [habs, abs_nonneg (Y k ω + Z k ω)]
    have hsq : (((k + 1 : ℝ) / 2) ^ (2 : ℕ)) < (Y k ω + Z k ω) ^ (2 : ℕ) := by
      simpa [sq_abs] using habs_sq
    have hsqrt_sq : Real.sqrt (n : ℝ) ^ (2 : ℕ) = n := by
      have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
      simpa [pow_two] using Real.sq_sqrt hn_nonneg
    have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show 0 < n by omega).ne'
    rw [div_pow, hsqrt_sq]
    field_simp [hn_ne]
    nlinarith
  have hthreshold :
      (1 / 32 : ℝ) < ((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ) := by
    -- Proof comment: middle-half indices make the previous lower bound larger than the fixed threshold.
    have hk_half : (n : ℝ) / 2 ≤ k + 1 := by
      nlinarith [hk_bound]
    have hc_big : (1 / 32 : ℝ) < ((k + 1 : ℝ) ^ (2 : ℕ)) / (4 * n) := by
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (show 0 < n by omega).ne'
      field_simp [hn_ne]
      nlinarith [hk_half, hn']
    exact lt_trans hc_big hc_lt
  -- Proof comment: once the threshold event is known, the indicator opens up to the square itself.
  change ((k + 1 : ℝ) ^ (2 : ℕ)) / (4 * n) ≤
    ite (((1 / 32 : ℝ) < ((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ)))
      (((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ)) 0
  rw [if_pos hthreshold]
  exact hc_lt.le

/-- Helper for Exercise 15.5.2: each summand in the middle half of a row contributes at least
`3 / (16 n)` to the Lindeberg truncated second-moment sum. -/
private theorem rareJumpPerturbed_lindebergTermLowerBound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : ℕ → Ω → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hZ_meas : ∀ n, Measurable (Z n))
    (hY_iid : IsIID Y P)
    (hYZ_indep : IndepFun (fun ω ↦ fun n : ℕ ↦ Y n ω) (fun ω ↦ fun n : ℕ ↦ Z n ω) P)
    (hY_mean : P[Y 0] = 0)
    (hY_var : Var[Y 0; P] = 1)
    (hZ_law : ∀ n, HasLaw (Z n) (rareJumpLaw n) P)
    {n k : ℕ} (hn8 : 8 ≤ n) (hk : k ∈ Finset.Icc (n / 2) (n - 1)) :
    3 / (16 * n : ℝ) ≤
      ∫ ω, Set.indicator
        {ω | (1 / 32 : ℝ) < ((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ)}
        (fun ω ↦ ((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ)) ω ∂P := by
  let entry : Ω → ℝ := fun ω ↦ ((Y k ω + Z k ω) / Real.sqrt (n : ℝ))
  let B : Set Ω := (Y k) ⁻¹' Set.Ioo (-2) 2 ∩ (Z k) ⁻¹' {x : ℝ | |x| = (k + 1 : ℝ)}
  let E : Set Ω := {ω | (1 / 32 : ℝ) < entry ω ^ (2 : ℕ)}
  let c : ℝ := ((k + 1 : ℝ) ^ (2 : ℕ)) / (4 * n)
  have hB_meas : MeasurableSet B := by
    -- Proof comment: both support constraints are measurable, hence so is their intersection.
    dsimp [B]
    measurability
  have hE_meas : MeasurableSet E := by
    -- Proof comment: the truncation event is measurable because the entry map is measurable.
    have hEntry_meas : Measurable entry := by
      dsimp [entry]
      exact ((hY_meas k).add (hZ_meas k)).div_const (Real.sqrt (n : ℝ))
    dsimp [E]
    exact measurableSet_lt measurable_const (hEntry_meas.pow_const 2)
  have hc_nonneg : 0 ≤ c := by
    -- Proof comment: the deterministic comparison constant is nonnegative.
    dsimp [c]
    positivity
  have hB_prob_real :
      (3 / 4 : ℝ) * (1 / ((k + 1 : ℝ) ^ (2 : ℕ))) ≤ P.real B := by
    have hB_prob :
        ENNReal.ofReal ((3 / 4 : ℝ) * (1 / ((k + 1 : ℝ) ^ (2 : ℕ)))) ≤ P B := by
      simpa [B] using
        rareJumpPerturbedSupportEventProbLowerBound
          (P := P) (Y := Y) (Z := Z) hY_meas hZ_meas hY_iid hYZ_indep hY_mean hY_var hZ_law k
    exact (ENNReal.ofReal_le_iff_le_toReal (by simp)).1 hB_prob
  have hleft_int : Integrable (Set.indicator B (fun _ : Ω ↦ c)) P := by
    -- Proof comment: indicators of measurable sets preserve integrability of constants.
    exact (integrable_const c).indicator hB_meas
  have hEntry_mem : MemLp entry 2 P := by
    -- Proof comment: use the dedicated entrywise `L²` lemma instead of the global Lindeberg hypothesis.
    simpa [entry] using
      rareJumpPerturbedEntry_memLpTwo
        (P := P) (Y := Y) (Z := Z) hY_meas hY_iid hY_var hZ_law n k
  have hright_int : Integrable (Set.indicator E (fun ω ↦ entry ω ^ (2 : ℕ))) P := by
    -- Proof comment: square integrability of the entry yields integrability of the truncated square.
    exact hEntry_mem.integrable_sq.indicator hE_meas
  have hmono :
      ∀ᵐ ω ∂P, Set.indicator B (fun _ : Ω ↦ c) ω ≤ Set.indicator E (fun ω ↦ entry ω ^ (2 : ℕ)) ω := by
    -- Proof comment: on `B` we use the deterministic lower bound, and off `B` the left indicator vanishes.
    filter_upwards [] with ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      exact
        rareJumpPerturbedSupportEventIndicatorLowerBound
          (Y := Y) (Z := Z) hn8 hk (by simpa [B] using hω)
    · rw [Set.indicator_of_notMem hω]
      by_cases hωE : ω ∈ E
      · rw [Set.indicator_of_mem hωE]
        positivity
      · rw [Set.indicator_of_notMem hωE]
  have hconst_le :
      c * P.real B ≤ ∫ ω, Set.indicator E (fun ω ↦ entry ω ^ (2 : ℕ)) ω ∂P := by
    -- Proof comment: compare the target integral with the constant lower bound on `B`.
    calc
      c * P.real B = ∫ ω, Set.indicator B (fun _ : Ω ↦ c) ω ∂P := by
        simpa [c, B, mul_comm] using (integral_indicator_const c hB_meas).symm
      _ ≤ ∫ ω, Set.indicator E (fun ω ↦ entry ω ^ (2 : ℕ)) ω ∂P := by
          exact integral_mono_ae hleft_int hright_int hmono
  have hprob_bound : 3 / (16 * n : ℝ) ≤ c * P.real B := by
    -- Proof comment: combine the probability lower bound for `B` with the deterministic constant `c`.
    have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show 0 < n by omega).ne'
    have hmul := mul_le_mul_of_nonneg_left hB_prob_real hc_nonneg
    have hconst :
        c * ((3 / 4 : ℝ) * (1 / ((k + 1 : ℝ) ^ (2 : ℕ)))) = 3 / (16 * n : ℝ) := by
      dsimp [c]
      field_simp [hn_ne, show ((k + 1 : ℝ) ^ (2 : ℕ)) ≠ 0 by positivity]
      ring
    rw [← hconst]
    exact hmul
  -- Proof comment: chaining the probability estimate with the integral comparison gives the desired term bound.
  exact le_trans hprob_bound hconst_le

/-- Helper for Exercise 15.5.2: the perturbed array's Lindeberg function stays uniformly away
from `0` along the tail. -/
private theorem rareJumpPerturbed_lindebergLowerBound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : ℕ → Ω → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hZ_meas : ∀ n, Measurable (Z n))
    (hY_iid : IsIID Y P)
    (hZ_indep : iIndepFun Z P)
    (hYZ_indep : IndepFun (fun ω ↦ fun n : ℕ ↦ Y n ω) (fun ω ↦ fun n : ℕ ↦ Z n ω) P)
    (hY_mean : P[Y 0] = 0)
    (hY_var : Var[Y 0; P] = 1)
    (hZ_law : ∀ n, HasLaw (Z n) (rareJumpLaw n) P) :
    ∀ᶠ n in atTop,
      3 / 64 ≤
        (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).lindebergFunction P (1 / 8) n := by
  let A := rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas
  refine Filter.eventually_atTop.2 ⟨8, fun n hn8 ↦ ?_⟩
  let term : ℕ → ℝ := fun k ↦
    ∫ ω, Set.indicator
      {ω | (1 / 32 : ℝ) < ((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ)}
      (fun ω ↦ ((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ)) ω ∂P
  have hterm_nonneg : ∀ k, 0 ≤ term k := by
    intro k
    refine integral_nonneg fun ω ↦ ?_
    change
      0 ≤
        ite ((1 / 32 : ℝ) < ((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ))
          (((Y k ω + Z k ω) / Real.sqrt (n : ℝ)) ^ (2 : ℕ)) 0
    split_ifs <;> positivity
  have hsum_Icc :
      Finset.sum (Finset.Icc (n / 2) (n - 1)) (fun _ : ℕ ↦ 3 / (16 * n : ℝ)) ≤
        Finset.sum (Finset.Icc (n / 2) (n - 1)) term := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    exact
      rareJumpPerturbed_lindebergTermLowerBound
        (P := P) (Y := Y) (Z := Z) hY_meas hZ_meas hY_iid hYZ_indep hY_mean hY_var hZ_law
        hn8 hk
  have hsubset : Finset.Icc (n / 2) (n - 1) ⊆ Finset.range n := by
    intro k hk
    have hk_upper : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
    have hn_pos : 0 < n := by omega
    exact Finset.mem_range.mpr (by omega)
  have hsum_subset :
      Finset.sum (Finset.Icc (n / 2) (n - 1)) term ≤ Finset.sum (Finset.range n) term := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun k hk hnot ↦ hterm_nonneg k)
  have hcard : (Finset.Icc (n / 2) (n - 1)).card = n - n / 2 := by
    rw [Nat.card_Icc]
    omega
  have hsum_const :
      Finset.sum (Finset.Icc (n / 2) (n - 1)) (fun _ : ℕ ↦ 3 / (16 * n : ℝ)) =
        (((n - n / 2 : ℕ) : ℝ) * (3 / (16 * n : ℝ))) := by
    simp [Finset.sum_const, hcard, nsmul_eq_mul]
  have hn' : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hmain : 3 / 64 ≤ (1 / 2 : ℝ) * Finset.sum (Finset.range n) term := by
    have hcount :
        (((n - n / 2 : ℕ) : ℝ) * (3 / (16 * n : ℝ))) ≤ Finset.sum (Finset.range n) term := by
      have hsum_Icc' :
          (((n - n / 2 : ℕ) : ℝ) * (3 / (16 * n : ℝ))) ≤ (Finset.Icc (n / 2) (n - 1)).sum term := by
        rw [← hsum_const]
        exact hsum_Icc
      exact le_trans hsum_Icc' (by simpa using hsum_subset)
    have hhalf : (3 / 32 : ℝ) ≤ ((n - n / 2 : ℕ) : ℝ) * (3 / (16 * n : ℝ)) := by
      have hn_ge_nat : n ≤ 2 * (n - n / 2) := by
        omega
      have hn_ge : (n : ℝ) / 2 ≤ ((n - n / 2 : ℕ) : ℝ) := by
        have hdouble : (n : ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by
          exact_mod_cast hn_ge_nat
        nlinarith
      have hfactor_nonneg : 0 ≤ 3 / (16 * n : ℝ) := by positivity
      have hscaled :
          (n : ℝ) / 2 * (3 / (16 * n : ℝ)) ≤ ((n - n / 2 : ℕ) : ℝ) * (3 / (16 * n : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hn_ge hfactor_nonneg
      have hmul : (n : ℝ) / 2 * (3 / (16 * n : ℝ)) = (3 / 32 : ℝ) := by
        have hn_ne : (n : ℝ) ≠ 0 := by
          exact_mod_cast (show 0 < n by omega).ne'
        field_simp [hn_ne]
        ring
      rw [← hmul]
      exact hscaled
    nlinarith
  have hsum_basic :
      (∑ i : Fin (A.rowLength n),
          ∫ ω, Set.indicator
            {ω | (1 / 32 : ℝ) < (A n i ω) ^ (2 : ℕ)}
            (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω ∂P
        ) = Finset.sum (Finset.range n) term := by
    simpa [A, term, rareJumpPerturbedStandardizedArray_apply, pow_two] using
      (Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ term k) n)
  have hsum_eq_two :
      (∑ i : Fin (A.rowLength n),
          ∫ ω, Set.indicator
            {ω | (1 / 8 : ℝ) ^ (2 : ℕ) * 2 < (A n i ω) ^ (2 : ℕ)}
            (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω ∂P
        ) = Finset.sum (Finset.range n) term := by
    have hthreshold : (1 / 8 : ℝ) ^ (2 : ℕ) * 2 = 1 / 32 := by
      norm_num
    have hterm_eq :
        ∀ i : Fin (A.rowLength n),
          ∫ ω, Set.indicator
            {ω | (1 / 8 : ℝ) ^ (2 : ℕ) * 2 < (A n i ω) ^ (2 : ℕ)}
            (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω ∂P =
            ∫ ω, Set.indicator
              {ω | (1 / 32 : ℝ) < (A n i ω) ^ (2 : ℕ)}
              (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω ∂P := by
      intro i
      refine integral_congr_ae ?_
      filter_upwards [] with ω
      rw [hthreshold]
    calc
      (∑ i : Fin (A.rowLength n),
          ∫ ω, Set.indicator
            {ω | (1 / 8 : ℝ) ^ (2 : ℕ) * 2 < (A n i ω) ^ (2 : ℕ)}
            (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω ∂P)
          =
            ∑ i : Fin (A.rowLength n),
              ∫ ω, Set.indicator
                {ω | (1 / 32 : ℝ) < (A n i ω) ^ (2 : ℕ)}
                (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω ∂P := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hterm_eq i
      _ = Finset.sum (Finset.range n) term := hsum_basic
  calc
    3 / 64 ≤ (1 / 2 : ℝ) * Finset.sum (Finset.range n) term := hmain
    _ = A.lindebergFunction P (1 / 8) n := by
          rw [RealRandomVariableArray.lindebergFunction_def]
          rw [rareJumpPerturbed_rowSumVariance_eq_two
            (P := P) (Y := Y) (Z := Z) hY_meas hZ_meas hY_iid hZ_indep hYZ_indep hY_var hZ_law
            hn8]
          rw [hsum_eq_two]
          norm_num

/-- Helper for Exercise 15.5.2: the rare jumps force a uniform positive lower bound on the
Lindeberg function, so the perturbed array is not Lindeberg. -/
private theorem rareJumpPerturbed_notSatisfiesLindeberg
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : ℕ → Ω → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hZ_meas : ∀ n, Measurable (Z n))
    (hY_iid : IsIID Y P)
    (hZ_indep : iIndepFun Z P)
    (hYZ_indep : IndepFun (fun ω ↦ fun n : ℕ ↦ Y n ω) (fun ω ↦ fun n : ℕ ↦ Z n ω) P)
    (hY_mean : P[Y 0] = 0)
    (hY_var : Var[Y 0; P] = 1)
    (hZ_law : ∀ n, HasLaw (Z n) (rareJumpLaw n) P) :
    ¬ (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).SatisfiesLindebergCondition P := by
  let A := rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas
  intro hL
  have hlower :
      ∀ᶠ n in atTop, 3 / 64 ≤ A.lindebergFunction P (1 / 8) n := by
    simpa [A] using
      rareJumpPerturbed_lindebergLowerBound
        (P := P) (Y := Y) (Z := Z) hY_meas hZ_meas hY_iid hZ_indep hYZ_indep
        hY_mean hY_var hZ_law
  have hsmall : ∀ᶠ n in atTop, A.lindebergFunction P (1 / 8) n < 3 / 128 := by
    exact (hL.lindeberg_tendsto (show 0 < (1 / 8 : ℝ) by norm_num)).eventually
      (Iio_mem_nhds (show (0 : ℝ) < 3 / 128 by norm_num))
  rcases Filter.eventually_atTop.1 hlower with ⟨N1, hN1⟩
  rcases Filter.eventually_atTop.1 hsmall with ⟨N2, hN2⟩
  let n : ℕ := max N1 N2
  have hnlow : 3 / 64 ≤ A.lindebergFunction P (1 / 8) n := hN1 n (le_max_left _ _)
  have hnsmall : A.lindebergFunction P (1 / 8) n < 3 / 128 := hN2 n (le_max_right _ _)
  have hbound : 3 / 128 ≤ A.lindebergFunction P (1 / 8) n := by
    have : (3 / 128 : ℝ) ≤ 3 / 64 := by norm_num
    exact le_trans this hnlow
  exact (not_lt_of_ge hbound hnsmall).elim

/-- Exercise 15.5.2: for a `0`-based Lean model of the textbook sequences `Y₁, Y₂, ...` and
`Z₁, Z₂, ...`, the laws of the row sums of
`rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas`, equivalently of the normalized sums
`n^{-1/2} ∑_{k < n} (Y_k + Z_k)`, converge weakly to the standard Gaussian law `𝒩(0, 1)` when
`Y` is i.i.d., the perturbations `Z_k` are independent with laws `rareJumpLaw k`, and `Z` is
independent of the whole sequence `Y`; but the associated standardized array does not satisfy the
chapter-owner Lindeberg condition. -/
theorem rareLargeJumps_clt_but_not_lindeberg
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : ℕ → Ω → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hZ_meas : ∀ n, Measurable (Z n))
    (hY_iid : IsIID Y P)
    (hZ_indep : iIndepFun Z P)
    (hYZ_indep : IndepFun (fun ω ↦ fun n : ℕ ↦ Y n ω) (fun ω ↦ fun n : ℕ ↦ Z n ω) P)
    (hY_mean : P[Y 0] = 0)
    (hY_var : Var[Y 0; P] = 1)
    (hZ_law : ∀ n, HasLaw (Z n) (rareJumpLaw n) P) :
    Tendsto
      (fun n ↦ (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).rowSumLaw P n)
      atTop
      (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) ∧
    ¬ (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).SatisfiesLindebergCondition P :=
  by
  -- Proof comment: reuse the CLT helper and the lower-bound contradiction for the Lindeberg
  -- function.
  refine ⟨?_, ?_⟩
  · exact
      rareJumpPerturbed_rowSumLaw_tendstoGaussian
        (P := P) (Y := Y) (Z := Z) hY_meas hZ_meas hY_iid hY_mean hY_var hZ_law
  · exact
      rareJumpPerturbed_notSatisfiesLindeberg
        (P := P) (Y := Y) (Z := Z) hY_meas hZ_meas hY_iid hZ_indep hYZ_indep
        hY_mean hY_var hZ_law

end
