/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ENNReal ProbabilityTheory Topology

namespace MeasureTheory

universe u

noncomputable section

/- Exercise 11.2.4 is `source-facing`: it gives a counterexample to the converse of
Theorem 11.14. Its `core/canonical` owner layer is the existing martingale API
`Martingale`, `MemLp`, `Filtration.limitProcess`, and the chapter's square-variation owner
`⟨X⟩[ℱ, μ]`. Since Theorem 11.14 is formulated with the owner hypothesis that
`⟨X⟩[ℱ, μ]` is almost surely bounded above along sample paths, the public statement below is kept
in that owner shape rather than via a parallel "finite limit" wrapper. -/

-- Proof sketch: use independent centered sparse jumps whose absolute first moments are summable
-- but whose second moments are all `1`. Example 10.6 turns their partial sums into a
-- square-integrable martingale with deterministic square variation `n`, while the `L¹` bound is
-- strong enough to invoke almost-sure convergence to the canonical limit process.

section Counterexample

/-- Helper for Exercise 11.2.4: the witness sample space is the real-valued path space indexed by
`ULift ℕ`, so it lives in universe `u`. -/
private abbrev Omega0 : Type u := ULift ℕ → ℝ

/-- Helper for Exercise 11.2.4: the `n`th rare-jump probability is `4 ^ -(n + 1)`. -/
private noncomputable def sparseJumpWeight (n : ℕ) : ℝ :=
  (4 : ℝ)⁻¹ ^ (n + 1)

/-- Helper for Exercise 11.2.4: the `n`th jump size is `2 ^ (n + 1)`. -/
private noncomputable def sparseJumpAmplitude (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (n + 1)

/-- Helper for Exercise 11.2.4: the `n`th increment law puts mass `1 - 4 ^ -(n + 1)` at `0` and
the remaining mass equally at `± 2 ^ (n + 1)`. -/
private noncomputable def sparseJumpMarginal (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - sparseJumpWeight n) • Measure.dirac 0 +
    ENNReal.ofReal (sparseJumpWeight n / 2) • Measure.dirac (sparseJumpAmplitude n) +
      ENNReal.ofReal (sparseJumpWeight n / 2) • Measure.dirac (-(sparseJumpAmplitude n))

/-- Helper for Exercise 11.2.4: the rare-jump probability is nonnegative. -/
private theorem sparseJumpWeight_nonneg (n : ℕ) :
    0 ≤ sparseJumpWeight n := by
  -- Proof comment: `4 ^ -(n + 1)` is a nonnegative power of a nonnegative number.
  have hbase_nonneg : 0 ≤ (4 : ℝ)⁻¹ := by positivity
  simpa [sparseJumpWeight] using pow_nonneg hbase_nonneg (n + 1)

/-- Helper for Exercise 11.2.4: the rare-jump probability never exceeds `1`. -/
private theorem sparseJumpWeight_le_one (n : ℕ) :
    sparseJumpWeight n ≤ 1 := by
  -- Proof comment: the base `4⁻¹ = 1 / 4` lies in `[0, 1]`, so every natural power does too.
  have hbase_nonneg : 0 ≤ (4 : ℝ)⁻¹ := by positivity
  have hbase_le_one : (4 : ℝ)⁻¹ ≤ 1 := by norm_num
  simpa [sparseJumpWeight] using
    (pow_le_one₀ hbase_nonneg hbase_le_one : (4 : ℝ)⁻¹ ^ (n + 1) ≤ 1)

/-- Helper for Exercise 11.2.4: the mass left at `0` is nonnegative. -/
private theorem sparseJumpZeroWeight_nonneg (n : ℕ) :
    0 ≤ 1 - sparseJumpWeight n := by
  -- Proof comment: the zero mass is the complement of the rare-jump probability.
  exact sub_nonneg.mpr (sparseJumpWeight_le_one n)

/-- Helper for Exercise 11.2.4: each sparse-jump marginal is a probability measure. -/
private theorem sparseJumpMarginal_isProbability (n : ℕ) :
    IsProbabilityMeasure (sparseJumpMarginal n) := by
  -- Proof comment: the three atomic weights add up to `1`.
  refine ⟨?_⟩
  have hzero_nonneg : 0 ≤ 1 - sparseJumpWeight n := sparseJumpZeroWeight_nonneg n
  have hside_nonneg : 0 ≤ sparseJumpWeight n / 2 := by
    exact div_nonneg (sparseJumpWeight_nonneg n) (by norm_num)
  have hside_sum_nonneg : 0 ≤ sparseJumpWeight n / 2 + sparseJumpWeight n / 2 := by
    nlinarith
  have hside_add :
      ENNReal.ofReal (sparseJumpWeight n / 2) + ENNReal.ofReal (sparseJumpWeight n / 2) =
        ENNReal.ofReal (sparseJumpWeight n / 2 + sparseJumpWeight n / 2) := by
    exact (ENNReal.ofReal_add hside_nonneg hside_nonneg).symm
  calc
    sparseJumpMarginal n Set.univ =
        ENNReal.ofReal (1 - sparseJumpWeight n) +
          ENNReal.ofReal (sparseJumpWeight n / 2) +
            ENNReal.ofReal (sparseJumpWeight n / 2) := by
          simp [sparseJumpMarginal, add_assoc]
    _ = ENNReal.ofReal (1 - sparseJumpWeight n) +
          ENNReal.ofReal (sparseJumpWeight n / 2 + sparseJumpWeight n / 2) := by
          rw [add_assoc, hside_add]
    _ = ENNReal.ofReal
          ((1 - sparseJumpWeight n) + (sparseJumpWeight n / 2 + sparseJumpWeight n / 2)) := by
          rw [← ENNReal.ofReal_add hzero_nonneg hside_sum_nonneg]
    _ = 1 := by
          have hweights :
              (1 - sparseJumpWeight n) + (sparseJumpWeight n / 2 + sparseJumpWeight n / 2) =
                (1 : ℝ) := by
            ring
          rw [hweights]
          norm_num

/-- Helper for Exercise 11.2.4: every strongly measurable real function is integrable against the
three-point sparse-jump marginal. -/
private theorem integrable_sparseJumpMarginal (n : ℕ) {f : ℝ → ℝ} (hf : StronglyMeasurable f) :
    Integrable f (sparseJumpMarginal n) := by
  -- Proof comment: each Dirac component is integrable, and finite sums preserve integrability.
  have h0 :
      Integrable f (ENNReal.ofReal (1 - sparseJumpWeight n) • Measure.dirac 0) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h1 :
      Integrable f
        (ENNReal.ofReal (sparseJumpWeight n / 2) • Measure.dirac (sparseJumpAmplitude n)) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h2 :
      Integrable f
        (ENNReal.ofReal (sparseJumpWeight n / 2) • Measure.dirac (-(sparseJumpAmplitude n))) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  simpa [sparseJumpMarginal] using
    (integrable_add_measure).2 ⟨(integrable_add_measure).2 ⟨h0, h1⟩, h2⟩

/-- Helper for Exercise 11.2.4: integrating against the sparse-jump marginal reduces to the
corresponding three-point weighted average. -/
private theorem integral_sparseJumpMarginal (n : ℕ) {f : ℝ → ℝ} (hf : StronglyMeasurable f) :
    ∫ x, f x ∂sparseJumpMarginal n =
      (1 - sparseJumpWeight n) * f 0 +
        (sparseJumpWeight n / 2) * f (sparseJumpAmplitude n) +
          (sparseJumpWeight n / 2) * f (-(sparseJumpAmplitude n)) := by
  -- Proof comment: expand the finite measure into its three Dirac components and evaluate each
  -- integral explicitly.
  have h0 :
      Integrable f (ENNReal.ofReal (1 - sparseJumpWeight n) • Measure.dirac 0) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h1 :
      Integrable f
        (ENNReal.ofReal (sparseJumpWeight n / 2) • Measure.dirac (sparseJumpAmplitude n)) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h2 :
      Integrable f
        (ENNReal.ofReal (sparseJumpWeight n / 2) • Measure.dirac (-(sparseJumpAmplitude n))) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h01 :
      Integrable f
        (ENNReal.ofReal (1 - sparseJumpWeight n) • Measure.dirac 0 +
          ENNReal.ofReal (sparseJumpWeight n / 2) • Measure.dirac (sparseJumpAmplitude n)) := by
    exact (integrable_add_measure).2 ⟨h0, h1⟩
  rw [sparseJumpMarginal, integral_add_measure h01 h2, integral_add_measure h0 h1,
    integral_smul_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac' f 0 hf, integral_dirac' f (sparseJumpAmplitude n) hf,
    integral_dirac' f (-(sparseJumpAmplitude n)) hf]
  have hzero_nonneg : 0 ≤ 1 - sparseJumpWeight n := sparseJumpZeroWeight_nonneg n
  have hside_nonneg : 0 ≤ sparseJumpWeight n / 2 := by
    exact div_nonneg (sparseJumpWeight_nonneg n) (by norm_num)
  simp [ENNReal.toReal_ofReal hzero_nonneg, ENNReal.toReal_ofReal hside_nonneg, add_assoc]

/-- Helper for Exercise 11.2.4: the sparse-jump marginal belongs to `L²`. -/
private theorem sparseJumpMarginal_memLp_two (n : ℕ) :
    MemLp id 2 (sparseJumpMarginal n) := by
  -- Proof comment: the square function is integrable because the law has finite support.
  exact (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
    (integrable_sparseJumpMarginal n (f := fun x : ℝ ↦ x ^ (2 : ℕ)) (by fun_prop))

/-- Helper for Exercise 11.2.4: the sparse-jump marginal is centered. -/
private theorem sparseJumpMarginal_mean_zero (n : ℕ) :
    ∫ x, x ∂sparseJumpMarginal n = 0 := by
  -- Proof comment: the positive and negative atoms have equal masses and opposite values.
  calc
    ∫ x, x ∂sparseJumpMarginal n =
        (1 - sparseJumpWeight n) * (0 : ℝ) +
          (sparseJumpWeight n / 2) * sparseJumpAmplitude n +
            (sparseJumpWeight n / 2) * (-(sparseJumpAmplitude n)) := by
          simpa using integral_sparseJumpMarginal n (f := fun x : ℝ ↦ x) stronglyMeasurable_id
    _ = 0 := by
          ring

/-- Helper for Exercise 11.2.4: the sparse-jump marginal has unit second moment. -/
private theorem sparseJumpMarginal_secondMoment (n : ℕ) :
    ∫ x, x ^ (2 : ℕ) ∂sparseJumpMarginal n = 1 := by
  have hamp_sq :
      (sparseJumpAmplitude n) ^ (2 : ℕ) = (4 : ℝ) ^ (n + 1) := by
    -- Proof comment: squaring `2 ^ (n + 1)` yields `4 ^ (n + 1)`.
    calc
      (sparseJumpAmplitude n) ^ (2 : ℕ) = ((2 : ℝ) ^ (n + 1)) ^ (2 : ℕ) := by
        rfl
      _ = (2 : ℝ) ^ ((n + 1) * 2) := by
        rw [pow_mul]
      _ = (2 : ℝ) ^ (2 * (n + 1)) := by ring_nf
      _ = ((2 : ℝ) ^ (2 : ℕ)) ^ (n + 1) := by
        rw [← pow_mul]
      _ = (4 : ℝ) ^ (n + 1) := by norm_num
  calc
    ∫ x, x ^ (2 : ℕ) ∂sparseJumpMarginal n =
        (sparseJumpWeight n / 2) * (sparseJumpAmplitude n) ^ (2 : ℕ) +
          (sparseJumpWeight n / 2) * (-(sparseJumpAmplitude n)) ^ (2 : ℕ) := by
          rw [integral_sparseJumpMarginal n (f := fun x : ℝ ↦ x ^ (2 : ℕ)) (by fun_prop)]
          ring
    _ = (sparseJumpWeight n / 2) * (4 : ℝ) ^ (n + 1) +
          (sparseJumpWeight n / 2) * (4 : ℝ) ^ (n + 1) := by
          have hneg_sq :
              (-(sparseJumpAmplitude n)) ^ (2 : ℕ) = (sparseJumpAmplitude n) ^ (2 : ℕ) := by
            ring
          rw [hamp_sq, hneg_sq, hamp_sq]
    _ = sparseJumpWeight n * (4 : ℝ) ^ (n + 1) := by ring
    _ = ((4 : ℝ)⁻¹ * 4) ^ (n + 1) := by
          rw [show sparseJumpWeight n = (4 : ℝ)⁻¹ ^ (n + 1) by rfl, ← mul_pow]
    _ = 1 := by
          norm_num

/-- Helper for Exercise 11.2.4: the sparse-jump marginal has geometric first absolute moment
`(1 / 2) ^ (n + 1)`. -/
private theorem sparseJumpMarginal_normMoment (n : ℕ) :
    ∫ x, ‖x‖ ∂sparseJumpMarginal n = (1 / 2 : ℝ) ^ (n + 1) := by
  have hamp_nonneg : 0 ≤ sparseJumpAmplitude n := by
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (n + 1) := by positivity
    simpa [sparseJumpAmplitude] using hpow_nonneg
  calc
    ∫ x, ‖x‖ ∂sparseJumpMarginal n =
        (sparseJumpWeight n / 2) * sparseJumpAmplitude n +
          (sparseJumpWeight n / 2) * sparseJumpAmplitude n := by
          rw [integral_sparseJumpMarginal n (f := fun x : ℝ ↦ ‖x‖) (by fun_prop)]
          simp [Real.norm_eq_abs, abs_of_nonneg hamp_nonneg]
    _ = sparseJumpWeight n * sparseJumpAmplitude n := by ring
    _ = (1 / 2 : ℝ) ^ (n + 1) := by
          unfold sparseJumpWeight sparseJumpAmplitude
          rw [← mul_pow]
          norm_num

/-- Helper for Exercise 11.2.4: the sparse-jump product family is indexed by `ULift ℕ`. -/
private noncomputable def sparseJumpFamily : ULift ℕ → Measure ℝ :=
  fun i ↦ sparseJumpMarginal i.down

/-- Helper for Exercise 11.2.4: every coordinate marginal in the product law is a probability
measure. -/
private instance sparseJumpFamily_isProbability (i : ULift ℕ) :
    IsProbabilityMeasure (sparseJumpFamily i) :=
  sparseJumpMarginal_isProbability i.down

/-- Helper for Exercise 11.2.4: the witness law is the infinite product of the sparse-jump
marginals. -/
private noncomputable def sparseJumpMeasure : Measure Omega0 :=
  Measure.infinitePi sparseJumpFamily

/-- Helper for Exercise 11.2.4: the sparse-jump product law is a probability measure. -/
private instance sparseJumpMeasure_isProbability :
    IsProbabilityMeasure sparseJumpMeasure := by
  change IsProbabilityMeasure (Measure.infinitePi sparseJumpFamily)
  infer_instance

/-- Helper for Exercise 11.2.4: the `n`th increment reads the `ULift.up n` coordinate of the path.
-/
private def sparseIncrement (n : ℕ) : Omega0 → ℝ :=
  fun ω ↦ ω (ULift.up n)

/-- Helper for Exercise 11.2.4: each sparse increment is measurable. -/
private theorem sparseIncrement_measurable (n : ℕ) :
    Measurable (sparseIncrement n) := by
  -- Proof comment: coordinate projections on a product measurable space are measurable.
  simpa [sparseIncrement] using measurable_pi_apply (ULift.up n)

/-- Helper for Exercise 11.2.4: the `n`th increment has exactly the prescribed sparse-jump law. -/
private theorem sparseIncrement_law (n : ℕ) :
    HasLaw (sparseIncrement n) (sparseJumpMarginal n) sparseJumpMeasure := by
  -- Proof comment: evaluation at `ULift.up n` is measure preserving for the infinite product law.
  simpa [sparseIncrement, sparseJumpMeasure, sparseJumpFamily] using
    (MeasurePreserving.hasLaw
      (measurePreserving_eval_infinitePi sparseJumpFamily (ULift.up n)) :
      HasLaw (Function.eval (ULift.up n)) (sparseJumpFamily (ULift.up n)) sparseJumpMeasure)

/-- Helper for Exercise 11.2.4: each sparse increment is identically distributed with the identity
under its one-dimensional marginal law. -/
private theorem sparseIncrement_identDistrib (n : ℕ) :
    IdentDistrib (sparseIncrement n) id sparseJumpMeasure (sparseJumpMarginal n) := by
  refine ⟨(sparseIncrement_measurable n).aemeasurable, aemeasurable_id, ?_⟩
  simpa using (sparseIncrement_law n).map_eq

/-- Helper for Exercise 11.2.4: the sparse increments are independent. -/
private theorem sparseIncrement_iIndepFun :
    iIndepFun sparseIncrement sparseJumpMeasure := by
  have hcoord :
      iIndepFun (fun i : ULift ℕ ↦ fun ω : Omega0 ↦ ω i) sparseJumpMeasure := by
    simpa [sparseJumpMeasure] using
      (iIndepFun_infinitePi (P := sparseJumpFamily) (fun _ ↦ measurable_id) :
        iIndepFun (fun i (ω : Omega0) ↦ ω i) sparseJumpMeasure)
  -- Proof comment: restrict the independent coordinate family along the injective map `ULift.up`.
  simpa [sparseIncrement] using hcoord.precomp ULift.up_injective

/-- Helper for Exercise 11.2.4: every sparse increment is square integrable. -/
private theorem sparseIncrement_memLp_two (n : ℕ) :
    MemLp (sparseIncrement n) 2 sparseJumpMeasure := by
  -- Proof comment: transport the one-dimensional `L²` statement through identical distribution.
  exact (sparseIncrement_identDistrib n).symm.memLp_snd (sparseJumpMarginal_memLp_two n)

/-- Helper for Exercise 11.2.4: every sparse increment is integrable. -/
private theorem sparseIncrement_integrable (n : ℕ) :
    Integrable (sparseIncrement n) sparseJumpMeasure := by
  -- Proof comment: `L²` integrability implies `L¹` integrability on a probability space.
  exact (sparseIncrement_memLp_two n).integrable (by norm_num)

/-- Helper for Exercise 11.2.4: every sparse increment has integrable square. -/
private theorem sparseIncrement_sqIntegrable (n : ℕ) :
    Integrable (fun ω ↦ (sparseIncrement n ω) ^ (2 : ℕ)) sparseJumpMeasure := by
  -- Proof comment: unwrap `MemLp` at exponent `2` into integrability of the square.
  exact (memLp_two_iff_integrable_sq
    ((sparseIncrement_measurable n).stronglyMeasurable.aestronglyMeasurable)).1
      (sparseIncrement_memLp_two n)

/-- Helper for Exercise 11.2.4: the sparse increments are centered. -/
private theorem sparseIncrement_mean_zero (n : ℕ) :
    sparseJumpMeasure[sparseIncrement n] = 0 := by
  -- Proof comment: the pushforward law is centered, so the coordinate expectation is `0`.
  simpa [sparseJumpMarginal_mean_zero n] using (sparseIncrement_law n).integral_eq

/-- Helper for Exercise 11.2.4: every sparse increment has second moment `1`. -/
private theorem sparseIncrement_secondMoment (n : ℕ) :
    sparseJumpMeasure[fun ω ↦ (sparseIncrement n ω) ^ (2 : ℕ)] = 1 := by
  -- Proof comment: push the square through identical distribution and use the explicit marginal
  -- second moment.
  simpa [Function.comp, sparseJumpMarginal_secondMoment n] using
    ((sparseIncrement_identDistrib n).comp (by fun_prop :
      Measurable (fun x : ℝ ↦ x ^ (2 : ℕ)))).integral_eq

/-- Helper for Exercise 11.2.4: the `L¹` norm of the `n`th sparse increment is exactly
`(1 / 2) ^ (n + 1)`. -/
private theorem sparseIncrement_eLpNorm_one (n : ℕ) :
    eLpNorm (sparseIncrement n) 1 sparseJumpMeasure = ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  -- Proof comment: rewrite the `L¹` norm as the integral of the pointwise norm and evaluate that
  -- integral through the one-dimensional marginal law.
  calc
    eLpNorm (sparseIncrement n) 1 sparseJumpMeasure =
        ENNReal.ofReal (∫ ω, ‖sparseIncrement n ω‖ ∂sparseJumpMeasure) := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          exact (ofReal_integral_norm_eq_lintegral_enorm (sparseIncrement_integrable n)).symm
    _ = ENNReal.ofReal (∫ x, ‖x‖ ∂sparseJumpMarginal n) := by
          refine congrArg ENNReal.ofReal ?_
          simpa [Function.comp] using
            ((sparseIncrement_identDistrib n).comp (by fun_prop :
              Measurable (fun x : ℝ ↦ ‖x‖))).integral_eq
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
          rw [sparseJumpMarginal_normMoment]

/-- Helper for Exercise 11.2.4: the martingale itself is the partial-sum process of the sparse
increments. -/
private def sparsePartialSum : ℕ → Omega0 → ℝ :=
  partialSum sparseIncrement

/-- Helper for Exercise 11.2.4: every deterministic stage of the sparse partial sums is
measurable. -/
private theorem sparsePartialSum_measurable (n : ℕ) :
    Measurable (sparsePartialSum n) := by
  -- Proof comment: finite partial sums of measurable increments are measurable.
  simpa [sparsePartialSum] using
    partialSum_measurable sparseIncrement sparseIncrement_measurable n

/-- Helper for Exercise 11.2.4: the natural filtration of the sparse partial sums. -/
private noncomputable def sparseFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace Omega0) :=
  Filtration.natural sparsePartialSum
    (fun n ↦ (sparsePartialSum_measurable n).stronglyMeasurable)

/-- Helper for Exercise 11.2.4: the sparse partial-sum process is a martingale for its natural
filtration. -/
private theorem sparsePartialSum_martingale :
    Martingale sparsePartialSum sparseFiltration sparseJumpMeasure := by
  -- Proof comment: Example 10.6 applies once the increments are measurable, integrable,
  -- centered, and independent.
  simpa [sparsePartialSum, sparseFiltration] using
    (independentCenteredPartialSums_martingale
      (Y := sparseIncrement) (μ := sparseJumpMeasure)
      (hY_meas := sparseIncrement_measurable)
      sparseIncrement_integrable sparseIncrement_mean_zero sparseIncrement_iIndepFun)

/-- Helper for Exercise 11.2.4: every deterministic stage of the sparse partial-sum process is in
`L²`. -/
private theorem sparsePartialSum_memLp_two (n : ℕ) :
    MemLp (sparsePartialSum n) 2 sparseJumpMeasure := by
  have hsq :
      Integrable (fun ω ↦ (sparsePartialSum n ω) ^ (2 : ℕ)) sparseJumpMeasure := by
    -- Proof comment: Example 10.6 packages square integrability of the finite partial sums.
    simpa [sparsePartialSum] using
      (independentCenteredPartialSums_squareIntegrable
        (Y := sparseIncrement) (μ := sparseJumpMeasure)
        sparseIncrement_measurable sparseIncrement_sqIntegrable n)
  exact (memLp_two_iff_integrable_sq
    ((sparsePartialSum_measurable n).stronglyMeasurable.aestronglyMeasurable)).2 hsq

/-- Helper for Exercise 11.2.4: the `L¹` norm of the sparse partial sums is dominated by the
corresponding finite geometric series. -/
private theorem sparsePartialSum_eLpNorm_one_le_geometricSum (n : ℕ) :
    eLpNorm (sparsePartialSum n) 1 sparseJumpMeasure ≤
      ENNReal.ofReal (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1)) := by
  induction n with
  | zero =>
      -- Proof comment: the empty partial sum is the zero process.
      have hzero : partialSum sparseIncrement 0 = (0 : Omega0 → ℝ) := by
        funext ω
        simp [partialSum]
      rw [sparsePartialSum, hzero, eLpNorm_zero]
      simp
  | succ n ih =>
      have hMeasSum :
          AEStronglyMeasurable (sparsePartialSum n) sparseJumpMeasure := by
        exact ((sparsePartialSum_measurable n).stronglyMeasurable).aestronglyMeasurable
      have hMeasInc :
          AEStronglyMeasurable (sparseIncrement n) sparseJumpMeasure := by
        exact ((sparseIncrement_measurable n).stronglyMeasurable).aestronglyMeasurable
      calc
        eLpNorm (sparsePartialSum (n + 1)) 1 sparseJumpMeasure =
            eLpNorm (fun ω ↦ sparsePartialSum n ω + sparseIncrement n ω) 1 sparseJumpMeasure := by
              refine eLpNorm_congr_ae (.of_forall fun ω ↦ ?_)
              simp [sparsePartialSum, partialSum, Finset.sum_range_succ]
        _ ≤ eLpNorm (sparsePartialSum n) 1 sparseJumpMeasure +
              eLpNorm (sparseIncrement n) 1 sparseJumpMeasure := by
              exact eLpNorm_add_le hMeasSum hMeasInc le_rfl
        _ ≤ ENNReal.ofReal (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1)) +
              ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
              exact add_le_add ih (by
                simpa using le_of_eq (sparseIncrement_eLpNorm_one n))
        _ = ENNReal.ofReal (∑ i ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (i + 1)) := by
              rw [← ENNReal.ofReal_add]
              · simp [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
              · positivity
              · positivity

/-- Helper for Exercise 11.2.4: the sparse partial sums are uniformly bounded in `L¹` by `1`. -/
private theorem sparsePartialSum_eLpNorm_one_le_one (n : ℕ) :
    eLpNorm (sparsePartialSum n) 1 sparseJumpMeasure ≤ 1 := by
  have hgeom :
      (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1)) ≤ 1 := by
    calc
      (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1)) =
          (1 / 2 : ℝ) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [pow_succ', mul_comm]
      _ ≤ (1 / 2 : ℝ) * 2 := by
            gcongr
            exact sum_geometric_two_le n
      _ = 1 := by norm_num
  calc
    eLpNorm (sparsePartialSum n) 1 sparseJumpMeasure ≤
        ENNReal.ofReal (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1)) :=
      sparsePartialSum_eLpNorm_one_le_geometricSum n
    _ ≤ ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_le_ofReal hgeom
    _ = 1 := by norm_num

/-- Helper for Exercise 11.2.4: the square variation of the sparse partial-sum martingale agrees
almost everywhere with the deterministic process `n ↦ n`. -/
private theorem sparsePartialSum_squareVariation_ae_eq_nat (n : ℕ) :
    ⟨sparsePartialSum⟩[sparseFiltration, sparseJumpMeasure] n =ᵐ[sparseJumpMeasure]
      fun _ ↦ (n : ℝ) := by
  -- Proof comment: Example 10.6 identifies the bracket with the deterministic sum of the second
  -- moments, and every second moment is `1`.
  simpa [sparsePartialSum, sparseFiltration, sparseIncrement_secondMoment] using
    (independentCenteredPartialSums_squareVariation_ae_eq_deterministicSquareVariation
      (Y := sparseIncrement) (μ := sparseJumpMeasure)
      sparseIncrement_measurable sparseIncrement_sqIntegrable
      sparseIncrement_mean_zero sparseIncrement_iIndepFun n)

/-- Helper for Exercise 11.2.4: the deterministic range `{0, 1, 2, ...}` in `ℝ` is not bounded
above. -/
private theorem not_bddAbove_natCastRange :
    ¬ BddAbove (Set.range fun n : ℕ ↦ (n : ℝ)) := by
  -- Proof comment: any real upper bound is violated by the next integer after its ceiling.
  intro hBdd
  rcases hBdd with ⟨a, ha⟩
  let n : ℕ := Nat.ceil a + 1
  have hlt : a < (n : ℝ) := by
    have hceil : a ≤ (Nat.ceil a : ℝ) := Nat.le_ceil a
    have hsucc : (Nat.ceil a : ℝ) < ((Nat.ceil a + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self (Nat.ceil a)
    simpa [n] using lt_of_le_of_lt hceil hsucc
  have hupper : (n : ℝ) ≤ a := ha ⟨n, rfl⟩
  exact (not_lt_of_ge hupper) hlt

end Counterexample

-- Proof sketch: choose a sparse-jump product law on `Omega0`, let `X` be the partial sums of the
-- coordinate increments, apply Example 10.6 for the martingale and square-variation identities,
-- use the geometric `L¹` bound to get convergence to `ℱ.limitProcess X μ`, and finally observe
-- that the bracket equals `n` almost surely and hence cannot be pathwise bounded above.
/-- Exercise 11.2.4: there exists a filtered probability space carrying a square-integrable
martingale that converges almost surely to its canonical limit process, but whose canonical square
variation `⟨X⟩[ℱ, μ]` is not almost surely bounded above along sample paths; equivalently, it does
not admit an almost surely finite real limit. -/
theorem exists_square_integrable_martingale_ae_tendsto_limitProcess_not_ae_bddAbove_squareVariation :
    ∃ (Ω : Type u) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ),
        Martingale X ℱ μ ∧
          (∀ n, MemLp (X n) 2 μ) ∧
          (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
          ¬ ∀ᵐ ω ∂μ, BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω) := by
  have hX : Martingale sparsePartialSum sparseFiltration sparseJumpMeasure :=
    sparsePartialSum_martingale
  have hX_memLp : ∀ n, MemLp (sparsePartialSum n) 2 sparseJumpMeasure :=
    sparsePartialSum_memLp_two
  have h_ae_tendsto :
      ∀ᵐ ω ∂sparseJumpMeasure,
        Tendsto (fun n ↦ sparsePartialSum n ω) atTop
          (𝓝 (sparseFiltration.limitProcess sparsePartialSum sparseJumpMeasure ω)) := by
    -- Proof comment: the martingale is uniformly `L¹`-bounded, so the canonical limit-process
    -- convergence theorem applies directly.
    exact hX.submartingale.ae_tendsto_limitProcess sparsePartialSum_eLpNorm_one_le_one
  have hSquareAll :
      ∀ᵐ ω ∂sparseJumpMeasure,
        ∀ n, ⟨sparsePartialSum⟩[sparseFiltration, sparseJumpMeasure] n ω = (n : ℝ) := by
    -- Proof comment: merge the timewise almost-everywhere bracket identities into one full-measure
    -- event before arguing pointwise.
    simpa [Filter.EventuallyEq] using
      (ae_all_iff.2 fun n ↦ sparsePartialSum_squareVariation_ae_eq_nat n)
  have hNotBdd :
      ¬ ∀ᵐ ω ∂sparseJumpMeasure,
        BddAbove (Set.range fun n ↦ ⟨sparsePartialSum⟩[sparseFiltration, sparseJumpMeasure] n ω) := by
    intro hBddAe
    have hnotFalseAe : ¬ ∀ᵐ ω ∂sparseJumpMeasure, False := by
      rw [ae_iff]
      simp
    have hFalseAe : ∀ᵐ ω ∂sparseJumpMeasure, False := by
      filter_upwards [hSquareAll, hBddAe] with ω hω hBdd
      have hNatBdd : BddAbove (Set.range fun n : ℕ ↦ (n : ℝ)) := by
        rcases hBdd with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        rintro x ⟨n, rfl⟩
        simpa [hω n] using ha ⟨n, rfl⟩
      exact not_bddAbove_natCastRange hNatBdd
    exact hnotFalseAe hFalseAe
  exact ⟨Omega0, inferInstance, sparseJumpMeasure, inferInstance, sparseFiltration, sparsePartialSum,
    hX, hX_memLp, h_ae_tendsto, hNotBdd⟩

end

end MeasureTheory
