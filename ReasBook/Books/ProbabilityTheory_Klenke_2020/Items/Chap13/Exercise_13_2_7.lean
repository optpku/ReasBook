/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.TietzeExtension

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported Topology unitInterval

universe u

namespace MeasureTheory.SignedMeasure

section General

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Integration of a bounded continuous real-valued test function against a signed measure, via
its Jordan decomposition. This is the signed-measure extension of the weak test-function pairing
from Definition 13.12 (1). -/
def weakIntegral (f : E →ᵇ ℝ) : SignedMeasure E → ℝ :=
  fun φ ↦
    ∫ x, f x ∂φ.toJordanDecomposition.posPart - ∫ x, f x ∂φ.toJordanDecomposition.negPart

omit [BorelSpace E] in
@[simp] theorem weakIntegral_apply (f : E →ᵇ ℝ) (φ : SignedMeasure E) :
    weakIntegral f φ =
      ∫ x, f x ∂φ.toJordanDecomposition.posPart -
        ∫ x, f x ∂φ.toJordanDecomposition.negPart :=
  rfl

/-- Integration of a compactly supported continuous real-valued test function against a signed
measure. This is the signed-measure extension of the vague test-function pairing from
Definition 13.12 (2). -/
def vagueIntegral (f : C_c(E, ℝ)) : SignedMeasure E → ℝ :=
  weakIntegral f.toBoundedContinuousFunction

omit [BorelSpace E] in
@[simp] theorem vagueIntegral_apply (f : C_c(E, ℝ)) (φ : SignedMeasure E) :
    vagueIntegral f φ =
      ∫ x, f x ∂φ.toJordanDecomposition.posPart -
        ∫ x, f x ∂φ.toJordanDecomposition.negPart :=
  rfl

/-- The zero signed measure has zero weak integral against every bounded continuous real-valued
test function. -/
theorem weakIntegral_zero (f : E →ᵇ ℝ) : weakIntegral f 0 = 0 := by
  -- The zero signed measure has trivial positive and negative parts.
  simp [weakIntegral, SignedMeasure.toJordanDecomposition_zero]

/-- A signed measure is Radon when both parts of its Jordan decomposition are Radon measures. This
is the source-facing domain condition for vague convergence of signed measures. -/
def IsRadon (φ : SignedMeasure E) : Prop :=
  IsRadonMeasure φ.toJordanDecomposition.posPart ∧
    IsRadonMeasure φ.toJordanDecomposition.negPart

/-- The weak topology on signed measures is the coarsest topology making integration against every
bounded continuous real-valued test function continuous. -/
@[reducible] def weakTopology (E : Type u) [MetricSpace E] [MeasurableSpace E] [BorelSpace E] :
    TopologicalSpace (SignedMeasure E) :=
  ⨅ f : E →ᵇ ℝ, TopologicalSpace.induced (weakIntegral f) inferInstance

instance instTopologicalSpaceSignedMeasure :
    TopologicalSpace (SignedMeasure E) :=
  weakTopology E

/-- A sequence of signed measures converges weakly when it converges in the owner topology
`SignedMeasure.weakTopology`. -/
def weaklyConvergesTo (φs : ℕ → SignedMeasure E) (φ : SignedMeasure E) : Prop :=
  Tendsto φs atTop (𝓝 φ)

/-- A sequence of signed measures converges weakly exactly when every bounded continuous
real-valued test integral converges. -/
theorem weaklyConvergesTo_iff {φs : ℕ → SignedMeasure E} {φ : SignedMeasure E} :
    weaklyConvergesTo φs φ ↔
      ∀ f : E →ᵇ ℝ,
        Tendsto (fun n ↦ weakIntegral f (φs n)) atTop (𝓝 (weakIntegral f φ)) := by
  simp [weaklyConvergesTo, nhds_iInf, nhds_induced, Filter.tendsto_iInf,
    Filter.tendsto_comap_iff, Function.comp_def]

/-- Weak convergence to the zero signed measure amounts to convergence of every bounded continuous
test integral to `0`. -/
theorem weaklyConvergesTo_zero_iff (φs : ℕ → SignedMeasure E) :
    weaklyConvergesTo φs 0 ↔
      ∀ f : E →ᵇ ℝ, Tendsto (fun n ↦ weakIntegral f (φs n)) atTop (𝓝 0) := by
  constructor
  · intro h f
    simpa [weakIntegral, SignedMeasure.toJordanDecomposition_zero] using
      (weaklyConvergesTo_iff.mp h) f
  · intro h
    exact weaklyConvergesTo_iff.mpr fun f ↦ by
      simpa [weakIntegral, SignedMeasure.toJordanDecomposition_zero] using h f

/-- A sequence of signed measures converges vaguely when both the limit and the whole sequence are
Radon signed measures and all compactly supported continuous real-valued test integrals converge.
This is the signed-measure extension of Definition 13.12 (2). -/
def vaguelyConvergesTo (φs : ℕ → SignedMeasure E) (φ : SignedMeasure E) : Prop :=
  IsRadon φ ∧
    (∀ n, IsRadon (φs n)) ∧
    ∀ f : C_c(E, ℝ), Tendsto (fun n ↦ vagueIntegral f (φs n)) atTop (𝓝 (vagueIntegral f φ))

/- Vague convergence of signed measures means exactly convergence of integrals against all
compactly supported continuous real-valued test functions, together with the ambient Radon signed
measure assumptions on the sequence and its limit. -/
omit [BorelSpace E] in
theorem vaguelyConvergesTo_iff (φs : ℕ → SignedMeasure E) (φ : SignedMeasure E) :
    vaguelyConvergesTo φs φ ↔
      IsRadon φ ∧
        (∀ n, IsRadon (φs n)) ∧
        ∀ f : C_c(E, ℝ),
          Tendsto (fun n ↦ vagueIntegral f (φs n)) atTop (𝓝 (vagueIntegral f φ)) :=
  Iff.rfl

end General

end MeasureTheory.SignedMeasure

section UnitIntervalCounterexample

open MeasureTheory.SignedMeasure

/-- The reciprocal point `1 / (n + 2)` belongs to the closed unit interval. -/
lemma reciprocal_nat_add_two_mem_unit_interval (n : ℕ) :
    (((n : ℝ) + 2)⁻¹) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · have hpos : 0 < (n : ℝ) + 2 := by positivity
    exact (inv_le_one₀ hpos).2 (by linarith)

/-- The point `1 / (n + 2)` in the closed unit interval. -/
def reciprocal_unit_interval_point (n : ℕ) : I :=
  ⟨((n : ℝ) + 2)⁻¹, reciprocal_nat_add_two_mem_unit_interval n⟩

/-- The value of `reciprocal_unit_interval_point`. -/
theorem reciprocal_unit_interval_point_val (n : ℕ) :
    ((reciprocal_unit_interval_point n : I) : ℝ) = ((n : ℝ) + 2)⁻¹ :=
  rfl

/-- The point `2 / (n + 2)` belongs to the closed unit interval. -/
lemma double_reciprocal_nat_add_two_mem_unit_interval (n : ℕ) :
    ((2 : ℝ) / ((n : ℝ) + 2)) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · have hpos : 0 < (n : ℝ) + 2 := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith

/-- The point `2 / (n + 2)` in the closed unit interval. -/
def double_reciprocal_unit_interval_point (n : ℕ) : I :=
  ⟨(2 : ℝ) / ((n : ℝ) + 2), double_reciprocal_nat_add_two_mem_unit_interval n⟩

/-- The value of `double_reciprocal_unit_interval_point`. -/
theorem double_reciprocal_unit_interval_point_val (n : ℕ) :
    ((double_reciprocal_unit_interval_point n : I) : ℝ) =
      (2 : ℝ) / ((n : ℝ) + 2) :=
  rfl

/-- The dyadic point `2^{-n}` belongs to the closed unit interval. -/
lemma dyadic_inverse_mem_unit_interval (n : ℕ) :
    (((2 : ℝ) ^ n)⁻¹) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
      induction n with
      | zero =>
          norm_num
      | succ n ih =>
          calc
            (1 : ℝ) ≤ (2 : ℝ) ^ n := ih
            _ ≤ (2 : ℝ) ^ n * 2 := by
              nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ n by positivity]
            _ = (2 : ℝ) ^ (n + 1) := by ring
    exact (inv_le_one₀ (by positivity : 0 < (2 : ℝ) ^ n)).2 hpow

/-- The dyadic point `2^{-n}` in the closed unit interval. -/
def dyadic_unit_interval_point (n : ℕ) : I :=
  ⟨((2 : ℝ) ^ n)⁻¹, dyadic_inverse_mem_unit_interval n⟩

/-- The value of `dyadic_unit_interval_point`. -/
theorem dyadic_unit_interval_point_val (n : ℕ) :
    ((dyadic_unit_interval_point n : I) : ℝ) = ((2 : ℝ) ^ n)⁻¹ :=
  rfl

/-- The shifted Dirac-difference sequence used in the signed weak-convergence counterexample on
`[0,1]`. -/
def shifted_point_mass_difference (n : ℕ) : SignedMeasure I :=
  (Measure.dirac (reciprocal_unit_interval_point n)).toSignedMeasure -
    (Measure.dirac (double_reciprocal_unit_interval_point n)).toSignedMeasure

/-- The shifted Dirac-difference sequence is the difference of the two indicated Dirac masses. -/
theorem shifted_point_mass_difference_def (n : ℕ) :
    shifted_point_mass_difference n =
      (Measure.dirac (reciprocal_unit_interval_point n)).toSignedMeasure -
        (Measure.dirac (double_reciprocal_unit_interval_point n)).toSignedMeasure :=
  rfl

/-- Helper for Exercise 13.2.7: the two support points of `shifted_point_mass_difference n` are
distinct. -/
lemma reciprocal_point_ne_double_reciprocal_point (n : ℕ) :
    reciprocal_unit_interval_point n ≠ double_reciprocal_unit_interval_point n := by
  intro h
  have hval :
      (((n : ℝ) + 2)⁻¹ : ℝ) = (2 : ℝ) / ((n : ℝ) + 2) := by
    simpa [reciprocal_unit_interval_point_val, double_reciprocal_unit_interval_point_val] using
      congrArg (fun x : I ↦ (x : ℝ)) h
  have hpos : 0 < (n : ℝ) + 2 := by positivity
  field_simp [hpos.ne'] at hval
  linarith

/-- Helper for Exercise 13.2.7: distinct Dirac masses are mutually singular. -/
lemma diracMutuallySingularOfNe {x y : I} (hxy : x ≠ y) :
    (Measure.dirac x).MutuallySingular (Measure.dirac y) := by
  refine ⟨{x}ᶜ, (MeasurableSet.singleton x).compl, ?_, ?_⟩
  · simp
  · have hyx : y ∉ ({x} : Set I) := by simpa using hxy.symm
    simp [Measure.dirac_apply', hyx]

/-- Helper for Exercise 13.2.7: the Jordan decomposition of a difference of distinct Dirac masses
is given by the two Dirac measures themselves. -/
def diracDifferenceJordanDecomposition (x y : I) (hxy : x ≠ y) : JordanDecomposition I where
  posPart := Measure.dirac x
  negPart := Measure.dirac y
  mutuallySingular := diracMutuallySingularOfNe hxy

/-- Helper for Exercise 13.2.7: rewriting the Jordan decomposition of a Dirac difference through
the explicit mutually singular pair avoids reopening the Hahn decomposition. -/
lemma toJordanDecomposition_diracDifference {x y : I} (hxy : x ≠ y) :
    ((Measure.dirac x).toSignedMeasure - (Measure.dirac y).toSignedMeasure).toJordanDecomposition =
      diracDifferenceJordanDecomposition x y hxy := by
  -- Compare the canonical Jordan decomposition from `JordanSub` with the explicit Dirac pair.
  calc
    ((Measure.dirac x).toSignedMeasure - (Measure.dirac y).toSignedMeasure).toJordanDecomposition =
        Measure.jordanDecompositionOfToSignedMeasureSub (Measure.dirac x) (Measure.dirac y) := by
          simpa using
            (Measure.toJordanDecomposition_toSignedMeasure_sub
              (μ := Measure.dirac x) (ν := Measure.dirac y))
    _ = diracDifferenceJordanDecomposition x y hxy := by
      apply JordanDecomposition.toSignedMeasure_injective
      calc
        (Measure.jordanDecompositionOfToSignedMeasureSub
            (Measure.dirac x) (Measure.dirac y)).toSignedMeasure =
            (Measure.dirac x).toSignedMeasure - (Measure.dirac y).toSignedMeasure := by
              simpa using
                (Measure.jordanDecompositionOfToSignedMeasureSub_toSignedMeasure
                  (μ := Measure.dirac x) (ν := Measure.dirac y))
        _ = (diracDifferenceJordanDecomposition x y hxy).toSignedMeasure := by
          simp [diracDifferenceJordanDecomposition, JordanDecomposition.toSignedMeasure]

/-- Helper for Exercise 13.2.7: the weak integral of the unscaled Dirac difference is the
corresponding difference of point evaluations. -/
lemma weakIntegral_shiftedPointMassDifference (f : I →ᵇ ℝ) (n : ℕ) :
    weakIntegral f (shifted_point_mass_difference n) =
      f (reciprocal_unit_interval_point n) - f (double_reciprocal_unit_interval_point n) := by
  -- Rewrite the Jordan decomposition using the explicit mutually singular Dirac pair.
  have hxy : reciprocal_unit_interval_point n ≠ double_reciprocal_unit_interval_point n :=
    reciprocal_point_ne_double_reciprocal_point n
  rw [shifted_point_mass_difference_def, weakIntegral, toJordanDecomposition_diracDifference hxy]
  simp [diracDifferenceJordanDecomposition]

/-- Helper for Exercise 13.2.7: scaling the Dirac difference scales the resulting weak integral by
the same real factor. -/
lemma weakIntegral_smul_shiftedPointMassDifference (f : I →ᵇ ℝ) (C : ℝ) (n : ℕ) :
    weakIntegral f (C • shifted_point_mass_difference n) =
      C * (f (reciprocal_unit_interval_point n) - f (double_reciprocal_unit_interval_point n)) := by
  have hxy : reciprocal_unit_interval_point n ≠ double_reciprocal_unit_interval_point n :=
    reciprocal_point_ne_double_reciprocal_point n
  by_cases hC : 0 ≤ C
  · -- Nonnegative scalars preserve the positive and negative parts.
    rw [shifted_point_mass_difference_def, weakIntegral, SignedMeasure.toJordanDecomposition_smul_real,
      toJordanDecomposition_diracDifference hxy,
      JordanDecomposition.real_smul_posPart_nonneg, JordanDecomposition.real_smul_negPart_nonneg]
    · simp [diracDifferenceJordanDecomposition, integral_smul_measure, smul_eq_mul,
        Real.toNNReal_of_nonneg hC, sub_eq_add_neg, mul_sub, hC]
      change
        C * f (reciprocal_unit_interval_point n) - C * f (double_reciprocal_unit_interval_point n) =
          C * (f (reciprocal_unit_interval_point n) - f (double_reciprocal_unit_interval_point n))
      ring
    · exact hC
    · exact hC
  · -- Negative scalars swap the positive and negative parts, but the final scalar formula remains
    -- the same after regrouping the two evaluations.
    rw [shifted_point_mass_difference_def, weakIntegral, SignedMeasure.toJordanDecomposition_smul_real,
      toJordanDecomposition_diracDifference hxy,
      JordanDecomposition.real_smul_posPart_neg, JordanDecomposition.real_smul_negPart_neg]
    · have hnonneg : 0 ≤ -C := by linarith
      simp [diracDifferenceJordanDecomposition, integral_smul_measure, smul_eq_mul,
        Real.toNNReal_of_nonneg hnonneg, sub_eq_add_neg, mul_sub, hnonneg]
      change
        (-C) * f (double_reciprocal_unit_interval_point n) +
            -((-C) * f (reciprocal_unit_interval_point n)) =
          C * (f (reciprocal_unit_interval_point n) +
            -f (double_reciprocal_unit_interval_point n))
      ring
    · exact lt_of_not_ge hC
    · exact lt_of_not_ge hC

/-- Helper for Exercise 13.2.7: the reciprocal support points converge to `0` in `[0,1]`. -/
lemma reciprocal_unit_interval_point_tendsto_zero :
    Tendsto reciprocal_unit_interval_point atTop (𝓝 (0 : I)) := by
  refine tendsto_subtype_rng.2 ?_
  simpa [reciprocal_unit_interval_point_val] using
    (tendsto_mul_add_inv_atTop_nhds_zero 1 2 one_ne_zero).comp tendsto_natCast_atTop_atTop

/-- Helper for Exercise 13.2.7: the doubled reciprocal support points also converge to `0` in
`[0,1]`. -/
lemma double_reciprocal_unit_interval_point_tendsto_zero :
    Tendsto double_reciprocal_unit_interval_point atTop (𝓝 (0 : I)) := by
  refine tendsto_subtype_rng.2 ?_
  simpa [double_reciprocal_unit_interval_point_val, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using
    (Filter.Tendsto.const_mul (2 : ℝ)
      ((tendsto_mul_add_inv_atTop_nhds_zero 1 2 one_ne_zero).comp tendsto_natCast_atTop_atTop))

/-- Helper for Exercise 13.2.7: every bounded continuous test function has vanishing evaluation
difference along the two support-point sequences. -/
lemma boundedContinuous_reciprocalDifference_tendsto_zero (f : I →ᵇ ℝ) :
    Tendsto
      (fun n ↦ f (reciprocal_unit_interval_point n) - f (double_reciprocal_unit_interval_point n))
      atTop (𝓝 0) := by
  -- Both support-point sequences converge to `0`, so continuity of `f` forces their values to
  -- converge to the same limit.
  have hrec :
      Tendsto (fun n ↦ f (reciprocal_unit_interval_point n)) atTop (𝓝 (f 0)) :=
    (f.continuous.continuousAt.tendsto).comp reciprocal_unit_interval_point_tendsto_zero
  have hdouble :
      Tendsto (fun n ↦ f (double_reciprocal_unit_interval_point n)) atTop (𝓝 (f 0)) :=
    (f.continuous.continuousAt.tendsto).comp double_reciprocal_unit_interval_point_tendsto_zero
  simpa using hrec.sub hdouble

/-- Part (i): every fixed rescaling of the shifted Dirac-difference sequence converges weakly to
zero for the signed weak-convergence notion from this exercise. -/
theorem weakly_convergent_rescalings_of_shifted_point_mass_difference {C : ℝ} :
    weaklyConvergesTo (fun n ↦ C • shifted_point_mass_difference n) 0 := by
  -- Rewrite weak convergence to `0` into convergence of all bounded continuous test integrals.
  rw [weaklyConvergesTo_zero_iff]
  intro f
  -- The weak integral is just a constant multiple of the evaluation difference from the two
  -- support points, and that difference already tends to `0`.
  simpa only [weakIntegral_smul_shiftedPointMassDifference, mul_zero] using
    (Tendsto.const_mul C (boundedContinuous_reciprocalDifference_tendsto_zero f))

/-- Helper for Exercise 13.2.7: in a compatible metric for the weak topology, every fixed
integer rescaling of `shifted_point_mass_difference` eventually lies in the reciprocal metric ball
around `0`. -/
lemma existsMetricThresholdForFixedRescaling
    [MetricSpace (SignedMeasure I)] (k : ℕ)
    (hconv :
      Tendsto
        (fun n ↦
          dist ((((k + 1 : ℝ) • shifted_point_mass_difference n) : SignedMeasure I)) 0)
        atTop (𝓝 0)) :
    ∃ N : ℕ, ∀ n ≥ N,
      dist (((k + 1 : ℝ) • shifted_point_mass_difference n) : SignedMeasure I) 0 <
        ((k + 1 : ℝ)⁻¹) := by
  -- Route correction: the original statement used the ambient weak-topology neighborhood filter,
  -- but the metric estimate only needs the already-normalized distance-to-zero convergence.
  rcases Metric.tendsto_atTop.1 hconv ((k + 1 : ℝ)⁻¹) (by positivity) with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg)] using hN n hn

/-- Helper for Exercise 13.2.7: the recursive envelope of a threshold function dominates both the
original thresholds and the index, so it can drive a diagonal `Nat.findGreatest` construction. -/
def diagonalThresholdEnvelope (N : ℕ → ℕ) : ℕ → ℕ
  | 0 => N 0
  | k + 1 => max (k + 1) (max (N (k + 1)) (diagonalThresholdEnvelope N k))

/-- Helper for Exercise 13.2.7: the threshold envelope is monotone. -/
lemma diagonalThresholdEnvelope_mono (N : ℕ → ℕ) :
    Monotone (diagonalThresholdEnvelope N) := by
  intro n m hnm
  induction hnm with
  | refl =>
      rfl
  | @step m hnm ih =>
      -- Each recursive step keeps the previous envelope value as one of the `max` entries.
      exact le_trans ih <| le_trans (le_max_right _ _) (le_max_right _ _)

/-- Helper for Exercise 13.2.7: every index is bounded by its threshold envelope. -/
lemma le_diagonalThresholdEnvelope (N : ℕ → ℕ) (k : ℕ) :
    k ≤ diagonalThresholdEnvelope N k := by
  induction k with
  | zero =>
      exact Nat.zero_le _
  | succ k ih =>
      -- The recursive definition inserts `k + 1` as the leading `max` entry.
      exact le_max_left _ _

/-- Helper for Exercise 13.2.7: the threshold envelope also dominates the original threshold
function. -/
lemma threshold_le_diagonalThresholdEnvelope (N : ℕ → ℕ) (k : ℕ) :
    N k ≤ diagonalThresholdEnvelope N k := by
  cases k with
  | zero =>
      rfl
  | succ k =>
      -- The recursive step inserts the new threshold as one of the `max` entries.
      exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- Helper for Exercise 13.2.7: `Nat.findGreatest` applied to the threshold envelope gives the
current diagonal rescaling index, shifted by one to keep the scales strictly positive. -/
def diagonalNatRescaling (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k ↦ diagonalThresholdEnvelope N k ≤ n) n + 1

/-- Helper for Exercise 13.2.7: the diagonal rescaling sequence is monotone. -/
lemma diagonalNatRescaling_mono (N : ℕ → ℕ) : Monotone (diagonalNatRescaling N) := by
  intro n m hnm
  -- Increase both the predicate and the search range in the `Nat.findGreatest` term.
  apply Nat.succ_le_succ
  exact Nat.findGreatest_mono
    (P := fun k ↦ diagonalThresholdEnvelope N k ≤ n)
    (Q := fun k ↦ diagonalThresholdEnvelope N k ≤ m)
    (fun k hk ↦ le_trans hk hnm) hnm

/-- Helper for Exercise 13.2.7: once the zeroth envelope value lies below `n`, the diagonal
rescaling index chosen at `n` still satisfies the envelope predicate. -/
lemma diagonalNatRescaling_spec (N : ℕ → ℕ) {n : ℕ}
    (hn : diagonalThresholdEnvelope N 0 ≤ n) :
    diagonalThresholdEnvelope N (diagonalNatRescaling N n - 1) ≤ n := by
  -- The zeroth envelope value supplies the witness needed to read back the `findGreatest`
  -- predicate at the selected index.
  have hfind :
      diagonalThresholdEnvelope N
          (Nat.findGreatest (fun k ↦ diagonalThresholdEnvelope N k ≤ n) n) ≤ n :=
    Nat.findGreatest_spec
      (P := fun k ↦ diagonalThresholdEnvelope N k ≤ n)
      (m := 0) (Nat.zero_le n) hn
  simpa [diagonalNatRescaling]

/-- Helper for Exercise 13.2.7: evaluating the diagonal rescaling at the envelope point for `k`
produces a scale at least `k + 1`. -/
lemma succ_le_diagonalNatRescaling_at_threshold (N : ℕ → ℕ) (k : ℕ) :
    k + 1 ≤ diagonalNatRescaling N (diagonalThresholdEnvelope N k) := by
  -- At the envelope point for `k`, the predicate used by `Nat.findGreatest` already holds at `k`.
  apply Nat.succ_le_succ
  exact Nat.le_findGreatest
    (le_diagonalThresholdEnvelope N k)
    (le_rfl : diagonalThresholdEnvelope N k ≤ diagonalThresholdEnvelope N k)

/-- Helper for Exercise 13.2.7: the diagonal rescaling tends to infinity. -/
lemma tendsto_diagonalNatRescaling_atTop (N : ℕ → ℕ) :
    Tendsto (diagonalNatRescaling N) atTop atTop := by
  -- The diagonal rescaling is monotone and already reaches scale `k + 1` at the envelope point
  -- for `k`, so it is unbounded.
  refine tendsto_atTop_atTop_of_monotone (diagonalNatRescaling_mono N) ?_
  intro k
  refine ⟨diagonalThresholdEnvelope N k, ?_⟩
  exact le_trans (Nat.le_succ k) (succ_le_diagonalNatRescaling_at_threshold N k)

/-- Part (ii): if the weak topology on signed measures over `[0,1]` were metrizable, one could
choose rescaling factors tending to infinity while retaining weak convergence to zero. -/
theorem metrizable_weak_convergence_yields_unbounded_rescalings
    [TopologicalSpace.MetrizableSpace (SignedMeasure I)] :
    ∃ C : ℕ → ℝ,
      Monotone C ∧ Tendsto C atTop atTop ∧ (∀ n, 0 < C n) ∧
        weaklyConvergesTo (fun n ↦ C n • shifted_point_mass_difference n) 0 := by
  -- Route correction: after installing a compatible metric, the diagonal argument is entirely
  -- metric and needs no extra topology-transport theorem.
  let instMetric : MetricSpace (SignedMeasure I) :=
    TopologicalSpace.metrizableSpaceMetric (SignedMeasure I)
  let _ : MetricSpace (SignedMeasure I) := instMetric
  let _ : TopologicalSpace (SignedMeasure I) :=
    instMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hfixed :
      ∀ k : ℕ,
        Tendsto
          (fun n ↦ (((k + 1 : ℝ) • shifted_point_mass_difference n) : SignedMeasure I))
          atTop (𝓝 0) := by
    intro k
    simpa [weaklyConvergesTo] using
      (weakly_convergent_rescalings_of_shifted_point_mass_difference (C := (k + 1 : ℝ)))
  have hthresholds :
      ∀ k : ℕ,
        ∃ N : ℕ, ∀ n ≥ N,
          dist (((k + 1 : ℝ) • shifted_point_mass_difference n) : SignedMeasure I) 0 <
            ((k + 1 : ℝ)⁻¹) := by
    intro k
    rcases Metric.tendsto_atTop.1 (hfixed k) ((k + 1 : ℝ)⁻¹) (by positivity) with ⟨N, hN⟩
    exact ⟨N, hN⟩
  choose N hN using hthresholds
  refine ⟨fun n ↦ diagonalNatRescaling N n, ?_, ?_, ?_, ?_⟩
  · -- The diagonal rescaling is monotone on `ℕ`, hence also after coercion to `ℝ`.
    intro m n hmn
    show (diagonalNatRescaling N m : ℝ) ≤ diagonalNatRescaling N n
    exact_mod_cast diagonalNatRescaling_mono N hmn
  · -- Coercing the unbounded natural diagonal sequence preserves convergence to `∞`.
    exact tendsto_natCast_atTop_atTop.comp (tendsto_diagonalNatRescaling_atTop N)
  · -- Each diagonal scale is at least `1`.
    intro n
    show (0 : ℝ) < diagonalNatRescaling N n
    exact_mod_cast Nat.succ_pos _
  · -- The diagonal metric estimate reduces the varying rescaling back to the fixed-scale bounds.
    rw [weaklyConvergesTo]
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    have hInv :
        Tendsto (fun n ↦ (((diagonalNatRescaling N n : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_diagonalNatRescaling_atTop N))
    rcases Metric.tendsto_atTop.1 hInv ε hε with ⟨M, hM⟩
    refine ⟨max M (diagonalThresholdEnvelope N 0), fun n hn => ?_⟩
    have hnM : M ≤ n := le_trans (le_max_left _ _) hn
    have hn0 : diagonalThresholdEnvelope N 0 ≤ n := le_trans (le_max_right _ _) hn
    let k := Nat.findGreatest (fun j ↦ diagonalThresholdEnvelope N j ≤ n) n
    have hdiag :
        diagonalThresholdEnvelope N k ≤ n := by
      exact
        Nat.findGreatest_spec
          (P := fun j ↦ diagonalThresholdEnvelope N j ≤ n)
          (m := 0) (Nat.zero_le n) hn0
    have hthreshold : N k ≤ n := le_trans (threshold_le_diagonalThresholdEnvelope N k) hdiag
    have hdist :
        dist
            ((((diagonalNatRescaling N n : ℕ) : ℝ) • shifted_point_mass_difference n) :
              SignedMeasure I)
            0 <
          (((diagonalNatRescaling N n : ℕ) : ℝ)⁻¹) := by
      simpa [diagonalNatRescaling, k] using hN k n hthreshold
    have hsmall :
        (((diagonalNatRescaling N n : ℕ) : ℝ)⁻¹) < ε := by
      simpa [Real.dist_eq, abs_of_nonneg (inv_nonneg.2 (show (0 : ℝ) ≤ diagonalNatRescaling N n by positivity))]
        using hM n hnM
    exact lt_trans hdist hsmall

/-- The closed dyadic subset of `[0,1]` used in Exercise 13.2.7. It consists of the limit point
`0` together with the nodes `2^{-n}`. -/
def dyadicNodeSet : Set I :=
  Set.insert (0 : I) (Set.range dyadic_unit_interval_point)

/-- Helper for Exercise 13.2.7: the dyadic points `2^{-n}` converge to `0` in `[0,1]`. -/
lemma dyadic_unit_interval_point_tendsto_zero :
    Tendsto dyadic_unit_interval_point atTop (𝓝 (0 : I)) := by
  -- The ambient real coordinates are the reciprocal powers `2^{-n}`.
  refine tendsto_subtype_rng.2 ?_
  simpa [dyadic_unit_interval_point_val] using
    (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))

/-- Helper for Exercise 13.2.7: the dyadic subset `dyadicNodeSet` is closed. -/
lemma isClosed_dyadicNodeSet : IsClosed dyadicNodeSet := by
  -- The set is the limit point `0` together with the convergent sequence `2^{-n}`.
  simpa [dyadicNodeSet] using
    (dyadic_unit_interval_point_tendsto_zero.isCompact_insert_range).isClosed

/-- Helper for Exercise 13.2.7: the dyadic points are strictly decreasing in their real values. -/
lemma dyadic_unit_interval_point_strictAnti :
    StrictAnti fun n ↦ ((dyadic_unit_interval_point n : I) : ℝ) := by
  intro m n hmn
  -- Compare the reciprocals by the strict monotonicity of `n ↦ 2 ^ n`.
  change ((2 : ℝ) ^ n)⁻¹ < ((2 : ℝ) ^ m)⁻¹
  exact (inv_lt_inv₀ (pow_pos zero_lt_two _) (pow_pos zero_lt_two _)).2
    (pow_lt_pow_right₀ one_lt_two hmn)

/-- Helper for Exercise 13.2.7: the dyadic node map is injective. -/
lemma dyadic_unit_interval_point_injective :
    Function.Injective dyadic_unit_interval_point := by
  intro m n hmn
  -- The strict antitonicity of the real coordinates rules out collisions.
  apply dyadic_unit_interval_point_strictAnti.injective
  simpa using congrArg (fun x : I ↦ (x : ℝ)) hmn

/-- Helper for Exercise 13.2.7: no dyadic point coincides with `0`. -/
lemma dyadic_unit_interval_point_ne_zero (n : ℕ) : dyadic_unit_interval_point n ≠ 0 := by
  intro hzero
  have hreal : (((2 : ℝ) ^ n)⁻¹ : ℝ) = 0 := by
    simpa [dyadic_unit_interval_point_val] using congrArg (fun x : I ↦ (x : ℝ)) hzero
  exact (inv_ne_zero (pow_ne_zero _ two_ne_zero)) hreal

/-- Helper for Exercise 13.2.7: reciprocal square roots vanish when the underlying sequence tends
to `∞`. -/
lemma inverseSqrt_tendsto_zero_of_tendsto_atTop {C : ℕ → ℝ}
    (hC_top : Tendsto C atTop atTop) :
    Tendsto (fun n ↦ (Real.sqrt (C n))⁻¹) atTop (𝓝 0) := by
  -- Push the divergence through `Real.sqrt`, then invert the resulting sequence.
  exact (Real.tendsto_sqrt_atTop.comp hC_top).inv_tendsto_atTop

/-- Helper for Exercise 13.2.7: the prescribed dyadic node values tend to `0` whenever
`C n → ∞`. -/
lemma dyadicNodeCoefficient_tendsto_zero {C : ℕ → ℝ}
    (hC_pos : ∀ n, 0 < C n) (hC_top : Tendsto C atTop atTop) :
    Tendsto (fun n ↦ (-1 : ℝ) ^ n / Real.sqrt (C n)) atTop (𝓝 0) := by
  -- Remove the alternating sign by passing to absolute values.
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hInv : Tendsto (fun n ↦ (Real.sqrt (C n))⁻¹) atTop (𝓝 0) :=
    inverseSqrt_tendsto_zero_of_tendsto_atTop hC_top
  refine hInv.congr' <| Filter.Eventually.of_forall fun n ↦ ?_
  -- The numerator has absolute value `1`, and the denominator is positive.
  have hsqrt : 0 < Real.sqrt (C n) := Real.sqrt_pos.2 (hC_pos n)
  calc
    (Real.sqrt (C n))⁻¹ = 1 / Real.sqrt (C n) := by rw [one_div]
    _ = |(-1 : ℝ) ^ n| / |Real.sqrt (C n)| := by
      rw [abs_of_nonneg hsqrt.le]
      simp
    _ = |(-1 : ℝ) ^ n / Real.sqrt (C n)| := (abs_div _ _).symm

/-- Helper for Exercise 13.2.7: the shifted geometric point `1 / (3 * 2^n)` belongs to `[0,1]`. -/
lemma shiftedDyadic_inverse_mem_unit_interval (n : ℕ) :
    ((((3 : ℝ) * 2 ^ n)⁻¹) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · have hdenom : (1 : ℝ) ≤ (3 : ℝ) * 2 ^ n := by
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.one_le_two_pow
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ n by positivity, hpow]
    exact (inv_le_one₀ (by positivity : 0 < (3 : ℝ) * 2 ^ n)).2 hdenom

/-- Helper for Exercise 13.2.7: the shifted geometric node `1 / (3 * 2^n)` in `[0,1]`. -/
def shiftedDyadicUnitIntervalPoint (n : ℕ) : I :=
  ⟨((3 : ℝ) * 2 ^ n)⁻¹, shiftedDyadic_inverse_mem_unit_interval n⟩

/-- Helper for Exercise 13.2.7: the real value of `shiftedDyadicUnitIntervalPoint`. -/
theorem shiftedDyadicUnitIntervalPoint_val (n : ℕ) :
    ((shiftedDyadicUnitIntervalPoint n : I) : ℝ) = ((3 : ℝ) * 2 ^ n)⁻¹ :=
  rfl

/-- Helper for Exercise 13.2.7: the sparse subsequence index whose two support points become
consecutive shifted dyadic nodes. -/
def shiftedDyadicSubsequenceIndex (n : ℕ) : ℕ :=
  3 * 2 ^ (n + 1) - 2

/-- Helper for Exercise 13.2.7: the reciprocal support point at the sparse index is the next
shifted dyadic node. -/
lemma reciprocal_shiftedDyadicSubsequenceIndex (n : ℕ) :
    reciprocal_unit_interval_point (shiftedDyadicSubsequenceIndex n) =
      shiftedDyadicUnitIntervalPoint (n + 1) := by
  apply Subtype.ext
  rw [reciprocal_unit_interval_point_val, shiftedDyadicUnitIntervalPoint_val,
    shiftedDyadicSubsequenceIndex]
  have hdenom : (((3 * 2 ^ (n + 1) - 2 : ℕ) : ℝ) + 2) = (3 : ℝ) * 2 ^ (n + 1) := by
    have hsub : 2 ≤ 3 * 2 ^ (n + 1) := by
      have hpow : 1 ≤ 2 ^ (n + 1) := Nat.succ_le_of_lt (Nat.two_pow_pos _)
      nlinarith
    exact_mod_cast Nat.sub_add_cancel hsub
  rw [hdenom]

/-- Helper for Exercise 13.2.7: the doubled reciprocal support point at the sparse index is the
previous shifted dyadic node. -/
lemma doubleReciprocal_shiftedDyadicSubsequenceIndex (n : ℕ) :
    double_reciprocal_unit_interval_point (shiftedDyadicSubsequenceIndex n) =
      shiftedDyadicUnitIntervalPoint n := by
  apply Subtype.ext
  rw [double_reciprocal_unit_interval_point_val, shiftedDyadicUnitIntervalPoint_val,
    shiftedDyadicSubsequenceIndex]
  have hdenom : (((3 * 2 ^ (n + 1) - 2 : ℕ) : ℝ) + 2) = (3 : ℝ) * 2 ^ (n + 1) := by
    have hsub : 2 ≤ 3 * 2 ^ (n + 1) := by
      have hpow : 1 ≤ 2 ^ (n + 1) := Nat.succ_le_of_lt (Nat.two_pow_pos _)
      nlinarith
    exact_mod_cast Nat.sub_add_cancel hsub
  rw [hdenom]
  have hpow : (2 : ℝ) ^ (n + 1) = (2 : ℝ) * 2 ^ n := by
    rw [pow_succ']
  rw [hpow]
  field_simp

/-- Helper for Exercise 13.2.7: the shifted dyadic nodes also converge to `0` in `[0,1]`. -/
lemma shiftedDyadicUnitIntervalPoint_tendsto_zero :
    Tendsto shiftedDyadicUnitIntervalPoint atTop (𝓝 (0 : I)) := by
  refine tendsto_subtype_rng.2 ?_
  have htop : Tendsto (fun n ↦ (3 : ℝ) * 2 ^ n) atTop atTop := by
    exact Tendsto.const_mul_atTop (show (0 : ℝ) < 3 by norm_num)
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  -- The real coordinates are reciprocals of a sequence diverging to `∞`.
  change Tendsto (fun n ↦ ((3 : ℝ) * 2 ^ n)⁻¹) atTop (𝓝 0)
  exact tendsto_inv_atTop_zero.comp htop

/-- Helper for Exercise 13.2.7: the shifted dyadic points are strictly decreasing in their real
coordinates. -/
lemma shiftedDyadicUnitIntervalPoint_strictAnti :
    StrictAnti fun n ↦ ((shiftedDyadicUnitIntervalPoint n : I) : ℝ) := by
  intro m n hmn
  -- Compare the reciprocals after moving to the real-coordinate formula.
  change ((3 : ℝ) * 2 ^ n)⁻¹ < ((3 : ℝ) * 2 ^ m)⁻¹
  refine (inv_lt_inv₀ (by positivity : 0 < (3 : ℝ) * 2 ^ n)
    (by positivity : 0 < (3 : ℝ) * 2 ^ m)).2 ?_
  have hpow : (2 : ℝ) ^ m < (2 : ℝ) ^ n := pow_lt_pow_right₀ one_lt_two hmn
  nlinarith

/-- Helper for Exercise 13.2.7: the shifted dyadic node map is injective. -/
lemma shiftedDyadicUnitIntervalPoint_injective :
    Function.Injective shiftedDyadicUnitIntervalPoint := by
  intro m n hmn
  apply shiftedDyadicUnitIntervalPoint_strictAnti.injective
  simpa using congrArg (fun x : I ↦ (x : ℝ)) hmn

/-- Helper for Exercise 13.2.7: no shifted dyadic node coincides with `0`. -/
lemma shiftedDyadicUnitIntervalPoint_ne_zero (n : ℕ) :
    shiftedDyadicUnitIntervalPoint n ≠ 0 := by
  intro hzero
  have hreal : (((3 : ℝ) * 2 ^ n)⁻¹ : ℝ) = 0 := by
    simpa [shiftedDyadicUnitIntervalPoint_val] using congrArg (fun x : I ↦ (x : ℝ)) hzero
  exact (inv_ne_zero (by positivity : (3 : ℝ) * 2 ^ n ≠ 0)) hreal

/-- Helper for Exercise 13.2.7: a shifted dyadic node lies strictly between the neighboring dyadic
nodes `2 ^ (-(n + 2))` and `2 ^ (-(n + 1))`. -/
lemma dyadic_twoSucc_lt_shiftedDyadicUnitIntervalPoint (n : ℕ) :
    ((dyadic_unit_interval_point (n + 2) : I) : ℝ) <
      ((shiftedDyadicUnitIntervalPoint n : I) : ℝ) := by
  rw [dyadic_unit_interval_point_val, shiftedDyadicUnitIntervalPoint_val]
  have hpow : (2 : ℝ) ^ (n + 2) = (4 : ℝ) * 2 ^ n := by
    rw [pow_add, pow_two]
    ring
  rw [hpow]
  exact (inv_lt_inv₀ (by positivity : 0 < (4 : ℝ) * 2 ^ n)
      (by positivity : 0 < (3 : ℝ) * 2 ^ n)).2 <| by
    have : (3 : ℝ) * 2 ^ n < (4 : ℝ) * 2 ^ n := by
      nlinarith [show (0 : ℝ) < 2 ^ n by positivity]
    simpa using this

/-- Helper for Exercise 13.2.7: a shifted dyadic node lies strictly below the preceding dyadic
node `2 ^ (-(n + 1))`. -/
lemma shiftedDyadicUnitIntervalPoint_lt_dyadic_succ (n : ℕ) :
    ((shiftedDyadicUnitIntervalPoint n : I) : ℝ) <
      ((dyadic_unit_interval_point (n + 1) : I) : ℝ) := by
  rw [dyadic_unit_interval_point_val, shiftedDyadicUnitIntervalPoint_val]
  have hpow : (2 : ℝ) ^ (n + 1) = (2 : ℝ) * 2 ^ n := by
    rw [pow_succ']
  rw [hpow]
  exact (inv_lt_inv₀ (by positivity : 0 < (3 : ℝ) * 2 ^ n)
      (by positivity : 0 < (2 : ℝ) * 2 ^ n)).2 <| by
    have : (2 : ℝ) * 2 ^ n < (3 : ℝ) * 2 ^ n := by
      nlinarith [show (0 : ℝ) < 2 ^ n by positivity]
    simpa [mul_comm] using this

/-- Helper for Exercise 13.2.7: the dyadic and shifted geometric node families are disjoint. -/
lemma dyadic_ne_shiftedDyadicUnitIntervalPoint (m n : ℕ) :
    dyadic_unit_interval_point m ≠ shiftedDyadicUnitIntervalPoint n := by
  intro h
  have hleft :
      ((dyadic_unit_interval_point (n + 2) : I) : ℝ) <
        ((shiftedDyadicUnitIntervalPoint n : I) : ℝ) :=
    dyadic_twoSucc_lt_shiftedDyadicUnitIntervalPoint n
  have hright :
      ((shiftedDyadicUnitIntervalPoint n : I) : ℝ) <
        ((dyadic_unit_interval_point (n + 1) : I) : ℝ) :=
    shiftedDyadicUnitIntervalPoint_lt_dyadic_succ n
  have hreal :
      ((dyadic_unit_interval_point m : I) : ℝ) =
        ((shiftedDyadicUnitIntervalPoint n : I) : ℝ) := by
    simpa using congrArg (fun x : I ↦ (x : ℝ)) h
  by_cases hm_le : m ≤ n + 1
  · have hm_lt : m < n + 2 := lt_of_le_of_lt hm_le (Nat.lt_succ_self _)
    have hbound :
        ((dyadic_unit_interval_point (n + 1) : I) : ℝ) ≤
          ((dyadic_unit_interval_point m : I) : ℝ) := by
      exact dyadic_unit_interval_point_strictAnti.antitone hm_le
    linarith
  · have hmn : n + 2 ≤ m := by
      exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hm_le)
    have hbound :
        ((dyadic_unit_interval_point m : I) : ℝ) ≤
          ((dyadic_unit_interval_point (n + 2) : I) : ℝ) := by
      exact dyadic_unit_interval_point_strictAnti.antitone hmn
    linarith

/-- The mixed closed node set used to prescribe both the dyadic interpolation values and the
support-aligned obstruction values. -/
def obstructionNodeSet : Set I :=
  dyadicNodeSet ∪ Set.range shiftedDyadicUnitIntervalPoint

/-- Helper for Exercise 13.2.7: the mixed node set is closed. -/
lemma isClosed_obstructionNodeSet : IsClosed obstructionNodeSet := by
  have hshift :
      IsClosed (Set.insert (0 : I) (Set.range shiftedDyadicUnitIntervalPoint)) := by
    -- The shifted dyadic nodes form another sequence converging to `0`.
    simpa using (shiftedDyadicUnitIntervalPoint_tendsto_zero.isCompact_insert_range).isClosed
  have hrewrite :
      obstructionNodeSet =
        dyadicNodeSet ∪ Set.insert (0 : I) (Set.range shiftedDyadicUnitIntervalPoint) := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Set.mem_insert_of_mem _ hx)
    · intro hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · rcases hx with rfl | hx
        · exact Or.inl (by
            change ((0 : I) = 0 ∨ (0 : I) ∈ Set.range dyadic_unit_interval_point)
            exact Or.inl rfl)
        · exact Or.inr hx
  -- Rewrite the obstruction set as a union of two closed sets, each carrying the common limit
  -- point `0`.
  rw [hrewrite]
  exact isClosed_dyadicNodeSet.union hshift

/-- Helper for Exercise 13.2.7: the shifted obstruction values also tend to `0` along the shifted
node family. -/
lemma shiftedDyadicNodeCoefficient_tendsto_zero {C : ℕ → ℝ}
    (hC_pos : ∀ n, 0 < C n) (hC_top : Tendsto C atTop atTop) :
    Tendsto
      (fun n ↦ if Odd n then (Real.sqrt (C (3 * 2 ^ n - 2)))⁻¹ else 0)
      atTop (𝓝 0) := by
  -- The sparse shifted indices tend to `∞`, so the inverse square-root branch tends to `0`; the
  -- parity gate only removes values and is therefore controlled by absolute values.
  have hindex_top : Tendsto (fun n ↦ 3 * 2 ^ n - 2) atTop atTop := by
    refine tendsto_atTop_mono (fun n ↦ ?_) tendsto_id
    have hpow_dom : n ≤ 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
    have hpow_le : 2 ^ n ≤ 3 * 2 ^ n - 2 := by
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    exact le_trans hpow_dom hpow_le
  have hInv :
      Tendsto (fun n ↦ (Real.sqrt (C (3 * 2 ^ n - 2)))⁻¹) atTop (𝓝 0) :=
    inverseSqrt_tendsto_zero_of_tendsto_atTop (hC_top.comp hindex_top)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero (fun _ ↦ abs_nonneg _) (fun n ↦ ?_) hInv
  dsimp
  by_cases hodd : Odd n
  · rw [if_pos hodd]
    simp [abs_of_nonneg, Real.sqrt_nonneg]
  · rw [if_neg hodd]
    simp [Real.sqrt_nonneg]

/-- Helper for Exercise 13.2.7: the punctured obstruction set is exactly the union of the dyadic
and shifted dyadic node families. -/
lemma mem_obstructionNodeSet_diff_zero_iff {x : I} :
    x ∈ obstructionNodeSet \ ({0} : Set I) ↔
      (∃ n, x = dyadic_unit_interval_point n) ∨
        ∃ n, x = shiftedDyadicUnitIntervalPoint n := by
  constructor
  · intro hx
    rcases hx.1 with hx | hx
    · simp only [dyadicNodeSet, Set.mem_insert_iff, Set.mem_range] at hx
      rcases hx with rfl | ⟨n, rfl⟩
      · exact (hx.2 rfl).elim
      · exact Or.inl ⟨n, rfl⟩
    · rcases hx with ⟨n, rfl⟩
      exact Or.inr ⟨n, rfl⟩
  · intro hx
    constructor
    · rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
      · exact Or.inl (by
          change dyadic_unit_interval_point n = 0 ∨
              dyadic_unit_interval_point n ∈ Set.range dyadic_unit_interval_point
          exact Or.inr ⟨n, rfl⟩)
      · exact Or.inr (by
          exact ⟨n, rfl⟩)
    · rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
      · simp [dyadic_unit_interval_point_ne_zero n]
      · simp [shiftedDyadicUnitIntervalPoint_ne_zero n]

/-- Helper for Exercise 13.2.7: the dyadic node `1` is isolated inside the punctured obstruction
set. -/
lemma dyadicZero_hasSingletonNeighborhood :
    ∃ U : Set I, IsOpen U ∧
      U ∩ (obstructionNodeSet \ ({0} : Set I)) = {dyadic_unit_interval_point 0} := by
  let a : ℝ := ((dyadic_unit_interval_point 1 : I) : ℝ)
  let U : Set I := {y : I | a < (y : ℝ)}
  have hUopen : IsOpen U := by
    -- Open rays in the ambient real coordinate restrict to open sets on `[0,1]`.
    simpa [U] using isOpen_lt continuous_const continuous_subtype_val
  refine ⟨U, hUopen, ?_⟩
  ext y
  constructor
  · intro hy
    rcases mem_obstructionNodeSet_diff_zero_iff.mp hy.2 with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · cases m with
      | zero =>
          simp
      | succ m =>
          have hbound :
              ((dyadic_unit_interval_point (m + 1) : I) : ℝ) ≤
                ((dyadic_unit_interval_point 1 : I) : ℝ) :=
            dyadic_unit_interval_point_strictAnti.antitone (Nat.succ_le_succ (Nat.zero_le _))
          exact (not_lt_of_ge hbound hy.1).elim
    · have hbound :
          ((shiftedDyadicUnitIntervalPoint m : I) : ℝ) ≤
            ((shiftedDyadicUnitIntervalPoint 0 : I) : ℝ) :=
        shiftedDyadicUnitIntervalPoint_strictAnti.antitone (Nat.zero_le _)
      have hsep :
          ((shiftedDyadicUnitIntervalPoint 0 : I) : ℝ) <
            ((dyadic_unit_interval_point 1 : I) : ℝ) :=
        shiftedDyadicUnitIntervalPoint_lt_dyadic_succ 0
      have hlt :
          ((shiftedDyadicUnitIntervalPoint m : I) : ℝ) <
            ((dyadic_unit_interval_point 1 : I) : ℝ) :=
        lt_of_le_of_lt hbound hsep
      exact (not_lt_of_ge hlt.le hy.1).elim
  · rintro rfl
    constructor
    · exact dyadic_unit_interval_point_strictAnti (by omega)
    · exact (mem_obstructionNodeSet_diff_zero_iff).2 <| Or.inl ⟨0, rfl⟩

/-- Helper for Exercise 13.2.7: every positive dyadic node is isolated inside the punctured
obstruction set. -/
lemma dyadicSucc_hasSingletonNeighborhood (n : ℕ) :
    ∃ U : Set I, IsOpen U ∧
      U ∩ (obstructionNodeSet \ ({0} : Set I)) = {dyadic_unit_interval_point (n + 1)} := by
  cases n with
  | zero =>
      let a : ℝ := ((shiftedDyadicUnitIntervalPoint 0 : I) : ℝ)
      let b : ℝ := ((dyadic_unit_interval_point 0 : I) : ℝ)
      let U : Set I := {y : I | a < (y : ℝ) ∧ (y : ℝ) < b}
      have hUopen : IsOpen U := by
        -- The first positive dyadic node lies between the top dyadic node and the first shifted
        -- node, so that interval isolates it.
        simpa [U] using
          (isOpen_lt continuous_const continuous_subtype_val).inter
            (isOpen_lt continuous_subtype_val continuous_const)
      refine ⟨U, hUopen, ?_⟩
      ext y
      constructor
      · intro hy
        rcases mem_obstructionNodeSet_diff_zero_iff.mp hy.2 with ⟨m, rfl⟩ | ⟨m, rfl⟩
        · cases m with
          | zero =>
              exact (not_lt_of_ge le_rfl hy.1.2).elim
          | succ m =>
              cases m with
              | zero =>
                  simp
              | succ m =>
                  have hbound :
                      ((dyadic_unit_interval_point (m + 2) : I) : ℝ) ≤
                        ((dyadic_unit_interval_point 2 : I) : ℝ) :=
                    dyadic_unit_interval_point_strictAnti.antitone (by omega)
                  have hsep :
                      ((dyadic_unit_interval_point 2 : I) : ℝ) <
                        ((shiftedDyadicUnitIntervalPoint 0 : I) : ℝ) :=
                    dyadic_twoSucc_lt_shiftedDyadicUnitIntervalPoint 0
                  have hlt :
                      ((dyadic_unit_interval_point (m + 2) : I) : ℝ) <
                        ((shiftedDyadicUnitIntervalPoint 0 : I) : ℝ) :=
                    lt_of_le_of_lt hbound hsep
                  exact (not_lt_of_ge hlt.le hy.1.1).elim
        · cases m with
          | zero =>
              exact (not_lt_of_ge le_rfl hy.1.1).elim
          | succ m =>
              have hbound :
                  ((shiftedDyadicUnitIntervalPoint (m + 1) : I) : ℝ) ≤
                    ((shiftedDyadicUnitIntervalPoint 0 : I) : ℝ) :=
                shiftedDyadicUnitIntervalPoint_strictAnti.antitone (Nat.zero_le _)
              exact (not_lt_of_ge hbound hy.1.1).elim
      · rintro rfl
        constructor
        · constructor
          · exact shiftedDyadicUnitIntervalPoint_lt_dyadic_succ 0
          · exact dyadic_unit_interval_point_strictAnti (by omega)
        · exact (mem_obstructionNodeSet_diff_zero_iff).2 <| Or.inl ⟨1, rfl⟩
  | succ n =>
      let a : ℝ := ((shiftedDyadicUnitIntervalPoint (n + 1) : I) : ℝ)
      let b : ℝ := ((shiftedDyadicUnitIntervalPoint n : I) : ℝ)
      let U : Set I := {y : I | a < (y : ℝ) ∧ (y : ℝ) < b}
      have hUopen : IsOpen U := by
        -- Consecutive shifted nodes bound the unique dyadic node between them.
        simpa [U] using
          (isOpen_lt continuous_const continuous_subtype_val).inter
            (isOpen_lt continuous_subtype_val continuous_const)
      refine ⟨U, hUopen, ?_⟩
      ext y
      constructor
      · intro hy
        rcases mem_obstructionNodeSet_diff_zero_iff.mp hy.2 with ⟨m, rfl⟩ | ⟨m, rfl⟩
        · by_cases hm_le : m ≤ n + 1
          · have hbound :
                ((dyadic_unit_interval_point (n + 1) : I) : ℝ) ≤
                  ((dyadic_unit_interval_point m : I) : ℝ) :=
              dyadic_unit_interval_point_strictAnti.antitone hm_le
            have hsep :
                ((shiftedDyadicUnitIntervalPoint n : I) : ℝ) <
                  ((dyadic_unit_interval_point (n + 1) : I) : ℝ) :=
              shiftedDyadicUnitIntervalPoint_lt_dyadic_succ n
            have hlt :
                ((shiftedDyadicUnitIntervalPoint n : I) : ℝ) <
                  ((dyadic_unit_interval_point m : I) : ℝ) :=
              lt_of_lt_of_le hsep hbound
            exact (not_lt_of_ge hlt.le hy.1.2).elim
          · by_cases hm_eq : m = n + 2
            · simp [hm_eq]
            · have hm_ge : n + 3 ≤ m := by omega
              have hbound :
                  ((dyadic_unit_interval_point m : I) : ℝ) ≤
                    ((dyadic_unit_interval_point (n + 3) : I) : ℝ) :=
                dyadic_unit_interval_point_strictAnti.antitone hm_ge
              have hsep :
                  ((dyadic_unit_interval_point (n + 3) : I) : ℝ) <
                    ((shiftedDyadicUnitIntervalPoint (n + 1) : I) : ℝ) :=
                dyadic_twoSucc_lt_shiftedDyadicUnitIntervalPoint (n + 1)
              have hlt :
                  ((dyadic_unit_interval_point m : I) : ℝ) <
                    ((shiftedDyadicUnitIntervalPoint (n + 1) : I) : ℝ) :=
                lt_of_le_of_lt hbound hsep
              exact (not_lt_of_ge hlt.le hy.1.1).elim
        · by_cases hm_le : m ≤ n
          · have hbound :
                ((shiftedDyadicUnitIntervalPoint n : I) : ℝ) ≤
                  ((shiftedDyadicUnitIntervalPoint m : I) : ℝ) :=
              shiftedDyadicUnitIntervalPoint_strictAnti.antitone hm_le
            exact (not_lt_of_ge hbound hy.1.2).elim
          · have hm_ge : n + 1 ≤ m := by omega
            have hbound :
                ((shiftedDyadicUnitIntervalPoint m : I) : ℝ) ≤
                  ((shiftedDyadicUnitIntervalPoint (n + 1) : I) : ℝ) :=
              shiftedDyadicUnitIntervalPoint_strictAnti.antitone hm_ge
            exact (not_lt_of_ge hbound hy.1.1).elim
      · rintro rfl
        constructor
        · constructor
          · exact shiftedDyadicUnitIntervalPoint_lt_dyadic_succ (n + 1)
          · exact dyadic_twoSucc_lt_shiftedDyadicUnitIntervalPoint n
        · exact (mem_obstructionNodeSet_diff_zero_iff).2 <| Or.inl ⟨n + 2, rfl⟩

/-- Helper for Exercise 13.2.7: every shifted dyadic node is isolated inside the punctured
obstruction set. -/
lemma shiftedDyadic_hasSingletonNeighborhood (n : ℕ) :
    ∃ U : Set I, IsOpen U ∧
      U ∩ (obstructionNodeSet \ ({0} : Set I)) = {shiftedDyadicUnitIntervalPoint n} := by
  let a : ℝ := ((dyadic_unit_interval_point (n + 2) : I) : ℝ)
  let b : ℝ := ((dyadic_unit_interval_point (n + 1) : I) : ℝ)
  let U : Set I := {y : I | a < (y : ℝ) ∧ (y : ℝ) < b}
  have hUopen : IsOpen U := by
    -- Consecutive dyadic nodes bound the unique shifted node between them.
    simpa [U] using
      (isOpen_lt continuous_const continuous_subtype_val).inter
        (isOpen_lt continuous_subtype_val continuous_const)
  refine ⟨U, hUopen, ?_⟩
  ext y
  constructor
  · intro hy
    rcases mem_obstructionNodeSet_diff_zero_iff.mp hy.2 with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · by_cases hm_le : m ≤ n + 1
      · have hbound :
            ((dyadic_unit_interval_point (n + 1) : I) : ℝ) ≤
              ((dyadic_unit_interval_point m : I) : ℝ) :=
          dyadic_unit_interval_point_strictAnti.antitone hm_le
        exact (not_lt_of_ge hbound hy.1.2).elim
      · have hm_ge : n + 2 ≤ m := by omega
        have hbound :
            ((dyadic_unit_interval_point m : I) : ℝ) ≤
              ((dyadic_unit_interval_point (n + 2) : I) : ℝ) :=
          dyadic_unit_interval_point_strictAnti.antitone hm_ge
        exact (not_lt_of_ge hbound hy.1.1).elim
    · by_cases hm_lt : m < n
      · have hbound :
            ((dyadic_unit_interval_point (n + 1) : I) : ℝ) ≤
              ((dyadic_unit_interval_point (m + 2) : I) : ℝ) :=
          dyadic_unit_interval_point_strictAnti.antitone (by omega)
        have hsep :
            ((dyadic_unit_interval_point (m + 2) : I) : ℝ) <
              ((shiftedDyadicUnitIntervalPoint m : I) : ℝ) :=
          dyadic_twoSucc_lt_shiftedDyadicUnitIntervalPoint m
        have hlt :
            ((dyadic_unit_interval_point (n + 1) : I) : ℝ) <
              ((shiftedDyadicUnitIntervalPoint m : I) : ℝ) :=
          lt_of_le_of_lt hbound hsep
        exact (not_lt_of_ge hlt.le hy.1.2).elim
      · by_cases hm_eq : m = n
        · simp [hm_eq]
        · have hm_ge : n + 1 ≤ m := by omega
          have hbound :
              ((shiftedDyadicUnitIntervalPoint m : I) : ℝ) ≤
                ((shiftedDyadicUnitIntervalPoint (n + 1) : I) : ℝ) :=
            shiftedDyadicUnitIntervalPoint_strictAnti.antitone hm_ge
          have hsep :
              ((shiftedDyadicUnitIntervalPoint (n + 1) : I) : ℝ) <
                ((dyadic_unit_interval_point (n + 2) : I) : ℝ) :=
            shiftedDyadicUnitIntervalPoint_lt_dyadic_succ (n + 1)
          have hlt :
              ((shiftedDyadicUnitIntervalPoint m : I) : ℝ) <
                ((dyadic_unit_interval_point (n + 2) : I) : ℝ) :=
            lt_of_le_of_lt hbound hsep
          exact (not_lt_of_ge hlt.le hy.1.1).elim
  · rintro rfl
    constructor
    · constructor
      · exact dyadic_twoSucc_lt_shiftedDyadicUnitIntervalPoint n
      · exact shiftedDyadicUnitIntervalPoint_lt_dyadic_succ n
    · exact (mem_obstructionNodeSet_diff_zero_iff).2 <| Or.inr ⟨n, rfl⟩

/-- Helper for Exercise 13.2.7: every nonzero node in the mixed obstruction set is isolated. -/
lemma isDiscrete_obstructionNodeSet_diff_zero :
    IsDiscrete (obstructionNodeSet \ ({0} : Set I)) := by
  -- The punctured node set is the disjoint union of three isolated families: the top dyadic node,
  -- the remaining dyadic tail, and the shifted dyadic nodes.
  rw [isDiscrete_iff_forall_exists_isOpen]
  intro x hx
  rcases mem_obstructionNodeSet_diff_zero_iff.mp hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · cases n with
    | zero =>
        exact dyadicZero_hasSingletonNeighborhood
    | succ n =>
        exact dyadicSucc_hasSingletonNeighborhood n
  · exact shiftedDyadic_hasSingletonNeighborhood n

-- Route correction: the prescribed values live first on the punctured obstruction-node subtype,
-- and the closed-subtype map is then obtained by setting the zero node to `0`.
section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Helper for Exercise 13.2.7: the common limit point `0` belongs to the obstruction node set. -/
lemma zero_mem_obstructionNodeSet : (0 : I) ∈ obstructionNodeSet := by
  -- The obstruction set contains the dyadic set, and the dyadic set contains `0`.
  exact Or.inl <| by
    change (0 : I) = 0 ∨ (0 : I) ∈ Set.range dyadic_unit_interval_point
    exact Or.inl rfl

/-- Helper for Exercise 13.2.7: every nonzero point of the closed obstruction subtype belongs to
the punctured obstruction set. -/
lemma mem_obstructionNodeSet_diff_zero_of_ne_zero (x : obstructionNodeSet) (hx0 : (x : I) ≠ 0) :
    (x : I) ∈ obstructionNodeSet \ ({0} : Set I) := by
  -- Keep the ambient membership from the subtype and record the nonzero side condition separately.
  exact ⟨x.property, hx0⟩

/-- Helper for Exercise 13.2.7: the prescribed values on the punctured obstruction-node subtype. -/
def obstructionNodePuncturedValue {C : ℕ → ℝ} (_hC_pos : ∀ n, 0 < C n) :
    {x : I // x ∈ obstructionNodeSet \ ({0} : Set I)} → ℝ :=
  fun x ↦
    if hdy : ∃ n, (x : I) = dyadic_unit_interval_point n then
      (-1 : ℝ) ^ Nat.find hdy / Real.sqrt (C (Nat.find hdy))
    else if hshift : ∃ n, (x : I) = shiftedDyadicUnitIntervalPoint n then
      let n := Nat.find hshift
      if Odd n then (Real.sqrt (C (3 * 2 ^ n - 2)))⁻¹ else 0
    else
      0

/-- Helper for Exercise 13.2.7: the punctured value assignment sends dyadic nodes to the
prescribed alternating inverse square-root values. -/
lemma obstructionNodePuncturedValue_dyadic {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n) (n : ℕ) :
    obstructionNodePuncturedValue (C := C) hC_pos
        ⟨dyadic_unit_interval_point n,
          (mem_obstructionNodeSet_diff_zero_iff).2 <| Or.inl ⟨n, rfl⟩⟩ =
      (-1 : ℝ) ^ n / Real.sqrt (C n) := by
  -- The dyadic witness is unique, so `Nat.find` recovers the original index.
  have hdy : ∃ m, dyadic_unit_interval_point n = dyadic_unit_interval_point m := ⟨n, rfl⟩
  have hfind : Nat.find hdy = n := by
    apply dyadic_unit_interval_point_injective
    exact (Nat.find_spec hdy).symm
  unfold obstructionNodePuncturedValue
  rw [dif_pos hdy]
  simp [hfind]

/-- Helper for Exercise 13.2.7: the punctured value assignment sends shifted dyadic nodes to the
parity obstruction values. -/
lemma obstructionNodePuncturedValue_shifted {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n) (n : ℕ) :
    obstructionNodePuncturedValue (C := C) hC_pos
        ⟨shiftedDyadicUnitIntervalPoint n,
          (mem_obstructionNodeSet_diff_zero_iff).2 <| Or.inr ⟨n, rfl⟩⟩ =
      if Odd n then (Real.sqrt (C (3 * 2 ^ n - 2)))⁻¹ else 0 := by
  -- The shifted node cannot also be dyadic, and injectivity fixes the shifted witness index.
  have hdy :
      ¬ ∃ m, shiftedDyadicUnitIntervalPoint n = dyadic_unit_interval_point m := by
    rintro ⟨m, hm⟩
    exact (dyadic_ne_shiftedDyadicUnitIntervalPoint m n) hm.symm
  have hshift : ∃ m, shiftedDyadicUnitIntervalPoint n = shiftedDyadicUnitIntervalPoint m := ⟨n, rfl⟩
  have hfind : Nat.find hshift = n := by
    apply shiftedDyadicUnitIntervalPoint_injective
    exact (Nat.find_spec hshift).symm
  unfold obstructionNodePuncturedValue
  rw [dif_neg hdy, dif_pos hshift]
  simp [hfind]

/-- Helper for Exercise 13.2.7: the closed-subtype obstruction map is obtained by assigning `0` to
the limit point and using the punctured value assignment everywhere else. -/
def obstructionNodeMap {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n) : obstructionNodeSet → ℝ :=
  fun x ↦
    if hx0 : (x : I) = 0 then
      0
    else
      obstructionNodePuncturedValue (C := C) hC_pos
        ⟨(x : I), mem_obstructionNodeSet_diff_zero_of_ne_zero x hx0⟩

/-- Helper for Exercise 13.2.7: away from the zero node, the closed-subtype map agrees with the
punctured value assignment. -/
lemma obstructionNodeMap_apply_of_ne_zero {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n)
    {x : obstructionNodeSet} (hx0 : (x : I) ≠ 0) :
    obstructionNodeMap (C := C) hC_pos x =
      obstructionNodePuncturedValue (C := C) hC_pos
        ⟨(x : I), mem_obstructionNodeSet_diff_zero_of_ne_zero x hx0⟩ := by
  -- The defining `if` immediately reduces on nonzero points.
  simp [obstructionNodeMap, hx0]

/-- Helper for Exercise 13.2.7: the obstruction map vanishes at the zero node. -/
lemma obstructionNodeMap_zero {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n) :
    obstructionNodeMap (C := C) hC_pos ⟨0, zero_mem_obstructionNodeSet⟩ = 0 := by
  -- The zero branch of the definition is the distinguished update value.
  simp [obstructionNodeMap]

/-- Helper for Exercise 13.2.7: the obstruction map sends dyadic nodes to the prescribed
alternating inverse square-root values. -/
lemma obstructionNodeMap_dyadic {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n) (n : ℕ) :
    obstructionNodeMap (C := C) hC_pos
        ⟨dyadic_unit_interval_point n, Or.inl <| by
          change dyadic_unit_interval_point n = 0 ∨
              dyadic_unit_interval_point n ∈ Set.range dyadic_unit_interval_point
          exact Or.inr ⟨n, rfl⟩⟩ =
      (-1 : ℝ) ^ n / Real.sqrt (C n) := by
  -- Dyadic nodes are nonzero, so the map reduces to the punctured-value formula.
  have hne : dyadic_unit_interval_point n ≠ 0 := dyadic_unit_interval_point_ne_zero n
  rw [obstructionNodeMap_apply_of_ne_zero (C := C) hC_pos hne]
  simpa using obstructionNodePuncturedValue_dyadic (C := C) hC_pos n

/-- Helper for Exercise 13.2.7: the obstruction map sends shifted dyadic nodes to the parity
obstruction values. -/
lemma obstructionNodeMap_shifted {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n) (n : ℕ) :
    obstructionNodeMap (C := C) hC_pos
        ⟨shiftedDyadicUnitIntervalPoint n, Or.inr ⟨n, rfl⟩⟩ =
      if Odd n then (Real.sqrt (C (3 * 2 ^ n - 2)))⁻¹ else 0 := by
  -- Shifted nodes are also nonzero, so the punctured-value formula applies unchanged.
  have hne : shiftedDyadicUnitIntervalPoint n ≠ 0 := shiftedDyadicUnitIntervalPoint_ne_zero n
  rw [obstructionNodeMap_apply_of_ne_zero (C := C) hC_pos hne]
  simpa using obstructionNodePuncturedValue_shifted (C := C) hC_pos n

/-- Helper for Exercise 13.2.7: even shifted dyadic nodes receive the value `0`. -/
lemma obstructionNodeMap_shifted_even {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n) (n : ℕ) :
    obstructionNodeMap (C := C) hC_pos
        ⟨shiftedDyadicUnitIntervalPoint (2 * n), Or.inr ⟨2 * n, rfl⟩⟩ = 0 := by
  -- The parity gate in the shifted formula kills the even nodes.
  have hnotOdd : ¬ Odd (2 * n) := by
    apply Nat.not_odd_iff_even.mpr
    rw [Nat.even_mul]
    exact Or.inl (by decide)
  simpa [obstructionNodeMap_shifted, hnotOdd] using
    obstructionNodeMap_shifted (C := C) hC_pos (2 * n)

/-- Helper for Exercise 13.2.7: odd shifted dyadic nodes receive the inverse square-root values
used in the sparse blow-up computation. -/
lemma obstructionNodeMap_shifted_odd {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n) (n : ℕ) :
    obstructionNodeMap (C := C) hC_pos
        ⟨shiftedDyadicUnitIntervalPoint (2 * n + 1), Or.inr ⟨2 * n + 1, rfl⟩⟩ =
      (Real.sqrt (C (shiftedDyadicSubsequenceIndex (2 * n))))⁻¹ := by
  -- On odd shifted nodes, the sparse index in the definition matches the blow-up subsequence.
  simpa [shiftedDyadicSubsequenceIndex] using
    obstructionNodeMap_shifted (C := C) hC_pos (2 * n + 1)

/-- Helper for Exercise 13.2.7: every nonzero obstruction node is a continuity point because it is
isolated inside the closed subtype. -/
lemma continuousAt_obstructionNodeMap_of_ne_zero {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n)
    {x : obstructionNodeSet} (hx0 : (x : I) ≠ 0) :
    ContinuousAt (obstructionNodeMap (C := C) hC_pos) x := by
  have hx :
      (x : I) ∈ obstructionNodeSet \ ({0} : Set I) :=
    mem_obstructionNodeSet_diff_zero_of_ne_zero x hx0
  obtain ⟨U, hUopen, hUeq⟩ :=
    (isDiscrete_iff_forall_exists_isOpen.mp isDiscrete_obstructionNodeSet_diff_zero) (x : I) hx
  let V : Set obstructionNodeSet := Subtype.val ⁻¹' (U \ ({0} : Set I))
  have hxV : x ∈ V := by
    -- The isolating neighborhood from discreteness still contains `x` after deleting `0`.
    have hxUdiff : (x : I) ∈ U ∩ (obstructionNodeSet \ ({0} : Set I)) := by
      rw [hUeq]
      simp
    exact ⟨hxUdiff.1, hx0⟩
  have hVopen : IsOpen V := by
    -- Pull back the ambient open set `U \ {0}` along the subtype inclusion.
    simpa [V] using ((hUopen.inter isOpen_ne).preimage continuous_subtype_val)
  have hVnhds : V ∈ 𝓝 x := hVopen.mem_nhds hxV
  have hEventually :
      obstructionNodeMap (C := C) hC_pos =ᶠ[𝓝 x]
        fun _ ↦ obstructionNodeMap (C := C) hC_pos x := by
    refine Filter.mem_of_superset hVnhds ?_
    intro y hy
    have hyU : (y : I) ∈ U := hy.1
    have hy0 : (y : I) ≠ 0 := hy.2
    have hyPunctured : (y : I) ∈ obstructionNodeSet \ ({0} : Set I) :=
      ⟨y.property, hy0⟩
    have hySingleton : (y : I) ∈ ({(x : I)} : Set I) := by
      have hyInter : (y : I) ∈ U ∩ (obstructionNodeSet \ ({0} : Set I)) := ⟨hyU, hyPunctured⟩
      rw [hUeq] at hyInter
      simpa using hyInter
    have hyx : y = x := by
      apply Subtype.ext
      simpa using hySingleton
    simpa [hyx]
  -- Eventual constancy near an isolated point gives continuity.
  exact hEventually.continuousAt

/-- Helper for Exercise 13.2.7: the obstruction map is continuous at the zero node because both
prescribed coefficient families tend to `0`. -/
lemma continuousAt_obstructionNodeMap_zero {C : ℕ → ℝ}
    (hC_pos : ∀ n, 0 < C n) (hC_top : Tendsto C atTop atTop) :
    ContinuousAt (obstructionNodeMap (C := C) hC_pos) ⟨0, zero_mem_obstructionNodeSet⟩ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  rcases Metric.tendsto_atTop.1 (dyadicNodeCoefficient_tendsto_zero (C := C) hC_pos hC_top)
      ε hε with ⟨Nd, hNd⟩
  rcases Metric.tendsto_atTop.1 (shiftedDyadicNodeCoefficient_tendsto_zero (C := C) hC_pos hC_top)
      ε hε with ⟨Ns, hNs⟩
  let N := max Nd Ns
  refine ⟨((dyadic_unit_interval_point (N + 2) : I) : ℝ), ?_, ?_⟩
  · -- The chosen dyadic radius is positive.
    rw [dyadic_unit_interval_point_val]
    positivity
  · intro x hx
    by_cases hxzero : x = ⟨0, zero_mem_obstructionNodeSet⟩
    · -- At the distinguished zero node, the target value is exactly `0`.
      simpa [hxzero, obstructionNodeMap_zero]
    · have hx0 : (x : I) ≠ 0 := by
        intro hx0'
        apply hxzero
        apply Subtype.ext
        simpa using hx0'
      have hxReal :
          ((x : I) : ℝ) < ((dyadic_unit_interval_point (N + 2) : I) : ℝ) := by
        have hxI := hx
        change dist (((x : I) : ℝ)) 0 < ((dyadic_unit_interval_point (N + 2) : I) : ℝ) at hxI
        simpa [Real.dist_eq, sub_zero, abs_of_nonneg x.1.2.1] using hxI
      have hxPunctured :
          (x : I) ∈ obstructionNodeSet \ ({0} : Set I) :=
        mem_obstructionNodeSet_diff_zero_of_ne_zero x hx0
      rcases mem_obstructionNodeSet_diff_zero_iff.mp hxPunctured with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- A sufficiently small dyadic node lies far enough out in the dyadic tail.
        have hmLarge : N + 2 < m := by
          by_contra hnot
          have hmLe : m ≤ N + 2 := Nat.le_of_not_gt hnot
          have hbound :
              ((dyadic_unit_interval_point (N + 2) : I) : ℝ) ≤
                ((dyadic_unit_interval_point m : I) : ℝ) :=
            dyadic_unit_interval_point_strictAnti.antitone hmLe
          rw [hm] at hxReal
          exact (not_lt_of_ge hbound hxReal).elim
        have hNle : N ≤ m := le_trans (Nat.le_add_right N 2) (Nat.le_of_lt hmLarge)
        have hNdLe : Nd ≤ m := le_trans (le_max_left _ _) hNle
        have hxEq :
            x =
              ⟨dyadic_unit_interval_point m, Or.inl <| by
                change dyadic_unit_interval_point m = 0 ∨
                    dyadic_unit_interval_point m ∈ Set.range dyadic_unit_interval_point
                exact Or.inr ⟨m, rfl⟩⟩ := by
          apply Subtype.ext
          simpa using hm
        simpa [hxEq, obstructionNodeMap_dyadic, obstructionNodeMap_zero] using hNd m hNdLe
      · -- A sufficiently small shifted node must also lie in the shifted tail.
        have hmGe : N ≤ m := by
          by_contra hnot
          have hmLt : m < N := Nat.lt_of_not_ge hnot
          have hbound :
              ((shiftedDyadicUnitIntervalPoint N : I) : ℝ) ≤
                ((shiftedDyadicUnitIntervalPoint m : I) : ℝ) :=
            shiftedDyadicUnitIntervalPoint_strictAnti.antitone (Nat.le_of_lt hmLt)
          have hsep :
              ((dyadic_unit_interval_point (N + 2) : I) : ℝ) <
                ((shiftedDyadicUnitIntervalPoint N : I) : ℝ) :=
            dyadic_twoSucc_lt_shiftedDyadicUnitIntervalPoint N
          rw [hm] at hxReal
          exact (not_lt_of_ge (le_trans hsep.le hbound) hxReal).elim
        have hNsLe : Ns ≤ m := le_trans (le_max_right _ _) hmGe
        have hxEq :
            x = ⟨shiftedDyadicUnitIntervalPoint m, Or.inr ⟨m, rfl⟩⟩ := by
          apply Subtype.ext
          simpa using hm
        simpa [hxEq, obstructionNodeMap_shifted, obstructionNodeMap_zero] using hNs m hNsLe

/-- Helper for Exercise 13.2.7: the obstruction map is continuous on the closed obstruction-node
subtype. -/
lemma continuous_obstructionNodeMap {C : ℕ → ℝ}
    (hC_pos : ∀ n, 0 < C n) (hC_top : Tendsto C atTop atTop) :
    Continuous (obstructionNodeMap (C := C) hC_pos) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx0 : (x : I) = 0
  · -- The only accumulation point of the node set is `0`, handled by the coefficient limits.
    have hxEq : x = ⟨0, zero_mem_obstructionNodeSet⟩ := by
      apply Subtype.ext
      simpa using hx0
    simpa [hxEq] using continuousAt_obstructionNodeMap_zero (C := C) hC_pos hC_top
  · -- Every nonzero node is isolated in the punctured obstruction set.
    exact continuousAt_obstructionNodeMap_of_ne_zero (C := C) hC_pos hx0

end

/-- Helper for Exercise 13.2.7: the sparse shifted-dyadic subsequence index tends to `∞`. -/
lemma shiftedDyadicSubsequenceIndex_tendsto_atTop :
    Tendsto shiftedDyadicSubsequenceIndex atTop atTop := by
  -- The sparse index stays ahead of the identity sequence, so it also tends to `∞`.
  refine tendsto_atTop_mono (fun n ↦ ?_) tendsto_id
  -- The exponential term dominates `n`, and the sparse index is even larger.
  have hpow_dom : n ≤ 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
  have hpow_le : 2 ^ n ≤ shiftedDyadicSubsequenceIndex n := by
    rw [shiftedDyadicSubsequenceIndex, pow_succ']
    have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  exact le_trans hpow_dom hpow_le

/-- Helper for Exercise 13.2.7: along the sparse subsequence whose support points are consecutive
shifted dyadic nodes, the weak integral computes to a square root of the scaling factor. -/
lemma shiftedDyadicSubsequenceIntegral_blowup {C : ℕ → ℝ}
    (hC_pos : ∀ n, 0 < C n) (f : I →ᵇ ℝ)
    (hf_even : ∀ n, f (shiftedDyadicUnitIntervalPoint (2 * n)) = 0)
    (hf_odd :
      ∀ n,
        f (shiftedDyadicUnitIntervalPoint (2 * n + 1)) =
          (Real.sqrt (C (shiftedDyadicSubsequenceIndex (2 * n))))⁻¹)
    (n : ℕ) :
    weakIntegral f
        (C (shiftedDyadicSubsequenceIndex (2 * n)) •
          shifted_point_mass_difference (shiftedDyadicSubsequenceIndex (2 * n))) =
      Real.sqrt (C (shiftedDyadicSubsequenceIndex (2 * n))) := by
  -- Rewrite the two support points in the sparse subsequence to consecutive shifted dyadic nodes.
  rw [weakIntegral_smul_shiftedPointMassDifference]
  rw [reciprocal_shiftedDyadicSubsequenceIndex (2 * n)]
  rw [doubleReciprocal_shiftedDyadicSubsequenceIndex (2 * n)]
  rw [hf_odd n, hf_even n, sub_zero]
  let m := shiftedDyadicSubsequenceIndex (2 * n)
  have hm_pos : 0 < C m := hC_pos m
  have hsqrt_pos : 0 < Real.sqrt (C m) := Real.sqrt_pos.2 hm_pos
  have hsq : C m = Real.sqrt (C m) * Real.sqrt (C m) := by
    calc
      C m = (Real.sqrt (C m)) ^ 2 := by
        symm
        exact Real.sq_sqrt (le_of_lt hm_pos)
      _ = Real.sqrt (C m) * Real.sqrt (C m) := by ring
  have hfactor :
      C m * (Real.sqrt (C m))⁻¹ =
        (Real.sqrt (C m) * Real.sqrt (C m)) * (Real.sqrt (C m))⁻¹ := by
    nth_rewrite 1 [hsq]
    rfl
  -- Replace `C m` by `(sqrt (C m))^2` so one factor cancels against the inverse square root.
  calc
    C m * (Real.sqrt (C m))⁻¹ = (Real.sqrt (C m) * Real.sqrt (C m)) * (Real.sqrt (C m))⁻¹ :=
      hfactor
    _ = Real.sqrt (C m) := by
      field_simp [hsqrt_pos.ne']

/-- Part (iii): an unbounded positive rescaling sequence admits a bounded continuous real-valued
weak test function on `[0,1]` whose integrals against the rescaled signed measures fail to
converge to `0`. On the compact interval `[0,1]`, this is equivalent to using an ordinary
continuous test function. -/
theorem unbounded_rescalings_admit_obstructing_bounded_continuous_function
    {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n) (hC_top : Tendsto C atTop atTop) :
    ∃ f : I →ᵇ ℝ,
      (∀ n, f (dyadic_unit_interval_point n) = (-1 : ℝ) ^ n / Real.sqrt (C n)) ∧
        ¬ Tendsto
          (fun n ↦ weakIntegral f (C n • shifted_point_mass_difference n))
          atTop (𝓝 0) := by
  -- Build the prescribed continuous function first on the closed obstruction-node subtype.
  have hCompact : IsCompact obstructionNodeSet := isClosed_obstructionNodeSet.isCompact
  let fClosedCont : C(obstructionNodeSet, ℝ) :=
    { toFun := obstructionNodeMap (C := C) hC_pos
      continuous_toFun := continuous_obstructionNodeMap (C := C) hC_pos hC_top }
  haveI : CompactSpace obstructionNodeSet := isCompact_iff_compactSpace.mp hCompact
  let fClosed : obstructionNodeSet →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact fClosedCont
  obtain ⟨f, _hfNorm, hfRestrict⟩ :=
    BoundedContinuousFunction.exists_norm_eq_restrict_eq_of_closed fClosed
      isClosed_obstructionNodeSet
  refine ⟨f, ?_, ?_⟩
  · intro n
    -- Evaluate the Tietze restriction equality at the dyadic subtype point.
    let x : obstructionNodeSet :=
      ⟨dyadic_unit_interval_point n, Or.inl <| by
        change dyadic_unit_interval_point n = 0 ∨
            dyadic_unit_interval_point n ∈ Set.range dyadic_unit_interval_point
        exact Or.inr ⟨n, rfl⟩⟩
    have hx := congrArg (fun h : obstructionNodeSet →ᵇ ℝ => h x) hfRestrict
    simpa [x, fClosed, fClosedCont, obstructionNodeMap_dyadic,
      BoundedContinuousFunction.restrict_apply] using hx
  · intro hTendsto
    have hEvenIndex : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
      -- The even subsequence still tends to infinity because it dominates the identity.
      refine tendsto_atTop_mono (fun n ↦ ?_) tendsto_id
      simpa [two_mul] using (Nat.le_add_left n n)
    have hSparse :
        Tendsto (fun n : ℕ ↦ shiftedDyadicSubsequenceIndex (2 * n)) atTop atTop :=
      shiftedDyadicSubsequenceIndex_tendsto_atTop.comp hEvenIndex
    have hSparseZero :
        Tendsto
          (fun n ↦
            weakIntegral f
              (C (shiftedDyadicSubsequenceIndex (2 * n)) •
                shifted_point_mass_difference (shiftedDyadicSubsequenceIndex (2 * n))))
          atTop (𝓝 0) :=
      hTendsto.comp hSparse
    have hfEven :
        ∀ n,
          f (shiftedDyadicUnitIntervalPoint (2 * n)) = 0 := by
      intro n
      -- The restriction equality also transfers the even shifted-node values.
      let x : obstructionNodeSet := ⟨shiftedDyadicUnitIntervalPoint (2 * n), Or.inr ⟨2 * n, rfl⟩⟩
      have hx := congrArg (fun h : obstructionNodeSet →ᵇ ℝ => h x) hfRestrict
      simpa [x, fClosed, fClosedCont, obstructionNodeMap_shifted_even,
        BoundedContinuousFunction.restrict_apply] using hx
    have hfOdd :
        ∀ n,
          f (shiftedDyadicUnitIntervalPoint (2 * n + 1)) =
            (Real.sqrt (C (shiftedDyadicSubsequenceIndex (2 * n))))⁻¹ := by
      intro n
      -- The odd shifted-node values produce the sparse blow-up along the chosen subsequence.
      let x : obstructionNodeSet :=
        ⟨shiftedDyadicUnitIntervalPoint (2 * n + 1), Or.inr ⟨2 * n + 1, rfl⟩⟩
      have hx := congrArg (fun h : obstructionNodeSet →ᵇ ℝ => h x) hfRestrict
      simpa [x, fClosed, fClosedCont, obstructionNodeMap_shifted_odd,
        BoundedContinuousFunction.restrict_apply] using hx
    have hBlowup :
        ∀ n,
          weakIntegral f
              (C (shiftedDyadicSubsequenceIndex (2 * n)) •
                shifted_point_mass_difference (shiftedDyadicSubsequenceIndex (2 * n))) =
            Real.sqrt (C (shiftedDyadicSubsequenceIndex (2 * n))) := by
      intro n
      -- The sparse subsequence turns the weak integral into the square root of the scaling factor.
      exact shiftedDyadicSubsequenceIntegral_blowup (C := C) hC_pos f hfEven hfOdd n
    have hLarge :
        ∀ᶠ n in atTop, 1 < Real.sqrt (C (shiftedDyadicSubsequenceIndex (2 * n))) := by
      -- Along the sparse even subsequence, the scaling factors still diverge to infinity.
      have hEventually :
          ∀ᶠ n in atTop, 2 ≤ C (shiftedDyadicSubsequenceIndex (2 * n)) :=
        (tendsto_atTop.1 (hC_top.comp hSparse)) 2
      filter_upwards [hEventually] with n hn
      have hsqrtNonneg : 0 ≤ Real.sqrt (C (shiftedDyadicSubsequenceIndex (2 * n))) :=
        Real.sqrt_nonneg _
      have hsq :
          Real.sqrt (C (shiftedDyadicSubsequenceIndex (2 * n))) *
              Real.sqrt (C (shiftedDyadicSubsequenceIndex (2 * n))) =
            C (shiftedDyadicSubsequenceIndex (2 * n)) := by
        simpa [pow_two] using
          (Real.sq_sqrt (le_trans zero_le_two hn) :
            (Real.sqrt (C (shiftedDyadicSubsequenceIndex (2 * n)))) ^ 2 =
              C (shiftedDyadicSubsequenceIndex (2 * n)))
      nlinarith
    rcases Metric.tendsto_atTop.1 hSparseZero 1 zero_lt_one with ⟨N0, hN0⟩
    rcases Filter.eventually_atTop.1 hLarge with ⟨N1, hN1⟩
    let N := max N0 N1
    have hSmall :
        dist
            (weakIntegral f
              (C (shiftedDyadicSubsequenceIndex (2 * N)) •
                shifted_point_mass_difference (shiftedDyadicSubsequenceIndex (2 * N))))
            0 < 1 := hN0 N (le_max_left _ _)
    have hBig :
        1 <
          weakIntegral f
            (C (shiftedDyadicSubsequenceIndex (2 * N)) •
              shifted_point_mass_difference (shiftedDyadicSubsequenceIndex (2 * N))) := by
      rw [hBlowup N]
      exact hN1 N (le_max_right _ _)
    have hNotSmall :
        ¬ dist
            (weakIntegral f
              (C (shiftedDyadicSubsequenceIndex (2 * N)) •
                shifted_point_mass_difference (shiftedDyadicSubsequenceIndex (2 * N))))
            0 < 1 := by
      let s :=
        weakIntegral f
          (C (shiftedDyadicSubsequenceIndex (2 * N)) •
            shifted_point_mass_difference (shiftedDyadicSubsequenceIndex (2 * N)))
      have hAbsGe :
          1 ≤ |s| := by
        exact le_trans hBig.le (le_abs_self s)
      simpa [s, Real.dist_eq, sub_zero] using (not_lt.mpr hAbsGe)
    exact hNotSmall hSmall

/-- Exercise 13.2.7: weak convergence on signed measures over `[0,1]` is not induced by any
metric. -/
theorem weak_convergence_on_signed_measures_over_unit_interval_not_metrizable :
    ¬ TopologicalSpace.MetrizableSpace (SignedMeasure I) := by
  intro hmetrizable
  haveI : TopologicalSpace.MetrizableSpace (SignedMeasure I) := hmetrizable
  obtain ⟨C, hC_mono, hC_top, hC_pos, hweak⟩ :=
    metrizable_weak_convergence_yields_unbounded_rescalings
  obtain ⟨f, hf_nodes, hnot_tendsto⟩ :=
    unbounded_rescalings_admit_obstructing_bounded_continuous_function hC_pos hC_top
  have htest :
      Tendsto (fun n ↦ weakIntegral f (C n • shifted_point_mass_difference n)) atTop (𝓝 0) :=
    (weaklyConvergesTo_zero_iff _).mp hweak f
  exact hnot_tendsto htest

end UnitIntervalCounterexample
