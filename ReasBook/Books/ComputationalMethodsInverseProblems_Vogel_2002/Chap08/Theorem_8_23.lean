/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4_1.Approximation
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_14.BV
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_22.BVBounded
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_18.Comparison
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16
import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_24
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section

namespace VariationalRegularization

open scoped VariationalRegularization.Approximation

variable {d : ℕ}

/-- Helper for Theorem 8.23: local objective owner used to avoid the aggregate/split import
collision between `Exercise_8_16` and `Theorem_8_19.Objective`. -/
def regularizedLeastSquaresFunctional
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (J : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) → EReal) :
    MeasureTheory.Lp ℝ p (domainMeasure Ω) → EReal :=
  fun f ↦ ((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) + (α : EReal) * J (lpToL1 f)

/-- Helper for Theorem 8.23: the defining formula for
`regularizedLeastSquaresFunctional`. -/
theorem regularizedLeastSquaresFunctional_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (J : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) → EReal)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    regularizedLeastSquaresFunctional K g α J f =
      ((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) + (α : EReal) * J (lpToL1 f) := by
  rfl

/-- Helper for Theorem 8.23: the TV specialization of the local objective owner. -/
def tvRegularizedLeastSquaresFunctional
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ) :
    MeasureTheory.Lp ℝ p (domainMeasure Ω) → EReal :=
  regularizedLeastSquaresFunctional K g α totalVariation

/-- Helper for Theorem 8.23: the defining formula for
`tvRegularizedLeastSquaresFunctional`. -/
theorem tvRegularizedLeastSquaresFunctional_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    tvRegularizedLeastSquaresFunctional K g α f =
      ((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) +
        (α : EReal) * totalVariation (lpToL1 f) := by
  rfl

/-- Helper for Theorem 8.23: a constrained minimizer of the exact TV objective. -/
def IsTvRegularizedMinimizer
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) : Prop :=
  f ∈ C ∧ IsMinOn (tvRegularizedLeastSquaresFunctional K datum α) C f

namespace IsTvRegularizedMinimizer

/-- Helper for Theorem 8.23: package admissibility and minimality as an exact TV minimizer. -/
theorem ofMemAndIsMinOn
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hf_mem : f ∈ C)
    (hf_isMinOn : IsMinOn (tvRegularizedLeastSquaresFunctional K datum α) C f) :
    IsTvRegularizedMinimizer C K datum α f :=
  ⟨hf_mem, hf_isMinOn⟩

/-- Helper for Theorem 8.23: an exact TV minimizer is admissible. -/
theorem mem
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hf : IsTvRegularizedMinimizer C K datum α f) :
    f ∈ C :=
  hf.1

/-- Helper for Theorem 8.23: an exact TV minimizer minimizes the exact objective. -/
theorem isMinOn
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hf : IsTvRegularizedMinimizer C K datum α f) :
    IsMinOn (tvRegularizedLeastSquaresFunctional K datum α) C f :=
  hf.2

end IsTvRegularizedMinimizer

/-- Helper for Theorem 8.23: a uniquely determined constrained minimizer of the exact TV
objective. -/
def IsUniqueTvRegularizedMinimizer
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (fStar : MeasureTheory.Lp ℝ p (domainMeasure Ω)) : Prop :=
  IsTvRegularizedMinimizer C K datum α fStar ∧
    ∀ f : MeasureTheory.Lp ℝ p (domainMeasure Ω),
      IsTvRegularizedMinimizer C K datum α f → f = fStar

namespace IsUniqueTvRegularizedMinimizer

/-- Helper for Theorem 8.23: any exact TV minimizer agrees with the unique one. -/
theorem eq
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {fStar f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hfStar : IsUniqueTvRegularizedMinimizer C K datum α fStar)
    (hf : IsTvRegularizedMinimizer C K datum α f) :
    f = fStar :=
  hfStar.2 f hf

end IsUniqueTvRegularizedMinimizer

namespace ApproximationUniformConvergence

/-- Helper for Theorem 8.23: negating an admissible field negates its divergence. -/
@[simp] lemma admissibleDivergence_neg
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (x : EuclideanSpace ℝ (Fin d)) :
    admissibleDivergence v.neg x = -admissibleDivergence v x := by
  -- Rewrite the derivative of the negated test field once, then simplify the coordinate sum.
  have hneg : fderiv ℝ (⇑(-v.toTestFunction)) x = -fderiv ℝ v.toTestFunction x := by
    change fderiv ℝ (fun y ↦ -v.toTestFunction y) x = -fderiv ℝ v.toTestFunction x
    simp
  rw [admissibleDivergence_def, admissibleDivergence_def, AdmissibleTestField.neg_toTestFunction]
  rw [hneg]
  simp

/-- Helper for Theorem 8.23: the divergence pairing integrand is integrable. -/
lemma pairingIntegrable
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Integrable (fun x ↦ f x * admissibleDivergence v x) (domainMeasure Ω) := by
  -- The `L¹` representative of `f` pairs integrably with the `L∞` divergence factor.
  have hf : MeasureTheory.MemLp (fun x ↦ f x) 1 (domainMeasure Ω) := by
    simpa using MeasureTheory.Lp.memLp f
  exact hf.integrable_mul (VariationalRegularization.admissibleDivergenceMemLpTop v)

/-- Helper for Theorem 8.23: the negated pairing owner agrees with pairing against `v.neg`. -/
lemma negPairingIntegral_eq_pairing_neg
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (v : AdmissibleTestField Ω) :
    (∫ x, (-(f x)) * admissibleDivergence v x ∂domainMeasure Ω) =
      admissibleDivergencePairing f v.neg := by
  -- Rewrite the negated divergence through `v.neg` and simplify the pointwise product.
  rw [admissibleDivergencePairing_def]
  simp [admissibleDivergence_neg, mul_comm]

/-- Helper for Theorem 8.23: the smooth penalty integrand is integrable on the finite domain. -/
lemma smoothPenaltyIntegrable
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (β : ℝ)
    (hβ : 0 < β)
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Integrable
      (fun x ↦ β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2))
      (domainMeasure Ω) := by
  -- On a finite-measure domain, continuity plus the uniform bound by `β` gives integrability.
  have hcont :
      Continuous fun x : EuclideanSpace ℝ (Fin d) ↦
        β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) := by
    have hv : Continuous v.toTestFunction := v.toTestFunction.continuous
    exact (Real.continuous_sqrt.comp
      (continuous_const.sub ((hv.norm).pow 2))).const_mul β
  refine MeasureTheory.Integrable.of_bound hcont.aestronglyMeasurable β ?_
  rw [domainMeasure_def, MeasureTheory.ae_restrict_iff']
  · filter_upwards with x hx
    have hnormle : ‖v.toTestFunction x‖ ≤ 1 := v.norm_le_one x hx
    have hsq_le : ‖v.toTestFunction x‖ ^ 2 ≤ 1 := by
      nlinarith [hnormle, norm_nonneg (v.toTestFunction x)]
    have hinside_nonneg : 0 ≤ 1 - ‖v.toTestFunction x‖ ^ 2 := sub_nonneg.mpr hsq_le
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) :=
      Real.sqrt_nonneg _
    have hsqrt_le_one : Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) ≤ 1 := by
      nlinarith [Real.sq_sqrt hinside_nonneg, hsqrt_nonneg]
    have hmul_nonneg :
        0 ≤ β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) :=
      mul_nonneg (le_of_lt hβ) hsqrt_nonneg
    simpa [Real.norm_of_nonneg hmul_nonneg] using
      mul_le_mul_of_nonneg_left hsqrt_le_one (le_of_lt hβ)
  · exact Ω.2.measurableSet

/-- Helper for Theorem 8.23: the smooth penalty integrand is nonnegative almost everywhere. -/
lemma smoothPenalty_nonneg_ae
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (β : ℝ)
    (hβ : 0 < β)
    (v : AdmissibleTestField Ω) :
    ∀ᵐ x ∂domainMeasure Ω,
      0 ≤ β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) := by
  -- The square-root factor is nonnegative, and the scalar `β` is positive.
  rw [domainMeasure_def, MeasureTheory.ae_restrict_iff']
  · filter_upwards with x hx
    have hnormle : ‖v.toTestFunction x‖ ≤ 1 := v.norm_le_one x hx
    have hsq_le : ‖v.toTestFunction x‖ ^ 2 ≤ 1 := by
      nlinarith [hnormle, norm_nonneg (v.toTestFunction x)]
    have hinside_nonneg : 0 ≤ 1 - ‖v.toTestFunction x‖ ^ 2 := sub_nonneg.mpr hsq_le
    exact mul_nonneg (le_of_lt hβ) (Real.sqrt_nonneg _)
  · exact Ω.2.measurableSet

/-- Helper for Theorem 8.23: the smooth penalty integral is bounded by `β * Vol(Ω)`. -/
lemma smoothPenaltyIntegral_le_volume
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (β : ℝ)
    (hβ : 0 < β)
    (v : AdmissibleTestField Ω) :
    ∫ x, β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) ∂domainMeasure Ω ≤
      β * (domainMeasure Ω Set.univ).toReal := by
  -- Compare the penalty integrand with the constant function `β` and integrate that bound.
  have hbound :
      ∀ᵐ x ∂domainMeasure Ω,
        β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) ≤ β := by
    rw [domainMeasure_def, MeasureTheory.ae_restrict_iff']
    · filter_upwards with x hx
      have hnormle : ‖v.toTestFunction x‖ ≤ 1 := v.norm_le_one x hx
      have hsq_le : ‖v.toTestFunction x‖ ^ 2 ≤ 1 := by
        nlinarith [hnormle, norm_nonneg (v.toTestFunction x)]
      have hinside_nonneg : 0 ≤ 1 - ‖v.toTestFunction x‖ ^ 2 := sub_nonneg.mpr hsq_le
      have hsqrt_le_one : Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) ≤ 1 := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) := Real.sqrt_nonneg _
        nlinarith [Real.sq_sqrt hinside_nonneg, hsqrt_nonneg]
      exact mul_le_of_le_one_right (le_of_lt hβ) hsqrt_le_one
    · exact Ω.2.measurableSet
  have hmono := MeasureTheory.integral_mono_ae
    (smoothPenaltyIntegrable β hβ v)
    (MeasureTheory.integrable_const β)
    hbound
  simpa [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm] using hmono

/-- Helper for Theorem 8.23: the Huber penalty integrand is integrable on the finite domain. -/
lemma huberPenaltyIntegrable
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (ε : ℝ)
    (hε : 0 < ε)
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Integrable
      (fun x ↦ (ε / 2) * ‖v.toTestFunction x‖ ^ 2)
      (domainMeasure Ω) := by
  -- On a finite-measure domain, continuity plus the uniform bound by `ε / 2` gives integrability.
  have hcont :
      Continuous fun x : EuclideanSpace ℝ (Fin d) ↦
        (ε / 2) * ‖v.toTestFunction x‖ ^ 2 := by
    have hv : Continuous v.toTestFunction := v.toTestFunction.continuous
    exact ((hv.norm).pow 2).const_mul (ε / 2)
  refine MeasureTheory.Integrable.of_bound hcont.aestronglyMeasurable (ε / 2) ?_
  rw [domainMeasure_def, MeasureTheory.ae_restrict_iff']
  · filter_upwards with x hx
    have hnormle : ‖v.toTestFunction x‖ ≤ 1 := v.norm_le_one x hx
    have hsq_le : ‖v.toTestFunction x‖ ^ 2 ≤ 1 := by
      nlinarith [hnormle, norm_nonneg (v.toTestFunction x)]
    have hmul_nonneg :
        0 ≤ (ε / 2) * ‖v.toTestFunction x‖ ^ 2 := by
      positivity
    simpa [Real.norm_of_nonneg hmul_nonneg] using
      mul_le_mul_of_nonneg_left hsq_le (by positivity : 0 ≤ ε / 2)
  · exact Ω.2.measurableSet

/-- Helper for Theorem 8.23: the Huber penalty is nonnegative almost everywhere. -/
lemma huberPenalty_nonneg_ae
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (ε : ℝ)
    (hε : 0 < ε)
    (v : AdmissibleTestField Ω) :
    ∀ᵐ x ∂domainMeasure Ω,
      0 ≤ (ε / 2) * ‖v.toTestFunction x‖ ^ 2 := by
  -- Both factors in the Huber penalty are nonnegative.
  filter_upwards with x
  positivity

/-- Helper for Theorem 8.23: the Huber penalty integral is bounded by `(ε / 2) * Vol(Ω)`. -/
lemma huberPenaltyIntegral_le_volume
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (ε : ℝ)
    (hε : 0 < ε)
    (v : AdmissibleTestField Ω) :
    ∫ x, (ε / 2) * ‖v.toTestFunction x‖ ^ 2 ∂domainMeasure Ω ≤
      (ε / 2) * (domainMeasure Ω Set.univ).toReal := by
  -- Compare the Huber penalty with the constant function `ε / 2` and integrate that bound.
  have hbound :
      ∀ᵐ x ∂domainMeasure Ω,
        (ε / 2) * ‖v.toTestFunction x‖ ^ 2 ≤ ε / 2 := by
    rw [domainMeasure_def, MeasureTheory.ae_restrict_iff']
    · filter_upwards with x hx
      have hnormle : ‖v.toTestFunction x‖ ≤ 1 := v.norm_le_one x hx
      have hsq_le : ‖v.toTestFunction x‖ ^ 2 ≤ 1 := by
        nlinarith [hnormle, norm_nonneg (v.toTestFunction x)]
      exact mul_le_of_le_one_right (by positivity : 0 ≤ ε / 2) hsq_le
    · exact Ω.2.measurableSet
  have hmono := MeasureTheory.integral_mono_ae
    (huberPenaltyIntegrable ε hε v)
    (MeasureTheory.integrable_const (ε / 2))
    hbound
  simpa [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm] using hmono

/-- Helper for Theorem 8.23: the Chapter 8 smooth approximation satisfies the source order window
around `TV`. -/
lemma smoothNormApproxTotalVariation_orderBounds
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (β : ℝ)
    (hβ : 0 < β)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    totalVariation f ≤ J_β β f ∧
      J_β β f ≤ totalVariation f + (((β * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal) := by
  constructor
  · -- Compare each divergence pairing with the `J_β` witness given by the negated test field.
    refine totalVariation_le_of_forall_admissibleDivergencePairing_le f ?_
    intro v
    rw [smoothNormApproxTotalVariation_def]
    have hmono :
        ∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω ≤
          ∫ x, f x * admissibleDivergence v x +
            β * Real.sqrt (1 - ‖v.neg.toTestFunction x‖ ^ 2) ∂domainMeasure Ω := by
      have hleft :
          MeasureTheory.Integrable
            (fun x ↦ f x * admissibleDivergence v x) (domainMeasure Ω) :=
        pairingIntegrable f v
      have hright := smoothPenaltyIntegrable β hβ v.neg
      refine MeasureTheory.integral_mono_ae hleft (hleft.add hright) ?_
      filter_upwards [smoothPenalty_nonneg_ae β hβ v.neg] with x hx
      linarith
    have hwitness_eq :
        (((∫ x, f x * admissibleDivergence v x +
            β * Real.sqrt (1 - ‖v.neg.toTestFunction x‖ ^ 2)
          ∂domainMeasure Ω) : ℝ) : EReal) =
          (((∫ x, (-(f x)) * admissibleDivergence v.neg x +
              β * Real.sqrt (1 - ‖v.neg.toTestFunction x‖ ^ 2)
            ∂domainMeasure Ω) : ℝ) : EReal) := by
      -- Route correction: rewrite the `v.neg` witness pointwise instead of fighting the `Lp`-neg
      -- normal form inside the main inequality.
      congr 1
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      simp [admissibleDivergence_neg, mul_comm]
    calc
      (admissibleDivergencePairing f v : EReal)
          = (((∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω) : ℝ) : EReal) := by
              rw [admissibleDivergencePairing_def]
      _ ≤ (((∫ x, f x * admissibleDivergence v x +
            β * Real.sqrt (1 - ‖v.neg.toTestFunction x‖ ^ 2)
          ∂domainMeasure Ω) : ℝ) : EReal) := by
              exact_mod_cast hmono
      _ = (((∫ x, (-(f x)) * admissibleDivergence v.neg x +
            β * Real.sqrt (1 - ‖v.neg.toTestFunction x‖ ^ 2)
          ∂domainMeasure Ω) : ℝ) : EReal) := hwitness_eq
      _ ≤ sSup (Set.range fun u : AdmissibleTestField Ω ↦
            (((∫ x, (-(f x)) * admissibleDivergence u x +
                    β * Real.sqrt (1 - ‖u.toTestFunction x‖ ^ 2)
                  ∂domainMeasure Ω) : ℝ) : EReal)) := by
              exact le_sSup ⟨v.neg, rfl⟩
  · -- Split the defining integral and bound the pairing and penalty terms separately.
    rw [smoothNormApproxTotalVariation_def]
    refine sSup_le ?_
    rintro _ ⟨v, rfl⟩
    calc
      (((∫ x, (-(f x)) * admissibleDivergence v x +
              β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
            ∂domainMeasure Ω) : ℝ) : EReal)
          = (((∫ x, (-(f x)) * admissibleDivergence v x ∂domainMeasure Ω) : ℝ) : EReal) +
              (((∫ x, β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
                  ∂domainMeasure Ω) : ℝ) : EReal) := by
              have hleft₀ :
                  MeasureTheory.Integrable
                    (fun x ↦ ((-f) x) * admissibleDivergence v x) (domainMeasure Ω) :=
                pairingIntegrable (-f) v
              have hleft :
                  MeasureTheory.Integrable
                    (fun x ↦ (-(f x)) * admissibleDivergence v x) (domainMeasure Ω) := by
                refine hleft₀.congr ?_
                filter_upwards [MeasureTheory.Lp.coeFn_neg f] with x hx
                rw [hx]
                simp [neg_mul]
              have hright := smoothPenaltyIntegrable β hβ v
              rw [MeasureTheory.integral_add hleft hright]
              norm_num
      _ = (admissibleDivergencePairing f v.neg : EReal) +
            (((∫ x, β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
                ∂domainMeasure Ω) : ℝ) : EReal) := by
              rw [negPairingIntegral_eq_pairing_neg]
      _ ≤ totalVariation f + (((β * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal) := by
              exact add_le_add
                (admissibleDivergencePairing_le_totalVariation f v.neg)
                (by exact_mod_cast smoothPenaltyIntegral_le_volume β hβ v)

/-- Helper for Theorem 8.23: the Chapter 8 Huber approximation satisfies the source order window
around `TV`. -/
lemma huberApproxTotalVariation_orderBounds
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (ε : ℝ)
    (hε : 0 < ε)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    totalVariation f -
        (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) ≤
      J_ε ε f ∧
      J_ε ε f ≤ totalVariation f := by
  let err : EReal := (((ε / 2) * (domainMeasure Ω Set.univ).toReal : ℝ) : EReal)
  constructor
  · -- First prove the additive version `TV ≤ J_ε + ((ε / 2)Vol(Ω))`, then rewrite it back.
    have hadd :
        totalVariation f ≤
          J_ε ε f + err := by
      refine totalVariation_le_of_forall_admissibleDivergencePairing_le f ?_
      intro v
      rw [huberApproxTotalVariation_def]
      have hpair₀ :
          MeasureTheory.Integrable
            (fun x ↦ ((-f) x) * admissibleDivergence v.neg x) (domainMeasure Ω) :=
        pairingIntegrable (-f) v.neg
      have hpair :
          MeasureTheory.Integrable
            (fun x ↦ (-(f x)) * admissibleDivergence v.neg x) (domainMeasure Ω) := by
        -- Normalize the negated `Lp` representative to the pointwise spelling used in the
        -- witness integrand.
        refine hpair₀.congr ?_
        filter_upwards [MeasureTheory.Lp.coeFn_neg f] with x hx
        rw [hx]
        simp
      have hwitness :
          MeasureTheory.Integrable
            (fun x ↦
              (-(f x)) * admissibleDivergence v.neg x -
                (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2) (domainMeasure Ω) :=
        hpair.sub (huberPenaltyIntegrable ε hε v.neg)
      have hdecomp :
          (admissibleDivergencePairing f v : EReal) =
            (((∫ x, (-(f x)) * admissibleDivergence v.neg x -
                    (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                  ∂domainMeasure Ω) : ℝ) : EReal) +
              (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                    ∂domainMeasure Ω) : ℝ) : EReal) := by
        -- Split the pairing into the `J_ε` witness term plus the Huber penalty remainder.
        rw [admissibleDivergencePairing_def]
        calc
          (((∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω) : ℝ) : EReal)
              = (((∫ x,
                    ((-(f x)) * admissibleDivergence v.neg x -
                        (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2) +
                      (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                  ∂domainMeasure Ω) : ℝ) : EReal) := by
                    congr 1
                    refine MeasureTheory.integral_congr_ae ?_
                    filter_upwards with x
                    simp [admissibleDivergence_neg, sub_eq_add_neg, add_assoc, mul_comm]
          _ = (((∫ x, (-(f x)) * admissibleDivergence v.neg x -
                    (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                  ∂domainMeasure Ω) : ℝ) : EReal) +
                (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                    ∂domainMeasure Ω) : ℝ) : EReal) := by
                    rw [MeasureTheory.integral_add hwitness (huberPenaltyIntegrable ε hε v.neg)]
                    norm_num
      calc
        (admissibleDivergencePairing f v : EReal)
            = (((∫ x, (-(f x)) * admissibleDivergence v.neg x -
                    (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                  ∂domainMeasure Ω) : ℝ) : EReal) +
                (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                    ∂domainMeasure Ω) : ℝ) : EReal) := hdecomp
        _ ≤ sSup (Set.range fun u : AdmissibleTestField Ω ↦
              (((∫ x, (-(f x)) * admissibleDivergence u x -
                      (ε / 2) * ‖u.toTestFunction x‖ ^ 2
                    ∂domainMeasure Ω) : ℝ) : EReal)) + err := by
              have hwitness_le :
                  (((∫ x, (-(f x)) * admissibleDivergence v.neg x -
                          (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                        ∂domainMeasure Ω) : ℝ) : EReal) ≤
                    sSup (Set.range fun u : AdmissibleTestField Ω ↦
                      (((∫ x, (-(f x)) * admissibleDivergence u x -
                              (ε / 2) * ‖u.toTestFunction x‖ ^ 2
                            ∂domainMeasure Ω) : ℝ) : EReal)) := by
                exact le_sSup
                  (s := Set.range fun u : AdmissibleTestField Ω ↦
                    (((∫ x, (-(f x)) * admissibleDivergence u x -
                            (ε / 2) * ‖u.toTestFunction x‖ ^ 2
                          ∂domainMeasure Ω) : ℝ) : EReal))
                  ⟨v.neg, rfl⟩
              have hpen :
                  (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                        ∂domainMeasure Ω) : ℝ) : EReal) ≤ err := by
                simpa [err] using
                  (show
                    (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                          ∂domainMeasure Ω) : ℝ) : EReal) ≤
                      (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) by
                      exact_mod_cast huberPenaltyIntegral_le_volume ε hε v.neg)
              exact add_le_add hwitness_le hpen
    -- Convert the additive window back to the textbook subtraction form.
    have herr_bot : err ≠ ⊥ := by
      simpa [err, EReal.coe_mul] using
        (EReal.coe_ne_bot ((ε / 2) * (domainMeasure Ω Set.univ).toReal))
    have herr_top : err ≠ ⊤ := by
      simpa [err, EReal.coe_mul] using
        (EReal.coe_ne_top ((ε / 2) * (domainMeasure Ω Set.univ).toReal))
    simpa [err] using
      (EReal.sub_le_iff_le_add (Or.inl herr_bot) (Or.inl herr_top)).2 hadd
  · -- Bound each Huber witness above by the unpenalized total-variation pairing.
    rw [huberApproxTotalVariation_def]
    refine sSup_le ?_
    rintro _ ⟨v, rfl⟩
    have hpair₀ :
        MeasureTheory.Integrable
          (fun x ↦ ((-f) x) * admissibleDivergence v x) (domainMeasure Ω) :=
      pairingIntegrable (-f) v
    have hpair :
        MeasureTheory.Integrable
          (fun x ↦ (-(f x)) * admissibleDivergence v x) (domainMeasure Ω) := by
      -- Normalize the negated `Lp` representative to the pointwise spelling used here.
      refine hpair₀.congr ?_
      filter_upwards [MeasureTheory.Lp.coeFn_neg f] with x hx
      rw [hx]
      simp
    have hmono :
        ∫ x, (-(f x)) * admissibleDivergence v x -
            (ε / 2) * ‖v.toTestFunction x‖ ^ 2 ∂domainMeasure Ω ≤
          ∫ x, (-(f x)) * admissibleDivergence v x ∂domainMeasure Ω := by
      -- The Huber penalty is nonnegative, so subtracting it can only decrease the witness.
      refine MeasureTheory.integral_mono_ae
        (hpair.sub (huberPenaltyIntegrable ε hε v))
        hpair ?_
      filter_upwards [huberPenalty_nonneg_ae ε hε v] with x hx
      linarith
    calc
      (((∫ x, (-(f x)) * admissibleDivergence v x -
              (ε / 2) * ‖v.toTestFunction x‖ ^ 2
            ∂domainMeasure Ω) : ℝ) : EReal)
          ≤ (((∫ x, (-(f x)) * admissibleDivergence v x
                ∂domainMeasure Ω) : ℝ) : EReal) := by
              exact_mod_cast hmono
      _ = (admissibleDivergencePairing f v.neg : EReal) := by
            rw [negPairingIntegral_eq_pairing_neg]
      _ ≤ totalVariation f := admissibleDivergencePairing_le_totalVariation f v.neg

end ApproximationUniformConvergence

/-- Helper for Theorem 8.23: `lpToL1` preserves addition on finite-measure domains. -/
lemma lpToL1_add
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f g : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    lpToL1 (f + g) = lpToL1 f + lpToL1 g := by
  -- Both sides are represented by the same almost-everywhere sum.
  refine MeasureTheory.Lp.ext ?_
  filter_upwards with x
  rfl

/-- Helper for Theorem 8.23: `lpToL1` preserves scalar multiplication on finite-measure domains. -/
lemma lpToL1_smul
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (c : ℝ)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    lpToL1 (c • f) = c • lpToL1 f := by
  -- Both sides are represented by the same almost-everywhere scalar multiple.
  refine MeasureTheory.Lp.ext ?_
  filter_upwards with x
  rfl

/-- Helper for Theorem 8.23: the canonical inclusion `lpToL1` satisfies the standard finite-measure
norm bound. -/
lemma lpToL1_norm_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    ‖lpToL1 f‖ ≤
      (domainMeasure Ω Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)).toReal * ‖f‖ := by
  -- Compare the `eLpNorm`s first; the `Lp` norm statement is just the corresponding `toReal`
  -- normalization.
  let fμ : (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ := f
  let C : ENNReal :=
    domainMeasure Ω Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)
  have hLp1 : MeasureTheory.MemLp fμ 1 (domainMeasure Ω) := by
    exact MeasureTheory.Lp.mem_Lp_iff_memLp.mp <|
      MeasureTheory.Lp.antitone (E := ℝ) (μ := domainMeasure Ω)
        (show (1 : ENNReal) ≤ p from Fact.out) f.2
  have hcompare :
      MeasureTheory.eLpNorm fμ 1 (domainMeasure Ω) ≤
        MeasureTheory.eLpNorm fμ p (domainMeasure Ω) * C :=
    MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (show (1 : ENNReal) ≤ p from Fact.out) fμ.aestronglyMeasurable
  have hC_ne_top : C ≠ ⊤ := by
    have hp_inv_le_one : 1 / p.toReal ≤ 1 := by
      by_cases hp_top : p = ⊤
      · simp [hp_top]
      · have hp_one : 1 ≤ p.toReal := by
          simpa using ENNReal.toReal_mono hp_top (show (1 : ENNReal) ≤ p from Fact.out)
        simpa [one_div] using inv_le_one_of_one_le₀ hp_one
    have hC_nonneg : 0 ≤ 1 / (1 : ENNReal).toReal - 1 / p.toReal := by
      simpa using sub_nonneg.mpr hp_inv_le_one
    exact
      (ENNReal.rpow_lt_top_of_nonneg
        hC_nonneg
        (MeasureTheory.measure_ne_top (domainMeasure Ω) Set.univ)).ne
  have hcompareRealENN :
      ENNReal.toReal (MeasureTheory.eLpNorm fμ 1 (domainMeasure Ω)) ≤
        ENNReal.toReal (MeasureTheory.eLpNorm fμ p (domainMeasure Ω) * C) := by
    exact
      (ENNReal.toReal_le_toReal hLp1.2.ne
        (ENNReal.mul_ne_top f.2.ne hC_ne_top)).2 hcompare
  -- Rewrite both `Lp` norms to the same `eLpNorm` spelling and apply the real-valued inequality.
  have hcompareReal :
      ‖lpToL1 f‖ ≤ C.toReal * ‖f‖ := by
    rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def, lpToL1_toAEEqFun]
    simpa [C, fμ, ENNReal.toReal_mul, mul_comm, mul_left_comm, mul_assoc] using hcompareRealENN
  simpa [C] using hcompareReal

/-- Helper for Theorem 8.23: `lpToL1` upgrades to a continuous linear map on finite-measure
domains. -/
def lpToL1ContinuousLinearMap
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)] :
    MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ] MeasureTheory.Lp ℝ 1 (domainMeasure Ω) :=
  LinearMap.mkContinuous
    { toFun := lpToL1
      map_add' := lpToL1_add
      map_smul' := lpToL1_smul }
    (domainMeasure Ω Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)).toReal
    lpToL1_norm_le

/-- Helper for Theorem 8.23: the continuous linear inclusion `lpToL1ContinuousLinearMap`
evaluates to `lpToL1`. -/
@[simp] lemma lpToL1ContinuousLinearMap_apply
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    lpToL1ContinuousLinearMap f = lpToL1 f := by
  -- `mkContinuous` does not change the underlying linear map on points.
  rw [lpToL1ContinuousLinearMap, LinearMap.mkContinuous_apply]
  rfl

/-- Helper for Theorem 8.23: an upper penalty envelope induces the corresponding upper objective
envelope. -/
lemma regularizedFunctional_le_tvRegularized_of_penalty_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα0 : 0 ≤ α)
    (J : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) → EReal)
    (e : ℝ)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (hJ :
      J (lpToL1 f) ≤
        totalVariation (lpToL1 f) + ((e : ℝ) : EReal)) :
    regularizedLeastSquaresFunctional K g α J f ≤
      tvRegularizedLeastSquaresFunctional K g α f + (α : EReal) * ((e : ℝ) : EReal) := by
  -- Rewrite both objectives once so the penalty comparison becomes the only nontrivial step.
  rw [regularizedLeastSquaresFunctional_def, tvRegularizedLeastSquaresFunctional_def]
  have hmul :
      (α : EReal) * J (lpToL1 f) ≤
        (α : EReal) * (totalVariation (lpToL1 f) + ((e : ℝ) : EReal)) :=
    mul_le_mul_of_nonneg_left hJ (by exact_mod_cast hα0)
  have hbase :
      (α : EReal) * J (lpToL1 f) + (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) ≤
        (α : EReal) * (totalVariation (lpToL1 f) + ((e : ℝ) : EReal)) +
          (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) :=
    add_le_add_left hmul (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal))
  calc
    (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) + (α : EReal) * J (lpToL1 f)
        ≤ (α : EReal) * (totalVariation (lpToL1 f) + ((e : ℝ) : EReal)) +
            (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) := by
      simpa [add_assoc, add_left_comm, add_comm] using hbase
    _ = (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) +
          (α : EReal) * totalVariation (lpToL1 f)) +
            (α : EReal) * ((e : ℝ) : EReal) := by
      rw [EReal.left_distrib_of_nonneg_of_ne_top
        (by exact_mod_cast hα0) (EReal.coe_ne_top α)]
      simp [add_assoc, add_comm]

/-- Helper for Theorem 8.23: a lower penalty envelope induces the corresponding lower objective
envelope. -/
lemma tvRegularized_le_regularizedFunctional_of_tv_le_penalty
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα0 : 0 ≤ α)
    (J : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) → EReal)
    (e : ℝ)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (hTV :
      totalVariation (lpToL1 f) ≤
        J (lpToL1 f) + ((e : ℝ) : EReal)) :
    tvRegularizedLeastSquaresFunctional K g α f ≤
      regularizedLeastSquaresFunctional K g α J f + (α : EReal) * ((e : ℝ) : EReal) := by
  -- Rewrite both objectives once so the penalty comparison becomes the only nontrivial step.
  rw [tvRegularizedLeastSquaresFunctional_def, regularizedLeastSquaresFunctional_def]
  have hmul :
      (α : EReal) * totalVariation (lpToL1 f) ≤
        (α : EReal) * (J (lpToL1 f) + ((e : ℝ) : EReal)) :=
    mul_le_mul_of_nonneg_left hTV (by exact_mod_cast hα0)
  have hbase :
      (α : EReal) * totalVariation (lpToL1 f) + (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) ≤
        (α : EReal) * (J (lpToL1 f) + ((e : ℝ) : EReal)) +
          (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) :=
    add_le_add_left hmul (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal))
  calc
    (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) + (α : EReal) * totalVariation (lpToL1 f)
        ≤ (α : EReal) * (J (lpToL1 f) + ((e : ℝ) : EReal)) +
            (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) := by
      simpa [add_assoc, add_left_comm, add_comm] using hbase
    _ = (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) +
          (α : EReal) * J (lpToL1 f)) +
            (α : EReal) * ((e : ℝ) : EReal) := by
      rw [EReal.left_distrib_of_nonneg_of_ne_top
        (by exact_mod_cast hα0) (EReal.coe_ne_top α)]
      simp [add_assoc, add_comm]

/-- Helper for Theorem 8.23: the smooth-approximation minimizer is an exact TV almost-minimizer
with the Exercise 8.16 volume error. -/
lemma smoothNormApprox_exactObjectiveGap
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    (fAlpha : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (fAlphaBeta : ℝ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (h_tv_solution : IsTvRegularizedMinimizer C K g α fAlpha)
    (h_beta_solution :
      ∀ β : ℝ, 0 < β →
        fAlphaBeta β ∈ C ∧
          IsMinOn
            (regularizedLeastSquaresFunctional K g α
              (J_β β))
            C (fAlphaBeta β))
    {β : ℝ}
    (hβ : 0 < β) :
    tvRegularizedLeastSquaresFunctional K g α (fAlphaBeta β) ≤
      tvRegularizedLeastSquaresFunctional K g α fAlpha +
        (α : EReal) * ((((β * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) := by
  rcases h_beta_solution β hβ with ⟨_hfβC, hfβmin⟩
  have hα0 : 0 ≤ α := le_of_lt hα
  -- Compare the perturbed and exact penalties at the minimizing point and the exact solution.
  rcases ApproximationUniformConvergence.smoothNormApproxTotalVariation_orderBounds
      β hβ (lpToL1 (fAlphaBeta β)) with ⟨hlowerBeta, _⟩
  rcases ApproximationUniformConvergence.smoothNormApproxTotalVariation_orderBounds
      β hβ (lpToL1 fAlpha) with ⟨_, hupperAlpha⟩
  have hleft :
      tvRegularizedLeastSquaresFunctional K g α (fAlphaBeta β) ≤
        regularizedLeastSquaresFunctional K g α (J_β β) (fAlphaBeta β) := by
    simpa using tvRegularized_le_regularizedFunctional_of_tv_le_penalty
      K g α hα0 (J_β β) 0 (fAlphaBeta β) (by simpa using hlowerBeta)
  have hmid :
      regularizedLeastSquaresFunctional K g α (J_β β) (fAlphaBeta β) ≤
        regularizedLeastSquaresFunctional K g α (J_β β) fAlpha :=
    hfβmin h_tv_solution.mem
  have hright :
      regularizedLeastSquaresFunctional K g α (J_β β) fAlpha ≤
        tvRegularizedLeastSquaresFunctional K g α fAlpha +
          (α : EReal) * ((((β * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) := by
    simpa using regularizedFunctional_le_tvRegularized_of_penalty_le
      K g α hα0 (J_β β)
      ((β * (domainMeasure Ω Set.univ).toReal) : ℝ) fAlpha hupperAlpha
  exact hleft.trans <| hmid.trans hright

/-- Helper for Theorem 8.23: the Huber-approximation minimizer is an exact TV almost-minimizer
with the Exercise 8.16 volume error. -/
lemma huberApprox_exactObjectiveGap
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    (fAlpha : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (fAlphaEpsilon : ℝ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (h_tv_solution : IsTvRegularizedMinimizer C K g α fAlpha)
    (h_epsilon_solution :
      ∀ ε : ℝ, 0 < ε →
        fAlphaEpsilon ε ∈ C ∧
          IsMinOn
            (regularizedLeastSquaresFunctional K g α
              (J_ε ε))
            C (fAlphaEpsilon ε))
    {ε : ℝ}
    (hε : 0 < ε) :
    tvRegularizedLeastSquaresFunctional K g α (fAlphaEpsilon ε) ≤
      tvRegularizedLeastSquaresFunctional K g α fAlpha +
        (α : EReal) * (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) := by
  rcases h_epsilon_solution ε hε with ⟨_hfεC, hfεmin⟩
  have hα0 : 0 ≤ α := le_of_lt hα
  -- Compare the perturbed and exact penalties at the minimizing point and the exact solution.
  rcases ApproximationUniformConvergence.huberApproxTotalVariation_orderBounds
      ε hε (lpToL1 (fAlphaEpsilon ε)) with
    ⟨hlowerEpsilon, _⟩
  rcases ApproximationUniformConvergence.huberApproxTotalVariation_orderBounds
      ε hε (lpToL1 fAlpha) with
    ⟨_, hupperAlpha⟩
  have hTVle :
      totalVariation (lpToL1 (fAlphaEpsilon ε)) ≤
        J_ε ε (lpToL1 (fAlphaEpsilon ε)) +
          (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) := by
    have herr_bot :
        (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) ≠ ⊥ := by
      exact EReal.coe_ne_bot _
    have herr_top :
        (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) ≠ ⊤ := by
      exact EReal.coe_ne_top _
    exact (EReal.sub_le_iff_le_add (Or.inl herr_bot) (Or.inl herr_top)).1 hlowerEpsilon
  have hleft :
      tvRegularizedLeastSquaresFunctional K g α (fAlphaEpsilon ε) ≤
        regularizedLeastSquaresFunctional K g α (J_ε ε) (fAlphaEpsilon ε) +
          (α : EReal) * (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) := by
    simpa using tvRegularized_le_regularizedFunctional_of_tv_le_penalty
      K g α hα0 (J_ε ε)
      (((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ)
      (fAlphaEpsilon ε) hTVle
  have hmid :
      regularizedLeastSquaresFunctional K g α (J_ε ε) (fAlphaEpsilon ε) ≤
        regularizedLeastSquaresFunctional K g α (J_ε ε) fAlpha :=
    hfεmin h_tv_solution.mem
  have hright :
      regularizedLeastSquaresFunctional K g α (J_ε ε) fAlpha ≤
        tvRegularizedLeastSquaresFunctional K g α fAlpha := by
    simpa using regularizedFunctional_le_tvRegularized_of_penalty_le
      K g α hα0 (J_ε ε) 0 fAlpha (by simpa using hupperAlpha)
  calc
    tvRegularizedLeastSquaresFunctional K g α (fAlphaEpsilon ε)
        ≤ regularizedLeastSquaresFunctional K g α (J_ε ε) (fAlphaEpsilon ε) +
            (α : EReal) * (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) :=
      hleft
    _ ≤ regularizedLeastSquaresFunctional K g α (J_ε ε) fAlpha +
          (α : EReal) * (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) := by
      simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right hmid
        ((α : EReal) * (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)))
    _ ≤ tvRegularizedLeastSquaresFunctional K g α fAlpha +
          (α : EReal) * (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) := by
      simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right hright
        ((α : EReal) * (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)))

/-- Helper for Theorem 8.23: along a positive parameter sequence converging to `0⁺`, the smooth
approximation minimizers satisfy an exact-objective gap with a vanishing scalar error. -/
lemma smoothNormApprox_seq_exactObjectiveGap
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    (fAlpha : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (fAlphaBeta : ℝ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (h_tv_solution : IsTvRegularizedMinimizer C K g α fAlpha)
    (h_beta_solution :
      ∀ β : ℝ, 0 < β →
        fAlphaBeta β ∈ C ∧
          IsMinOn
            (regularizedLeastSquaresFunctional K g α
              (J_β β))
            C (fAlphaBeta β))
    (βs : ℕ → ℝ)
    (hβs : Filter.Tendsto βs Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0))) :
    Filter.Tendsto
        (fun n ↦ α * (βs n * (domainMeasure Ω Set.univ).toReal))
        Filter.atTop
        (nhds 0) ∧
      ∀ᶠ n in Filter.atTop,
        fAlphaBeta (βs n) ∈ C ∧
          tvRegularizedLeastSquaresFunctional K g α (fAlphaBeta (βs n)) ≤
            tvRegularizedLeastSquaresFunctional K g α fAlpha +
              (((α * (βs n * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) := by
  -- Push the parameter sequence through the scalar error map.
  have hδ :
      Filter.Tendsto
        (fun n ↦ α * (βs n * (domainMeasure Ω Set.univ).toReal))
        Filter.atTop
        (nhds (0 : ℝ)) := by
    have hcont : Continuous fun β : ℝ ↦ α * (β * (domainMeasure Ω Set.univ).toReal) := by
      continuity
    simpa [Function.comp_def] using hcont.continuousAt.continuousWithinAt.tendsto.comp hβs
  have hβs_pos : ∀ᶠ n in Filter.atTop, βs n ∈ Set.Ioi (0 : ℝ) :=
    eventually_mem_of_tendsto_nhdsWithin hβs
  refine ⟨by simpa using hδ, ?_⟩
  filter_upwards [hβs_pos] with n hn
  have hgap := smoothNormApprox_exactObjectiveGap
    C K g α hα fAlpha fAlphaBeta h_tv_solution h_beta_solution hn
  exact ⟨(h_beta_solution (βs n) hn).1, by simpa using hgap⟩

/-- Helper for Theorem 8.23: along a positive parameter sequence converging to `0⁺`, the Huber
approximation minimizers satisfy an exact-objective gap with a vanishing scalar error. -/
lemma huberApprox_seq_exactObjectiveGap
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    (fAlpha : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (fAlphaEpsilon : ℝ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (h_tv_solution : IsTvRegularizedMinimizer C K g α fAlpha)
    (h_epsilon_solution :
      ∀ ε : ℝ, 0 < ε →
        fAlphaEpsilon ε ∈ C ∧
          IsMinOn
            (regularizedLeastSquaresFunctional K g α
              (J_ε ε))
            C (fAlphaEpsilon ε))
    (εs : ℕ → ℝ)
    (hεs : Filter.Tendsto εs Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0))) :
    Filter.Tendsto
        (fun n ↦ α * ((εs n / 2) * (domainMeasure Ω Set.univ).toReal))
        Filter.atTop
        (nhds 0) ∧
      ∀ᶠ n in Filter.atTop,
        fAlphaEpsilon (εs n) ∈ C ∧
          tvRegularizedLeastSquaresFunctional K g α (fAlphaEpsilon (εs n)) ≤
            tvRegularizedLeastSquaresFunctional K g α fAlpha +
              (((α * ((εs n / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) := by
  -- Push the parameter sequence through the scalar error map.
  have hδ :
      Filter.Tendsto
        (fun n ↦ α * ((εs n / 2) * (domainMeasure Ω Set.univ).toReal))
        Filter.atTop
        (nhds (0 : ℝ)) := by
    have hcont : Continuous fun ε : ℝ ↦ α * ((ε / 2) * (domainMeasure Ω Set.univ).toReal) := by
      continuity
    simpa [Function.comp_def] using hcont.continuousAt.continuousWithinAt.tendsto.comp hεs
  have hεs_pos : ∀ᶠ n in Filter.atTop, εs n ∈ Set.Ioi (0 : ℝ) :=
    eventually_mem_of_tendsto_nhdsWithin hεs
  refine ⟨by simpa using hδ, ?_⟩
  filter_upwards [hεs_pos] with n hn
  have hgap := huberApprox_exactObjectiveGap
    C K g α hα fAlpha fAlphaEpsilon h_tv_solution h_epsilon_solution hn
  exact ⟨(h_epsilon_solution (εs n) hn).1, by simpa using hgap⟩

/-- Helper for Theorem 8.23: any exact-TV almost-minimizing sequence that converges strongly in
`L^p` must converge to the unique exact TV minimizer. -/
lemma eq_tvSolution_of_tendsto_of_eventually_exactObjectiveGap
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hp_lt : p < ((d : ENNReal) / ((d - 1 : ℕ) : ENNReal)))
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (hC_closed : IsClosed C)
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    (fAlpha : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (h_tv_solution : IsTvRegularizedMinimizer C K g α fAlpha)
    (h_tv_unique : IsUniqueTvRegularizedMinimizer C K g α fAlpha)
    (u : ℕ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    {x : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hu : Filter.Tendsto u Filter.atTop (nhds x))
    (hu_mem : ∀ᶠ n in Filter.atTop, u n ∈ C)
    (δ : ℕ → ℝ)
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hgap :
      ∀ᶠ n in Filter.atTop,
        tvRegularizedLeastSquaresFunctional K g α (u n) ≤
          tvRegularizedLeastSquaresFunctional K g α fAlpha + (((δ n : ℝ) : EReal))) :
    x = fAlpha := by
  have hxC : x ∈ C :=
    hC_closed.mem_of_tendsto hu hu_mem
  by_cases hFtop : tvRegularizedLeastSquaresFunctional K g α fAlpha = ⊤
  · have hxMin : IsMinOn (tvRegularizedLeastSquaresFunctional K g α) C x := by
      -- In the top-valued case every feasible point has the same objective value.
      change ∀ y ∈ C,
        tvRegularizedLeastSquaresFunctional K g α x ≤
          tvRegularizedLeastSquaresFunctional K g α y
      intro y hy
      have hxTop :
          tvRegularizedLeastSquaresFunctional K g α x = ⊤ := by
        have hle : tvRegularizedLeastSquaresFunctional K g α fAlpha ≤
            tvRegularizedLeastSquaresFunctional K g α x :=
          h_tv_solution.isMinOn hxC
        rw [hFtop] at hle
        exact top_le_iff.1 hle
      have hyTop :
          tvRegularizedLeastSquaresFunctional K g α y = ⊤ := by
        have hle : tvRegularizedLeastSquaresFunctional K g α fAlpha ≤
            tvRegularizedLeastSquaresFunctional K g α y :=
          h_tv_solution.isMinOn hy
        rw [hFtop] at hle
        exact top_le_iff.1 hle
      rw [hxTop, hyTop]
    exact h_tv_unique.eq <| IsTvRegularizedMinimizer.ofMemAndIsMinOn hxC hxMin
  · have hp_top : p < (⊤ : ENNReal) :=
      lt_of_lt_of_le hp_lt le_top
    -- Local instance justification (Fact): the weak-`L^p` TV liminf theorem requires an explicit
    -- witness `p < ⊤`, and this is not inferable from the current context without packaging it.
    letI : Fact (p < (⊤ : ENNReal)) := ⟨hp_top⟩
    let residual : MeasureTheory.Lp ℝ p (domainMeasure Ω) → ℝ :=
      fun f ↦ ‖K f - g‖ ^ 2 / 2
    -- Separate the continuous residual term from the weakly lower semicontinuous TV term.
    have hresidualCont : Continuous residual := by
      continuity
    have hresidualLiminf :
        (residual x : EReal) ≤
          Filter.liminf (fun n ↦ (residual (u n) : EReal)) Filter.atTop :=
      LowerSemicontinuousAt.leLiminfEReal_of_tendsto
        (f := residual) (x := x) (u := u) (F := Filter.atTop)
        hresidualCont.continuousAt.lowerSemicontinuousAt hu
    have huL1Raw :
        Filter.Tendsto
          (fun n ↦ lpToL1ContinuousLinearMap (Ω := Ω) (p := p) (u n))
          Filter.atTop
          (nhds (lpToL1ContinuousLinearMap (Ω := Ω) (p := p) x)) :=
      ((lpToL1ContinuousLinearMap (Ω := Ω) (p := p)).continuous.tendsto x).comp hu
    have huL1 :
        Filter.Tendsto (fun n ↦ lpToL1 (u n)) Filter.atTop (nhds (lpToL1 x)) := by
      -- Transport the strong `L^p` convergence through the continuous inclusion `L^p(Ω) → L¹(Ω)`.
      simpa using huL1Raw
    have htvLiminf :
        totalVariation (lpToL1 x) ≤
          Filter.liminf (fun n ↦ totalVariation (lpToL1 (u n))) Filter.atTop :=
      lpTotalVariation_le_liminf_of_tendstoL1 (Ω := Ω)
        (u := fun n ↦ lpToL1 (u n)) (g := lpToL1 x) huL1
    have htvScaledLiminf :
        (α : EReal) * totalVariation (lpToL1 x) ≤
          Filter.liminf
            (fun n ↦ (α : EReal) * totalVariation (lpToL1 (u n)))
            Filter.atTop := by
      rw [EReal.liminf_const_mul_of_nonneg_of_ne_top
        (f := Filter.atTop)
        (u := fun n ↦ totalVariation (lpToL1 (u n)))
        (c := (α : EReal))]
      · exact mul_le_mul_of_nonneg_left htvLiminf (by exact_mod_cast le_of_lt hα)
      · exact_mod_cast le_of_lt hα
      · exact EReal.coe_ne_top α
    have hobjectiveLiminf :
        tvRegularizedLeastSquaresFunctional K g α x ≤
          Filter.liminf
            (fun n ↦ tvRegularizedLeastSquaresFunctional K g α (u n))
            Filter.atTop := by
      rw [tvRegularizedLeastSquaresFunctional_def]
      have hadd :
          (residual x : EReal) + (α : EReal) * totalVariation (lpToL1 x) ≤
            Filter.liminf (fun n ↦ (residual (u n) : EReal)) Filter.atTop +
              Filter.liminf
                (fun n ↦ (α : EReal) * totalVariation (lpToL1 (u n)))
                Filter.atTop :=
        add_le_add hresidualLiminf htvScaledLiminf
      exact hadd.trans <|
        EReal.le_liminf_add
          (u := fun n ↦ (residual (u n) : EReal))
          (v := fun n ↦ (α : EReal) * totalVariation (lpToL1 (u n)))
          (f := Filter.atTop)
    have hδE :
        Filter.Tendsto (fun n ↦ (((δ n : ℝ) : EReal))) Filter.atTop (nhds (0 : EReal)) := by
      exact continuous_coe_real_ereal.tendsto 0 |>.comp hδ
    have hupperTendsto :
        Filter.Tendsto
          (fun n ↦
            tvRegularizedLeastSquaresFunctional K g α fAlpha + (((δ n : ℝ) : EReal)))
          Filter.atTop
          (nhds (tvRegularizedLeastSquaresFunctional K g α fAlpha)) := by
      have hadd :
          ContinuousAt
            (fun p : EReal × EReal ↦ p.1 + p.2)
            (tvRegularizedLeastSquaresFunctional K g α fAlpha, 0) :=
        EReal.continuousAt_add
          (p := (tvRegularizedLeastSquaresFunctional K g α fAlpha, 0))
          (Or.inr (by simp))
          (Or.inr (by simp))
      have hpair :
          Filter.Tendsto
            (fun n ↦
              (tvRegularizedLeastSquaresFunctional K g α fAlpha, (((δ n : ℝ) : EReal))))
            Filter.atTop
            (nhds (tvRegularizedLeastSquaresFunctional K g α fAlpha, 0)) :=
        tendsto_const_nhds.prodMk_nhds hδE
      have hupperRaw :
          Filter.Tendsto
            (fun n ↦
              (fun p : EReal × EReal ↦ p.1 + p.2)
                (tvRegularizedLeastSquaresFunctional K g α fAlpha, (((δ n : ℝ) : EReal))))
            Filter.atTop
            (nhds
              ((fun p : EReal × EReal ↦ p.1 + p.2)
                (tvRegularizedLeastSquaresFunctional K g α fAlpha, 0))) :=
        hadd.tendsto.comp hpair
      simpa using hupperRaw
    have hupperLiminf :
        Filter.liminf
            (fun n ↦ tvRegularizedLeastSquaresFunctional K g α (u n))
            Filter.atTop ≤
          tvRegularizedLeastSquaresFunctional K g α fAlpha := by
      calc
        Filter.liminf
            (fun n ↦ tvRegularizedLeastSquaresFunctional K g α (u n))
            Filter.atTop
            ≤ Filter.liminf
                (fun n ↦
                  tvRegularizedLeastSquaresFunctional K g α fAlpha + (((δ n : ℝ) : EReal)))
                Filter.atTop := by
                  exact Filter.liminf_le_liminf hgap
        _ = tvRegularizedLeastSquaresFunctional K g α fAlpha := by
              simpa using hupperTendsto.liminf_eq
    have hxMin : IsMinOn (tvRegularizedLeastSquaresFunctional K g α) C x := by
      -- The liminf bounds show that the limit point is another exact minimizer.
      intro y hy
      exact (hobjectiveLiminf.trans hupperLiminf).trans (h_tv_solution.isMinOn hy)
    exact h_tv_unique.eq <| IsTvRegularizedMinimizer.ofMemAndIsMinOn hxC hxMin

/-- Helper for Theorem 8.23: an exact-objective upper bound controls the total-variation term. -/
lemma tvObjectiveSublevel_totalVariationBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    {B : EReal}
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hObj :
      tvRegularizedLeastSquaresFunctional K g α f ≤ B) :
    (α : EReal) * totalVariation (lpToL1 f) ≤ B := by
  -- Drop the nonnegative residual term from the exact objective.
  have hres_nonneg :
      (0 : EReal) ≤ (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) := by
    exact_mod_cast (show 0 ≤ ‖K f - g‖ ^ 2 / 2 by positivity)
  have hpenalty_le :
      (α : EReal) * totalVariation (lpToL1 f) ≤
        (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) +
          (α : EReal) * totalVariation (lpToL1 f)) := by
    simpa [add_comm] using
      (le_add_of_nonneg_left hres_nonneg :
        (α : EReal) * totalVariation (lpToL1 f) ≤
          (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) +
            (α : EReal) * totalVariation (lpToL1 f))
  calc
    (α : EReal) * totalVariation (lpToL1 f)
        ≤ (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) +
            (α : EReal) * totalVariation (lpToL1 f)) :=
      hpenalty_le
    _ = tvRegularizedLeastSquaresFunctional K g α f := by
      rw [tvRegularizedLeastSquaresFunctional_def]
    _ ≤ B := hObj

/-- Helper for Theorem 8.23: an exact-objective upper bound also controls the quadratic residual
term. -/
lemma tvObjectiveSublevel_residualBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    {B : EReal}
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hObj :
      tvRegularizedLeastSquaresFunctional K g α f ≤ B) :
    (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) ≤ B := by
  have hpenalty_nonneg :
      (0 : EReal) ≤ (α : EReal) * totalVariation (lpToL1 f) := by
    have htv_nonneg : (0 : EReal) ≤ totalVariation (lpToL1 f) := by
      have hdiv_zero :
          ∀ x : EuclideanSpace ℝ (Fin d),
            admissibleDivergence (AdmissibleTestField.zero Ω) x = 0 := by
        intro x
        have hfd :
            fderiv ℝ (⇑(0 : TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1)) x = 0 := by
          change fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin d) =>
            (0 : EuclideanSpace ℝ (Fin d))) x = 0
          simp
        rw [admissibleDivergence_def, AdmissibleTestField.zero_toTestFunction, hfd]
        simp
      rw [totalVariation_def]
      refine le_sSup ?_
      refine ⟨AdmissibleTestField.zero Ω, by
        change
          ((admissibleDivergencePairing
              (lpToL1 f) (AdmissibleTestField.zero Ω) : ℝ) : EReal) = 0
        rw [admissibleDivergencePairing_def]
        simp [hdiv_zero]⟩
    exact mul_nonneg (by exact_mod_cast le_of_lt hα)
      htv_nonneg
  -- Drop the nonnegative TV penalty to keep only the least-squares residual term.
  have hresidual_le :
      (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) ≤
        (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) +
          (α : EReal) * totalVariation (lpToL1 f) := by
    exact le_add_of_nonneg_right hpenalty_nonneg
  calc
    (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal))
        ≤ (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) +
            (α : EReal) * totalVariation (lpToL1 f) :=
      hresidual_le
    _ = tvRegularizedLeastSquaresFunctional K g α f := by
      rw [tvRegularizedLeastSquaresFunctional_def]
    _ ≤ B := hObj

/-- Helper for Theorem 8.23: strong `L^p` convergence preserves exact-objective upper bounds. -/
lemma tvObjective_le_of_tendsto_of_eventually_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hp_lt : p < ((d : ENNReal) / ((d - 1 : ℕ) : ENNReal)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    {B : EReal}
    (u : ℕ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    {x : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hu : Filter.Tendsto u Filter.atTop (nhds x))
    (huB :
      ∀ᶠ n in Filter.atTop,
        tvRegularizedLeastSquaresFunctional K g α (u n) ≤ B) :
    tvRegularizedLeastSquaresFunctional K g α x ≤ B := by
  have hp_top : p < (⊤ : ENNReal) :=
    lt_of_lt_of_le hp_lt le_top
  -- Local instance justification (Fact): the weak-`L^p` TV liminf theorem requires an explicit
  -- witness `p < ⊤`, and this is not inferable from the current context without packaging it.
  letI : Fact (p < (⊤ : ENNReal)) := ⟨hp_top⟩
  let residual : MeasureTheory.Lp ℝ p (domainMeasure Ω) → ℝ :=
    fun f ↦ ‖K f - g‖ ^ 2 / 2
  -- Separate the continuous residual term from the weakly lower semicontinuous TV term.
  have hresidualCont : Continuous residual := by
    continuity
  have hresidualLiminf :
      (residual x : EReal) ≤
        Filter.liminf (fun n ↦ (residual (u n) : EReal)) Filter.atTop :=
    LowerSemicontinuousAt.leLiminfEReal_of_tendsto
      (f := residual) (x := x) (u := u) (F := Filter.atTop)
      hresidualCont.continuousAt.lowerSemicontinuousAt hu
  have huL1Raw :
      Filter.Tendsto
        (fun n ↦ lpToL1ContinuousLinearMap (Ω := Ω) (p := p) (u n))
        Filter.atTop
        (nhds (lpToL1ContinuousLinearMap (Ω := Ω) (p := p) x)) :=
    ((lpToL1ContinuousLinearMap (Ω := Ω) (p := p)).continuous.tendsto x).comp hu
  have huL1 :
      Filter.Tendsto (fun n ↦ lpToL1 (u n)) Filter.atTop (nhds (lpToL1 x)) := by
    -- Transport the strong `L^p` convergence through the continuous inclusion `L^p(Ω) → L¹(Ω)`.
    simpa using huL1Raw
  have htvLiminf :
      totalVariation (lpToL1 x) ≤
        Filter.liminf (fun n ↦ totalVariation (lpToL1 (u n))) Filter.atTop :=
    lpTotalVariation_le_liminf_of_tendstoL1 (Ω := Ω)
      (u := fun n ↦ lpToL1 (u n)) (g := lpToL1 x) huL1
  have htvScaledLiminf :
      (α : EReal) * totalVariation (lpToL1 x) ≤
        Filter.liminf
          (fun n ↦ (α : EReal) * totalVariation (lpToL1 (u n)))
          Filter.atTop := by
    rw [EReal.liminf_const_mul_of_nonneg_of_ne_top
      (f := Filter.atTop)
      (u := fun n ↦ totalVariation (lpToL1 (u n)))
      (c := (α : EReal))]
    · exact mul_le_mul_of_nonneg_left htvLiminf (by exact_mod_cast le_of_lt hα)
    · exact_mod_cast le_of_lt hα
    · exact EReal.coe_ne_top α
  have hobjectiveLiminf :
      tvRegularizedLeastSquaresFunctional K g α x ≤
        Filter.liminf
          (fun n ↦ tvRegularizedLeastSquaresFunctional K g α (u n))
          Filter.atTop := by
    rw [tvRegularizedLeastSquaresFunctional_def]
    have hadd :
        (residual x : EReal) + (α : EReal) * totalVariation (lpToL1 x) ≤
          Filter.liminf (fun n ↦ (residual (u n) : EReal)) Filter.atTop +
            Filter.liminf
              (fun n ↦ (α : EReal) * totalVariation (lpToL1 (u n)))
              Filter.atTop :=
      add_le_add hresidualLiminf htvScaledLiminf
    exact hadd.trans <|
      EReal.le_liminf_add
        (u := fun n ↦ (residual (u n) : EReal))
        (v := fun n ↦ (α : EReal) * totalVariation (lpToL1 (u n)))
        (f := Filter.atTop)
  have hupperLiminf :
      Filter.liminf
          (fun n ↦ tvRegularizedLeastSquaresFunctional K g α (u n))
          Filter.atTop ≤ B := by
    calc
      Filter.liminf
          (fun n ↦ tvRegularizedLeastSquaresFunctional K g α (u n))
          Filter.atTop
          ≤ Filter.liminf (fun _ : ℕ ↦ B) Filter.atTop := by
            exact Filter.liminf_le_liminf huB
      _ = B := by
            rw [Filter.liminf_const]
  exact hobjectiveLiminf.trans hupperLiminf

/-- Helper for Theorem 8.23: away from the one-dimensional endpoint, the owner-side critical
exponent is exactly the source ratio. -/
lemma criticalExponent_eq_sourceRatio_of_ne_one
    (hd1 : d ≠ 1) :
    BVCompactness.criticalExponent d = ((d : ENNReal) / ((d - 1 : ℕ) : ENNReal)) := by
  -- Route correction: outside `module`, this is a direct owner-side definitional rewrite.
  simp [BVCompactness.criticalExponent, hd1]

/-- Helper for Theorem 8.23: the source exponent bound implies the owner-side
`BVCompactness.criticalExponent` bound. -/
lemma ltCriticalExponentOfLtSourceRatio
    {p : ENNReal}
    (hp_lt : p < ((d : ENNReal) / ((d - 1 : ℕ) : ENNReal))) :
    p < BVCompactness.criticalExponent d := by
  by_cases hd1 : d = 1
  · -- In dimension one the owner-side exponent is explicitly `⊤`.
    have hp_top : p < (⊤ : ENNReal) := by
      simpa [hd1] using hp_lt
    subst hd1
    simpa [BVCompactness.criticalExponent_one] using hp_top
  · -- Outside the one-dimensional endpoint, rewrite once to the source ratio and reuse `hp_lt`.
    simpa [criticalExponent_eq_sourceRatio_of_ne_one (d := d) hd1] using hp_lt

/-- Helper for Theorem 8.23: a finite exact-objective upper bound yields an unscaled total
variation bound. -/
lemma tvObjectiveSublevel_totalVariationBound_of_ltTop
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    (B : EReal)
    (hB : B < ⊤)
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hObj :
      tvRegularizedLeastSquaresFunctional K g α f ≤ B) :
    totalVariation (lpToL1 f) ≤ (B / (α : EReal)).toReal := by
  -- First isolate the scaled TV term already controlled by the objective bound.
  have hscaled :
      (α : EReal) * totalVariation (lpToL1 f) ≤ B :=
    tvObjectiveSublevel_totalVariationBound K g α hObj
  have hαE_pos : (0 : EReal) < (α : EReal) := by
    exact_mod_cast hα
  have hαE_ne_top : (α : EReal) ≠ ⊤ :=
    EReal.coe_ne_top α
  have hdiv_ne_top : B / (α : EReal) ≠ ⊤ := by
    -- The quotient stays finite because both `B` and `α` are finite and `α > 0`.
    rw [EReal.div_eq_inv_mul]
    refine (EReal.mul_ne_top ((α : EReal)⁻¹) B).2 ?_
    constructor
    · exact Or.inl <| ne_bot_of_gt <| EReal.inv_pos_of_pos_ne_top hαE_pos hαE_ne_top
    constructor
    · exact Or.inl <| EReal.inv_nonneg_of_nonneg <| le_of_lt hαE_pos
    constructor
    · exact Or.inl <| (EReal.inv_lt_top (α : EReal)).ne
    · exact Or.inr <| ne_of_lt hB
  have htv_div :
      totalVariation (lpToL1 f) ≤ B / (α : EReal) := by
    -- Divide the scaled bound by the positive regularization parameter.
    exact (EReal.le_div_iff_mul_le hαE_pos hαE_ne_top).2 <| by
      simpa [mul_comm] using hscaled
  exact htv_div.trans <| EReal.le_coe_toReal hdiv_ne_top

/-- Helper for Theorem 8.23: a finite exact-TV sublevel should admit an eventual `L¹(Ω)` bound
once the constant mode is controlled on bounded domains. -/
lemma eventualLpToL1Bound_of_eventually_tvSublevel
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    (hK_one : K (MeasureTheory.Lp.const p (domainMeasure Ω) (1 : ℝ)) ≠ 0)
    (B : EReal)
    (hB : B < ⊤)
    (u : ℕ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (huB :
      ∀ᶠ n in Filter.atTop,
        tvRegularizedLeastSquaresFunctional K g α (u n) ≤
          B) :
    ∃ M : ℝ, ∀ᶠ n in Filter.atTop, ‖lpToL1 (u n)‖ ≤ M := by
  -- Route correction: the remaining analytic core is the sequence-level constant-mode coercivity
  -- estimate needed before any BV compactness argument can start.
  -- TODO: normalize a contradiction subsequence using the finite sublevel `B`, use the resulting
  -- uniform TV and residual bounds to extract a nonzero `L^p` limit with `TV = 0` and `K x = 0`,
  -- and then close with a source-backed zero-TV rigidity lemma.
  have _hB := hB
  have _huB := huB
  sorry

/-- Helper for Theorem 8.23: lifting an `L^p(Ω)` point to `BV(Ω)` and back through
`BVCompactness.toLp` recovers the original point. -/
lemma toLp_of_bvLift_eq
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal}
    [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp_le : p ≤ BVCompactness.criticalExponent d)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (hf : IsBV (lpToL1 f)) :
    BVCompactness.toLp hd hΩ hp_le (BV.ofLp (lpToL1 f) hf) = f := by
  -- Compare the transported point on the common almost-everywhere representative.
  refine MeasureTheory.Lp.ext ?_
  rw [BVCompactness.toLp_toAEEqFun, BV.ofLp_toL1, lpToL1_toAEEqFun]

/-- Helper for Theorem 8.23: an explicit `‖·‖ + TV` witness packages directly into
`IsBVBounded`. -/
lemma isBVBounded_of_norm_add_totalVariation_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {S : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))}
    (hS :
      ∃ C : ℝ, ∀ ⦃f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)⦄, f ∈ S →
        ((‖f‖ : ℝ) : EReal) + totalVariation f ≤ (C : EReal)) :
    IsBVBounded S := by
  -- Route correction: outside `module`, the BV-boundedness predicate unfolds to the given witness.
  simpa [IsBVBounded] using hS

/-- Helper for Theorem 8.23: an eventual `L¹(Ω)` bound and eventual exact-objective upper bound
make a tail of the sequence image BV-bounded. -/
lemma exactGapSequence_isBVBounded
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    (B : EReal)
    (hB : B < ⊤)
    (u : ℕ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (hL1 : ∃ M : ℝ, ∀ᶠ n in Filter.atTop, ‖lpToL1 (u n)‖ ≤ M)
    (huB :
      ∀ᶠ n in Filter.atTop,
        tvRegularizedLeastSquaresFunctional K g α (u n) ≤ B) :
    ∃ N : ℕ,
      IsBVBounded
        {w : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) |
          ∃ n : ℕ, N ≤ n ∧ w = lpToL1 (u n)} := by
  rcases hL1 with ⟨M, hM⟩
  rcases Filter.eventually_atTop.1 hM with ⟨N₁, hN₁⟩
  rcases Filter.eventually_atTop.1 huB with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  -- Unfold the BV-boundedness witness directly and combine the tail `L¹` and TV bounds.
  refine isBVBounded_of_norm_add_totalVariation_le ?_
  refine ⟨M + (B / (α : EReal)).toReal, ?_⟩
  intro w hw
  rcases hw with ⟨n, hn, rfl⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn
  have hnorm : ‖lpToL1 (u n)‖ ≤ M :=
    hN₁ n hn₁
  have htv :
      totalVariation (lpToL1 (u n)) ≤ (B / (α : EReal)).toReal :=
    tvObjectiveSublevel_totalVariationBound_of_ltTop
      (Ω := Ω) (p := p) K g α hα B hB (hN₂ n hn₂)
  -- Combine the tail `L¹` and total-variation bounds into the BV-boundedness inequality.
  calc
    ((‖lpToL1 (u n)‖ : ℝ) : EReal) + totalVariation (lpToL1 (u n))
        ≤ (M : EReal) + (((B / (α : EReal)).toReal : ℝ) : EReal) := by
          exact add_le_add (by exact_mod_cast hnorm) htv
    _ = ((M + (B / (α : EReal)).toReal : ℝ) : EReal) := by
          rw [EReal.coe_add]

/-- Helper for Theorem 8.23: if the exact TV minimizer has objective value `⊤`, then every
feasible point has the same objective value and must coincide with the unique minimizer. -/
lemma eq_tvSolution_of_mem_of_tvObjective_eq_top
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (fAlpha : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (h_tv_solution : IsTvRegularizedMinimizer C K g α fAlpha)
    (h_tv_unique : IsUniqueTvRegularizedMinimizer C K g α fAlpha)
    (hFtop : tvRegularizedLeastSquaresFunctional K g α fAlpha = ⊤)
    {y : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hy : y ∈ C) :
    y = fAlpha := by
  have hyMin : IsMinOn (tvRegularizedLeastSquaresFunctional K g α) C y := by
    -- In the top-valued case every feasible point is again a minimizer.
    change ∀ z ∈ C,
      tvRegularizedLeastSquaresFunctional K g α y ≤
        tvRegularizedLeastSquaresFunctional K g α z
    intro z hz
    have htop :
        tvRegularizedLeastSquaresFunctional K g α y = ⊤ := by
      have hle : tvRegularizedLeastSquaresFunctional K g α fAlpha ≤
          tvRegularizedLeastSquaresFunctional K g α y :=
        h_tv_solution.isMinOn hy
      rw [hFtop] at hle
      exact top_le_iff.1 hle
    have hzTop :
        tvRegularizedLeastSquaresFunctional K g α z = ⊤ := by
      have hle : tvRegularizedLeastSquaresFunctional K g α fAlpha ≤
          tvRegularizedLeastSquaresFunctional K g α z :=
        h_tv_solution.isMinOn hz
      rw [hFtop] at hle
      exact top_le_iff.1 hle
    rw [htop, hzTop]
  exact h_tv_unique.eq <| IsTvRegularizedMinimizer.ofMemAndIsMinOn hy hyMin

/-- Helper for Theorem 8.23: an exact-objective almost-minimizing sequence admits a strongly
convergent subsequence once one tail of its `L¹(Ω)` image is BV-bounded. -/
lemma exactGapSequence_subseq_tendsto
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp_lt : p < ((d : ENNReal) / ((d - 1 : ℕ) : ENNReal)))
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (hC_closed : IsClosed C)
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    (B : EReal)
    (_hB : B < ⊤)
    (u : ℕ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (hTail :
      ∃ N : ℕ,
        IsBVBounded
          {w : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) |
            ∃ n : ℕ, N ≤ n ∧ w = lpToL1 (u n)})
    (hu :
      ∀ᶠ n in Filter.atTop,
        u n ∈ C ∧
          tvRegularizedLeastSquaresFunctional K g α (u n) ≤ B) :
    ∃ x : MeasureTheory.Lp ℝ p (domainMeasure Ω), ∃ ψ : ℕ → ℕ,
      x ∈ C ∧
        tvRegularizedLeastSquaresFunctional K g α x ≤ B ∧
        StrictMono ψ ∧
        Filter.Tendsto (u ∘ ψ) Filter.atTop (nhds x) :=
by
  rcases hTail with ⟨N, hT⟩
  let T : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :=
    {w : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) |
      ∃ n : ℕ, N ≤ n ∧ w = lpToL1 (u n)}
  let S : Set (BV Ω) := {v : BV Ω | v.toL1 ∈ T}
  rcases hT.norm_add_totalVariation_le with ⟨M, hM⟩
  have hS :
      IsBVBounded (BV.toL1 '' S) := by
    -- Passing from BV lifts back to their `L¹(Ω)` representatives only shrinks the tail image.
    refine IsBVBounded.mono hT ?_
    rintro _ ⟨v, hvS, rfl⟩
    exact hvS
  have hp_crit : p < BVCompactness.criticalExponent d := by
    -- Reduce the source exponent bound to the owner-side `criticalExponent` spelling once.
    exact ltCriticalExponentOfLtSourceRatio (d := d) hp_lt
  have hp_le : p ≤ BVCompactness.criticalExponent d :=
    le_of_lt hp_crit
  let emb : BV Ω → MeasureTheory.Lp ℝ p (domainMeasure Ω) :=
    BVCompactness.toSubcriticalLp hd hΩ hp_crit
  have hcompact :
      IsCompact (closure (emb '' S)) := by
    -- Route correction: the compactness theorem is already available on the aggregate owner.
    simpa [emb, BVCompactness.subcriticalLpImage, BVCompactness.lpImage,
      BVCompactness.toSubcriticalLp] using
      BVCompactness.subcriticalLp hd hΩ S hS hp_crit
  have hu_closure :
      ∀ᶠ n in Filter.atTop, u n ∈ closure (emb '' S) := by
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hwT : lpToL1 (u n) ∈ T := by
      exact ⟨n, hn, rfl⟩
    have hwBV : IsBV (lpToL1 (u n)) := by
      -- The BV-boundedness estimate gives the finite `‖·‖ + TV` witness needed for `BV.ofLp`.
      exact (isBV_iff _).2 <|
        lt_of_le_of_lt (hM hwT) (by exact EReal.coe_lt_top M)
    let v : BV Ω := BV.ofLp (lpToL1 (u n)) hwBV
    have hvS : v ∈ S := by
      simpa [S, v, BV.ofLp_toL1] using hwT
    have huv : emb v = u n := by
      simpa [emb, v, hp_le, BVCompactness.toSubcriticalLp] using toLp_of_bvLift_eq
        (Ω := Ω) (p := p) hd hΩ hp_le (u n) hwBV
    exact subset_closure ⟨v, hvS, huv⟩
  obtain ⟨x, _hxcl, ψ, hψmono, hψtendsto⟩ :=
    hcompact.tendsto_subseq' hu_closure.frequently
  have huψ :
      ∀ᶠ n in Filter.atTop,
        u (ψ n) ∈ C ∧
          tvRegularizedLeastSquaresFunctional K g α (u (ψ n)) ≤ B := by
    exact hψmono.tendsto_atTop.eventually hu
  have hxC : x ∈ C :=
    hC_closed.mem_of_tendsto hψtendsto (huψ.mono fun _ hn ↦ hn.1)
  have hxB :
      tvRegularizedLeastSquaresFunctional K g α x ≤ B := by
    -- Lower semicontinuity of the exact objective passes the eventual exact-sublevel bound
    -- to the subsequential limit.
    exact tvObjective_le_of_tendsto_of_eventually_le
      (Ω := Ω) (p := p) hp_lt K g α hα (u ∘ ψ) hψtendsto
      (huψ.mono fun _ hn ↦ hn.2)
  exact ⟨x, ψ, hxC, hxB, hψmono, hψtendsto⟩

/- thm_8_23. Main labeled source-facing entry.

Theorem 8.23 splits into the two atomic convergence clauses below. In both
clauses the limit is a fixed TV-regularized solution `fAlpha`, so the file
keeps the minimal source-faithful uniqueness premise making that limit
canonical, while leaving the perturbed families as arbitrary minimizing
selections. -/

/-- thm_8_23 (1). Theorem 8.23 (1). Fix `α > 0` and the Chapter 8
least-squares/TV objective
`tvRegularizedLeastSquaresFunctional K g α` on a closed constraint set `C ⊆ L^p(Ω)`
with `1 ≤ p < d / (d - 1)` and `K 1 ≠ 0`. If `fAlpha` is the unique corresponding
TV-regularized solution and `fAlphaBeta β` is the corresponding regularized solution after
replacing `TV` by `J_β β`, then `fAlphaBeta` converges to `fAlpha` in `L^p`
norm as `β → 0⁺` on bounded `Ω`. -/
theorem smoothNormApproxRegularizedSolutions_tendsto_tvSolution
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp_lt : p < ((d : ENNReal) / ((d - 1 : ℕ) : ENNReal)))
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))) (hC_closed : IsClosed C)
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)) (α : ℝ) (hα : 0 < α)
    (hK_one : K (MeasureTheory.Lp.const p (domainMeasure Ω) (1 : ℝ)) ≠ 0)
    (fAlpha : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (fAlphaBeta : ℝ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (h_tv_solution : IsTvRegularizedMinimizer C K g α fAlpha)
    (h_tv_unique : IsUniqueTvRegularizedMinimizer C K g α fAlpha)
    (h_beta_solution :
      ∀ β : ℝ, 0 < β →
        fAlphaBeta β ∈ C ∧
          IsMinOn
            (regularizedLeastSquaresFunctional K g α
              (J_β β))
            C (fAlphaBeta β)) :
    Filter.Tendsto fAlphaBeta (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds fAlpha) := by
  by_cases hFtop : tvRegularizedLeastSquaresFunctional K g α fAlpha = ⊤
  · -- In the top-valued case the feasible set is already the singleton `{fAlpha}`.
    have heq :
        fAlphaBeta =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] fun _ ↦ fAlpha := by
      filter_upwards [self_mem_nhdsWithin] with β hβ
      exact eq_tvSolution_of_mem_of_tvObjective_eq_top
        C K g α fAlpha h_tv_solution h_tv_unique hFtop (h_beta_solution β hβ).1
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  · -- Route correction: reduce convergence to the subsequence criterion and isolate compactness.
    refine Filter.tendsto_of_subseq_tendsto fun βs hβs ↦ ?_
    rcases smoothNormApprox_seq_exactObjectiveGap
        C K g α hα fAlpha fAlphaBeta h_tv_solution h_beta_solution βs hβs with ⟨hδ, hgap⟩
    have hsmall :
        ∀ᶠ n in Filter.atTop,
          α * (βs n * (domainMeasure Ω Set.univ).toReal) < 1 := by
      exact hδ.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 1))
    have hu :
        ∀ᶠ n in Filter.atTop,
          fAlphaBeta (βs n) ∈ C ∧
            tvRegularizedLeastSquaresFunctional K g α (fAlphaBeta (βs n)) ≤
              tvRegularizedLeastSquaresFunctional K g α fAlpha + 1 := by
      filter_upwards [hgap, hsmall] with n hnGap hnSmall
      refine ⟨hnGap.1, ?_⟩
      have herr :
          (((α * (βs n * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) ≤ 1 := by
        exact_mod_cast le_of_lt hnSmall
      exact hnGap.2.trans <|
        by simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_left herr (tvRegularizedLeastSquaresFunctional K g α fAlpha)
    have hB :
        tvRegularizedLeastSquaresFunctional K g α fAlpha + 1 < ⊤ := by
      have hone : (1 : EReal) ≠ ⊤ := by
        intro h
        cases h
      exact EReal.add_lt_top hFtop hone
    have huMem : ∀ᶠ n in Filter.atTop, fAlphaBeta (βs n) ∈ C :=
      hgap.mono fun _ hn ↦ hn.1
    have hL1 :
        ∃ M : ℝ, ∀ᶠ n in Filter.atTop, ‖lpToL1 (fAlphaBeta (βs n))‖ ≤ M :=
      eventualLpToL1Bound_of_eventually_tvSublevel
        (Ω := Ω) (p := p) hΩ K g α hα hK_one
        (tvRegularizedLeastSquaresFunctional K g α fAlpha + 1) hB
        (fun n ↦ fAlphaBeta (βs n)) (hu.mono fun _ hn ↦ hn.2)
    rcases exactGapSequence_isBVBounded
        (Ω := Ω) (p := p) K g α hα
        (tvRegularizedLeastSquaresFunctional K g α fAlpha + 1) hB
        (fun n ↦ fAlphaBeta (βs n)) hL1
        (hu.mono fun _ hn ↦ hn.2) with
      ⟨N, hTail⟩
    rcases exactGapSequence_subseq_tendsto
        hd hΩ hp_lt C hC_closed K g α hα
        (tvRegularizedLeastSquaresFunctional K g α fAlpha + 1) hB
        (fun n ↦ fAlphaBeta (βs n)) ⟨N, hTail⟩ hu with
      ⟨x, ψ, _hxC, _hxB, hψ, hlim⟩
    have huMemSub : ∀ᶠ n in Filter.atTop, fAlphaBeta (βs (ψ n)) ∈ C :=
      hψ.tendsto_atTop.eventually huMem
    have hδSub :
        Filter.Tendsto
          (fun n ↦ α * (βs (ψ n) * (domainMeasure Ω Set.univ).toReal))
          Filter.atTop
          (nhds 0) :=
      hδ.comp hψ.tendsto_atTop
    have hgapSub :
        ∀ᶠ n in Filter.atTop,
          tvRegularizedLeastSquaresFunctional K g α (fAlphaBeta (βs (ψ n))) ≤
            tvRegularizedLeastSquaresFunctional K g α fAlpha +
              (((α * (βs (ψ n) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) :=
      hψ.tendsto_atTop.eventually hgap |>.mono fun _ hn ↦ hn.2
    have hxEq :
        x = fAlpha :=
      eq_tvSolution_of_tendsto_of_eventually_exactObjectiveGap
        hp_lt C hC_closed K g α hα fAlpha h_tv_solution h_tv_unique
        (fun n ↦ fAlphaBeta (βs (ψ n))) hlim huMemSub
        (fun n ↦ α * (βs (ψ n) * (domainMeasure Ω Set.univ).toReal)) hδSub hgapSub
    refine ⟨ψ, ?_⟩
    simpa [Function.comp_def, hxEq] using hlim

/-- thm_8_23 (2). Theorem 8.23 (2). Fix `α > 0` and the Chapter 8
least-squares/TV objective
`tvRegularizedLeastSquaresFunctional K g α` on a closed constraint set `C ⊆ L^p(Ω)`
with `1 ≤ p < d / (d - 1)` and `K 1 ≠ 0`. If `fAlpha` is the unique corresponding
TV-regularized solution and `fAlphaEpsilon ε` is the corresponding regularized solution after
replacing `TV` by `J_ε ε`, then `fAlphaEpsilon` converges to `fAlpha` in `L^p`
norm as `ε → 0⁺` on bounded `Ω`. -/
theorem huberApproxRegularizedSolutions_tendsto_tvSolution
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp_lt : p < ((d : ENNReal) / ((d - 1 : ℕ) : ENNReal)))
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))) (hC_closed : IsClosed C)
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)) (α : ℝ) (hα : 0 < α)
    (hK_one : K (MeasureTheory.Lp.const p (domainMeasure Ω) (1 : ℝ)) ≠ 0)
    (fAlpha : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (fAlphaEpsilon : ℝ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (h_tv_solution : IsTvRegularizedMinimizer C K g α fAlpha)
    (h_tv_unique : IsUniqueTvRegularizedMinimizer C K g α fAlpha)
    (h_epsilon_solution :
      ∀ ε : ℝ, 0 < ε →
        fAlphaEpsilon ε ∈ C ∧
          IsMinOn
            (regularizedLeastSquaresFunctional K g α
              (J_ε ε))
            C (fAlphaEpsilon ε)) :
    Filter.Tendsto fAlphaEpsilon (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds fAlpha) := by
  by_cases hFtop : tvRegularizedLeastSquaresFunctional K g α fAlpha = ⊤
  · -- In the top-valued case the feasible set is already the singleton `{fAlpha}`.
    have heq :
        fAlphaEpsilon =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] fun _ ↦ fAlpha := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact eq_tvSolution_of_mem_of_tvObjective_eq_top
        C K g α fAlpha h_tv_solution h_tv_unique hFtop (h_epsilon_solution ε hε).1
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  · -- Route correction: reduce convergence to the subsequence criterion and isolate compactness.
    refine Filter.tendsto_of_subseq_tendsto fun εs hεs ↦ ?_
    rcases huberApprox_seq_exactObjectiveGap
        C K g α hα fAlpha fAlphaEpsilon h_tv_solution h_epsilon_solution εs hεs with
      ⟨hδ, hgap⟩
    have hsmall :
        ∀ᶠ n in Filter.atTop,
          α * ((εs n / 2) * (domainMeasure Ω Set.univ).toReal) < 1 := by
      exact hδ.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 1))
    have hu :
        ∀ᶠ n in Filter.atTop,
          fAlphaEpsilon (εs n) ∈ C ∧
            tvRegularizedLeastSquaresFunctional K g α (fAlphaEpsilon (εs n)) ≤
              tvRegularizedLeastSquaresFunctional K g α fAlpha + 1 := by
      filter_upwards [hgap, hsmall] with n hnGap hnSmall
      refine ⟨hnGap.1, ?_⟩
      have herr :
          (((α * ((εs n / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) ≤ 1 := by
        exact_mod_cast le_of_lt hnSmall
      exact hnGap.2.trans <|
        by simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_left herr (tvRegularizedLeastSquaresFunctional K g α fAlpha)
    have hB :
        tvRegularizedLeastSquaresFunctional K g α fAlpha + 1 < ⊤ := by
      have hone : (1 : EReal) ≠ ⊤ := by
        intro h
        cases h
      exact EReal.add_lt_top hFtop hone
    have huMem : ∀ᶠ n in Filter.atTop, fAlphaEpsilon (εs n) ∈ C :=
      hgap.mono fun _ hn ↦ hn.1
    have hL1 :
        ∃ M : ℝ, ∀ᶠ n in Filter.atTop, ‖lpToL1 (fAlphaEpsilon (εs n))‖ ≤ M :=
      eventualLpToL1Bound_of_eventually_tvSublevel
        (Ω := Ω) (p := p) hΩ K g α hα hK_one
        (tvRegularizedLeastSquaresFunctional K g α fAlpha + 1) hB
        (fun n ↦ fAlphaEpsilon (εs n)) (hu.mono fun _ hn ↦ hn.2)
    rcases exactGapSequence_isBVBounded
        (Ω := Ω) (p := p) K g α hα
        (tvRegularizedLeastSquaresFunctional K g α fAlpha + 1) hB
        (fun n ↦ fAlphaEpsilon (εs n)) hL1
        (hu.mono fun _ hn ↦ hn.2) with
      ⟨N, hTail⟩
    rcases exactGapSequence_subseq_tendsto
        hd hΩ hp_lt C hC_closed K g α hα
        (tvRegularizedLeastSquaresFunctional K g α fAlpha + 1) hB
        (fun n ↦ fAlphaEpsilon (εs n)) ⟨N, hTail⟩ hu with
      ⟨x, ψ, _hxC, _hxB, hψ, hlim⟩
    have huMemSub : ∀ᶠ n in Filter.atTop, fAlphaEpsilon (εs (ψ n)) ∈ C :=
      hψ.tendsto_atTop.eventually huMem
    have hδSub :
        Filter.Tendsto
          (fun n ↦ α * ((εs (ψ n) / 2) * (domainMeasure Ω Set.univ).toReal))
          Filter.atTop
          (nhds 0) :=
      hδ.comp hψ.tendsto_atTop
    have hgapSub :
        ∀ᶠ n in Filter.atTop,
          tvRegularizedLeastSquaresFunctional K g α (fAlphaEpsilon (εs (ψ n))) ≤
            tvRegularizedLeastSquaresFunctional K g α fAlpha +
              (((α * ((εs (ψ n) / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) :=
      hψ.tendsto_atTop.eventually hgap |>.mono fun _ hn ↦ hn.2
    have hxEq :
        x = fAlpha :=
      eq_tvSolution_of_tendsto_of_eventually_exactObjectiveGap
        hp_lt C hC_closed K g α hα fAlpha h_tv_solution h_tv_unique
        (fun n ↦ fAlphaEpsilon (εs (ψ n))) hlim huMemSub
        (fun n ↦ α * ((εs (ψ n) / 2) * (domainMeasure Ω Set.univ).toReal)) hδSub hgapSub
    refine ⟨ψ, ?_⟩
    simpa [Function.comp_def, hxEq] using hlim

end VariationalRegularization
