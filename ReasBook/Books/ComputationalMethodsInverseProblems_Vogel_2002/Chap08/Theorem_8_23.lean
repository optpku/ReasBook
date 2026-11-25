/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4_1.Approximation
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_14.BV
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_22.BVBounded
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_18.Comparison
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_19.Objective
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_20.Minimizer
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_16
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Poincare
import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_23.TVSublevel
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

/- The minimizer predicates are shared with Theorem 8.20; penalty envelopes
and finite-measure inclusion estimates are imported from Exercise 8.16 and
Theorem 8.18. Keeping one owner allows these chapter modules to be imported
together. -/

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

/-- Helper for Theorem 8.23: lifting an `L^p(Ω)` point to `BV(Ω)` and back through
`BVCompactness.toLp` recovers the original point. -/
lemma toLp_of_bvLift_eq
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal}
    [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    [HasBoundedBVExtension Ω]
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
    [HasBoundedBVExtension Ω]
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
with `1 ≤ p < d / (d - 1)`, `K 1 ≠ 0`, and the explicit mean-value
Poincaré inequality `HasLpTVPoincare Ω p`. If `fAlpha` is the unique corresponding
TV-regularized solution and `fAlphaBeta β` is the corresponding regularized solution after
replacing `TV` by `J_β β`, then `fAlphaBeta` converges to `fAlpha` in `L^p`
norm as `β → 0⁺` on bounded `Ω` with `HasBoundedBVExtension Ω`. -/
theorem smoothNormApproxRegularizedSolutions_tendsto_tvSolution
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    [HasBoundedBVExtension Ω]
    (hp_lt : p < ((d : ENNReal) / ((d - 1 : ℕ) : ENNReal)))
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))) (hC_closed : IsClosed C)
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)) (α : ℝ) (hα : 0 < α)
    (hK_one : K (MeasureTheory.Lp.const p (domainMeasure Ω) (1 : ℝ)) ≠ 0)
    (h_poincare : HasLpTVPoincare Ω p)
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
        (Ω := Ω) (p := p) h_poincare K g α hα hK_one
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
with `1 ≤ p < d / (d - 1)`, `K 1 ≠ 0`, and the explicit mean-value
Poincaré inequality `HasLpTVPoincare Ω p`. If `fAlpha` is the unique corresponding
TV-regularized solution and `fAlphaEpsilon ε` is the corresponding regularized solution after
replacing `TV` by `J_ε ε`, then `fAlphaEpsilon` converges to `fAlpha` in `L^p`
norm as `ε → 0⁺` on bounded `Ω` with `HasBoundedBVExtension Ω`. -/
theorem huberApproxRegularizedSolutions_tendsto_tvSolution
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    [HasBoundedBVExtension Ω]
    (hp_lt : p < ((d : ENNReal) / ((d - 1 : ℕ) : ENNReal)))
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))) (hC_closed : IsClosed C)
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)) (α : ℝ) (hα : 0 < α)
    (hK_one : K (MeasureTheory.Lp.const p (domainMeasure Ω) (1 : ℝ)) ≠ 0)
    (h_poincare : HasLpTVPoincare Ω p)
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
        (Ω := Ω) (p := p) h_poincare K g α hα hK_one
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
