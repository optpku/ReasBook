module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.FiniteObjectivesAndGrowth
public import glowinski_admm_counterexample.GlowinskiADMM.lemma_5_1_4_Objectives

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM

/-- The orientation of the second consensus block is the first-block
orientation with the multiplier negated. -/
theorem FiniteObjectivesAndGrowth.ObjectiveData.hasUniqueBlockMinimizers
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f g : E → ℝ}
    (hf : FiniteObjectivesAndGrowth.ObjectiveData f)
    (hg : FiniteObjectivesAndGrowth.ObjectiveData g) :
    HasUniqueBlockMinimizers (ofReal f) (ofReal g) := by
  refine ⟨hf.uniqueMinimizers, ?_⟩
  intro center dual
  have h := hg.uniqueMinimizers center (-dual)
  have identity (z : E) :
      inner ℝ (-dual) (z - center) + ‖z - center‖ ^ 2 / 2 =
        inner ℝ dual (center - z) + ‖center - z‖ ^ 2 / 2 := by
    rw [show z - center = -(center - z) by abel,
      inner_neg_left, inner_neg_right, norm_neg, neg_neg]
  simpa only [identity] using h

namespace IsStrictProjectionCycle

open ProjectionCycle

/-- The paper's proposition `prop:finite`, including both fixed objective pairs:
the original periodic cycle and the perturbed phase rays with geometric growth.
Each pair has unique finite block minimizers at every input, a zero-valued
origin KKT triple, and the origin as a primal optimum. -/
theorem finiteObjectivesAndGrowth {N d : ℕ} (γ : ℝ)
    (η ν : ZMod N → EuclideanSpace ℝ (Fin d)) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hcycle : IsStrictProjectionCycle γ η ν)
    (hnonzero : ∃ i, residual γ ν i ≠ 0)
    (hsym : HasOrthogonalCyclicSymmetry η ν) :
    (∃ f g : EuclideanSpace ℝ (Fin d) → ℝ,
      IsFiniteClosedConvexPiecewiseQuadratic f ∧
      IsFiniteClosedConvexPiecewiseQuadratic g ∧ Continuous f ∧ Continuous g ∧
      HasUniqueBlockMinimizers (ofReal f) (ofReal g) ∧
      IsTrajectory γ (ofReal f) (ofReal g) (xSequence γ η ν) (ySequence η)
        (dualSequence ν) ∧
      HasUniqueUpdates (ofReal f) (ofReal g) (xSequence γ η ν) (ySequence η)
        (dualSequence ν) ∧
      (∃ p : ℕ, 0 < p ∧ p ∣ N ∧
        HasExactPeriod p (xSequence γ η ν) (ySequence η) (dualSequence ν)) ∧
      (∃ c : ℝ, 0 < c ∧
        ∀ k, f (xSequence γ η ν (k + 1)) + g (ySequence η (k + 1)) = c) ∧
      IsKKT (ofReal f) (ofReal g) 0 0 0 ∧
      IsPrimalMinimizer (ofReal f) (ofReal g) 0 ∧ f 0 + g 0 = 0) ∧
    (∃ f g : EuclideanSpace ℝ (Fin d) → ℝ, ∃ κ c_r c_f : ℝ,
      IsFiniteClosedConvexPiecewiseQuadratic f ∧
      IsFiniteClosedConvexPiecewiseQuadratic g ∧ Continuous f ∧ Continuous g ∧
      HasUniqueBlockMinimizers (ofReal f) (ofReal g) ∧ 1 < κ ∧ 0 < c_r ∧ 0 < c_f ∧
      IsTrajectory γ (ofReal f) (ofReal g)
        (GeometricGrowth.sequence κ (GeometricGrowth.vertex γ κ η ν))
        (GeometricGrowth.sequence κ η) (GeometricGrowth.sequence κ ν) ∧
      HasUniqueUpdates (ofReal f) (ofReal g)
        (GeometricGrowth.sequence κ (GeometricGrowth.vertex γ κ η ν))
        (GeometricGrowth.sequence κ η) (GeometricGrowth.sequence κ ν) ∧
      (GeometricGrowth.sequence κ η 0, GeometricGrowth.sequence κ ν 0) =
        (κ⁻¹ • η (-1), κ⁻¹ • ν (-1)) ∧
      (∀ k,
        (GeometricGrowth.sequence κ (GeometricGrowth.vertex γ κ η ν) (k + 1),
          GeometricGrowth.sequence κ η (k + 1), GeometricGrowth.sequence κ ν (k + 1)) =
        (κ ^ k • GeometricGrowth.vertex γ κ η ν (k : ZMod N),
          κ ^ k • η (k : ZMod N), κ ^ k • ν (k : ZMod N))) ∧
      (∀ k, ‖GeometricGrowth.sequence κ (GeometricGrowth.vertex γ κ η ν) (k + 1) -
        GeometricGrowth.sequence κ η (k + 1)‖ = c_r * κ ^ k) ∧
      (∀ k, f (GeometricGrowth.sequence κ (GeometricGrowth.vertex γ κ η ν) (k + 1)) +
        g (GeometricGrowth.sequence κ η (k + 1)) = c_f * κ ^ (2 * k)) ∧
      IsKKT (ofReal f) (ofReal g) 0 0 0 ∧
      IsPrimalMinimizer (ofReal f) (ofReal g) 0 ∧ f 0 + g 0 = 0) := by
  letI : NeZero N := ⟨by omega⟩
  constructor
  · obtain ⟨f, g, hf, hg, htrajectory, hunique, hperiod, hvalue, hkkt, hprimal, hzero⟩ :=
      FiniteObjectivesAndGrowth.periodic γ η ν hN hγ hcycle hsym
    exact ⟨f, g, hf.piecewiseQuadratic, hg.piecewiseQuadratic, hf.continuous, hg.continuous,
      hf.hasUniqueBlockMinimizers hg, htrajectory, hunique, hperiod, hvalue, hkkt,
      hprimal, hzero⟩
  · obtain ⟨f, g, κ, c_r, c_f, hf, hg, hκ, hcr, hcf, htrajectory, hunique,
        hresidual, hvalue, hkkt, hprimal, hzero⟩ :=
      FiniteObjectivesAndGrowth.growth γ η ν hγ hcycle hnonzero hsym
    refine ⟨f, g, κ, c_r, c_f, hf.piecewiseQuadratic, hg.piecewiseQuadratic,
      hf.continuous, hg.continuous, hf.hasUniqueBlockMinimizers hg, hκ, hcr, hcf,
      htrajectory, hunique, ?_, ?_, hresidual, hvalue, hkkt, hprimal, hzero⟩
    · simp [GeometricGrowth.sequence]
    · intro k
      simp only [GeometricGrowth.sequence_succ (zero_lt_one.trans hκ).ne']

end IsStrictProjectionCycle
end ConsensusADMM
