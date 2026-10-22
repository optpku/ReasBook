/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.lemma_5_1_2_StrictProjectionCycle
public import glowinski_admm_counterexample.GlowinskiADMM.lemma_5_1_4_Objectives
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.SmoothRealization

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM.IsStrictProjectionCycle

open ConsensusADMM ProjectionCycle

/-- Lemma 5.1.4: strict finite projection-cycle data with a nonzero residual admit
smooth strongly convex objectives whose unit-penalty consensus ADMM trajectory is the
prescribed cycle with its exact minimal period, positive constant trajectory value,
globally unique block minimizers, unique KKT triple `(0, 0, 0)`, and optimal value zero. -/
theorem smoothStronglyConvexRealization {N d : ℕ} (γ : ℝ)
    (η ν : ZMod N → EuclideanSpace ℝ (Fin d)) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hcycle : ConsensusADMM.IsStrictProjectionCycle γ η ν)
    (hnonzero : ∃ i, residual γ ν i ≠ 0) :
    ∃ f g : EuclideanSpace ℝ (Fin d) → ℝ,
      IsSmoothStronglyConvex f ∧ IsSmoothStronglyConvex g ∧
      IsTrajectory γ (ofReal f) (ofReal g) (xSequence γ η ν) (ySequence η)
        (dualSequence ν) ∧
      HasUniqueBlockMinimizers (ofReal f) (ofReal g) ∧
      (∃ p : ℕ, 0 < p ∧ p ∣ N ∧
        HasExactPeriod p (xSequence γ η ν) (ySequence η) (dualSequence ν)) ∧
      (∃ c : ℝ, 0 < c ∧
        ∀ k, f (xSequence γ η ν (k + 1)) + g (ySequence η (k + 1)) = c) ∧
      IsUniqueKKT (ofReal f) (ofReal g) 0 0 0 ∧
      IsPrimalMinimizer (ofReal f) (ofReal g) 0 ∧ f 0 + g 0 = 0 := by
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨f, ⟨hf⟩⟩ := SmoothRealization.exists_interpolates
    (xVertex γ η ν) (firstNormal γ η ν) hcycle.1
  obtain ⟨g, ⟨hg⟩⟩ := SmoothRealization.exists_interpolates
    η (secondNormal γ ν) hcycle.2
  have htrajectory := (ofRealSupportedCycle_updates γ η ν f g hγ hf.supports hg.supports).1
  have hblocks : HasUniqueBlockMinimizers (ofReal f) (ofReal g) := by
    constructor
    · intro center dual
      exact SmoothRealization.exists_unique_augmented_ofReal f hf.modulus hf.modulus_pos
        hf.contDiff.continuous hf.stronglyConvex hf.zero hf.lower center dual
    · intro center dual
      have h := SmoothRealization.exists_unique_augmented_ofReal g hg.modulus hg.modulus_pos
        hg.contDiff.continuous hg.stronglyConvex hg.zero hg.lower center (-dual)
      have identity (z : EuclideanSpace ℝ (Fin d)) :
          inner ℝ (-dual) (z - center) + ‖z - center‖ ^ 2 / 2 =
            inner ℝ dual (center - z) + ‖center - z‖ ^ 2 / 2 := by
        rw [show z - center = -(center - z) by abel,
          inner_neg_left, inner_neg_right, norm_neg, neg_neg]
      simpa only [identity] using h
  have hf_nonneg (z : EuclideanSpace ℝ (Fin d)) : 0 ≤ f z :=
    (mul_nonneg (half_pos hf.modulus_pos).le (sq_nonneg _)).trans (hf.lower z)
  have hg_nonneg (z : EuclideanSpace ℝ (Fin d)) : 0 ≤ g z :=
    (mul_nonneg (half_pos hg.modulus_pos).le (sq_nonneg _)).trans (hg.lower z)
  obtain ⟨hkkt, _, hprimal⟩ := ofRealOriginOptimality f g hf.zero hg.zero hf_nonneg hg_nonneg
  have huniquekkt : IsUniqueKKT (ofReal f) (ofReal g) 0 0 0 := by
    refine ⟨hkkt, ?_⟩
    intro x y dual hother
    have hxy : x = y := hother.1
    have hfirst : f x + inner ℝ (-dual) (-x) ≤ 0 := by
      simpa only [ofReal_apply, hf.zero, zero_sub, ← EReal.coe_add,
        ← EReal.coe_zero, EReal.coe_le_coe_iff] using hother.2.1 0
    have hsecond : g x + inner ℝ dual (-x) ≤ 0 := by
      simpa only [ofReal_apply, hg.zero, ← hxy, zero_sub, ← EReal.coe_add,
        ← EReal.coe_zero, EReal.coe_le_coe_iff] using hother.2.2 0
    have hsum : f x + g x ≤ 0 := by
      simp only [inner_neg_left] at hfirst
      linarith
    have hxnorm : ‖x‖ ^ 2 = 0 := by
      have hmu := hf.modulus_pos
      nlinarith [hf.lower x, hg_nonneg x, sq_nonneg ‖x‖]
    have hx : x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hxnorm)
    have hy : y = 0 := hxy.symm.trans hx
    have hdual : -dual = 0 := SmoothRealization.supporting_normal_at_origin_eq_zero
      hf.derivative_zero (by
        intro z
        simpa only [ofReal_apply, hx, sub_zero, ← EReal.coe_add,
          EReal.coe_le_coe_iff] using hother.2.1 z)
    exact ⟨hx, hy, neg_eq_zero.mp hdual⟩
  refine ⟨f, g, ⟨hf.modulus, hf.constant, hf.modulus_pos, hf.stronglyConvex,
    hf.contDiff, hf.lipschitz⟩, ⟨hg.modulus, hg.constant, hg.modulus_pos,
    hg.stronglyConvex, hg.contDiff, hg.lipschitz⟩, htrajectory, hblocks,
    IsProjectionCycle.minimalPeriod_dvd γ η ν hN hγ hcycle.isProjectionCycle,
    ⟨hf.level + hg.level, add_pos hf.level_pos hg.level_pos, ?_⟩,
    huniquekkt, hprimal, ?_⟩
  · intro k
    simp only [xSequence_succ, ySequence_succ, hf.values, hg.values]
  · rw [hf.zero, hg.zero, add_zero]

end ConsensusADMM.IsStrictProjectionCycle
