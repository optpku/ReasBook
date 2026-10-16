module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.GeometricGrowth
public import glowinski_admm_counterexample.ReasLib.Convex.SmoothInterpolation.Conjugate
public import Mathlib.Analysis.Convex.Continuous

@[expose] public section

open Set
open scoped RealInnerProductSpace

namespace ConsensusADMM.FiniteObjectivesAndGrowth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- Every augmented block problem has a unique finite minimizer, for all
centers and multipliers, rather than only along one prescribed trajectory. -/
def UniqueAugmentedMinimizers (f : E → ℝ) : Prop :=
  ∀ center dual, ∃! p, ofReal f p ≠ ⊤ ∧ ofReal f p ≠ ⊥ ∧ ∀ z,
    ofReal f p + ((inner ℝ dual (p - center) + ‖p - center‖ ^ 2 / 2 : ℝ) : EReal) ≤
      ofReal f z + ((inner ℝ dual (z - center) + ‖z - center‖ ^ 2 / 2 : ℝ) : EReal)

/-- A finite convex objective minimized at zero has uniquely solvable
unit-penalty block problems. Quadratic regularization supplies coercivity. -/
theorem uniqueAugmented_of_nonnegative (f : E → ℝ) (hc : Continuous f)
    (hf : ConvexOn ℝ univ f) (h0 : f 0 = 0) (hpos : ∀ x, 0 ≤ f x) :
    UniqueAugmentedMinimizers f := by
  intro center dual
  let H : E → ℝ := fun x ↦ f x + ‖x‖ ^ 2 / 2
  have hH : SmoothInterpolation.QuadraticCore H 1 := by
    refine ⟨by norm_num, hc.add ((continuous_norm.pow 2).div_const 2), ?_, ?_, ?_⟩
    · rw [strongConvexOn_iff_convex]
      convert hf using 1
      ext x
      dsimp [H]
      ring
    · simp [H, h0]
    · intro x
      dsimp [H]
      linarith [hpos x]
  obtain ⟨p, hp⟩ := hH.exists_minimizer (center - dual)
  have identity (x : E) :
      f x + (inner ℝ dual (x - center) + ‖x - center‖ ^ 2 / 2) =
        H x - inner ℝ (center - dual) x +
          (‖center‖ ^ 2 / 2 - inner ℝ dual center) := by
    dsimp [H]
    rw [inner_sub_right, inner_sub_left, norm_sub_sq_real, real_inner_comm x center]
    ring
  refine ⟨p, ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _, ?_⟩, ?_⟩
  · intro z
    simp only [ofReal_apply, ← EReal.coe_add, EReal.coe_le_coe_iff, identity]
    linarith [hp z]
  · intro z hz
    have hzp : H z - inner ℝ (center - dual) z ≤ H p - inner ℝ (center - dual) p := by
      simpa only [ofReal_apply, ← EReal.coe_add, EReal.coe_le_coe_iff,
        identity, add_le_add_iff_right] using hz.2.2 p
    have hb := SmoothInterpolation.strong_minimum_bound
      (hH.tilt_stronglyConvex (center - dual)) hp z
    have hn : ‖z - p‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z - p‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

/-- All global properties of either max-square objective used in the paper. -/
structure ObjectiveData (f : E → ℝ) : Prop where
  piecewiseQuadratic : IsFiniteClosedConvexPiecewiseQuadratic f
  continuous : Continuous f
  zero : f 0 = 0
  nonnegative : ∀ x, 0 ≤ f x
  uniqueMinimizers : UniqueAugmentedMinimizers f

/-- The existing finite max-square certificate also certifies continuity and
global solvability of every augmented block problem. -/
theorem objectiveData_of_nonnegative (f : E → ℝ)
    (hf : IsFiniteClosedConvexPiecewiseQuadratic f) (h0 : f 0 = 0)
    (hpos : ∀ x, 0 ≤ f x) : ObjectiveData f := by
  have hc : Continuous f := continuousOn_univ.mp (hf.1.continuousOn isOpen_univ)
  exact ⟨hf, hc, h0, hpos, uniqueAugmented_of_nonnegative f hc hf.1 h0 hpos⟩

variable {N : ℕ} [NeZero N]

/-- The periodic half of the finite-objectives proposition preserves the
prescribed trajectory and its positive minimal period. -/
theorem periodic (γ : ℝ) (η ν : ZMod N → E) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hstrict : IsStrictProjectionCycle γ η ν)
    (hsym : ProjectionCycle.HasOrthogonalCyclicSymmetry η ν) :
    ∃ f g : E → ℝ, ObjectiveData f ∧ ObjectiveData g ∧
      IsTrajectory γ (ofReal f) (ofReal g) (ProjectionCycle.xSequence γ η ν)
        (ProjectionCycle.ySequence η) (ProjectionCycle.dualSequence ν) ∧
      HasUniqueUpdates (ofReal f) (ofReal g) (ProjectionCycle.xSequence γ η ν)
        (ProjectionCycle.ySequence η) (ProjectionCycle.dualSequence ν) ∧
      (∃ p : ℕ, 0 < p ∧ p ∣ N ∧ HasExactPeriod p (ProjectionCycle.xSequence γ η ν)
        (ProjectionCycle.ySequence η) (ProjectionCycle.dualSequence ν)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ k,
        f (ProjectionCycle.xSequence γ η ν (k + 1)) +
          g (ProjectionCycle.ySequence η (k + 1)) = c) ∧
      IsKKT (ofReal f) (ofReal g) 0 0 0 ∧
      IsPrimalMinimizer (ofReal f) (ofReal g) 0 ∧ f 0 + g 0 = 0 := by
  obtain ⟨hsymX, hsymY⟩ := projectionCycleSupportFamilies_hasOrthogonalCyclicSymmetry
    γ η ν hsym
  obtain ⟨αX, hαX, hselfX, hactiveX⟩ := cyclicSupport_activeForm
    (ProjectionCycle.xVertex γ η ν) (ProjectionCycle.firstNormal γ η ν) hstrict.1 hsymX
  obtain ⟨αY, hαY, hselfY, hactiveY⟩ := cyclicSupport_activeForm
    η (ProjectionCycle.secondNormal γ ν) hstrict.2 hsymY
  obtain ⟨f, hfpw, hf0, hfpos, hfray⟩ := maxSquareObjective_spec
    (ProjectionCycle.xVertex γ η ν) (ProjectionCycle.firstNormal γ η ν)
    αX hαX hselfX hactiveX
  obtain ⟨g, hgpw, hg0, hgpos, hgray⟩ := maxSquareObjective_spec
    η (ProjectionCycle.secondNormal γ ν) αY hαY hselfY hactiveY
  have hfsupport := fun i z ↦ (hfray 1 zero_le_one i).2 z
  have hgsupport := fun i z ↦ (hgray 1 zero_le_one i).2 z
  simp only [one_smul] at hfsupport hgsupport
  obtain ⟨htrajectory, hunique⟩ := ofRealSupportedCycle_updates γ η ν f g hγ hfsupport hgsupport
  obtain ⟨hkkt, _, hprimal⟩ := ofRealOriginOptimality f g hf0 hg0 hfpos hgpos
  refine ⟨f, g, objectiveData_of_nonnegative f hfpw hf0 hfpos,
    objectiveData_of_nonnegative g hgpw hg0 hgpos, htrajectory, hunique,
    IsProjectionCycle.minimalPeriod_dvd γ η ν hN hγ hstrict.isProjectionCycle,
    ⟨αX / 2 + αY / 2, by positivity, ?_⟩, hkkt, hprimal, by rw [hf0, hg0, add_zero]⟩
  intro k
  have hfval := (hfray 1 zero_le_one (k : ZMod N)).1
  have hgval := (hgray 1 zero_le_one (k : ZMod N)).1
  simpa only [one_smul, one_pow, one_mul, ProjectionCycle.xSequence_succ,
    ProjectionCycle.ySequence_succ] using congrArg₂ (· + ·) hfval hgval

open GeometricGrowth in
/-- The growing half uses a second fixed pair of finite objectives. Its exact
sequences retain the paper's phase rays and the scaled predecessor initialization. -/
theorem growth (γ : ℝ) (η ν : ZMod N → E) (hγ : 0 < γ)
    (hstrict : IsStrictProjectionCycle γ η ν)
    (hnonzero : ∃ i, ProjectionCycle.residual γ ν i ≠ 0)
    (hsym : ProjectionCycle.HasOrthogonalCyclicSymmetry η ν) :
    ∃ f g : E → ℝ, ∃ κ c_r c_f : ℝ,
      ObjectiveData f ∧ ObjectiveData g ∧ 1 < κ ∧ 0 < c_r ∧ 0 < c_f ∧
      IsTrajectory γ (ofReal f) (ofReal g)
        (sequence κ (vertex γ κ η ν)) (sequence κ η) (sequence κ ν) ∧
      HasUniqueUpdates (ofReal f) (ofReal g)
        (sequence κ (vertex γ κ η ν)) (sequence κ η) (sequence κ ν) ∧
      (∀ k, ‖sequence κ (vertex γ κ η ν) (k + 1) - sequence κ η (k + 1)‖ =
        c_r * κ ^ k) ∧
      (∀ k, f (sequence κ (vertex γ κ η ν) (k + 1)) +
        g (sequence κ η (k + 1)) = c_f * κ ^ (2 * k)) ∧
      IsKKT (ofReal f) (ofReal g) 0 0 0 ∧
      IsPrimalMinimizer (ofReal f) (ofReal g) 0 ∧ f 0 + g 0 = 0 := by
  obtain ⟨κ, hκ, hfirst, hsecond, i, hi⟩ := expanding_data γ η ν hstrict hnonzero
  have hκpos : 0 < κ := zero_lt_one.trans hκ
  obtain ⟨hsymX, hsymY, U, hU⟩ := symmetry γ κ η ν hsym
  have hnorm (j : ZMod N) : ‖residual γ κ ν j‖ = ‖residual γ κ ν 0‖ := by
    have h := cyclicInner_eq_zeroPhase (residual γ κ ν) (residual γ κ ν) U hU j
    simp only [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (residual γ κ ν j), norm_nonneg (residual γ κ ν 0)]
  have hrpos : 0 < ‖residual γ κ ν 0‖ := by
    rw [← hnorm i]
    exact norm_pos_iff.mpr hi
  obtain ⟨αX, hαX, hselfX, hactiveX⟩ := cyclicSupport_activeForm
    (vertex γ κ η ν) (firstNormal γ κ η ν) hfirst hsymX
  obtain ⟨αY, hαY, hselfY, hactiveY⟩ := cyclicSupport_activeForm
    η (secondNormal γ κ ν) hsecond hsymY
  obtain ⟨f, hfpw, hf0, hfpos, hfray⟩ := maxSquareObjective_spec
    (vertex γ κ η ν) (firstNormal γ κ η ν) αX hαX hselfX hactiveX
  obtain ⟨g, hgpw, hg0, hgpos, hgray⟩ := maxSquareObjective_spec
    η (secondNormal γ κ ν) αY hαY hselfY hactiveY
  obtain ⟨htrajectory, hunique⟩ := supported_updates γ κ η ν f g hγ hκpos
    (fun t ht i ↦ (hfray t ht i).2) (fun t ht i ↦ (hgray t ht i).2)
  obtain ⟨hkkt, hvalue, hprimal⟩ := ofRealOriginOptimality f g hf0 hg0 hfpos hgpos
  refine ⟨f, g, κ, ‖residual γ κ ν 0‖, αX / 2 + αY / 2,
    objectiveData_of_nonnegative f hfpw hf0 hfpos,
    objectiveData_of_nonnegative g hgpw hg0 hgpos, hκ, hrpos, by positivity,
    htrajectory, hunique, ?_, ?_, hkkt, hprimal, by rw [hf0, hg0, add_zero]⟩
  · intro k
    rw [sequence_succ hκpos.ne', sequence_succ hκpos.ne', ← smul_sub,
      vertex, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hκpos.le _), hnorm]
    exact mul_comm _ _
  · intro k
    rw [sequence_succ hκpos.ne', sequence_succ hκpos.ne',
      (hfray _ (pow_nonneg hκpos.le _) _).1, (hgray _ (pow_nonneg hκpos.le _) _).1]
    rw [Nat.mul_comm 2 k, pow_mul]
    ring

end ConsensusADMM.FiniteObjectivesAndGrowth
