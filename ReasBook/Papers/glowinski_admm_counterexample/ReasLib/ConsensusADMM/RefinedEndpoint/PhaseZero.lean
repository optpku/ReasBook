/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.SupportedObjectives
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycleStrictification

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM.RefinedEndpoint

universe u

variable {N : ℕ} [NeZero N] {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `N` strict comparisons at phase zero: the origin and each nonzero
cyclic displacement. Appendix C.3 verifies these for each of the two blocks. -/
def ZeroPhaseStrictSupports (p n : ZMod N → E) : Prop :=
  0 < inner ℝ (n 0) (p 0) ∧
    ∀ j, j ≠ 0 → 0 < inner ℝ (n 0) (p 0 - p j)

/-- An orthogonal phase shift preserves a support product at any fixed
cyclic displacement, including displacements crossing phase zero. -/
theorem inner_displacement_eq_zeroPhase (p n : ZMod N → E)
    (symmetry : ProjectionCycle.HasOrthogonalCyclicSymmetry p n)
    (i j : ZMod N) :
    inner ℝ (n i) (p i - p (i + j)) =
      inner ℝ (n 0) (p 0 - p j) := by
  obtain ⟨U, advance⟩ := symmetry
  let f : ZMod N → ℝ := fun k ↦ inner ℝ (n k) (p k - p (k + j))
  have hstep (k : ZMod N) : f (k + 1) = f k := by
    dsimp only [f]
    rw [← (advance k).2, ← (advance k).1,
      show k + 1 + j = (k + j) + 1 by abel,
      ← (advance (k + j)).1, ← U.map_sub, U.inner_map_map]
  simpa only [f, zero_add] using
    ProjectionCycle.cyclic_statistic_constant f hstep i 0

/-- Under orthogonal cyclic symmetry, `N` strict phase-zero comparisons
are equivalent to all `N²` strict nonself support comparisons. -/
theorem strictNonselfSupports_iff_zeroPhase (p n : ZMod N → E)
    (symmetry : ProjectionCycle.HasOrthogonalCyclicSymmetry p n) :
    ProjectionCycle.StrictNonselfSupports p n ↔ ZeroPhaseStrictSupports p n := by
  constructor
  · intro supports
    exact supports 0
  · intro supports i
    obtain ⟨U, advance⟩ := symmetry
    refine ⟨?_, fun j hji ↦ ?_⟩
    · rw [cyclicInner_eq_zeroPhase p n U advance i]
      exact supports.1
    · have hdiff : j - i ≠ 0 := sub_ne_zero.mpr hji
      have h := inner_displacement_eq_zeroPhase p n ⟨U, advance⟩ i (j - i)
      rw [show i + (j - i) = j by abel] at h
      rw [h]
      exact supports.2 (j - i) hdiff

/-- Both derived vertex-normal pairs inherit the common orthogonal phase
shift, so the two phase-zero support lists certify a strict projection cycle. -/
theorem strictProjectionCycle_of_zeroPhase (γ : ℝ) (η ν : ZMod N → E)
    (symmetry : ProjectionCycle.HasOrthogonalCyclicSymmetry η ν)
    (hfirst : ZeroPhaseStrictSupports (ProjectionCycle.xVertex γ η ν)
      (ProjectionCycle.firstNormal γ η ν))
    (hsecond : ZeroPhaseStrictSupports η (ProjectionCycle.secondNormal γ ν)) :
    IsStrictProjectionCycle γ η ν := by
  obtain ⟨hsymFirst, hsymSecond⟩ :=
    projectionCycleSupportFamilies_hasOrthogonalCyclicSymmetry γ η ν symmetry
  exact ⟨(strictNonselfSupports_iff_zeroPhase _ _ hsymFirst).2 hfirst,
    (strictNonselfSupports_iff_zeroPhase _ _ hsymSecond).2 hsecond⟩

/-- Positive residual square at one phase suffices to refute convergence;
no assertion about the minimal period is needed for this endpoint bound. -/
theorem endpoint_lt_of_zeroPhase (γ : ℝ) (η ν : ZMod N → E)
    (hN : 2 ≤ N) (hγ : 0 < γ) (hγtwo : γ < 2)
    (symmetry : ProjectionCycle.HasOrthogonalCyclicSymmetry η ν)
    (hfirst : ZeroPhaseStrictSupports (ProjectionCycle.xVertex γ η ν)
      (ProjectionCycle.firstNormal γ η ν))
    (hsecond : ZeroPhaseStrictSupports η (ProjectionCycle.secondNormal γ ν))
    (hresidual : 0 < ‖ProjectionCycle.residual γ ν 0‖ ^ 2) :
    ADMM.uniformConvergenceEndpoint < γ := by
  have hcycle := strictProjectionCycle_of_zeroPhase γ η ν symmetry hfirst hsecond
  have hnonzero : ∃ i, ProjectionCycle.residual γ ν i ≠ 0 := by
    refine ⟨0, ?_⟩
    intro hzero
    simp [hzero] at hresidual
  exact IsProjectionCycle.uniformConvergenceEndpoint_lt γ η ν hN hγ hγtwo
    hcycle.isProjectionCycle hnonzero (Or.inl hcycle.1)

end ConsensusADMM.RefinedEndpoint
