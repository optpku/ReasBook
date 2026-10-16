module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycle

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM

universe u

namespace ProjectionCycle

/-- Strict support against the origin and every phase vertex other than `p i`. -/
def StrictNonselfSupports {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p n : ZMod N → E) : Prop :=
  ∀ i, 0 < inner ℝ (n i) (p i) ∧
    ∀ j, j ≠ i → 0 < inner ℝ (n i) (p i - p j)

/-- Strict nonself support is exactly strict support against zero and each distinct phase. -/
theorem strictNonselfSupports_iff {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p n : ZMod N → E} :
    StrictNonselfSupports p n ↔
      ∀ i, 0 < inner ℝ (n i) (p i) ∧
        ∀ j, j ≠ i → 0 < inner ℝ (n i) (p i - p j) := by
  -- Expose the origin and distinct-phase inequalities in the definition.
  rfl

/-- Orthogonal cyclic symmetry advances both cycle families by one phase. -/
def HasOrthogonalCyclicSymmetry {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (η ν : ZMod N → E) : Prop :=
  ∃ U : E ≃ₗᵢ[ℝ] E, ∀ i, U (η i) = η (i + 1) ∧ U (ν i) = ν (i + 1)

/-- Orthogonal cyclic symmetry is witnessed by one isometry advancing both families. -/
theorem hasOrthogonalCyclicSymmetry_iff {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {η ν : ZMod N → E} :
    HasOrthogonalCyclicSymmetry η ν ↔
      ∃ U : E ≃ₗᵢ[ℝ] E, ∀ i, U (η i) = η (i + 1) ∧ U (ν i) = ν (i + 1) := by
  -- Expose the isometry witnessing cyclic symmetry.
  rfl

end ProjectionCycle

/-- At least one of the two projection-cycle blocks has all nonself supports strict. -/
def HasStrictBlock {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) : Prop :=
  ProjectionCycle.StrictNonselfSupports (ProjectionCycle.xVertex γ η ν)
      (ProjectionCycle.firstNormal γ η ν) ∨
    ProjectionCycle.StrictNonselfSupports η (ProjectionCycle.secondNormal γ ν)

/-- Having a strict block is the disjunction of strict first- and second-block support. -/
theorem hasStrictBlock_iff {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {γ : ℝ} {η ν : ZMod N → E} :
    HasStrictBlock γ η ν ↔
      ProjectionCycle.StrictNonselfSupports (ProjectionCycle.xVertex γ η ν)
          (ProjectionCycle.firstNormal γ η ν) ∨
        ProjectionCycle.StrictNonselfSupports η (ProjectionCycle.secondNormal γ ν) := by
  -- Expose the choice of a strict support block.
  rfl

/-- A strict projection cycle has strict nonself supports in both blocks. -/
def IsStrictProjectionCycle {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) : Prop :=
  ProjectionCycle.StrictNonselfSupports (ProjectionCycle.xVertex γ η ν)
      (ProjectionCycle.firstNormal γ η ν) ∧
    ProjectionCycle.StrictNonselfSupports η (ProjectionCycle.secondNormal γ ν)

/-- A strict projection cycle is exactly the pair of strict support families. -/
theorem isStrictProjectionCycle_iff {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {γ : ℝ} {η ν : ZMod N → E} :
    IsStrictProjectionCycle γ η ν ↔
      ProjectionCycle.StrictNonselfSupports (ProjectionCycle.xVertex γ η ν)
          (ProjectionCycle.firstNormal γ η ν) ∧
        ProjectionCycle.StrictNonselfSupports η (ProjectionCycle.secondNormal γ ν) := by
  -- Expose the two strict support families.
  rfl

namespace IsStrictProjectionCycle

/-- Forgetting strictness turns a strict projection cycle into a projection cycle. -/
theorem isProjectionCycle {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {γ : ℝ} {η ν : ZMod N → E}
    (hcycle : IsStrictProjectionCycle γ η ν) : IsProjectionCycle γ η ν := by
  -- Each strict support inequality implies the corresponding non-strict one.
  rcases isStrictProjectionCycle_iff.mp hcycle with ⟨hfirst, hsecond⟩
  apply isProjectionCycle_iff.mpr
  constructor
  · show ProjectionCycle.NonselfSupports (ProjectionCycle.xVertex γ η ν)
      (ProjectionCycle.firstNormal γ η ν)
    intro i
    exact ⟨(hfirst i).1.le, fun j hj ↦ ((hfirst i).2 j hj).le⟩
  · show ProjectionCycle.NonselfSupports η (ProjectionCycle.secondNormal γ ν)
    intro i
    exact ⟨(hsecond i).1.le, fun j hj ↦ ((hsecond i).2 j hj).le⟩

end IsStrictProjectionCycle

end ConsensusADMM
