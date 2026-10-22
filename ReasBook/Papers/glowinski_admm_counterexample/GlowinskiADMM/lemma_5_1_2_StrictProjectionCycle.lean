/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.StrictProjectionCycle

@[expose] public section

open scoped RealInnerProductSpace

universe u

/- Compatibility checks for the shared strict projection-cycle API. -/
#check (ConsensusADMM.ProjectionCycle.StrictNonselfSupports :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    (ZMod N → E) → (ZMod N → E) → Prop)

#check (ConsensusADMM.ProjectionCycle.strictNonselfSupports_iff :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {p n : ZMod N → E},
    ConsensusADMM.ProjectionCycle.StrictNonselfSupports p n ↔
      ∀ i, 0 < inner ℝ (n i) (p i) ∧
        ∀ j, j ≠ i → 0 < inner ℝ (n i) (p i - p j))

#check (ConsensusADMM.ProjectionCycle.HasOrthogonalCyclicSymmetry :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    (ZMod N → E) → (ZMod N → E) → Prop)

#check (ConsensusADMM.ProjectionCycle.hasOrthogonalCyclicSymmetry_iff :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {η ν : ZMod N → E},
    ConsensusADMM.ProjectionCycle.HasOrthogonalCyclicSymmetry η ν ↔
      ∃ U : E ≃ₗᵢ[ℝ] E, ∀ i, U (η i) = η (i + 1) ∧ U (ν i) = ν (i + 1))

#check (ConsensusADMM.HasStrictBlock :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ℝ → (ZMod N → E) → (ZMod N → E) → Prop)

#check (ConsensusADMM.hasStrictBlock_iff :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {γ : ℝ} {η ν : ZMod N → E},
    ConsensusADMM.HasStrictBlock γ η ν ↔
      ConsensusADMM.ProjectionCycle.StrictNonselfSupports
          (ConsensusADMM.ProjectionCycle.xVertex γ η ν)
          (ConsensusADMM.ProjectionCycle.firstNormal γ η ν) ∨
        ConsensusADMM.ProjectionCycle.StrictNonselfSupports η
          (ConsensusADMM.ProjectionCycle.secondNormal γ ν))

#check (ConsensusADMM.IsStrictProjectionCycle :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ℝ → (ZMod N → E) → (ZMod N → E) → Prop)

#check (ConsensusADMM.isStrictProjectionCycle_iff :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {γ : ℝ} {η ν : ZMod N → E},
    ConsensusADMM.IsStrictProjectionCycle γ η ν ↔
      ConsensusADMM.ProjectionCycle.StrictNonselfSupports
          (ConsensusADMM.ProjectionCycle.xVertex γ η ν)
          (ConsensusADMM.ProjectionCycle.firstNormal γ η ν) ∧
        ConsensusADMM.ProjectionCycle.StrictNonselfSupports η
          (ConsensusADMM.ProjectionCycle.secondNormal γ ν))

#check (ConsensusADMM.IsStrictProjectionCycle.isProjectionCycle :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {γ : ℝ} {η ν : ZMod N → E},
    ConsensusADMM.IsStrictProjectionCycle γ η ν →
      ConsensusADMM.IsProjectionCycle γ η ν)
