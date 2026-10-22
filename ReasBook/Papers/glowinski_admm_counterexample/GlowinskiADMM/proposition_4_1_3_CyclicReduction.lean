/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.CyclicReduction

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM

universe u

namespace ProjectionCycle

#check (ConsensusADMM.ProjectionCycle.HasConstantPositiveResidual :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ℝ → (ZMod N → E) → Prop)

#check (ConsensusADMM.ProjectionCycle.hasConstantPositiveResidual_iff :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {γ : ℝ} {ν : ZMod N → E},
    ConsensusADMM.ProjectionCycle.HasConstantPositiveResidual γ ν ↔
      ∃ c : ℝ, 0 < c ∧ ∀ i, ‖ConsensusADMM.ProjectionCycle.residual γ ν i‖ = c)

#check (ConsensusADMM.ProjectionCycle.HasCirculantGram :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    (ZMod N → E) → (ZMod N → E) → Prop)

#check (ConsensusADMM.ProjectionCycle.hasCirculantGram_iff :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {η ν : ZMod N → E},
    ConsensusADMM.ProjectionCycle.HasCirculantGram η ν ↔
      (∀ i j, inner ℝ (η (i + 1)) (η (j + 1)) = inner ℝ (η i) (η j)) ∧
        (∀ i j, inner ℝ (η (i + 1)) (ν (j + 1)) = inner ℝ (η i) (ν j)) ∧
        ∀ i j, inner ℝ (ν (i + 1)) (ν (j + 1)) = inner ℝ (ν i) (ν j))

end ProjectionCycle

#check (ConsensusADMM.IsCyclicReduction :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ℝ → (ZMod N → E) → (ZMod N → E) → Prop)

#check (ConsensusADMM.isCyclicReduction_iff :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {γ : ℝ} {η ν : ZMod N → E},
    ConsensusADMM.IsCyclicReduction γ η ν ↔
      ConsensusADMM.IsProjectionCycle γ η ν ∧
        ConsensusADMM.ProjectionCycle.HasConstantPositiveResidual γ ν ∧
        ConsensusADMM.ProjectionCycle.HasCirculantGram η ν)

end ConsensusADMM
