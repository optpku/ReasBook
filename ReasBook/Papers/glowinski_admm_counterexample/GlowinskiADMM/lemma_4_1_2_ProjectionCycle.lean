module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycle

@[expose] public section

open scoped RealInnerProductSpace

universe u

/- The ZMod-indexed projection-cycle compatibility surface is owned by
`ReasLib.Optimization.ADMM.ProjectionCycle`. -/

#check (ConsensusADMM.ProjectionCycle.residual :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E],
    ℝ → (ZMod N → E) → ZMod N → E)

#check (ConsensusADMM.ProjectionCycle.residual_apply :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
      (γ : ℝ) (ν : ZMod N → E) (i : ZMod N),
    ConsensusADMM.ProjectionCycle.residual γ ν i = γ⁻¹ • (ν i - ν (i - 1)))

#check (ConsensusADMM.ProjectionCycle.xVertex :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E],
    ℝ → (ZMod N → E) → (ZMod N → E) → ZMod N → E)

#check (ConsensusADMM.ProjectionCycle.xVertex_apply :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
      (γ : ℝ) (η ν : ZMod N → E) (i : ZMod N),
    ConsensusADMM.ProjectionCycle.xVertex γ η ν i =
      η i + ConsensusADMM.ProjectionCycle.residual γ ν i)

#check (ConsensusADMM.ProjectionCycle.firstNormal :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E],
    ℝ → (ZMod N → E) → (ZMod N → E) → ZMod N → E)

#check (ConsensusADMM.ProjectionCycle.firstNormal_apply :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
      (γ : ℝ) (η ν : ZMod N → E) (i : ZMod N),
    ConsensusADMM.ProjectionCycle.firstNormal γ η ν i =
      η (i - 1) - ν (i - 1) - ConsensusADMM.ProjectionCycle.xVertex γ η ν i)

#check (ConsensusADMM.ProjectionCycle.secondNormal :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E],
    ℝ → (ZMod N → E) → ZMod N → E)

#check (ConsensusADMM.ProjectionCycle.secondNormal_apply :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
      (γ : ℝ) (ν : ZMod N → E) (i : ZMod N),
    ConsensusADMM.ProjectionCycle.secondNormal γ ν i =
      ν (i - 1) + ConsensusADMM.ProjectionCycle.residual γ ν i)

#check (ConsensusADMM.ProjectionCycle.NonselfSupports :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    (ZMod N → E) → (ZMod N → E) → Prop)

#check (ConsensusADMM.ProjectionCycle.nonselfSupports_iff :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {p n : ZMod N → E},
    ConsensusADMM.ProjectionCycle.NonselfSupports p n ↔
      ∀ i, 0 ≤ inner ℝ (n i) (p i) ∧
        ∀ j, j ≠ i → 0 ≤ inner ℝ (n i) (p i - p j))

#check (ConsensusADMM.ProjectionCycle.xSet :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E],
    ℝ → (ZMod N → E) → (ZMod N → E) → Set E)

#check (ConsensusADMM.ProjectionCycle.xSet_def :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
      (γ : ℝ) (η ν : ZMod N → E),
    ConsensusADMM.ProjectionCycle.xSet γ η ν =
      convexHull ℝ (Set.insert 0 (Set.range (ConsensusADMM.ProjectionCycle.xVertex γ η ν))))

#check (ConsensusADMM.ProjectionCycle.ySet :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E],
    (ZMod N → E) → Set E)

#check (ConsensusADMM.ProjectionCycle.ySet_def :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E] (η : ZMod N → E),
    ConsensusADMM.ProjectionCycle.ySet η =
      convexHull ℝ (Set.insert 0 (Set.range η)))

#check (ConsensusADMM.ProjectionCycle.xSequence :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E],
    ℝ → (ZMod N → E) → (ZMod N → E) → ℕ → E)

#check (ConsensusADMM.ProjectionCycle.xSequence_apply :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
      (γ : ℝ) (η ν : ZMod N → E) (k : ℕ),
    ConsensusADMM.ProjectionCycle.xSequence γ η ν k =
      ConsensusADMM.ProjectionCycle.xVertex γ η ν ((k : ZMod N) - 1))

#check (ConsensusADMM.ProjectionCycle.xSequence_succ :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
      (γ : ℝ) (η ν : ZMod N → E) (k : ℕ),
    ConsensusADMM.ProjectionCycle.xSequence γ η ν (k + 1) =
      ConsensusADMM.ProjectionCycle.xVertex γ η ν (k : ZMod N))

#check (ConsensusADMM.ProjectionCycle.ySequence :
  ∀ {N : ℕ} {E : Type u}, (ZMod N → E) → ℕ → E)

#check (ConsensusADMM.ProjectionCycle.ySequence_apply :
  ∀ {N : ℕ} {E : Type u} (η : ZMod N → E) (k : ℕ),
    ConsensusADMM.ProjectionCycle.ySequence η k = η ((k : ZMod N) - 1))

#check (ConsensusADMM.ProjectionCycle.ySequence_zero :
  ∀ {N : ℕ} {E : Type u} (η : ZMod N → E),
    ConsensusADMM.ProjectionCycle.ySequence η 0 = η (-1))

#check (ConsensusADMM.ProjectionCycle.ySequence_succ :
  ∀ {N : ℕ} {E : Type u} (η : ZMod N → E) (k : ℕ),
    ConsensusADMM.ProjectionCycle.ySequence η (k + 1) = η (k : ZMod N))

#check (ConsensusADMM.ProjectionCycle.dualSequence :
  ∀ {N : ℕ} {E : Type u}, (ZMod N → E) → ℕ → E)

#check (ConsensusADMM.ProjectionCycle.dualSequence_apply :
  ∀ {N : ℕ} {E : Type u} (ν : ZMod N → E) (k : ℕ),
    ConsensusADMM.ProjectionCycle.dualSequence ν k = ν ((k : ZMod N) - 1))

#check (ConsensusADMM.ProjectionCycle.dualSequence_zero :
  ∀ {N : ℕ} {E : Type u} (ν : ZMod N → E),
    ConsensusADMM.ProjectionCycle.dualSequence ν 0 = ν (-1))

#check (ConsensusADMM.ProjectionCycle.dualSequence_succ :
  ∀ {N : ℕ} {E : Type u} (ν : ZMod N → E) (k : ℕ),
    ConsensusADMM.ProjectionCycle.dualSequence ν (k + 1) = ν (k : ZMod N))

#check (ConsensusADMM.ProjectionCycle.primalResidual :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E],
    ℝ → (ZMod N → E) → (ZMod N → E) → ℕ → E)

#check (ConsensusADMM.ProjectionCycle.primalResidual_apply :
  ∀ {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
      (γ : ℝ) (η ν : ZMod N → E) (k : ℕ),
    ConsensusADMM.ProjectionCycle.primalResidual γ η ν k =
      ConsensusADMM.ProjectionCycle.residual γ ν (k : ZMod N))

#check (ConsensusADMM.IsProjectionCycle :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ℝ → (ZMod N → E) → (ZMod N → E) → Prop)

#check (ConsensusADMM.isProjectionCycle_iff :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {γ : ℝ} {η ν : ZMod N → E},
    ConsensusADMM.IsProjectionCycle γ η ν ↔
      ConsensusADMM.ProjectionCycle.NonselfSupports
          (ConsensusADMM.ProjectionCycle.xVertex γ η ν)
          (ConsensusADMM.ProjectionCycle.firstNormal γ η ν) ∧
        ConsensusADMM.ProjectionCycle.NonselfSupports η
          (ConsensusADMM.ProjectionCycle.secondNormal γ ν))
