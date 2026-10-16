module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycle

@[expose] public section

universe u

/- The compatibility surface for finite cyclic ADMM configurations. -/
#check (ConsensusADMM.CycleConfig :
  (N : ℕ) → (E : Type u) → [AddCommGroup E] → [Module ℝ E] → Type u)
