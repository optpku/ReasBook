module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.CyclicReduction

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM

universe u

/- Proposition 4.1.3: an `N`-periodic consensus ADMM trajectory with a nonzero
residual admits a cyclic projection reduction in dimension at most `2 * N - 2`,
at the same multiplier factor. -/
#check (ConsensusADMM.existsCyclicReduction :
  ∀ {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (f g : E → EReal) (x y dual : ℕ → E)
    (hN : 2 ≤ N) (hγ : 0 < γ)
    (hf : ADMM.IsClosedProperConvex f) (hg : ADMM.IsClosedProperConvex g)
    (htrajectory : ConsensusADMM.IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (hnonzero : ∃ k, x (k + 1) - y (k + 1) ≠ 0),
    ∃ d : ℕ, d ≤ 2 * N - 2 ∧
      ∃ η ν : ZMod N → EuclideanSpace ℝ (Fin d),
        ConsensusADMM.IsCyclicReduction γ η ν)

end ConsensusADMM
