/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.FixedPolytopes
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycleStrictification
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

namespace ADMM.EndpointBounds

open ConsensusADMM
open scoped MatrixOrder

/-- The original Gram realization supplies every hypothesis of strictification. -/
theorem criticalInput
    (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
    (factor : S.transpose * S = Period48.gramMatrix) :
    0 < criticalFactor ∧ criticalFactor < 2 ∧
      IsProjectionCycle criticalFactor (Period48.Realization.eta S)
        (Period48.Realization.nu S criticalFactor) ∧
      (∃ i, ProjectionCycle.residual criticalFactor
          (Period48.Realization.nu S criticalFactor) i ≠ 0) ∧
      HasStrictBlock criticalFactor (Period48.Realization.eta S)
        (Period48.Realization.nu S criticalFactor) := by
  have hcycle := Period48.FixedPolytopes.isProjectionCycle S factor criticalFactor le_rfl
  obtain ⟨c, hc, hres⟩ :=
    Period48.FixedPolytopes.constantPositiveResidual S factor criticalFactor le_rfl
  have hn : ∃ i, ProjectionCycle.residual criticalFactor
      (Period48.Realization.nu S criticalFactor) i ≠ 0 := by
    refine ⟨0, ?_⟩
    intro hz
    have hh := hres 0
    rw [hz, norm_zero] at hh
    linarith
  exact ⟨criticalFactor_pos, by rw [criticalFactor_eq]; norm_num, hcycle, hn,
    Or.inr (Period48.FixedPolytopes.secondSupports_strict S factor)⟩

/-- The valid initial prefixes are bounded, and strictification gives the strict
upper endpoint estimate independently of any convergence lower estimate. -/
theorem prefix_bounded_and_endpoint_lt :
    BddAbove {c : ℝ | 0 < c ∧ ∀ t, 0 < t → t < c → UniformConvergenceAt t} ∧
      uniformConvergenceEndpoint < criticalFactor := by
  classical
  obtain ⟨S, hS⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := Period48.gramMatrix)).mp
    Period48.FixedPolytopes.gramMatrix_posDef.posSemidef.nonneg
  have factor : S.transpose * S = Period48.gramMatrix := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hS.symm
  obtain ⟨hpos, htwo, hcycle, hn, hs⟩ := criticalInput S factor
  constructor
  · obtain ⟨d, _, eta, nu, hstrict, hn', _⟩ :=
      ConsensusADMM.IsProjectionCycle.strictifyOneBlock criticalFactor
        (Period48.Realization.eta S) (Period48.Realization.nu S criticalFactor)
        (by norm_num) hpos htwo hcycle hn hs
    have hfail := ConsensusADMM.IsProjectionCycle.not_uniformConvergenceAt criticalFactor
      eta nu (by norm_num) hpos hstrict.isProjectionCycle hn'
    refine ⟨criticalFactor, ?_⟩
    intro c hc
    by_contra h
    exact hfail (hc.2 criticalFactor hpos (lt_of_not_ge h))
  · exact ConsensusADMM.IsProjectionCycle.uniformConvergenceEndpoint_lt criticalFactor
      (Period48.Realization.eta S) (Period48.Realization.nu S criticalFactor)
      (by norm_num) hpos htwo hcycle hn hs

end ADMM.EndpointBounds
