/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.J0
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness

@[expose] public section

/- Algorithm 9.1.2: for J₀ = 2K - I₉₆ with K the period-48 two-block integer
matrix, fraction-free elimination starts from B⁽⁰⁾ = J₀ and b₋₁ = 1, and for
k = 0,…,94 updates the trailing entries by
B⁽ᵏ⁺¹⁾ᵢⱼ = (b_k · B⁽ᵏ⁾ᵢⱼ - B⁽ᵏ⁾ᵢₖ · B⁽ᵏ⁾ₖⱼ) / b_{k-1} with b_k = B⁽ᵏ⁾ₖₖ,
where each division is exact in ℤ. The 96 leading principal determinants are
b_0,…,b_94, B⁽⁹⁵⁾₉₅,₉₅, each at least 1, so Sylvester's criterion gives J₀ ≻ 0. -/
#check (ConsensusADMM.Period48.j0 : Matrix (Fin 96) (Fin 96) ℤ)
#check ConsensusADMM.Period48.j0_apply
#check ConsensusADMM.Period48.j0_blocks
#check ConsensusADMM.Period48.j0_isSymm
#check ConsensusADMM.Period48.FractionFree.stage
#check ConsensusADMM.Period48.FractionFree.previousPivot
#check ConsensusADMM.Period48.FractionFree.pivot
#check ConsensusADMM.Period48.FractionFree.principal
#check ConsensusADMM.Period48.FractionFree.stage_zero
#check ConsensusADMM.Period48.FractionFree.stage_succ_apply
#check ConsensusADMM.Period48.FractionFree.previousPivot_zero
#check ConsensusADMM.Period48.FractionFree.previousPivot_succ
#check ConsensusADMM.Period48.FractionFree.pivot_apply
#check ConsensusADMM.Period48.FractionFree.principal_apply
#check ConsensusADMM.Period48.FractionFree.previousPivot_dvd_update
#check ConsensusADMM.Period48.FractionFree.pivot_eq_det
#check ConsensusADMM.Period48.FractionFree.one_le_pivot
#check (ConsensusADMM.Period48.j0_posDef : (ConsensusADMM.Period48.j0.map (Int.castRingHom ℝ)).PosDef)
