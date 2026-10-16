module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.GramMatrix

@[expose] public section

/- Definition 4.1.5: the exact period-48 constants, alternating vector, rank-one
perturbation of the integer matrix, and its parity-dependent support contributions. -/
#check (ConsensusADMM.Period48.gramMatrix : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
#check ConsensusADMM.Period48.gammaZero
#check ConsensusADMM.Period48.sigma
#check ConsensusADMM.Period48.alternating
#check ConsensusADMM.Period48.perturbationVector
#check ConsensusADMM.Period48.gramMatrix_isSymm
#check ConsensusADMM.Period48.alternatingSupport_odd
#check ConsensusADMM.Period48.alternatingSupport_even
#check ConsensusADMM.Period48.alternatingOriginSupport_eq
#check ConsensusADMM.Period48.integerMatrix
