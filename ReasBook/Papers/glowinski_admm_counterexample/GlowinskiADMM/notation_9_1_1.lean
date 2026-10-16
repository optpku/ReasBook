module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.IntegerMatrix

@[expose] public section

/- Notation 9.1.1: the unscaled integer matrix `K` uses the period-48 convention
`Circ(t) i j = t (j - i)`, the displayed rows `p`, `q`, and `c`, and blocks
`Circ(p)`, `Circ(c)`, `Circ(c)ᵀ`, and `Circ(q)`, with no scaling. -/
#check
  (ConsensusADMM.Period48.integerMatrix :
    Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℤ)

#check ConsensusADMM.Period48.circulant
#check ConsensusADMM.Period48.circulant_apply
#check ConsensusADMM.Period48.p
#check ConsensusADMM.Period48.q
#check ConsensusADMM.Period48.c
#check ConsensusADMM.Period48.p_reflect
#check ConsensusADMM.Period48.q_reflect
#check ConsensusADMM.Period48.integerMatrix_apply
#check ConsensusADMM.Period48.integerMatrix_transpose
