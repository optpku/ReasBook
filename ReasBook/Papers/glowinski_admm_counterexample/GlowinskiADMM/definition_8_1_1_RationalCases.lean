module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCases

@[expose] public section

/- The exact rational finite-memory cases remain available through their stable namespace. -/
#check (ADMM.FiniteMemory.Reconstruction.caseOne :
  ADMM.FiniteMemory.Reconstruction.RationalCase 2)
