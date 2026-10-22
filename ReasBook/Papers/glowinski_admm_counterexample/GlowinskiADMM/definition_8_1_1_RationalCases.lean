/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCases

@[expose] public section

/- The exact rational finite-memory cases remain available through their stable namespace. -/
#check (ADMM.FiniteMemory.Reconstruction.caseOne :
  ADMM.FiniteMemory.Reconstruction.RationalCase 2)
