/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.Core

@[expose] public section

namespace ConsensusADMM.Period48.FractionFree

-- Rewrite to the proved scalar-keyed recurrence before proof-producing evaluation.
-- Its explicit stage and coordinate arguments keep memoization keys small.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
set_option cbv.maxSteps 100000000 in
/-- The first forty-eight pivots of the elimination are the first forty-eight recorded
pivots. -/
lemma pivotsFirstHalf_eq : (runFromAt 0 j0 48).2 = (List.ofFn pivotTable).take 48 := by
  -- A closed equation between computable integer lists: proof-producing
  -- call-by-value evaluation shares repeated entries of the elimination.
  rw [← keyedPivots_eq_runFromAt]
  decide_cbv

run_cmd do
  let axioms ← Lean.collectAxioms ``ConsensusADMM.Period48.FractionFree.pivotsFirstHalf_eq
  for a in axioms do
    unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      throwError "Unexpected axiom in pivotsFirstHalf_eq: {a}"
  IO.eprintln "[verified] FractionFree.pivotsFirstHalf_eq; foundational axioms only"

end ConsensusADMM.Period48.FractionFree
