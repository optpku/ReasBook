module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.MidBridge

@[expose] public section

namespace ConsensusADMM.Period48.FractionFree

-- Rewrite to the proved scalar-keyed recurrence before proof-producing evaluation.
-- Its explicit stage and coordinate arguments keep memoization keys small.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
set_option cbv.maxSteps 100000000 in
/-- The pivots recorded by the last forty-eight elimination steps, started from the recorded
intermediate stage, are the last forty-eight recorded pivots. -/
lemma pivotsSecondHalf_eq :
    (runFromAt 48 stageMid 48).2 = (List.ofFn pivotTable).drop 48 := by
  -- A closed equation between computable integer lists: proof-producing evaluation of the second half
  -- of the elimination started from the recorded intermediate stage.  The stage is a literal
  -- rather than a definition that has to be unfolded step by step, which keeps the recursion
  -- depth of the evaluation inside the kernel budget.
  rw [← midPivots_eq_runFromAt]
  decide_cbv

run_cmd do
  let axioms ← Lean.collectAxioms ``ConsensusADMM.Period48.FractionFree.pivotsSecondHalf_eq
  for a in axioms do
    unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      throwError "Unexpected axiom in pivotsSecondHalf_eq: {a}"
  IO.eprintln "[verified] FractionFree.pivotsSecondHalf_eq; foundational axioms only"

end ConsensusADMM.Period48.FractionFree
