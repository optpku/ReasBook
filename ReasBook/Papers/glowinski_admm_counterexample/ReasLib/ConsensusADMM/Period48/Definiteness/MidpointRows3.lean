/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.MidpointRows2
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row48
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row49
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row50
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row51
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row52
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row53
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row54
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row55
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row56
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row57
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row58
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row59
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row60
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row61
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row62
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row63

@[expose] public section

namespace ConsensusADMM.Period48.FractionFree

/-- The staged literal certificates recover original midpoint rows48–63. -/
lemma stageMidBlockForth_checked :
    List.ofFn (fun k : Fin 16 => fun j : Fin 96 =>
        (runFromAt 0 j0 48).1 ⟨k.val + 48, by omega⟩ j) =
      List.ofFn (fun k : Fin 16 => fun j : Fin 96 =>
        stageMid ⟨k.val + 48, by omega⟩ j) := by
  apply List.ofFn_inj.mpr
  funext k
  fin_cases k
  · exact TrailingCertificates.Row48.row_checked
  · exact TrailingCertificates.Row49.row_checked
  · exact TrailingCertificates.Row50.row_checked
  · exact TrailingCertificates.Row51.row_checked
  · exact TrailingCertificates.Row52.row_checked
  · exact TrailingCertificates.Row53.row_checked
  · exact TrailingCertificates.Row54.row_checked
  · exact TrailingCertificates.Row55.row_checked
  · exact TrailingCertificates.Row56.row_checked
  · exact TrailingCertificates.Row57.row_checked
  · exact TrailingCertificates.Row58.row_checked
  · exact TrailingCertificates.Row59.row_checked
  · exact TrailingCertificates.Row60.row_checked
  · exact TrailingCertificates.Row61.row_checked
  · exact TrailingCertificates.Row62.row_checked
  · exact TrailingCertificates.Row63.row_checked

run_cmd do
  for a in ← Lean.collectAxioms ``ConsensusADMM.Period48.FractionFree.stageMidBlockForth_checked do
    unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      throwError "Unexpected axiom in midpoint block3: {a}"
  Lean.logInfo "PASS: original midpoint block3; foundational axioms only."

end ConsensusADMM.Period48.FractionFree
