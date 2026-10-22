/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.MidpointRows3
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row64
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row65
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row66
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row67
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row68
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row69
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row70
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row71
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row72
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row73
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row74
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row75
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row76
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row77
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row78
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row79

@[expose] public section

namespace ConsensusADMM.Period48.FractionFree

/-- The staged literal certificates recover original midpoint rows64–79. -/
lemma stageMidBlockFifth_checked :
    List.ofFn (fun k : Fin 16 => fun j : Fin 96 =>
        (runFromAt 0 j0 48).1 ⟨k.val + 64, by omega⟩ j) =
      List.ofFn (fun k : Fin 16 => fun j : Fin 96 =>
        stageMid ⟨k.val + 64, by omega⟩ j) := by
  apply List.ofFn_inj.mpr
  funext k
  fin_cases k
  · exact TrailingCertificates.Row64.row_checked
  · exact TrailingCertificates.Row65.row_checked
  · exact TrailingCertificates.Row66.row_checked
  · exact TrailingCertificates.Row67.row_checked
  · exact TrailingCertificates.Row68.row_checked
  · exact TrailingCertificates.Row69.row_checked
  · exact TrailingCertificates.Row70.row_checked
  · exact TrailingCertificates.Row71.row_checked
  · exact TrailingCertificates.Row72.row_checked
  · exact TrailingCertificates.Row73.row_checked
  · exact TrailingCertificates.Row74.row_checked
  · exact TrailingCertificates.Row75.row_checked
  · exact TrailingCertificates.Row76.row_checked
  · exact TrailingCertificates.Row77.row_checked
  · exact TrailingCertificates.Row78.row_checked
  · exact TrailingCertificates.Row79.row_checked

run_cmd do
  for a in ← Lean.collectAxioms ``ConsensusADMM.Period48.FractionFree.stageMidBlockFifth_checked do
    unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      throwError "Unexpected axiom in midpoint block4: {a}"
  Lean.logInfo "PASS: original midpoint block4; foundational axioms only."

end ConsensusADMM.Period48.FractionFree
