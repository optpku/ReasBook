/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.MidpointRows4
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row80
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row81
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row82
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row83
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row84
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row85
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row86
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row87
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row88
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row89
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row90
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row91
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row92
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row93
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row94
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TrailingCertificates.Row95

@[expose] public section

namespace ConsensusADMM.Period48.FractionFree

/-- The staged literal certificates recover original midpoint rows80–95. -/
lemma stageMidBlockSixth_checked :
    List.ofFn (fun k : Fin 16 => fun j : Fin 96 =>
        (runFromAt 0 j0 48).1 ⟨k.val + 80, by omega⟩ j) =
      List.ofFn (fun k : Fin 16 => fun j : Fin 96 =>
        stageMid ⟨k.val + 80, by omega⟩ j) := by
  apply List.ofFn_inj.mpr
  funext k
  fin_cases k
  · exact TrailingCertificates.Row80.row_checked
  · exact TrailingCertificates.Row81.row_checked
  · exact TrailingCertificates.Row82.row_checked
  · exact TrailingCertificates.Row83.row_checked
  · exact TrailingCertificates.Row84.row_checked
  · exact TrailingCertificates.Row85.row_checked
  · exact TrailingCertificates.Row86.row_checked
  · exact TrailingCertificates.Row87.row_checked
  · exact TrailingCertificates.Row88.row_checked
  · exact TrailingCertificates.Row89.row_checked
  · exact TrailingCertificates.Row90.row_checked
  · exact TrailingCertificates.Row91.row_checked
  · exact TrailingCertificates.Row92.row_checked
  · exact TrailingCertificates.Row93.row_checked
  · exact TrailingCertificates.Row94.row_checked
  · exact TrailingCertificates.Row95.row_checked

run_cmd do
  for a in ← Lean.collectAxioms ``ConsensusADMM.Period48.FractionFree.stageMidBlockSixth_checked do
    unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      throwError "Unexpected axiom in midpoint block5: {a}"
  Lean.logInfo "PASS: original midpoint block5; foundational axioms only."

end ConsensusADMM.Period48.FractionFree
