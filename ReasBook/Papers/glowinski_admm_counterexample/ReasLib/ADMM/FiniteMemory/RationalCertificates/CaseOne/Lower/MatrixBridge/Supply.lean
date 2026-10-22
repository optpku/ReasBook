/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.MatrixBridge.SupplyRow7
public meta import Lean.Util.CollectAxioms
@[expose] public section
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge

/-- Every entry of the supplied exact table agrees with the original quadratic definition. -/
theorem supplyMatrix_eq : supplyMatrix caseData (endpointGamma caseData .lower) = literalQ := by
  ext ⟨i, a⟩ j
  fin_cases i <;> fin_cases a
  · exact supply_row_0 j
  · exact supply_row_1 j
  · exact supply_row_2 j
  · exact supply_row_3 j
  · exact supply_row_4 j
  · exact supply_row_5 j
  · exact supply_row_6 j
  · exact supply_row_7 j

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in ← Lean.collectAxioms ``supplyMatrix_eq do
    unless allowed.contains name do
      throwError "Disallowed axiom in exact supply certificate: {name}"
  Lean.logInfo "[verified] original supply matrix equals literal table; foundational axioms only"

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge
