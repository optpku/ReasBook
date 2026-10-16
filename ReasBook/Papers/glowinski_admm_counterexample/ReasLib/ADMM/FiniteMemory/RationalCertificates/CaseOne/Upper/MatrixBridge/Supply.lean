module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Upper.MatrixBridge.SupplyRow7
public meta import Lean.Util.CollectAxioms
@[expose] public section
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge

/-- Every entry of the supplied exact table agrees with the original quadratic definition. -/
theorem supplyMatrix_eq : supplyMatrix caseData (endpointGamma caseData .upper) = literalQ := by
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

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge
