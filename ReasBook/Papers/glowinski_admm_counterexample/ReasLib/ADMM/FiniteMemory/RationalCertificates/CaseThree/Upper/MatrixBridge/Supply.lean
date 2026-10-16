module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.SupplyRow19
public meta import Lean.Util.CollectAxioms
@[expose] public section
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge

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
  · exact supply_row_8 j
  · exact supply_row_9 j
  · exact supply_row_10 j
  · exact supply_row_11 j
  · exact supply_row_12 j
  · exact supply_row_13 j
  · exact supply_row_14 j
  · exact supply_row_15 j
  · exact supply_row_16 j
  · exact supply_row_17 j
  · exact supply_row_18 j
  · exact supply_row_19 j

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in ← Lean.collectAxioms ``supplyMatrix_eq do
    unless allowed.contains name do
      throwError "Disallowed axiom in exact supply certificate: {name}"
  Lean.logInfo "[verified] original supply matrix equals literal table; foundational axioms only"

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
