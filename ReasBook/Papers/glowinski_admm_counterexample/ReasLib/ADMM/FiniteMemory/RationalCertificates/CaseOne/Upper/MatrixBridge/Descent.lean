module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Upper.MatrixBridge.DescentNumeric
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Upper.MatrixBridge.Supply
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Upper.Descent.Local
public meta import Lean.Util.CollectAxioms

@[expose] public section
set_option maxRecDepth 4096
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge
open MatrixAssembly

/-- The original descent construction agrees with the checked literal matrix. -/
theorem descentMatrix_eq (hP : storageMatrix caseData .upper = literalP) :
    descentMatrix caseData .upper = literalDescent := by
  ext i j
  rw [descentMatrix_factored, hP, supplyMatrix_eq]
  exact cachedDescent i j

/-- Both original descent obligations follow from the verified storage comparison. -/
theorem descentChecks (hP : storageMatrix caseData .upper = literalP) :
    descentMatrix caseData .upper * constantModes 4 = 0 ∧
      PositivePivots (1 / 10000000) (descentPrincipal caseData .upper) := by
  constructor
  · rw [descentMatrix_eq hP]
    exact cachedDescentKernel
  · have principal : descentPrincipal caseData .upper = ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.Descent.candidateK := by
      ext i j
      rw [descentPrincipal_apply, descentMatrix_eq hP]
      exact cachedDescentPrincipal i j
    rw [principal]
    exact ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.Descent.candidatePositive

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in ← Lean.collectAxioms ``descentChecks do
    unless allowed.contains name do
      throwError "Disallowed axiom in exact descent checks: {name}"
  Lean.logInfo "[verified] descent kernel and original LDL pivots follow from the storage equality"

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge
