/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.MatrixBridge.DescentNumeric
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.MatrixBridge.Supply
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.Descent.Local
public meta import Lean.Util.CollectAxioms

@[expose] public section
set_option maxRecDepth 4096
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge
open MatrixAssembly

/-- The original descent construction agrees with the checked literal matrix. -/
theorem descentMatrix_eq (hP : storageMatrix caseData .lower = literalP) :
    descentMatrix caseData .lower = literalDescent := by
  ext i j
  rw [descentMatrix_factored, hP, supplyMatrix_eq]
  exact cachedDescent i j

/-- Both original descent obligations follow from the verified storage comparison. -/
theorem descentChecks (hP : storageMatrix caseData .lower = literalP) :
    descentMatrix caseData .lower * constantModes 4 = 0 ∧
      PositivePivots (1 / 10000000) (descentPrincipal caseData .lower) := by
  constructor
  · rw [descentMatrix_eq hP]
    exact cachedDescentKernel
  · have principal : descentPrincipal caseData .lower = ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.Descent.candidateK := by
      ext i j
      rw [descentPrincipal_apply, descentMatrix_eq hP]
      exact cachedDescentPrincipal i j
    rw [principal]
    exact ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.Descent.candidatePositive

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in ← Lean.collectAxioms ``descentChecks do
    unless allowed.contains name do
      throwError "Disallowed axiom in exact descent checks: {name}"
  Lean.logInfo "[verified] descent kernel and original LDL pivots follow from the storage equality"

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge
