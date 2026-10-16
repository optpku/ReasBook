module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalReconstruction
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCaseData
public meta import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalReconstruction
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalComputation
public meta import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalComputation

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.MatrixBridge.Lower
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.MatrixBridge.Descent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Upper.MatrixBridge.Lower
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Upper.MatrixBridge.Descent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseTwo.Lower.MatrixBridge.Lower
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseTwo.Lower.MatrixBridge.Descent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseTwo.Upper.MatrixBridge.Lower
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseTwo.Upper.MatrixBridge.Descent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Lower.MatrixBridge.Lower
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Lower.MatrixBridge.Descent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.Lower
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.Descent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.MatrixBridge.Lower
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.MatrixBridge.Descent
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.MatrixBridge.Lower
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.MatrixBridge.Descent

@[expose] public section

namespace ADMM.FiniteMemory.Reconstruction

/-- The first rational table has the exact endpoint, lag, interpolation, and storage data. -/
theorem caseOne_spec :
    (caseOne.gammaLower, caseOne.gammaUpper, (caseOne.lagMinus .F).length,
      (caseOne.packedMu .F).length, (caseOne.upperTriangle .lower).length) =
      (3 / 2, 17 / 10, 2, 4, 10) := by
  -- Reduce the stored scalar projections and the three concrete mapped-list lengths.
  norm_num [caseOne, RationalCase.ofNumerators, RationalCase.rationalList]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- All exact positivity, balance, kernel, and pivot checks hold for `caseOne`. -/
theorem caseOneValid : Valid caseOne := by
  apply Valid.ofChecks
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact RationalCertificates.CaseOne.Lower.MatrixBridge.mu_nonneg
  · intro e
    cases e
    · exact RationalCertificates.CaseOne.Lower.MatrixBridge.terminal_symm
    · exact RationalCertificates.CaseOne.Upper.MatrixBridge.terminal_symm
  · intro e
    cases e
    · exact (RationalCertificates.CaseOne.Lower.MatrixBridge.descentChecks
        RationalCertificates.CaseOne.Lower.MatrixBridge.storage_eq).1
    · exact (RationalCertificates.CaseOne.Upper.MatrixBridge.descentChecks
        RationalCertificates.CaseOne.Upper.MatrixBridge.storage_eq).1
  · intro e
    cases e
    · exact (RationalCertificates.CaseOne.Lower.MatrixBridge.descentChecks
        RationalCertificates.CaseOne.Lower.MatrixBridge.storage_eq).2
    · exact (RationalCertificates.CaseOne.Upper.MatrixBridge.descentChecks
        RationalCertificates.CaseOne.Upper.MatrixBridge.storage_eq).2
  · intro e
    cases e
    · exact RationalCertificates.CaseOne.Lower.MatrixBridge.lowerPositive
    · exact RationalCertificates.CaseOne.Upper.MatrixBridge.lowerPositive


/-- The second rational table has the exact endpoint, lag, interpolation, and storage data. -/
theorem caseTwo_spec :
    (caseTwo.gammaLower, caseTwo.gammaUpper, (caseTwo.lagMinus .F).length,
      (caseTwo.packedMu .F).length, (caseTwo.upperTriangle .lower).length) =
      (17 / 10, 187 / 100, 6, 36, 78) := by
  -- Reduce the stored scalar projections and the three concrete mapped-list lengths.
  norm_num [caseTwo, RationalCase.ofNumerators, RationalCase.rationalList]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- All exact positivity, balance, kernel, and pivot checks hold for `caseTwo`. -/
theorem caseTwoValid : Valid caseTwo := by
  apply Valid.ofChecks
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact RationalCertificates.CaseTwo.Lower.MatrixBridge.mu_nonneg
  · intro e
    cases e
    · exact RationalCertificates.CaseTwo.Lower.MatrixBridge.terminal_symm
    · exact RationalCertificates.CaseTwo.Upper.MatrixBridge.terminal_symm
  · intro e
    cases e
    · exact (RationalCertificates.CaseTwo.Lower.MatrixBridge.descentChecks
        RationalCertificates.CaseTwo.Lower.MatrixBridge.storage_eq).1
    · exact (RationalCertificates.CaseTwo.Upper.MatrixBridge.descentChecks
        RationalCertificates.CaseTwo.Upper.MatrixBridge.storage_eq).1
  · intro e
    cases e
    · exact (RationalCertificates.CaseTwo.Lower.MatrixBridge.descentChecks
        RationalCertificates.CaseTwo.Lower.MatrixBridge.storage_eq).2
    · exact (RationalCertificates.CaseTwo.Upper.MatrixBridge.descentChecks
        RationalCertificates.CaseTwo.Upper.MatrixBridge.storage_eq).2
  · intro e
    cases e
    · exact RationalCertificates.CaseTwo.Lower.MatrixBridge.lowerPositive
    · exact RationalCertificates.CaseTwo.Upper.MatrixBridge.lowerPositive


/-- The third rational table has the exact endpoint, lag, interpolation, and storage data. -/
theorem caseThree_spec :
    (caseThree.gammaLower, caseThree.gammaUpper, (caseThree.lagMinus .F).length,
      (caseThree.packedMu .F).length, (caseThree.upperTriangle .lower).length) =
      (187 / 100, 47 / 25, 8, 64, 136) := by
  -- Reduce the stored scalar projections and the three concrete mapped-list lengths.
  norm_num [caseThree, RationalCase.ofNumerators, RationalCase.rationalList]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- All exact positivity, balance, kernel, and pivot checks hold for `caseThree`. -/
theorem caseThreeValid : Valid caseThree := by
  apply Valid.ofChecks
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact RationalCertificates.CaseThree.Lower.MatrixBridge.mu_nonneg
  · intro e
    cases e
    · exact RationalCertificates.CaseThree.Lower.MatrixBridge.terminal_symm
    · exact RationalCertificates.CaseThree.Upper.MatrixBridge.terminal_symm
  · intro e
    cases e
    · exact (RationalCertificates.CaseThree.Lower.MatrixBridge.descentChecks
        RationalCertificates.CaseThree.Lower.MatrixBridge.storage_eq).1
    · exact (RationalCertificates.CaseThree.Upper.MatrixBridge.descentChecks
        RationalCertificates.CaseThree.Upper.MatrixBridge.storage_eq).1
  · intro e
    cases e
    · exact (RationalCertificates.CaseThree.Lower.MatrixBridge.descentChecks
        RationalCertificates.CaseThree.Lower.MatrixBridge.storage_eq).2
    · exact (RationalCertificates.CaseThree.Upper.MatrixBridge.descentChecks
        RationalCertificates.CaseThree.Upper.MatrixBridge.storage_eq).2
  · intro e
    cases e
    · exact RationalCertificates.CaseThree.Lower.MatrixBridge.lowerPositive
    · exact RationalCertificates.CaseThree.Upper.MatrixBridge.lowerPositive


/-- The fourth rational table has the exact endpoint, lag, interpolation, and storage data. -/
theorem caseFour_spec :
    (caseFour.gammaLower, caseFour.gammaUpper, (caseFour.lagMinus .F).length,
      (caseFour.packedMu .F).length, (caseFour.upperTriangle .lower).length) =
      (47 / 25, 377 / 200, 8, 64, 136) := by
  -- Reduce the stored scalar projections and the three concrete mapped-list lengths.
  norm_num [caseFour, RationalCase.ofNumerators, RationalCase.rationalList]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- All exact positivity, balance, kernel, and pivot checks hold for `caseFour`. -/
theorem caseFourValid : Valid caseFour := by
  apply Valid.ofChecks
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact RationalCertificates.CaseFour.Lower.MatrixBridge.mu_nonneg
  · intro e
    cases e
    · exact RationalCertificates.CaseFour.Lower.MatrixBridge.terminal_symm
    · exact RationalCertificates.CaseFour.Upper.MatrixBridge.terminal_symm
  · intro e
    cases e
    · exact (RationalCertificates.CaseFour.Lower.MatrixBridge.descentChecks
        RationalCertificates.CaseFour.Lower.MatrixBridge.storage_eq).1
    · exact (RationalCertificates.CaseFour.Upper.MatrixBridge.descentChecks
        RationalCertificates.CaseFour.Upper.MatrixBridge.storage_eq).1
  · intro e
    cases e
    · exact (RationalCertificates.CaseFour.Lower.MatrixBridge.descentChecks
        RationalCertificates.CaseFour.Lower.MatrixBridge.storage_eq).2
    · exact (RationalCertificates.CaseFour.Upper.MatrixBridge.descentChecks
        RationalCertificates.CaseFour.Upper.MatrixBridge.storage_eq).2
  · intro e
    cases e
    · exact RationalCertificates.CaseFour.Lower.MatrixBridge.lowerPositive
    · exact RationalCertificates.CaseFour.Upper.MatrixBridge.lowerPositive


/-- The four endpoint pairs test `224` pivots across their sixteen exact matrices. -/
theorem allCasesPivotCount :
    4 * (2 * (2 + 1)) + 4 * (2 * (6 + 1)) +
      4 * (2 * (8 + 1)) + 4 * (2 * (8 + 1)) = 224 := by
  -- Normalize the four closed natural-number contributions.
  norm_num

end ADMM.FiniteMemory.Reconstruction
