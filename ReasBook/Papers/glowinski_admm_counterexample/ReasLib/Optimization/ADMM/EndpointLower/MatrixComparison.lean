module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower.ProofSupport
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower.Descent.Lookups
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower.Lower.Lookups

public meta import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.Descent.Lookups
public meta import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.Lower.Lookups
public meta import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.Descent.Lookups
public meta import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.Lookups
public meta import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower.Descent.Lookups
public meta import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower.Lower.Lookups

@[expose] public section

namespace ADMM.FiniteMemory.Reconstruction.EndpointLower

/-- A completely checked point to the right of the paper's displayed endpoint. -/
noncomputable def gamma : ℝ := 377 / 200 + 1 / 100000000

def descentQ : Matrix (Fin 10 × Fin 2) (Fin 10 × Fin 2) ℚ :=
  (-1 / 500000 : ℚ) • descentMatrix caseFour .lower +
    (500001 / 500000 : ℚ) • descentMatrix caseFour .upper

def lowerQ : Matrix (Fin 9 × Fin 2) (Fin 9 × Fin 2) ℚ :=
  (-1 / 500000 : ℚ) • lowerMatrix caseFour .lower +
    (500001 / 500000 : ℚ) • lowerMatrix caseFour .upper

lemma originalPrincipalLower : descentPrincipal caseFour .lower =
    RationalCertificates.CaseFour.Lower.Descent.candidateK := by
  ext i j
  rw [descentPrincipal_apply,
    RationalCertificates.CaseFour.Lower.MatrixBridge.descentMatrix_eq
      RationalCertificates.CaseFour.Lower.MatrixBridge.storage_eq]
  exact RationalCertificates.CaseFour.Lower.MatrixBridge.cachedDescentPrincipal i j

lemma originalPrincipalUpper : descentPrincipal caseFour .upper =
    RationalCertificates.CaseFour.Upper.Descent.candidateK := by
  ext i j
  rw [descentPrincipal_apply,
    RationalCertificates.CaseFour.Upper.MatrixBridge.descentMatrix_eq
      RationalCertificates.CaseFour.Upper.MatrixBridge.storage_eq]
  exact RationalCertificates.CaseFour.Upper.MatrixBridge.cachedDescentPrincipal i j

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
/-- Every newly certified principal entry is the exact affine extrapolation. -/
theorem descentPrincipal_eq_candidate :
    (fun i j : Fin 9 × Fin 2 => descentQ (i.1.castSucc, i.2)
      (j.1.castSucc, j.2)) = Descent.candidateK := by
  ext i j
  change (-1 / 500000 : ℚ) * descentPrincipal caseFour .lower i j +
    (500001 / 500000 : ℚ) * descentPrincipal caseFour .upper i j = _
  rw [originalPrincipalLower, originalPrincipalUpper]
  fin_cases i <;> fin_cases j <;> norm_num [RationalCertificates.CaseFour.Upper.Lower.candidateK]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
/-- Every newly certified lower-matrix entry is the exact affine extrapolation. -/
theorem lower_eq_candidate : lowerQ = Lower.candidateK := by
  rw [lowerQ, RationalCertificates.CaseFour.Lower.MatrixBridge.lowerMatrix_eq,
    RationalCertificates.CaseFour.Upper.MatrixBridge.lowerMatrix_eq]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [RationalCertificates.CaseFour.Upper.Lower.candidateK]
  fin_cases i <;> fin_cases j
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (0, 0) = Lower.candidateK (0, 0) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_0,
      Pilot.lookupK0_0, Lower.lookupK0_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (0, 1) = Lower.candidateK (0, 0) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_1,
      Pilot.lookupK0_1, Lower.lookupK0_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (1, 0) = Lower.candidateK (0, 0) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_2,
      Pilot.lookupK0_2, Lower.lookupK0_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (1, 1) = Lower.candidateK (0, 0) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_3,
      Pilot.lookupK0_3, Lower.lookupK0_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (2, 0) = Lower.candidateK (0, 0) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_4,
      Pilot.lookupK0_4, Lower.lookupK0_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (2, 1) = Lower.candidateK (0, 0) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_5,
      Pilot.lookupK0_5, Lower.lookupK0_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (3, 0) = Lower.candidateK (0, 0) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_6,
      Pilot.lookupK0_6, Lower.lookupK0_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (3, 1) = Lower.candidateK (0, 0) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_7,
      Pilot.lookupK0_7, Lower.lookupK0_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (4, 0) = Lower.candidateK (0, 0) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_8,
      Pilot.lookupK0_8, Lower.lookupK0_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (4, 1) = Lower.candidateK (0, 0) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_9,
      Pilot.lookupK0_9, Lower.lookupK0_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (5, 0) = Lower.candidateK (0, 0) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_10,
      Pilot.lookupK0_10, Lower.lookupK0_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (5, 1) = Lower.candidateK (0, 0) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_11,
      Pilot.lookupK0_11, Lower.lookupK0_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (6, 0) = Lower.candidateK (0, 0) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_12,
      Pilot.lookupK0_12, Lower.lookupK0_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (6, 1) = Lower.candidateK (0, 0) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_13,
      Pilot.lookupK0_13, Lower.lookupK0_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (7, 0) = Lower.candidateK (0, 0) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_14,
      Pilot.lookupK0_14, Lower.lookupK0_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (7, 1) = Lower.candidateK (0, 0) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_15,
      Pilot.lookupK0_15, Lower.lookupK0_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (8, 0) = Lower.candidateK (0, 0) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_16,
      Pilot.lookupK0_16, Lower.lookupK0_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 0) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 0) (8, 1) = Lower.candidateK (0, 0) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK0_17,
      Pilot.lookupK0_17, Lower.lookupK0_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (0, 0) = Lower.candidateK (0, 1) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_0,
      Pilot.lookupK1_0, Lower.lookupK1_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (0, 1) = Lower.candidateK (0, 1) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_1,
      Pilot.lookupK1_1, Lower.lookupK1_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (1, 0) = Lower.candidateK (0, 1) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_2,
      Pilot.lookupK1_2, Lower.lookupK1_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (1, 1) = Lower.candidateK (0, 1) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_3,
      Pilot.lookupK1_3, Lower.lookupK1_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (2, 0) = Lower.candidateK (0, 1) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_4,
      Pilot.lookupK1_4, Lower.lookupK1_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (2, 1) = Lower.candidateK (0, 1) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_5,
      Pilot.lookupK1_5, Lower.lookupK1_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (3, 0) = Lower.candidateK (0, 1) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_6,
      Pilot.lookupK1_6, Lower.lookupK1_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (3, 1) = Lower.candidateK (0, 1) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_7,
      Pilot.lookupK1_7, Lower.lookupK1_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (4, 0) = Lower.candidateK (0, 1) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_8,
      Pilot.lookupK1_8, Lower.lookupK1_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (4, 1) = Lower.candidateK (0, 1) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_9,
      Pilot.lookupK1_9, Lower.lookupK1_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (5, 0) = Lower.candidateK (0, 1) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_10,
      Pilot.lookupK1_10, Lower.lookupK1_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (5, 1) = Lower.candidateK (0, 1) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_11,
      Pilot.lookupK1_11, Lower.lookupK1_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (6, 0) = Lower.candidateK (0, 1) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_12,
      Pilot.lookupK1_12, Lower.lookupK1_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (6, 1) = Lower.candidateK (0, 1) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_13,
      Pilot.lookupK1_13, Lower.lookupK1_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (7, 0) = Lower.candidateK (0, 1) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_14,
      Pilot.lookupK1_14, Lower.lookupK1_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (7, 1) = Lower.candidateK (0, 1) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_15,
      Pilot.lookupK1_15, Lower.lookupK1_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (8, 0) = Lower.candidateK (0, 1) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_16,
      Pilot.lookupK1_16, Lower.lookupK1_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (0, 1) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (0, 1) (8, 1) = Lower.candidateK (0, 1) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK1_17,
      Pilot.lookupK1_17, Lower.lookupK1_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (0, 0) = Lower.candidateK (1, 0) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_0,
      Pilot.lookupK2_0, Lower.lookupK2_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (0, 1) = Lower.candidateK (1, 0) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_1,
      Pilot.lookupK2_1, Lower.lookupK2_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (1, 0) = Lower.candidateK (1, 0) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_2,
      Pilot.lookupK2_2, Lower.lookupK2_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (1, 1) = Lower.candidateK (1, 0) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_3,
      Pilot.lookupK2_3, Lower.lookupK2_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (2, 0) = Lower.candidateK (1, 0) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_4,
      Pilot.lookupK2_4, Lower.lookupK2_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (2, 1) = Lower.candidateK (1, 0) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_5,
      Pilot.lookupK2_5, Lower.lookupK2_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (3, 0) = Lower.candidateK (1, 0) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_6,
      Pilot.lookupK2_6, Lower.lookupK2_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (3, 1) = Lower.candidateK (1, 0) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_7,
      Pilot.lookupK2_7, Lower.lookupK2_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (4, 0) = Lower.candidateK (1, 0) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_8,
      Pilot.lookupK2_8, Lower.lookupK2_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (4, 1) = Lower.candidateK (1, 0) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_9,
      Pilot.lookupK2_9, Lower.lookupK2_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (5, 0) = Lower.candidateK (1, 0) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_10,
      Pilot.lookupK2_10, Lower.lookupK2_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (5, 1) = Lower.candidateK (1, 0) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_11,
      Pilot.lookupK2_11, Lower.lookupK2_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (6, 0) = Lower.candidateK (1, 0) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_12,
      Pilot.lookupK2_12, Lower.lookupK2_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (6, 1) = Lower.candidateK (1, 0) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_13,
      Pilot.lookupK2_13, Lower.lookupK2_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (7, 0) = Lower.candidateK (1, 0) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_14,
      Pilot.lookupK2_14, Lower.lookupK2_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (7, 1) = Lower.candidateK (1, 0) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_15,
      Pilot.lookupK2_15, Lower.lookupK2_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (8, 0) = Lower.candidateK (1, 0) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_16,
      Pilot.lookupK2_16, Lower.lookupK2_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 0) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 0) (8, 1) = Lower.candidateK (1, 0) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK2_17,
      Pilot.lookupK2_17, Lower.lookupK2_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (0, 0) = Lower.candidateK (1, 1) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_0,
      Pilot.lookupK3_0, Lower.lookupK3_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (0, 1) = Lower.candidateK (1, 1) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_1,
      Pilot.lookupK3_1, Lower.lookupK3_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (1, 0) = Lower.candidateK (1, 1) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_2,
      Pilot.lookupK3_2, Lower.lookupK3_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (1, 1) = Lower.candidateK (1, 1) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_3,
      Pilot.lookupK3_3, Lower.lookupK3_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (2, 0) = Lower.candidateK (1, 1) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_4,
      Pilot.lookupK3_4, Lower.lookupK3_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (2, 1) = Lower.candidateK (1, 1) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_5,
      Pilot.lookupK3_5, Lower.lookupK3_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (3, 0) = Lower.candidateK (1, 1) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_6,
      Pilot.lookupK3_6, Lower.lookupK3_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (3, 1) = Lower.candidateK (1, 1) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_7,
      Pilot.lookupK3_7, Lower.lookupK3_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (4, 0) = Lower.candidateK (1, 1) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_8,
      Pilot.lookupK3_8, Lower.lookupK3_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (4, 1) = Lower.candidateK (1, 1) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_9,
      Pilot.lookupK3_9, Lower.lookupK3_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (5, 0) = Lower.candidateK (1, 1) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_10,
      Pilot.lookupK3_10, Lower.lookupK3_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (5, 1) = Lower.candidateK (1, 1) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_11,
      Pilot.lookupK3_11, Lower.lookupK3_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (6, 0) = Lower.candidateK (1, 1) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_12,
      Pilot.lookupK3_12, Lower.lookupK3_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (6, 1) = Lower.candidateK (1, 1) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_13,
      Pilot.lookupK3_13, Lower.lookupK3_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (7, 0) = Lower.candidateK (1, 1) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_14,
      Pilot.lookupK3_14, Lower.lookupK3_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (7, 1) = Lower.candidateK (1, 1) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_15,
      Pilot.lookupK3_15, Lower.lookupK3_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (8, 0) = Lower.candidateK (1, 1) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_16,
      Pilot.lookupK3_16, Lower.lookupK3_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (1, 1) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (1, 1) (8, 1) = Lower.candidateK (1, 1) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK3_17,
      Pilot.lookupK3_17, Lower.lookupK3_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (0, 0) = Lower.candidateK (2, 0) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_0,
      Pilot.lookupK4_0, Lower.lookupK4_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (0, 1) = Lower.candidateK (2, 0) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_1,
      Pilot.lookupK4_1, Lower.lookupK4_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (1, 0) = Lower.candidateK (2, 0) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_2,
      Pilot.lookupK4_2, Lower.lookupK4_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (1, 1) = Lower.candidateK (2, 0) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_3,
      Pilot.lookupK4_3, Lower.lookupK4_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (2, 0) = Lower.candidateK (2, 0) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_4,
      Pilot.lookupK4_4, Lower.lookupK4_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (2, 1) = Lower.candidateK (2, 0) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_5,
      Pilot.lookupK4_5, Lower.lookupK4_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (3, 0) = Lower.candidateK (2, 0) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_6,
      Pilot.lookupK4_6, Lower.lookupK4_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (3, 1) = Lower.candidateK (2, 0) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_7,
      Pilot.lookupK4_7, Lower.lookupK4_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (4, 0) = Lower.candidateK (2, 0) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_8,
      Pilot.lookupK4_8, Lower.lookupK4_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (4, 1) = Lower.candidateK (2, 0) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_9,
      Pilot.lookupK4_9, Lower.lookupK4_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (5, 0) = Lower.candidateK (2, 0) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_10,
      Pilot.lookupK4_10, Lower.lookupK4_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (5, 1) = Lower.candidateK (2, 0) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_11,
      Pilot.lookupK4_11, Lower.lookupK4_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (6, 0) = Lower.candidateK (2, 0) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_12,
      Pilot.lookupK4_12, Lower.lookupK4_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (6, 1) = Lower.candidateK (2, 0) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_13,
      Pilot.lookupK4_13, Lower.lookupK4_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (7, 0) = Lower.candidateK (2, 0) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_14,
      Pilot.lookupK4_14, Lower.lookupK4_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (7, 1) = Lower.candidateK (2, 0) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_15,
      Pilot.lookupK4_15, Lower.lookupK4_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (8, 0) = Lower.candidateK (2, 0) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_16,
      Pilot.lookupK4_16, Lower.lookupK4_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 0) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 0) (8, 1) = Lower.candidateK (2, 0) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK4_17,
      Pilot.lookupK4_17, Lower.lookupK4_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (0, 0) = Lower.candidateK (2, 1) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_0,
      Pilot.lookupK5_0, Lower.lookupK5_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (0, 1) = Lower.candidateK (2, 1) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_1,
      Pilot.lookupK5_1, Lower.lookupK5_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (1, 0) = Lower.candidateK (2, 1) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_2,
      Pilot.lookupK5_2, Lower.lookupK5_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (1, 1) = Lower.candidateK (2, 1) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_3,
      Pilot.lookupK5_3, Lower.lookupK5_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (2, 0) = Lower.candidateK (2, 1) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_4,
      Pilot.lookupK5_4, Lower.lookupK5_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (2, 1) = Lower.candidateK (2, 1) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_5,
      Pilot.lookupK5_5, Lower.lookupK5_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (3, 0) = Lower.candidateK (2, 1) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_6,
      Pilot.lookupK5_6, Lower.lookupK5_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (3, 1) = Lower.candidateK (2, 1) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_7,
      Pilot.lookupK5_7, Lower.lookupK5_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (4, 0) = Lower.candidateK (2, 1) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_8,
      Pilot.lookupK5_8, Lower.lookupK5_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (4, 1) = Lower.candidateK (2, 1) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_9,
      Pilot.lookupK5_9, Lower.lookupK5_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (5, 0) = Lower.candidateK (2, 1) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_10,
      Pilot.lookupK5_10, Lower.lookupK5_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (5, 1) = Lower.candidateK (2, 1) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_11,
      Pilot.lookupK5_11, Lower.lookupK5_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (6, 0) = Lower.candidateK (2, 1) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_12,
      Pilot.lookupK5_12, Lower.lookupK5_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (6, 1) = Lower.candidateK (2, 1) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_13,
      Pilot.lookupK5_13, Lower.lookupK5_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (7, 0) = Lower.candidateK (2, 1) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_14,
      Pilot.lookupK5_14, Lower.lookupK5_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (7, 1) = Lower.candidateK (2, 1) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_15,
      Pilot.lookupK5_15, Lower.lookupK5_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (8, 0) = Lower.candidateK (2, 1) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_16,
      Pilot.lookupK5_16, Lower.lookupK5_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (2, 1) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (2, 1) (8, 1) = Lower.candidateK (2, 1) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK5_17,
      Pilot.lookupK5_17, Lower.lookupK5_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (0, 0) = Lower.candidateK (3, 0) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_0,
      Pilot.lookupK6_0, Lower.lookupK6_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (0, 1) = Lower.candidateK (3, 0) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_1,
      Pilot.lookupK6_1, Lower.lookupK6_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (1, 0) = Lower.candidateK (3, 0) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_2,
      Pilot.lookupK6_2, Lower.lookupK6_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (1, 1) = Lower.candidateK (3, 0) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_3,
      Pilot.lookupK6_3, Lower.lookupK6_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (2, 0) = Lower.candidateK (3, 0) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_4,
      Pilot.lookupK6_4, Lower.lookupK6_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (2, 1) = Lower.candidateK (3, 0) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_5,
      Pilot.lookupK6_5, Lower.lookupK6_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (3, 0) = Lower.candidateK (3, 0) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_6,
      Pilot.lookupK6_6, Lower.lookupK6_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (3, 1) = Lower.candidateK (3, 0) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_7,
      Pilot.lookupK6_7, Lower.lookupK6_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (4, 0) = Lower.candidateK (3, 0) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_8,
      Pilot.lookupK6_8, Lower.lookupK6_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (4, 1) = Lower.candidateK (3, 0) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_9,
      Pilot.lookupK6_9, Lower.lookupK6_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (5, 0) = Lower.candidateK (3, 0) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_10,
      Pilot.lookupK6_10, Lower.lookupK6_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (5, 1) = Lower.candidateK (3, 0) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_11,
      Pilot.lookupK6_11, Lower.lookupK6_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (6, 0) = Lower.candidateK (3, 0) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_12,
      Pilot.lookupK6_12, Lower.lookupK6_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (6, 1) = Lower.candidateK (3, 0) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_13,
      Pilot.lookupK6_13, Lower.lookupK6_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (7, 0) = Lower.candidateK (3, 0) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_14,
      Pilot.lookupK6_14, Lower.lookupK6_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (7, 1) = Lower.candidateK (3, 0) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_15,
      Pilot.lookupK6_15, Lower.lookupK6_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (8, 0) = Lower.candidateK (3, 0) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_16,
      Pilot.lookupK6_16, Lower.lookupK6_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 0) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 0) (8, 1) = Lower.candidateK (3, 0) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK6_17,
      Pilot.lookupK6_17, Lower.lookupK6_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (0, 0) = Lower.candidateK (3, 1) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_0,
      Pilot.lookupK7_0, Lower.lookupK7_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (0, 1) = Lower.candidateK (3, 1) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_1,
      Pilot.lookupK7_1, Lower.lookupK7_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (1, 0) = Lower.candidateK (3, 1) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_2,
      Pilot.lookupK7_2, Lower.lookupK7_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (1, 1) = Lower.candidateK (3, 1) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_3,
      Pilot.lookupK7_3, Lower.lookupK7_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (2, 0) = Lower.candidateK (3, 1) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_4,
      Pilot.lookupK7_4, Lower.lookupK7_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (2, 1) = Lower.candidateK (3, 1) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_5,
      Pilot.lookupK7_5, Lower.lookupK7_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (3, 0) = Lower.candidateK (3, 1) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_6,
      Pilot.lookupK7_6, Lower.lookupK7_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (3, 1) = Lower.candidateK (3, 1) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_7,
      Pilot.lookupK7_7, Lower.lookupK7_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (4, 0) = Lower.candidateK (3, 1) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_8,
      Pilot.lookupK7_8, Lower.lookupK7_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (4, 1) = Lower.candidateK (3, 1) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_9,
      Pilot.lookupK7_9, Lower.lookupK7_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (5, 0) = Lower.candidateK (3, 1) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_10,
      Pilot.lookupK7_10, Lower.lookupK7_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (5, 1) = Lower.candidateK (3, 1) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_11,
      Pilot.lookupK7_11, Lower.lookupK7_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (6, 0) = Lower.candidateK (3, 1) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_12,
      Pilot.lookupK7_12, Lower.lookupK7_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (6, 1) = Lower.candidateK (3, 1) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_13,
      Pilot.lookupK7_13, Lower.lookupK7_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (7, 0) = Lower.candidateK (3, 1) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_14,
      Pilot.lookupK7_14, Lower.lookupK7_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (7, 1) = Lower.candidateK (3, 1) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_15,
      Pilot.lookupK7_15, Lower.lookupK7_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (8, 0) = Lower.candidateK (3, 1) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_16,
      Pilot.lookupK7_16, Lower.lookupK7_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (3, 1) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (3, 1) (8, 1) = Lower.candidateK (3, 1) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK7_17,
      Pilot.lookupK7_17, Lower.lookupK7_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (0, 0) = Lower.candidateK (4, 0) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_0,
      Pilot.lookupK8_0, Lower.lookupK8_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (0, 1) = Lower.candidateK (4, 0) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_1,
      Pilot.lookupK8_1, Lower.lookupK8_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (1, 0) = Lower.candidateK (4, 0) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_2,
      Pilot.lookupK8_2, Lower.lookupK8_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (1, 1) = Lower.candidateK (4, 0) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_3,
      Pilot.lookupK8_3, Lower.lookupK8_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (2, 0) = Lower.candidateK (4, 0) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_4,
      Pilot.lookupK8_4, Lower.lookupK8_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (2, 1) = Lower.candidateK (4, 0) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_5,
      Pilot.lookupK8_5, Lower.lookupK8_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (3, 0) = Lower.candidateK (4, 0) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_6,
      Pilot.lookupK8_6, Lower.lookupK8_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (3, 1) = Lower.candidateK (4, 0) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_7,
      Pilot.lookupK8_7, Lower.lookupK8_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (4, 0) = Lower.candidateK (4, 0) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_8,
      Pilot.lookupK8_8, Lower.lookupK8_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (4, 1) = Lower.candidateK (4, 0) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_9,
      Pilot.lookupK8_9, Lower.lookupK8_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (5, 0) = Lower.candidateK (4, 0) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_10,
      Pilot.lookupK8_10, Lower.lookupK8_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (5, 1) = Lower.candidateK (4, 0) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_11,
      Pilot.lookupK8_11, Lower.lookupK8_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (6, 0) = Lower.candidateK (4, 0) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_12,
      Pilot.lookupK8_12, Lower.lookupK8_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (6, 1) = Lower.candidateK (4, 0) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_13,
      Pilot.lookupK8_13, Lower.lookupK8_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (7, 0) = Lower.candidateK (4, 0) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_14,
      Pilot.lookupK8_14, Lower.lookupK8_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (7, 1) = Lower.candidateK (4, 0) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_15,
      Pilot.lookupK8_15, Lower.lookupK8_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (8, 0) = Lower.candidateK (4, 0) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_16,
      Pilot.lookupK8_16, Lower.lookupK8_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 0) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 0) (8, 1) = Lower.candidateK (4, 0) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK8_17,
      Pilot.lookupK8_17, Lower.lookupK8_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (0, 0) = Lower.candidateK (4, 1) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_0,
      Pilot.lookupK9_0, Lower.lookupK9_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (0, 1) = Lower.candidateK (4, 1) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_1,
      Pilot.lookupK9_1, Lower.lookupK9_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (1, 0) = Lower.candidateK (4, 1) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_2,
      Pilot.lookupK9_2, Lower.lookupK9_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (1, 1) = Lower.candidateK (4, 1) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_3,
      Pilot.lookupK9_3, Lower.lookupK9_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (2, 0) = Lower.candidateK (4, 1) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_4,
      Pilot.lookupK9_4, Lower.lookupK9_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (2, 1) = Lower.candidateK (4, 1) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_5,
      Pilot.lookupK9_5, Lower.lookupK9_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (3, 0) = Lower.candidateK (4, 1) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_6,
      Pilot.lookupK9_6, Lower.lookupK9_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (3, 1) = Lower.candidateK (4, 1) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_7,
      Pilot.lookupK9_7, Lower.lookupK9_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (4, 0) = Lower.candidateK (4, 1) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_8,
      Pilot.lookupK9_8, Lower.lookupK9_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (4, 1) = Lower.candidateK (4, 1) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_9,
      Pilot.lookupK9_9, Lower.lookupK9_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (5, 0) = Lower.candidateK (4, 1) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_10,
      Pilot.lookupK9_10, Lower.lookupK9_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (5, 1) = Lower.candidateK (4, 1) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_11,
      Pilot.lookupK9_11, Lower.lookupK9_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (6, 0) = Lower.candidateK (4, 1) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_12,
      Pilot.lookupK9_12, Lower.lookupK9_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (6, 1) = Lower.candidateK (4, 1) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_13,
      Pilot.lookupK9_13, Lower.lookupK9_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (7, 0) = Lower.candidateK (4, 1) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_14,
      Pilot.lookupK9_14, Lower.lookupK9_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (7, 1) = Lower.candidateK (4, 1) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_15,
      Pilot.lookupK9_15, Lower.lookupK9_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (8, 0) = Lower.candidateK (4, 1) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_16,
      Pilot.lookupK9_16, Lower.lookupK9_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (4, 1) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (4, 1) (8, 1) = Lower.candidateK (4, 1) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK9_17,
      Pilot.lookupK9_17, Lower.lookupK9_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (0, 0) = Lower.candidateK (5, 0) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_0,
      Pilot.lookupK10_0, Lower.lookupK10_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (0, 1) = Lower.candidateK (5, 0) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_1,
      Pilot.lookupK10_1, Lower.lookupK10_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (1, 0) = Lower.candidateK (5, 0) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_2,
      Pilot.lookupK10_2, Lower.lookupK10_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (1, 1) = Lower.candidateK (5, 0) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_3,
      Pilot.lookupK10_3, Lower.lookupK10_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (2, 0) = Lower.candidateK (5, 0) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_4,
      Pilot.lookupK10_4, Lower.lookupK10_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (2, 1) = Lower.candidateK (5, 0) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_5,
      Pilot.lookupK10_5, Lower.lookupK10_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (3, 0) = Lower.candidateK (5, 0) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_6,
      Pilot.lookupK10_6, Lower.lookupK10_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (3, 1) = Lower.candidateK (5, 0) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_7,
      Pilot.lookupK10_7, Lower.lookupK10_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (4, 0) = Lower.candidateK (5, 0) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_8,
      Pilot.lookupK10_8, Lower.lookupK10_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (4, 1) = Lower.candidateK (5, 0) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_9,
      Pilot.lookupK10_9, Lower.lookupK10_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (5, 0) = Lower.candidateK (5, 0) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_10,
      Pilot.lookupK10_10, Lower.lookupK10_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (5, 1) = Lower.candidateK (5, 0) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_11,
      Pilot.lookupK10_11, Lower.lookupK10_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (6, 0) = Lower.candidateK (5, 0) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_12,
      Pilot.lookupK10_12, Lower.lookupK10_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (6, 1) = Lower.candidateK (5, 0) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_13,
      Pilot.lookupK10_13, Lower.lookupK10_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (7, 0) = Lower.candidateK (5, 0) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_14,
      Pilot.lookupK10_14, Lower.lookupK10_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (7, 1) = Lower.candidateK (5, 0) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_15,
      Pilot.lookupK10_15, Lower.lookupK10_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (8, 0) = Lower.candidateK (5, 0) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_16,
      Pilot.lookupK10_16, Lower.lookupK10_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 0) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 0) (8, 1) = Lower.candidateK (5, 0) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK10_17,
      Pilot.lookupK10_17, Lower.lookupK10_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (0, 0) = Lower.candidateK (5, 1) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_0,
      Pilot.lookupK11_0, Lower.lookupK11_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (0, 1) = Lower.candidateK (5, 1) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_1,
      Pilot.lookupK11_1, Lower.lookupK11_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (1, 0) = Lower.candidateK (5, 1) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_2,
      Pilot.lookupK11_2, Lower.lookupK11_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (1, 1) = Lower.candidateK (5, 1) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_3,
      Pilot.lookupK11_3, Lower.lookupK11_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (2, 0) = Lower.candidateK (5, 1) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_4,
      Pilot.lookupK11_4, Lower.lookupK11_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (2, 1) = Lower.candidateK (5, 1) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_5,
      Pilot.lookupK11_5, Lower.lookupK11_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (3, 0) = Lower.candidateK (5, 1) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_6,
      Pilot.lookupK11_6, Lower.lookupK11_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (3, 1) = Lower.candidateK (5, 1) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_7,
      Pilot.lookupK11_7, Lower.lookupK11_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (4, 0) = Lower.candidateK (5, 1) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_8,
      Pilot.lookupK11_8, Lower.lookupK11_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (4, 1) = Lower.candidateK (5, 1) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_9,
      Pilot.lookupK11_9, Lower.lookupK11_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (5, 0) = Lower.candidateK (5, 1) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_10,
      Pilot.lookupK11_10, Lower.lookupK11_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (5, 1) = Lower.candidateK (5, 1) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_11,
      Pilot.lookupK11_11, Lower.lookupK11_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (6, 0) = Lower.candidateK (5, 1) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_12,
      Pilot.lookupK11_12, Lower.lookupK11_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (6, 1) = Lower.candidateK (5, 1) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_13,
      Pilot.lookupK11_13, Lower.lookupK11_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (7, 0) = Lower.candidateK (5, 1) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_14,
      Pilot.lookupK11_14, Lower.lookupK11_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (7, 1) = Lower.candidateK (5, 1) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_15,
      Pilot.lookupK11_15, Lower.lookupK11_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (8, 0) = Lower.candidateK (5, 1) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_16,
      Pilot.lookupK11_16, Lower.lookupK11_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (5, 1) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (5, 1) (8, 1) = Lower.candidateK (5, 1) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK11_17,
      Pilot.lookupK11_17, Lower.lookupK11_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (0, 0) = Lower.candidateK (6, 0) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_0,
      Pilot.lookupK12_0, Lower.lookupK12_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (0, 1) = Lower.candidateK (6, 0) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_1,
      Pilot.lookupK12_1, Lower.lookupK12_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (1, 0) = Lower.candidateK (6, 0) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_2,
      Pilot.lookupK12_2, Lower.lookupK12_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (1, 1) = Lower.candidateK (6, 0) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_3,
      Pilot.lookupK12_3, Lower.lookupK12_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (2, 0) = Lower.candidateK (6, 0) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_4,
      Pilot.lookupK12_4, Lower.lookupK12_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (2, 1) = Lower.candidateK (6, 0) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_5,
      Pilot.lookupK12_5, Lower.lookupK12_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (3, 0) = Lower.candidateK (6, 0) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_6,
      Pilot.lookupK12_6, Lower.lookupK12_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (3, 1) = Lower.candidateK (6, 0) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_7,
      Pilot.lookupK12_7, Lower.lookupK12_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (4, 0) = Lower.candidateK (6, 0) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_8,
      Pilot.lookupK12_8, Lower.lookupK12_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (4, 1) = Lower.candidateK (6, 0) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_9,
      Pilot.lookupK12_9, Lower.lookupK12_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (5, 0) = Lower.candidateK (6, 0) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_10,
      Pilot.lookupK12_10, Lower.lookupK12_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (5, 1) = Lower.candidateK (6, 0) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_11,
      Pilot.lookupK12_11, Lower.lookupK12_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (6, 0) = Lower.candidateK (6, 0) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_12,
      Pilot.lookupK12_12, Lower.lookupK12_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (6, 1) = Lower.candidateK (6, 0) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_13,
      Pilot.lookupK12_13, Lower.lookupK12_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (7, 0) = Lower.candidateK (6, 0) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_14,
      Pilot.lookupK12_14, Lower.lookupK12_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (7, 1) = Lower.candidateK (6, 0) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_15,
      Pilot.lookupK12_15, Lower.lookupK12_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (8, 0) = Lower.candidateK (6, 0) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_16,
      Pilot.lookupK12_16, Lower.lookupK12_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 0) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 0) (8, 1) = Lower.candidateK (6, 0) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK12_17,
      Pilot.lookupK12_17, Lower.lookupK12_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (0, 0) = Lower.candidateK (6, 1) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_0,
      Pilot.lookupK13_0, Lower.lookupK13_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (0, 1) = Lower.candidateK (6, 1) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_1,
      Pilot.lookupK13_1, Lower.lookupK13_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (1, 0) = Lower.candidateK (6, 1) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_2,
      Pilot.lookupK13_2, Lower.lookupK13_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (1, 1) = Lower.candidateK (6, 1) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_3,
      Pilot.lookupK13_3, Lower.lookupK13_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (2, 0) = Lower.candidateK (6, 1) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_4,
      Pilot.lookupK13_4, Lower.lookupK13_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (2, 1) = Lower.candidateK (6, 1) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_5,
      Pilot.lookupK13_5, Lower.lookupK13_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (3, 0) = Lower.candidateK (6, 1) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_6,
      Pilot.lookupK13_6, Lower.lookupK13_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (3, 1) = Lower.candidateK (6, 1) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_7,
      Pilot.lookupK13_7, Lower.lookupK13_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (4, 0) = Lower.candidateK (6, 1) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_8,
      Pilot.lookupK13_8, Lower.lookupK13_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (4, 1) = Lower.candidateK (6, 1) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_9,
      Pilot.lookupK13_9, Lower.lookupK13_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (5, 0) = Lower.candidateK (6, 1) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_10,
      Pilot.lookupK13_10, Lower.lookupK13_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (5, 1) = Lower.candidateK (6, 1) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_11,
      Pilot.lookupK13_11, Lower.lookupK13_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (6, 0) = Lower.candidateK (6, 1) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_12,
      Pilot.lookupK13_12, Lower.lookupK13_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (6, 1) = Lower.candidateK (6, 1) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_13,
      Pilot.lookupK13_13, Lower.lookupK13_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (7, 0) = Lower.candidateK (6, 1) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_14,
      Pilot.lookupK13_14, Lower.lookupK13_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (7, 1) = Lower.candidateK (6, 1) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_15,
      Pilot.lookupK13_15, Lower.lookupK13_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (8, 0) = Lower.candidateK (6, 1) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_16,
      Pilot.lookupK13_16, Lower.lookupK13_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (6, 1) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (6, 1) (8, 1) = Lower.candidateK (6, 1) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK13_17,
      Pilot.lookupK13_17, Lower.lookupK13_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (0, 0) = Lower.candidateK (7, 0) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_0,
      Pilot.lookupK14_0, Lower.lookupK14_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (0, 1) = Lower.candidateK (7, 0) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_1,
      Pilot.lookupK14_1, Lower.lookupK14_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (1, 0) = Lower.candidateK (7, 0) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_2,
      Pilot.lookupK14_2, Lower.lookupK14_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (1, 1) = Lower.candidateK (7, 0) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_3,
      Pilot.lookupK14_3, Lower.lookupK14_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (2, 0) = Lower.candidateK (7, 0) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_4,
      Pilot.lookupK14_4, Lower.lookupK14_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (2, 1) = Lower.candidateK (7, 0) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_5,
      Pilot.lookupK14_5, Lower.lookupK14_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (3, 0) = Lower.candidateK (7, 0) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_6,
      Pilot.lookupK14_6, Lower.lookupK14_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (3, 1) = Lower.candidateK (7, 0) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_7,
      Pilot.lookupK14_7, Lower.lookupK14_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (4, 0) = Lower.candidateK (7, 0) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_8,
      Pilot.lookupK14_8, Lower.lookupK14_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (4, 1) = Lower.candidateK (7, 0) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_9,
      Pilot.lookupK14_9, Lower.lookupK14_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (5, 0) = Lower.candidateK (7, 0) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_10,
      Pilot.lookupK14_10, Lower.lookupK14_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (5, 1) = Lower.candidateK (7, 0) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_11,
      Pilot.lookupK14_11, Lower.lookupK14_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (6, 0) = Lower.candidateK (7, 0) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_12,
      Pilot.lookupK14_12, Lower.lookupK14_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (6, 1) = Lower.candidateK (7, 0) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_13,
      Pilot.lookupK14_13, Lower.lookupK14_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (7, 0) = Lower.candidateK (7, 0) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_14,
      Pilot.lookupK14_14, Lower.lookupK14_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (7, 1) = Lower.candidateK (7, 0) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_15,
      Pilot.lookupK14_15, Lower.lookupK14_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (8, 0) = Lower.candidateK (7, 0) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_16,
      Pilot.lookupK14_16, Lower.lookupK14_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 0) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 0) (8, 1) = Lower.candidateK (7, 0) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK14_17,
      Pilot.lookupK14_17, Lower.lookupK14_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (0, 0) = Lower.candidateK (7, 1) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_0,
      Pilot.lookupK15_0, Lower.lookupK15_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (0, 1) = Lower.candidateK (7, 1) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_1,
      Pilot.lookupK15_1, Lower.lookupK15_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (1, 0) = Lower.candidateK (7, 1) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_2,
      Pilot.lookupK15_2, Lower.lookupK15_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (1, 1) = Lower.candidateK (7, 1) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_3,
      Pilot.lookupK15_3, Lower.lookupK15_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (2, 0) = Lower.candidateK (7, 1) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_4,
      Pilot.lookupK15_4, Lower.lookupK15_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (2, 1) = Lower.candidateK (7, 1) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_5,
      Pilot.lookupK15_5, Lower.lookupK15_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (3, 0) = Lower.candidateK (7, 1) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_6,
      Pilot.lookupK15_6, Lower.lookupK15_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (3, 1) = Lower.candidateK (7, 1) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_7,
      Pilot.lookupK15_7, Lower.lookupK15_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (4, 0) = Lower.candidateK (7, 1) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_8,
      Pilot.lookupK15_8, Lower.lookupK15_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (4, 1) = Lower.candidateK (7, 1) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_9,
      Pilot.lookupK15_9, Lower.lookupK15_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (5, 0) = Lower.candidateK (7, 1) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_10,
      Pilot.lookupK15_10, Lower.lookupK15_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (5, 1) = Lower.candidateK (7, 1) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_11,
      Pilot.lookupK15_11, Lower.lookupK15_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (6, 0) = Lower.candidateK (7, 1) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_12,
      Pilot.lookupK15_12, Lower.lookupK15_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (6, 1) = Lower.candidateK (7, 1) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_13,
      Pilot.lookupK15_13, Lower.lookupK15_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (7, 0) = Lower.candidateK (7, 1) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_14,
      Pilot.lookupK15_14, Lower.lookupK15_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (7, 1) = Lower.candidateK (7, 1) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_15,
      Pilot.lookupK15_15, Lower.lookupK15_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (8, 0) = Lower.candidateK (7, 1) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_16,
      Pilot.lookupK15_16, Lower.lookupK15_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (7, 1) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (7, 1) (8, 1) = Lower.candidateK (7, 1) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK15_17,
      Pilot.lookupK15_17, Lower.lookupK15_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (0, 0) = Lower.candidateK (8, 0) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_0,
      Pilot.lookupK16_0, Lower.lookupK16_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (0, 1) = Lower.candidateK (8, 0) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_1,
      Pilot.lookupK16_1, Lower.lookupK16_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (1, 0) = Lower.candidateK (8, 0) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_2,
      Pilot.lookupK16_2, Lower.lookupK16_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (1, 1) = Lower.candidateK (8, 0) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_3,
      Pilot.lookupK16_3, Lower.lookupK16_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (2, 0) = Lower.candidateK (8, 0) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_4,
      Pilot.lookupK16_4, Lower.lookupK16_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (2, 1) = Lower.candidateK (8, 0) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_5,
      Pilot.lookupK16_5, Lower.lookupK16_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (3, 0) = Lower.candidateK (8, 0) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_6,
      Pilot.lookupK16_6, Lower.lookupK16_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (3, 1) = Lower.candidateK (8, 0) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_7,
      Pilot.lookupK16_7, Lower.lookupK16_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (4, 0) = Lower.candidateK (8, 0) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_8,
      Pilot.lookupK16_8, Lower.lookupK16_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (4, 1) = Lower.candidateK (8, 0) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_9,
      Pilot.lookupK16_9, Lower.lookupK16_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (5, 0) = Lower.candidateK (8, 0) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_10,
      Pilot.lookupK16_10, Lower.lookupK16_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (5, 1) = Lower.candidateK (8, 0) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_11,
      Pilot.lookupK16_11, Lower.lookupK16_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (6, 0) = Lower.candidateK (8, 0) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_12,
      Pilot.lookupK16_12, Lower.lookupK16_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (6, 1) = Lower.candidateK (8, 0) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_13,
      Pilot.lookupK16_13, Lower.lookupK16_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (7, 0) = Lower.candidateK (8, 0) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_14,
      Pilot.lookupK16_14, Lower.lookupK16_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (7, 1) = Lower.candidateK (8, 0) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_15,
      Pilot.lookupK16_15, Lower.lookupK16_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (8, 0) = Lower.candidateK (8, 0) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_16,
      Pilot.lookupK16_16, Lower.lookupK16_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 0) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 0) (8, 1) = Lower.candidateK (8, 0) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK16_17,
      Pilot.lookupK16_17, Lower.lookupK16_17]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (0, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (0, 0) = Lower.candidateK (8, 1) (0, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_0,
      Pilot.lookupK17_0, Lower.lookupK17_0]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (0, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (0, 1) = Lower.candidateK (8, 1) (0, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_1,
      Pilot.lookupK17_1, Lower.lookupK17_1]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (1, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (1, 0) = Lower.candidateK (8, 1) (1, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_2,
      Pilot.lookupK17_2, Lower.lookupK17_2]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (1, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (1, 1) = Lower.candidateK (8, 1) (1, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_3,
      Pilot.lookupK17_3, Lower.lookupK17_3]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (2, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (2, 0) = Lower.candidateK (8, 1) (2, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_4,
      Pilot.lookupK17_4, Lower.lookupK17_4]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (2, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (2, 1) = Lower.candidateK (8, 1) (2, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_5,
      Pilot.lookupK17_5, Lower.lookupK17_5]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (3, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (3, 0) = Lower.candidateK (8, 1) (3, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_6,
      Pilot.lookupK17_6, Lower.lookupK17_6]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (3, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (3, 1) = Lower.candidateK (8, 1) (3, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_7,
      Pilot.lookupK17_7, Lower.lookupK17_7]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (4, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (4, 0) = Lower.candidateK (8, 1) (4, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_8,
      Pilot.lookupK17_8, Lower.lookupK17_8]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (4, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (4, 1) = Lower.candidateK (8, 1) (4, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_9,
      Pilot.lookupK17_9, Lower.lookupK17_9]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (5, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (5, 0) = Lower.candidateK (8, 1) (5, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_10,
      Pilot.lookupK17_10, Lower.lookupK17_10]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (5, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (5, 1) = Lower.candidateK (8, 1) (5, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_11,
      Pilot.lookupK17_11, Lower.lookupK17_11]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (6, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (6, 0) = Lower.candidateK (8, 1) (6, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_12,
      Pilot.lookupK17_12, Lower.lookupK17_12]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (6, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (6, 1) = Lower.candidateK (8, 1) (6, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_13,
      Pilot.lookupK17_13, Lower.lookupK17_13]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (7, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (7, 0) = Lower.candidateK (8, 1) (7, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_14,
      Pilot.lookupK17_14, Lower.lookupK17_14]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (7, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (7, 1) = Lower.candidateK (8, 1) (7, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_15,
      Pilot.lookupK17_15, Lower.lookupK17_15]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (8, 0) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (8, 0) = Lower.candidateK (8, 1) (8, 0)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_16,
      Pilot.lookupK17_16, Lower.lookupK17_16]
    norm_num
  · change (-1 / 500000 : ℚ) * RationalCertificates.CaseFour.Lower.Lower.candidateK (8, 1) (8, 1) +
      (500001 / 500000 : ℚ) * Pilot.candidateK (8, 1) (8, 1) = Lower.candidateK (8, 1) (8, 1)
    rw [RationalCertificates.CaseFour.Lower.Lower.lookupK17_17,
      Pilot.lookupK17_17, Lower.lookupK17_17]
    norm_num

lemma descentQ_symm : descentQ.IsSymm := by
  have h (e : Endpoint) : (descentMatrix caseFour e).IsSymm :=
    rationalMatrixOfQuadratic_isSymm _
  exact ((h .lower).smul _).add ((h .upper).smul _)

lemma lowerQ_symm : lowerQ.IsSymm := by
  have h (e : Endpoint) : (lowerMatrix caseFour e).IsSymm :=
    rationalMatrixOfQuadratic_isSymm _
  exact ((h .lower).smul _).add ((h .upper).smul _)

lemma descentQ_kernel : descentQ * constantModes 10 = 0 := by
  simp only [descentQ, Matrix.add_mul, Matrix.smul_mul,
    caseFourValid.descent_kernel, smul_zero, add_zero]

lemma theta_value :
    (gamma - (caseFour.gammaLower : ℝ)) /
      ((caseFour.gammaUpper : ℝ) - caseFour.gammaLower) = 500001 / 500000 := by
  norm_num [gamma, caseFour, RationalCase.ofNumerators]

lemma descent_cast :
    ADMM.FiniteMemory.descentMatrix gamma caseFour.omega caseFour.epsilon
      (lagMinusNNReal caseFourValid) (lagPlusNNReal caseFourValid)
      (intervalStorage caseFour gamma) = castMatrix descentQ := by
  rw [intervalDescentMatrix_eq_affine caseFourValid gamma]
  simp only [theta_value]
  change (1 - (500001 : ℝ) / 500000) •
      ADMM.FiniteMemory.descentMatrix (endpointGamma caseFour .lower) caseFour.omega
        caseFour.epsilon (lagMinusNNReal caseFourValid) (lagPlusNNReal caseFourValid)
        (endpointStorage caseFour .lower) +
    ((500001 : ℝ) / 500000) •
      ADMM.FiniteMemory.descentMatrix (endpointGamma caseFour .upper) caseFour.omega
        caseFour.epsilon (lagMinusNNReal caseFourValid) (lagPlusNNReal caseFourValid)
        (endpointStorage caseFour .upper) = _
  rw [← cast_descentMatrix caseFourValid .lower, ← cast_descentMatrix caseFourValid .upper]
  ext i j
  simp only [castMatrix_apply, descentQ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

lemma lower_cast :
    ADMM.FiniteMemory.lowerMatrix gamma caseFour.zeta (intervalStorage caseFour gamma)
      (muNNReal caseFourValid) = castMatrix lowerQ := by
  rw [intervalLowerMatrix_eq_affine caseFourValid gamma]
  simp only [theta_value]
  change (1 - (500001 : ℝ) / 500000) •
      ADMM.FiniteMemory.lowerMatrix (endpointGamma caseFour .lower) caseFour.zeta
        (endpointStorage caseFour .lower) (muNNReal caseFourValid) +
    ((500001 : ℝ) / 500000) •
      ADMM.FiniteMemory.lowerMatrix (endpointGamma caseFour .upper) caseFour.zeta
        (endpointStorage caseFour .upper) (muNNReal caseFourValid) = _
  rw [← cast_lowerMatrix caseFourValid .lower, ← cast_lowerMatrix caseFourValid .upper]
  ext i j
  simp only [castMatrix_apply, lowerQ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

end ADMM.FiniteMemory.Reconstruction.EndpointLower
