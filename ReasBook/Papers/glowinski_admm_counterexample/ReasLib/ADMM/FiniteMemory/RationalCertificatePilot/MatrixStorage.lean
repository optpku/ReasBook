/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.Matrix
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixAction
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixLookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.CaseLookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin

@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

namespace ADMM.FiniteMemory.Reconstruction.Pilot
open MatrixAssembly

/-- The prefix candidates are exactly the finite sums of the action candidates. -/
theorem cachedPrefix (i : Fin 9 × Fin 2) (j : Fin 2) :
    -(∑ t : Fin 10, if t ≤ i.1.castSucc then literalAction (t, i.2) j else 0) =
      literalPrefix i j := by
  rcases i with ⟨i, a⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, Fin.le_iff_val_le_val]

/-- The principal block is the original packed rational data. -/
theorem cachedA : upperTriangleMatrix caseData .upper = literalA := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;> norm_num [Fin.lt_def]

/-- The off-diagonal block candidates satisfy the prescribed matrix completion. -/
theorem cachedT (i : Fin 8 × Fin 2) (j : Fin 2) :
    literalPrefix (i.1.castSucc, i.2) j - (literalA * constantModes 8) i j = literalT i j := by
  rcases i with ⟨i, a⟩
  rw [mul_constantModes]
  fin_cases i <;> fin_cases a <;> fin_cases j <;> norm_num [Fin.sum_univ_succ]

/-- The terminal candidates satisfy the last block-row completion. -/
theorem cachedW (i j : Fin 2) :
    literalPrefix (Fin.last 8, i) j -
      (∑ k : Fin 8 × Fin 2, literalT k i * constantModes 8 k j) = literalW i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, constantModes, Fin.last]

/-- The full storage candidates are the checked blockwise assembly. -/
theorem cachedP (i j : Fin 9 × Fin 2) :
    (if hi : i.1 < 8 then
      if hj : j.1 < 8 then literalA (⟨i.1, hi⟩, i.2) (⟨j.1, hj⟩, j.2)
      else literalT (⟨i.1, hi⟩, i.2) j.2
    else if hj : j.1 < 8 then literalT (⟨j.1, hj⟩, j.2) i.2
    else literalW i.2 j.2) = literalP i j := by
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;> norm_num [Fin.lt_def]

/-- A verified action table fixes the entire storage matrix. -/
theorem storage_eq_of_action
    (ha : supplyConstantModes caseData (endpointGamma caseData .upper) = literalAction) :
    storageMatrix caseData .upper = literalP := by
  have hp := prefix_eq_of_layers ha cachedPrefix
  have ht := offDiagonal_eq_of_layers hp cachedA cachedT
  have hw := terminal_eq_of_layers hp ht cachedW
  exact storage_eq_of_layers cachedA ht hw cachedP

end ADMM.FiniteMemory.Reconstruction.Pilot
