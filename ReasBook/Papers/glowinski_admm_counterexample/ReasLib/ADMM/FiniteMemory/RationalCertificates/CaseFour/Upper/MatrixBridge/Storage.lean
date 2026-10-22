/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.MatrixBridge.Action

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixAction
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.MatrixBridge.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.MatrixBridge.CaseLookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixFin

@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.MatrixBridge
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

/-- The original storage matrix equals the independently checked rational table. -/
theorem storage_eq : storageMatrix caseData .upper = literalP := by
  have hp : cumulativePrefix caseData (endpointGamma caseData .upper) = literalPrefix := by
    ext i j
    rw [cumulativePrefix_apply, action_eq]
    exact cachedPrefix i j
  have ht : storageOffDiagonal caseData .upper = literalT := by
    ext i j
    rw [storageOffDiagonal_apply, hp, cachedA]
    exact cachedT i j
  have hw : storageTerminal caseData .upper = literalW := by
    ext i j
    rw [storageTerminal_apply, hp, ht]
    exact cachedW i j
  ext i j
  simp only [storageMatrix, cachedA, ht, hw]
  exact cachedP i j

/-- The completed terminal block is symmetric. -/
theorem terminal_symm : (storageTerminal caseData .upper).IsSymm := by
  have hp : cumulativePrefix caseData (endpointGamma caseData .upper) = literalPrefix := by
    ext i j
    rw [cumulativePrefix_apply, action_eq]
    exact cachedPrefix i j
  have ht : storageOffDiagonal caseData .upper = literalT := by
    ext i j
    rw [storageOffDiagonal_apply, hp, cachedA]
    exact cachedT i j
  have hw : storageTerminal caseData .upper = literalW := by
    ext i j
    rw [storageTerminal_apply, hp, ht]
    exact cachedW i j
  rw [hw]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.transpose_apply]

#print axioms storage_eq
#print axioms terminal_symm
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.MatrixBridge
