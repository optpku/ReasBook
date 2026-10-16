module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixAssembly

@[expose] public section

namespace ADMM.FiniteMemory.Reconstruction.MatrixAssembly

/-- Rational polarization is symmetric, so only one triangle needs evaluation. -/
theorem supplyMatrix_comm {ℓ : ℕ} (c : RationalCase ℓ) (γ : ℚ)
    (i j : Fin (ℓ + 2) × Fin 2) :
    supplyMatrix c γ i j = supplyMatrix c γ j i := by
  change (supply c γ (unitVector i + unitVector j) - supply c γ (unitVector i) -
    supply c γ (unitVector j)) / 2 =
    (supply c γ (unitVector j + unitVector i) - supply c γ (unitVector j) -
      supply c γ (unitVector i)) / 2
  rw [add_comm (unitVector i) (unitVector j)]
  ring

/-- Embed storage on the previous history, inserting a zero initial pair. -/
def previousPadding {k : ℕ} (P : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) :
    Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℚ := fun i j ↦
  Fin.cases 0 (fun a ↦ Fin.cases 0 (fun b ↦ P (a, i.2) (b, j.2)) j.1) i.1

/-- Embed storage on the current history, inserting a zero terminal pair. -/
def currentPadding {k : ℕ} (P : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) :
    Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℚ := fun i j ↦
  Fin.lastCases 0 (fun a ↦ Fin.lastCases 0 (fun b ↦ P (a, i.2) (b, j.2)) j.1) i.1

/-- Inserting a zero initial block realizes the previous-history contraction. -/
theorem quadratic_previousPadding {k : ℕ}
    (P : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (Z : (Fin (k + 1) × Fin 2) → ℚ) :
    quadraticStorage (previousPadding P) Z =
      quadraticStorage P (fun i ↦ Z (i.1.succ, i.2)) := by
  simp only [quadraticStorage, Fintype.sum_prod_type]
  rw [Fin.sum_univ_succ]
  simp only [previousPadding, Fin.cases_zero, zero_mul, Finset.sum_const_zero, zero_add,
    Fin.cases_succ]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.cases_succ]

/-- Inserting a zero final block realizes the current-history contraction. -/
theorem quadratic_currentPadding {k : ℕ}
    (P : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (Z : (Fin (k + 1) × Fin 2) → ℚ) :
    quadraticStorage (currentPadding P) Z =
      quadraticStorage P (fun i ↦ Z (i.1.castSucc, i.2)) := by
  simp only [quadraticStorage, Fintype.sum_prod_type]
  rw [Fin.sum_univ_castSucc]
  simp only [currentPadding, Fin.lastCases_last, zero_mul, Finset.sum_const_zero,
    add_zero, Fin.lastCases_castSucc]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_last, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.lastCases_castSucc]

/-- Descent entries are sparse padded-storage entries minus the supply matrix. -/
theorem descentMatrix_factored {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (i j : Fin (ℓ + 2) × Fin 2) :
    descentMatrix c e i j =
      (previousPadding (storageMatrix c e) i j +
        previousPadding (storageMatrix c e) j i) / 2 -
      (currentPadding (storageMatrix c e) i j +
        currentPadding (storageMatrix c e) j i) / 2 -
      supplyMatrix c (endpointGamma c e) i j := by
  have hp := quadratic_previousPadding (storageMatrix c e)
  have hc := quadratic_currentPadding (storageMatrix c e)
  unfold descentMatrix
  simp_rw [← hp, ← hc, polar_sub]
  simp only [Matrix.sub_apply, polar_storage, supplyMatrix]

end ADMM.FiniteMemory.Reconstruction.MatrixAssembly
