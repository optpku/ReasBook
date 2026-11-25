/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.StateSignals
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.FinitePrefix
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GeneratedHistory

@[expose] public section

namespace ADMM.UnitCircle.Initialized

open ADMM.ConvergenceProof Supply
open scoped BigOperators

noncomputable section

/-- The two actual generated graph-position sequences, with time zero the first update. -/
def actualPoint {m : ℕ} (η w : ℕ → Fin m → ℝ) (b : Fin 2) : ℕ → Fin m → ℝ :=
  if b = 0 then generatedPosition η w .F else generatedPosition η w .J

def actualNormal {m : ℕ} (γ : ℝ) (η w : ℕ → Fin m → ℝ) (b : Fin 2) : ℕ → Fin m → ℝ :=
  if b = 0 then generatedNormal γ η w .F else generatedNormal γ η w .J

/-- The actual residual at every positive generated step. -/
def actualResidual {m : ℕ} (w : ℕ → Fin m → ℝ) (k : ℕ) : Fin m → ℝ :=
  w (k + 1) - w k

/-- Dropping the initial state changes the generated positions only at the first update. -/
theorem auxPoint_eq_actual_after_zero {m : ℕ} (η w : ℕ → Fin m → ℝ) (b : Fin 2)
    (k : ℕ) (hk : 0 < k) :
    auxPoint (fun j ↦ η (j + 1)) (fun j ↦ w (j + 1)) b k = actualPoint η w b k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  by_cases hb : b = 0 <;>
    simp [auxPoint, auxResidual, actualPoint, hb, generatedPosition, zeroDelay_add]

/-- The same first-step locality holds for both actual graph normals. -/
theorem auxNormal_eq_actual_after_zero {m : ℕ} (γ : ℝ) (η w : ℕ → Fin m → ℝ)
    (b : Fin 2) (k : ℕ) (hk : 0 < k) :
    auxNormal γ (fun j ↦ η (j + 1)) (fun j ↦ w (j + 1)) b k =
      actualNormal γ η w b k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  by_cases hb : b = 0 <;>
    simp [auxNormal, auxMultiplier, actualNormal, hb,
      generatedNormal, generatedPosition, zeroDelay_add] <;> module

/-- The auxiliary and actual residuals agree after their single initial correction. -/
theorem auxResidual_eq_actual_after_zero {m : ℕ} (w : ℕ → Fin m → ℝ)
    (k : ℕ) (hk : 1 ≤ k) :
    auxResidual (fun j ↦ w (j + 1)) k = actualResidual w k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp [auxResidual, actualResidual, zeroDelay_add]

def actualSupply {m ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ) (η w : ℕ → Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ b : Fin 2, blockSupply c b (actualPoint η w b) (actualNormal γ η w b) k

def auxSupply {m ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ) (η w : ℕ → Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ b : Fin 2, blockSupply c b
    (auxPoint (fun j ↦ η (j + 1)) (fun j ↦ w (j + 1)) b)
    (auxNormal γ (fun j ↦ η (j + 1)) (fun j ↦ w (j + 1)) b) k

/-- The complete actual and auxiliary supplies differ on a fixed finite prefix. -/
theorem auxSupply_eq_actual_after_prefix {m ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ)
    (η w : ℕ → Fin m → ℝ) (k : ℕ) (hk : ℓ + 1 ≤ k) :
    auxSupply c γ η w k = actualSupply c γ η w k := by
  apply Finset.sum_congr rfl
  intro b _
  apply blockSupply_eq_after_prefix c b _ _ _ _
    (auxPoint_eq_actual_after_zero η w b) (auxNormal_eq_actual_after_zero γ η w b) k hk

/-- The manuscript's initialization error constant: finite, fixed, and independent of α. -/
def initializationError {m ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ)
    (η w : ℕ → Fin m → ℝ) : ℝ :=
  (∑ k ∈ Finset.range (ℓ + 1), |auxSupply c γ η w k - actualSupply c γ η w k|) +
    c.epsilon * |coordinateSquare (auxResidual (fun j ↦ w (j + 1)) 0) -
      coordinateSquare (actualResidual w 0)|

end

end ADMM.UnitCircle.Initialized
