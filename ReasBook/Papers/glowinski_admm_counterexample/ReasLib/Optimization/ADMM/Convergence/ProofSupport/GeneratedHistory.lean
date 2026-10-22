/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.Certificate
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.TiltedValues

@[expose] public section

open ADMM.FiniteMemory

namespace ADMM.ConvergenceProof

/-- A moving newest-first history whose oldest entry is at time `k`. -/
def generatedHistory {m ℓ : ℕ} (η w : ℕ → Fin m → ℝ) (k : ℕ) :
    (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ :=
  fun i ↦ if i.2 = 0 then η (k + i.1.rev.val) else w (k + i.1.rev.val)

/-- The generated graph position at step `k + 1`, in normalized coordinates. -/
def generatedPosition {m : ℕ} (η w : ℕ → Fin m → ℝ) (b : Block) (k : ℕ) : Fin m → ℝ :=
  match b with
  | .F => η (k + 1) + (w (k + 1) - w k)
  | .J => η (k + 1)

/-- The generated graph normal at step `k + 1`, in normalized coordinates. -/
def generatedNormal {m : ℕ} (γ : ℝ) (η w : ℕ → Fin m → ℝ)
    (b : Block) (k : ℕ) : Fin m → ℝ :=
  match b with
  | .F => η k - γ • w k - generatedPosition η w .F k
  | .J => γ • w k + (w (k + 1) - w k)

/-- Adjacent moving histories overlap on their common states. -/
theorem generatedHistory_shift {m ℓ : ℕ} (η w : ℕ → Fin m → ℝ)
    (k : ℕ) (i : Fin (ℓ + 1) × Fin 2) :
    generatedHistory η w (k + 1) (i.1.succ, i.2) =
      generatedHistory η w k (i.1.castSucc, i.2) := by
  simp only [generatedHistory, Fin.rev_succ, Fin.rev_castSucc, Fin.val_castSucc,
    Fin.val_succ]
  congr 2 <;> omega

/-- The history residual is the consecutive difference of scaled multipliers. -/
theorem generatedHistory_residual {m ℓ : ℕ} (η w : ℕ → Fin m → ℝ)
    (k : ℕ) (j : Fin (ℓ + 1)) :
    FiniteMemory.residual (generatedHistory η w k) j =
      w (k + j.rev.val + 1) - w (k + j.rev.val) := by
  simp [FiniteMemory.residual, generatedHistory, Fin.rev_castSucc, Fin.rev_succ,
    Nat.add_assoc]

/-- Coordinate extraction commutes with residuals. -/
theorem residual_coordinate {m ℓ : ℕ}
    (Z : (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ) (j : Fin (ℓ + 1)) (a : Fin m) :
    FiniteMemory.residual (fun i ↦ Z i a) j = FiniteMemory.residual Z j a := rfl

/-- Graph positions extracted from a moving history are the generated orbit
positions at the corresponding positive step. -/
theorem generatedHistory_position {m ℓ : ℕ} (η w : ℕ → Fin m → ℝ)
    (b : Block) (k : ℕ) (j : Fin (ℓ + 1)) :
    graphPosition b (generatedHistory η w k) j =
      generatedPosition η w b (k + j.rev.val) := by
  cases b <;>
    simp [graphPosition, FiniteMemory.residual, generatedHistory, generatedPosition,
      Fin.rev_castSucc, Fin.rev_succ, Nat.add_assoc]

/-- The extracted graph normals use the same generated time as the positions. -/
theorem generatedHistory_normal {m ℓ : ℕ} (γ : ℝ) (η w : ℕ → Fin m → ℝ)
    (b : Block) (k : ℕ) (j : Fin (ℓ + 1)) :
    graphNormal γ b (generatedHistory η w k) j =
      generatedNormal γ η w b (k + j.rev.val) := by
  cases b <;>
    simp [graphNormal, graphPosition, FiniteMemory.residual, generatedHistory, generatedNormal,
      generatedPosition, Fin.rev_castSucc, Fin.rev_succ, Nat.add_assoc]

/-- Coordinate extraction commutes with the history graph position. -/
theorem graphPosition_coordinate {m ℓ : ℕ}
    (Z : (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ) (b : Block)
    (j : Fin (ℓ + 1)) (a : Fin m) :
    graphPosition b (fun i ↦ Z i a) j = graphPosition b Z j a := by
  cases b <;> rfl

/-- Coordinate extraction commutes with the history graph normal. -/
theorem graphNormal_coordinate {m ℓ : ℕ}
    (Z : (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ) (γ : ℝ) (b : Block)
    (j : Fin (ℓ + 1)) (a : Fin m) :
    graphNormal γ b (fun i ↦ Z i a) j = graphNormal γ b Z j a := by
  cases b <;> rfl

/-- The predecessor interpolation position is a generated position, after
selecting one coordinate. -/
theorem generatedHistory_interpolationPosition {m ℓ : ℕ}
    (η w : ℕ → Fin m → ℝ) (b : Block) (k : ℕ) (j : Fin ℓ) (a : Fin m) :
    interpolationPosition b (some j)
      (fun i ↦ generatedHistory η w k (i.1.succ, i.2) a) =
      generatedPosition η w b (k + j.rev.val) a := by
  cases b <;>
    simp [interpolationPosition, generatedHistory, generatedPosition, Fin.rev_castSucc,
      Fin.rev_succ, Nat.add_assoc] <;> ring

/-- The predecessor interpolation normal is the corresponding generated normal. -/
theorem generatedHistory_interpolationNormal {m ℓ : ℕ}
    (γ : ℝ) (η w : ℕ → Fin m → ℝ) (b : Block) (k : ℕ) (j : Fin ℓ) (a : Fin m) :
    interpolationNormal γ b (some j)
      (fun i ↦ generatedHistory η w k (i.1.succ, i.2) a) =
      generatedNormal γ η w b (k + j.rev.val) a := by
  cases b <;>
    simp [interpolationNormal, interpolationPosition, generatedHistory,
      generatedPosition, generatedNormal, Fin.rev_castSucc, Fin.rev_succ,
      Nat.add_assoc] <;> ring

/-- The real tilted value history uses only positive generated steps. -/
noncomputable def generatedValues {m ℓ : ℕ}
    (f : Block → (Fin m → ℝ) → EReal) (η w : ℕ → Fin m → ℝ)
    (k : ℕ) (b : Block) (j : Fin (ℓ + 1)) : ℝ :=
  tiltedValue (f b) 0 0 (generatedPosition η w b (k + j.rev.val))

/-- The generated value histories overlap with exactly the shift required by
certificate descent. -/
theorem generatedValues_shift {m ℓ : ℕ}
    (f : Block → (Fin m → ℝ) → EReal) (η w : ℕ → Fin m → ℝ)
    (k : ℕ) (b : Block) (j : Fin ℓ) :
    generatedValues f η w (k + 1) b j.succ = generatedValues f η w k b j.castSucc := by
  simp only [generatedValues, Fin.rev_succ, Fin.rev_castSucc, Fin.val_castSucc,
    Fin.val_succ]
  congr 2 <;> omega

end ADMM.ConvergenceProof
