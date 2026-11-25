/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_25.ScalarResidual
public import Mathlib.Analysis.Normed.Operator.Basic

public section
noncomputable section
namespace TsvdDiscrepancy
universe u v
variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- TSVD discrepancy choice using the raw squared residual and the adjacent
integer threshold rule. With mode variance `σ²/n`, the total noise threshold is
`σ²`; dividing the residual by `n` again would give the wrong scale. -/
@[expose] def IsDiscrepancyChoiceAt
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (σ : ℝ) (n m : ℕ) : Prop :=
  IsResidualDiscrepancyChoiceAt
    (fun n m ↦ ‖K n (Rtsvd n m (d n)) - d n‖ ^ 2) σ n m

/-- The pointwise characterization of the corrected discrepancy rule. -/
theorem isDiscrepancyChoiceAt_iff
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (σ : ℝ) (n m : ℕ) :
    IsDiscrepancyChoiceAt K d Rtsvd σ n m ↔
      m ≤ n ∧ ‖K n (Rtsvd n m (d n)) - d n‖ ^ 2 ≤ σ ^ 2 ∧
        (0 < m → σ ^ 2 ≤ ‖K n (Rtsvd n (m - 1) (d n)) - d n‖ ^ 2) := by
  rfl

/-- Asymptotic discrepancy families satisfy the crossing rule beyond a finite
prefix. The scalar spectral model has such admissible choices eventually,
as proved by `exists_discrepancyChoice_eventually`. -/
@[expose] def IsDiscrepancyChoiceFamily
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (σ : ℝ) (m : ℕ → ℕ) : Prop :=
  ∀ᶠ n in Filter.atTop, IsDiscrepancyChoiceAt K d Rtsvd σ n (m n)

/-- The defining characterization of a discrepancy family. -/
theorem isDiscrepancyChoiceFamily_iff
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (σ : ℝ) (m : ℕ → ℕ) :
    IsDiscrepancyChoiceFamily K d Rtsvd σ m ↔
      ∀ᶠ n in Filter.atTop, IsDiscrepancyChoiceAt K d Rtsvd σ n (m n) := by
  rfl
end TsvdDiscrepancy
