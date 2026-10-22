/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Objective

public section

noncomputable section

namespace TsvdDiscrepancy

universe u v

section

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exercise 7.20 / Theorem 7.25 support: at positive data size `n`, a TSVD
truncation index `m` is a discrepancy-principle choice when it lies in the
source admissible set `𝒵(n)` and satisfies the displayed discrepancy equation
`(7.88)`. -/
@[expose] def IsDiscrepancyChoiceAt
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (σ : ℝ) (n : ℕ+) (m : ℕ) : Prop :=
  m ∈ TsvdEstimation.admissibleIndexSet (n : ℕ) ∧
    ‖K n (Rtsvd n m (d n)) - d n‖ ^ 2 / (n : ℝ) = σ ^ 2

/-- The defining characterization of `IsDiscrepancyChoiceAt`. -/
theorem isDiscrepancyChoiceAt_iff
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (σ : ℝ) (n : ℕ+) (m : ℕ) :
    IsDiscrepancyChoiceAt K d Rtsvd σ n m ↔
      m ∈ TsvdEstimation.admissibleIndexSet (n : ℕ) ∧
        ‖K n (Rtsvd n m (d n)) - d n‖ ^ 2 / (n : ℝ) = σ ^ 2 := by
  rfl

/-- A TSVD discrepancy-choice family selects, for each positive data size, a
truncation index solving `(7.88)` on the admissible set `𝒵(n)`. -/
@[expose] def IsDiscrepancyChoiceFamily
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (σ : ℝ) (mDiscrep : ℕ → ℕ) : Prop :=
  ∀ n : ℕ+, IsDiscrepancyChoiceAt K d Rtsvd σ n (mDiscrep n)

/-- The defining pointwise characterization of `IsDiscrepancyChoiceFamily`. -/
theorem isDiscrepancyChoiceFamily_iff
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (σ : ℝ) (mDiscrep : ℕ → ℕ) :
    IsDiscrepancyChoiceFamily K d Rtsvd σ mDiscrep ↔
      ∀ n : ℕ+, IsDiscrepancyChoiceAt K d Rtsvd σ n (mDiscrep n) := by
  rfl

end

end TsvdDiscrepancy

end
