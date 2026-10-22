/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6.EstimationError

public section

noncomputable section

namespace TsvdEstimation

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The source admissible truncation-index family `𝒵(n)` used for TSVD in
Proposition 7.15. -/
@[expose] def admissibleIndexSet : ℕ → Set ℕ :=
  fun n ↦ Set.Icc 0 n

namespace Notation

/-- Scoped notation for the Chapter 7 admissible truncation-index family `𝒵`. -/
scoped notation "𝒵" => admissibleIndexSet

/-- Scoped notation for the `n`th Chapter 7 admissible truncation-index set
`𝒵(n)`. -/
scoped notation "𝒵(" n ")" => admissibleIndexSet n

end Notation

open scoped TsvdEstimation.Notation

/-- Membership in `𝒵(n)` is the interval condition
`0 ≤ m ∧ m ≤ n`. -/
@[simp] theorem mem_admissibleIndexSet_iff (n m : ℕ) :
    m ∈ 𝒵(n) ↔ m ∈ Set.Icc 0 n := by
  rfl

/-- The Chapter 7 TSVD expected squared estimation-error objective as a
function of the truncation index `m` at fixed data size `n`. -/
@[expose] def expectedSqErrorObjective
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F) : ℕ → ℕ → ℝ :=
  fun n m ↦ FilterRegularization.expectedSqEstimationError μ (R n m) (K n) fTrue (η n)

/-- Evaluate `expectedSqErrorObjective` at a fixed data size and truncation
index. -/
@[simp] theorem expectedSqErrorObjective_apply
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F) (n m : ℕ) :
    expectedSqErrorObjective μ K R fTrue η n m =
      FilterRegularization.expectedSqEstimationError μ (R n m) (K n) fTrue (η n) := by
  rfl

end

end TsvdEstimation
