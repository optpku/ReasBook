/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Objective
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

noncomputable section

namespace TsvdGcv

open scoped TsvdEstimation.Notation

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The denominator-valid TSVD truncation indices for expected GCV at data size
`n`, obtained by restricting the source admissible set `𝒵(n)` to the indices
with `m < n`. This excludes the singular endpoint where the GCV denominator
vanishes. -/
@[expose] def gcvAdmissibleIndexSet : ℕ → Set ℕ :=
  fun n ↦ {m | m ∈ 𝒵(n) ∧ m < n}

/-- Membership in `gcvAdmissibleIndexSet n` means membership in the source
TSVD admissible set together with the denominator-valid inequality `m < n`. -/
@[simp] theorem mem_gcvAdmissibleIndexSet_iff (n m : ℕ) :
    m ∈ gcvAdmissibleIndexSet n ↔
      m ∈ 𝒵(n) ∧ m < n := by
  -- Unfold the owned admissible-set wrapper once to expose its pair of
  -- defining side conditions.
  rfl

/-- The TSVD GCV-valid admissible set is contained in the source admissible set
`𝒵(n)`. -/
theorem gcvAdmissibleIndexSet_subset_admissibleIndexSet (n : ℕ) :
    gcvAdmissibleIndexSet n ⊆ 𝒵(n) := by
  -- Membership in the GCV-valid set already contains the source admissibility
  -- component.
  intro m hm
  exact (mem_gcvAdmissibleIndexSet_iff n m).1 hm |>.1

/-- The concrete `n`-indexed expected GCV objective for a TSVD reconstruction
family `R n m`, written as the expected normalized squared residual divided by
the TSVD complement-trace factor `(1 - m / n)^2`. -/
@[expose] def expectedObjective
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F) :
    ℕ → ℕ → ℝ :=
  fun n m ↦
    (∫ ω, ‖K n (R n m (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 / (n : ℝ) ∂μ) /
      (1 - (m : ℝ) / (n : ℝ)) ^ 2

/-- The defining formula for `TsvdGcv.expectedObjective`. -/
@[simp] theorem expectedObjective_apply
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F)
    (n m : ℕ) :
    expectedObjective μ K R fTrue η n m =
      (∫ ω, ‖K n (R n m (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 / (n : ℝ) ∂μ) /
        (1 - (m : ℝ) / (n : ℝ)) ^ 2 := by
  -- The expected GCV objective is defined by this concrete residual quotient.
  rfl

end

end TsvdGcv
