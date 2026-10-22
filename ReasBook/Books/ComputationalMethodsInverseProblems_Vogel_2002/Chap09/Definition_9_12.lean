/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_2.IndexSets
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_9.CriticalPoint
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Remark_9_11.StrictComplementarity

public section

noncomputable section

/- Definition 9.12 (1). A nondegenerate critical point for `(9.16)` is
formalized by `NonnegativeOrthant.StrictComplementarity`. -/
#check NonnegativeOrthant.StrictComplementarity

namespace NonnegativeOrthant

variable {n : ℕ}
variable {J : EuclideanSpace ℝ (Fin n) → ℝ}
variable {f : EuclideanSpace ℝ (Fin n)}

/-- Under `IsCriticalPoint J f`, failure of strict complementarity is witnessed
by a coordinate where both `f` and `gradient J f` vanish. -/
theorem exists_eq_zero_and_gradient_eq_zero_of_not_strictComplementarity
    (hcrit : IsCriticalPoint J f)
    (hnot : ¬ StrictComplementarity J f) :
    ∃ i : Fin n, f i = 0 ∧ gradient J f i = 0 := by
  classical
  rw [strictComplementarity_iff] at hnot
  push Not at hnot
  rcases hnot with ⟨i, hfi, hgrad⟩
  refine ⟨i, hfi, le_antisymm hgrad (hcrit.gradientNonneg i)⟩

/-- A coordinate with `f i = 0` and `gradient J f i = 0` rules out strict
complementarity. -/
theorem not_strictComplementarity_of_exists_eq_zero_and_gradient_eq_zero
    (hzero : ∃ i : Fin n, f i = 0 ∧ gradient J f i = 0) :
    ¬ StrictComplementarity J f := by
  rintro hsc
  rcases hzero with ⟨i, hfi, hgrad⟩
  have hpos : 0 < gradient J f i := pos_of_eq_zero hsc hfi
  simp [hgrad] at hpos

/-- Definition 9.12 (2). Under `IsCriticalPoint J f`, degeneracy is equivalent
to the existence of a coordinate `i` with `f i = 0` and `gradient J f i = 0`. -/
theorem not_strictComplementarity_iff_exists_eq_zero_and_gradient_eq_zero
    (hcrit : IsCriticalPoint J f) :
    ¬ StrictComplementarity J f ↔
      ∃ i : Fin n, f i = 0 ∧ gradient J f i = 0 := by
  constructor
  · exact exists_eq_zero_and_gradient_eq_zero_of_not_strictComplementarity hcrit
  · exact not_strictComplementarity_of_exists_eq_zero_and_gradient_eq_zero

/-- Under `IsCriticalPoint J f`, degeneracy is equivalent to the existence of an
active index whose gradient component vanishes. This is the active-set form of
Definition 9.12 used when interpreting active-index histograms. -/
theorem not_strictComplementarity_iff_exists_mem_active_and_gradient_eq_zero
    (hcrit : IsCriticalPoint J f) :
    ¬ StrictComplementarity J f ↔
      ∃ i : Fin n, i ∈ ActiveSet.active (fun j g ↦ g j) f ∧ gradient J f i = 0 := by
  rw [not_strictComplementarity_iff_exists_eq_zero_and_gradient_eq_zero hcrit]
  constructor
  · rintro ⟨i, hfi, hgrad⟩
    refine ⟨i, (ActiveSet.mem_active (fun j g ↦ g j) f i).2 hfi, hgrad⟩
  · rintro ⟨i, hi, hgrad⟩
    exact ⟨i, (ActiveSet.mem_active (fun j g ↦ g j) f i).1 hi, hgrad⟩

end NonnegativeOrthant
