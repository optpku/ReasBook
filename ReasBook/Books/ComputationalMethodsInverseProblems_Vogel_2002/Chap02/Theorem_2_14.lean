/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_7.WellPosed
import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_17.Pseudoinverse
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

public section

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- A compact operator with closed range has finite-dimensional range. -/
theorem finiteDimensional_range_of_isCompactOperator_of_isClosed_range
    (K : H₁ →L[𝕜] H₂) (hK : IsCompactOperator K) (hclosed : IsClosed (Set.range K)) :
    FiniteDimensional 𝕜 K.range := by
  let Kr : H₁ →L[𝕜] K.range := K.codRestrict K.range (fun x ↦ ⟨x, rfl⟩)
  let Kp : H₂ →L[𝕜] H₁ := K.pseudoInverseOfClosedRange hclosed
  have hKr : IsCompactOperator Kr := by
    exact hK.codRestrict (fun x ↦ show K x ∈ K.range from ⟨x, rfl⟩) hclosed
  have h_id :
      IsCompactOperator (ContinuousLinearMap.id 𝕜 K.range) := by
    have h_comp :
        IsCompactOperator (Kr.comp (Kp.comp K.range.subtypeL)) :=
      hKr.comp_clm (Kp.comp K.range.subtypeL)
    have h_comp_eq :
        Kr.comp (Kp.comp K.range.subtypeL) =
          ContinuousLinearMap.id 𝕜 K.range := by
      ext y
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        ContinuousLinearMap.id_apply]
      have h_pseudo : Kp ↑y = (K.kerOrthogonalEquivRange.symm y : H₁) := by
        simpa [Kp] using
          pseudoInverseOfClosedRange_apply_of_mem_range K hclosed y.property
      rw [h_pseudo]
      simpa [Kr] using congrArg Subtype.val (K.kerOrthogonalEquivRange_symm_apply y)
    simpa [h_comp_eq] using h_comp
  exact
    (isCompactOperator_id_iff_finiteDimensional :
      IsCompactOperator (ContinuousLinearMap.id 𝕜 K.range) ↔ FiniteDimensional 𝕜 K.range).1 h_id

/-- Theorem 2.14 (1). A compact operator with infinite-dimensional range is not surjective. -/
theorem not_surjective_of_isCompactOperator_of_infiniteDimensional_range
    (K : H₁ →L[𝕜] H₂) (hK : IsCompactOperator K)
    (h_range_inf : ¬ FiniteDimensional 𝕜 K.range) :
    ¬ Function.Surjective K := by
  intro hsurj
  have hclosed : IsClosed (Set.range K) := by
    rw [Set.range_eq_univ.2 hsurj]
    exact isClosed_univ
  exact h_range_inf <|
    finiteDimensional_range_of_isCompactOperator_of_isClosed_range K hK hclosed

/-- Theorem 2.14 (2). A compact operator with infinite-dimensional range does not have closed
range. -/
theorem not_isClosed_range_of_isCompactOperator_of_infiniteDimensional_range
    (K : H₁ →L[𝕜] H₂) (hK : IsCompactOperator K)
    (h_range_inf : ¬ FiniteDimensional 𝕜 K.range) :
    ¬ IsClosed (Set.range K) := by
  intro hclosed
  exact h_range_inf <|
    finiteDimensional_range_of_isCompactOperator_of_isClosed_range K hK hclosed

section

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [DivisionRing 𝕜]
variable [TopologicalSpace H₁] [AddCommGroup H₁] [Module 𝕜 H₁]
variable [TopologicalSpace H₂] [AddCommGroup H₂] [Module 𝕜 H₂]

/-- Theorem 2.14 (3). On an infinite-dimensional `𝕜`-vector space, any continuous linear operator
with finite-dimensional range is not injective; in particular this applies to compact operators. -/
theorem not_injective_of_infiniteDimensional_of_finiteDimensional_range
    (K : H₁ →L[𝕜] H₂)
    (hH₁ : ¬ FiniteDimensional 𝕜 H₁)
    (h_range_fin : FiniteDimensional 𝕜 K.range) :
    ¬ Function.Injective K := by
  intro h_inj
  have h_rangeRestrict_inj : Function.Injective K.rangeRestrict.toLinearMap := by
    simpa [ContinuousLinearMap.toLinearMap_rangeRestrict] using
      K.toLinearMap.injective_rangeRestrict_iff.2 h_inj
  exact hH₁ (FiniteDimensional.of_injective K.rangeRestrict.toLinearMap h_rangeRestrict_inj)

end

/-- Infinite-dimensional range for a compact operator forces ill-posedness. -/
theorem illPosed_of_isCompactOperator_of_infiniteDimensional_range
    (K : H₁ →L[𝕜] H₂) (hK : IsCompactOperator K)
    (h_range_inf : ¬ FiniteDimensional 𝕜 K.range) :
    OperatorEquation.illPosed K := by
  intro hWellPosed
  exact
    not_surjective_of_isCompactOperator_of_infiniteDimensional_range K hK h_range_inf
      hWellPosed.bijective.2

section

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [DivisionRing 𝕜]
variable [TopologicalSpace H₁] [AddCommGroup H₁] [Module 𝕜 H₁]
variable [TopologicalSpace H₂] [AddCommGroup H₂] [Module 𝕜 H₂]

/-- On an infinite-dimensional `𝕜`-vector space, finite-dimensional range forces ill-posedness for
a continuous linear operator; this recovers Theorem 2.14 for compact operators as a special case.
-/
theorem illPosed_of_infiniteDimensional_of_finiteDimensional_range
    (K : H₁ →L[𝕜] H₂)
    (hH₁ : ¬ FiniteDimensional 𝕜 H₁)
    (h_range_fin : FiniteDimensional 𝕜 K.range) :
    OperatorEquation.illPosed K := by
  intro hWellPosed
  exact
    not_injective_of_infiniteDimensional_of_finiteDimensional_range K hH₁ h_range_fin
      hWellPosed.bijective.1

end

end ContinuousLinearMap
