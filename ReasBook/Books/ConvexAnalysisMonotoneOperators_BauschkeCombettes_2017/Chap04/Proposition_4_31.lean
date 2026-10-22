/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_4

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

open EuclideanGeometry
open scoped InnerProductSpace

universe u

section

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- The Douglas--Rachford combination `T₁ (2T₂ - Id) + Id - T₂` of two self-maps. -/
def douglasRachfordOperator (T₁ T₂ : H → H) : H → H :=
  fun x ↦ T₁ ((2 : ℝ) • T₂ x - x) + x - T₂ x

/-- The Douglas--Rachford operator acts by `x ↦ T₁ (2 • T₂ x - x) + x - T₂ x`. -/
theorem douglasRachfordOperator_apply (T₁ T₂ : H → H) (x : H) :
    douglasRachfordOperator T₁ T₂ x = T₁ ((2 : ℝ) • T₂ x - x) + x - T₂ x := by
  rfl

/-- Proposition 4.31 (1): for any self-maps `T₁` and `T₂`, the reflector of
`T = T₁ (2T₂ - Id) + Id - T₂` is the composition `(2T₁ - Id) ∘ (2T₂ - Id)`. -/
theorem reflected_douglasRachfordOperator_eq_comp_reflectedMap
    {T₁ T₂ : H → H} :
    (fun x ↦ (2 : ℝ) • douglasRachfordOperator T₁ T₂ x - x) =
      (fun x ↦ (2 : ℝ) • T₁ x - x) ∘ fun x ↦ (2 : ℝ) • T₂ x - x := by
  funext x
  simp [douglasRachfordOperator, two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- On the whole space, firm nonexpansiveness is equivalent to the canonical
`LipschitzWith 1` condition for the reflector `x ↦ 2 • T x - x`. -/
private theorem firmlyNonexpansive_iff_lipschitzWith_one_reflectedMap {T : H → H} :
    FirmlyNonexpansive T ↔ LipschitzWith 1 (fun x ↦ (2 : ℝ) • T x - x) := by
  rw [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ]
  rw [← reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn (Set.univ : Set H)
    (fun x : Set.univ ↦ T x)]
  constructor
  · intro hT
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [reflectedMap, Subtype.dist_eq, dist_eq_norm, one_mul] using
      hT ⟨x, by simp⟩ ⟨y, by simp⟩
  · intro hR x y
    simpa [reflectedMap, Subtype.dist_eq, dist_eq_norm, one_mul] using
      hR.dist_le_mul x y

/-- Proposition 4.31 (2): the Douglas--Rachford operator associated to firmly nonexpansive `T₁`
and `T₂` is firmly nonexpansive. -/
theorem douglasRachfordOperator_firmlyNonexpansive
    {T₁ T₂ : H → H}
    (hT₁ : FirmlyNonexpansive T₁) (hT₂ : FirmlyNonexpansive T₂) :
    FirmlyNonexpansive (douglasRachfordOperator T₁ T₂) := by
  rw [firmlyNonexpansive_iff_lipschitzWith_one_reflectedMap]
  have hR₁ :
      LipschitzWith 1 (fun x ↦ (2 : ℝ) • T₁ x - x) :=
    firmlyNonexpansive_iff_lipschitzWith_one_reflectedMap.1 hT₁
  have hR₂ :
      LipschitzWith 1 (fun x ↦ (2 : ℝ) • T₂ x - x) :=
    firmlyNonexpansive_iff_lipschitzWith_one_reflectedMap.1 hT₂
  simpa [reflected_douglasRachfordOperator_eq_comp_reflectedMap] using hR₁.comp hR₂

end

section

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [NoZeroSMulDivisors ℝ H]

/-- A self-map and its reflector `x ↦ 2 • T x - x` have the same fixed points. -/
private lemma fixedPoints_reflectedMap_eq_fixedPoints
    (T : H → H) :
    Function.fixedPoints (fun x ↦ (2 : ℝ) • T x - x) = Function.fixedPoints T := by
  ext y
  constructor
  · intro hy
    rw [Function.mem_fixedPoints_iff] at hy ⊢
    change (2 : ℝ) • T y - y = y at hy
    have hzero : (2 : ℝ) • (T y - y) = 0 := by
      calc
        (2 : ℝ) • (T y - y) = (2 : ℝ) • T y - (2 : ℝ) • y := by
          rw [smul_sub]
        _ = ((2 : ℝ) • T y - y) - y := by
          simp [two_smul, sub_eq_add_neg, add_assoc]
        _ = 0 := by
          rw [hy, sub_self]
    rcases smul_eq_zero.mp hzero with htwo | hsub
    · norm_num at htwo
    · exact sub_eq_zero.mp hsub
  · intro hy
    rw [Function.mem_fixedPoints_iff] at hy ⊢
    change T y = y at hy
    rw [hy]
    simp [two_smul]

/-- Proposition 4.31 (3): for any self-maps `T₁` and `T₂`, the fixed points of the
Douglas--Rachford operator coincide with the fixed points of the composed reflected maps
`(2T₁ - Id) ∘ (2T₂ - Id)`. -/
theorem fixedPoints_douglasRachfordOperator_eq_fixedPoints_reflected_comp
    {T₁ T₂ : H → H} :
    Function.fixedPoints (douglasRachfordOperator T₁ T₂) =
      Function.fixedPoints ((fun x ↦ (2 : ℝ) • T₁ x - x) ∘ fun x ↦ (2 : ℝ) • T₂ x - x) := by
  calc
    Function.fixedPoints (douglasRachfordOperator T₁ T₂) =
        Function.fixedPoints (fun x ↦ (2 : ℝ) • douglasRachfordOperator T₁ T₂ x - x) := by
          symm
          exact fixedPoints_reflectedMap_eq_fixedPoints _
    _ =
        Function.fixedPoints ((fun x ↦ (2 : ℝ) • T₁ x - x) ∘ fun x ↦ (2 : ℝ) • T₂ x - x) := by
          rw [reflected_douglasRachfordOperator_eq_comp_reflectedMap]

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 4.31 (4): if `T₁` is the orthogonal projection onto an affine subspace `A`, then
the fixed points of the corresponding Douglas--Rachford operator are exactly the points where
`T₁` and `T₂` agree. -/
theorem fixedPoints_douglasRachfordOperator_eq_agreement_set_of_affine_projector
    {A : AffineSubspace ℝ H} [Nonempty A] [A.direction.HasOrthogonalProjection] {T₂ : H → H} :
    Function.fixedPoints
        (douglasRachfordOperator (fun x ↦ (orthogonalProjection A x : H)) T₂) =
      {x : H | (orthogonalProjection A x : H) = T₂ x} := by
  ext x
  rw [Function.mem_fixedPoints_iff]
  change
    douglasRachfordOperator (fun z ↦ (orthogonalProjection A z : H)) T₂ x = x ↔
      (orthogonalProjection A x : H) = T₂ x
  constructor
  · intro hx
    have hproj : (orthogonalProjection A ((2 : ℝ) • T₂ x - x) : H) = T₂ x := by
      have hdx : (orthogonalProjection A ((2 : ℝ) • T₂ x - x) : H) + x - T₂ x = x := by
        simpa [douglasRachfordOperator] using hx
      have hsub : (orthogonalProjection A ((2 : ℝ) • T₂ x - x) : H) + x = T₂ x + x := by
        exact sub_eq_iff_eq_add'.mp hdx
      exact add_right_cancel hsub
    have hchar :
        T₂ x ∈ (A : Set H) ∧ ((2 : ℝ) • T₂ x - x) - T₂ x ∈ A.directionᗮ := by
      exact (coe_orthogonalProjection_eq_iff_mem).mp hproj
    refine (coe_orthogonalProjection_eq_iff_mem).2 ?_
    rcases hchar with ⟨hyA, horth⟩
    refine ⟨hyA, ?_⟩
    have hneg : -(((2 : ℝ) • T₂ x - x) - T₂ x) ∈ A.directionᗮ := Submodule.neg_mem _ horth
    simpa [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg
  · intro hx
    have hxchar : T₂ x ∈ (A : Set H) ∧ x - T₂ x ∈ A.directionᗮ := by
      exact (coe_orthogonalProjection_eq_iff_mem).mp hx
    have hproj : (orthogonalProjection A ((2 : ℝ) • T₂ x - x) : H) = T₂ x := by
      refine (coe_orthogonalProjection_eq_iff_mem).2 ?_
      rcases hxchar with ⟨hyA, horth⟩
      refine ⟨hyA, ?_⟩
      have hneg : -(x - T₂ x) ∈ A.directionᗮ := Submodule.neg_mem _ horth
      simpa [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg
    simp [douglasRachfordOperator, hproj]

end
