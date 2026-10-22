/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace (toDual toDualMap)
open WithLp (ofLp toLp)
open scoped Gradient Pointwise

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 3.19 is `source-facing`: it defines the stationary-point predicate for the
`ℓ₁`-regularized problem. The owner abstraction in this domain is the chapter composite
stationarity predicate `is_stationary_point`; the `ℓ₁` subdifferential expression only appears in
the source-facing specification theorem below. -/

recall is_differentiable_at
recall is_stationary_point
recall subdifferential
recall subdifferentialAt
recall subdifferentialAt_const_mul_eq_smul_subdifferentialAt

-- Semantic recall note: `lean_leansearch` returned only generic differentiability/gradient
-- declarations, so this item stays source-facing around the chapter stationary-point API.

private theorem l1Norm_convexOn : ConvexOn ℝ Set.univ (fun y : E ↦ ‖y‖₁) := by
  let l1Map : E →ₗ[ℝ] WithLp (1 : ENNReal) (Fin n → ℝ) :=
    ((WithLp.linearEquiv (1 : ENNReal) ℝ (Fin n → ℝ)).symm.toLinearMap).comp
      ((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin n → ℝ)).toLinearMap)
  have hconv : ConvexOn ℝ Set.univ (fun y : E ↦ ‖l1Map y‖) := by
    simpa using convexOn_univ_norm.comp_linearMap l1Map
  simpa [EuclideanSpace.l1Norm, l1Map] using hconv

/-- Definition 3.19: a point `x` is stationary for the `ℓ₁`-regularized
problem `min_y f y + λ ‖y‖₁` when the chapter stationary-point predicate
is specialized to the nonsmooth term `y ↦ ((lam * ‖y‖₁ : ℝ) : EReal)`.
The companion theorems below expose the owner-subdifferential formulation,
and then the scaled and coordinatewise corollaries under `0 ≤ lam`. -/
def is_l1_regularized_stationary_point (f : E → EReal) (lam : ℝ) (x : E) : Prop :=
  is_stationary_point f (fun y ↦ ((lam * ‖y‖₁ : ℝ) : EReal)) x

/-- The predicate `is_l1_regularized_stationary_point` is definitionally the
chapter stationary-point predicate for the `ℓ₁`-regularized objective. -/
theorem is_l1_regularized_stationary_point_def
    {f : E → EReal} {lam : ℝ} {x : E} :
    is_l1_regularized_stationary_point f lam x ↔
      is_stationary_point f (fun y ↦ ((lam * ‖y‖₁ : ℝ) : EReal)) x :=
  Iff.rfl

/-- The owner proposition `is_l1_regularized_stationary_point` is equivalent to the chapter
differentiability condition together with the owner-subdifferential formulation of
`-∇ f(x) ∈ ∂ (y ↦ lam * ‖y‖₁) (x)`. -/
@[simp] theorem is_l1_regularized_stationary_point_iff
    {f : E → EReal} {lam : ℝ} {x : E} :
    is_l1_regularized_stationary_point f lam x ↔
      is_differentiable_at f x ∧
        (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : Module.Dual ℝ E) ∈
          subdifferential (fun y ↦ ((lam * ‖y‖₁ : ℝ) : EReal)) x := by
  rw [is_l1_regularized_stationary_point_def, is_stationary_point_iff]

/-- Under `0 ≤ lam`, the owner subdifferential formulation rewrites to the scaled real-valued
`ℓ₁`-subdifferential statement `-∇ f(x) ∈ lam • ∂ ‖·‖₁ (x)`. -/
theorem is_l1_regularized_stationary_point_iff_smul_subdifferentialAt
    {f : E → EReal} {lam : ℝ} (hlam : 0 ≤ lam) {x : E} :
    is_l1_regularized_stationary_point f lam x ↔
      is_differentiable_at f x ∧
        (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : StrongDual ℝ E) ∈
          lam • subdifferentialAt (fun y : E ↦ ‖y‖₁) x := by
  have hscaled :
      subdifferentialAt (fun y : E ↦ lam * ‖y‖₁) x =
        lam • subdifferentialAt (fun y : E ↦ ‖y‖₁) x :=
    subdifferentialAt_const_mul_eq_smul_subdifferentialAt lam hlam l1Norm_convexOn
  rw [is_l1_regularized_stationary_point_iff]
  constructor
  · rintro ⟨hdiff, hsub⟩
    refine ⟨hdiff, ?_⟩
    have hsub' :
        (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : StrongDual ℝ E) ∈
          subdifferentialAt (fun y : E ↦ lam * ‖y‖₁) x := by
      simpa [subdifferentialAt] using hsub
    exact hscaled ▸ hsub'
  · rintro ⟨hdiff, hsub⟩
    refine ⟨hdiff, ?_⟩
    have hsub' :
        (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : StrongDual ℝ E) ∈
          subdifferentialAt (fun y : E ↦ lam * ‖y‖₁) x := by
      exact hscaled.symm ▸ hsub
    simpa [subdifferentialAt] using hsub'

/-- Under `0 ≤ lam`, the `ℓ₁`-regularized stationarity condition is equivalent to the
coordinatewise sign conditions of `(3.85)`, obtained by combining the owner stationarity predicate
with Proposition 3.17's description of the `ℓ₁` subdifferential. -/
theorem is_l1_regularized_stationary_point_iff_coordinatewise
    {f : E → EReal} {lam : ℝ} (hlam : 0 ≤ lam) {x : E} :
    is_l1_regularized_stationary_point f lam x ↔
      is_differentiable_at f x ∧
        ∀ i,
          (0 < x i → (∇ (fun y ↦ (f y).toReal) x) i = -lam) ∧
            (x i < 0 → (∇ (fun y ↦ (f y).toReal) x) i = lam) ∧
              (x i = 0 → (∇ (fun y ↦ (f y).toReal) x) i ∈ Set.Icc (-lam) lam) := by
  let gradx : E := ∇ (fun y ↦ (f y).toReal) x
  rw [is_l1_regularized_stationary_point_iff_smul_subdifferentialAt hlam]
  constructor
  · rintro ⟨hdiff, hsub⟩
    refine ⟨hdiff, ?_⟩
    rw [Set.mem_smul_set] at hsub
    rcases hsub with ⟨φ, hφ, hEqφ⟩
    rcases (toDual ℝ E).surjective φ with ⟨w, rfl⟩
    have hw : w ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖y‖₁) x := by
      simpa [mem_euclideanSubdifferentialAt_iff,
        InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hφ
    have hwEq : lam • w = -gradx := by
      apply (toDualMap ℝ E).injective
      simpa [gradx, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hEqφ
    have hwcoord := mem_euclideanSubdifferentialAt_l1_norm_iff.1 hw
    intro i
    constructor
    · intro hxi
      have hsign : w i = 1 := by
        have hi : x i ≠ 0 := ne_of_gt hxi
        simpa [Real.sign_of_pos hxi] using hwcoord.1 i (by simpa using hi)
      have hi : lam * w i = -(gradx i) := by
        have hEval := congrArg (fun v : E ↦ v i) hwEq
        simpa [Pi.smul_apply] using hEval
      rw [hsign] at hi
      have hgrad_i : gradx i = -lam := by linarith
      simpa [gradx] using hgrad_i
    · constructor
      · intro hxi
        have hsign : w i = -1 := by
          have hi : x i ≠ 0 := ne_of_lt hxi
          simpa [Real.sign_of_neg hxi] using hwcoord.1 i (by simpa using hi)
        have hi : lam * w i = -(gradx i) := by
          have hEval := congrArg (fun v : E ↦ v i) hwEq
          simpa [Pi.smul_apply] using hEval
        rw [hsign] at hi
        have hgrad_i : gradx i = lam := by linarith
        simpa [gradx] using hgrad_i
      · intro hxi
        have hwbound : |w i| ≤ 1 := by
          simpa using hwcoord.2 i (by simpa using hxi)
        have hi : lam * w i = -(gradx i) := by
          have hEval := congrArg (fun v : E ↦ v i) hwEq
          simpa [Pi.smul_apply] using hEval
        have hgrad_abs : |gradx i| ≤ lam := by
          calc
            |gradx i| = |-(gradx i)| := by rw [abs_neg]
            _ = |lam * w i| := by rw [← hi]
            _ = lam * |w i| := by rw [abs_mul, abs_of_nonneg hlam]
            _ ≤ lam * 1 := mul_le_mul_of_nonneg_left hwbound hlam
            _ = lam := by ring
        exact Set.mem_Icc.mpr (abs_le.mp hgrad_abs)
  · rintro ⟨hdiff, hcoord⟩
    refine ⟨hdiff, ?_⟩
    by_cases hlam0 : lam = 0
    · have hgrad_zero : gradx = 0 := by
        ext i
        by_cases hxi_pos : 0 < x i
        · simpa [gradx, hlam0] using (hcoord i).1 hxi_pos
        · by_cases hxi_neg : x i < 0
          · simpa [gradx, hlam0] using (hcoord i).2.1 hxi_neg
          · have hxi_zero : x i = 0 := by linarith
            have hmem : gradx i ∈ Set.Icc (-lam) lam := by
              simpa [gradx] using (hcoord i).2.2 hxi_zero
            have hzero : gradx i = 0 := by
              have hle := (Set.mem_Icc.mp hmem).2
              have hge := (Set.mem_Icc.mp hmem).1
              simpa [hlam0] using le_antisymm hle (by simpa [hlam0] using hge)
            exact hzero
      have hw : toLp 2 (sgn (ofLp x)) ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖y‖₁) x := by
        rw [subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints]
        exact ⟨sgn (ofLp x), sign_vector_mem_l1CoordinateSubgradientVectors (ofLp x), by simp⟩
      have hw' :
          toDualMap ℝ E (toLp 2 (sgn (ofLp x))) ∈
            subdifferentialAt (fun y : E ↦ ‖y‖₁) x := by
        simpa [mem_euclideanSubdifferentialAt_iff] using hw
      refine Set.mem_smul_set.mpr ?_
      refine ⟨toDualMap ℝ E (toLp 2 (sgn (ofLp x))), hw', ?_⟩
      simp [hlam0, hgrad_zero, gradx, InnerProductSpace.toDual_apply_eq_toDualMap_apply]
    · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam0)
      let w : E := (-lam⁻¹) • gradx
      have hw : w ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖y‖₁) x := by
        rw [mem_euclideanSubdifferentialAt_l1_norm_iff]
        constructor
        · intro i hxi
          have hxi' : x i ≠ 0 := by simpa using hxi
          rcases lt_or_gt_of_ne hxi' with hxi_neg | hxi_pos
          · have hgrad_i : gradx i = lam := by
              simpa [gradx] using (hcoord i).2.1 hxi_neg
            calc
              w i = (-lam⁻¹) * gradx i := by simp [w]
              _ = -1 := by rw [hgrad_i]; field_simp [hlam0]
              _ = Real.sign (x i) := by simp [Real.sign_of_neg hxi_neg]
          · have hgrad_i : gradx i = -lam := by
              simpa [gradx] using (hcoord i).1 hxi_pos
            calc
              w i = (-lam⁻¹) * gradx i := by simp [w]
              _ = 1 := by rw [hgrad_i]; field_simp [hlam0]
              _ = Real.sign (x i) := by simp [Real.sign_of_pos hxi_pos]
        · intro i hxi
          have hmem : gradx i ∈ Set.Icc (-lam) lam := by
            simpa [gradx] using (hcoord i).2.2 (by simpa using hxi)
          have hgrad_abs : |gradx i| ≤ lam := by
            exact abs_le.mpr (Set.mem_Icc.mp hmem)
          calc
            |w i| = |(-lam⁻¹) * gradx i| := by simp [w]
            _ = lam⁻¹ * |gradx i| := by rw [abs_mul, abs_neg, abs_of_nonneg (inv_nonneg.2 hlam)]
            _ ≤ lam⁻¹ * lam := mul_le_mul_of_nonneg_left hgrad_abs (inv_nonneg.2 hlam)
            _ = 1 := by field_simp [hlam0]
      have hw' :
          toDualMap ℝ E w ∈
            subdifferentialAt (fun y : E ↦ ‖y‖₁) x := by
        simpa [mem_euclideanSubdifferentialAt_iff] using hw
      have hwEq : lam • w = -gradx := by
        ext i
        calc
          (lam • w) i = lam * ((-lam⁻¹) * gradx i) := by simp [w]
          _ = -gradx i := by field_simp [hlam0]
      refine Set.mem_smul_set.mpr ?_
      refine ⟨toDualMap ℝ E w, hw', ?_⟩
      simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using congrArg (toDualMap ℝ E) hwEq

end
