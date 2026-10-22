/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_12
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Lemma_2_4
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Proposition_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped Pointwise

section

variable {ι κ : Type*} [Fintype κ]

/-- The affine feasible set cut out by the linear equations `B x = b`, viewed as the fiber of the
matrix linear map over `b`. -/
def affine_linear_constraint_set (B : Matrix ι κ ℝ) (b : ι → ℝ) : Set (κ → ℝ) :=
  B.mulVecLin ⁻¹' {b}

/-- Membership in `affine_linear_constraint_set B b` means satisfying the linear system
`B x = b`. -/
@[simp] theorem mem_affine_linear_constraint_set (B : Matrix ι κ ℝ) (b : ι → ℝ) (x : κ → ℝ) :
    x ∈ affine_linear_constraint_set B b ↔ B *ᵥ x = b := by
  simp [affine_linear_constraint_set]

/-- The homogeneous constraint set `ker B = {x | B x = 0}`, realized as the kernel of the matrix
linear map. -/
def homogeneous_linear_constraint_set (B : Matrix ι κ ℝ) : Set (κ → ℝ) :=
  LinearMap.ker B.mulVecLin

/-- Membership in `homogeneous_linear_constraint_set B` means solving the homogeneous system
`B x = 0`. -/
@[simp] theorem mem_homogeneous_linear_constraint_set (B : Matrix ι κ ℝ) (x : κ → ℝ) :
    x ∈ homogeneous_linear_constraint_set B ↔ B *ᵥ x = 0 := by
  simp [homogeneous_linear_constraint_set]

/-- Helper for Example 2.8: a nonempty affine fiber `B x = b` is the translate of the kernel
`B z = 0` by any chosen solution `x₀`. -/
private theorem affineLinearConstraintSet_eq_singleton_add_homogeneous
    (B : Matrix ι κ ℝ) (b : ι → ℝ) (x₀ : κ → ℝ)
    (hx₀ : x₀ ∈ affine_linear_constraint_set B b) :
    affine_linear_constraint_set B b =
      ({x₀} : Set (κ → ℝ)) + homogeneous_linear_constraint_set B := by
  have hx₀Eq : B *ᵥ x₀ = b := (mem_affine_linear_constraint_set B b x₀).1 hx₀
  ext x
  constructor
  · intro hx
    -- Rewrite a feasible point as the base point `x₀` plus a kernel vector.
    refine Set.mem_add.2 ⟨x₀, by simp, x - x₀, ?_, ?_⟩
    · rw [mem_homogeneous_linear_constraint_set]
      -- Subtract the equations `B x = b` and `B x₀ = b` to land in the kernel.
      have hxEq : B *ᵥ x = b := (mem_affine_linear_constraint_set B b x).1 hx
      have hx₀Eq : B *ᵥ x₀ = b := (mem_affine_linear_constraint_set B b x₀).1 hx₀
      calc
        B *ᵥ (x - x₀) = B *ᵥ x - B *ᵥ x₀ := by rw [Matrix.mulVec_sub]
        _ = b - b := by rw [hxEq, hx₀Eq]
        _ = 0 := sub_self b
    · ext i
      simp [sub_eq_add_neg]
  · intro hx
    rcases Set.mem_add.1 hx with ⟨u, hu, z, hz, rfl⟩
    rcases Set.mem_singleton_iff.1 hu with rfl
    rw [mem_affine_linear_constraint_set]
    -- Adding a kernel vector to a chosen solution preserves feasibility.
    rw [Matrix.mulVec_add, hx₀Eq, (mem_homogeneous_linear_constraint_set B z).1 hz, add_zero]

omit [Fintype κ] in
/-- Helper for Example 2.8: the support function of a singleton is evaluation at its unique
point. -/
private theorem supportFunction_singleton_eq_eval (x₀ : κ → ℝ) :
    support_function ({x₀} : Set (κ → ℝ)) = fun y ↦ (y x₀ : EReal) := by
  ext y
  -- The image set is a singleton, so its unique element is automatically greatest.
  have hmax :
      IsGreatest ((fun x : κ → ℝ ↦ (y x : EReal)) '' ({x₀} : Set (κ → ℝ))) (y x₀ : EReal) := by
    constructor
    · exact ⟨x₀, by simp, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      rcases Set.mem_singleton_iff.1 hx with rfl
      simp
  exact support_function_eq_of_isGreatest_image ({x₀} : Set (κ → ℝ)) y hmax

-- Proof sketch: every feasible point of `affine_linear_constraint_set B b` can be written as
-- `z + x₀` with `z ∈ homogeneous_linear_constraint_set B`, and conversely every such translate is
-- feasible because `x₀ ∈ affine_linear_constraint_set B b`. Rewriting the supremum in the
-- definition of `support_function`
-- along this translation gives the stated affine shift formula.
/-- Translating the homogeneous solution set by a particular solution `x₀` adds the evaluation
`y ↦ y x₀` to the support function. -/
theorem support_function_affine_linear_constraint_set_eq_eval_add_support_function_homogeneous
    (B : Matrix ι κ ℝ) (b : ι → ℝ) (x₀ : κ → ℝ)
    (hx₀ : x₀ ∈ affine_linear_constraint_set B b) :
    support_function (affine_linear_constraint_set B b) =
      fun y ↦ (y x₀ : EReal) + support_function (homogeneous_linear_constraint_set B) y := by
  -- Route correction: rewrite the affine fiber as a Minkowski sum before touching the support
  -- function, instead of manipulating the defining supremum directly.
  rw [affineLinearConstraintSet_eq_singleton_add_homogeneous B b x₀ hx₀]
  rw [support_function_minkowski_sum_eq_add]
  rw [supportFunction_singleton_eq_eval]
  rfl

end

section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local instance instDecidableEqι : DecidableEq ι := Classical.decEq ι
local instance instDecidableEqκ : DecidableEq κ := Classical.decEq κ

/-- The dual-space realization of `Range(Bᵀ)` under the canonical dot-product equivalence
`ℝⁿ ≃ (ℝⁿ)*`, obtained from the range of the transpose matrix linear map. -/
def transpose_range_dual (B : Matrix ι κ ℝ) : Set (Module.Dual ℝ (κ → ℝ)) :=
  dotProductEquiv ℝ κ '' (LinearMap.range Bᵀ.mulVecLin : Set (κ → ℝ))

/-- A dual vector lies in `transpose_range_dual B` exactly when it is represented by `Bᵀ *ᵥ z` for
some `z`. -/
@[simp] theorem mem_transpose_range_dual
    (B : Matrix ι κ ℝ) (y : Module.Dual ℝ (κ → ℝ)) :
    y ∈ transpose_range_dual B ↔ ∃ z : ι → ℝ, dotProductEquiv ℝ κ (Bᵀ *ᵥ z) = y := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rcases LinearMap.mem_range.1 hv with ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨Bᵀ *ᵥ z, LinearMap.mem_range.2 ⟨z, rfl⟩, rfl⟩

@[simp] theorem transpose_range_dual_eq_set_range (B : Matrix ι κ ℝ) :
    transpose_range_dual B =
      Set.range (((dotProductEquiv ℝ κ).toLinearMap).comp Bᵀ.mulVecLin) := by
  ext y
  simp [mem_transpose_range_dual, Set.mem_range, Matrix.mulVec_transpose]

/-- Helper for Example 2.8: on a submodule, the polar inequality is equivalent to vanishing. -/
private theorem polarCone_coeSubmodule_eq_dualAnnihilator
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (W : Submodule ℝ E) :
    polar_cone (W : Set E) = W.dualAnnihilator := by
  ext φ
  rw [mem_polar_cone]
  constructor
  · intro h
    change φ ∈ W.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    -- Test the polar inequality on `w` and `-w` to upgrade nonpositivity to equality.
    have hle : φ w ≤ 0 := h w hw
    have hneg : φ (-w) ≤ 0 := h (-w) (by simpa using W.neg_mem hw)
    have hge : 0 ≤ φ w := by
      have hneg' : -φ w ≤ 0 := by simpa using hneg
      exact neg_nonpos.mp hneg'
    exact le_antisymm hle hge
  · intro h
    change φ ∈ W.dualAnnihilator at h
    rw [Submodule.mem_dualAnnihilator] at h
    -- Vanishing on the submodule is stronger than the polar-cone inequality.
    intro w hw
    simp [h w hw]

/-- Helper for Example 2.8: transporting a Euclidean dual vector through `B.mulVecLin.dualMap`
corresponds to multiplying by `Bᵀ` before applying `dotProductEquiv`. -/
private theorem mulVecLin_dualMap_apply_dotProductEquiv
    (B : Matrix ι κ ℝ) (z : ι → ℝ) :
    B.mulVecLin.dualMap (dotProductEquiv ℝ ι z) =
      dotProductEquiv ℝ κ (Bᵀ *ᵥ z) := by
  apply LinearMap.ext
  intro x
  -- Compare both dual vectors by evaluating them on an arbitrary `x`.
  calc
    B.mulVecLin.dualMap (dotProductEquiv ℝ ι z) x
        = dotProduct z (B *ᵥ x) := by
            simp [LinearMap.dualMap_apply, dotProductEquiv]
    _ = dotProduct (Bᵀ *ᵥ z) x := by
          rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    _ = dotProductEquiv ℝ κ (Bᵀ *ᵥ z) x := by
          simp [dotProductEquiv]

/-- Helper for Example 2.8: the abstract dual-map range of `B.mulVecLin` is exactly the concrete
dual-space realization of `Range(Bᵀ)`. -/
private theorem range_mulVecLinDualMap_eq_transposeRangeDual
    (B : Matrix ι κ ℝ) :
    (LinearMap.range B.mulVecLin.dualMap : Set (Module.Dual ℝ (κ → ℝ))) =
      transpose_range_dual B := by
  ext y
  constructor
  · intro hy
    rcases LinearMap.mem_range.1 hy with ⟨φ, rfl⟩
    -- Represent the source dual vector by coordinates, then transport through the dual map.
    refine (mem_transpose_range_dual B _).2 ?_
    refine ⟨(dotProductEquiv ℝ ι).symm φ, ?_⟩
    simpa using
      (mulVecLin_dualMap_apply_dotProductEquiv (B := B) ((dotProductEquiv ℝ ι).symm φ)).symm
  · intro hy
    rcases (mem_transpose_range_dual B y).1 hy with ⟨z, rfl⟩
    -- A transpose-range witness gives an explicit preimage in the dual-map range.
    exact LinearMap.mem_range.2 ⟨dotProductEquiv ℝ ι z,
      mulVecLin_dualMap_apply_dotProductEquiv (B := B) z⟩

-- Proof sketch: identify a dual vector with its representing vector via
-- `dotProductEquiv ℝ κ`.
-- Then the textbook argument shows that a functional is nonpositive on every `x` with `B x = 0`
-- exactly when it is represented by some vector in `Range(Bᵀ)`.
/-- The polar cone of the homogeneous solution set `ker B` is the dual-space image of
`Range(Bᵀ)`. -/
theorem polar_cone_homogeneous_linear_constraint_set_eq_transpose_range_dual
    (B : Matrix ι κ ℝ) :
    polar_cone (homogeneous_linear_constraint_set B) = transpose_range_dual B := by
  -- Route correction: keep the proof abstract as `polar(submodule) = annihilator(submodule)` and
  -- only use the matrix transpose bridge at the last step.
  calc
    (polar_cone (homogeneous_linear_constraint_set B) :
        Set (Module.Dual ℝ (κ → ℝ)))
        = ((LinearMap.ker B.mulVecLin).dualAnnihilator :
            Set (Module.Dual ℝ (κ → ℝ))) := by
            rw [homogeneous_linear_constraint_set, polarCone_coeSubmodule_eq_dualAnnihilator]
            rfl
    _ = (LinearMap.range B.mulVecLin.dualMap : Set (Module.Dual ℝ (κ → ℝ))) := by
          rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    _ = transpose_range_dual B := range_mulVecLinDualMap_eq_transposeRangeDual B

-- Proof sketch: translate the feasible set by a chosen solution `x₀ ∈ affine_linear_constraint_set
-- B b`, so every `x` with `B x = b` becomes `z + x₀` with `B z = 0`; this is the preceding
-- translation formula. Then identify
-- `σ_{ker B}` with the indicator of the polar cone of `ker B`, and rewrite that polar cone using
-- `polar_cone_homogeneous_linear_constraint_set_eq_transpose_range_dual`.
/-- Example 2.8: if `x₀` satisfies `B x₀ = b`, then the support function of
`C = {x | B x = b}` is the affine functional `y ↦ y x₀` plus the indicator of the dual-space
realization of `Range(Bᵀ)`. -/
theorem support_function_affine_linear_constraint_set_eq_eval_add_indicator_transpose_range_dual
    (B : Matrix ι κ ℝ) (b : ι → ℝ) (x₀ : κ → ℝ)
    (hx₀ : x₀ ∈ affine_linear_constraint_set B b) :
    support_function (affine_linear_constraint_set B b) =
      fun y ↦ (y x₀ : EReal) + (δ_ (transpose_range_dual B)) y := by
  have hcone : IsCone (homogeneous_linear_constraint_set B) := by
    rw [isCone_iff_smul_mem]
    intro a _ha x hx
    rw [mem_homogeneous_linear_constraint_set] at hx ⊢
    -- The kernel of a linear map is closed under scalar multiplication.
    simp [Matrix.mulVec_smul, hx]
  have hzero : (0 : κ → ℝ) ∈ homogeneous_linear_constraint_set B := by
    -- The zero vector always solves the homogeneous system.
    rw [mem_homogeneous_linear_constraint_set]
    simp
  calc
    support_function (affine_linear_constraint_set B b)
        = fun y ↦ (y x₀ : EReal) + support_function (homogeneous_linear_constraint_set B) y :=
            support_function_affine_linear_constraint_set_eq_eval_add_support_function_homogeneous
              B b x₀ hx₀
    _ = fun y ↦ (y x₀ : EReal) + (δ_ (polar_cone (homogeneous_linear_constraint_set B))) y := by
          -- Replace the homogeneous support function by the cone indicator formula.
          congr with y
          rw [support_function_eq_indicatorFunction_polarCone
            (homogeneous_linear_constraint_set B) hcone hzero]
    _ = fun y ↦ (y x₀ : EReal) + (δ_ (transpose_range_dual B)) y := by
          -- Rewrite the polar cone using the transpose-range description proved above.
          ext y
          simp [polar_cone_homogeneous_linear_constraint_set_eq_transpose_range_dual]

end
