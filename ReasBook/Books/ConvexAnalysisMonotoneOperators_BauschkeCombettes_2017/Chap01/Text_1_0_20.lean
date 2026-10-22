/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

private lemma centered_map_smul_of_affine_combination (T : X → Y)
    (hT : ∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y)
    (x : X) (μ : ℝ) :
    T (μ • x) - T 0 = μ • (T x - T 0) := by
  have hAffine : T (μ • x) = μ • T x + (1 - μ) • T 0 := by
    simpa using hT x 0 (1 - μ)
  have hShift : (1 - μ) • T 0 = -(μ • T 0) + T 0 := by
    rw [sub_eq_add_neg, add_smul, one_smul, neg_smul]
    abel
  rw [sub_eq_iff_eq_add]
  calc
    T (μ • x) = μ • T x + (1 - μ) • T 0 := hAffine
    _ = μ • T x + (-(μ • T 0) + T 0) := by rw [hShift]
    _ = μ • (T x - T 0) + T 0 := by
      rw [smul_sub, sub_eq_add_neg]
      abel

private lemma centered_map_half_sum_of_affine_combination (T : X → Y)
    (hT : ∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y)
    (x y : X) :
    T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) - T 0 =
      (1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0)) := by
  have hMidpoint :
      T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) = (1 / 2 : ℝ) • T x + (1 / 2 : ℝ) • T y := by
    have h := hT x y (1 / 2 : ℝ)
    norm_num at h
    exact h
  have hHalf : ((1 / 2 : ℝ) • T 0) + (1 / 2 : ℝ) • T 0 = T 0 := by
    rw [← add_smul]
    norm_num
  calc
    T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) - T 0
        = ((1 / 2 : ℝ) • T x + (1 / 2 : ℝ) • T y) -
            (((1 / 2 : ℝ) • T 0) + (1 / 2 : ℝ) • T 0) := by
              rw [hMidpoint, hHalf]
    _ = (1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0)) := by
      rw [smul_add, smul_sub, smul_sub]
      abel

private lemma centered_map_add_of_affine_combination (T : X → Y)
    (hT : ∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y)
    (x y : X) :
    T (x + y) - T 0 = (T x - T 0) + (T y - T 0) := by
  have hScale :=
    centered_map_smul_of_affine_combination T hT
      (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) (2 : ℝ)
  have hx : (2 : ℝ) • ((1 / 2 : ℝ) • x) = x := by
    calc
      (2 : ℝ) • ((1 / 2 : ℝ) • x) = ((2 : ℝ) * (1 / 2 : ℝ)) • x := by
        simp
      _ = x := by norm_num
  have hy : (2 : ℝ) • ((1 / 2 : ℝ) • y) = y := by
    calc
      (2 : ℝ) • ((1 / 2 : ℝ) • y) = ((2 : ℝ) * (1 / 2 : ℝ)) • y := by
        simp
      _ = y := by norm_num
  have hArg : (2 : ℝ) • (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) = x + y := by
    rw [smul_add, hx, hy]
  have hCentered :
      (2 : ℝ) • ((1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0))) =
        (T x - T 0) + (T y - T 0) := by
    calc
      (2 : ℝ) • ((1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0))) =
          ((2 : ℝ) * (1 / 2 : ℝ)) • ((T x - T 0) + (T y - T 0)) := by
            simp
      _ = (T x - T 0) + (T y - T 0) := by norm_num
  calc
    T (x + y) - T 0
        = T ((2 : ℝ) • (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y)) - T 0 := by rw [hArg]
    _ = (2 : ℝ) • (T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) - T 0) := hScale
    _ = (2 : ℝ) • ((1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0))) := by
          rw [centered_map_half_sum_of_affine_combination T hT x y]
    _ = (T x - T 0) + (T y - T 0) := hCentered

/-- Companion bridge for Text 1.0.20: the textbook affine-combination formula for a map `T`
is equivalent to the existence of a bundled affine map with underlying function `T`. -/
theorem affine_combination_iff_exists_affineMap (T : X → Y) :
    (∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y) ↔
      ∃ A : X →ᵃ[ℝ] Y, (A : X → Y) = T := by
  constructor
  · intro hT
    let L : X →ₗ[ℝ] Y := IsLinearMap.mk' (fun x : X ↦ T x - T 0)
      { map_add := fun x y ↦ centered_map_add_of_affine_combination T hT x y
        map_smul := fun t x ↦ centered_map_smul_of_affine_combination T hT x t }
    refine ⟨AffineMap.mk' T L 0 ?_, rfl⟩
    intro x
    simp [L, sub_eq_add_neg, add_assoc]
  · rintro ⟨A, rfl⟩ x y t
    simpa [AffineMap.lineMap_apply_module] using A.apply_lineMap x y t

/-- Text 1.0.20: a map between real vector spaces is affine, in the canonical sense of arising
from an element of `X →ᵃ[ℝ] Y`, exactly when its translate through the origin,
`x ↦ T x - T 0`, is linear. -/
theorem affine_iff_isLinearMap_sub_apply_zero (T : X → Y) :
    (∃ A : X →ᵃ[ℝ] Y, (A : X → Y) = T) ↔
      IsLinearMap ℝ (fun x : X ↦ T x - T 0) := by
  constructor
  · rintro ⟨A, rfl⟩
    have hCentered : (fun x : X ↦ A x - A 0) = A.linear := by
      funext x
      simpa using (congrArg (fun f : X → Y ↦ f x) A.decomp').symm
    rw [hCentered]
    exact A.linear.isLinear
  · intro hL
    let L : X →ₗ[ℝ] Y := IsLinearMap.mk' (fun x : X ↦ T x - T 0) hL
    refine ⟨AffineMap.mk' T L 0 ?_, rfl⟩
    intro x
    simp [L, sub_eq_add_neg, add_assoc]
