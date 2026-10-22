/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: pass to the affine span of `C`, where `intrinsicInterior ℝ C` becomes the ordinary
-- interior and, in finite dimension, `closure C` agrees with the intrinsic closure. Then apply the
-- ambient convex-topology theorem `Convex.combo_interior_closure_mem_interior` in that affine-span
-- model and transport the result back to `E`.
/-- Lemma 5.23: line segment principle for relative interior. If `C` is convex, `x` lies in the
relative interior of `C`, `y` lies in the closure of `C`, and `0 < t ≤ 1`, then
`t • x + (1 - t) • y` also lies in the relative interior of `C`. -/
theorem Convex.combo_intrinsicInterior_closure_mem_intrinsicInterior {C : Set E} (hC : Convex ℝ C)
    {x y : E} (hx : x ∈ intrinsicInterior ℝ C) (hy : y ∈ closure C) {t : ℝ}
    (ht_pos : 0 < t) (ht_le_one : t ≤ 1) :
    t • x + (1 - t) • y ∈ intrinsicInterior ℝ C := by
  let A : Set (affineSpan ℝ C) := (↑) ⁻¹' C
  rcases mem_intrinsicInterior.1 hx with ⟨x', hx', rfl⟩
  have hy' : y ∈ intrinsicClosure ℝ C := by
    simpa using hy
  rcases mem_intrinsicClosure.1 hy' with ⟨y', hy'cl, rfl⟩
  haveI : Nonempty (affineSpan ℝ C) := ⟨y'⟩
  let φ := AffineIsometryEquiv.constVSub ℝ y'
  let T := φ '' A
  have hTpre : Convex ℝ (φ.symm ⁻¹' A) := by
    simpa [A, Function.comp_def] using
      hC.affine_preimage (((affineSpan ℝ C).subtype.comp φ.symm.toAffineEquiv.toAffineMap))
  have hT_eq : T = φ.symm ⁻¹' A := by
    simpa [T] using (φ.toEquiv.image_eq_preimage_symm A)
  have hT : Convex ℝ T := by
    rw [hT_eq]
    exact hTpre
  have hinterior : φ '' interior A = interior T := by
    simpa [T] using (φ.toHomeomorph.image_interior A)
  have hclosure : φ '' closure A = closure T := by
    simpa [T] using (φ.toHomeomorph.image_closure A)
  have hxT : φ x' ∈ interior T := by
    rw [← hinterior]
    exact ⟨x', hx', rfl⟩
  have hyT : φ y' ∈ closure T := by
    rw [← hclosure]
    exact ⟨y', hy'cl, rfl⟩
  have hzT : t • φ x' + (1 - t) • φ y' ∈ interior T :=
    hT.combo_interior_closure_mem_interior hxT hyT ht_pos (sub_nonneg.mpr ht_le_one) (by ring)
  have hzLine : (AffineMap.lineMap (φ y') (φ x')) t ∈ interior T := by
    simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using hzT
  have hzA : (AffineMap.lineMap y' x') t ∈ interior A := by
    have hzT' : φ ((AffineMap.lineMap y' x') t) ∈ interior T := by
      change φ.toAffineEquiv ((AffineMap.lineMap y' x') t) ∈ interior T
      rw [φ.toAffineEquiv.apply_lineMap y' x' t]
      exact hzLine
    rw [← hinterior] at hzT'
    simpa using hzT'
  refine mem_intrinsicInterior.2 ?_
  refine ⟨(AffineMap.lineMap y' x') t, hzA, ?_⟩
  calc
    ↑((AffineMap.lineMap y' x') t) = AffineMap.lineMap (↑y') (↑x') t := rfl
    _ = t • (↑x' : E) + (1 - t) • (↑y' : E) := by
      simp [AffineMap.lineMap_apply_module, add_comm]

end
