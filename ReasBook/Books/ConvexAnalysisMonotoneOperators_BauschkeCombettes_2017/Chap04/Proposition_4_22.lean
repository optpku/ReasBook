/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Corollary_2_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Function Set

/-- The restricted fixed points of an ambient self-map are exactly its fixed points in `D`. -/
private lemma image_fixedPointsWithin_restrict_eq_fixedPointSetOn
    {H : Type u} {D : Set H} {T : H → H} :
    Subtype.val '' fixedPointsWithin (fun x : D ↦ T x) = fixedPointSetOn D T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_fixedPointSetOn_iff.mpr ⟨y.2, mem_fixedPointsWithin_iff _ |>.mp hy⟩
  · intro hx
    rcases mem_fixedPointSetOn_iff.mp hx with ⟨hxD, hfix⟩
    exact ⟨⟨x, hxD⟩, mem_fixedPointsWithin_iff _ |>.mpr hfix, rfl⟩

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 4.22: subtracting a point on the segment from `u` rewrites as the
corresponding affine combination of the endpoint residuals. -/
private lemma sub_lineMap_eq_affine_combination_sub (u x y : H) (α : ℝ) :
    u - AffineMap.lineMap x y α = α • (u - y) + (1 - α) • (u - x) := by
  -- Rewrite the difference as a difference of two line maps with the same parameter.
  calc
    u - AffineMap.lineMap x y α = AffineMap.lineMap u u α - AffineMap.lineMap x y α := by
      rw [AffineMap.lineMap_same_apply]
    _ = AffineMap.lineMap (u - x) (u - y) α := by
      simpa using AffineMap.lineMap_vsub_lineMap u u x y α
    _ = α • (u - y) + (1 - α) • (u - x) := by
      -- The vector-valued line map is the usual affine combination of its endpoints.
      simpa [add_comm, add_left_comm, add_assoc] using
        (AffineMap.lineMap_apply_module (u - x) (u - y) α)

/-- Helper for Proposition 4.22: the Corollary 2.15 squared-norm identity for the residual to a
line-map point. -/
private lemma norm_sq_sub_lineMap_add_weighted_norm_sub_sq (u x y : H) (α : ℝ) :
    ‖u - AffineMap.lineMap x y α‖ ^ 2 + α * (1 - α) * ‖x - y‖ ^ 2 =
      α * ‖u - y‖ ^ 2 + (1 - α) * ‖u - x‖ ^ 2 := by
  have hxy : (u - y) - (u - x) = x - y := by
    abel_nf
  have hres :=
    norm_sq_affine_combination_add_weighted_norm_sub_sq (u - y) (u - x) α
  rw [hxy] at hres
  rw [sub_lineMap_eq_affine_combination_sub]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hres

/-- Helper for Proposition 4.22: the squared residual at a point of the segment joining two fixed
points is nonpositive, hence zero. -/
private lemma lineMap_residual_sq_le_zero_of_isQuasinonexpansiveOn
    {D : Set H} (hD_convex : Convex ℝ D) {T : D → H}
    (hT : IsQuasinonexpansiveOn T) {x y : D}
    (hx : x ∈ fixedPointsWithin T) (hy : y ∈ fixedPointsWithin T)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let z : D := ⟨AffineMap.lineMap (x : H) y α, hD_convex.lineMap_mem x.2 y.2 hα⟩
    ‖T z - z‖ ^ 2 ≤ 0 := by
  dsimp
  let z : D := ⟨AffineMap.lineMap (x : H) y α, hD_convex.lineMap_mem x.2 y.2 hα⟩
  have hxfix : T x = (x : H) := mem_fixedPointsWithin_iff T |>.mp hx
  have hyfix : T y = (y : H) := mem_fixedPointsWithin_iff T |>.mp hy
  have hTx : ‖T z - x‖ ≤ ‖(z : H) - x‖ := by
    simpa [hxfix] using hT z x hxfix
  have hTy : ‖T z - y‖ ≤ ‖(z : H) - y‖ := by
    simpa [hyfix] using hT z y hyfix
  have hTx_sq : ‖T z - x‖ ^ 2 ≤ ‖(z : H) - x‖ ^ 2 := by
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using hTx
  have hTy_sq : ‖T z - y‖ ^ 2 ≤ ‖(z : H) - y‖ ^ 2 := by
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using hTy
  have hcompare :
      ‖T z - z‖ ^ 2 + α * (1 - α) * ‖(x : H) - y‖ ^ 2 ≤
        α * ‖(z : H) - y‖ ^ 2 + (1 - α) * ‖(z : H) - x‖ ^ 2 := by
    rw [show ‖T z - z‖ ^ 2 + α * (1 - α) * ‖(x : H) - y‖ ^ 2 =
        α * ‖T z - y‖ ^ 2 + (1 - α) * ‖T z - x‖ ^ 2 by
        simpa [z] using norm_sq_sub_lineMap_add_weighted_norm_sub_sq (T z) (x : H) y α]
    nlinarith [hTy_sq, hTx_sq, hα.1, hα.2]
  have hzero :
      α * ‖(z : H) - y‖ ^ 2 + (1 - α) * ‖(z : H) - x‖ ^ 2 =
        α * (1 - α) * ‖(x : H) - y‖ ^ 2 := by
    have hz_eq := norm_sq_sub_lineMap_add_weighted_norm_sub_sq (z : H) (x : H) y α
    simpa [z] using hz_eq.symm
  nlinarith [hcompare, hzero]

/-- Helper for Proposition 4.22: every point of the segment joining two fixed points is again a
fixed point of the restricted map. -/
private lemma lineMap_mem_fixedPointsWithin_of_isQuasinonexpansiveOn
    {D : Set H} (hD_convex : Convex ℝ D) {T : D → H}
    (hT : IsQuasinonexpansiveOn T) {x y : D}
    (hx : x ∈ fixedPointsWithin T) (hy : y ∈ fixedPointsWithin T)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (⟨AffineMap.lineMap (x : H) y α, hD_convex.lineMap_mem x.2 y.2 hα⟩ : D) ∈
      fixedPointsWithin T := by
  let z : D := ⟨AffineMap.lineMap (x : H) y α, hD_convex.lineMap_mem x.2 y.2 hα⟩
  have hsq : ‖T z - z‖ ^ 2 ≤ 0 := by
    simpa [z] using
      lineMap_residual_sq_le_zero_of_isQuasinonexpansiveOn hD_convex hT hx hy hα
  have hsq_eq : ‖T z - z‖ ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
  have hnorm_eq : ‖T z - z‖ = 0 := sq_eq_zero_iff.mp hsq_eq
  exact mem_fixedPointsWithin_iff T |>.mpr <| sub_eq_zero.mp (norm_eq_zero.mp hnorm_eq)

-- Proof sketch: if `x` and `y` are fixed points of `T : D → H`, the convexity of `D` puts every
-- segment point back in `D`. Applying quasinonexpansiveness relative to the fixed endpoints and
-- the Hilbert-space identity from Corollary 2.15 forces the residual there to vanish, so the
-- segment stays in the fixed-point set.
/-- Helper for Proposition 4.22: the ambient image of the fixed-point set of a quasinonexpansive
map on a convex domain is convex. -/
private lemma convex_image_fixedPointsWithin_of_isQuasinonexpansiveOn
    {D : Set H} (hD_convex : Convex ℝ D) {T : D → H}
    (hT : IsQuasinonexpansiveOn T) :
    Convex ℝ (Subtype.val '' fixedPointsWithin T : Set H) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  have hb_one : b ≤ (1 : ℝ) := by
    linarith
  let z : D := ⟨AffineMap.lineMap (x' : H) y' b, hD_convex.lineMap_mem x'.2 y'.2 ⟨hb, hb_one⟩⟩
  have hz : z ∈ fixedPointsWithin T := by
    simpa [z] using
      lineMap_mem_fixedPointsWithin_of_isQuasinonexpansiveOn hD_convex hT hx' hy' ⟨hb, hb_one⟩
  refine ⟨z, hz, ?_⟩
  have ha_eq : a = 1 - b := by
    linarith
  rw [ha_eq]
  simp [z, AffineMap.lineMap_apply_module, add_comm]

/-- Proposition 4.22: if `D` is a nonempty convex subset of a real Hilbert space and `T`
is quasinonexpansive on `D`, then the fixed-point set of `T` in `D` is convex. -/
theorem convex_fixedPointSetOn_of_quasinonexpansiveOn
    {D : Set H} (hD : D.Nonempty) (hD_convex : Convex ℝ D) {T : H → H}
    (hT : QuasinonexpansiveOn D T) :
    Convex ℝ (fixedPointSetOn D T) := by
  let _ : D.Nonempty := hD
  let S : D → H := fun x ↦ T x
  have hS : IsQuasinonexpansiveOn S := by
    rw [isQuasinonexpansiveOn_iff]
    intro x y hy
    have hy' : (y : H) ∈ fixedPointSetOn D T := by
      exact mem_fixedPointSetOn_iff.mpr ⟨y.2, hy⟩
    simpa [S] using (quasinonexpansiveOn_iff.mp hT) x x.2 y hy'
  simpa [S, image_fixedPointsWithin_restrict_eq_fixedPointSetOn] using
    convex_image_fixedPointsWithin_of_isQuasinonexpansiveOn hD_convex hS

end
