/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_54

noncomputable section

/-- Helper for Lemma 3.2.6: replacing the distinguished coordinate of `y` by `t` produces the
ambient point lying on the `i0`-axis fiber through `y`. -/
def coordinateReplace
    {n : ℕ} (i0 : Fin n) (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  y + EuclideanSpace.single i0 (t - y.ofLp i0)

/-- Helper for Lemma 3.2.6: `coordinateReplace i0 y t` has coordinate `t` at `i0` and agrees with
`y` away from `i0`. -/
lemma coordinateReplace_apply
    {n : ℕ} (i0 : Fin n) (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) (j : Fin n) :
    coordinateReplace i0 y t j = if j = i0 then t else y.ofLp j := by
  -- Split according to whether the queried coordinate is the distinguished one.
  by_cases hj : j = i0
  · subst hj
    simp [coordinateReplace]
  · simp [coordinateReplace, hj]

/-- Helper for Lemma 3.2.6: the affine line changing only the `i0`-coordinate is exactly
`coordinateReplace i0 y`. -/
lemma coordinateLineMap_apply
    {n : ℕ} (i0 : Fin n) (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (AffineMap.lineMap (coordinateReplace i0 y 0) (coordinateReplace i0 y 1)) t =
      coordinateReplace i0 y t := by
  -- Compare the two points coordinatewise.
  ext j
  by_cases hj : j = i0
  · subst hj
    simp [AffineMap.lineMap_apply, coordinateReplace_apply]
  · simp [AffineMap.lineMap_apply, coordinateReplace_apply, hj]

/-- Helper for Lemma 3.2.6: every coordinate fiber of a convex set is a convex subset of `ℝ`. -/
lemma convex_coordinateFiber
    {n : ℕ} (i0 : Fin n) (y : EuclideanSpace ℝ (Fin n))
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU_convex : Convex ℝ U) :
    Convex ℝ {t : ℝ | coordinateReplace i0 y t ∈ U} := by
  let line : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) :=
    AffineMap.lineMap (coordinateReplace i0 y 0) (coordinateReplace i0 y 1)
  have hpre :
      line ⁻¹' U = {t : ℝ | coordinateReplace i0 y t ∈ U} := by
    -- The affine parametrization is exactly the coordinate-update map.
    ext t
    simp [line, coordinateLineMap_apply (i0 := i0) (y := y) (t := t)]
  -- Convexity is preserved by affine preimages.
  rw [← hpre]
  exact hU_convex.affine_preimage line

/-- Helper for Lemma 3.2.6: updating the distinguished coordinate commutes with convex
combinations. -/
lemma update_convexCombination
    {n : ℕ} (i0 : Fin n) (y z : EuclideanSpace ℝ (Fin n)) (s t a b : ℝ) :
    coordinateReplace i0 (a • y + b • z) (a • s + b • t) =
      a • coordinateReplace i0 y s + b • coordinateReplace i0 z t := by
  -- Compare coordinates on and off the distinguished index.
  ext j
  by_cases hj : j = i0
  · subst hj
    simp [coordinateReplace_apply]
  · simp [coordinateReplace_apply, hj]

/-- Helper for Lemma 3.2.6: the set of attainable `i0`-coordinate values of a convex body is a
convex subset of `ℝ`. -/
lemma convex_firstCoordinateSupport
    {n : ℕ} (i0 : Fin n) {U : Set (EuclideanSpace ℝ (Fin n))} (hU_convex : Convex ℝ U) :
    Convex ℝ {t : ℝ | ∃ y : EuclideanSpace ℝ (Fin n), coordinateReplace i0 y t ∈ U} := by
  intro s hs t ht a b ha hb hab
  rcases hs with ⟨y, hyU⟩
  rcases ht with ⟨z, hzU⟩
  refine ⟨a • y + b • z, ?_⟩
  -- Rewrite the updated witness as the convex combination of the two original witnesses.
  rw [update_convexCombination]
  exact hU_convex hyU hzU ha hb hab
