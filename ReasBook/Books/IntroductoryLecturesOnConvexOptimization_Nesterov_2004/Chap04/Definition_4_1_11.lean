/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 4.1.11 lies in the nonlinear-transformation / triangular-coordinate domain.

Sampled owner declarations:
* project `NonlinearConvexTransformation` in `Definition_4_1_10`, the nearby owner for a
  source-facing change of variables on `EuclideanSpace ℝ (Fin n)`;
* mathlib `Differentiable`, the canonical regularity predicate for the coordinate-correction
  maps `φ₁, …, φₙ₋₁`;
* mathlib `Fin.cons`, the canonical owner API for assembling a `Fin (n + 1)`-tuple from its first
  coordinate and remaining coordinates;
* mathlib subtype indices `{i : Fin (n + 1) // i ≠ 0}`, the canonical way to speak about the
  higher coordinates while keeping the first coordinate separate;
* mathlib `EuclideanSpace.equiv`, the canonical bridge between `EuclideanSpace ℝ (Fin k)` and
  coordinate functions `Fin k → ℝ`.
* mathlib `CoeFun`, the canonical way to expose the resulting transformation as a map
  `ℝⁿ⁺¹ → ℝⁿ⁺¹`.

Best owner abstraction:
* source-facing: the triangular transformation itself;
* core/canonical: the family of differentiable correction maps indexed by the nonzero
  coordinates, each defined on the space of strictly earlier coordinates;
* bridge/view: the prefix-coordinate extraction map and the coordinate formulas for evaluating the
  induced transformation via `Fin.cons`.

Primitive data:
* for each nonzero coordinate `i`, a differentiable map `φᵢ : ℝⁱ → ℝ` on the earlier
  coordinates only.

Derived API:
* the induced map `u : ℝⁿ⁺¹ → ℝⁿ⁺¹`;
* the first-coordinate identity `u¹(x) = x¹`;
* for each nonzero coordinate `i`, the formula `uⁱ(x) = xⁱ + φᵢ(x¹, …, xⁱ⁻¹)`.

This keeps the source-facing owner at the transformation level and avoids a parallel wrapper for
the induced map. -/

/-- The higher coordinates of `ℝⁿ⁺¹`, i.e. all coordinates except the first one. -/
abbrev HigherCoord (n : ℕ) := { i : Fin n.succ // i ≠ 0 }

/-- Definition 4.1.11: a triangular transformation of `ℝⁿ⁺¹` is determined by differentiable
coordinate-correction maps for the higher coordinates, where the correction at coordinate `i`
depends only on the strictly earlier coordinates `0, …, i - 1`. The associated map
`u : ℝⁿ⁺¹ → ℝⁿ⁺¹` is recovered by coercion to a function in the namespace below. -/
structure TriangularTransformation (n : ℕ) where
  /-- The correction term for the higher coordinate `i`, depending only on the earlier
  coordinates. -/
  correction (i : HigherCoord n) : EuclideanSpace ℝ (Fin i.1) → ℝ
  /-- Each coordinate-correction map is differentiable on its natural Euclidean domain. -/
  differentiable_correction (i : HigherCoord n) : Differentiable ℝ (correction i)

namespace TriangularTransformation

/-- The vector of the coordinates of `x` strictly preceding the higher coordinate `i`. -/
def previousCoordinates {n : ℕ} (x : EuclideanSpace ℝ (Fin n.succ)) (i : HigherCoord n) :
    EuclideanSpace ℝ (Fin i.1) :=
  (EuclideanSpace.equiv (Fin i.1) ℝ).symm fun j ↦
    x (Fin.castLT j (lt_trans j.2 i.1.2))

/-- Evaluating `previousCoordinates x i` at `j` returns the `j`-th coordinate of `x`. -/
@[simp] theorem previousCoordinates_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n.succ))
    (i : HigherCoord n) (j : Fin i.1) :
    previousCoordinates x i j = x (Fin.castLT j (lt_trans j.2 i.1.2)) := by
  simp [previousCoordinates]

/-- The triangular transformation acts on `x : ℝⁿ⁺¹` by leaving the first coordinate fixed and
adding to each higher coordinate a correction depending only on the earlier coordinates. -/
def toFun {n : ℕ} (u : TriangularTransformation n) :
    EuclideanSpace ℝ (Fin n.succ) → EuclideanSpace ℝ (Fin n.succ) :=
  fun x ↦
    (EuclideanSpace.equiv (Fin n.succ) ℝ).symm <|
      Fin.cons (x 0) fun i ↦
        x i.succ +
          u.correction ⟨i.succ, Fin.succ_ne_zero i⟩
            (previousCoordinates x ⟨i.succ, Fin.succ_ne_zero i⟩)

instance {n : ℕ} : CoeFun (TriangularTransformation n)
    (fun _ ↦ EuclideanSpace ℝ (Fin n.succ) → EuclideanSpace ℝ (Fin n.succ)) where
  coe := toFun

/-- The first coordinate of a triangular transformation is unchanged. -/
@[simp] theorem coe_apply_zero {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    u x 0 = x 0 := by
  simp [TriangularTransformation.toFun]

/-- At a higher coordinate `i`, evaluating a triangular transformation adds the corresponding
correction term depending only on the earlier coordinates. -/
@[simp] theorem coe_apply_higherCoord {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) (i : HigherCoord n) :
    u x i.1 = x i.1 + u.correction i (previousCoordinates x i) := by
  rcases i with ⟨i, hi⟩
  cases i using Fin.cases with
  | zero => cases (hi rfl)
  | succ i =>
      simp [TriangularTransformation.toFun]

/-- At the higher coordinate `i.succ`, evaluating a triangular transformation adds the
corresponding correction term depending only on the earlier coordinates `0, …, i`. -/
@[simp] theorem coe_apply_succ {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) (i : Fin n) :
    u x i.succ = x i.succ +
      u.correction ⟨i.succ, Fin.succ_ne_zero i⟩
        (previousCoordinates x ⟨i.succ, Fin.succ_ne_zero i⟩) := by
  simpa using
    coe_apply_higherCoord u x ⟨i.succ, Fin.succ_ne_zero i⟩

end TriangularTransformation
