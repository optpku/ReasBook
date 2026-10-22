/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

namespace Nesterov.Chap04.Proposition_4_1_6

/-- The higher coordinates of `ℝⁿ⁺¹`, namely all coordinates except the first one. -/
abbrev HigherCoord (n : ℕ) := { i : Fin n.succ // i ≠ 0 }

/-- The standard basis of `ℝⁿ⁺¹` used to read Jacobian matrices entrywise. -/
abbrev standardBasis (n : ℕ) :
    Module.Basis (Fin n.succ) ℝ (EuclideanSpace ℝ (Fin n.succ)) :=
  (EuclideanSpace.basisFun (Fin n.succ) ℝ).toBasis

/-- The continuous linear map extracting the `i`-th coordinate of `ℝⁿ⁺¹`. -/
abbrev coordCLM {n : ℕ} (i : Fin n.succ) :
    EuclideanSpace ℝ (Fin n.succ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp
    (EuclideanSpace.equiv (Fin n.succ) ℝ).toContinuousLinearMap

/-- The continuous linear map keeping only the coordinates strictly before `i`. -/
def previousCoordinatesCLM {n : ℕ} (i : HigherCoord n) :
    EuclideanSpace ℝ (Fin n.succ) →L[ℝ] EuclideanSpace ℝ (Fin i.1) :=
  ((EuclideanSpace.equiv (Fin i.1) ℝ).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun j : Fin i.1 ↦
      coordCLM (Fin.castLT j (lt_trans j.2 i.1.2)))

/-- The vector of coordinates of `x` strictly preceding the higher coordinate `i`. -/
def previousCoordinates {n : ℕ} (x : EuclideanSpace ℝ (Fin n.succ)) (i : HigherCoord n) :
    EuclideanSpace ℝ (Fin i.1) :=
  previousCoordinatesCLM i x

/-- Evaluating `previousCoordinates x i` at `j` returns the `j`-th coordinate of `x`. -/
@[simp] theorem previousCoordinates_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n.succ))
    (i : HigherCoord n) (j : Fin i.1) :
    previousCoordinates x i j = x (Fin.castLT j (lt_trans j.2 i.1.2)) := by
  simp [previousCoordinates, previousCoordinatesCLM, coordCLM]

/-- Proposition 4.1.6 is modeled by a triangular transformation on `ℝⁿ⁺¹`. The correction at a
higher coordinate depends only on the strictly earlier coordinates. -/
structure TriangularTransformation (n : ℕ) where
  /-- The correction term attached to the higher coordinate `i`. -/
  correction (i : HigherCoord n) : EuclideanSpace ℝ (Fin i.1) → ℝ
  /-- Each correction term is differentiable on its natural Euclidean domain. -/
  differentiable_correction (i : HigherCoord n) : Differentiable ℝ (correction i)

namespace TriangularTransformation

/-- The coordinate tuple defining the triangular transformation before identifying it with
`EuclideanSpace`. -/
def toCoordinates {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    Fin n.succ → ℝ :=
  Fin.cons (x 0) fun i ↦
    x i.succ +
      u.correction ⟨i.succ, Fin.succ_ne_zero i⟩
        (previousCoordinates x ⟨i.succ, Fin.succ_ne_zero i⟩)

/-- The triangular transformation acts by fixing the first coordinate and adding a prefix-dependent
correction to each higher coordinate. -/
def toFun {n : ℕ} (u : TriangularTransformation n) :
    EuclideanSpace ℝ (Fin n.succ) → EuclideanSpace ℝ (Fin n.succ) :=
  fun x ↦ (EuclideanSpace.equiv (Fin n.succ) ℝ).symm (toCoordinates u x)

instance {n : ℕ} : CoeFun (TriangularTransformation n)
    (fun _ ↦ EuclideanSpace ℝ (Fin n.succ) → EuclideanSpace ℝ (Fin n.succ)) where
  coe := toFun

/-- The first coordinate of a triangular transformation is unchanged. -/
@[simp] theorem coe_apply_zero {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    u x 0 = x 0 := by
  simp [TriangularTransformation.toFun, TriangularTransformation.toCoordinates]

/-- A higher coordinate is obtained by adding the corresponding correction term. -/
@[simp] theorem coe_apply_succ {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) (i : Fin n) :
    u x i.succ = x i.succ +
      u.correction ⟨i.succ, Fin.succ_ne_zero i⟩
        (previousCoordinates x ⟨i.succ, Fin.succ_ne_zero i⟩) := by
  simp [TriangularTransformation.toFun, TriangularTransformation.toCoordinates]

/-- Helper for Proposition 4.1.6: the triangular transformation is differentiable because each
coordinate is either a coordinate projection or a differentiable correction composed with the
prefix-coordinate map. -/
theorem differentiable {n : ℕ} (u : TriangularTransformation n) :
    Differentiable ℝ u := by
  have hcoords : Differentiable ℝ (u.toCoordinates) := by
    refine (differentiable_pi).2 ?_
    intro i
    cases i using Fin.cases with
    | zero =>
        -- The first coordinate is the identity coordinate map.
        simpa [TriangularTransformation.toCoordinates, coordCLM] using
          (coordCLM (n := n) 0).differentiable
    | succ i =>
        -- Higher coordinates are sums of the identity coordinate and the correction term.
        have hcoord : Differentiable ℝ
            (fun x : EuclideanSpace ℝ (Fin n.succ) ↦ x i.succ) := by
          simpa [coordCLM] using (coordCLM (n := n) i.succ).differentiable
        have hcorr : Differentiable ℝ
            (fun x : EuclideanSpace ℝ (Fin n.succ) ↦
              u.correction ⟨i.succ, Fin.succ_ne_zero i⟩
                (previousCoordinates x ⟨i.succ, Fin.succ_ne_zero i⟩)) := by
          exact (u.differentiable_correction ⟨i.succ, Fin.succ_ne_zero i⟩).comp
            (previousCoordinatesCLM ⟨i.succ, Fin.succ_ne_zero i⟩).differentiable
        simpa [TriangularTransformation.toCoordinates] using hcoord.add hcorr
  -- Transfer differentiability from coordinate tuples back to `EuclideanSpace`.
  simpa [TriangularTransformation.toFun] using
    ((EuclideanSpace.equiv (Fin n.succ) ℝ).symm.differentiable.comp hcoords)

end TriangularTransformation

/-- The Jacobian matrix of `u` in the standard basis. -/
abbrev jacobianMatrix {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    Matrix (Fin n.succ) (Fin n.succ) ℝ :=
  LinearMap.toMatrix (standardBasis n) (standardBasis n) (fderiv ℝ u x).toLinearMap

/-- Helper for Proposition 4.1.6: perturbing `x` in a coordinate `j` which is not strictly earlier
than `i` leaves the prefix coordinates before `i` unchanged. -/
lemma previousCoordinates_add_basis_of_not_lt {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n.succ)) (i : HigherCoord n)
    (j : Fin n.succ) (t : ℝ) (hji : ¬ j < i.1) :
    previousCoordinates
        (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) i =
      previousCoordinates x i := by
  ext k
  -- The perturbed basis vector has zero contribution on coordinates strictly before `i`.
  have hneq : Fin.castLT k (lt_trans k.2 i.1.2) ≠ j := by
    intro hEq
    apply hji
    have hklt : Fin.castLT k (lt_trans k.2 i.1.2) < i.1 := by
      simpa [Fin.lt_def, Fin.val_castLT] using k.2
    simpa [hEq] using hklt
  simp [previousCoordinates_apply, hneq]

/-- Helper for Proposition 4.1.6: differentiating the `i`-th output coordinate along the `j`-th
standard basis direction reads off the `(i,j)` Jacobian entry. -/
lemma jacobian_entry_hasDerivAt {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) (i j : Fin n.succ) :
    HasDerivAt
      (fun t : ℝ ↦
        u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) i)
      (jacobianMatrix u x i j) 0 := by
  let e := EuclideanSpace.basisFun (Fin n.succ) ℝ j
  have hu : HasFDerivAt u (fderiv ℝ u x) x := by
    exact (TriangularTransformation.differentiable u x).hasFDerivAt
  have hcoord : HasFDerivAt (fun y ↦ u y i)
      ((coordCLM (n := n) i).comp (fderiv ℝ u x)) x := by
    simpa [coordCLM] using ((coordCLM (n := n) i).hasFDerivAt.comp x hu)
  have hcoord0 : HasFDerivAt (fun y ↦ u y i)
      ((coordCLM (n := n) i).comp (fderiv ℝ u x)) (x + (0 : ℝ) • e) := by
    simpa [e] using hcoord
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • e) e (0 : ℝ) := by
    simpa [e] using (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x)
  -- Compose the derivative of the coordinate function with the basis-direction line.
  have hslice := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hcoord0 hline
  simpa [jacobianMatrix, e, LinearMap.toMatrix_apply] using hslice

/-- Helper for Proposition 4.1.6: Jacobian entries above the diagonal vanish, so the standard
matrix of the derivative is triangular in the `toMatrix` convention. -/
lemma jacobian_matrix_entry_eq_zero_of_later {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) {i j : Fin n.succ} (hij : i < j) :
    jacobianMatrix u x i j = 0 := by
  have hslice := jacobian_entry_hasDerivAt (u := u) (x := x) i j
  cases i using Fin.cases with
  | zero =>
      -- The first coordinate is fixed, so varying any later coordinate leaves it constant.
      have hconst : HasDerivAt
          (fun t : ℝ ↦
            u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) 0)
          0 0 := by
        have hfun :
            (fun t : ℝ ↦
              u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) 0) =
            fun _ : ℝ ↦ x 0 := by
          funext t
          have hne : j ≠ (0 : Fin n.succ) := ne_of_gt hij
          simp [TriangularTransformation.coe_apply_zero, hne]
        rw [hfun]
        simpa using (hasDerivAt_const (0 : ℝ) (x 0))
      exact hslice.unique hconst
  | succ k =>
      -- Later-coordinate perturbations do not affect the correction term at coordinate `k.succ`.
      have hnot : ¬ j < k.succ := not_lt_of_ge (le_of_lt hij)
      have hconst : HasDerivAt
          (fun t : ℝ ↦
            u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) k.succ)
          0 0 := by
        have hfun :
            (fun t : ℝ ↦
              u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) k.succ) =
            fun _ : ℝ ↦ u x k.succ := by
          funext t
          have hprev := previousCoordinates_add_basis_of_not_lt
            (x := x) (i := ⟨k.succ, Fin.succ_ne_zero k⟩) (j := j) (t := t) hnot
          have hcoord :
              (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) k.succ = x k.succ := by
            simp [ne_of_gt hij]
          rw [TriangularTransformation.coe_apply_succ, TriangularTransformation.coe_apply_succ]
          rw [hprev, hcoord]
        rw [hfun]
        simpa using (hasDerivAt_const (0 : ℝ) (u x k.succ))
      exact hslice.unique hconst

/-- Helper for Proposition 4.1.6: each diagonal Jacobian entry equals `1` because the
corresponding output coordinate depends affinely on its own input coordinate with slope `1`. -/
lemma jacobian_matrix_diagonal_eq_one {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) (i : Fin n.succ) :
    jacobianMatrix u x i i = 1 := by
  have hslice := jacobian_entry_hasDerivAt (u := u) (x := x) i i
  cases i using Fin.cases with
  | zero =>
      -- Along the first coordinate, the map is exactly `t ↦ u x 0 + t`.
      have haffine : HasDerivAt
          (fun t : ℝ ↦
            u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ 0)) 0)
          1 0 := by
        have hfun :
            (fun t : ℝ ↦
              u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ 0)) 0) =
            fun t : ℝ ↦ u x 0 + t := by
          funext t
          simp [TriangularTransformation.coe_apply_zero, add_comm]
        rw [hfun]
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (u x 0)
      exact hslice.unique haffine
  | succ k =>
      -- At coordinate `k.succ`, the prefix term is unchanged by perturbing the same coordinate.
      have haffine : HasDerivAt
          (fun t : ℝ ↦
            u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ k.succ)) k.succ)
          1 0 := by
        have hprev := fun t : ℝ ↦ previousCoordinates_add_basis_of_not_lt
          (x := x) (i := ⟨k.succ, Fin.succ_ne_zero k⟩) (j := k.succ) (t := t)
          (by simp)
        have hfun :
            (fun t : ℝ ↦
              u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ k.succ)) k.succ) =
            fun t : ℝ ↦ u x k.succ + t := by
          funext t
          rw [TriangularTransformation.coe_apply_succ, TriangularTransformation.coe_apply_succ]
          have hcoord :
              (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ k.succ)) k.succ =
                x k.succ + t := by
            simp
          rw [hprev t, hcoord]
          ac_rfl
        rw [hfun]
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (u x k.succ)
      exact hslice.unique haffine

/-- Helper for Proposition 4.1.6: in `LinearMap.toMatrix` coordinates, the Jacobian is
lower triangular, i.e. entries with `i < j` vanish. -/
lemma jacobianMatrix_blockTriangular {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    (jacobianMatrix u x).BlockTriangular OrderDual.toDual := by
  intro i j hij
  -- `OrderDual.toDual j < OrderDual.toDual i` is exactly `i < j`.
  exact jacobian_matrix_entry_eq_zero_of_later (u := u) (x := x) (by simpa using hij)

/-- Proposition 4.1.6: for a triangular transformation, the Jacobian matrix has unit diagonal and
triangular zero pattern, so its determinant is `1` at every point. In the `toMatrix` convention
used here, that zero pattern is lower triangular, which is the matrix transpose convention of the
source's upper-triangular statement. -/
theorem triangularTransformation_fderiv_det_eq_one {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    (fderiv ℝ u x).det = 1 := by
  let J := jacobianMatrix u x
  have htri : J.BlockTriangular OrderDual.toDual := by
    simpa [J] using jacobianMatrix_blockTriangular (u := u) (x := x)
  have hdiag : ∀ i : Fin n.succ, J i i = 1 := by
    intro i
    simpa [J] using jacobian_matrix_diagonal_eq_one (u := u) (x := x) i
  -- The entrywise lemmas turn the determinant into the product of the diagonal entries.
  calc
    (fderiv ℝ u x).det = J.det := by
      symm
      simpa [J, jacobianMatrix] using
        (LinearMap.det_toMatrix (standardBasis n) (fderiv ℝ u x).toLinearMap)
    _ = ∏ i, J i i := by
      exact Matrix.det_of_lowerTriangular J htri
    _ = ∏ _ : Fin n.succ, (1 : ℝ) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      simp [hdiag i]
    _ = 1 := by
      simp

/-- Helper for Proposition 4.1.6: determinant `1` implies that the derivative is nonsingular at
every point. -/
theorem triangularTransformation_fderiv_det_ne_zero {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    (fderiv ℝ u x).det ≠ 0 := by
  rw [triangularTransformation_fderiv_det_eq_one (u := u) (x := x)]
  norm_num

end Nesterov.Chap04.Proposition_4_1_6
