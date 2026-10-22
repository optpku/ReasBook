/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_2.IndexSets
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul

public section

noncomputable section

namespace ActiveSet

universe u

variable {ι : Type u} [DecidableEq ι]

/-- The diagonal matrix `D_A` attached to an active set `A`, with diagonal
entry `1` on active indices and `0` otherwise. -/
noncomputable def activeDiagonal (A : Set ι) : Matrix ι ι ℝ :=
  open Classical in
  Matrix.diagonal (fun i ↦ if i ∈ A then 1 else 0)

/-- The `(i,j)` entry of `activeDiagonal A` is `1` on the active diagonal and
`0` elsewhere. -/
theorem activeDiagonal_apply (A : Set ι) (i j : ι) :
    (open Classical in
      activeDiagonal A i j = if i = j then if i ∈ A then 1 else 0 else 0) := by
  classical
  -- Expand the diagonal mask so the entry formula is immediate.
  simp [activeDiagonal, Matrix.diagonal_apply]

/-- The diagonal mask `D_I = 1 - D_A` attached to an active set `A`. -/
noncomputable def inactiveDiagonal (A : Set ι) : Matrix ι ι ℝ :=
  1 - activeDiagonal A

/-- The `(i,j)` entry of `inactiveDiagonal A` is `1` on inactive diagonal
coordinates and `0` elsewhere. -/
theorem inactiveDiagonal_apply (A : Set ι) (i j : ι) :
    (open Classical in
      inactiveDiagonal A i j = if i = j then if i ∈ A then 0 else 1 else 0) := by
  classical
  -- Read `D_I = 1 - D_A` entrywise and simplify diagonal and off-diagonal cases.
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ A
    · simp [inactiveDiagonal, activeDiagonal_apply, hi]
    · simp [inactiveDiagonal, activeDiagonal_apply, hi]
  · simp [inactiveDiagonal, activeDiagonal_apply, hij]

variable [Fintype ι]

/-- The reduced Hessian associated to an active set `A` and an ambient Hessian
matrix `H`, defined by the matrix-mask formula `D_I * H * D_I + D_A`. -/
noncomputable def reducedHessian (A : Set ι) (H : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  inactiveDiagonal A * H * inactiveDiagonal A + activeDiagonal A

/-- The reduced Hessian has the source entrywise form: active rows or columns
give the Kronecker delta, and inactive coordinates retain the ambient Hessian
entry. -/
theorem reducedHessian_apply (A : Set ι) (H : Matrix ι ι ℝ) (i j : ι) :
    (open Classical in
      reducedHessian A H i j =
        if i ∈ A ∨ j ∈ A then if i = j then 1 else 0 else H i j) := by
  classical
  -- Normalize `D_I` to a literal diagonal matrix before using the diagonal product formulas.
  have hInactive :
      inactiveDiagonal A = Matrix.diagonal (fun k ↦ if k ∈ A then 0 else 1) := by
    ext k l
    simp [inactiveDiagonal_apply, Matrix.diagonal_apply]
  -- After rewriting both masks entrywise, the remaining work is a finite case split.
  rw [reducedHessian, hInactive]
  by_cases hi : i ∈ A
  · by_cases hj : j ∈ A
    · by_cases hij : i = j
      · simp [activeDiagonal_apply, hj, hij, Matrix.add_apply, mul_assoc]
      · simp [activeDiagonal_apply, hi, hj, hij, Matrix.add_apply, mul_assoc]
    · by_cases hij : i = j
      · simp [activeDiagonal_apply, hj, hij, Matrix.add_apply, mul_assoc]
      · simp [activeDiagonal_apply, hi, hj, hij, Matrix.add_apply, mul_assoc]
  · by_cases hj : j ∈ A
    · by_cases hij : i = j
      · simp [activeDiagonal_apply, hj, hij, Matrix.add_apply, mul_assoc]
      · simp [activeDiagonal_apply, hi, hj, hij, Matrix.add_apply, mul_assoc]
    · by_cases hij : i = j
      · simp [activeDiagonal_apply, hj, hij, Matrix.add_apply, mul_assoc]
      · simp [activeDiagonal_apply, hi, hj, hij, Matrix.add_apply, mul_assoc]

/-- Rewriting `reducedHessian A H` by its defining mask formula recovers
`D_I * H * D_I + D_A`. -/
theorem reducedHessian_eq (A : Set ι) (H : Matrix ι ι ℝ) :
    reducedHessian A H = inactiveDiagonal A * H * inactiveDiagonal A + activeDiagonal A := by
  -- This is exactly the defining matrix-mask formula.
  rfl

end ActiveSet

namespace NonnegativeOrthant

variable {n : ℕ}

/-- The active diagonal `D_A(f)` for the nonnegative-orthant active set of a
point `f`. -/
noncomputable abbrev activeDiagonal
    (f : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  ActiveSet.activeDiagonal (ActiveSet.active (fun i x ↦ x i) f)

/-- The `(i,j)` entry of `activeDiagonal f` is `1` exactly on diagonal
coordinates where `f i = 0`. -/
theorem activeDiagonal_apply
    (f : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    activeDiagonal f i j = if i = j then if f i = 0 then 1 else 0 else 0 := by
  -- Specialize the generic active-set formula and rewrite activity as vanishing.
  simpa [activeDiagonal, ActiveSet.mem_active] using
    (ActiveSet.activeDiagonal_apply (A := ActiveSet.active (fun i x ↦ x i) f) i j)

/-- The inactive diagonal `D_I(f) = 1 - D_A(f)` for the nonnegative-orthant
active set of `f`. -/
noncomputable abbrev inactiveDiagonal
    (f : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  ActiveSet.inactiveDiagonal (ActiveSet.active (fun i x ↦ x i) f)

/-- The `(i,j)` entry of `inactiveDiagonal f` is `1` exactly on diagonal
coordinates where `f i ≠ 0`, and `0` elsewhere. -/
theorem inactiveDiagonal_apply
    (f : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    inactiveDiagonal f i j = if i = j then if f i = 0 then 0 else 1 else 0 := by
  -- Transport the generic inactive-mask entry formula to the orthant coordinates.
  simpa [inactiveDiagonal, ActiveSet.mem_active] using
    (ActiveSet.inactiveDiagonal_apply (A := ActiveSet.active (fun i x ↦ x i) f) i j)

/-
Definition 9.20. The reduced Hessian on the nonnegative orthant is formalized
by `NonnegativeOrthant.reducedHessian`. Its reusable generic active-set matrix
helpers are the `ActiveSet.*` declarations in this file.
-/
/-- The reduced Hessian `H_R(f)` on the nonnegative orthant from
Definition 9.20 is the active-set specialization of
`ActiveSet.reducedHessian`. -/
noncomputable abbrev reducedHessian
    (f : EuclideanSpace ℝ (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ActiveSet.reducedHessian (ActiveSet.active (fun i x ↦ x i) f) H

/-- Definition 9.20. The nonnegative-orthant reduced Hessian has the source
coordinate formula, with active coordinates contributing `δᵢⱼ` and inactive
coordinates retaining the ambient Hessian entry. -/
theorem reducedHessian_apply
    (f : EuclideanSpace ℝ (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    reducedHessian f H i j =
      if f i = 0 ∨ f j = 0 then if i = j then 1 else 0 else H i j := by
  -- Specialize the generic reduced-Hessian entry formula and rewrite activity predicates.
  simpa [reducedHessian, ActiveSet.mem_active] using
    (ActiveSet.reducedHessian_apply
      (A := ActiveSet.active (fun i x ↦ x i) f) H i j)

/-- Helper for Definition 9.20: rewriting `reducedHessian f H` by its defining
mask formula recovers `D_I(f) * H * D_I(f) + D_A(f)`. -/
theorem reducedHessian_eq
    (f : EuclideanSpace ℝ (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) :
    reducedHessian f H = inactiveDiagonal f * H * inactiveDiagonal f + activeDiagonal f := by
  simpa [reducedHessian, inactiveDiagonal, activeDiagonal] using
    ActiveSet.reducedHessian_eq (ActiveSet.active (fun i x ↦ x i) f) H

end NonnegativeOrthant

#check NonnegativeOrthant.reducedHessian
