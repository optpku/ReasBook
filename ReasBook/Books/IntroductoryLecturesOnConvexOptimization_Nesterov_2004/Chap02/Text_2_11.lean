/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_5_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient MatrixOrder SmoothConvex

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "p" => normSeminorm ℝ E

/- Primary domain: Euclidean smooth convex objectives.

Source/core/bridge triage:
* source-facing: the hard instance `quadraticHardInstanceFamily (L : ℝ) k`;
  together with the textbook Hessian sandwich
  `0 ≤ ∇² (quadraticHardInstanceFamily (L : ℝ) k) x ≤ L • 1`;
* core/canonical: `quadraticHardInstanceFamily (L : ℝ) k ∈ 𝓕[L, p]¹¹`;
* bridge/view: the Hessian-quadratic-form characterization
  `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded`.

Relevant owner-style declarations sampled in this domain:
* `quadraticHardInstanceFamily` in `Definition_2_10`;
* `quadraticObjective` and `quadraticObjective_gradient_eq` in `Definition_1_9_1` /
  `Proposition_1_5_7`;
* `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded` in `Theorem_2_6`;
* `hessianMatrix_toEuclideanLin` and
  `fderiv_gradient_isSymmetric_of_contDiffAt` in Chapter 1 Hessian API.

Primitive data:
- the hard instance `quadraticHardInstanceFamily (L : ℝ) k : E → ℝ`.

Derived API:
- the source-facing Hessian quadratic-form and Loewner bounds of Text 2.11;
- the canonical owner-membership corollary
  `quadraticHardInstanceFamily (L : ℝ) k ∈ 𝓕[L, p]¹¹`;
- convexity and Euclidean `L`-Lipschitz continuity of the gradient as owner-derived
  consequences.
-/

private theorem quadraticObjective_contDiff
    {m : ℕ} (α : ℝ) (a : EuclideanSpace ℝ (Fin m))
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) :
    ContDiff ℝ 2 (quadraticObjective α a A) := by
  obtain ⟨hcontDiff, _⟩ :=
    symmetric_quadratic_contDiff_and_gradient_lipschitz α a A hA
  rw [show (2 : WithTop ℕ∞) = (1 : ℕ) + 1 by norm_num, contDiff_succ_iff_hasFDerivAt]
  refine ⟨fun x ↦ innerSL ℝ (a + A.toEuclideanLin x), ?_, ?_⟩
  · have hAffine :
        ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin m) ↦ a + A.toEuclideanLin x) := by
      simpa [Pi.add_apply, add_assoc, add_comm, add_left_comm] using
        contDiff_const.add
          (ContinuousLinearMap.contDiff A.toEuclideanLin.toContinuousLinearMap)
    exact (innerSL ℝ).contDiff.comp hAffine
  · intro x
    have hgrad :
        HasGradientAt (quadraticObjective α a A) (∇ (quadraticObjective α a A) x) x :=
      (hcontDiff.contDiffAt.differentiableAt one_ne_zero).hasGradientAt
    rw [quadraticObjective_gradient_eq α a A hA] at hgrad
    simpa using hgrad.hasFDerivAt

private theorem smoothLowerBoundFunction_contDiff (L : ℝ) (k : ℕ+) :
    ContDiff ℝ 2 (smoothLowerBoundFunction L k) := by
  unfold smoothLowerBoundFunction
  simpa using
    quadraticObjective_contDiff 0
      (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ))
      ((L / 4) • pathTridiagonalMatrix k)
      ((pathTridiagonalMatrix_isSymm k).smul (L / 4))

private def hardInstancePrefix (k : Fin n) (x : E) :
    EuclideanSpace ℝ (Fin (k.1 + 1)) :=
  (EuclideanSpace.equiv (Fin (k.1 + 1)) ℝ).symm
    (fun i ↦ x (Fin.castLE (Nat.succ_le_of_lt k.2) i))

/-- Helper for Text 2.11: the prefix restriction is the continuous linear map that keeps the
first `k.1 + 1` coordinates. -/
private def hardInstancePrefixLinear (k : Fin n) :
    E →L[ℝ] EuclideanSpace ℝ (Fin (k.1 + 1)) :=
  ((EuclideanSpace.equiv (Fin (k.1 + 1)) ℝ).symm.toContinuousLinearEquiv :
      (Fin (k.1 + 1) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (k.1 + 1))).toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i : Fin (k.1 + 1) =>
        (ContinuousLinearMap.proj (R := ℝ)
          (i := Fin.castLE (Nat.succ_le_of_lt k.2) i) :
            (Fin n → ℝ) →L[ℝ] ℝ)).comp
      ((EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap))

/-- Helper for Text 2.11: the linear prefix map evaluates to the same coordinates as the
source-facing prefix restriction. -/
private theorem hardInstancePrefix_eq_linear_apply (k : Fin n) (x : E) :
    hardInstancePrefixLinear k x = hardInstancePrefix k x := by
  ext i
  simp [hardInstancePrefixLinear, hardInstancePrefix]

private theorem hardInstancePrefix_contDiff (k : Fin n) :
    ContDiff ℝ 2 (hardInstancePrefix k) := by
  -- Use the continuous linear prefix map, then return to the source-facing definition.
  simpa [funext (hardInstancePrefix_eq_linear_apply k)] using
    ContinuousLinearMap.contDiff (hardInstancePrefixLinear k)

/-- Helper for Text 2.11: a `C²` scalar field has a differentiable gradient. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {m : Type*} [NormedAddCommGroup m] [InnerProductSpace ℝ m] [CompleteSpace m]
    {f : m → ℝ} {x : m} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  let D : StrongDual ℝ m →L[ℝ] m :=
    (InnerProductSpace.toDual ℝ m).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite the gradient through the Riesz map so the chain rule applies directly.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Text 2.11: precomposing a differentiable scalar field with a continuous linear map
pulls back its gradient by the adjoint. -/
private theorem hasGradientAt_comp_continuousLinearMap
    {m : Type*} [NormedAddCommGroup m] [InnerProductSpace ℝ m] [CompleteSpace m]
    {f : m → ℝ} (A : E →L[ℝ] m) {x : E}
    (hf : DifferentiableAt ℝ f (A x)) :
    HasGradientAt (f ∘ A) (A.adjoint (∇ f (A x))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hcomp := (hf.hasGradientAt.hasFDerivAt).comp x A.hasFDerivAt
  convert hcomp using 1
  ext y
  calc
    inner ℝ (A.adjoint (∇ f (A x))) y = inner ℝ y (A.adjoint (∇ f (A x))) := by
      rw [real_inner_comm]
    _ = inner ℝ (A y) (∇ f (A x)) := A.adjoint_inner_right y (∇ f (A x))
    _ = inner ℝ (∇ f (A x)) (A y) := by
      rw [real_inner_comm]

/-- Helper for Text 2.11: precomposing by a continuous linear map transports the Hessian
quadratic form to the image direction. -/
private theorem hessian_quadratic_form_comp_continuousLinearMap
    {m : Type*} [NormedAddCommGroup m] [InnerProductSpace ℝ m] [CompleteSpace m]
    {f : m → ℝ} (A : E →L[ℝ] m) (hf : ContDiff ℝ 2 f) (x h : E) :
    inner ℝ (hessian (f ∘ A) x h) h =
      inner ℝ (hessian f (A x) (A h)) (A h) := by
  have hgradEq :
      ∇ (f ∘ A) = fun y : E ↦ A.adjoint (∇ f (A y)) := by
    refine gradient_eq ?_
    intro y
    exact hasGradientAt_comp_continuousLinearMap A
      (hf.contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
  have hgradDiff : DifferentiableAt ℝ (∇ f) (A x) :=
    differentiableAt_gradient_of_contDiffAt_two hf.contDiffAt
  have hinner :
      HasFDerivAt (fun y : E ↦ ∇ f (A y)) ((hessian f (A x)).comp A) x := by
    -- Differentiate the gradient after the linear prefix map.
    change HasFDerivAt (∇ f ∘ A) ((hessian f (A x)).comp A) x
    exact hgradDiff.hasFDerivAt.comp x A.hasFDerivAt
  have houter :
      HasFDerivAt (fun y : E ↦ A.adjoint (∇ f (A y)))
        ((A.adjoint).comp ((hessian f (A x)).comp A)) x := by
    -- The adjoint itself is linear, so its derivative is constant.
    exact A.adjoint.hasFDerivAt.comp x hinner
  have hderivEq :
      fderiv ℝ (fun y : E ↦ A.adjoint (∇ f (A y))) x =
        (A.adjoint).comp ((hessian f (A x)).comp A) := houter.fderiv
  -- Replace the pulled-back gradient by its derivative formula.
  suffices hmain :
      inner ℝ ((A.adjoint) ((hessian f (A x)).comp A h)) h =
        inner ℝ (hessian f (A x) (A h)) (A h) by
    simpa [hessian, hgradEq, hderivEq] using hmain
  calc
    inner ℝ ((A.adjoint) ((hessian f (A x)).comp A h)) h =
        inner ℝ h ((A.adjoint) ((hessian f (A x)).comp A h)) := by
          rw [real_inner_comm]
    _ = inner ℝ (A h) ((hessian f (A x)).comp A h) :=
        A.adjoint_inner_right h ((hessian f (A x)).comp A h)
    _ = inner ℝ (hessian f (A x) (A h)) (A h) := by
          rw [ContinuousLinearMap.comp_apply, real_inner_comm]

private theorem quadraticHardInstanceFamily_contDiff (L : NNReal) (k : Fin n) :
    ContDiff ℝ 2 (quadraticHardInstanceFamily (L : ℝ) k) := by
  unfold quadraticHardInstanceFamily
  exact
    (smoothLowerBoundFunction_contDiff (L : ℝ) (Nat.succPNat k.1)).comp
      (hardInstancePrefix_contDiff k)

/-- Helper for Text 2.11: the Euclidean inner product with the prefix tridiagonal matrix agrees
with the corresponding coordinate `dotProduct`. -/
private theorem pathTridiagonal_inner_eq_dotProduct_mulVec_prefix
    (k : Fin n) (y : EuclideanSpace ℝ (Fin (k.1 + 1))) :
    inner ℝ (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) y =
      dotProduct y (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1)) y) := by
  -- Rewrite the Euclidean inner product as the coordinate dot product used by `Matrix.mulVec`.
  calc
    inner ℝ (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) y =
        dotProduct y (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) := by
          simpa [dotProduct_comm] using
            (EuclideanSpace.inner_eq_star_dotProduct
              (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) y)
    _ = dotProduct y (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1)) y) := by
          rw [Matrix.toEuclideanLin_apply]
          rfl

/-- Helper for Text 2.11: each tridiagonal entry contributes its diagonal term and subtracts its
two possible neighboring terms. -/
private theorem pathTridiagonal_entry_mul_eq_diag_sub_neighbors
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) (i j : Fin (m + 1)) :
    pathTridiagonalMatrix (Nat.succPNat m) i j * y j =
      (if i = j then 2 * y j else 0) -
      (if (i : ℕ) + 1 = (j : ℕ) then y j else 0) -
      (if (j : ℕ) + 1 = (i : ℕ) then y j else 0) := by
  -- Split the matrix entry into the diagonal, forward-edge, and backward-edge cases.
  by_cases hij : i = j
  · subst hij
    simp [pathTridiagonalMatrix_apply]
  · by_cases hnext : (i : ℕ) + 1 = (j : ℕ)
    · have hprev : ¬(j : ℕ) + 1 = (i : ℕ) := by
        omega
      simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]
    · by_cases hprev : (j : ℕ) + 1 = (i : ℕ)
      · simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]
      · simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]

/-- Helper for Text 2.11: the diagonal part of the tridiagonal quadratic form is exactly
`2 * ∑ y_i^2`. -/
private theorem pathTridiagonal_diag_sum
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) :
    (∑ x : Fin (m + 1), y x * ∑ x1 : Fin (m + 1), if x = x1 then 2 * y x1 else 0) =
      2 * ∑ x : Fin (m + 1), y x ^ 2 := by
  -- Only the diagonal entry survives in each inner sum, so the result is twice the square sum.
  simp [pow_two]
  ring_nf
  rw [Finset.sum_mul]

/-- Helper for Text 2.11: the forward off-diagonal contribution is the chain sum
`∑ y_i y_{i+1}`. -/
private theorem pathTridiagonal_forward_sum
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) :
    (∑ x : Fin (m + 1), y x * ∑ x1 : Fin (m + 1),
      if (x : ℕ) + 1 = (x1 : ℕ) then y x1 else 0) =
      ∑ i : Fin m, y (Fin.castLE (Nat.le_succ m) i) * y i.succ := by
  -- Split off the last coordinate, whose forward neighbor does not exist, and identify the
  -- remaining inner sums with the successor coordinates.
  rw [Fin.sum_univ_castSucc]
  have hlast :
      (∑ x1 : Fin (m + 1), if ↑(Fin.last m) + 1 = (x1 : ℕ) then y x1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hEq : ¬m + 1 = (x : ℕ) := (Nat.ne_of_lt x.2).symm
    simp [Fin.val_last, hEq]
  rw [hlast, mul_zero, add_zero]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hinner :
      (∑ x1 : Fin (m + 1), if ↑x.castSucc + 1 = (x1 : ℕ) then y x1 else 0) = y x.succ := by
    rw [Fintype.sum_eq_single x.succ]
    · simp
    · intro z hz
      by_cases hEq : ↑x + 1 = (z : ℕ)
      · exfalso
        apply hz
        ext
        simpa using hEq.symm
      · simp [hEq]
  rw [hinner]
  congr 1

/-- Helper for Text 2.11: the backward off-diagonal contribution is the same chain sum
`∑ y_i y_{i+1}`. -/
private theorem pathTridiagonal_backward_sum
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) :
    (∑ x : Fin (m + 1), y x * ∑ x1 : Fin (m + 1),
      if (x1 : ℕ) + 1 = (x : ℕ) then y x1 else 0) =
      ∑ i : Fin m, y (Fin.castLE (Nat.le_succ m) i) * y i.succ := by
  -- Split off the first coordinate, whose backward neighbor does not exist, and match each
  -- remaining inner sum with the predecessor coordinate.
  rw [Fin.sum_univ_succ]
  -- The head contribution vanishes because no index precedes `0`.
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.add_eq_zero_iff, Fin.val_eq_zero_iff,
    one_ne_zero, and_false, ↓reduceIte, Finset.sum_const_zero, mul_zero, Fin.val_succ,
    Nat.add_right_cancel_iff, zero_add]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hinner :
      (∑ x1 : Fin (m + 1), if (x1 : ℕ) = x then y x1 else 0) = y x.castSucc := by
    rw [Fintype.sum_eq_single x.castSucc]
    · simp
    · intro z hz
      by_cases hEq : (z : ℕ) = x
      · exfalso
        apply hz
        ext
        simpa using hEq
      · simp [hEq]
  rw [hinner]
  simpa [show y (Fin.castLE (Nat.le_succ m) x) = y x.castSucc by rfl] using
    (mul_comm (y x.castSucc) (y x.succ)).symm

/-- Helper for Text 2.11: the path tridiagonal quadratic form has the normal form
`2 * ∑ y_i^2 - 2 * ∑ y_i y_{i+1}` on the active prefix coordinates. -/
private theorem pathTridiagonal_dotProduct_eq_normal_form
    (k : Fin n) (y : EuclideanSpace ℝ (Fin (k.1 + 1))) :
    dotProduct y (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1)) y) =
      2 * (∑ i : Fin (k.1 + 1), y i ^ 2) -
        2 * ∑ i : Fin k.1, y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ := by
  -- Expand each tridiagonal entry into one diagonal and two neighboring contributions, then
  -- evaluate those three sums separately.
  calc
    dotProduct y (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1)) y) =
        ∑ x : Fin (k.1 + 1), y x * ∑ x1 : Fin (k.1 + 1),
          pathTridiagonalMatrix (Nat.succPNat k.1) x x1 * y x1 := rfl
    _ = ∑ x : Fin (k.1 + 1), y x *
          ∑ x1 : Fin (k.1 + 1),
            ((if x = x1 then 2 * y x1 else 0) -
              (if (x : ℕ) + 1 = (x1 : ℕ) then y x1 else 0) -
              (if (x1 : ℕ) + 1 = (x : ℕ) then y x1 else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x1 hx1
          rw [pathTridiagonal_entry_mul_eq_diag_sub_neighbors y x x1]
    _ = ∑ x : Fin (k.1 + 1),
          ((y x * ∑ x1 : Fin (k.1 + 1), if x = x1 then 2 * y x1 else 0) -
            (y x * ∑ x1 : Fin (k.1 + 1), if (x : ℕ) + 1 = (x1 : ℕ) then y x1 else 0) -
            (y x * ∑ x1 : Fin (k.1 + 1), if (x1 : ℕ) + 1 = (x : ℕ) then y x1 else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          ring
    _ = (∑ x : Fin (k.1 + 1), y x * ∑ x1 : Fin (k.1 + 1), if x = x1 then 2 * y x1 else 0) -
          (∑ x : Fin (k.1 + 1), y x * ∑ x1 : Fin (k.1 + 1),
            if (x : ℕ) + 1 = (x1 : ℕ) then y x1 else 0) -
          (∑ x : Fin (k.1 + 1), y x * ∑ x1 : Fin (k.1 + 1),
            if (x1 : ℕ) + 1 = (x : ℕ) then y x1 else 0) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = 2 * (∑ i : Fin (k.1 + 1), y i ^ 2) -
          2 * ∑ i : Fin k.1, y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ := by
          rw [pathTridiagonal_diag_sum, pathTridiagonal_forward_sum, pathTridiagonal_backward_sum]
          ring

/-- Helper for Text 2.11: the endpoint-plus-edge chain expression has the same normal form
`2 * ∑ y_i^2 - 2 * ∑ y_i y_{i+1}`. -/
private theorem chain_expression_eq_normal_form
    (k : Fin n) (y : EuclideanSpace ℝ (Fin (k.1 + 1))) :
    y 0 ^ 2 +
      (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i) - y i.succ) ^ 2) +
      y (Fin.last k.1) ^ 2 =
        2 * (∑ i : Fin (k.1 + 1), y i ^ 2) -
          2 * ∑ i : Fin k.1, y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ := by
  -- Expand the edge squares, then rewrite the full prefix square sum once from the left endpoint
  -- and once from the right endpoint.
  have hcast_eq :
      (∑ i : Fin (k.1 + 1), y i ^ 2) =
        (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) + (y (Fin.last k.1)) ^ 2 := by
    calc
      (∑ i : Fin (k.1 + 1), y i ^ 2) =
          (∑ i : Fin k.1, y i.castSucc ^ 2) + (y (Fin.last k.1)) ^ 2 := by
            rw [Fin.sum_univ_castSucc]
      _ = (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) +
            (y (Fin.last k.1)) ^ 2 := by
            congr 1
  have hsucc_eq :
      (∑ i : Fin (k.1 + 1), y i ^ 2) =
        (y 0) ^ 2 + (∑ i : Fin k.1, (y i.succ) ^ 2) := by
    rw [Fin.sum_univ_succ]
  have hexpand :
      (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i) - y i.succ) ^ 2) =
        (∑ i : Fin k.1, ((y (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 -
          2 * (y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ) + (y i.succ) ^ 2)) := by
    -- Rewrite each edge square into the standard quadratic normal form.
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  have hsum_expand :
      (∑ i : Fin k.1, ((y (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 -
        2 * (y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ) + (y i.succ) ^ 2)) =
        (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) -
          2 * (∑ i : Fin k.1, y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ) +
          (∑ i : Fin k.1, (y i.succ) ^ 2) := by
    -- Separate the square, cross, and successor-square sums before the final algebra step.
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  nlinarith [hcast_eq, hsucc_eq, hexpand, hsum_expand]

/-- Helper for Text 2.11: on the active prefix coordinates, the path tridiagonal quadratic form is
exactly the endpoint-plus-edge chain expression from Nesterov's proof. -/
private theorem pathTridiagonal_quadratic_form_eq_chain_prefix
    (k : Fin n) (y : EuclideanSpace ℝ (Fin (k.1 + 1))) :
    inner ℝ (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) y =
      y 0 ^ 2 +
        (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i) - y i.succ) ^ 2) +
        y (Fin.last k.1) ^ 2 := by
  -- Route correction: move the algebraic core to the native prefix space, where both sides share
  -- the same normal form.
  calc
    inner ℝ (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) y =
        dotProduct y (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1)) y) := by
          rw [pathTridiagonal_inner_eq_dotProduct_mulVec_prefix]
    _ = 2 * (∑ i : Fin (k.1 + 1), y i ^ 2) -
          2 * ∑ i : Fin k.1, y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ := by
          rw [pathTridiagonal_dotProduct_eq_normal_form]
    _ = y 0 ^ 2 +
          (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i) - y i.succ) ^ 2) +
          y (Fin.last k.1) ^ 2 := by
          symm
          rw [chain_expression_eq_normal_form]

/-- Helper for Text 2.11: the quadratic form of the path tridiagonal matrix on the prefix
coordinates is exactly Nesterov's endpoint-plus-edge chain form. -/
private theorem pathTridiagonal_quadratic_form_eq_chain
    (k : Fin n) (h : E) :
    inner ℝ
      (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin (hardInstancePrefix k h)))
      (hardInstancePrefix k h) =
        nesterovChainQuadraticForm k h := by
  -- Instantiate the native-prefix identity at the restricted vector `hardInstancePrefix k h`.
  simpa [nesterovChainQuadraticForm, hardInstancePrefix] using
    pathTridiagonal_quadratic_form_eq_chain_prefix k (hardInstancePrefix k h)

/-- Helper for Text 2.11: the Hessian quadratic form of the hard instance is the source-facing
chain expression from the textbook proof. -/
private theorem quadraticHardInstanceFamily_hessian_chain_formula
    (L : NNReal) (k : Fin n) (x h : E) :
    inner ℝ (hessian (quadraticHardInstanceFamily (L : ℝ) k) x h) h =
      ((L : ℝ) / 4) * nesterovChainQuadraticForm k h := by
  -- Route correction: Proposition 2.2 now exports the owner bridge only after the explicit chain
  -- formula is supplied, so Text 2.11 has to establish that source-facing identity first.
  have hcomp :=
    hessian_quadratic_form_comp_continuousLinearMap
      (hardInstancePrefixLinear k)
      (smoothLowerBoundFunction_contDiff (L : ℝ) (Nat.succPNat k.1))
      x h
  have hhess :
      (hessian (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
          (hardInstancePrefix k x) : _ →ₗ[ℝ] _) =
        (((((L : ℝ) / 4) • pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin) :
          _ →ₗ[ℝ] _) := by
    calc
      (hessian (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
          (hardInstancePrefix k x) : _ →ₗ[ℝ] _) =
          (∇² (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
            (hardInstancePrefix k x)).toEuclideanLin := by
              symm
              simpa using
                hessianMatrix_toEuclideanLin
                  (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
                  (hardInstancePrefix k x)
      _ = (((((L : ℝ) / 4) • pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin) :
            _ →ₗ[ℝ] _) := by
              rw [smoothLowerBoundFunction_hessian_eq_tridiagonal]
  have hhess_apply :
      hessian (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
          (hardInstancePrefix k x) (hardInstancePrefixLinear k h) =
        ((((L : ℝ) / 4) • pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin)
          (hardInstancePrefixLinear k h) := by
    exact
      congrArg
        (fun T :
          EuclideanSpace ℝ (Fin (k.1 + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k.1 + 1)) ↦
            T (hardInstancePrefixLinear k h))
        hhess
  have hscale :
      ((((L : ℝ) / 4) • pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin
        (hardInstancePrefixLinear k h)) =
          ((L : ℝ) / 4) •
            (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin)
              (hardInstancePrefixLinear k h)) := by
    rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply, Matrix.smul_mulVec,
      WithLp.toLp_smul]
  -- First transport the Hessian quadratic form through the prefix map, then identify the constant
  -- tridiagonal Hessian operator and finally rewrite it into the chain expression.
  calc
    inner ℝ (hessian (quadraticHardInstanceFamily (L : ℝ) k) x h) h =
        inner ℝ
          (hessian (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
            (hardInstancePrefix k x) (hardInstancePrefixLinear k h))
          (hardInstancePrefixLinear k h) := by
            simpa [quadraticHardInstanceFamily, hardInstancePrefix_eq_linear_apply] using hcomp
    _ = inner ℝ
          ((((L : ℝ) / 4) • pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin
            (hardInstancePrefixLinear k h))
          (hardInstancePrefixLinear k h) := by
            rw [hhess_apply]
    _ = ((L : ℝ) / 4) * inner ℝ
          (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin)
            (hardInstancePrefixLinear k h))
          (hardInstancePrefixLinear k h) := by
            rw [hscale]
            rw [real_inner_smul_left]
    _ = ((L : ℝ) / 4) * nesterovChainQuadraticForm k h := by
            simpa [hardInstancePrefix_eq_linear_apply] using
              congrArg (((L : ℝ) / 4) * ·) (pathTridiagonal_quadratic_form_eq_chain k h)

/-- Companion quadratic-form version of Text 2.11: the hard instance Hessian is nonnegative and
bounded above by `L` in every Euclidean direction. -/
theorem quadraticHardInstanceFamily_hessian_quadratic_form_bounded
    (L : NNReal) (k : Fin n) (x h : E) :
    0 ≤ inner ℝ (hessian (quadraticHardInstanceFamily (L : ℝ) k) x h) h ∧
      inner ℝ (hessian (quadraticHardInstanceFamily (L : ℝ) k) x h) h ≤
        (L : ℝ) * ‖h‖ ^ (2 : ℕ) := by
  have hEq := quadraticHardInstanceFamily_hessian_chain_formula L k x h
  constructor
  · -- The chain quadratic form is a sum of squares.
    nlinarith [L.2, hEq, nesterovChainQuadraticForm_nonneg k h]
  · -- Proposition 2.2 bounds the chain form by `4 ‖h‖²`, which matches the Hessian scaling.
    nlinarith [L.2, hEq, nesterovChainQuadraticForm_le_four_mul_norm_sq k h]

/-- Text 2.11: for every `k : Fin n`, representing the textbook index
`k.1 + 1 ∈ {1, ..., n}`, the Hessian matrix of the hard instance `f_k` satisfies
`0 ≤ ∇² f_k(x) ≤ L I_n` for every `x ∈ ℝⁿ`. -/
theorem quadraticHardInstanceFamily_hessian_loewner_bounds
    (L : NNReal) (k : Fin n) (x : E) :
    0 ≤ ∇² (quadraticHardInstanceFamily (L : ℝ) k) x ∧
      ∇² (quadraticHardInstanceFamily (L : ℝ) k) x ≤ (L : ℝ) • (1 : Mat) := by
  let f : E → ℝ := quadraticHardInstanceFamily (L : ℝ) k
  have hcont : ContDiff ℝ 2 f := by
    simpa [f] using quadraticHardInstanceFamily_contDiff L k
  have hquad :
      ∀ h : E,
        0 ≤ inner ℝ (hessian f x h) h ∧
          inner ℝ (hessian f x h) h ≤ (L : ℝ) * ‖h‖ ^ (2 : ℕ) := by
    intro h
    simpa [f] using quadraticHardInstanceFamily_hessian_quadratic_form_bounded L k x h
  constructor
  · rw [Matrix.nonneg_iff_posSemidef, ← Matrix.isPositive_toEuclideanLin_iff]
    rw [LinearMap.isPositive_iff, hessianMatrix_toEuclideanLin]
    constructor
    · simpa [f] using fderiv_gradient_isSymmetric_of_contDiffAt hcont.contDiffAt
    · intro h
      exact (hquad h).1
  · refine sub_nonneg.mp ?_
    rw [Matrix.nonneg_iff_posSemidef, ← Matrix.isPositive_toEuclideanLin_iff]
    have hpos :
        (((L : ℝ) • (1 : E →L[ℝ] E) - hessian f x) : E →ₗ[ℝ] E).IsPositive := by
      rw [LinearMap.isPositive_iff]
      constructor
      · exact
          (LinearMap.isPositive_one.smul_of_nonneg L.2).isSymmetric.sub
            (fderiv_gradient_isSymmetric_of_contDiffAt hcont.contDiffAt)
      · intro h
        have hh' : 0 ≤ (L : ℝ) * ‖h‖ ^ (2 : ℕ) - inner ℝ (hessian f x h) h := by
          linarith [(hquad h).2]
        simpa [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K] using hh'
    have hbridge :
        (((L : ℝ) • (1 : Mat) - ∇² f x).toEuclideanLin : E →ₗ[ℝ] E) =
          (((L : ℝ) • (1 : E →L[ℝ] E) - hessian f x) : E →ₗ[ℝ] E) := by
      calc
        (((L : ℝ) • (1 : Mat) - ∇² f x).toEuclideanLin : E →ₗ[ℝ] E) =
            (L : ℝ) • LinearMap.id - ((∇² f x).toEuclideanLin : E →ₗ[ℝ] E) := by
              simp
        _ = (L : ℝ) • LinearMap.id - (hessian f x : E →ₗ[ℝ] E) := by
              rw [hessianMatrix_toEuclideanLin]
        _ = (((L : ℝ) • (1 : E →L[ℝ] E) - hessian f x) : E →ₗ[ℝ] E) := by
              ext z
              simp
    rw [hbridge]
    exact hpos

/-- Text 2.11 in canonical owner form: the hard instance `f_k` satisfies the chapter owner
predicate `𝓕_L^{1,1}(ℝⁿ)`, so its convexity and Euclidean `L`-Lipschitz gradient are available
from the canonical smooth-convex API. -/
theorem quadraticHardInstanceFamily_mem_smooth_convex_objective
    (L : NNReal) (k : Fin n) :
    quadraticHardInstanceFamily (L : ℝ) k ∈ 𝓕[L, p]¹¹ := by
  let f : E → ℝ := quadraticHardInstanceFamily (L : ℝ) k
  have hcont : ContDiff ℝ 2 f := by
    simpa [f] using quadraticHardInstanceFamily_contDiff L k
  refine (convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded hcont).2 ?_
  intro x h
  simpa [f] using quadraticHardInstanceFamily_hessian_quadratic_form_bounded L k x h
