/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Order.Monotone.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Definition_7_3_extra_1

open Matrix

-- Domain sampling:
-- * source-facing owner: `solvesLevenbergMarquardtNormalEquation`
-- * sampled project declarations in this domain:
--   `solvesLevenbergMarquardtNormalEquation`
--   `levenbergMarquardtAngle_antitoneOn`
--   `levenbergMarquardtRegularizedNormalMatrix`
-- * core/canonical owner in this chapter: the regularized normal-equation relation, with the
--   matrix family `Jᵀ * J + μ • 1` only as supporting data
-- * primitive data: the Jacobian `J`, residual vector `r`, and a family of steps solving the
--   regularized normal equations on the genuine positive damping domain
-- * derived API removed here: the redundant total inverse-based step definition on all `μ : ℝ`
--   whose values outside the positive regime were not source-faithful

section

variable {m n : ℕ}

local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ
local notation "ResidualVector" => EuclideanSpace ℝ (Fin m)
local notation "Step" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Chapter07 Theorem 7.3.1: positive damping makes the regularized normal matrix
positive definite. -/
lemma regularized_normal_matrix_posDef
    (J : JacobianMatrix) {μ : ℝ} (hμ : 0 < μ) :
    (Jᵀ * J + μ • (1 : MatrixN)).PosDef := by
  -- The Gram term is positive semidefinite, while the damping term is positive definite.
  have hDamping : (μ • (1 : MatrixN)).PosDef := by
    simpa using (Matrix.PosDef.smul (Matrix.PosDef.one : (1 : MatrixN).PosDef) hμ)
  simpa [add_comm] using
    Matrix.PosDef.add_posSemidef hDamping (Matrix.posSemidef_conjTranspose_mul_self J)

/-- Helper for Chapter07 Theorem 7.3.1: the damped quadratic model differs from its value at a
normal-equation solution by the positive-definite quadratic gap. -/
lemma regularized_quadratic_gap
    (J : JacobianMatrix) (g : Fin n → ℝ) (s x : Step) {μ : ℝ}
    (hμ : 0 < μ)
    (hs : solvesLevenbergMarquardtNormalEquation J g μ s) :
    let A : MatrixN := Jᵀ * J + μ • (1 : MatrixN)
    (((x ⬝ᵥ A.mulVec x) / 2 + g ⬝ᵥ x) -
        ((s ⬝ᵥ A.mulVec s) / 2 + g ⬝ᵥ s)) =
      ((x - s) ⬝ᵥ A.mulVec (x - s)) / 2 := by
  -- Use symmetry of the positive definite matrix to complete the square exactly.
  let A : MatrixN := Jᵀ * J + μ • (1 : MatrixN)
  have hA : A.PosDef := by
    simpa [A] using regularized_normal_matrix_posDef J hμ
  have hAt : Aᵀ = A := by
    simpa using hA.1.eq
  have hsA : A.mulVec s = -g := by
    simpa [A] using hs
  have hvec : Matrix.vecMul s A = Aᵀ.mulVec s := by
    simpa using (Matrix.vecMul_transpose Aᵀ s)
  have hsym : s ⬝ᵥ A.mulVec x = x ⬝ᵥ A.mulVec s := by
    calc
      s ⬝ᵥ A.mulVec x = Matrix.vecMul s A ⬝ᵥ x := by
        rw [Matrix.dotProduct_mulVec]
      _ = Aᵀ.mulVec s ⬝ᵥ x := by
        rw [hvec]
      _ = A.mulVec s ⬝ᵥ x := by
        rw [hAt]
      _ = x ⬝ᵥ A.mulVec s := by
        rw [dotProduct_comm]
  have hgA : g = -(A.mulVec s) := by
    simpa using (congrArg Neg.neg hsA).symm
  have hsx : g ⬝ᵥ x = -(x ⬝ᵥ A.mulVec s) := by
    calc
      g ⬝ᵥ x = (-(A.mulVec s)) ⬝ᵥ x := by
        rw [hgA]
      _ = -(A.mulVec s ⬝ᵥ x) := by
        rw [neg_dotProduct]
      _ = -(x ⬝ᵥ A.mulVec s) := by
        rw [dotProduct_comm]
  have hss : g ⬝ᵥ s = -(s ⬝ᵥ A.mulVec s) := by
    calc
      g ⬝ᵥ s = (-(A.mulVec s)) ⬝ᵥ s := by
        rw [hgA]
      _ = -(A.mulVec s ⬝ᵥ s) := by
        rw [neg_dotProduct]
      _ = -(s ⬝ᵥ A.mulVec s) := by
        rw [dotProduct_comm]
  have h_expand :
      ((x - s : Step) ⬝ᵥ A.mulVec (x - s : Step)) =
        x ⬝ᵥ A.mulVec x - x ⬝ᵥ A.mulVec s - s ⬝ᵥ A.mulVec x + s ⬝ᵥ A.mulVec s := by
    change (x.ofLp - s.ofLp) ⬝ᵥ A.mulVec (x.ofLp - s.ofLp) =
      x.ofLp ⬝ᵥ A.mulVec x.ofLp - x.ofLp ⬝ᵥ A.mulVec s.ofLp -
        s.ofLp ⬝ᵥ A.mulVec x.ofLp + s.ofLp ⬝ᵥ A.mulVec s.ofLp
    have hsubx :
        (x.ofLp - s.ofLp) ⬝ᵥ A.mulVec x.ofLp =
          x.ofLp ⬝ᵥ A.mulVec x.ofLp - s.ofLp ⬝ᵥ A.mulVec x.ofLp := by
      rw [sub_dotProduct]
    rw [Matrix.mulVec_sub, dotProduct_sub]
    have hsub :
        (x.ofLp - s.ofLp) ⬝ᵥ A.mulVec s.ofLp =
          x.ofLp ⬝ᵥ A.mulVec s.ofLp - s.ofLp ⬝ᵥ A.mulVec s.ofLp := by
      rw [sub_dotProduct]
    rw [hsubx, hsub]
    ring_nf
  calc
    (((x ⬝ᵥ A.mulVec x) / 2 + g ⬝ᵥ x) -
        ((s ⬝ᵥ A.mulVec s) / 2 + g ⬝ᵥ s)) =
        ((x ⬝ᵥ A.mulVec x) - (s ⬝ᵥ A.mulVec s)) / 2 + (g ⬝ᵥ x - g ⬝ᵥ s) := by
      ring
    _ = ((x ⬝ᵥ A.mulVec x) - (s ⬝ᵥ A.mulVec s)) / 2
          + (-(x ⬝ᵥ A.mulVec s) - -(s ⬝ᵥ A.mulVec s)) := by
      rw [hsx, hss]
    _ = ((x ⬝ᵥ A.mulVec x) - 2 * (x ⬝ᵥ A.mulVec s) + (s ⬝ᵥ A.mulVec s)) / 2 := by
      ring_nf
    _ = ((x ⬝ᵥ A.mulVec x) - (x ⬝ᵥ A.mulVec s) - (s ⬝ᵥ A.mulVec x) +
          (s ⬝ᵥ A.mulVec s)) / 2 := by
      rw [hsym]
      ring_nf
    _ = (((x - s) : Step) ⬝ᵥ A.mulVec ((x - s : Step))) / 2 := by
      rw [h_expand]

/-- Helper for Chapter07 Theorem 7.3.1: a positive-damping normal-equation step strictly minimizes
its damped quadratic model. -/
lemma regularized_quadratic_strict_min
    (J : JacobianMatrix) (g : Fin n → ℝ) (s x : Step) {μ : ℝ}
    (hμ : 0 < μ)
    (hs : solvesLevenbergMarquardtNormalEquation J g μ s)
    (hxs : x ≠ s) :
    ((s ⬝ᵥ ((Jᵀ * J + μ • (1 : MatrixN)).mulVec s)) / 2 + g ⬝ᵥ s) <
      ((x ⬝ᵥ ((Jᵀ * J + μ • (1 : MatrixN)).mulVec x)) / 2 + g ⬝ᵥ x) := by
  -- The gap formula reduces strict minimality to positivity of the regularized quadratic form.
  have hA : (Jᵀ * J + μ • (1 : MatrixN)).PosDef :=
    regularized_normal_matrix_posDef J hμ
  have hquad :
      0 < (x - s) ⬝ᵥ ((Jᵀ * J + μ • (1 : MatrixN)).mulVec (x - s)) := by
    have hxsub : ((x - s : Step) : Fin n → ℝ) ≠ 0 := by
      intro hzero
      apply hxs
      ext i
      have hi : x.ofLp i - s.ofLp i = 0 := by
        simpa using congrFun hzero i
      linarith
    simpa using hA.dotProduct_mulVec_pos (x := x - s) hxsub
  have hgap := regularized_quadratic_gap J g s x hμ hs
  have hhalf :
      0 < ((x - s) ⬝ᵥ ((Jᵀ * J + μ • (1 : MatrixN)).mulVec (x - s))) / 2 := by
    exact div_pos hquad (by norm_num)
  have :
      ((x ⬝ᵥ ((Jᵀ * J + μ • (1 : MatrixN)).mulVec x)) / 2 + g ⬝ᵥ x) =
        ((s ⬝ᵥ ((Jᵀ * J + μ • (1 : MatrixN)).mulVec s)) / 2 + g ⬝ᵥ s) +
          (((x - s) ⬝ᵥ ((Jᵀ * J + μ • (1 : MatrixN)).mulVec (x - s))) / 2) := by
    simpa [sub_eq_iff_eq_add'] using hgap
  calc
    ((s ⬝ᵥ ((Jᵀ * J + μ • (1 : MatrixN)).mulVec s)) / 2 + g ⬝ᵥ s) <
        ((s ⬝ᵥ ((Jᵀ * J + μ • (1 : MatrixN)).mulVec s)) / 2 + g ⬝ᵥ s) +
          (((x - s) ⬝ᵥ ((Jᵀ * J + μ • (1 : MatrixN)).mulVec (x - s))) / 2) :=
      lt_add_of_pos_right _ hhalf
    _ = ((x ⬝ᵥ ((Jᵀ * J + μ • (1 : MatrixN)).mulVec x)) / 2 + g ⬝ᵥ x) := by
      simpa [add_comm] using this.symm

/-- Helper for Chapter07 Theorem 7.3.1: changing the damping parameter only adds a scalar multiple
of `‖x‖²` to the damped quadratic model. -/
lemma regularized_quadratic_shift
    (J : JacobianMatrix) (g : Fin n → ℝ) (x : Step) (μ₁ μ₂ : ℝ) :
    ((x ⬝ᵥ ((Jᵀ * J + μ₂ • (1 : MatrixN)).mulVec x)) / 2 + g ⬝ᵥ x) =
      ((x ⬝ᵥ ((Jᵀ * J + μ₁ • (1 : MatrixN)).mulVec x)) / 2 + g ⬝ᵥ x) +
        ((μ₂ - μ₁) / 2) * ‖x‖ ^ 2 := by
  -- Expanding the identity term isolates the damping contribution as `((μ₂ - μ₁) / 2) * ‖x‖²`.
  have hnorm : x ⬝ᵥ x = ‖x‖ ^ 2 := by
    rw [dotProduct]
    simpa [pow_two] using (EuclideanSpace.real_norm_sq_eq x).symm
  have hone : x ⬝ᵥ (1 : MatrixN).mulVec x = ‖x‖ ^ 2 := by
    simpa [Matrix.one_mulVec] using hnorm
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul]
  nth_rewrite 1 [hone]
  nth_rewrite 1 [hone]
  ring_nf

/-- Helper for Chapter07 Theorem 7.3.1: distinct positive damping parameters produce distinct
Levenberg-Marquardt steps when the Gauss-Newton gradient is nonzero. -/
lemma steps_at_distinct_damping_ne
    (J : JacobianMatrix) (r : ResidualVector) (s : ℝ → Step)
    (hgrad : Jᵀ.mulVec r ≠ 0)
    (h_step :
      ∀ ⦃μ : ℝ⦄, 0 < μ → solvesLevenbergMarquardtNormalEquation J (Jᵀ.mulVec r) μ (s μ))
    {μ₁ μ₂ : ℝ} (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (hlt : μ₁ < μ₂) :
    s μ₁ ≠ s μ₂ := by
  -- Equal steps would force the positive scalar `(μ₂ - μ₁)` to annihilate the same vector.
  intro hEq
  have hs₁ :
      (Jᵀ * J + μ₁ • (1 : MatrixN)).mulVec (s μ₁) = -(Jᵀ.mulVec r) := by
    simpa using h_step hμ₁
  have hs₂ :
      (Jᵀ * J + μ₂ • (1 : MatrixN)).mulVec (s μ₁) = -(Jᵀ.mulVec r) := by
    simpa [hEq] using h_step hμ₂
  have hzero :
      ((Jᵀ * J + μ₂ • (1 : MatrixN)) - (Jᵀ * J + μ₁ • (1 : MatrixN))).mulVec (s μ₁) = 0 := by
    rw [Matrix.sub_mulVec, hs₂, hs₁, sub_self]
  have hsZeroFun : ((s μ₁ : Step) : Fin n → ℝ) = 0 := by
    ext i
    have hi : (μ₂ - μ₁) * ((s μ₁ : Step) : Fin n → ℝ) i = 0 := by
      have hcoord := congrFun hzero i
      simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec,
        sub_eq_add_neg, Pi.add_apply, Pi.smul_apply] at hcoord
      ring_nf at hcoord
      nlinarith [hcoord]
    have hδ : μ₂ - μ₁ ≠ 0 := sub_ne_zero.mpr hlt.ne'
    rcases mul_eq_zero.mp hi with hzero | hzero
    · exact (hδ hzero).elim
    · simpa using hzero
  have hsZero : s μ₁ = 0 := by
    ext i
    simpa using congrFun hsZeroFun i
  have : Jᵀ.mulVec r = 0 := by
    have hs₁' := h_step hμ₁
    simpa [hsZero] using hs₁'
  exact hgrad this

/-- Chapter07 Theorem 7.3.1: if the Gauss-Newton gradient `Jᵀ.mulVec r` is nonzero and, for each
positive damping parameter `μ`, the step `s μ` satisfies the regularized normal equation
`(Jᵀ * J + μ • 1).mulVec (s μ) = -(Jᵀ.mulVec r)`, then the Euclidean norm `‖s μ‖` decreases
strictly as `μ` increases on `Set.Ioi 0`. -/
theorem levenbergMarquardtStep_norm_strictAntiOn
    (J : JacobianMatrix) (r : ResidualVector) (s : ℝ → Step)
    (hgrad : Jᵀ.mulVec r ≠ 0)
    (h_step :
      ∀ ⦃μ : ℝ⦄, 0 < μ → solvesLevenbergMarquardtNormalEquation J (Jᵀ.mulVec r) μ (s μ)) :
    StrictAntiOn (fun μ : ℝ ↦ ‖s μ‖) (Set.Ioi 0) := by
  intro μ₁ hμ₁ μ₂ hμ₂ hlt
  -- Compare the same quadratic model at the two LM steps and use the damping shift explicitly.
  have hne : s μ₁ ≠ s μ₂ :=
    steps_at_distinct_damping_ne J r s hgrad h_step hμ₁ hμ₂ hlt
  have hmin₁ :
      ((s μ₁ ⬝ᵥ ((Jᵀ * J + μ₁ • (1 : MatrixN)).mulVec (s μ₁))) / 2 +
          Jᵀ.mulVec r ⬝ᵥ s μ₁) <
        ((s μ₂ ⬝ᵥ ((Jᵀ * J + μ₁ • (1 : MatrixN)).mulVec (s μ₂))) / 2 +
          Jᵀ.mulVec r ⬝ᵥ s μ₂) :=
    regularized_quadratic_strict_min J (Jᵀ.mulVec r) (s μ₁) (s μ₂) hμ₁ (h_step hμ₁) hne.symm
  have hmin₂ :
      ((s μ₂ ⬝ᵥ ((Jᵀ * J + μ₂ • (1 : MatrixN)).mulVec (s μ₂))) / 2 +
          Jᵀ.mulVec r ⬝ᵥ s μ₂) <
        ((s μ₁ ⬝ᵥ ((Jᵀ * J + μ₂ • (1 : MatrixN)).mulVec (s μ₁))) / 2 +
          Jᵀ.mulVec r ⬝ᵥ s μ₁) :=
    regularized_quadratic_strict_min J (Jᵀ.mulVec r) (s μ₂) (s μ₁) hμ₂ (h_step hμ₂) hne
  let q11 :=
    ((s μ₁ ⬝ᵥ ((Jᵀ * J + μ₁ • (1 : MatrixN)).mulVec (s μ₁))) / 2 +
      Jᵀ.mulVec r ⬝ᵥ s μ₁)
  let q12 :=
    ((s μ₂ ⬝ᵥ ((Jᵀ * J + μ₁ • (1 : MatrixN)).mulVec (s μ₂))) / 2 +
      Jᵀ.mulVec r ⬝ᵥ s μ₂)
  let q21 :=
    ((s μ₁ ⬝ᵥ ((Jᵀ * J + μ₂ • (1 : MatrixN)).mulVec (s μ₁))) / 2 +
      Jᵀ.mulVec r ⬝ᵥ s μ₁)
  let q22 :=
    ((s μ₂ ⬝ᵥ ((Jᵀ * J + μ₂ • (1 : MatrixN)).mulVec (s μ₂))) / 2 +
      Jᵀ.mulVec r ⬝ᵥ s μ₂)
  have hshift₁ : q21 = q11 + ((μ₂ - μ₁) / 2) * ‖s μ₁‖ ^ 2 := by
    simpa [q11, q21] using regularized_quadratic_shift J (Jᵀ.mulVec r) (s μ₁) μ₁ μ₂
  have hshift₂ : q22 = q12 + ((μ₂ - μ₁) / 2) * ‖s μ₂‖ ^ 2 := by
    simpa [q12, q22] using regularized_quadratic_shift J (Jᵀ.mulVec r) (s μ₂) μ₁ μ₂
  have hmin₁' : q11 < q12 := by
    simpa [q11, q12] using hmin₁
  have hmin₂' : q22 < q21 := by
    simpa [q21, q22] using hmin₂
  have hshifted :
      q12 + ((μ₂ - μ₁) / 2) * ‖s μ₂‖ ^ 2 <
      q11 + ((μ₂ - μ₁) / 2) * ‖s μ₁‖ ^ 2 := by
    linarith [hmin₂', hshift₁, hshift₂]
  have hscaled :
      ((μ₂ - μ₁) / 2) * ‖s μ₂‖ ^ 2 < ((μ₂ - μ₁) / 2) * ‖s μ₁‖ ^ 2 := by
    linarith [hmin₁', hshifted]
  have hsq : ‖s μ₂‖ ^ 2 < ‖s μ₁‖ ^ 2 := by
    have hδ : 0 < (μ₂ - μ₁) / 2 := by
      linarith
    by_contra hsq'
    have hle : ‖s μ₁‖ ^ 2 ≤ ‖s μ₂‖ ^ 2 := le_of_not_gt hsq'
    have hmul :
        ((μ₂ - μ₁) / 2) * ‖s μ₁‖ ^ 2 ≤ ((μ₂ - μ₁) / 2) * ‖s μ₂‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hle hδ.le
    linarith
  nlinarith [hsq, norm_nonneg (s μ₁), norm_nonneg (s μ₂)]

end
