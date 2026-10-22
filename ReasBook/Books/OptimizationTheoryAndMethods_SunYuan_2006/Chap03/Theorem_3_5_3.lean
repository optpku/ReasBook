/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Algorithm_3_5_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1
import OptimizationTheoryAndMethods_SunYuan_2006.Matrix.UnitLowerTriangular

noncomputable section

open Matrix

section NegativeCurvaturePivotDirection

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Hessian" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling pass:
-- * primary domain: negative-curvature directions produced from the LDL pivot data in
--   Algorithm 3.5.2 for a Euclidean Hessian matrix;
-- * sampled source/core owners:
--   `negativeCurvaturePivotScores` / `negativeCurvatureUnitVector` and the Step 3 direction
--   constructor from `Algorithm_3_5_2`,
--   `IsNegativeCurvatureDirectionAt` / `hessianQuadraticAt` from `Definition_3_5_1`,
--   `IsDescentDirectionAt` / `IsDescentDirectionAt.exists_localDecrease` from
--   `Chapter01/Definition_1_4_3`,
--   and `Matrix.IsUnitLowerTriangular` from `Matrix/UnitLowerTriangular`;
-- * owner abstraction chosen here: the algorithmic primitive data is owned by
--   the pivot score and solve equation, while the mathematical conclusions are owned by
--   `IsNegativeCurvatureDirectionAt` and `IsDescentDirectionAt`;
-- * primitive data vs. derived API: for part (1), the source-facing primitive inputs are just
--   the selected pivot `t`, the negativity of `negativeCurvaturePivotScores dDiag eDiag t`,
--   and the solve equation `Lkᵀ dk = e_t`; the negative-curvature and local-decrease
--   conclusions are derived API on top of those owners;
-- * bridge/view note: `Gk` remains only the Euclidean matrix realization of the Hessian via
--   `Matrix.toEuclideanCLM`, so this file does not introduce a second Hessian owner.

variable
  {f : Point → ℝ} {x : Point}
  {Gk Lk : Hessian} {dDiag eDiag : Fin n → ℝ}

local notation "Glin" =>
  ((Matrix.toEuclideanCLM : Hessian ≃⋆ₐ[ℝ] Point →L[ℝ] Point) Gk)

/-- Helper for Chapter03 Theorem 3.5.3: when every coordinate strictly above `j` vanishes, the
`j`-th row of the transposed unit-lower factor reduces to its diagonal contribution. -/
lemma transpose_row_eq_current_entry_of_zero_tail
    (Lk : Hessian)
    (j : Fin n)
    (dk : Point)
    (hLk_unitLower : Lk.IsUnitLowerTriangular)
    (hAbove : ∀ r : Fin n, j < r → dk r = 0) :
    ((Lk.transpose).mulVec dk) j = dk j := by
  -- Route correction: isolate the `j`-th row directly and kill every off-diagonal term with
  -- lower-triangularity below `j` and the zero-tail hypothesis above `j`.
  have hsum : ∑ r : Fin n, Lk.transpose j r * dk r = dk j := by
    calc
      ∑ r : Fin n, Lk.transpose j r * dk r = Lk.transpose j j * dk j := by
        refine Finset.sum_eq_single j ?_ ?_
        · intro r _ hr
          by_cases hrj : r < j
          · rw [show Lk.transpose j r = 0 by
                  simpa using hLk_unitLower.apply_eq_zero hrj]
            simp
          · have hjr : j < r := lt_of_le_of_ne (le_of_not_gt hrj) (by simpa using hr.symm)
            rw [hAbove r hjr]
            simp
        · simp
      _ = dk j := by
        simp [hLk_unitLower.apply_diag]
  simpa [Matrix.mulVec, dotProduct] using hsum

/-- Helper for Chapter03 Theorem 3.5.3: once the coordinates strictly above `j` vanish, the
upper-triangular solve `Lkᵀ dk = e_t` determines the `j`-th coordinate exactly. -/
lemma transpose_solve_entry_eq_unitVector_entry
    (Lk : Hessian)
    (t j : Fin n)
    (dk : Point)
    (solve_eq : Lk.transpose.mulVec dk = negativeCurvatureUnitVector t)
    (hLk_unitLower : Lk.IsUnitLowerTriangular)
    (hAbove : ∀ r : Fin n, j < r → dk r = 0) :
    dk j = negativeCurvatureUnitVector t j := by
  -- Collapse the `j`-th row of the solve equation to the diagonal term `dk j`.
  have hrow :
      ((Lk.transpose).mulVec dk) j = dk j :=
    transpose_row_eq_current_entry_of_zero_tail (Lk := Lk) (j := j) (dk := dk)
      hLk_unitLower hAbove
  -- Then read the coordinate directly from the right-hand side `e_t`.
  have hsolve : ((Lk.transpose).mulVec dk) j = negativeCurvatureUnitVector t j := by
    simpa using congrFun solve_eq j
  exact hrow.symm.trans hsolve

/-- Helper for Chapter03 Theorem 3.5.3: reverse back-substitution on `Lkᵀ dk = e_t` forces every
coordinate strictly above the pivot index `t` to vanish. -/
lemma reverse_back_substitution_zero_above_pivot
    (Lk : Hessian)
    (t : Fin n)
    (dk : Point)
    (solve_eq : Lk.transpose.mulVec dk = negativeCurvatureUnitVector t)
    (hLk_unitLower : Lk.IsUnitLowerTriangular) :
    ∀ j : Fin n, t < j → dk j = 0 := by
  -- Reverse induction on `Fin.rev` turns “indices above `j`” into the ordinary strong-induction
  -- hypotheses on smaller reversed indices.
  intro j htj
  let motive : Fin n → Prop := fun i ↦ t < i.rev → dk i.rev = 0
  have hrev : motive j.rev := by
    refine Fin.strong_induction_on (motive := motive) (i := j.rev) ?_
    intro i ih hti
    have hAbove : ∀ r : Fin n, i.rev < r → dk r = 0 := by
      intro r hir
      have hrrev : r.rev < i := by
        simpa using (Fin.rev_lt_rev.mpr hir)
      have htr : t < r := lt_trans hti hir
      simpa using ih r.rev hrrev (by simpa using htr)
    have hentry :
        dk i.rev = negativeCurvatureUnitVector t i.rev :=
      transpose_solve_entry_eq_unitVector_entry (Lk := Lk) (t := t) (j := i.rev) (dk := dk)
        solve_eq hLk_unitLower hAbove
    have hne : i.rev ≠ t := by
      intro h
      subst h
      exact lt_irrefl _ hti
    simpa [motive, negativeCurvatureUnitVector_apply, hne] using hentry
  have hzero : dk j.rev.rev = 0 := hrev (by simpa using htj)
  simpa using hzero

/-- Helper for Chapter03 Theorem 3.5.3: solving `Lkᵀ dk = e_t` with `Lk` unit lower triangular
forces the textbook normal form `dk t = 1` and `dk j = 0` for every `j > t`. -/
lemma pivot_normal_form_of_transpose_solve_unitVector
    (Lk : Hessian)
    (t : Fin n)
    (dk : Point)
    (solve_eq : Lk.transpose.mulVec dk = negativeCurvatureUnitVector t)
    (hLk_unitLower : Lk.IsUnitLowerTriangular) :
    dk t = 1 ∧ ∀ j : Fin n, t < j → dk j = 0 := by
  -- First record the reverse back-substitution invariant above the pivot.
  have hzeroAbove :
      ∀ j : Fin n, t < j → dk j = 0 :=
    reverse_back_substitution_zero_above_pivot (Lk := Lk) (t := t) (dk := dk)
      solve_eq hLk_unitLower
  -- Then the pivot row has no tail terms left, so it reads off the unit-vector value `1`.
  have hpivot :
      dk t = negativeCurvatureUnitVector t t :=
    transpose_solve_entry_eq_unitVector_entry (Lk := Lk) (t := t) (j := t) (dk := dk)
      solve_eq hLk_unitLower hzeroAbove
  constructor
  · simpa [negativeCurvatureUnitVector_apply] using hpivot
  · exact hzeroAbove

/-- Helper for Chapter03 Theorem 3.5.3: the LDLᵀ quadratic term along the solve direction equals
the selected diagonal entry `dDiag t`. -/
lemma factorized_quadratic_eq_selected_diagonal
    (Lk : Hessian)
    (dDiag : Fin n → ℝ)
    (t : Fin n)
    (dk : Point)
    (solve_eq : Lk.transpose.mulVec dk = negativeCurvatureUnitVector t) :
    dotProduct dk (((Lk * Matrix.diagonal dDiag * Lk.transpose).mulVec dk)) = dDiag t := by
  let diagonalSolve : Fin n → ℝ :=
    Matrix.mulVec (Matrix.diagonal dDiag) (Matrix.mulVec (Matrix.transpose Lk) dk)
  have hmove :
      dotProduct dk (Matrix.mulVec Lk diagonalSolve) =
        dotProduct diagonalSolve (Matrix.mulVec (Matrix.transpose Lk) dk) := by
    -- Move the left factor across the bilinear form before inserting the solve equation.
    simpa [diagonalSolve] using
      (Matrix.dotProduct_transpose_mulVec (A := Matrix.transpose Lk) (x := dk)
        (y := diagonalSolve))
  calc
    dotProduct dk (((Lk * Matrix.diagonal dDiag * Lk.transpose).mulVec dk))
        = dotProduct dk (Matrix.mulVec Lk diagonalSolve) := by
            simp [diagonalSolve, Matrix.mul_assoc, Matrix.mulVec_mulVec]
    _ = dotProduct diagonalSolve (Matrix.mulVec (Matrix.transpose Lk) dk) := hmove
    _ = dotProduct ((Matrix.diagonal dDiag).mulVec (negativeCurvatureUnitVector t))
          (negativeCurvatureUnitVector t) := by
            simpa [diagonalSolve] using
              congrArg
                (fun v : Fin n → ℝ => dotProduct (Matrix.mulVec (Matrix.diagonal dDiag) v) v)
                solve_eq
    _ = dDiag t := by
      rw [negativeCurvatureUnitVector, Matrix.diagonal_mulVec_single, dotProduct]
      rw [Finset.sum_eq_single t]
      · simp
      · intro i _ hit
        simp [Pi.single_apply, hit]
      · intro ht
        simp at ht

/-- Helper for Chapter03 Theorem 3.5.3: the diagonal correction contributes at least the selected
entry `eDiag t` because all diagonal corrections are nonnegative and `dk t = 1`. -/
lemma diagonal_correction_ge_selected_entry
    (t : Fin n)
    (dk : Point)
    (hCorrection_nonneg : ∀ i : Fin n, 0 ≤ eDiag i)
    (hdk_t : dk t = 1) :
    eDiag t ≤ dotProduct dk ((Matrix.diagonal eDiag).mulVec dk) := by
  have hnonneg_term : ∀ i : Fin n, 0 ≤ dk i * ((Matrix.diagonal eDiag).mulVec dk) i := by
    intro i
    -- Each diagonal term is `eDiag i * dk i^2`, so it is nonnegative.
    rw [Matrix.mulVec_diagonal]
    nlinarith [hCorrection_nonneg i, sq_nonneg (dk i)]
  have hpivot_le :
      dk t * ((Matrix.diagonal eDiag).mulVec dk) t ≤
        dotProduct dk ((Matrix.diagonal eDiag).mulVec dk) := by
    simpa [dotProduct] using
      (Finset.single_le_sum
        (fun i hi => hnonneg_term i)
        (show t ∈ (Finset.univ : Finset (Fin n)) by simp))
  have hpivot_eq :
      eDiag t = dk t * ((Matrix.diagonal eDiag).mulVec dk) t := by
    rw [Matrix.mulVec_diagonal, hdk_t]
    ring
  rw [hpivot_eq]
  exact hpivot_le

/-- Chapter03 Theorem 3.5.3 (1): let `Gk` be the Hessian of `f` at `x`, let
`Gk + Matrix.diagonal eDiag = Lk * Matrix.diagonal dDiag * Lkᵀ`, and let `t` be the selected
pivot from Algorithm 3.5.2 with negative score
`negativeCurvaturePivotScores dDiag eDiag t < 0`. If `dk` solves `Lkᵀ dk = e_t` and `Lk` is
unit lower triangular, then `dk` is a negative curvature direction at `x`. This uses the
Chapter 3 owner
`IsNegativeCurvatureDirectionAt` directly rather than keeping a parallel quadratic-negativity
wrapper theorem. -/
theorem negativeCurvaturePivotDirection
    (t : Fin n)
    (negative : negativeCurvaturePivotScores dDiag eDiag t < 0)
    (dk : Point)
    (solve_eq : Lk.transpose.mulVec dk = negativeCurvatureUnitVector t)
    (hHessian : HasFDerivAt (gradient f) Glin x)
    (hLk_unitLower : Lk.IsUnitLowerTriangular)
    (hCorrection_nonneg : ∀ i : Fin n, 0 ≤ eDiag i)
    (hFactorization : Gk + Matrix.diagonal eDiag = Lk * Matrix.diagonal dDiag * Lk.transpose) :
    IsNegativeCurvatureDirectionAt f x dk := by
  rw [isNegativeCurvatureDirectionAt_iff]
  -- Convert the Hessian quadratic form to the matrix quadratic form `dkᵀ Gk dk`.
  have hquadratic_matrix :
      hessianQuadraticAt f x dk = dotProduct dk (Gk.mulVec dk) := by
    calc
      hessianQuadraticAt f x dk = inner ℝ dk (Glin dk) := by
        simp [hessianQuadraticAt, hessianAt, hHessian.fderiv]
      _ = dotProduct dk (Gk.mulVec dk) := by
        simpa [Glin] using (Matrix.inner_toEuclideanCLM Gk dk dk)
  -- Recover the textbook normal form of the solve direction from the triangular system.
  obtain ⟨hdk_t, _hzeroAbove⟩ :=
    pivot_normal_form_of_transpose_solve_unitVector (Lk := Lk) (t := t) (dk := dk)
      solve_eq hLk_unitLower
  have hfactorized_term :
      dotProduct dk (((Lk * Matrix.diagonal dDiag * Lk.transpose).mulVec dk)) = dDiag t :=
    factorized_quadratic_eq_selected_diagonal (Lk := Lk) (dDiag := dDiag) (t := t) (dk := dk)
      solve_eq
  have hcorrection_term :
      eDiag t ≤ dotProduct dk ((Matrix.diagonal eDiag).mulVec dk) :=
    diagonal_correction_ge_selected_entry (eDiag := eDiag) (t := t) (dk := dk)
      hCorrection_nonneg hdk_t
  -- Compare the Hessian quadratic form with the factorized matrix and the nonnegative correction.
  have hfactorization_dot :
      dotProduct dk (Gk.mulVec dk) + dotProduct dk ((Matrix.diagonal eDiag).mulVec dk) = dDiag t := by
    have hdot :
        dotProduct dk (Gk.mulVec dk) + dotProduct dk ((Matrix.diagonal eDiag).mulVec dk) =
          dotProduct dk (((Lk * Matrix.diagonal dDiag * Lk.transpose).mulVec dk)) := by
      simpa [Matrix.add_mulVec, dotProduct_add] using
        congrArg (fun M : Hessian => dotProduct dk (M.mulVec dk)) hFactorization
    rwa [hfactorized_term] at hdot
  have hnegative_score : dDiag t - eDiag t < 0 := by
    simpa using negative
  have hmatrix_neg :
      dotProduct dk (Gk.mulVec dk) < 0 := by
    have hupper :
        dotProduct dk (Gk.mulVec dk) ≤ dDiag t - eDiag t := by
      linarith
    exact lt_of_le_of_lt hupper hnegative_score
  rw [hquadratic_matrix]
  exact hmatrix_neg

end NegativeCurvaturePivotDirection

section NegativeCurvaturePivotDirectionSignChoice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {x : E}

/- Chapter03 Theorem 3.5.3 (2): direct recall of the canonical Chapter 1 sign-choice theorem
`isDescentDirectionAt_or_neg`. Once the pivot direction `dk` is fixed and is not orthogonal to
the gradient at `x`, one of the two signs `dk` and `-dk` is a descent direction. -/
#check isDescentDirectionAt_or_neg

/-- A thin local-decrease companion for Theorem 3.5.3 (2), derived from the canonical
descent-direction sign choice via the Chapter 2 search-ray owner. -/
theorem negativeCurvaturePivotDirection_descentSignChoice_localDecrease
    (dk : E)
    (hNonorth : inner ℝ (gradient f x) dk ≠ 0) :
    (∃ δ > 0, ∀ α : ℝ, 0 < α → α < δ → f (x + α • dk) < f x) ∨
      ∃ δ > 0, ∀ α : ℝ, 0 < α → α < δ → f (x + α • (-dk)) < f x :=
  (isDescentDirectionAt_or_neg f x dk hNonorth).imp
    IsDescentDirectionAt.exists_localDecrease
    IsDescentDirectionAt.exists_localDecrease

end NegativeCurvaturePivotDirectionSignChoice

end
