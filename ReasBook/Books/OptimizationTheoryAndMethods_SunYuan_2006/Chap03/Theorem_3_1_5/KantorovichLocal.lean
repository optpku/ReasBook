/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3
import Mathlib.Analysis.Matrix.PosDef

open Matrix

noncomputable section

namespace KantorovichLocal

section

variable {n : ℕ}
variable (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)

/-- Helper for Chapter03 Theorem 3.1.5: a unitary eigenbasis change preserves the Euclidean
dot product on `ℝ^n`. -/
lemma dotProduct_unitary_mulVec
    (U : Matrix.unitaryGroup (Fin n) ℝ) (y z : Fin n → ℝ) :
    ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) ⬝ᵥ
        ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) =
      y ⬝ᵥ z :=
  have htranspose :
      ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ) = star (U : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Matrix.star_apply]
  have hGram :
      ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
    rw [htranspose]
    exact U.2.1
  -- Rewrite the outer dot product into the Gram matrix of the unitary eigenbasis.
  calc
    ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) ⬝ᵥ
        ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) =
        (((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) ᵥ*
            (U : Matrix (Fin n) (Fin n) ℝ)) ⬝ᵥ z := by
      rw [Matrix.dotProduct_mulVec]
    _ = (y ᵥ*
          (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ) *
            (U : Matrix (Fin n) (Fin n) ℝ))) ⬝ᵥ z := by
      rw [Matrix.vecMul_mulVec]
    _ = (y ᵥ* (1 : Matrix (Fin n) (Fin n) ℝ)) ⬝ᵥ z := by
      rw [hGram]
    _ = y ⬝ᵥ z := by
      rw [Matrix.vecMul_one]

/-- Helper for Chapter03 Theorem 3.1.5: conjugating `G⁻¹` by an orthonormal eigenbasis produces
the diagonal matrix of inverse positive-definite eigenvalues. -/
lemma star_eigenvectorUnitary_mul_inv_mul_eigenvectorUnitary :
    let U : Matrix.unitaryGroup (Fin n) ℝ := hG.isHermitian.eigenvectorUnitary
    (star (U : Matrix (Fin n) (Fin n) ℝ)) * G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ) =
      diagonal (fun i => (posDefEigenvalues G hG i)⁻¹) := by
  let U : Matrix.unitaryGroup (Fin n) ℝ := hG.isHermitian.eigenvectorUnitary
  have hDiag :
      (star (U : Matrix (Fin n) (Fin n) ℝ)) * G * (U : Matrix (Fin n) (Fin n) ℝ) =
        diagonal (fun i => posDefEigenvalues G hG i) := by
    -- First diagonalize `G` itself in its orthonormal eigenbasis.
    simpa [U, Unitary.conjStarAlgAut_apply, posDefEigenvalues_def] using
      hG.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  letI : Invertible G := hG.isUnit.invertible
  have hInner :
      (U : Matrix (Fin n) (Fin n) ℝ) *
          (star (U : Matrix (Fin n) (Fin n) ℝ) *
            (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ))) =
        G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ) := by
    -- Cancel the `U * star U` pair before taking the right inverse.
    calc
      (U : Matrix (Fin n) (Fin n) ℝ) *
          (star (U : Matrix (Fin n) (Fin n) ℝ) *
            (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ))) =
          ((U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ)) *
            (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ)) := by
        rw [Matrix.mul_assoc]
      _ = 1 * (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ)) := by
        rw [U.2.2]
      _ = G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ) := by
        simp
  have hAssocInv :
      ((star (U : Matrix (Fin n) (Fin n) ℝ)) * G * (U : Matrix (Fin n) (Fin n) ℝ)) *
          ((star (U : Matrix (Fin n) (Fin n) ℝ)) * G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ)) =
        (star (U : Matrix (Fin n) (Fin n) ℝ)) *
          (G * (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ))) := by
    -- Reassociate the middle `U * star U` block and then cancel it with `hInner`.
    simpa [Matrix.mul_assoc] using
      congrArg
        (fun M : Matrix (Fin n) (Fin n) ℝ ↦
          (star (U : Matrix (Fin n) (Fin n) ℝ)) * (G * M))
        hInner
  have hRightInv :
      diagonal (fun i => posDefEigenvalues G hG i) *
          ((star (U : Matrix (Fin n) (Fin n) ℝ)) * G⁻¹ *
            (U : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
    -- The conjugated inverse is the right inverse of the diagonalized model of `G`.
    calc
      diagonal (fun i => posDefEigenvalues G hG i) *
          ((star (U : Matrix (Fin n) (Fin n) ℝ)) * G⁻¹ *
            (U : Matrix (Fin n) (Fin n) ℝ)) =
          ((star (U : Matrix (Fin n) (Fin n) ℝ)) * G *
            (U : Matrix (Fin n) (Fin n) ℝ)) *
            ((star (U : Matrix (Fin n) (Fin n) ℝ)) * G⁻¹ *
              (U : Matrix (Fin n) (Fin n) ℝ)) := by
        rw [← hDiag]
      _ = (star (U : Matrix (Fin n) (Fin n) ℝ)) *
            (G * (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ))) := by
        rw [hAssocInv]
      _ = (star (U : Matrix (Fin n) (Fin n) ℝ)) *
            (((G * G⁻¹) * (U : Matrix (Fin n) (Fin n) ℝ))) := by
        rw [Matrix.mul_assoc]
      _ = (star (U : Matrix (Fin n) (Fin n) ℝ)) *
            (1 * (U : Matrix (Fin n) (Fin n) ℝ)) := by
        rw [Matrix.mul_inv_of_invertible]
      _ = 1 := by
        simpa [Matrix.mul_assoc] using
          (U.2.1 :
            star (U : Matrix (Fin n) (Fin n) ℝ) *
              (U : Matrix (Fin n) (Fin n) ℝ) = 1)
  have hInv :
      (diagonal (fun i => posDefEigenvalues G hG i))⁻¹ =
        (star (U : Matrix (Fin n) (Fin n) ℝ)) * G⁻¹ *
          (U : Matrix (Fin n) (Fin n) ℝ) := by
    exact Matrix.inv_eq_right_inv hRightInv
  calc
    (star (U : Matrix (Fin n) (Fin n) ℝ)) * G⁻¹ *
        (U : Matrix (Fin n) (Fin n) ℝ) =
        (diagonal (fun i => posDefEigenvalues G hG i))⁻¹ := by
      simpa using hInv.symm
    _ = diagonal (fun i => (posDefEigenvalues G hG i)⁻¹) := by
      -- Reduce the diagonal inverse to pointwise scalar inversion.
      ext i j
      by_cases hij : i = j
      · subst hij
        let f : Fin n → ℝ := fun k ↦ posDefEigenvalues G hG k
        have hf_ne : ∀ k, f k ≠ 0 := by
          intro k
          have hpos : 0 < f k := by
            simpa [f, posDefEigenvalues_def] using hG.eigenvalues_pos k
          exact hpos.ne'
        let u : (Fin n → ℝ)ˣ :=
          { val := f
            inv := fun k ↦ (f k)⁻¹
            val_inv := by
              funext k
              exact mul_inv_cancel₀ (hf_ne k)
            inv_val := by
              funext k
              exact inv_mul_cancel₀ (hf_ne k) }
        have hInvFun : Ring.inverse f = ↑(u⁻¹) := by
          exact Ring.inverse_unit u
        have hEntry : Ring.inverse f i = (f i)⁻¹ := by
          rw [hInvFun]
          rfl
        simpa [Matrix.inv_diagonal, f] using hEntry
      · simp [Matrix.inv_diagonal, hij]

/-- Helper for Chapter03 Theorem 3.1.5: in an orthonormal eigenbasis of a positive-definite
matrix, the three quadratic forms from the Kantorovich quotient become diagonal weighted sums. -/
lemma quadratic_forms_in_posDef_eigenbasis
    (x : Fin n → ℝ) :
    let U : Matrix.unitaryGroup (Fin n) ℝ := hG.isHermitian.eigenvectorUnitary
    let y : Fin n → ℝ := (star (U : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x
    x ⬝ᵥ x = ∑ i, (y i)^2 ∧
      x ⬝ᵥ (G *ᵥ x) = ∑ i, posDefEigenvalues G hG i * (y i)^2 ∧
      x ⬝ᵥ (G⁻¹ *ᵥ x) = ∑ i, (posDefEigenvalues G hG i)⁻¹ * (y i)^2 := by
  let U : Matrix.unitaryGroup (Fin n) ℝ := hG.isHermitian.eigenvectorUnitary
  let y : Fin n → ℝ := (star (U : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x
  let D : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => posDefEigenvalues G hG i)
  let Dinv : Matrix (Fin n) (Fin n) ℝ :=
    diagonal (fun i => (posDefEigenvalues G hG i)⁻¹)
  have hxrepr : x = (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y := by
    -- Undo the eigenbasis change to recover the original vector.
    calc
      x = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x := by
        symm
        exact Matrix.one_mulVec x
      _ = ((U : Matrix (Fin n) (Fin n) ℝ) *
            star (U : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x := by
        rw [U.2.2]
      _ = (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ
            ((star (U : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec]
      _ = (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y := by
        rfl
  have hDiag :
      (star (U : Matrix (Fin n) (Fin n) ℝ)) * G * (U : Matrix (Fin n) (Fin n) ℝ) = D := by
    -- Rewrite the Hermitian spectral theorem into the project eigenvalue owner.
    simpa [U, D, Unitary.conjStarAlgAut_apply, posDefEigenvalues_def] using
      hG.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hInvDiag :
      (star (U : Matrix (Fin n) (Fin n) ℝ)) * G⁻¹ *
        (U : Matrix (Fin n) (Fin n) ℝ) = Dinv := by
    -- Route correction: isolate the inverse diagonalization before assembling the quotient.
    simpa [U, Dinv] using
      star_eigenvectorUnitary_mul_inv_mul_eigenvectorUnitary (G := G) (hG := hG)
  have hMul :
      G * (U : Matrix (Fin n) (Fin n) ℝ) = (U : Matrix (Fin n) (Fin n) ℝ) * D := by
    -- Left-multiply the diagonalization identity and cancel `U * star U = 1`.
    have hLeft := congrArg
      (fun M : Matrix (Fin n) (Fin n) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) * M) hDiag
    have hCancel :
        (U : Matrix (Fin n) (Fin n) ℝ) *
            (star (U : Matrix (Fin n) (Fin n) ℝ) *
              (G * (U : Matrix (Fin n) (Fin n) ℝ))) =
          G * (U : Matrix (Fin n) (Fin n) ℝ) := by
      calc
        (U : Matrix (Fin n) (Fin n) ℝ) *
            (star (U : Matrix (Fin n) (Fin n) ℝ) *
              (G * (U : Matrix (Fin n) (Fin n) ℝ))) =
            ((U : Matrix (Fin n) (Fin n) ℝ) *
                star (U : Matrix (Fin n) (Fin n) ℝ)) *
              (G * (U : Matrix (Fin n) (Fin n) ℝ)) := by
          rw [Matrix.mul_assoc]
        _ = 1 * (G * (U : Matrix (Fin n) (Fin n) ℝ)) := by
          rw [U.2.2]
        _ = G * (U : Matrix (Fin n) (Fin n) ℝ) := by
          simp
    calc
      G * (U : Matrix (Fin n) (Fin n) ℝ) =
          (U : Matrix (Fin n) (Fin n) ℝ) *
            (star (U : Matrix (Fin n) (Fin n) ℝ) *
              (G * (U : Matrix (Fin n) (Fin n) ℝ))) := by
        rw [hCancel]
      _ = (U : Matrix (Fin n) (Fin n) ℝ) * D := by
        simpa [Matrix.mul_assoc] using hLeft
  have hInvMul :
      G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ) = (U : Matrix (Fin n) (Fin n) ℝ) * Dinv := by
    -- Transport the inverse diagonalization in the same way.
    have hLeft := congrArg
      (fun M : Matrix (Fin n) (Fin n) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) * M) hInvDiag
    have hCancel :
        (U : Matrix (Fin n) (Fin n) ℝ) *
            (star (U : Matrix (Fin n) (Fin n) ℝ) *
              (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ))) =
          G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ) := by
      calc
        (U : Matrix (Fin n) (Fin n) ℝ) *
            (star (U : Matrix (Fin n) (Fin n) ℝ) *
              (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ))) =
            ((U : Matrix (Fin n) (Fin n) ℝ) *
                star (U : Matrix (Fin n) (Fin n) ℝ)) *
              (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ)) := by
          rw [Matrix.mul_assoc]
        _ = 1 * (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ)) := by
          rw [U.2.2]
        _ = G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ) := by
          simp
    calc
      G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ) =
          (U : Matrix (Fin n) (Fin n) ℝ) *
            (star (U : Matrix (Fin n) (Fin n) ℝ) *
              (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ))) := by
        rw [hCancel]
      _ = (U : Matrix (Fin n) (Fin n) ℝ) * Dinv := by
        simpa [Matrix.mul_assoc] using hLeft
  have hMulVec :
      G *ᵥ ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) =
        (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ (D *ᵥ y) := by
    -- Apply the transported matrix identity to the coordinate vector.
    calc
      G *ᵥ ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) =
          (G * (U : Matrix (Fin n) (Fin n) ℝ)) *ᵥ y := by
        rw [Matrix.mulVec_mulVec]
      _ = ((U : Matrix (Fin n) (Fin n) ℝ) * D) *ᵥ y := by
        rw [hMul]
      _ = (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ (D *ᵥ y) := by
        rw [← Matrix.mulVec_mulVec]
  have hInvMulVec :
      G⁻¹ *ᵥ ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) =
        (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ (Dinv *ᵥ y) := by
    -- The inverse quadratic form transports in the same way.
    calc
      G⁻¹ *ᵥ ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) =
          (G⁻¹ * (U : Matrix (Fin n) (Fin n) ℝ)) *ᵥ y := by
        rw [Matrix.mulVec_mulVec]
      _ = ((U : Matrix (Fin n) (Fin n) ℝ) * Dinv) *ᵥ y := by
        rw [hInvMul]
      _ = (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ (Dinv *ᵥ y) := by
        rw [← Matrix.mulVec_mulVec]
  refine ⟨?_, ?_⟩
  · -- The Euclidean norm is preserved by the unitary eigenbasis change.
    calc
      x ⬝ᵥ x =
          ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) ⬝ᵥ
            ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) := by
        rw [hxrepr]
      _ = y ⬝ᵥ y := by
        exact dotProduct_unitary_mulVec (U := U) (y := y) (z := y)
      _ = ∑ i, (y i)^2 := by
        simp [dotProduct, pow_two]
  · refine ⟨?_, ?_⟩
    · -- Rewrite the `G`-quadratic form into the diagonal eigenvalue model.
      calc
        x ⬝ᵥ (G *ᵥ x) =
            ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) ⬝ᵥ
              (G *ᵥ ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y)) := by
          rw [hxrepr]
        _ = ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) ⬝ᵥ
              ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ (D *ᵥ y)) := by
          rw [hMulVec]
        _ = y ⬝ᵥ (D *ᵥ y) := by
          exact dotProduct_unitary_mulVec (U := U) (y := y) (z := D *ᵥ y)
        _ = ∑ i, posDefEigenvalues G hG i * (y i)^2 := by
          simp [D, Matrix.mulVec_diagonal, dotProduct, pow_two, mul_left_comm]
    · -- Rewrite the `G⁻¹`-quadratic form into the diagonal inverse-eigenvalue model.
      calc
        x ⬝ᵥ (G⁻¹ *ᵥ x) =
            ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) ⬝ᵥ
              (G⁻¹ *ᵥ ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y)) := by
          rw [hxrepr]
        _ = ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) ⬝ᵥ
              ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ (Dinv *ᵥ y)) := by
          rw [hInvMulVec]
        _ = y ⬝ᵥ (Dinv *ᵥ y) := by
          exact dotProduct_unitary_mulVec (U := U) (y := y) (z := Dinv *ᵥ y)
        _ = ∑ i, (posDefEigenvalues G hG i)⁻¹ * (y i)^2 := by
          simp [Dinv, Matrix.mulVec_diagonal, dotProduct, pow_two, mul_left_comm]

/-- Helper for Chapter03 Theorem 3.1.5: the secant line through the endpoint values of
`μ ↦ 1 / μ` dominates that convex function on `[lambdaMin, lambdaMax]`. -/
private lemma one_div_le_endpoint_secant_of_mem_Icc
    {lambdaMin lambdaMax μ : ℝ}
    (hLambdaMinPos : 0 < lambdaMin)
    (hLambdaOrder : lambdaMin ≤ lambdaMax)
    (hμ : μ ∈ Set.Icc lambdaMin lambdaMax) :
    μ⁻¹ ≤ (lambdaMax + lambdaMin - μ) / (lambdaMax * lambdaMin) := by
  have hμPos : 0 < μ := lt_of_lt_of_le hLambdaMinPos hμ.1
  have hLambdaMaxPos : 0 < lambdaMax := lt_of_lt_of_le hLambdaMinPos hLambdaOrder
  have hSquare :
      0 ≤ (μ - lambdaMin) * (lambdaMax - μ) := by
    nlinarith [sub_nonneg.mpr hμ.1, sub_nonneg.mpr hμ.2]
  -- Clear the positive denominator and reduce to the obvious endpoint square inequality.
  field_simp [hμPos.ne', hLambdaMinPos.ne', hLambdaMaxPos.ne']
  nlinarith

/-- Helper for Chapter03 Theorem 3.1.5: the quadratic `a ↦ a * (lambdaMax + lambdaMin - a)` is
maximized at the midpoint of the endpoint interval. -/
private lemma quadratic_peak_bound_on_endpoint_interval
    {lambdaMin lambdaMax a : ℝ}
    (_ha : a ∈ Set.Icc lambdaMin lambdaMax) :
    a * (lambdaMax + lambdaMin - a) ≤ (lambdaMax + lambdaMin) ^ (2 : ℕ) / 4 := by
  have hSquare : 0 ≤ (2 * a - (lambdaMax + lambdaMin)) ^ (2 : ℕ) := sq_nonneg _
  -- Rewrite the peak bound as the nonnegativity of the centered square.
  nlinarith

/-- Helper for Chapter03 Theorem 3.1.5: on the native `Fin n → ℝ` surface, the Kantorovich
quotient is bounded below by the endpoint expression formed from the extreme eigenvalues. -/
lemma centeredQuadraticObjective_kantorovich_ratio_bound_fin
    (lambdaMax lambdaMin : ℝ)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    (x ⬝ᵥ x) ^ (2 : ℕ) /
        ((x ⬝ᵥ (G *ᵥ x)) * (x ⬝ᵥ (G⁻¹ *ᵥ x))) ≥
      ((4 : ℝ) * lambdaMax * lambdaMin) / (lambdaMax + lambdaMin) ^ (2 : ℕ) := by
  rcases (isGreatest_posDefEigenvalues_iff G hG lambdaMax).1 hLambdaMax with
    ⟨⟨iMax, hiMax⟩, hUpperEig⟩
  rcases (isLeast_posDefEigenvalues_iff G hG lambdaMin).1 hLambdaMin with
    ⟨⟨iMin, hiMin⟩, hLowerEig⟩
  have hLambdaMinPos : 0 < lambdaMin := by
    -- The least positive-definite eigenvalue remains positive.
    rw [← hiMin]
    simpa [posDefEigenvalues_def] using hG.eigenvalues_pos iMin
  have hLambdaMaxPos : 0 < lambdaMax := by
    -- The greatest positive-definite eigenvalue remains positive.
    rw [← hiMax]
    simpa [posDefEigenvalues_def] using hG.eigenvalues_pos iMax
  have hLambdaOrder : lambdaMin ≤ lambdaMax := by
    -- The least eigenvalue bounds the greatest one from below.
    rw [← hiMax]
    exact hLowerEig iMax
  have hQuad := quadratic_forms_in_posDef_eigenbasis (G := G) (hG := hG) x
  rcases hQuad with ⟨hxx, hGx, hGinvx⟩
  let U : Matrix.unitaryGroup (Fin n) ℝ := hG.isHermitian.eigenvectorUnitary
  let y : Fin n → ℝ := (star (U : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x
  let S : ℝ := ∑ i, (y i)^2
  let ξ : Fin n → ℝ := fun i ↦ (y i)^2 / S
  let a : ℝ := ∑ i, posDefEigenvalues G hG i * ξ i
  let b : ℝ := ∑ i, (posDefEigenvalues G hG i)⁻¹ * ξ i
  have hxx_nonneg : 0 ≤ x ⬝ᵥ x := by
    simpa [dotProduct, pow_two] using
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i) : 0 ≤ ∑ i : Fin n, (x i)^2)
  have hxx_ne : x ⬝ᵥ x ≠ 0 := by
    intro hzero
    exact hx ((dotProduct_self_eq_zero).1 hzero)
  have hxx_pos : 0 < x ⬝ᵥ x := by
    exact lt_of_le_of_ne hxx_nonneg (Ne.symm hxx_ne)
  have hS_eq : x ⬝ᵥ x = S := by
    simpa [S, y, U] using hxx
  have hS_pos : 0 < S := by
    rw [← hS_eq]
    exact hxx_pos
  have hS_ne : S ≠ 0 := hS_pos.ne'
  have hξ_nonneg : ∀ i, 0 ≤ ξ i := by
    intro i
    exact div_nonneg (sq_nonneg (y i)) hS_pos.le
  have hξ_sum : ∑ i, ξ i = 1 := by
    -- Normalize the squared coordinates into a probability vector.
    calc
      ∑ i, ξ i = (∑ i, (y i)^2) / S := by
        simp [ξ, Finset.sum_div]
      _ = 1 := by
        simp [S, hS_ne]
  have hSa : S * a = ∑ i, posDefEigenvalues G hG i * (y i)^2 := by
    -- Clearing the common denominator `S` recovers the `G`-quadratic sum.
    calc
      S * a = S * ∑ i, posDefEigenvalues G hG i * ξ i := by
        rfl
      _ = ∑ i, S * (posDefEigenvalues G hG i * ξ i) := by
        rw [Finset.mul_sum]
      _ = ∑ i, posDefEigenvalues G hG i * (y i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        unfold ξ
        field_simp [hS_ne]
  have hSb : S * b = ∑ i, (posDefEigenvalues G hG i)⁻¹ * (y i)^2 := by
    -- The same denominator clearing works for the inverse quadratic form.
    calc
      S * b = S * ∑ i, (posDefEigenvalues G hG i)⁻¹ * ξ i := by
        rfl
      _ = ∑ i, S * ((posDefEigenvalues G hG i)⁻¹ * ξ i) := by
        rw [Finset.mul_sum]
      _ = ∑ i, (posDefEigenvalues G hG i)⁻¹ * (y i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        unfold ξ
        field_simp [hS_ne]
  have hGquad_pos : 0 < x ⬝ᵥ (G *ᵥ x) := hG.dotProduct_mulVec_pos hx
  have hGinv_pos : 0 < x ⬝ᵥ (G⁻¹ *ᵥ x) := by
    simpa using hG.inv.dotProduct_mulVec_pos hx
  have ha_pos : 0 < a := by
    -- Divide the positive `G`-quadratic form by the positive scale `S`.
    rw [hGx, ← hSa] at hGquad_pos
    nlinarith
  have hb_pos : 0 < b := by
    -- Divide the positive inverse quadratic form by the positive scale `S`.
    rw [hGinvx, ← hSb] at hGinv_pos
    nlinarith
  have hEig_mem : ∀ i, posDefEigenvalues G hG i ∈ Set.Icc lambdaMin lambdaMax := by
    intro i
    exact ⟨hLowerEig i, hUpperEig i⟩
  have ha_mem : a ∈ Set.Icc lambdaMin lambdaMax := by
    constructor
    · calc
        lambdaMin = lambdaMin * ∑ i, ξ i := by
          simp [hξ_sum]
        _ = ∑ i, lambdaMin * ξ i := by
          rw [Finset.mul_sum]
        _ ≤ ∑ i, posDefEigenvalues G hG i * ξ i := by
          apply Finset.sum_le_sum
          intro i _
          nlinarith [hLowerEig i, hξ_nonneg i]
        _ = a := by
          rfl
    · calc
        a = ∑ i, posDefEigenvalues G hG i * ξ i := by
          rfl
        _ ≤ ∑ i, lambdaMax * ξ i := by
          apply Finset.sum_le_sum
          intro i _
          nlinarith [hUpperEig i, hξ_nonneg i]
        _ = lambdaMax * ∑ i, ξ i := by
          rw [Finset.mul_sum]
        _ = lambdaMax := by
          simp [hξ_sum]
  have hsec :
      ∀ i, (posDefEigenvalues G hG i)⁻¹ ≤
        (lambdaMax + lambdaMin - posDefEigenvalues G hG i) / (lambdaMax * lambdaMin) := by
    intro i
    exact one_div_le_endpoint_secant_of_mem_Icc hLambdaMinPos hLambdaOrder (hEig_mem i)
  have hNumerator :
      ∑ i, (lambdaMax + lambdaMin - posDefEigenvalues G hG i) * ξ i =
        lambdaMax + lambdaMin - a := by
    -- The weighted secant numerator collapses to the weighted average `a`.
    calc
      ∑ i, (lambdaMax + lambdaMin - posDefEigenvalues G hG i) * ξ i =
          ∑ i, ((lambdaMax + lambdaMin) * ξ i -
            posDefEigenvalues G hG i * ξ i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, (lambdaMax + lambdaMin) * ξ i -
            ∑ i, posDefEigenvalues G hG i * ξ i := by
        rw [Finset.sum_sub_distrib]
      _ = (lambdaMax + lambdaMin) * ∑ i, ξ i -
            ∑ i, posDefEigenvalues G hG i * ξ i := by
        rw [Finset.mul_sum]
      _ = lambdaMax + lambdaMin - a := by
        simp [a, hξ_sum]
  have hb_le : b ≤ (lambdaMax + lambdaMin - a) / (lambdaMax * lambdaMin) := by
    -- Sum the scalar secant bounds against the nonnegative weights `ξ`.
    calc
      b = ∑ i, (posDefEigenvalues G hG i)⁻¹ * ξ i := by
        rfl
      _ ≤ ∑ i,
            ((lambdaMax + lambdaMin - posDefEigenvalues G hG i) /
              (lambdaMax * lambdaMin)) * ξ i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hsec i) (hξ_nonneg i)
      _ = (∑ i,
            (lambdaMax + lambdaMin - posDefEigenvalues G hG i) * ξ i) /
            (lambdaMax * lambdaMin) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (lambdaMax + lambdaMin - a) / (lambdaMax * lambdaMin) := by
        rw [hNumerator]
  have hDenBound :
      a * b ≤ (lambdaMax + lambdaMin) ^ (2 : ℕ) / (4 * lambdaMax * lambdaMin) := by
    -- Bound the denominator first by the secant estimate, then by the midpoint maximum.
    have htmp :
        a * b ≤ a * ((lambdaMax + lambdaMin - a) / (lambdaMax * lambdaMin)) := by
      exact mul_le_mul_of_nonneg_left hb_le ha_pos.le
    have hpeak := quadratic_peak_bound_on_endpoint_interval ha_mem
    have hden_pos : 0 < lambdaMax * lambdaMin := mul_pos hLambdaMaxPos hLambdaMinPos
    have hpeak' :
        a * ((lambdaMax + lambdaMin - a) / (lambdaMax * lambdaMin)) ≤
          (lambdaMax + lambdaMin) ^ (2 : ℕ) / (4 * lambdaMax * lambdaMin) := by
      have hmul := div_le_div_of_nonneg_right hpeak hden_pos.le
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact htmp.trans hpeak'
  have hQuot :
      (x ⬝ᵥ x) ^ (2 : ℕ) /
          ((x ⬝ᵥ (G *ᵥ x)) * (x ⬝ᵥ (G⁻¹ *ᵥ x))) = 1 / (a * b) := by
    -- Once the three quadratic forms are written as `S`, `S a`, and `S b`, the quotient
    -- collapses exactly to `1 / (a * b)`.
    rw [hxx, hGx, hGinvx, ← hSa, ← hSb]
    field_simp [hS_ne, ha_pos.ne', hb_pos.ne']
    ring
  have hDenPos : 0 < a * b := mul_pos ha_pos hb_pos
  have hRecip :
      1 / ((lambdaMax + lambdaMin) ^ (2 : ℕ) / (4 * lambdaMax * lambdaMin)) ≤
        1 / (a * b) := by
    exact one_div_le_one_div_of_le hDenPos hDenBound
  have hConst :
      1 / ((lambdaMax + lambdaMin) ^ (2 : ℕ) / (4 * lambdaMax * lambdaMin)) =
        ((4 : ℝ) * lambdaMax * lambdaMin) / (lambdaMax + lambdaMin) ^ (2 : ℕ) := by
    field_simp
      [hLambdaMaxPos.ne', hLambdaMinPos.ne',
        show (lambdaMax + lambdaMin) ^ (2 : ℕ) ≠ 0 by positivity]
  rw [hQuot]
  rw [← hConst]
  exact hRecip

end

end KantorovichLocal
