/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Exercise_9_11

open Matrix

noncomputable section

-- Semantic recall: `Exercise_9_11` owns the source-facing inverse-KKT blocks `kktInverseU`,
-- `kktInverseW`, and `kktInverseT`. This file reuses those owners and states the generalized
-- elimination formulas for them directly.

section

variable {n m k : ℕ}

local notation "HessianMatrix" => Matrix (Fin n) (Fin n) ℝ
local notation "ConstraintMatrix" => Matrix (Fin n) (Fin m) ℝ
local notation "LeftInverseMatrix" => Matrix (Fin n) (Fin m) ℝ
local notation "ReducedBasisMatrix" => Matrix (Fin n) (Fin k) ℝ

/-- The affine map `P = I - G Z (Zᵀ G Z)⁻¹ Zᵀ` from `(9.3.31)`. -/
def reducedProjection (G : HessianMatrix) (Z : ReducedBasisMatrix) : HessianMatrix :=
  1 - G * Z * (Zᵀ * G * Z)⁻¹ * Zᵀ

#print axioms reducedProjection

/-- Unfolding `reducedProjection G Z` gives the source formula `(9.3.31)`. -/
theorem reducedProjection_eq (G : HessianMatrix) (Z : ReducedBasisMatrix) :
    reducedProjection G Z = 1 - G * Z * (Zᵀ * G * Z)⁻¹ * Zᵀ := rfl

/-- Helper for Chapter09 Exercise 9.12: applying the inverse KKT matrix to a block right-hand
side produces a primal-dual pair satisfying the corresponding KKT system. -/
lemma inverse_kkt_pair_satisfies_rhs
    (G : HessianMatrix) (A : ConstraintMatrix) (Z : ReducedBasisMatrix)
    (rhs₁ : Fin n → ℝ) (rhs₂ : Fin m → ℝ)
    (hA : Function.Injective A.mulVec) (hZ : IsReducedNullMatrix A Z)
    (hReduced : (Zᵀ * G * Z).PosDef) :
    let y := (kktMatrix G A)⁻¹.mulVec (Sum.elim rhs₁ rhs₂)
    SatisfiesEqualityConstrainedQpKKTSystem G A rhs₁ rhs₂ (y ∘ Sum.inl) (y ∘ Sum.inr) := by
  let y := (kktMatrix G A)⁻¹.mulVec (Sum.elim rhs₁ rhs₂)
  have hKKTUnit : IsUnit (kktMatrix G A) :=
    kktMatrix_isUnit_of_reducedHessian_posDef G A Z hA hZ hReduced
  have hKKTDet : IsUnit (kktMatrix G A).det :=
    (kktMatrix G A).isUnit_iff_isUnit_det.mp hKKTUnit
  have hy_decomp : y = Sum.elim (y ∘ Sum.inl) (y ∘ Sum.inr) := by
    funext i
    cases i <;> rfl
  have hy_block :
      (kktMatrix G A).mulVec y = Sum.elim rhs₁ rhs₂ := by
    -- The inverse KKT operator sends the requested right-hand side back to a genuine KKT pair.
    calc
      (kktMatrix G A).mulVec y =
          (kktMatrix G A).mulVec ((kktMatrix G A)⁻¹.mulVec (Sum.elim rhs₁ rhs₂)) := by
            rfl
      _ = ((kktMatrix G A) * (kktMatrix G A)⁻¹).mulVec (Sum.elim rhs₁ rhs₂) := by
            exact Matrix.mulVec_mulVec
              (Sum.elim rhs₁ rhs₂) (kktMatrix G A) (kktMatrix G A)⁻¹
      _ = Sum.elim rhs₁ rhs₂ := by
            rw [Matrix.mul_nonsing_inv (kktMatrix G A) hKKTDet]
            simp
  have hy_block' :
      (kktMatrix G A).mulVec (Sum.elim (y ∘ Sum.inl) (y ∘ Sum.inr)) = Sum.elim rhs₁ rhs₂ := by
    rw [← hy_decomp]
    exact hy_block
  exact (kktMatrix_mulVec_sumElim_iff G A rhs₁ rhs₂ (y ∘ Sum.inl) (y ∘ Sum.inr)).1 hy_block'

/-- Helper for Chapter09 Exercise 9.12: every KKT solution with zero dual right-hand side has
its primal component given by the reduced-space null-space formula. -/
lemma primal_solution_of_zero_dual_rhs_eq_nullspace_formula
    (G : HessianMatrix) (A : ConstraintMatrix) (Z : ReducedBasisMatrix)
    (hZ : IsReducedNullMatrix A Z) (hReduced : (Zᵀ * G * Z).PosDef)
    {p : Fin n → ℝ} {x : Fin n → ℝ} {lam : Fin m → ℝ}
    (hSystem : SatisfiesEqualityConstrainedQpKKTSystem G A p 0 x lam) :
    x = (Z * (Zᵀ * G * Z)⁻¹ * Zᵀ).mulVec p := by
  have hx_mem_ker : Aᵀ.mulVec x = 0 := by
    -- The zero dual right-hand side means the primal variable already lies in `ker Aᵀ`.
    simpa using hSystem.dual_eq
  obtain ⟨u, hu⟩ := hZ.eq_mulVec x hx_mem_ker
  have hPrimal : G.mulVec x = p + A.mulVec lam := sub_eq_iff_eq_add.mp hSystem.primal_eq
  have hATZ : Aᵀ * Z = 0 := transpose_mul_reducedBasis_eq_zero A Z hZ
  have hZTA : Zᵀ * A = 0 := by
    -- Transposing `Aᵀ Z = 0` gives the orthogonality identity `Zᵀ A = 0`.
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hATZ
  have hCompressed : (Zᵀ * G * Z).mulVec u = Zᵀ.mulVec p := by
    -- Compress the primal equation through `Zᵀ` and eliminate the multiplier term by `Zᵀ A = 0`.
    calc
      (Zᵀ * G * Z).mulVec u = Zᵀ.mulVec (G.mulVec (Z.mulVec u)) := by
        rw [Matrix.mul_assoc]
        rw [← Matrix.mulVec_mulVec u Zᵀ (G * Z)]
        congr 1
        symm
        exact Matrix.mulVec_mulVec u G Z
      _ = Zᵀ.mulVec (G.mulVec x) := by rw [hu]
      _ = Zᵀ.mulVec (p + A.mulVec lam) := by rw [hPrimal]
      _ = Zᵀ.mulVec p + Zᵀ.mulVec (A.mulVec lam) := by rw [Matrix.mulVec_add]
      _ = Zᵀ.mulVec p + (Zᵀ * A).mulVec lam := by
            rw [← Matrix.mulVec_mulVec lam Zᵀ A]
      _ = Zᵀ.mulVec p := by simp [hZTA]
  have hReducedDet : IsUnit (Zᵀ * G * Z).det :=
    (Zᵀ * G * Z).isUnit_iff_isUnit_det.mp hReduced.isUnit
  have hCompressedCandidate :
      (Zᵀ * G * Z).mulVec ((Zᵀ * G * Z)⁻¹.mulVec (Zᵀ.mulVec p)) = Zᵀ.mulVec p := by
    -- Inverting the reduced Hessian solves the compressed reduced-space equation for `u`.
    calc
      (Zᵀ * G * Z).mulVec ((Zᵀ * G * Z)⁻¹.mulVec (Zᵀ.mulVec p)) =
          ((Zᵀ * G * Z) * (Zᵀ * G * Z)⁻¹).mulVec (Zᵀ.mulVec p) := by
            exact Matrix.mulVec_mulVec
              (Zᵀ.mulVec p) (Zᵀ * G * Z) ((Zᵀ * G * Z)⁻¹)
      _ = Zᵀ.mulVec p := by
            rw [Matrix.mul_nonsing_inv (Zᵀ * G * Z) hReducedDet]
            simp
  have hReducedInj : Function.Injective (Zᵀ * G * Z).mulVec :=
    Matrix.mulVec_injective_of_isUnit hReduced.isUnit
  have hu_formula : u = (Zᵀ * G * Z)⁻¹.mulVec (Zᵀ.mulVec p) :=
    hReducedInj (hCompressed.trans hCompressedCandidate.symm)
  -- Substitute the reduced coordinates back into `x = Z u`.
  calc
    x = Z.mulVec u := hu.symm
    _ = Z.mulVec ((Zᵀ * G * Z)⁻¹.mulVec (Zᵀ.mulVec p)) := by rw [hu_formula]
    _ = (Z * (Zᵀ * G * Z)⁻¹).mulVec (Zᵀ.mulVec p) := by
          exact Matrix.mulVec_mulVec
            (Zᵀ.mulVec p) Z ((Zᵀ * G * Z)⁻¹)
    _ = (Z * (Zᵀ * G * Z)⁻¹ * Zᵀ).mulVec p := by
          rw [Matrix.mul_assoc]
          simpa [Matrix.mul_assoc] using
            (Matrix.mulVec_mulVec p (Z * (Zᵀ * G * Z)⁻¹) Zᵀ)

/-- Helper for Chapter09 Exercise 9.12: the primal component of the inverse-KKT action on a pure
primal right-hand side is exactly the `U` block action. -/
lemma inverse_pure_primal_primal_component_eq_u_block
    (G : HessianMatrix) (A : ConstraintMatrix) (p : Fin n → ℝ) :
    (((kktMatrix G A)⁻¹).mulVec (Sum.elim p 0)) ∘ Sum.inl = (kktInverseU G A).mulVec p := by
  -- Route correction: isolate the unstable block extraction here so the main proof stays in the
  -- KKT-system API.
  rw [← Matrix.fromBlocks_toBlocks ((kktMatrix G A)⁻¹)]
  ext i
  simp [kktInverseU, Matrix.fromBlocks_mulVec]

/-- Helper for Chapter09 Exercise 9.12: the `U` block acts on every primal right-hand side by
the reduced-space null-space formula. -/
lemma kkt_inverse_u_mulVec_eq_nullspace_formula
    (G : HessianMatrix) (A : ConstraintMatrix) (Z : ReducedBasisMatrix)
    (hA : Function.Injective A.mulVec) (hZ : IsReducedNullMatrix A Z)
    (hReduced : (Zᵀ * G * Z).PosDef)
    (p : Fin n → ℝ) :
    (kktInverseU G A).mulVec p = (Z * (Zᵀ * G * Z)⁻¹ * Zᵀ).mulVec p := by
  let y := ((kktMatrix G A)⁻¹).mulVec (Sum.elim p 0)
  have hSystem :
      SatisfiesEqualityConstrainedQpKKTSystem G A p 0 (y ∘ Sum.inl) (y ∘ Sum.inr) :=
    inverse_kkt_pair_satisfies_rhs G A Z p 0 hA hZ hReduced
  have hPrimal :
      y ∘ Sum.inl = (Z * (Zᵀ * G * Z)⁻¹ * Zᵀ).mulVec p :=
    primal_solution_of_zero_dual_rhs_eq_nullspace_formula G A Z hZ hReduced hSystem
  -- Read the inverse-generated KKT pair through the `U` block, then apply the reduced-space
  -- formula for zero dual right-hand side.
  calc
    (kktInverseU G A).mulVec p = y ∘ Sum.inl := by
      simpa [y] using (inverse_pure_primal_primal_component_eq_u_block G A p).symm
    _ = (Z * (Zᵀ * G * Z)⁻¹ * Zᵀ).mulVec p := hPrimal

/-- Chapter09 Exercise 9.12 (1): if `A` has full column rank, `G` is symmetric, `Z` spans
`ker Aᵀ`, and the reduced Hessian `Zᵀ G Z` is positive definite, then the `U` block of
`(kktMatrix G A)⁻¹` is `Z (Zᵀ G Z)⁻¹ Zᵀ`, i.e. formula `(9.3.58)`. -/
theorem kktInverseU_eq_nullSpaceFormula
    (G : HessianMatrix) (A : ConstraintMatrix) (Z : ReducedBasisMatrix)
    (hA : Function.Injective A.mulVec) (hGsym : G.IsSymm)
    (hZ : IsReducedNullMatrix A Z) (hReduced : (Zᵀ * G * Z).PosDef) :
    kktInverseU G A = Z * (Zᵀ * G * Z)⁻¹ * Zᵀ := by
  -- Compare the `U` block and the reduced-space operator on basis vectors of the primal space.
  ext i j
  have hMulVec :=
    kkt_inverse_u_mulVec_eq_nullspace_formula G A Z hA hZ hReduced (Pi.single j 1)
  simpa [Matrix.mulVec_single_one] using congrFun hMulVec i

/-- Helper for Chapter09 Exercise 9.12: transposing the generalized projector rewrites it into
the source formula `I - Z (Zᵀ G Z)⁻¹ Zᵀ G`. -/
lemma reducedProjection_transpose_eq
    (G : HessianMatrix) (Z : ReducedBasisMatrix) (hGsym : G.IsSymm)
    (hReduced : (Zᵀ * G * Z).PosDef) :
    (reducedProjection G Z)ᵀ = 1 - (Z * (Zᵀ * G * Z)⁻¹ * Zᵀ) * G := by
  set M : Matrix (Fin k) (Fin k) ℝ := Zᵀ * G * Z with hMDef
  have hMSymm : M.IsSymm := by
    simpa [hMDef] using hReduced.isHermitian
  -- Normalize the transpose of the projector using symmetry of `G` and of the reduced Hessian.
  calc
    (reducedProjection G Z)ᵀ = (1 - G * Z * M⁻¹ * Zᵀ)ᵀ := by
      rw [reducedProjection_eq, hMDef]
    _ = 1 - (Zᵀ)ᵀ * (M⁻¹)ᵀ * Zᵀ * Gᵀ := by
          simp [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 - Z * M⁻¹ * Zᵀ * G := by
          simp [hGsym.eq, (Matrix.IsSymm.inv hMSymm).eq, Matrix.mul_assoc]
    _ = 1 - (Z * M⁻¹ * Zᵀ) * G := by simp [Matrix.mul_assoc]
    _ = 1 - (Z * (Zᵀ * G * Z)⁻¹ * Zᵀ) * G := by rw [hMDef]

/-- Helper for Chapter09 Exercise 9.12: the transpose of the generalized projector annihilates
the reduced null-space basis `Z`. -/
lemma reducedProjection_transpose_mul_reducedBasis_eq_zero
    (G : HessianMatrix) (Z : ReducedBasisMatrix) (hGsym : G.IsSymm)
    (hReduced : (Zᵀ * G * Z).PosDef) :
    (reducedProjection G Z)ᵀ * Z = 0 := by
  set M : Matrix (Fin k) (Fin k) ℝ := Zᵀ * G * Z with hM
  have hMDet : IsUnit M.det := by
    have hMPos : M.PosDef := by simpa [hM] using hReduced
    exact M.isUnit_iff_isUnit_det.mp hMPos.isUnit
  -- Rewrite `Pᵀ Z` into `Z - Z M⁻¹ M` and cancel the reduced Hessian.
  calc
    (reducedProjection G Z)ᵀ * Z = (1 - (Z * M⁻¹ * Zᵀ) * G) * Z := by
      rw [reducedProjection_transpose_eq G Z hGsym hReduced, hM]
    _ = Z - Z * M⁻¹ * (Zᵀ * G * Z) := by
      simp [Matrix.sub_mul, Matrix.mul_assoc]
    _ = Z - Z := by
      rw [hM, Matrix.nonsing_inv_mul_cancel_right M Z hMDet]
    _ = 0 := sub_self Z

/-- Helper for Chapter09 Exercise 9.12: after applying the transpose projector, the left inverse
`Y` reconstructs the same projected vector from its constraint image. -/
lemma reducedProjection_transpose_mul_leftInverse_mul_constraintTranspose_eq
    (G : HessianMatrix) (A : ConstraintMatrix) (Y : LeftInverseMatrix) (Z : ReducedBasisMatrix)
    (hGsym : G.IsSymm) (hY : Aᵀ * Y = 1) (hZ : IsReducedNullMatrix A Z)
    (hReduced : (Zᵀ * G * Z).PosDef) :
    (reducedProjection G Z)ᵀ * Y * Aᵀ = (reducedProjection G Z)ᵀ := by
  have hResidual :
      (reducedProjection G Z)ᵀ * ((1 : HessianMatrix) - Y * Aᵀ) = 0 := by
    ext i j
    let e : Fin n → ℝ := Pi.single j 1
    have hKer :
        Aᵀ.mulVec (((1 : HessianMatrix) - Y * Aᵀ).mulVec e) = 0 := by
      have hAYResidual : Aᵀ * ((1 : HessianMatrix) - Y * Aᵀ) = 0 := by
        calc
          Aᵀ * ((1 : HessianMatrix) - Y * Aᵀ) = Aᵀ - Aᵀ * (Y * Aᵀ) := by
            rw [Matrix.mul_sub, Matrix.mul_one]
          _ = Aᵀ - (Aᵀ * Y) * Aᵀ := by rw [Matrix.mul_assoc]
          _ = Aᵀ - Aᵀ := by rw [hY, Matrix.one_mul]
          _ = 0 := sub_self Aᵀ
      -- Every column of `I - Y Aᵀ` lies in `ker Aᵀ`.
      calc
        Aᵀ.mulVec (((1 : HessianMatrix) - Y * Aᵀ).mulVec e) =
            (Aᵀ * ((1 : HessianMatrix) - Y * Aᵀ)).mulVec e := by
              exact Matrix.mulVec_mulVec e Aᵀ ((1 : HessianMatrix) - Y * Aᵀ)
        _ = 0 := by simpa [hAYResidual]
    obtain ⟨u, hu⟩ := hZ.eq_mulVec (((1 : HessianMatrix) - Y * Aᵀ).mulVec e) hKer
    have hKill :
        (reducedProjection G Z)ᵀ.mulVec (((1 : HessianMatrix) - Y * Aᵀ).mulVec e) = 0 := by
      -- Reduced-space directions are annihilated by the transpose projector.
      calc
        (reducedProjection G Z)ᵀ.mulVec (((1 : HessianMatrix) - Y * Aᵀ).mulVec e) =
            (reducedProjection G Z)ᵀ.mulVec (Z.mulVec u) := by rw [hu]
        _ = ((reducedProjection G Z)ᵀ * Z).mulVec u := by
              exact Matrix.mulVec_mulVec u ((reducedProjection G Z)ᵀ) Z
        _ = 0 := by
              simp [reducedProjection_transpose_mul_reducedBasis_eq_zero G Z hGsym hReduced]
    have hColumn :
        (((reducedProjection G Z)ᵀ * ((1 : HessianMatrix) - Y * Aᵀ)).mulVec e) i = 0 := by
      simpa [Matrix.mulVec_mulVec] using congrFun hKill i
    simpa [e, Matrix.mulVec_single_one] using hColumn
  have hResidualExpanded :
      (reducedProjection G Z)ᵀ - (reducedProjection G Z)ᵀ * (Y * Aᵀ) = 0 := by
    simpa [Matrix.mul_sub, Matrix.mul_one] using hResidual
  -- Reassemble `Pᵀ Y Aᵀ` from the vanishing of `Pᵀ (I - Y Aᵀ)`.
  calc
    (reducedProjection G Z)ᵀ * Y * Aᵀ = (reducedProjection G Z)ᵀ * (Y * Aᵀ) := by
      rw [Matrix.mul_assoc]
    _ = (reducedProjection G Z)ᵀ := by
      exact (sub_eq_zero.mp hResidualExpanded).symm

/-- Helper for Chapter09 Exercise 9.12: the generalized-elimination formulas produce a KKT
solution for every pure dual right-hand side `(0, q)`. -/
lemma dual_rhs_solution_has_generalized_elimination_form
    (G : HessianMatrix) (A : ConstraintMatrix) (Y : LeftInverseMatrix) (Z : ReducedBasisMatrix)
    (q : Fin m → ℝ)
    (hA : Function.Injective A.mulVec) (hGsym : G.IsSymm) (hY : Aᵀ * Y = 1)
    (hZ : IsReducedNullMatrix A Z) (hReduced : (Zᵀ * G * Z).PosDef) :
    SatisfiesEqualityConstrainedQpKKTSystem G A 0 q
      ((-(reducedProjection G Z)ᵀ * Y).mulVec q)
      ((-Yᵀ * G * (reducedProjection G Z)ᵀ * Y).mulVec q) := by
  let P : HessianMatrix := reducedProjection G Z
  have hATZ : Aᵀ * Z = 0 := transpose_mul_reducedBasis_eq_zero A Z hZ
  have hATPT : Aᵀ * Pᵀ = Aᵀ := by
    -- The transpose projector preserves every constraint row because its correction term is in
    -- the reduced null space.
    have hCorrection :
        Aᵀ * ((Z * (Zᵀ * G * Z)⁻¹ * Zᵀ) * G) = 0 := by
      calc
        Aᵀ * ((Z * (Zᵀ * G * Z)⁻¹ * Zᵀ) * G) =
            ((Aᵀ * Z) * (Zᵀ * G * Z)⁻¹ * Zᵀ) * G := by
              simp [Matrix.mul_assoc]
        _ = 0 := by simp [hATZ]
    calc
      Aᵀ * Pᵀ = Aᵀ * (1 - (Z * (Zᵀ * G * Z)⁻¹ * Zᵀ) * G) := by
        rw [show P = reducedProjection G Z by rfl, reducedProjection_transpose_eq G Z hGsym hReduced]
      _ = Aᵀ := by
        rw [Matrix.mul_sub, Matrix.mul_one]
        rw [hCorrection]
        simp
  have hATPTY : Aᵀ * Pᵀ * Y = 1 := by
    calc
      Aᵀ * Pᵀ * Y = Aᵀ * Y := by rw [hATPT]
      _ = 1 := hY
  have hAYTP : A * Yᵀ * P = P := by
    -- Transpose the reconstruction identity to move from `Pᵀ` back to `P`.
    have hTranspose :=
      congrArg Matrix.transpose
        (reducedProjection_transpose_mul_leftInverse_mul_constraintTranspose_eq
          G A Y Z hGsym hY hZ hReduced)
    simpa [P, Matrix.transpose_mul, Matrix.mul_assoc] using hTranspose
  have hPG : P * G = G * Pᵀ := by
    -- Both sides normalize to the same expanded projector-with-Hessian product.
    calc
      P * G = (1 - G * Z * (Zᵀ * G * Z)⁻¹ * Zᵀ) * G := by
        rw [show P = reducedProjection G Z by rfl, reducedProjection_eq]
      _ = G - G * Z * (Zᵀ * G * Z)⁻¹ * Zᵀ * G := by
        simp [Matrix.sub_mul, Matrix.mul_assoc]
      _ = G * (1 - (Z * (Zᵀ * G * Z)⁻¹ * Zᵀ) * G) := by
        rw [Matrix.mul_sub, Matrix.mul_one]
        simp [Matrix.mul_assoc]
      _ = G * Pᵀ := by
        rw [show P = reducedProjection G Z by rfl, reducedProjection_transpose_eq G Z hGsym hReduced]
  have hPrimalBridge : A * Yᵀ * G * Pᵀ * Y = G * Pᵀ * Y := by
    -- Replace `G Pᵀ` by `P G`, use the transposed reconstruction identity, and convert back.
    calc
      A * Yᵀ * G * Pᵀ * Y = A * Yᵀ * (G * Pᵀ) * Y := by
        simp [Matrix.mul_assoc]
      _ = A * Yᵀ * (P * G) * Y := by rw [hPG.symm]
      _ = (A * Yᵀ * P) * G * Y := by
        simp [Matrix.mul_assoc]
      _ = P * G * Y := by rw [hAYTP]
      _ = G * Pᵀ * Y := by
        simpa [Matrix.mul_assoc] using congrArg (fun M => M * Y) hPG
  refine ⟨?_, ?_⟩
  · -- Rewrite the primal block equation into a single matrix identity and close it with the
    -- projector bridge.
    calc
      G.mulVec ((-Pᵀ * Y).mulVec q) - A.mulVec ((-Yᵀ * G * Pᵀ * Y).mulVec q) =
          (G * (-Pᵀ * Y) - A * (-Yᵀ * G * Pᵀ * Y)).mulVec q := by
            rw [Matrix.sub_mulVec]
            simp [Matrix.mulVec_mulVec]
      _ = 0 := by
        have hPrimalMat : G * (-Pᵀ * Y) - A * (-Yᵀ * G * Pᵀ * Y) = 0 := by
          calc
            G * (-Pᵀ * Y) - A * (-Yᵀ * G * Pᵀ * Y) =
                -(G * Pᵀ * Y) + A * Yᵀ * G * Pᵀ * Y := by
                  simp [sub_eq_add_neg, Matrix.mul_assoc]
            _ = -(G * Pᵀ * Y) + G * Pᵀ * Y := by rw [hPrimalBridge]
            _ = 0 := by simp
        rw [hPrimalMat]
        simp
  · -- The dual block equation is exactly `(-Aᵀ) * (-Pᵀ Y) = I`.
    calc
      -Aᵀ.mulVec ((-Pᵀ * Y).mulVec q) = -((Aᵀ * (-Pᵀ * Y)).mulVec q) := by
        rw [← Matrix.mulVec_mulVec q Aᵀ (-Pᵀ * Y)]
      _ = q := by
        have hDualMat : Aᵀ * (-Pᵀ * Y) = -1 := by
          calc
            Aᵀ * (-Pᵀ * Y) = -(Aᵀ * Pᵀ * Y) := by simp [Matrix.mul_assoc]
            _ = -1 := by rw [hATPTY]
        rw [hDualMat]
        simpa [Matrix.neg_mulVec]

/-- Helper for Chapter09 Exercise 9.12: the pure-dual inverse-KKT action splits into the `W` and
`T` block actions on the primal and multiplier components. -/
lemma inverse_pure_dual_components_eq_w_t_blocks
    (G : HessianMatrix) (A : ConstraintMatrix) (q : Fin m → ℝ) :
    ((((kktMatrix G A)⁻¹).mulVec (Sum.elim 0 q)) ∘ Sum.inl = (kktInverseW G A).mulVec q) ∧
      ((((kktMatrix G A)⁻¹).mulVec (Sum.elim 0 q)) ∘ Sum.inr = (kktInverseT G A).mulVec q) := by
  -- Route correction: isolate the second block extraction once so the uniqueness proof only
  -- compares KKT pairs.
  constructor
  · rw [← Matrix.fromBlocks_toBlocks ((kktMatrix G A)⁻¹)]
    ext i
    simp [kktInverseW, Matrix.fromBlocks_mulVec]
  · rw [← Matrix.fromBlocks_toBlocks ((kktMatrix G A)⁻¹)]
    ext i
    simp [kktInverseT, Matrix.fromBlocks_mulVec]

/-- Helper for Chapter09 Exercise 9.12: the inverse KKT blocks acting on a pure dual right-hand
side agree with the generalized-elimination formulas for both the primal and multiplier
components. -/
lemma dual_rhs_inverse_blocks_mulVec_eq_generalized_elimination
    (G : HessianMatrix) (A : ConstraintMatrix) (Y : LeftInverseMatrix) (Z : ReducedBasisMatrix)
    (q : Fin m → ℝ)
    (hA : Function.Injective A.mulVec) (hGsym : G.IsSymm) (hY : Aᵀ * Y = 1)
    (hZ : IsReducedNullMatrix A Z) (hReduced : (Zᵀ * G * Z).PosDef) :
    (kktInverseW G A).mulVec q = (-(reducedProjection G Z)ᵀ * Y).mulVec q ∧
      (kktInverseT G A).mulVec q = (-Yᵀ * G * (reducedProjection G Z)ᵀ * Y).mulVec q := by
  let y := ((kktMatrix G A)⁻¹).mulVec (Sum.elim 0 q)
  have hInverse :
      SatisfiesEqualityConstrainedQpKKTSystem G A 0 q (y ∘ Sum.inl) (y ∘ Sum.inr) :=
    inverse_kkt_pair_satisfies_rhs G A Z 0 q hA hZ hReduced
  have hExplicit :
      SatisfiesEqualityConstrainedQpKKTSystem G A 0 q
        ((-(reducedProjection G Z)ᵀ * Y).mulVec q)
        ((-Yᵀ * G * (reducedProjection G Z)ᵀ * Y).mulVec q) :=
    dual_rhs_solution_has_generalized_elimination_form G A Y Z q hA hGsym hY hZ hReduced
  obtain ⟨xLambda, hxLambda, hxUnique⟩ :=
    existsUnique_kktPair_of_reducedHessian_posDef G A Z 0 (-q) hA hZ hReduced
  have hInversePair : (y ∘ Sum.inl, y ∘ Sum.inr) = xLambda := by
    refine hxUnique _ ?_
    simpa using hInverse
  have hExplicitPair :
      (((-(reducedProjection G Z)ᵀ * Y).mulVec q),
        ((-Yᵀ * G * (reducedProjection G Z)ᵀ * Y).mulVec q)) = xLambda := by
    refine hxUnique _ ?_
    simpa using hExplicit
  have hPairEq :
      (y ∘ Sum.inl, y ∘ Sum.inr) =
        (((-(reducedProjection G Z)ᵀ * Y).mulVec q),
          ((-Yᵀ * G * (reducedProjection G Z)ᵀ * Y).mulVec q)) := by
    exact hInversePair.trans hExplicitPair.symm
  have hBlocks := inverse_pure_dual_components_eq_w_t_blocks G A q
  constructor
  · -- Uniqueness identifies the inverse-generated primal component with the generalized
    -- elimination primal formula.
    calc
      (kktInverseW G A).mulVec q = y ∘ Sum.inl := by
        simpa [y] using hBlocks.1.symm
      _ = (-(reducedProjection G Z)ᵀ * Y).mulVec q := by
        simpa using congrArg Prod.fst hPairEq
  · -- The same uniqueness argument identifies the multiplier component.
    calc
      (kktInverseT G A).mulVec q = y ∘ Sum.inr := by
        simpa [y] using hBlocks.2.symm
      _ = (-Yᵀ * G * (reducedProjection G Z)ᵀ * Y).mulVec q := by
        simpa using congrArg Prod.snd hPairEq

/-- Chapter09 Exercise 9.12 (2): under the same generalized-elimination hypotheses, the `W`
block of `(kktMatrix G A)⁻¹` is `-Pᵀ Y`, where `P = reducedProjection G Z`, `G` is symmetric,
and `Y` satisfies `Aᵀ Y = I`, i.e. formula `(9.3.59)`. -/
theorem kktInverseW_eq_neg_projectionTranspose_mul_leftInverse
    (G : HessianMatrix) (A : ConstraintMatrix) (Y : LeftInverseMatrix) (Z : ReducedBasisMatrix)
    (hA : Function.Injective A.mulVec) (hGsym : G.IsSymm) (hY : Aᵀ * Y = 1)
    (hZ : IsReducedNullMatrix A Z) (hReduced : (Zᵀ * G * Z).PosDef) :
    kktInverseW G A = -(reducedProjection G Z)ᵀ * Y := by
  -- Compare the `W` block and the generalized-elimination operator on basis vectors of the
  -- multiplier space.
  ext i j
  have hMulVec :=
    (dual_rhs_inverse_blocks_mulVec_eq_generalized_elimination
      G A Y Z (Pi.single j 1) hA hGsym hY hZ hReduced).1
  simpa [Matrix.mulVec_single_one] using congrFun hMulVec i

/-- Chapter09 Exercise 9.12 (3): under the same generalized-elimination hypotheses, the `T`
block of `(kktMatrix G A)⁻¹` is `-Yᵀ G Pᵀ Y`, where `P = reducedProjection G Z`, `G` is
symmetric, and `Y` satisfies `Aᵀ Y = I`, i.e. formula `(9.3.60)`. -/
theorem kktInverseT_eq_neg_leftInverseTranspose_mul_hessian_mul_projectionTranspose_mul_leftInverse
    (G : HessianMatrix) (A : ConstraintMatrix) (Y : LeftInverseMatrix) (Z : ReducedBasisMatrix)
    (hA : Function.Injective A.mulVec) (hGsym : G.IsSymm) (hY : Aᵀ * Y = 1)
    (hZ : IsReducedNullMatrix A Z) (hReduced : (Zᵀ * G * Z).PosDef) :
    kktInverseT G A = -Yᵀ * G * (reducedProjection G Z)ᵀ * Y := by
  -- Compare the `T` block and the generalized-elimination multiplier operator on basis vectors.
  ext i j
  have hMulVec :=
    (dual_rhs_inverse_blocks_mulVec_eq_generalized_elimination
      G A Y Z (Pi.single j 1) hA hGsym hY hZ hReduced).2
  simpa [Matrix.mulVec_single_one] using congrFun hMulVec i

end
