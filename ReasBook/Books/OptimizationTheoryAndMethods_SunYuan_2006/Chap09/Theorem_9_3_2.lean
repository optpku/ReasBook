/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced `Matrix.PosDef` and
-- `Matrix.PosDef.isUnit` as the canonical positive-definite and nonsingularity API. This file
-- keeps the Chapter 9 owners `kktMatrix` and `IsReducedNullMatrix` explicit, but only their
-- positive-definiteness theorems stay specialized to `ℝ`.

section

variable {R : Type*} [Ring R]
variable {n m : ℕ}

/-- The block KKT matrix `[[G, -A], [-Aᵀ, 0]]` for an equality-constrained quadratic program. -/
def kktMatrix (G : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin m) R) :
    Matrix (Sum (Fin n) (Fin m)) (Sum (Fin n) (Fin m)) R :=
  Matrix.fromBlocks G (-A) (-A.transpose) 0

#print axioms kktMatrix

/-- Unfolding `kktMatrix G A` gives the source block matrix `[[G, -A], [-Aᵀ, 0]]`. -/
theorem kktMatrix_eq (G : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin m) R) :
    kktMatrix G A = Matrix.fromBlocks G (-A) (-A.transpose) 0 := rfl

/-- A pair `(x, λ)` satisfies the block KKT system with right-hand side `(rhs₁, rhs₂)` when
`G.mulVec x - A.mulVec λ = rhs₁` and `-A.transpose.mulVec x = rhs₂`. -/
structure SatisfiesEqualityConstrainedQpKKTSystem
    (G : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin m) R)
    (rhs₁ : Fin n → R) (rhs₂ : Fin m → R) (x : Fin n → R) (lam : Fin m → R) : Prop where
  primal_eq : G.mulVec x - A.mulVec lam = rhs₁
  dual_eq : -A.transpose.mulVec x = rhs₂

/-- Unfolding `SatisfiesEqualityConstrainedQpKKTSystem G A rhs₁ rhs₂ x lam` gives the source
primal and dual block equations. -/
theorem satisfiesEqualityConstrainedQpKKTSystem_iff
    (G : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin m) R)
    (rhs₁ : Fin n → R) (rhs₂ : Fin m → R) (x : Fin n → R) (lam : Fin m → R) :
    SatisfiesEqualityConstrainedQpKKTSystem G A rhs₁ rhs₂ x lam ↔
      G.mulVec x - A.mulVec lam = rhs₁ ∧ -A.transpose.mulVec x = rhs₂ := by
  refine ⟨fun h ↦ ⟨h.primal_eq, h.dual_eq⟩, ?_⟩
  rintro ⟨hPrimal, hDual⟩
  exact ⟨hPrimal, hDual⟩

end

section

variable {R : Type*} [Semiring R]
variable {n m k : ℕ}

/-- A matrix `Z` is a reduced-null-space matrix for `A` when its range is exactly `ker Aᵀ`. -/
structure IsReducedNullMatrix
    (A : Matrix (Fin n) (Fin m) R) (Z : Matrix (Fin n) (Fin k) R) : Prop where
  mem_ker : ∀ u : Fin k → R, A.transpose.mulVec (Z.mulVec u) = 0
  eq_mulVec :
    ∀ p : Fin n → R, A.transpose.mulVec p = 0 → ∃ u : Fin k → R, Z.mulVec u = p

/-- Unfolding `IsReducedNullMatrix A Z` gives the source kernel-inclusion and kernel-surjectivity
conditions for the reduced-null-space matrix `Z`. -/
theorem isReducedNullMatrix_iff
    (A : Matrix (Fin n) (Fin m) R) (Z : Matrix (Fin n) (Fin k) R) :
    IsReducedNullMatrix A Z ↔
      (∀ u : Fin k → R, A.transpose.mulVec (Z.mulVec u) = 0) ∧
        ∀ p : Fin n → R, A.transpose.mulVec p = 0 → ∃ u : Fin k → R, Z.mulVec u = p := by
  refine ⟨fun h ↦ ⟨h.mem_ker, h.eq_mulVec⟩, ?_⟩
  rintro ⟨hKer, hSurj⟩
  exact ⟨hKer, hSurj⟩

end

variable {n m k : ℕ}

local notation "PrimalPoint" => Fin n → ℝ
local notation "DualPoint" => Fin m → ℝ
local notation "ReducedPoint" => Fin k → ℝ
local notation "HessianMatrix" => Matrix (Fin n) (Fin n) ℝ
local notation "ConstraintMatrix" => Matrix (Fin n) (Fin m) ℝ
local notation "ReducedBasisMatrix" => Matrix (Fin n) (Fin k) ℝ

/-- Helper for Chapter09 Theorem 9.3.2: multiplying the block vector `(x, λ)` by the KKT matrix
is equivalent to satisfying the two KKT equations with right-hand side `(rhs₁, rhs₂)`. -/
lemma kktMatrix_mulVec_sumElim_iff
    (G : HessianMatrix) (A : ConstraintMatrix)
    (rhs₁ : PrimalPoint) (rhs₂ : DualPoint) (x : PrimalPoint) (lam : DualPoint) :
    (kktMatrix G A).mulVec (Sum.elim x lam) = Sum.elim rhs₁ rhs₂ ↔
      SatisfiesEqualityConstrainedQpKKTSystem G A rhs₁ rhs₂ x lam := by
  -- Split the block-vector identity into its primal and dual components.
  rw [satisfiesEqualityConstrainedQpKKTSystem_iff]
  constructor
  · intro hVec
    constructor
    · ext i
      simpa [kktMatrix, sub_eq_add_neg, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using
        congrFun hVec (Sum.inl i)
    · ext i
      simpa [kktMatrix, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using
        congrFun hVec (Sum.inr i)
  · rintro ⟨hPrimal, hDual⟩
    ext i <;> cases i with
    | inl i =>
        simpa [kktMatrix, sub_eq_add_neg, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using
          congrFun hPrimal i
    | inr i =>
        simpa [kktMatrix, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using
          congrFun hDual i

/-- Helper for Chapter09 Theorem 9.3.2: the reduced-null-space condition implies the matrix
identity `Aᵀ Z = 0`. -/
lemma transpose_mul_reducedBasis_eq_zero
    (A : ConstraintMatrix) (Z : ReducedBasisMatrix) (hZ : IsReducedNullMatrix A Z) :
    A.transpose * Z = 0 := by
  -- Test the product on each basis vector to turn the kernel condition into a matrix equality.
  ext i j
  have hColumn : (A.transpose * Z).col j = 0 := by
    calc
      (A.transpose * Z).col j = (A.transpose * Z).mulVec (Pi.single j 1) := by
        symm
        exact Matrix.mulVec_single_one (A.transpose * Z) j
      _ = A.transpose.mulVec (Z.mulVec (Pi.single j 1)) := by
        symm
        exact Matrix.mulVec_mulVec (Pi.single j 1) A.transpose Z
      _ = 0 := by
        simpa [Matrix.mulVec_single_one] using hZ.mem_ker (Pi.single j 1)
  have hij : (A.transpose * Z).col j i = 0 := by
    simpa using congrArg (fun c => c i) hColumn
  simpa using hij

/-- Helper for Chapter09 Theorem 9.3.2: any vector in the kernel of the KKT matrix must vanish. -/
lemma eq_zero_of_kktMatrix_mulVec_eq_zero
    (G : HessianMatrix) (A : ConstraintMatrix) (Z : ReducedBasisMatrix)
    (hA : Function.Injective A.mulVec) (hZ : IsReducedNullMatrix A Z)
    (hReduced : (Z.transpose * G * Z).PosDef)
    {y : Sum (Fin n) (Fin m) → ℝ} (hy : (kktMatrix G A).mulVec y = 0) :
    y = 0 := by
  let p : PrimalPoint := y ∘ Sum.inl
  let v : DualPoint := y ∘ Sum.inr
  have hy_decomp : y = Sum.elim p v := by
    funext i
    cases i <;> simp [p, v]
  have hy_block : (kktMatrix G A).mulVec (Sum.elim p v) =
      Sum.elim (0 : PrimalPoint) (0 : DualPoint) := by
    calc
      (kktMatrix G A).mulVec (Sum.elim p v) = (kktMatrix G A).mulVec y := by
        simpa [hy_decomp]
      _ = 0 := hy
      _ = Sum.elim (0 : PrimalPoint) (0 : DualPoint) := by
        ext i <;> cases i <;> rfl
  have hSystem : SatisfiesEqualityConstrainedQpKKTSystem G A 0 0 p v :=
    (kktMatrix_mulVec_sumElim_iff G A 0 0 p v).1 hy_block
  have hp_mem_ker : A.transpose.mulVec p = 0 := by
    -- Read off the dual block equation `-Aᵀ p = 0`.
    simpa using hSystem.dual_eq
  obtain ⟨u, hu⟩ := hZ.eq_mulVec p hp_mem_ker
  have hPrimal : G.mulVec p = A.mulVec v := sub_eq_zero.mp hSystem.primal_eq
  have hATZ : A.transpose * Z = 0 := transpose_mul_reducedBasis_eq_zero A Z hZ
  have hZTA : Z.transpose * A = 0 := by
    -- Transpose the previous identity to obtain the orthogonality rewrite `Zᵀ A = 0`.
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hATZ
  have hCompressed : (Z.transpose * G * Z).mulVec u = 0 := by
    -- Compress the primal equation by `Zᵀ` and eliminate the constraint term using `Zᵀ A = 0`.
    calc
      (Z.transpose * G * Z).mulVec u = Z.transpose.mulVec (G.mulVec (Z.mulVec u)) := by
        rw [Matrix.mul_assoc]
        simp [Matrix.mulVec_mulVec]
      _ = Z.transpose.mulVec (G.mulVec p) := by simp [hu]
      _ = Z.transpose.mulVec (A.mulVec v) := by rw [hPrimal]
      _ = (Z.transpose * A).mulVec v := by simp [Matrix.mulVec_mulVec]
      _ = 0 := by simp [hZTA]
  have hReducedInj : Function.Injective (Z.transpose * G * Z).mulVec :=
    Matrix.mulVec_injective_of_isUnit hReduced.isUnit
  have hu_zero : u = 0 := hReducedInj (by simpa using hCompressed)
  have hp_zero : p = 0 := by
    -- The reduced coordinates vanish, so the primal component vanishes as well.
    simpa [hu_zero] using hu.symm
  have hAv_zero : A.mulVec v = 0 := by
    -- Substitute `p = 0` back into the primal equation.
    simpa [hp_zero] using hPrimal.symm
  have hv_zero : v = 0 := hA (by simpa using hAv_zero)
  calc
    y = Sum.elim p v := hy_decomp
    _ = 0 := by
      ext i <;> cases i <;> simp [hp_zero, hv_zero]

/-- Chapter09 Theorem 9.3.2 (1): if `A` has full column rank, `Z` spans `ker Aᵀ`, and the
reduced Hessian `Zᵀ G Z` is positive definite, then the KKT matrix `kktMatrix G A` is
nonsingular. -/
theorem kktMatrix_isUnit_of_reducedHessian_posDef
    (G : HessianMatrix) (A : ConstraintMatrix) (Z : ReducedBasisMatrix)
    (hA : Function.Injective A.mulVec) (hZ : IsReducedNullMatrix A Z)
    (hReduced : (Z.transpose * G * Z).PosDef) :
    IsUnit (kktMatrix G A) := by
  -- The source proof shows that the KKT matrix has trivial kernel, hence is invertible.
  apply (Matrix.mulVec_injective_iff_isUnit).mp
  intro y₁ y₂ hEq
  have hSub : (kktMatrix G A).mulVec (y₁ - y₂) = 0 := by
    simpa [Matrix.mulVec_sub, hEq]
  have hZero : y₁ - y₂ = 0 :=
    eq_zero_of_kktMatrix_mulVec_eq_zero G A Z hA hZ hReduced hSub
  exact sub_eq_zero.mp hZero

/-- Chapter09 Theorem 9.3.2 (2): for the equality-constrained quadratic program data given by
the linear term `g` and constraint target `b`, under the same hypotheses, equation `(9.3.46)`
has a unique KKT pair `(xStar, λStar)`. With the sign convention of
`SatisfiesEqualityConstrainedQpKKTSystem`, this is the block system with right-hand side
`(-g, -b)`. -/
theorem existsUnique_kktPair_of_reducedHessian_posDef
    (G : HessianMatrix) (A : ConstraintMatrix) (Z : ReducedBasisMatrix)
    (g : PrimalPoint) (b : DualPoint)
    (hA : Function.Injective A.mulVec) (hZ : IsReducedNullMatrix A Z)
    (hReduced : (Z.transpose * G * Z).PosDef) :
    ∃! xLambda : PrimalPoint × DualPoint,
      SatisfiesEqualityConstrainedQpKKTSystem G A (-g) (-b) xLambda.1 xLambda.2 := by
  have hKKTUnit : IsUnit (kktMatrix G A) :=
    kktMatrix_isUnit_of_reducedHessian_posDef G A Z hA hZ hReduced
  have hSurj : Function.Surjective (kktMatrix G A).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hKKTUnit
  obtain ⟨y, hy⟩ := hSurj (Sum.elim (-g) (-b))
  let x : PrimalPoint := y ∘ Sum.inl
  let lam : DualPoint := y ∘ Sum.inr
  have hy_decomp : y = Sum.elim x lam := by
    funext i
    cases i <;> simp [x, lam]
  have hy_block : (kktMatrix G A).mulVec (Sum.elim x lam) = Sum.elim (-g) (-b) := by
    calc
      (kktMatrix G A).mulVec (Sum.elim x lam) = (kktMatrix G A).mulVec y := by
        simpa [hy_decomp]
      _ = Sum.elim (-g) (-b) := hy
  have hSystem : SatisfiesEqualityConstrainedQpKKTSystem G A (-g) (-b) x lam :=
    (kktMatrix_mulVec_sumElim_iff G A (-g) (-b) x lam).1 hy_block
  refine ⟨(x, lam), hSystem, ?_⟩
  intro xLambda hOther
  have hInj : Function.Injective (kktMatrix G A).mulVec :=
    Matrix.mulVec_injective_of_isUnit hKKTUnit
  have hOther_block :
      (kktMatrix G A).mulVec (Sum.elim xLambda.1 xLambda.2) = Sum.elim (-g) (-b) :=
    (kktMatrix_mulVec_sumElim_iff G A (-g) (-b) xLambda.1 xLambda.2).2 hOther
  have hVecEq : Sum.elim xLambda.1 xLambda.2 = y := by
    -- Injectivity of the same KKT map upgrades equality of right-hand sides to equality of pairs.
    exact hInj (hOther_block.trans hy.symm)
  have hx_eq : xLambda.1 = x := by
    funext i
    simpa [x] using congrFun hVecEq (Sum.inl i)
  have hlam_eq : xLambda.2 = lam := by
    funext i
    simpa [lam] using congrFun hVecEq (Sum.inr i)
  exact Prod.ext hx_eq hlam_eq
