/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.UnitaryGroup

open scoped Matrix

noncomputable section

-- This file owns the project's canonical matrix-valued Moore-Penrose pseudoinverse over an
-- `RCLike` scalar. Exercise 1.5 and Theorem 1.2.7 reuse its `ℂ` specialization.

namespace Matrix

open LinearMap

local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- The Moore-Penrose pseudoinverse matrix obtained from the canonical range-projection
construction, with columns given by the pseudoinverse images of the standard basis vectors
of `EuclideanSpace 𝕜 m`. -/
def pseudoinverse {𝕜 m n : Type} [RCLike 𝕜] [Fintype m] [Fintype n]
    (A : Matrix m n 𝕜) : Matrix n m 𝕜 :=
  let T : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m := A.toEuclideanLin
  let K : Submodule 𝕜 (EuclideanSpace 𝕜 n) := T.ker
  fun i j ↦
    let y : T.range := T.range.orthogonalProjectionOnto (EuclideanSpace.single j (1 : 𝕜))
    let hK : IsCompl Kᗮ K := K.isCompl_orthogonal.symm
    ((((kerComplementEquivRange T hK).symm y : Kᗮ) : EuclideanSpace 𝕜 n) i)

scoped postfix:max "⁺" => Matrix.pseudoinverse

/-- The canonical Moore-Penrose pseudoinverse image `A⁺ b` in Euclidean coordinates. -/
def pseudoinverseMulVec {𝕜 m n : Type} [RCLike 𝕜] [Fintype m] [Fintype n]
    (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) : EuclideanSpace 𝕜 n :=
  (A⁺).toEuclideanLin b

/-- Evaluating `Matrix.pseudoinverseMulVec A b` recovers the source vector `A⁺ b`. -/
@[simp] theorem pseudoinverseMulVec_eq_toEuclideanLin_pseudoinverse
    {𝕜 m n : Type} [RCLike 𝕜] [Fintype m] [Fintype n]
    (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    pseudoinverseMulVec A b = (A⁺).toEuclideanLin b := rfl

/-- A rectangular matrix is diagonal when all off-diagonal entries vanish. -/
def IsRectangularDiagonal {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  ∀ i j, i.1 ≠ j.1 → D i j = 0

/-- A singular value decomposition of `A` is a factorization `A = U * D * Vᴴ` with unitary
factors `U` and `V` and a rectangular-diagonal middle factor `D` whose diagonal entries are
real and nonnegative. -/
def IsSingularValueDecomposition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (D : Matrix (Fin m) (Fin n) ℂ)
    (V : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A = U * D * Vᴴ ∧
    U ∈ unitaryGroup (Fin m) ℂ ∧
    V ∈ unitaryGroup (Fin n) ℂ ∧
    IsRectangularDiagonal D ∧
    ∀ i j, i.1 = j.1 → ∃ σ : ℝ, 0 ≤ σ ∧ D i j = (σ : ℂ)

/-- Helper for Chapter01 Exercise 1.5: a zero diagonal entry forces the whole matching row of a
rectangular diagonal matrix to vanish. -/
lemma row_eq_zero_of_isRectangularDiagonal_zero {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D)
    {i : Fin n} {j : Fin m} (hij : i.1 = j.1) (hD : D j i = 0) :
    ∀ l : Fin n, D j l = 0 := by
  intro l
  by_cases hl : l.1 = j.1
  · -- On the diagonal, the matching column is uniquely determined by the shared index.
    have hli : l = i := Fin.ext (hl.trans hij.symm)
    simpa [hli] using hD
  · -- Off the diagonal, the rectangular-diagonal hypothesis already gives the vanishing.
    exact hdiag j l (by
      intro hjl
      exact hl hjl.symm)

/-- Helper for Chapter01 Exercise 1.5: a nonzero diagonal entry gives an explicit preimage of the
corresponding standard basis vector in the range of `D.toEuclideanLin`. -/
lemma single_mem_range_of_isRectangularDiagonal_nonzero {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D)
    {i : Fin n} {j : Fin m} (hij : i.1 = j.1) (hD : D j i ≠ 0) :
    EuclideanSpace.single j (1 : ℂ) ∈ D.toEuclideanLin.range := by
  refine ⟨EuclideanSpace.single i ((D j i)⁻¹ : ℂ), ?_⟩
  -- The diagonal preimage is the corresponding reciprocal basis vector.
  rw [Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single, Matrix.mulVec_single,
    ← EuclideanSpace.toLp_single j (1 : ℂ)]
  congr 1
  ext k
  by_cases hk : k = j
  · -- On the matching row, the diagonal entry survives and cancels with its reciprocal.
    subst hk
    simp [Pi.single_apply, hD]
  · by_cases hki : k.1 = i.1
    · -- Any other row with the same index would equal `j`, contradicting `k ≠ j`.
      exact (hk (Fin.ext (hki.trans hij))).elim
    · -- Off the matching row, the rectangular-diagonal hypothesis kills the entry.
      simp [Pi.single_apply, hk, hdiag k i hki]

/-- Helper for Chapter01 Exercise 1.5: if the matching diagonal entry vanishes, then the
corresponding standard basis vector is orthogonal to the range of `D.toEuclideanLin`. -/
lemma single_mem_range_orthogonal_of_isRectangularDiagonal_zero {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D)
    {i : Fin n} {j : Fin m} (hij : i.1 = j.1) (hD : D j i = 0) :
    EuclideanSpace.single j (1 : ℂ) ∈ D.toEuclideanLin.rangeᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  rcases hy with ⟨x, rfl⟩
  -- The whole `j`th row is zero, so every range vector has zero `j`th coordinate.
  have hrow := row_eq_zero_of_isRectangularDiagonal_zero D hdiag hij hD
  have hcoord : (D.toEuclideanLin x) j = 0 := by
    rw [Matrix.toEuclideanLin_apply]
    simp [Matrix.mulVec, dotProduct, hrow]
  -- The basis vector `e_j` is therefore orthogonal to every vector in the range.
  simp [EuclideanSpace.inner_single_right, hcoord]

/-- Helper for Chapter01 Exercise 1.5: the ambient orthogonal projection onto the range of a
rectangular diagonal matrix either fixes the matching basis vector or kills it, according to
whether the corresponding diagonal entry is nonzero. -/
lemma starProjection_single_of_isRectangularDiagonal {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D)
    {i : Fin n} {j : Fin m} (hij : i.1 = j.1) :
    D.toEuclideanLin.range.starProjection (EuclideanSpace.single j (1 : ℂ)) =
      if D j i = 0 then 0 else EuclideanSpace.single j (1 : ℂ) := by
  by_cases hD : D j i = 0
  · -- In the zero branch, `e_j` is orthogonal to the range, so its projection is `0`.
    have hproj :
        D.toEuclideanLin.range.starProjection (EuclideanSpace.single j (1 : ℂ)) = 0 := by
      apply Submodule.eq_starProjection_of_mem_orthogonal
      · exact zero_mem _
      · simpa using
          single_mem_range_orthogonal_of_isRectangularDiagonal_zero D hdiag hij hD
    simpa [hD] using hproj
  · -- In the nonzero branch, `e_j` already lies in the range, so projection fixes it.
    have hproj :
        D.toEuclideanLin.range.starProjection (EuclideanSpace.single j (1 : ℂ)) =
          EuclideanSpace.single j (1 : ℂ) :=
      (Submodule.starProjection_eq_self_iff
        (K := D.toEuclideanLin.range)).2
        (single_mem_range_of_isRectangularDiagonal_nonzero D hdiag hij hD)
    simpa [hD] using hproj

/-- Helper for Chapter01 Exercise 1.5: once `e_j` lies in the range, the orthogonal projection
onto the range fixes it. -/
lemma orthogonalProjectionOnto_single_of_isRectangularDiagonal_nonzero {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D)
    {i : Fin n} {j : Fin m} (hij : i.1 = j.1) (hD : D j i ≠ 0) :
    D.toEuclideanLin.range.orthogonalProjectionOnto (EuclideanSpace.single j (1 : ℂ)) =
      ⟨EuclideanSpace.single j (1 : ℂ),
        single_mem_range_of_isRectangularDiagonal_nonzero D hdiag hij hD⟩ := by
  -- This basis vector already lies in the range, so projection fixes it.
  simpa using
    D.toEuclideanLin.range.orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨EuclideanSpace.single j (1 : ℂ),
        single_mem_range_of_isRectangularDiagonal_nonzero D hdiag hij hD⟩

/-- Helper for Chapter01 Exercise 1.5: if the matching diagonal entry vanishes, the orthogonal
projection of `e_j` onto the range is zero. -/
lemma orthogonalProjectionOnto_single_eq_zero_of_isRectangularDiagonal_zero {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D)
    {i : Fin n} {j : Fin m} (hij : i.1 = j.1) (hD : D j i = 0) :
    D.toEuclideanLin.range.orthogonalProjectionOnto (EuclideanSpace.single j (1 : ℂ)) = 0 := by
  -- Orthogonality to the full range forces the range projection to vanish.
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
  exact single_mem_range_orthogonal_of_isRectangularDiagonal_zero D hdiag hij hD

/-- Helper for Chapter01 Exercise 1.5: `EuclideanSpace.single` does not depend on which
`DecidableEq` instance on `Fin m` is used to build it. -/
lemma single_eq_of_decidableEq {m : ℕ} (d₁ d₂ : DecidableEq (Fin m)) (j : Fin m) (c : ℂ) :
    @EuclideanSpace.single (Fin m) ℂ _ d₁ j c = @EuclideanSpace.single (Fin m) ℂ _ d₂ j c := by
  -- Compare both vectors coordinatewise; the point mass is the same function either way.
  ext k
  by_cases hk : k = j
  · subst hk
    simp [EuclideanSpace.single_apply]
  · simp [EuclideanSpace.single_apply, hk]

/-- Helper for Chapter01 Exercise 1.5: if row `j` has no matching diagonal column at all, then
the range projection of `e_j` is zero. -/
lemma orthogonalProjectionOnto_single_eq_zero_of_isRectangularDiagonal_no_matching_column
    {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D)
    {j : Fin m} (hnomatch : ¬ ∃ i0 : Fin n, i0.1 = j.1) :
    D.toEuclideanLin.range.orthogonalProjectionOnto (EuclideanSpace.single j (1 : ℂ)) = 0 := by
  -- Show first that the whole row `j` vanishes, so `e_j` is orthogonal to the range.
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
  rw [Submodule.mem_orthogonal]
  intro y hy
  rcases hy with ⟨x, rfl⟩
  have hrow : ∀ l : Fin n, D j l = 0 := by
    intro l
    have hjl : j.1 ≠ l.1 := by
      intro hEq
      exact hnomatch ⟨l, hEq.symm⟩
    exact hdiag j l hjl
  have hcoord : (D.toEuclideanLin x) j = 0 := by
    rw [Matrix.toEuclideanLin_apply]
    simp [Matrix.mulVec, dotProduct, hrow]
  -- Once every range vector has zero `j`-th coordinate, it is orthogonal to `e_j`.
  simp [EuclideanSpace.inner_single_right, hcoord]

/-- Helper for Chapter01 Exercise 1.5: a unitary matrix acts isometrically on Euclidean
coordinates. -/
lemma toEuclideanLin_isometry_of_mem_unitaryGroup {n : Type} [Fintype n]
    (V : Matrix n n ℂ) (hV : V ∈ unitaryGroup n ℂ) :
    Isometry (Matrix.toEuclideanLin V) := by
  -- Transport the unitary identity `Vᴴ * V = 1` to the adjoint-composition identity.
  have hcomp : V.toEuclideanLin.adjoint ∘ₗ V.toEuclideanLin = 1 := by
    calc
      V.toEuclideanLin.adjoint ∘ₗ V.toEuclideanLin
          = (Vᴴ).toEuclideanLin ∘ₗ V.toEuclideanLin := by
              rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      _ = ((Vᴴ) * V).toEuclideanLin := by
            symm
            simpa [Matrix.toEuclideanLin] using
              (Matrix.toLpLin_mul_same (p := (2 : ENNReal)) (A := Vᴴ) (B := V))
      _ = (1 : Matrix n n ℂ).toEuclideanLin := by
            simpa using congrArg Matrix.toEuclideanLin
              (show Vᴴ * V = 1 from Matrix.mem_unitaryGroup_iff'.mp hV)
      _ = (1 : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) := by
            rw [show (1 : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) = LinearMap.id by rfl]
            simpa [Matrix.toEuclideanLin] using
              (Matrix.toLpLin_one (p := (2 : ENNReal)) (n := n) (R := ℂ))
  -- Once `adjoint ∘ V = 1`, the inner product is preserved.
  have hinner : ∀ x y, inner ℂ (V.toEuclideanLin x) (V.toEuclideanLin y) = inner ℂ x y := by
    intro x y
    calc
      inner ℂ (V.toEuclideanLin x) (V.toEuclideanLin y) =
          inner ℂ x ((V.toEuclideanLin.adjoint ∘ₗ V.toEuclideanLin) y) := by
            rw [← LinearMap.adjoint_inner_right, LinearMap.comp_apply]
      _ = inner ℂ x y := by
            simpa using congrArg (fun T => inner ℂ x (T y)) hcomp
  -- Convert inner-product preservation into norm preservation on the original linear map.
  refine AddMonoidHomClass.isometry_of_norm V.toEuclideanLin ?_
  intro x
  simpa [LinearMap.isometryOfInner] using
    (V.toEuclideanLin.isometryOfInner hinner).norm_map x

/-- Helper for Chapter01 Exercise 1.5: `kerComplementEquivRange.symm` is determined by an
explicit preimage once that preimage lies in the chosen kernel complement. -/
lemma LinearMap.kerComplementEquivRange_symm_eq_of_mem_orthogonal_of_apply
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E]
    (T : E →ₗ[ℂ] F) (hK : IsCompl T.kerᗮ T.ker) (y : T.range) (x : E)
    (hx : x ∈ T.kerᗮ) (hTx : T x = (y : F)) :
    ((kerComplementEquivRange T hK).symm y : T.kerᗮ) = ⟨x, hx⟩ := by
  -- Apply the forward equivalence: both sides map to the same range element `y`.
  apply (kerComplementEquivRange T hK).injective
  have hy :
      (kerComplementEquivRange T hK) ((kerComplementEquivRange T hK).symm y) = y :=
    (kerComplementEquivRange T hK).apply_symm_apply y
  have hx' : (kerComplementEquivRange T hK) ⟨x, hx⟩ = y := by
    -- The explicit candidate already has the prescribed image in the range.
    apply Subtype.ext
    simpa [LinearMap.kerComplementEquivRange_apply_coe] using hTx
  exact hy.trans hx'.symm

/-- Helper for Chapter01 Exercise 1.5: a nonzero diagonal entry sends the reciprocal basis vector
to the matching basis vector in the codomain. -/
lemma toEuclideanLin_single_inv_of_isRectangularDiagonal_nonzero {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D)
    {i : Fin n} {j : Fin m} (hij : i.1 = j.1) (hD : D j i ≠ 0) :
    D.toEuclideanLin (EuclideanSpace.single i ((D j i)⁻¹ : ℂ)) =
      EuclideanSpace.single j (1 : ℂ) := by
  -- The reciprocal basis vector isolates the single nonzero diagonal entry in row `j`.
  rw [Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single, Matrix.mulVec_single,
    ← EuclideanSpace.toLp_single j (1 : ℂ)]
  congr 1
  ext k
  by_cases hk : k = j
  · -- On the matching row the diagonal entry cancels with its reciprocal.
    subst hk
    simp [Pi.single_apply, hD]
  · by_cases hki : k.1 = i.1
    · -- Another row with the same index would force `k = j`, contradicting `hk`.
      exact (hk (Fin.ext (hki.trans hij))).elim
    · -- Off the matching row the rectangular-diagonal hypothesis kills the entry.
      simp [Pi.single_apply, hk, hdiag k i hki]

/-- Helper for Chapter01 Exercise 1.5: a reciprocal diagonal basis vector already lies in the
orthogonal complement of the kernel of `D.toEuclideanLin`. -/
lemma single_mem_ker_orthogonal_of_isRectangularDiagonal_nonzero {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D)
    {i : Fin n} {j : Fin m} (hij : i.1 = j.1) (hD : D j i ≠ 0) (c : ℂ) :
    EuclideanSpace.single i c ∈ (D.toEuclideanLin).kerᗮ := by
  -- It suffices to show every kernel vector has zero `i`th coordinate.
  rw [Submodule.mem_orthogonal']
  intro x hx
  have hx0 : D.toEuclideanLin x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hxj : (D.toEuclideanLin x) j = 0 := by
    simpa using congrArg (fun y => y j) hx0
  have hsum : ∑ l, D j l * x.ofLp l = D j i * x.ofLp i := by
    -- Row `j` only sees the matching column `i`.
    refine Finset.sum_eq_single i ?_ ?_
    · intro l _ hli
      have hjl : j.1 ≠ l.1 := by
        intro hEq
        apply hli
        exact Fin.ext (hEq.symm.trans hij.symm)
      simp [hdiag j l hjl]
    · intro hi
      simp at hi
  have hcoord : x i = 0 := by
    have hxj' : ∑ l, D j l * x.ofLp l = 0 := by
      simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct] using hxj
    rw [hsum] at hxj'
    exact (mul_eq_zero.mp hxj').resolve_left hD
  -- Once the `i`th coordinate is zero, the inner product with the basis vector vanishes.
  simp [EuclideanSpace.inner_single_left, hcoord]

/-- Helper for Chapter01 Exercise 1.5: the least-norm preimage of the projected basis vector is
either zero or the reciprocal matching basis vector. -/
lemma projected_single_preimage_of_isRectangularDiagonal {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D)
    {i : Fin n} {j : Fin m} (hij : i.1 = j.1) :
    ((((kerComplementEquivRange D.toEuclideanLin
        (D.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
        (D.toEuclideanLin.range.orthogonalProjectionOnto
          (EuclideanSpace.single j (1 : ℂ))) : (D.toEuclideanLin).kerᗮ) :
        EuclideanSpace ℂ (Fin n))) =
      if D j i = 0 then 0 else EuclideanSpace.single i ((D j i)⁻¹ : ℂ) := by
  by_cases hD : D j i = 0
  · have hproj :
        D.toEuclideanLin.range.orthogonalProjectionOnto (EuclideanSpace.single j (1 : ℂ)) = 0 :=
      orthogonalProjectionOnto_single_eq_zero_of_isRectangularDiagonal_zero D hdiag hij hD
    -- In the zero branch, the range projection vanishes, so the least-norm preimage is `0`.
    have hsymm :
        ((kerComplementEquivRange D.toEuclideanLin
            (D.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
            (0 : D.toEuclideanLin.range) : (D.toEuclideanLin).kerᗮ) = 0 := by
      simpa using
        (LinearMap.kerComplementEquivRange_symm_eq_of_mem_orthogonal_of_apply
          (T := D.toEuclideanLin) (hK := D.toEuclideanLin.ker.isCompl_orthogonal.symm)
          (y := (0 : D.toEuclideanLin.range)) (x := 0) (by simp) (by simp))
    simpa [hD, hproj] using congrArg Subtype.val hsymm
  · have hproj :
        D.toEuclideanLin.range.orthogonalProjectionOnto (EuclideanSpace.single j (1 : ℂ)) =
          ⟨EuclideanSpace.single j (1 : ℂ),
            single_mem_range_of_isRectangularDiagonal_nonzero D hdiag hij hD⟩ :=
      orthogonalProjectionOnto_single_of_isRectangularDiagonal_nonzero D hdiag hij hD
    have hx :
        EuclideanSpace.single i ((D j i)⁻¹ : ℂ) ∈ (D.toEuclideanLin).kerᗮ :=
      single_mem_ker_orthogonal_of_isRectangularDiagonal_nonzero D hdiag hij hD _
    have himage :
        D.toEuclideanLin (EuclideanSpace.single i ((D j i)⁻¹ : ℂ)) =
          EuclideanSpace.single j (1 : ℂ) :=
      toEuclideanLin_single_inv_of_isRectangularDiagonal_nonzero D hdiag hij hD
    -- In the nonzero branch, the explicit reciprocal basis vector has the right image and norm.
    have hsymm :
        ((kerComplementEquivRange D.toEuclideanLin
            (D.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
            ⟨EuclideanSpace.single j (1 : ℂ),
              single_mem_range_of_isRectangularDiagonal_nonzero D hdiag hij hD⟩ :
            (D.toEuclideanLin).kerᗮ) =
          ⟨EuclideanSpace.single i ((D j i)⁻¹ : ℂ), hx⟩ := by
      exact LinearMap.kerComplementEquivRange_symm_eq_of_mem_orthogonal_of_apply
        (T := D.toEuclideanLin) (hK := D.toEuclideanLin.ker.isCompl_orthogonal.symm)
        (y := ⟨EuclideanSpace.single j (1 : ℂ),
          single_mem_range_of_isRectangularDiagonal_nonzero D hdiag hij hD⟩)
        (x := EuclideanSpace.single i ((D j i)⁻¹ : ℂ)) hx himage
    simpa [hD, hproj] using congrArg Subtype.val hsymm

/-- Helper for Chapter01 Exercise 1.5: unfolding the owner definition identifies a pseudoinverse
entry with the corresponding coordinate of the canonical least-norm preimage. -/
lemma pseudoinverse_entry_eq_projected_single_preimage_coord {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (i : Fin n) (j : Fin m) :
    D⁺ i j =
      ((((kerComplementEquivRange D.toEuclideanLin
          (D.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
          (D.toEuclideanLin.range.orthogonalProjectionOnto
            (EuclideanSpace.single j (1 : ℂ))) : (D.toEuclideanLin).kerᗮ) :
          EuclideanSpace ℂ (Fin n)) i) := by
  -- Unfold the owner once, then normalize the basis vector across the definitional `DecidableEq`.
  classical
  simp only [Matrix.pseudoinverse]
  rw [single_eq_of_decidableEq
    (d₁ := Classical.decEq (Fin m))
    (d₂ := instDecidableEqFin m) j (1 : ℂ)]
  rfl

/-- Helper for Chapter01 Exercise 1.5: reading the `i`th coordinate of the canonical least-norm
preimage reproduces the reciprocal diagonal formula from `(1.2.54)`. -/
lemma projected_single_preimage_coord_of_isRectangularDiagonal {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D)
    (i : Fin n) (j : Fin m) :
    ((((kerComplementEquivRange D.toEuclideanLin
        (D.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
        (D.toEuclideanLin.range.orthogonalProjectionOnto
          (EuclideanSpace.single j (1 : ℂ))) : (D.toEuclideanLin).kerᗮ) :
        EuclideanSpace ℂ (Fin n)) i) =
      if h : i.1 = j.1 then if D j i = 0 then 0 else (D j i)⁻¹ else 0 := by
  by_cases hij : i.1 = j.1
  · -- On the matching diagonal, read off the coordinate from the whole-vector preimage formula.
    have hcoord :
        ((((kerComplementEquivRange D.toEuclideanLin
            (D.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
            (D.toEuclideanLin.range.orthogonalProjectionOnto
              (EuclideanSpace.single j (1 : ℂ))) : (D.toEuclideanLin).kerᗮ) :
            EuclideanSpace ℂ (Fin n)) i) =
          (if D j i = 0 then 0 else EuclideanSpace.single i ((D j i)⁻¹ : ℂ)) i := by
      exact congrArg (fun x : EuclideanSpace ℂ (Fin n) => x i)
        (projected_single_preimage_of_isRectangularDiagonal D hdiag hij)
    have hvalue :
        (if D j i = 0 then 0 else EuclideanSpace.single i ((D j i)⁻¹ : ℂ)) i =
          if D j i = 0 then 0 else (D j i)⁻¹ := by
      by_cases hD : D j i = 0
      · simp [hD]
      · simp [hD]
    calc
      ((((kerComplementEquivRange D.toEuclideanLin
          (D.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
          (D.toEuclideanLin.range.orthogonalProjectionOnto
            (EuclideanSpace.single j (1 : ℂ))) : (D.toEuclideanLin).kerᗮ) :
          EuclideanSpace ℂ (Fin n)) i) =
          (if D j i = 0 then 0 else EuclideanSpace.single i ((D j i)⁻¹ : ℂ)) i :=
        hcoord
      _ = if D j i = 0 then 0 else (D j i)⁻¹ := hvalue
      _ = if h : i.1 = j.1 then if D j i = 0 then 0 else (D j i)⁻¹ else 0 := by
        simp [hij]
  · by_cases hmatch : ∃ i0 : Fin n, i0.1 = j.1
    · rcases hmatch with ⟨i0, hi0j⟩
      have hi_ne : i ≠ i0 := by
        intro hii0
        apply hij
        simpa [hii0] using hi0j
      -- A matching column exists, but it is different from `i`, so the `i`th coordinate vanishes.
      have hcoord :
          ((((kerComplementEquivRange D.toEuclideanLin
              (D.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
              (D.toEuclideanLin.range.orthogonalProjectionOnto
                (EuclideanSpace.single j (1 : ℂ))) : (D.toEuclideanLin).kerᗮ) :
              EuclideanSpace ℂ (Fin n)) i) =
            (if D j i0 = 0 then 0 else EuclideanSpace.single i0 ((D j i0)⁻¹ : ℂ)) i := by
        exact congrArg (fun x : EuclideanSpace ℂ (Fin n) => x i)
          (projected_single_preimage_of_isRectangularDiagonal D hdiag hi0j)
      have hvalue :
          (if D j i0 = 0 then 0 else EuclideanSpace.single i0 ((D j i0)⁻¹ : ℂ)) i = 0 := by
        by_cases hD : D j i0 = 0
        · simp [hD]
        · simp [hD, hi_ne]
      calc
        ((((kerComplementEquivRange D.toEuclideanLin
            (D.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
            (D.toEuclideanLin.range.orthogonalProjectionOnto
              (EuclideanSpace.single j (1 : ℂ))) : (D.toEuclideanLin).kerᗮ) :
            EuclideanSpace ℂ (Fin n)) i) =
            (if D j i0 = 0 then 0 else EuclideanSpace.single i0 ((D j i0)⁻¹ : ℂ)) i :=
          hcoord
        _ = 0 := hvalue
        _ = if h : i.1 = j.1 then if D j i = 0 then 0 else (D j i)⁻¹ else 0 := by
          simp [hij]
    · -- If no matching column exists at all, both the range projection and its least-norm preimage
      -- are zero, so every coordinate vanishes.
      have hproj :
          D.toEuclideanLin.range.orthogonalProjectionOnto
              (EuclideanSpace.single j (1 : ℂ)) = 0 :=
        orthogonalProjectionOnto_single_eq_zero_of_isRectangularDiagonal_no_matching_column
          D hdiag hmatch
      have hpreimage :
          ((((kerComplementEquivRange D.toEuclideanLin
              (D.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
              (D.toEuclideanLin.range.orthogonalProjectionOnto
                (EuclideanSpace.single j (1 : ℂ))) : (D.toEuclideanLin).kerᗮ) :
              EuclideanSpace ℂ (Fin n))) = 0 := by
        -- Rewrite the projected target to `0`, then use uniqueness of the kernel-complement preimage.
        rw [hproj]
        simpa using congrArg Subtype.val
          (LinearMap.kerComplementEquivRange_symm_eq_of_mem_orthogonal_of_apply
            (T := D.toEuclideanLin) (hK := D.toEuclideanLin.ker.isCompl_orthogonal.symm)
            (y := (0 : D.toEuclideanLin.range)) (x := 0) (by simp) (by simp))
      simpa [hij] using congrArg (fun x : EuclideanSpace ℂ (Fin n) => x i) hpreimage

/-- For a rectangular diagonal matrix `D`, the canonical `D⁺` is given by the source formula
`(1.2.54)`: transpose `D` and replace each nonzero diagonal entry by its reciprocal. -/
theorem pseudoinverse_apply_of_isRectangularDiagonal {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (hdiag : IsRectangularDiagonal D) (i : Fin n) (j : Fin m) :
    D⁺ i j = if h : i.1 = j.1 then if D j i = 0 then 0 else (D j i)⁻¹ else 0 := by
  -- Route correction: compute the whole least-norm preimage vector first, then read its `i`th
  -- coordinate. This matches the source diagonal-owner route and avoids further subtype algebra.
  calc
    D⁺ i j =
        ((((kerComplementEquivRange D.toEuclideanLin
            (D.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
            (D.toEuclideanLin.range.orthogonalProjectionOnto
              (EuclideanSpace.single j (1 : ℂ))) : (D.toEuclideanLin).kerᗮ) :
            EuclideanSpace ℂ (Fin n)) i) :=
      pseudoinverse_entry_eq_projected_single_preimage_coord D i j
    _ = if h : i.1 = j.1 then if D j i = 0 then 0 else (D j i)⁻¹ else 0 :=
      projected_single_preimage_coord_of_isRectangularDiagonal D hdiag i j

/-- Helper for Chapter01 Exercise 1.5: the matrix-valued owner `A⁺` realizes the canonical
least-norm preimage map on arbitrary Euclidean vectors, not just on standard basis vectors. -/
lemma pseudoinverseMulVec_eq_projected_preimage {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (b : EuclideanSpace ℂ (Fin m)) :
    pseudoinverseMulVec A b =
      ((((kerComplementEquivRange A.toEuclideanLin
          (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
          (A.toEuclideanLin.range.orthogonalProjectionOnto b) :
          (A.toEuclideanLin).kerᗮ) : EuclideanSpace ℂ (Fin n))) := by
  let F : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (A⁺).toEuclideanLin
  let G : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((A.toEuclideanLin).kerᗮ).subtype ∘ₗ
      ((kerComplementEquivRange A.toEuclideanLin
        (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm.toLinearMap ∘ₗ
        A.toEuclideanLin.range.orthogonalProjectionOnto.toLinearMap)
  have hsingle :
      ∀ j : Fin m, F (EuclideanSpace.single j (1 : ℂ)) = G (EuclideanSpace.single j (1 : ℂ)) := by
    intro j
    ext i
    -- Compare both linear maps on the standard basis vectors, where the owner was defined.
    calc
      F (EuclideanSpace.single j (1 : ℂ)) i = A⁺ i j := by
        simp [F, Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single, Matrix.mulVec_single,
          PiLp.toLp_apply]
      _ =
          ((((kerComplementEquivRange A.toEuclideanLin
              (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
              (A.toEuclideanLin.range.orthogonalProjectionOnto
                (EuclideanSpace.single j (1 : ℂ))) : (A.toEuclideanLin).kerᗮ) :
              EuclideanSpace ℂ (Fin n)) i) :=
        pseudoinverse_entry_eq_projected_single_preimage_coord A i j
      _ = G (EuclideanSpace.single j (1 : ℂ)) i := by
        simp [G]
  have hsum :
      ∀ x : EuclideanSpace ℂ (Fin m),
        x = ∑ j : Fin m, x j • EuclideanSpace.single j (1 : ℂ) := by
    intro x
    ext k
    symm
    simpa [Pi.single_apply] using congrArg (fun v : Fin m → ℂ => v k)
      (Pi.sum_single_apply (v := fun j : Fin m => x.ofLp j))
  -- Since both sides are linear and agree on the standard basis, they agree everywhere.
  calc
    pseudoinverseMulVec A b = F b := rfl
    _ = G b := by
      rw [hsum b]
      simp [F, G, hsingle, map_sum]
    _ =
        ((((kerComplementEquivRange A.toEuclideanLin
            (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
            (A.toEuclideanLin.range.orthogonalProjectionOnto b) :
            (A.toEuclideanLin).kerᗮ) : EuclideanSpace ℂ (Fin n))) := by
      simp [G]

/-- Helper for Chapter01 Exercise 1.5: the canonical pseudoinverse image lies in the orthogonal
complement of the kernel. -/
lemma pseudoinverseMulVec_mem_orthogonal_kernel {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (b : EuclideanSpace ℂ (Fin m)) :
    pseudoinverseMulVec A b ∈ (A.toEuclideanLin).kerᗮ := by
  -- Rewrite the owner to the chosen kernel-complement element.
  rw [pseudoinverseMulVec_eq_projected_preimage]
  exact ((kerComplementEquivRange A.toEuclideanLin
    (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
    (A.toEuclideanLin.range.orthogonalProjectionOnto b)).property

/-- Helper for Chapter01 Exercise 1.5: applying `A` to the canonical pseudoinverse image returns
the orthogonal projection onto the range of `A.toEuclideanLin`. -/
lemma toEuclideanLin_pseudoinverseMulVec_eq_range_projection {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (b : EuclideanSpace ℂ (Fin m)) :
    A.toEuclideanLin (pseudoinverseMulVec A b) =
      A.toEuclideanLin.range.orthogonalProjectionOnto b := by
  -- Rewrite to the explicit kernel-complement preimage and apply the forward equivalence.
  rw [pseudoinverseMulVec_eq_projected_preimage]
  exact congrArg Subtype.val
    ((kerComplementEquivRange A.toEuclideanLin
      (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).apply_symm_apply
      (A.toEuclideanLin.range.orthogonalProjectionOnto b))

/-- Helper for Chapter01 Exercise 1.5: a unitary matrix followed by its conjugate transpose acts
as the identity on Euclidean coordinates. -/
lemma toEuclideanLin_mul_conjTranspose_apply_of_mem_unitaryGroup {n : Type} [Fintype n]
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (x : EuclideanSpace ℂ n) :
    U.toEuclideanLin ((Uᴴ).toEuclideanLin x) = x := by
  have hcomp : U.toEuclideanLin ∘ₗ (Uᴴ).toEuclideanLin = 1 := by
    calc
      U.toEuclideanLin ∘ₗ (Uᴴ).toEuclideanLin = (U * Uᴴ).toEuclideanLin := by
        symm
        simpa [Matrix.toEuclideanLin] using
          (Matrix.toLpLin_mul_same (p := (2 : ENNReal)) (A := U) (B := Uᴴ))
      _ = (1 : Matrix n n ℂ).toEuclideanLin := by
        have hUUh : U * Uᴴ = 1 := by
          simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hU)
        simpa using congrArg Matrix.toEuclideanLin hUUh
      _ = (1 : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) := by
        rw [show (1 : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) = LinearMap.id by rfl]
        simpa [Matrix.toEuclideanLin] using
          (Matrix.toLpLin_one (p := (2 : ENNReal)) (n := n) (R := ℂ))
  -- Evaluate the linear-map identity at the chosen vector.
  simpa [LinearMap.comp_apply] using congrArg (fun T => T x) hcomp

/-- Helper for Chapter01 Exercise 1.5: the conjugate transpose of a unitary matrix followed by
the matrix itself acts as the identity on Euclidean coordinates. -/
lemma conjTranspose_toEuclideanLin_apply_of_mem_unitaryGroup {n : Type} [Fintype n]
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (x : EuclideanSpace ℂ n) :
    (Uᴴ).toEuclideanLin (U.toEuclideanLin x) = x := by
  have hcomp : (Uᴴ).toEuclideanLin ∘ₗ U.toEuclideanLin = 1 := by
    calc
      (Uᴴ).toEuclideanLin ∘ₗ U.toEuclideanLin = (Uᴴ * U).toEuclideanLin := by
        symm
        simpa [Matrix.toEuclideanLin] using
          (Matrix.toLpLin_mul_same (p := (2 : ENNReal)) (A := Uᴴ) (B := U))
      _ = (1 : Matrix n n ℂ).toEuclideanLin := by
        have hUhU : Uᴴ * U = 1 := by
          simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hU)
        simpa using congrArg Matrix.toEuclideanLin hUhU
      _ = (1 : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) := by
        rw [show (1 : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) = LinearMap.id by rfl]
        simpa [Matrix.toEuclideanLin] using
          (Matrix.toLpLin_one (p := (2 : ENNReal)) (n := n) (R := ℂ))
  -- Evaluate the linear-map identity at the chosen vector.
  simpa [LinearMap.comp_apply] using congrArg (fun T => T x) hcomp

/-- Helper for Chapter01 Exercise 1.5: left multiplication by a unitary factor pulls the target
vector back by the conjugate transpose before taking the canonical least-norm preimage. -/
lemma pseudoinverseMulVec_mul_unitary_left {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) ℂ) (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U ∈ unitaryGroup (Fin m) ℂ) (b : EuclideanSpace ℂ (Fin m)) :
    pseudoinverseMulVec (U * B) b =
      pseudoinverseMulVec B ((Uᴴ).toEuclideanLin b) := by
  let p : B.toEuclideanLin.range := B.toEuclideanLin.range.orthogonalProjectionOnto
    ((Uᴴ).toEuclideanLin b)
  have hUB :
      (U * B).toEuclideanLin = U.toEuclideanLin ∘ₗ B.toEuclideanLin := by
    -- Rewrite left multiplication as composition on Euclidean coordinate maps.
    symm
    simpa [Matrix.toEuclideanLin] using
      (Matrix.toLpLin_mul_same (p := (2 : ENNReal)) (A := U) (B := B))
  have hUleft :
      (Uᴴ).toEuclideanLin ∘ₗ U.toEuclideanLin =
        (1 : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) := by
    -- Transport the unitary identity `Uᴴ * U = 1` to Euclidean coordinates.
    calc
      (Uᴴ).toEuclideanLin ∘ₗ U.toEuclideanLin = (Uᴴ * U).toEuclideanLin := by
        symm
        simpa [Matrix.toEuclideanLin] using
          (Matrix.toLpLin_mul_same (p := (2 : ENNReal)) (A := Uᴴ) (B := U))
      _ = (1 : Matrix (Fin m) (Fin m) ℂ).toEuclideanLin := by
        simpa [Matrix.star_eq_conjTranspose] using
          congrArg Matrix.toEuclideanLin (Matrix.mem_unitaryGroup_iff'.mp hU)
      _ = (1 : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) := by
        rw [show (1 : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) = LinearMap.id by rfl]
        simpa [Matrix.toEuclideanLin] using
          (Matrix.toLpLin_one (p := (2 : ENNReal)) (n := Fin m) (R := ℂ))
  have hUleft_apply (x : EuclideanSpace ℂ (Fin m)) :
      (Uᴴ).toEuclideanLin (U.toEuclideanLin x) = x := by
    -- Evaluate the transported unitary identity at the chosen vector.
    simpa [LinearMap.comp_apply] using congrArg (fun T => T x) hUleft
  have hx :
      pseudoinverseMulVec B ((Uᴴ).toEuclideanLin b) ∈ ((U * B).toEuclideanLin).kerᗮ := by
    -- The least-norm preimage for `B` is still orthogonal to the transported kernel.
    rw [Submodule.mem_orthogonal']
    intro z hz
    have hz0 : (U * B).toEuclideanLin z = 0 := by
      simpa [LinearMap.mem_ker] using hz
    have hzB0 : B.toEuclideanLin z = 0 := by
      have hUz0 : (Uᴴ).toEuclideanLin ((U * B).toEuclideanLin z) = 0 := by
        simpa using congrArg ((Uᴴ).toEuclideanLin) hz0
      simpa [hUB, LinearMap.comp_apply, hUleft_apply] using hUz0
    have hzB : z ∈ B.toEuclideanLin.ker := by
      simpa [LinearMap.mem_ker] using hzB0
    exact (Submodule.mem_orthogonal' _ _).1
      (pseudoinverseMulVec_mem_orthogonal_kernel B ((Uᴴ).toEuclideanLin b)) z hzB
  have hy_mem : U.toEuclideanLin p ∈ ((U * B).toEuclideanLin).range := by
    -- The transported projected image is visibly in the range of `U * B`.
    refine ⟨pseudoinverseMulVec B ((Uᴴ).toEuclideanLin b), ?_⟩
    calc
      (U * B).toEuclideanLin (pseudoinverseMulVec B ((Uᴴ).toEuclideanLin b)) =
          U.toEuclideanLin
            (B.toEuclideanLin (pseudoinverseMulVec B ((Uᴴ).toEuclideanLin b))) := by
        simp [hUB, LinearMap.comp_apply]
      _ = U.toEuclideanLin p := by
        rw [toEuclideanLin_pseudoinverseMulVec_eq_range_projection]
  have horth : b - U.toEuclideanLin p ∈ ((U * B).toEuclideanLin).rangeᗮ := by
    -- The residual is orthogonal after pulling it back through the unitary action.
    rw [Submodule.mem_orthogonal']
    intro z hz
    rcases hz with ⟨w, rfl⟩
    have hbase :
        inner ℂ (((Uᴴ).toEuclideanLin b) - p) (B.toEuclideanLin w) = 0 := by
      exact (Submodule.mem_orthogonal' _ _).1
        (Submodule.sub_starProjection_mem_orthogonal
          (K := B.toEuclideanLin.range) ((Uᴴ).toEuclideanLin b))
        (B.toEuclideanLin w) ⟨w, rfl⟩
    calc
      inner ℂ (b - U.toEuclideanLin p) ((U * B).toEuclideanLin w) =
          inner ℂ (b - U.toEuclideanLin p) (U.toEuclideanLin (B.toEuclideanLin w)) := by
        simp [hUB, LinearMap.comp_apply]
      _ = inner ℂ ((Uᴴ).toEuclideanLin (b - U.toEuclideanLin p)) (B.toEuclideanLin w) := by
        rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
        exact (LinearMap.adjoint_inner_left (A := U.toEuclideanLin)
            (x := B.toEuclideanLin w) (y := b - U.toEuclideanLin p)).symm
      _ = inner ℂ (((Uᴴ).toEuclideanLin b) - p) (B.toEuclideanLin w) := by
        simp [LinearMap.map_sub, hUleft_apply]
      _ = 0 := hbase
  have hproj :
      ((U * B).toEuclideanLin).range.orthogonalProjectionOnto b = ⟨U.toEuclideanLin p, hy_mem⟩ := by
    -- The transported image is exactly the orthogonal projection onto the new range.
    apply Subtype.ext
    exact Submodule.eq_starProjection_of_mem_orthogonal hy_mem horth
  have hsymm :
      ((kerComplementEquivRange (U * B).toEuclideanLin
          (((U * B).toEuclideanLin).ker.isCompl_orthogonal.symm)).symm
          (((U * B).toEuclideanLin).range.orthogonalProjectionOnto b) :
          ((U * B).toEuclideanLin).kerᗮ) =
        ⟨pseudoinverseMulVec B ((Uᴴ).toEuclideanLin b), hx⟩ := by
    -- Uniqueness in the kernel complement identifies the transported candidate.
    refine LinearMap.kerComplementEquivRange_symm_eq_of_mem_orthogonal_of_apply
      (T := (U * B).toEuclideanLin)
      (hK := ((U * B).toEuclideanLin).ker.isCompl_orthogonal.symm)
      (y := ((U * B).toEuclideanLin).range.orthogonalProjectionOnto b)
      (x := pseudoinverseMulVec B ((Uᴴ).toEuclideanLin b))
      hx ?_
    calc
      (U * B).toEuclideanLin (pseudoinverseMulVec B ((Uᴴ).toEuclideanLin b)) = U.toEuclideanLin p := by
        rw [hUB, LinearMap.comp_apply, toEuclideanLin_pseudoinverseMulVec_eq_range_projection]
      _ = (((U * B).toEuclideanLin).range.orthogonalProjectionOnto b : EuclideanSpace ℂ (Fin m)) := by
        symm
        exact congrArg Subtype.val hproj
  -- Rewrite the owner definition to the chosen kernel-complement preimage.
  rw [pseudoinverseMulVec_eq_projected_preimage]
  simpa using congrArg Subtype.val hsymm

/-- Helper for Chapter01 Exercise 1.5: right multiplication by a unitary factor transports the
canonical least-norm preimage through the corresponding Euclidean action. -/
lemma pseudoinverseMulVec_mul_unitary_right {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : V ∈ unitaryGroup (Fin n) ℂ) (b : EuclideanSpace ℂ (Fin m)) :
    pseudoinverseMulVec (B * Vᴴ) b =
      V.toEuclideanLin (pseudoinverseMulVec B b) := by
  let x0 := pseudoinverseMulVec B b
  have hBV :
      (B * Vᴴ).toEuclideanLin = B.toEuclideanLin ∘ₗ (Vᴴ).toEuclideanLin := by
    -- Rewrite right multiplication as composition on Euclidean coordinate maps.
    symm
    simpa [Matrix.toEuclideanLin] using
      (Matrix.toLpLin_mul_same (p := (2 : ENNReal)) (A := B) (B := Vᴴ))
  have hVleft :
      (Vᴴ).toEuclideanLin ∘ₗ V.toEuclideanLin =
        (1 : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
    -- Transport the unitary identity `Vᴴ * V = 1` to Euclidean coordinates.
    calc
      (Vᴴ).toEuclideanLin ∘ₗ V.toEuclideanLin = (Vᴴ * V).toEuclideanLin := by
        symm
        simpa [Matrix.toEuclideanLin] using
          (Matrix.toLpLin_mul_same (p := (2 : ENNReal)) (A := Vᴴ) (B := V))
      _ = (1 : Matrix (Fin n) (Fin n) ℂ).toEuclideanLin := by
        simpa [Matrix.star_eq_conjTranspose] using
          congrArg Matrix.toEuclideanLin (Matrix.mem_unitaryGroup_iff'.mp hV)
      _ = (1 : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
        rw [show (1 : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = LinearMap.id by rfl]
        simpa [Matrix.toEuclideanLin] using
          (Matrix.toLpLin_one (p := (2 : ENNReal)) (n := Fin n) (R := ℂ))
  have hVleft_apply (x : EuclideanSpace ℂ (Fin n)) :
      (Vᴴ).toEuclideanLin (V.toEuclideanLin x) = x := by
    -- Evaluate the transported unitary identity at the chosen vector.
    simpa [LinearMap.comp_apply] using congrArg (fun T => T x) hVleft
  have hx : V.toEuclideanLin x0 ∈ ((B * Vᴴ).toEuclideanLin).kerᗮ := by
    -- Rotating a least-norm preimage by `V` preserves orthogonality to the transported kernel.
    rw [Submodule.mem_orthogonal']
    intro z hz
    have hz0 : (B * Vᴴ).toEuclideanLin z = 0 := by
      simpa [LinearMap.mem_ker] using hz
    have hzB0 : B.toEuclideanLin ((Vᴴ).toEuclideanLin z) = 0 := by
      simpa [hBV, LinearMap.comp_apply] using hz0
    have hzB : (Vᴴ).toEuclideanLin z ∈ B.toEuclideanLin.ker := by
      simpa [LinearMap.mem_ker] using hzB0
    calc
      inner ℂ (V.toEuclideanLin x0) z = inner ℂ x0 ((Vᴴ).toEuclideanLin z) := by
        simpa [Matrix.toEuclideanLin_conjTranspose_eq_adjoint] using
          (LinearMap.adjoint_inner_right (A := V.toEuclideanLin)
            (x := x0) (y := z)).symm
      _ = 0 := by
        exact (Submodule.mem_orthogonal' _ _).1
          (pseudoinverseMulVec_mem_orthogonal_kernel B b) ((Vᴴ).toEuclideanLin z) hzB
  have hy_mem : B.toEuclideanLin x0 ∈ ((B * Vᴴ).toEuclideanLin).range := by
    -- The projected image for `B` is still in the range after inserting `Vᴴ`.
    refine ⟨V.toEuclideanLin x0, ?_⟩
    calc
      (B * Vᴴ).toEuclideanLin (V.toEuclideanLin x0) =
          B.toEuclideanLin ((Vᴴ).toEuclideanLin (V.toEuclideanLin x0)) := by
        simp [hBV, LinearMap.comp_apply]
      _ = B.toEuclideanLin x0 := by
        rw [hVleft_apply]
  have horth : b - B.toEuclideanLin x0 ∈ ((B * Vᴴ).toEuclideanLin).rangeᗮ := by
    -- Every vector in the new range already lies in the old range, so the same residual is orthogonal.
    rw [Submodule.mem_orthogonal']
    intro z hz
    rcases hz with ⟨w, rfl⟩
    have hzB : (B * Vᴴ).toEuclideanLin w ∈ B.toEuclideanLin.range := by
      refine ⟨(Vᴴ).toEuclideanLin w, ?_⟩
      simp [hBV, LinearMap.comp_apply]
    calc
      inner ℂ (b - B.toEuclideanLin x0) ((B * Vᴴ).toEuclideanLin w) =
          inner ℂ (b - B.toEuclideanLin.range.orthogonalProjectionOnto b)
            ((B * Vᴴ).toEuclideanLin w) := by
        rw [toEuclideanLin_pseudoinverseMulVec_eq_range_projection]
      _ = 0 := by
        exact (Submodule.mem_orthogonal' _ _).1
          (Submodule.sub_starProjection_mem_orthogonal (K := B.toEuclideanLin.range) b)
          ((B * Vᴴ).toEuclideanLin w) hzB
  have hproj :
      ((B * Vᴴ).toEuclideanLin).range.orthogonalProjectionOnto b = ⟨B.toEuclideanLin x0, hy_mem⟩ := by
    -- The image of the rotated least-norm preimage is the orthogonal projection onto the new range.
    apply Subtype.ext
    exact Submodule.eq_starProjection_of_mem_orthogonal hy_mem horth
  have hsymm :
      ((kerComplementEquivRange (B * Vᴴ).toEuclideanLin
          (((B * Vᴴ).toEuclideanLin).ker.isCompl_orthogonal.symm)).symm
          (((B * Vᴴ).toEuclideanLin).range.orthogonalProjectionOnto b) :
          ((B * Vᴴ).toEuclideanLin).kerᗮ) =
        ⟨V.toEuclideanLin x0, hx⟩ := by
    -- Uniqueness in the kernel complement identifies the rotated candidate.
    refine LinearMap.kerComplementEquivRange_symm_eq_of_mem_orthogonal_of_apply
      (T := (B * Vᴴ).toEuclideanLin)
      (hK := ((B * Vᴴ).toEuclideanLin).ker.isCompl_orthogonal.symm)
      (y := ((B * Vᴴ).toEuclideanLin).range.orthogonalProjectionOnto b)
      (x := V.toEuclideanLin x0)
      hx ?_
    calc
      (B * Vᴴ).toEuclideanLin (V.toEuclideanLin x0) = B.toEuclideanLin x0 := by
        rw [hBV, LinearMap.comp_apply, hVleft_apply]
      _ = (((B * Vᴴ).toEuclideanLin).range.orthogonalProjectionOnto b : EuclideanSpace ℂ (Fin m)) := by
        symm
        exact congrArg Subtype.val hproj
  -- Rewrite the owner definition to the chosen rotated preimage.
  rw [pseudoinverseMulVec_eq_projected_preimage]
  simpa [x0] using congrArg Subtype.val hsymm

/-- Chapter01 Exercise 1.5: if `A = U * D * Vᴴ` is a singular value decomposition, then
`A⁺ = V * D⁺ * Uᴴ`. For rectangular diagonal `D`, the preceding theorem identifies `D⁺`
with the source formula `(1.2.54)`. -/
theorem pseudoinverse_eq_mul_pseudoinverse_of_singularValueDecomposition {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (U : Matrix (Fin m) (Fin m) ℂ)
    (D : Matrix (Fin m) (Fin n) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hSVD : IsSingularValueDecomposition A U D V) :
    A⁺ = V * D⁺ * Uᴴ := by
  rcases hSVD with ⟨hA, hU, hV, -, -⟩
  have hA' : A = (U * D) * Vᴴ := by
    -- Reassociate the SVD factorization into the exact shape used by the transport lemmas.
    simpa [Matrix.mul_assoc] using hA
  ext i j
  let e : EuclideanSpace ℂ (Fin m) := EuclideanSpace.single j (1 : ℂ)
  have hvec :
      pseudoinverseMulVec A e = ((V * D⁺ * Uᴴ).toEuclideanLin) e := by
    -- Transport the canonical least-norm preimage through the two unitary factors.
    calc
      pseudoinverseMulVec A e = pseudoinverseMulVec ((U * D) * Vᴴ) e := by
        simpa [hA']
      _ = V.toEuclideanLin (pseudoinverseMulVec (U * D) e) := by
        simpa using pseudoinverseMulVec_mul_unitary_right (B := U * D) (V := V) hV e
      _ = V.toEuclideanLin (pseudoinverseMulVec D ((Uᴴ).toEuclideanLin e)) := by
        rw [pseudoinverseMulVec_mul_unitary_left (B := D) (U := U) hU e]
      _ = V.toEuclideanLin ((D⁺).toEuclideanLin ((Uᴴ).toEuclideanLin e)) := by
        rfl
      _ = ((V * D⁺ * Uᴴ).toEuclideanLin) e := by
        have hDU :
            (D⁺ * Uᴴ).toEuclideanLin = D⁺.toEuclideanLin ∘ₗ (Uᴴ).toEuclideanLin := by
          -- Convert the inner matrix product into composition.
          symm
          simpa [Matrix.toEuclideanLin] using
            (Matrix.toLpLin_mul_same (p := (2 : ENNReal)) (A := D⁺) (B := Uᴴ))
        have hVDU :
            (V * (D⁺ * Uᴴ)).toEuclideanLin = V.toEuclideanLin ∘ₗ (D⁺ * Uᴴ).toEuclideanLin := by
          -- Convert the outer matrix product into composition.
          symm
          simpa [Matrix.toEuclideanLin] using
            (Matrix.toLpLin_mul_same (p := (2 : ENNReal)) (A := V) (B := D⁺ * Uᴴ))
        simpa [Matrix.mul_assoc, hDU, hVDU, LinearMap.comp_apply]
  -- Compare the two matrices on the standard basis vector `e_j` and read the `i`th coordinate.
  calc
    A⁺ i j = (pseudoinverseMulVec A e) i := by
      simpa [e, pseudoinverseMulVec_eq_toEuclideanLin_pseudoinverse, Matrix.toEuclideanLin_apply,
        EuclideanSpace.ofLp_single, Matrix.mulVec_single]
    _ = (((V * D⁺ * Uᴴ).toEuclideanLin) e) i := by
      simpa using congrArg (fun x : EuclideanSpace ℂ (Fin n) => x i) hvec
    _ = (V * D⁺ * Uᴴ) i j := by
      simp [e, Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single, Matrix.mulVec, dotProduct]
      rw [Matrix.mul_apply]
      simp [Matrix.conjTranspose]

end Matrix
