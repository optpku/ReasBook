/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Exercise_1_5

noncomputable section

namespace Matrix

open LinearMap

variable {m n : Type} [Fintype m] [Fintype n]

local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- The residual norm `x ↦ ‖A x - b‖` for the linear least-squares problem `A x = b`. -/
def leastSquaresResidual (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    ℝ :=
  ‖Matrix.toEuclideanLin A x - b‖

/-- A least-squares solution of `Matrix.toEuclideanLin A x = b` is a global minimizer of the
residual norm. -/
abbrev IsLeastSquaresSolution (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    (x : EuclideanSpace ℂ n) : Prop :=
  IsMinOn (leastSquaresResidual A b) Set.univ x

/-- The set of all least-squares solutions of `Matrix.toEuclideanLin A x = b`. -/
def leastSquaresSolutionSet (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    Set (EuclideanSpace ℂ n) :=
  {x | IsLeastSquaresSolution A b x}

/-- A minimal least-squares solution is a least-squares solution of minimal Euclidean norm among
all least-squares solutions. -/
abbrev IsMinimalLeastSquaresSolution (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    (x : EuclideanSpace ℂ n) : Prop :=
  IsLeastSquaresSolution A b x ∧
    IsMinOn (fun z : EuclideanSpace ℂ n ↦ ‖z‖) (leastSquaresSolutionSet A b) x

/-- Helper for Chapter01 Theorem 1.2.7: `EuclideanSpace.single` does not depend on the chosen
`DecidableEq` instance on the index type. -/
private lemma euclideanSingle_eq_of_decidableEq
    {ι : Type} (d₁ d₂ : DecidableEq ι) (j : ι) (c : ℂ) :
    @EuclideanSpace.single ι ℂ _ d₁ j c = @EuclideanSpace.single ι ℂ _ d₂ j c := by
  -- Compare both point-mass vectors coordinatewise.
  ext k
  by_cases hk : k = j
  · subst hk
    simp
  · simp [hk]

/-- Helper for Chapter01 Theorem 1.2.7: unfolding `A⁺` identifies each pseudoinverse entry with
the corresponding coordinate of the canonical least-norm preimage of a basis vector. -/
private lemma pseudoinverseEntry_eq_projectedSinglePreimageCoord
    (A : Matrix m n ℂ) (i : n) (j : m) :
    A⁺ i j =
      ((((LinearMap.kerComplementEquivRange (Matrix.toEuclideanLin A)
          ((Matrix.toEuclideanLin A).ker.isCompl_orthogonal.symm)).symm
          ((Matrix.toEuclideanLin A).range.orthogonalProjectionOnto
            (EuclideanSpace.single j (1 : ℂ))) : (Matrix.toEuclideanLin A).kerᗮ) :
          EuclideanSpace ℂ n) i) := by
  -- Unfold the owner once, then normalize the basis vector across the definitional `DecidableEq`.
  classical
  simpa [Matrix.pseudoinverse] using
    (rfl :
      A⁺ i j =
        ((((LinearMap.kerComplementEquivRange (Matrix.toEuclideanLin A)
            ((Matrix.toEuclideanLin A).ker.isCompl_orthogonal.symm)).symm
            ((Matrix.toEuclideanLin A).range.orthogonalProjectionOnto
              (EuclideanSpace.single j (1 : ℂ))) : (Matrix.toEuclideanLin A).kerᗮ) :
            EuclideanSpace ℂ n) i))

/-- Helper for Chapter01 Theorem 1.2.7: `Matrix.pseudoinverseMulVec A b` is the canonical
least-norm preimage of the range projection of `b`. -/
lemma pseudoinverseMulVec_eq_projectedPreimage
    (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    Matrix.pseudoinverseMulVec A b =
      ((((LinearMap.kerComplementEquivRange (Matrix.toEuclideanLin A)
          ((Matrix.toEuclideanLin A).ker.isCompl_orthogonal.symm)).symm
          ((Matrix.toEuclideanLin A).range.orthogonalProjectionOnto b) :
          (Matrix.toEuclideanLin A).kerᗮ) : EuclideanSpace ℂ n)) := by
  let F : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ n := (A⁺).toEuclideanLin
  let G : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ n :=
    (((Matrix.toEuclideanLin A).kerᗮ).subtype) ∘ₗ
      ((LinearMap.kerComplementEquivRange (Matrix.toEuclideanLin A)
        ((Matrix.toEuclideanLin A).ker.isCompl_orthogonal.symm)).symm.toLinearMap ∘ₗ
        ((Matrix.toEuclideanLin A).range.orthogonalProjectionOnto.toLinearMap))
  have hsingle :
      ∀ j : m, F (EuclideanSpace.single j (1 : ℂ)) = G (EuclideanSpace.single j (1 : ℂ)) := by
    intro j
    ext i
    -- Compare the two linear maps on the standard basis vectors.
    calc
      F (EuclideanSpace.single j (1 : ℂ)) i = A⁺ i j := by
        simp [F, Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single, Matrix.mulVec_single,
          PiLp.toLp_apply]
      _ =
          ((((LinearMap.kerComplementEquivRange (Matrix.toEuclideanLin A)
              ((Matrix.toEuclideanLin A).ker.isCompl_orthogonal.symm)).symm
              ((Matrix.toEuclideanLin A).range.orthogonalProjectionOnto
                (EuclideanSpace.single j (1 : ℂ))) : (Matrix.toEuclideanLin A).kerᗮ) :
              EuclideanSpace ℂ n) i) :=
        pseudoinverseEntry_eq_projectedSinglePreimageCoord A i j
      _ = G (EuclideanSpace.single j (1 : ℂ)) i := by
        simp [G]
  have hsum :
      ∀ x : EuclideanSpace ℂ m,
        x = ∑ j : m, x j • EuclideanSpace.single j (1 : ℂ) := by
    intro x
    ext k
    -- Every vector is the sum of its coordinates against the standard basis.
    symm
    simpa [Pi.single_apply] using congrArg (fun v : m → ℂ => v k)
      (Pi.sum_single_apply (v := fun j : m => x.ofLp j))
  -- Since both sides are linear and agree on the standard basis, they agree everywhere.
  calc
    Matrix.pseudoinverseMulVec A b = F b := rfl
    _ = G b := by
      rw [hsum b]
      simp [F, G, hsingle, map_sum]
    _ =
        ((((LinearMap.kerComplementEquivRange (Matrix.toEuclideanLin A)
            ((Matrix.toEuclideanLin A).ker.isCompl_orthogonal.symm)).symm
            ((Matrix.toEuclideanLin A).range.orthogonalProjectionOnto b) :
            (Matrix.toEuclideanLin A).kerᗮ) : EuclideanSpace ℂ n)) := by
      simp [G]

/-- The source vector `A⁺ b = Matrix.pseudoinverseMulVec A b` lies in
`(Matrix.toEuclideanLin A).kerᗮ`. -/
theorem pseudoinverseMulVec_mem_ker_orthogonal (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    Matrix.pseudoinverseMulVec A b ∈ (Matrix.toEuclideanLin A).kerᗮ := by
  -- Rewrite to the canonical kernel-complement preimage.
  rw [pseudoinverseMulVec_eq_projectedPreimage]
  exact ((LinearMap.kerComplementEquivRange (Matrix.toEuclideanLin A)
    ((Matrix.toEuclideanLin A).ker.isCompl_orthogonal.symm)).symm
    ((Matrix.toEuclideanLin A).range.orthogonalProjectionOnto b)).property

/-- Applying `Matrix.toEuclideanLin A` to `A⁺ b = Matrix.pseudoinverseMulVec A b` recovers the
orthogonal projection of `b` onto `(Matrix.toEuclideanLin A).range`. -/
theorem toEuclideanLin_pseudoinverseMulVec (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    Matrix.toEuclideanLin A (Matrix.pseudoinverseMulVec A b) =
      (Matrix.toEuclideanLin A).range.orthogonalProjectionOnto b := by
  -- Rewrite to the explicit least-norm preimage and apply the forward equivalence.
  rw [pseudoinverseMulVec_eq_projectedPreimage]
  exact congrArg Subtype.val
    ((LinearMap.kerComplementEquivRange (Matrix.toEuclideanLin A)
      ((Matrix.toEuclideanLin A).ker.isCompl_orthogonal.symm)).apply_symm_apply
      ((Matrix.toEuclideanLin A).range.orthogonalProjectionOnto b))

/-- Helper for Chapter01 Theorem 1.2.7: a vector is a least-squares solution exactly when its
image under `Matrix.toEuclideanLin A` is the orthogonal projection of `b` onto the range. -/
lemma isLeastSquaresSolution_iff_image_eq_rangeProjection
    (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    IsLeastSquaresSolution A b x ↔
      Matrix.toEuclideanLin A x =
        (Matrix.toEuclideanLin A).range.orthogonalProjectionOnto b := by
  let T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m := Matrix.toEuclideanLin A
  let p : T.range := T.range.orthogonalProjectionOnto b
  constructor
  · intro hx
    have hxMin : ∀ z : EuclideanSpace ℂ n,
        leastSquaresResidual A b x ≤ leastSquaresResidual A b z :=
      (isMinOn_univ_iff.mp hx)
    have hx_mem : T x ∈ T.range := ⟨x, rfl⟩
    let distToRange : T.range → ℝ := fun y ↦ ‖b - (y : EuclideanSpace ℂ m)‖
    have hdist_bdd : BddBelow (Set.range distToRange) := by
      refine ⟨0, Set.forall_mem_range.2 ?_⟩
      intro y
      exact norm_nonneg _
    have hupper :
        ‖b - T x‖ ≤ ⨅ y : T.range, distToRange y := by
      refine le_ciInf ?_
      intro y
      rcases y with ⟨y, hy⟩
      rcases hy with ⟨z, rfl⟩
      simpa [leastSquaresResidual, T, norm_sub_rev] using hxMin z
    have hlower :
        (⨅ y : T.range, distToRange y) ≤ ‖b - T x‖ := by
      exact ciInf_le hdist_bdd ⟨T x, hx_mem⟩
    have hEqInf : ‖b - T x‖ = ⨅ y : T.range, distToRange y :=
      le_antisymm hupper hlower
    have horth :
        b - T x ∈ T.rangeᗮ :=
      (Submodule.mem_orthogonal' _ _).2
        ((T.range.norm_eq_iInf_iff_inner_eq_zero hx_mem).mp hEqInf)
    -- The range point with orthogonal residual is the orthogonal projection.
    have hstar : T.range.starProjection b = T x :=
      T.range.eq_starProjection_of_mem_orthogonal hx_mem horth
    simpa [p, T] using hstar.symm
  · intro hx
    let distToRange : T.range → ℝ := fun y ↦ ‖b - (y : EuclideanSpace ℂ m)‖
    have hdist_bdd : BddBelow (Set.range distToRange) := by
      refine ⟨0, Set.forall_mem_range.2 ?_⟩
      intro y
      exact norm_nonneg _
    have hpMinimal : ‖b - (p : EuclideanSpace ℂ m)‖ = ⨅ y : T.range, distToRange y := by
      simpa [p, distToRange] using T.range.starProjection_minimal b
    -- The projection point minimizes the distance to the range, hence also the residual.
    change IsMinOn (leastSquaresResidual A b) Set.univ x
    rw [isMinOn_univ_iff]
    intro z
    have hz_mem : T z ∈ T.range := ⟨z, rfl⟩
    have hzLower :
        (⨅ y : T.range, distToRange y) ≤ ‖b - T z‖ := by
      exact ciInf_le hdist_bdd ⟨T z, hz_mem⟩
    calc
      leastSquaresResidual A b x = ‖b - (p : EuclideanSpace ℂ m)‖ := by
        rw [leastSquaresResidual, hx, norm_sub_rev]
      _ = ⨅ y : T.range, ‖b - y‖ := hpMinimal
      _ ≤ ‖b - T z‖ := hzLower
      _ = leastSquaresResidual A b z := by
        rw [leastSquaresResidual, norm_sub_rev]

/-- Helper for Chapter01 Theorem 1.2.7: every least-squares solution differs from
`Matrix.pseudoinverseMulVec A b` by an element of the kernel of `Matrix.toEuclideanLin A`. -/
lemma sub_pseudoinverseMulVec_mem_ker_of_isLeastSquaresSolution
    (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) {x : EuclideanSpace ℂ n}
    (hx : IsLeastSquaresSolution A b x) :
    x - Matrix.pseudoinverseMulVec A b ∈ (Matrix.toEuclideanLin A).ker := by
  have hxProj :=
    (isLeastSquaresSolution_iff_image_eq_rangeProjection A b x).mp hx
  have h0 :
      Matrix.toEuclideanLin A (x - Matrix.pseudoinverseMulVec A b) = 0 := by
    -- Both vectors have the same image, so their difference lands in the kernel.
    rw [LinearMap.map_sub, hxProj, toEuclideanLin_pseudoinverseMulVec]
    simp
  exact LinearMap.mem_ker.2 h0

/-- Helper for Chapter01 Theorem 1.2.7: among all least-squares solutions, the pseudoinverse
solution has the smallest Euclidean norm. -/
lemma norm_pseudoinverseMulVec_le_of_isLeastSquaresSolution
    (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) {x : EuclideanSpace ℂ n}
    (hx : IsLeastSquaresSolution A b x) :
    ‖Matrix.pseudoinverseMulVec A b‖ ≤ ‖x‖ := by
  let x0 := Matrix.pseudoinverseMulVec A b
  have hker :
      x - x0 ∈ (Matrix.toEuclideanLin A).ker :=
    sub_pseudoinverseMulVec_mem_ker_of_isLeastSquaresSolution A b hx
  have horth :
      x0 ∈ (Matrix.toEuclideanLin A).kerᗮ :=
    pseudoinverseMulVec_mem_ker_orthogonal A b
  have hinner :
      inner ℂ x0 (x - x0) = 0 := by
    exact Submodule.inner_left_of_mem_orthogonal hker horth
  have hdecomp :
      x0 + (x - x0) = x := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (sub_add_cancel x x0)
  have hpyth :
      ‖x‖ ^ 2 = ‖x0‖ ^ 2 + ‖x - x0‖ ^ 2 := by
    -- Decompose `x` into orthogonal kernel and kernel-complement parts.
    simpa [pow_two, hdecomp] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x0 (x - x0) hinner
  have hx0nonneg : 0 ≤ ‖x0‖ := norm_nonneg _
  have hxnonneg : 0 ≤ ‖x‖ := norm_nonneg _
  have hnonneg : 0 ≤ ‖x - x0‖ ^ 2 := sq_nonneg _
  nlinarith

/-- The source vector `A⁺ b = Matrix.pseudoinverseMulVec A b` is a minimal least-squares
solution of `Matrix.toEuclideanLin A x = b`. -/
theorem pseudoinverseMulVec_isMinimalLeastSquaresSolution
    (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    IsMinimalLeastSquaresSolution A b (Matrix.pseudoinverseMulVec A b) := by
  constructor
  · -- The pseudoinverse image has the projected range image, so it is least-squares optimal.
    exact
      (isLeastSquaresSolution_iff_image_eq_rangeProjection
        A b (Matrix.pseudoinverseMulVec A b)).2
        (toEuclideanLin_pseudoinverseMulVec A b)
  · -- Any least-squares solution has norm at least that of the pseudoinverse image.
    intro z hz
    exact norm_pseudoinverseMulVec_le_of_isLeastSquaresSolution A b hz

/-- Chapter01 Theorem 1.2.7: for `A ∈ ℂ^(m × n)` and `b ∈ ℂ^m`, a vector `x` equals
`Matrix.pseudoinverseMulVec A b = A⁺ b` if and only if it is a least-squares solution of
`Matrix.toEuclideanLin A x = b` with minimal norm among all least-squares solutions. This
expresses that `A⁺ b` is the unique minimal least-squares solution of `Matrix.toEuclideanLin A x
= b` in the Euclidean norm. -/
theorem eq_pseudoinverseMulVec_iff_isMinimalLeastSquaresSolution
    (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    (x : EuclideanSpace ℂ n) :
    x = Matrix.pseudoinverseMulVec A b ↔ IsMinimalLeastSquaresSolution A b x :=
  by
    constructor
    · intro hx
      -- The forward direction is the already-proved minimality of the pseudoinverse image.
      simpa [hx] using pseudoinverseMulVec_isMinimalLeastSquaresSolution A b
    · intro hx
      rcases hx with ⟨hxLeast, hxMinNorm⟩
      have hxMinNorm' := isMinOn_iff.mp hxMinNorm
      have hx0Minimal := pseudoinverseMulVec_isMinimalLeastSquaresSolution A b
      have hnorm_ge :
          ‖Matrix.pseudoinverseMulVec A b‖ ≤ ‖x‖ :=
        norm_pseudoinverseMulVec_le_of_isLeastSquaresSolution A b hxLeast
      have hnorm_le :
          ‖x‖ ≤ ‖Matrix.pseudoinverseMulVec A b‖ :=
        hxMinNorm' (Matrix.pseudoinverseMulVec A b) hx0Minimal.1
      have hnorm_eq :
          ‖x‖ = ‖Matrix.pseudoinverseMulVec A b‖ :=
        le_antisymm hnorm_le hnorm_ge
      let x0 := Matrix.pseudoinverseMulVec A b
      have hker :
          x - x0 ∈ (Matrix.toEuclideanLin A).ker :=
        sub_pseudoinverseMulVec_mem_ker_of_isLeastSquaresSolution A b hxLeast
      have horth :
          x0 ∈ (Matrix.toEuclideanLin A).kerᗮ :=
        pseudoinverseMulVec_mem_ker_orthogonal A b
      have hinner :
          inner ℂ x0 (x - x0) = 0 := by
        exact Submodule.inner_left_of_mem_orthogonal hker horth
      have hdecomp :
          x0 + (x - x0) = x := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (sub_add_cancel x x0)
      have hpyth :
          ‖x‖ ^ 2 = ‖x0‖ ^ 2 + ‖x - x0‖ ^ 2 := by
        -- Route correction: uniqueness is proved through the orthogonal kernel decomposition,
        -- not by re-running the least-squares minimization argument a second time.
        simpa [pow_two, hdecomp] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x0 (x - x0) hinner
      have hnorm_sq_eq : ‖x‖ ^ 2 = ‖x0‖ ^ 2 := by
        exact congrArg (fun t : ℝ => t ^ 2) hnorm_eq
      have hzeroNorm : ‖x - x0‖ = 0 := by
        have hnonneg : 0 ≤ ‖x - x0‖ ^ 2 := sq_nonneg _
        nlinarith
      have hzero : x - x0 = 0 :=
        norm_eq_zero.1 hzeroNorm
      simpa [x0] using sub_eq_zero.1 hzero

/-- A vector is a minimal least-squares solution exactly when it equals the source pseudoinverse
image `A⁺ b = Matrix.pseudoinverseMulVec A b`. -/
theorem isMinimalLeastSquaresSolution_iff_eq_pseudoinverseMulVec
    (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    (x : EuclideanSpace ℂ n) :
    IsMinimalLeastSquaresSolution A b x ↔
      x = Matrix.pseudoinverseMulVec A b := by
  simpa using
    (eq_pseudoinverseMulVec_iff_isMinimalLeastSquaresSolution A b x).symm

end Matrix
