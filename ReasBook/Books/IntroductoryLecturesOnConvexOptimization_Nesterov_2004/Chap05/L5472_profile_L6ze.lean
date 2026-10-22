/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_4_1

set_option profiler true


-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped MatrixOrder RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n
local notation "Point" => SymmMat × SymmMat

local notation "Z" => WithLp 2 Point
local notation "ofZ" => (WithLp.ofLp : Z → Point)
local notation "BlockMat" => Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ
local notation "BigMat" => Matrix (Fin (n + n)) (Fin (n + n)) ℝ
local notation "BigSymmMat" => 𝕊^(n + n)

/- Lemma 5.4.7.2 lies in the Chapter 5 self-concordant-barrier / symmetric-matrix inverse-epigraph
domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Chap05/Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  in `Chap05/Theorem_5_4_1_2`, the canonical owner of the recession-direction barrier lower
  bound;
* mathlib `WithLp.prodContinuousLinearEquiv`, the canonical `L²` product bridge between raw pairs
  and the ambient Hilbert-space owner;
* `RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup`,
  `RealSymmetricMatrixSpace.symmetricMatrixNormedSpace`, and
  `RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace` in `Chap05/Definition_5_4_4_2`, the
  chapter owner layer for the intrinsic Frobenius geometry on `𝕊^n`;
* `𝕊^n` in `Chap05/Definition_5_4_4_1`, the chapter owner for real symmetric matrices;
* `𝕊^n₊` in `Chap05/Definition_5_4_4_3`, the positive-semidefinite cone owner;
* `𝕊^n₊₊` in `Chap05/Definition_5_4_4_5`, the intrinsic strict positive-definite cone owner.

Best owner abstraction:
* source-facing: the inverse epigraph `𝓘_n = {(X, Y) | X ≻ 0, Y ⪰ X⁻¹}`;
* core/canonical: the barrier owner on the canonical ambient product `Z = WithLp 2 (𝕊^n × 𝕊^n)`;
* bridge/view: the source-facing raw-pair set `matrixInverseEpigraph` and its pullback along
  `WithLp.ofLp`.

Primitive data:
* `n : ℕ`;
* the source-facing set `matrixInverseEpigraph : Set (𝕊^n × 𝕊^n)`.

Derived API:
* the membership theorem `mem_matrixInverseEpigraph_iff`;
* the barrier-parameter lower bound
  `matrixInverseEpigraph_barrierParameter_ge_two_mul_dimension`.

The previous file encoded points of `𝓘_n` as raw coordinates in the full matrix-entry Euclidean
space and rebuilt projection/instance scaffolding just to recover the symmetric matrices. That
ambient level is too low: the source mathematics is about symmetric matrices and the chapter
already owns `𝕊^n`, `𝕊^n₊₊`, and their Frobenius Hilbert-space structure. This refinement
therefore keeps the public set owner on the intrinsic product `𝕊^n × 𝕊^n`, but moves the barrier
theorem itself to the canonical `L²` product owner `Z = WithLp 2 (𝕊^n × 𝕊^n)` via the bridge
`WithLp.ofLp`. Downstream users now reuse the chapter owner instances directly instead of carrying
any parallel local ambient geometry.
-/

/-- The inverse-epigraph set `𝓘_n = {(X, Y) | X ≻ 0, Y ⪰ X⁻¹}` of symmetric real `n × n`
matrices. -/
def matrixInverseEpigraph : Set Point :=
  {XY | XY.1 ∈ 𝕊^n₊₊ ∧ (XY.1 : Mat)⁻¹ ≤ (XY.2 : Mat)}

/-- A pair `(X, Y)` belongs to `matrixInverseEpigraph` exactly when `X` is positive definite and
`Y` dominates `X⁻¹` in the Löwner order. -/
@[simp] theorem mem_matrixInverseEpigraph_iff (XY : Point) :
    XY ∈ matrixInverseEpigraph ↔
      XY.1 ∈ 𝕊^n₊₊ ∧ (XY.1 : Mat)⁻¹ ≤ (XY.2 : Mat) :=
  Iff.rfl

/-- Helper for Lemma 5.4.7.2: the inverse-epigraph condition is equivalent to positive
semidefiniteness of the associated Schur-complement block matrix. -/
private theorem matrixInverseEpigraph_iff_block_posSemidef (XY : Point) :
    XY ∈ matrixInverseEpigraph ↔
      XY.1 ∈ 𝕊^n₊₊ ∧
        (Matrix.fromBlocks ((XY.1 : SymmMat) : Mat) 1 1 ((XY.2 : SymmMat) : Mat)).PosSemidef := by
  constructor
  · rintro ⟨hX, hXY⟩
    -- Convert the order inequality `X⁻¹ ≤ Y` into the Schur-complement positivity condition.
    have hXpos : ((XY.1 : SymmMat) : Mat).PosDef := by
      simpa using strictPositiveSemidefiniteCone_posDef (X := ⟨XY.1, hX⟩)
    letI : Invertible (((XY.1 : SymmMat) : Mat)) :=
      Matrix.invertibleOfIsUnitDet _ (by
        simpa [Matrix.isUnit_iff_isUnit_det] using hXpos.isUnit)
    have hschur :
        (((XY.2 : SymmMat) : Mat) - 1ᴴ * (((XY.1 : SymmMat) : Mat))⁻¹ * 1).PosSemidef := by
      rw [Matrix.conjTranspose_one, one_mul, mul_one]
      simpa [Matrix.le_iff] using hXY
    exact ⟨hX, by
      simpa using
        (Matrix.PosDef.fromBlocks₁₁
          (B := (1 : Mat)) (((XY.2 : SymmMat) : Mat)) hXpos).2 hschur⟩
  · rintro ⟨hX, hblock⟩
    -- Read the Schur complement back as the Löwner inequality `X⁻¹ ≤ Y`.
    have hXpos : ((XY.1 : SymmMat) : Mat).PosDef := by
      simpa using strictPositiveSemidefiniteCone_posDef (X := ⟨XY.1, hX⟩)
    letI : Invertible (((XY.1 : SymmMat) : Mat)) :=
      Matrix.invertibleOfIsUnitDet _ (by
        simpa [Matrix.isUnit_iff_isUnit_det] using hXpos.isUnit)
    have hschur :
        (((XY.2 : SymmMat) : Mat) - 1ᴴ * (((XY.1 : SymmMat) : Mat))⁻¹ * 1).PosSemidef := by
      have hblock' :
          (Matrix.fromBlocks
            ((XY.1 : SymmMat) : Mat)
            (1 : Mat)
            ((1 : Mat)ᴴ)
            ((XY.2 : SymmMat) : Mat)).PosSemidef := by
        simpa [Matrix.conjTranspose_one] using hblock
      simpa using
        (Matrix.PosDef.fromBlocks₁₁
          (B := (1 : Mat)) (((XY.2 : SymmMat) : Mat)) hXpos).1 hblock'
    refine ⟨hX, ?_⟩
    simpa [Matrix.le_iff, Matrix.conjTranspose_one, one_mul, mul_one] using hschur

/-- Helper for Lemma 5.4.7.2: the inverse epigraph is convex. -/
private theorem matrixInverseEpigraph_convex :
    Convex ℝ (matrixInverseEpigraph (n := n)) := by
  intro XY hXY UV hUV a b ha hb hab
  rw [matrixInverseEpigraph_iff_block_posSemidef] at hXY hUV ⊢
  refine ⟨?_, ?_⟩
  · -- The strict `X`-cone is the interior of the PSD cone, hence convex.
    simpa [strictPositiveSemidefiniteCone_eq_interior] using
      (Convex.interior (positiveSemidefiniteCone_convex n)) hXY.1 hUV.1 ha hb hab
  · -- The Schur-complement block condition is preserved under convex combinations.
    have hblock :
        Matrix.fromBlocks
            ((((a • XY + b • UV).1 : SymmMat) : Mat)) (1 : Mat) (1 : Mat)
            ((((a • XY + b • UV).2 : SymmMat) : Mat)) =
          a • Matrix.fromBlocks
              (((XY.1 : SymmMat) : Mat)) (1 : Mat) (1 : Mat) (((XY.2 : SymmMat) : Mat)) +
            b • Matrix.fromBlocks
              (((UV.1 : SymmMat) : Mat)) (1 : Mat) (1 : Mat) (((UV.2 : SymmMat) : Mat)) := by
      ext i j
      cases i
      · cases j <;> simp [← add_mul, hab]
      · cases j <;> simp [← add_mul, hab]
    rw [hblock]
    exact (hXY.2.smul ha).add (hUV.2.smul hb)

/-- Helper for Lemma 5.4.7.2: the diagonal single-entry projector is symmetric. -/
private theorem coordinate_projector_diagonal_mem_symmetric_subspace
    (i : Fin n) :
    Matrix.diagonal (Pi.single i (1 : ℝ)) ∈ 𝕊^n := by
  -- A diagonal matrix is symmetric, so it belongs to the intrinsic symmetric carrier.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm, Matrix.IsSymm]
  ext j k
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [hjk, eq_comm]

/-- Helper for Lemma 5.4.7.2: the `i`-th coordinate rank-one projector in `𝕊^n`. -/
private def coordinateProjector
    (n : ℕ) (i : Fin n) : 𝕊^n :=
  ⟨Matrix.diagonal (Pi.single i (1 : ℝ)),
    coordinate_projector_diagonal_mem_symmetric_subspace (n := n) i⟩

/-- Helper for Lemma 5.4.7.2: the coordinate projector is the diagonal matrix with one nonzero
entry. -/
private theorem coordinate_projector_eq_diagonal_single
    (i : Fin n) :
    ((coordinateProjector n i : 𝕊^n) : Mat) = Matrix.diagonal (Pi.single i (1 : ℝ)) := by
  -- The projector is definitionally the single-entry diagonal matrix.
  rfl

/-- Helper for Lemma 5.4.7.2: each coordinate projector is positive semidefinite. -/
private theorem coordinate_projector_posSemidef
    (i : Fin n) :
    (((coordinateProjector n i : 𝕊^n) : Mat)).PosSemidef := by
  -- The projector has nonnegative diagonal entries, so its quadratic form is nonnegative.
  rw [coordinate_projector_eq_diagonal_single (n := n) i]
  exact Matrix.PosSemidef.diagonal <| by
    intro j
    by_cases hji : j = i
    · simp [Pi.single_apply, hji]
    · simp [hji]

/-- Helper for Lemma 5.4.7.2: moving one unit backward along a coordinate projector leaves the
strict positive-definite cone. -/
private theorem one_sub_coordinate_projector_not_mem_strictPositiveSemidefiniteCone
    (i : Fin n) :
    (1 : 𝕊^n) - coordinateProjector n i ∉ (𝕊^n₊₊ : Set (𝕊^n)) := by
  intro hmem
  -- The witness vector `eᵢ` kills the quadratic form of `I - eᵢeᵢᵀ`.
  let M : Mat := (((1 : 𝕊^n) - coordinateProjector n i : 𝕊^n) : Mat)
  let u : Fin n → ℝ := Pi.single i (1 : ℝ)
  have hpos : M.PosDef := by
    simpa using
      (strictPositiveSemidefiniteCone_posDef
        (X := ⟨(1 : 𝕊^n) - coordinateProjector n i, hmem⟩))
  have hmul : M *ᵥ u = 0 := by
    -- The `i`-th column of `I - eᵢeᵢᵀ` is zero.
    rw [Matrix.mulVec_single_one]
    ext j
    by_cases hji : j = i
    · subst hji
      simp [M, coordinate_projector_eq_diagonal_single]
    · simp [M, coordinate_projector_eq_diagonal_single, hji]
  have hu_ne : u ≠ 0 := by
    change (Pi.single i (1 : ℝ) : Fin n → ℝ) ≠ 0
    exact (Pi.single_eq_zero_iff (i := i)).not.mpr one_ne_zero
  have hzero_lt : (0 : ℝ) < 0 := by
    -- Positive definiteness contradicts the vanished quadratic form.
    have hquad_pos : 0 < dotProduct u (M *ᵥ u) := hpos.dotProduct_mulVec_pos hu_ne
    have hquad_zero : dotProduct u (M *ᵥ u) = 0 := by
      rw [hmul, dotProduct_zero]
    exact hquad_zero.symm ▸ hquad_pos
  exact (lt_irrefl 0) hzero_lt

/-- Helper for Lemma 5.4.7.2: the block matrix attached to a point of the inverse epigraph. -/
private def blockMatrix
    (XY : Point) : BlockMat :=
  Matrix.fromBlocks ((XY.1 : SymmMat) : Mat) 1 1 ((XY.2 : SymmMat) : Mat)

/-- Helper for Lemma 5.4.7.2: the block matrix associated to a symmetric pair is itself
symmetric. -/
private theorem blockMatrix_isSymm
    (XY : Point) :
    (blockMatrix XY).IsSymm := by
  -- The diagonal blocks are symmetric and the off-diagonal blocks are both the identity.
  refine Matrix.IsSymm.fromBlocks ?_ ?_ ?_
  · simpa using RealSymmetricMatrixSpace.isSymm XY.1
  · simp
  · simpa using RealSymmetricMatrixSpace.isSymm XY.2

/-- Helper for Lemma 5.4.7.2: after reindexing from `Fin n ⊕ Fin n` to `Fin (n + n)`, the block
matrix lies in the symmetric subspace `𝕊^(n+n)`. -/
private theorem blockMatrix_reindexed_mem_symmetric_subspace
    (XY : Point) :
    (blockMatrix XY).submatrix finSumFinEquiv.symm finSumFinEquiv.symm ∈ BigSymmMat := by
  -- Reindexing preserves symmetry, so the block matrix can be viewed in the intrinsic carrier.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa using (blockMatrix_isSymm (n := n) XY).submatrix finSumFinEquiv.symm

/-- Helper for Lemma 5.4.7.2: the reindexed block matrix, packaged in the intrinsic symmetric
carrier `𝕊^(n+n)`. -/
private def blockSymm
    (XY : Point) : BigSymmMat :=
  ⟨(blockMatrix XY).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    blockMatrix_reindexed_mem_symmetric_subspace (n := n) XY⟩

/-- Helper for Lemma 5.4.7.2: the reindexed symmetric block-matrix map is continuous. -/
private theorem blockSymm_continuous :
    Continuous (blockSymm (n := n)) := by
  -- The block construction and the fixed reindexing are linear, hence continuous.
  have hblock :
      Continuous (fun XY : Point ↦ blockMatrix XY) := by
    simpa [blockMatrix] using
      (Continuous.matrix_fromBlocks
        (A := fun XY : Point ↦ ((XY.1 : SymmMat) : Mat))
        (B := fun _ : Point ↦ (1 : Mat))
        (C := fun _ : Point ↦ (1 : Mat))
        (D := fun XY : Point ↦ ((XY.2 : SymmMat) : Mat))
        (continuous_subtype_val.comp continuous_fst)
        continuous_const
        continuous_const
        (continuous_subtype_val.comp continuous_snd))
  refine Continuous.subtype_mk ?_ ?_
  simpa [blockSymm] using hblock.matrix_submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Helper for Lemma 5.4.7.2: the coordinate projectors reconstruct the identity. -/
private theorem sum_coordinate_projectors_eq_one :
    ∑ i : Fin n, coordinateProjector n i = (1 : 𝕊^n) := by
  -- Summing the diagonal projectors recovers the identity diagonal.
  apply Subtype.ext
  simpa [coordinate_projector_eq_diagonal_single, Matrix.diagonal_single] using
    (Matrix.sum_single_one : ∑ i : Fin n, Matrix.single i i (1 : ℝ) = (1 : Mat))

/-- Helper for Lemma 5.4.7.2: the two coordinate-projector families in the `X`- and `Y`-slots. -/
private def coordinateDirection
    : Fin n ⊕ Fin n → Point
  | Sum.inl i => (coordinateProjector n i, 0)
  | Sum.inr i => (0, coordinateProjector n i)

/-- Helper for Lemma 5.4.7.2: the coordinate directions sum to `(I, I)`. -/
private theorem sum_coordinate_directions_eq_one_pair :
    ∑ i : Fin n ⊕ Fin n, coordinateDirection i = ((1 : SymmMat), (1 : SymmMat)) := by
  -- Separate the `X`- and `Y`-slot sums and rewrite both by the projector decomposition.
  rw [Fintype.sum_sum_type]
  ext i j <;>
    simp [Prod.fst_sum, Prod.snd_sum, coordinateDirection, sum_coordinate_projectors_eq_one]

/-- Helper for Lemma 5.4.7.2: adding a scaled coordinate projector in the `X`-block gives a
positive-semidefinite block perturbation. -/
private theorem coordinate_projector_block_left_posSemidef
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    (Matrix.fromBlocks
      (t • (((coordinateProjector n i : 𝕊^n) : Mat)))
      0 0 (0 : Mat)).PosSemidef := by
  -- Embed the PSD coordinate projector into the top-left block by conjugation.
  let E : Matrix (Fin n ⊕ Fin n) (Fin n) ℝ := Matrix.fromBlocks (1 : Mat) 0
  have hE :
      E * (t • (((coordinateProjector n i : 𝕊^n) : Mat))) * Eᴴ =
        Matrix.fromBlocks
          (t • (((coordinateProjector n i : 𝕊^n) : Mat)))
          0 0 (0 : Mat) := by
    ext a b
    cases a
    · cases b <;> simp [E]
    · cases b <;> simp [E]
  rw [← hE]
  exact (((coordinate_projector_posSemidef (n := n) i).smul ht).mul_mul_conjTranspose_same E)

/-- Helper for Lemma 5.4.7.2: adding a scaled coordinate projector in the `Y`-block gives a
positive-semidefinite block perturbation. -/
private theorem coordinate_projector_block_right_posSemidef
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    (Matrix.fromBlocks
      (0 : Mat) 0 0 (t • (((coordinateProjector n i : 𝕊^n) : Mat)))).PosSemidef := by
  -- Embed the PSD coordinate projector into the bottom-right block by conjugation.
  let E : Matrix (Fin n ⊕ Fin n) (Fin n) ℝ := Matrix.fromBlocks 0 (1 : Mat)
  have hE :
      E * (t • (((coordinateProjector n i : 𝕊^n) : Mat))) * Eᴴ =
        Matrix.fromBlocks
          (0 : Mat)
          0 0 (t • (((coordinateProjector n i : 𝕊^n) : Mat))) := by
    ext a b
    cases a
    · cases b <;> simp [E]
    · cases b <;> simp [E]
  rw [← hE]
  exact (((coordinate_projector_posSemidef (n := n) i).smul ht).mul_mul_conjTranspose_same E)

/-- Helper for Lemma 5.4.7.2: each coordinate direction is a recession direction of the inverse
epigraph. -/
private theorem coordinate_direction_recession_of_matrixInverseEpigraph
    (i : Fin n ⊕ Fin n) :
    ∀ ⦃XY : Point⦄, XY ∈ matrixInverseEpigraph → ∀ t : ℝ, 0 ≤ t →
      XY + t • coordinateDirection i ∈ matrixInverseEpigraph := by
  intro XY hXY t ht
  cases i with
  | inl i =>
      rw [matrixInverseEpigraph_iff_block_posSemidef] at hXY ⊢
      refine ⟨?_, ?_⟩
      · -- In the `X`-slot, strict positivity survives after adding a PSD projector perturbation.
        have hXpos : ((XY.1 : SymmMat) : Mat).PosDef := by
          simpa using strictPositiveSemidefiniteCone_posDef (X := ⟨XY.1, hXY.1⟩)
        have hstep : ((XY + t • coordinateDirection (Sum.inl i)).1 : Mat).PosDef := by
          simpa [coordinateDirection] using
            hXpos.add_posSemidef
              (((coordinate_projector_posSemidef (n := n) i)).smul ht)
        exact mem_strictPositiveSemidefiniteCone_of_posDef hstep
      · -- The block matrix gains exactly the left PSD perturbation.
        have hblock :
            blockMatrix (XY + t • coordinateDirection (Sum.inl i)) =
              blockMatrix XY +
                Matrix.fromBlocks
                  (t • (((coordinateProjector n i : 𝕊^n) : Mat)))
                  0 0 (0 : Mat) := by
          ext a b
          cases a
          · cases b <;> simp [blockMatrix, coordinateDirection]
          · cases b <;> simp [blockMatrix, coordinateDirection]
        simpa [blockMatrix] using
          (show (blockMatrix (XY + t • coordinateDirection (Sum.inl i))).PosSemidef from by
            rw [hblock]
            exact hXY.2.add (coordinate_projector_block_left_posSemidef (n := n) i ht))
  | inr i =>
      rw [matrixInverseEpigraph_iff_block_posSemidef] at hXY ⊢
      refine ⟨?_, ?_⟩
      · -- In the `Y`-slot, the strict `X`-positivity is unchanged.
        simpa [coordinateDirection] using hXY.1
      · -- The block matrix gains exactly the right PSD perturbation.
        have hblock :
            blockMatrix (XY + t • coordinateDirection (Sum.inr i)) =
              blockMatrix XY +
                Matrix.fromBlocks
                  (0 : Mat)
                  0 0 (t • (((coordinateProjector n i : 𝕊^n) : Mat))) := by
          ext a b
          cases a
          · cases b <;> simp [blockMatrix, coordinateDirection]
          · cases b <;> simp [blockMatrix, coordinateDirection]
        simpa [blockMatrix] using
          (show (blockMatrix (XY + t • coordinateDirection (Sum.inr i))).PosSemidef from by
            rw [hblock]
            exact hXY.2.add (coordinate_projector_block_right_posSemidef (n := n) i ht))

/-- Helper for Lemma 5.4.7.2: stepping back by `γ` along any coordinate direction leaves the
inverse epigraph. -/
private theorem gamma_sub_coordinate_direction_not_mem_matrixInverseEpigraph
    (γ : ℝ) (hγ : 1 < γ) (i : Fin n ⊕ Fin n) :
    (((γ • (1 : SymmMat)), (γ • (1 : SymmMat))) : Point) -
        γ • coordinateDirection i ∉ matrixInverseEpigraph := by
  have hγ_pos : 0 < γ := lt_trans zero_lt_one hγ
  have hγ_ne : γ ≠ 0 := hγ_pos.ne'
  cases i with
  | inl i =>
      intro hmem
      rw [mem_matrixInverseEpigraph_iff] at hmem
      have hscaled_mem :
          (γ • ((1 : SymmMat) - coordinateProjector n i) : SymmMat) ∈ (𝕊^n₊₊ : Set (𝕊^n)) := by
        -- The backward step in the `X`-slot is exactly a positive scalar multiple of `I - Pᵢ`.
        simpa [coordinateDirection, smul_sub] using hmem.1
      have hscaled_pos :
          (((γ • ((1 : SymmMat) - coordinateProjector n i) : SymmMat) : Mat)).PosDef := by
        simpa using strictPositiveSemidefiniteCone_posDef (X := ⟨_, hscaled_mem⟩)
      have hbase_pos :
          ((((1 : SymmMat) - coordinateProjector n i : SymmMat) : Mat)).PosDef := by
        -- Scale the positive-definite matrix back by `γ⁻¹` to recover `I - Pᵢ`.
        have hback :
            (γ⁻¹ •
              (((γ • ((1 : SymmMat) - coordinateProjector n i) : SymmMat) : Mat))).PosDef := by
          simpa using hscaled_pos.smul (inv_pos.mpr hγ_pos)
        simpa [smul_smul, inv_mul_cancel₀ hγ_ne] using hback
      exact one_sub_coordinate_projector_not_mem_strictPositiveSemidefiniteCone
        (n := n) i <|
        mem_strictPositiveSemidefiniteCone_of_posDef hbase_pos
  | inr i =>
      intro hmem
      rw [mem_matrixInverseEpigraph_iff] at hmem
      have hle := hmem.2
      have hbound :
          ((((γ • ((1 : SymmMat) - coordinateProjector n i) : SymmMat) : Mat)) -
            (((γ • (1 : SymmMat) : SymmMat) : Mat))⁻¹).PosSemidef := by
        -- The backward step in the `Y`-slot would force the Schur complement to stay PSD.
        simpa [coordinateDirection, smul_sub, Matrix.le_iff] using hle
      have hInv :
          (((γ • (1 : SymmMat) : SymmMat) : Mat))⁻¹ = γ⁻¹ • (1 : Mat) := by
        -- The inverse of `γ I` is `(1 / γ) I`.
        have hdet : IsUnit ((1 : Mat).det) := by
          simp
        simpa using
          (Matrix.inv_smul' (A := (1 : Mat)) (k := Units.mk0 γ hγ_ne) hdet)
      have hdiag_nonneg :
          0 ≤
            ((((γ • ((1 : SymmMat) - coordinateProjector n i) : SymmMat) : Mat)) -
              (((γ • (1 : SymmMat) : SymmMat) : Mat))⁻¹) i i := by
        simpa using hbound.diag_nonneg (i := i)
      rw [hInv] at hdiag_nonneg
      have hdiag :
          ((((γ • ((1 : SymmMat) - coordinateProjector n i) : SymmMat) : Mat)) -
              γ⁻¹ • (1 : Mat)) i i = -(γ⁻¹) := by
        simp [coordinate_projector_eq_diagonal_single]
      rw [hdiag] at hdiag_nonneg
      linarith [inv_pos.mpr hγ_pos]

/-- Helper for Lemma 5.4.7.2: strict positivity of both the `X`-block and the reindexed block
matrix already places a point in the inverse epigraph. -/
private theorem block_strict_neighborhood_subset_matrixInverseEpigraph
    {XY : Point}
    (hX : XY.1 ∈ 𝕊^n₊₊)
    (hblock : blockSymm XY ∈ 𝕊^(n + n)₊₊) :
    XY ∈ matrixInverseEpigraph := by
  -- Read strict positivity as positive semidefiniteness on both ambient matrices.
  rw [matrixInverseEpigraph_iff_block_posSemidef]
  refine ⟨hX, ?_⟩
  have hblock_psd :
      (((blockSymm XY : BigSymmMat) : BigMat)).PosSemidef := by
    exact (strictPositiveSemidefiniteCone_posDef (X := ⟨blockSymm XY, hblock⟩)).posSemidef
  -- Transport the PSD statement back across the fixed reindexing equivalence.
  simpa [blockSymm] using
    (Matrix.posSemidef_submatrix_equiv
      (M := blockMatrix XY) finSumFinEquiv.symm).mp hblock_psd

/-- Helper for Lemma 5.4.7.2: the block matrix at the base point `(γ I, γ I)` is positive
definite. -/
private theorem gamma_basepoint_block_matrix_posDef
    {γ : ℝ} (hγ : 1 < γ) :
    (blockMatrix ((((γ • (1 : SymmMat)), (γ • (1 : SymmMat))) : Point))).PosDef := by
  -- The quadratic form of `[[γI, I], [I, γI]]` splits as
  -- `(γ - 1) (‖x‖² + ‖y‖²) + ‖x + y‖²`.
  let base : Point := ((γ • (1 : SymmMat)), (γ • (1 : SymmMat)))
  let M : BlockMat := blockMatrix base
  have hγ_sub_pos : 0 < γ - 1 := sub_pos.mpr hγ
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [M, base, blockMatrix] using (blockMatrix_isSymm (n := n) base).isHermitian
  · intro z hz
    let x : Fin n → ℝ := fun i ↦ z (Sum.inl i)
    let y : Fin n → ℝ := fun i ↦ z (Sum.inr i)
    have hx_nonneg : 0 ≤ dotProduct x x := by
      simpa using (dotProduct_star_self_nonneg x)
    have hy_nonneg : 0 ≤ dotProduct y y := by
      simpa using (dotProduct_star_self_nonneg y)
    have hxy_nonneg : 0 ≤ dotProduct (x + y) (x + y) := by
      simpa using (dotProduct_star_self_nonneg (x + y))
    have hxy_ne : x ≠ 0 ∨ y ≠ 0 := by
      by_contra hxy
      push_neg at hxy
      apply hz
      ext i
      cases i with
      | inl i =>
          simpa [x] using congrFun hxy.1 i
      | inr i =>
          simpa [y] using congrFun hxy.2 i
    have hsum_nonneg : 0 ≤ dotProduct x x + dotProduct y y := add_nonneg hx_nonneg hy_nonneg
    have hsum_pos : 0 < dotProduct x x + dotProduct y y := by
      refine lt_of_le_of_ne hsum_nonneg ?_
      intro hsum_zero
      have hx_zero : x = 0 := by
        apply dotProduct_self_eq_zero.mp
        nlinarith
      have hy_zero : y = 0 := by
        apply dotProduct_self_eq_zero.mp
        nlinarith
      exact hxy_ne.elim (fun hx => hx hx_zero) (fun hy => hy hy_zero)
    have hformula :
        dotProduct z (M *ᵥ z) =
          (γ - 1) * (dotProduct x x + dotProduct y y) + dotProduct (x + y) (x + y) := by
      simp [M, base, blockMatrix, x, y, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
        Finset.sum_add_distrib, Finset.add_sum, mul_add, add_mul]
      ring
    rw [hformula]
    exact add_pos_of_pos_of_nonneg (mul_pos hγ_sub_pos hsum_pos) hxy_nonneg

/-- Helper for Lemma 5.4.7.2: the base point `(γ I, γ I)` lies in the interior of the inverse
epigraph when `γ > 1`. -/
private theorem gamma_basepoint_mem_interior_matrixInverseEpigraph
    {γ : ℝ} (hγ : 1 < γ) :
    (((γ • (1 : SymmMat)), (γ • (1 : SymmMat))) : Point) ∈ interior matrixInverseEpigraph := by
  let base : Point := ((γ • (1 : SymmMat)), (γ • (1 : SymmMat)))
  have hγ_pos : 0 < γ := lt_trans zero_lt_one hγ
  have hX_strict : (γ • (1 : SymmMat) : SymmMat) ∈ 𝕊^n₊₊ := by
    -- The first coordinate is the positive scalar multiple `γ I`.
    refine mem_strictPositiveSemidefiniteCone_of_posDef ?_
    simpa using (Matrix.PosDef.one : (1 : Mat).PosDef).smul hγ_pos
  have hblock_strict : blockSymm base ∈ 𝕊^(n + n)₊₊ := by
    -- Certify strict block positivity by the standalone base-point factorization lemma.
    have hblock_pos :
        (blockMatrix base).PosDef := by
      simpa [base] using gamma_basepoint_block_matrix_posDef (n := n) hγ
    have hblock_reindexed :
        (((blockSymm base : BigSymmMat) : BigMat)).PosDef := by
      simpa [blockSymm] using hblock_pos.submatrix finSumFinEquiv.symm.injective
    exact mem_strictPositiveSemidefiniteCone_of_posDef hblock_reindexed
  -- The strict `X`-cone and strict block cone provide an open neighborhood inside the epigraph.
  rw [mem_interior_iff_mem_nhds]
  have hfirst :
      Prod.fst ⁻¹' (𝕊^n₊₊ : Set SymmMat) ∈ nhds base := by
    exact continuous_fst.continuousAt.preimage_mem_nhds <|
      by simpa [strictPositiveSemidefiniteCone_eq_interior] using
        (isOpen_interior.mem_nhds hX_strict)
  have hsecond :
      blockSymm ⁻¹' (𝕊^(n + n)₊₊ : Set BigSymmMat) ∈ nhds base := by
    exact blockSymm_continuous.continuousAt.preimage_mem_nhds <|
      by simpa [strictPositiveSemidefiniteCone_eq_interior] using
        (isOpen_interior.mem_nhds hblock_strict)
  have hnhds : matrixInverseEpigraph ∈ nhds base := by
    refine Filter.mem_of_superset (Filter.inter_mem hfirst hsecond) ?_
    intro XY hXY
    exact block_strict_neighborhood_subset_matrixInverseEpigraph hXY.1 hXY.2
  simpa [base] using hnhds

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` to
-- `matrixInverseEpigraph` with base point `(γ I, γ I)` for `γ > 1`, recession directions the
-- `2n` rank-one directions `(eᵢ eᵢᵀ, 0)` and `(0, eᵢ eᵢᵀ)`, backward-step coefficients
-- `β = γ`, and forward coefficients `α = γ - 1`. The combined step reaches `(I, I)`,
-- giving `ν ≥ 2n * γ / (1 + γ)`; letting `γ → ∞` yields `ν ≥ 2n`.
/-- Lemma 5.4.7.2: any self-concordant barrier for the inverse-epigraph set
`𝓘_n = {(X, Y) | X ≻ 0, Y ⪰ X⁻¹}` has parameter at least `2 n`. -/
theorem matrixInverseEpigraph_barrierParameter_ge_two_mul_dimension
    {ν : NNReal} {F : Z → ℝ}
    (hF : IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior matrixInverseEpigraph) ν F) :
    (2 * n : ℝ) ≤ (ν : ℝ) := by
  by_cases hn : n = 0
  · -- In dimension `0`, the claimed lower bound is the trivial nonnegativity of `ν`.
    rw [hn]
    norm_num
  · by_contra hν
    have hlt : (ν : ℝ) < (2 * n : ℝ) := not_le.mp hν
    let Q : Set Z := ofZ ⁻¹' matrixInverseEpigraph
    have hQ_convex : Convex ℝ Q := by
      -- Pull the raw inverse-epigraph convexity back by rewriting through `WithLp.ofLp`.
      intro x hx y hy a b ha hb hab
      change ofZ (a • x + b • y) ∈ matrixInverseEpigraph
      have hxRaw : ofZ x ∈ matrixInverseEpigraph := by
        simpa [Q] using hx
      have hyRaw : ofZ y ∈ matrixInverseEpigraph := by
        simpa [Q] using hy
      simpa using (matrixInverseEpigraph_convex (n := n) hxRaw hyRaw ha hb hab)
    have hQ_interior :
        interior Q = ofZ ⁻¹' interior matrixInverseEpigraph := by
      -- The canonical `WithLp` product homeomorphism transports interiors to preimages.
      let e : Z ≃L[ℝ] Point := (WithLp.linearEquiv 2 ℝ Point).toContinuousLinearEquiv
      simpa [Q, e] using (e.toHomeomorph.preimage_interior matrixInverseEpigraph).symm
    have hFQ :
        IsSelfConcordantBarrierOnWith
          (interior Q) ν F := by
      -- Rewrite the barrier domain once through the exact `WithLp` interior bridge.
      simpa [hQ_interior] using hF
    let γ : ℝ := 2 * (2 * n : ℝ) / ((2 * n : ℝ) - (ν : ℝ))
    have h2n_pos : 0 < (2 * n : ℝ) := by positivity
    have hden_pos : 0 < (2 * n : ℝ) - (ν : ℝ) := sub_pos.mpr hlt
    have hγ : 1 < γ := by
      -- Choosing `γ = 2 * (2n) / (2n - ν)` makes the final barrier lower bound exceed `ν`.
      rw [show γ = 2 * (2 * n : ℝ) / ((2 * n : ℝ) - (ν : ℝ)) by rfl]
      rw [one_lt_div hden_pos]
      nlinarith [h2n_pos, (show 0 ≤ (ν : ℝ) from ν.2)]
    let xBarRaw : Point := ((γ • (1 : SymmMat)), (γ • (1 : SymmMat)))
    let xBar : Z := WithLp.toLp 2 xBarRaw
    let p : Fin n ⊕ Fin n → Z := fun i ↦ WithLp.toLp 2 (coordinateDirection i)
    let β : Fin n ⊕ Fin n → ℝ := fun _ ↦ γ
    let α : Fin n ⊕ Fin n → ℝ := fun _ ↦ γ - 1
    have hxBar :
        xBar ∈ interior Q := by
      -- Transport the raw interior base point `(γ I, γ I)` to the `WithLp` barrier domain.
      rw [hQ_interior]
      simpa [xBar, xBarRaw] using
        (gamma_basepoint_mem_interior_matrixInverseEpigraph (n := n) hγ)
    have hrecession :
        ∀ i, ∀ ⦃x : Z⦄, x ∈ Q → ∀ t : ℝ, 0 ≤ t → x + t • p i ∈ Q := by
      intro i x hx t ht
      -- The source recession directions transport directly through `WithLp.ofLp`.
      have hxRaw : ofZ x ∈ matrixInverseEpigraph := by

end
