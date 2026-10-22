/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_18
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_8
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_9
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_15
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_5

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

section

variable {m n : ℕ}

local notation "𝕄" => Matrix (Fin m) (Fin n) ℝ
local notation "Mₘ" => Matrix (Fin m) (Fin m) ℝ
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "𝕍" => Fin (min m n) → ℝ

/-- The ambient real matrix space is equipped with its Frobenius norm. -/
local instance : NormedAddCommGroup 𝕄 := Matrix.frobeniusNormedAddCommGroup

/-- The ambient real matrix space is a normed real vector space. -/
local instance : NormedSpace ℝ 𝕄 := Matrix.frobeniusNormedSpace

/-- The ambient real matrix space is equipped with its Frobenius inner product. -/
local instance : InnerProductSpace ℝ 𝕄 := Matrix.frobeniusInnerProductSpace

/-- The singular-value coordinate space carries the standard Euclidean seminormed structure. -/
private abbrev vectorSeminormedAddCommGroup : SeminormedAddCommGroup 𝕍 :=
  (1 : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).toSeminormedAddCommGroup
    Matrix.PosDef.one.posSemidef

/-- The singular-value coordinate space carries the standard Euclidean normed structure. -/
private abbrev vectorNormedAddCommGroup : NormedAddCommGroup 𝕍 :=
  (1 : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).toNormedAddCommGroup Matrix.PosDef.one

local instance : SeminormedAddCommGroup 𝕍 := vectorSeminormedAddCommGroup
local instance : NormedAddCommGroup 𝕍 := vectorNormedAddCommGroup
local instance : Norm 𝕍 := vectorNormedAddCommGroup.toNorm
local instance : PseudoMetricSpace 𝕍 := vectorNormedAddCommGroup.toPseudoMetricSpace
local instance : MetricSpace 𝕍 := vectorNormedAddCommGroup.toMetricSpace
local instance : UniformSpace 𝕍 := vectorNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace
local instance : TopologicalSpace 𝕍 :=
  vectorNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The singular-value coordinate space carries the standard Euclidean inner product. -/
local instance : InnerProductSpace ℝ 𝕍 :=
  (1 : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).toInnerProductSpace
    Matrix.PosDef.one.posSemidef

/-- The singular-value coordinate space is locally compact in its Euclidean geometry. -/
local instance : LocallyCompactSpace 𝕍 :=
  LocallyCompactSpace.of_finiteDimensional_of_complete ℝ 𝕍

/-- The singular-value coordinate space is proper in its Euclidean geometry. -/
local instance : ProperSpace 𝕍 := ProperSpace.of_locallyCompactSpace ℝ

/-- The singular-value coordinate space is complete in its Euclidean geometry. -/
local instance : CompleteSpace 𝕍 := complete_of_proper

/-- The coordinatewise sign pattern attached to a singular-value vector. -/
def signPattern (x : Fin (min m n) → ℝ) : Fin (min m n) → ℝ :=
  fun i ↦ if x i < 0 then -1 else 1

/-- The sign pattern has absolute value `1` in every coordinate. -/
lemma abs_signPattern (x : Fin (min m n) → ℝ) (i : Fin (min m n)) :
    |signPattern x i| = 1 := by
  -- Each coordinate of the sign pattern is either `-1` or `1`.
  by_cases hxi : x i < 0
  · simp [signPattern, hxi]
  · simp [signPattern, hxi]

/-- Multiplying the sign pattern by the absolute value recovers the original coordinate. -/
lemma signPattern_mul_abs (x : Fin (min m n) → ℝ) (i : Fin (min m n)) :
    signPattern x i * |x i| = x i := by
  -- Split by the sign of the coordinate and simplify the absolute value accordingly.
  by_cases hxi : x i < 0
  · simp [signPattern, hxi, abs_of_neg hxi]
  · have hxi_nonneg : 0 ≤ x i := le_of_not_gt hxi
    simp [signPattern, hxi, abs_of_nonneg hxi_nonneg]

/-- The diagonal matrix of the sign pattern is orthogonal. -/
noncomputable def signDiagonalOrthogonal
    (x : Fin (min m n) → ℝ) : Matrix.orthogonalGroup (Fin (min m n)) ℝ := by
  let s : Fin (min m n) → ℝ := signPattern x
  have hsq : ∀ i : Fin (min m n), s i * s i = 1 := by
    intro i
    by_cases hxi : x i < 0
    · simp [s, signPattern, hxi]
    · simp [s, signPattern, hxi]
  refine ⟨Matrix.diagonal s, ?_⟩
  refine (Matrix.mem_orthogonalGroup_iff (A := Matrix.diagonal s) (R := ℝ)).2 ?_
  calc
    Matrix.diagonal s * (Matrix.diagonal s)ᵀ = Matrix.diagonal s * Matrix.diagonal s := by
      simp
    _ = Matrix.diagonal (fun i ↦ s i * s i) := by
      rw [Matrix.diagonal_mul_diagonal]
    _ = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hsq]
      · simp [hij]

/-- The sign orthogonal acts by coordinatewise multiplication. -/
lemma signDiagonalOrthogonal_mulVec
    (x z : Fin (min m n) → ℝ) :
    (((signDiagonalOrthogonal x : Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
        Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z =
      fun i ↦ signPattern x i * z i := by
  -- A diagonal matrix acts coordinatewise on vectors.
  ext i
  simp [signDiagonalOrthogonal, Matrix.mulVec_diagonal, signPattern]

/-- Helper for Proposition 7.5: moving an orthogonal transpose across a dot product is equivalent
to acting on the first vector by the orthogonal matrix. -/
private lemma dotProduct_transpose_mulVec_eq_dotProduct_smul
    (A : Matrix.orthogonalGroup (Fin (min m n)) ℝ)
    (y z : Fin (min m n) → ℝ) :
    dotProduct y
        ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).transpose.mulVec z) =
      dotProduct (A • y) z := by
  -- Rewrite the left pairing by moving the transpose to the first input.
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rfl

/-- Helper for Proposition 7.5: an orthogonal matrix followed by its transpose acts trivially on
the common singular-value coordinate space. -/
private lemma orthogonal_mulVec_transpose_mulVec
    (A : Matrix.orthogonalGroup (Fin (min m n)) ℝ)
    (z : Fin (min m n) → ℝ) :
    ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec
        ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).transpose.mulVec z) = z := by
  -- Collapse the matrix product to the identity by orthogonality.
  rw [Matrix.mulVec_mulVec]
  have hA :
      (A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ) *
          (A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff
      (A := (A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)) (R := ℝ)).1 A.2
  rw [hA, Matrix.one_mulVec]

/-- Helper for Proposition 7.5: an orthogonal matrix followed by its transpose acts trivially on
the common singular-value coordinate space. -/
private lemma proposition7_5_orthogonal_transpose_mulVec_mulVec
    (A : Matrix.orthogonalGroup (Fin (min m n)) ℝ) (x : Fin (min m n) → ℝ) :
    ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).transpose).mulVec
        ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).mulVec x) = x := by
  -- Collapse the transpose-after-action product to the identity.
  rw [Matrix.mulVec_mulVec]
  have hA :
      (A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).transpose *
          (A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin (min m n)) ℝ).1 A.2
  rw [hA, Matrix.one_mulVec]

/-- Helper for Proposition 7.5: orthogonal precomposition transports the conjugate witness range by
the matching change of variables. -/
private lemma conjugate_integrand_range_precompose_orthogonal_eq
    (A : Matrix.orthogonalGroup (Fin (min m n)) ℝ)
    (f : (Fin (min m n) → ℝ) → EReal)
    (y : Fin (min m n) → ℝ) :
    Set.range
        (fun x : Fin (min m n) → ℝ ↦
          (((dotProductEquiv ℝ (Fin (min m n)) y) x : ℝ) : EReal) - f (A • x)) =
      Set.range
        (fun z : Fin (min m n) → ℝ ↦
          (((dotProductEquiv ℝ (Fin (min m n)) (A • y)) z : ℝ) : EReal) - f z) := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨A • x, ?_⟩
    simp only
    have hAx : A • x = ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec x := rfl
    have hx :
        ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).transpose).mulVec (A • x) = x := by
      rw [hAx]
      exact proposition7_5_orthogonal_transpose_mulVec_mulVec A x
    have hdot :
        (((dotProductEquiv ℝ (Fin (min m n)) y)
            (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).transpose).mulVec
              (A • x)) : ℝ) : EReal) =
          (((dotProductEquiv ℝ (Fin (min m n)) (A • y)) (A • x) : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal))
        (dotProduct_transpose_mulVec_eq_dotProduct_smul A y (A • x))
    rw [← hdot, hx]
  · rintro ⟨z, rfl⟩
    refine ⟨((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).transpose).mulVec z, ?_⟩
    simp only
    have hz : A • (A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).transpose.mulVec z = z := by
      change ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec
          (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).transpose).mulVec z) = z
      exact orthogonal_mulVec_transpose_mulVec A z
    have hdot :
        (((dotProductEquiv ℝ (Fin (min m n)) y)
            ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ).transpose.mulVec z) : ℝ) :
            EReal) =
          (((dotProductEquiv ℝ (Fin (min m n)) (A • y)) z : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal))
        (dotProduct_transpose_mulVec_eq_dotProduct_smul A y z)
    rw [hdot, hz]

/-- Helper for Proposition 7.5: precomposing the primal profile by an orthogonal matrix transports
the Fenchel conjugate point by that same orthogonal action. -/
private lemma conjugate_function_precompose_orthogonal_eq
    (A : Matrix.orthogonalGroup (Fin (min m n)) ℝ)
    (f : (Fin (min m n) → ℝ) → EReal)
    (y : Fin (min m n) → ℝ) :
    conjugate_function (fun x : Fin (min m n) → ℝ ↦ f (A • x))
        (dotProductEquiv ℝ (Fin (min m n)) y) =
      conjugate_function f (dotProductEquiv ℝ (Fin (min m n)) (A • y)) := by
  -- Replace the defining supremum range by the orthogonal change of variables.
  rw [conjugate_function_apply, conjugate_function_apply,
    conjugate_integrand_range_precompose_orthogonal_eq]

/-- Extend the sign pattern by `1` outside the common diagonal block on the row index set. -/
def rectangularSignPattern
    (x : Fin (min m n) → ℝ) : Fin m → ℝ :=
  fun i ↦
    if h : i.1 < min m n then
      signPattern x ⟨i.1, h⟩
    else 1

/-- The rectangularly extended sign pattern defines an orthogonal row matrix. -/
noncomputable def rectangularSignOrthogonal
    (x : Fin (min m n) → ℝ) : Matrix.orthogonalGroup (Fin m) ℝ := by
  let s : Fin m → ℝ := rectangularSignPattern (m := m) (n := n) x
  have hsq : ∀ i : Fin m, s i * s i = 1 := by
    intro i
    by_cases hi : i.1 < min m n
    · have hcoord : signPattern x ⟨i.1, hi⟩ * signPattern x ⟨i.1, hi⟩ = 1 := by
        -- Coordinates inside the common block still have sign `±1`.
        by_cases hneg : x ⟨i.1, hi⟩ < 0
        · simp [signPattern, hneg]
        · simp [signPattern, hneg]
      simpa [s, rectangularSignPattern, hi] using hcoord
    · -- Outside the common block, the extension is the identity sign.
      simp [s, rectangularSignPattern, hi]
  refine ⟨Matrix.diagonal s, ?_⟩
  refine (Matrix.mem_orthogonalGroup_iff (A := Matrix.diagonal s) (R := ℝ)).2 ?_
  calc
    Matrix.diagonal s * (Matrix.diagonal s)ᵀ = Matrix.diagonal s * Matrix.diagonal s := by
      simp
    _ = Matrix.diagonal (fun i ↦ s i * s i) := by
      rw [Matrix.diagonal_mul_diagonal]
    _ = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hsq]
      · simp [hij]

/-- Extending the same permutation to the row and column index sets reindexes the rectangular
diagonal profile entrywise by the original permutation on the common diagonal block. -/
lemma rectangularDiagonalProfile_perm_extension_apply
    (σ : Equiv.Perm (Fin (min m n))) (z : Fin (min m n) → ℝ) (i : Fin m) (j : Fin n) :
    let σm : Equiv.Perm (Fin m) :=
      σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_left m n))
    let σn : Equiv.Perm (Fin n) :=
      σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_right m n))
    (orthogonalRectangularDiagonalProfileMap
        (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z) i j =
      if h : i.1 = j.1 then z (σ ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩) else 0 := by
  let σm : Equiv.Perm (Fin m) :=
    σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_left m n))
  let σn : Equiv.Perm (Fin n) :=
    σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_right m n))
  have hentry :
      (orthogonalRectangularDiagonalProfileMap
          (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z) i j =
        rectangularDiagonalProfile z (σm i) (σn j) := by
    have hleft :
        ∀ x : Fin n,
          ((((permutationOrthogonalMatrix σm : Matrix.orthogonalGroup (Fin m) ℝ) :
              Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile z) i x) =
            rectangularDiagonalProfile z (σm i) x := by
      intro x
      -- Left multiplication by the extended row permutation just reindexes the row coordinate.
      simpa [permutationOrthogonalMatrix] using
        (show ((σm.permMatrix ℝ * rectangularDiagonalProfile z) i x) =
            rectangularDiagonalProfile z (σm i) x by
          simp [Matrix.mul_apply])
    have htranspose :
        (((permutationOrthogonalMatrix σn : Matrix.orthogonalGroup (Fin n) ℝ) :
            Matrix (Fin n) (Fin n) ℝ)ᵀ) =
          ((σn⁻¹).permMatrix ℝ) := by
      -- The transpose of a permutation matrix is the permutation matrix of the inverse.
      rw [permutationOrthogonalMatrix]
      exact Matrix.transpose_permMatrix (R := ℝ) (σ := σn)
    have hright :=
      congrFun
        (Matrix.vecMul_permMatrix (R := ℝ) (σ := σn⁻¹)
          (v := fun x : Fin n ↦ rectangularDiagonalProfile z (σm i) x)) j
    -- After normalizing the transpose, the right multiplication is exactly the row action
    -- of the inverse permutation matrix.
    calc
      (orthogonalRectangularDiagonalProfileMap
          (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z) i j =
          ((fun x : Fin n ↦ rectangularDiagonalProfile z (σm i) x) ᵥ*
            ((σn⁻¹).permMatrix ℝ)) j := by
              rw [orthogonalRectangularDiagonalProfileMap_apply, Matrix.mul_apply, htranspose]
              simp_rw [hleft]
              rfl
      _ = rectangularDiagonalProfile z (σm i) (σn j) := by
            simpa [Matrix.vecMul, dotProduct] using hright
  have hmain :
      (orthogonalRectangularDiagonalProfileMap
          (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z) i j =
        if h : i.1 = j.1 then z (σ ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩) else 0 := by
    calc
      (orthogonalRectangularDiagonalProfileMap
          (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z) i j =
          rectangularDiagonalProfile z (σm i) (σn j) := hentry
      _ = if h : i.1 = j.1 then z (σ ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩) else 0 := by
            by_cases hij : i.1 = j.1
            · have hi : i.1 < min m n := Nat.lt_min.mpr ⟨i.2, hij ▸ j.2⟩
              have hj : j.1 < min m n := by
                simpa [hij] using hi
              let eL : Fin (min m n) ↪ Fin m := Fin.castLEEmb (Nat.min_le_left m n)
              let eR : Fin (min m n) ↪ Fin n := Fin.castLEEmb (Nat.min_le_right m n)
              have hσm : σm i = eL (σ ⟨i.1, hi⟩) := by
                have hi_cast : eL ⟨i.1, hi⟩ = i := by
                  ext
                  rfl
                -- Inside the common block, the row extension agrees with the original permutation.
                simpa [σm, eL, hi_cast] using
                  (Equiv.Perm.viaFintypeEmbedding_apply_image
                    (e := σ) (f := eL) ⟨i.1, hi⟩)
              have hσn : σn j = eR (σ ⟨j.1, hj⟩) := by
                have hj_cast : eR ⟨j.1, hj⟩ = j := by
                  ext
                  rfl
                -- Inside the common block, the column extension agrees with the same original
                -- permutation.
                simpa [σn, eR, hj_cast] using
                  (Equiv.Perm.viaFintypeEmbedding_apply_image
                    (e := σ) (f := eR) ⟨j.1, hj⟩)
              have hσn' : σn j = eR (σ ⟨i.1, hi⟩) := by
                simpa [hij] using hσn
              -- On the common diagonal block, both extensions hit the same permuted coordinate.
              rw [rectangularDiagonalProfile_apply]
              simp [eL, eR, hij, hσm, hσn']
            · by_cases hi : i.1 < min m n
              · by_cases hj : j.1 < min m n
                · let eL : Fin (min m n) ↪ Fin m := Fin.castLEEmb (Nat.min_le_left m n)
                  let eR : Fin (min m n) ↪ Fin n := Fin.castLEEmb (Nat.min_le_right m n)
                  have hσm : σm i = eL (σ ⟨i.1, hi⟩) := by
                    have hi_cast : eL ⟨i.1, hi⟩ = i := by
                      ext
                      rfl
                    -- Both indices lie in the common block, so each extension is again the
                    -- original permutation on that block.
                    simpa [σm, eL, hi_cast] using
                      (Equiv.Perm.viaFintypeEmbedding_apply_image
                        (e := σ) (f := eL) ⟨i.1, hi⟩)
                  have hσn : σn j = eR (σ ⟨j.1, hj⟩) := by
                    have hj_cast : eR ⟨j.1, hj⟩ = j := by
                      ext
                      rfl
                    simpa [σn, eR, hj_cast] using
                      (Equiv.Perm.viaFintypeEmbedding_apply_image
                        (e := σ) (f := eR) ⟨j.1, hj⟩)
                  have hNe : (σ ⟨i.1, hi⟩).1 ≠ (σ ⟨j.1, hj⟩).1 := by
                    intro hEq
                    apply hij
                    exact congrArg Fin.val (σ.injective (Fin.ext hEq))
                  -- Different diagonal coordinates remain different after applying the same
                  -- permutation.
                  rw [hσm, hσn, rectangularDiagonalProfile_apply]
                  simp [eL, eR, hNe, hij]
                · let eL : Fin (min m n) ↪ Fin m := Fin.castLEEmb (Nat.min_le_left m n)
                  let eR : Fin (min m n) ↪ Fin n := Fin.castLEEmb (Nat.min_le_right m n)
                  have hσm : σm i = eL (σ ⟨i.1, hi⟩) := by
                    have hi_cast : eL ⟨i.1, hi⟩ = i := by
                      ext
                      rfl
                    -- The row index is still in range, so the extension acts by `σ`.
                    simpa [σm, eL, hi_cast] using
                      (Equiv.Perm.viaFintypeEmbedding_apply_image
                        (e := σ) (f := eL) ⟨i.1, hi⟩)
                  have hσn : σn j = j := by
                    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
                    intro hjRange
                    rcases hjRange with ⟨a, ha⟩
                    have haj : a.1 = j.1 := by
                      simpa [eR] using congrArg Fin.val ha
                    exact hj (haj ▸ a.2)
                  have hNe : (σ ⟨i.1, hi⟩).1 ≠ j.1 := by
                    intro hEq
                    exact hj (hEq ▸ (σ ⟨i.1, hi⟩).2)
                  -- A common-block row cannot land on an out-of-range column index.
                  rw [hσm, hσn, rectangularDiagonalProfile_apply]
                  simp [eL, hNe, hij]
              · by_cases hj : j.1 < min m n
                · let eL : Fin (min m n) ↪ Fin m := Fin.castLEEmb (Nat.min_le_left m n)
                  let eR : Fin (min m n) ↪ Fin n := Fin.castLEEmb (Nat.min_le_right m n)
                  have hσm : σm i = i := by
                    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
                    intro hiRange
                    rcases hiRange with ⟨a, ha⟩
                    have hai : a.1 = i.1 := by
                      simpa [eL] using congrArg Fin.val ha
                    exact hi (hai ▸ a.2)
                  have hσn : σn j = eR (σ ⟨j.1, hj⟩) := by
                    have hj_cast : eR ⟨j.1, hj⟩ = j := by
                      ext
                      rfl
                    -- The column index is still in range, so the extension acts by `σ`.
                    simpa [σn, eR, hj_cast] using
                      (Equiv.Perm.viaFintypeEmbedding_apply_image
                        (e := σ) (f := eR) ⟨j.1, hj⟩)
                  have hNe : i.1 ≠ (σ ⟨j.1, hj⟩).1 := by
                    intro hEq
                    exact hi (hEq ▸ (σ ⟨j.1, hj⟩).2)
                  -- Symmetrically, an out-of-range row cannot meet a common-block column on the
                  -- diagonal.
                  rw [hσm, hσn, rectangularDiagonalProfile_apply]
                  simp [eR, hNe, hij]
                · let eL : Fin (min m n) ↪ Fin m := Fin.castLEEmb (Nat.min_le_left m n)
                  let eR : Fin (min m n) ↪ Fin n := Fin.castLEEmb (Nat.min_le_right m n)
                  have hσm : σm i = i := by
                    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
                    intro hiRange
                    rcases hiRange with ⟨a, ha⟩
                    have hai : a.1 = i.1 := by
                      simpa [eL] using congrArg Fin.val ha
                    exact hi (hai ▸ a.2)
                  have hσn : σn j = j := by
                    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
                    intro hjRange
                    rcases hjRange with ⟨a, ha⟩
                    have haj : a.1 = j.1 := by
                      simpa [eR] using congrArg Fin.val ha
                    exact hj (haj ▸ a.2)
                  -- Outside the common block, both extensions are the identity, so the
                  -- off-diagonal condition is unchanged.
                  rw [hσm, hσn, rectangularDiagonalProfile_apply]
                  simp [hij]
  simpa [σm, σn] using hmain

/-- Extending the same permutation to the row and column index sets reindexes the rectangular
diagonal profile by that permutation. -/
lemma rectangularDiagonalProfile_perm_extension_eq
    (σ : Equiv.Perm (Fin (min m n))) (z : Fin (min m n) → ℝ) :
    let σm : Equiv.Perm (Fin m) :=
      σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_left m n))
    let σn : Equiv.Perm (Fin n) :=
      σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_right m n))
    orthogonalRectangularDiagonalProfileMap
        (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z =
      rectangularDiagonalProfile (z ∘ σ) := by
  let σm : Equiv.Perm (Fin m) :=
    σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_left m n))
  let σn : Equiv.Perm (Fin n) :=
    σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_right m n))
  ext i j
  -- The explicit entrywise owner matches the defining formula of the reindexed diagonal profile.
  simpa [σm, σn, rectangularDiagonalProfile_apply] using
    rectangularDiagonalProfile_perm_extension_apply (m := m) (n := n) σ z i j

/-- The rectangularly extended sign matrix restores the signs of the diagonal profile while
leaving the column factor trivial. -/
lemma rectangularDiagonalProfile_left_sign_eq
    (x : Fin (min m n) → ℝ) :
    orthogonalRectangularDiagonalProfileMap (rectangularSignOrthogonal (m := m) (n := n) x) 1
        (fun i ↦ |x i|) =
      rectangularDiagonalProfile x := by
  -- Evaluate the row-sign orthogonal map entrywise and separate the diagonal and off-diagonal
  -- cases of the rectangular profile.
  ext i j
  by_cases hij : i.1 = j.1
  · have hj_m : j.1 < m := hij ▸ i.2
    -- On the common diagonal block, the sign matrix contributes exactly `signPattern x i`.
    simp [orthogonalRectangularDiagonalProfileMap_apply, rectangularDiagonalProfile_apply,
      rectangularSignOrthogonal, rectangularSignPattern, hij, hj_m, signPattern_mul_abs]
  · -- Off the common diagonal block, both the raw profile and its signed version vanish.
    simp [orthogonalRectangularDiagonalProfileMap_apply, rectangularDiagonalProfile_apply,
      rectangularSignOrthogonal, rectangularSignPattern, hij]

/-- The raw rectangular diagonal profile is an orthogonal image of the canonical sorted
absolute-value profile `|x|↓`. -/
lemma rectangularDiagonalProfile_eq_orthogonalRectangularDiagonalProfileMap_abs_descending
    (x : Fin (min m n) → ℝ) :
    ∃ U : Matrix.orthogonalGroup (Fin m) ℝ,
      ∃ V : Matrix.orthogonalGroup (Fin n) ℝ,
        rectangularDiagonalProfile x =
          orthogonalRectangularDiagonalProfileMap U V
            (Function.descendingRearrangement (fun i ↦ |x i|)) := by
  let τ : Equiv.Perm (Fin (min m n)) :=
    (Tuple.sort (fun i ↦ |x i|) * Fin.revPerm).symm
  let xdesc : Fin (min m n) → ℝ :=
    Function.descendingRearrangement (fun i ↦ |x i|)
  let σm : Equiv.Perm (Fin m) :=
    τ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_left m n))
  let σn : Equiv.Perm (Fin n) :=
    τ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_right m n))
  have hsort :
      permutationOrthogonalMatrix τ.symm • (fun i ↦ |x i|) = xdesc := by
    -- The concrete sorting permutation sends `|x|` to its decreasing rearrangement `|x|↓`.
    have hsort_tuple :
        permutationOrthogonalMatrix τ.symm • (fun i ↦ |x i|) =
          _root_.descendingRearrangement (fun i ↦ |x i|) := by
      simpa [τ] using
        (descendingRearrangement_eq_sort_perm_smul (fun i ↦ |x i|))
    dsimp [xdesc]
    rw [function_descendingRearrangement_eq_descendingRearrangement
      (m := m) (n := n) (x := fun i ↦ |x i|)]
    exact hsort_tuple
  have hτmul :
      permutationOrthogonalMatrix τ * permutationOrthogonalMatrix τ.symm =
        (1 : Matrix.orthogonalGroup (Fin (min m n)) ℝ) := by
    -- The inverse permutation cancels the sorting permutation inside the orthogonal group.
    apply Subtype.ext
    change τ.permMatrix ℝ * (τ⁻¹).permMatrix ℝ = 1
    calc
      τ.permMatrix ℝ * (τ⁻¹).permMatrix ℝ =
          (τ⁻¹ * τ).permMatrix ℝ :=
        (Matrix.permMatrix_mul (R := ℝ) (σ := τ⁻¹) (τ := τ)).symm
      _ = 1 := by simp
  have hunsort_smul :
      permutationOrthogonalMatrix τ • xdesc = (fun i ↦ |x i|) := by
    have happly :=
      congrArg
        (fun v : Fin (min m n) → ℝ ↦ permutationOrthogonalMatrix τ • v)
        hsort
    -- Applying the inverse sorting permutation recovers the original absolute values.
    calc
      permutationOrthogonalMatrix τ • xdesc =
          (permutationOrthogonalMatrix τ * permutationOrthogonalMatrix τ.symm) •
            (fun i ↦ |x i|) := by
              symm
              simpa [smul_smul] using happly
      _ = (1 : Matrix.orthogonalGroup (Fin (min m n)) ℝ) • (fun i ↦ |x i|) := by
            rw [hτmul]
      _ = (fun i ↦ |x i|) := by
            simp
  have hunsort :
      xdesc ∘ τ = (fun i ↦ |x i|) := by
    -- Rewriting the orthogonal action as coordinate permutation gives the desired vector identity.
    simpa [permutationOrthogonalMatrix_smul] using hunsort_smul
  have hperm :
      orthogonalRectangularDiagonalProfileMap
          (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) xdesc =
        rectangularDiagonalProfile (fun i ↦ |x i|) := by
    -- The common permutation on rows and columns turns the sorted profile into the raw absolute
    -- diagonal profile.
    simpa [σm, σn, hunsort] using
      (rectangularDiagonalProfile_perm_extension_eq (m := m) (n := n) τ xdesc)
  let U : Matrix.orthogonalGroup (Fin m) ℝ :=
    rectangularSignOrthogonal (m := m) (n := n) x * permutationOrthogonalMatrix σm
  let V : Matrix.orthogonalGroup (Fin n) ℝ := permutationOrthogonalMatrix σn
  refine ⟨U, V, ?_⟩
  -- Route correction: first unsort `|x|↓` to the raw absolute diagonal profile, then restore the
  -- original signs by the row-sign orthogonal.
  calc
    rectangularDiagonalProfile x =
        orthogonalRectangularDiagonalProfileMap
          (rectangularSignOrthogonal (m := m) (n := n) x) 1
          (fun i ↦ |x i|) := by
            symm
            exact rectangularDiagonalProfile_left_sign_eq (m := m) (n := n) x
    _ = orthogonalRectangularDiagonalProfileMap U V xdesc := by
          dsimp [U, V]
          rw [orthogonalRectangularDiagonalProfileMap_apply,
            orthogonalRectangularDiagonalProfileMap_apply]
          rw [orthogonalRectangularDiagonalProfileMap_apply] at hperm
          calc
            ((rectangularSignOrthogonal (m := m) (n := n) x :
                Matrix.orthogonalGroup (Fin m) ℝ) :
                Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile (fun i ↦ |x i|) *
                (((1 : Matrix.orthogonalGroup (Fin n) ℝ) :
                  Matrix (Fin n) (Fin n) ℝ)ᵀ) =
              ((rectangularSignOrthogonal (m := m) (n := n) x :
                  Matrix.orthogonalGroup (Fin m) ℝ) :
                  Matrix (Fin m) (Fin m) ℝ) *
                ((((permutationOrthogonalMatrix σm :
                    Matrix.orthogonalGroup (Fin m) ℝ) :
                    Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile xdesc) *
                  (((permutationOrthogonalMatrix σn :
                      Matrix.orthogonalGroup (Fin n) ℝ) :
                      Matrix (Fin n) (Fin n) ℝ)ᵀ)) := by
                rw [hperm]
                simp
            _ =
              ((rectangularSignOrthogonal (m := m) (n := n) x *
                  permutationOrthogonalMatrix σm :
                    Matrix.orthogonalGroup (Fin m) ℝ) :
                    Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile xdesc *
                  (((permutationOrthogonalMatrix σn :
                      Matrix.orthogonalGroup (Fin n) ℝ) :
                      Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
                simp [Matrix.mul_assoc]

/-- Every coordinate of the sorted absolute-value profile is nonnegative. -/
lemma descendingRearrangement_abs_nonneg
    (x : Fin (min m n) → ℝ) (i : Fin (min m n)) :
    0 ≤ Function.descendingRearrangement (fun j ↦ |x j|) i := by
  -- Every entry of the merge-sorted list of absolute values comes from an original absolute value.
  rw [Function.descendingRearrangement_apply]
  let L := (List.ofFn fun j : Fin (min m n) ↦ |x j|).mergeSort (· ≥ ·)
  have hiL : i.1 < L.length := by
    simpa [L] using i.2
  rw [show L.getD i 0 = L.get ⟨i.1, hiL⟩ by
    simpa [L] using (List.getD_eq_get L 0 ⟨i.1, hiL⟩)]
  have hmem_sorted : L.get ⟨i.1, hiL⟩ ∈ L := List.get_mem L ⟨i.1, hiL⟩
  have hmem_original : L.get ⟨i.1, hiL⟩ ∈ List.ofFn (fun j : Fin (min m n) ↦ |x j|) := by
    exact (List.mem_mergeSort).1 hmem_sorted
  rcases (List.mem_ofFn).1 hmem_original with ⟨j, hj⟩
  simpa [L, hj] using abs_nonneg (x j)

/-- The singular values of `rectangularDiagonalProfile x` are `|x|↓`. -/
lemma singular_value_function_rectangularDiagonalProfile_eq_abs_descendingRearrangement
    (x : Fin (min m n) → ℝ) :
    singular_value_function (rectangularDiagonalProfile x) =
      Function.descendingRearrangement (fun i ↦ |x i|) := by
  rcases
    rectangularDiagonalProfile_eq_orthogonalRectangularDiagonalProfileMap_abs_descending
      (m := m) (n := n) x with
    ⟨U, V, hUV⟩
  -- The orthogonal packaging reduces the singular values to the canonical sorted absolute profile.
  rw [hUV]
  simpa using
    singular_value_function_orthogonalRectangularDiagonalMap_eq_of_nonneg_antitone
      U V (Function.descendingRearrangement (fun i ↦ |x i|))
      (descendingRearrangement_abs_nonneg (m := m) (n := n) x)
      (antitone_function_descendingRearrangement (m := m) (n := n) (fun i ↦ |x i|))

/-- If an orthogonal precomposition preserves the canonical absolute-sorted representative `|x|↓`,
then an absolutely permutation symmetric function is invariant under that precomposition. -/
lemma absolutelySymmetric_precompose_eq_of_preserves_abs_descendingRearrangement
    (f : (Fin (min m n) → ℝ) → EReal) (hf : Function.IsAbsolutelyPermutationSymmetric f)
    (A : Matrix.orthogonalGroup (Fin (min m n)) ℝ)
    (hA :
      ∀ z : Fin (min m n) → ℝ,
        Function.descendingRearrangement
            (fun i ↦
              |(((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i|) =
          Function.descendingRearrangement (fun i ↦ |z i|)) :
    (fun z : Fin (min m n) → ℝ ↦
      f (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z)) = f := by
  ext z
  -- Replace both inputs by the same canonical representative `|z|↓`.
  calc
    f (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) =
        f (Function.descendingRearrangement
          (fun i ↦ |(((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i|)) :=
      hf.map_eq_abs_descendingRearrangement
        (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z)
    _ = f (Function.descendingRearrangement (fun i ↦ |z i|)) := by
          rw [hA z]
    _ = f z := (hf.map_eq_abs_descendingRearrangement z).symm

/-- Pulling the conjugate back along `dotProductEquiv` preserves absolute permutation symmetry. -/
lemma dotProduct_conjugate_profile_is_absolutely_permutation_symmetric
    (f : (Fin (min m n) → ℝ) → EReal) (hf : Function.IsAbsolutelyPermutationSymmetric f)
    (hfconv : is_convex_function f) :
    Function.IsAbsolutelyPermutationSymmetric
      (fun x : Fin (min m n) → ℝ ↦
        conjugate_function f (dotProductEquiv ℝ (Fin (min m n)) x)) := by
  let hproper : IsProperExtendedRealFunction f := ⟨hf.ne_bot, hf.effective_domain_nonempty⟩
  let hconj := isProperExtendedRealFunction_conjugate_function f hproper hfconv
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_
      map_eq_abs_descendingRearrangement := ?_ }
  · intro x
    -- Properness of the conjugate profile transports through `dotProductEquiv`.
    exact hconj.ne_bot (dotProductEquiv ℝ (Fin (min m n)) x)
  · rcases hconj.effective_domain_nonempty with ⟨y, hy⟩
    refine ⟨(dotProductEquiv ℝ (Fin (min m n))).symm y, ?_⟩
    have hdual :
        dotProductEquiv ℝ (Fin (min m n))
            ((dotProductEquiv ℝ (Fin (min m n))).symm y) = y :=
      (dotProductEquiv ℝ (Fin (min m n))).apply_symm_apply y
    -- The effective-domain witness pulls back through the linear equivalence unchanged.
    simpa [hdual] using hy
  · intro x
    let σ : Equiv.Perm (Fin (min m n)) :=
      (Tuple.sort (fun i ↦ |x i|) * Fin.revPerm).symm
    let A : Matrix.orthogonalGroup (Fin (min m n)) ℝ :=
      signDiagonalOrthogonal x * permutationOrthogonalMatrix σ
    let xdesc : Fin (min m n) → ℝ :=
      Function.descendingRearrangement (fun i ↦ |x i|)
    have hperm :
        (((permutationOrthogonalMatrix σ :
            Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
            Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc =
          (fun i ↦ |x i|) := by
      have hsort :
          permutationOrthogonalMatrix σ.symm • (fun i ↦ |x i|) = xdesc := by
        -- The concrete sorting permutation sends `|x|` to its decreasing rearrangement `|x|↓`.
        rw [show xdesc = Function.descendingRearrangement (fun i ↦ |x i|) by rfl]
        rw [function_descendingRearrangement_eq_descendingRearrangement
            (x := fun i ↦ |x i|)]
        simpa [σ] using
          (descendingRearrangement_eq_sort_perm_smul (fun i ↦ |x i|))
      have hperm_smul :
          permutationOrthogonalMatrix σ • xdesc = (fun i ↦ |x i|) := by
        -- Applying the inverse permutation to the sorted profile recovers the original absolute
        -- values.
        have happly :=
          congrArg
            (fun v : Fin (min m n) → ℝ ↦ permutationOrthogonalMatrix σ • v)
            hsort
        have hσmul :
            permutationOrthogonalMatrix σ * permutationOrthogonalMatrix σ.symm =
              (1 : Matrix.orthogonalGroup (Fin (min m n)) ℝ) := by
          apply Subtype.ext
          -- The inverse permutation matrix cancels the original one inside the orthogonal group.
          change σ.permMatrix ℝ * (σ⁻¹).permMatrix ℝ = 1
          calc
            σ.permMatrix ℝ * (σ⁻¹).permMatrix ℝ =
                (σ⁻¹ * σ).permMatrix ℝ :=
              (Matrix.permMatrix_mul (R := ℝ) (σ := σ⁻¹) (τ := σ)).symm
            _ = 1 := by simp
        calc
          permutationOrthogonalMatrix σ • xdesc =
              (permutationOrthogonalMatrix σ * permutationOrthogonalMatrix σ.symm) •
                (fun i ↦ |x i|) := by
                  symm
                  simpa [smul_smul] using happly
          _ = (1 : Matrix.orthogonalGroup (Fin (min m n)) ℝ) • (fun i ↦ |x i|) := by
                rw [hσmul]
          _ = (fun i ↦ |x i|) := by
                simp
      simpa using hperm_smul
    have hA_to_x :
        ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc = x := by
      -- Route correction: first unsort `|x|↓` to `|x|`, then restore the signs coordinatewise.
      calc
        ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc =
            ((signDiagonalOrthogonal x :
              Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
              Matrix (Fin (min m n)) (Fin (min m n)) ℝ).mulVec
                ((((permutationOrthogonalMatrix σ :
                  Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
                  Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc) := by
                  simp [A, Matrix.mulVec_mulVec]
        _ = ((signDiagonalOrthogonal x :
              Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
              Matrix (Fin (min m n)) (Fin (min m n)) ℝ).mulVec (fun i ↦ |x i|) := by
                rw [hperm]
        _ = x := by
              ext i
              rw [signDiagonalOrthogonal_mulVec]
              exact signPattern_mul_abs x i
    have hA_preserves :
        ∀ z : Fin (min m n) → ℝ,
          Function.descendingRearrangement
              (fun i ↦
                |(((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i|) =
            Function.descendingRearrangement (fun i ↦ |z i|) := by
      intro z
      have hAz :
          ∀ i,
            (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i =
              signPattern x i * z (σ i) := by
        intro i
        -- Split the action into the sign diagonal followed by the inverse sorting permutation.
        calc
          (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i =
              (((signDiagonalOrthogonal x :
                Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
                Matrix (Fin (min m n)) (Fin (min m n)) ℝ).mulVec
                  ((((permutationOrthogonalMatrix σ :
                    Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
                    Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z)) i := by
                    simp [A, Matrix.mulVec_mulVec]
          _ = signPattern x i *
                ((((permutationOrthogonalMatrix σ :
                  Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
                  Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i := by
                  rw [signDiagonalOrthogonal_mulVec]
          _ = signPattern x i * z (σ i) := by
                calc
                  signPattern x i *
                      ((((permutationOrthogonalMatrix σ :
                        Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
                        Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i =
                      signPattern x i * ((z ∘ σ) i) := by
                        congr 1
                        simpa [permutationOrthogonalMatrix] using
                          congrFun (Matrix.permMatrix_mulVec (R := ℝ) (σ := σ) (v := z)) i
                  _ = signPattern x i * z (σ i) := by
                        rfl
      have habs :
          (fun i ↦ |(((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i|) =
            (fun i ↦ |z i|) ∘ σ := by
        ext i
        rw [hAz i, abs_mul, abs_signPattern]
        simp
      -- Absolute values remove the sign diagonal, and permutations preserve decreasing
      -- rearrangement.
      rw [habs]
      rw [function_descendingRearrangement_eq_descendingRearrangement
          (((fun i ↦ |z i|) ∘ σ))]
      rw [function_descendingRearrangement_eq_descendingRearrangement
          (fun i ↦ |z i|)]
      exact descendingRearrangement_comp_perm (x := fun i ↦ |z i|) σ
    have hpre :
        (fun z : Fin (min m n) → ℝ ↦
          f (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z)) = f :=
      absolutelySymmetric_precompose_eq_of_preserves_abs_descendingRearrangement
        f hf A hA_preserves
    have hconj_transport :
        conjugate_function
            (fun z : Fin (min m n) → ℝ ↦
              f (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z))
            (dotProductEquiv ℝ (Fin (min m n)) xdesc) =
          conjugate_function f
            (dotProductEquiv ℝ (Fin (min m n))
              (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc)) := by
      -- The Chapter 7 conjugate transport theorem matches the explicit `mulVec` presentation.
      change conjugate_function (fun z : Fin (min m n) → ℝ ↦ f (A • z))
          (dotProductEquiv ℝ (Fin (min m n)) xdesc) =
        conjugate_function f
          (dotProductEquiv ℝ (Fin (min m n)) (A • xdesc))
      exact conjugate_function_precompose_orthogonal_eq A f xdesc
    -- The conjugate at `x` is the conjugate at `|x|↓` after the corresponding signed
    -- permutation.
    calc
      conjugate_function f (dotProductEquiv ℝ (Fin (min m n)) x) =
          conjugate_function f
            (dotProductEquiv ℝ (Fin (min m n))
              (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc)) := by
                rw [hA_to_x]
      _ = conjugate_function
            (fun z : Fin (min m n) → ℝ ↦
              f (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z))
            (dotProductEquiv ℝ (Fin (min m n)) xdesc) := by
              symm
              exact hconj_transport
      _ = conjugate_function f (dotProductEquiv ℝ (Fin (min m n)) xdesc) := by
            rw [hpre]

/-- Helper for Proposition 7.5: taking the `dotProductEquiv`-pullback conjugate twice recovers the
Chapter 4 biconjugate of the vector profile. -/
private lemma dotProduct_conjugate_profile_biconjugate_eq
    (f : (Fin (min m n) → ℝ) → EReal) :
    (fun x : Fin (min m n) → ℝ ↦
      conjugate_function
        (fun z : Fin (min m n) → ℝ ↦
          conjugate_function f (dotProductEquiv ℝ (Fin (min m n)) z))
        (dotProductEquiv ℝ (Fin (min m n)) x)) =
      biconjugate_function f := by
  funext x
  -- Compare the two defining suprema by transporting witnesses through `dotProductEquiv`.
  rw [conjugate_function_apply, biconjugate_function_apply]
  congr 1
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨dotProductEquiv ℝ (Fin (min m n)) z, ?_⟩
    simp [dotProduct_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨(dotProductEquiv ℝ (Fin (min m n))).symm y, ?_⟩
    have hdual :
        dotProductEquiv ℝ (Fin (min m n))
            ((dotProductEquiv ℝ (Fin (min m n))).symm y) = y :=
      (dotProductEquiv ℝ (Fin (min m n))).apply_symm_apply y
    have hpair' :
        (dotProductEquiv ℝ (Fin (min m n))
            ((dotProductEquiv ℝ (Fin (min m n))).symm y)) x = y x := by
      exact congrArg (fun ψ : Module.Dual ℝ (Fin (min m n) → ℝ) => ψ x) hdual
    have hpair :
        dotProduct x ((dotProductEquiv ℝ (Fin (min m n))).symm y) = y x := by
      simpa [dotProductEquiv, dotProduct_comm] using hpair'
    simp [hdual, hpair]

/- Proposition 7.5 is `source-facing`: the textbook defines
`T = {Y : ℝ^(m × n) | σ(Y) ∈ C}` and expresses the projection formula through the chapter's
projection owner `P[...]` together with the singular-value SVD data of `X`. The canonical matrix
reconstruction owner already present in the project is
`orthogonalRectangularDiagonalMap U V`. -/

/-- The rectangular diagonal matrix with diagonal entries `x` and off-diagonal entries `0`. -/
def rectangularDiagonal (x : Fin (min m n) → ℝ) : 𝕄 :=
  fun i j ↦
    if h : i.1 = j.1 then
      x ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩
    else 0

-- Proof sketch: unfold `rectangularDiagonal`; its `(i,j)` entry is the corresponding coordinate
-- of `x` when the row and column indices agree, and `0` otherwise.
/-- Evaluating `rectangularDiagonal x` returns the corresponding diagonal entry of `x` on the
common diagonal and `0` away from it. -/
theorem rectangularDiagonal_apply (x : Fin (min m n) → ℝ) (i : Fin m) (j : Fin n) :
    rectangularDiagonal x i j =
      if h : i.1 = j.1 then
        x ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩
      else 0 := by
  rfl

/-- The orthogonal image of the rectangular diagonal matrix with diagonal `x`. -/
def orthogonalRectangularDiagonalMap
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Fin (min m n) → ℝ) → 𝕄 :=
  fun x ↦
    (U : Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonal x *
      ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)

-- Proof sketch: unfold `orthogonalRectangularDiagonalMap`; evaluation at `x` is definitionally
-- the product `U * rectangularDiagonal x * Vᵀ`.
/-- Evaluating `orthogonalRectangularDiagonalMap U V` at `x` yields
`U * rectangularDiagonal x * Vᵀ`. -/
@[simp] theorem orthogonalRectangularDiagonalMap_apply
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : Fin (min m n) → ℝ) :
    orthogonalRectangularDiagonalMap U V x =
      (U : Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonal x *
        ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
  rfl

/-- The rectangular spectral set associated with `C` consists of the real `m × n` matrices whose
ordered singular-value vector lies in `C`. -/
def rectangularSpectralSet (C : Set (Fin (min m n) → ℝ)) : Set 𝕄 :=
  singular_value_function ⁻¹' C

/-- The rectangular spectral set is the preimage of `C` under `singular_value_function`. -/
theorem rectangularSpectralSet_eq_preimage (C : Set (Fin (min m n) → ℝ)) :
    rectangularSpectralSet C = singular_value_function ⁻¹' C := by
  rfl

-- Proof sketch: unfold `rectangularSpectralSet`; membership is exactly the condition that the
-- ordered singular-value vector of `Y` lies in `C`.
/-- A matrix belongs to `rectangularSpectralSet C` exactly when its ordered singular-value vector
lies in `C`. -/
theorem mem_rectangularSpectralSet_iff {C : Set (Fin (min m n) → ℝ)} {Y : 𝕄} :
    Y ∈ rectangularSpectralSet C ↔ singular_value_function Y ∈ C := by
  rfl

/-- Helper for Proposition 7.5: the local rectangular diagonal owner agrees with the earlier
Chapter 7 rectangular profile owner. -/
lemma rectangularDiagonal_eq_profile (x : Fin (min m n) → ℝ) :
    rectangularDiagonal x = rectangularDiagonalProfile x := by
  -- Both rectangular diagonal owners are defined by the same entrywise formula.
  rfl

/-- Helper for Proposition 7.5: the local orthogonal rectangular diagonal owner agrees with the
earlier Chapter 7 profile-map owner. -/
lemma orthogonalRectangularDiagonalMap_eq_profileMap
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : Fin (min m n) → ℝ) :
    orthogonalRectangularDiagonalMap U V x =
      orthogonalRectangularDiagonalProfileMap U V x := by
  -- Rewrite the local owner through the already-proved profile-map API.
  rw [orthogonalRectangularDiagonalMap_apply,
    orthogonalRectangularDiagonalProfileMap_apply, rectangularDiagonal_eq_profile]

/-- Helper for Proposition 7.5: absolute permutation symmetry sends every member of `C` to its
canonical representative `|z|↓`, so the sorted absolute-value profile stays in `C`. -/
lemma descendingAbs_mem_of_mem
    (C : Set (Fin (min m n) → ℝ))
    (hC_abs : Function.IsAbsolutelyPermutationSymmetric (extendedIndicator C))
    {z : Fin (min m n) → ℝ} (hz : z ∈ C) :
    Function.descendingRearrangement (fun i ↦ |z i|) ∈ C := by
  -- Rewrite the indicator value through the symmetry normal form `z ↦ |z|↓`.
  have hmap :
      extendedIndicator C z =
        extendedIndicator C (Function.descendingRearrangement (fun i ↦ |z i|)) :=
    hC_abs.map_eq_abs_descendingRearrangement z
  have hz_zero : extendedIndicator C z = 0 := by
    simp [extendedIndicator, hz]
  have hdesc_zero :
      extendedIndicator C (Function.descendingRearrangement (fun i ↦ |z i|)) = 0 := by
    rw [← hmap, hz_zero]
  by_contra hdesc
  simp [extendedIndicator, hdesc] at hdesc_zero

/-- Helper for Proposition 7.5: a closed convex absolutely permutation-symmetric profile has a
closed convex rectangular spectral lift. -/
lemma absolutelySymmetricSpectralClosedConvexForward
    (f : (Fin (min m n) → ℝ) → EReal)
    (hf : Function.IsAbsolutelyPermutationSymmetric f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    LowerSemicontinuous (f ∘ singular_value_function) ∧
      is_convex_function (f ∘ singular_value_function) := by
  let fconj : (Fin (min m n) → ℝ) → EReal :=
    fun x ↦ conjugate_function f (dotProductEquiv ℝ (Fin (min m n)) x)
  have hfconj_symm : Function.IsAbsolutelyPermutationSymmetric fconj :=
    dotProduct_conjugate_profile_is_absolutely_permutation_symmetric f hf hf_convex
  have hmatrix_conj :
      (fun Y : 𝕄 ↦ conjugate_function (f ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)) =
        fconj ∘ singular_value_function := by
    -- The first spectral conjugate formula identifies the matrix conjugate with the vector one.
    simpa [fconj, Function.comp] using matrix_spectral_conjugate_formula f hf
  have hmatrix_conj_conj :
      (fun Y : 𝕄 ↦ conjugate_function (fconj ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)) =
        (fun x : Fin (min m n) → ℝ ↦
          conjugate_function fconj (dotProductEquiv ℝ (Fin (min m n)) x)) ∘
          singular_value_function := by
    -- Apply the same spectral formula once more to the conjugate profile.
    simpa [Function.comp] using matrix_spectral_conjugate_formula fconj hfconj_symm
  have hproper : IsProperExtendedRealFunction f := ⟨hf.ne_bot, hf.effective_domain_nonempty⟩
  have hself : biconjugate_function f = f :=
    biconjugate_function_eq_self_of_proper_closed_convex f hproper hf_closed hf_convex
  have hmatrix_self :
      (fun Y : 𝕄 ↦ conjugate_function (fconj ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)) =
        f ∘ singular_value_function := by
    -- The second conjugation turns the vector profile into its Chapter 4 biconjugate.
    calc
      (fun Y : 𝕄 ↦ conjugate_function (fconj ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)) =
          (fun x : Fin (min m n) → ℝ ↦
            conjugate_function fconj (dotProductEquiv ℝ (Fin (min m n)) x)) ∘
            singular_value_function := hmatrix_conj_conj
      _ = biconjugate_function f ∘ singular_value_function := by
            rw [dotProduct_conjugate_profile_biconjugate_eq f]
      _ = f ∘ singular_value_function := by
            rw [hself]
  let G : 𝕄 → EReal :=
    fun Y ↦ conjugate_function (f ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)
  have hdouble : G∗ = f ∘ singular_value_function := by
    -- Rewrite the primal conjugate of `G` through the stabilized matrix-side biconjugate route.
    funext Y
    calc
      (G∗) Y = conjugate_function G ↑(toDualMap ℝ 𝕄 Y) := by
        rw [conjugate_function_primal_apply]
      _ = f (singular_value_function Y) := by
        exact congrFun
          (show (fun Y : 𝕄 ↦ conjugate_function G ↑(toDualMap ℝ 𝕄 Y)) =
              f ∘ singular_value_function by
            calc
              (fun Y : 𝕄 ↦ conjugate_function G ↑(toDualMap ℝ 𝕄 Y)) =
                  (fun Y : 𝕄 ↦
                    conjugate_function (fconj ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)) := by
                      simp [G, hmatrix_conj]
              _ = f ∘ singular_value_function := hmatrix_self) Y
  have hclosedconv := conjugate_function_closed_and_convex G
  -- The double conjugate is exactly the spectral lift.
  rw [hdouble] at hclosedconv
  exact hclosedconv

/-- Helper for Proposition 7.5: if `δ_C` is absolutely permutation symmetric and `C` is closed
and convex, then the associated rectangular spectral set is convex. -/
lemma convex_rectangularSpectralSet_of_absSymm_closed_convex
    (C : Set (Fin (min m n) → ℝ))
    (hC_abs : Function.IsAbsolutelyPermutationSymmetric (extendedIndicator C))
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    Convex ℝ (rectangularSpectralSet C) :=
by
  -- Route correction: instead of reproving spectral convexity from scratch, apply the Chapter 7
  -- closed/convex transfer theorem to the indicator lift and then read back its effective domain.
  have hlift_closed_convex :
      LowerSemicontinuous (extendedIndicator C ∘ singular_value_function) ∧
        is_convex_function (extendedIndicator C ∘ singular_value_function) :=
    absolutelySymmetricSpectralClosedConvexForward (f := extendedIndicator C) hC_abs
      ((extendedIndicator_lowerSemicontinuous_iff_isClosed C).2 hC_closed)
      (extendedIndicator_isConvexFunction_of_convex C hC_convex)
  have hdom_convex :
      Convex ℝ (effective_domain (extendedIndicator C ∘ singular_value_function)) :=
    effective_domain_convex_of_is_convex_function hlift_closed_convex.2
  have hdom_eq :
      effective_domain (extendedIndicator C ∘ singular_value_function) =
        rectangularSpectralSet C := by
    ext Y
    by_cases hY : singular_value_function Y ∈ C
    · simp [rectangularSpectralSet, effective_domain, Function.comp, extendedIndicator, hY]
    · simp [rectangularSpectralSet, effective_domain, Function.comp, extendedIndicator, hY]
  rw [← hdom_eq]
  exact hdom_convex

/-- Helper for Proposition 7.5: transporting a rectangular diagonal model by fixed left/right
orthogonal changes of coordinates only changes the orthogonal factors. -/
lemma orthogonal_transport_orthogonalRectangularDiagonalMap_eq
    (U U1 : Matrix.orthogonalGroup (Fin m) ℝ)
    (V V1 : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : Fin (min m n) → ℝ) :
    ((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U1 V1 x * (V : Mₙ) =
      orthogonalRectangularDiagonalMap (U⁻¹ * U1) (V⁻¹ * V1) x := by
  let U' : Matrix.orthogonalGroup (Fin m) ℝ := U⁻¹ * U1
  let V' : Matrix.orthogonalGroup (Fin n) ℝ := V⁻¹ * V1
  -- Normalize the transported rectangular SVD coordinates once at the owner level.
  calc
    ((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U1 V1 x * (V : Mₙ)
        = ((U : Mₘ)ᵀ) * (((U1 : Mₘ) * rectangularDiagonal x * ((V1 : Mₙ)ᵀ))) * (V : Mₙ) := by
            rw [orthogonalRectangularDiagonalMap_apply]
    _ = ((U : Mₘ)ᵀ) * ((((U1 : Mₘ) * rectangularDiagonal x * ((V1 : Mₙ)ᵀ))) * (V : Mₙ)) := by
          simpa using
            Matrix.mul_assoc ((U : Mₘ)ᵀ)
              (((U1 : Mₘ) * rectangularDiagonal x * ((V1 : Mₙ)ᵀ))) (V : Mₙ)
    _ = (U : Mₘ)ᵀ * (((U1 : Mₘ) * rectangularDiagonal x) * (((V1 : Mₙ)ᵀ) * (V : Mₙ))) := by
          simpa [mul_assoc] using
            congrArg
              (fun M : Matrix (Fin m) (Fin n) ℝ ↦ (U : Mₘ)ᵀ * M)
              (Matrix.mul_assoc ((U1 : Mₘ) * rectangularDiagonal x) ((V1 : Mₙ)ᵀ) (V : Mₙ))
    _ = (U : Mₘ)ᵀ * ((U1 : Mₘ) * (rectangularDiagonal x * (((V1 : Mₙ)ᵀ) * (V : Mₙ)))) := by
          exact congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ (U : Mₘ)ᵀ * M)
            (Matrix.mul_assoc (U1 : Mₘ) (rectangularDiagonal x) (((V1 : Mₙ)ᵀ) * (V : Mₙ)))
    _ = ((U : Mₘ)ᵀ * (U1 : Mₘ)) * (rectangularDiagonal x * (((V1 : Mₙ)ᵀ) * (V : Mₙ))) := by
          exact (Matrix.mul_assoc (U : Mₘ)ᵀ (U1 : Mₘ)
            (rectangularDiagonal x * (((V1 : Mₙ)ᵀ) * (V : Mₙ)))).symm
    _ = (((U : Mₘ)ᵀ * (U1 : Mₘ)) * rectangularDiagonal x) * (((V1 : Mₙ)ᵀ) * (V : Mₙ)) := by
          exact (Matrix.mul_assoc ((U : Mₘ)ᵀ * (U1 : Mₘ)) (rectangularDiagonal x)
            (((V1 : Mₙ)ᵀ) * (V : Mₙ))).symm
    _ = (U' : Mₘ) * rectangularDiagonal x * ((V' : Mₙ)ᵀ) := by
          simp [U', V', Matrix.star_eq_conjTranspose,
            Matrix.conjTranspose_eq_transpose_of_trivial]
    _ = orthogonalRectangularDiagonalMap U' V' x := by
          rw [orthogonalRectangularDiagonalMap_apply]

/-- Helper for Proposition 7.5: conjugating the orthogonal rectangular diagonal model back by the
same orthogonal factors recovers the bare rectangular diagonal matrix. -/
lemma orthogonal_conjugate_orthogonalRectangularDiagonalMap_eq_rectangularDiagonal
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : Fin (min m n) → ℝ) :
    ((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U V x * (V : Mₙ) =
      rectangularDiagonal x := by
  -- Specialize the transport identity to the same left/right factors.
  simpa [orthogonalRectangularDiagonalMap_apply] using
    orthogonal_transport_orthogonalRectangularDiagonalMap_eq
      (U := U) (U1 := U) (V := V) (V1 := V) x

/-- Helper for Proposition 7.5: orthogonal transport on the left and right preserves the
singular-value profile of a rectangular matrix. -/
lemma singular_value_function_orthogonal_rectangular_eq
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (Z : 𝕄) :
    singular_value_function (((U : Mₘ)ᵀ) * Z * (V : Mₙ)) = singular_value_function Z := by
  obtain ⟨U1, V1, hZ⟩ :=
    exists_orthogonal_rectangular_diagonalization_with_singular_value_function Z
  have htransport :
      ((U : Mₘ)ᵀ) * Z * (V : Mₙ) =
        orthogonalRectangularDiagonalMap (U⁻¹ * U1) (V⁻¹ * V1) (singular_value_function Z) := by
    -- Rewrite the transported matrix by the ordered singular-value decomposition of `Z`.
    calc
      ((U : Mₘ)ᵀ) * Z * (V : Mₙ)
          = ((U : Mₘ)ᵀ) *
              orthogonalRectangularDiagonalProfileMap U1 V1 (singular_value_function Z) *
              (V : Mₙ) := by
                simpa using
                  congrArg
                    (fun M : 𝕄 ↦ ((U : Mₘ)ᵀ) * M * (V : Mₙ))
                    hZ
      _ = ((U : Mₘ)ᵀ) *
            orthogonalRectangularDiagonalMap U1 V1 (singular_value_function Z) *
            (V : Mₙ) := by
              simpa using
                congrArg
                  (fun M : 𝕄 ↦ ((U : Mₘ)ᵀ) * M * (V : Mₙ))
                  (orthogonalRectangularDiagonalMap_eq_profileMap U1 V1
                    (singular_value_function Z)).symm
      _ = orthogonalRectangularDiagonalMap (U⁻¹ * U1) (V⁻¹ * V1) (singular_value_function Z) := by
            exact orthogonal_transport_orthogonalRectangularDiagonalMap_eq
              (U := U) (U1 := U1) (V := V) (V1 := V1) (singular_value_function Z)
  -- The transported matrix remains an orthogonal image of the same sorted singular-value vector.
  rw [htransport, orthogonalRectangularDiagonalMap_eq_profileMap]
  exact singular_value_function_orthogonalRectangularDiagonalMap_eq_of_nonneg_antitone
    (U⁻¹ * U1) (V⁻¹ * V1) (singular_value_function Z)
    (singular_value_function_nonneg Z) (singular_value_function_antitone Z)

/-- Helper for Proposition 7.5: the orthogonal rectangular diagonal reconstruction has singular
values `|z|↓`. -/
lemma singularValueFunction_orthogonalRectangularDiagonalMap_eq_absDescending
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (z : Fin (min m n) → ℝ) :
    singular_value_function (orthogonalRectangularDiagonalMap U V z) =
      Function.descendingRearrangement (fun i ↦ |z i|) := by
  -- Route correction: normalize once to the bare diagonal model, then use the canonical Chapter 7
  -- formula `σ(dg(z)) = |z|↓` instead of rebuilding the sign/permutation argument locally.
  calc
    singular_value_function (orthogonalRectangularDiagonalMap U V z)
      =
        singular_value_function
          (((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U V z * (V : Mₙ)) := by
          symm
          exact singular_value_function_orthogonal_rectangular_eq U V
            (orthogonalRectangularDiagonalMap U V z)
    _ = singular_value_function (rectangularDiagonal z) := by
          rw [orthogonal_conjugate_orthogonalRectangularDiagonalMap_eq_rectangularDiagonal]
    _ = Function.descendingRearrangement (fun i ↦ |z i|) := by
          simpa [rectangularDiagonal_eq_profile] using
            (singular_value_function_rectangularDiagonalProfile_eq_abs_descendingRearrangement
              (m := m) (n := n) z)

/-- Helper for Proposition 7.5: the Frobenius norm is invariant under left/right orthogonal
transport of a rectangular matrix. -/
lemma frobenius_norm_orthogonal_rectangular_eq
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (A : 𝕄) :
    ‖((U : Mₘ)ᵀ) * A * (V : Mₙ)‖ = ‖A‖ := by
  have hUUt : (U : Mₘ) * (U : Mₘ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (U : Mₘ)) (R := ℝ)).1 U.2
  have hVUt : (V : Mₙ) * (V : Mₙ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (V : Mₙ)) (R := ℝ)).1 V.2
  -- Rewrite both norms through the trace of the corresponding Gram matrices.
  rw [frobenius_norm_eq_sqrt_trace_transpose_mul, frobenius_norm_eq_sqrt_trace_transpose_mul]
  congr 1
  calc
    Matrix.trace ((((U : Mₘ)ᵀ * A * (V : Mₙ))ᵀ) * ((U : Mₘ)ᵀ * A * (V : Mₙ)))
      = Matrix.trace ((V : Mₙ)ᵀ * (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) * (V : Mₙ)) := by
            have hinner :
                (U : Mₘ) * ((U : Mₘ)ᵀ * A * (V : Mₙ)) =
                  (((U : Mₘ) * (U : Mₘ)ᵀ) * A) * (V : Mₙ) := by
              calc
                (U : Mₘ) * ((U : Mₘ)ᵀ * A * (V : Mₙ))
                    = (U : Mₘ) * (((U : Mₘ)ᵀ * A) * (V : Mₙ)) := by
                        rfl
                _ = ((U : Mₘ) * ((U : Mₘ)ᵀ * A)) * (V : Mₙ) := by
                      exact (Matrix.mul_assoc (U : Mₘ) ((U : Mₘ)ᵀ * A) (V : Mₙ)).symm
                _ = (((U : Mₘ) * (U : Mₘ)ᵀ) * A) * (V : Mₙ) := by
                      exact congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ M * (V : Mₙ))
                        (Matrix.mul_assoc (U : Mₘ) (U : Mₘ)ᵀ A).symm
            have hmat :
                (V : Mₙ)ᵀ * (Aᵀ * (U : Mₘ)) * ((U : Mₘ)ᵀ * A * (V : Mₙ)) =
                  (V : Mₙ)ᵀ * (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) * (V : Mₙ) := by
              calc
                (V : Mₙ)ᵀ * (Aᵀ * (U : Mₘ)) * ((U : Mₘ)ᵀ * A * (V : Mₙ))
                    = (((V : Mₙ)ᵀ * Aᵀ) * (U : Mₘ)) * ((U : Mₘ)ᵀ * A * (V : Mₙ)) := by
                        exact congrArg
                          (fun M : Matrix (Fin n) (Fin m) ℝ ↦ M * ((U : Mₘ)ᵀ * A * (V : Mₙ)))
                          (Matrix.mul_assoc (V : Mₙ)ᵀ Aᵀ (U : Mₘ)).symm
                _ = ((V : Mₙ)ᵀ * Aᵀ) * ((U : Mₘ) * ((U : Mₘ)ᵀ * A * (V : Mₙ))) := by
                      exact Matrix.mul_assoc ((V : Mₙ)ᵀ * Aᵀ) (U : Mₘ)
                        ((U : Mₘ)ᵀ * A * (V : Mₙ))
                _ = ((V : Mₙ)ᵀ * Aᵀ) * ((((U : Mₘ) * (U : Mₘ)ᵀ) * A) * (V : Mₙ)) := by
                      exact congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ ((V : Mₙ)ᵀ * Aᵀ) * M)
                        hinner
                _ = (((V : Mₙ)ᵀ * Aᵀ) * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) * (V : Mₙ) := by
                      exact (Matrix.mul_assoc ((V : Mₙ)ᵀ * Aᵀ) (((U : Mₘ) * (U : Mₘ)ᵀ) * A)
                        (V : Mₙ)).symm
                _ = (V : Mₙ)ᵀ * (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) * (V : Mₙ) := by
                      exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M * (V : Mₙ))
                        (Matrix.mul_assoc (V : Mₙ)ᵀ Aᵀ (((U : Mₘ) * (U : Mₘ)ᵀ) * A))
            simpa [Matrix.transpose_mul, mul_assoc] using congrArg Matrix.trace hmat
    _ = Matrix.trace ((V : Mₙ) * (V : Mₙ)ᵀ * (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A))) := by
          exact Matrix.trace_mul_cycle ((V : Mₙ)ᵀ)
            (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) (V : Mₙ)
    _ = Matrix.trace (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) := by
          rw [hVUt]
          simp
    _ = Matrix.trace (Aᵀ * A) := by
          have hleft : ((U : Mₘ) * (U : Mₘ)ᵀ) * A = A := by
            rw [hUUt]
            simp
          simp [hleft]

/-- Helper for Proposition 7.5: the trace of the Gram matrix of a rectangular diagonal matrix is
the sum of the squares of its diagonal entries. -/
lemma rectangularDiagonal_trace_sum_sq (x : Fin (min m n) → ℝ) :
    Matrix.trace ((rectangularDiagonal x)ᵀ * rectangularDiagonal x) = ∑ i, x i ^ 2 := by
  let f : ℕ → ℝ := fun j ↦ if h : j < min m n then x ⟨j, h⟩ ^ 2 else 0
  -- Rewrite through the profile owner and split the trace into the active diagonal block.
  rw [rectangularDiagonal_eq_profile]
  have hgram :
      (rectangularDiagonalProfile x)ᵀ * rectangularDiagonalProfile x =
        Matrix.diagonal (fun j : Fin n ↦ if h : j.1 < min m n then x ⟨j.1, h⟩ ^ 2 else 0) := by
    simpa using rectangularDiagonalProfile_conjTranspose_mul_eq_squared_tail
      (m := m) (n := n) x
  rw [hgram, Matrix.trace_diagonal]
  have hmin : min m n ≤ n := Nat.min_le_right _ _
  have hhead :
      (∑ j ∈ Finset.range (min m n), f j) = ∑ i : Fin (min m n), x i ^ 2 := by
    have hfin : (∑ i : Fin (min m n), f i) = ∑ i : Fin (min m n), x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      show f i = x i ^ 2
      dsimp [f]
      rw [if_pos i.2]
    calc
      (∑ j ∈ Finset.range (min m n), f j) = ∑ i : Fin (min m n), f i := by
        exact (Fin.sum_univ_eq_sum_range f (min m n)).symm
      _ = ∑ i : Fin (min m n), x i ^ 2 := hfin
  have htail :
      (∑ j ∈ Finset.Ico (min m n) n, f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : ¬ j < min m n := by
      exact not_lt_of_ge (Finset.mem_Ico.mp hj).1
    change (if h : j < min m n then x ⟨j, h⟩ ^ 2 else 0) = 0
    simpa [f] using
      (dif_neg hj' :
        (if h : j < min m n then x ⟨j, h⟩ ^ 2 else 0) = 0)
  calc
    (∑ i : Fin n, if h : i.1 < min m n then x ⟨i.1, h⟩ ^ 2 else 0)
      = ∑ j ∈ Finset.range n, f j := by
          exact Fin.sum_univ_eq_sum_range f n
    _ = (∑ j ∈ Finset.range (min m n), f j) + (∑ j ∈ Finset.Ico (min m n) n, f j) := by
          symm
          exact Finset.sum_range_add_sum_Ico _ hmin
    _ = ∑ i : Fin (min m n), x i ^ 2 := by
          rw [hhead, htail, add_zero]

/-- Helper for Proposition 7.5: the Frobenius norm of a rectangular diagonal matrix is the
ambient `ℓ²` norm of its diagonal profile. -/
lemma frobenius_norm_rectangularDiagonal_eq
    (x : Fin (min m n) → ℝ) :
    ‖rectangularDiagonal x‖ = ‖x‖ := by
  -- Rewrite both norms to the same square-root-of-sum-of-squares normal form.
  rw [frobenius_norm_eq_sqrt_trace_transpose_mul, rectangularDiagonal_trace_sum_sq]
  have hxnorm :
      ‖x‖ = √(∑ i, x i ^ (2 : ℕ)) := by
    simpa [dotProduct, Matrix.one_mulVec, pow_two] using
      norm_eq_sqrt_dotProduct_mulVec_of_posDef
        (1 : Matrix (Fin (min m n)) (Fin (min m n)) ℝ) Matrix.PosDef.one x
  simpa using hxnorm.symm

/-- Helper for Proposition 7.5: the Frobenius distance between two rectangular diagonal matrices
matches the ambient `ℓ²` distance between their diagonal profiles. -/
lemma frobenius_norm_rectangularDiagonal_sub_eq
    (x y : Fin (min m n) → ℝ) :
    ‖rectangularDiagonal x - rectangularDiagonal y‖ = ‖x - y‖ := by
  -- The rectangular diagonal owner is entrywise linear in its vector input.
  rw [← frobenius_norm_rectangularDiagonal_eq (x := x - y)]
  congr 1
  ext i j
  by_cases h : i.1 = j.1
  · simp [rectangularDiagonal_apply, h, sub_eq_add_neg]
  · simp [rectangularDiagonal_apply, h, sub_eq_add_neg]

/-- Helper for Proposition 7.5: keeping the orthogonal singular-vector factors fixed turns matrix
distance into vector distance on the diagonal profile. -/
lemma orthogonalRectangularDiagonal_distance_eq
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (x y : Fin (min m n) → ℝ) :
    ‖orthogonalRectangularDiagonalMap U V x - orthogonalRectangularDiagonalMap U V y‖ =
      ‖x - y‖ := by
  have hconj :
      ((U : Mₘ)ᵀ) *
          (orthogonalRectangularDiagonalMap U V x - orthogonalRectangularDiagonalMap U V y) *
          (V : Mₙ) =
        rectangularDiagonal x - rectangularDiagonal y := by
    -- Conjugate the difference termwise back to the diagonal model.
    calc
      ((U : Mₘ)ᵀ) *
          (orthogonalRectangularDiagonalMap U V x - orthogonalRectangularDiagonalMap U V y) *
          (V : Mₙ)
          = (((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U V x -
              ((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U V y) *
              (V : Mₙ) := by
                rw [Matrix.mul_sub]
      _ = ((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U V x * (V : Mₙ) -
            ((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U V y * (V : Mₙ) := by
              rw [Matrix.sub_mul]
      _ = rectangularDiagonal x - rectangularDiagonal y := by
            rw [orthogonal_conjugate_orthogonalRectangularDiagonalMap_eq_rectangularDiagonal,
              orthogonal_conjugate_orthogonalRectangularDiagonalMap_eq_rectangularDiagonal]
  -- Orthogonal transport preserves the Frobenius norm, so only the diagonal difference remains.
  calc
    ‖orthogonalRectangularDiagonalMap U V x - orthogonalRectangularDiagonalMap U V y‖
        = ‖((U : Mₘ)ᵀ) *
            (orthogonalRectangularDiagonalMap U V x - orthogonalRectangularDiagonalMap U V y) *
            (V : Mₙ)‖ := by
              symm
              exact frobenius_norm_orthogonal_rectangular_eq U V
                (orthogonalRectangularDiagonalMap U V x - orthogonalRectangularDiagonalMap U V y)
    _ = ‖rectangularDiagonal x - rectangularDiagonal y‖ := by rw [hconj]
    _ = ‖x - y‖ := frobenius_norm_rectangularDiagonal_sub_eq x y

/-- Helper for Proposition 7.5: the singular-value map is `1`-Lipschitz from the Frobenius norm
to the ambient `ℓ²` norm. -/
lemma singularValueDistance_le_frobeniusDistance
    (W X : 𝕄) :
    ‖singular_value_function W - singular_value_function X‖ ≤ ‖W - X‖ := by
  let σW : Fin (min m n) → ℝ := singular_value_function W
  let σX : Fin (min m n) → ℝ := singular_value_function X
  let wE : EuclideanSpace ℝ (Fin (min m n)) := WithLp.toLp (p := (2 : ENNReal)) σW
  let xE : EuclideanSpace ℝ (Fin (min m n)) := WithLp.toLp (p := (2 : ENNReal)) σX
  have hwE_inner : ⟪wE, wE⟫_ℝ = dotProduct σW σW := by
    simpa only [wE] using EuclideanSpace.inner_toLp_toLp σW σW
  have hσW_sq : ‖wE‖ ^ (2 : ℕ) = dotProduct σW σW := by
    calc
      ‖wE‖ ^ (2 : ℕ) = ⟪wE, wE⟫_ℝ := by
            exact (real_inner_self_eq_norm_sq wE).symm
      _ = dotProduct σW σW := hwE_inner
  have hxE_inner : ⟪xE, xE⟫_ℝ = dotProduct σX σX := by
    simpa only [xE] using EuclideanSpace.inner_toLp_toLp σX σX
  have hσX_sq : ‖xE‖ ^ (2 : ℕ) = dotProduct σX σX := by
    calc
      ‖xE‖ ^ (2 : ℕ) = ⟪xE, xE⟫_ℝ := by
            exact (real_inner_self_eq_norm_sq xE).symm
      _ = dotProduct σX σX := hxE_inner
  have hσ_inner : ⟪wE, xE⟫_ℝ = dotProduct σW σX := by
    simpa [wE, xE, dotProduct_comm] using EuclideanSpace.inner_toLp_toLp σW σX
  have hσ_norm :
      ‖(WithLp.toLp (p := (2 : ENNReal)) (σW - σX) :
          EuclideanSpace ℝ (Fin (min m n)))‖ = ‖σW - σX‖ := by
    have hfun_norm :
        ‖σW - σX‖ = √(∑ i, (σW i - σX i) ^ (2 : ℕ)) := by
      simpa [dotProduct, Matrix.one_mulVec, pow_two] using
        norm_eq_sqrt_dotProduct_mulVec_of_posDef
          (1 : Matrix (Fin (min m n)) (Fin (min m n)) ℝ) Matrix.PosDef.one (σW - σX)
    have hEuclid_norm :
        ‖(WithLp.toLp (p := (2 : ENNReal)) (σW - σX) :
            EuclideanSpace ℝ (Fin (min m n)))‖ =
          √(∑ i, (σW i - σX i) ^ (2 : ℕ)) := by
      simpa [pow_two] using
        euclideanSpace_norm_eq_sqrt_sum_sq
          (WithLp.toLp (p := (2 : ENNReal)) (σW - σX))
    exact hEuclid_norm.trans hfun_norm.symm
  have hleft :
      ‖singular_value_function W - singular_value_function X‖ ^ (2 : ℕ) =
        dotProduct σW σW - 2 * dotProduct σW σX + dotProduct σX σX := by
    -- Rewrite the vector norm squared through the Euclidean `toLp` owner.
    calc
      ‖singular_value_function W - singular_value_function X‖ ^ (2 : ℕ)
          = ‖(WithLp.toLp (p := (2 : ENNReal)) (σW - σX) :
              EuclideanSpace ℝ (Fin (min m n)))‖ ^ (2 : ℕ) := by
                rw [hσ_norm]
      _ = ‖wE - xE‖ ^ (2 : ℕ) := by simp [wE, xE, WithLp.toLp_sub]
      _ = ‖wE‖ ^ (2 : ℕ) - 2 * ⟪wE, xE⟫_ℝ + ‖xE‖ ^ (2 : ℕ) := norm_sub_sq_real wE xE
      _ = dotProduct σW σW - 2 * dotProduct σW σX + dotProduct σX σX := by
            rw [hσW_sq, hσ_inner, hσX_sq]
  have hW_sq : ‖W‖ ^ (2 : ℕ) = Matrix.trace (Wᵀ * W) := by
    rw [frobenius_norm_eq_sqrt_trace_transpose_mul]
    have hnonneg :
        0 ≤ Matrix.trace (Wᵀ * W) := by
      rw [trace_transpose_mul_eq_dotProduct_singular_value_function]
      exact Finset.sum_nonneg fun i hi ↦ mul_self_nonneg (singular_value_function W i)
    exact Real.sq_sqrt hnonneg
  have hX_sq : ‖X‖ ^ (2 : ℕ) = Matrix.trace (Xᵀ * X) := by
    rw [frobenius_norm_eq_sqrt_trace_transpose_mul]
    have hnonneg :
        0 ≤ Matrix.trace (Xᵀ * X) := by
      rw [trace_transpose_mul_eq_dotProduct_singular_value_function]
      exact Finset.sum_nonneg fun i hi ↦ mul_self_nonneg (singular_value_function X i)
    exact Real.sq_sqrt hnonneg
  have hWX_inner : ⟪W, X⟫_ℝ = Matrix.trace (Wᵀ * X) := by
    rw [real_inner_comm]
    simpa using toDualMap_apply_eq_trace_transpose_mul (X := W) (Y := X)
  have hright :
      ‖W - X‖ ^ (2 : ℕ) =
        Matrix.trace (Wᵀ * W) - 2 * Matrix.trace (Wᵀ * X) + Matrix.trace (Xᵀ * X) := by
    -- Rewrite the matrix norm squared through the Frobenius inner product.
    calc
      ‖W - X‖ ^ (2 : ℕ) = ‖W‖ ^ (2 : ℕ) - 2 * ⟪W, X⟫_ℝ + ‖X‖ ^ (2 : ℕ) := by
            exact norm_sub_sq_real W X
      _ = Matrix.trace (Wᵀ * W) - 2 * Matrix.trace (Wᵀ * X) + Matrix.trace (Xᵀ * X) := by
            rw [hW_sq, hWX_inner, hX_sq]
  have hvn : Matrix.trace (Wᵀ * X) ≤ dotProduct σW σX := by
    simpa [σW, σX] using von_neumann_trace_inequality W X
  have htraceW : Matrix.trace (Wᵀ * W) = dotProduct σW σW := by
    simpa [σW] using trace_transpose_mul_eq_dotProduct_singular_value_function W
  have htraceX : Matrix.trace (Xᵀ * X) = dotProduct σX σX := by
    simpa [σX] using trace_transpose_mul_eq_dotProduct_singular_value_function X
  have hsq :
      ‖singular_value_function W - singular_value_function X‖ ^ (2 : ℕ) ≤ ‖W - X‖ ^ (2 : ℕ) := by
    rw [hleft, hright, htraceW, htraceX]
    nlinarith [hvn]
  have hsq' :
      ‖σW - σX‖ ^ 2 ≤ ‖W - X‖ ^ 2 := by
    simpa [pow_two] using hsq
  have hfinal : ‖σW - σX‖ ≤ ‖W - X‖ := by
    nlinarith [hsq', norm_nonneg (σW - σX), norm_nonneg (W - X)]
  simpa [σW, σX] using hfinal

-- Proof sketch: let `T := rectangularSpectralSet C`. The projection-indicator identity rewrites
-- `P[T] X` and `P[C] (σ(X))` as proximal sets of the indicator functions `δ_T` and `δ_C`. The
-- rectangular spectral proximal formula applies once `extendedIndicator C` is absolutely
-- permutation symmetric; using the singular value decomposition
-- `X = U * rectangularDiagonal (σ(X)) * Vᵀ`, rewrite the resulting proximal identity back in
-- terms of projection mappings.
/-- Proposition 7.5: if `C ⊆ ℝ^(min(m,n))` is nonempty, closed, and convex and its indicator
function is absolutely permutation symmetric, then the projection
set of a real `m × n` matrix `X` onto the rectangular spectral set
`T = {Y | σ(Y) ∈ C}` is obtained by applying the same orthogonal singular-vector factors from a
singular value decomposition `X = U * rectangularDiagonal (σ(X)) * Vᵀ` to the projection set of
the singular-value vector `σ(X)` onto `C`. This is the chapter's set-valued rendering of the
textbook identity `P_T(X) = U dg(P_C(σ(X))) Vᵀ`. -/
theorem projection_mapping_rectangularSpectralSet_eq_image_projection_mapping_singular_values
    (C : Set (Fin (min m n) → ℝ))
    (hC_abs : Function.IsAbsolutelyPermutationSymmetric (extendedIndicator C))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (X : 𝕄) (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (hsvd : X = orthogonalRectangularDiagonalMap U V (singular_value_function X)) :
    P[rectangularSpectralSet C] X =
      orthogonalRectangularDiagonalMap U V '' P[C] (singular_value_function X) := by
  let σ : Fin (min m n) → ℝ := singular_value_function X
  let T : Set 𝕄 := rectangularSpectralSet C
  have hT_convex : Convex ℝ T :=
    convex_rectangularSpectralSet_of_absSymm_closed_convex C hC_abs hC_closed hC_convex
  obtain ⟨z, hz_proj⟩ :=
    projection_mapping_nonempty_of_nonempty_isClosed C hC_nonempty hC_closed σ
  let Y0 : 𝕄 := orthogonalRectangularDiagonalMap U V z
  have hz_mem : z ∈ C := mem_of_mem_projection_mapping hz_proj
  have hY0_memT : Y0 ∈ T := by
    -- The witness shares the same singular vectors as `X`, and its singular values are `|z|↓`.
    rw [mem_rectangularSpectralSet_iff]
    have hdesc_mem :
        Function.descendingRearrangement (fun i ↦ |z i|) ∈ C :=
      descendingAbs_mem_of_mem C hC_abs hz_mem
    have hσY0 :
        singular_value_function Y0 =
          Function.descendingRearrangement (fun i ↦ |z i|) := by
      simpa [Y0] using
        singularValueFunction_orthogonalRectangularDiagonalMap_eq_absDescending
          (U := U) (V := V) (z := z)
    rw [hσY0]
    exact hdesc_mem
  have hY0_proj : Y0 ∈ P[T] X := by
    rw [mem_projection_mapping_iff]
    refine ⟨hY0_memT, ?_⟩
    rw [isMinOn_iff]
    intro W hW
    have hσW_mem : singular_value_function W ∈ C := (mem_rectangularSpectralSet_iff.mp hW)
    have hz_min :
        ‖z - σ‖ ≤ ‖singular_value_function W - σ‖ := by
      exact (isMinOn_iff.mp (mem_projection_mapping_iff.mp hz_proj).2)
        (singular_value_function W) hσW_mem
    have hσW_le :
        ‖singular_value_function W - σ‖ ≤ ‖W - X‖ :=
      singularValueDistance_le_frobeniusDistance W X
    -- Compare any matrix competitor with the lifted vector projection witness.
    calc
      ‖Y0 - X‖ = ‖z - σ‖ := by
        dsimp [Y0]
        rw [hsvd]
        exact orthogonalRectangularDiagonal_distance_eq (U := U) (V := V) z σ
      _ ≤ ‖singular_value_function W - σ‖ := hz_min
      _ ≤ ‖W - X‖ := hσW_le
  have hY0_image : Y0 ∈ orthogonalRectangularDiagonalMap U V '' P[C] σ := by
    exact ⟨z, hz_proj, rfl⟩
  have hproj_left_subs : (P[T] X).Subsingleton :=
    projection_mapping_subsingleton T hT_convex X
  have hproj_right_subs : (orthogonalRectangularDiagonalMap U V '' P[C] σ).Subsingleton := by
    intro Y1 hY1 Y2 hY2
    rcases hY1 with ⟨z1, hz1, rfl⟩
    rcases hY2 with ⟨z2, hz2, rfl⟩
    have hz12 : z1 = z2 :=
      (projection_mapping_subsingleton C hC_convex σ) hz1 hz2
    simp [hz12]
  -- Each set is a subsingleton containing the same witness `Y0`, so they coincide.
  ext Y
  constructor
  · intro hY
    have hYY0 : Y = Y0 := hproj_left_subs hY hY0_proj
    simpa [hYY0] using hY0_image
  · intro hY
    have hYY0 : Y = Y0 := hproj_right_subs hY hY0_image
    simpa [hYY0] using hY0_proj

end
