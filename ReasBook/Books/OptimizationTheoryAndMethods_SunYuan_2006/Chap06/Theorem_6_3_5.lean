/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Theorem_6_3_3
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

open scoped BigOperators
open scoped ThirdOrderTensor

section

variable {n p : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Tensor3" => ThirdOrderTensor n

-- Semantic recall: Chapter 6 already owns the source-facing third-order tensor API through
-- `ThirdOrderTensor`, `⟪u, v, w⟫₃`, `ThirdOrderTensor.mulVecVec`,
-- `ThirdOrderTensor.fullFrobeniusNorm`,
-- and `tensorLeastNormFeasibleSet`. This file adds only the symmetric third-order interpolation
-- surface for Theorem 6.3.5.

namespace ThirdOrderTensor

/-- A symmetric third-order tensor is invariant under permuting its three coordinate indices. -/
def IsSymmetric (T : ThirdOrderTensor n) : Prop :=
  ∀ σ : Equiv.Perm (Fin 3), ∀ i : Fin 3 → Fin n,
    T (i (σ 0)) (i (σ 1)) (i (σ 2)) = T (i 0) (i 1) (i 2)

/-- Helper for `ThirdOrderTensor.IsSymmetric`: the two adjacent coordinate symmetries imply
invariance under each generator `Equiv.swap t.castSucc t.succ` of `Perm (Fin 3)`. -/
lemma adjacentSwapInvariant
    (T : ThirdOrderTensor n)
    (h01 : ∀ i j k, T i j k = T j i k)
    (h12 : ∀ i j k, T i j k = T i k j)
    (t : Fin 2) (idx : Fin 3 → Fin n) :
    T (idx ((Equiv.swap t.castSucc t.succ) 0))
      (idx ((Equiv.swap t.castSucc t.succ) 1))
      (idx ((Equiv.swap t.castSucc t.succ) 2)) =
      T (idx 0) (idx 1) (idx 2) := by
  -- Each generator is one of the two adjacent swaps, so `fin_cases` reduces to the
  -- corresponding hypothesis immediately.
  fin_cases t
  · simpa [Equiv.swap_apply_def] using (h01 (idx 0) (idx 1) (idx 2)).symm
  · simpa [Equiv.swap_apply_def] using (h12 (idx 0) (idx 1) (idx 2)).symm

/-- Helper for `ThirdOrderTensor.IsSymmetric`: permutation invariance is closed under
multiplication in `Perm (Fin 3)`. -/
lemma permInvariantMul
    (T : ThirdOrderTensor n)
    {σ τ : Equiv.Perm (Fin 3)}
    (hσ : ∀ idx : Fin 3 → Fin n,
      T (idx (σ 0)) (idx (σ 1)) (idx (σ 2)) = T (idx 0) (idx 1) (idx 2))
    (hτ : ∀ idx : Fin 3 → Fin n,
      T (idx (τ 0)) (idx (τ 1)) (idx (τ 2)) = T (idx 0) (idx 1) (idx 2)) :
    ∀ idx : Fin 3 → Fin n,
      T (idx ((σ * τ) 0)) (idx ((σ * τ) 1)) (idx ((σ * τ) 2)) =
        T (idx 0) (idx 1) (idx 2) := by
  intro idx
  -- Apply invariance under the right factor to the reindexed coordinates, then under the left.
  calc
    T (idx ((σ * τ) 0)) (idx ((σ * τ) 1)) (idx ((σ * τ) 2))
        = T ((idx ∘ σ) (τ 0)) ((idx ∘ σ) (τ 1)) ((idx ∘ σ) (τ 2)) := by
            simp [Equiv.Perm.mul_apply, Function.comp_apply]
    _ = T ((idx ∘ σ) 0) ((idx ∘ σ) 1) ((idx ∘ σ) 2) := hτ (idx ∘ σ)
    _ = T (idx (σ 0)) (idx (σ 1)) (idx (σ 2)) := rfl
    _ = T (idx 0) (idx 1) (idx 2) := hσ idx

/-- Helper for `ThirdOrderTensor.IsSymmetric`: the two adjacent transpositions already generate
full permutation invariance. -/
lemma isSymmetricOfAdjacentTranspositions
    (T : ThirdOrderTensor n)
    (h01 : ∀ i j k, T i j k = T j i k)
    (h12 : ∀ i j k, T i j k = T i k j) :
    T.IsSymmetric := by
  let generators : Set (Equiv.Perm (Fin 3)) :=
    Set.range fun t : Fin 2 ↦ Equiv.swap t.castSucc t.succ
  intro σ idx
  have hgen :
      σ ∈ Submonoid.closure generators := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ 2]
    simp
  have hclosure :
      ∀ τ ∈ Submonoid.closure generators,
        ∀ idx : Fin 3 → Fin n,
          T (idx (τ 0)) (idx (τ 1)) (idx (τ 2)) = T (idx 0) (idx 1) (idx 2) := by
    intro τ hτ
    exact
      (Submonoid.closure_induction
        (fun υ hυ idx ↦ by
          rcases hυ with ⟨t, rfl⟩
          exact adjacentSwapInvariant T h01 h12 t idx)
        (by
          intro idx
          rfl)
        (fun υ ρ hυ hρ hυinv hρinv idx ↦ permInvariantMul T hυinv hρinv idx)
        hτ : ∀ idx : Fin 3 → Fin n,
          T (idx (τ 0)) (idx (τ 1)) (idx (τ 2)) = T (idx 0) (idx 1) (idx 2))
  -- The adjacent swaps generate the whole permutation group, and the invariance predicate is
  -- closed under those generators, the identity, and multiplication.
  exact hclosure σ hgen idx

/-- Symmetry can be checked on the adjacent transpositions generating `Perm (Fin 3)`. -/
theorem isSymmetric_iff_adjacent_transpositions
    (T : ThirdOrderTensor n) :
    T.IsSymmetric ↔
      (∀ i j k, T i j k = T j i k) ∧
        ∀ i j k, T i j k = T i k j := by
  constructor
  · intro hsymm
    -- Read off the two adjacent swaps directly from the full permutation-invariance axiom.
    refine ⟨?_, ?_⟩
    · intro i j k
      simpa [Equiv.swap_apply_def] using (hsymm (Equiv.swap 0 1) ![i, j, k]).symm
    · intro i j k
      simpa [Equiv.swap_apply_def] using (hsymm (Equiv.swap 1 2) ![i, j, k]).symm
  · intro h
    -- The adjacent swaps generate `Perm (Fin 3)`, so the closure argument applies.
    rcases h with ⟨h01, h12⟩
    exact isSymmetricOfAdjacentTranspositions T h01 h12

end ThirdOrderTensor

/-- Helper for Chapter06 Theorem 6.3.5: `mulVecVec` is compatible with scalar multiplication in
the tensor argument. -/
lemma tensorSmul_mulVecVec
    (c : ℝ) (T : Tensor3) (v w : Point) :
    (c • T).mulVecVec v w = c • T.mulVecVec v w := by
  -- The tensor contraction is coordinatewise linear, so the scalar factor pulls through each
  -- coordinate sum.
  ext i
  simp [ThirdOrderTensor.mulVecVec_apply_eq_sum, mul_assoc, Finset.mul_sum]

/-- Helper for Chapter06 Theorem 6.3.5: the source full-coordinate Frobenius norm agrees with the
norm of the flattened tensor owner used in the orthogonality argument. -/
lemma thirdOrderTensorFullFrobeniusNorm_eq_flatten_norm (T : Tensor3) :
    T.fullFrobeniusNorm = ‖ThirdOrderTensor.flatten T‖ :=
  ThirdOrderTensor.fullFrobeniusNorm_eq_flatten_norm T

/-- Helper for Chapter06 Theorem 6.3.5: if the flattened tensor is zero, then all tensor
coordinates vanish. -/
lemma tensor_eq_zero_of_flatten_eq_zero
    {T : Tensor3} (hT : ThirdOrderTensor.flatten T = 0) :
    T = 0 := by
  -- Evaluate the flattened equality on each nested coordinate to recover the original entries.
  ext i j k
  have hcoord :=
    congrArg (fun U : ThirdOrderTensor.Flattened n ↦ ((U.ofLp i).ofLp j).ofLp k) hT
  simpa [tensorFlatten_apply] using hcoord

/-- The symmetrized third-order tensor
`∑ k, (b k ⊗ s k ⊗ s k + s k ⊗ b k ⊗ s k + s k ⊗ s k ⊗ b k)`. -/
def symmetricThirdTensorCombination (s b : Fin p → Point) : Tensor3 :=
  ∑ k, (⟪b k, s k, s k⟫₃ + ⟪s k, b k, s k⟫₃ + ⟪s k, s k, b k⟫₃)

/-- The tensor `symmetricThirdTensorCombination s b` is symmetric in its three indices. -/
theorem symmetricThirdTensorCombination_isSymmetric
    (s b : Fin p → Point) :
    (symmetricThirdTensorCombination s b).IsSymmetric := by
  -- Check symmetry on the two adjacent transpositions and reduce each coordinate identity to
  -- commutativity of scalar multiplication.
  rw [ThirdOrderTensor.isSymmetric_iff_adjacent_transpositions]
  refine ⟨?_, ?_⟩
  · intro i j k
    simp [symmetricThirdTensorCombination, ThirdOrderTensor.rankOne_apply, mul_assoc, mul_left_comm,
      mul_comm]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring
  · intro i j k
    simp [symmetricThirdTensorCombination, ThirdOrderTensor.rankOne_apply, mul_assoc, mul_left_comm,
      mul_comm]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring

/-- The interpolation condition `Tc (s i) (s i) = a i` for the symmetrized coefficient family
`b`. -/
def symmetricThirdTensorCombinationInterpolates
    (s : Fin p → Point) (a : Fin p → Point) (b : Fin p → Point) : Prop :=
  tensorLeastNormInterpolates s a (symmetricThirdTensorCombination s b)

/-- The feasible set of symmetric third-order tensors interpolating `a` on the data sites `s`. -/
def symmetricThirdTensorFeasibleSet (s : Fin p → Point) (a : Fin p → Point) : Set Tensor3 :=
  {T | T.IsSymmetric ∧ T ∈ tensorLeastNormFeasibleSet s a}

/-- Unfolding `symmetricThirdTensorFeasibleSet s a` gives symmetry together with the interpolation
conditions on the data sites `s`. -/
theorem mem_symmetricThirdTensorFeasibleSet_iff
    (s : Fin p → Point) (a : Fin p → Point) (T : Tensor3) :
    T ∈ symmetricThirdTensorFeasibleSet s a ↔
      T.IsSymmetric ∧ tensorLeastNormInterpolates s a T :=
  Iff.rfl

/-- For a symmetrized tensor combination, feasibility is equivalent to the interpolation
conditions because symmetry is automatic. -/
theorem symmetricThirdTensorCombination_mem_feasibleSet_iff
    (s : Fin p → Point) (a : Fin p → Point) (b : Fin p → Point) :
    symmetricThirdTensorCombination s b ∈ symmetricThirdTensorFeasibleSet s a ↔
      symmetricThirdTensorCombinationInterpolates s a b := by
  simp [symmetricThirdTensorFeasibleSet, symmetricThirdTensorCombinationInterpolates,
    symmetricThirdTensorCombination_isSymmetric, tensorLeastNormFeasibleSet]

/-- `T` is a symmetric least-Frobenius-norm solution of problem `(6.3.43)` when it is feasible
for the symmetric interpolation problem and minimizes the Frobenius norm on that feasible set. The
uniqueness of the symmetrized coefficient family is recorded separately as companion API. -/
def IsSymmetricThirdTensorLeastNormSolution
    (s : Fin p → Point) (a : Fin p → Point) (T : Tensor3) : Prop :=
  T ∈ symmetricThirdTensorFeasibleSet s a ∧
    IsMinOn (fun U ↦ U.fullFrobeniusNorm) (symmetricThirdTensorFeasibleSet s a) T

namespace IsSymmetricThirdTensorLeastNormSolution

/-- A symmetric least-norm solution is feasible for the symmetric interpolation problem. -/
theorem mem_feasibleSet
    {s : Fin p → Point} {a : Fin p → Point} {T : Tensor3}
    (hT : IsSymmetricThirdTensorLeastNormSolution s a T) :
    T ∈ symmetricThirdTensorFeasibleSet s a :=
  hT.1

/-- A symmetric least-norm solution minimizes the Frobenius norm on the symmetric feasible set. -/
theorem isMinOn
    {s : Fin p → Point} {a : Fin p → Point} {T : Tensor3}
    (hT : IsSymmetricThirdTensorLeastNormSolution s a T) :
    IsMinOn (fun U ↦ U.fullFrobeniusNorm) (symmetricThirdTensorFeasibleSet s a) T :=
  hT.2

end IsSymmetricThirdTensorLeastNormSolution

/-- Helper for Chapter06 Theorem 6.3.5: adding coefficient families commutes with the
symmetrized tensor combination. -/
lemma symmetricThirdTensorCombination_add
    (s b c : Fin p → Point) :
    symmetricThirdTensorCombination s (b + c) =
      symmetricThirdTensorCombination s b + symmetricThirdTensorCombination s c := by
  -- Extensionality on tensor coordinates reduces the claim to distributivity inside the finite
  -- sum defining the combination.
  ext i j k
  simp [symmetricThirdTensorCombination, ThirdOrderTensor.rankOne_apply, add_mul, mul_add,
    Finset.sum_add_distrib]
  abel

/-- Helper for Chapter06 Theorem 6.3.5: scaling the coefficient family scales the symmetrized
tensor combination. -/
lemma symmetricThirdTensorCombination_smul
    (s : Fin p → Point) (r : ℝ) (b : Fin p → Point) :
    symmetricThirdTensorCombination s (r • b) =
      r • symmetricThirdTensorCombination s b := by
  -- Extensionality on tensor coordinates reduces the statement to pulling one scalar factor
  -- through each finite sum.
  ext i j k
  simp [symmetricThirdTensorCombination, ThirdOrderTensor.rankOne_apply, Finset.mul_sum,
    mul_assoc]
  ring

/-- Helper for Chapter06 Theorem 6.3.5: the symmetrized tensor combination is linear in its
coefficient family. -/
def symmetricThirdTensorCombinationLinearMap
    (s : Fin p → Point) : (Fin p → Point) →ₗ[ℝ] Tensor3 :=
  { toFun := symmetricThirdTensorCombination s
    map_add' := symmetricThirdTensorCombination_add s
    map_smul' := symmetricThirdTensorCombination_smul s }

/-- Helper for Chapter06 Theorem 6.3.5: the ordinary Gram-inverse family gives dual sample
vectors for a linearly independent family `s`. -/
def symmetricThirdTensorDualFamily
    (s : Fin p → Point) : Fin p → Point :=
  fun i ↦ ∑ k, ((Matrix.gram ℝ s)⁻¹ i k) • s k

/-- Helper for Chapter06 Theorem 6.3.5: the Gram-inverse family is dual to the sample family
with respect to the Euclidean dot product. -/
theorem dotProduct_symmetricThirdTensorDualFamily
    (s : Fin p → Point) (hlin : LinearIndependent ℝ s) (i j : Fin p) :
    dotProduct (symmetricThirdTensorDualFamily s i) (s j) = if i = j then 1 else 0 :=
  by
  have hGramUnit : IsUnit (Matrix.gram ℝ s) :=
    (Matrix.posDef_gram_of_linearIndependent hlin).isUnit
  have hGramDetUnit : IsUnit (Matrix.gram ℝ s).det :=
    (Matrix.isUnit_iff_isUnit_det (Matrix.gram ℝ s)).mp hGramUnit
  -- Expand the dual family into a Gram-inverse weighted sum and rewrite the result as one matrix
  -- entry of `(Matrix.gram ℝ s)⁻¹ * Matrix.gram ℝ s`.
  calc
    dotProduct (symmetricThirdTensorDualFamily s i) (s j)
        = ∑ k, dotProduct (((Matrix.gram ℝ s)⁻¹ i k) • s k) (s j) := by
            simpa [symmetricThirdTensorDualFamily] using
              sum_dotProduct (Finset.univ)
                (fun k : Fin p ↦ ((Matrix.gram ℝ s)⁻¹ i k) • s k) (s j)
    _ = ∑ k, ((Matrix.gram ℝ s)⁻¹ i k) * dotProduct (s k) (s j) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [dotProduct, Finset.mul_sum, mul_assoc]
    _ = ∑ k, ((Matrix.gram ℝ s)⁻¹ i k) * (Matrix.gram ℝ s) k j := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          calc
            ((Matrix.gram ℝ s)⁻¹ i k) * dotProduct (s k) (s j)
                = ((Matrix.gram ℝ s)⁻¹ i k) * inner ℝ (s k) (s j) := by
                    congr 1
                    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
            _ = ((Matrix.gram ℝ s)⁻¹ i k) * (Matrix.gram ℝ s) k j := by
                    rw [Matrix.gram_apply]
    _ = (((Matrix.gram ℝ s)⁻¹ * Matrix.gram ℝ s) i j) := by
          rw [Matrix.mul_apply]
    _ = (1 : Matrix (Fin p) (Fin p) ℝ) i j := by
          rw [Matrix.nonsing_inv_mul _ hGramDetUnit]
    _ = if i = j then 1 else 0 := by
          rw [Matrix.one_apply]

/-- Helper for Chapter06 Theorem 6.3.5: symmetry lets the last two contraction arguments of
`mulVecVec` commute. -/
lemma mulVecVec_comm_of_isSymmetric
    {T : Tensor3} (hT : T.IsSymmetric) (v w : Point) :
    T.mulVecVec v w = T.mulVecVec w v := by
  rcases (ThirdOrderTensor.isSymmetric_iff_adjacent_transpositions T).1 hT with ⟨_, h12⟩
  -- Swap the last two tensor slots coordinatewise and regroup the resulting finite sums.
  ext i
  rw [ThirdOrderTensor.mulVecVec_apply_eq_sum, ThirdOrderTensor.mulVecVec_apply_eq_sum]
  calc
    ∑ j, ∑ k, T i j k * v.ofLp j * w.ofLp k
        = ∑ j, ∑ k, T i k j * v.ofLp j * w.ofLp k := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [h12]
    _ = ∑ j, ∑ k, T i k j * w.ofLp k * v.ofLp j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = ∑ j, ∑ k, T i j k * w.ofLp j * v.ofLp k := by
          rw [Finset.sum_comm]

/-- Helper for Chapter06 Theorem 6.3.5: symmetry in the first two tensor slots swaps the vector
paired against `mulVecVec`. -/
lemma dot_mulVecVec_eq_of_isSymmetric
    {T : Tensor3} (hT : T.IsSymmetric) (u v w : Point) :
    dotProduct u (T.mulVecVec v w) = dotProduct v (T.mulVecVec u w) :=
  by
  rcases (ThirdOrderTensor.isSymmetric_iff_adjacent_transpositions T).1 hT with ⟨h01, _⟩
  -- Rewrite both dot products as triple coordinate sums, then swap the first two tensor slots
  -- using symmetry.
  have hsum :
      ∑ x, u x * (∑ y, ∑ z, T x y z * (v y * w z)) =
        ∑ y, v y * (∑ x, ∑ z, T y x z * (u x * w z)) := by
    calc
      ∑ x, u x * (∑ y, ∑ z, T x y z * (v y * w z))
          = ∑ x, ∑ y, ∑ z, T x y z * (u x * (v y * w z)) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              calc
                u x * (∑ y, ∑ z, T x y z * (v y * w z))
                    = ∑ y, ∑ z, u x * (T x y z * (v y * w z)) := by
                        rw [Finset.mul_sum]
                        refine Finset.sum_congr rfl ?_
                        intro y hy
                        rw [Finset.mul_sum]
                _ = ∑ y, ∑ z, T x y z * (u x * (v y * w z)) := by
                        refine Finset.sum_congr rfl ?_
                        intro y hy
                        refine Finset.sum_congr rfl ?_
                        intro z hz
                        ring
      _ = ∑ y, ∑ x, ∑ z, T y x z * (v y * (u x * w z)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro y hy
            refine Finset.sum_congr rfl ?_
            intro x hx
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [h01]
            ring
      _ = ∑ y, v y * (∑ x, ∑ z, T y x z * (u x * w z)) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            calc
              ∑ x, ∑ z, T y x z * (v y * (u x * w z))
                  = ∑ x, ∑ z, v y * (T y x z * (u x * w z)) := by
                      refine Finset.sum_congr rfl ?_
                      intro x hx
                      refine Finset.sum_congr rfl ?_
                      intro z hz
                      ring
              _ = v y * (∑ x, ∑ z, T y x z * (u x * w z)) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    rw [Finset.mul_sum]
  simpa [dotProduct, ThirdOrderTensor.mulVecVec_apply_eq_sum, mul_assoc] using hsum

/-- Helper for Chapter06 Theorem 6.3.5: flattening the symmetrized tensor combination turns it
into the corresponding finite sum in the Hilbert-space owner. -/
lemma symmetricThirdTensorCombination_flatten_eq_sum
    (s b : Fin p → Point) :
    ThirdOrderTensor.flatten (symmetricThirdTensorCombination s b) =
      ∑ k, (ThirdOrderTensor.flatten (⟪b k, s k, s k⟫₃ : Tensor3) +
        ThirdOrderTensor.flatten (⟪s k, b k, s k⟫₃ : Tensor3) +
        ThirdOrderTensor.flatten (⟪s k, s k, b k⟫₃ : Tensor3)) := by
  -- Extensionality on the nested `PiLp` coordinates reduces flattening to tensor coordinates.
  ext i j k
  simp [symmetricThirdTensorCombination, ThirdOrderTensor.flatten]

/-- Helper for Chapter06 Theorem 6.3.5: against a symmetric residual, each of the three rank-one
summands contributes the same sample pairing. -/
lemma symmetricThirdTensorCombination_flatten_inner_symmetric_eq_sum
    (s b : Fin p → Point) {R : Tensor3} (hR : R.IsSymmetric) :
    inner ℝ (ThirdOrderTensor.flatten (symmetricThirdTensorCombination s b))
      (ThirdOrderTensor.flatten R) =
      3 * ∑ k, dotProduct (b k) (R.mulVecVec (s k) (s k)) := by
  -- Rewrite the flattened combination as a finite sum and collapse the three symmetric
  -- contributions at each sample site.
  rw [symmetricThirdTensorCombination_flatten_eq_sum, sum_inner]
  calc
    ∑ k,
        inner ℝ
          (ThirdOrderTensor.flatten (⟪b k, s k, s k⟫₃ : Tensor3) +
            ThirdOrderTensor.flatten (⟪s k, b k, s k⟫₃ : Tensor3) +
            ThirdOrderTensor.flatten (⟪s k, s k, b k⟫₃ : Tensor3))
          (ThirdOrderTensor.flatten R)
        =
        ∑ k,
          (dotProduct (b k) (R.mulVecVec (s k) (s k)) +
            dotProduct (s k) (R.mulVecVec (b k) (s k)) +
            dotProduct (s k) (R.mulVecVec (s k) (b k))) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [inner_add_left, inner_add_left, tensorFlatten_rankOne_inner, tensorFlatten_rankOne_inner,
        tensorFlatten_rankOne_inner]
    _ =
        ∑ k, (3 : ℝ) * dotProduct (b k) (R.mulVecVec (s k) (s k)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [dot_mulVecVec_eq_of_isSymmetric hR (s k) (b k) (s k),
        mulVecVec_comm_of_isSymmetric hR (s k) (b k),
        dot_mulVecVec_eq_of_isSymmetric hR (s k) (b k) (s k)]
      ring
    _ = 3 * ∑ k, dotProduct (b k) (R.mulVecVec (s k) (s k)) := by
      rw [Finset.mul_sum]

/-- Helper for Chapter06 Theorem 6.3.5: package the interpolation equations for
`symmetricThirdTensorCombination s b` as a linear map on coefficient families. -/
def symmetricThirdTensorInterpolationLinearMap
    (s : Fin p → Point) : (Fin p → Point) →ₗ[ℝ] (Fin p → Point) where
  toFun := fun b i ↦ (symmetricThirdTensorCombination s b).mulVecVec (s i) (s i)
  map_add' b c := by
    -- First rewrite coefficient addition through the tensor combination, then distribute the
    -- contraction over tensor addition.
    funext i
    have hcomb :
        symmetricThirdTensorCombination s (b + c) =
          symmetricThirdTensorCombination s b + symmetricThirdTensorCombination s c :=
      (symmetricThirdTensorCombinationLinearMap s).map_add b c
    rw [hcomb]
    exact tensorAdd_mulVecVec
      (symmetricThirdTensorCombination s b) (symmetricThirdTensorCombination s c) (s i) (s i)
  map_smul' r b := by
    -- Rewrite coefficient scaling through the tensor combination, then pull the scalar through
    -- the tensor contraction.
    funext i
    have hcomb :
        symmetricThirdTensorCombination s (r • b) = r • symmetricThirdTensorCombination s b :=
      (symmetricThirdTensorCombinationLinearMap s).map_smul r b
    rw [hcomb]
    exact tensorSmul_mulVecVec r (symmetricThirdTensorCombination s b) (s i) (s i)

/-- Unfolding `symmetricThirdTensorCombinationInterpolates s a b` is the same as evaluating the
coefficient-to-data linear map at `b`. -/
theorem symmetricThirdTensorCombinationInterpolates_iff
    (s : Fin p → Point) (a : Fin p → Point) (b : Fin p → Point) :
    symmetricThirdTensorCombinationInterpolates s a b ↔
      symmetricThirdTensorInterpolationLinearMap s b = a := by
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrArg (fun f : Fin p → Point ↦ f i) h

/-- Helper for Chapter06 Theorem 6.3.5: if the symmetrized tensor combination interpolates the
zero data, then the tensor itself vanishes. -/
lemma symmetricThirdTensorCombination_eq_zero_of_interpolates_zero
    (s b : Fin p → Point)
    (hzero : symmetricThirdTensorCombinationInterpolates s 0 b) :
    symmetricThirdTensorCombination s b = 0 := by
  let T := symmetricThirdTensorCombination s b
  have hinner :
      inner ℝ (ThirdOrderTensor.flatten T) (ThirdOrderTensor.flatten T) = 0 := by
    -- Pair the tensor against itself and use the zero interpolation equations to kill each
    -- sample contribution.
    simpa [T] using
      calc
        inner ℝ (ThirdOrderTensor.flatten (symmetricThirdTensorCombination s b))
            (ThirdOrderTensor.flatten T)
            =
            3 * ∑ k, dotProduct (b k) (T.mulVecVec (s k) (s k)) := by
              exact symmetricThirdTensorCombination_flatten_inner_symmetric_eq_sum s b
                (symmetricThirdTensorCombination_isSymmetric s b)
        _ = 0 := by
          rw [show ∑ k, dotProduct (b k) (T.mulVecVec (s k) (s k)) = 0 by
            refine Finset.sum_eq_zero ?_
            intro k hk
            simp [T, hzero k]]
          ring
  have hflat : ThirdOrderTensor.flatten T = 0 := by
    exact (inner_self_eq_zero.mp hinner)
  exact tensor_eq_zero_of_flatten_eq_zero hflat

/-- Helper for Chapter06 Theorem 6.3.5: evaluating the symmetrized tensor combination on the
Gram-inverse dual vectors recovers a single coefficient plus its scalar component along `s i`. -/
lemma symmetricThirdTensorCombination_mulVecVec_dualFamily
    (s b : Fin p → Point) (hlin : LinearIndependent ℝ s) (i : Fin p) :
    (symmetricThirdTensorCombination s b).mulVecVec
        (symmetricThirdTensorDualFamily s i) (symmetricThirdTensorDualFamily s i) =
      b i + (2 * dotProduct (symmetricThirdTensorDualFamily s i) (b i)) • s i :=
  by
  let d : Point := symmetricThirdTensorDualFamily s i
  let F : Fin p → Point := fun k ↦
    (if i = k then 1 else 0) • b k +
      (dotProduct d (b k) * (if i = k then 1 else 0)) • s k +
      ((if i = k then 1 else 0) * dotProduct d (b k)) • s k
  have hdual : ∀ k : Fin p, dotProduct d (s k) = if i = k then 1 else 0 := by
    intro k
    simpa [d] using dotProduct_symmetricThirdTensorDualFamily s hlin i k
  -- Distribute the contraction across the finite sum and evaluate each rank-one summand at the
  -- Gram-inverse dual vector.
  calc
    (symmetricThirdTensorCombination s b).mulVecVec d d
        =
        ∑ k, ((⟪b k, s k, s k⟫₃ : Tensor3).mulVecVec d d +
          (⟪s k, b k, s k⟫₃ : Tensor3).mulVecVec d d +
          (⟪s k, s k, b k⟫₃ : Tensor3).mulVecVec d d) := by
            simpa [symmetricThirdTensorCombination, tensorAdd_mulVecVec] using
              (tensorSum_mulVecVec (Finset.univ : Finset (Fin p))
                (fun k : Fin p ↦
                  (⟪b k, s k, s k⟫₃ : Tensor3) +
                    ⟪s k, b k, s k⟫₃ + ⟪s k, s k, b k⟫₃)
                d d)
    _ = ∑ k, F k := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [tensorRankOne_mulVecVec, tensorRankOne_mulVecVec, tensorRankOne_mulVecVec]
          rw [hdual k]
          by_cases hik : i = k
          · simp [F, hik]
          · simp [F, hik]
    _ = F i := by
          refine Finset.sum_eq_single i ?_ ?_
          · intro k hk hki
            dsimp [F]
            split_ifs with hik
            · exact (hki hik.symm).elim
            · simp
          · simp [F]
    _ = b i + dotProduct d (b i) • s i + dotProduct d (b i) • s i := by
          simp [F]
    _ = b i + (2 * dotProduct d (b i)) • s i := by
          rw [add_assoc, ← two_smul ℝ (dotProduct d (b i) • s i)]
          simp [smul_smul, mul_assoc]

/-- Helper for Chapter06 Theorem 6.3.5: a zero symmetrized tensor combination has zero
coefficients, recovered from the Gram-inverse dual family. -/
lemma coeff_eq_zero_of_symmetricThirdTensorCombination_eq_zero
    (s b : Fin p → Point) (hlin : LinearIndependent ℝ s)
    (hT : symmetricThirdTensorCombination s b = 0) :
    b = 0 :=
  by
  funext i
  let d : Point := symmetricThirdTensorDualFamily s i
  let β : ℝ := dotProduct d (b i)
  have hEvalZero :
      (symmetricThirdTensorCombination s b).mulVecVec d d = 0 := by
    -- Evaluating the zero tensor at the dual pair shows that the explicit combination vanishes
    -- there as well.
    have hZeroTensorEval : (0 : Tensor3).mulVecVec d d = 0 := by
      ext l
      simp [ThirdOrderTensor.mulVecVec_apply_eq_sum]
    calc
      (symmetricThirdTensorCombination s b).mulVecVec d d = (0 : Tensor3).mulVecVec d d := by
        exact congrArg (fun T : Tensor3 ↦ T.mulVecVec d d) hT
      _ = 0 := hZeroTensorEval
  have hMain : b i + (2 * β) • s i = 0 := by
    -- The dual-family evaluation formula isolates the `i`-th coefficient up to its scalar
    -- component along `s i`.
    calc
      b i + (2 * β) • s i =
          (symmetricThirdTensorCombination s b).mulVecVec d d := by
            symm
            simpa [d, β] using symmetricThirdTensorCombination_mulVecVec_dualFamily s b hlin i
      _ = 0 := hEvalZero
  have hβEq : β + 2 * β = 0 := by
    -- Pairing the previous identity with the same dual vector turns the vector equation into a
    -- scalar equation for the remaining component `β`.
    simpa [β, d, dotProduct_add, dotProduct_smul, dotProduct_symmetricThirdTensorDualFamily, hlin,
      mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun x : Point ↦ dotProduct d x) hMain
  have hβZero : β = 0 := by
    have hThreeβ := hβEq
    ring_nf at hThreeβ
    exact (mul_eq_zero.mp hThreeβ).resolve_right (by norm_num)
  -- Once the scalar component vanishes, the recovered coefficient itself must be zero.
  simp [hβZero] at hMain
  simpa using hMain

/-- Helper for Chapter06 Theorem 6.3.5: the coefficient-to-data linear map is injective for a
linearly independent sample family. -/
lemma symmetricThirdTensorInterpolationLinearMap_injective
    (s : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    Function.Injective (symmetricThirdTensorInterpolationLinearMap s) := by
  intro b c hbc
  have hsub :
      symmetricThirdTensorInterpolationLinearMap s (b - c) = 0 := by
    rw [LinearMap.map_sub, hbc, sub_self]
  have hzeroInterp : symmetricThirdTensorCombinationInterpolates s 0 (b - c) :=
    (symmetricThirdTensorCombinationInterpolates_iff s 0 (b - c)).2 hsub
  have hcombZero :
      symmetricThirdTensorCombination s (b - c) = 0 :=
    symmetricThirdTensorCombination_eq_zero_of_interpolates_zero s (b - c) hzeroInterp
  have hcoeffZero :
      b - c = 0 :=
    coeff_eq_zero_of_symmetricThirdTensorCombination_eq_zero s (b - c) hlin hcombZero
  exact sub_eq_zero.mp hcoeffZero

/-- Helper for Chapter06 Theorem 6.3.5: under linear independence, the interpolation linear map
is a linear equivalence, so the coefficient family is determined explicitly by the data `a`. -/
def symmetricThirdTensorInterpolationLinearEquiv
    (s : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    (Fin p → Point) ≃ₗ[ℝ] (Fin p → Point) :=
  (symmetricThirdTensorInterpolationLinearMap s).linearEquivOfInjective
    (symmetricThirdTensorInterpolationLinearMap_injective s hlin) rfl

/-- Helper for Chapter06 Theorem 6.3.5: under linear independence, the symmetric coefficient
family satisfying the interpolation equations is unique. -/
theorem existsUnique_symmetricThirdTensorCombinationInterpolates
    (s a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    ∃! b : Fin p → Point, symmetricThirdTensorCombinationInterpolates s a b := by
  let e : (Fin p → Point) ≃ₗ[ℝ] (Fin p → Point) :=
    symmetricThirdTensorInterpolationLinearEquiv s hlin
  refine ⟨e.symm a, ?_, ?_⟩
  · -- The chosen coefficients interpolate `a` because the linear equivalence is inverse to `L`.
    exact (symmetricThirdTensorCombinationInterpolates_iff s a (e.symm a)).2 (e.apply_symm_apply a)
  · intro b hb
    -- Any other interpolating family has the same image under the linear equivalence, hence it
    -- must coincide with the chosen one.
    have hb' : e b = a := by
      change symmetricThirdTensorInterpolationLinearMap s b = a
      exact (symmetricThirdTensorCombinationInterpolates_iff s a b).1 hb
    exact e.injective (hb'.trans (e.apply_symm_apply a).symm)

/-- Helper for Chapter06 Theorem 6.3.5: the canonical symmetric tensor combination is a
least-Frobenius-norm point of the symmetric feasible set. -/
theorem symmetricThirdTensorCombination_isMinOnFeasibleSet
    (s a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    let b := Classical.choose (existsUnique_symmetricThirdTensorCombinationInterpolates s a hlin)
    IsMinOn (fun T ↦ T.fullFrobeniusNorm) (symmetricThirdTensorFeasibleSet s a)
      (symmetricThirdTensorCombination s b) := by
  let b : Fin p → Point :=
    Classical.choose (existsUnique_symmetricThirdTensorCombinationInterpolates s a hlin)
  let Tc : Tensor3 := symmetricThirdTensorCombination s b
  have hTcInterp : symmetricThirdTensorCombinationInterpolates s a b :=
    (Classical.choose_spec (existsUnique_symmetricThirdTensorCombinationInterpolates s a hlin)).1
  have hTcFeasible : Tc ∈ symmetricThirdTensorFeasibleSet s a := by
    -- The canonical coefficient family is feasible because its symmetrized tensor interpolates `a`
    -- and symmetry is automatic.
    exact (symmetricThirdTensorCombination_mem_feasibleSet_iff s a b).2 hTcInterp
  rw [isMinOn_iff]
  intro T hT
  let R : Tensor3 := T - Tc
  have hTsymm : T.IsSymmetric := (mem_symmetricThirdTensorFeasibleSet_iff s a T).1 hT |>.1
  have hTInterp : tensorLeastNormInterpolates s a T :=
    (mem_symmetricThirdTensorFeasibleSet_iff s a T).1 hT |>.2
  have hRsymm : R.IsSymmetric := by
    -- Route correction: subtract the canonical feasible tensor from a symmetric feasible tensor so
    -- the residual remains in the symmetric subspace where the orthogonality identity applies.
    rcases (ThirdOrderTensor.isSymmetric_iff_adjacent_transpositions T).1 hTsymm with ⟨hT01, hT12⟩
    rcases (ThirdOrderTensor.isSymmetric_iff_adjacent_transpositions Tc).1
      (symmetricThirdTensorCombination_isSymmetric s b) with ⟨hTc01, hTc12⟩
    rw [ThirdOrderTensor.isSymmetric_iff_adjacent_transpositions]
    refine ⟨?_, ?_⟩
    · intro i j k
      simp [R, hT01 i j k, hTc01 i j k]
    · intro i j k
      simp [R, hT12 i j k, hTc12 i j k]
  have horth :
      inner ℝ (ThirdOrderTensor.flatten Tc) (ThirdOrderTensor.flatten R) = 0 := by
    -- The residual interpolation values vanish, so the symmetric inner-product identity collapses
    -- to zero.
    calc
      inner ℝ (ThirdOrderTensor.flatten Tc) (ThirdOrderTensor.flatten R)
          = 3 * ∑ k, dotProduct (b k) (R.mulVecVec (s k) (s k)) := by
              simpa [Tc] using
                symmetricThirdTensorCombination_flatten_inner_symmetric_eq_sum s b hRsymm
      _ = 0 := by
        rw [show ∑ k, dotProduct (b k) (R.mulVecVec (s k) (s k)) = 0 by
          refine Finset.sum_eq_zero ?_
          intro k hk
          have hResidual :
              R.mulVecVec (s k) (s k) = 0 := by
            calc
              R.mulVecVec (s k) (s k) = T.mulVecVec (s k) (s k) - Tc.mulVecVec (s k) (s k) := by
                simpa [R] using tensorSub_mulVecVec T Tc (s k) (s k)
              _ = a k - a k := by
                rw [hTInterp k, hTcInterp k]
              _ = 0 := sub_self _
          simp [hResidual]]
        ring
  have hflatten_add :
      ThirdOrderTensor.flatten T = ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R := by
    -- Rewrite flattening through `R = T - Tc` before invoking Pythagoras.
    have hflatten_sub' :
        ThirdOrderTensor.flatten R =
          ThirdOrderTensor.flatten T - ThirdOrderTensor.flatten Tc := by
      simpa [R] using tensorFlatten_sub T Tc
    calc
      ThirdOrderTensor.flatten T =
          ThirdOrderTensor.flatten Tc +
            (ThirdOrderTensor.flatten T - ThirdOrderTensor.flatten Tc) := by
        simp [sub_eq_add_neg, add_left_comm]
      _ = ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R := by
        rw [hflatten_sub'.symm]
  have hpyth :
      ‖ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R‖ *
          ‖ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R‖ =
        ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ +
          ‖ThirdOrderTensor.flatten R‖ * ‖ThirdOrderTensor.flatten R‖ := by
    -- Orthogonality gives the Hilbert-space Pythagoras identity in the flattened owner.
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hmul_le :
      ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ ≤
        ‖ThirdOrderTensor.flatten T‖ * ‖ThirdOrderTensor.flatten T‖ := by
    -- The residual norm contributes a nonnegative term, so the candidate norm square is minimal.
    calc
      ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ ≤
          ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ +
            ‖ThirdOrderTensor.flatten R‖ * ‖ThirdOrderTensor.flatten R‖ := by
        exact le_add_of_nonneg_right (mul_self_nonneg ‖ThirdOrderTensor.flatten R‖)
      _ = ‖ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R‖ *
            ‖ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R‖ := by
        symm
        exact hpyth
      _ = ‖ThirdOrderTensor.flatten T‖ * ‖ThirdOrderTensor.flatten T‖ := by
        rw [← hflatten_add]
  have hnorm_flat :
      ‖ThirdOrderTensor.flatten Tc‖ ≤ ‖ThirdOrderTensor.flatten T‖ := by
    -- Since both norms are nonnegative reals, the squared inequality descends to the norms.
    have habs :
        |‖ThirdOrderTensor.flatten Tc‖| ≤ |‖ThirdOrderTensor.flatten T‖| :=
      (abs_le_iff_mul_self_le).2 hmul_le
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using habs
  -- Rewrite the flattened Hilbert-space inequality back to the stated Frobenius norm objective.
  calc
    Tc.fullFrobeniusNorm = ‖ThirdOrderTensor.flatten Tc‖ :=
      thirdOrderTensorFullFrobeniusNorm_eq_flatten_norm Tc
    _ ≤ ‖ThirdOrderTensor.flatten T‖ := hnorm_flat
    _ = T.fullFrobeniusNorm := by
      symm
      exact thirdOrderTensorFullFrobeniusNorm_eq_flatten_norm T

/-- Under `LinearIndependent ℝ s`, there is a unique symmetric least-Frobenius-norm solution of
problem `(6.3.43)`. -/
theorem existsUnique_isSymmetricThirdTensorLeastNormSolution
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    ∃! T : Tensor3, IsSymmetricThirdTensorLeastNormSolution s a T := by
  let b : Fin p → Point :=
    Classical.choose (existsUnique_symmetricThirdTensorCombinationInterpolates s a hlin)
  let Tc : Tensor3 := symmetricThirdTensorCombination s b
  have hTcInterp : symmetricThirdTensorCombinationInterpolates s a b :=
    (Classical.choose_spec (existsUnique_symmetricThirdTensorCombinationInterpolates s a hlin)).1
  have hTcSol : IsSymmetricThirdTensorLeastNormSolution s a Tc := by
    -- The canonical coefficient family is feasible, and the orthogonality/Pythagoras argument
    -- already proves that its symmetrized tensor is least norm on the feasible set.
    refine ⟨(symmetricThirdTensorCombination_mem_feasibleSet_iff s a b).2 hTcInterp, ?_⟩
    simpa [b, Tc] using symmetricThirdTensorCombination_isMinOnFeasibleSet s a hlin
  refine ⟨Tc, hTcSol, ?_⟩
  intro T hT
  let R : Tensor3 := T - Tc
  have hTsymm : T.IsSymmetric :=
    (mem_symmetricThirdTensorFeasibleSet_iff s a T).1 hT.mem_feasibleSet |>.1
  have hTInterp : tensorLeastNormInterpolates s a T :=
    (mem_symmetricThirdTensorFeasibleSet_iff s a T).1 hT.mem_feasibleSet |>.2
  have hRsymm : R.IsSymmetric := by
    -- Route correction: compare an arbitrary minimizer to the canonical one by working with their
    -- symmetric residual `R = T - Tc`.
    rcases (ThirdOrderTensor.isSymmetric_iff_adjacent_transpositions T).1 hTsymm with ⟨hT01, hT12⟩
    rcases (ThirdOrderTensor.isSymmetric_iff_adjacent_transpositions Tc).1
      ((mem_symmetricThirdTensorFeasibleSet_iff s a Tc).1 hTcSol.mem_feasibleSet |>.1) with
      ⟨hTc01, hTc12⟩
    rw [ThirdOrderTensor.isSymmetric_iff_adjacent_transpositions]
    refine ⟨?_, ?_⟩
    · intro i j k
      simp [R, hT01 i j k, hTc01 i j k]
    · intro i j k
      simp [R, hT12 i j k, hTc12 i j k]
  have horth :
      inner ℝ (ThirdOrderTensor.flatten Tc) (ThirdOrderTensor.flatten R) = 0 := by
    -- Both tensors interpolate the same data, so the symmetric residual contributes zero at every
    -- sample site in the orthogonality identity.
    calc
      inner ℝ (ThirdOrderTensor.flatten Tc) (ThirdOrderTensor.flatten R)
          = 3 * ∑ k, dotProduct (b k) (R.mulVecVec (s k) (s k)) := by
              simpa [Tc] using
                symmetricThirdTensorCombination_flatten_inner_symmetric_eq_sum s b hRsymm
      _ = 0 := by
        rw [show ∑ k, dotProduct (b k) (R.mulVecVec (s k) (s k)) = 0 by
          refine Finset.sum_eq_zero ?_
          intro k hk
          have hResidual :
              R.mulVecVec (s k) (s k) = 0 := by
            calc
              R.mulVecVec (s k) (s k) = T.mulVecVec (s k) (s k) - Tc.mulVecVec (s k) (s k) := by
                simpa [R] using tensorSub_mulVecVec T Tc (s k) (s k)
              _ = a k - a k := by
                rw [hTInterp k, hTcInterp k]
              _ = 0 := sub_self _
          simp [hResidual]]
        ring
  have hflatten_add :
      ThirdOrderTensor.flatten T = ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R := by
    -- Rewrite flattening through subtraction before applying the Hilbert-space Pythagoras identity.
    have hflatten_sub' :
        ThirdOrderTensor.flatten R =
          ThirdOrderTensor.flatten T - ThirdOrderTensor.flatten Tc := by
      simpa [R] using tensorFlatten_sub T Tc
    calc
      ThirdOrderTensor.flatten T =
          ThirdOrderTensor.flatten Tc +
            (ThirdOrderTensor.flatten T - ThirdOrderTensor.flatten Tc) := by
        simp [sub_eq_add_neg, add_left_comm]
      _ = ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R := by
        rw [hflatten_sub'.symm]
  have hpyth :
      ‖ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R‖ *
          ‖ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R‖ =
        ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ +
          ‖ThirdOrderTensor.flatten R‖ * ‖ThirdOrderTensor.flatten R‖ := by
    -- Orthogonality upgrades the residual decomposition to a Pythagoras identity.
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hnormEq :
      Tc.fullFrobeniusNorm = T.fullFrobeniusNorm := by
    have hTcMin := hTcSol.isMinOn
    have hTMin := hT.isMinOn
    rw [isMinOn_iff] at hTcMin hTMin
    apply le_antisymm
    · exact hTcMin T hT.mem_feasibleSet
    · exact hTMin Tc hTcSol.mem_feasibleSet
  have hnormFlatEq :
      ‖ThirdOrderTensor.flatten Tc‖ = ‖ThirdOrderTensor.flatten T‖ := by
    simpa [thirdOrderTensorFullFrobeniusNorm_eq_flatten_norm] using hnormEq
  have hpyth' :
      ‖ThirdOrderTensor.flatten T‖ * ‖ThirdOrderTensor.flatten T‖ =
        ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ +
          ‖ThirdOrderTensor.flatten R‖ * ‖ThirdOrderTensor.flatten R‖ := by
    simpa [hflatten_add] using hpyth
  have hRnormSq :
      ‖ThirdOrderTensor.flatten R‖ * ‖ThirdOrderTensor.flatten R‖ = 0 := by
    have hEq :
        ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ +
          ‖ThirdOrderTensor.flatten R‖ * ‖ThirdOrderTensor.flatten R‖ =
        ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ := by
      simpa [hnormFlatEq] using hpyth'.symm
    exact add_eq_left.mp hEq
  have hRflatZero : ThirdOrderTensor.flatten R = 0 := by
    exact norm_eq_zero.mp (mul_self_eq_zero.mp hRnormSq)
  have hRzero : R = 0 := tensor_eq_zero_of_flatten_eq_zero hRflatZero
  exact sub_eq_zero.mp (by simpa [R] using hRzero)

/-- Under `LinearIndependent ℝ s`, there exists a symmetric least-Frobenius-norm solution of the
interpolation problem. -/
theorem exists_isSymmetricThirdTensorLeastNormSolution
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    ∃ T : Tensor3, IsSymmetricThirdTensorLeastNormSolution s a T :=
  ExistsUnique.exists <| existsUnique_isSymmetricThirdTensorLeastNormSolution s a hlin

/-- The canonical symmetrized coefficient family, recovered explicitly from the interpolation
linear equivalence under `LinearIndependent ℝ s`. -/
def symmetricThirdTensorLeastNormCoefficients
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) : Fin p → Point :=
  (symmetricThirdTensorInterpolationLinearEquiv s hlin).symm a

/-- The explicit symmetric tensor built from
`symmetricThirdTensorLeastNormCoefficients s a hlin`. -/
def symmetricThirdTensorLeastNormSolution
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) : Tensor3 :=
  symmetricThirdTensorCombination s (symmetricThirdTensorLeastNormCoefficients s a hlin)

/-- Expanding the canonical least-norm tensor through its coefficient family recovers the source
formula of Theorem 6.3.5. -/
theorem symmetricThirdTensorLeastNormSolution_eq_combination
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    symmetricThirdTensorLeastNormSolution s a hlin =
      symmetricThirdTensorCombination s (symmetricThirdTensorLeastNormCoefficients s a hlin) :=
  rfl

/-- Chapter06 Theorem 6.3.5: if `s : Fin p → ℝ^n` is linearly independent and `a : Fin p → ℝ^n`,
then the symmetric least-Frobenius-norm solution of problem `(6.3.43)` is the explicit tensor
`symmetricThirdTensorLeastNormSolution s a hlin = symmetricThirdTensorCombination s (b)`, where
`b = symmetricThirdTensorLeastNormCoefficients s a hlin` is the uniquely determined coefficient
family satisfying the interpolation equations. The companion coefficient uniqueness statement is
recorded separately via `existsUnique_symmetricThirdTensorLeastNormCoefficients`. The source's
side condition `p ≤ n` is redundant once `s` is linearly independent and is therefore omitted
from the Lean statement. -/
theorem symmetricThirdTensorLeastNormSolution_spec
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    symmetricThirdTensorLeastNormSolution s a hlin =
        symmetricThirdTensorCombination s (symmetricThirdTensorLeastNormCoefficients s a hlin) ∧
      IsSymmetricThirdTensorLeastNormSolution s a
        (symmetricThirdTensorLeastNormSolution s a hlin) :=
  by
  let b : Fin p → Point := symmetricThirdTensorLeastNormCoefficients s a hlin
  let bChoice : Fin p → Point :=
    Classical.choose (existsUnique_symmetricThirdTensorCombinationInterpolates s a hlin)
  have hbInterp : symmetricThirdTensorCombinationInterpolates s a b := by
    -- The explicit coefficients are the inverse image of the data under the interpolation linear
    -- equivalence.
    exact (symmetricThirdTensorCombinationInterpolates_iff s a b).2 <|
      by
        change (symmetricThirdTensorInterpolationLinearEquiv s hlin) b = a
        simpa [b, symmetricThirdTensorLeastNormCoefficients] using
          (symmetricThirdTensorInterpolationLinearEquiv s hlin).apply_symm_apply a
  have hbChoiceInterp : symmetricThirdTensorCombinationInterpolates s a bChoice :=
    (Classical.choose_spec (existsUnique_symmetricThirdTensorCombinationInterpolates s a hlin)).1
  have hbChoiceEq : bChoice = b := by
    -- The interpolation equations determine the coefficient family uniquely, so the choose-based
    -- witness agrees with the explicit linear-equivalence coefficients.
    exact ExistsUnique.unique
      (existsUnique_symmetricThirdTensorCombinationInterpolates s a hlin)
      hbChoiceInterp hbInterp
  have hMinChoice :
      IsMinOn (fun T ↦ T.fullFrobeniusNorm) (symmetricThirdTensorFeasibleSet s a)
        (symmetricThirdTensorCombination s bChoice) := by
    -- The earlier least-norm theorem already proves minimality for the unique interpolating
    -- coefficient family returned by `Classical.choose`.
    simpa [bChoice] using symmetricThirdTensorCombination_isMinOnFeasibleSet s a hlin
  have hMin :
      IsMinOn (fun T ↦ T.fullFrobeniusNorm) (symmetricThirdTensorFeasibleSet s a)
        (symmetricThirdTensorCombination s b) := by
    -- Rewriting by coefficient uniqueness transports the choose-based minimality statement to the
    -- explicit coefficient family.
    simpa [hbChoiceEq] using hMinChoice
  have hFeasible :
      symmetricThirdTensorCombination s b ∈ symmetricThirdTensorFeasibleSet s a := by
    -- The explicit coefficients interpolate the data, and symmetry of the tensor combination is
    -- automatic.
    exact (symmetricThirdTensorCombination_mem_feasibleSet_iff s a b).2 hbInterp
  refine ⟨symmetricThirdTensorLeastNormSolution_eq_combination s a hlin, ?_⟩
  -- Assemble feasibility and minimality for the explicit tensor built from the explicit
  -- coefficient family.
  simpa [symmetricThirdTensorLeastNormSolution, b] using
    (show IsSymmetricThirdTensorLeastNormSolution s a (symmetricThirdTensorCombination s b) from
      ⟨hFeasible, hMin⟩)

/-- The canonical symmetric least-Frobenius-norm solution is feasible for the symmetric
interpolation problem. -/
theorem symmetricThirdTensorLeastNormSolution_mem_feasibleSet
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    symmetricThirdTensorLeastNormSolution s a hlin ∈ symmetricThirdTensorFeasibleSet s a :=
  (symmetricThirdTensorLeastNormSolution_spec s a hlin).2.mem_feasibleSet

/-- The canonical symmetric least-Frobenius-norm solution minimizes the Frobenius norm on the
symmetric feasible set. -/
theorem symmetricThirdTensorLeastNormSolution_isMinOn
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    IsMinOn (fun U ↦ U.fullFrobeniusNorm) (symmetricThirdTensorFeasibleSet s a)
      (symmetricThirdTensorLeastNormSolution s a hlin) :=
  (symmetricThirdTensorLeastNormSolution_spec s a hlin).2.isMinOn

/-- The canonical symmetric least-Frobenius-norm solution is symmetric. -/
theorem symmetricThirdTensorLeastNormSolution_isSymmetric
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    (symmetricThirdTensorLeastNormSolution s a hlin).IsSymmetric :=
  ((mem_symmetricThirdTensorFeasibleSet_iff s a _).1 <|
    symmetricThirdTensorLeastNormSolution_mem_feasibleSet s a hlin).1

/-- The canonical symmetric least-Frobenius-norm solution interpolates the prescribed data on the
sites `s`. -/
theorem symmetricThirdTensorLeastNormSolution_interpolates
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    tensorLeastNormInterpolates s a (symmetricThirdTensorLeastNormSolution s a hlin) :=
  ((mem_symmetricThirdTensorFeasibleSet_iff s a _).1 <|
    symmetricThirdTensorLeastNormSolution_mem_feasibleSet s a hlin).2

/-- Two symmetric least-Frobenius-norm solutions of problem `(6.3.43)` coincide. -/
theorem eq_of_isSymmetricThirdTensorLeastNormSolution
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s)
    {T U : Tensor3}
    (hT : IsSymmetricThirdTensorLeastNormSolution s a T)
    (hU : IsSymmetricThirdTensorLeastNormSolution s a U) :
    T = U :=
  (existsUnique_isSymmetricThirdTensorLeastNormSolution s a hlin).unique hT hU

namespace IsSymmetricThirdTensorLeastNormSolution

/-- Any symmetric least-Frobenius-norm solution agrees with the canonical owner of
Theorem 6.3.5. -/
theorem eq_solution
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s)
    {T : Tensor3} (hT : IsSymmetricThirdTensorLeastNormSolution s a T) :
    T = symmetricThirdTensorLeastNormSolution s a hlin :=
  (existsUnique_isSymmetricThirdTensorLeastNormSolution s a hlin).unique hT
    (symmetricThirdTensorLeastNormSolution_spec s a hlin).2

end IsSymmetricThirdTensorLeastNormSolution

/-- The canonical symmetric least-Frobenius-norm solution has a unique symmetrized coefficient
family satisfying the interpolation conditions. -/
theorem existsUnique_symmetricThirdTensorLeastNormCoefficients
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    ∃! b : Fin p → Point,
      symmetricThirdTensorLeastNormSolution s a hlin = symmetricThirdTensorCombination s b ∧
        symmetricThirdTensorCombinationInterpolates s a b :=
  by
    refine ⟨symmetricThirdTensorLeastNormCoefficients s a hlin, ?_, ?_⟩
    · refine ⟨symmetricThirdTensorLeastNormSolution_eq_combination s a hlin, ?_⟩
      exact
        (symmetricThirdTensorCombinationInterpolates_iff s a
          (symmetricThirdTensorLeastNormCoefficients s a hlin)).2
          (by
            change
              (symmetricThirdTensorInterpolationLinearEquiv s hlin)
                  (symmetricThirdTensorLeastNormCoefficients s a hlin) = a
            simpa [symmetricThirdTensorLeastNormCoefficients] using
              (symmetricThirdTensorInterpolationLinearEquiv s hlin).apply_symm_apply a)
    intro b hb
    exact (existsUnique_symmetricThirdTensorCombinationInterpolates s a hlin).unique hb.2
      (by
        exact
          (symmetricThirdTensorCombinationInterpolates_iff s a
            (symmetricThirdTensorLeastNormCoefficients s a hlin)).2
            (by
              change
                (symmetricThirdTensorInterpolationLinearEquiv s hlin)
                    (symmetricThirdTensorLeastNormCoefficients s a hlin) = a
              simpa [symmetricThirdTensorLeastNormCoefficients] using
                (symmetricThirdTensorInterpolationLinearEquiv s hlin).apply_symm_apply a))

/-- The canonical coefficient family represents the canonical least-norm tensor and satisfies the
source interpolation conditions. -/
theorem symmetricThirdTensorLeastNormCoefficients_spec
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    symmetricThirdTensorLeastNormSolution s a hlin =
        symmetricThirdTensorCombination s (symmetricThirdTensorLeastNormCoefficients s a hlin) ∧
      symmetricThirdTensorCombinationInterpolates s a
        (symmetricThirdTensorLeastNormCoefficients s a hlin) := by
  refine ⟨symmetricThirdTensorLeastNormSolution_eq_combination s a hlin, ?_⟩
  exact
    (symmetricThirdTensorCombinationInterpolates_iff s a
      (symmetricThirdTensorLeastNormCoefficients s a hlin)).2
      (by
        change
          (symmetricThirdTensorInterpolationLinearEquiv s hlin)
              (symmetricThirdTensorLeastNormCoefficients s a hlin) = a
        simpa [symmetricThirdTensorLeastNormCoefficients] using
          (symmetricThirdTensorInterpolationLinearEquiv s hlin).apply_symm_apply a)

/-- The canonical symmetric coefficient family satisfies the interpolation conditions
`Tc (s i) (s i) = a i`. -/
theorem symmetricThirdTensorLeastNormCoefficients_interpolates
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    symmetricThirdTensorCombinationInterpolates s a
      (symmetricThirdTensorLeastNormCoefficients s a hlin) :=
  (symmetricThirdTensorLeastNormCoefficients_spec s a hlin).2

namespace symmetricThirdTensorLeastNormCoefficients

/-- Any symmetrized coefficient family representing the canonical least-norm tensor and
satisfying the interpolation conditions coincides with the canonical coefficient family. -/
theorem eq_of_eq_combination_and_interpolates
    (s : Fin p → Point) (a : Fin p → Point) (hlin : LinearIndependent ℝ s)
    {b : Fin p → Point}
    (hb₁ :
      symmetricThirdTensorLeastNormSolution s a hlin = symmetricThirdTensorCombination s b)
    (hb₂ : symmetricThirdTensorCombinationInterpolates s a b) :
    b = symmetricThirdTensorLeastNormCoefficients s a hlin :=
  (existsUnique_symmetricThirdTensorLeastNormCoefficients s a hlin).unique
    ⟨hb₁, hb₂⟩ (symmetricThirdTensorLeastNormCoefficients_spec s a hlin)

end symmetricThirdTensorLeastNormCoefficients

namespace IsSymmetricThirdTensorLeastNormSolution

/-- Under `LinearIndependent ℝ s`, a symmetric least-norm solution has a unique symmetrized
coefficient family satisfying the interpolation conditions. -/
theorem existsUnique_coefficients
    {s : Fin p → Point} {a : Fin p → Point} (hlin : LinearIndependent ℝ s)
    {T : Tensor3} (hT : IsSymmetricThirdTensorLeastNormSolution s a T) :
    ∃! b : Fin p → Point,
      T = symmetricThirdTensorCombination s b ∧
        symmetricThirdTensorCombinationInterpolates s a b := by
  refine ⟨symmetricThirdTensorLeastNormCoefficients s a hlin, ?_, ?_⟩
  · refine ⟨?_, symmetricThirdTensorLeastNormCoefficients_interpolates s a hlin⟩
    rw [IsSymmetricThirdTensorLeastNormSolution.eq_solution s a hlin hT]
    exact symmetricThirdTensorLeastNormSolution_eq_combination s a hlin
  · intro b hb
    apply symmetricThirdTensorLeastNormCoefficients.eq_of_eq_combination_and_interpolates
      s a hlin
    · calc
        symmetricThirdTensorLeastNormSolution s a hlin = T := by
          simpa using
            (IsSymmetricThirdTensorLeastNormSolution.eq_solution s a hlin hT).symm
        _ = symmetricThirdTensorCombination s b := hb.1
    · exact hb.2

end IsSymmetricThirdTensorLeastNormSolution

end
