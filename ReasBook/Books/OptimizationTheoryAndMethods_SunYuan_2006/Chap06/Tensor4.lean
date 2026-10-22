/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Perm.Sign

noncomputable section

open scoped BigOperators

/-- Fourth-order tensors for `Tensor4`: coordinate arrays `V i j k l : ℝ`. This matches the
Chapter 6 tensor/Frobenius owner style used for `ThirdOrderTensor`. -/
abbrev Tensor4 (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

namespace Tensor4

/-- The canonical nested `PiLp` Hilbert-space owner for flattening a fourth-order coordinate
tensor. -/
abbrev Flattened (n : ℕ) :=
  PiLp 2 fun _ : Fin n ↦ PiLp 2 fun _ : Fin n ↦ PiLp 2 fun _ : Fin n ↦ PiLp 2 fun _ : Fin n ↦ ℝ

/-- The rank-one fourth-order tensor `u ⊗ v ⊗ w ⊗ x` with entries
`u i * v j * w k * x l`. -/
def rankOne (u v w x : Point) : _root_.Tensor4 n :=
  fun i j k l ↦ u i * v j * w k * x l

scoped[Tensor4] notation:max "⟪" u ", " v ", " w ", " x "⟫₄" => rankOne u v w x

open scoped Tensor4

/-- Unfolding `⟪u, v, w, x⟫₄` gives the component formula
`u i * v j * w k * x l`. -/
@[simp] theorem rankOne_apply (u v w x : Point) (i j k l : Fin n) :
    (⟪u, v, w, x⟫₄) i j k l = u i * v j * w k * x l := rfl

/-- The tensor-vector-vector-vector contraction
`∑ i j k l, V i j k l * u i * v j * w k * x l`. -/
def apply (V : _root_.Tensor4 n) (u v w x : Point) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, V i j k l * u i * v j * w k * x l

/-- Unfolding `Tensor4.apply` gives the coordinate contraction formula. -/
theorem apply_eq (V : _root_.Tensor4 n) (u v w x : Point) :
    V.apply u v w x = ∑ i, ∑ j, ∑ k, ∑ l, V i j k l * u i * v j * w k * x l := rfl

/-- Contracting a rank-one tensor against four vectors gives the corresponding product of
Euclidean inner products. -/
theorem apply_rankOne
    (u v w x a b c d : Point) :
    (⟪u, v, w, x⟫₄).apply a b c d =
      inner ℝ u a * inner ℝ v b * inner ℝ w c * inner ℝ x d := by
  let sx : ℝ := ∑ l, x l * d l
  let sw : ℝ := ∑ k, w k * c k
  let sv : ℝ := ∑ j, v j * b j
  -- Expand the contraction and rewrite the rank-one tensor into coordinate products.
  rw [apply_eq]
  simp_rw [rankOne_apply]
  -- Separate the four finite sums one index at a time until only Euclidean inner products remain.
  calc
    ∑ i, ∑ j, ∑ k, ∑ l, u i * v j * w k * x l * a i * b j * c k * d l
        = ∑ i, ∑ j, ∑ k, ((u i * a i) * (v j * b j) * (w k * c k)) * sx := by
            subst sx
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro l _
            ring
    _ = ∑ i, ∑ j, (((u i * a i) * (v j * b j)) * sw) * sx := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            subst sw
            rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = ∑ i, ((u i * a i) * sv) * (sw * sx) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            calc
              ∑ j, (((u i * a i) * (v j * b j)) * sw) * sx
                  = ∑ j, ((u i * a i) * (v j * b j)) * (sw * sx) := by
                      refine Finset.sum_congr rfl ?_
                      intro j _
                      ring
              _ = ((u i * a i) * sv) * (sw * sx) := by
                      subst sv
                      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = (∑ i, u i * a i) * (sv * (sw * sx)) := by
            calc
              ∑ i, ((u i * a i) * sv) * (sw * sx)
                  = ∑ i, (u i * a i) * (sv * (sw * sx)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i _
                      ring
              _ = (∑ i, u i * a i) * (sv * (sw * sx)) := by
                      rw [← Finset.sum_mul]
  -- Each factor is exactly the Euclidean inner product written in coordinates.
  subst sv sw sx
  simp [PiLp.inner_apply, mul_assoc, mul_comm]

/-- Flatten a fourth-order tensor into the canonical nested `PiLp` Hilbert-space owner used by
the source Frobenius-norm argument. -/
def flatten (V : _root_.Tensor4 n) : Flattened n :=
  WithLp.toLp 2 fun i : Fin n ↦
    WithLp.toLp 2 fun j : Fin n ↦
      WithLp.toLp 2 fun k : Fin n ↦
        WithLp.toLp 2 fun l : Fin n ↦ V i j k l

/-- Unfolding the canonical flattening recovers the original tensor coordinate. -/
@[simp] theorem flatten_apply
    (V : _root_.Tensor4 n) (i j k l : Fin n) :
    ((((flatten V).ofLp i).ofLp j).ofLp k).ofLp l = V i j k l := rfl

/-- The Frobenius norm of a fourth-order tensor is the `ℓ²` norm of its coordinate array. -/
def frobeniusNorm (V : _root_.Tensor4 n) : ℝ :=
  ‖flatten V‖

/-- Unfolding `V.frobeniusNorm` through the canonical flattening gives the ambient `ℓ²` norm on
the fully flattened tensor coordinates. -/
theorem frobeniusNorm_eq_flatten_norm (V : _root_.Tensor4 n) :
    V.frobeniusNorm = ‖flatten V‖ := rfl

/-- Unfolding `V.frobeniusNorm` gives the ambient `ℓ²` norm on the tensor coordinates through the
canonical flattening owner. -/
theorem frobeniusNorm_eq (V : _root_.Tensor4 n) :
    V.frobeniusNorm = ‖flatten V‖ :=
  frobeniusNorm_eq_flatten_norm V

/-- A symmetric fourth-order tensor is invariant under permuting its four coordinate indices. -/
def IsSymmetric (V : _root_.Tensor4 n) : Prop :=
  ∀ σ : Equiv.Perm (Fin 4), ∀ i : Fin 4 → Fin n,
    V (i (σ 0)) (i (σ 1)) (i (σ 2)) (i (σ 3)) = V (i 0) (i 1) (i 2) (i 3)

/-- Helper for Tensor4: the three adjacent coordinate symmetries imply invariance under each
generator `Equiv.swap t.castSucc t.succ` of `Perm (Fin 4)`. -/
lemma adjacentSwapInvariant
    (V : _root_.Tensor4 n)
    (h01 : ∀ i j k l, V i j k l = V j i k l)
    (h12 : ∀ i j k l, V i j k l = V i k j l)
    (h23 : ∀ i j k l, V i j k l = V i j l k)
    (t : Fin 3) (idx : Fin 4 → Fin n) :
    V (idx ((Equiv.swap t.castSucc t.succ) 0))
      (idx ((Equiv.swap t.castSucc t.succ) 1))
      (idx ((Equiv.swap t.castSucc t.succ) 2))
      (idx ((Equiv.swap t.castSucc t.succ) 3)) =
      V (idx 0) (idx 1) (idx 2) (idx 3) := by
  -- Each generator is one of the three adjacent swaps from the statement, so `fin_cases`
  -- reduces directly to the corresponding hypothesis.
  fin_cases t
  · simpa [Equiv.swap_apply_def] using (h01 (idx 0) (idx 1) (idx 2) (idx 3)).symm
  · simpa [Equiv.swap_apply_def] using (h12 (idx 0) (idx 1) (idx 2) (idx 3)).symm
  · simpa [Equiv.swap_apply_def] using (h23 (idx 0) (idx 1) (idx 2) (idx 3)).symm

/-- Helper for Tensor4: permutation invariance is closed under multiplying permutations in
`Perm (Fin 4)`. -/
lemma permInvariantMul
    (V : _root_.Tensor4 n)
    {σ τ : Equiv.Perm (Fin 4)}
    (hσ : ∀ idx : Fin 4 → Fin n,
      V (idx (σ 0)) (idx (σ 1)) (idx (σ 2)) (idx (σ 3)) =
        V (idx 0) (idx 1) (idx 2) (idx 3))
    (hτ : ∀ idx : Fin 4 → Fin n,
      V (idx (τ 0)) (idx (τ 1)) (idx (τ 2)) (idx (τ 3)) =
        V (idx 0) (idx 1) (idx 2) (idx 3)) :
    ∀ idx : Fin 4 → Fin n,
      V (idx ((σ * τ) 0)) (idx ((σ * τ) 1)) (idx ((σ * τ) 2)) (idx ((σ * τ) 3)) =
        V (idx 0) (idx 1) (idx 2) (idx 3) := by
  intro idx
  -- Apply invariance under the right factor to the reindexed coordinates, then under the left.
  calc
    V (idx ((σ * τ) 0)) (idx ((σ * τ) 1)) (idx ((σ * τ) 2)) (idx ((σ * τ) 3))
        = V ((idx ∘ σ) (τ 0)) ((idx ∘ σ) (τ 1)) ((idx ∘ σ) (τ 2)) ((idx ∘ σ) (τ 3)) := by
            simp [Equiv.Perm.mul_apply, Function.comp_apply]
    _ = V ((idx ∘ σ) 0) ((idx ∘ σ) 1) ((idx ∘ σ) 2) ((idx ∘ σ) 3) :=
          hτ (idx ∘ σ)
    _ = V (idx (σ 0)) (idx (σ 1)) (idx (σ 2)) (idx (σ 3)) := rfl
    _ = V (idx 0) (idx 1) (idx 2) (idx 3) := hσ idx

/-- Helper for Tensor4: invariance under the three adjacent transpositions already gives full
`Tensor4.IsSymmetric`. -/
lemma isSymmetricOfAdjacentTranspositions
    (V : _root_.Tensor4 n)
    (h01 : ∀ i j k l, V i j k l = V j i k l)
    (h12 : ∀ i j k l, V i j k l = V i k j l)
    (h23 : ∀ i j k l, V i j k l = V i j l k) :
    IsSymmetric V := by
  intro σ idx
  have hgen :
      σ ∈ Submonoid.closure (Set.range fun t : Fin 3 ↦ Equiv.swap t.castSucc t.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ 3]
    simp
  -- The adjacent swaps generate the whole permutation group, and the invariance predicate is
  -- closed under those generators, the identity, and multiplication.
  exact Submonoid.closure_induction
    (s := Set.range fun t : Fin 3 ↦ Equiv.swap t.castSucc t.succ)
    (motive := fun τ _ ↦ ∀ idx : Fin 4 → Fin n,
      V (idx (τ 0)) (idx (τ 1)) (idx (τ 2)) (idx (τ 3)) =
        V (idx 0) (idx 1) (idx 2) (idx 3))
    (fun τ hτ idx => by
      rcases hτ with ⟨t, rfl⟩
      exact adjacentSwapInvariant V h01 h12 h23 t idx)
    (by
      intro idx
      rfl)
    (fun τ υ hτ hυ hτinv hυinv idx => permInvariantMul V hτinv hυinv idx)
    hgen idx

/-- Tensor4: symmetry can be checked on the adjacent transpositions generating `Perm (Fin 4)`. -/
theorem isSymmetric_iff_adjacent_transpositions
    (V : _root_.Tensor4 n) :
    IsSymmetric V ↔
      (∀ i j k l, V i j k l = V j i k l) ∧
        (∀ i j k l, V i j k l = V i k j l) ∧
          ∀ i j k l, V i j k l = V i j l k := by
  constructor
  · intro hsymm
    -- Read off the three adjacent swaps directly from the full permutation-invariance axiom.
    refine ⟨?_, ?_, ?_⟩
    · intro i j k l
      simpa [Equiv.swap_apply_def] using (hsymm (Equiv.swap 0 1) ![i, j, k, l]).symm
    · intro i j k l
      simpa [Equiv.swap_apply_def] using (hsymm (Equiv.swap 1 2) ![i, j, k, l]).symm
    · intro i j k l
      simpa [Equiv.swap_apply_def] using (hsymm (Equiv.swap 2 3) ![i, j, k, l]).symm
  · intro h
    -- The three adjacent swaps generate `Perm (Fin 4)`, so the helper closure argument applies.
    rcases h with ⟨h01, h12, h23⟩
    exact isSymmetricOfAdjacentTranspositions V h01 h12 h23

end Tensor4

end
