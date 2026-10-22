/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.Block

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [Zero R]

-- `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs` already owns `Matrix.IsIrreducible`
-- for the nonnegative-matrix notion, so this file keeps the source's unrestricted
-- subset-witness notion under distinct names. Specializing to `Matrix (Fin n) (Fin n) ℝ`
-- recovers the textbook real-matrix definition.

/-- Chapter01 Definition 1.2.11. A square matrix indexed by a finite type is subset reducible
if there is a nonempty proper subset `J` of indices such that `A k j = 0` for every `k ∈ J` and
`j ∉ J`. For `A : Matrix (Fin n) (Fin n) ℝ`, this is exactly the source definition. -/
def IsSubsetReducible (A : Matrix ι ι R) : Prop :=
  ∃ J : Finset ι,
    J.Nonempty ∧ J.card < Fintype.card ι ∧
      ∀ ⦃k j : ι⦄, k ∈ J → j ∉ J → A k j = 0

/-- Source subset reducibility is classically decidable. -/
noncomputable instance instDecidableIsSubsetReducible (A : Matrix ι ι R) :
    Decidable A.IsSubsetReducible :=
  Classical.propDecidable _

/-- A square matrix is source-irreducible if it is not subset reducible. -/
def IsSubsetIrreducible (A : Matrix ι ι R) : Prop :=
  ¬ A.IsSubsetReducible

/- The source reducibility predicate is equivalent to the subset-witness formulation. -/
omit [DecidableEq ι] in
@[simp] theorem isSubsetReducible_iff (A : Matrix ι ι R) :
    A.IsSubsetReducible ↔
      ∃ J : Finset ι,
        J.Nonempty ∧ J.card < Fintype.card ι ∧
          ∀ ⦃k j : ι⦄, k ∈ J → j ∉ J → A k j = 0 :=
  Iff.rfl

/-- The subset-reducibility condition is equivalent to a simultaneous row-column reindexing into a
two-by-two block upper triangular form. The complement block is listed first so that the zero
lower-left block matches the source vanishing condition `A k j = 0` for `k ∈ J` and `j ∉ J`. -/
theorem isSubsetReducible_iff_exists_blockTriangularForm (A : Matrix ι ι R) :
    A.IsSubsetReducible ↔
      ∃ J : Finset ι,
        J.Nonempty ∧ J.card < Fintype.card ι ∧
          let e := (Equiv.sumCompl fun i ↦ i ∉ J).symm
          (reindex e e A).BlockTriangular (Sum.elim (fun _ ↦ (0 : Fin 2)) fun _ ↦ 1) := by
  constructor
  · rintro ⟨J, hJ_nonempty, hJ_card, hzero⟩
    refine ⟨J, hJ_nonempty, hJ_card, ?_⟩
    let e := (Equiv.sumCompl fun i ↦ i ∉ J).symm
    rw [blockTriangular_reindex_iff]
    intro i j hij
    have hi : i ∈ J := by
      by_contra hi
      have hi0 : (Sum.elim (fun _ ↦ (0 : Fin 2)) fun _ ↦ 1) (e i) = 0 := by
        simp [e, hi]
      have : ¬ (Sum.elim (fun _ ↦ (0 : Fin 2)) fun _ ↦ 1) (e j) <
          (Sum.elim (fun _ ↦ (0 : Fin 2)) fun _ ↦ 1) (e i) := by
        simp [hi0]
      exact this hij
    have hj : j ∉ J := by
      by_contra hj
      have hi1 : (Sum.elim (fun _ ↦ (0 : Fin 2)) fun _ ↦ 1) (e i) = 1 := by
        simp [e, hi]
      have hj1 : (Sum.elim (fun _ ↦ (0 : Fin 2)) fun _ ↦ 1) (e j) = 1 := by
        simp [e, hj]
      have : ¬ (Sum.elim (fun _ ↦ (0 : Fin 2)) fun _ ↦ 1) (e j) <
          (Sum.elim (fun _ ↦ (0 : Fin 2)) fun _ ↦ 1) (e i) := by
        simp [hi1, hj1]
      exact this hij
    exact hzero hi hj
  · rintro ⟨J, hJ_nonempty, hJ_card, hblock⟩
    refine ⟨J, hJ_nonempty, hJ_card, ?_⟩
    let e := (Equiv.sumCompl fun i ↦ i ∉ J).symm
    rw [blockTriangular_reindex_iff] at hblock
    intro k j hk hj
    exact hblock (by simp [hk, hj])

/- The source irreducible predicate is the negation of `Matrix.IsSubsetReducible`. -/
omit [DecidableEq ι] in
@[simp] theorem isSubsetIrreducible_iff_not_isSubsetReducible (A : Matrix ι ι R) :
    A.IsSubsetIrreducible ↔ ¬ A.IsSubsetReducible :=
  Iff.rfl

end Matrix
