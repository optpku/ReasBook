/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Swap

@[expose] public section

open scoped Matrix

namespace Matrix

section RowOperations

variable {n : ℕ}

/-- The elementary integer row-swap matrix exchanging rows `i` and `j`. -/
abbrev rowSwapMatrix (i j : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.swap ℤ i j

/-- The elementary integer row-sign matrix negating row `i`. -/
def rowNegMatrix (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  fun r c ↦ if r = c then if r = i then (-1 : ℤ) else 1 else 0

/-- The elementary integer row-addition matrix adding `c` times row `j` to row `i`. -/
def rowAddMatrix (i j : Fin n) (c : ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun r k ↦
    if r = i then
      if k = i then 1 else if k = j then c else 0
    else if r = k then 1 else 0

/-- A square integer matrix is elementary unimodular if it is a row swap, a row sign change,
or an integer row addition matrix. -/
def IsElementaryUnimodularRowMatrix (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∃ i j : Fin n, i ≠ j ∧ M = rowSwapMatrix i j) ∨
    (∃ i : Fin n, M = rowNegMatrix i) ∨
      ∃ i j : Fin n, ∃ c : ℤ, i ≠ j ∧ M = rowAddMatrix i j c

/-- A square integer matrix is reachable by unimodular row operations if it is obtained from the
identity by finitely many left multiplications by elementary unimodular row matrices. -/
def reachableByUnimodularRowOps (U : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ ops : List (Matrix (Fin n) (Fin n) ℤ),
    (∀ M ∈ ops, IsElementaryUnimodularRowMatrix M) ∧
      ops.foldl (fun A E ↦ E * A) (1 : Matrix (Fin n) (Fin n) ℤ) = U

/-- The determinant of a row-swap matrix is a unit in `ℤ`. -/
theorem isUnit_det_rowSwapMatrix (i j : Fin n) :
    IsUnit (rowSwapMatrix i j).det := by
  -- The swap matrix is its own left inverse, so its determinant is a unit.
  exact isUnit_det_of_left_inverse (swap_mul_self i j)

/-- The determinant of a row-sign matrix is a unit in `ℤ`. -/
theorem isUnit_det_rowNegMatrix (i : Fin n) :
    IsUnit (rowNegMatrix i).det := by
  -- Express the sign change through the determinant API for a scaled row update.
  have hneg :
      rowNegMatrix i =
        (1 : Matrix (Fin n) (Fin n) ℤ).updateRow i
          ((-1 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) i) := by
    ext r k
    by_cases hri : r = i
    · subst r
      by_cases hik : i = k
      · subst k
        simp [rowNegMatrix]
      · simp [rowNegMatrix, hik]
    · by_cases hrk : r = k
      · subst k
        simp [rowNegMatrix, hri]
      · simp [rowNegMatrix, hri, hrk]
  -- Scaling that row by `-1` multiplies the determinant of the identity by `-1`.
  rw [hneg, det_updateRow_smul, updateRow_eq_self, det_one, mul_one]
  exact isUnit_neg_one

/-- The determinant of a row-addition matrix is a unit in `ℤ`. -/
theorem isUnit_det_rowAddMatrix (i j : Fin n) (c : ℤ) (hij : i ≠ j) :
    IsUnit (rowAddMatrix i j c).det := by
  -- Put the custom matrix into the canonical identity-row-update form.
  have hadd :
      rowAddMatrix i j c =
        (1 : Matrix (Fin n) (Fin n) ℤ).updateRow i
          ((1 : Matrix (Fin n) (Fin n) ℤ) i +
            c • (1 : Matrix (Fin n) (Fin n) ℤ) j) := by
    ext r k
    by_cases hri : r = i
    · subst r
      by_cases hki : k = i
      · subst k
        simp [rowAddMatrix, hij.symm]
      · by_cases hkj : k = j
        · subst k
          simp [rowAddMatrix, hij, hki]
        · have hik : i ≠ k := Ne.symm hki
          have hjk : j ≠ k := Ne.symm hkj
          simp [rowAddMatrix, hki, hkj, hik, hjk]
    · by_cases hrk : r = k
      · subst k
        simp [rowAddMatrix, hri]
      · simp [rowAddMatrix, hri, hrk]
  -- Adding a multiple of a distinct row preserves the identity determinant.
  rw [hadd, det_updateRow_add_smul_self _ hij c, det_one]
  exact isUnit_one

/-- The identity matrix is reachable by the empty sequence of unimodular row operations. -/
theorem reachableByUnimodularRowOps_one :
    reachableByUnimodularRowOps (1 : Matrix (Fin n) (Fin n) ℤ) := by
  -- The empty operation list has no membership obligations and folds to the identity.
  refine ⟨[], ?_, ?_⟩
  · intro M hM
    simp at hM
  · rfl

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3/RowOperations.lean
Reachability by unimodular row operations is closed under concatenating row-operation sequences. -/
theorem reachableByUnimodularRowOps_mul
    {U V : Matrix (Fin n) (Fin n) ℤ}
    (hU : reachableByUnimodularRowOps U)
    (hV : reachableByUnimodularRowOps V) :
    reachableByUnimodularRowOps (V * U) := by
  -- Extract the two operation lists and their accumulated left products.
  rcases hU with ⟨opsU, hOpsU, hFoldU⟩
  rcases hV with ⟨opsV, hOpsV, hFoldV⟩
  -- Folding left multiplications from `A` gives the fold from `1`, followed by `A`.
  have foldFromInitial
      (ops : List (Matrix (Fin n) (Fin n) ℤ))
      (A : Matrix (Fin n) (Fin n) ℤ) :
      ops.foldl (fun X E ↦ E * X) A =
        ops.foldl (fun X E ↦ E * X) 1 * A := by
    induction ops generalizing A with
    | nil => simp
    | cons E ops ih =>
        simp only [List.foldl_cons]
        calc
          ops.foldl (fun X F ↦ F * X) (E * A) =
              ops.foldl (fun X F ↦ F * X) 1 * (E * A) := ih (E * A)
          _ = (ops.foldl (fun X F ↦ F * X) 1 * E) * A := by
            rw [mul_assoc]
          _ = ops.foldl (fun X F ↦ F * X) E * A := by
            exact congrArg (fun X ↦ X * A) (ih E).symm
          _ = ops.foldl (fun X F ↦ F * X) (E * 1) * A := by
            exact congrArg
              (fun X ↦ ops.foldl (fun Y F ↦ F * Y) X * A) (mul_one E).symm
  -- Concatenation preserves elementary membership and composes the accumulated products.
  refine ⟨opsU ++ opsV, ?_, ?_⟩
  · intro M hM
    rw [List.mem_append] at hM
    cases hM with
    | inl h => exact hOpsU M h
    | inr h => exact hOpsV M h
  · rw [List.foldl_append, hFoldU, foldFromInitial, hFoldV]

end RowOperations

end Matrix

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_ed002b0b44801c329960"
#print axioms _root_.Matrix.reachableByUnimodularRowOps_mul
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_ed002b0b44801c329960"
