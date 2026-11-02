import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic search tools such as
-- `lean_leansearch`, so the canonical API was verified directly from mathlib's
-- `Matrix.Determinant.TotallyUnimodular` file and the local Chapter 4 usage in `Theorem 4.4`.

/- Definition 4.2-extra-1 (1): a matrix is totally unimodular exactly when every square
submatrix has determinant `0`, `1`, or `-1`. In mathlib this is the canonical predicate
`Matrix.IsTotallyUnimodular`, and `Matrix.isTotallyUnimodular_iff` is its square-submatrix
characterization. -/
recall Matrix.IsTotallyUnimodular
recall Matrix.isTotallyUnimodular_iff

/- Definition 4.2-extra-1 (2): it follows from total unimodularity that every entry of the matrix
is `0`, `1`, or `-1`. In mathlib this is the theorem `Matrix.IsTotallyUnimodular.apply`. -/
recall Matrix.IsTotallyUnimodular.apply

private def exampleMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![(-1 : ℤ), 1, 0; 1, 0, 1; 0, 1, 1]

private theorem exampleMatrix_minor_det_mem_range_fin_zero :
    ∀ f : Fin 0 → Fin 3, ∀ g : Fin 0 → Fin 3, f.Injective → g.Injective →
      (exampleMatrix.submatrix f g).det ∈ Set.range SignType.cast := by
  intro f g _ _
  refine ⟨1, ?_⟩
  simp [exampleMatrix]

set_option linter.style.nativeDecide false in
private theorem exampleMatrix_minor_det_mem_range_fin_one :
    ∀ f : Fin 1 → Fin 3, ∀ g : Fin 1 → Fin 3, f.Injective → g.Injective →
      (exampleMatrix.submatrix f g).det ∈ Set.range SignType.cast := by
  native_decide

set_option linter.style.nativeDecide false in
private theorem exampleMatrix_minor_det_mem_range_fin_two :
    ∀ f : Fin 2 → Fin 3, ∀ g : Fin 2 → Fin 3, f.Injective → g.Injective →
      (exampleMatrix.submatrix f g).det ∈ Set.range SignType.cast := by
  native_decide

set_option linter.style.nativeDecide false in
private theorem exampleMatrix_minor_det_mem_range_fin_three :
    ∀ f : Fin 3 → Fin 3, ∀ g : Fin 3 → Fin 3, f.Injective → g.Injective →
      (exampleMatrix.submatrix f g).det ∈ Set.range SignType.cast := by
  native_decide

private theorem exampleMatrix_isTotallyUnimodular : exampleMatrix.IsTotallyUnimodular := by
  intro k f g hf hg
  have hk : k ≤ 3 := by
    simpa using Fintype.card_le_of_injective f hf
  interval_cases k
  · exact exampleMatrix_minor_det_mem_range_fin_zero f g hf hg
  · exact exampleMatrix_minor_det_mem_range_fin_one f g hf hg
  · exact exampleMatrix_minor_det_mem_range_fin_two f g hf hg
  · exact exampleMatrix_minor_det_mem_range_fin_three f g hf hg

/-- Definition 4.2-extra-1: the matrix
`!![-1, 1, 0; 1, 0, 1; 0, 1, 1]` is totally unimodular. -/
theorem definition_4_2_extra_1_example_matrix_isTotallyUnimodular :
    ((!![(-1 : ℤ), 1, 0; 1, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) ℤ)).IsTotallyUnimodular := by
  simpa [exampleMatrix] using exampleMatrix_isTotallyUnimodular
