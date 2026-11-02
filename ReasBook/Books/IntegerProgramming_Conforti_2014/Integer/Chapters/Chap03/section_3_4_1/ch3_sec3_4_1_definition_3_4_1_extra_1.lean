import Mathlib

universe u v w

open scoped BigOperators Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the declarations
-- below use the standard mathlib APIs for `Submodule.span`, `LinearIndependent`, `Basis`,
-- matrix kernels, and matrix rank.

variable {K : Type u}
variable {n : Type v}

/- Definition 3.4.1-extra-1 (1): the canonical owner for “a vector lies in the span iff it is a
linear combination” is `Submodule.mem_span_range_iff_exists_fun`. -/
recall Submodule.mem_span_range_iff_exists_fun

/- Definition 3.4.1-extra-1 (2): the canonical owner for the finite-family criterion for linear
independence is `Fintype.linearIndependent_iff`. -/
recall Fintype.linearIndependent_iff

/- Definition 3.4.1-extra-1 (5): the canonical owner for the cardinality of a finite basis is
`Module.finrank_eq_card_basis`. -/
recall Module.finrank_eq_card_basis

section Matrix

/-
Domain sampling for the matrix part:
- source-facing layer: solution sets of homogeneous systems `A *ᵥ x = 0` in the coordinate vector
  space `n → K`
- core/canonical owner: the commutative mathlib owners `A.mulVecLin.ker` and `Matrix.rank`
- bridge/view: the zero locus `{x | A *ᵥ x = 0}` of the matrix equation

Because this section uses the left-action owner `mulVecLin` on `n → K`, it stays in the
commutative coordinate-space setting of the upstream matrix API.
-/
variable [Field K] [Fintype n]

/-- Helper for Definition 3.4.1-extra-1: composing the quotient map with quotient coordinates does
not enlarge the kernel, so its kernel is exactly the original submodule. -/
lemma quotient_coordinate_map_ker_eq_submodule (U : Submodule K (n → K)) :
    LinearMap.ker (((Module.finBasis K ((n → K) ⧸ U)).equivFun.toLinearMap).comp U.mkQ) = U := by
  -- The quotient map already has kernel `U`, and quotient coordinates are injective.
  rw [LinearMap.ker_comp_of_ker_eq_bot]
  · exact Submodule.ker_mkQ (p := U)
  · exact ((Module.finBasis K ((n → K) ⧸ U)).equivFun.ker :
      LinearMap.ker ((Module.finBasis K ((n → K) ⧸ U)).equivFun.toLinearMap) = ⊥)

/-- Helper for Definition 3.4.1-extra-1: every submodule of the finite coordinate space can be
realized as the zero locus of a homogeneous matrix equation. -/
lemma submodule_set_eq_matrix_zero_locus (U : Submodule K (n → K)) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) n K, (U : Set (n → K)) = {x | A *ᵥ x = 0} := by
  classical
  let ψ : (n → K) →ₗ[K] Fin (Module.finrank K ((n → K) ⧸ U)) → K :=
    ((Module.finBasis K ((n → K) ⧸ U)).equivFun.toLinearMap).comp U.mkQ
  refine ⟨Module.finrank K ((n → K) ⧸ U), LinearMap.toMatrix' ψ, ?_⟩
  ext x
  -- Rewrite membership in `U` through the quotient-coordinate kernel, then convert that linear
  -- map to its matrix form.
  constructor
  · intro hx
    have hxker : x ∈ LinearMap.ker ψ := by
      rw [quotient_coordinate_map_ker_eq_submodule (U := U)]
      exact hx
    have hψ : ψ x = 0 := by
      simpa [LinearMap.mem_ker] using hxker
    simpa [LinearMap.toMatrix'_mulVec] using hψ
  · intro hx
    have hψ : ψ x = 0 := by
      simpa [LinearMap.toMatrix'_mulVec] using hx
    have hxker : x ∈ LinearMap.ker ψ := by
      rw [LinearMap.mem_ker]
      exact hψ
    rw [quotient_coordinate_map_ker_eq_submodule (U := U)] at hxker
    exact hxker

/-- Helper for Definition 3.4.1-extra-1: the zero locus of `A *ᵥ x = 0` is exactly the underlying
set of the kernel of the associated linear map. -/
lemma matrix_zero_locus_eq_ker_set {m : ℕ} (A : Matrix (Fin m) n K) :
    ((A.mulVecLin.ker : Submodule K (n → K)) : Set (n → K)) = {x | A *ᵥ x = 0} := by
  ext x
  -- Unfolding the kernel reduces the statement to the defining equation `A *ᵥ x = 0`.
  simp [LinearMap.mem_ker]

/-- Definition 3.4.1-extra-1 (3): a subset of the finite coordinate space `n → K` is a linear
space exactly when it is the underlying set of a submodule, equivalently when it is the solution
set of a homogeneous linear system `A *ᵥ x = 0`. -/
theorem set_is_linear_space_iff_eq_matrix_kernel
    (L : Set (n → K)) :
    (∃ U : Submodule K (n → K), (U : Set (n → K)) = L) ↔
      ∃ m : ℕ, ∃ A : Matrix (Fin m) n K, L = {x | A *ᵥ x = 0} := by
  constructor
  · rintro ⟨U, rfl⟩
    -- Route correction: realize the linear space through the quotient by `U`, then convert the
    -- quotient-coordinate map to a matrix.
    simpa using submodule_set_eq_matrix_zero_locus (U := U)
  · rintro ⟨m, A, hA⟩
    -- The reverse direction uses the canonical submodule kernel of the matrix action.
    refine ⟨A.mulVecLin.ker, ?_⟩
    calc
      ((A.mulVecLin.ker : Submodule K (n → K)) : Set (n → K)) = {x | A *ᵥ x = 0} :=
        matrix_zero_locus_eq_ker_set (A := A)
      _ = L := hA.symm

/-- Definition 3.4.1-extra-1 (4): the dimension of the solution space of `A *ᵥ x = 0` is
the number of columns minus the rank. -/
theorem finrank_matrix_kernel_eq_card_sub_rank
    {m : Type w} (A : Matrix m n K) :
    Module.finrank K A.mulVecLin.ker = Fintype.card n - A.rank := by
  have h : A.rank + Module.finrank K A.mulVecLin.ker = Fintype.card n := by
    simpa [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  omega

/-- Definition 3.4.1-extra-1 (4): for a matrix with `n` columns indexed by `Fin n`, the
dimension of the solution space of `A *ᵥ x = 0` is `n - rank(A)`. -/
theorem finrank_matrix_kernel_eq_ambient_sub_rank
    {m : Type*} {n : ℕ} (A : Matrix m (Fin n) K) :
    Module.finrank K A.mulVecLin.ker = n - A.rank := by
  simpa using finrank_matrix_kernel_eq_card_sub_rank A

end Matrix

section Span

variable [DivisionRing K]

/-- Definition 3.4.1-extra-1 (6): if `S'` is an inclusionwise maximal linearly independent subset
of `S`, then `S'` generates the same linear space as `S`. This is stated on the ambient set
`S' ⊆ S` through the canonical owner `LinearIndepOn K id S'`. -/
theorem span_eq_span_of_maximal_linearly_independent_subset
    {V : Type*} [AddCommGroup V] [Module K V] {S S' : Set V}
    (hsubset : S' ⊆ S)
    (hindep : LinearIndepOn K id S')
    (hmax : ∀ ⦃x : V⦄, x ∈ S → x ∉ S' → ¬ LinearIndepOn K id (insert x S')) :
    Submodule.span K S = Submodule.span K S' := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro x hx
    by_cases hx' : x ∈ S'
    · exact Submodule.subset_span hx'
    · by_contra hxspan
      have hinsert : LinearIndepOn K id (insert x S') :=
        (LinearIndepOn.notMem_span_iff_id hindep).1 hxspan |>.1
      exact hmax hx hx' hinsert
  · exact Submodule.span_mono hsubset

end Span
