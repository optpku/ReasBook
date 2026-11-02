import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_16.ch3_sec3_16_definition_3_16_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open Module
open scoped Matrix

section Remark316Extra2

section InnerProduct

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [Finite ι]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Helper for Remark 3.16-extra-2: if a vector is orthogonal to every basis vector of `L`, then
it is orthogonal to every vector of `L`. -/
lemma inner_eq_zero_of_basis_inner_eq_zero
    (L : Submodule 𝕜 E) (b : Basis ι 𝕜 L) {x : E}
    (hx : ∀ i, ⟪((b i : L) : E), x⟫ = 0) :
    ∀ y : L, ⟪(y : E), x⟫ = 0 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  intro y
  have hy' : (((∑ i, (b.repr y i) • b i : L) : L) : E) = (y : E) :=
    congrArg (fun z : L ↦ (z : E)) (b.sum_repr y)
  have hcoe :
      (((∑ i, (b.repr y i) • b i : L) : L) : E) =
        ∑ i, (b.repr y i) • (((b i : L) : E) : E) := by
    change L.subtype (∑ i, (b.repr y i) • b i) = ∑ i, (b.repr y i) • L.subtype (b i)
    rw [map_sum]
    simp
  have hy : (y : E) = ∑ i, (b.repr y i) • ((((b i : L) : E) : E)) := hy'.symm.trans hcoe
  calc
    ⟪(y : E), x⟫ = ⟪(∑ i, (b.repr y i) • (((b i : L) : E) : E)), x⟫ := by rw [hy]
    _ = ∑ i, (starRingEnd 𝕜) (b.repr y i) * ⟪((b i : L) : E), x⟫ := by
      simp_rw [sum_inner, inner_smul_left]
    _ = 0 := by simp [hx]

/-- A vector belongs to the orthogonal complement exactly when it is orthogonal to each basis
vector of the subspace. -/
theorem mem_orthogonal_iff_inner_basis_eq_zero
    (L : Submodule 𝕜 E) (b : Basis ι 𝕜 L) (x : E) :
    x ∈ Lᗮ ↔ ∀ i, ⟪((b i : L) : E), x⟫ = 0 := by
  constructor
  · intro hx i
    exact (L.mem_orthogonal x).1 hx _ (b i).property
  · intro hx
    rw [Submodule.mem_orthogonal]
    intro y hy
    simpa using inner_eq_zero_of_basis_inner_eq_zero L b hx ⟨y, hy⟩

/-- Remark 3.16-extra-2 (1): if `b = (ℓ¹, ..., ℓᵗ)` is a basis of a subspace `L`, then the
orthogonal complement of `L` is the intersection of the kernels of the linear forms
`x ↦ ⟪(b i : E), x⟫`. This is the basis-indexed specialization of
`Submodule.orthogonal_eq_inter`. -/
theorem orthogonal_eq_iInf_ker_inner_basis
    (L : Submodule 𝕜 E) (b : Basis ι 𝕜 L) :
    Lᗮ = ⨅ i, LinearMap.ker ((innerSL 𝕜 (((b i : L) : E))).toLinearMap) := by
  ext x
  rw [mem_orthogonal_iff_inner_basis_eq_zero L b]
  simp [LinearMap.mem_ker]

end InnerProduct

section FiniteDimensional

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/- Remark 3.16-extra-2 (2), owner form: in a finite-dimensional inner product space,
`Submodule.finrank_add_finrank_orthogonal` is the canonical dimension statement. -/
recall Submodule.finrank_add_finrank_orthogonal

end FiniteDimensional

section Euclidean

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Remark 3.16-extra-2 (2): for a subspace `L ⊆ ℝ^n`, the dimensions of `L` and `Lᗮ` add up
to `n`. This is the `ℝ^n` specialization of `Submodule.finrank_add_finrank_orthogonal`. -/
theorem finrank_add_finrank_orthogonal_eq_fin (L : Submodule ℝ E) :
    finrank ℝ L + finrank ℝ Lᗮ = n := by
  simpa [finrank_euclideanSpace_fin] using L.finrank_add_finrank_orthogonal

end Euclidean

section RealInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped Polar

/- Remark 3.16-extra-2 (3), owner form: `orthogonalBilin_innerₗ` identifies orthogonal
complements with the orthogonal submodule for the real inner-product bilinear form. -/
recall orthogonalBilin_innerₗ

/-- Helper for Remark 3.16-extra-2 (3): for a linear subspace of a real inner-product space,
membership in the chapter polar is the same as membership in the orthogonal complement. -/
theorem mem_polar_submodule_iff_mem_orthogonal
    (L : Submodule ℝ E) (x : E) :
    x ∈ (L : Set E)* ↔ x ∈ Submodule.orthogonal L := by
  rw [Set.mem_polar_iff, Submodule.mem_orthogonal]
  constructor
  · intro hx y hy
    have hzero : inner ℝ x y = 0 := by
      by_contra hzero
      let t : ℝ := 2 / inner ℝ x y
      have ht : inner ℝ x (t • y) ≤ 1 := hx (t • y) (L.smul_mem t hy)
      have htwo : inner ℝ x (t • y) = 2 := by
        calc
          inner ℝ x (t • y) = t * inner ℝ x y := by rw [inner_smul_right]
          _ = 2 := by
            dsimp [t]
            field_simp [hzero]
      linarith
    simpa [inner_eq_zero_symm] using hzero
  · intro hx y hy
    have hzero : inner ℝ x y = 0 := by
      simpa [inner_eq_zero_symm] using hx y hy
    simp [hzero]

/-- Remark 3.16-extra-2 (3): for a linear subspace `L`, the chapter polar `L*` is the
orthogonal complement `Lᗮ`. -/
theorem polar_submodule_eq_orthogonal (L : Submodule ℝ E) :
    (L : Set E)* = (Submodule.orthogonal L : Set E) := by
  ext x
  exact mem_polar_submodule_iff_mem_orthogonal L x

/-- Helper for Remark 3.16-extra-2: the inner-product polar submodule is characterized by the same
orthogonality condition as the orthogonal complement. -/
lemma mem_polarSubmodule_inner_iff
    (L : Submodule ℝ E) (x : E) :
    x ∈ LinearMap.polarSubmodule (innerₗ E) L ↔ ∀ y ∈ L, inner ℝ y x = 0 := by
  change x ∈ (innerₗ E).polar L ↔ ∀ y ∈ L, inner ℝ y x = 0
  rw [LinearMap.polar_subMulAction]
  simp

/-- Companion bridge for Remark 3.16-extra-2 (3): over `ℝ`, the orthogonal complement of a
subspace is its polar submodule for the inner-product bilinear form. -/
theorem orthogonal_eq_polarSubmodule_inner (L : Submodule ℝ E) :
    Lᗮ = LinearMap.polarSubmodule (innerₗ E) L := by
  ext x
  rw [Submodule.mem_orthogonal, mem_polarSubmodule_inner_iff]

end RealInner

end Remark316Extra2
