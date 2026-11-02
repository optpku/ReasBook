import Mathlib

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the declarations
-- below were matched against the local Chapter 3 matrix/vector conventions and mathlib's
-- `LinearIndependent`, `Matrix.submatrix`, `Matrix.mulVec`, and `Matrix.vecMul` APIs.

section Definition314Extra1

variable {m n : ℕ}
variable {𝕜 : Type*}

/-- For Definition 3.14-extra-1 (1): the feasible solutions of the standard equality-form system
`A x = b`, `x ≥ 0`. -/
def standard_equality_form
    [NonUnitalNonAssocSemiring 𝕜] [Preorder 𝕜]
    (A : Matrix (Fin m) (Fin n) 𝕜)
    (b : Fin m → 𝕜) : Set (Fin n → 𝕜) :=
  {x : Fin n → 𝕜 | A *ᵥ x = b ∧ 0 ≤ x}

/-- Membership in `standard_equality_form A b` is exactly the system `A *ᵥ x = b` together with
coordinatewise nonnegativity. -/
theorem mem_standard_equality_form_iff
    [NonUnitalNonAssocSemiring 𝕜] [Preorder 𝕜]
    {A : Matrix (Fin m) (Fin n) 𝕜}
    {b : Fin m → 𝕜}
    {x : Fin n → 𝕜} :
    x ∈ standard_equality_form A b ↔ A *ᵥ x = b ∧ 0 ≤ x := Iff.rfl

/-- Membership in `standard_equality_form A b` together with integrality on the coordinates
indexed by `I` is exactly the conjunction of the equality constraints, nonnegativity, and the
indexed integrality conditions. -/
theorem mem_standard_equality_form_inter_integral_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (x : Fin n → ℝ) :
    x ∈ standard_equality_form A b ∩ {x : Fin n → ℝ | ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ)} ↔
      A *ᵥ x = b ∧ 0 ≤ x ∧ ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ) := by
  rw [Set.mem_inter_iff, mem_standard_equality_form_iff]
  constructor
  · rintro ⟨hx, hI⟩
    exact ⟨hx.1, hx.2, hI⟩
  · rintro ⟨hAx, hx_nonneg, hI⟩
    exact ⟨⟨hAx, hx_nonneg⟩, hI⟩

open Set.powersetCard

/-- For Definition 3.14-extra-1 (4): a basis for `A` is a choice of `m` columns whose square
submatrix is nonsingular. The primitive data is the underlying `m`-element column set; the
ordered embedding used to form `A_B` is the canonical increasing enumeration of that set. -/
structure standard_form_basis
    [Semiring 𝕜]
    (A : Matrix (Fin m) (Fin n) 𝕜) where
  columns : Set.powersetCard (Fin n) m
  basis_matrix_isUnit :
    IsUnit (A.submatrix id (ofFinEmbEquiv.symm columns))

namespace standard_form_basis

open Set.powersetCard

section Semiring

variable [Semiring 𝕜]
variable {A : Matrix (Fin m) (Fin n) 𝕜}

/-- The canonical increasing enumeration of the basis columns. -/
abbrev cols (B : standard_form_basis A) : Fin m ↪o Fin n :=
  ofFinEmbEquiv.symm B.columns

/-- The square matrix `A_B` extracted from the basis columns. -/
abbrev basis_matrix (B : standard_form_basis A) : Matrix (Fin m) (Fin m) 𝕜 :=
  A.submatrix id B.cols

notation:max "A₍" B "₎" => standard_form_basis.basis_matrix B

/-- The canonical ordered embedding enumerates exactly the chosen basis columns. -/
theorem mem_columns_iff_mem_range
    (B : standard_form_basis A)
    (j : Fin n) :
    j ∈ B.columns ↔ j ∈ Set.range B.cols := by
  simpa [cols] using
    (mem_range_ofFinEmbEquiv_symm_iff_mem B.columns j).symm

/-- The entries of the basis matrix are the entries of `A` on the chosen columns. -/
theorem basis_matrix_apply
    (B : standard_form_basis A)
    (i j : Fin m) :
    A₍B₎ i j = A i (B.cols j) := rfl

/-- Helper for Definition 3.14-extra-1: the canonical basis-column enumeration identifies
`Fin m` with the range of `B.cols`. -/
noncomputable abbrev colsRangeEquiv
    (B : standard_form_basis A) :
    Fin m ≃ Set.range B.cols :=
  Equiv.ofInjective B.cols B.cols.injective

/-- The restricted cost vector `c_B` obtained by reading `c` on the basis columns. -/
abbrev basis_costs
    (B : standard_form_basis A)
    (c : Fin n → 𝕜) : Fin m → 𝕜 :=
  fun i ↦ c (B.cols i)

notation:max c "₍" B "₎" => standard_form_basis.basis_costs B c

/-- The entries of `c_B` are the coordinates of `c` on the basis columns. -/
theorem basis_costs_apply
    (B : standard_form_basis A)
    (c : Fin n → 𝕜)
    (i : Fin m) :
    c₍B₎ i = c (B.cols i) := rfl

end Semiring

section Field

variable [Field 𝕜]
variable {A : Matrix (Fin m) (Fin n) 𝕜}

/-- For Definition 3.14-extra-1 (5): the basic variables attached to a basis satisfy
`x_B = A_B⁻¹ b`. -/
noncomputable abbrev basic_variables
    (B : standard_form_basis A)
    (b : Fin m → 𝕜) : Fin m → 𝕜 :=
  A₍B₎⁻¹ *ᵥ b

notation:max "x₍" B "₎" => standard_form_basis.basic_variables B

/-- `x_B` is the vector `(A_B)⁻¹ b`. -/
theorem basic_variables_eq_inv_mulVec
    (B : standard_form_basis A)
    (b : Fin m → 𝕜) :
    x₍B₎ b = A₍B₎⁻¹ *ᵥ b := rfl

/-- The basic solution attached to `B` is the full `n`-vector whose nonzero coordinates occur on
the basis columns and whose basis coordinates are `x_B = A_B⁻¹ b`. -/
noncomputable def basic_solution
    (B : standard_form_basis A)
    (b : Fin m → 𝕜) : Fin n → 𝕜 :=
  Function.extend B.cols (x₍B₎ b) 0

/-- On the basis columns, the full basic solution agrees with `x_B`. -/
theorem basic_solution_apply_cols
    (B : standard_form_basis A)
    (b : Fin m → 𝕜)
    (i : Fin m) :
    B.basic_solution b (B.cols i) = x₍B₎ b i := by
  have hcols : Function.Injective B.cols := B.cols.injective
  simpa [basic_solution] using hcols.extend_apply (x₍B₎ b) (0 : Fin n → 𝕜) i

/-- Away from the chosen basis columns, the full basic solution vanishes. -/
theorem basic_solution_eq_zero_of_not_mem_columns
    (B : standard_form_basis A)
    (b : Fin m → 𝕜)
    {j : Fin n}
    (hj : j ∉ B.columns) :
    B.basic_solution b j = 0 := by
  have hrange : j ∉ Set.range B.cols := by
    simpa [B.mem_columns_iff_mem_range j] using hj
  have hcols : ¬ ∃ i, B.cols i = j := by
    simpa [Set.mem_range] using hrange
  rw [basic_solution]
  simpa using Function.extend_apply' (x₍B₎ b) (0 : Fin n → 𝕜) j hcols

/-- Helper for Definition 3.14-extra-1: multiplying `A` by the full basic solution is the same as
multiplying the square basis matrix `A₍B₎` by the basic-variable vector `x₍B₎ b`. -/
theorem basic_solution_mulVec_eq_basis_matrix_mulVec
    (B : standard_form_basis A)
    (b : Fin m → 𝕜) :
    A *ᵥ B.basic_solution b = A₍B₎ *ᵥ x₍B₎ b := by
  -- Route correction: first restrict the row sum to the basis-column range, then reindex it by
  -- the canonical enumeration `B.cols`.
  ext i
  calc
    (A *ᵥ B.basic_solution b) i = dotProduct (fun j : Fin n ↦ A i j) (B.basic_solution b) := by
      change dotProduct (fun j : Fin n ↦ A i j) (B.basic_solution b) =
        dotProduct (fun j : Fin n ↦ A i j) (B.basic_solution b)
      rfl
    _ = ∑ j : Fin n, A i j * B.basic_solution b j := by
          simp [dotProduct]
    _ =
        Finset.sum (Finset.univ.filter (fun j : Fin n ↦ j ∈ Set.range B.cols))
          (fun j : Fin n ↦ A i j * B.basic_solution b j) := by
            -- Coordinates outside the basis range vanish in the extended basic solution.
            refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
            intro j _ hj_not_mem
            have hj_not_range : j ∉ Set.range B.cols := by
              simpa using hj_not_mem
            have hj_not_columns : j ∉ B.columns := by
              simpa [B.mem_columns_iff_mem_range j] using hj_not_range
            rw [B.basic_solution_eq_zero_of_not_mem_columns b hj_not_columns, mul_zero]
    _ = ∑ j : Set.range B.cols, A i j.1 * B.basic_solution b j.1 := by
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := Finset.univ)
              (p := fun j : Fin n ↦ j ∈ Set.range B.cols)
              (f := fun j : Fin n ↦ A i j * B.basic_solution b j)).symm
    _ = ∑ k : Fin m, A i (B.cols k) * B.basic_solution b (B.cols k) := by
          -- Reindex the surviving sum by the canonical equivalence `Fin m ≃ Set.range B.cols`.
          exact
            (Fintype.sum_equiv B.colsRangeEquiv
              (fun k : Fin m ↦ A i (B.cols k) * B.basic_solution b (B.cols k))
              (fun j : Set.range B.cols ↦ A i j.1 * B.basic_solution b j.1)
              (fun k ↦ rfl)).symm
    _ = ∑ k : Fin m, A₍B₎ i k * x₍B₎ b k := by
          -- On basis columns, `basic_solution` agrees with `x_B`, and `A₍B₎` records those columns.
          simp [B.basic_solution_apply_cols]
    _ = dotProduct (fun k : Fin m ↦ A₍B₎ i k) (x₍B₎ b) := by
          simp [dotProduct]
    _ = (A₍B₎ *ᵥ x₍B₎ b) i := by
          change dotProduct (fun k : Fin m ↦ A₍B₎ i k) (x₍B₎ b) =
            dotProduct (fun k : Fin m ↦ A₍B₎ i k) (x₍B₎ b)
          rfl

/-- Helper for Definition 3.14-extra-1: every nonzero coordinate of the basic solution lies on a
chosen basis column. -/
theorem basic_solution_support_subset_columns
    (B : standard_form_basis A)
    (b : Fin m → 𝕜) :
    Function.support (B.basic_solution b) ⊆ B.columns := by
  -- A coordinate outside `B.columns` vanishes by construction of the extended basic solution.
  refine Function.support_subset_iff'.2 ?_
  intro j hj
  exact B.basic_solution_eq_zero_of_not_mem_columns b hj

/-- Helper for Definition 3.14-extra-1: every support index of the basic solution comes from the
canonical basis-column enumeration `B.cols`. -/
theorem basic_solution_support_mem_range_cols
    (B : standard_form_basis A)
    (b : Fin m → 𝕜)
    (j : Function.support (B.basic_solution b)) :
    j.1 ∈ Set.range B.cols := by
  -- Convert support membership into basis-column membership, then into range membership.
  rw [← B.mem_columns_iff_mem_range j.1]
  exact B.basic_solution_support_subset_columns b j.2

/-- The basis-attached basic solution solves `A x = b`. -/
theorem basic_solution_eq_system
    (B : standard_form_basis A)
    (b : Fin m → 𝕜) :
    A *ᵥ B.basic_solution b = b := by
  -- Route correction: cancel the square basis matrix through the determinant-based nonsingular
  -- inverse API instead of manufacturing a separate `Invertible` instance.
  let AB : Matrix (Fin m) (Fin m) 𝕜 := A.submatrix id B.cols
  have hBasisUnit : IsUnit AB := by
    simpa [AB, standard_form_basis.basis_matrix] using B.basis_matrix_isUnit
  have hdet : IsUnit AB.det :=
    (Matrix.isUnit_iff_isUnit_det (A := AB)).mp hBasisUnit
  have hmul : AB * AB⁻¹ = 1 := Matrix.mul_nonsing_inv (A := AB) hdet
  calc
    A *ᵥ B.basic_solution b = AB *ᵥ x₍B₎ b := by
      simpa [AB, standard_form_basis.basis_matrix] using
        B.basic_solution_mulVec_eq_basis_matrix_mulVec b
    _ = AB *ᵥ (AB⁻¹ *ᵥ b) := by
          rw [B.basic_variables_eq_inv_mulVec]
    _ = (AB * AB⁻¹) *ᵥ b := by
          exact Matrix.mulVec_mulVec b AB AB⁻¹
    _ = (1 : Matrix (Fin m) (Fin m) 𝕜) *ᵥ b := by
          rw [hmul]
    _ = b := by
          exact Matrix.one_mulVec b

/-- For Definition 3.14-extra-1 (6): a basis is primal feasible when `(A_B)⁻¹ b` is
coordinatewise nonnegative. -/
abbrev is_primal_feasible
    [Preorder 𝕜]
    (B : standard_form_basis A)
    (b : Fin m → 𝕜) : Prop :=
  0 ≤ x₍B₎ b

/-- Unfolding primal feasibility gives the nonnegativity of `(A_B)⁻¹ b`. -/
theorem is_primal_feasible_iff
    [Preorder 𝕜]
    (B : standard_form_basis A)
    (b : Fin m → 𝕜) :
    B.is_primal_feasible b ↔ 0 ≤ x₍B₎ b := Iff.rfl

/-- For Definition 3.14-extra-1 (7): the dual vector associated with a basis is
`ȳ = c_B (A_B)⁻¹`. -/
noncomputable abbrev dual_vector
    (B : standard_form_basis A)
    (c : Fin n → 𝕜) : Fin m → 𝕜 :=
  c₍B₎ ᵥ* A₍B₎⁻¹

notation:max "ȳ₍" B "₎" => standard_form_basis.dual_vector B

/-- `ȳ_B` is the row-vector product `c_B (A_B)⁻¹`. -/
theorem dual_vector_eq_vecMul_inv
    (B : standard_form_basis A)
    (c : Fin n → 𝕜) :
    ȳ₍B₎ c = c₍B₎ ᵥ* A₍B₎⁻¹ := rfl

/-- For Definition 3.14-extra-1 (8): a basis is dual feasible when its associated dual vector is
feasible for the dual system `y A ≥ c`. -/
abbrev is_dual_feasible
    [Preorder 𝕜]
    (B : standard_form_basis A)
    (c : Fin n → 𝕜) : Prop :=
  ȳ₍B₎ c ᵥ* A ≥ c

/-- Unfolding dual feasibility gives the pointwise inequality `ȳ A ≥ c`. -/
theorem is_dual_feasible_iff
    [Preorder 𝕜]
    (B : standard_form_basis A)
    (c : Fin n → 𝕜) :
    B.is_dual_feasible c ↔ ȳ₍B₎ c ᵥ* A ≥ c := Iff.rfl

/-- For Definition 3.14-extra-1 (9): the reduced costs associated with a basis are the coefficients
of `c - ȳ A`. -/
noncomputable abbrev reduced_costs
    (B : standard_form_basis A)
    (c : Fin n → 𝕜) : Fin n → 𝕜 :=
  c - ȳ₍B₎ c ᵥ* A

notation:max "c̄₍" B "₎" => standard_form_basis.reduced_costs B

/-- The reduced costs are exactly the coefficients of `c - ȳ A`. -/
theorem reduced_costs_eq
    (B : standard_form_basis A)
    (c : Fin n → 𝕜) :
    c̄₍B₎ c = c - ȳ₍B₎ c ᵥ* A := rfl

/-- For Definition 3.14-extra-1 (10): a basis is optimal when it is both primal feasible and dual
feasible. -/
def is_optimal
    [Preorder 𝕜]
    (B : standard_form_basis A)
    (b : Fin m → 𝕜)
    (c : Fin n → 𝕜) : Prop :=
  B.is_primal_feasible b ∧ B.is_dual_feasible c

/-- Unfolding optimality gives the conjunction of primal and dual feasibility. -/
theorem is_optimal_iff
    [Preorder 𝕜]
    (B : standard_form_basis A)
    (b : Fin m → 𝕜)
    (c : Fin n → 𝕜) :
    B.is_optimal b c ↔ B.is_primal_feasible b ∧ B.is_dual_feasible c := Iff.rfl

theorem is_optimal.primal_feasible
    [Preorder 𝕜]
    {A : Matrix (Fin m) (Fin n) 𝕜}
    {B : standard_form_basis A}
    {b : Fin m → 𝕜}
    {c : Fin n → 𝕜}
    (h : B.is_optimal b c) :
    B.is_primal_feasible b :=
  h.1

theorem is_optimal.dual_feasible
    [Preorder 𝕜]
    {A : Matrix (Fin m) (Fin n) 𝕜}
    {B : standard_form_basis A}
    {b : Fin m → 𝕜}
    {c : Fin n → 𝕜}
    (h : B.is_optimal b c) :
    B.is_dual_feasible c :=
  h.2

end Field

end standard_form_basis

/-- For Definition 3.14-extra-1 (2): a solution of `A x = b` is basic when it is the basic solution
attached to some `m`-column invertible basis of `A`. -/
def is_basic_solution
    [Field 𝕜]
    (A : Matrix (Fin m) (Fin n) 𝕜)
    (b : Fin m → 𝕜)
    (x : Fin n → 𝕜) : Prop :=
  ∃ B : standard_form_basis A, B.basic_solution b = x

/-- Unfolding `is_basic_solution A b x` gives existence of a basis whose associated basic
solution is `x`. -/
theorem is_basic_solution_iff
    [Field 𝕜]
    {A : Matrix (Fin m) (Fin n) 𝕜}
    {b : Fin m → 𝕜}
    {x : Fin n → 𝕜} :
    is_basic_solution A b x ↔ ∃ B : standard_form_basis A, B.basic_solution b = x := Iff.rfl

theorem is_basic_solution.eq_system
    [Field 𝕜]
    {A : Matrix (Fin m) (Fin n) 𝕜}
    {b : Fin m → 𝕜}
    {x : Fin n → 𝕜}
    (h : is_basic_solution A b x) :
    A *ᵥ x = b := by
  rcases h with ⟨B, rfl⟩
  exact B.basic_solution_eq_system b

/-- Definition 3.14-extra-1 (2): a basic solution has linearly independent support columns. This
follows from realizing `x` as the basis-attached basic solution for some invertible `m`-column
basis. -/
theorem is_basic_solution.support_columns_linearIndependent
    [Field 𝕜]
    {A : Matrix (Fin m) (Fin n) 𝕜}
    {b : Fin m → 𝕜}
    {x : Fin n → 𝕜}
    (h : is_basic_solution A b x) :
    LinearIndependent 𝕜 (fun j : Function.support x ↦ fun i : Fin m ↦ A i j) := by
  rcases h with ⟨B, rfl⟩
  let toBasis : Function.support (B.basic_solution b) → Fin m :=
    fun j ↦ B.colsRangeEquiv.symm ⟨j.1, B.basic_solution_support_mem_range_cols b j⟩
  have htoBasis_apply (j : Function.support (B.basic_solution b)) :
      B.cols (toBasis j) = j.1 := by
    -- Each support index already lies in the range of `B.cols`, so `toBasis` recovers its unique
    -- basis index.
    simpa [toBasis, standard_form_basis.colsRangeEquiv] using
      (Equiv.apply_ofInjective_symm B.cols.injective
        ⟨j.1, B.basic_solution_support_mem_range_cols b j⟩)
  have htoBasis_injective : Function.Injective toBasis := by
    -- The recovered basis index is unique because `B.cols` is injective.
    intro j₁ j₂ hEq
    apply Subtype.ext
    have hcols : B.cols (toBasis j₁) = B.cols (toBasis j₂) := congrArg B.cols hEq
    simpa [htoBasis_apply j₁, htoBasis_apply j₂] using hcols
  have hBasisColumns :
      LinearIndependent 𝕜 (fun k : Fin m ↦ fun i : Fin m ↦ A i (B.cols k)) := by
    -- The square basis matrix has linearly independent columns, and those columns are exactly the
    -- columns of `A` selected by `B`.
    let AB : Matrix (Fin m) (Fin m) 𝕜 := A.submatrix id B.cols
    have hBasisUnit : IsUnit AB := by
      simpa [AB, standard_form_basis.basis_matrix] using B.basis_matrix_isUnit
    have hBasisMatrix : LinearIndependent 𝕜 AB.col :=
      (Matrix.linearIndependent_cols_iff_isUnit (A := AB)).mpr hBasisUnit
    simpa [AB, B.basis_matrix_apply, Matrix.col] using hBasisMatrix
  -- Pull the support-indexed columns back to the basis-column family.
  convert (LinearIndependent.comp hBasisColumns toBasis htoBasis_injective) using 1
  funext j
  ext i
  simp [Function.comp, htoBasis_apply]

/-- For Definition 3.14-extra-1 (3): a basic feasible solution is a basic solution whose
coordinates are nonnegative. -/
def is_basic_feasible_solution
    [Field 𝕜] [Preorder 𝕜]
    (A : Matrix (Fin m) (Fin n) 𝕜)
    (b : Fin m → 𝕜)
    (x : Fin n → 𝕜) : Prop :=
  0 ≤ x ∧ is_basic_solution A b x

/-- Unfolding `is_basic_feasible_solution A b x` gives nonnegativity together with basicity. -/
theorem is_basic_feasible_solution_iff
    [Field 𝕜] [Preorder 𝕜]
    {A : Matrix (Fin m) (Fin n) 𝕜}
    {b : Fin m → 𝕜}
    {x : Fin n → 𝕜} :
    is_basic_feasible_solution A b x ↔ 0 ≤ x ∧ is_basic_solution A b x := Iff.rfl

theorem is_basic_feasible_solution.feasible
    [Field 𝕜] [Preorder 𝕜]
    {A : Matrix (Fin m) (Fin n) 𝕜}
    {b : Fin m → 𝕜}
    {x : Fin n → 𝕜}
    (h : is_basic_feasible_solution A b x) :
    x ∈ standard_equality_form A b := by
  exact ⟨h.2.eq_system, h.1⟩

theorem is_basic_feasible_solution.basic
    [Field 𝕜] [Preorder 𝕜]
    {A : Matrix (Fin m) (Fin n) 𝕜}
    {b : Fin m → 𝕜}
    {x : Fin n → 𝕜}
    (h : is_basic_feasible_solution A b x) :
    is_basic_solution A b x :=
  h.2

end Definition314Extra1
