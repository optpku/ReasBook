import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_lemma_4_45
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped BigOperators Matrix
open scoped SplitHullNotation

section Remark_5_5_extra_1

variable {m n : ℕ}

/-- A point of the cut-generating linear program data set `C`, with coordinates
`(α, β, u, u₀, v, v₀)`. -/
structure SplitCutCertificate (m n : ℕ) where
  α : Fin n → ℝ
  β : ℝ
  u : Fin m → ℝ
  u0 : ℝ
  v : Fin m → ℝ
  v0 : ℝ

/-- The cone `C` of cut-generating LP certificates satisfying the system `(5.35)`. -/
def cut_generating_cone
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (π : Fin n → ℤ)
    (π0 : ℤ) : Set (SplitCutCertificate m n) :=
  {ζ |
    ζ.α = ζ.u ᵥ* A + ζ.u0 • (fun i ↦ (π i : ℝ)) ∧
      ζ.α = ζ.v ᵥ* A - ζ.v0 • (fun i ↦ (π i : ℝ)) ∧
      ζ.u ⬝ᵥ b + ζ.u0 * (π0 : ℝ) ≤ ζ.β ∧
      ζ.v ⬝ᵥ b - ζ.v0 * ((π0 : ℝ) + 1) ≤ ζ.β ∧
      0 ≤ ζ.u ∧
      0 ≤ ζ.u0 ∧
      0 ≤ ζ.v ∧
      0 ≤ ζ.v0}

/-- Membership in `cut_generating_cone A b π π0` is exactly the system `(5.35)` on the
certificate coordinates. -/
theorem mem_cut_generating_cone_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (ζ : SplitCutCertificate m n) :
    ζ ∈ cut_generating_cone A b π π0 ↔
      ζ.α = ζ.u ᵥ* A + ζ.u0 • (fun i ↦ (π i : ℝ)) ∧
        ζ.α = ζ.v ᵥ* A - ζ.v0 • (fun i ↦ (π i : ℝ)) ∧
        ζ.u ⬝ᵥ b + ζ.u0 * (π0 : ℝ) ≤ ζ.β ∧
        ζ.v ⬝ᵥ b - ζ.v0 * ((π0 : ℝ) + 1) ≤ ζ.β ∧
        0 ≤ ζ.u ∧
        0 ≤ ζ.u0 ∧
        0 ≤ ζ.v ∧
        0 ≤ ζ.v0 :=
  Iff.rfl

/-- The objective value `β - α x̄` attached to a cut-generating certificate. -/
def split_cut_objective
    (xBar : Fin n → ℝ)
    (ζ : SplitCutCertificate m n) : ℝ :=
  ζ.β - ζ.α ⬝ᵥ xBar

/-- Helper for Remark 5.5-extra-1: the lower split branch is the original system augmented with
the split row `π x ≤ π₀`. -/
lemma lowerSplitBranch_eq_polyhedronLeSet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    split_branch_lower (polyhedron_le_set A b) π π0 =
      polyhedron_le_set (Fin.snoc A (fun j ↦ (π j : ℝ))) (Fin.snoc b (π0 : ℝ)) := by
  ext x
  rw [mem_split_branch_lower_iff, mem_polyhedron_le_set_iff, mem_polyhedron_le_set_iff]
  constructor
  · rintro ⟨hxP, hxSplit⟩
    -- The augmented system keeps the original rows
    -- and appends the split inequality as the last row.
    refine Fin.lastCases ?_ (fun i ↦ ?_)
    · simpa [Matrix.mulVec, split_dot, dotProduct, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last] using hxSplit
    · simpa [Matrix.mulVec, Fin.snoc_castSucc] using hxP i
  · intro hx
    -- Reading the augmented system rowwise recovers both the base polyhedron and the split row.
    refine ⟨?_, ?_⟩
    · intro i
      simpa [Matrix.mulVec, Fin.snoc_castSucc] using hx i.castSucc
    · simpa [Matrix.mulVec, split_dot, dotProduct, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last] using hx (Fin.last m)

/-- Helper for Remark 5.5-extra-1: the upper split branch is the original system augmented with
the row `-π x ≤ -(π₀ + 1)`. -/
lemma upperSplitBranch_eq_polyhedronLeSet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    split_branch_upper (polyhedron_le_set A b) π π0 =
      polyhedron_le_set
        (Fin.snoc A (fun j ↦ -((π j : ℝ))))
        (Fin.snoc b (-((π0 : ℝ) + 1))) := by
  ext x
  rw [mem_split_branch_upper_iff, mem_polyhedron_le_set_iff, mem_polyhedron_le_set_iff]
  constructor
  · rintro ⟨hxP, hxSplit⟩
    -- The upper branch is encoded by moving `π₀ + 1 ≤ π x` to the equivalent row inequality.
    refine Fin.lastCases ?_ (fun i ↦ ?_)
    · have hlast : -(split_dot π x) ≤ -((π0 : ℝ) + 1) := by
        linarith
      simpa [Matrix.mulVec, split_dot, dotProduct, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last] using hlast
    · simpa [Matrix.mulVec, Fin.snoc_castSucc] using hxP i
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i
      simpa [Matrix.mulVec, Fin.snoc_castSucc] using hx i.castSucc
    · have hlast :
        -((split_dot π x)) ≤ -((π0 : ℝ) + 1) := by
          simpa [Matrix.mulVec, split_dot, dotProduct, Fin.sum_univ_castSucc,
            Fin.snoc_castSucc, Fin.snoc_last] using hx (Fin.last m)
      linarith

/-- Helper for Remark 5.5-extra-1: multiplying an augmented row system by `x` separates into the
original matrix product and the last-row contribution. -/
lemma snocMatrix_mulVec
    (A : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin n → ℝ)
    (x : Fin n → ℝ) :
    (Fin.snoc A r) *ᵥ x = Fin.snoc (A *ᵥ x) (r ⬝ᵥ x) := by
  ext i
  -- Evaluate the augmented matrix row by row.
  cases i using Fin.lastCases with
  | last =>
      simp [Matrix.mulVec, dotProduct]
  | cast i =>
      simp [Matrix.mulVec]

/-- Helper for Remark 5.5-extra-1: multiplying a row multiplier against an augmented matrix
separates into the old rows and the split row. -/
lemma vecMul_snocMatrix
    (u : Fin (m + 1) → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin n → ℝ) :
    u ᵥ* (Fin.snoc A r) =
      (fun i ↦ u i.castSucc) ᵥ* A + u (Fin.last m) • r := by
  ext j
  -- Split the multiplier sum into the first `m` coordinates and the last coordinate.
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Pi.add_apply, Pi.smul_apply, add_comm, mul_comm]

/-- Helper for Remark 5.5-extra-1: the right-hand side of an augmented system also separates into
the original dot product and the last scalar term. -/
lemma dotProduct_snoc
    (u : Fin (m + 1) → ℝ)
    (b : Fin m → ℝ)
    (t : ℝ) :
    u ⬝ᵥ Fin.snoc b t = (fun i ↦ u i.castSucc) ⬝ᵥ b + u (Fin.last m) * t := by
  -- Split the dot product at the last coordinate.
  simp [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, add_comm, mul_comm]

/-- Helper for Remark 5.5-extra-1: matrix polyhedra `polyhedron_le_set A b` are closed. -/
lemma polyhedronLeSet_isClosed
    {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ)
    (b : Fin m → ℝ) :
    IsClosed (polyhedron_le_set A b) := by
  rw [show polyhedron_le_set A b = ⋂ i : Fin m, {x : Fin k → ℝ | (A *ᵥ x) i ≤ b i} by
    ext x
    constructor
    · intro hx
      simpa [polyhedron_le_set] using hx
    · intro hx
      simpa [polyhedron_le_set] using hx]
  refine isClosed_iInter ?_
  intro i
  have hcont : Continuous fun x : Fin k → ℝ ↦ (A *ᵥ x) i := by
    exact (continuous_apply i).comp A.mulVecLin.continuous_of_finiteDimensional
  exact isClosed_le hcont continuous_const

/-- Helper for Remark 5.5-extra-1: the split hull of a matrix polyhedron is again a polyhedron. -/
lemma splitHull_isPolyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    is_polyhedron ((polyhedron_le_set A b)^(π, π0)) := by
  simpa [split_hull, split_branch_lower, split_branch_upper, split_dot] using
    convexHull_split_polyhedra_is_polyhedron
      A b (fun j : Fin n ↦ (π j : ℝ)) (π0 : ℝ) ((π0 : ℝ) + 1)

/-- Helper for Remark 5.5-extra-1: assuming both split branches are nonempty, an inequality
`α x ≤ β` is valid for `P^(π, π₀)` if and only if it is represented by a point of the
cut-generating cone `C` from `(5.35)`. -/
theorem valid_inequality_on_split_polyhedron_iff_exists_certificate
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (h_lower : Set.Nonempty (split_branch_lower (polyhedron_le_set A b) π π0))
    (h_upper : Set.Nonempty (split_branch_upper (polyhedron_le_set A b) π π0))
    (α : Fin n → ℝ)
    (β : ℝ) :
    is_valid_inequality ((polyhedron_le_set A b)^(π, π0)) α β ↔
      ∃ ζ ∈ cut_generating_cone A b π π0, ζ.α = α ∧ ζ.β = β := by
  let lowerA : Matrix (Fin (m + 1)) (Fin n) ℝ := Fin.snoc A (fun j ↦ (π j : ℝ))
  let lowerb : Fin (m + 1) → ℝ := Fin.snoc b (π0 : ℝ)
  let upperA : Matrix (Fin (m + 1)) (Fin n) ℝ := Fin.snoc A (fun j ↦ -((π j : ℝ)))
  let upperb : Fin (m + 1) → ℝ := Fin.snoc b (-((π0 : ℝ) + 1))
  constructor
  · intro hvalid
    -- Route correction: convert split-hull validity to branchwise validity, then apply Theorem 3.22
    -- to the two augmented systems.
    have hvalidUnion :
        is_valid_inequality
          (split_branch_lower (polyhedron_le_set A b) π π0 ∪
            split_branch_upper (polyhedron_le_set A b) π π0)
          α β := by
      simpa [split_hull] using
        (is_valid_inequality_convexHull_iff
          (S :=
            split_branch_lower (polyhedron_le_set A b) π π0 ∪
              split_branch_upper (polyhedron_le_set A b) π π0)
          (α := α) (β := β)).1 hvalid
    have hvalidLower :
        is_valid_inequality (split_branch_lower (polyhedron_le_set A b) π π0) α β := by
      rw [is_valid_inequality_iff] at hvalidUnion ⊢
      intro x hx
      exact hvalidUnion (Or.inl hx)
    have hvalidUpper :
        is_valid_inequality (split_branch_upper (polyhedron_le_set A b) π π0) α β := by
      rw [is_valid_inequality_iff] at hvalidUnion ⊢
      intro x hx
      exact hvalidUnion (Or.inr hx)
    have hLowerNonempty : Set.Nonempty (polyhedron_le_set lowerA lowerb) := by
      simpa [lowerA, lowerb, lowerSplitBranch_eq_polyhedronLeSet] using h_lower
    have hUpperNonempty : Set.Nonempty (polyhedron_le_set upperA upperb) := by
      simpa [upperA, upperb, upperSplitBranch_eq_polyhedronLeSet] using h_upper
    have hvalidLowerMatrix : is_valid_inequality (polyhedron_le_set lowerA lowerb) α β := by
      simpa [lowerA, lowerb, lowerSplitBranch_eq_polyhedronLeSet] using hvalidLower
    have hvalidUpperMatrix : is_valid_inequality (polyhedron_le_set upperA upperb) α β := by
      simpa [upperA, upperb, upperSplitBranch_eq_polyhedronLeSet] using hvalidUpper
    rcases
      (valid_inequality_iff_exists_nonneg_row_multiplier lowerA lowerb α β hLowerNonempty).1
        hvalidLowerMatrix with
      ⟨uLower, huLower_nonneg, huLower_row, huLower_rhs⟩
    rcases
      (valid_inequality_iff_exists_nonneg_row_multiplier upperA upperb α β hUpperNonempty).1
        hvalidUpperMatrix with
      ⟨uUpper, huUpper_nonneg, huUpper_row, huUpper_rhs⟩
    let ζ : SplitCutCertificate m n :=
      { α := α
        β := β
        u := fun i ↦ uLower i.castSucc
        u0 := uLower (Fin.last m)
        v := fun i ↦ uUpper i.castSucc
        v0 := uUpper (Fin.last m) }
    refine ⟨ζ, ?_, rfl, rfl⟩
    rw [mem_cut_generating_cone_iff]
    dsimp [ζ, lowerA, lowerb, upperA, upperb]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Decompose the lower multiplier identity into `(u, u₀)`.
      calc
        α = uLower ᵥ* Fin.snoc A (fun j ↦ (π j : ℝ)) := huLower_row.symm
        _ = (fun i ↦ uLower i.castSucc) ᵥ* A + uLower (Fin.last m) • (fun j ↦ (π j : ℝ)) := by
          rw [vecMul_snocMatrix]
    · -- Decompose the upper multiplier identity into `(v, v₀)`.
      calc
        α = uUpper ᵥ* Fin.snoc A (fun j ↦ -((π j : ℝ))) := huUpper_row.symm
        _ = (fun i ↦ uUpper i.castSucc) ᵥ* A +
              uUpper (Fin.last m) • (fun j ↦ -((π j : ℝ))) := by
              rw [vecMul_snocMatrix]
        _ = (fun i ↦ uUpper i.castSucc) ᵥ* A -
              uUpper (Fin.last m) • (fun j ↦ (π j : ℝ)) := by
              ext j
              simp [sub_eq_add_neg]
    · -- The lower right-hand side bound becomes `u b + u₀ π₀ ≤ β`.
      calc
        (fun i ↦ uLower i.castSucc) ⬝ᵥ b + uLower (Fin.last m) * (π0 : ℝ)
            = uLower ⬝ᵥ Fin.snoc b (π0 : ℝ) := by
                rw [dotProduct_snoc]
        _ ≤ β := huLower_rhs
    · -- The upper right-hand side bound becomes `v b - v₀ (π₀ + 1) ≤ β`.
      calc
        (fun i ↦ uUpper i.castSucc) ⬝ᵥ b - uUpper (Fin.last m) * ((π0 : ℝ) + 1)
            = uUpper ⬝ᵥ Fin.snoc b (-((π0 : ℝ) + 1)) := by
                rw [dotProduct_snoc]
                ring
        _ ≤ β := huUpper_rhs
    · intro i
      exact huLower_nonneg i.castSucc
    · exact huLower_nonneg (Fin.last m)
    · intro i
      exact huUpper_nonneg i.castSucc
    · exact huUpper_nonneg (Fin.last m)
  · rintro ⟨ζ, hζ, hα, hβ⟩
    rw [mem_cut_generating_cone_iff] at hζ
    rcases hζ with
      ⟨hLower_row, hUpper_row, hLower_rhs, hUpper_rhs, hu_nonneg, hu0_nonneg, hv_nonneg,
        hv0_nonneg⟩
    have hLowerNonempty : Set.Nonempty (polyhedron_le_set lowerA lowerb) := by
      simpa [lowerA, lowerb, lowerSplitBranch_eq_polyhedronLeSet] using h_lower
    have hUpperNonempty : Set.Nonempty (polyhedron_le_set upperA upperb) := by
      simpa [upperA, upperb, upperSplitBranch_eq_polyhedronLeSet] using h_upper
    have hvalidLowerMatrix : is_valid_inequality (polyhedron_le_set lowerA lowerb) α β := by
      -- Feed the lower certificate directly into Theorem 3.22 on the augmented system.
      refine
        (valid_inequality_iff_exists_nonneg_row_multiplier lowerA lowerb α β hLowerNonempty).2 ?_
      refine ⟨Fin.snoc ζ.u ζ.u0, ?_, ?_, ?_⟩
      · refine Fin.lastCases ?_ (fun i ↦ ?_)
        · simpa using hu0_nonneg
        · simpa using hu_nonneg i
      · calc
          (Fin.snoc ζ.u ζ.u0) ᵥ* lowerA = ζ.u ᵥ* A + ζ.u0 • (fun i ↦ (π i : ℝ)) := by
            rw [vecMul_snocMatrix]
            ext i
            simp
          _ = ζ.α := by simpa [hα] using hLower_row.symm
          _ = α := hα
      · calc
          (Fin.snoc ζ.u ζ.u0) ⬝ᵥ lowerb = ζ.u ⬝ᵥ b + ζ.u0 * (π0 : ℝ) := by
            rw [dotProduct_snoc]
            simp
          _ ≤ ζ.β := hLower_rhs
          _ = β := hβ
    have hvalidUpperMatrix : is_valid_inequality (polyhedron_le_set upperA upperb) α β := by
      -- The upper certificate is handled by the signed augmented row system.
      refine
        (valid_inequality_iff_exists_nonneg_row_multiplier upperA upperb α β hUpperNonempty).2 ?_
      refine ⟨Fin.snoc ζ.v ζ.v0, ?_, ?_, ?_⟩
      · refine Fin.lastCases ?_ (fun i ↦ ?_)
        · simpa using hv0_nonneg
        · simpa using hv_nonneg i
      · calc
          (Fin.snoc ζ.v ζ.v0) ᵥ* upperA = ζ.v ᵥ* A + ζ.v0 • (fun i ↦ -((π i : ℝ))) := by
            rw [vecMul_snocMatrix]
            ext i
            simp
          _ = ζ.α := by
            rw [hUpper_row]
            ext i
            simp [sub_eq_add_neg]
          _ = α := hα
      · calc
          (Fin.snoc ζ.v ζ.v0) ⬝ᵥ upperb = ζ.v ⬝ᵥ b - ζ.v0 * ((π0 : ℝ) + 1) := by
            rw [dotProduct_snoc]
            simp
            ring
          _ ≤ ζ.β := hUpper_rhs
          _ = β := hβ
    have hvalidLower :
        is_valid_inequality (split_branch_lower (polyhedron_le_set A b) π π0) α β := by
      simpa [lowerA, lowerb, lowerSplitBranch_eq_polyhedronLeSet] using hvalidLowerMatrix
    have hvalidUpper :
        is_valid_inequality (split_branch_upper (polyhedron_le_set A b) π π0) α β := by
      simpa [upperA, upperb, upperSplitBranch_eq_polyhedronLeSet] using hvalidUpperMatrix
    have hvalidUnion :
        is_valid_inequality
          (split_branch_lower (polyhedron_le_set A b) π π0 ∪
            split_branch_upper (polyhedron_le_set A b) π π0)
          α β := by
      rw [is_valid_inequality_iff]
      intro x hx
      rcases hx with hx | hx
      · exact hvalidLower hx
      · exact hvalidUpper hx
    -- Validity on the union is equivalent to validity on the split hull
    -- by convexity of the halfspace.
    simpa [split_hull] using
      (is_valid_inequality_convexHull_iff
        (S :=
          split_branch_lower (polyhedron_le_set A b) π π0 ∪
            split_branch_upper (polyhedron_le_set A b) π π0)
        (α := α) (β := β)).2 hvalidUnion

/-- Helper for Remark 5.5-extra-1: if a certificate in `C` defines an inequality that is not valid
for the original polyhedron `P`, then the split multipliers satisfy `u₀ > 0` and `v₀ > 0`. -/
theorem positive_split_scalars_of_not_valid_on_base_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (π : Fin n → ℤ)
    (π0 : ℤ)
    {ζ : SplitCutCertificate m n}
    (hζ : ζ ∈ cut_generating_cone A b π π0)
    (hnot_valid : ¬ is_valid_inequality (polyhedron_le_set A b) ζ.α ζ.β) :
    0 < ζ.u0 ∧ 0 < ζ.v0 := by
  rw [mem_cut_generating_cone_iff] at hζ
  rcases hζ with
    ⟨hLower_row, hUpper_row, hLower_rhs, hUpper_rhs, hu_nonneg, hu0_nonneg, hv_nonneg,
      hv0_nonneg⟩
  have hP_nonempty : Set.Nonempty (polyhedron_le_set A b) := by
    by_contra hEmpty
    apply hnot_valid
    rw [is_valid_inequality_iff]
    intro x hx
    exact (hEmpty ⟨x, hx⟩).elim
  have hu0_ne : ζ.u0 ≠ 0 := by
    intro hu0_zero
    have hvalid : is_valid_inequality (polyhedron_le_set A b) ζ.α ζ.β := by
      -- If `u₀ = 0`, the lower multiplier already certifies validity on the base polyhedron.
      refine
        (valid_inequality_iff_exists_nonneg_row_multiplier A b ζ.α ζ.β hP_nonempty).2 ?_
      refine ⟨ζ.u, hu_nonneg, ?_, ?_⟩
      · simpa [hu0_zero] using hLower_row.symm
      · simpa [hu0_zero] using hLower_rhs
    exact hnot_valid hvalid
  have hv0_ne : ζ.v0 ≠ 0 := by
    intro hv0_zero
    have hvalid : is_valid_inequality (polyhedron_le_set A b) ζ.α ζ.β := by
      -- If `v₀ = 0`, the upper multiplier also collapses to a base-polyhedron certificate.
      refine
        (valid_inequality_iff_exists_nonneg_row_multiplier A b ζ.α ζ.β hP_nonempty).2 ?_
      refine ⟨ζ.v, hv_nonneg, ?_, ?_⟩
      · simpa [hv0_zero, sub_eq_add_neg] using hUpper_row.symm
      · simpa [hv0_zero, sub_eq_add_neg] using hUpper_rhs
    exact hnot_valid hvalid
  -- Combine nonnegativity from the cone with nonvanishing to get strict positivity.
  exact
    ⟨lt_of_le_of_ne hu0_nonneg (Ne.symm hu0_ne), lt_of_le_of_ne hv0_nonneg (Ne.symm hv0_ne)⟩

/-- Remark 5.5-extra-1. Assuming both split branches are nonempty, a point `xBar` lies in
`(polyhedron_le_set A b)^(π, π₀)` if and only if no certificate in the cut-generating cone `C`
from `(5.35)` gives a negative value for the objective `β - α xBar` from `(5.36)`. -/
theorem mem_split_hull_iff_no_negative_cut_generating_certificate
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (h_lower : Set.Nonempty (split_branch_lower (polyhedron_le_set A b) π π0))
    (h_upper : Set.Nonempty (split_branch_upper (polyhedron_le_set A b) π π0))
    (xBar : Fin n → ℝ) :
    xBar ∈ ((polyhedron_le_set A b)^(π, π0)) ↔
      ¬ ∃ ζ ∈ cut_generating_cone A b π π0, split_cut_objective xBar ζ < 0 := by
  constructor
  · intro hxBar hneg
    rcases hneg with ⟨ζ, hζ, hobj⟩
    -- A negative objective would contradict validity of the certificate inequality at `xBar`.
    have hvalid :
        is_valid_inequality ((polyhedron_le_set A b)^(π, π0)) ζ.α ζ.β := by
      exact
        (valid_inequality_on_split_polyhedron_iff_exists_certificate
          A b π π0 h_lower h_upper ζ.α ζ.β).2 ⟨ζ, hζ, rfl, rfl⟩
    have hbound : ζ.α ⬝ᵥ xBar ≤ ζ.β := hvalid hxBar
    dsimp [split_cut_objective] at hobj
    linarith
  · intro hno
    by_contra hxBar_not_mem
    have hPolyhedron : is_polyhedron (polyhedron_le_set A b) := ⟨m, A, b, rfl⟩
    have hSplit_polyhedron : is_polyhedron ((polyhedron_le_set A b)^(π, π0)) :=
      splitHull_isPolyhedron A b π π0
    rcases hSplit_polyhedron with ⟨k, B, d, hBd⟩
    have hSplit_closed : IsClosed ((polyhedron_le_set A b)^(π, π0)) := by
      -- The polyhedral presentation gives the closedness hypothesis needed for separation.
      rw [hBd]
      exact polyhedronLeSet_isClosed B d
    have hSplit_convex : Convex ℝ ((polyhedron_le_set A b)^(π, π0)) := by
      -- The split hull is a convex hull by definition.
      simpa [split_hull] using
        convex_convexHull ℝ
          (split_branch_lower (polyhedron_le_set A b) π π0 ∪
            split_branch_upper (polyhedron_le_set A b) π π0)
    obtain ⟨f, β, hsep, hxsep⟩ :=
      geometric_hahn_banach_closed_point
        (s := ((polyhedron_le_set A b)^(π, π0)))
        (x := xBar) hSplit_convex hSplit_closed hxBar_not_mem
    obtain ⟨α, hrep⟩ := strongDual_eq_dotProduct_fin f
    have hvalid :
        is_valid_inequality ((polyhedron_le_set A b)^(π, π0)) α β := by
      -- Rewrite the separating functional as a dot product with `α`.
      rw [is_valid_inequality_iff]
      intro x hx
      exact le_of_lt (by simpa [hrep x] using hsep x hx)
    have hlt : β < α ⬝ᵥ xBar := by
      simpa [hrep xBar] using hxsep
    rcases
      (valid_inequality_on_split_polyhedron_iff_exists_certificate
        A b π π0 h_lower h_upper α β).1 hvalid with
      ⟨ζ, hζ, hζα, hζβ⟩
    apply hno
    refine ⟨ζ, hζ, ?_⟩
    rw [split_cut_objective, hζα, hζβ]
    linarith

/-- Helper for Remark 5.5-extra-1: the normalization `u₀ + v₀ = 1` used when the underlying
inequality is not valid for `P`. -/
def split_scalar_normalization
    (ζ : SplitCutCertificate m n) : Prop :=
  ζ.u0 + ζ.v0 = 1

/-- Characterization of `split_scalar_normalization` by the scalar identity `u₀ + v₀ = 1`. -/
theorem split_scalar_normalization_iff
    (ζ : SplitCutCertificate m n) :
    split_scalar_normalization ζ ↔ ζ.u0 + ζ.v0 = 1 :=
  Iff.rfl

/-- Helper for Remark 5.5-extra-1: Balas' standard normalization condition
`∑ i, u i + u₀ + ∑ i, v i + v₀ = 1`. -/
def standard_split_normalization
    (ζ : SplitCutCertificate m n) : Prop :=
  (∑ i, ζ.u i) + ζ.u0 + (∑ i, ζ.v i) + ζ.v0 = 1

/-- Characterization of `standard_split_normalization` by Balas' standard normalization
identity. -/
theorem standard_split_normalization_iff
    (ζ : SplitCutCertificate m n) :
    standard_split_normalization ζ ↔
      (∑ i, ζ.u i) + ζ.u0 + (∑ i, ζ.v i) + ζ.v0 = 1 :=
  Iff.rfl

end Remark_5_5_extra_1
