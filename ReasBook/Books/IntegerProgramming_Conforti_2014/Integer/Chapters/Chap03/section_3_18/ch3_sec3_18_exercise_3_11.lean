import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_definition_3_7_extra_1

open scoped BigOperators Matrix Pointwise

-- This exercise is stated on the Chapter 3 owner surface `polyhedron_le_set` and
-- `recessionCone`; the kept subsystem is the canonical row-restriction view
-- `A.submatrix (Subtype.val : {i // i ∈ I} → Fin m) id` together with
-- `b ∘ (Subtype.val : {i // i ∈ I} → Fin m)`.

/-- Membership in the row-restricted subsystem
`A.submatrix (Subtype.val : {i // i ∈ I} → Fin m) id *ᵥ x ≤
  b ∘ (Subtype.val : {i // i ∈ I} → Fin m)` is
exactly the family of inequalities indexed by `I`. -/
theorem mem_restricted_rows_mulVec_le_iff
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin m))
    (x : Fin n → ℝ) :
    A.submatrix (Subtype.val : {i // i ∈ I} → Fin m) id *ᵥ x ≤
        b ∘ (Subtype.val : {i // i ∈ I} → Fin m) ↔
      ∀ i : Fin m, i ∈ I → (A *ᵥ x) i ≤ b i := by
  constructor
  · intro hx i hi
    simpa using hx ⟨i, hi⟩
  · intro hx i
    simpa using hx i.1 i.2

/-- Any vector with nonpositive homogeneous image under `A` is a recession direction of the
polyhedron `polyhedron_le_set A b`. -/
lemma mem_recessionCone_polyhedron_le_set_of_mulVec_nonpos
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {r : Fin n → ℝ}
    (hr : A *ᵥ r ≤ 0) :
    r ∈ recessionCone (polyhedron_le_set A b) := by
  rw [mem_recessionCone_iff]
  intro x hx a ha
  change A *ᵥ (x + a • r) ≤ b
  intro i
  have hmul : a * (A *ᵥ r) i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (hr i)
  have hsum : (A *ᵥ x) i + a * (A *ᵥ r) i ≤ b i := by
    linarith [hx i, hmul]
  simpa [polyhedron_le_set, Matrix.mulVec_add, Matrix.mulVec_smul] using hsum

/-
The recession-fixed row set is the source-facing derived view used in this exercise. It is built
from the Chapter 3 owner `recessionCone`, and unlike `implicit_equality_indices` it records the
rows preserved under recession translations rather than the rows forced to equality on all feasible
points.
-/
private def recessionFixedRows
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin m) :=
  {i : Fin m |
    ∀ r : Fin n → ℝ, r ∈ recessionCone (polyhedron_le_set A b) → (A *ᵥ r) i = 0}

private theorem mem_recessionFixedRows_iff
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {i : Fin m} :
    i ∈ recessionFixedRows A b ↔
      ∀ r : Fin n → ℝ, r ∈ recessionCone (polyhedron_le_set A b) → (A *ᵥ r) i = 0 := by
  rfl

/-- Bridge to Section 3.7: every implicit equality row of a nonempty polyhedron vanishes on each
recession direction. This is the exact compatibility used here; the recession-fixed row subsystem
is in general larger than the implicit-equality subsystem. -/
lemma row_eq_zero_of_mem_implicit_equality_indices
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b))
    {i : Fin m}
    (hi : i ∈ implicit_equality_indices A b)
    {r : Fin n → ℝ}
    (hr : r ∈ recessionCone (polyhedron_le_set A b)) :
    (A *ᵥ r) i = 0 := by
  rcases h_nonempty with ⟨x, hx⟩
  have hi' : is_implicit_equality A b i := (mem_implicit_equality_indices_iff A b i).1 hi
  rw [mem_recessionCone_iff] at hr
  have hx_eq : (A *ᵥ x) i = b i := hi' hx
  have hxr : A *ᵥ (x + r) ≤ b := by
    simpa using hr hx 1 zero_le_one
  have hxr_eq : (A *ᵥ (x + r)) i = b i := hi' hxr
  have hsum : (A *ᵥ (x + r)) i = (A *ᵥ x) i + (A *ᵥ r) i := by
    rw [Matrix.mulVec_add]
    simp
  linarith

/-- Set-level form of the Section 3.7 bridge: for a nonempty polyhedron, every implicit equality
index belongs to the recession-fixed row subsystem. -/
theorem implicit_equality_indices_subset_rows_vanishing_on_recessionCone
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b)) :
    implicit_equality_indices A b ⊆
      {i : Fin m |
        ∀ r : Fin n → ℝ, r ∈ recessionCone (polyhedron_le_set A b) → (A *ᵥ r) i = 0} := by
  intro i hi r hr
  exact row_eq_zero_of_mem_implicit_equality_indices A b h_nonempty hi hr

private lemma row_eq_zero_of_mem_recessionFixedRows
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {i : Fin m}
    (hi : i ∈ recessionFixedRows A b)
    {r : Fin n → ℝ}
    (hr : r ∈ recessionCone (polyhedron_le_set A b)) :
    (A *ᵥ r) i = 0 := by
  exact (mem_recessionFixedRows_iff A b).1 hi r hr

private lemma exists_strict_drop_direction_of_not_mem_recessionFixedRows
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b))
    {i : Fin m}
    (hi : i ∉ recessionFixedRows A b) :
    ∃ r : Fin n → ℝ,
      r ∈ recessionCone (polyhedron_le_set A b) ∧
      (A *ᵥ r) i < 0 := by
  have hi' :
      ¬ ∀ r : Fin n → ℝ, r ∈ recessionCone (polyhedron_le_set A b) → (A *ᵥ r) i = 0 := by
    simpa [mem_recessionFixedRows_iff] using hi
  push Not at hi'
  rcases hi' with ⟨r, hr, hr_ne⟩
  have hr_nonpos : A *ᵥ r ≤ 0 := by
    rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b h_nonempty] at hr
    exact hr
  exact ⟨r, hr, lt_of_le_of_ne (hr_nonpos i) hr_ne⟩

private lemma exists_common_drop_direction
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b)) :
    ∃ d : Fin n → ℝ,
      (∀ j : Fin m, (A *ᵥ d) j ≤ 0) ∧
      (∀ j : Fin m, j ∈ recessionFixedRows A b → (A *ᵥ d) j = 0) ∧
      (∀ j : Fin m, j ∉ recessionFixedRows A b → (A *ᵥ d) j < 0) := by
  classical
  have hdrop :
      ∀ i : Fin m, i ∉ recessionFixedRows A b →
        ∃ r : Fin n → ℝ,
          r ∈ recessionCone (polyhedron_le_set A b) ∧
          (A *ᵥ r) i < 0 := by
    intro i hi
    exact exists_strict_drop_direction_of_not_mem_recessionFixedRows A b h_nonempty hi
  choose w hw_rec hw_strict using hdrop
  have hw_nonpos :
      ∀ i : Fin m, ∀ hi : i ∉ recessionFixedRows A b, A *ᵥ w i hi ≤ 0 := by
    intro i hi
    have hw : w i hi ∈ recessionCone (polyhedron_le_set A b) := hw_rec i hi
    rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b h_nonempty] at hw
    exact hw
  let v : Fin m → Fin n → ℝ := fun i ↦
    if hi : i ∈ recessionFixedRows A b then 0 else w i hi
  let d : Fin n → ℝ := ∑ i : Fin m, v i
  refine ⟨d, ?_, ?_, ?_⟩
  · intro j
    rw [show (A *ᵥ d) j = ∑ i : Fin m, (A *ᵥ v i) j by
      simp [d, Matrix.mulVec_sum, Finset.sum_apply]]
    exact Finset.sum_nonpos fun i _ ↦ by
      by_cases hi : i ∈ recessionFixedRows A b
      · simp [v, hi]
      · simpa [v, hi] using hw_nonpos i hi j
  · intro j hj
    rw [show (A *ᵥ d) j = ∑ i : Fin m, (A *ᵥ v i) j by
      simp [d, Matrix.mulVec_sum, Finset.sum_apply]]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ recessionFixedRows A b
    · simp [v, hi]
    · have hzero :
          (A *ᵥ w i hi) j = 0 :=
        row_eq_zero_of_mem_recessionFixedRows A b hj (hw_rec i hi)
      simp [v, hi, hzero]
  · intro j hj
    let f : Fin m → ℝ := fun i ↦ (A *ᵥ v i) j
    have hsplit :
        Finset.sum (Finset.univ.erase j) f + f j = Finset.sum Finset.univ f := by
      exact Finset.univ.sum_erase_add f (Finset.mem_univ j)
    have hsum_nonpos : Finset.sum (Finset.univ.erase j) f ≤ 0 := by
      exact Finset.sum_nonpos fun i hi ↦ by
        by_cases hi' : i ∈ recessionFixedRows A b
        · simp [v, hi']
        · simpa [f, v, hi'] using hw_nonpos i hi' j
    have hstrict : f j < 0 := by
      simp [f, v, hj, hw_strict j hj]
    have htotal : ∑ i : Fin m, f i = (A *ᵥ d) j := by
      simp [f, d, Matrix.mulVec_sum, Finset.sum_apply]
    rw [← htotal, ← hsplit]
    linarith

/-- Once a common decreasing direction is available, a sufficiently large nonnegative shift along
it restores all omitted inequalities simultaneously. -/
lemma exists_feasible_shift_of_common_drop_direction
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I' : Set (Fin m))
    {y d : Fin n → ℝ}
    (hy : ∀ i : Fin m, i ∈ I' → (A *ᵥ y) i ≤ b i)
    (hd_zero : ∀ j : Fin m, j ∈ I' → (A *ᵥ d) j = 0)
    (hd_strict : ∀ j : Fin m, j ∉ I' → (A *ᵥ d) j < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ i : Fin m, (A *ᵥ (y + t • d)) i ≤ b i := by
  classical
  let threshold : Fin m → ℝ := fun i ↦
    if hi : i ∈ I' then
      0
    else
      max 0 (((A *ᵥ y) i - b i) / (-(A *ᵥ d) i))
  let t : ℝ := ∑ i : Fin m, threshold i
  refine ⟨t, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ ↦ by
      by_cases hi : i ∈ I'
      · simp [threshold, hi]
      · simp [threshold, hi]
  · intro i
    have ht_ge : threshold i ≤ t := by
      exact Finset.univ.single_le_sum
        (fun j _ ↦ by
          by_cases hj : j ∈ I'
          · simp [threshold, hj]
          · simp [threshold, hj])
        (by simp)
    by_cases hi : i ∈ I'
    · have hrow_zero : (A *ᵥ d) i = 0 := hd_zero i hi
      calc
        (A *ᵥ (y + t • d)) i
            = (A *ᵥ y) i + t * (A *ᵥ d) i := by
                rw [Matrix.mulVec_add, Matrix.mulVec_smul]
                simp
        _ = (A *ᵥ y) i := by simp [hrow_zero]
        _ ≤ b i := hy i hi
    · have hden_pos : 0 < -(A *ᵥ d) i := by
        linarith [hd_strict i hi]
      have hratio_le_threshold :
          ((A *ᵥ y) i - b i) / (-(A *ᵥ d) i) ≤ threshold i := by
        simp [threshold, hi]
      have hratio_le_t :
          ((A *ᵥ y) i - b i) / (-(A *ᵥ d) i) ≤ t :=
        le_trans hratio_le_threshold ht_ge
      have hscaled :
          (A *ᵥ y) i - b i ≤ t * (-(A *ᵥ d) i) := by
        exact (div_le_iff₀ hden_pos).mp hratio_le_t
      calc
        (A *ᵥ (y + t • d)) i
            = (A *ᵥ y) i + t * (A *ᵥ d) i := by
                rw [Matrix.mulVec_add, Matrix.mulVec_smul]
                simp
        _ ≤ b i := by
          nlinarith

private theorem polyhedron_add_recession_neg_eq_subsystem_aux
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b)) :
    polyhedron_le_set A b + -recessionCone (polyhedron_le_set A b) =
      {y : Fin n → ℝ |
        A.submatrix (Subtype.val : {i // i ∈ recessionFixedRows A b} → Fin m) id *ᵥ y ≤
          b ∘ (Subtype.val : {i // i ∈ recessionFixedRows A b} → Fin m)} := by
  ext y
  constructor
  · intro hy
    rcases Set.mem_add.mp hy with ⟨x, hx, r, hr, rfl⟩
    exact
      (mem_restricted_rows_mulVec_le_iff A b (recessionFixedRows A b)
        (x + r)).2 <| by
      intro i hi
      have hneg_rec : -r ∈ recessionCone (polyhedron_le_set A b) := by
        rwa [← mem_neg_recessionCone_iff]
      have hrow_zero_neg :
          (A *ᵥ (-r)) i = 0 :=
        row_eq_zero_of_mem_recessionFixedRows A b hi hneg_rec
      have hrow_zero : (A *ᵥ r) i = 0 := by
        simpa [Matrix.mulVec_neg] using congrArg Neg.neg hrow_zero_neg
      calc
        (A *ᵥ (x + r)) i
            = (A *ᵥ x) i + (A *ᵥ r) i := by
                rw [Matrix.mulVec_add]
                simp
        _ = (A *ᵥ x) i := by simp [hrow_zero]
        _ ≤ b i := hx i
  · intro hy
    have hy' :=
      (mem_restricted_rows_mulVec_le_iff A b (recessionFixedRows A b) y).1 hy
    rcases exists_common_drop_direction A b h_nonempty with
      ⟨d, hd_nonpos, hd_zero, hd_strict⟩
    rcases
        exists_feasible_shift_of_common_drop_direction A b (recessionFixedRows A b)
          hy' hd_zero hd_strict with
      ⟨t, ht_nonneg, ht_feasible⟩
    have htd_nonpos : A *ᵥ (t • d) ≤ 0 := by
      intro i
      have hmul : t * (A *ᵥ d) i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht_nonneg (hd_nonpos i)
      simpa [Matrix.mulVec_smul] using hmul
    have htd_rec : t • d ∈ recessionCone (polyhedron_le_set A b) :=
      mem_recessionCone_polyhedron_le_set_of_mulVec_nonpos A b htd_nonpos
    refine Set.mem_add.mpr ?_
    refine ⟨y + t • d, ht_feasible, -(t • d), ?_, ?_⟩
    · simpa using htd_rec
    · ext i
      simp

/-- Exercise 3.11. Let
`I' := {i | ∀ r ∈ recessionCone (polyhedron_le_set A b), (A *ᵥ r) i = 0}`,
the set of rows of `A` that vanish on every recession direction of
`P := polyhedron_le_set A b`. Then `P + -recessionCone P` is exactly the subsystem cut out by the
rows indexed by `I'`. -/
theorem polyhedron_add_recession_neg_eq_subsystem
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b)) :
    polyhedron_le_set A b + -recessionCone (polyhedron_le_set A b) =
      {y : Fin n → ℝ |
        A.submatrix
            (Subtype.val :
              {i //
                i ∈ {i : Fin m |
                  ∀ r : Fin n → ℝ,
                    r ∈ recessionCone (polyhedron_le_set A b) → (A *ᵥ r) i = 0}} →
                Fin m) id *ᵥ y ≤
          b ∘
            (Subtype.val :
              {i //
                i ∈ {i : Fin m |
                  ∀ r : Fin n → ℝ,
                    r ∈ recessionCone (polyhedron_le_set A b) → (A *ᵥ r) i = 0}} →
                Fin m)} := by
  simpa [recessionFixedRows] using polyhedron_add_recession_neg_eq_subsystem_aux A b h_nonempty
