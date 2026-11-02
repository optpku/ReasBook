import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_definition_3_7_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2

open scoped BigOperators Matrix

/-- The subset of `{x | A *ᵥ x ≤ b}` cut out by making every row in `I` active. -/
def active_constraint_face {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (I : Set (Fin m)) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ |
    (∀ i : Fin m, i ∈ I → (A *ᵥ x) i = b i) ∧
    (∀ i : Fin m, i ∉ I → (A *ᵥ x) i ≤ b i)}

/-- The defining expansion of `active_constraint_face`. -/
theorem mem_active_constraint_face_iff {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ} {I : Set (Fin m)} {x : Fin n → ℝ} :
    x ∈ active_constraint_face A b I ↔
      (∀ i : Fin m, i ∈ I → (A *ᵥ x) i = b i) ∧
      (∀ i : Fin m, i ∉ I → (A *ᵥ x) i ≤ b i) := by
  -- This is exactly the defining predicate of `active_constraint_face`.
  rfl

/-- Helper for Theorem 3.24: every point of the active-constraint face is feasible for
`polyhedron_le_set A b`. -/
lemma mem_polyhedron_of_mem_active_constraint_face
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {I : Set (Fin m)}
    {x : Fin n → ℝ} (hx : x ∈ active_constraint_face A b I) :
    x ∈ polyhedron_le_set A b := by
  change A *ᵥ x ≤ b
  -- Split according to whether the row is prescribed to be active.
  rcases hx with ⟨hactive, hinactive⟩
  intro i
  by_cases hi : i ∈ I
  · exact le_of_eq (hactive i hi)
  · exact hinactive i hi

/-- Helper for Theorem 3.24: summing selected rows and then taking the dot product with `x`
matches summing the corresponding row evaluations `(A *ᵥ x) i`. -/
lemma row_sum_dotProduct_eq_selected_row_sum
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) (x : Fin n → ℝ) :
    (Finset.sum s (fun i ↦ A i) : Fin n → ℝ) ⬝ᵥ x = Finset.sum s (fun i ↦ (A *ᵥ x) i) := by
  -- Reassociate the dot product across the finite sum of rows.
  calc
    (Finset.sum s (fun i ↦ A i) : Fin n → ℝ) ⬝ᵥ x = Finset.sum s (fun i ↦ A i ⬝ᵥ x) := by
      rw [sum_dotProduct]
    _ = Finset.sum s (fun i ↦ (A *ᵥ x) i) := by
      simp [Matrix.mulVec]

/-- Helper for Theorem 3.24: on a feasible point, equality in the sum of the selected
inequalities is equivalent to each selected row being active. -/
lemma selected_row_sum_eq_iff_active_constraints
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {I : Set (Fin m)}
    {x : Fin n → ℝ} (hx : x ∈ polyhedron_le_set A b) :
    (Finset.sum I.toFinite.toFinset (fun i ↦ (A *ᵥ x) i) =
        Finset.sum I.toFinite.toFinset (fun i ↦ b i)) ↔
      ∀ i : Fin m, i ∈ I → (A *ᵥ x) i = b i := by
  classical
  let s : Finset (Fin m) := I.toFinite.toFinset
  change (Finset.sum s (fun i ↦ (A *ᵥ x) i) = Finset.sum s (fun i ↦ b i)) ↔
      ∀ i : Fin m, i ∈ I → (A *ᵥ x) i = b i
  change A *ᵥ x ≤ b at hx
  constructor
  · intro hsum
    -- Convert equality of the selected sums into vanishing nonnegative slacks.
    have hslack_sum :
        Finset.sum s (fun i ↦ b i - (A *ᵥ x) i) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    have hslack_zero :
        ∀ i ∈ s, b i - (A *ᵥ x) i = 0 := by
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i hi ↦ sub_nonneg.mpr (hx i))).1 hslack_sum
    intro i hiI
    have his : i ∈ s := by
      simpa [s] using hiI
    exact (sub_eq_zero.mp (hslack_zero i his)).symm
  · intro hactive
    -- Once every selected row is active, the two selected sums coincide termwise.
    apply Finset.sum_congr rfl
    intro i hi
    exact hactive i (by simpa [s] using hi)

/-- Activating one row means staying feasible and forcing that row to hold at equality. -/
theorem active_constraint_face_singleton_eq
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin m) :
    active_constraint_face A b ({j} : Set (Fin m)) =
      face_set (polyhedron_le_set A b) (A j) (b j) := by
  ext x
  rw [mem_face_set_iff]
  constructor
  · intro hx
    refine ⟨mem_polyhedron_of_mem_active_constraint_face hx, ?_⟩
    simpa [Matrix.mulVec] using (mem_active_constraint_face_iff.mp hx).1 j (by simp)
  · rintro ⟨hxP, hxj⟩
    have hxP' : A *ᵥ x ≤ b := hxP
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro i hi
      have hij : i = j := by simpa using hi
      simpa [hij, Matrix.mulVec] using hxj
    · intro i hi
      exact hxP' i

/-- Theorem 3.24 (1) (Characterization of the Faces). For every subset `I` of the row indices,
the points of `P = polyhedron_le_set A b` where the constraints in `I` are active
form an exposed face of `P`. Here the face relation is expressed by mathlib's canonical
`IsExposed` predicate. -/
theorem active_constraint_face_isExposed
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin m)) :
    IsExposed ℝ (polyhedron_le_set A b) (active_constraint_face A b I) := by
  classical
  by_cases hFace_nonempty : (active_constraint_face A b I).Nonempty
  · let s : Finset (Fin m) := I.toFinite.toFinset
    let c : Fin n → ℝ := Finset.sum s (fun i ↦ A i)
    let δ : ℝ := Finset.sum s (fun i ↦ b i)
    have hvalid : is_valid_inequality (polyhedron_le_set A b) c δ := by
      intro x hxP
      have hxP' : A *ᵥ x ≤ b := hxP
      calc
        c ⬝ᵥ x = Finset.sum s (fun i ↦ (A *ᵥ x) i) := by
          simpa [c] using row_sum_dotProduct_eq_selected_row_sum A s x
        _ ≤ Finset.sum s (fun i ↦ b i) := by
          exact Finset.sum_le_sum (fun i hi ↦ hxP' i)
        _ = δ := rfl
    obtain ⟨x₀, hx₀⟩ := hFace_nonempty
    have hx₀_face : x₀ ∈ face_set (polyhedron_le_set A b) c δ := by
      rw [mem_face_set_iff]
      refine ⟨mem_polyhedron_of_mem_active_constraint_face hx₀, ?_⟩
      rcases hx₀ with ⟨hactive, _⟩
      calc
        c ⬝ᵥ x₀ = Finset.sum s (fun i ↦ (A *ᵥ x₀) i) := by
          simpa [c] using row_sum_dotProduct_eq_selected_row_sum A s x₀
        _ = Finset.sum s (fun i ↦ b i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hactive i (by simpa [s] using hi)
        _ = δ := rfl
    have hface_eq :
        active_constraint_face A b I = face_set (polyhedron_le_set A b) c δ := by
      ext x
      rw [mem_face_set_iff]
      constructor
      · intro hx
        refine ⟨mem_polyhedron_of_mem_active_constraint_face hx, ?_⟩
        rcases hx with ⟨hactive, _⟩
        calc
          c ⬝ᵥ x = Finset.sum s (fun i ↦ (A *ᵥ x) i) := by
            simpa [c] using row_sum_dotProduct_eq_selected_row_sum A s x
          _ = Finset.sum s (fun i ↦ b i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hactive i (by simpa [s] using hi)
          _ = δ := rfl
      · rintro ⟨hxP, hxEq⟩
        have hx_sum :
            Finset.sum s (fun i ↦ (A *ᵥ x) i) = Finset.sum s (fun i ↦ b i) := by
          calc
            Finset.sum s (fun i ↦ (A *ᵥ x) i) = c ⬝ᵥ x := by
              simpa [c] using (row_sum_dotProduct_eq_selected_row_sum A s x).symm
            _ = δ := hxEq
            _ = Finset.sum s (fun i ↦ b i) := rfl
        refine (mem_active_constraint_face_iff).2 ?_
        constructor
        · exact (selected_row_sum_eq_iff_active_constraints hxP).1 hx_sum
        · intro i hi
          exact hxP i
    rw [hface_eq, face_set_eq_toExposed_of_mem hvalid hx₀_face]
    exact ContinuousLinearMap.toExposed.isExposed
  · -- If the activated system is inconsistent, the resulting face is empty, hence exposed.
    have hface_empty : active_constraint_face A b I = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact hFace_nonempty ⟨x, hx⟩
    rw [hface_empty]
    exact isExposed_empty

/-- Helper for Theorem 3.24: a nonempty exposed face of `polyhedron_le_set A b` is
the equality face of one valid inequality `c ⬝ᵥ x ≤ δ`. -/
lemma exists_eq_face_set_of_isExposed_of_nonempty
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {F : Set (Fin n → ℝ)}
    (hF_face : IsExposed ℝ (polyhedron_le_set A b) F)
    (hF_nonempty : F.Nonempty) :
    ∃ c : Fin n → ℝ, ∃ δ : ℝ,
      is_valid_inequality (polyhedron_le_set A b) c δ ∧
        F = face_set (polyhedron_le_set A b) c δ := by
  rcases (isExposed_iff_eq_empty_or_eq_face_set.mp hF_face) with hF_empty | ⟨c, δ, hvalid, hF⟩
  · obtain ⟨x, hx⟩ := hF_nonempty
    exfalso
    simp [hF_empty] at hx
  · exact ⟨c, δ, hvalid, hF⟩

/-- Helper for Theorem 3.24: if a valid inequality for `polyhedron_le_set A b` is
attained on its equality face, then it comes from a nonnegative row multiplier with exact
objective value. -/
theorem exists_nonneg_multiplier_of_attained_valid_inequality
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (δ : ℝ)
    (hvalid : is_valid_inequality (polyhedron_le_set A b) c δ)
    (hattained : (face_set (polyhedron_le_set A b) c δ).Nonempty) :
    ∃ u : Fin m → ℝ, (∀ i : Fin m, 0 ≤ u i) ∧ u ᵥ* A = c ∧ u ⬝ᵥ b = δ := by
  obtain ⟨x₀, hx₀_face⟩ := hattained
  have hx₀_polyhedron : x₀ ∈ polyhedron_le_set A b := (mem_face_set_iff.mp hx₀_face).1
  have hx₀_eq : c ⬝ᵥ x₀ = δ := (mem_face_set_iff.mp hx₀_face).2
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := ⟨x₀, hx₀_polyhedron⟩
  obtain ⟨u, hu_nonneg, hrow, hub_le⟩ :=
    (valid_inequality_iff_exists_nonneg_row_multiplier A b c δ hP_nonempty).mp hvalid
  have hδ_le : δ ≤ u ⬝ᵥ b := by
    -- Evaluate the multiplier certificate at a point where the valid inequality is tight.
    calc
      δ = c ⬝ᵥ x₀ := hx₀_eq.symm
      _ = (u ᵥ* A) ⬝ᵥ x₀ := by
        rw [← hrow]
      _ = u ⬝ᵥ (A *ᵥ x₀) := by
        rw [← Matrix.dotProduct_mulVec]
      _ ≤ u ⬝ᵥ b := by
        -- Nonnegative weights preserve the rowwise feasibility inequality `A *ᵥ x₀ ≤ b`.
        exact dotProduct_le_dotProduct_of_nonneg_left hx₀_polyhedron hu_nonneg
  have hδ_eq : u ⬝ᵥ b = δ := le_antisymm hub_le hδ_le
  refine ⟨u, ?_, hrow, hδ_eq⟩
  -- Convert the pointwise nonnegativity certificate into the theorem's explicit form.
  intro i
  exact hu_nonneg i

/-- Helper for Theorem 3.24: once a valid inequality is written as a nonnegative row
combination, its equality section is exactly the active-constraint face supported on the positive
entries of that multiplier. -/
lemma mem_face_set_iff_mem_active_constraint_face_of_support
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ} {δ : ℝ}
    {u : Fin m → ℝ} (hu : ∀ i : Fin m, 0 ≤ u i) (hrow : u ᵥ* A = c) (hδ : u ⬝ᵥ b = δ)
    {x : Fin n → ℝ} :
    x ∈ face_set (polyhedron_le_set A b) c δ ↔
      x ∈ active_constraint_face A b {i : Fin m | 0 < u i} := by
  rw [mem_face_set_iff]
  constructor
  · rintro ⟨hxP, hxEq⟩
    have hxP' : A *ᵥ x ≤ b := hxP
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro i hi
      -- Equality of the weighted slacks forces every positive-weight row to be active.
      have hslack_dot_zero : u ⬝ᵥ (b - A *ᵥ x) = 0 := by
        calc
          u ⬝ᵥ (b - A *ᵥ x) = u ⬝ᵥ b - u ⬝ᵥ (A *ᵥ x) := by
            rw [dotProduct_sub]
          _ = δ - c ⬝ᵥ x := by
            rw [hδ, ← hrow, Matrix.dotProduct_mulVec]
          _ = 0 := by
            rw [hxEq, sub_self]
      have hterm_zero :
          ∀ i : Fin m, u i * (b i - (A *ᵥ x) i) = 0 := by
        have hsum_zero :
            ∑ i : Fin m, u i * (b i - (A *ᵥ x) i) = 0 := by
          simpa [dotProduct] using hslack_dot_zero
        have hzero_on_univ :
            ∀ i ∈ (Finset.univ : Finset (Fin m)), u i * (b i - (A *ᵥ x) i) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun i hiFin ↦ mul_nonneg (hu i) (sub_nonneg.mpr (hxP' i)))).1 hsum_zero
        intro i
        exact hzero_on_univ i (Finset.mem_univ i)
      have hslack_zero : b i - (A *ᵥ x) i = 0 := by
        exact (mul_eq_zero.mp (hterm_zero i)).resolve_left (ne_of_gt hi)
      exact (sub_eq_zero.mp hslack_zero).symm
    · intro i hi
      exact hxP' i
  · intro hx
    have hxP : x ∈ polyhedron_le_set A b :=
      mem_polyhedron_of_mem_active_constraint_face hx
    refine (mem_face_set_iff).2 ⟨hxP, ?_⟩
    have hu_zero :
        ∀ i : Fin m, i ∉ ({i : Fin m | 0 < u i} : Set (Fin m)) → u i = 0 := by
      intro i hi
      exact le_antisymm (le_of_not_gt hi) (hu i)
    have hterm_eq :
        ∀ i : Fin m, u i * (A *ᵥ x) i = u i * b i := by
      intro i
      by_cases hi : 0 < u i
      · rw [(mem_active_constraint_face_iff.mp hx).1 i hi]
      · simp [hu_zero i hi]
    have hdot_eq : u ⬝ᵥ (A *ᵥ x) = u ⬝ᵥ b := by
      unfold dotProduct
      exact Finset.sum_congr rfl (fun i hi ↦ hterm_eq i)
    calc
      c ⬝ᵥ x = (u ᵥ* A) ⬝ᵥ x := by
        rw [hrow]
      _ = u ⬝ᵥ (A *ᵥ x) := by
        rw [← Matrix.dotProduct_mulVec]
      _ = u ⬝ᵥ b := hdot_eq
      _ = δ := hδ

/-- Theorem 3.24 (2) (Characterization of the Faces). Conversely, every nonempty exposed face of
the polyhedron `P = polyhedron_le_set A b` is the active-constraint face cut out by
some subset `I` of the defining inequalities. Here the face relation is expressed by mathlib's
canonical `IsExposed` predicate. -/
theorem exists_eq_active_constraint_face_of_isExposed
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (hF_face : IsExposed ℝ (polyhedron_le_set A b) F)
    (hF_nonempty : F.Nonempty) :
    ∃ I : Set (Fin m), F = active_constraint_face A b I := by
  obtain ⟨c, δ, hvalid, hF_section⟩ :=
    exists_eq_face_set_of_isExposed_of_nonempty hF_face hF_nonempty
  obtain ⟨u, hu, hrow, hδ⟩ :=
    exists_nonneg_multiplier_of_attained_valid_inequality A b c δ hvalid <| hF_section ▸ hF_nonempty
  refine ⟨{i : Fin m | 0 < u i}, ?_⟩
  -- Route correction: close the converse by the multiplier-support description from the source
  -- proof, rather than switching to an unrelated characterization of faces.
  ext x
  rw [hF_section, mem_face_set_iff_mem_active_constraint_face_of_support hu hrow hδ]
