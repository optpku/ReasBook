import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_1.ch3_sec3_4_1_definition_3_4_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_definition_3_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.Recession
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_theorem_3_40
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_14

open scoped Matrix Pointwise

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the exercise below
-- is organized around the existing Chapter 3 owners `is_polyhedron`, `is_pointed`,
-- `IsExtremeRayOfPolyhedron`, and `IsEdgeOf`, together with mathlib's canonical
-- `Set.extremePoints ℝ` owner for vertices.

/-- Helper for Exercise 3.27: membership in the ray hull of a singleton is exactly being a
nonnegative scalar multiple of its generator. -/
lemma mem_singleton_ray_hull_iff
    {n : ℕ} {r x : Fin n → ℝ} :
    x ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) ↔
      ∃ μ : ℝ, 0 ≤ μ ∧ x = μ • r := by
  have hmem :
      x ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) ↔
        ∃ q : ℕ, ∃ rays : Fin q → Fin n → ℝ, (∀ j, rays j ∈ ({r} : Set (Fin n → ℝ))) ∧
          ∃ coeff : Fin q → ℝ, (∀ j, 0 ≤ coeff j) ∧ x = ∑ j, coeff j • rays j := by
    simpa using (mem_hull_iff (X := ({r} : Set (Fin n → ℝ))) (v := x))
  rw [hmem]
  constructor
  · rintro ⟨q, rays, hrays, coeff, hcoeff, hsum⟩
    refine ⟨∑ j, coeff j, Finset.sum_nonneg fun j _ ↦ hcoeff j, ?_⟩
    calc
      x = ∑ j, coeff j • rays j := hsum
      _ = ∑ j, coeff j • r := by
            apply Finset.sum_congr rfl
            intro j hj
            have hrj : rays j = r := Set.mem_singleton_iff.mp (hrays j)
            simp [hrj]
      _ = (∑ j, coeff j) • r := by
            rw [Finset.sum_smul]
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨1, fun _ ↦ r, ?_, fun _ ↦ μ, ?_, ?_⟩
    · intro j
      simp
    · intro j
      exact hμ
    · simp

/-- Bridge/view for Exercise 3.27: the source-written translated ray through `x̄` with direction
`r` is the singleton translate of the canonical ray hull used by `IsExtremeRayOfPolyhedron`. -/
theorem translated_ray_eq_singleton_add_ray_hull
    {n : ℕ} (xbar r : Fin n → ℝ) :
    {x : Fin n → ℝ | ∃ μ : ℝ, 0 ≤ μ ∧ x = xbar + μ • r} =
      {xbar} + (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨μ, hμ, rfl⟩
    -- Rewrite the source-style translated half-line as a singleton translate by the canonical ray.
    refine Set.mem_add.mpr ?_
    refine ⟨xbar, by simp, μ • r, ?_, by simp⟩
    exact mem_singleton_ray_hull_iff.mpr ⟨μ, hμ, rfl⟩
  · intro hx
    rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, rfl⟩
    rcases Set.mem_singleton_iff.mp hy with rfl
    rcases mem_singleton_ray_hull_iff.mp hz with ⟨μ, hμ, hμr⟩
    exact ⟨μ, hμ, by simp [hμr]⟩

/-- Helper for Exercise 3.27: every generator belongs to its own singleton ray hull. -/
lemma self_mem_singleton_ray_hull
    {n : ℕ} (r : Fin n → ℝ) :
    r ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  -- The singleton-support coefficient family with weight `1` realizes the generator itself.
  exact mem_singleton_ray_hull_iff.mpr ⟨1, by positivity, by simp⟩

/-- Helper for Exercise 3.27: the ray hull of `0` collapses to the singleton `{0}`. -/
lemma singleton_ray_hull_zero
    {n : ℕ} :
    (PointedCone.hull ℝ ({(0 : Fin n → ℝ)} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) =
      ({0} : Set (Fin n → ℝ)) := by
  ext x
  rw [mem_singleton_ray_hull_iff]
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    simp
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨0, le_rfl, by simp⟩

/-- Helper for Exercise 3.27: an extreme ray generator of a polyhedron is nonzero. -/
lemma extreme_ray_ne_zero
    {n : ℕ} {P : Set (Fin n → ℝ)} {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron P r) :
    r ≠ 0 := by
  rw [isExtremeRayOfPolyhedron_iff, isExtremeRayOfCone_iff] at hr
  intro hr_zero
  have hzero_edge : IsEdgeOf (recessionCone P) ({0} : Set (Fin n → ℝ)) := by
    simpa [hr_zero, singleton_ray_hull_zero] using hr
  -- The singleton `{0}` has zero-dimensional affine direction, contradicting the edge axiom.
  have hdim_zero : Module.finrank ℝ (affineSpan ℝ ({0} : Set (Fin n → ℝ))).direction = 0 := by
    rw [direction_affineSpan, vectorSpan_singleton]
    simp
  have hdim_one : Module.finrank ℝ (affineSpan ℝ ({0} : Set (Fin n → ℝ))).direction = 1 :=
    hzero_edge.finrank_direction_eq_one
  have : (0 : ℕ) = 1 := by
    rwa [hdim_zero] at hdim_one
  exact Nat.zero_ne_one this

/-- A nonempty pointed polyhedron has a nonempty extreme-point set. -/
lemma pointed_polyhedron_extremePoints_nonempty
    {n : ℕ} {P : Set (Fin n → ℝ)}
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty)
    (hP_pointed : is_pointed P) :
    (P.extremePoints ℝ).Nonempty := by
  exact (polyhedron_extremePoints_nonempty_iff_is_pointed hP_polyhedron hP_nonempty).2 hP_pointed

/-- Helper for Exercise 3.27: every matrix polyhedron is convex. -/
lemma polyhedron_le_set_convex
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  intro x hx y hy a₁ a₂ ha₁ ha₂ ha_sum
  -- Convex combinations preserve each row inequality separately.
  intro i
  have hx_i : (A *ᵥ x) i ≤ b i := hx i
  have hy_i : (A *ᵥ y) i ≤ b i := hy i
  have hcomb :
      (A *ᵥ (a₁ • x + a₂ • y)) i = a₁ * (A *ᵥ x) i + a₂ * (A *ᵥ y) i := by
    simp [Matrix.mulVec_add, Matrix.mulVec_smul, mul_add, add_mul]
  rw [hcomb]
  have hle :
      a₁ * (A *ᵥ x) i + a₂ * (A *ᵥ y) i ≤ a₁ * b i + a₂ * b i :=
    add_le_add
      (mul_le_mul_of_nonneg_left hx_i ha₁)
      (mul_le_mul_of_nonneg_left hy_i ha₂)
  calc
    a₁ * (A *ᵥ x) i + a₂ * (A *ᵥ y) i ≤ a₁ * b i + a₂ * b i := hle
    _ = (a₁ + a₂) * b i := by ring
    _ = b i := by rw [ha_sum, one_mul]

/-- Helper for Exercise 3.27: the homogeneous system `A *ᵥ x ≤ 0` written as a polyhedron. -/
abbrev matrix_polyhedral_cone
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  polyhedron_le_set A 0

/-- Helper for Exercise 3.27: membership in `matrix_polyhedral_cone A` is the rowwise inequality
`A *ᵥ x ≤ 0`. -/
theorem mem_matrix_polyhedral_cone
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ∈ matrix_polyhedral_cone A ↔ A *ᵥ x ≤ 0 := by
  rfl

/-- Helper for Exercise 3.27: the recession cone of `polyhedron_le_set A b` is exactly the
homogeneous matrix cone with the same coefficient matrix. -/
lemma recessionCone_polyhedron_eq_matrix_polyhedral_cone
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty) :
    recessionCone (polyhedron_le_set A b) = matrix_polyhedral_cone A := by
  -- Rewrite both owners to the same homogeneous rowwise inequality system.
  ext x
  rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b hP_nonempty]
  rw [mem_matrix_polyhedral_cone]
  rfl

/-- Helper for Exercise 3.27: a nonzero vector has some nonzero coordinate. -/
lemma exists_nonzero_coordinate_of_ne_zero
    {n : ℕ} {x : Fin n → ℝ}
    (hx : x ≠ 0) :
    ∃ j : Fin n, x j ≠ 0 := by
  -- If every coordinate vanished, extensionality would force the whole vector to be `0`.
  by_contra h
  apply hx
  ext j
  by_contra hj
  exact h ⟨j, hj⟩

/-- Helper for Exercise 3.27: augment the homogeneous system `A *ᵥ x ≤ 0` with the two slice
rows forcing the coordinate `x j` to equal `r j`. -/
def coneCoordinateSliceMatrix
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) :
    Matrix (Fin (m + 2)) (Fin n) ℝ :=
  fun i ↦
    Fin.cases
      (Pi.single j (1 : ℝ))
      (fun i' ↦ Fin.cases (Pi.single j (-1 : ℝ)) (fun i'' ↦ A i'') i')
      i

/-- Helper for Exercise 3.27: the right-hand side for the coordinate slice through `r`. -/
def coneCoordinateSliceRhs
    {m n : ℕ}
    (r : Fin n → ℝ)
    (j : Fin n) :
    Fin (m + 2) → ℝ :=
  fun i ↦
    Fin.cases (r j)
      (fun i' ↦ Fin.cases (-r j) (fun _ ↦ (0 : ℝ)) i')
      i

/-- Helper for Exercise 3.27: every tail row of the coordinate-slice matrix is an original row of
`A`. -/
lemma coneCoordinateSliceMatrix_tail_row
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n)
    (i : Fin m) :
    coneCoordinateSliceMatrix A j i.succ.succ = A i := by
  -- After skipping the two auxiliary rows, the slice system is literally the original matrix.
  ext k
  simp [coneCoordinateSliceMatrix]

/-- Helper for Exercise 3.27: every tail row of the coordinate-slice right-hand side is `0`. -/
lemma coneCoordinateSliceRhs_tail_row
    {m n : ℕ}
    (r : Fin n → ℝ)
    (j : Fin n)
    (i : Fin m) :
    coneCoordinateSliceRhs r j i.succ.succ = 0 := by
  -- The coordinate slice only changes the first two right-hand-side entries.
  simp [coneCoordinateSliceRhs]

/-- Helper for Exercise 3.27: any non-auxiliary slice row is one of the original rows of `A`. -/
lemma exists_tail_index_of_ne_auxiliary_slice_row
    {m : ℕ}
    {p : Fin (m + 2)}
    (hp0 : p ≠ 0)
    (hp1 : p ≠ 1) :
    ∃ i : Fin m, p = i.succ.succ := by
  -- A row index in `Fin (m + 2)` is either one of the two auxiliary rows or a tail row.
  rcases p with ⟨k, hk⟩
  cases k with
  | zero =>
      exact False.elim (hp0 rfl)
  | succ k =>
      cases k with
      | zero =>
          exact False.elim (hp1 rfl)
      | succ k =>
          refine ⟨⟨k, by omega⟩, rfl⟩

/-- Helper for Exercise 3.27: the two auxiliary slice rows are negatives of each other, so they
cannot both appear in a linearly independent family. -/
lemma not_linearIndependent_auxiliary_slice_rows
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) :
    ¬ LinearIndependent ℝ
      (![coneCoordinateSliceMatrix A j 0, coneCoordinateSliceMatrix A j 1] :
        Fin 2 → Fin n → ℝ) := by
  intro hlin
  have hrow0 : coneCoordinateSliceMatrix A j 0 = Pi.single j (1 : ℝ) := rfl
  have hrow1 : coneCoordinateSliceMatrix A j 1 = Pi.single j (-1 : ℝ) := rfl
  -- The two auxiliary rows sum to zero because they are coordinatewise negatives.
  have hsum :
      ∑ i : Fin 2,
          ((![1, 1] : Fin 2 → ℝ) i) •
            (![coneCoordinateSliceMatrix A j 0, coneCoordinateSliceMatrix A j 1] :
              Fin 2 → Fin n → ℝ) i = 0 := by
    ext k
    rw [Fin.sum_univ_two]
    by_cases hk : k = j
    · subst hk
      simp [hrow0, hrow1, Pi.single_apply]
    · simp [hrow0, hrow1, Pi.single_apply, hk]
  have hcoeff_zero :=
    (Fintype.linearIndependent_iff.mp hlin) (![1, 1] : Fin 2 → ℝ) hsum
  have h0 : ((![1, 1] : Fin 2 → ℝ) 0) = 0 := hcoeff_zero 0
  norm_num at h0

/-- Helper for Exercise 3.27: the augmented slice system is exactly the cone system together with
the equation `x j = r j`. -/
lemma mem_coneCoordinateSlice_iff
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin n → ℝ)
    (j : Fin n)
    {x : Fin n → ℝ} :
    x ∈ polyhedron_le_set (coneCoordinateSliceMatrix A j) (coneCoordinateSliceRhs r j) ↔
      x ∈ matrix_polyhedral_cone A ∧ x j = r j := by
  have hrow0 : coneCoordinateSliceMatrix A j 0 = Pi.single j (1 : ℝ) := rfl
  have hrow1 : coneCoordinateSliceMatrix A j 1 = Pi.single j (-1 : ℝ) := rfl
  have hrhs0 : coneCoordinateSliceRhs r j (0 : Fin (m + 2)) = r j := by
    simp [coneCoordinateSliceRhs]
  have hrhs1 : coneCoordinateSliceRhs r j (1 : Fin (m + 2)) = -r j := by
    cases m <;> rfl
  rw [mem_polyhedron_le_set_iff, mem_matrix_polyhedral_cone]
  constructor
  · intro hx
    constructor
    · intro i
      -- Tail rows of the slice are exactly the original homogeneous inequalities.
      simpa [Matrix.mulVec, coneCoordinateSliceMatrix_tail_row, coneCoordinateSliceRhs_tail_row]
        using hx i.succ.succ
    · -- The first two auxiliary inequalities force the selected coordinate to equal `r j`.
      have hleft : x j ≤ r j := by
        have hleft_raw : (coneCoordinateSliceMatrix A j *ᵥ x) 0 ≤ coneCoordinateSliceRhs r j 0 :=
          hx 0
        change (coneCoordinateSliceMatrix A j 0) ⬝ᵥ x ≤ coneCoordinateSliceRhs r j 0 at hleft_raw
        rw [hrow0, hrhs0, dotProduct] at hleft_raw
        simpa [Pi.single_apply] using hleft_raw
      have hright : -x j ≤ -r j := by
        have hright_raw : (coneCoordinateSliceMatrix A j *ᵥ x) 1 ≤ coneCoordinateSliceRhs r j 1 :=
          hx 1
        change (coneCoordinateSliceMatrix A j 1) ⬝ᵥ x ≤ coneCoordinateSliceRhs r j 1 at hright_raw
        rw [hrow1, hrhs1, dotProduct] at hright_raw
        simpa [Pi.single_apply] using hright_raw
      linarith
  · rintro ⟨hx_cone, hxj⟩
    -- Rebuild the slice inequalities from the cone inequalities and the fixed coordinate.
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      change (coneCoordinateSliceMatrix A j 0) ⬝ᵥ x ≤ coneCoordinateSliceRhs r j 0
      rw [hrow0, hrhs0, dotProduct]
      simpa [Pi.single_apply, hxj]
    · by_cases hi1 : i = 1
      · subst hi1
        change (coneCoordinateSliceMatrix A j 1) ⬝ᵥ x ≤ coneCoordinateSliceRhs r j 1
        rw [hrow1, hrhs1, dotProduct]
        simpa [Pi.single_apply, hxj]
      · rcases exists_tail_index_of_ne_auxiliary_slice_row hi0 hi1 with ⟨i', rfl⟩
        simpa [Matrix.mulVec, coneCoordinateSliceMatrix_tail_row, coneCoordinateSliceRhs_tail_row]
          using hx_cone i'

/-- Helper for Exercise 3.27: the extreme-ray generator itself belongs to its coordinate slice. -/
lemma extreme_ray_mem_coneCoordinateSlice
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron (polyhedron_le_set A b) r)
    (j : Fin n) :
    r ∈ polyhedron_le_set (coneCoordinateSliceMatrix A j) (coneCoordinateSliceRhs r j) := by
  have hr_edge :
      IsEdgeOf (recessionCone (polyhedron_le_set A b))
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    exact (isExtremeRayOfCone_iff).1 ((isExtremeRayOfPolyhedron_iff).1 hr)
  have hr_mem_recession : r ∈ recessionCone (polyhedron_le_set A b) := by
    exact hr_edge.isExtreme.1 (self_mem_singleton_ray_hull r)
  rw [mem_coneCoordinateSlice_iff]
  constructor
  · rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone A b hP_nonempty] at hr_mem_recession
    exact hr_mem_recession
  · rfl

/-- Helper for Exercise 3.27: once the coordinate slice fixes `x j = r j`, every point of that
slice lying on the singleton ray through `r` is equal to `r`. -/
lemma eq_of_mem_coneCoordinateSlice_and_mem_singleton_ray_hull
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {r x : Fin n → ℝ}
    (j : Fin n)
    (hrj : r j ≠ 0)
    (hx_slice :
      x ∈ polyhedron_le_set (coneCoordinateSliceMatrix A j) (coneCoordinateSliceRhs r j))
    (hx_ray : x ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) :
    x = r := by
  rcases mem_singleton_ray_hull_iff.mp hx_ray with ⟨μ, hμ, rfl⟩
  have hcoord : μ * r j = r j := by
    simpa using (mem_coneCoordinateSlice_iff A r j).mp hx_slice |>.2
  have hmu_eq : μ = 1 := by
    have hmul_zero : (μ - 1) * r j = 0 := by
      linarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hmul_zero).resolve_right hrj))
  -- Matching the fixed coordinate with a nonzero one forces the scaling to be `1`.
  simp [hmu_eq]

/-- Helper for Exercise 3.27: after rewriting `P` as `polyhedron_le_set A b`, Theorem 3.35
produces `n - 1` active independent rows at the given extreme recession ray. -/
lemma exists_active_linearlyIndependent_rows_of_extremePoint
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ polyhedron_le_set A b)
    (hxbar_extreme : xbar ∈ (polyhedron_le_set A b).extremePoints ℝ) :
    ∃ I : Fin n ↪ Fin m,
      (∀ i : Fin n, (A *ᵥ xbar) (I i) = b (I i)) ∧
        LinearIndependent ℝ (fun i : Fin n ↦ A (I i)) := by
  classical
  let activeRows : Set (Fin n → ℝ) :=
    Set.range fun i : {i // (A *ᵥ xbar) i = b i} ↦ A i.1
  have hspan : Submodule.span ℝ activeRows = ⊤ := by
    by_contra hspan_ne
    let K : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ activeRows
    have hKlt : K < ⊤ := lt_of_le_of_ne le_top hspan_ne
    obtain ⟨φ, hφ_ne, hKker⟩ := Submodule.exists_le_ker_of_lt_top K hKlt
    let r : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm φ
    have hr_ne : r ≠ 0 := by
      intro hr
      apply hφ_ne
      simpa [r, hr] using ((dotProductEquiv ℝ (Fin n)).apply_symm_apply φ).symm
    have hactive_eval : ∀ i : Fin m, (A *ᵥ xbar) i = b i → (A *ᵥ r) i = 0 := by
      intro i hi
      have hAi_mem : A i ∈ K := by
        refine Submodule.subset_span ?_
        exact ⟨⟨i, hi⟩, rfl⟩
      have hφAi : φ (A i) = 0 := by
        simpa using hKker hAi_mem
      have hφr : (dotProductEquiv ℝ (Fin n)) r = φ := by
        simp [r]
      have hdot : dotProduct r (A i) = 0 := by
        simpa [hφAi] using congrArg (fun f : Module.Dual ℝ (Fin n → ℝ) => f (A i)) hφr
      have hrowdot : dotProduct (A i) r = 0 := by
        simpa [dotProduct_comm] using hdot
      simpa [Matrix.mulVec, dotProduct] using hrowdot
    let δ : Fin m → ℝ := fun i ↦
      if hi : (A *ᵥ xbar) i = b i then 1
      else if hzero : (A *ᵥ r) i = 0 then 1
      else (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i|
    have hδ_pos : ∀ i : Fin m, 0 < δ i := by
      intro i
      by_cases hi : (A *ᵥ xbar) i = b i
      · simp [δ, hi]
      · by_cases hzero : (A *ᵥ r) i = 0
        · simp [δ, hi, hzero]
        · have hlt : (A *ᵥ xbar) i < b i := lt_of_le_of_ne (hxbar i) hi
          have hnum : 0 < b i - (A *ᵥ xbar) i := sub_pos.mpr hlt
          have hden : 0 < |(A *ᵥ r) i| := abs_pos.mpr hzero
          simp [δ, hi, hzero, div_pos hnum hden]
    let δs : Finset ℝ := insert 1 (Finset.univ.image δ)
    let ε : ℝ := δs.min' (by simp [δs]) / 2
    have hmin_pos : 0 < δs.min' (by simp [δs]) := by
      have hmin_mem : δs.min' (by simp [δs]) ∈ δs := Finset.min'_mem _ _
      rcases Finset.mem_insert.mp hmin_mem with h1 | himage
      · simpa [h1]
      · rcases Finset.mem_image.mp himage with ⟨i, _, hi⟩
        rw [← hi]
        exact hδ_pos i
    have hε_pos : 0 < ε := half_pos hmin_pos
    have hε_le : ∀ i : Fin m, ε ≤ δ i := by
      intro i
      have hmin_le : δs.min' (by simp [δs]) ≤ δ i := by
        apply Finset.min'_le
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      have hhalf_le : δs.min' (by simp [δs]) / 2 ≤ δs.min' (by simp [δs]) := by
        linarith
      exact hhalf_le.trans hmin_le
    have hperturb_eval (σ : ℝ) (i : Fin m) :
        (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := by
      -- Expand the row evaluation on the perturbed point once and reuse it in each case split.
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      simp
    have hperturb_mem : ∀ {σ : ℝ}, |σ| ≤ ε → xbar + σ • r ∈ polyhedron_le_set A b := by
      intro σ hσ
      rw [mem_polyhedron_le_set_iff]
      intro i
      by_cases hi : (A *ᵥ xbar) i = b i
      · -- Active rows stay fixed because the perturbation annihilates them.
        calc
          (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
          _ = b i := by simp [hi, hactive_eval i hi]
          _ ≤ b i := le_rfl
      · by_cases hzero : (A *ᵥ r) i = 0
        · -- Rows with zero slope keep their original slack.
          calc
            (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
            _ = (A *ᵥ xbar) i := by simp [hzero]
            _ ≤ b i := hxbar i
        · -- For strictly sloped rows, choose `ε` small enough to preserve feasibility.
          have hlt : (A *ᵥ xbar) i < b i := lt_of_le_of_ne (hxbar i) hi
          have hσ_bound : |σ| ≤ (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i| := by
            calc
              |σ| ≤ ε := hσ
              _ ≤ δ i := hε_le i
              _ = (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i| := by simp [δ, hi, hzero]
          have hden : 0 < |(A *ᵥ r) i| := abs_pos.mpr hzero
          have hmul_le :
              |σ| * |(A *ᵥ r) i| ≤ b i - (A *ᵥ xbar) i := by
            have hmul := mul_le_mul_of_nonneg_right hσ_bound hden.le
            have hcancel :
                ((b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i|) * |(A *ᵥ r) i| =
                  b i - (A *ᵥ xbar) i := by
              field_simp [hden.ne']
            simpa [hcancel] using hmul
          have habs_le : |σ * (A *ᵥ r) i| ≤ b i - (A *ᵥ xbar) i := by
            simpa [abs_mul] using hmul_le
          have hterm_le : σ * (A *ᵥ r) i ≤ b i - (A *ᵥ xbar) i := by
            exact (le_abs_self _).trans habs_le
          calc
            (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
            _ ≤ b i := by linarith
    let xMinus : Fin n → ℝ := xbar - ε • r
    let xPlus : Fin n → ℝ := xbar + ε • r
    have hxMinus : xMinus ∈ polyhedron_le_set A b := by
      have hneg : |(-ε : ℝ)| ≤ ε := by simpa [abs_of_nonneg hε_pos.le]
      simpa [xMinus, sub_eq_add_neg] using (hperturb_mem (σ := -ε) hneg)
    have hxPlus : xPlus ∈ polyhedron_le_set A b := by
      have hpos : |(ε : ℝ)| ≤ ε := by simpa [abs_of_nonneg hε_pos.le]
      simpa [xPlus] using (hperturb_mem (σ := ε) hpos)
    have hxMinus_ne : xMinus ≠ xbar := by
      intro hEq
      have hsmul : ε • r = 0 := sub_eq_self.mp hEq
      exact hr_ne ((smul_eq_zero.mp hsmul).resolve_left (ne_of_gt hε_pos))
    have hxPlus_ne : xPlus ≠ xbar := by
      intro hEq
      have hsmul : ε • r = 0 := by
        have := congrArg (fun u : Fin n → ℝ ↦ u - xbar) hEq
        simpa [xPlus, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      exact hr_ne ((smul_eq_zero.mp hsmul).resolve_left (ne_of_gt hε_pos))
    have hxbar_segment : xbar ∈ segment ℝ xMinus xPlus := by
      -- The midpoint identity places `xbar` on the segment between the two perturbations.
      simpa [xMinus, xPlus] using (mem_segment_sub_add (𝕜 := ℝ) xbar (ε • r))
    have hxbar_open : xbar ∈ openSegment ℝ xMinus xPlus := by
      exact mem_openSegment_of_ne_left_right hxMinus_ne hxPlus_ne hxbar_segment
    have hxext := (mem_extremePoints_iff_left).mp hxbar_extreme
    exact hxMinus_ne (hxext.2 xMinus hxMinus xPlus hxPlus hxbar_open)
  have hdim : Module.finrank ℝ ↥(Submodule.span ℝ activeRows) = n := by
    rw [hspan]
    simpa using (Module.finrank_fin_fun ℝ (n := n))
  obtain ⟨g, hg_mem, _hg_span, hg_linear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ activeRows
  let e : Fin (Module.finrank ℝ ↥(Submodule.span ℝ activeRows)) ≃ Fin n :=
    (Fin.castOrderIso hdim).toEquiv
  let rows : Fin n → Fin n → ℝ := fun i ↦ g (e.symm i)
  have hrows_mem : ∀ i : Fin n, rows i ∈ activeRows := by
    intro i
    exact hg_mem (e.symm i)
  have hrows_linear : LinearIndependent ℝ rows := by
    exact (linearIndependent_equiv e.symm).2 hg_linear
  have hrows_mem' :
      ∀ i : Fin n, ∃ j : {j // (A *ᵥ xbar) j = b j}, A j.1 = rows i := by
    intro i
    simpa [activeRows] using hrows_mem i
  let chosen : Fin n → {j // (A *ᵥ xbar) j = b j} :=
    fun i ↦ Classical.choose (hrows_mem' i)
  have hchosen_row : ∀ i : Fin n, A (chosen i).1 = rows i := by
    intro i
    exact Classical.choose_spec (hrows_mem' i)
  have hchosen_injective : Function.Injective fun i : Fin n ↦ (chosen i).1 := by
    intro i j hij
    apply hrows_linear.injective
    calc
      rows i = A (chosen i).1 := (hchosen_row i).symm
      _ = A (chosen j).1 := by simpa [hij]
      _ = rows j := hchosen_row j
  let I : Fin n ↪ Fin m := ⟨fun i ↦ (chosen i).1, hchosen_injective⟩
  refine ⟨I, ?_, ?_⟩
  · intro i
    -- The chosen row witnesses come from the active-row subtype by construction.
    exact (chosen i).2
  · have hrows : (fun i : Fin n ↦ A (I i)) = rows := by
      funext i
      exact hchosen_row i
    simpa [hrows] using hrows_linear

/-- Helper for Exercise 3.27: after rewriting `P` as `polyhedron_le_set A b`, the coordinate-slice
point `r` is extreme because any slice segment through `r` stays on the same singleton ray. -/
lemma coneCoordinateSliceExtremePoint
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron (polyhedron_le_set A b) r)
    (j : Fin n)
    (hrj : r j ≠ 0) :
    r ∈ (polyhedron_le_set (coneCoordinateSliceMatrix A j) (coneCoordinateSliceRhs r j)).extremePoints
      ℝ := by
  have hr_edge :
      IsEdgeOf (recessionCone (polyhedron_le_set A b))
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    exact (isExtremeRayOfCone_iff).1 ((isExtremeRayOfPolyhedron_iff).1 hr)
  refine (mem_extremePoints_iff_left).2 ?_
  constructor
  · exact extreme_ray_mem_coneCoordinateSlice A b hP_nonempty hr j
  · intro x hx y hy hr_open
    have hx_recession : x ∈ recessionCone (polyhedron_le_set A b) := by
      rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone A b hP_nonempty]
      exact (mem_coneCoordinateSlice_iff A r j).mp hx |>.1
    have hy_recession : y ∈ recessionCone (polyhedron_le_set A b) := by
      rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone A b hP_nonempty]
      exact (mem_coneCoordinateSlice_iff A r j).mp hy |>.1
    have hx_ray :
        x ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
      hr_edge.isExtreme.left_mem_of_mem_openSegment
        hx_recession hy_recession (self_mem_singleton_ray_hull r) hr_open
    -- Extremality in the recession cone reduces the slice segment to the singleton point `r`.
    exact eq_of_mem_coneCoordinateSlice_and_mem_singleton_ray_hull A j hrj hx hx_ray

/-- Helper for Exercise 3.27: `n` linearly independent rows in `ℝ^n` cannot all annihilate a
vector unless that vector is zero. -/
lemma eq_zero_of_linearIndependent_rows_annihilate
    {n : ℕ}
    {rows : Fin n → Fin n → ℝ}
    {x : Fin n → ℝ}
    (hrows : LinearIndependent ℝ rows)
    (hann : ∀ i : Fin n, rows i ⬝ᵥ x = 0) :
    x = 0 := by
  by_cases hn : n = 0
  · subst hn
    ext i
    exact Fin.elim0 i
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    have hspan : Submodule.span ℝ (Set.range rows) = ⊤ := by
      -- A linearly independent family of `n` vectors in `ℝ^n` already spans the ambient space.
      exact
        hrows.span_eq_top_of_card_eq_finrank
          (by simpa using (Module.finrank_fin_fun ℝ (n := n)).symm)
    have hdot_zero :
        ∀ v ∈ Submodule.span ℝ (Set.range rows), v ⬝ᵥ x = 0 := by
      intro v hv
      -- Extend the vanishing dot-product relation from the generators to their span.
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
      · intro y hy
        rcases hy with ⟨i, rfl⟩
        exact hann i
      · simp
      · intro u w hu hw hu_zero hw_zero
        rw [add_dotProduct, hu_zero, hw_zero]
        simp
      · intro a v hv hv_zero
        rw [smul_dotProduct, hv_zero]
        simp
    ext i
    have hi_mem : Pi.single i (1 : ℝ) ∈ Submodule.span ℝ (Set.range rows) := by
      rw [hspan]
      exact Submodule.mem_top
    -- Test the vanishing functional on the `i`th coordinate vector.
    have hi_dot : (Pi.single i (1 : ℝ)) ⬝ᵥ x = 0 := hdot_zero (Pi.single i (1 : ℝ)) hi_mem
    have hi_single : (Pi.single i (1 : ℝ)) ⬝ᵥ x = x i := by
      rw [dotProduct, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    exact hi_single.symm.trans hi_dot

/-- Helper for Exercise 3.27: deleting the unique auxiliary row from an active independent slice
family leaves `n - 1` original rows of `A` that annihilate `r` and remain linearly independent. -/
lemma coordinateSliceActiveRowsDropToOriginalRows
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {r : Fin n → ℝ}
    (j : Fin n)
    (hrj : r j ≠ 0)
    (J : Fin n ↪ Fin (m + 2))
    (hJ_active :
      ∀ i : Fin n,
        (coneCoordinateSliceMatrix A j *ᵥ r) (J i) = coneCoordinateSliceRhs r j (J i))
    (hJ_linearIndependent :
      LinearIndependent ℝ (fun i : Fin n ↦ coneCoordinateSliceMatrix A j (J i))) :
    ∃ I : Fin (n - 1) ↪ Fin m,
      (∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0) ∧
        LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)) := by
  have haux_exists : ∃ kAux : Fin n, J kAux = 0 ∨ J kAux = 1 := by
    by_contra haux
    have hJ_nonaux : ∀ k : Fin n, J k ≠ 0 ∧ J k ≠ 1 := by
      intro k
      constructor
      · intro h0
        exact haux ⟨k, Or.inl h0⟩
      · intro h1
        exact haux ⟨k, Or.inr h1⟩
    let tail : Fin n → Fin m := fun k ↦
      Classical.choose
        (exists_tail_index_of_ne_auxiliary_slice_row (hJ_nonaux k).1 (hJ_nonaux k).2)
    have htail_eq : ∀ k : Fin n, J k = (tail k).succ.succ := by
      intro k
      exact
        Classical.choose_spec
          (exists_tail_index_of_ne_auxiliary_slice_row (hJ_nonaux k).1 (hJ_nonaux k).2)
    have htail_active : ∀ k : Fin n, (A *ᵥ r) (tail k) = 0 := by
      intro k
      have hk := hJ_active k
      rw [htail_eq k] at hk
      simpa [Matrix.mulVec, coneCoordinateSliceMatrix_tail_row, coneCoordinateSliceRhs_tail_row]
        using hk
    have htail_linearIndependent : LinearIndependent ℝ (fun k : Fin n ↦ A (tail k)) := by
      -- Once every chosen slice row is a tail row, the slice family is literally a family of rows of `A`.
      simpa [htail_eq, coneCoordinateSliceMatrix_tail_row] using hJ_linearIndependent
    have hr_zero : r = 0 := by
      apply eq_zero_of_linearIndependent_rows_annihilate htail_linearIndependent
      intro k
      simpa [Matrix.mulVec, dotProduct] using htail_active k
    exact hrj (by simpa [hr_zero])
  obtain ⟨kAux, hkAux⟩ := haux_exists
  have hno_two_aux :
      ∀ {a b : Fin n}, a ≠ b → J a = 0 → J b = 1 → False := by
    intro a b hab hJa hJb
    let e : Fin 2 → Fin n := ![a, b]
    have he_inj : Function.Injective e := by
      intro u v huv
      fin_cases u <;> fin_cases v
      · rfl
      · have : a = b := by simpa [e] using huv
        exact False.elim (hab this)
      · have : a = b := by simpa [e] using huv.symm
        exact False.elim (hab this)
      · rfl
    have hpair_linearIndependent :
        LinearIndependent ℝ
          (fun t : Fin 2 ↦ coneCoordinateSliceMatrix A j (J (e t))) :=
      hJ_linearIndependent.comp e he_inj
    let pairRows : Fin 2 → Fin n → ℝ :=
      ![coneCoordinateSliceMatrix A j 0, coneCoordinateSliceMatrix A j 1]
    have hpair_eq :
        (fun t : Fin 2 ↦ coneCoordinateSliceMatrix A j (J (e t))) = pairRows := by
      funext t
      fin_cases t <;> simp [pairRows, e, hJa, hJb]
    have hpair_linearIndependent' :
        LinearIndependent ℝ
          (fun t : Fin 2 ↦ pairRows t) := by
      simpa [hpair_eq] using hpair_linearIndependent
    exact not_linearIndependent_auxiliary_slice_rows A j hpair_linearIndependent'
  have hother_nonaux :
      ∀ {k : Fin n}, k ≠ kAux → J k ≠ 0 ∧ J k ≠ 1 := by
    intro k hk
    constructor
    · intro hk0
      cases hkAux with
      | inl hkAux0 =>
          exact hk (J.injective (hk0.trans hkAux0.symm))
      | inr hkAux1 =>
          exact False.elim (hno_two_aux hk hk0 hkAux1)
    · intro hk1
      cases hkAux with
      | inl hkAux0 =>
          have hkAux_ne_k : kAux ≠ k := fun h => hk h.symm
          exact False.elim (hno_two_aux hkAux_ne_k hkAux0 hk1)
      | inr hkAux1 =>
          exact hk (J.injective (hk1.trans hkAux1.symm))
  have hn_pos : 0 < n := Fin.pos_iff_nonempty.mpr ⟨kAux⟩
  have hn_cast : (n - 1) + 1 = n := by
    omega
  let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm kAux
  let skip : Fin (n - 1) → Fin n := fun i ↦ Fin.cast hn_cast (pivot.succAboveEmb i)
  have hskip_ne_aux : ∀ i : Fin (n - 1), skip i ≠ kAux := by
    intro i
    intro hskip
    have :
        pivot.succAboveEmb i = pivot := by
      apply Fin.cast_injective hn_cast
      simpa [skip, pivot] using hskip
    exact Fin.succAbove_ne pivot i this
  let tail : Fin (n - 1) → Fin m := fun i ↦
    Classical.choose
      (exists_tail_index_of_ne_auxiliary_slice_row
        ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).1
        ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).2)
  have htail_eq :
      ∀ i : Fin (n - 1), J (skip i) = (tail i).succ.succ := by
    intro i
    exact
      Classical.choose_spec
        (exists_tail_index_of_ne_auxiliary_slice_row
          ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).1
          ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).2)
  let I : Fin (n - 1) ↪ Fin m :=
    ⟨tail, by
      intro i i' hij
      apply pivot.succAboveEmb.inj'
      apply Fin.cast_injective hn_cast
      apply J.injective
      calc
        J (skip i) = (tail i).succ.succ := htail_eq i
        _ = (tail i').succ.succ := by simpa [hij]
        _ = J (skip i') := (htail_eq i').symm⟩
  refine ⟨I, ?_, ?_⟩
  · intro i
    have hi := hJ_active (skip i)
    rw [htail_eq i] at hi
    -- Tail slice equalities are exactly the original homogeneous equalities.
    simpa [I, Matrix.mulVec, coneCoordinateSliceMatrix_tail_row, coneCoordinateSliceRhs_tail_row]
      using hi
  · have hskip_linearIndependent :
        LinearIndependent ℝ
          (fun i : Fin (n - 1) ↦ coneCoordinateSliceMatrix A j (J (skip i))) := by
      exact hJ_linearIndependent.comp skip (by
        intro i i' hij
        apply pivot.succAboveEmb.inj'
        apply Fin.cast_injective hn_cast
        exact hij)
    -- After deleting the auxiliary row, the remaining slice rows are the original rows of `A`.
    simpa [I, htail_eq, coneCoordinateSliceMatrix_tail_row] using hskip_linearIndependent

/-- Helper for Exercise 3.27: after rewriting `P` as `polyhedron_le_set A b`, Theorem 3.35
produces `n - 1` active independent rows at the given extreme recession ray. -/
lemma extreme_recession_ray_exists_active_linearlyIndependent_rows
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (hP_pointed : is_pointed (polyhedron_le_set A b))
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron (polyhedron_le_set A b) r) :
    ∃ I : Fin (n - 1) ↪ Fin m,
      (∀ i : Fin (n - 1), Matrix.mulVec A r (I i) = 0) ∧
        LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)) := by
  have hr_ne_zero : r ≠ 0 := extreme_ray_ne_zero hr
  obtain ⟨j, hrj⟩ := exists_nonzero_coordinate_of_ne_zero hr_ne_zero
  have hr_extreme_slice :
      r ∈
        (polyhedron_le_set (coneCoordinateSliceMatrix A j) (coneCoordinateSliceRhs r j)).extremePoints
          ℝ :=
    coneCoordinateSliceExtremePoint A b hP_nonempty hr j hrj
  obtain ⟨J, hJ_active, hJ_linearIndependent⟩ :=
    exists_active_linearlyIndependent_rows_of_extremePoint
      (coneCoordinateSliceMatrix A j) (coneCoordinateSliceRhs r j)
      (extreme_ray_mem_coneCoordinateSlice A b hP_nonempty hr j)
      hr_extreme_slice
  -- Delete the unique auxiliary slice row and keep the remaining original rows.
  exact
    coordinateSliceActiveRowsDropToOriginalRows
      A j hrj J hJ_active hJ_linearIndependent

/-- Helper for Exercise 3.27: the selected active equalities admit an affine solution because the
chosen rows have full row rank. -/
-- TODO: replace this placeholder by the surjectivity-of-`mulVecLin` argument after the local API
-- mismatch around `finrank` is repaired.
lemma selectedRowsEqualityWitness
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i))) :
    ∃ x0 : Fin n → ℝ, ∀ i : Fin (n - 1), (A *ᵥ x0) (I i) = b (I i) := by
  let S : Submodule ℝ (Fin n → ℝ) :=
    Submodule.span ℝ (Set.range fun i : Fin (n - 1) ↦ A (I i))
  let coeffValue : (Fin (n - 1) →₀ ℝ) →ₗ[ℝ] ℝ :=
    Finsupp.lsum ℝ fun i : Fin (n - 1) ↦ LinearMap.id.smulRight (b (I i))
  let ψ : S →ₗ[ℝ] ℝ :=
    coeffValue.comp (LinearIndependent.repr hI_linearIndependent)
  obtain ⟨T, hST⟩ := S.exists_isCompl
  let φ : (Fin n → ℝ) →ₗ[ℝ] ℝ := ψ.comp (S.projectionOnto T hST)
  let x0 : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm φ
  refine ⟨x0, ?_⟩
  intro i
  have hphi : (dotProductEquiv ℝ (Fin n)) x0 = φ := by
    simp [x0]
  have hrow_mem : A (I i) ∈ S := by
    exact Submodule.subset_span ⟨i, rfl⟩
  have hproj :
      S.projectionOnto T hST (A (I i)) = ⟨A (I i), hrow_mem⟩ := by
    -- Projecting a selected row back onto its own span does not change it.
    simpa using S.projectionOnto_apply_left hST ⟨A (I i), hrow_mem⟩
  have hrepr :
      LinearIndependent.repr hI_linearIndependent ⟨A (I i), hrow_mem⟩ = Finsupp.single i 1 := by
    apply LinearIndependent.repr_eq_single
    rfl
  -- Evaluate the extended linear functional on each selected row and convert back through
  -- `dotProductEquiv`.
  calc
    (A *ᵥ x0) (I i) = A (I i) ⬝ᵥ x0 := by
      simp [Matrix.mulVec]
    _ = x0 ⬝ᵥ A (I i) := by
          rw [dotProduct_comm]
    _ = φ (A (I i)) := by
          simpa using
            congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ ↦ f (A (I i))) hphi
    _ = ψ ⟨A (I i), hrow_mem⟩ := by
          simp [φ, hproj]
    _ = coeffValue (Finsupp.single i 1) := by
          simp [ψ, hrepr]
    _ = b (I i) := by
          simp [coeffValue]

/-- Helper for Exercise 3.27: any dual-feasible multiplier for the selected-row objective can put
positive weight only on rows whose slope along `r` is zero. -/
lemma dualSupportRowsAreZeroSlope
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron (polyhedron_le_set A b) r)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    {u : Fin m → ℝ}
    (hu :
      u ∈ dual_feasible_region A (∑ i : Fin (n - 1), A (I i))) :
    ∀ j : Fin m, 0 < u j → (A *ᵥ r) j = 0 := by
  rcases (mem_dual_feasible_region_iff A (∑ i : Fin (n - 1), A (I i)) u).mp hu with
    ⟨hu_row, hu_nonneg⟩
  have hr_edge :
      IsEdgeOf (recessionCone (polyhedron_le_set A b))
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    exact (isExtremeRayOfCone_iff).1 ((isExtremeRayOfPolyhedron_iff).1 hr)
  have hr_mem_recession : r ∈ recessionCone (polyhedron_le_set A b) := by
    exact hr_edge.isExtreme.1 (self_mem_singleton_ray_hull r)
  have hr_nonpos : A *ᵥ r ≤ 0 := by
    -- Rewriting the recession cone as the homogeneous matrix system gives the rowwise slopes.
    rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone A b hP_nonempty] at hr_mem_recession
    exact (mem_matrix_polyhedral_cone A r).mp hr_mem_recession
  have hrow_sum_zero : (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ r = 0 := by
    let B : Matrix (Fin (n - 1)) (Fin n) ℝ := fun i j ↦ A (I i) j
    calc
      (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ r = ∑ i : Fin (n - 1), (A *ᵥ r) (I i) := by
        simpa [B, Matrix.mulVec] using row_sum_dotProduct_eq_selected_row_sum B Finset.univ r
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact hI_active i
  have hdual_eval_zero : u ⬝ᵥ (A *ᵥ r) = 0 := by
    -- Evaluate the dual equality `u ᵥ* A = ∑ A (I i)` on the extreme-ray direction `r`.
    calc
      u ⬝ᵥ (A *ᵥ r) = (u ᵥ* A) ⬝ᵥ r := by
        rw [Matrix.dotProduct_mulVec]
      _ = (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ r := by
        rw [hu_row]
      _ = 0 := hrow_sum_zero
  have hneg_sum_zero : ∑ j : Fin m, -(u j * (A *ᵥ r) j) = 0 := by
    -- Negating the zero sum puts every term into a nonnegative form.
    simpa [dotProduct] using congrArg Neg.neg hdual_eval_zero
  have hneg_term_zero :
      ∀ j : Fin m, -(u j * (A *ᵥ r) j) = 0 := by
    intro j
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _hk ↦
          neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hu_nonneg k) (hr_nonpos k)))).1
        hneg_sum_zero j (Finset.mem_univ j)
  intro j huj_pos
  have hprod_zero : u j * (A *ᵥ r) j = 0 := by
    exact neg_eq_zero.mp (hneg_term_zero j)
  exact (mul_eq_zero.mp hprod_zero).resolve_left (ne_of_gt huj_pos)

/-- Helper for Exercise 3.27: every zero-slope row lies in the span of the selected active
independent rows. -/
lemma zeroSlopeRow_mem_span_selectedRows
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {r : Fin n → ℝ}
    (hr_ne_zero : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    {j : Fin m}
    (hj_zero : (A *ᵥ r) j = 0) :
    A j ∈ Submodule.span ℝ (Set.range fun i : Fin (n - 1) ↦ A (I i)) := by
  let S : Submodule ℝ (Fin n → ℝ) :=
    Submodule.span ℝ (Set.range fun i : Fin (n - 1) ↦ A (I i))
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductStrongDual r).toLinearMap
  have hS_le : S ≤ LinearMap.ker L := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    -- Each selected row annihilates `r`, so the entire span sits in the orthogonal hyperplane.
    change L (A (I i)) = 0
    change dotProductStrongDual r (A (I i)) = 0
    rw [dotProductStrongDual_apply, dotProduct_comm]
    simpa [Matrix.mulVec] using hI_active i
  have hL_ne : L ≠ 0 := by
    obtain ⟨k, hk_nonzero⟩ := exists_nonzero_coordinate_of_ne_zero hr_ne_zero
    intro hL_zero
    have hk_eval : L (Pi.single k 1) = 0 := by
      simpa [hL_zero]
    have : r k = 0 := by
      simpa [L, dotProductStrongDual_apply, dotProduct, Pi.single_apply] using hk_eval
    exact hk_nonzero this
  have hS_finrank : Module.finrank ℝ S = n - 1 := by
    simpa [S] using finrank_span_eq_card (R := ℝ) (b := fun i : Fin (n - 1) ↦ A (I i))
      hI_linearIndependent
  have hker_finrank : Module.finrank ℝ (LinearMap.ker L) = n - 1 := by
    have hker_add_one :
        Module.finrank ℝ (LinearMap.ker L) + 1 = n := by
      simpa [L, Module.finrank_fintype_fun_eq_card] using
        Module.Dual.finrank_ker_add_one_of_ne_zero (f := L) hL_ne
    omega
  have hS_eq : S = LinearMap.ker L := by
    exact Submodule.eq_of_le_of_finrank_eq hS_le (hS_finrank.trans hker_finrank.symm)
  have hj_mem_ker : A j ∈ LinearMap.ker L := by
    -- The target row also annihilates `r`, so it belongs to the same hyperplane.
    change L (A j) = 0
    change dotProductStrongDual r (A j) = 0
    rw [dotProductStrongDual_apply, dotProduct_comm]
    simpa [Matrix.mulVec] using hj_zero
  change A j ∈ S
  exact hS_eq.symm ▸ hj_mem_ker

/-- Helper for Exercise 3.27: a zero-slope row is a linear combination of the selected active
independent rows. -/
lemma zeroSlopeRow_eq_selectedRowsCombination
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {r : Fin n → ℝ}
    (hr_ne_zero : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    {j : Fin m}
    (hj_zero : (A *ᵥ r) j = 0) :
    ∃ coeff : Fin (n - 1) → ℝ, A j = ∑ i : Fin (n - 1), coeff i • A (I i) := by
  have hj_mem :
      A j ∈ Submodule.span ℝ (Set.range fun i : Fin (n - 1) ↦ A (I i)) :=
    zeroSlopeRow_mem_span_selectedRows A hr_ne_zero I hI_active hI_linearIndependent hj_zero
  rw [Submodule.mem_span_range_iff_exists_fun] at hj_mem
  rcases hj_mem with ⟨coeff, hcoeff⟩
  exact ⟨coeff, hcoeff.symm⟩

/-- Helper for Exercise 3.27: on the affine slice where the selected rows are fixed at their
right-hand sides, every zero-slope row takes the same value. -/
lemma zeroSlopeRowsConstantOnSelectedEqualities
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {r x y : Fin n → ℝ}
    {b : Fin m → ℝ}
    (hr_ne_zero : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    (hx_eq : ∀ i : Fin (n - 1), (A *ᵥ x) (I i) = b (I i))
    (hy_eq : ∀ i : Fin (n - 1), (A *ᵥ y) (I i) = b (I i))
    {j : Fin m}
    (hj_zero : (A *ᵥ r) j = 0) :
    (A *ᵥ x) j = (A *ᵥ y) j := by
  obtain ⟨coeff, hrow⟩ :=
    zeroSlopeRow_eq_selectedRowsCombination A hr_ne_zero I hI_active hI_linearIndependent hj_zero
  -- Rewrite the zero-slope row through the selected basis at `x`.
  have hx_row_eval :
      (A *ᵥ x) j = ∑ i : Fin (n - 1), coeff i * b (I i) := by
    calc
      (A *ᵥ x) j = A j ⬝ᵥ x := by
        simp [Matrix.mulVec]
      _ = (∑ i : Fin (n - 1), coeff i • A (I i)) ⬝ᵥ x := by
        rw [hrow]
      _ = ∑ i : Fin (n - 1), coeff i * (A (I i) ⬝ᵥ x) := by
        rw [sum_dotProduct]
        apply Finset.sum_congr rfl
        intro i hi
        rw [smul_dotProduct]
        simp [smul_eq_mul]
      _ = ∑ i : Fin (n - 1), coeff i * b (I i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hdot : A (I i) ⬝ᵥ x = (A *ᵥ x) (I i) := by
          simp [Matrix.mulVec]
        rw [hdot, hx_eq i]
  -- The same selected-row coordinates give the same row value at `y`.
  have hy_row_eval :
      (A *ᵥ y) j = ∑ i : Fin (n - 1), coeff i * b (I i) := by
    calc
      (A *ᵥ y) j = A j ⬝ᵥ y := by
        simp [Matrix.mulVec]
      _ = (∑ i : Fin (n - 1), coeff i • A (I i)) ⬝ᵥ y := by
        rw [hrow]
      _ = ∑ i : Fin (n - 1), coeff i * (A (I i) ⬝ᵥ y) := by
        rw [sum_dotProduct]
        apply Finset.sum_congr rfl
        intro i hi
        rw [smul_dotProduct]
        simp [smul_eq_mul]
      _ = ∑ i : Fin (n - 1), coeff i * b (I i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hdot : A (I i) ⬝ᵥ y = (A *ᵥ y) (I i) := by
          simp [Matrix.mulVec]
        rw [hdot, hy_eq i]
  rw [hx_row_eval, hy_row_eval]

/-- Helper for Exercise 3.27: summing the rows indexed by `I` produces a valid inequality of the
ambient polyhedron. -/
lemma selected_rows_sum_is_valid_inequality
    {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Fin k ↪ Fin m) :
    is_valid_inequality (polyhedron_le_set A b)
      (∑ i : Fin k, A (I i))
      (∑ i : Fin k, b (I i)) := by
  intro x hx
  -- Sum the defining inequalities row by row along the chosen injection.
  calc
    (∑ i : Fin k, A (I i)) ⬝ᵥ x = ∑ j : Fin n, ((∑ i : Fin k, A (I i)) j) * x j := by
      simp [dotProduct]
    _ = ∑ j : Fin n, (∑ i : Fin k, A (I i) j) * x j := by
      simp
    _ = ∑ j : Fin n, ∑ i : Fin k, A (I i) j * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ = ∑ i : Fin k, ∑ j : Fin n, A (I i) j * x j := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin k, Matrix.mulVec A x (I i) := by
      simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ i : Fin k, b (I i) := by
      exact Finset.sum_le_sum fun i hi ↦ hx (I i)

/-- Helper for Exercise 3.27: the dual multiplier supported on the selected rows records each row
of `I` with coefficient `1`. -/
def selected_rows_dual_multiplier
    {m k : ℕ} (I : Fin k ↪ Fin m) : Fin m → ℝ :=
  fun j ↦ ∑ i : Fin k, if I i = j then 1 else 0

/-- Helper for Exercise 3.27: the selected-row dual multiplier is entrywise nonnegative. -/
lemma selected_rows_dual_multiplier_nonneg
    {m k : ℕ} (I : Fin k ↪ Fin m) :
    0 ≤ selected_rows_dual_multiplier I := by
  -- Each coordinate is a finite sum of `0`s and `1`s.
  intro j
  simp [selected_rows_dual_multiplier]

/-- Helper for Exercise 3.27: the selected-row dual multiplier reproduces the sum of the chosen
rows under left multiplication. -/
lemma selected_rows_dual_multiplier_vecMul
    {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (I : Fin k ↪ Fin m) :
    Matrix.vecMul (selected_rows_dual_multiplier I) A = ∑ i : Fin k, A (I i) := by
  -- Expand the left multiplication and collapse the indicator sum at each chosen row.
  ext j
  calc
    (Matrix.vecMul (selected_rows_dual_multiplier I) A) j
        = ∑ t : Fin m, selected_rows_dual_multiplier I t * A t j := by
            simp [Matrix.vecMul, dotProduct]
    _ = ∑ t : Fin m, (∑ i : Fin k, if I i = t then 1 else 0) * A t j := by
          simp [selected_rows_dual_multiplier]
    _ = ∑ i : Fin k, ∑ t : Fin m, (if I i = t then 1 else 0) * A t j := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
    _ = ∑ i : Fin k, A (I i) j := by
          apply Finset.sum_congr rfl
          intro i hi
          simp
    _ = (∑ i : Fin k, A (I i)) j := by
          simp

/-- Helper for Exercise 3.27: the selected-row dual multiplier evaluates on `b` as the sum of the
selected right-hand sides. -/
lemma selected_rows_dual_multiplier_dot_rhs
    {m k : ℕ}
    (b : Fin m → ℝ)
    (I : Fin k ↪ Fin m) :
    selected_rows_dual_multiplier I ⬝ᵥ b = ∑ i : Fin k, b (I i) := by
  -- The same indicator collapse works for the right-hand side vector.
  calc
    selected_rows_dual_multiplier I ⬝ᵥ b
        = ∑ t : Fin m, selected_rows_dual_multiplier I t * b t := by
            simp [dotProduct]
    _ = ∑ t : Fin m, (∑ i : Fin k, if I i = t then 1 else 0) * b t := by
          simp [selected_rows_dual_multiplier]
    _ = ∑ i : Fin k, ∑ t : Fin m, (if I i = t then 1 else 0) * b t := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
    _ = ∑ i : Fin k, b (I i) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp

/-- Helper for Exercise 3.27: the selected-row dual multiplier is dual feasible for the row-sum
objective attached to `I`. -/
lemma selected_rows_dual_multiplier_mem_dual_feasible_region
    {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (I : Fin k ↪ Fin m) :
    selected_rows_dual_multiplier I ∈
      dual_feasible_region A (∑ i : Fin k, A (I i)) := by
  -- Dual feasibility is exactly the row-sum identity together with coordinatewise nonnegativity.
  rw [mem_dual_feasible_region_iff]
  exact ⟨selected_rows_dual_multiplier_vecMul A I, selected_rows_dual_multiplier_nonneg I⟩

/-- Helper for Exercise 3.27: the selected-row-sum objective attains a maximum on
`polyhedron_le_set A b`. -/
lemma selectedRowsObjectiveOptimalFaceNonempty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (I : Fin (n - 1) ↪ Fin m) :
    ∃ β : ℝ,
      (face_set (polyhedron_le_set A b)
        (∑ i : Fin (n - 1), A (I i))
        β).Nonempty := by
  let c : Fin n → ℝ := ∑ i : Fin (n - 1), A (I i)
  have hP_primal : Set.Nonempty (primal_feasible_region A b) := by
    simpa [polyhedron_le_set, primal_feasible_region] using hP_nonempty
  have hD_nonempty : Set.Nonempty (dual_feasible_region A c) := by
    refine ⟨selected_rows_dual_multiplier I, ?_⟩
    -- The selected-row indicator multiplier is a concrete dual-feasible point for the row-sum
    -- objective.
    simpa [c] using selected_rows_dual_multiplier_mem_dual_feasible_region A I
  obtain ⟨xStar, hxStar, _hGreatest⟩ :=
    linear_programming_duality_primal_optimum_exists A b c hP_primal hD_nonempty
  refine ⟨c ⬝ᵥ xStar, xStar, ?_⟩
  rw [mem_face_set_iff]
  constructor
  · -- The primal optimizer is feasible for the ambient polyhedron.
    simpa [polyhedron_le_set, primal_feasible_region] using hxStar
  · -- Its own objective value is the exposing equality of the optimal face.
    rfl

/-- Helper for Exercise 3.27: for a nonempty optimal equality face of `polyhedron_le_set A b`,
the recession directions are exactly the ambient recession directions annihilated by the exposing
functional. -/
lemma recessionCone_face_set_eq_zero_directions
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {c : Fin n → ℝ}
    {δ : ℝ}
    (hFace_nonempty : (face_set (polyhedron_le_set A b) c δ).Nonempty)
    {s : Fin n → ℝ} :
    s ∈ recessionCone (face_set (polyhedron_le_set A b) c δ) ↔
      s ∈ recessionCone (polyhedron_le_set A b) ∧ c ⬝ᵥ s = 0 := by
  obtain ⟨x₀, hx₀_face⟩ := hFace_nonempty
  have hP_nonempty : (polyhedron_le_set A b).Nonempty :=
    ⟨x₀, (mem_face_set_iff.mp hx₀_face).1⟩
  constructor
  · intro hs
    have hs_face := (mem_recessionCone_iff.mp hs)
    have hAs_nonpos : A *ᵥ s ≤ 0 := by
      -- Test the recession property of the equality face at the fixed feasible base point `x₀`.
      change A *ᵥ s ≤ 0
      intro i
      by_contra h_not_le
      have hpos : 0 < (A *ᵥ s) i := lt_of_not_ge h_not_le
      let a : ℝ := (b i - (A *ᵥ x₀) i + 1) / (A *ᵥ s) i
      have hx₀_polyhedron : x₀ ∈ polyhedron_le_set A b := (mem_face_set_iff.mp hx₀_face).1
      have hx₀_le : (A *ᵥ x₀) i ≤ b i := hx₀_polyhedron i
      have ha_nonneg : 0 ≤ a := by
        dsimp [a]
        refine div_nonneg ?_ hpos.le
        linarith
      have hxa_face : x₀ + a • s ∈ face_set (polyhedron_le_set A b) c δ :=
        hs_face hx₀_face a ha_nonneg
      have hxa_polyhedron : x₀ + a • s ∈ polyhedron_le_set A b :=
        (mem_face_set_iff.mp hxa_face).1
      have hrow : (A *ᵥ x₀) i + a * (A *ᵥ s) i ≤ b i := by
        simpa [Matrix.mulVec_add, Matrix.mulVec_smul] using hxa_polyhedron i
      have ha_mul : a * (A *ᵥ s) i = b i - (A *ᵥ x₀) i + 1 := by
        dsimp [a]
        field_simp [hpos.ne']
      linarith
    have hs_polyhedron : s ∈ recessionCone (polyhedron_le_set A b) := by
      rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b hP_nonempty]
      exact hAs_nonpos
    have hcs_zero : c ⬝ᵥ s = 0 := by
      have hx₁_face : x₀ + s ∈ face_set (polyhedron_le_set A b) c δ := by
        simpa using hs_face hx₀_face 1 zero_le_one
      have hx₀_eq : c ⬝ᵥ x₀ = δ := (mem_face_set_iff.mp hx₀_face).2
      have hx₁_eq : c ⬝ᵥ (x₀ + s) = δ := (mem_face_set_iff.mp hx₁_face).2
      calc
        c ⬝ᵥ s = c ⬝ᵥ (x₀ + s) - c ⬝ᵥ x₀ := by
          rw [dotProduct_add]
          ring
        _ = δ - δ := by rw [hx₁_eq, hx₀_eq]
        _ = 0 := by ring
    exact ⟨hs_polyhedron, hcs_zero⟩
  · rintro ⟨hs_polyhedron, hcs_zero⟩
    rw [mem_recessionCone_iff]
    intro x hx a ha
    rw [mem_face_set_iff] at hx ⊢
    constructor
    · -- The ambient recession property preserves feasibility of the polyhedron.
      exact (mem_recessionCone_iff.mp hs_polyhedron) hx.1 a ha
    · -- The annihilation condition keeps the exposing equality fixed along `s`.
      calc
        c ⬝ᵥ (x + a • s) = c ⬝ᵥ x + a * (c ⬝ᵥ s) := by
          simp [dotProduct_add, dotProduct_smul]
        _ = δ + a * 0 := by rw [hx.2, hcs_zero]
        _ = δ := by ring

/-- Helper for Exercise 3.27: once a valid inequality is attained on a nonempty equality face,
that face is the active-constraint face supported on the positive coordinates of some nonnegative
row multiplier. -/
lemma row_sum_optimal_face_eq_active_constraint_face_of_dual_support
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    {β : ℝ}
    (hvalid : is_valid_inequality (polyhedron_le_set A b) c β)
    (hFace_nonempty : (face_set (polyhedron_le_set A b) c β).Nonempty) :
    ∃ xStar uStar β' J,
      xStar ∈ primal_feasible_region A b ∧
        uStar ∈ dual_feasible_region A c ∧
          β' = c ⬝ᵥ xStar ∧
            J = {j : Fin m | 0 < uStar j} ∧
              xStar ∈ face_set (polyhedron_le_set A b) c β' ∧
                IsExposed ℝ (polyhedron_le_set A b)
                  (face_set (polyhedron_le_set A b) c β') ∧
                face_set (polyhedron_le_set A b) c β' = active_constraint_face A b J := by
  have hFace_nonempty' : (face_set (polyhedron_le_set A b) c β).Nonempty := hFace_nonempty
  obtain ⟨xStar, hxStar_face⟩ := hFace_nonempty
  obtain ⟨uStar, hu_nonneg, hu_row, hu_beta⟩ :=
    exists_nonneg_multiplier_of_attained_valid_inequality A b c β hvalid hFace_nonempty'
  let J : Set (Fin m) := {j : Fin m | 0 < uStar j}
  have hxStar_primal : xStar ∈ primal_feasible_region A b := by
    exact (mem_face_set_iff.mp hxStar_face).1
  have huStar_dual : uStar ∈ dual_feasible_region A c := by
    rw [mem_dual_feasible_region_iff]
    exact ⟨hu_row, hu_nonneg⟩
  have hFace_exposed : IsExposed ℝ (polyhedron_le_set A b) (face_set (polyhedron_le_set A b) c β) :=
    isExposed_face_set_of_valid_inequality hvalid
  have hFace_eq :
      face_set (polyhedron_le_set A b) c β = active_constraint_face A b J := by
    ext x
    rw [mem_face_set_iff_mem_active_constraint_face_of_support hu_nonneg hu_row hu_beta]
  refine ⟨xStar, uStar, β, J, hxStar_primal, huStar_dual, ?_, rfl, hxStar_face, hFace_exposed,
    hFace_eq⟩
  exact (mem_face_set_iff.mp hxStar_face).2.symm

/-- Helper for Exercise 3.27: the equality face cut out by the sum of the selected rows at the
textbook right-hand side already lies in the face where those rows are individually active. -/
lemma optimal_face_subset_selected_rows_face
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Fin (n - 1) ↪ Fin m) :
    face_set (polyhedron_le_set A b)
      (∑ i : Fin (n - 1), A (I i))
      (∑ i : Fin (n - 1), b (I i)) ⊆
      active_constraint_face A b (Set.range I) := by
  intro x hx
  rw [mem_face_set_iff] at hx
  have hx_sum :
      ∑ i : Fin (n - 1), (A *ᵥ x) (I i) = ∑ i : Fin (n - 1), b (I i) := by
    -- Rewrite the face equality as equality of the selected row evaluations.
    let B : Matrix (Fin (n - 1)) (Fin n) ℝ := fun i j ↦ A (I i) j
    calc
      ∑ i : Fin (n - 1), (A *ᵥ x) (I i)
          = (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ x := by
              simpa [B, Matrix.mulVec] using
                (row_sum_dotProduct_eq_selected_row_sum B Finset.univ x).symm
      _ = ∑ i : Fin (n - 1), b (I i) := hx.2
  refine (mem_active_constraint_face_iff).2 ?_
  constructor
  · intro j hj
    rcases hj with ⟨i, rfl⟩
    have hslack_sum :
        ∑ t : Fin (n - 1), (b (I t) - (A *ᵥ x) (I t)) = 0 := by
      rw [Finset.sum_sub_distrib, hx_sum, sub_self]
    have hslack_zero :
        ∀ t : Fin (n - 1), b (I t) - (A *ᵥ x) (I t) = 0 := by
      intro t
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun u _hu ↦ sub_nonneg.mpr (hx.1 (I u)))).1
          hslack_sum t (Finset.mem_univ t)
    exact (sub_eq_zero.mp (hslack_zero i)).symm
  · intro j hj
    -- Outside the selected rows, feasibility in the ambient polyhedron already gives the bound.
    exact hx.1 j

/-- Helper for Exercise 3.27: any point on the selected-row equality face provides a nonempty
instance of the selected-rows active-constraint face. -/
lemma selected_rows_face_nonempty_of_row_sum_face_nonempty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Fin (n - 1) ↪ Fin m)
    (hFace_nonempty :
      (face_set (polyhedron_le_set A b)
        (∑ i : Fin (n - 1), A (I i))
        (∑ i : Fin (n - 1), b (I i))).Nonempty) :
    (active_constraint_face A b (Set.range I)).Nonempty := by
  rcases hFace_nonempty with ⟨x, hx⟩
  -- Push the existing nonempty equality face witness into the candidate selected-rows face.
  exact ⟨x, optimal_face_subset_selected_rows_face A b I hx⟩

/-- Helper for Exercise 3.27: if a recession direction makes the selected row-sum functional
vanish, then each selected row already vanishes on that direction. -/
lemma selected_rows_vanish_of_row_sum_zero
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (I : Fin (n - 1) ↪ Fin m)
    {s : Fin n → ℝ}
    (hs : s ∈ recessionCone (polyhedron_le_set A b))
    (hsum_zero : (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ s = 0) :
    ∀ i : Fin (n - 1), (A *ᵥ s) (I i) = 0 := by
  let B : Matrix (Fin (n - 1)) (Fin n) ℝ := fun i j ↦ A (I i) j
  have hs_nonpos : A *ᵥ s ≤ 0 := by
    -- Rewriting the recession cone as the homogeneous matrix system gives rowwise nonpositivity.
    rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone A b hP_nonempty] at hs
    exact (mem_matrix_polyhedral_cone A s).mp hs
  have hsum_rows :
      (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ s = ∑ i : Fin (n - 1), (A *ᵥ s) (I i) := by
    -- View the selected rows as a small matrix and apply the existing row-sum identity once.
    simpa [B, Matrix.mulVec] using row_sum_dotProduct_eq_selected_row_sum B Finset.univ s
  have hsum_terms : ∑ i : Fin (n - 1), (A *ᵥ s) (I i) = 0 := by
    simpa [hsum_rows] using hsum_zero
  have hsum_eval :
      (∑ i : Fin (n - 1), -((A *ᵥ s) (I i))) = 0 := by
    -- Negating the vanishing sum puts the terms in a nonnegative form.
    simpa using congrArg Neg.neg hsum_terms
  have hterm_zero :
      ∀ i : Fin (n - 1), -((A *ᵥ s) (I i)) = 0 := by
    intro i
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _hj ↦ neg_nonneg.mpr (hs_nonpos (I j)))).1 hsum_eval i (Finset.mem_univ i)
  intro i
  have hneg : -((A *ᵥ s) (I i)) = 0 := hterm_zero i
  linarith

/-- Helper for Exercise 3.27: the common zero set of the `n - 1` active independent rows is the
line spanned by the extreme-ray generator `r`. -/
lemma mem_span_singleton_of_selected_rows_zero
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {r s : Fin n → ℝ}
    (hr_ne_zero : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    (hs_zero : ∀ i : Fin (n - 1), (A *ᵥ s) (I i) = 0) :
    s ∈ Submodule.span ℝ ({r} : Set (Fin n → ℝ)) := by
  have hn_pos : 0 < n := by
    -- A nonzero vector cannot live in the zero-dimensional ambient space.
    by_contra hn
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    apply hr_ne_zero
    ext i
    exact Fin.elim0 i
  let B : Matrix (Fin (n - 1)) (Fin n) ℝ := fun i j ↦ A (I i) j
  have hB_rows : LinearIndependent ℝ B.row := by
    -- The selected rows of `A` are exactly the rows of the submatrix `B`.
    simpa [B, Matrix.row] using hI_linearIndependent
  have hB_rank : B.rank = n - 1 := by
    -- Full row rank records the source fact that the active rows are linearly independent.
    simpa [B] using LinearIndependent.rank_matrix hB_rows
  have hker_finrank : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 1 := by
    calc
      Module.finrank ℝ (LinearMap.ker B.mulVecLin) = n - B.rank := by
        simpa using finrank_matrix_kernel_eq_ambient_sub_rank B
      _ = n - (n - 1) := by rw [hB_rank]
      _ = 1 := by omega
  have hr_ker : r ∈ LinearMap.ker B.mulVecLin := by
    -- The extreme-ray generator is annihilated by each selected active row.
    change B *ᵥ r = 0
    ext i
    simpa [B, Matrix.mulVec] using hI_active i
  have hs_ker : s ∈ LinearMap.ker B.mulVecLin := by
    -- The candidate direction satisfies the same selected-row equalities.
    change B *ᵥ s = 0
    ext i
    simpa [B, Matrix.mulVec] using hs_zero i
  have hr_sub_ne_zero : (⟨r, hr_ker⟩ : LinearMap.ker B.mulVecLin) ≠ 0 := by
    -- Passing to the kernel subtype does not create a new zero vector.
    intro hzero
    apply hr_ne_zero
    exact congrArg Subtype.val hzero
  obtain ⟨μ, hμ⟩ :=
    exists_smul_eq_of_finrank_eq_one
      (V := LinearMap.ker B.mulVecLin) hker_finrank
      (x := ⟨r, hr_ker⟩) hr_sub_ne_zero ⟨s, hs_ker⟩
  -- Convert the one-dimensional kernel relation back to the ambient vector space.
  exact Submodule.mem_span_singleton.mpr ⟨μ, by simpa using congrArg Subtype.val hμ⟩

/-- Helper for Exercise 3.27: on recession directions, vanishing of the row-sum functional for
the selected active independent rows is equivalent to lying on the ray generated by `r`. -/
lemma extreme_ray_row_sum_zero_iff_mem_ray_hull
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (hP_pointed : is_pointed (polyhedron_le_set A b))
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron (polyhedron_le_set A b) r)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    {s : Fin n → ℝ}
    (hs : s ∈ recessionCone (polyhedron_le_set A b)) :
    ((∑ i : Fin (n - 1), A (I i)) ⬝ᵥ s = 0 ↔
      s ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
  have hr_ne_zero : r ≠ 0 := extreme_ray_ne_zero hr
  have hr_edge :
      IsEdgeOf (recessionCone (polyhedron_le_set A b))
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    exact (isExtremeRayOfCone_iff).1 ((isExtremeRayOfPolyhedron_iff).1 hr)
  have hr_mem_recession : r ∈ recessionCone (polyhedron_le_set A b) := by
    exact hr_edge.isExtreme.1 (self_mem_singleton_ray_hull r)
  constructor
  · intro hsum_zero
    have hs_zero :
        ∀ i : Fin (n - 1), (A *ᵥ s) (I i) = 0 :=
      selected_rows_vanish_of_row_sum_zero A b hP_nonempty I hs hsum_zero
    have hs_span :
        s ∈ Submodule.span ℝ ({r} : Set (Fin n → ℝ)) :=
      mem_span_singleton_of_selected_rows_zero A hr_ne_zero I hI_active hI_linearIndependent hs_zero
    rcases Submodule.mem_span_singleton.mp hs_span with ⟨μ, hs_eq⟩
    have hμ_nonneg : 0 ≤ μ := by
      by_contra hμ_neg
      have hμ_lt : μ < 0 := lt_of_not_ge hμ_neg
      have hminus_r : -r ∈ recessionCone (polyhedron_le_set A b) := by
        have hs_scaled :
            ((-μ)⁻¹ : ℝ) • s ∈ recessionCone (polyhedron_le_set A b) :=
          smul_mem_recessionCone hs (inv_nonneg.mpr (by linarith))
        have hscaled_eq : ((-μ)⁻¹ : ℝ) • s = -r := by
          have hmul : ((-μ)⁻¹ : ℝ) * μ = -1 := by
            calc
              ((-μ)⁻¹ : ℝ) * μ = (-(μ⁻¹)) * μ := by rw [inv_neg]
              _ = -(μ⁻¹ * μ) := by ring
              _ = -1 := by rw [inv_mul_cancel₀ hμ_lt.ne]
          calc
            ((-μ)⁻¹ : ℝ) • s = ((-μ)⁻¹ : ℝ) • (μ • r) := by rw [hs_eq]
            _ = (((-μ)⁻¹ : ℝ) * μ) • r := by rw [smul_smul]
            _ = (-1 : ℝ) • r := by rw [hmul]
            _ = -r := by simp
        rw [← hscaled_eq]
        exact hs_scaled
      have hr_lineality : r ∈ linealitySpace (polyhedron_le_set A b) := by
        -- A negative scalar multiple in the recession cone would make `r` a lineality direction.
        rw [linealitySpace_eq_recessionCone_inter_neg]
        refine ⟨hr_mem_recession, ?_⟩
        rw [mem_neg_recessionCone_iff]
        exact hminus_r
      have : r = 0 :=
        (is_pointed_iff_eq_zero_of_mem_linealitySpace.mp hP_pointed) r hr_lineality
      exact hr_ne_zero this
    exact mem_singleton_ray_hull_iff.mpr ⟨μ, hμ_nonneg, hs_eq.symm⟩
  · intro hs_ray
    rcases mem_singleton_ray_hull_iff.mp hs_ray with ⟨μ, hμ_nonneg, rfl⟩
    -- Every nonnegative multiple of `r` lies in the same zero-slope row-sum level set.
    calc
      (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ (μ • r)
          = μ * ((∑ i : Fin (n - 1), A (I i)) ⬝ᵥ r) := by
              calc
                (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ (μ • r)
                    = ∑ x : Fin n, (∑ c : Fin (n - 1), A (I c) x) * (μ * r x) := by
                        simp [dotProduct]
                _ = μ * ∑ x : Fin n, (∑ c : Fin (n - 1), A (I c) x) * r x := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro x hx
                      ring
                _ = μ * ((∑ i : Fin (n - 1), A (I i)) ⬝ᵥ r) := by
                      simp [dotProduct]
      _ = μ * 0 := by
            congr 1
            let B : Matrix (Fin (n - 1)) (Fin n) ℝ := fun i j ↦ A (I i) j
            calc
              (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ r
                  = ∑ i : Fin (n - 1), (A *ᵥ r) (I i) := by
                      simpa [B, Matrix.mulVec] using row_sum_dotProduct_eq_selected_row_sum B Finset.univ r
              _ = 0 := by
                    apply Finset.sum_eq_zero
                    intro i hi
                    exact hI_active i
      _ = 0 := by ring

/-- Helper for Exercise 3.27: the nonempty optimal face exposed by the selected row-sum
functional has recession cone exactly the singleton ray hull generated by `r`. -/
lemma optimal_face_recession_eq_singleton_ray_hull
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (hP_pointed : is_pointed (polyhedron_le_set A b))
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron (polyhedron_le_set A b) r)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    {β : ℝ}
    (hFace_nonempty :
      (face_set (polyhedron_le_set A b) (∑ i : Fin (n - 1), A (I i)) β).Nonempty) :
    recessionCone (face_set (polyhedron_le_set A b) (∑ i : Fin (n - 1), A (I i)) β) =
      (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  ext s
  constructor
  · intro hs_face
    have hs_zero :
        s ∈ recessionCone (polyhedron_le_set A b) ∧
          (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ s = 0 :=
      (recessionCone_face_set_eq_zero_directions A b hFace_nonempty).mp hs_face
    exact
      (extreme_ray_row_sum_zero_iff_mem_ray_hull
        A b hP_nonempty hP_pointed hr I hI_active hI_linearIndependent hs_zero.1).mp hs_zero.2
  · intro hs_ray
    have hr_edge :
        IsEdgeOf (recessionCone (polyhedron_le_set A b))
          (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
      exact (isExtremeRayOfCone_iff).1 ((isExtremeRayOfPolyhedron_iff).1 hr)
    have hr_mem_recession : r ∈ recessionCone (polyhedron_le_set A b) := by
      exact hr_edge.isExtreme.1 (self_mem_singleton_ray_hull r)
    have hs_recession : s ∈ recessionCone (polyhedron_le_set A b) := by
      rcases mem_singleton_ray_hull_iff.mp hs_ray with ⟨μ, hμ_nonneg, rfl⟩
      exact smul_mem_recessionCone hr_mem_recession hμ_nonneg
    have hs_zero :
        (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ s = 0 :=
      (extreme_ray_row_sum_zero_iff_mem_ray_hull
        A b hP_nonempty hP_pointed hr I hI_active hI_linearIndependent hs_recession).mpr hs_ray
    exact (recessionCone_face_set_eq_zero_directions A b hFace_nonempty).mpr ⟨hs_recession, hs_zero⟩

/-- Helper for Exercise 3.27: an equality face of `polyhedron_le_set A b` is itself a
polyhedron. -/
lemma face_set_is_polyhedron
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (δ : ℝ) :
    is_polyhedron (face_set (polyhedron_le_set A b) c δ) := by
  let B : Matrix (Fin (m + 2)) (Fin n) ℝ :=
    fun i j ↦ Fin.cases (c j) (fun i' ↦ Fin.cases (-c j) (fun i'' ↦ A i'' j) i') i
  let d : Fin (m + 2) → ℝ :=
    fun i ↦ Fin.cases δ (fun i' ↦ Fin.cases (-δ) b i') i
  refine ⟨m + 2, B, d, ?_⟩
  ext x
  rw [mem_face_set_iff]
  constructor
  · rintro ⟨hxP, hxEq⟩
    have hxEq_sum : ∑ j : Fin n, c j * x j = δ := by
      simpa [dotProduct] using hxEq
    -- Add the two inequalities `c ⬝ᵥ x ≤ δ` and `-c ⬝ᵥ x ≤ -δ` to the original system.
    change B *ᵥ x ≤ d
    intro i
    cases i using Fin.cases with
    | zero =>
        -- The first augmented row is exactly the exposing inequality `c ⬝ᵥ x ≤ δ`.
        simpa [B, d, Matrix.mulVec, dotProduct] using hxEq_sum.le
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            -- The second augmented row is the negated exposing inequality.
            have hneg_sum : ∑ j : Fin n, (-c j) * x j ≤ -δ := by
              have hneg_eq : ∑ j : Fin n, (-c j) * x j = -δ := by
                calc
                  ∑ j : Fin n, (-c j) * x j = ∑ j : Fin n, -(c j * x j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
                  _ = -(∑ j : Fin n, c j * x j) := by
                    rw [Finset.sum_neg_distrib]
                  _ = -δ := by rw [hxEq_sum]
              exact hneg_eq.le
            convert hneg_sum using 1
        | succ i =>
            simpa [B, d, Matrix.mulVec, dotProduct] using hxP i
  · intro hxB
    refine ⟨?_, ?_⟩
    · -- The tail rows of the augmented system are exactly the original inequalities `A *ᵥ x ≤ b`.
      intro i
      simpa [B, d, Matrix.mulVec, dotProduct] using hxB i.succ.succ
    · -- The first two added rows force the exposing functional to hold at equality.
      have hupper_sum : ∑ j : Fin n, c j * x j ≤ δ := by
        simpa [B, d, Matrix.mulVec, dotProduct] using hxB 0
      have hlower_sum : δ ≤ ∑ j : Fin n, c j * x j := by
        have hneg_sum : ∑ j : Fin n, (-c j) * x j ≤ -δ := by
          convert hxB (Fin.succ 0) using 1
        have hneg_sum' : -(∑ j : Fin n, c j * x j) ≤ -δ := by
          calc
            -(∑ j : Fin n, c j * x j) = ∑ j : Fin n, (-c j) * x j := by
              calc
                -(∑ j : Fin n, c j * x j) = ∑ j : Fin n, -(c j * x j) := by
                  rw [Finset.sum_neg_distrib]
                _ = ∑ j : Fin n, (-c j) * x j := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ ≤ -δ := hneg_sum
        linarith
      have hxEq_sum : ∑ j : Fin n, c j * x j = δ := by
        linarith
      simpa [dotProduct] using hxEq_sum

/-- Helper for Exercise 3.27: a nonempty active-constraint face is itself a polyhedron. -/
lemma active_constraint_face_is_polyhedron_of_nonempty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin m))
    (hFace_nonempty : (active_constraint_face A b I).Nonempty) :
    is_polyhedron (active_constraint_face A b I) := by
  have hFace_exposed : IsExposed ℝ (polyhedron_le_set A b) (active_constraint_face A b I) :=
    active_constraint_face_isExposed A b I
  rcases exists_eq_face_set_of_isExposed_of_nonempty hFace_exposed hFace_nonempty with
    ⟨c, δ, hvalid, hface_eq⟩
  -- Reuse the canonical equality-face owner and then rewrite back to the active face.
  simpa [hface_eq] using face_set_is_polyhedron A b c δ

/-- Helper for Exercise 3.27: the selected active-constraint face has recession cone equal to the
singleton ray generated by `r`. -/
lemma selected_rows_face_recession_eq_singleton_ray_hull
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (hP_pointed : is_pointed (polyhedron_le_set A b))
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron (polyhedron_le_set A b) r)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    (hFace_nonempty : (active_constraint_face A b (Set.range I)).Nonempty) :
    recessionCone (active_constraint_face A b (Set.range I)) =
      (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  let F : Set (Fin n → ℝ) := active_constraint_face A b (Set.range I)
  obtain ⟨x₀, hx₀⟩ := hFace_nonempty
  have hr_edge :
      IsEdgeOf (recessionCone (polyhedron_le_set A b))
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    exact (isExtremeRayOfCone_iff).1 ((isExtremeRayOfPolyhedron_iff).1 hr)
  have hr_mem_recession :
      r ∈ recessionCone (polyhedron_le_set A b) := by
    exact hr_edge.isExtreme.1 (self_mem_singleton_ray_hull r)
  ext s
  constructor
  · intro hsF
    rw [mem_recessionCone_iff] at hsF
    have hsP : s ∈ recessionCone (polyhedron_le_set A b) := by
      have hs_nonpos : A *ᵥ s ≤ 0 := by
        intro j
        by_contra h_not_le
        have hpos : 0 < (A *ᵥ s) j := lt_of_not_ge h_not_le
        let a : ℝ := (b j - (A *ᵥ x₀) j + 1) / (A *ᵥ s) j
        have hx₀P : x₀ ∈ polyhedron_le_set A b :=
          mem_polyhedron_of_mem_active_constraint_face hx₀
        have hx₀_le : (A *ᵥ x₀) j ≤ b j := hx₀P j
        have ha_nonneg : 0 ≤ a := by
          dsimp [a]
          refine div_nonneg ?_ hpos.le
          linarith
        have hxaF : x₀ + a • s ∈ F := hsF hx₀ a ha_nonneg
        have hxaP : x₀ + a • s ∈ polyhedron_le_set A b :=
          mem_polyhedron_of_mem_active_constraint_face hxaF
        have hrow : (A *ᵥ x₀) j + a * (A *ᵥ s) j ≤ b j := by
          simpa [Matrix.mulVec_add, Matrix.mulVec_smul] using hxaP j
        have ha_mul : a * (A *ᵥ s) j = b j - (A *ᵥ x₀) j + 1 := by
          dsimp [a]
          field_simp [hpos.ne']
        linarith
      rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone A b hP_nonempty]
      exact (mem_matrix_polyhedral_cone A s).2 hs_nonpos
    have hx₁ : x₀ + s ∈ F := by
      simpa [F] using hsF hx₀ 1 zero_le_one
    have hs_zero_rows : ∀ i : Fin (n - 1), (A *ᵥ s) (I i) = 0 := by
      intro i
      have hx₀_eq :
          (A *ᵥ x₀) (I i) = b (I i) :=
        (mem_active_constraint_face_iff.mp hx₀).1 (I i) ⟨i, rfl⟩
      have hx₁_eq :
          (A *ᵥ (x₀ + s)) (I i) = b (I i) :=
        (mem_active_constraint_face_iff.mp hx₁).1 (I i) ⟨i, rfl⟩
      have hrow :
          (A *ᵥ x₀) (I i) + (A *ᵥ s) (I i) = (A *ᵥ x₀) (I i) := by
        simpa [Matrix.mulVec_add] using hx₁_eq.trans hx₀_eq.symm
      linarith
    have hs_row_sum_zero :
        (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ s = 0 := by
      let B : Matrix (Fin (n - 1)) (Fin n) ℝ := fun i j ↦ A (I i) j
      calc
        (∑ i : Fin (n - 1), A (I i)) ⬝ᵥ s
            = ∑ i : Fin (n - 1), (A *ᵥ s) (I i) := by
                simpa [B, Matrix.mulVec] using row_sum_dotProduct_eq_selected_row_sum B Finset.univ s
        _ = 0 := by
              apply Finset.sum_eq_zero
              intro i hi
              exact hs_zero_rows i
    exact
      (extreme_ray_row_sum_zero_iff_mem_ray_hull
        A b hP_nonempty hP_pointed hr I hI_active hI_linearIndependent hsP).mp
        hs_row_sum_zero
  · intro hs_ray
    rw [mem_recessionCone_iff]
    intro x hx a ha
    rcases mem_singleton_ray_hull_iff.mp hs_ray with ⟨μ, hμ_nonneg, rfl⟩
    have hxP : x ∈ polyhedron_le_set A b :=
      mem_polyhedron_of_mem_active_constraint_face hx
    have hxaP :
        x + (a * μ) • r ∈ polyhedron_le_set A b :=
      (mem_recessionCone_iff.mp hr_mem_recession) hxP (a * μ) (mul_nonneg ha hμ_nonneg)
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro j hj
      rcases hj with ⟨i, rfl⟩
      have hx_eq :
          (A *ᵥ x) (I i) = b (I i) :=
        (mem_active_constraint_face_iff.mp hx).1 (I i) ⟨i, rfl⟩
      -- The selected equalities stay active because each selected row annihilates `r`.
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, smul_smul, hx_eq, hI_active i, mul_assoc]
        using hx_eq
    · intro j hj
      -- Outside the selected rows, ambient recession preserves feasibility.
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc]
        using hxaP j

/-- Helper for Exercise 3.27: the selected active-constraint face moves only along the line
spanned by `r`. -/
lemma selected_rows_face_direction_eq_span_singleton
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {r : Fin n → ℝ}
    (hr_ne_zero : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    (hFace_nonempty : (active_constraint_face A b (Set.range I)).Nonempty)
    (hFace_recession :
      recessionCone (active_constraint_face A b (Set.range I)) =
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) :
    (affineSpan ℝ (active_constraint_face A b (Set.range I))).direction = ℝ ∙ r := by
  let F : Set (Fin n → ℝ) := active_constraint_face A b (Set.range I)
  obtain ⟨x₀, hx₀⟩ := hFace_nonempty
  have hdir_le :
      (affineSpan ℝ F).direction ≤ ℝ ∙ r := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hx₀]
    rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hs_zero : ∀ i : Fin (n - 1), (A *ᵥ (x - x₀)) (I i) = 0 := by
      intro i
      have hx_eq :
          (A *ᵥ x) (I i) = b (I i) :=
        (mem_active_constraint_face_iff.mp hx).1 (I i) ⟨i, rfl⟩
      have hx₀_eq :
          (A *ᵥ x₀) (I i) = b (I i) :=
        (mem_active_constraint_face_iff.mp hx₀).1 (I i) ⟨i, rfl⟩
      rw [Matrix.mulVec_sub, Pi.sub_apply, hx_eq, hx₀_eq]
      ring
    -- Every displacement inside the selected face satisfies the same active equalities.
    exact mem_span_singleton_of_selected_rows_zero A hr_ne_zero I hI_active hI_linearIndependent hs_zero
  have hr_recF : r ∈ recessionCone F := by
    simpa [F, hFace_recession] using self_mem_singleton_ray_hull r
  have hr_dir : r ∈ (affineSpan ℝ F).direction := by
    have hx₁ : x₀ + r ∈ F := by
      simpa [F] using (mem_recessionCone_iff.mp hr_recF) hx₀ 1 zero_le_one
    -- A recession step from `x₀` yields a concrete direction vector of the affine span.
    simpa using
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx₁) (mem_affineSpan ℝ hx₀)
  have hspan_le : ℝ ∙ r ≤ (affineSpan ℝ F).direction :=
    (Submodule.span_singleton_le_iff_mem r ((affineSpan ℝ F).direction)).2 hr_dir
  exact le_antisymm hdir_le hspan_le

/-- Helper for Exercise 3.27: the selected active-constraint face is one-dimensional. -/
lemma selected_rows_face_finrank_direction_eq_one
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {r : Fin n → ℝ}
    (hr_ne_zero : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    (hFace_nonempty : (active_constraint_face A b (Set.range I)).Nonempty)
    (hFace_recession :
      recessionCone (active_constraint_face A b (Set.range I)) =
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) :
    Module.finrank ℝ (affineSpan ℝ (active_constraint_face A b (Set.range I))).direction = 1 := by
  have hdir_eq :
      (affineSpan ℝ (active_constraint_face A b (Set.range I))).direction = ℝ ∙ r :=
    selected_rows_face_direction_eq_span_singleton
      A b hr_ne_zero I hI_active hI_linearIndependent hFace_nonempty hFace_recession
  rw [hdir_eq]
  simpa using finrank_span_singleton hr_ne_zero

/-- Helper for Exercise 3.27: a set whose recession cone is a nonzero singleton ray is pointed. -/
lemma pointed_of_singleton_ray_recession
    {n : ℕ} {Q : Set (Fin n → ℝ)} {r : Fin n → ℝ}
    (hr_ne_zero : r ≠ 0)
    (hQ_recession :
      recessionCone Q = (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) :
    is_pointed Q := by
  -- A lineality direction lies in both the ray and its negative, so nonzero `r` forces it to be `0`.
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro d hd
  rw [linealitySpace_eq_recessionCone_inter_neg] at hd
  rcases hd with ⟨hd_rec, hd_neg⟩
  rcases mem_singleton_ray_hull_iff.mp (by simpa [hQ_recession] using hd_rec) with ⟨μ, hμ, hd_eq⟩
  have hneg_rec : -d ∈ recessionCone Q := by
    rw [mem_neg_recessionCone_iff] at hd_neg
    exact hd_neg
  rcases mem_singleton_ray_hull_iff.mp (by simpa [hQ_recession] using hneg_rec) with
    ⟨ν, hν, hneg_eq⟩
  have hsum_zero : (μ + ν) • r = 0 := by
    calc
      (μ + ν) • r = μ • r + ν • r := by rw [add_smul]
      _ = d + (-d) := by rw [← hd_eq, ← hneg_eq]
      _ = 0 := by abel
  have hμν_zero : μ + ν = 0 := by
    rcases smul_eq_zero.mp hsum_zero with hμν_zero | hr_zero
    · exact hμν_zero
    · exact False.elim (hr_ne_zero hr_zero)
  have hμ_zero : μ = 0 := by linarith
  calc
    d = μ • r := hd_eq
    _ = 0 := by simp [hμ_zero]

/-- Helper for Exercise 3.27: an edge of an exposed face is already an edge of the ambient
polyhedron. -/
lemma edge_of_exposed_face_is_edge_of_polyhedron
    {n : ℕ} {P F G : Set (Fin n → ℝ)}
    (hF_exposed : IsExposed ℝ P F)
    (hG_edge : IsEdgeOf F G) :
    IsEdgeOf P G := by
  refine ⟨hG_edge.convex, ?_, hG_edge.finrank_direction_eq_one⟩
  -- Extremality composes along the exposed-face inclusion `G ⊆ F ⊆ P`.
  exact hF_exposed.isExtreme.trans hG_edge.isExtreme

/-- Helper for Exercise 3.27: if the recession cone is the singleton ray generated by a nonzero
vector, then its recession-cone dimension is exactly `1`. -/
lemma recessionConeDim_eq_one_of_singleton_ray_hull
    {n : ℕ} {Q : Set (Fin n → ℝ)} {r : Fin n → ℝ}
    (hr_ne_zero : r ≠ 0)
    (hQ_recession :
      recessionCone Q = (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) :
    recessionConeDim Q = 1 := by
  -- Rewrite the recession cone to the source ray and identify its span with `ℝ ∙ r`.
  rw [recessionConeDim, hQ_recession]
  have hspan :
      Submodule.span ℝ
          ((PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) =
        ℝ ∙ r := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      rcases mem_singleton_ray_hull_iff.mp hx with ⟨μ, _hμ, rfl⟩
      exact Submodule.mem_span_singleton.mpr ⟨μ, rfl⟩
    · exact
        (Submodule.span_singleton_le_iff_mem r
          (Submodule.span ℝ
            ((PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) : Set
              (Fin n → ℝ)))).mpr <|
          Submodule.subset_span (self_mem_singleton_ray_hull r)
  rw [hspan]
  simpa using finrank_span_singleton hr_ne_zero

/-- Helper for Exercise 3.27: a convex set with affine-span direction `ℝ ∙ r`, recession cone
`cone(r)`, and an extreme point `xbar` is exactly the translated ray through `xbar`. -/
lemma face_eq_singleton_add_ray_hull_of_extreme_point
    {n : ℕ} {F : Set (Fin n → ℝ)} {r xbar : Fin n → ℝ}
    (hF_convex : Convex ℝ F)
    (hxbar : xbar ∈ F.extremePoints ℝ)
    (hr_ne_zero : r ≠ 0)
    (hF_recession :
      recessionCone F = (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
    (hF_direction : (affineSpan ℝ F).direction = ℝ ∙ r) :
    F = {xbar} + (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  have hxbar_mem : xbar ∈ F := extremePoints_subset hxbar
  ext x
  constructor
  · intro hx
    have hx_dir : x - xbar ∈ (affineSpan ℝ F).direction := by
      simpa using
        AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hxbar_mem)
    rcases Submodule.mem_span_singleton.mp (by simpa [hF_direction] using hx_dir) with ⟨μ, hμ⟩
    have hx_eq : x = xbar + μ • r := by
      calc
        x = xbar + (x - xbar) := by abel
        _ = xbar + μ • r := by rw [hμ]
    have hμ_nonneg : 0 ≤ μ := by
      by_contra hμ_neg
      have hμ_lt : μ < 0 := lt_of_not_ge hμ_neg
      let z : Fin n → ℝ := xbar + (-μ) • r
      have hz_mem : z ∈ F := by
        have hr_rec : r ∈ recessionCone F := by
          simpa [hF_recession] using self_mem_singleton_ray_hull r
        -- Moving forward from the extreme point stays inside `F`.
        exact (mem_recessionCone_iff.mp hr_rec) hxbar_mem (-μ) (by linarith)
      have hx_ne : x ≠ xbar := by
        intro hxx
        have hμr_zero : μ • r = 0 := by
          simpa [hxx] using hμ
        rcases smul_eq_zero.mp hμr_zero with hμ_zero | hr_zero
        · linarith
        · exact False.elim (hr_ne_zero hr_zero)
      have hz_ne : z ≠ xbar := by
        intro hzx
        have hμr_zero : (-μ) • r = 0 := by
          simpa [z] using congrArg (fun y ↦ y - xbar) hzx
        rcases smul_eq_zero.mp hμr_zero with hμ_zero | hr_zero
        · linarith
        · exact False.elim (hr_ne_zero hr_zero)
      have hmid : midpoint ℝ x z = xbar := by
        -- The negative coefficient makes `xbar` the midpoint of `x` and the forward translate `z`.
        rw [hx_eq]
        dsimp [z]
        simpa [sub_eq_add_neg] using midpoint_add_sub ℝ xbar (μ • r)
      have hseg : xbar ∈ segment ℝ x z := by
        rw [← hmid]
        exact midpoint_mem_segment x z
      have hcontra :=
        (mem_extremePoints_iff_forall_segment.mp hxbar).2 x hx z hz_mem hseg
      rcases hcontra with hxx | hzx
      · exact hx_ne hxx
      · exact hz_ne hzx
    -- Once the coefficient is nonnegative, `x` lies on the translated singleton ray.
    refine Set.mem_add.mpr ?_
    refine ⟨xbar, by simp, μ • r, ?_, by simpa [hx_eq]⟩
    exact mem_singleton_ray_hull_iff.mpr ⟨μ, hμ_nonneg, rfl⟩
  · intro hx
    rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, rfl⟩
    rcases Set.mem_singleton_iff.mp hy with rfl
    have hz_rec : z ∈ recessionCone F := by
      simpa [hF_recession] using hz
    -- Any point of the translated ray is obtained by a recession step from `xbar`.
    simpa using (mem_recessionCone_iff.mp hz_rec) hxbar_mem 1 zero_le_one

/-- Helper for Exercise 3.27: a one-dimensional submodule containing a nonzero vector is exactly
the span of that vector. -/
lemma submodule_eq_span_singleton_of_finrank_eq_one
    {n : ℕ}
    {D : Submodule ℝ (Fin n → ℝ)}
    {r : Fin n → ℝ}
    (hrD : r ∈ D)
    (hr_ne_zero : r ≠ 0)
    (hfinrank : Module.finrank ℝ D = 1) :
    D = ℝ ∙ r := by
  have hle : ℝ ∙ r ≤ D :=
    (Submodule.span_singleton_le_iff_mem r D).2 hrD
  -- Compare the one-dimensional span of `r` with the target submodule by finrank.
  symm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [hfinrank]
  simpa using finrank_span_singleton hr_ne_zero

/-- Helper for Exercise 3.27: the selected-row objective provides one nonempty exposed face whose
recession cone is exactly the ray generated by `r`; finite-face theory then gives an
inclusion-minimal such face. -/
lemma existsMinimalExposedFaceWithRayRecession
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (hP_pointed : is_pointed (polyhedron_le_set A b))
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron (polyhedron_le_set A b) r)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i))) :
    ∃ F : Set (Fin n → ℝ),
      F.Nonempty ∧
        IsExposed ℝ (polyhedron_le_set A b) F ∧
          recessionCone F =
            (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) ∧
            Minimal
              (fun G : Set (Fin n → ℝ) ↦
                G.Nonempty ∧
                  IsExposed ℝ (polyhedron_le_set A b) G ∧
                    recessionCone G =
                      (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
              F := by
  classical
  have hPolyhedron : is_polyhedron (polyhedron_le_set A b) := ⟨m, A, b, rfl⟩
  let c : Fin n → ℝ := ∑ i : Fin (n - 1), A (I i)
  have hP_primal : Set.Nonempty (primal_feasible_region A b) := by
    simpa [primal_feasible_region] using hP_nonempty
  have hD_nonempty : Set.Nonempty (dual_feasible_region A c) := by
    refine ⟨selected_rows_dual_multiplier I, ?_⟩
    simpa [c] using selected_rows_dual_multiplier_mem_dual_feasible_region A I
  obtain ⟨xStar, hxStar, hGreatest⟩ :=
    linear_programming_duality_primal_optimum_exists A b c hP_primal hD_nonempty
  let β : ℝ := c ⬝ᵥ xStar
  let F0 : Set (Fin n → ℝ) :=
    face_set (polyhedron_le_set A b) c β
  have hF0_nonempty : F0.Nonempty := by
    refine ⟨xStar, ?_⟩
    rw [mem_face_set_iff]
    exact ⟨hxStar, rfl⟩
  have hF0_valid : is_valid_inequality (polyhedron_le_set A b) c β := by
    intro x hx
    exact hGreatest.2 ⟨x, hx, rfl⟩
  have hF0_exposed : IsExposed ℝ (polyhedron_le_set A b) F0 := by
    -- The initial face is exposed by the selected-row valid inequality.
    simpa [F0] using isExposed_face_set_of_valid_inequality hF0_valid
  have hF0_recession :
      recessionCone F0 =
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    -- The stable optimal-face API already identifies its recession cone with the target ray.
    simpa [F0] using
      optimal_face_recession_eq_singleton_ray_hull
        A b hP_nonempty hP_pointed hr I hI_active hI_linearIndependent hF0_nonempty
  let S : Set (Set (Fin n → ℝ)) :=
    {G : Set (Fin n → ℝ) |
      G.Nonempty ∧
        IsExposed ℝ (polyhedron_le_set A b) G ∧
          recessionCone G =
            (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ))}
  have hS_finite : S.Finite := by
    -- Only finitely many exposed faces of a polyhedron exist.
    exact (polyhedron_finite_faces hPolyhedron).subset fun G hG ↦ hG.2.1
  have hF0_mem : F0 ∈ S := ⟨hF0_nonempty, hF0_exposed, hF0_recession⟩
  obtain ⟨F, _, hF_min_raw⟩ := Set.Finite.exists_le_minimal hS_finite hF0_mem
  have hF_min :
      Minimal
        (fun G : Set (Fin n → ℝ) ↦
          G.Nonempty ∧
            IsExposed ℝ (polyhedron_le_set A b) G ∧
              recessionCone G =
                (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
        F := by
    simpa [S] using hF_min_raw
  exact ⟨F, hF_min.prop.1, hF_min.prop.2.1, hF_min.prop.2.2, hF_min⟩

/-- Helper for Exercise 3.27: if a nonempty exposed face with recession cone `cone(r)` still has
direction dimension greater than `1`, then optimizing a functional that vanishes on the recession
cone produces a proper exposed subface with the same recession cone. -/
lemma existsProperSubfaceWithSameRayRecessionOfDirectionGtOne
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {r : Fin n → ℝ}
    (hr_ne_zero : r ≠ 0)
    {F : Set (Fin n → ℝ)}
    (hF_nonempty : F.Nonempty)
    (hF_exposed : IsExposed ℝ (polyhedron_le_set A b) F)
    (hF_recession :
      recessionCone F =
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
    (hdim_gt_one : 1 < Module.finrank ℝ (affineSpan ℝ F).direction) :
    ∃ G : Set (Fin n → ℝ),
      G.Nonempty ∧
        IsExposed ℝ (polyhedron_le_set A b) G ∧
          G ⊂ F ∧
            recessionCone G =
              (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  classical
  have hPolyhedron : is_polyhedron (polyhedron_le_set A b) := ⟨m, A, b, rfl⟩
  rcases exists_eq_face_set_of_isExposed_of_nonempty hF_exposed hF_nonempty with
    ⟨c₀, δ₀, _hvalid, hF_eq_face⟩
  have hF_polyhedron : is_polyhedron F := by
    -- Reuse the canonical equality-face owner to represent `F` as a polyhedron.
    simpa [hF_eq_face] using face_set_is_polyhedron A b c₀ δ₀
  rcases is_polyhedron_iff.mp hF_polyhedron with ⟨k, B, d, hF_eq_polyhedron⟩
  have hF_nonempty' : (polyhedron_le_set B d).Nonempty := by
    simpa [hF_eq_polyhedron] using hF_nonempty
  have hF_recession' :
      recessionCone (polyhedron_le_set B d) =
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    simpa [hF_eq_polyhedron] using hF_recession
  have hDirection_eq :
      (affineSpan ℝ (polyhedron_le_set B d)).direction =
        (affineSpan ℝ F).direction := by
    simpa [hF_eq_polyhedron]
  have hdim_gt_one' :
      1 < Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set B d)).direction := by
    rw [hDirection_eq]
    exact hdim_gt_one
  have hdim_gap :
      polyhedronDim (polyhedron_le_set B d) >
        recessionConeDim (polyhedron_le_set B d) := by
    -- The target face has larger affine-span dimension than its one-dimensional recession cone.
    rw [polyhedronDim, recessionConeDim_eq_one_of_singleton_ray_hull hr_ne_zero hF_recession']
    exact hdim_gt_one'
  obtain ⟨e, he_recession, he_nonconstant⟩ :=
    exists_nonconstant_functional_vanishing_on_recession_cone B d hdim_gap
  have hHom_nonempty : Set.Nonempty (primal_feasible_region B (0 : Fin k → ℝ)) := by
    refine ⟨0, ?_⟩
    simp [primal_feasible_region]
  have hHom_valid : is_valid_inequality (polyhedron_le_set B (0 : Fin k → ℝ)) e 0 := by
    intro s hs
    have hs_recession : s ∈ recessionCone (polyhedron_le_set B d) := by
      rw [polyhedron_recessionCone_eq_homogeneous_solution_set B d hF_nonempty']
      exact hs
    have hs_zero : e ⬝ᵥ s = 0 := he_recession s hs_recession
    simpa [hs_zero]
  obtain ⟨u, hu_nonneg, hu_row, _hu_eval⟩ :=
    (valid_inequality_iff_exists_nonneg_row_multiplier
      B (0 : Fin k → ℝ) e 0
      (by
        refine ⟨0, ?_⟩
        simp [polyhedron_le_set])).mp hHom_valid
  have hDual_nonempty : Set.Nonempty (dual_feasible_region B e) := by
    refine ⟨u, ?_⟩
    rw [mem_dual_feasible_region_iff]
    exact ⟨hu_row, hu_nonneg⟩
  obtain ⟨xStar, hxStar, hGreatest⟩ :=
    linear_programming_duality_primal_optimum_exists
      B d e
      (by simpa [primal_feasible_region] using hF_nonempty')
      hDual_nonempty
  let β : ℝ := e ⬝ᵥ xStar
  let G : Set (Fin n → ℝ) := face_set (polyhedron_le_set B d) e β
  have hG_nonempty : G.Nonempty := by
    refine ⟨xStar, ?_⟩
    rw [mem_face_set_iff]
    exact ⟨hxStar, rfl⟩
  have hG_valid : is_valid_inequality (polyhedron_le_set B d) e β := by
    intro x hx
    exact hGreatest.2 ⟨x, hx, rfl⟩
  have hG_exposed_local : IsExposed ℝ (polyhedron_le_set B d) G := by
    -- The optimizer set of `e` on `F` is exposed in `F`.
    exact isExposed_face_set_of_valid_inequality hG_valid
  have hG_subset_local : G ⊆ polyhedron_le_set B d := by
    intro x hx
    exact (mem_face_set_iff.mp hx).1
  have hNotConstAtβ : ¬ ∀ x ∈ polyhedron_le_set B d, e ⬝ᵥ x = β := by
    intro hconst
    exact he_nonconstant ⟨β, hconst⟩
  have hNotAllAtβ : ∃ y ∈ polyhedron_le_set B d, e ⬝ᵥ y ≠ β := by
    by_contra hno
    push Not at hno
    exact hNotConstAtβ hno
  rcases hNotAllAtβ with ⟨y, hy_mem, hy_ne⟩
  have hy_le : e ⬝ᵥ y ≤ β := hGreatest.2 ⟨y, hy_mem, rfl⟩
  have hy_not_mem : y ∉ G := by
    intro hyG
    exact hy_ne (mem_face_set_iff.mp hyG).2
  have hG_ssubset_local : G ⊂ polyhedron_le_set B d := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨hG_subset_local, ?_⟩
    intro hEq
    apply hy_not_mem
    simpa [G, hEq] using hy_mem
  have hG_exposed : IsExposed ℝ (polyhedron_le_set A b) G := by
    -- A face of the face `F` is a face of the ambient polyhedron.
    have hG_exposed_in_F : IsExposed ℝ F G := by
      simpa [hF_eq_polyhedron] using hG_exposed_local
    exact
      (isExposed_iff_isExposed_of_subset
        (P := polyhedron_le_set A b) (F := F) (G := G) hPolyhedron hF_exposed).mp
        hG_exposed_in_F |>.1
  have hG_ssubset : G ⊂ F := by
    simpa [hF_eq_polyhedron] using hG_ssubset_local
  have hG_recession :
      recessionCone G =
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    have hG_recession_local :
        recessionCone G = recessionCone (polyhedron_le_set B d) := by
      ext s
      rw [recessionCone_face_set_eq_zero_directions B d hG_nonempty]
      constructor
      · intro hs
        exact hs.1
      · intro hs
        exact ⟨hs, he_recession s hs⟩
    calc
      recessionCone G = recessionCone (polyhedron_le_set B d) := hG_recession_local
      _ = (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := hF_recession'
  exact ⟨G, hG_nonempty, hG_exposed, hG_ssubset, hG_recession⟩

/-- Helper for Exercise 3.27: an inclusion-minimal nonempty exposed face whose recession cone is
`cone(r)` must have affine direction exactly `ℝ ∙ r`. -/
lemma minimalRayFace_direction_eq_span_singleton
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {r : Fin n → ℝ}
    (hr_ne_zero : r ≠ 0)
    {F : Set (Fin n → ℝ)}
    (hF_nonempty : F.Nonempty)
    (hF_exposed : IsExposed ℝ (polyhedron_le_set A b) F)
    (hF_recession :
      recessionCone F =
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
    (hF_minimal :
      Minimal
        (fun G : Set (Fin n → ℝ) ↦
          G.Nonempty ∧
            IsExposed ℝ (polyhedron_le_set A b) G ∧
              recessionCone G =
                (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
        F) :
    (affineSpan ℝ F).direction = ℝ ∙ r := by
  have hF_nonempty' : F.Nonempty := hF_nonempty
  obtain ⟨x₀, hx₀⟩ := hF_nonempty
  have hr_recF : r ∈ recessionCone F := by
    simpa [hF_recession] using self_mem_singleton_ray_hull r
  have hx₁ : x₀ + r ∈ F := by
    -- A recession step from any face point stays in the face.
    simpa using (mem_recessionCone_iff.mp hr_recF) hx₀ 1 zero_le_one
  have hr_dir : r ∈ (affineSpan ℝ F).direction := by
    -- The recession generator is therefore a concrete direction vector of the affine span.
    simpa using
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx₁) (mem_affineSpan ℝ hx₀)
  have hfinrank_le_one :
      Module.finrank ℝ (affineSpan ℝ F).direction ≤ 1 := by
    by_contra hnot_le
    have hdim_gt_one : 1 < Module.finrank ℝ (affineSpan ℝ F).direction := lt_of_not_ge hnot_le
    rcases
        existsProperSubfaceWithSameRayRecessionOfDirectionGtOne
          A b hr_ne_zero hF_nonempty' hF_exposed hF_recession hdim_gt_one with
      ⟨G, hG_nonempty, hG_exposed, hG_ssubset, hG_recession⟩
    have hG_eq : G = F := Minimal.eq_of_subset hF_minimal
      ⟨hG_nonempty, hG_exposed, hG_recession⟩
      hG_ssubset.subset
    exact hG_ssubset.ne hG_eq
  have hspan_le : ℝ ∙ r ≤ (affineSpan ℝ F).direction :=
    (Submodule.span_singleton_le_iff_mem r _).2 hr_dir
  have hfinrank_ge_one :
      1 ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by
    simpa [finrank_span_singleton hr_ne_zero] using Submodule.finrank_mono hspan_le
  have hfinrank_eq_one :
      Module.finrank ℝ (affineSpan ℝ F).direction = 1 :=
    le_antisymm hfinrank_le_one hfinrank_ge_one
  -- The minimal face is one-dimensional, so the nonzero recession generator spans its direction.
  exact submodule_eq_span_singleton_of_finrank_eq_one hr_dir hr_ne_zero hfinrank_eq_one

/-- Exercise 3.27. If `P` is a nonempty pointed polyhedron and `r` generates an extreme ray of
`P`, then some vertex `x̄` of `P` determines an edge of `P` whose carrier is the translated ray
`x̄ + cone(r)`. The source-facing owner layer is the chapter API
`is_polyhedron`/`is_pointed`/`IsExtremeRayOfPolyhedron`/`IsEdgeOf`; the explicit translated-ray
set is the bridge/view identified by `translated_ray_eq_singleton_add_ray_hull`. -/
theorem pointed_polyhedron_extreme_ray_has_incident_edge
    {n : ℕ} {P : Set (Fin n → ℝ)} {r : Fin n → ℝ}
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty)
    (hP_pointed : is_pointed P)
    (hr : IsExtremeRayOfPolyhedron P r) :
    ∃ xbar : Fin n → ℝ,
      xbar ∈ P.extremePoints ℝ ∧
        IsEdgeOf P
          ({xbar} + (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
  rcases hP_polyhedron with ⟨m, A, b, rfl⟩
  -- Route correction: an arbitrary vertex need not be incident to the chosen extreme ray.
  -- The stable verified prefix is that the given generator is a nonzero recession direction.
  have hr_ne_zero : r ≠ 0 := extreme_ray_ne_zero hr
  have hr_edge :
      IsEdgeOf (recessionCone (polyhedron_le_set A b))
        (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    exact (isExtremeRayOfCone_iff).1 ((isExtremeRayOfPolyhedron_iff).1 hr)
  have hr_mem : r ∈ recessionCone (polyhedron_le_set A b) := by
    exact hr_edge.isExtreme.1 (self_mem_singleton_ray_hull r)
  obtain ⟨I, hI_active, hI_linearIndependent⟩ :=
    extreme_recession_ray_exists_active_linearlyIndependent_rows A b hP_nonempty hP_pointed hr
  obtain ⟨F, hF_nonempty, hF_exposed, hF_recession, hF_minimal⟩ :=
    existsMinimalExposedFaceWithRayRecession
      A b hP_nonempty hP_pointed hr I hI_active hI_linearIndependent
  have hF_polyhedron : is_polyhedron F := by
    rcases exists_eq_face_set_of_isExposed_of_nonempty hF_exposed hF_nonempty with
      ⟨c, δ, _hvalid, hF_eq_face⟩
    -- The minimal exposed face is still an equality face of the ambient polyhedron.
    simpa [hF_eq_face] using face_set_is_polyhedron A b c δ
  have hF_pointed : is_pointed F :=
    pointed_of_singleton_ray_recession hr_ne_zero hF_recession
  have hF_direction :
      (affineSpan ℝ F).direction = ℝ ∙ r :=
    minimalRayFace_direction_eq_span_singleton
      A b hr_ne_zero hF_nonempty hF_exposed hF_recession hF_minimal
  have hF_finrank :
      Module.finrank ℝ (affineSpan ℝ F).direction = 1 := by
    rw [hF_direction]
    simpa using finrank_span_singleton hr_ne_zero
  obtain ⟨xbar, hxbar_face⟩ :=
    pointed_polyhedron_extremePoints_nonempty hF_polyhedron hF_nonempty hF_pointed
  have hF_eq :
      F = {xbar} + (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    -- Classify the one-dimensional selected face as the translated ray through its vertex.
    have hF_convex : Convex ℝ F :=
      hF_exposed.convex (polyhedron_le_set_convex A b)
    exact face_eq_singleton_add_ray_hull_of_extreme_point
      hF_convex hxbar_face hr_ne_zero hF_recession hF_direction
  have hxbar : xbar ∈ (polyhedron_le_set A b).extremePoints ℝ := by
    -- Extreme points of the selected exposed face remain extreme in the ambient polyhedron.
    exact hF_exposed.isExtreme.extremePoints_subset_extremePoints hxbar_face
  have hEdge :
      IsEdgeOf (polyhedron_le_set A b)
        ({xbar} + (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) :=
    -- Package the minimal ray-preserving face as an edge and then rewrite its carrier.
    by
      have hEdgeF : IsEdgeOf F F := by
        refine ⟨?_, IsExtreme.refl (𝕜 := ℝ) F, hF_finrank⟩
        exact hF_exposed.convex (polyhedron_le_set_convex A b)
      have hEdgeRay :
          IsEdgeOf F
            ({xbar} + (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
        simpa [hF_eq] using hEdgeF
      exact edge_of_exposed_face_is_edge_of_polyhedron hF_exposed hEdgeRay
  exact ⟨xbar, hxbar, hEdge⟩
