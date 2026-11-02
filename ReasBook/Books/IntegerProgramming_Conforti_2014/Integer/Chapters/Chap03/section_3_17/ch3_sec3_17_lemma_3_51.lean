import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_definition_3_5_1_extra_1

open scoped BigOperators Matrix

-- This file reuses the Chapter 3 owners `matrix_cone`, `matrix_polyhedral_cone`, and `mw_pair`.

/-- Helper for Lemma 3.51: file-local alias for the homogeneous inequality cone cut out by `A`. -/
private abbrev matrixPolyhedralCone
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | A *ᵥ x ≤ 0}

/-- Helper for Lemma 3.51: membership in the local polyhedral-cone alias is exactly the rowwise
homogeneous inequality system. -/
private theorem memMatrixPolyhedralCone
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ∈ matrixPolyhedralCone A ↔ A *ᵥ x ≤ 0 := by
  rfl

local notation "matrix_polyhedral_cone" => matrixPolyhedralCone

/-- Helper for Lemma 3.51: file-local alias for the MW-pair predicate using the stable Chapter 3
owners `matrix_polyhedral_cone` and `matrix_cone`. -/
private def mwPair
    {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (R : Matrix (Fin n) (Fin k) ℝ) :
    Prop :=
  matrix_polyhedral_cone A = (matrix_cone R : Set (Fin n → ℝ))

local notation "mw_pair" => mwPair

/-- Append the row `a` to the matrix `A`. -/
def append_row
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin (m + 1)) (Fin n) ℝ :=
  fun i j ↦
    if h : i.1 < m then
      A ⟨i.1, h⟩ j
    else
      a j

/-- On the original rows, `append_row` agrees with `A`. -/
theorem append_row_apply_castSucc
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    append_row A a (Fin.castSucc i) j = A i j := by
  -- The appended matrix agrees with `A` on the original rows.
  simp [append_row]

/-- On the new last row, `append_row` agrees with `a`. -/
theorem append_row_apply_last
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin n → ℝ)
    (j : Fin n) :
    append_row A a (Fin.last m) j = a j := by
  -- The final row is exactly the appended row.
  simp [append_row]

/-- The pairwise ray added by the double description construction from a negative column `rj`
and a positive column `rk` with respect to the new row `a`. -/
def double_description_ray
    {n : ℕ} (a rj rk : Fin n → ℝ) : Fin n → ℝ :=
  fun t ↦ (a ⬝ᵥ rk) * rj t - (a ⬝ᵥ rj) * rk t

/-- Coordinate formula for the pairwise double-description ray. -/
theorem double_description_ray_apply
    {n : ℕ} (a rj rk : Fin n → ℝ) (t : Fin n) :
    double_description_ray a rj rk t = (a ⬝ᵥ rk) * rj t - (a ⬝ᵥ rj) * rk t := by
  -- This is the defining coordinate formula.
  rfl

/-- `R'` is obtained from `R` by one double-description step with respect to the appended row
`a` when every new column satisfies the enlarged system, every old column cut out by
`a ⬝ᵥ r ≤ 0` is retained, and every negative-positive pair contributes its standard new ray. -/
def is_double_description_step
    {m n k k' : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin k) ℝ)
    (a : Fin n → ℝ)
    (R' : Matrix (Fin n) (Fin k') ℝ) : Prop :=
  (∀ j' : Fin k', append_row A a *ᵥ (fun i : Fin n ↦ R' i j') ≤ 0) ∧
    (∀ j : Fin k,
      a ⬝ᵥ (fun i : Fin n ↦ R i j) ≤ 0 →
        ∃ j' : Fin k', ∀ i : Fin n, R' i j' = R i j) ∧
    ∀ j_neg j_pos : Fin k,
      a ⬝ᵥ (fun i : Fin n ↦ R i j_neg) < 0 →
      0 < a ⬝ᵥ (fun i : Fin n ↦ R i j_pos) →
        ∃ j' : Fin k',
          ∀ i : Fin n,
            R' i j' =
              double_description_ray a (fun t : Fin n ↦ R t j_neg) (fun t : Fin n ↦ R t j_pos) i

/-- Expanded form of `is_double_description_step`. -/
theorem is_double_description_step_iff
    {m n k k' : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin k) ℝ)
    (a : Fin n → ℝ)
    (R' : Matrix (Fin n) (Fin k') ℝ) :
    is_double_description_step A R a R' ↔
      (∀ j' : Fin k', append_row A a *ᵥ (fun i : Fin n ↦ R' i j') ≤ 0) ∧
        (∀ j : Fin k,
          a ⬝ᵥ (fun i : Fin n ↦ R i j) ≤ 0 →
            ∃ j' : Fin k', ∀ i : Fin n, R' i j' = R i j) ∧
        (∀ j_neg j_pos : Fin k,
          a ⬝ᵥ (fun i : Fin n ↦ R i j_neg) < 0 →
          0 < a ⬝ᵥ (fun i : Fin n ↦ R i j_pos) →
            ∃ j' : Fin k',
              ∀ i : Fin n,
                R' i j' =
                  double_description_ray a
                    (fun t : Fin n ↦ R t j_neg)
                    (fun t : Fin n ↦ R t j_pos) i) := by
  -- This theorem only unfolds the definition.
  rfl

/-- Helper for Lemma 3.51: the enlarged inequality system splits into the old system together
with the new appended-row inequality. -/
theorem append_row_mulVec_le_zero_iff
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin n → ℝ)
    (x : Fin n → ℝ) :
    append_row A a *ᵥ x ≤ 0 ↔ A *ᵥ x ≤ 0 ∧ a ⬝ᵥ x ≤ 0 := by
  constructor
  · intro hx
    constructor
    · intro i
      -- Restrict the enlarged inequality to an old row.
      simpa [Matrix.mulVec, append_row_apply_castSucc] using hx i.castSucc
    · -- Evaluate the enlarged inequality on the newly appended row.
      simpa [Matrix.mulVec, append_row_apply_last] using hx (Fin.last m)
  · rintro ⟨hA, ha⟩
    intro i
    -- Every row of the enlarged matrix is either an old row or the new final row.
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa [Matrix.mulVec, append_row_apply_castSucc] using hA j
    · simpa [Matrix.mulVec, append_row_apply_last] using ha

/-- Helper for Lemma 3.51: every retained old column of the previous cone already belongs to the
new column cone. -/
theorem retained_old_column_mem_new_cone
    {m n k k' : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {R : Matrix (Fin n) (Fin k) ℝ}
    {a : Fin n → ℝ}
    {R' : Matrix (Fin n) (Fin k') ℝ}
    (hstep : is_double_description_step A R a R')
    {j : Fin k}
    (hj : a ⬝ᵥ (fun i : Fin n ↦ R i j) ≤ 0) :
    (fun i : Fin n ↦ R i j) ∈ matrix_cone R' := by
  -- Use the retention clause to match the old column with a new column of `R'`.
  rcases hstep.2.1 j hj with ⟨j', hj'⟩
  refine mem_matrix_cone_iff.mpr ?_
  refine ⟨Pi.single j' 1, ?_, ?_⟩
  · intro t
    by_cases ht : t = j'
    · subst ht
      simp [Pi.single]
    · simp [Pi.single, ht]
  · ext i
    simpa only [Matrix.col, hj', Matrix.transpose_apply] using
      congrFun (Matrix.mulVec_single_one R' j') i

/-- Helper for Lemma 3.51: if every used old column already satisfies the new inequality, then
the whole old conic combination belongs to the updated cone. -/
theorem retained_old_combination_mem_new_cone
    {m n k k' : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {R : Matrix (Fin n) (Fin k) ℝ}
    {a : Fin n → ℝ}
    {R' : Matrix (Fin n) (Fin k') ℝ}
    (hstep : is_double_description_step A R a R')
    {μ : Fin k → ℝ}
    (hμ_nonneg : ∀ j : Fin k, 0 ≤ μ j)
    (hused : ∀ j : Fin k, μ j ≠ 0 → a ⬝ᵥ (fun i : Fin n ↦ R i j) ≤ 0) :
    R *ᵥ μ ∈ matrix_cone R' := by
  -- Expand the old cone point as a finite sum of scaled old columns.
  have hscaled :
      ∀ j : Fin k, μ j • (fun i : Fin n ↦ R i j) ∈ matrix_cone R' := by
    intro j
    by_cases hzero : μ j = 0
    · have hzero_mem : (0 : Fin n → ℝ) ∈ matrix_cone R' :=
        Submodule.zero_mem (matrix_cone R' : PointedCone ℝ (Fin n → ℝ))
      rw [hzero]
      simpa only [zero_smul] using hzero_mem
    · have hcol : (fun i : Fin n ↦ R i j) ∈ matrix_cone R' :=
        retained_old_column_mem_new_cone hstep (hused j hzero)
      exact PointedCone.smul_mem (matrix_cone R') (hμ_nonneg j) hcol
  have hsum :
      Finset.sum Finset.univ (fun j : Fin k ↦ μ j • (fun i : Fin n ↦ R i j)) ∈ matrix_cone R' := by
    exact Submodule.sum_mem (matrix_cone R') (fun j _ ↦ hscaled j)
  have hmulVec :
      R *ᵥ μ = Finset.sum Finset.univ (fun j : Fin k ↦ μ j • (fun i : Fin n ↦ R i j)) := by
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  -- Replace the finite column sum with the standard matrix-vector product.
  rw [hmulVec]
  exact hsum

/-- Helper for Lemma 3.51: every point in the new column hull satisfies the enlarged system. -/
theorem matrix_column_hull_subset_feasible_of_dd_step
    {m n k k' : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {R : Matrix (Fin n) (Fin k) ℝ}
    {a : Fin n → ℝ}
    {R' : Matrix (Fin n) (Fin k') ℝ}
    (hstep : is_double_description_step A R a R') :
    (matrix_cone R' : Set (Fin n → ℝ)) ⊆ matrix_polyhedral_cone (append_row A a) := by
  intro x hx
  refine (memMatrixPolyhedralCone (append_row A a) x).2 ?_
  rcases (mem_matrix_cone_iff).1 hx with ⟨y, hy_nonneg, rfl⟩
  intro i
  -- After composing the two matrix-vector products, the `i`-th coordinate is a sum of
  -- nonpositive terms with nonnegative coefficients.
  rw [Matrix.mulVec_mulVec]
  change ∑ j : Fin k', ((append_row A a * R') i j) * y j ≤ 0
  refine Finset.sum_nonpos ?_
  intro j hj
  have hcol_entry : ((append_row A a * R') i j) ≤ 0 := by
    simpa [Matrix.mul_apply, Matrix.mulVec] using (hstep.1 j i)
  exact mul_nonpos_of_nonpos_of_nonneg hcol_entry (hy_nonneg j)

/-- Helper for Lemma 3.51: every double-description ray has zero value on the newly appended
row functional `a`. -/
theorem doubleDescriptionRay_rowDot_eq_zero
    {n : ℕ}
    (a rj rk : Fin n → ℝ) :
    a ⬝ᵥ double_description_ray a rj rk = 0 := by
  -- Expand the ray and cancel the two symmetric mixed products.
  have hray :
      double_description_ray a rj rk =
        (a ⬝ᵥ rk) • rj - (a ⬝ᵥ rj) • rk := by
    ext t
    simp [double_description_ray, sub_eq_add_neg]
  calc
    a ⬝ᵥ double_description_ray a rj rk
        = (a ⬝ᵥ rk) * (a ⬝ᵥ rj) - (a ⬝ᵥ rj) * (a ⬝ᵥ rk) := by
            rw [hray, dotProduct_sub, dotProduct_smul, dotProduct_smul]
            simp [smul_eq_mul, mul_comm]
    _ = 0 := by ring

/-- Helper for Lemma 3.51: if a nonnegative conic combination has nonpositive value on the new row
and uses a column with positive new-row value, then it also uses a column with negative new-row
value. -/
theorem exists_negative_used_column_of_nonpositive_row_value
    {n k : ℕ}
    {R : Matrix (Fin n) (Fin k) ℝ}
    {a : Fin n → ℝ}
    {μ : Fin k → ℝ}
    (hμ_nonneg : ∀ j : Fin k, 0 ≤ μ j)
    {jPos : Fin k}
    (hjPos_used : μ jPos ≠ 0)
    (hjPos : 0 < a ⬝ᵥ (fun i : Fin n ↦ R i jPos))
    (hnew : a ⬝ᵥ (R *ᵥ μ) ≤ 0) :
    ∃ jNeg : Fin k, μ jNeg ≠ 0 ∧ a ⬝ᵥ (fun i : Fin n ↦ R i jNeg) < 0 := by
  by_contra hnone
  have hterm_nonneg :
      ∀ j : Fin k, 0 ≤ μ j * (a ⬝ᵥ (fun i : Fin n ↦ R i j)) := by
    intro j
    by_cases hj_used : μ j = 0
    · simp [hj_used]
    · have hj_row_nonneg : 0 ≤ a ⬝ᵥ (fun i : Fin n ↦ R i j) := by
        by_contra hj_row_neg
        exact hnone ⟨j, hj_used, lt_of_not_ge hj_row_neg⟩
      exact mul_nonneg (hμ_nonneg j) hj_row_nonneg
  have hjPos_coeff_pos : 0 < μ jPos * (a ⬝ᵥ (fun i : Fin n ↦ R i jPos)) := by
    have hμ_pos : 0 < μ jPos := lt_of_le_of_ne (hμ_nonneg jPos) (by simpa using hjPos_used.symm)
    exact mul_pos hμ_pos hjPos
  have hrest_nonneg :
      0 ≤
        Finset.sum
          (Finset.univ.erase jPos)
          (fun j : Fin k ↦ μ j * (a ⬝ᵥ (fun i : Fin n ↦ R i j))) := by
    exact Finset.sum_nonneg fun j _ ↦ hterm_nonneg j
  have hsum_decomp :
      Finset.sum Finset.univ (fun j : Fin k ↦ μ j * (a ⬝ᵥ (fun i : Fin n ↦ R i j))) =
        Finset.sum
            (Finset.univ.erase jPos)
            (fun j : Fin k ↦ μ j * (a ⬝ᵥ (fun i : Fin n ↦ R i j))) +
          μ jPos * (a ⬝ᵥ (fun i : Fin n ↦ R i jPos)) := by
    exact
      (Finset.univ.sum_erase_add
        (f := fun j : Fin k ↦ μ j * (a ⬝ᵥ (fun i : Fin n ↦ R i j)))
        (a := jPos)
        (Finset.mem_univ jPos)).symm
  have hsum_pos :
      0 < Finset.sum Finset.univ (fun j : Fin k ↦ μ j * (a ⬝ᵥ (fun i : Fin n ↦ R i j))) := by
    rw [hsum_decomp]
    exact add_pos_of_nonneg_of_pos hrest_nonneg hjPos_coeff_pos
  have hrow_eval :
      a ⬝ᵥ (R *ᵥ μ) =
        Finset.sum Finset.univ (fun j : Fin k ↦ μ j * (a ⬝ᵥ (fun i : Fin n ↦ R i j))) := by
    rw [Matrix.dotProduct_mulVec]
    simp [Matrix.vecMul, dotProduct, mul_comm]
  have hsum_nonpos :
      Finset.sum Finset.univ (fun j : Fin k ↦ μ j * (a ⬝ᵥ (fun i : Fin n ↦ R i j))) ≤ 0 := by
    simpa [hrow_eval] using hnew
  linarith

/-- Helper for Lemma 3.51: eliminating one used negative-positive pair replaces the old
coefficient vector by a smaller-support one together with one double-description ray. -/
theorem supportReductionViaDoubleDescriptionRay
    {n k : ℕ}
    {R : Matrix (Fin n) (Fin k) ℝ}
    {a : Fin n → ℝ}
    {μ : Fin k → ℝ}
    (hμ_nonneg : ∀ j : Fin k, 0 ≤ μ j)
    {jNeg jPos : Fin k}
    (hjNeg_used : μ jNeg ≠ 0)
    (hjPos_used : μ jPos ≠ 0)
    (hjNeg : a ⬝ᵥ (fun i : Fin n ↦ R i jNeg) < 0)
    (hjPos : 0 < a ⬝ᵥ (fun i : Fin n ↦ R i jPos)) :
    ∃ α : ℝ, ∃ μ' : Fin k → ℝ,
      0 ≤ α ∧
      (∀ t : Fin k, 0 ≤ μ' t) ∧
      R *ᵥ μ = R *ᵥ μ' +
        α • double_description_ray a (fun i : Fin n ↦ R i jNeg) (fun i : Fin n ↦ R i jPos) ∧
      a ⬝ᵥ (R *ᵥ μ') = a ⬝ᵥ (R *ᵥ μ) ∧
      (Finset.univ.filter (fun t : Fin k ↦ μ' t ≠ 0)).card <
        (Finset.univ.filter (fun t : Fin k ↦ μ t ≠ 0)).card := by
  have hneq : jNeg ≠ jPos := by
    intro hEq
    subst hEq
    linarith
  let p : ℝ := a ⬝ᵥ (fun i : Fin n ↦ R i jPos)
  let q : ℝ := -(a ⬝ᵥ (fun i : Fin n ↦ R i jNeg))
  let αNeg : ℝ := μ jNeg / p
  let αPos : ℝ := μ jPos / q
  let α : ℝ := min αNeg αPos
  let δ : Fin k → ℝ := Pi.single jNeg p + Pi.single jPos q
  let μ' : Fin k → ℝ :=
    fun t ↦
      if htNeg : t = jNeg then
        μ t - α * p
      else if htPos : t = jPos then
        μ t - α * q
      else
        μ t
  have hp_pos : 0 < p := by
    simpa [p] using hjPos
  have hq_pos : 0 < q := by
    simpa [q] using neg_pos.mpr hjNeg
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hα_nonneg : 0 ≤ α := by
    -- The elimination amount is the minimum of two admissible nonnegative quotients.
    dsimp [α]
    exact le_min
      (div_nonneg (hμ_nonneg jNeg) (le_of_lt hp_pos))
      (div_nonneg (hμ_nonneg jPos) (le_of_lt hq_pos))
  have hαp : α * p ≤ μ jNeg := by
    have hle : α ≤ αNeg := by
      exact min_le_left _ _
    calc
      α * p ≤ αNeg * p := by
        exact mul_le_mul_of_nonneg_right hle (le_of_lt hp_pos)
      _ = μ jNeg := by
        simp [αNeg, hp_ne]
  have hαq : α * q ≤ μ jPos := by
    have hle : α ≤ αPos := by
      exact min_le_right _ _
    calc
      α * q ≤ αPos * q := by
        exact mul_le_mul_of_nonneg_right hle (le_of_lt hq_pos)
      _ = μ jPos := by
        simp [αPos, hq_ne]
  have hμ'_nonneg : ∀ t : Fin k, 0 ≤ μ' t := by
    intro t
    by_cases htNeg : t = jNeg
    · subst htNeg
      simpa [μ'] using sub_nonneg.mpr hαp
    · by_cases htPos : t = jPos
      · subst htPos
        simpa [μ', htNeg] using sub_nonneg.mpr hαq
      · simpa [μ', htNeg, htPos] using hμ_nonneg t
  have hdelta_ray :
      R *ᵥ δ =
        double_description_ray a (fun i : Fin n ↦ R i jNeg) (fun i : Fin n ↦ R i jPos) := by
    -- The correction vector picks exactly the two columns entering the DD ray.
    ext i
    simp [δ, p, q, double_description_ray, Matrix.mulVec_add, Matrix.mulVec_single,
      Matrix.col, sub_eq_add_neg, smul_eq_mul, mul_comm]
  have hμ_eq : μ = μ' + α • δ := by
    -- The adjusted coefficients plus the correction vector recover the original coefficients.
    funext t
    by_cases htNeg : t = jNeg
    · subst htNeg
      simp [μ', δ, α, p, q, hneq]
    · by_cases htPos : t = jPos
      · subst htPos
        simp [μ', δ, α, p, q, htNeg]
      · simp [μ', δ, α, p, q, htNeg, htPos]
  have hdecomp :
      R *ᵥ μ = R *ᵥ μ' +
        α • double_description_ray a (fun i : Fin n ↦ R i jNeg) (fun i : Fin n ↦ R i jPos) := by
    -- Transport the coefficient identity through the matrix action and rewrite the correction.
    calc
      R *ᵥ μ = R *ᵥ (μ' + α • δ) := by rw [hμ_eq]
      _ = R *ᵥ μ' + R *ᵥ (α • δ) := by rw [Matrix.mulVec_add]
      _ = R *ᵥ μ' + α • (R *ᵥ δ) := by rw [Matrix.mulVec_smul]
      _ = R *ᵥ μ' +
          α • double_description_ray a (fun i : Fin n ↦ R i jNeg) (fun i : Fin n ↦ R i jPos) := by
            rw [hdelta_ray]
  have hrow_preserved : a ⬝ᵥ (R *ᵥ μ') = a ⬝ᵥ (R *ᵥ μ) := by
    -- The DD ray lies on the new hyperplane, so the new-row value is unchanged.
    have hdot := congrArg (fun x : Fin n → ℝ ↦ a ⬝ᵥ x) hdecomp
    simpa [dotProduct_add, dotProduct_smul, doubleDescriptionRay_rowDot_eq_zero] using hdot.symm
  let support : (Fin k → ℝ) → Finset (Fin k) := fun ν ↦
    Finset.univ.filter (fun t : Fin k ↦ ν t ≠ 0)
  have hsubset : support μ' ⊆ support μ := by
    intro t ht
    have htμ' : μ' t ≠ 0 := by
      simpa [support] using ht
    by_cases htNeg : t = jNeg
    · subst htNeg
      simpa [support] using hjNeg_used
    · by_cases htPos : t = jPos
      · subst htPos
        simpa [support] using hjPos_used
      · simpa [support, μ', htNeg, htPos] using htμ'
  have hdrop : μ' jNeg = 0 ∨ μ' jPos = 0 := by
    -- The minimum choice of `α` makes at least one adjusted coefficient vanish.
    by_cases hcase : αNeg ≤ αPos
    · left
      simp [μ', α, αNeg, min_eq_left hcase, hp_ne]
    · right
      have hcase' : αPos ≤ αNeg := le_of_not_ge hcase
      simp [μ', α, αPos, min_eq_right hcase', hq_ne, hneq.symm]
  have hsupport_lt : (support μ').card < (support μ).card := by
    have hne : support μ' ≠ support μ := by
      intro hsupp
      rcases hdrop with hdropNeg | hdropPos
      · have hmem : jNeg ∈ support μ := by
          simp [support, hjNeg_used]
        have hnot_mem : jNeg ∉ support μ' := by
          simp [support, hdropNeg]
        have hmem' : jNeg ∈ support μ' := by
          simpa [hsupp] using hmem
        exact hnot_mem hmem'
      · have hmem : jPos ∈ support μ := by
          simp [support, hjPos_used]
        have hnot_mem : jPos ∉ support μ' := by
          simp [support, hdropPos]
        have hmem' : jPos ∈ support μ' := by
          simpa [hsupp] using hmem
        exact hnot_mem hmem'
    exact Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).2 ⟨hsubset, hne⟩)
  exact ⟨α, μ', hα_nonneg, hμ'_nonneg, hdecomp, hrow_preserved, hsupport_lt⟩

/-- Helper for Lemma 3.51: an old conic combination satisfying the new appended-row inequality
belongs to the updated cone. -/
theorem old_cone_point_mem_new_cone_of_dd_step
    {m n k k' : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {R : Matrix (Fin n) (Fin k) ℝ}
    {a : Fin n → ℝ}
    {R' : Matrix (Fin n) (Fin k') ℝ}
    (hstep : is_double_description_step A R a R')
    {μ : Fin k → ℝ}
    (hμ_nonneg : ∀ j : Fin k, 0 ≤ μ j)
    (hnew : a ⬝ᵥ (R *ᵥ μ) ≤ 0) :
    R *ᵥ μ ∈ matrix_cone R' := by
  classical
  let support : (Fin k → ℝ) → Finset (Fin k) := fun ν ↦
    Finset.univ.filter (fun j : Fin k ↦ ν j ≠ 0)
  let P : ℕ → Prop := fun s =>
    ∀ ν : Fin k → ℝ,
      (support ν).card = s →
      (∀ j : Fin k, 0 ≤ ν j) →
      a ⬝ᵥ (R *ᵥ ν) ≤ 0 →
      R *ᵥ ν ∈ matrix_cone R'
  have hP : ∀ s : ℕ, P s := by
    intro s
    refine Nat.strong_induction_on s ?_
    intro t ih ν hν_card hν_nonneg hν_new
    by_cases hall :
        ∀ j : Fin k, ν j ≠ 0 → a ⬝ᵥ (fun i : Fin n ↦ R i j) ≤ 0
    · -- If every used old column survives the new inequality, the retained-column lemma closes.
      exact retained_old_combination_mem_new_cone hstep hν_nonneg hall
    · -- Otherwise, choose a used positive column and pair it with a forced used negative one.
      push Not at hall
      rcases hall with ⟨jPos, hjPos_used, hjPos⟩
      rcases exists_negative_used_column_of_nonpositive_row_value
          hν_nonneg hjPos_used hjPos hν_new with
        ⟨jNeg, hjNeg_used, hjNeg⟩
      rcases
          supportReductionViaDoubleDescriptionRay
            hν_nonneg hjNeg_used hjPos_used hjNeg hjPos with
        ⟨α, ν', hα_nonneg, hν'_nonneg, hdecomp, hrow_eq, hcard_lt⟩
      have hν'_new : a ⬝ᵥ (R *ᵥ ν') ≤ 0 := by
        linarith [hν_new, hrow_eq]
      have hrec : R *ᵥ ν' ∈ matrix_cone R' := by
        have hlt_support : (support ν').card < (support ν).card := by
          simpa [support] using hcard_lt
        have hlt : (support ν').card < t := by
          simpa [hν_card] using hlt_support
        exact ih (support ν').card hlt ν' rfl hν'_nonneg hν'_new
      have hray_mem :
          double_description_ray a (fun i : Fin n ↦ R i jNeg) (fun i : Fin n ↦ R i jPos) ∈
            matrix_cone R' := by
        -- The double-description step adds this exact ray as a column of `R'`.
        rcases hstep.2.2 jNeg jPos hjNeg hjPos with ⟨j', hj'⟩
        refine mem_matrix_cone_iff.mpr ?_
        refine ⟨Pi.single j' 1, ?_, ?_⟩
        · intro t
          by_cases ht : t = j'
          · subst ht
            simp [Pi.single]
          · simp [Pi.single, ht]
        · ext i
          simpa only [Matrix.col, hj', Matrix.transpose_apply] using
            congrFun (Matrix.mulVec_single_one R' j') i
      have hscaled_ray_mem :
          α • double_description_ray a (fun i : Fin n ↦ R i jNeg) (fun i : Fin n ↦ R i jPos) ∈
            matrix_cone R' := by
        exact PointedCone.smul_mem (matrix_cone R') hα_nonneg hray_mem
      have hsum_mem :
          R *ᵥ ν' +
            α • double_description_ray a (fun i : Fin n ↦ R i jNeg) (fun i : Fin n ↦ R i jPos) ∈
              matrix_cone R' := by
        exact Submodule.add_mem (matrix_cone R') hrec hscaled_ray_mem
      simpa [hdecomp] using hsum_mem
  exact hP (support μ).card μ rfl hμ_nonneg hnew

/-- Lemma 3.51. If `(A_i, R_i)` is an MW-pair, `A_{i+1}` is obtained by appending the row
`a^{i+1}`, and `R_{i+1}` is the matrix produced by one double-description step, then
`(A_{i+1}, R_{i+1})` is again an MW-pair. -/
theorem mw_pair_append_row_of_dd_step
    {m n k k' : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin k) ℝ)
    (a : Fin n → ℝ)
    (R' : Matrix (Fin n) (Fin k') ℝ)
    (hMW : mw_pair A R)
    (hstep : is_double_description_step A R a R') :
    mw_pair (append_row A a) R' := by
  -- It suffices to identify the feasible set of the enlarged system with the new column hull.
  change matrix_polyhedral_cone (append_row A a) = (matrix_cone R' : Set (Fin n → ℝ))
  ext x
  rw [memMatrixPolyhedralCone]
  constructor
  · intro hx
    -- Split the enlarged feasibility into the old system and the new row.
    rcases (append_row_mulVec_le_zero_iff A a x).1 hx with ⟨hx_old, hx_new⟩
    have hx_old_poly : x ∈ matrix_polyhedral_cone A := (memMatrixPolyhedralCone A x).2 hx_old
    have hx_old_cone : x ∈ matrix_cone R := by
      rw [hMW] at hx_old_poly
      exact hx_old_poly
    rcases (mem_matrix_cone_iff).1 hx_old_cone with
      ⟨μ, hμ_nonneg, hμx⟩
    -- Apply the yet-to-be-completed elimination helper to the old cone witness.
    have hμ_new : a ⬝ᵥ (R *ᵥ μ) ≤ 0 := by
      simpa [hμx] using hx_new
    simpa [hμx] using
      old_cone_point_mem_new_cone_of_dd_step hstep hμ_nonneg hμ_new
  · intro hx
    -- Every new conic combination is feasible because each new column is feasible.
    exact matrix_column_hull_subset_feasible_of_dd_step hstep hx
