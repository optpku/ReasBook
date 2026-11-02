import Mathlib

open scoped BigOperators Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the declarations
-- below were aligned against local Chapter 3 precedent using `Matrix *ᵥ`, `Fin.last`, and
-- `Fin.snoc`.

variable {𝕜 : Type*}

section FourierStepData

variable [Ring 𝕜] [LinearOrder 𝕜]


/-- Rows with positive last coefficient in one Fourier-Motzkin step. -/
abbrev FourierPositiveIndex {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) :=
  { i : ι // 0 < A i (Fin.last n) }

/-- Rows with negative last coefficient in one Fourier-Motzkin step. -/
abbrev FourierNegativeIndex {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) :=
  { i : ι // A i (Fin.last n) < 0 }

/-- Rows whose last coefficient already vanishes. -/
abbrev FourierZeroIndex {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) :=
  { i : ι // A i (Fin.last n) = 0 }

/-- Indices for the inequalities produced by one Fourier-Motzkin step. -/
abbrev FourierStepIndex {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) :=
  (FourierPositiveIndex A × FourierNegativeIndex A) ⊕ FourierZeroIndex A

/-- The coefficient matrix of the one-step Fourier-Motzkin elimination system. -/
def fourier_step_matrix {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) :
    Matrix (FourierStepIndex A) (Fin n) 𝕜
  | Sum.inl ⟨i, k⟩, j =>
      A i.1 (Fin.last n) * A k.1 j.castSucc - A k.1 (Fin.last n) * A i.1 j.castSucc
  | Sum.inr i, j =>
      A i.1 j.castSucc

/-- The right-hand side of the one-step Fourier-Motzkin elimination system. -/
def fourier_step_rhs {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) (b : ι → 𝕜) :
    FourierStepIndex A → 𝕜
  | Sum.inl ⟨i, k⟩ =>
      A i.1 (Fin.last n) * b k.1 - A k.1 (Fin.last n) * b i.1
  | Sum.inr i =>
      b i.1

/-- The Fourier-Motzkin elimination system obtained from `A *ᵥ y ≤ b` by eliminating the last
coordinate, written canonically as the explicit eliminated matrix system. -/
abbrev satisfies_fourier_motzkin_step
    {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) (b : ι → 𝕜) (x : Fin n → 𝕜) : Prop :=
  fourier_step_matrix A *ᵥ x ≤ fourier_step_rhs A b

/-- Expanded form of `satisfies_fourier_motzkin_step`. -/
theorem satisfies_fourier_motzkin_step_iff
    {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) (b : ι → 𝕜) (x : Fin n → 𝕜) :
    satisfies_fourier_motzkin_step A b x ↔
      ((∀ i k : ι,
          0 < A i (Fin.last n) →
          A k (Fin.last n) < 0 →
            A i (Fin.last n) * (∑ j : Fin n, A k j.castSucc * x j) -
                A k (Fin.last n) * (∑ j : Fin n, A i j.castSucc * x j) ≤
              A i (Fin.last n) * b k - A k (Fin.last n) * b i) ∧
        ∀ i : ι,
          A i (Fin.last n) = 0 →
            (∑ j : Fin n, A i j.castSucc * x j) ≤ b i) := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i k hi_pos hk_neg
      have hpair :
          (fourier_step_matrix A *ᵥ x) (Sum.inl ⟨⟨i, hi_pos⟩, ⟨k, hk_neg⟩⟩) ≤
            fourier_step_rhs A b (Sum.inl ⟨⟨i, hi_pos⟩, ⟨k, hk_neg⟩⟩) := hx _
      have hpair' :
          ∑ j : Fin n,
              (A i (Fin.last n) * A k j.castSucc - A k (Fin.last n) * A i j.castSucc) * x j ≤
            A i (Fin.last n) * b k - A k (Fin.last n) * b i := by
        simpa [Matrix.mulVec, dotProduct, fourier_step_matrix, fourier_step_rhs] using hpair
      simpa [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        Finset.sum_sub_distrib, sub_eq_add_neg, left_distrib, right_distrib, mul_assoc]
        using hpair'
    · intro i hzero
      have hzero_row :
          (fourier_step_matrix A *ᵥ x) (Sum.inr ⟨i, hzero⟩) ≤
            fourier_step_rhs A b (Sum.inr ⟨i, hzero⟩) := hx _
      simpa [satisfies_fourier_motzkin_step, fourier_step_matrix, fourier_step_rhs,
        Matrix.mulVec, dotProduct] using hzero_row
  · rintro ⟨hpair, hzero⟩
    intro s
    rcases s with ⟨⟨i, hi_pos⟩, ⟨k, hk_neg⟩⟩ | ⟨i, hzero_row⟩
    · have hpair' :
          ∑ j : Fin n,
              (A i (Fin.last n) * A k j.castSucc - A k (Fin.last n) * A i j.castSucc) * x j ≤
            A i (Fin.last n) * b k - A k (Fin.last n) * b i := by
        simpa [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib,
          Finset.sum_sub_distrib, sub_eq_add_neg, left_distrib, right_distrib, mul_assoc]
          using hpair i k hi_pos hk_neg
      simpa [satisfies_fourier_motzkin_step, fourier_step_matrix, fourier_step_rhs,
        Matrix.mulVec, dotProduct] using hpair'
    · simpa [satisfies_fourier_motzkin_step, fourier_step_matrix, fourier_step_rhs,
        Matrix.mulVec, dotProduct] using hzero i hzero_row

end FourierStepData

section Ring

variable [Ring 𝕜]

/-- Helper for Theorem 3.1: rewriting a row of `A *ᵥ (Fin.snoc x t)` as the contribution from the
first `n` coordinates plus the last-column term. -/
lemma mulVec_snoc_apply
    {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) (x : Fin n → 𝕜) (t : 𝕜) (i : ι) :
    (A *ᵥ (Fin.snoc x t)) i =
      (∑ j : Fin n, A i j.castSucc * x j) + A i (Fin.last n) * t := by
  -- Split the dot product into the first `n` coordinates and the last coordinate.
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

end Ring

section OrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Helper for Theorem 3.1: a positive last coefficient rewrites a row inequality as an upper bound
for the last coordinate. -/
lemma positive_last_coordinate_row_iff
    {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) (b : ι → 𝕜) (x : Fin n → 𝕜)
    {i : ι} {t : 𝕜} (hi_pos : 0 < A i (Fin.last n)) :
    (∑ j : Fin n, A i j.castSucc * x j) + A i (Fin.last n) * t ≤ b i ↔
      t ≤ (b i - ∑ j : Fin n, A i j.castSucc * x j) / A i (Fin.last n) := by
  constructor
  · intro hrow
    -- Move the projected row sum to the right and divide by the positive coefficient.
    rw [le_div_iff₀ hi_pos]
    nlinarith [hrow]
  · intro ht
    -- Convert the bound on `t` back into the original row inequality.
    rw [le_div_iff₀ hi_pos] at ht
    nlinarith [ht]

/-- Helper for Theorem 3.1: a negative last coefficient rewrites a row inequality as a lower bound
for the last coordinate. -/
lemma negative_last_coordinate_row_iff
    {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) (b : ι → 𝕜) (x : Fin n → 𝕜)
    {i : ι} {t : 𝕜} (hi_neg : A i (Fin.last n) < 0) :
    (∑ j : Fin n, A i j.castSucc * x j) + A i (Fin.last n) * t ≤ b i ↔
      ((∑ j : Fin n, A i j.castSucc * x j) - b i) / (-A i (Fin.last n)) ≤ t := by
  have hi_pos : 0 < -A i (Fin.last n) := by
    nlinarith [hi_neg]
  constructor
  · intro hrow
    -- Move the row inequality into lower-bound form and divide by the positive quantity `-aᵢₙ`.
    rw [div_le_iff₀ hi_pos]
    nlinarith [hrow]
  · intro ht
    -- Clear the denominator and recover the original row inequality.
    rw [div_le_iff₀ hi_pos] at ht
    nlinarith [ht]

/-- Helper for Theorem 3.1: a feasible extension yields each paired Fourier-Motzkin inequality by
eliminating the last coordinate. -/
lemma pair_inequality_of_feasible_extension
    {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) (b : ι → 𝕜) (x : Fin n → 𝕜) {t : 𝕜}
    (hxt : A *ᵥ (Fin.snoc x t) ≤ b) {i k : ι}
    (hi_pos : 0 < A i (Fin.last n)) (hk_neg : A k (Fin.last n) < 0) :
    A i (Fin.last n) * (∑ j : Fin n, A k j.castSucc * x j) -
        A k (Fin.last n) * (∑ j : Fin n, A i j.castSucc * x j) ≤
      A i (Fin.last n) * b k - A k (Fin.last n) * b i := by
  have hk_row :
      (∑ j : Fin n, A k j.castSucc * x j) + A k (Fin.last n) * t ≤ b k := by
    -- Rewrite the `k`th row into the textbook split form.
    simpa [mulVec_snoc_apply] using hxt k
  have hi_row :
      (∑ j : Fin n, A i j.castSucc * x j) + A i (Fin.last n) * t ≤ b i := by
    -- Rewrite the `i`th row into the textbook split form.
    simpa [mulVec_snoc_apply] using hxt i
  have hk_scaled :
      A i (Fin.last n) *
          ((∑ j : Fin n, A k j.castSucc * x j) + A k (Fin.last n) * t) ≤
        A i (Fin.last n) * b k := by
    -- Multiply the `k`th inequality by the positive coefficient `aᵢₙ`.
    exact mul_le_mul_of_nonneg_left hk_row hi_pos.le
  have hi_scaled :
      (-A k (Fin.last n)) *
          ((∑ j : Fin n, A i j.castSucc * x j) + A i (Fin.last n) * t) ≤
        (-A k (Fin.last n)) * b i := by
    -- Multiply the `i`th inequality by the positive coefficient `-aₖₙ`.
    exact mul_le_mul_of_nonneg_left hi_row (by nlinarith [hk_neg])
  -- Adding the scaled inequalities cancels the `t`-terms and produces the Fourier pair inequality.
  nlinarith [hk_scaled, hi_scaled]

/-- Helper for Theorem 3.1: each Fourier pair inequality says that every negative-row lower bound is
at most every positive-row upper bound. -/
lemma pair_inequality_yields_lower_le_upper
    {ι : Type*} {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) (b : ι → 𝕜) (x : Fin n → 𝕜)
    {i k : ι} (hi_pos : 0 < A i (Fin.last n)) (hk_neg : A k (Fin.last n) < 0)
    (hpair :
      A i (Fin.last n) * (∑ j : Fin n, A k j.castSucc * x j) -
          A k (Fin.last n) * (∑ j : Fin n, A i j.castSucc * x j) ≤
        A i (Fin.last n) * b k - A k (Fin.last n) * b i) :
    ((∑ j : Fin n, A k j.castSucc * x j) - b k) / (-A k (Fin.last n)) ≤
      (b i - ∑ j : Fin n, A i j.castSucc * x j) / A i (Fin.last n) := by
  have hk_pos : 0 < -A k (Fin.last n) := by
    nlinarith [hk_neg]
  -- Clear the positive denominators and reduce to the given paired inequality.
  rw [div_le_div_iff₀ hk_pos hi_pos]
  nlinarith [hpair]

/-- Helper for Theorem 3.1: a point satisfying the Fourier-Motzkin step admits a compatible choice
of the eliminated last coordinate. -/
lemma exists_feasible_last_coordinate_of_fourier_step
    {ι : Type*} [Finite ι] {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) (b : ι → 𝕜) (x : Fin n → 𝕜)
    (hx : satisfies_fourier_motzkin_step A b x) :
    ∃ t : 𝕜, A *ᵥ (Fin.snoc x t) ≤ b := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hx' := (satisfies_fourier_motzkin_step_iff A b x).1 hx
  set posRows : Finset ι := Finset.univ.filter fun i ↦ 0 < A i (Fin.last n)
  set negRows : Finset ι := Finset.univ.filter fun i ↦ A i (Fin.last n) < 0
  set upper : ι → 𝕜 := fun i ↦
    (b i - ∑ j : Fin n, A i j.castSucc * x j) / A i (Fin.last n)
  set lower : ι → 𝕜 := fun i ↦
    ((∑ j : Fin n, A i j.castSucc * x j) - b i) / (-A i (Fin.last n))
  by_cases hneg : negRows.Nonempty
  · by_cases hpos : posRows.Nonempty
    · refine ⟨negRows.sup' hneg lower, ?_⟩
      intro i
      have hi_cases := lt_trichotomy (A i (Fin.last n)) 0
      rcases hi_cases with hi_neg | hzero | hi_pos
      · -- A negative row only requires the chosen `t` to lie above its lower bound.
        rw [mulVec_snoc_apply]
        have hi_mem : i ∈ negRows := by
          simp [negRows, hi_neg]
        have h_lower : lower i ≤ negRows.sup' hneg lower := by
          exact Finset.le_sup' lower hi_mem
        simpa [lower] using
          (negative_last_coordinate_row_iff A b x hi_neg).2 h_lower
      · -- A zero row is already part of the projected system.
        rw [mulVec_snoc_apply]
        have hzero_row : (∑ j : Fin n, A i j.castSucc * x j) ≤ b i := hx'.2 i hzero
        simpa [hzero] using hzero_row
      · -- A positive row follows because every lower bound is below its upper bound.
        rw [mulVec_snoc_apply]
        have hi_mem : i ∈ posRows := by
          simp [posRows, hi_pos]
        have h_upper : negRows.sup' hneg lower ≤ upper i := by
          refine Finset.sup'_le hneg lower ?_
          intro k hk
          have hk_neg : A k (Fin.last n) < 0 := by
            simpa [negRows] using hk
          exact
            pair_inequality_yields_lower_le_upper A b x hi_pos hk_neg
              (hx'.1 i k hi_pos hk_neg)
        simpa [upper] using
          (positive_last_coordinate_row_iff A b x hi_pos).2 h_upper
    · refine ⟨negRows.sup' hneg lower, ?_⟩
      intro i
      have hi_cases := lt_trichotomy (A i (Fin.last n)) 0
      rcases hi_cases with hi_neg | hzero | hi_pos
      · -- With no positive rows, negative rows are still handled by the supremum of lower bounds.
        rw [mulVec_snoc_apply]
        have hi_mem : i ∈ negRows := by
          simp [negRows, hi_neg]
        have h_lower : lower i ≤ negRows.sup' hneg lower := by
          exact Finset.le_sup' lower hi_mem
        simpa [lower] using
          (negative_last_coordinate_row_iff A b x hi_neg).2 h_lower
      · -- Zero rows remain unchanged after inserting the last coordinate.
        rw [mulVec_snoc_apply]
        have hzero_row : (∑ j : Fin n, A i j.castSucc * x j) ≤ b i := hx'.2 i hzero
        simpa [hzero] using hzero_row
      · -- Route correction: this branch is impossible because a positive coefficient would make
        -- `posRows` nonempty.
        exfalso
        apply hpos
        exact ⟨i, by simp [posRows, hi_pos]⟩
  · by_cases hpos : posRows.Nonempty
    · refine ⟨posRows.inf' hpos upper, ?_⟩
      intro i
      have hi_cases := lt_trichotomy (A i (Fin.last n)) 0
      rcases hi_cases with hi_neg | hzero | hi_pos
      · -- Route correction: this branch is impossible because a negative coefficient would make
        -- `negRows` nonempty.
        exfalso
        apply hneg
        exact ⟨i, by simp [negRows, hi_neg]⟩
      · -- Zero rows are already controlled by the second half of `hx`.
        rw [mulVec_snoc_apply]
        have hzero_row : (∑ j : Fin n, A i j.castSucc * x j) ≤ b i := hx'.2 i hzero
        simpa [hzero] using hzero_row
      · -- With no negative rows, the infimum of upper bounds is itself an admissible upper bound.
        rw [mulVec_snoc_apply]
        have hi_mem : i ∈ posRows := by
          simp [posRows, hi_pos]
        have h_upper : posRows.inf' hpos upper ≤ upper i := by
          exact Finset.inf'_le upper hi_mem
        simpa [upper] using
          (positive_last_coordinate_row_iff A b x hi_pos).2 h_upper
    · refine ⟨0, ?_⟩
      intro i
      have hi_cases := lt_trichotomy (A i (Fin.last n)) 0
      rcases hi_cases with hi_neg | hzero | hi_pos
      · -- Route correction: with both filtered sets empty, a negative row cannot occur.
        exfalso
        apply hneg
        exact ⟨i, by simp [negRows, hi_neg]⟩
      · -- Every surviving row has zero last coefficient, so `t = 0` is feasible.
        rw [mulVec_snoc_apply]
        have hzero_row : (∑ j : Fin n, A i j.castSucc * x j) ≤ b i := hx'.2 i hzero
        simpa [hzero] using hzero_row
      · -- Route correction: with both filtered sets empty, a positive row cannot occur.
        exfalso
        apply hpos
        exact ⟨i, by simp [posRows, hi_pos]⟩

/-- Theorem 3.1. A vector of the first `n` coordinates satisfies the Fourier-Motzkin elimination
system if and only if it extends to a vector satisfying `A *ᵥ y ≤ b`. -/
theorem fourier_motzkin_step_iff_exists_last_coordinate
    {ι : Type*} [Finite ι] {n : ℕ} (A : Matrix ι (Fin (n + 1)) 𝕜) (b : ι → 𝕜)
    (x : Fin n → 𝕜) :
    satisfies_fourier_motzkin_step A b x ↔
      ∃ x_last : 𝕜, A *ᵥ (Fin.snoc x x_last) ≤ b := by
  constructor
  · -- The converse direction is the interval argument from the textbook proof.
    exact exists_feasible_last_coordinate_of_fourier_step A b x
  · rintro ⟨x_last, hx_last⟩
    exact (satisfies_fourier_motzkin_step_iff A b x).2 ⟨
      (fun i k hi_pos hk_neg ↦ pair_inequality_of_feasible_extension A b x hx_last hi_pos hk_neg),
      fun i hzero ↦ by
        -- When the last coefficient vanishes, the feasible row already equals the projected row.
        simpa [mulVec_snoc_apply, hzero] using hx_last i⟩

end OrderedField
