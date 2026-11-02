import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_1.ch3_sec3_1_theorem_3_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_1.ch3_sec3_1_remark_3_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_1.ch3_sec3_1_algorithm_3_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_definition_3_3_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

universe u

/-- Helper for Theorem 3.7: the augmented matrix encoding `z - c ⬝ᵥ x ≤ 0` together with
`A *ᵥ x ≤ b`. -/
def augmented_objective_matrix
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ :=
  fun i j ↦ Fin.cases
      (Fin.cases 1 fun j' ↦ -c j')
      (fun i' ↦ Fin.cases 0 fun j' ↦ A i' j')
      i j

/-- Helper for Theorem 3.7: the right-hand side of the augmented objective system. -/
def augmented_objective_rhs
    {m : ℕ}
    (b : Fin m → ℝ) :
    Fin (m + 1) → ℝ :=
  fun i ↦ Fin.cases 0 b i

/-- Helper for Theorem 3.7: evaluating the augmented matrix at `(z, x)` recovers the objective
slack in the first coordinate and the original primal slacks afterwards. -/
lemma augmented_objective_matrix_mulVec_cons
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ)
    (z : ℝ)
    (x : Fin n → ℝ) :
    augmented_objective_matrix A c *ᵥ Fin.cons z x =
      Fin.cons (z - c ⬝ᵥ x) (A *ᵥ x) := by
  -- Evaluate the augmented system row by row.
  ext i
  cases i using Fin.cases with
  | zero =>
      -- The first row is exactly the objective slack `z - c ⬝ᵥ x`.
      simp [augmented_objective_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        sub_eq_add_neg]
  | succ i =>
      -- Every remaining row is one of the original inequalities.
      simp [augmented_objective_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Helper for Theorem 3.7: augmented feasibility at level `z` is exactly primal feasibility of
`x` together with the upper bound `z ≤ c ⬝ᵥ x`. -/
lemma augmented_objective_feasible_iff
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (z : ℝ)
    (x : Fin n → ℝ) :
    augmented_objective_matrix A c *ᵥ Fin.cons z x ≤ augmented_objective_rhs b ↔
      x ∈ primal_feasible_region A b ∧ z ≤ c ⬝ᵥ x := by
  -- Rewrite the augmented system into the first objective row and the original primal rows.
  rw [augmented_objective_matrix_mulVec_cons A c z x, mem_primal_feasible_region_iff A b x]
  constructor
  · intro hAug
    constructor
    · -- The nonzero rows are exactly the original primal inequalities.
      intro i
      simpa [augmented_objective_rhs] using hAug i.succ
    · -- The zero row is the single objective inequality `z - c ⬝ᵥ x ≤ 0`.
      have h0 := hAug 0
      simpa [augmented_objective_rhs] using h0
  · rintro ⟨hx, hz⟩ i
    cases i using Fin.cases with
    | zero =>
        -- Reassemble the first augmented row from the objective upper bound.
        simpa [augmented_objective_rhs] using hz
    | succ i =>
        -- Reassemble the original primal rows into the augmented system.
        simpa [augmented_objective_rhs] using hx i

/-- Helper for Theorem 3.7: every primal-feasible point yields an augmented feasible point at its
objective value. -/
lemma augmented_objective_system_feasible_of_primal_feasible
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ primal_feasible_region A b) :
    augmented_objective_matrix A c *ᵥ Fin.cons (c ⬝ᵥ x) x ≤ augmented_objective_rhs b := by
  -- Route correction: package the augmented row split once, then specialize it at `z = c ⬝ᵥ x`.
  exact (augmented_objective_feasible_iff A b c (c ⬝ᵥ x) x).2 ⟨hx, le_rfl⟩

/-- Helper for Theorem 3.7: every feasible augmented point is bounded above by every dual-feasible
objective value. -/
lemma augmented_objective_level_le_of_dual_feasible
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    {z : ℝ}
    {x : Fin n → ℝ}
    {u : Fin m → ℝ}
    (hAug : augmented_objective_matrix A c *ᵥ Fin.cons z x ≤ augmented_objective_rhs b)
    (hu : u ∈ dual_feasible_region A c) :
    z ≤ u ⬝ᵥ b := by
  rcases (augmented_objective_feasible_iff A b c z x).1 hAug with ⟨hx_feas, hz⟩
  rcases (mem_primal_feasible_region_iff A b x).mp hx_feas with hx_primal
  rcases (mem_dual_feasible_region_iff A c u).mp hu with ⟨hu_eq, hu_nonneg⟩
  have hweak : c ⬝ᵥ x ≤ u ⬝ᵥ b := by
    -- Re-express the primal value through the dual equality and then use rowwise monotonicity.
    calc
      c ⬝ᵥ x = (u ᵥ* A) ⬝ᵥ x := by rw [hu_eq]
      _ = u ⬝ᵥ (A *ᵥ x) := by rw [Matrix.dotProduct_mulVec]
      _ ≤ u ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hx_primal hu_nonneg
  -- Combine the augmented first-row bound with the usual weak-duality estimate.
  calc
    z ≤ c ⬝ᵥ x := hz
    _ ≤ u ⬝ᵥ b := hweak

/-- Helper for Theorem 3.7: a nonempty one-variable system of linear inequalities that is bounded
above has a greatest feasible value given by one positive-coefficient row. -/
lemma exists_isGreatest_one_variable_system_of_nonempty_bddAbove
    {ι : Type*} [Finite ι]
    (B : Matrix ι (Fin 1) ℝ)
    (r : ι → ℝ)
    (hnonempty : Set.Nonempty {z : ℝ | B *ᵥ (fun _ : Fin 1 ↦ z) ≤ r})
    (hbounded : BddAbove {z : ℝ | B *ᵥ (fun _ : Fin 1 ↦ z) ≤ r}) :
    ∃ h : ι, 0 < B h 0 ∧
      IsGreatest {z : ℝ | B *ᵥ (fun _ : Fin 1 ↦ z) ≤ r} (r h / B h 0) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  rcases hnonempty with ⟨z₀, hz₀⟩
  let posRows : Finset ι := Finset.univ.filter fun i ↦ 0 < B i 0
  have hrow_of_mem :
      ∀ {z : ℝ} (hz : B *ᵥ (fun _ : Fin 1 ↦ z) ≤ r) (i : ι), B i 0 * z ≤ r i := by
    intro z hz i
    simpa [Matrix.mulVec, dotProduct] using hz i
  have hpos_nonempty : posRows.Nonempty := by
    by_contra hpos_empty
    rcases hbounded with ⟨a, ha⟩
    have hcoeff_nonpos : ∀ i : ι, B i 0 ≤ 0 := by
      intro i
      by_contra hi
      exact hpos_empty ⟨i, by simp [posRows, not_le.mp hi]⟩
    let z' : ℝ := max a z₀ + 1
    have hz'_feasible : B *ᵥ (fun _ : Fin 1 ↦ z') ≤ r := by
      intro i
      have hz₀_row : B i 0 * z₀ ≤ r i := hrow_of_mem hz₀ i
      have hz'_ge : z₀ ≤ z' := by
        dsimp [z']
        linarith [le_max_right a z₀]
      have hmul : B i 0 * z' ≤ B i 0 * z₀ := by
        exact mul_le_mul_of_nonpos_left hz'_ge (hcoeff_nonpos i)
      simpa [Matrix.mulVec, dotProduct] using hmul.trans hz₀_row
    have hz'_gt : a < z' := by
      dsimp [z']
      linarith [le_max_left a z₀]
    exact (not_lt_of_ge (ha hz'_feasible)) hz'_gt
  rcases posRows.exists_min_image (fun i ↦ r i / B i 0) hpos_nonempty with
    ⟨h, hh_mem, hh_min⟩
  have hh_pos : 0 < B h 0 := by
    simpa [posRows] using hh_mem
  have hz₀_le : z₀ ≤ r h / B h 0 := by
    have hz₀_row : B h 0 * z₀ ≤ r h := hrow_of_mem hz₀ h
    exact (le_div_iff₀ hh_pos).2 (by simpa [mul_comm] using hz₀_row)
  refine ⟨h, hh_pos, ?_⟩
  constructor
  · -- The minimizing positive row gives a feasible terminal value.
    intro i
    by_cases hi_pos : 0 < B i 0
    · have hi_mem : i ∈ posRows := by
        simp [posRows, hi_pos]
      have hz_le : r h / B h 0 ≤ r i / B i 0 := hh_min i hi_mem
      simpa [Matrix.mulVec, dotProduct, mul_comm] using (le_div_iff₀ hi_pos).1 hz_le
    · have hi_nonpos : B i 0 ≤ 0 := le_of_not_gt hi_pos
      have hz₀_row : B i 0 * z₀ ≤ r i := hrow_of_mem hz₀ i
      have hmul : B i 0 * (r h / B h 0) ≤ B i 0 * z₀ := by
        exact mul_le_mul_of_nonpos_left hz₀_le hi_nonpos
      simpa [Matrix.mulVec, dotProduct] using hmul.trans hz₀_row
  · -- Any feasible value is bounded above by the positive row that realizes the minimum ratio.
    intro z hz
    have hz_row : B h 0 * z ≤ r h := hrow_of_mem hz h
    exact (le_div_iff₀ hh_pos).2 (by simpa [mul_comm] using hz_row)

/-- Helper for Theorem 3.7: every primal-feasible/dual-feasible pair satisfies weak duality. -/
lemma weak_duality_feasible_pair
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    {x : Fin n → ℝ}
    {u : Fin m → ℝ}
    (hx : x ∈ primal_feasible_region A b)
    (hu : u ∈ dual_feasible_region A c) :
    c ⬝ᵥ x ≤ u ⬝ᵥ b := by
  rcases (mem_primal_feasible_region_iff A b x).mp hx with hx_feas
  rcases (mem_dual_feasible_region_iff A c u).mp hu with ⟨hu_eq, hu_nonneg⟩
  -- Rewrite the primal objective as `u ⬝ᵥ (A *ᵥ x)` and then use feasibility rowwise.
  calc
    c ⬝ᵥ x = (u ᵥ* A) ⬝ᵥ x := by rw [hu_eq]
    _ = u ⬝ᵥ (A *ᵥ x) := by rw [Matrix.dotProduct_mulVec]
    _ ≤ u ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hx_feas hu_nonneg

/-- Helper for Theorem 3.7: a dual feasible point gives a global upper bound on all primal
objective values. -/
lemma primal_objective_values_bddAbove_of_dual_nonempty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hD : Set.Nonempty (dual_feasible_region A c)) :
    BddAbove (primal_objective_values A b c) := by
  rcases hD with ⟨u, hu⟩
  refine ⟨u ⬝ᵥ b, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  -- Weak duality turns the fixed dual feasible point into a uniform upper bound.
  exact weak_duality_feasible_pair A b c hx hu

/-- Helper for Theorem 3.7: a primal feasible point gives a global lower bound on all dual
objective values. -/
lemma dual_objective_values_bddBelow_of_primal_nonempty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : Set.Nonempty (primal_feasible_region A b)) :
    BddBelow (dual_objective_values A b c) := by
  rcases hP with ⟨x, hx⟩
  refine ⟨c ⬝ᵥ x, ?_⟩
  rintro z ⟨u, hu, rfl⟩
  -- The same weak-duality inequality gives the lower bound in the dual objective set.
  exact weak_duality_feasible_pair A b c hx hu

/-- Helper for Theorem 3.7: every valid inequality on a nonempty finite system comes from a
nonnegative row multiplier. -/
lemma exists_nonneg_row_multiplier_of_valid_inequality
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ)
    (b : m → ℝ)
    (c : n → ℝ)
    (δ : ℝ)
    (hP_nonempty : Set.Nonempty {x : n → ℝ | A *ᵥ x ≤ b})
    (hvalid : ∀ ⦃x : n → ℝ⦄, x ∈ {x : n → ℝ | A *ᵥ x ≤ b} → c ⬝ᵥ x ≤ δ) :
    ∃ u : m → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ := by
  let M : Matrix (n ⊕ Unit) (m ⊕ Unit) ℝ :=
    Matrix.fromBlocks A.transpose 0 (fun _ i ↦ b i) (1 : Matrix Unit Unit ℝ)
  let d : (n ⊕ Unit) → ℝ := Sum.elim c fun _ ↦ δ
  have htranspose_mulVec (u : m → ℝ) : A.transpose *ᵥ u = u ᵥ* A := by
    simpa using (Matrix.vecMul_transpose A.transpose u).symm
  have hbottom_block_mulVec (u : m → ℝ) :
      ((fun _ i ↦ b i : Matrix Unit m ℝ) *ᵥ u) () = u ⬝ᵥ b := by
    change ∑ i, b i * u i = u ⬝ᵥ b
    simpa [dotProduct] using dotProduct_comm b u
  have hrow_eval (w : (n ⊕ Unit) → ℝ) (i : m) :
      (w ᵥ* M) (Sum.inl i) = (A *ᵥ (w ∘ Sum.inl)) i + w (Sum.inr ()) * b i := by
    have htop : ((w ∘ Sum.inl) ᵥ* A.transpose) i = (A *ᵥ (w ∘ Sum.inl)) i := by
      simpa using congrFun (Matrix.vecMul_transpose A (w ∘ Sum.inl)) i
    calc
      (w ᵥ* M) (Sum.inl i)
          = ((w ∘ Sum.inl) ᵥ* A.transpose) i + ((w ∘ Sum.inr) ᵥ* (fun _ j ↦ b j)) i := by
              simp [M, Matrix.vecMul_fromBlocks]
      _ = (A *ᵥ (w ∘ Sum.inl)) i + ((w ∘ Sum.inr) ᵥ* (fun _ j ↦ b j)) i := by
            rw [htop]
      _ = (A *ᵥ (w ∘ Sum.inl)) i + w (Sum.inr ()) * b i := by
            simp [Matrix.vecMul, dotProduct]
  have hslack_eval (w : (n ⊕ Unit) → ℝ) :
      (w ᵥ* M) (Sum.inr ()) = w (Sum.inr ()) := by
    simp [M, Matrix.vecMul_fromBlocks]
  have hdual_eval (w : (n ⊕ Unit) → ℝ) :
      w ⬝ᵥ d = c ⬝ᵥ (w ∘ Sum.inl) + w (Sum.inr ()) * δ := by
    have hw : w = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) := by
      funext s
      rcases s with j | _
      · rfl
      · rfl
    calc
      w ⬝ᵥ d = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) ⬝ᵥ Sum.elim c (fun _ ↦ δ) := by
        rw [hw]
        rfl
      _ = (w ∘ Sum.inl) ⬝ᵥ c + (w ∘ Sum.inr) ⬝ᵥ (fun _ ↦ δ) := by
        simpa using
          sumElim_dotProduct_sumElim (w ∘ Sum.inl) c ((w ∘ Sum.inr) : Unit → ℝ)
            (fun _ : Unit ↦ δ)
      _ = c ⬝ᵥ (w ∘ Sum.inl) + w (Sum.inr ()) * δ := by
        simp [dotProduct_comm]
  have hfeasible :
      (∃ z : m ⊕ Unit → ℝ, M *ᵥ z = d ∧ 0 ≤ z) ↔
        ∃ u : m → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ := by
    constructor
    · rintro ⟨z, hz, hz_nonneg⟩
      let u : m → ℝ := z ∘ Sum.inl
      have hu_row : u ᵥ* A = c := by
        ext j
        have hj : (M *ᵥ z) (Sum.inl j) = d (Sum.inl j) :=
          congrFun hz (Sum.inl j)
        simpa [M, d, u, Matrix.fromBlocks_mulVec, htranspose_mulVec u] using hj
      have hu_eval_le : u ⬝ᵥ b ≤ δ := by
        have hbottom : (M *ᵥ z) (Sum.inr ()) = d (Sum.inr ()) :=
          congrFun hz (Sum.inr ())
        have hs_nonneg : 0 ≤ z (Sum.inr ()) := hz_nonneg (Sum.inr ())
        have hbottom' : u ⬝ᵥ b + z (Sum.inr ()) = δ := by
          simpa [M, d, u, Matrix.fromBlocks_mulVec, hbottom_block_mulVec] using hbottom
        linarith
      exact ⟨u, fun i ↦ hz_nonneg (Sum.inl i), hu_row, hu_eval_le⟩
    · rintro ⟨u, hu_nonneg, hu_row, hu_eval_le⟩
      let z : m ⊕ Unit → ℝ := Sum.elim u fun _ ↦ δ - u ⬝ᵥ b
      refine ⟨z, ?_, ?_⟩
      · ext s
        rcases s with j | _
        · simpa [M, d, z, Matrix.fromBlocks_mulVec, htranspose_mulVec u] using congrFun hu_row j
        · have hbottom : u ⬝ᵥ b + (δ - u ⬝ᵥ b) = δ := by
            ring
          simp [M, d, z, Matrix.fromBlocks_mulVec, hbottom_block_mulVec, hbottom]
      · intro s
        rcases s with i | _
        · exact hu_nonneg i
        · exact sub_nonneg.mpr hu_eval_le
  have hdual :
      (∀ w : (n ⊕ Unit) → ℝ, w ᵥ* M ≤ 0 → w ⬝ᵥ d ≤ 0) ↔
        ∀ ⦃x : n → ℝ⦄, x ∈ {x : n → ℝ | A *ᵥ x ≤ b} → c ⬝ᵥ x ≤ δ := by
    constructor
    · intro h x hx
      let w : (n ⊕ Unit) → ℝ := Sum.elim x fun _ ↦ (-1 : ℝ)
      have hw : w ᵥ* M ≤ 0 := by
        intro s
        rcases s with i | _
        · have hi : (A *ᵥ x) i + w (Sum.inr ()) * b i ≤ 0 := by
            simpa [w, sub_eq_add_neg] using sub_nonpos.mpr (hx i)
          simpa [hrow_eval, w] using hi
        · have hneg : (-1 : ℝ) ≤ 0 := neg_nonpos.mpr zero_le_one
          simp [hslack_eval, w, hneg]
      have hwd : w ⬝ᵥ d ≤ 0 := h w hw
      have hsub : c ⬝ᵥ x - δ ≤ 0 := by
        simpa [hdual_eval, w, sub_eq_add_neg] using hwd
      exact sub_nonpos.mp hsub
    · intro hvalid' w hw
      let x : n → ℝ := w ∘ Sum.inl
      let α : ℝ := w (Sum.inr ())
      have hα_nonpos : α ≤ 0 := by
        simpa [α, hslack_eval] using hw (Sum.inr ())
      rcases lt_or_eq_of_le hα_nonpos with hα_neg | hα_zero
      · let t : ℝ := -α
        have ht_pos : 0 < t := by
          simpa [t] using neg_pos.mpr hα_neg
        let y : n → ℝ := t⁻¹ • x
        have hy : y ∈ {x : n → ℝ | A *ᵥ x ≤ b} := by
          intro i
          have hi : (A *ᵥ x) i + α * b i ≤ 0 := by
            simpa [x, α, hrow_eval] using hw (Sum.inl i)
          have hbound : (A *ᵥ x) i ≤ t * b i := by
            have hsub : (A *ᵥ x) i - t * b i ≤ 0 := by
              simpa [t, sub_eq_add_neg] using hi
            exact sub_nonpos.mp hsub
          calc
            (A *ᵥ y) i = t⁻¹ * (A *ᵥ x) i := by
              simp [y, Matrix.mulVec_smul]
            _ ≤ t⁻¹ * (t * b i) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr ht_pos.le)
            _ = b i := by
              rw [← mul_assoc, inv_mul_cancel₀ ht_pos.ne', one_mul]
        have hy_valid : c ⬝ᵥ y ≤ δ := hvalid' hy
        have hx_eq : x = t • y := by
          ext j
          dsimp [y]
          calc
            x j = (t * t⁻¹) * x j := by rw [mul_inv_cancel₀ ht_pos.ne', one_mul]
            _ = t * (t⁻¹ * x j) := by ring
        have hwd_eq : w ⬝ᵥ d = t * (c ⬝ᵥ y - δ) := by
          calc
            w ⬝ᵥ d = c ⬝ᵥ x + α * δ := by
              simp [x, α, hdual_eval]
            _ = c ⬝ᵥ (t • y) - t * δ := by
              simp [hx_eq, t, α]
            _ = t * (c ⬝ᵥ y) - t * δ := by
              rw [dotProduct_smul, smul_eq_mul]
            _ = t * (c ⬝ᵥ y - δ) := by
              ring
        rw [hwd_eq]
        exact mul_nonpos_of_nonneg_of_nonpos ht_pos.le (sub_nonpos.mpr hy_valid)
      · have hdir : A *ᵥ x ≤ 0 := by
          intro i
          have hi : (A *ᵥ x) i + α * b i ≤ 0 := by
            simpa [x, α, hrow_eval] using hw (Sum.inl i)
          simpa [hα_zero] using hi
        obtain ⟨x₀, hx₀⟩ := hP_nonempty
        have hcx_nonpos : c ⬝ᵥ x ≤ 0 := by
          by_contra hcx
          have hcx_pos : 0 < c ⬝ᵥ x := lt_of_not_ge hcx
          let t : ℝ := (δ - c ⬝ᵥ x₀ + 1) / (c ⬝ᵥ x)
          have ht_nonneg : 0 ≤ t := by
            dsimp [t]
            refine div_nonneg ?_ hcx_pos.le
            linarith [hvalid' hx₀]
          have hxt : x₀ + t • x ∈ {x : n → ℝ | A *ᵥ x ≤ b} := by
            intro i
            have hmuli : t * (A *ᵥ x) i ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos ht_nonneg (hdir i)
            have hsum : (A *ᵥ x₀) i + t * (A *ᵥ x) i ≤ b i := by
              linarith [hx₀ i]
            simpa [Matrix.mulVec_add, Matrix.mulVec_smul] using hsum
          have hxt_valid : c ⬝ᵥ (x₀ + t • x) ≤ δ := hvalid' hxt
          have ht_mul : t * (c ⬝ᵥ x) = δ - c ⬝ᵥ x₀ + 1 := by
            dsimp [t]
            field_simp [hcx_pos.ne']
          have : δ + 1 ≤ δ := by
            calc
              δ + 1 = c ⬝ᵥ x₀ + t * (c ⬝ᵥ x) := by
                linarith
              _ = c ⬝ᵥ (x₀ + t • x) := by
                rw [dotProduct_add, dotProduct_smul]
                simp [smul_eq_mul]
              _ ≤ δ := hxt_valid
          linarith
        simpa [x, α, hα_zero, hdual_eval] using hcx_nonpos
  have hcertificate :
      (∃ u : m → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ) ↔
        ∀ w : (n ⊕ Unit) → ℝ, w ᵥ* M ≤ 0 → w ⬝ᵥ d ≤ 0 := by
    exact hfeasible.symm.trans <|
      feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers M d
  -- Route correction: the earlier valid-inequality/Farkas route avoids the false global `HEq`
  -- transport bridge and directly produces the nonnegative multiplier needed for duality.
  exact hcertificate.2 ((hdual).2 hvalid)

/-- Helper for Theorem 3.7: after `k` Fourier eliminations on the augmented objective system,
exactly `n - k` primal coordinates remain alongside the distinguished objective coordinate `z`. -/
lemma augmented_objective_stage_dim_eq_tail_succ
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ)
    {k : ℕ}
    (hk : k ≤ n) :
    fourier_stage_dim (augmented_objective_matrix A c) k = (n - k) + 1 := by
  -- The augmented system starts with `n + 1` variables, so after `k` eliminations one
  -- objective coordinate and `n - k` primal coordinates remain.
  rw [fourier_stage_dim_eq]
  omega

/-- Helper for Theorem 3.7: transporting a fixed-column matrix across a dimension equality is
equivalent to transporting the test vector back across the inverse equality. -/
lemma cast_matrix_feasibility_iff
    {ι : Type*}
    {p q : ℕ}
    (h : p = q)
    (A : Matrix ι (Fin p) ℝ)
    (b : ι → ℝ)
    (x : Fin q → ℝ) :
    cast (congrArg (fun t ↦ Matrix ι (Fin t) ℝ) h) A *ᵥ x ≤ b ↔
      A *ᵥ cast (congrArg (fun t ↦ Fin t → ℝ) h.symm) x ≤ b := by
  -- Both feasibility propositions are definitionally identical after eliminating the cast.
  cases h
  rfl

/-- Helper for Theorem 3.7: a tuple is recovered by appending its last coordinate to its tail. -/
lemma fin_snoc_castSucc_last_eq_self
    {n : ℕ}
    (x : Fin (n + 1) → ℝ) :
    Fin.snoc (fun i : Fin n ↦ x i.castSucc) (x (Fin.last n)) = x := by
  -- Check the last coordinate and the cast-succ coordinates separately.
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j
    simp

/-- Helper for Theorem 3.7: one Fourier step on the augmented objective system removes exactly the
last remaining primal coordinate while keeping the objective coordinate `z` fixed. -/
lemma augmented_objective_stage_succ_feasible_iff_exists_last
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    {k : ℕ}
    (hk : k < n)
    (z : ℝ)
    (x : Fin (n - (k + 1)) → ℝ) :
    let M := augmented_objective_matrix A c
    let d := augmented_objective_rhs b
    let hDim : fourier_stage_dim M k = ((n - (k + 1)) + 1) + 1 := by
      calc
        fourier_stage_dim M k = (n - k) + 1 :=
          augmented_objective_stage_dim_eq_tail_succ A c (Nat.le_of_lt hk)
        _ = ((n - (k + 1)) + 1) + 1 := by omega
    let hNext : fourier_stage_dim M (k + 1) = (n - (k + 1)) + 1 :=
      augmented_objective_stage_dim_eq_tail_succ A c (Nat.succ_le_of_lt hk)
    fourier_stage_matrix M (k + 1) *ᵥ
        cast (congrArg (fun t ↦ Fin t → ℝ) hNext.symm) (Fin.cons z x) ≤
      fourier_stage_rhs M d (k + 1) ↔
      ∃ t : ℝ,
        fourier_stage_matrix M k *ᵥ
            cast (congrArg (fun t ↦ Fin t → ℝ) hDim.symm) (Fin.cons z (Fin.snoc x t)) ≤
          fourier_stage_rhs M d k := by
  -- Route correction: use the owner one-step feasibility theorem and undo only the column cast.
  dsimp
  let M := augmented_objective_matrix A c
  let d := augmented_objective_rhs b
  let hDim : fourier_stage_dim M k = ((n - (k + 1)) + 1) + 1 := by
    calc
      fourier_stage_dim M k = (n - k) + 1 :=
        augmented_objective_stage_dim_eq_tail_succ A c (Nat.le_of_lt hk)
      _ = ((n - (k + 1)) + 1) + 1 := by omega
  let hNext : fourier_stage_dim M (k + 1) = (n - (k + 1)) + 1 :=
    augmented_objective_stage_dim_eq_tail_succ A c (Nat.succ_le_of_lt hk)
  let Mk : Matrix (fourier_stage_row M k) (Fin (((n - (k + 1)) + 1) + 1)) ℝ :=
    cast
      (congrArg
        (fun t ↦ Matrix (fourier_stage_row M k) (Fin t) ℝ)
        hDim)
      (fourier_stage_matrix M k)
  calc
    fourier_stage_matrix M (k + 1) *ᵥ
        cast (congrArg (fun t ↦ Fin t → ℝ) hNext.symm) (Fin.cons z x) ≤
      fourier_stage_rhs M d (k + 1)
      ↔
        fourier_step_matrix Mk *ᵥ Fin.cons z x ≤
          fourier_step_rhs Mk (fourier_stage_rhs M d k) := by
            simpa [Mk, hDim, hNext] using
              fourier_stage_succ_feasibility_iff M d hDim hNext (Fin.cons z x)
    _ ↔ ∃ t : ℝ, Mk *ᵥ Fin.snoc (Fin.cons z x) t ≤ fourier_stage_rhs M d k := by
          simpa [satisfies_fourier_motzkin_step] using
            fourier_motzkin_step_iff_exists_last_coordinate
              Mk
              (fourier_stage_rhs M d k)
              (Fin.cons z x)
    _ ↔ ∃ t : ℝ,
          fourier_stage_matrix M k *ᵥ
              cast (congrArg (fun t ↦ Fin t → ℝ) hDim.symm) (Fin.cons z (Fin.snoc x t)) ≤
            fourier_stage_rhs M d k := by
          refine exists_congr ?_
          intro t
          -- Undo the stage-`k` matrix cast after rebuilding the full `(z, x, t)` tuple.
          have hcons :
              Fin.cons z (Fin.snoc x t) =
                Fin.snoc (α := fun _ ↦ ℝ) (Fin.cons z x) t := by
            simpa using (Fin.cons_snoc_eq_snoc_cons (β := ℝ) z x t)
          simpa [Mk, hcons] using
            cast_matrix_feasibility_iff
              hDim
              (fourier_stage_matrix M k)
              (fourier_stage_rhs M d k)
              (Fin.snoc (α := fun _ ↦ ℝ) (Fin.cons z x) t)

/-- Helper for Theorem 3.7: when one more primal coordinate remains, the tail length at stage `k`
is the successor of the tail length at stage `k + 1`. -/
lemma augmented_objective_tail_succ_eq
    {n k : ℕ}
    (hk : k < n) :
    n - k = (n - (k + 1)) + 1 := by
  -- This is the arithmetic normalization needed to split a stage-`k` tail witness by `Fin.snoc`.
  omega

/-- Helper for Theorem 3.7: casting a `Fin.cons` vector across a tail-length equality is the same
as fixing the first coordinate and casting only the tail. -/
lemma cast_fin_cons_eq
    {p q : ℕ}
    (h : p = q)
    (z : ℝ)
    (x : Fin p → ℝ) :
    cast (congrArg (fun t ↦ Fin (t + 1) → ℝ) h) (Fin.cons z x) =
      Fin.cons z (cast (congrArg (fun t ↦ Fin t → ℝ) h) x) := by
  -- Eliminate the dimension equality so both sides reduce to the same tuple.
  cases h
  rfl

/-- Helper for Theorem 3.7: after `k` elimination steps, feasibility of the stage-`k` augmented
system at objective level `z` is equivalent to feasibility of the original augmented system at the
same level. -/
lemma augmented_objective_stage_feasible_iff_original
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (z : ℝ) :
    ∀ {k : ℕ}, (hk : k ≤ n) →
      let M := augmented_objective_matrix A c
      let d := augmented_objective_rhs b
      let hDim : fourier_stage_dim M k = (n - k) + 1 :=
        augmented_objective_stage_dim_eq_tail_succ A c hk
      (∃ x : Fin (n - k) → ℝ,
          fourier_stage_matrix M k *ᵥ
              cast (congrArg (fun t ↦ Fin t → ℝ) hDim.symm) (Fin.cons z x) ≤
            fourier_stage_rhs M d k) ↔
        ∃ x : Fin n → ℝ, M *ᵥ Fin.cons z x ≤ d := by
  -- Route correction: peel off one surviving primal coordinate at each successor stage, while the
  -- distinguished objective coordinate `z` stays in the first position throughout.
  intro k hk
  induction k with
  | zero =>
      -- Stage `0` is the original augmented system, so only the dimension cast disappears.
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, by simpa using hx⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by simpa using hx⟩
  | succ k ih =>
      have hklt : k < n := Nat.lt_of_succ_le hk
      have hkle : k ≤ n := Nat.le_of_lt hklt
      have htail : n - k = (n - (k + 1)) + 1 :=
        augmented_objective_tail_succ_eq hklt
      constructor
      · rintro ⟨x, hx⟩
        have hx' :
            fourier_stage_matrix (augmented_objective_matrix A c) (k + 1) *ᵥ
                cast
                  (congrArg
                    (fun t ↦ Fin t → ℝ)
                    (augmented_objective_stage_dim_eq_tail_succ A c
                      (k := k + 1) hk).symm)
                  (Fin.cons z x) ≤
              fourier_stage_rhs (augmented_objective_matrix A c) (augmented_objective_rhs b)
                (k + 1) := by
          -- Reexpress the witness in the exact public successor-stage shape.
          simpa using hx
        rcases
            (augmented_objective_stage_succ_feasible_iff_exists_last A b c hklt z x).1 hx'
          with ⟨last, hlast⟩
        have hprev :
            fourier_stage_matrix (augmented_objective_matrix A c) k *ᵥ
                cast
                  (congrArg
                    (fun t ↦ Fin t → ℝ)
                    (augmented_objective_stage_dim_eq_tail_succ A c
                      (k := k) hkle).symm)
                  (Fin.cons z
                    (cast
                      (congrArg (fun t ↦ Fin t → ℝ) htail.symm)
                      (Fin.snoc x last))) ≤
              fourier_stage_rhs (augmented_objective_matrix A c) (augmented_objective_rhs b) k := by
          -- Normalize the arithmetic tail equality so the stage-`k` witness matches the induction
          -- hypothesis exactly.
          have hconsCast :
              Fin.cons z
                  (cast
                    (congrArg (fun t ↦ Fin t → ℝ) htail.symm)
                    (Fin.snoc x last)) =
                cast
                  (congrArg (fun t ↦ Fin (t + 1) → ℝ) htail.symm)
                  (Fin.cons z (Fin.snoc x last)) := by
            symm
            exact cast_fin_cons_eq htail.symm z (Fin.snoc x last)
          simpa [htail, hconsCast] using hlast
        exact (ih hkle).mp ⟨
          cast
            (congrArg (fun t ↦ Fin t → ℝ) htail.symm)
            (Fin.snoc x last),
          hprev
        ⟩
      · rintro hx
        rcases (ih hkle).mpr hx with ⟨w, hw⟩
        let w' : Fin ((n - (k + 1)) + 1) → ℝ :=
          cast (congrArg (fun t ↦ Fin t → ℝ) htail) w
        let x : Fin (n - (k + 1)) → ℝ := fun i ↦ w' i.castSucc
        let last : ℝ := w' (Fin.last (n - (k + 1)))
        have hsnoc : Fin.snoc x last = w' := by
          -- Decompose the casted stage-`k` tail witness into its tail and last coordinate.
          simpa [x, last] using fin_snoc_castSucc_last_eq_self w'
        have hw_tail :
            cast (congrArg (fun t ↦ Fin t → ℝ) htail.symm) (Fin.snoc x last) = w := by
          -- Casting the reconstructed `Fin.snoc` witness back recovers the original stage-`k`
          -- tail witness.
          simpa [w'] using congrArg
            (cast (congrArg (fun t ↦ Fin t → ℝ) htail.symm))
            hsnoc
        have hw_cast :
            fourier_stage_matrix (augmented_objective_matrix A c) k *ᵥ
                cast
                  (congrArg
                    (fun t ↦ Fin t → ℝ)
                    (augmented_objective_stage_dim_eq_tail_succ A c
                      (k := k) hkle).symm)
                  (Fin.cons z
                    (cast
                      (congrArg (fun t ↦ Fin t → ℝ) htail.symm)
                      (Fin.snoc x last))) ≤
              fourier_stage_rhs (augmented_objective_matrix A c) (augmented_objective_rhs b) k := by
          -- Rewrite the induction witness into the `Fin.snoc` form consumed by one more Fourier
          -- elimination step.
          simpa [hw_tail] using hw
        have hnext :
            fourier_stage_matrix (augmented_objective_matrix A c) (k + 1) *ᵥ
                cast
                  (congrArg
                    (fun t ↦ Fin t → ℝ)
                    (augmented_objective_stage_dim_eq_tail_succ A c
                      (k := k + 1) hk).symm)
                  (Fin.cons z x) ≤
              fourier_stage_rhs (augmented_objective_matrix A c) (augmented_objective_rhs b)
                (k + 1) := by
          -- One more successor-stage equivalence removes exactly the recovered last coordinate.
          have hconsCast :
              Fin.cons z
                  (cast
                    (congrArg (fun t ↦ Fin t → ℝ) htail.symm)
                    (Fin.snoc x last)) =
                cast
                  (congrArg (fun t ↦ Fin (t + 1) → ℝ) htail.symm)
                  (Fin.cons z (Fin.snoc x last)) := by
            symm
            exact cast_fin_cons_eq htail.symm z (Fin.snoc x last)
          have hw_step :
              fourier_stage_matrix (augmented_objective_matrix A c) k *ᵥ
                  cast
                    (congrArg
                      (fun t ↦ Fin t → ℝ)
                      (let M := augmented_objective_matrix A c
                       calc
                         fourier_stage_dim M k = (n - k) + 1 :=
                           augmented_objective_stage_dim_eq_tail_succ A c hkle
                         _ = ((n - (k + 1)) + 1) + 1 := by omega).symm)
                    (Fin.cons z (Fin.snoc x last)) ≤
                fourier_stage_rhs
                  (augmented_objective_matrix A c)
                  (augmented_objective_rhs b)
                  k := by
            -- Undo the tail cast so the witness is in the exact shape expected by the step lemma.
            simpa [htail, hconsCast] using hw_cast
          exact (augmented_objective_stage_succ_feasible_iff_exists_last A b c hklt z x).2
            ⟨last, hw_step⟩
        exact ⟨x, by simpa using hnext⟩

/-- Helper for Theorem 3.7: once the remaining tail has dimension zero, every terminal witness
rewrites to the canonical one-variable vector after transporting both sides to the same stage
dimension. -/
lemma terminalTailCast_eq_canonical
    {d n : ℕ}
    (hTail : d = (n - n) + 1)
    (hTerminal : d = 1)
    (z : ℝ)
    (x : Fin (n - n) → ℝ) :
    cast (congrArg (fun t ↦ Fin t → ℝ) hTail.symm) (Fin.cons z x) =
      cast (congrArg (fun t ↦ Fin t → ℝ) hTerminal.symm) (fun _ : Fin 1 ↦ z) := by
  -- First collapse the zero-dimensional tail to the unique one-coordinate terminal vector.
  have hCollapse :
      cast (congrArg (fun t ↦ Fin t → ℝ) (by simp : (n - n) + 1 = 1)) (Fin.cons z x) =
        (fun _ : Fin 1 ↦ z) := by
    apply cast_eq_iff_heq.mpr
    let hOne : Fin ((n - n) + 1) = Fin 1 := by
      simp
    refine Function.hfunext hOne ?_
    intro i j hij
    fin_cases j
    have hi0 : (i : ℕ) = 0 := Fin.val_eq_val_of_heq hij
    cases i using Fin.cases with
    | zero =>
        simp
    | succ i =>
        exfalso
        simp at hi0
  have hTailToTerminal : d = 1 := by
    simpa using hTail
  -- After identifying the ambient dimension with `1`, the collapse lemma is exactly the goal.
  subst hTailToTerminal
  simpa using hCollapse

/-- Helper for Theorem 3.7: the original augmented system at level `z` is feasible exactly when
the terminal one-variable Fourier stage is feasible at the same `z`. -/
lemma augmented_objective_system_feasible_iff_terminal_stage
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (z : ℝ) :
    let M := augmented_objective_matrix A c
    let d := augmented_objective_rhs b
    let hTerminal : fourier_stage_dim M n = 1 :=
      by simpa using augmented_objective_stage_dim_eq_tail_succ A c (le_rfl : n ≤ n)
    (∃ x : Fin n → ℝ, M *ᵥ Fin.cons z x ≤ d) ↔
      fourier_stage_matrix M n *ᵥ
          cast (congrArg (fun t ↦ Fin t → ℝ) hTerminal.symm) (fun _ : Fin 1 ↦ z) ≤
        fourier_stage_rhs M d n := by
  -- Route correction: package the full elimination chain once, then specialize it at the
  -- terminal stage where the tail vector has dimension zero.
  dsimp
  let M := augmented_objective_matrix A c
  let d := augmented_objective_rhs b
  let hTail : fourier_stage_dim M n = (n - n) + 1 :=
    augmented_objective_stage_dim_eq_tail_succ A c (le_rfl : n ≤ n)
  let hTerminal : fourier_stage_dim M n = 1 := by
    simpa using hTail
  have hStage :
      (∃ x : Fin n → ℝ, M *ᵥ Fin.cons z x ≤ d) ↔
        ∃ x : Fin (n - n) → ℝ,
          fourier_stage_matrix M n *ᵥ
              cast
                  (congrArg (fun t ↦ Fin t → ℝ)
                    hTail.symm)
                  (Fin.cons z x) ≤
            fourier_stage_rhs M d n := by
    -- Specializing the stage-feasibility theorem at `k = n` reduces the original system to the
    -- terminal stage with a zero-dimensional tail.
    simpa [M, d] using
      (augmented_objective_stage_feasible_iff_original A b c z (k := n) (le_rfl : n ≤ n)).symm
  have hTerminalVec :
      (∃ x : Fin (n - n) → ℝ,
          fourier_stage_matrix M n *ᵥ
              cast
                  (congrArg (fun t ↦ Fin t → ℝ)
                    hTail.symm)
                  (Fin.cons z x) ≤
            fourier_stage_rhs M d n) ↔
        fourier_stage_matrix M n *ᵥ
            cast (congrArg (fun t ↦ Fin t → ℝ) hTerminal.symm) (fun _ : Fin 1 ↦ z) ≤
          fourier_stage_rhs M d n := by
    constructor
    · rintro ⟨x, hx⟩
      -- The terminal tail has type `Fin 0 → ℝ`, so every witness collapses to the constant
      -- one-coordinate vector carrying only `z`.
      simpa [terminalTailCast_eq_canonical hTail hTerminal z x] using hx
    · intro hx
      -- Conversely, the canonical terminal vector induces the unique `Fin 0` tail witness.
      refine ⟨fun _ ↦ 0, ?_⟩
      simpa [terminalTailCast_eq_canonical hTail hTerminal z (fun _ ↦ 0)] using hx
  -- Compose the full elimination equivalence with the terminal-vector normalization.
  exact hStage.trans hTerminalVec

/-- Helper for Theorem 3.7: a nonnegative multiplier for the augmented objective system
specializes to a dual-feasible vector once the first objective column is normalized to `1`. -/
lemma augmentedMultiplierToDualWitness
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    {y : Fin (m + 1) → ℝ}
    {β : ℝ}
    (hy_nonneg : 0 ≤ y)
    (hy_row : y ᵥ* augmented_objective_matrix A c = Fin.cons 1 0)
    (hy_rhs : y ⬝ᵥ augmented_objective_rhs b = β) :
    let u : Fin m → ℝ := fun i ↦ y i.succ
    u ∈ dual_feasible_region A c ∧ u ⬝ᵥ b = β := by
  let u : Fin m → ℝ := fun i ↦ y i.succ
  have hy_zero : y 0 = 1 := by
    -- The objective column of the augmented matrix records the leading multiplier directly.
    have h0 := congrFun hy_row 0
    simpa [augmented_objective_matrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using h0
  have hu_row : u ᵥ* A = c := by
    ext j
    -- The successor columns encode the original row equation after removing the objective entry.
    have hj := congrFun hy_row j.succ
    have hj' : -(y 0) * c j + (u ᵥ* A) j = 0 := by
      simpa [u, augmented_objective_matrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
        using hj
    rw [hy_zero] at hj'
    linarith
  have hu_rhs : u ⬝ᵥ b = β := by
    -- The augmented right-hand side has zero in the objective row, so only the tail contributes.
    calc
      u ⬝ᵥ b = y ⬝ᵥ augmented_objective_rhs b := by
        simp [u, augmented_objective_rhs, dotProduct, Fin.sum_univ_succ]
      _ = β := hy_rhs
  have hu_mem : u ∈ dual_feasible_region A c := by
    -- Tail coordinates inherit nonnegativity and the row equation from the augmented multiplier.
    exact (mem_dual_feasible_region_iff A c u).2 ⟨hu_row, fun i ↦ hy_nonneg i.succ⟩
  exact ⟨hu_mem, hu_rhs⟩

/-- Theorem 3.7 (Linear Programming Duality). If the primal feasible region
`P = {x | A *ᵥ x ≤ b}` and the dual feasible region `D = {u | u ᵥ* A = c ∧ 0 ≤ u}` are both
nonempty, then there are feasible points `x* ∈ P` and `u* ∈ D` with matching objective value,
and those values realize the primal maximum and dual minimum. -/
lemma exists_optimal_primal_dual_pair
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : Set.Nonempty (primal_feasible_region A b))
    (hD : Set.Nonempty (dual_feasible_region A c)) :
    ∃ xStar ∈ primal_feasible_region A b,
      ∃ uStar ∈ dual_feasible_region A c,
        c ⬝ᵥ xStar = uStar ⬝ᵥ b ∧
          IsGreatest (primal_objective_values A b c) (c ⬝ᵥ xStar) ∧
          IsLeast (dual_objective_values A b c) (uStar ⬝ᵥ b) := by
  let M := augmented_objective_matrix A c
  let d := augmented_objective_rhs b
  let hTerminal : fourier_stage_dim M n = 1 := by
    simpa [M] using augmented_objective_stage_dim_eq_tail_succ A c (k := n) (le_rfl : n ≤ n)
  let B : Matrix (fourier_stage_row M n) (Fin 1) ℝ :=
    cast
      (congrArg (fun t ↦ Matrix (fourier_stage_row M n) (Fin t) ℝ) hTerminal)
      (fourier_stage_matrix M n)
  have hterminalFeasible_iff :
      ∀ z : ℝ,
        B *ᵥ (fun _ : Fin 1 ↦ z) ≤ fourier_stage_rhs M d n ↔
          ∃ x : Fin n → ℝ, M *ᵥ Fin.cons z x ≤ d := by
    intro z
    -- Move the terminal-stage cast into the vector and then use the full elimination theorem.
    calc
      B *ᵥ (fun _ : Fin 1 ↦ z) ≤ fourier_stage_rhs M d n ↔
          fourier_stage_matrix M n *ᵥ
              cast (congrArg (fun t ↦ Fin t → ℝ) hTerminal.symm) (fun _ : Fin 1 ↦ z) ≤
            fourier_stage_rhs M d n := by
              simpa [B] using
                cast_matrix_feasibility_iff
                  hTerminal
                  (fourier_stage_matrix M n)
                  (fourier_stage_rhs M d n)
                  (fun _ : Fin 1 ↦ z)
      _ ↔ ∃ x : Fin n → ℝ, M *ᵥ Fin.cons z x ≤ d := by
            simpa [M, d] using (augmented_objective_system_feasible_iff_terminal_stage A b c z).symm
  have hterminalNonempty :
      Set.Nonempty {z : ℝ | B *ᵥ (fun _ : Fin 1 ↦ z) ≤ fourier_stage_rhs M d n} := by
    rcases hP with ⟨x₀, hx₀⟩
    refine ⟨c ⬝ᵥ x₀, ?_⟩
    -- A primal-feasible point is feasible for the augmented system at its own objective value.
    exact (hterminalFeasible_iff (c ⬝ᵥ x₀)).2 ⟨x₀,
      augmented_objective_system_feasible_of_primal_feasible A b c hx₀⟩
  have hterminalBddAbove :
      BddAbove {z : ℝ | B *ᵥ (fun _ : Fin 1 ↦ z) ≤ fourier_stage_rhs M d n} := by
    rcases hD with ⟨u₀, hu₀⟩
    refine ⟨u₀ ⬝ᵥ b, ?_⟩
    rintro z hz
    rcases (hterminalFeasible_iff z).1 hz with ⟨x, hx⟩
    -- Every terminal feasible level is bounded above by every dual-feasible value.
    exact augmented_objective_level_le_of_dual_feasible A b c hx hu₀
  rcases
      exists_isGreatest_one_variable_system_of_nonempty_bddAbove
        B
        (fourier_stage_rhs M d n)
        hterminalNonempty
        hterminalBddAbove with
    ⟨h, hh_pos, hgreatest⟩
  let zStar : ℝ := fourier_stage_rhs M d n h / B h 0
  have hzStar_mem :
      B *ᵥ (fun _ : Fin 1 ↦ zStar) ≤ fourier_stage_rhs M d n := hgreatest.1
  rcases (hterminalFeasible_iff zStar).1 hzStar_mem with ⟨xStar, hxAugStar⟩
  have hxStarData := (augmented_objective_feasible_iff A b c zStar xStar).1 hxAugStar
  have hxStar : xStar ∈ primal_feasible_region A b := hxStarData.1
  have hzStar_le : zStar ≤ c ⬝ᵥ xStar := hxStarData.2
  have hxStar_terminal :
      B *ᵥ (fun _ : Fin 1 ↦ c ⬝ᵥ xStar) ≤ fourier_stage_rhs M d n := by
    -- Reinsert the primal optimizer candidate into the terminal-stage equivalence.
    exact (hterminalFeasible_iff (c ⬝ᵥ xStar)).2 ⟨xStar,
      augmented_objective_system_feasible_of_primal_feasible A b c hxStar⟩
  have hxStar_le : c ⬝ᵥ xStar ≤ zStar := hgreatest.2 hxStar_terminal
  have hvalueStar : c ⬝ᵥ xStar = zStar := le_antisymm hxStar_le hzStar_le
  have hAugNonempty :
      Set.Nonempty {w : Fin (n + 1) → ℝ | M *ᵥ w ≤ d} := by
    rcases hP with ⟨x₀, hx₀⟩
    refine ⟨Fin.cons (c ⬝ᵥ x₀) x₀, ?_⟩
    exact augmented_objective_system_feasible_of_primal_feasible A b c hx₀
  have hvalidAug :
      ∀ ⦃w : Fin (n + 1) → ℝ⦄, w ∈ {w : Fin (n + 1) → ℝ | M *ᵥ w ≤ d} →
        (Fin.cons (1 : ℝ) (0 : Fin n → ℝ)) ⬝ᵥ w ≤ zStar := by
    intro w hw
    let z : ℝ := w 0
    let x : Fin n → ℝ := fun i ↦ w i.succ
    have hw_eq : Fin.cons z x = w := by
      ext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        rfl
    have hz_terminal :
        B *ᵥ (fun _ : Fin 1 ↦ z) ≤ fourier_stage_rhs M d n := by
      -- Any augmented-feasible point yields a terminal-feasible objective level.
      exact (hterminalFeasible_iff z).2 ⟨x, by simpa [z, x, hw_eq, M, d] using hw⟩
    have hz_le_star : z ≤ zStar := hgreatest.2 hz_terminal
    -- The distinguished coefficient vector extracts the objective coordinate `z`.
    simpa [z, dotProduct, Fin.sum_univ_succ] using hz_le_star
  obtain ⟨y, hy_nonneg, hy_row, hy_rhs_le⟩ :=
    exists_nonneg_row_multiplier_of_valid_inequality
      M
      d
      (Fin.cons (1 : ℝ) (0 : Fin n → ℝ))
      zStar
      hAugNonempty
      hvalidAug
  let uStar : Fin m → ℝ := fun i ↦ y i.succ
  have huStar_pkg :
      uStar ∈ dual_feasible_region A c ∧ uStar ⬝ᵥ b = y ⬝ᵥ d := by
    -- Normalize the augmented multiplier by discarding the objective coordinate.
    simpa [uStar, d] using
      augmentedMultiplierToDualWitness
        A
        b
        c
        hy_nonneg
        hy_row
        (β := y ⬝ᵥ d)
        rfl
  have huStar : uStar ∈ dual_feasible_region A c := huStar_pkg.1
  have huStar_eq_rhs : uStar ⬝ᵥ b = y ⬝ᵥ d := huStar_pkg.2
  have huStar_le : uStar ⬝ᵥ b ≤ zStar := by
    calc
      uStar ⬝ᵥ b = y ⬝ᵥ d := huStar_eq_rhs
      _ ≤ zStar := hy_rhs_le
  have hweakStar : c ⬝ᵥ xStar ≤ uStar ⬝ᵥ b :=
    weak_duality_feasible_pair A b c hxStar huStar
  have huStar_le_value : uStar ⬝ᵥ b ≤ c ⬝ᵥ xStar := by
    simpa [hvalueStar] using huStar_le
  have hvalue : c ⬝ᵥ xStar = uStar ⬝ᵥ b := le_antisymm hweakStar huStar_le_value
  have hprimalGreatest :
      IsGreatest (primal_objective_values A b c) (c ⬝ᵥ xStar) := by
    refine ⟨⟨xStar, hxStar, rfl⟩, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    -- Weak duality against the chosen dual optimizer bounds every primal value above by `zStar`.
    calc
      c ⬝ᵥ x ≤ uStar ⬝ᵥ b := weak_duality_feasible_pair A b c hx huStar
      _ = c ⬝ᵥ xStar := hvalue.symm
  have hdualLeast :
      IsLeast (dual_objective_values A b c) (uStar ⬝ᵥ b) := by
    refine ⟨⟨uStar, huStar, rfl⟩, ?_⟩
    rintro z ⟨u, hu, rfl⟩
    -- The same equality turns weak duality with the chosen primal optimizer into a lower bound.
    calc
      uStar ⬝ᵥ b = c ⬝ᵥ xStar := hvalue.symm
      _ ≤ u ⬝ᵥ b := weak_duality_feasible_pair A b c hxStar hu
  exact ⟨xStar, hxStar, uStar, huStar, hvalue, hprimalGreatest, hdualLeast⟩

/-- Consequence of Theorem 3.7: if the primal feasible region
`P = {x | A *ᵥ x ≤ b}` and the dual feasible region `D = {u | u ᵥ* A = c ∧ 0 ≤ u}` are both
nonempty, then strong duality holds: the primal optimal value equals the dual optimal value. -/
theorem linear_programming_duality_optimal_value_eq
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    linear_programming_strong_duality A b c := by
  intro hP hD
  rcases exists_optimal_primal_dual_pair A b c hP hD with
    ⟨xStar, hxStar, uStar, huStar, hvalue, hprimal, hdual⟩
  -- The shared optimal pair identifies both the primal supremum and the dual infimum.
  calc
    sSup (primal_objective_values A b c) = c ⬝ᵥ xStar := hprimal.csSup_eq
    _ = uStar ⬝ᵥ b := hvalue
    _ = sInf (dual_objective_values A b c) := hdual.csInf_eq.symm

/-- Consequence of Theorem 3.7: if the primal feasible region
`P = {x | A *ᵥ x ≤ b}` and the dual feasible region `D = {u | u ᵥ* A = c ∧ 0 ≤ u}` are both
nonempty, then the primal maximum is attained at some feasible point `x* ∈ P`. -/
theorem linear_programming_duality_primal_optimum_exists
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : Set.Nonempty (primal_feasible_region A b))
    (hD : Set.Nonempty (dual_feasible_region A c)) :
    ∃ xStar ∈ primal_feasible_region A b,
      IsGreatest (primal_objective_values A b c) (c ⬝ᵥ xStar) := by
  rcases exists_optimal_primal_dual_pair A b c hP hD with
    ⟨xStar, hxStar, uStar, huStar, hvalue, hprimal, hdual⟩
  -- The stronger helper already packages the primal optimizer and its maximality proof.
  exact ⟨xStar, hxStar, hprimal⟩

/-- Consequence of Theorem 3.7: if the primal feasible region
`P = {x | A *ᵥ x ≤ b}` and the dual feasible region `D = {u | u ᵥ* A = c ∧ 0 ≤ u}` are both
nonempty, then the dual minimum is attained at some feasible point `u* ∈ D`. -/
theorem linear_programming_duality_dual_optimum_exists
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : Set.Nonempty (primal_feasible_region A b))
    (hD : Set.Nonempty (dual_feasible_region A c)) :
    ∃ uStar ∈ dual_feasible_region A c,
      IsLeast (dual_objective_values A b c) (uStar ⬝ᵥ b) := by
  rcases exists_optimal_primal_dual_pair A b c hP hD with
    ⟨xStar, hxStar, uStar, huStar, hvalue, hprimal, hdual⟩
  -- The same stronger helper also packages the dual minimizer and its optimality proof.
  exact ⟨uStar, huStar, hdual⟩
