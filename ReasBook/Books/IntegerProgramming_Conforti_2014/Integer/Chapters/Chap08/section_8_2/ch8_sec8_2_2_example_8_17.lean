/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_2.ch8_sec8_2_1_example_8_14

open scoped BigOperators

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tool such as
-- `lean_leansearch`, so this file reuses the Chapter 8 generalized-assignment block API from
-- Example 8.14 directly.

section Example817

variable {m n : ℕ}

/-- The profit contributed by a column `z` for agent `j`. -/
def column_profit
    (c : Fin m → Fin n → ℝ)
    (j : Fin n)
    (z : Fin m → Bool) : ℝ :=
  ∑ i, c i j * bool_entry (z i)

/-- The objective value of a master problem indexed by a family of column subsets `A_j`. -/
def master_objective
    (c : Fin m → Fin n → ℝ)
    (A : Fin n → Finset (Fin m → Bool))
    (lam : Fin n → (Fin m → Bool) → ℝ) : ℝ :=
  ∑ j, ∑ z ∈ A j, column_profit c j z * lam j z

/-- Feasibility for the restricted master problem, represented as a full Dantzig-Wolfe feasible
solution whose support is contained in the selected subsets `S_j`. -/
def restricted_master_feasible
    (t : Fin m → Fin n → ℝ)
    (T : Fin n → ℝ)
    (S : Fin n → Finset (Fin m → Bool))
    (lam : Fin n → (Fin m → Bool) → ℝ) : Prop :=
  generalized_assignment_master_feasible_on
      (generalized_assignment_block_patterns t T) lam ∧
    ∀ j z, z ∈ generalized_assignment_block_patterns t T j → z ∉ S j → lam j z = 0

/-- Unfolding characterization of restricted master feasibility. -/
theorem restricted_master_feasible_iff
    {t : Fin m → Fin n → ℝ}
    {T : Fin n → ℝ}
    {S : Fin n → Finset (Fin m → Bool)}
    {lam : Fin n → (Fin m → Bool) → ℝ} :
    restricted_master_feasible t T S lam ↔
      generalized_assignment_master_feasible_on
          (generalized_assignment_block_patterns t T) lam ∧
        ∀ j z, z ∈ generalized_assignment_block_patterns t T j → z ∉ S j → lam j z = 0 :=
  Iff.rfl

/-- The feasible set of the restricted master problem indexed by the selected column families
`S_j`. -/
def restricted_master_feasible_set
    (t : Fin m → Fin n → ℝ)
    (T : Fin n → ℝ)
    (S : Fin n → Finset (Fin m → Bool)) :
    Set (Fin n → (Fin m → Bool) → ℝ) :=
  {lam | restricted_master_feasible t T S lam}

/-- Membership in `restricted_master_feasible_set t T S` is exactly restricted master
feasibility. -/
theorem mem_restricted_master_feasible_set_iff
    {t : Fin m → Fin n → ℝ}
    {T : Fin n → ℝ}
    {S : Fin n → Finset (Fin m → Bool)}
    {lam : Fin n → (Fin m → Bool) → ℝ} :
    lam ∈ restricted_master_feasible_set t T S ↔
      restricted_master_feasible t T S lam :=
  Iff.rfl

/-- The feasible set of the full Dantzig-Wolfe master problem on the canonical block families
`Q_j = generalized_assignment_block_patterns t T j`. -/
def generalized_assignment_master_feasible_set
    (t : Fin m → Fin n → ℝ)
    (T : Fin n → ℝ) :
    Set (Fin n → (Fin m → Bool) → ℝ) :=
  {lam |
    generalized_assignment_master_feasible_on
      (generalized_assignment_block_patterns t T) lam}

/-- Membership in `generalized_assignment_master_feasible_set t T` is exactly feasibility for the
full Dantzig-Wolfe master problem on the canonical block-pattern family. -/
theorem mem_generalized_assignment_master_feasible_set_iff
    {t : Fin m → Fin n → ℝ}
    {T : Fin n → ℝ}
    {lam : Fin n → (Fin m → Bool) → ℝ} :
    lam ∈ generalized_assignment_master_feasible_set t T ↔
      generalized_assignment_master_feasible_on
        (generalized_assignment_block_patterns t T) lam :=
  Iff.rfl

/-- The objective values attained by feasible restricted master solutions on the selected
subfamilies `S_j`. -/
def restricted_master_objective_values
    (c : Fin m → Fin n → ℝ)
    (t : Fin m → Fin n → ℝ)
    (T : Fin n → ℝ)
    (S : Fin n → Finset (Fin m → Bool)) : Set ℝ :=
  master_objective c S '' restricted_master_feasible_set t T S

/-- The objective values attained by feasible full-master solutions on the canonical block
families `Q_j`. -/
def generalized_assignment_master_objective_values
    (c : Fin m → Fin n → ℝ)
    (t : Fin m → Fin n → ℝ)
    (T : Fin n → ℝ) : Set ℝ :=
  master_objective c (generalized_assignment_block_patterns t T) ''
    generalized_assignment_master_feasible_set t T

/-- On a restricted master feasible point, the restricted and full Dantzig-Wolfe objectives
coincide. -/
theorem restricted_master_objective_eq_relaxation_objective
    (c : Fin m → Fin n → ℝ)
    (t : Fin m → Fin n → ℝ)
    (T : Fin n → ℝ)
    (S : Fin n → Finset (Fin m → Bool))
    (hsubset : ∀ j, S j ⊆ generalized_assignment_block_patterns t T j)
    (lam : Fin n → (Fin m → Bool) → ℝ)
    (hfeas : restricted_master_feasible t T S lam) :
    master_objective c S lam =
      master_objective c (generalized_assignment_block_patterns t T) lam := by
  -- Expand restricted feasibility so the proof can zero out every column outside `S j`.
  rcases (restricted_master_feasible_iff.mp hfeas) with ⟨_hmaster, hzero⟩
  -- Compare the restricted and full block sums one block at a time.
  unfold master_objective
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact Finset.sum_subset (hsubset j) (fun z hz hnotmem ↦ by
    simp [hzero j z hz hnotmem])

/-- The dual objective value `∑_i π_i + ∑_j σ_j` for the master problem. -/
def master_dual_objective
    (pi : Fin m → ℝ)
    (sigma : Fin n → ℝ) : ℝ :=
  (∑ i, pi i) + ∑ j, sigma j

/-- Dual feasibility for a master problem indexed by a family of column subsets `A_j`. -/
def master_dual_feasible_on
    (c : Fin m → Fin n → ℝ)
    (A : Fin n → Finset (Fin m → Bool))
    (pi : Fin m → ℝ)
    (sigma : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ pi i) ∧
    ∀ j z, z ∈ A j → column_profit c j z ≤ (∑ i, pi i * bool_entry (z i)) + sigma j

/-- Unfolding characterization of dual feasibility for a master problem indexed by `A_j`. -/
theorem master_dual_feasible_on_iff
    {c : Fin m → Fin n → ℝ}
    {A : Fin n → Finset (Fin m → Bool)}
    {pi : Fin m → ℝ}
    {sigma : Fin n → ℝ} :
    master_dual_feasible_on c A pi sigma ↔
      (∀ i, 0 ≤ pi i) ∧
        ∀ j z, z ∈ A j → column_profit c j z ≤ (∑ i, pi i * bool_entry (z i)) + sigma j :=
  Iff.rfl

/-- The reduced cost of the Dantzig-Wolfe column variable indexed by `z ∈ Q_j`. -/
def column_reduced_cost
    (c : Fin m → Fin n → ℝ)
    (pi : Fin m → ℝ)
    (sigma : Fin n → ℝ)
    (j : Fin n)
    (z : Fin m → Bool) : ℝ :=
  -sigma j + ∑ i, (c i j - pi i) * bool_entry (z i)

/-- The reduced-cost values attained on the canonical block family `Q_j`. -/
def column_reduced_cost_values
    (t : Fin m → Fin n → ℝ)
    (T : Fin n → ℝ)
    (c : Fin m → Fin n → ℝ)
    (pi : Fin m → ℝ)
    (sigma : Fin n → ℝ)
    (j : Fin n) : Set ℝ :=
  column_reduced_cost c pi sigma j ''
    (generalized_assignment_block_patterns t T j : Set (Fin m → Bool))

/-- Any feasible block pattern contributes its reduced cost to
`column_reduced_cost_values t T c pi sigma j`. -/
theorem column_reduced_cost_mem_values
    {t : Fin m → Fin n → ℝ}
    {T : Fin n → ℝ}
    {c : Fin m → Fin n → ℝ}
    {pi : Fin m → ℝ}
    {sigma : Fin n → ℝ}
    {j : Fin n}
    {z : Fin m → Bool}
    (hz : z ∈ generalized_assignment_block_patterns t T j) :
    column_reduced_cost c pi sigma j z ∈ column_reduced_cost_values t T c pi sigma j :=
  ⟨z, hz, rfl⟩

/-- Helper for Example 8.17: nonpositive reduced cost is exactly the full-master dual inequality
for the corresponding column. -/
lemma column_reduced_cost_nonpos_iff
    (c : Fin m → Fin n → ℝ)
    (pi : Fin m → ℝ)
    (sigma : Fin n → ℝ)
    (j : Fin n)
    (z : Fin m → Bool) :
    column_reduced_cost c pi sigma j z ≤ 0 ↔
      column_profit c j z ≤ (∑ i, pi i * bool_entry (z i)) + sigma j := by
  -- Rewrite the reduced cost into the profit-minus-dual-slack normal form.
  unfold column_reduced_cost column_profit
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hrewrite :
      -sigma j + (∑ x, c x j * bool_entry (z x) - ∑ x, pi x * bool_entry (z x)) =
        (∑ i, c i j * bool_entry (z i)) - ((∑ i, pi i * bool_entry (z i)) + sigma j) := by
    ring
  rw [hrewrite]
  exact sub_nonpos

/-- If `zeta j` is the maximum reduced cost over the capacity-feasible binary patterns in `Q_j`
and these pricing values are all nonpositive, then the optimal dual solution of the restricted
master problem is feasible for the dual of the full Dantzig-Wolfe relaxation. -/
theorem pricing_value_nonpositive_implies_relaxation_dual_feasible
    (t : Fin m → Fin n → ℝ)
    (T : Fin n → ℝ)
    (c : Fin m → Fin n → ℝ)
    (S : Fin n → Finset (Fin m → Bool))
    (pi : Fin m → ℝ)
    (sigma : Fin n → ℝ)
    (zeta : Fin n → ℝ)
    (hdual : master_dual_feasible_on c S pi sigma)
    (hpricing :
      ∀ j,
        IsGreatest (column_reduced_cost_values t T c pi sigma j) (zeta j))
    (hnonpos : ∀ j, zeta j ≤ 0) :
    master_dual_feasible_on c (generalized_assignment_block_patterns t T) pi sigma := by
  -- Keep the nonnegativity part from the restricted dual and reprove the column inequalities
  -- from the pricing maxima.
  rcases (master_dual_feasible_on_iff.mp hdual) with ⟨hpi, _hSdual⟩
  refine (master_dual_feasible_on_iff).2 ?_
  constructor
  · exact hpi
  · intro j z hz
    have hzval :
        column_reduced_cost c pi sigma j z ∈
          column_reduced_cost_values t T c pi sigma j :=
      column_reduced_cost_mem_values hz
    have hred_le_zeta : column_reduced_cost c pi sigma j z ≤ zeta j :=
      (hpricing j).2 hzval
    have hred_nonpos : column_reduced_cost c pi sigma j z ≤ 0 :=
      le_trans hred_le_zeta (hnonpos j)
    exact (column_reduced_cost_nonpos_iff c pi sigma j z).mp hred_nonpos

/-- Helper for Example 8.17: every feasible primal-dual pair for a master owner `A` satisfies
the usual weak-duality inequality. -/
lemma master_weak_duality_on
    (c : Fin m → Fin n → ℝ)
    (A : Fin n → Finset (Fin m → Bool))
    (lam : Fin n → (Fin m → Bool) → ℝ)
    (pi : Fin m → ℝ)
    (sigma : Fin n → ℝ)
    (hfeas : generalized_assignment_master_feasible_on A lam)
    (hdual : master_dual_feasible_on c A pi sigma) :
    master_objective c A lam ≤ master_dual_objective pi sigma := by
  -- Unpack the primal and dual side conditions once so the main inequality can follow a
  -- single calculation.
  rcases (generalized_assignment_master_feasible_on_iff.mp hfeas) with
    ⟨hlam_nonneg, hlink, hconvex⟩
  rcases (master_dual_feasible_on_iff.mp hdual) with ⟨hpi_nonneg, hcol⟩
  have hprofit_by_block :
      ∀ j,
        ∑ z ∈ A j, (∑ i, pi i * bool_entry (z i)) * lam j z =
          ∑ i, pi i * generalized_assignment_dw_point A lam i j := by
    intro j
    -- Commute the block and item sums so the projected point `generalized_assignment_dw_point`
    -- appears explicitly.
    calc
      ∑ z ∈ A j, (∑ i, pi i * bool_entry (z i)) * lam j z
        = ∑ z ∈ A j, ∑ i, (pi i * bool_entry (z i)) * lam j z := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            simpa using
              (Finset.sum_mul Finset.univ (fun i ↦ pi i * bool_entry (z i)) (lam j z))
      _ = ∑ i, ∑ z ∈ A j, (pi i * bool_entry (z i)) * lam j z := by
            rw [Finset.sum_comm]
      _ = ∑ i, pi i * generalized_assignment_dw_point A lam i j := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              ∑ z ∈ A j, (pi i * bool_entry (z i)) * lam j z
                = ∑ z ∈ A j, pi i * (bool_entry (z i) * lam j z) := by
                    refine Finset.sum_congr rfl ?_
                    intro z hz
                    ring
              _ = pi i * ∑ z ∈ A j, bool_entry (z i) * lam j z := by
                    simpa using
                      (Finset.mul_sum (A j) (fun z ↦ bool_entry (z i) * lam j z) (pi i)).symm
              _ = pi i * generalized_assignment_dw_point A lam i j := by
                    rw [generalized_assignment_dw_point]
  have hprofit_part :
      ∑ j, ∑ z ∈ A j, (∑ i, pi i * bool_entry (z i)) * lam j z =
        ∑ i, pi i * (∑ j, generalized_assignment_dw_point A lam i j) := by
    -- Sum the blockwise normal forms and then commute the remaining finite sums.
    calc
      ∑ j, ∑ z ∈ A j, (∑ i, pi i * bool_entry (z i)) * lam j z
        = ∑ j, ∑ i, pi i * generalized_assignment_dw_point A lam i j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact hprofit_by_block j
      _ = ∑ i, ∑ j, pi i * generalized_assignment_dw_point A lam i j := by
            rw [Finset.sum_comm]
      _ = ∑ i, pi i * (∑ j, generalized_assignment_dw_point A lam i j) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using
              (Finset.mul_sum Finset.univ
                (fun j ↦ generalized_assignment_dw_point A lam i j) (pi i)).symm
  have hsigma_part :
      ∑ j, ∑ z ∈ A j, sigma j * lam j z =
        ∑ j, sigma j * (∑ z ∈ A j, lam j z) := by
    -- Factor the constant dual variable `sigma j` out of each block sum.
    refine Finset.sum_congr rfl ?_
    intro j hj
    simpa using (Finset.mul_sum (A j) (fun z ↦ lam j z) (sigma j)).symm
  have hpi_bound :
      ∑ i, pi i * (∑ j, generalized_assignment_dw_point A lam i j) ≤ ∑ i, pi i := by
    -- The linking inequalities bound each projected coordinate by `1`, and `pi_i ≥ 0`
    -- preserves that bound under multiplication.
    refine Finset.sum_le_sum ?_
    intro i hi
    simpa using mul_le_mul_of_nonneg_left (hlink i) (hpi_nonneg i)
  have hsigma_eq :
      ∑ j, sigma j * (∑ z ∈ A j, lam j z) = ∑ j, sigma j := by
    -- The convexity equation makes each block mass equal to `1`.
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hconvex j]
    ring
  calc
    master_objective c A lam
      = ∑ j, ∑ z ∈ A j, column_profit c j z * lam j z := rfl
    _ ≤ ∑ j, ∑ z ∈ A j, (((∑ i, pi i * bool_entry (z i)) + sigma j) * lam j z) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          refine Finset.sum_le_sum ?_
          intro z hz
          exact mul_le_mul_of_nonneg_right (hcol j z hz) (hlam_nonneg j z hz)
    _ = ∑ j,
          ((∑ z ∈ A j, (∑ i, pi i * bool_entry (z i)) * lam j z) +
            ∑ z ∈ A j, sigma j * lam j z) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp_rw [add_mul]
          exact Finset.sum_add_distrib
    _ = (∑ j, ∑ z ∈ A j, (∑ i, pi i * bool_entry (z i)) * lam j z) +
          ∑ j, ∑ z ∈ A j, sigma j * lam j z := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i, pi i * (∑ j, generalized_assignment_dw_point A lam i j)) +
          ∑ j, sigma j * (∑ z ∈ A j, lam j z) := by
          rw [hprofit_part, hsigma_part]
    _ ≤ (∑ i, pi i) + ∑ j, sigma j := by
          exact add_le_add hpi_bound (le_of_eq hsigma_eq)
    _ = master_dual_objective pi sigma := by
          rw [master_dual_objective]

/-- Example 8.17 (1): if every pricing problem has value `zeta_j ≤ 0`, then any optimal solution
to the restricted master problem is also optimal for the full Dantzig-Wolfe relaxation. -/
theorem example_8_17_master_optimal_is_relaxation_optimal
    (t : Fin m → Fin n → ℝ)
    (T : Fin n → ℝ)
    (c : Fin m → Fin n → ℝ)
    (S : Fin n → Finset (Fin m → Bool))
    (hsubset : ∀ j, S j ⊆ generalized_assignment_block_patterns t T j)
    (pi : Fin m → ℝ)
    (sigma : Fin n → ℝ)
    (zeta : Fin n → ℝ)
    (hdual : master_dual_feasible_on c S pi sigma)
    (hpricing :
      ∀ j,
        IsGreatest (column_reduced_cost_values t T c pi sigma j) (zeta j))
    (hnonpos : ∀ j, zeta j ≤ 0)
    (lamStar : Fin n → (Fin m → Bool) → ℝ)
    (hfeas : restricted_master_feasible t T S lamStar)
    (hopt : IsGreatest
      (restricted_master_objective_values c t T S)
      (master_objective c S lamStar))
    (hobj : master_objective c S lamStar = master_dual_objective pi sigma) :
    IsGreatest
      (generalized_assignment_master_objective_values c t T)
      (master_objective c (generalized_assignment_block_patterns t T) lamStar) := by
  -- Route correction: the final theorem is easiest once the restricted objective is identified
  -- with the full objective and weak duality is available for the full owner.
  let _ :
      IsGreatest (restricted_master_objective_values c t T S)
        (master_objective c S lamStar) := hopt
  have hfeas_full :
      generalized_assignment_master_feasible_on
        (generalized_assignment_block_patterns t T) lamStar :=
    (restricted_master_feasible_iff.mp hfeas).1
  have hdual_full :
      master_dual_feasible_on c (generalized_assignment_block_patterns t T) pi sigma :=
    pricing_value_nonpositive_implies_relaxation_dual_feasible
      t T c S pi sigma zeta hdual hpricing hnonpos
  have hobj_full :
      master_objective c (generalized_assignment_block_patterns t T) lamStar =
        master_dual_objective pi sigma := by
    -- Rewrite the restricted-master objective in `hobj` to the full-owner objective.
    calc
      master_objective c (generalized_assignment_block_patterns t T) lamStar =
          master_objective c S lamStar := by
            symm
            exact
              restricted_master_objective_eq_relaxation_objective
                c t T S hsubset lamStar hfeas
      _ = master_dual_objective pi sigma := hobj
  refine ⟨?_, ?_⟩
  · -- The candidate value is attained by the restricted optimum itself, viewed in the full owner.
    refine ⟨lamStar, ?_, rfl⟩
    exact (mem_generalized_assignment_master_feasible_set_iff).2 hfeas_full
  · intro y hy
    rcases hy with ⟨lam, hlam, rfl⟩
    -- Every feasible full-master value is bounded above by the common dual objective value.
    calc
      master_objective c (generalized_assignment_block_patterns t T) lam ≤
          master_dual_objective pi sigma :=
        master_weak_duality_on c (generalized_assignment_block_patterns t T) lam pi sigma
          ((mem_generalized_assignment_master_feasible_set_iff).mp hlam) hdual_full
      _ = master_objective c (generalized_assignment_block_patterns t T) lamStar := by
          exact hobj_full.symm

/-- Example 8.17 (2): if the `j`-th pricing problem has positive value and `zStar` attains that
value, then the corresponding column variable `lambda_(zStar)^j` has positive reduced cost. -/
theorem example_8_17_positive_pricing_value_gives_positive_reduced_cost
    (t : Fin m → Fin n → ℝ)
    (T : Fin n → ℝ)
    (c : Fin m → Fin n → ℝ)
    (pi : Fin m → ℝ)
    (sigma : Fin n → ℝ)
    (j : Fin n)
    (zeta : ℝ)
    (zStar : Fin m → Bool)
    (hpricing :
      IsGreatest (column_reduced_cost_values t T c pi sigma j) zeta)
    (hpos : 0 < zeta)
    (hzStar : zStar ∈ generalized_assignment_block_patterns t T j ∧
      column_reduced_cost c pi sigma j zStar = zeta) :
    0 < column_reduced_cost c pi sigma j zStar := by
  -- The source statement includes the pricing optimality witness, but positivity only needs the
  -- equality identifying the witness value.
  let _ : IsGreatest (column_reduced_cost_values t T c pi sigma j) zeta := hpricing
  -- The witness equality identifies the reduced cost with the positive pricing value.
  simpa [hzStar.2] using hpos

end Example817
