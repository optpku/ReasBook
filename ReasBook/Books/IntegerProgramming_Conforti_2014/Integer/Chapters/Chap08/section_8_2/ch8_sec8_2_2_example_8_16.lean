import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Order
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_2.ch8_sec8_2_1_example_8_15

open scoped BigOperators

section Example816

universe u

variable {α : Type u} {m : ℕ}

/-- The restricted master problem attached to the pattern subset `S'` is feasible at `x` when
the covering inequalities hold, every variable is nonnegative, and the variables outside `S'`
vanish. -/
def cutting_stock_master_feasible
    (S' : Finset α) (pattern : α → Fin m → ℕ) (b : Fin m → ℝ) (x : α → ℝ) : Prop :=
  (∀ i, b i ≤ Finset.sum S' (fun a ↦ (pattern a i : ℝ) * x a)) ∧
    (∀ a, 0 ≤ x a) ∧
      ∀ a ∉ S', x a = 0

/-- Unfolding characterization of restricted master feasibility. -/
theorem cutting_stock_master_feasible_iff
    {S' : Finset α} {pattern : α → Fin m → ℕ} {b : Fin m → ℝ} {x : α → ℝ} :
    cutting_stock_master_feasible S' pattern b x ↔
      (∀ i, b i ≤ Finset.sum S' (fun a ↦ (pattern a i : ℝ) * x a)) ∧
        (∀ a, 0 ≤ x a) ∧
          ∀ a ∉ S', x a = 0 :=
  Iff.rfl

/-- The feasible set of the restricted master problem on `S'`. -/
def cutting_stock_master_feasible_set
    (S' : Finset α) (pattern : α → Fin m → ℕ) (b : Fin m → ℝ) : Set (α → ℝ) :=
  {x | cutting_stock_master_feasible S' pattern b x}

/-- Membership in `cutting_stock_master_feasible_set S' pattern b` is exactly restricted master
feasibility. -/
theorem mem_cutting_stock_master_feasible_set_iff
    {S' : Finset α} {pattern : α → Fin m → ℕ} {b : Fin m → ℝ} {x : α → ℝ} :
    x ∈ cutting_stock_master_feasible_set S' pattern b ↔
      cutting_stock_master_feasible S' pattern b x :=
  Iff.rfl

/-- The dual of the restricted master problem is feasible at `π` when every pattern in `S'`
satisfies its reduced-cost inequality and `π` is coordinatewise nonnegative. -/
def cutting_stock_master_dual_feasible
    (S' : Finset α) (pattern : α → Fin m → ℕ) (π : Fin m → ℝ) : Prop :=
  (∀ a ∈ S', ∑ i, (pattern a i : ℝ) * π i ≤ 1) ∧
    ∀ i, 0 ≤ π i

/-- Unfolding characterization of restricted master dual feasibility. -/
theorem cutting_stock_master_dual_feasible_iff
    {S' : Finset α} {pattern : α → Fin m → ℕ} {π : Fin m → ℝ} :
    cutting_stock_master_dual_feasible S' pattern π ↔
      (∀ a ∈ S', ∑ i, (pattern a i : ℝ) * π i ≤ 1) ∧
        ∀ i, 0 ≤ π i :=
  Iff.rfl

/-- The dual-feasible set of the restricted master problem on `S'`. -/
def cutting_stock_master_dual_feasible_set
    (S' : Finset α) (pattern : α → Fin m → ℕ) : Set (Fin m → ℝ) :=
  {π | cutting_stock_master_dual_feasible S' pattern π}

/-- Membership in `cutting_stock_master_dual_feasible_set S' pattern` is exactly restricted dual
feasibility. -/
theorem mem_cutting_stock_master_dual_feasible_set_iff
    {S' : Finset α} {pattern : α → Fin m → ℕ} {π : Fin m → ℝ} :
    π ∈ cutting_stock_master_dual_feasible_set S' pattern ↔
      cutting_stock_master_dual_feasible S' pattern π :=
  Iff.rfl

/-- The restricted master objective is the total mass assigned to the active pattern set `S'`. -/
def cutting_stock_master_objective
    (S' : Finset α) (x : α → ℝ) : ℝ :=
  Finset.sum S' x

/-- The dual restricted master objective is `∑ i, b_i π_i`. -/
def cutting_stock_master_dual_objective
    (b : Fin m → ℝ) (π : Fin m → ℝ) : ℝ :=
  ∑ i, b i * π i

/-- A full cutting-stock master solution assigns finitely supported real weights to the canonical
pattern owner `cutting_patterns W w`. -/
abbrev cutting_stock_pattern_assignment (w : Fin m → ℕ) (W : ℕ) :=
  cutting_patterns W w →₀ ℝ

/-- Feasibility for the full cutting-stock master problem on the canonical pattern owner. -/
def cutting_stock_full_master_feasible
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℝ)
    (x : cutting_stock_pattern_assignment w W) : Prop :=
  (∀ i, b i ≤ x.sum (fun z r ↦ (z.1 i : ℝ) * r)) ∧
    ∀ z, 0 ≤ x z

/-- Unfolding characterization of full cutting-stock master feasibility. -/
theorem cutting_stock_full_master_feasible_iff
    {w : Fin m → ℕ} {W : ℕ} {b : Fin m → ℝ} {x : cutting_stock_pattern_assignment w W} :
    cutting_stock_full_master_feasible w W b x ↔
      (∀ i, b i ≤ x.sum (fun z r ↦ (z.1 i : ℝ) * r)) ∧
        ∀ z, 0 ≤ x z :=
  Iff.rfl

/-- The feasible set of the full cutting-stock master problem on `cutting_patterns W w`. -/
def cutting_stock_full_master_feasible_set
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℝ) :
    Set (cutting_stock_pattern_assignment w W) :=
  {x | cutting_stock_full_master_feasible w W b x}

/-- Membership in `cutting_stock_full_master_feasible_set w W b` is exactly full master
feasibility. -/
theorem mem_cutting_stock_full_master_feasible_set_iff
    {w : Fin m → ℕ} {W : ℕ} {b : Fin m → ℝ} {x : cutting_stock_pattern_assignment w W} :
    x ∈ cutting_stock_full_master_feasible_set w W b ↔
      cutting_stock_full_master_feasible w W b x :=
  Iff.rfl

/-- The full master objective counts the total mass assigned to the canonical pattern owner. -/
def cutting_stock_full_master_objective
    {w : Fin m → ℕ} {W : ℕ} (x : cutting_stock_pattern_assignment w W) : ℝ :=
  x.sum (fun _ r ↦ r)

/-- The objective values attained by feasible full-master solutions on `cutting_patterns W w`. -/
def cutting_stock_full_master_objective_values
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℝ) : Set ℝ :=
  cutting_stock_full_master_objective '' cutting_stock_full_master_feasible_set w W b

/-- The pricing objective is `∑ i, π_i z_i`. -/
def cutting_stock_pricing_objective
    (π : Fin m → ℝ) (z : Fin m → ℕ) : ℝ :=
  ∑ i, π i * (z i : ℝ)

/-- The dual of the full cutting-stock master problem is feasible at `π` when every canonical
cutting pattern satisfies its reduced-cost inequality and `π` is coordinatewise nonnegative. -/
def cutting_stock_master_dual_feasible_on_cutting_patterns
    (w : Fin m → ℕ) (W : ℕ) (π : Fin m → ℝ) : Prop :=
  (∀ z ∈ cutting_patterns W w, cutting_stock_pricing_objective π z ≤ 1) ∧
    ∀ i, 0 ≤ π i

/-- Unfolding characterization of full dual feasibility on `cutting_patterns W w`. -/
theorem cutting_stock_master_dual_feasible_on_cutting_patterns_iff
    {w : Fin m → ℕ} {W : ℕ} {π : Fin m → ℝ} :
    cutting_stock_master_dual_feasible_on_cutting_patterns w W π ↔
      (∀ z ∈ cutting_patterns W w, cutting_stock_pricing_objective π z ≤ 1) ∧
        ∀ i, 0 ≤ π i :=
  Iff.rfl

/-- The objective values attained by feasible restricted master solutions on `S'`. -/
def cutting_stock_master_objective_values
    (S' : Finset α) (pattern : α → Fin m → ℕ) (b : Fin m → ℝ) : Set ℝ :=
  cutting_stock_master_objective S' '' cutting_stock_master_feasible_set S' pattern b

/-- The objective values attained by dual-feasible restricted master solutions on `S'`. -/
def cutting_stock_master_dual_objective_values
    (S' : Finset α) (pattern : α → Fin m → ℕ) (b : Fin m → ℝ) : Set ℝ :=
  cutting_stock_master_dual_objective b '' cutting_stock_master_dual_feasible_set S' pattern

/-- The objective values attained on the canonical cutting-pattern owner `cutting_patterns W w`. -/
def cutting_stock_pricing_objective_values
    (w : Fin m → ℕ) (W : ℕ) (π : Fin m → ℝ) : Set ℝ :=
  cutting_stock_pricing_objective π '' cutting_patterns W w

/-- If `x` vanishes outside `S'`, then enlarging the active pattern set from `S'` to `S` does not
change the restricted master objective. -/
theorem cutting_stock_master_objective_eq_of_zero_outside
    {S S' : Finset α} {x : α → ℝ}
    (hsubset : S' ⊆ S)
    (hzero : ∀ a ∉ S', x a = 0) :
    cutting_stock_master_objective S x = cutting_stock_master_objective S' x := by
  classical
  have hsum : Finset.sum S' x = Finset.sum S x := by
    refine Finset.sum_subset hsubset ?_
    intro a haS haS'
    exact hzero a haS'
  rw [cutting_stock_master_objective, cutting_stock_master_objective]
  exact hsum.symm

/-- If a vector is feasible for the restricted master problem on `S'`, then it is also feasible
for the master problem on any larger pattern set `S` containing `S'`. -/
theorem cutting_stock_master_feasible_mono
    {S S' : Finset α} {pattern : α → Fin m → ℕ} {b : Fin m → ℝ} {x : α → ℝ}
    (hsubset : S' ⊆ S)
    (hx : cutting_stock_master_feasible S' pattern b x) :
    cutting_stock_master_feasible S pattern b x := by
  classical
  rcases hx with ⟨hcover, hnonneg, hzero⟩
  refine ⟨?_, hnonneg, ?_⟩
  · intro i
    calc
      b i ≤ Finset.sum S' (fun a ↦ (pattern a i : ℝ) * x a) := hcover i
      _ = Finset.sum S (fun a ↦ (pattern a i : ℝ) * x a) := by
        refine Finset.sum_subset hsubset ?_
        intro a haS haS'
        rw [hzero a haS']
        simp
  · intro a haS
    exact hzero a (fun haS' ↦ haS (hsubset haS'))

/-- The restricted master solution on `S` induces a finitely supported solution on the canonical
pattern owner by summing the weights of duplicate pattern indices. -/
noncomputable def cutting_stock_master_to_full_assignment
    (S : Finset α) (pattern : α → Fin m → ℕ) (w : Fin m → ℕ) (W : ℕ)
    (hpattern_mem : ∀ a ∈ S, pattern a ∈ cutting_patterns W w)
    (x : α → ℝ) : cutting_stock_pattern_assignment w W :=
  Finset.sum S.attach fun a ↦ Finsupp.single ⟨pattern a, hpattern_mem a a.2⟩ (x a)

/-- Evaluating the canonical full assignment induced from `S` collects exactly the coefficients of
those indices in `S` that encode the same cutting pattern. -/
theorem cutting_stock_master_to_full_assignment_apply
    {S : Finset α} {pattern : α → Fin m → ℕ} {w : Fin m → ℕ} {W : ℕ}
    (hpattern_mem : ∀ a ∈ S, pattern a ∈ cutting_patterns W w)
    (x : α → ℝ) (z : cutting_patterns W w) :
    cutting_stock_master_to_full_assignment S pattern w W hpattern_mem x z =
      Finset.sum S.attach fun a ↦ if pattern a = z then x a else 0 := by
  classical
  rw [cutting_stock_master_to_full_assignment, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl ?_
  intro a ha
  by_cases hEq : pattern a = z
  · have hSubtype : (⟨pattern a, hpattern_mem a a.2⟩ : cutting_patterns W w) = z :=
      Subtype.ext hEq
    simp [hEq]
  · have hSubtype : (⟨pattern a, hpattern_mem a a.2⟩ : cutting_patterns W w) ≠ z := by
      intro hz
      apply hEq
      exact congrArg Subtype.val hz
    simp [hEq, hSubtype]

/-- The induced canonical full assignment has the same objective value as the restricted master
solution on `S`. -/
theorem cutting_stock_master_to_full_assignment_objective
    {S : Finset α} {pattern : α → Fin m → ℕ} {w : Fin m → ℕ} {W : ℕ}
    (hpattern_mem : ∀ a ∈ S, pattern a ∈ cutting_patterns W w)
    (x : α → ℝ) :
    cutting_stock_full_master_objective
        (cutting_stock_master_to_full_assignment S pattern w W hpattern_mem x) =
      cutting_stock_master_objective S x := by
  classical
  rw [cutting_stock_master_to_full_assignment]
  rw [show cutting_stock_master_objective S x = Finset.sum S.attach (fun a ↦ x a) by
    simpa [cutting_stock_master_objective] using (Finset.sum_attach S fun a ↦ x a).symm]
  induction S.attach using Finset.induction_on with
  | empty =>
      simp [cutting_stock_full_master_objective]
  | insert a t ha ih =>
      simp [Finset.sum_insert, ha, cutting_stock_full_master_objective, Finsupp.sum_add_index']
      simpa [cutting_stock_full_master_objective] using ih

/-- The full covering sum of the induced canonical assignment agrees with the restricted covering
sum on the finite index family `S`. -/
theorem cutting_stock_master_to_full_assignment_cover_sum
    {S : Finset α} {pattern : α → Fin m → ℕ} {w : Fin m → ℕ} {W : ℕ}
    (hpattern_mem : ∀ a ∈ S, pattern a ∈ cutting_patterns W w)
    (x : α → ℝ) (i : Fin m) :
    (cutting_stock_master_to_full_assignment S pattern w W hpattern_mem x).sum
        (fun z r ↦ (z.1 i : ℝ) * r) =
      Finset.sum S (fun a ↦ (pattern a i : ℝ) * x a) := by
  classical
  rw [cutting_stock_master_to_full_assignment]
  rw [show Finset.sum S (fun a ↦ (pattern a i : ℝ) * x a) =
      Finset.sum S.attach (fun a ↦ (pattern a i : ℝ) * x a) by
    simpa using (Finset.sum_attach S fun a ↦ (pattern a i : ℝ) * x a).symm]
  induction S.attach using Finset.induction_on with
  | empty =>
      simp
  | insert a t ha ih =>
      simp [Finset.sum_insert, ha, Finsupp.sum_add_index', mul_add]
      simpa using ih

/-- A restricted master feasible solution becomes feasible for the canonical full master owner
after aggregating duplicate pattern indices. -/
theorem cutting_stock_master_to_full_assignment_feasible
    {S : Finset α} {pattern : α → Fin m → ℕ} {b : Fin m → ℝ}
    {w : Fin m → ℕ} {W : ℕ} {x : α → ℝ}
    (hx : cutting_stock_master_feasible S pattern b x)
    (hpattern_mem : ∀ a ∈ S, pattern a ∈ cutting_patterns W w) :
    cutting_stock_full_master_feasible w W b
      (cutting_stock_master_to_full_assignment S pattern w W hpattern_mem x) := by
  rcases hx with ⟨hcover, hnonneg, _hzero⟩
  refine ⟨?_, ?_⟩
  · intro i
    rw [cutting_stock_master_to_full_assignment_cover_sum hpattern_mem x i]
    exact hcover i
  · intro z
    rw [cutting_stock_master_to_full_assignment_apply hpattern_mem x z]
    haveI : DecidableEq ↥S := Classical.decEq _
    induction S.attach using Finset.induction_on with
    | empty =>
        simp
    | insert a t ha ih =>
        by_cases hEq : pattern a = z
        · simpa [Finset.sum_insert, ha, hEq] using add_nonneg (hnonneg a) ih
        · simp [Finset.sum_insert, ha, hEq, ih]

/-- If an optimal pricing solution has value at most `1`, then the corresponding dual vector is
feasible for every pattern in the canonical cutting-pattern owner `cutting_patterns W w`. -/
theorem cutting_stock_master_dual_feasible_on_cutting_patterns_of_pricing_optimum_le_one
    (w : Fin m → ℕ) (W : ℕ) (π : Fin m → ℝ)
    (zStar : Fin m → ℕ)
    (hzStar :
      IsGreatest
        (cutting_stock_pricing_objective_values w W π)
        (cutting_stock_pricing_objective π zStar))
    (hζ : cutting_stock_pricing_objective π zStar ≤ 1)
    (hπ_nonneg : ∀ i, 0 ≤ π i) :
    cutting_stock_master_dual_feasible_on_cutting_patterns w W π := by
  refine ⟨?_, hπ_nonneg⟩
  intro z hz
  have hvalue_mem :
      cutting_stock_pricing_objective π z ∈ cutting_stock_pricing_objective_values w W π := by
    exact ⟨z, hz, rfl⟩
  exact le_trans (hzStar.2 hvalue_mem) hζ

/-- Every feasible pair for the full cutting-stock master problem and its full dual satisfies weak
duality. -/
theorem cutting_stock_full_master_weak_duality
    {w : Fin m → ℕ} {W : ℕ} {b : Fin m → ℝ}
    {x : cutting_stock_pattern_assignment w W} {π : Fin m → ℝ}
    (hx : cutting_stock_full_master_feasible w W b x)
    (hπ : cutting_stock_master_dual_feasible_on_cutting_patterns w W π) :
    cutting_stock_master_dual_objective b π ≤ cutting_stock_full_master_objective x := by
  rcases hx with ⟨hcover, hx_nonneg⟩
  rcases hπ with ⟨hpricing, hπ_nonneg⟩
  calc
    cutting_stock_master_dual_objective b π
      = ∑ i, b i * π i := rfl
    _ ≤ ∑ i, (x.sum (fun z r ↦ (z.1 i : ℝ) * r)) * π i := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      exact mul_le_mul_of_nonneg_right (hcover i) (hπ_nonneg i)
    _ = Finset.sum x.support (fun z ↦ ∑ i, (z.1 i : ℝ) * x z * π i) := by
      simp only [Finsupp.sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = Finset.sum x.support (fun z ↦ ∑ i, π i * (z.1 i : ℝ) * x z) := by
      refine Finset.sum_congr rfl fun z hz ↦ ?_
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      calc
        (z.1 i : ℝ) * x z * π i = ((z.1 i : ℝ) * x z) * π i := by rw [mul_assoc]
        _ = π i * ((z.1 i : ℝ) * x z) := by rw [mul_comm]
        _ = π i * (z.1 i : ℝ) * x z := by rw [mul_assoc]
    _ = Finset.sum x.support (fun z ↦ (∑ i, π i * (z.1 i : ℝ)) * x z) := by
      refine Finset.sum_congr rfl fun z hz ↦ ?_
      simpa [mul_assoc] using
        (Finset.sum_mul Finset.univ (fun i ↦ π i * (z.1 i : ℝ)) (x z)).symm
    _ = x.sum (fun z r ↦ cutting_stock_pricing_objective π z * r) := by
      simp [Finsupp.sum, cutting_stock_pricing_objective]
    _ ≤ x.sum (fun z r ↦ 1 * r) := by
      refine Finsupp.sum_le_sum ?_
      intro z hz
      exact mul_le_mul_of_nonneg_right (hpricing z z.2) (hx_nonneg z)
    _ = cutting_stock_full_master_objective x := by
      simp [cutting_stock_full_master_objective, Finsupp.sum]

/-- Example 8.16 (1). If the pricing optimum satisfies `ζ ≤ 1`, `x̄` is feasible for the
restricted master problem, and the coordinatewise nonnegative dual vector `π̄` has the same
objective value, then the induced finitely supported assignment on the canonical pattern owner
`cutting_patterns W w` is already optimal for the full linear-programming relaxation of the
cutting-stock problem. -/
theorem cutting_stock_master_optimal_for_full_lp_of_pricing_value_le_one
    (S' : Finset α) (pattern : α → Fin m → ℕ) (b : Fin m → ℝ)
    (w : Fin m → ℕ) (W : ℕ)
    (xBar : α → ℝ) (πBar : Fin m → ℝ) (zStar : Fin m → ℕ)
    (hxBar_feas : cutting_stock_master_feasible S' pattern b xBar)
    (hπBar_nonneg : ∀ i, 0 ≤ πBar i)
    (hzStar :
      IsGreatest
        (cutting_stock_pricing_objective_values w W πBar)
        (cutting_stock_pricing_objective πBar zStar))
    (hζ : cutting_stock_pricing_objective πBar zStar ≤ 1)
    (hstrong :
      cutting_stock_master_objective S' xBar = cutting_stock_master_dual_objective b πBar)
    (hpattern_mem : ∀ a ∈ S', pattern a ∈ cutting_patterns W w) :
    IsLeast
      (cutting_stock_full_master_objective_values w W b)
      (cutting_stock_full_master_objective
        (cutting_stock_master_to_full_assignment S' pattern w W hpattern_mem xBar)) := by
  have hxBar_full : cutting_stock_full_master_feasible w W b
      (cutting_stock_master_to_full_assignment S' pattern w W hpattern_mem xBar) :=
    cutting_stock_master_to_full_assignment_feasible hxBar_feas hpattern_mem
  have hπBar_full : cutting_stock_master_dual_feasible_on_cutting_patterns w W πBar :=
    cutting_stock_master_dual_feasible_on_cutting_patterns_of_pricing_optimum_le_one
      w W πBar zStar hzStar hζ hπBar_nonneg
  have hobj_eq :
      cutting_stock_full_master_objective
          (cutting_stock_master_to_full_assignment S' pattern w W hpattern_mem xBar) =
        cutting_stock_master_dual_objective b πBar := by
    calc
      cutting_stock_full_master_objective
          (cutting_stock_master_to_full_assignment S' pattern w W hpattern_mem xBar) =
        cutting_stock_master_objective S' xBar :=
          cutting_stock_master_to_full_assignment_objective hpattern_mem xBar
      _ = cutting_stock_master_dual_objective b πBar := hstrong
  refine ⟨?_, ?_⟩
  · refine ⟨cutting_stock_master_to_full_assignment S' pattern w W hpattern_mem xBar, ?_, rfl⟩
    exact hxBar_full
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    calc
      cutting_stock_full_master_objective
          (cutting_stock_master_to_full_assignment S' pattern w W hpattern_mem xBar) =
        cutting_stock_master_dual_objective b πBar := hobj_eq
      _ ≤ cutting_stock_full_master_objective x :=
        cutting_stock_full_master_weak_duality hx hπBar_full

/-- Example 8.16 (2). Any pricing pattern with value `ζ > 1` has negative reduced cost
`1 - ∑ i, π̄_i z_i^*`; in particular this applies to an optimal pricing solution when the optimal
value satisfies `ζ > 1`. -/
theorem cutting_stock_pattern_has_negative_reduced_cost_of_pricing_value_gt_one
    (πBar : Fin m → ℝ) (zStar : Fin m → ℕ)
    (hζ : 1 < cutting_stock_pricing_objective πBar zStar) :
    1 - cutting_stock_pricing_objective πBar zStar < 0 := by
  simpa using sub_lt_zero.mpr hζ

end Example816
