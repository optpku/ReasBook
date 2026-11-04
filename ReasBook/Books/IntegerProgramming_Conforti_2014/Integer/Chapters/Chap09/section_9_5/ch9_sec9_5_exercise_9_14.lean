/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_exercise_9_13

open scoped Matrix
open SingleIntegerBranchNode

section Exercise914

variable {n : ℕ}

/-- The objective values `c ⬝ᵥ x` attained on the feasible region `P`. -/
def linear_objective_values
    (P : Set (Fin n → ℝ))
    (c : Fin n → ℝ) : Set ℝ :=
  (fun x : Fin n → ℝ ↦ c ⬝ᵥ x) '' P

/-- The optimal value of the linear objective `c ⬝ᵥ x` over the feasible region `P`. -/
noncomputable def linear_objective_value
    (P : Set (Fin n → ℝ))
    (c : Fin n → ℝ) : ℝ :=
  sSup (linear_objective_values P c)

/-- The optimal value of the linear objective `c ⬝ᵥ x` over the feasible region `P`, recorded in
`WithBot ℝ` so that infeasible linear programs have value `⊥`. -/
noncomputable def linear_objective_lp_value
    (P : Set (Fin n → ℝ))
    (c : Fin n → ℝ) : WithBot ℝ :=
  sSup (((↑) : ℝ → WithBot ℝ) '' linear_objective_values P c)

/-- `linear_objective_lp_value P c` unfolds to the `WithBot` supremum of the attained objective
values on `P`. -/
theorem linear_objective_lp_value_eq_sSup
    (P : Set (Fin n → ℝ))
    (c : Fin n → ℝ) :
    linear_objective_lp_value P c =
      sSup (((↑) : ℝ → WithBot ℝ) '' linear_objective_values P c) :=
  rfl

/-- `IsNodeOptimalPoint P c x` means that `x` is feasible for the node LP with feasible set `P`
and attains the maximum of the linear objective `c ⬝ᵥ x` over `P`. -/
def IsNodeOptimalPoint
    (P : Set (Fin n → ℝ))
    (c x : Fin n → ℝ) : Prop :=
  x ∈ P ∧ ∀ ⦃y : Fin n → ℝ⦄, y ∈ P → c ⬝ᵥ y ≤ c ⬝ᵥ x

theorem isNodeOptimalPoint_iff
    (P : Set (Fin n → ℝ))
    (c x : Fin n → ℝ) :
    IsNodeOptimalPoint P c x ↔
      x ∈ P ∧ ∀ ⦃y : Fin n → ℝ⦄, y ∈ P → c ⬝ᵥ y ≤ c ⬝ᵥ x :=
  Iff.rfl

theorem IsNodeOptimalPoint.mem
    {P : Set (Fin n → ℝ)}
    {c x : Fin n → ℝ}
    (hx : IsNodeOptimalPoint P c x) :
    x ∈ P :=
  hx.1

theorem IsNodeOptimalPoint.objective_le
    {P : Set (Fin n → ℝ)}
    {c x y : Fin n → ℝ}
    (hx : IsNodeOptimalPoint P c x)
    (hy : y ∈ P) :
    c ⬝ᵥ y ≤ c ⬝ᵥ x :=
  hx.2 hy

/-- The coordinate-specialized node LP obtained by restricting `P` with the one-variable
branch-and-bound node `N` on coordinate `j`. -/
def coordinate_branch_feasible_set
    (P : Set (Fin n → ℝ))
    (j : Fin n)
    (N : SingleIntegerBranchNode) : Set (Fin n → ℝ) :=
  {x | x ∈ P ∧ N.Allows (x j)}

/-- The objective values attained on the coordinate-specialized node LP. -/
def coordinate_branch_objective_values
    (P : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (j : Fin n)
    (N : SingleIntegerBranchNode) : Set ℝ :=
  linear_objective_values (coordinate_branch_feasible_set P j N) c

/-- Membership in `coordinate_branch_feasible_set P j N` means satisfying the base feasible set
and the one-coordinate branch restriction recorded by `N`. -/
theorem mem_coordinate_branch_feasible_set_iff
    {P : Set (Fin n → ℝ)}
    {j : Fin n}
    {N : SingleIntegerBranchNode}
    {x : Fin n → ℝ} :
    x ∈ coordinate_branch_feasible_set P j N ↔ x ∈ P ∧ N.Allows (x j) :=
  Iff.rfl

/-- The optimal objective value of the coordinate-specialized node LP, recorded in `WithBot ℝ` so
that an infeasible node has value `⊥`. -/
noncomputable def coordinate_branch_lp_value
    (P : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (j : Fin n)
    (N : SingleIntegerBranchNode) : WithBot ℝ :=
  linear_objective_lp_value (coordinate_branch_feasible_set P j N) c

/-- The optimal objective value of the equality branch `x_j = t`. -/
noncomputable abbrev coordinate_fixed_lp_value
    (P : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (j : Fin n)
    (t : ℤ) : WithBot ℝ :=
  coordinate_branch_lp_value P c j (fixed t)

/-- The optimal objective value of the left split branch `x_j ≤ t`. -/
noncomputable abbrev coordinate_left_split_lp_value
    (P : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (j : Fin n)
    (t : ℤ) : WithBot ℝ :=
  coordinate_branch_lp_value P c j (leftSplit t)

/-- The optimal objective value of the right split branch `t ≤ x_j`. -/
noncomputable abbrev coordinate_right_split_lp_value
    (P : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (j : Fin n)
    (t : ℤ) : WithBot ℝ :=
  coordinate_branch_lp_value P c j (rightSplit t)

/-- Helper for Exercise 9.14: an optimal point of the parent node bounds every lifted objective
value attained on a branch-feasible subset. -/
lemma linear_objective_values_bddAbove_of_subset_of_optimalPoint
    {Q P : Set (Fin n → ℝ)}
    {c x : Fin n → ℝ}
    (hQP : Q ⊆ P)
    (hx : IsNodeOptimalPoint P c x) :
    BddAbove ((((↑) : ℝ → WithBot ℝ) '' linear_objective_values Q c)) := by
  -- Every branch-feasible point is still feasible for the parent LP, so the parent optimum
  -- bounds its objective value and hence the lifted objective image.
  refine ⟨↑(c ⬝ᵥ x), ?_⟩
  intro z hz
  rcases hz with ⟨r, hr, rfl⟩
  rcases hr with ⟨y, hyQ, rfl⟩
  have hyP : y ∈ P := hQP hyQ
  exact_mod_cast hx.objective_le hyP

/-- Helper for Exercise 9.14: any lifted set of real objective values in `WithBot ℝ` is directed
for the order comparison needed by conditional suprema. -/
lemma liftedRealImage_directedOn
    (s : Set ℝ) :
    DirectedOn (· ≤ ·) (((↑) : ℝ → WithBot ℝ) '' s) := by
  -- Two lifted real values are comparable, so one of them already dominates the pair.
  intro a ha b hb
  rcases ha with ⟨ra, hra, rfl⟩
  rcases hb with ⟨rb, hrb, rfl⟩
  by_cases h : ra ≤ rb
  · refine ⟨(rb : WithBot ℝ), ?_, ?_, le_rfl⟩
    · exact ⟨rb, hrb, rfl⟩
    · simpa using h
  · have h' : rb ≤ ra := le_of_not_ge h
    refine ⟨(ra : WithBot ℝ), ?_, le_rfl, ?_⟩
    · exact ⟨ra, hra, rfl⟩
    · simpa using h'

/-- Helper for Exercise 9.14: enlarging the feasible region can only increase the LP objective
value recorded in `WithBot ℝ` when the larger lifted objective image is bounded above. -/
lemma linear_objective_lp_value_mono
    {P₁ P₂ : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    (hP : P₁ ⊆ P₂)
    (hB : BddAbove ((((↑) : ℝ → WithBot ℝ) '' linear_objective_values P₂ c))) :
    linear_objective_lp_value P₁ c ≤ linear_objective_lp_value P₂ c := by
  -- Route correction: compare conditional suprema directly on the lifted objective-value images.
  rw [linear_objective_lp_value_eq_sSup, linear_objective_lp_value_eq_sSup]
  set S₁ : Set (WithBot ℝ) := (((↑) : ℝ → WithBot ℝ) '' linear_objective_values P₁ c)
  set S₂ : Set (WithBot ℝ) := (((↑) : ℝ → WithBot ℝ) '' linear_objective_values P₂ c)
  have hdir₁ : DirectedOn (· ≤ ·) S₁ := by
    change DirectedOn (· ≤ ·) ((((↑) : ℝ → WithBot ℝ) '' linear_objective_values P₁ c))
    exact liftedRealImage_directedOn (linear_objective_values P₁ c)
  have hdir₂ : DirectedOn (· ≤ ·) S₂ := by
    change DirectedOn (· ≤ ·) ((((↑) : ℝ → WithBot ℝ) '' linear_objective_values P₂ c))
    exact liftedRealImage_directedOn (linear_objective_values P₂ c)
  have hB₂ : BddAbove S₂ := by
    simpa [S₂] using hB
  have hsubset : S₁ ⊆ S₂ := by
    intro z hz
    rcases hz with ⟨r, hr, rfl⟩
    rcases hr with ⟨y, hyP₁, rfl⟩
    refine ⟨c ⬝ᵥ y, ?_, rfl⟩
    exact ⟨y, hP hyP₁, rfl⟩
  by_cases hS₁ : S₁.Nonempty
  · exact hdir₁.csSup_le_csSup hdir₂ hB₂ hS₁ hsubset
  · have hS₁_empty : S₁ = ∅ := Set.not_nonempty_iff_eq_empty.1 hS₁
    rw [hS₁_empty]
    simp

/-- Helper for Exercise 9.14: every left-split feasible point can be moved to the floor equality
branch without decreasing the objective value. -/
lemma left_split_exists_fixed_floor_ge_objective
    {P : Set (Fin n → ℝ)}
    {c x : Fin n → ℝ}
    {j : Fin n}
    (hP : Convex ℝ P)
    (hx : IsNodeOptimalPoint P c x)
    (hfrac : Int.fract (x j) ≠ 0)
    {y : Fin n → ℝ}
    (hy :
      y ∈ coordinate_branch_feasible_set P j (leftSplit (Int.floor (x j)))) :
    ∃ u,
      u ∈ coordinate_branch_feasible_set P j (fixed (Int.floor (x j))) ∧
      c ⬝ᵥ y ≤ c ⬝ᵥ u := by
  -- Move the left-split point along the segment from `y` to the parent optimum `x`
  -- until the `j`-coordinate reaches the floor boundary.
  have hy_branch : y ∈ P ∧ y j ≤ Int.floor (x j) := by
    simpa [mem_coordinate_branch_feasible_set_iff] using hy
  have hyP : y ∈ P := hy_branch.1
  have hy_le_floor : y j ≤ Int.floor (x j) := hy_branch.2
  have hfloor_lt_x : (Int.floor (x j) : ℝ) < x j := by
    exact Int.floor_lt_self_iff.2 (Int.fract_ne_zero_iff.1 hfrac)
  let θ : ℝ := ((Int.floor (x j) : ℝ) - y j) / (x j - y j)
  let u : Fin n → ℝ := (1 - θ) • y + θ • x
  have hnum_nonneg : 0 ≤ (Int.floor (x j) : ℝ) - y j := by
    linarith
  have hden_pos : 0 < x j - y j := by
    linarith
  have hden_nonneg : 0 ≤ x j - y j := hden_pos.le
  have hnum_le_den : (Int.floor (x j) : ℝ) - y j ≤ x j - y j := by
    linarith
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ]
    exact div_nonneg hnum_nonneg hden_nonneg
  have hθ_le_one : θ ≤ 1 := by
    dsimp [θ]
    exact (div_le_one hden_pos).2 hnum_le_den
  have h_one_sub_nonneg : 0 ≤ 1 - θ := by
    linarith
  have hweights : (1 - θ) + θ = 1 := by
    ring
  have huP : u ∈ P := by
    -- Convexity keeps the interpolated point inside the parent feasible set.
    exact hP hyP hx.mem h_one_sub_nonneg hθ_nonneg hweights
  have hden_ne : x j - y j ≠ 0 := by
    linarith
  have hu_coord : u j = Int.floor (x j) := by
    -- The interpolation parameter was chosen so the distinguished coordinate lands on the floor.
    calc
      u j = (1 - θ) * y j + θ * x j := by
        simp [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      _ = Int.floor (x j) := by
        dsimp [θ]
        field_simp [hden_ne]
        ring
  have hu_fixed :
      u ∈ coordinate_branch_feasible_set P j (fixed (Int.floor (x j))) := by
    refine (mem_coordinate_branch_feasible_set_iff).2 ?_
    constructor
    · exact huP
    · simpa [SingleIntegerBranchNode.allows_fixed_iff] using hu_coord
  have hy_obj_le : c ⬝ᵥ y ≤ c ⬝ᵥ x := hx.objective_le hyP
  have hu_objective :
      c ⬝ᵥ u = (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ x) := by
    -- Expand the objective on the convex combination once so the comparison becomes scalar.
    calc
      c ⬝ᵥ u = c ⬝ᵥ ((1 - θ) • y + θ • x) := by
        rfl
      _ = c ⬝ᵥ ((1 - θ) • y) + c ⬝ᵥ (θ • x) := by
        rw [dotProduct_add]
      _ = (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ x) := by
        rw [dotProduct_smul, dotProduct_smul]
        simp [smul_eq_mul]
  have hy_le_hu : c ⬝ᵥ y ≤ c ⬝ᵥ u := by
    -- Replacing part of the weight on `y` by weight on the optimal point `x` can only improve
    -- the objective value.
    have hθ_obj :
        θ * (c ⬝ᵥ y) ≤ θ * (c ⬝ᵥ x) := by
      exact mul_le_mul_of_nonneg_left hy_obj_le hθ_nonneg
    have hsum_le :
        (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ y) ≤
          (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ x) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hθ_obj ((1 - θ) * (c ⬝ᵥ y))
    calc
      c ⬝ᵥ y = (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ y) := by
        ring
      _ ≤ (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ x) := hsum_le
      _ = c ⬝ᵥ u := by
        rw [hu_objective]
  exact ⟨u, hu_fixed, hy_le_hu⟩

/-- Helper for Exercise 9.14: every right-split feasible point can be moved to the ceiling
equality branch without decreasing the objective value. -/
lemma right_split_exists_fixed_ceil_ge_objective
    {P : Set (Fin n → ℝ)}
    {c x : Fin n → ℝ}
    {j : Fin n}
    (hP : Convex ℝ P)
    (hx : IsNodeOptimalPoint P c x)
    (hfrac : Int.fract (x j) ≠ 0)
    {y : Fin n → ℝ}
    (hy :
      y ∈ coordinate_branch_feasible_set P j (rightSplit (Int.ceil (x j)))) :
    ∃ u,
      u ∈ coordinate_branch_feasible_set P j (fixed (Int.ceil (x j))) ∧
      c ⬝ᵥ y ≤ c ⬝ᵥ u := by
  -- Move the right-split point along the segment from `y` to `x`
  -- until the `j`-coordinate reaches the ceiling boundary.
  have hy_branch : y ∈ P ∧ Int.ceil (x j) ≤ y j := by
    simpa [mem_coordinate_branch_feasible_set_iff] using hy
  have hyP : y ∈ P := hy_branch.1
  have hceil_le_y : Int.ceil (x j) ≤ y j := hy_branch.2
  have hnotint : x j ∉ Set.range Int.cast := Int.fract_ne_zero_iff.1 hfrac
  have hceil_eq_floor_add_one :
      Int.ceil (x j) = Int.floor (x j) + 1 := by
    exact (Int.ceil_eq_floor_add_one_iff_notMem _).2 hnotint
  have hx_lt_ceil : x j < Int.ceil (x j) := by
    calc
      x j < (Int.floor (x j) : ℝ) + 1 := Int.lt_floor_add_one (x j)
      _ = Int.ceil (x j) := by
        norm_num [hceil_eq_floor_add_one]
  let θ : ℝ := (y j - Int.ceil (x j)) / (y j - x j)
  let u : Fin n → ℝ := (1 - θ) • y + θ • x
  have hnum_nonneg : 0 ≤ y j - Int.ceil (x j) := by
    linarith
  have hden_pos : 0 < y j - x j := by
    linarith
  have hden_nonneg : 0 ≤ y j - x j := hden_pos.le
  have hnum_le_den : y j - Int.ceil (x j) ≤ y j - x j := by
    linarith
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ]
    exact div_nonneg hnum_nonneg hden_nonneg
  have hθ_le_one : θ ≤ 1 := by
    dsimp [θ]
    exact (div_le_one hden_pos).2 hnum_le_den
  have h_one_sub_nonneg : 0 ≤ 1 - θ := by
    linarith
  have hweights : (1 - θ) + θ = 1 := by
    ring
  have huP : u ∈ P := by
    -- Convexity keeps the interpolated point inside the parent feasible set.
    exact hP hyP hx.mem h_one_sub_nonneg hθ_nonneg hweights
  have hden_ne : y j - x j ≠ 0 := by
    linarith
  have hu_coord : u j = Int.ceil (x j) := by
    -- The interpolation parameter was chosen so the distinguished coordinate lands on the ceiling.
    calc
      u j = (1 - θ) * y j + θ * x j := by
        simp [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      _ = Int.ceil (x j) := by
        dsimp [θ]
        field_simp [hden_ne]
        ring
  have hu_fixed :
      u ∈ coordinate_branch_feasible_set P j (fixed (Int.ceil (x j))) := by
    refine (mem_coordinate_branch_feasible_set_iff).2 ?_
    constructor
    · exact huP
    · simpa [SingleIntegerBranchNode.allows_fixed_iff] using hu_coord
  have hy_obj_le : c ⬝ᵥ y ≤ c ⬝ᵥ x := hx.objective_le hyP
  have hu_objective :
      c ⬝ᵥ u = (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ x) := by
    -- Expand the objective on the convex combination once so the comparison becomes scalar.
    calc
      c ⬝ᵥ u = c ⬝ᵥ ((1 - θ) • y + θ • x) := by
        rfl
      _ = c ⬝ᵥ ((1 - θ) • y) + c ⬝ᵥ (θ • x) := by
        rw [dotProduct_add]
      _ = (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ x) := by
        rw [dotProduct_smul, dotProduct_smul]
        simp [smul_eq_mul]
  have hy_le_hu : c ⬝ᵥ y ≤ c ⬝ᵥ u := by
    -- Replacing part of the weight on `y` by weight on the optimal point `x` again improves
    -- the objective value.
    have hθ_obj :
        θ * (c ⬝ᵥ y) ≤ θ * (c ⬝ᵥ x) := by
      exact mul_le_mul_of_nonneg_left hy_obj_le hθ_nonneg
    have hsum_le :
        (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ y) ≤
          (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ x) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hθ_obj ((1 - θ) * (c ⬝ᵥ y))
    calc
      c ⬝ᵥ y = (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ y) := by
        ring
      _ ≤ (1 - θ) * (c ⬝ᵥ y) + θ * (c ⬝ᵥ x) := hsum_le
      _ = c ⬝ᵥ u := by
        rw [hu_objective]
  exact ⟨u, hu_fixed, hy_le_hu⟩

/-- Helper for Exercise 9.14: the floor equality branch has the same LP value as the usual left
split branch `x_j ≤ ⌊x_j⌋` at a fractional optimal point. -/
lemma coordinate_left_split_lp_value_eq_fixed_floor
    {P : Set (Fin n → ℝ)}
    {c x : Fin n → ℝ}
    {j : Fin n}
    (hP : Convex ℝ P)
    (hx : IsNodeOptimalPoint P c x)
    (hfrac : Int.fract (x j) ≠ 0) :
    coordinate_left_split_lp_value P c j (Int.floor (x j)) =
      coordinate_fixed_lp_value P c j (Int.floor (x j)) := by
  have hleft_subset_parent :
      coordinate_branch_feasible_set P j (leftSplit (Int.floor (x j))) ⊆ P := by
    intro y hy
    exact (mem_coordinate_branch_feasible_set_iff.1 hy).1
  have hfixed_subset_parent :
      coordinate_branch_feasible_set P j (fixed (Int.floor (x j))) ⊆ P := by
    intro y hy
    exact (mem_coordinate_branch_feasible_set_iff.1 hy).1
  have hBleft :
      BddAbove ((((↑) : ℝ → WithBot ℝ) ''
        linear_objective_values
          (coordinate_branch_feasible_set P j (leftSplit (Int.floor (x j)))) c)) := by
    exact linear_objective_values_bddAbove_of_subset_of_optimalPoint hleft_subset_parent hx
  have hBfixed :
      BddAbove ((((↑) : ℝ → WithBot ℝ) ''
        linear_objective_values
          (coordinate_branch_feasible_set P j (fixed (Int.floor (x j)))) c)) := by
    exact linear_objective_values_bddAbove_of_subset_of_optimalPoint hfixed_subset_parent hx
  have hfixed_subset_left :
      coordinate_branch_feasible_set P j (fixed (Int.floor (x j))) ⊆
        coordinate_branch_feasible_set P j (leftSplit (Int.floor (x j))) := by
    intro y hy
    have hy_fixed : y ∈ P ∧ y j = Int.floor (x j) := by
      simpa [mem_coordinate_branch_feasible_set_iff] using hy
    refine (mem_coordinate_branch_feasible_set_iff).2 ?_
    constructor
    · exact hy_fixed.1
    · simp [SingleIntegerBranchNode.allows_leftSplit_iff, hy_fixed.2]
  apply le_antisymm
  · -- Route correction: prove the hard direction pointwise on attained objective values.
    simp only [coordinate_left_split_lp_value, coordinate_fixed_lp_value,
      coordinate_branch_lp_value, linear_objective_lp_value_eq_sSup]
    set Sleft : Set (WithBot ℝ) := (((↑) : ℝ → WithBot ℝ) ''
      linear_objective_values
        (coordinate_branch_feasible_set P j (leftSplit (Int.floor (x j)))) c)
    set Sfixed : Set (WithBot ℝ) := (((↑) : ℝ → WithBot ℝ) ''
      linear_objective_values
        (coordinate_branch_feasible_set P j (fixed (Int.floor (x j)))) c)
    have hdir_left : DirectedOn (· ≤ ·) Sleft := by
      change DirectedOn (· ≤ ·)
        ((((↑) : ℝ → WithBot ℝ) ''
          linear_objective_values
            (coordinate_branch_feasible_set P j (leftSplit (Int.floor (x j)))) c))
      exact liftedRealImage_directedOn
        (linear_objective_values
          (coordinate_branch_feasible_set P j (leftSplit (Int.floor (x j)))) c)
    have hdir_fixed : DirectedOn (· ≤ ·) Sfixed := by
      change DirectedOn (· ≤ ·)
        ((((↑) : ℝ → WithBot ℝ) ''
          linear_objective_values
            (coordinate_branch_feasible_set P j (fixed (Int.floor (x j)))) c))
      exact liftedRealImage_directedOn
        (linear_objective_values
          (coordinate_branch_feasible_set P j (fixed (Int.floor (x j)))) c)
    have hBleft' : BddAbove Sleft := by
      simpa [Sleft] using hBleft
    have hBfixed' : BddAbove Sfixed := by
      simpa [Sfixed] using hBfixed
    by_cases hSleft : Sleft.Nonempty
    · refine (hdir_left.csSup_le_iff hBleft' hSleft).2 ?_
      intro z hz
      rcases hz with ⟨r, hr, rfl⟩
      rcases hr with ⟨y, hy, rfl⟩
      obtain ⟨u, hu, hyu⟩ := left_split_exists_fixed_floor_ge_objective hP hx hfrac hy
      have hu_mem : (((c ⬝ᵥ u : ℝ) : WithBot ℝ)) ∈ Sfixed := by
        refine ⟨c ⬝ᵥ u, ?_, rfl⟩
        exact ⟨u, hu, rfl⟩
      have hyu_lift :
          (((c ⬝ᵥ y : ℝ) : WithBot ℝ)) ≤ ((c ⬝ᵥ u : ℝ) : WithBot ℝ) := by
        exact_mod_cast hyu
      exact le_trans hyu_lift (hdir_fixed.le_csSup hBfixed' hu_mem)
    · have hSleft_empty : Sleft = ∅ := Set.not_nonempty_iff_eq_empty.1 hSleft
      rw [hSleft_empty]
      simp
  · -- The easy direction comes from the equality branch being a subset of the left split branch.
    simpa [coordinate_left_split_lp_value, coordinate_fixed_lp_value, coordinate_branch_lp_value]
      using linear_objective_lp_value_mono hfixed_subset_left hBleft

/-- Helper for Exercise 9.14: the ceiling equality branch has the same LP value as the usual
right split branch `⌈x_j⌉ ≤ x_j` at a fractional optimal point. -/
lemma coordinate_right_split_lp_value_eq_fixed_ceil
    {P : Set (Fin n → ℝ)}
    {c x : Fin n → ℝ}
    {j : Fin n}
    (hP : Convex ℝ P)
    (hx : IsNodeOptimalPoint P c x)
    (hfrac : Int.fract (x j) ≠ 0) :
    coordinate_right_split_lp_value P c j (Int.ceil (x j)) =
      coordinate_fixed_lp_value P c j (Int.ceil (x j)) := by
  have hright_subset_parent :
      coordinate_branch_feasible_set P j (rightSplit (Int.ceil (x j))) ⊆ P := by
    intro y hy
    exact (mem_coordinate_branch_feasible_set_iff.1 hy).1
  have hfixed_subset_parent :
      coordinate_branch_feasible_set P j (fixed (Int.ceil (x j))) ⊆ P := by
    intro y hy
    exact (mem_coordinate_branch_feasible_set_iff.1 hy).1
  have hBright :
      BddAbove ((((↑) : ℝ → WithBot ℝ) ''
        linear_objective_values
          (coordinate_branch_feasible_set P j (rightSplit (Int.ceil (x j)))) c)) := by
    exact linear_objective_values_bddAbove_of_subset_of_optimalPoint hright_subset_parent hx
  have hBfixed :
      BddAbove ((((↑) : ℝ → WithBot ℝ) ''
        linear_objective_values
          (coordinate_branch_feasible_set P j (fixed (Int.ceil (x j)))) c)) := by
    exact linear_objective_values_bddAbove_of_subset_of_optimalPoint hfixed_subset_parent hx
  have hfixed_subset_right :
      coordinate_branch_feasible_set P j (fixed (Int.ceil (x j))) ⊆
        coordinate_branch_feasible_set P j (rightSplit (Int.ceil (x j))) := by
    intro y hy
    have hy_fixed : y ∈ P ∧ y j = Int.ceil (x j) := by
      simpa [mem_coordinate_branch_feasible_set_iff] using hy
    refine (mem_coordinate_branch_feasible_set_iff).2 ?_
    constructor
    · exact hy_fixed.1
    · simp [SingleIntegerBranchNode.allows_rightSplit_iff, hy_fixed.2]
  apply le_antisymm
  · -- Route correction: the hard direction is the ceiling-side pointwise witness comparison.
    simp only [coordinate_right_split_lp_value, coordinate_fixed_lp_value,
      coordinate_branch_lp_value, linear_objective_lp_value_eq_sSup]
    set Sright : Set (WithBot ℝ) := (((↑) : ℝ → WithBot ℝ) ''
      linear_objective_values
        (coordinate_branch_feasible_set P j (rightSplit (Int.ceil (x j)))) c)
    set Sfixed : Set (WithBot ℝ) := (((↑) : ℝ → WithBot ℝ) ''
      linear_objective_values
        (coordinate_branch_feasible_set P j (fixed (Int.ceil (x j)))) c)
    have hdir_right : DirectedOn (· ≤ ·) Sright := by
      change DirectedOn (· ≤ ·)
        ((((↑) : ℝ → WithBot ℝ) ''
          linear_objective_values
            (coordinate_branch_feasible_set P j (rightSplit (Int.ceil (x j)))) c))
      exact liftedRealImage_directedOn
        (linear_objective_values
          (coordinate_branch_feasible_set P j (rightSplit (Int.ceil (x j)))) c)
    have hdir_fixed : DirectedOn (· ≤ ·) Sfixed := by
      change DirectedOn (· ≤ ·)
        ((((↑) : ℝ → WithBot ℝ) ''
          linear_objective_values
            (coordinate_branch_feasible_set P j (fixed (Int.ceil (x j)))) c))
      exact liftedRealImage_directedOn
        (linear_objective_values
          (coordinate_branch_feasible_set P j (fixed (Int.ceil (x j)))) c)
    have hBright' : BddAbove Sright := by
      simpa [Sright] using hBright
    have hBfixed' : BddAbove Sfixed := by
      simpa [Sfixed] using hBfixed
    by_cases hSright : Sright.Nonempty
    · refine (hdir_right.csSup_le_iff hBright' hSright).2 ?_
      intro z hz
      rcases hz with ⟨r, hr, rfl⟩
      rcases hr with ⟨y, hy, rfl⟩
      obtain ⟨u, hu, hyu⟩ := right_split_exists_fixed_ceil_ge_objective hP hx hfrac hy
      have hu_mem : (((c ⬝ᵥ u : ℝ) : WithBot ℝ)) ∈ Sfixed := by
        refine ⟨c ⬝ᵥ u, ?_, rfl⟩
        exact ⟨u, hu, rfl⟩
      have hyu_lift :
          (((c ⬝ᵥ y : ℝ) : WithBot ℝ)) ≤ ((c ⬝ᵥ u : ℝ) : WithBot ℝ) := by
        exact_mod_cast hyu
      exact le_trans hyu_lift (hdir_fixed.le_csSup hBfixed' hu_mem)
    · have hSright_empty : Sright = ∅ := Set.not_nonempty_iff_eq_empty.1 hSright
      rw [hSright_empty]
      simp
  · -- The equality branch is contained in the right split branch.
    simpa [coordinate_right_split_lp_value, coordinate_fixed_lp_value, coordinate_branch_lp_value]
      using linear_objective_lp_value_mono hfixed_subset_right hBright

/-- Helper for Exercise 9.14: among all equality branches `x_j = t` with
`0 ≤ t ≤ ⌊x_j⌋`, the floor branch attains the greatest LP value. -/
lemma floorFixedBranch_isGreatest_on_leftIndexRange
    {P : Set (Fin n → ℝ)}
    {c x : Fin n → ℝ}
    {j : Fin n}
    (hP : Convex ℝ P)
    (hx : IsNodeOptimalPoint P c x)
    (hx_nonneg : 0 ≤ x j)
    (hfrac : Int.fract (x j) ≠ 0) :
    IsGreatest
      ((fun t : ℤ ↦ coordinate_fixed_lp_value P c j t) '' Set.Icc (0 : ℤ) (Int.floor (x j)))
      (coordinate_fixed_lp_value P c j (Int.floor (x j))) := by
  have hleft_subset_parent :
      coordinate_branch_feasible_set P j (leftSplit (Int.floor (x j))) ⊆ P := by
    intro y hy
    exact (mem_coordinate_branch_feasible_set_iff.1 hy).1
  have hBleft :
      BddAbove ((((↑) : ℝ → WithBot ℝ) ''
        linear_objective_values
          (coordinate_branch_feasible_set P j (leftSplit (Int.floor (x j)))) c)) := by
    exact linear_objective_values_bddAbove_of_subset_of_optimalPoint hleft_subset_parent hx
  refine ⟨?_, ?_⟩
  · -- The floor index itself belongs to the left discrete index range.
    refine ⟨Int.floor (x j), ?_, rfl⟩
    constructor
    · exact Int.floor_nonneg.mpr hx_nonneg
    · exact le_rfl
  · -- Every smaller equality branch is contained in the floor left split, so its value is smaller.
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    have hfixed_subset_left :
        coordinate_branch_feasible_set P j (fixed t) ⊆
          coordinate_branch_feasible_set P j (leftSplit (Int.floor (x j))) := by
      intro y hy
      have hy_fixed : y ∈ P ∧ y j = t := by
        simpa [mem_coordinate_branch_feasible_set_iff] using hy
      have ht_real : (t : ℝ) ≤ Int.floor (x j) := by
        exact_mod_cast ht.2
      refine (mem_coordinate_branch_feasible_set_iff).2 ?_
      constructor
      · exact hy_fixed.1
      · simpa [SingleIntegerBranchNode.allows_leftSplit_iff, hy_fixed.2] using ht_real
    calc
      coordinate_fixed_lp_value P c j t ≤
          coordinate_left_split_lp_value P c j (Int.floor (x j)) := by
            simpa [coordinate_left_split_lp_value, coordinate_fixed_lp_value,
              coordinate_branch_lp_value] using
              linear_objective_lp_value_mono hfixed_subset_left hBleft
      _ = coordinate_fixed_lp_value P c j (Int.floor (x j)) := by
            exact coordinate_left_split_lp_value_eq_fixed_floor hP hx hfrac

/-- Helper for Exercise 9.14: among all equality branches `x_j = t` with
`⌈x_j⌉ ≤ t ≤ u`, the ceiling branch attains the greatest LP value. -/
lemma ceilFixedBranch_isGreatest_on_rightIndexRange
    {P : Set (Fin n → ℝ)}
    {c x : Fin n → ℝ}
    {j : Fin n}
    {u : ℕ}
    (hP : Convex ℝ P)
    (hx : IsNodeOptimalPoint P c x)
    (hx_le_u : x j ≤ u)
    (hfrac : Int.fract (x j) ≠ 0) :
    IsGreatest
      ((fun t : ℤ ↦ coordinate_fixed_lp_value P c j t) '' Set.Icc (Int.ceil (x j)) (u : ℤ))
      (coordinate_fixed_lp_value P c j (Int.ceil (x j))) := by
  have hright_subset_parent :
      coordinate_branch_feasible_set P j (rightSplit (Int.ceil (x j))) ⊆ P := by
    intro y hy
    exact (mem_coordinate_branch_feasible_set_iff.1 hy).1
  have hBright :
      BddAbove ((((↑) : ℝ → WithBot ℝ) ''
        linear_objective_values
          (coordinate_branch_feasible_set P j (rightSplit (Int.ceil (x j)))) c)) := by
    exact linear_objective_values_bddAbove_of_subset_of_optimalPoint hright_subset_parent hx
  refine ⟨?_, ?_⟩
  · -- The ceiling index belongs to the right discrete index range by the upper bound hypothesis.
    refine ⟨Int.ceil (x j), ?_, rfl⟩
    constructor
    · exact le_rfl
    · exact Int.ceil_le.mpr hx_le_u
  · -- Every larger equality branch is contained in the ceiling right split,
    -- so its value is smaller.
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    have hfixed_subset_right :
        coordinate_branch_feasible_set P j (fixed t) ⊆
          coordinate_branch_feasible_set P j (rightSplit (Int.ceil (x j))) := by
      intro y hy
      have hy_fixed : y ∈ P ∧ y j = t := by
        simpa [mem_coordinate_branch_feasible_set_iff] using hy
      have ht_real : (Int.ceil (x j) : ℝ) ≤ t := by
        exact_mod_cast ht.1
      refine (mem_coordinate_branch_feasible_set_iff).2 ?_
      constructor
      · exact hy_fixed.1
      · simpa [SingleIntegerBranchNode.allows_rightSplit_iff, hy_fixed.2] using ht_real
    calc
      coordinate_fixed_lp_value P c j t ≤
          coordinate_right_split_lp_value P c j (Int.ceil (x j)) := by
            simpa [coordinate_right_split_lp_value, coordinate_fixed_lp_value,
              coordinate_branch_lp_value] using
              linear_objective_lp_value_mono hfixed_subset_right hBright
      _ = coordinate_fixed_lp_value P c j (Int.ceil (x j)) := by
            exact coordinate_right_split_lp_value_eq_fixed_ceil hP hx hfrac

/-- For Exercise 9.14, let `xⁱ` be an optimal solution of the node LP `LPᵢ`, let the chosen
integer coordinate `j` satisfy `0 ≤ xⁱ_j`, and assume `xⁱ_j` is fractional. Then the equality
branch with `tₗ = ⌊xⁱ_j⌋` has the largest LP objective value among all equality branches
`x_j = t` with `0 ≤ t ≤ tₗ`. -/
theorem exercise_9_14_floor_branch_value_eq_left_discrete_max
    {P : Set (Fin n → ℝ)}
    {c x : Fin n → ℝ}
    {j : Fin n}
    (hP : Convex ℝ P)
    (hx : IsNodeOptimalPoint P c x)
    (hx_nonneg : 0 ≤ x j)
    (hfrac : Int.fract (x j) ≠ 0) :
    coordinate_fixed_lp_value P c j (Int.floor (x j)) =
      sSup
        ((fun t : ℤ ↦ coordinate_fixed_lp_value P c j t) ''
          Set.Icc (0 : ℤ) (Int.floor (x j))) := by
  -- Reduce the discrete supremum to the verified greatest-element statement at the floor branch.
  simpa using
    (floorFixedBranch_isGreatest_on_leftIndexRange hP hx hx_nonneg hfrac).csSup_eq.symm

/-- For Exercise 9.14, under the same hypotheses, the equality branch with
`tᵤ = ⌈xⁱ_j⌉` has the largest LP objective value among all equality branches
`x_j = t` with `tᵤ ≤ t ≤ u`. -/
theorem exercise_9_14_ceil_branch_value_eq_right_discrete_max
    {P : Set (Fin n → ℝ)}
    {c x : Fin n → ℝ}
    {j : Fin n}
    {u : ℕ}
    (hP : Convex ℝ P)
    (hx : IsNodeOptimalPoint P c x)
    (hx_le_u : x j ≤ u)
    (hfrac : Int.fract (x j) ≠ 0) :
    coordinate_fixed_lp_value P c j (Int.ceil (x j)) =
      sSup
        ((fun t : ℤ ↦ coordinate_fixed_lp_value P c j t) ''
          Set.Icc (Int.ceil (x j)) (u : ℤ)) := by
  -- Reduce the discrete supremum to the verified greatest-element statement at the ceiling branch.
  simpa using
    (ceilFixedBranch_isGreatest_on_rightIndexRange hP hx hx_le_u hfrac).csSup_eq.symm

/-- Exercise 9.14. If the node-selection rule explores the preferred equality branches
`x_j = ⌊xⁱ_j⌋` and `x_j = ⌈xⁱ_j⌉` before the other `u + 1` equality branches, then this
multiway branching gives no stronger LP bound than the usual split disjunction
`x_j ≤ ⌊xⁱ_j⌋` or `x_j ≥ ⌈xⁱ_j⌉`: the best of the two preferred equality-branch bounds is exactly
the best of the two ordinary split-branch bounds. -/
theorem exercise_9_14_priority_equality_branching_has_no_bound_advantage
    {P : Set (Fin n → ℝ)}
    {c x : Fin n → ℝ}
    {j : Fin n}
    {u : ℕ}
    (hP : Convex ℝ P)
    (hx : IsNodeOptimalPoint P c x)
    (hx_nonneg : 0 ≤ x j)
    (hx_le_u : x j ≤ u)
    (hfrac : Int.fract (x j) ≠ 0) :
    max
        (coordinate_left_split_lp_value P c j (Int.floor (x j)))
        (coordinate_right_split_lp_value P c j (Int.ceil (x j))) =
      max
        (coordinate_fixed_lp_value P c j (Int.floor (x j)))
        (coordinate_fixed_lp_value P c j (Int.ceil (x j))) := by
  -- These bound hypotheses are part of the exercise statement even though this comparison only
  -- uses the floor/ceiling split-equality identities.
  let _ := hx_nonneg
  let _ := hx_le_u
  -- Rewrite the preferred split-branch bounds to the corresponding equality-branch bounds.
  rw [coordinate_left_split_lp_value_eq_fixed_floor hP hx hfrac]
  rw [coordinate_right_split_lp_value_eq_fixed_ceil hP hx hfrac]

end Exercise914
