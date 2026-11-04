/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_knapsack_cover

-- Chapter 7.1 reuses the Chapter 3 knapsack and facet-inequality owners and adds the
-- cover-specific restricted-polytope API on top.

section SupportRestriction

variable {V : Type}

/-- The vectors supported on `S` are those that vanish on every coordinate outside `S`. -/
def zero_outside (S : Finset V) : Set (V → ℝ) :=
  {x | ∀ v, v ∉ S → x v = 0}

/-- Membership in `zero_outside S` means that all coordinates outside `S` vanish. -/
theorem mem_zero_outside_iff
    (S : Finset V) (x : V → ℝ) :
    x ∈ zero_outside S ↔ ∀ v, v ∉ S → x v = 0 :=
  Iff.rfl

end SupportRestriction

section Proposition71

variable {n : ℕ}

open scoped BigOperators

/-- The coefficient vector of the cover inequality attached to `C`. -/
def cover_indicator (C : Finset (Fin n)) : Fin n → ℝ :=
  fun j ↦ if j ∈ C then 1 else 0

/-- The coefficient vector `cover_indicator C` has value `1` on `C` and `0` off `C`. -/
theorem cover_indicator_apply
    (C : Finset (Fin n)) (j : Fin n) :
    cover_indicator C j = if j ∈ C then 1 else 0 :=
  rfl

/-- Helper for Proposition 7.1: dotting `cover_indicator C` with `x` recovers the coordinate sum
over `C`. -/
theorem coverIndicator_dot_eq_sum
    (C : Finset (Fin n)) (x : Fin n → ℝ) :
    cover_indicator C ⬝ᵥ x = C.sum x := by
  -- Expand the indicator dot product into the cover sum.
  simp [dotProduct, cover_indicator]

/-- The restricted polytope `P_C = conv(K) ∩ {x : ℝ^n | x_j = 0 for j ∉ C}` associated with a
cover `C`. -/
def cover_restricted_polytope
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n)) : Set (Fin n → ℝ) :=
  zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∩ zero_outside C

/-- Membership in `cover_restricted_polytope weights capacity C` means belonging to the knapsack
polytope and vanishing outside `C`. -/
theorem mem_cover_restricted_polytope_iff
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n)) (x : Fin n → ℝ) :
    x ∈ cover_restricted_polytope weights capacity C ↔
      x ∈ zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∧
        x ∈ zero_outside C :=
  Iff.rfl

/-- Helper for Proposition 7.1: every cover has at least two indices when each singleton item is
feasible. -/
theorem cover_card_ge_two
    (weights : Fin n → ℕ) (capacity : ℕ)
    (hweights_le_capacity : ∀ j, weights j ≤ capacity)
    (C : Finset (Fin n))
    (hC_cover : IsKnapsackCover weights capacity C) :
    2 ≤ C.card := by
  -- First rule out the empty cover.
  have hC_nonempty : C.Nonempty := by
    by_contra hC_empty
    rw [Finset.not_nonempty_iff_eq_empty] at hC_empty
    have hcover_lt : capacity < C.sum weights :=
      (isKnapsackCover_iff weights capacity C).1 hC_cover
    rw [hC_empty, Finset.sum_empty] at hcover_lt
    exact Nat.not_lt_zero capacity hcover_lt
  by_cases htwo : 2 ≤ C.card
  · exact htwo
  -- Otherwise the nonempty cover must be a singleton, which contradicts singleton feasibility.
  have hcard_one : C.card = 1 := by
    have hpos : 0 < C.card := Finset.card_pos.mpr hC_nonempty
    omega
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard_one
  have hcover_lt : capacity < ({j} : Finset (Fin n)).sum weights :=
    (isKnapsackCover_iff weights capacity {j}).1 hC_cover
  rw [Finset.sum_singleton] at hcover_lt
  exact False.elim <| (not_lt_of_ge (hweights_le_capacity j)) hcover_lt

/-- Helper for Proposition 7.1: the omit-one point attached to `j ∈ C` has value `1` on
`C.erase j` and `0` elsewhere. -/
def omitPoint
    (C : Finset (Fin n)) (j : Fin n) : Fin n → ℝ :=
  fun i ↦ if i ∈ C.erase j then 1 else 0

/-- Helper for Proposition 7.1: the omit-one point is supported on the cover. -/
theorem omitPoint_mem_zeroOutside
    (C : Finset (Fin n)) (j : Fin n) :
    omitPoint C j ∈ zero_outside C := by
  -- Coordinates outside `C` are automatically zero because `C.erase j ⊆ C`.
  intro i hiC
  simp [omitPoint, hiC]

/-- Helper for Proposition 7.1: the weighted sum of the omit-one point is the erased cover-weight
sum. -/
theorem omitPoint_weightedSum_eq_eraseWeightSum
    (weights : Fin n → ℕ) (C : Finset (Fin n))
    {j : Fin n} (_hj : j ∈ C) :
    ∑ i, (weights i : ℝ) * omitPoint C j i = (((C.erase j).sum weights : ℕ) : ℝ) := by
  -- Rewrite the indicator-style sum as the erased finite sum.
  calc
    ∑ i, (weights i : ℝ) * omitPoint C j i =
        (fun i ↦ (weights i : ℝ)) ⬝ᵥ omitPoint C j := by
      rfl
    _ = omitPoint C j ⬝ᵥ (fun i ↦ (weights i : ℝ)) := by
      rw [dotProduct_comm]
    _ = cover_indicator (C.erase j) ⬝ᵥ (fun i ↦ (weights i : ℝ)) := by
      rfl
    _ = (((C.erase j).sum weights : ℕ) : ℝ) := by
      simpa using coverIndicator_dot_eq_sum (C.erase j) (fun i ↦ (weights i : ℝ))

/-- Helper for Proposition 7.1: summing the omit-one point over `C` gives the erased cardinality.
-/
theorem omitPoint_coverSum_eq_cardErase
    (C : Finset (Fin n)) {j : Fin n} (_hj : j ∈ C) :
    C.sum (omitPoint C j) = ((C.erase j).card : ℝ) := by
  -- The omit-one point contributes `1` exactly on `C.erase j`.
  have hsplit : (C.erase j).sum (omitPoint C j) = C.sum (omitPoint C j) := by
    simpa [omitPoint] using (C.sum_erase_add (omitPoint C j) _hj)
  calc
    C.sum (omitPoint C j) = (C.erase j).sum (omitPoint C j) := hsplit.symm
    _ = (C.erase j).sum (fun _ ↦ (1 : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [omitPoint, hi]
    _ = ((C.erase j).card : ℝ) := by
      simp

/-- Helper for Proposition 7.1: the omit-one point is a feasible `0/1` knapsack point under
minimality. -/
theorem omitPoint_mem_zeroOneKnapsackSet
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n))
    (hC_min : IsMinimalKnapsackCover weights capacity C)
    {j : Fin n} (hj : j ∈ C) :
    omitPoint C j ∈
      zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · -- Every coordinate of the omit-one point is either `0` or `1`.
    intro i
    by_cases hi : i ∈ C.erase j
    · right
      simp [omitPoint, hi]
    · left
      simp [omitPoint, hi]
  · -- The erased cover stays feasible by minimality.
    rw [omitPoint_weightedSum_eq_eraseWeightSum weights C hj]
    exact_mod_cast hC_min.erase_sum_le j hj

/-- Helper for Proposition 7.1: the omit-one point belongs to the restricted polytope `P_C`. -/
theorem omitPoint_mem_coverRestrictedPolytope
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n))
    (hC_min : IsMinimalKnapsackCover weights capacity C)
    {j : Fin n} (hj : j ∈ C) :
    omitPoint C j ∈ cover_restricted_polytope weights capacity C := by
  rw [mem_cover_restricted_polytope_iff]
  constructor
  · -- A feasible generator of the knapsack set lies in its convex hull.
    rw [zero_one_knapsack_polytope_eq_convexHull]
    exact subset_convexHull ℝ (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
      (omitPoint_mem_zeroOneKnapsackSet weights capacity C hC_min hj)
  · -- The omit-one point already vanishes off the cover.
    exact omitPoint_mem_zeroOutside C j

/-- Helper for Proposition 7.1: summing the omit-one point over `C` gives the cover right-hand
side. -/
theorem omitPoint_coverSum_eq_rhs
    (C : Finset (Fin n)) {j : Fin n} (hj : j ∈ C) :
    C.sum (omitPoint C j) = cover_inequality_rhs C := by
  -- Rewrite the cover sum to the erased cardinality normal form.
  rw [omitPoint_coverSum_eq_cardErase C hj, cover_inequality_rhs_eq]
  simpa using (Finset.cast_card_erase_of_mem (R := ℝ) hj)

/-- Helper for Proposition 7.1: dotting any coefficient vector with an omit-one point keeps only
the coefficients on `C.erase j`. -/
theorem omitPoint_dot_eq_sum_erase
    (d : Fin n → ℝ) (C : Finset (Fin n)) (j : Fin n) :
    d ⬝ᵥ omitPoint C j = (C.erase j).sum d := by
  -- Commute the dot product and identify the omit-one point with the erased-cover indicator.
  calc
    d ⬝ᵥ omitPoint C j = omitPoint C j ⬝ᵥ d := by
      rw [dotProduct_comm]
    _ = cover_indicator (C.erase j) ⬝ᵥ d := by
      rfl
    _ = (C.erase j).sum d := coverIndicator_dot_eq_sum (C.erase j) d

/-- Helper for Proposition 7.1: affine halfspaces given by linear inequalities are convex. -/
theorem linearInequalitySublevel_convex
    (c : Fin n → ℝ) (δ : ℝ) :
    Convex ℝ {x : Fin n → ℝ | c ⬝ᵥ x ≤ δ} := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductStrongDual c).toLinearMap
  have hpre :
      {x : Fin n → ℝ | c ⬝ᵥ x ≤ δ} = L ⁻¹' Set.Iic δ := by
    ext x
    simp [L, dotProductStrongDual_apply]
  -- Rewrite the halfspace as a linear preimage of a convex interval.
  rw [hpre]
  exact (convex_Iic δ).linear_preimage L

/-- Helper for Proposition 7.1: every binary feasible generator satisfies the cover inequality of
any cover `D`. -/
theorem binaryKnapsackGenerator_coverInequality
    (weights : Fin n → ℕ) (capacity : ℕ) (D : Finset (Fin n))
    {x : Fin n → ℝ}
    (hx : x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
    (hD_cover : IsKnapsackCover weights capacity D) :
    cover_indicator D ⬝ᵥ x ≤ cover_inequality_rhs D := by
  rw [mem_zero_one_knapsack_set_iff] at hx
  rcases hx with ⟨hbin, hcapacity⟩
  rw [coverIndicator_dot_eq_sum, cover_inequality_rhs_eq]
  by_contra hviol
  have hx_one : ∀ j ∈ D, x j = 1 := by
    intro j hj
    obtain hxj | hxj := hbin j
    · have hsum_erase : (D.erase j).sum x + x j = D.sum x := by
        simpa using D.sum_erase_add x hj
      have herase_le : (D.erase j).sum x ≤ ((D.erase j).card : ℝ) := by
        calc
          (D.erase j).sum x ≤ (D.erase j).sum (fun _ ↦ (1 : ℝ)) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            obtain hxi | hxi := hbin i
            · simp [hxi]
            · simp [hxi]
          _ = ((D.erase j).card : ℝ) := by
            simp
      have hcard_erase : ((D.erase j).card : ℝ) = (D.card : ℝ) - 1 := by
        simpa using (Finset.cast_card_erase_of_mem (R := ℝ) hj)
      linarith
    · exact hxj
  have hsum_weights :
      (((D.sum weights : ℕ) : ℝ)) = D.sum (fun i ↦ (weights i : ℝ) * x i) := by
    -- On `D`, the violation forces every binary coordinate to equal `1`.
    calc
      (((D.sum weights : ℕ) : ℝ)) = D.sum (fun i ↦ (weights i : ℝ)) := by
        simp
      _ = D.sum (fun i ↦ (weights i : ℝ) * x i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hx_one i hi, mul_one]
  have hterm_nonneg : ∀ i, 0 ≤ (weights i : ℝ) * x i := by
    intro i
    obtain hxi | hxi := hbin i
    · simp [hxi]
    · exact mul_nonneg (by exact_mod_cast Nat.zero_le (weights i)) (by simp [hxi])
  have hsubset_sum :
      D.sum (fun i ↦ (weights i : ℝ) * x i) ≤
        Finset.univ.sum (fun i ↦ (weights i : ℝ) * x i) := by
    exact Finset.sum_le_univ_sum_of_nonneg (fun i ↦ hterm_nonneg i)
  have hcover_lt : (capacity : ℝ) < (((D.sum weights : ℕ) : ℝ)) := by
    exact_mod_cast (isKnapsackCover_iff weights capacity D).1 hD_cover
  linarith

/-- Helper for Proposition 7.1: every cover inequality is valid on the full `0,1` knapsack
polytope. -/
theorem coverInequality_validOnKnapsackPolytope
    (weights : Fin n → ℕ) (capacity : ℕ) (D : Finset (Fin n))
    (hD_cover : IsKnapsackCover weights capacity D) :
    is_valid_inequality
      (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
      (cover_indicator D)
      (cover_inequality_rhs D) := by
  rw [zero_one_knapsack_polytope_eq_convexHull]
  intro x hx
  -- It is enough to verify the inequality on binary generators of the convex hull.
  have hsubset :
      convexHull ℝ (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ)) ⊆
        {y : Fin n → ℝ | cover_indicator D ⬝ᵥ y ≤ cover_inequality_rhs D} := by
    refine convexHull_min ?_ (linearInequalitySublevel_convex (cover_indicator D)
      (cover_inequality_rhs D))
    intro y hy
    exact binaryKnapsackGenerator_coverInequality weights capacity D hy hD_cover
  exact hsubset hx

/-- Helper for Proposition 7.1: every subcover inequality remains valid on the restricted
polytope `P_C`. -/
theorem subcoverInequality_validOnRestrictedPolytope
    (weights : Fin n → ℕ) (capacity : ℕ)
    (C D : Finset (Fin n))
    (_hD_subset : D ⊆ C)
    (hD_cover : IsKnapsackCover weights capacity D) :
    is_valid_inequality
      (cover_restricted_polytope weights capacity C)
      (cover_indicator D)
      (cover_inequality_rhs D) := by
  intro x hx
  -- Restriction only shrinks the ambient set, so full-polytope validity suffices.
  exact coverInequality_validOnKnapsackPolytope weights capacity D hD_cover hx.1

/-- Helper for Proposition 7.1: the coordinate upper bound `x i ≤ 1` is valid on the restricted
polytope `P_C`. -/
theorem coordinateUpper_validOnRestrictedPolytope
    (weights : Fin n → ℕ) (capacity : ℕ)
    (C : Finset (Fin n)) (i : Fin n) :
    is_valid_inequality
      (cover_restricted_polytope weights capacity C)
      (Pi.single i (1 : ℝ))
      1 := by
  have hfull :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
        (Pi.single i (1 : ℝ))
        1 := by
    rw [zero_one_knapsack_polytope_eq_convexHull]
    intro x hx
    have hsubset :
        convexHull ℝ (zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ)) ⊆
          {y : Fin n → ℝ | Pi.single i (1 : ℝ) ⬝ᵥ y ≤ 1} := by
      refine convexHull_min ?_ (linearInequalitySublevel_convex (Pi.single i (1 : ℝ)) 1)
      intro y hy
      rw [mem_zero_one_knapsack_set_iff] at hy
      rcases hy with ⟨hbin, _⟩
      obtain hyi | hyi := hbin i
      · simp [hyi]
      · simp [hyi]
    exact hsubset hx
  intro x hx
  exact hfull hx.1

/-- Helper for Proposition 7.1: the omit-one point lies in the cover face. -/
theorem coverErasePoint_memFace
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n))
    (hC_min : IsMinimalKnapsackCover weights capacity C)
    {j : Fin n} (hj : j ∈ C) :
    omitPoint C j ∈
      face_set
        (cover_restricted_polytope weights capacity C)
        (cover_indicator C)
        (cover_inequality_rhs C) := by
  -- The omit-one point is feasible and attains the cover inequality at equality.
  refine (mem_face_set_iff).2 ?_
  exact ⟨omitPoint_mem_coverRestrictedPolytope weights capacity C hC_min hj,
    by simpa [coverIndicator_dot_eq_sum] using omitPoint_coverSum_eq_rhs C hj⟩

/-- Helper for Proposition 7.1: on the restricted polytope, a normal vector that is constant on
`C` evaluates as that constant times the cover sum. -/
theorem dotProduct_eq_constant_mul_coverSum_onRestrictedPolytope
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n))
    {d x : Fin n → ℝ} {t : ℝ}
    (hx : x ∈ cover_restricted_polytope weights capacity C)
    (hconst : ∀ j ∈ C, d j = t) :
    d ⬝ᵥ x = t * C.sum x := by
  have hx_zero : ∀ j, j ∉ C → x j = 0 := (mem_zero_outside_iff C x).1 hx.2
  have hx_eq : x = fun j ↦ if j ∈ C then x j else 0 := by
    ext j
    by_cases hj : j ∈ C
    · simp [hj]
    · simp [hj, hx_zero j hj]
  -- Rewrite every nonzero coefficient on the support to the common constant `t`.
  calc
    d ⬝ᵥ x = d ⬝ᵥ (fun j ↦ if j ∈ C then x j else 0) := by
      exact congrArg (fun y ↦ d ⬝ᵥ y) hx_eq
    _ = C.sum (fun j ↦ d j * x j) := by
      simp [dotProduct]
    _ = C.sum (fun j ↦ t * x j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [hconst j hj]
    _ = t * C.sum x := by
      rw [Finset.mul_sum]

/-- Helper for Proposition 7.1: if `i ∈ C`, then the unit vector `e_i` belongs to the restricted
polytope `P_C`. -/
theorem singleOne_mem_coverRestrictedPolytope
    (weights : Fin n → ℕ) (capacity : ℕ)
    (hweights_le_capacity : ∀ j, weights j ≤ capacity)
    (C : Finset (Fin n)) {i : Fin n} (hi : i ∈ C) :
    Pi.single i (1 : ℝ) ∈ cover_restricted_polytope weights capacity C := by
  rw [mem_cover_restricted_polytope_iff]
  constructor
  · -- Feasibility follows because item `i` is not overweight on its own.
    have hi_not_over :
        i ∉ zero_one_knapsack_overweight_indices (fun j ↦ (weights j : ℝ)) (capacity : ℝ) := by
      simpa [zero_one_knapsack_overweight_indices] using
        not_lt_of_ge (show (weights i : ℝ) ≤ (capacity : ℝ) by
          exact_mod_cast hweights_le_capacity i)
    exact single_one_mem_zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) i hi_not_over
  · -- The unit vector is supported on `C` because `i ∈ C`.
    intro j hj
    by_cases hji : j = i
    · subst hji
      exact False.elim (hj hi)
    · simp [hji]

/-- Helper for Proposition 7.1: a nonminimal cover contains an index whose deletion is still a
cover. -/
theorem exists_erase_cover_of_not_minimal
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n))
    (hC_cover : IsKnapsackCover weights capacity C)
    (hnot_min : ¬ IsMinimalKnapsackCover weights capacity C) :
    ∃ i ∈ C, IsKnapsackCover weights capacity (C.erase i) := by
  by_contra hno
  have h_all_feasible : ∀ i ∈ C, (C.erase i).sum weights ≤ capacity := by
    intro i hi
    by_contra hgt
    have hcover_erase : IsKnapsackCover weights capacity (C.erase i) := by
      exact (isKnapsackCover_iff weights capacity (C.erase i)).2 (lt_of_not_ge hgt)
    exact hno ⟨i, hi, hcover_erase⟩
  -- Reassembling the cover and all erase-feasibility inequalities gives minimality.
  exact hnot_min <| (isMinimalKnapsackCover_iff weights capacity C).2 ⟨hC_cover, h_all_feasible⟩

/-- Helper for Proposition 7.1: any exposed proper face containing the cover face is cut out by a
normal vector that is constant on the cover coordinates. -/
theorem containingFace_constantOnCover
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n))
    (hC_min : IsMinimalKnapsackCover weights capacity C)
    {d : Fin n → ℝ} {ε : ℝ}
    (hcontain :
      face_set
          (cover_restricted_polytope weights capacity C)
          (cover_indicator C)
          (cover_inequality_rhs C) ⊆
        face_set
          (cover_restricted_polytope weights capacity C)
          d
          ε) :
    ∃ t, (∀ j ∈ C, d j = t) ∧ ε = t * cover_inequality_rhs C := by
  have hC_nonempty : C.Nonempty := by
    by_contra hC_empty
    rw [Finset.not_nonempty_iff_eq_empty] at hC_empty
    have hcover_lt : capacity < C.sum weights := hC_min.sum_gt_capacity
    rw [hC_empty, Finset.sum_empty] at hcover_lt
    exact Nat.not_lt_zero capacity hcover_lt
  obtain ⟨j0, hj0⟩ := hC_nonempty
  have hsumErase_eq : ∀ j, j ∈ C → (C.erase j).sum d = ε := by
    intro j hj
    have hjFace :
        omitPoint C j ∈
          face_set
            (cover_restricted_polytope weights capacity C)
            (cover_indicator C)
            (cover_inequality_rhs C) :=
      coverErasePoint_memFace weights capacity C hC_min hj
    have hjContain :
        omitPoint C j ∈
          face_set
            (cover_restricted_polytope weights capacity C)
            d
            ε :=
      hcontain hjFace
    -- Every omit-one witness satisfies the containing-face equation.
    simpa [omitPoint_dot_eq_sum_erase] using (mem_face_set_iff.mp hjContain).2
  let t := d j0
  have hconst : ∀ j ∈ C, d j = t := by
    intro j hj
    have hsumj : (C.erase j).sum d + d j = C.sum d := by
      simpa using C.sum_erase_add d hj
    have hsumj0 : (C.erase j0).sum d + d j0 = C.sum d := by
      simpa using C.sum_erase_add d hj0
    -- Comparing the equal erased sums forces every active coefficient to equal the anchor one.
    dsimp [t]
    linarith [hsumErase_eq j hj, hsumErase_eq j0 hj0, hsumj, hsumj0]
  refine ⟨t, hconst, ?_⟩
  have hj0P :
      omitPoint C j0 ∈ cover_restricted_polytope weights capacity C :=
    omitPoint_mem_coverRestrictedPolytope weights capacity C hC_min hj0
  have hj0Contain :
      omitPoint C j0 ∈
        face_set
          (cover_restricted_polytope weights capacity C)
          d
          ε :=
    hcontain (coverErasePoint_memFace weights capacity C hC_min hj0)
  -- Evaluating the containing face on one omit-one witness recovers the exposed right-hand side.
  calc
    ε = d ⬝ᵥ omitPoint C j0 := (mem_face_set_iff.mp hj0Contain).2.symm
    _ = t * C.sum (omitPoint C j0) :=
      dotProduct_eq_constant_mul_coverSum_onRestrictedPolytope
        weights capacity C hj0P hconst
    _ = t * cover_inequality_rhs C := by
      rw [omitPoint_coverSum_eq_rhs C hj0]

/-- Helper for Proposition 7.1: once a containing face has constant coefficients on `C`, its
equality set is already contained in the cover face. -/
theorem containingFace_subset_coverFace_of_constantOnCover
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n))
    {d : Fin n → ℝ} {ε t : ℝ}
    (hconst : ∀ j ∈ C, d j = t)
    (hε : ε = t * cover_inequality_rhs C)
    (ht : 0 < t) :
    face_set
        (cover_restricted_polytope weights capacity C)
        d
        ε ⊆
      face_set
        (cover_restricted_polytope weights capacity C)
        (cover_indicator C)
        (cover_inequality_rhs C) := by
  intro x hx
  rcases (mem_face_set_iff.mp hx) with ⟨hxP, hxEq⟩
  have hxEq' : d ⬝ᵥ x = t * cover_inequality_rhs C := by
    simpa [hε] using hxEq
  have hdot :
      d ⬝ᵥ x = t * C.sum x :=
    dotProduct_eq_constant_mul_coverSum_onRestrictedPolytope weights capacity C hxP hconst
  have hsum_eq : C.sum x = cover_inequality_rhs C := by
    -- The positive scalar `t` lets us transport the exposed-face equation back to the cover sum.
    have hmul : t * C.sum x = t * cover_inequality_rhs C := by
      calc
        t * C.sum x = d ⬝ᵥ x := by simpa using hdot.symm
        _ = t * cover_inequality_rhs C := hxEq'
    nlinarith [hmul, ht]
  exact (mem_face_set_iff).2 ⟨hxP, by simpa [coverIndicator_dot_eq_sum] using hsum_eq⟩

/-- Helper for Proposition 7.1: if deleting `i` still leaves a cover, then every point on the
cover face has `i`th coordinate equal to `1`. -/
theorem coverFace_coordinate_eq_one_of_eraseCover
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n))
    {i : Fin n} (hi : i ∈ C)
    (hEraseCover : IsKnapsackCover weights capacity (C.erase i))
    {x : Fin n → ℝ}
    (hx :
      x ∈
        face_set
          (cover_restricted_polytope weights capacity C)
          (cover_indicator C)
          (cover_inequality_rhs C)) :
    x i = 1 := by
  rcases (mem_face_set_iff.mp hx) with ⟨hxP, hxEq⟩
  have hsubvalid :=
    subcoverInequality_validOnRestrictedPolytope
      weights capacity C (C.erase i) (Finset.erase_subset i C) hEraseCover
  have hsub :
      (C.erase i).sum x ≤ cover_inequality_rhs (C.erase i) := by
    simpa [coverIndicator_dot_eq_sum] using hsubvalid hxP
  have hcoord :
      x i ≤ 1 := by
    have hcoordValid := coordinateUpper_validOnRestrictedPolytope weights capacity C i
    simpa [dotProduct, Pi.single_apply] using hcoordValid hxP
  have hsum :
      (C.erase i).sum x + x i = cover_inequality_rhs C := by
    calc
      (C.erase i).sum x + x i = C.sum x := by
        simpa using C.sum_erase_add x hi
      _ = cover_inequality_rhs C := by
        simpa [coverIndicator_dot_eq_sum] using hxEq
  have hcard :
      (((C.erase i).card : ℝ)) = (C.card : ℝ) - 1 := by
    simpa using (Finset.cast_card_erase_of_mem (R := ℝ) hi)
  -- The erase-cover inequality plus the unit-box bound force the deleted coordinate to be `1`.
  rw [cover_inequality_rhs_eq, hcard] at hsub
  rw [cover_inequality_rhs_eq] at hsum
  linarith


/-- Proposition 7.1. Let `K` be the `0,1` knapsack set with weights `weights` and capacity
`capacity`, and let `C` be a cover for `K`. Assuming each single item is itself feasible,
that is, `weights j ≤ capacity` for all `j`, the cover inequality associated with `C` is
facet-defining for
`P_C = conv(K) ∩ {x : ℝ^n | x_j = 0 for j ∉ C}` if and only if `C` is a minimal cover. -/
theorem cover_inequality_facet_defining_iff_minimal_cover
    (weights : Fin n → ℕ) (capacity : ℕ)
    (hweights_le_capacity : ∀ j, weights j ≤ capacity)
    (C : Finset (Fin n))
    (hC_cover : IsKnapsackCover weights capacity C) :
    facet_defining_inequality
      (cover_restricted_polytope weights capacity C)
      (cover_indicator C)
      (cover_inequality_rhs C) ↔
      IsMinimalKnapsackCover weights capacity C := by
  let P := cover_restricted_polytope weights capacity C
  let F := face_set P (cover_indicator C) (cover_inequality_rhs C)
  have hzeroPoly :
      (0 : Fin n → ℝ) ∈
        zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
    simpa using zero_mem_zero_one_knapsack_polytope
      (fun i ↦ (weights i : ℝ))
      (show (0 : ℝ) ≤ (capacity : ℝ) by exact_mod_cast Nat.zero_le capacity)
  have hzeroSupport : (0 : Fin n → ℝ) ∈ zero_outside C := by
    intro j hj
    simp
  have hzeroP : (0 : Fin n → ℝ) ∈ P := by
    simpa [P, mem_cover_restricted_polytope_iff] using And.intro hzeroPoly hzeroSupport
  constructor
  · intro hfacet
    have hfacetFace : is_facet P F := by
      simpa [P, F] using (facet_defining_inequality_iff.mp hfacet).2
    by_contra hnot_min
    obtain ⟨i, hi, hEraseCover⟩ :=
      exists_erase_cover_of_not_minimal weights capacity C hC_cover hnot_min
    have hsubset_coord :
        F ⊆ face_set P (Pi.single i (1 : ℝ)) 1 := by
      intro x hxF
      have hxi_one :
          x i = 1 :=
        coverFace_coordinate_eq_one_of_eraseCover
          weights capacity C hi hEraseCover (by simpa [P, F] using hxF)
      -- The erase-cover bridge turns the cover face into a coordinate-one face.
      exact (mem_face_set_iff).2
        ⟨(mem_face_set_iff.mp hxF).1, by simp [hxi_one]⟩
    have hcoordProper : is_proper_face P (face_set P (Pi.single i (1 : ℝ)) 1) := by
      rw [is_proper_face_iff]
      refine ⟨?_, ?_, ?_⟩
      · simpa [P] using
          isExposed_face_set_of_valid_inequality
            (coordinateUpper_validOnRestrictedPolytope weights capacity C i)
      · have hsingleP : Pi.single i (1 : ℝ) ∈ P := by
          simpa [P] using
            singleOne_mem_coverRestrictedPolytope
              weights capacity hweights_le_capacity C hi
        exact ⟨Pi.single i 1,
          (mem_face_set_iff).2 ⟨hsingleP, by simp⟩⟩
      · refine ⟨?_, ?_⟩
        · intro x hx
          exact (mem_face_set_iff.mp hx).1
        · intro hPsup
          have hzeroFace : (0 : Fin n → ℝ) ∈ face_set P (Pi.single i (1 : ℝ)) 1 :=
            hPsup hzeroP
          have hzeroEq : Pi.single i (1 : ℝ) ⬝ᵥ (0 : Fin n → ℝ) = 1 :=
            (mem_face_set_iff.mp hzeroFace).2
          simp [dotProduct, Pi.single_apply] at hzeroEq
    have hcoordEq :
        face_set P (Pi.single i (1 : ℝ)) 1 = F :=
      is_facet_maximal hfacetFace hcoordProper hsubset_coord
    have hsingleFace : Pi.single i (1 : ℝ) ∈ face_set P (Pi.single i (1 : ℝ)) 1 := by
      refine (mem_face_set_iff).2 ?_
      refine ⟨?_, by simp [dotProduct, Pi.single_apply]⟩
      simpa [P] using
        singleOne_mem_coverRestrictedPolytope weights capacity hweights_le_capacity C hi
    have hsingleNotF : Pi.single i (1 : ℝ) ∉ F := by
      intro hsingleF
      have hEraseCard_ge_two :
          2 ≤ (C.erase i).card :=
        cover_card_ge_two weights capacity hweights_le_capacity (C.erase i) hEraseCover
      have hEraseCard_ge_two_real :
          (2 : ℝ) ≤ ((C.erase i).card : ℝ) := by
        exact_mod_cast hEraseCard_ge_two
      have hcard :
          (((C.erase i).card : ℝ)) = (C.card : ℝ) - 1 := by
        simpa using (Finset.cast_card_erase_of_mem (R := ℝ) hi)
      have hEq :
          cover_indicator C ⬝ᵥ Pi.single i (1 : ℝ) = cover_inequality_rhs C :=
        (mem_face_set_iff.mp hsingleF).2
      rw [cover_inequality_rhs_eq, ← hcard] at hEq
      have hEq' : (1 : ℝ) = ((C.erase i).card : ℝ) := by
        simpa [cover_indicator, dotProduct, Pi.single_apply, hi] using hEq
      linarith
    exact hsingleNotF (by simpa [hcoordEq] using hsingleFace)
  · intro hC_min
    have hC_cover_min : IsKnapsackCover weights capacity C := inferInstance
    have hvalid :
        is_valid_inequality P (cover_indicator C) (cover_inequality_rhs C) := by
      simpa [P] using
        subcoverInequality_validOnRestrictedPolytope
          weights capacity C C (by intro j hj; exact hj) hC_cover_min
    have hC_card_ge_two :
        2 ≤ C.card :=
      cover_card_ge_two weights capacity hweights_le_capacity C hC_cover_min
    have hC_nonempty : C.Nonempty := by
      have hcard_pos : 0 < C.card := by
        omega
      exact Finset.card_pos.mp hcard_pos
    have hRhs_pos : 0 < cover_inequality_rhs C := by
      have hC_card_ge_two_real : (2 : ℝ) ≤ (C.card : ℝ) := by
        exact_mod_cast hC_card_ge_two
      rw [cover_inequality_rhs_eq]
      linarith
    have hproper : is_proper_face P F := by
      rw [is_proper_face_iff]
      refine ⟨?_, ?_, ?_⟩
      · simpa [P, F] using isExposed_face_set_of_valid_inequality hvalid
      · obtain ⟨j0, hj0⟩ := hC_nonempty
        exact ⟨omitPoint C j0, by
          simpa [P, F] using coverErasePoint_memFace weights capacity C hC_min hj0⟩
      · refine ⟨?_, ?_⟩
        · intro x hx
          exact (mem_face_set_iff.mp hx).1
        · intro hPsup
          have hzeroFace : (0 : Fin n → ℝ) ∈ F := hPsup hzeroP
          have hzeroEq :
              cover_indicator C ⬝ᵥ (0 : Fin n → ℝ) = cover_inequality_rhs C :=
            (mem_face_set_iff.mp hzeroFace).2
          have hzeroEq' : (0 : ℝ) = cover_inequality_rhs C := by
            simpa [coverIndicator_dot_eq_sum] using hzeroEq
          exact (ne_of_gt hRhs_pos) hzeroEq'.symm
    refine (facet_defining_inequality_iff).2 ?_
    refine ⟨hvalid, (is_facet_iff).2 ?_⟩
    refine ⟨hproper, ?_⟩
    intro G hG hsubset
    rcases (is_proper_face_iff.mp hG) with ⟨hG_exposed, hG_nonempty, hG_ssubset⟩
    rcases hG_exposed.exists_eq_face_set_of_nonempty hG_nonempty with
      ⟨d, ε, hvalidG, hG_eq⟩
    have hsubset' :
        F ⊆ face_set P d ε := by
      simpa [F, hG_eq] using hsubset
    -- Route correction: normalize the exposing vector on `C` with omit-one witnesses, then
    -- transport that normalized equation back to the cover face.
    obtain ⟨t, hconst, hε⟩ :=
      containingFace_constantOnCover weights capacity C hC_min hsubset'
    have hε_nonneg : 0 ≤ ε := by
      have hzeroValid : d ⬝ᵥ (0 : Fin n → ℝ) ≤ ε := hvalidG hzeroP
      simpa using hzeroValid
    have ht_nonneg : 0 ≤ t := by
      by_contra ht_neg
      have hmul_neg : t * cover_inequality_rhs C < 0 :=
        mul_neg_of_neg_of_pos (lt_of_not_ge ht_neg) hRhs_pos
      rw [hε] at hε_nonneg
      linarith
    have ht_ne : t ≠ 0 := by
      intro ht_zero
      have hface_eq_P : face_set P d ε = P := by
        ext x
        rw [mem_face_set_iff]
        constructor
        · intro hx
          exact hx.1
        · intro hxP
          have hconst_zero : ∀ j ∈ C, d j = 0 := by
            intro j hj
            rw [hconst j hj, ht_zero]
          refine ⟨hxP, ?_⟩
          calc
            d ⬝ᵥ x = 0 * C.sum x := by
              simpa using
                dotProduct_eq_constant_mul_coverSum_onRestrictedPolytope
                  weights capacity C hxP hconst_zero
            _ = ε := by
              simp [hε, ht_zero]
      exact hG_ssubset.ne (hG_eq.trans hface_eq_P)
    have ht : 0 < t := by
      exact lt_of_le_of_ne ht_nonneg (by simpa using ht_ne.symm)
    have hsubset_back :
        face_set P d ε ⊆ F := by
      simpa [P, F] using
        containingFace_subset_coverFace_of_constantOnCover
          weights capacity C hconst hε ht
    have hface_eq : face_set P d ε = F :=
      Set.Subset.antisymm hsubset_back hsubset'
    simpa [F] using hG_eq.trans hface_eq

end Proposition71
