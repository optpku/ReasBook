/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1

open Set
open scoped BigOperators

-- This file uses mathlib's existing `convexHull`/`affineSpan` APIs directly. Its public facet
-- statements stay on the source-facing simple plant location polytope in `(x,y)`-coordinates.

/-- The binary feasible points for the simple plant location formulation. -/
def simple_plant_location_feasible_set (m n : ℕ) :
    Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
  { p |
      (∀ i, ∑ j, p.1 i j = 1) ∧
      (∀ i j, p.1 i j ≤ p.2 j) ∧
      (∀ i j, p.1 i j = 0 ∨ p.1 i j = 1) ∧
      (∀ j, p.2 j = 0 ∨ p.2 j = 1) }

/-- Unfolding lemma for membership in `simple_plant_location_feasible_set`. -/
theorem mem_simple_plant_location_feasible_set_iff
    {m n : ℕ} {p : (Fin m → Fin n → ℝ) × (Fin n → ℝ)} :
    p ∈ simple_plant_location_feasible_set m n ↔
      (∀ i, ∑ j, p.1 i j = 1) ∧
      (∀ i j, p.1 i j ≤ p.2 j) ∧
      (∀ i j, p.1 i j = 0 ∨ p.1 i j = 1) ∧
      (∀ j, p.2 j = 0 ∨ p.2 j = 1) := by
  -- This is just the definition of membership in the feasible set.
  rfl

/-- The simple plant location polytope is the convex hull of its binary feasible points. -/
def simple_plant_location_polytope (m n : ℕ) :
    Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
  convexHull ℝ (simple_plant_location_feasible_set m n)

/-- Unfolding lemma for `simple_plant_location_polytope`. -/
theorem simple_plant_location_polytope_eq (m n : ℕ) :
    simple_plant_location_polytope m n =
      convexHull ℝ (simple_plant_location_feasible_set m n) := by
  -- The polytope was defined as this convex hull.
  rfl

/-- The equality face `x i j = 0` of the simple plant location polytope. -/
def simple_plant_location_x_zero_face (m n : ℕ) (i : Fin m) (j : Fin n) :
    Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ simple_plant_location_polytope m n ∧ p.1 i j = 0}

/-- The equality face `y j = 1` of the simple plant location polytope. -/
def simple_plant_location_y_one_face (m n : ℕ) (j : Fin n) :
    Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ simple_plant_location_polytope m n ∧ p.2 j = 1}

/-- The equality face `x i j = y j` of the simple plant location polytope. -/
def simple_plant_location_linking_face (m n : ℕ) (i : Fin m) (j : Fin n) :
    Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ simple_plant_location_polytope m n ∧ p.1 i j = p.2 j}

/-- Helper for Exercise 3.22: the binary point that assigns every customer to the single open
facility `a`. -/
def simple_plant_location_base_point (m n : ℕ) (a : Fin n) :
    (Fin m → Fin n → ℝ) × (Fin n → ℝ) :=
  (fun _ j ↦ if j = a then 1 else 0,
    fun j ↦ if j = a then 1 else 0)

/-- Helper for Exercise 3.22: the binary point obtained from the base configuration at `a` by
reassigning customer `i₀` to facility `ℓ` and opening `ℓ` as well. -/
def simple_plant_location_reassign_point (m n : ℕ) (a : Fin n) (i₀ : Fin m) (ℓ : Fin n) :
    (Fin m → Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i j ↦ if i = i₀ then if j = ℓ then 1 else 0 else if j = a then 1 else 0,
    fun j ↦ if j = a ∨ j = ℓ then 1 else 0)

/-- Helper for Exercise 3.22: the binary point that keeps all assignments at the base facility
`a` but opens an extra facility `ℓ`. -/
def simple_plant_location_extra_open_point (m n : ℕ) (a : Fin n) (ℓ : Fin n) :
    (Fin m → Fin n → ℝ) × (Fin n → ℝ) :=
  (fun _ j ↦ if j = a then 1 else 0,
    fun j ↦ if j = a ∨ j = ℓ then 1 else 0)

/-- Helper for Exercise 3.22: the base point is feasible for the simple plant location set. -/
theorem simple_plant_location_base_point_mem_feasible_set
    {m n : ℕ} (a : Fin n) :
    simple_plant_location_base_point m n a ∈ simple_plant_location_feasible_set m n := by
  -- Each row has a single `1` at `a`, every coordinate is binary, and only facility `a` is open.
  rw [mem_simple_plant_location_feasible_set_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp [simple_plant_location_base_point]
  · intro i j
    by_cases hj : j = a
    · simp [simple_plant_location_base_point, hj]
    · simp [simple_plant_location_base_point, hj]
  · intro i j
    by_cases hj : j = a
    · simp [simple_plant_location_base_point, hj]
    · simp [simple_plant_location_base_point, hj]
  · intro j
    by_cases hj : j = a
    · simp [simple_plant_location_base_point, hj]
    · simp [simple_plant_location_base_point, hj]

/-- Helper for Exercise 3.22: a single-customer reassignment point is still feasible. -/
theorem simple_plant_location_reassign_point_mem_feasible_set
    {m n : ℕ} (a : Fin n) (i₀ : Fin m) (ℓ : Fin n) :
    simple_plant_location_reassign_point m n a i₀ ℓ ∈
      simple_plant_location_feasible_set m n := by
  -- The modified row keeps one unit of assignment, the untouched rows stay at the base point,
  -- and opening both facilities makes the upper bounds immediate.
  rw [mem_simple_plant_location_feasible_set_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = i₀
    · simp [simple_plant_location_reassign_point, hi]
    · simp [simple_plant_location_reassign_point, hi]
  · intro i j
    by_cases hi : i = i₀
    · by_cases hjℓ : j = ℓ
      · simp [simple_plant_location_reassign_point, hi, hjℓ]
      · by_cases hja : j = a
        · have haℓ : ¬a = ℓ := by
            intro h
            apply hjℓ
            simpa [hja] using h
          simp [simple_plant_location_reassign_point, hi, hja, haℓ]
        · simp [simple_plant_location_reassign_point, hi, hjℓ, hja]
    · by_cases hja : j = a
      · simp [simple_plant_location_reassign_point, hi, hja]
      · by_cases hjℓ : j = ℓ
        · have hℓa : ¬ℓ = a := by
            intro h
            apply hja
            simpa [hjℓ] using h
          simp [simple_plant_location_reassign_point, hi, hjℓ, hℓa]
        · simp [simple_plant_location_reassign_point, hi, hja, hjℓ]
  · intro i j
    by_cases hi : i = i₀
    · by_cases hjℓ : j = ℓ
      · simp [simple_plant_location_reassign_point, hi, hjℓ]
      · simp [simple_plant_location_reassign_point, hi, hjℓ]
    · by_cases hja : j = a
      · simp [simple_plant_location_reassign_point, hi, hja]
      · simp [simple_plant_location_reassign_point, hi, hja]
  · intro j
    by_cases hja : j = a
    · simp [simple_plant_location_reassign_point, hja]
    · by_cases hjℓ : j = ℓ
      · simp [simple_plant_location_reassign_point, hjℓ]
      · simp [simple_plant_location_reassign_point, hja, hjℓ]

/-- Helper for Exercise 3.22: opening an extra facility without changing the assignments stays
feasible. -/
theorem simple_plant_location_extra_open_point_mem_feasible_set
    {m n : ℕ} (a : Fin n) (ℓ : Fin n) :
    simple_plant_location_extra_open_point m n a ℓ ∈
      simple_plant_location_feasible_set m n := by
  -- The assignment part is the base point, while the `y`-part only gains one extra open facility.
  rw [mem_simple_plant_location_feasible_set_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp [simple_plant_location_extra_open_point]
  · intro i j
    by_cases hja : j = a
    · simp [simple_plant_location_extra_open_point, hja]
    · by_cases hjℓ : j = ℓ
      · have hℓa : ¬ℓ = a := by
          intro h
          apply hja
          simpa [hjℓ] using h
        simp [simple_plant_location_extra_open_point, hjℓ, hℓa]
      · simp [simple_plant_location_extra_open_point, hja, hjℓ]
  · intro i j
    by_cases hja : j = a
    · simp [simple_plant_location_extra_open_point, hja]
    · simp [simple_plant_location_extra_open_point, hja]
  · intro j
    by_cases hja : j = a
    · simp [simple_plant_location_extra_open_point, hja]
    · by_cases hjℓ : j = ℓ
      · simp [simple_plant_location_extra_open_point, hjℓ]
      · simp [simple_plant_location_extra_open_point, hja, hjℓ]

/-- Helper for Exercise 3.22: the simple plant location polytope is nonempty because it contains
every feasible base point. -/
theorem simple_plant_location_polytope_nonempty
    {m n : ℕ} (a : Fin n) :
    (simple_plant_location_polytope m n).Nonempty := by
  -- Feasible points lie in the convex hull by the universal subset inclusion.
  refine ⟨simple_plant_location_base_point m n a, ?_⟩
  exact subset_convexHull ℝ _ (simple_plant_location_base_point_mem_feasible_set a)

/-- Helper for Exercise 3.22: the row-sum linear map records the assignment total in each
customer row. -/
def simple_plant_location_rowSum (m n : ℕ) :
    ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] (Fin m → ℝ) where
  toFun p i := ∑ j, p.1 i j
  map_add' p q := by
    -- Row sums distribute over addition coordinatewise.
    ext i
    change ∑ j, (p.1 i j + q.1 i j) = ∑ j, p.1 i j + ∑ j, q.1 i j
    simpa using Finset.sum_add_distrib
  map_smul' c p := by
    -- Row sums also commute with scalar multiplication.
    ext i
    change ∑ j, c * p.1 i j = c * ∑ j, p.1 i j
    rw [Finset.mul_sum]

/-- Helper for Exercise 3.22: the `(i,j)` coordinate basis vector in the assignment block. -/
def simple_plant_location_x_basis (m n : ℕ) (i : Fin m) (j : Fin n) :
    Fin m → Fin n → ℝ :=
  Pi.single i (Pi.single j 1)

/-- Helper for Exercise 3.22: the `j`th coordinate basis vector in the facility block. -/
def simple_plant_location_y_basis (n : ℕ) (j : Fin n) :
    Fin n → ℝ :=
  Pi.single j 1

/-- Helper for Exercise 3.22: the assignment-coordinate functional extracting `x i j`. -/
def simple_plant_location_x_coordinate (m n : ℕ) (i : Fin m) (j : Fin n) :
    ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ where
  toFun p := p.1 i j
  map_add' p q := by
    -- The distinguished assignment coordinate is additive.
    simp
  map_smul' c p := by
    -- The distinguished assignment coordinate is homogeneous.
    simp

/-- Helper for Exercise 3.22: the facility-coordinate functional extracting `y j`. -/
def simple_plant_location_y_coordinate (m n : ℕ) (j : Fin n) :
    ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ where
  toFun p := p.2 j
  map_add' p q := by
    -- The distinguished facility coordinate is additive.
    simp
  map_smul' c p := by
    -- The distinguished facility coordinate is homogeneous.
    simp

/-- Helper for Exercise 3.22: the linking slack functional `x i j - y j`. -/
def simple_plant_location_linking_gap (m n : ℕ) (i : Fin m) (j : Fin n) :
    ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
  simple_plant_location_x_coordinate m n i j -
    simple_plant_location_y_coordinate m n j

/-- Helper for Exercise 3.22: every feasible point already lies in the polytope. -/
theorem simple_plant_location_mem_polytope_of_mem_feasible_set
    {m n : ℕ} {p : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ simple_plant_location_feasible_set m n) :
    p ∈ simple_plant_location_polytope m n := by
  -- The polytope is the convex hull of the feasible set.
  exact subset_convexHull ℝ _ hp

/-- Helper for Exercise 3.22: every feasible point satisfies the nonnegativity inequality
`x i j ≥ 0`. -/
theorem simple_plant_location_x_coordinate_nonneg_of_mem_feasible_set
    {m n : ℕ} {p : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ simple_plant_location_feasible_set m n) (i : Fin m) (j : Fin n) :
    0 ≤ simple_plant_location_x_coordinate m n i j p := by
  -- The binary description says each assignment coordinate is either `0` or `1`.
  rw [mem_simple_plant_location_feasible_set_iff] at hp
  rcases hp.2.2.1 i j with hij | hij <;> simp [simple_plant_location_x_coordinate, hij]

/-- Helper for Exercise 3.22: every feasible point satisfies the upper bound `y j ≤ 1`. -/
theorem simple_plant_location_y_coordinate_le_one_of_mem_feasible_set
    {m n : ℕ} {p : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ simple_plant_location_feasible_set m n) (j : Fin n) :
    simple_plant_location_y_coordinate m n j p ≤ 1 := by
  -- The binary description says each facility coordinate is either `0` or `1`.
  rw [mem_simple_plant_location_feasible_set_iff] at hp
  rcases hp.2.2.2 j with hj | hj <;> simp [simple_plant_location_y_coordinate, hj]

/-- Helper for Exercise 3.22: every feasible point satisfies the linking inequality
`x i j - y j ≤ 0`. -/
theorem simple_plant_location_linking_gap_nonpos_of_mem_feasible_set
    {m n : ℕ} {p : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ simple_plant_location_feasible_set m n) (i : Fin m) (j : Fin n) :
    simple_plant_location_linking_gap m n i j p ≤ 0 := by
  -- This is exactly the feasibility constraint `x i j ≤ y j`.
  rw [mem_simple_plant_location_feasible_set_iff] at hp
  have hij : p.1 i j ≤ p.2 j := hp.2.1 i j
  simpa [simple_plant_location_linking_gap, simple_plant_location_x_coordinate,
    simple_plant_location_y_coordinate, sub_eq_add_neg] using sub_nonpos.mpr hij

/-- Helper for Exercise 3.22: every polytope point satisfies the nonnegativity inequality
`x i j ≥ 0`. -/
theorem simple_plant_location_x_coordinate_nonneg_of_mem_polytope
    {m n : ℕ} {p : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ simple_plant_location_polytope m n) (i : Fin m) (j : Fin n) :
    0 ≤ simple_plant_location_x_coordinate m n i j p := by
  let L := -simple_plant_location_x_coordinate m n i j
  let H : Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := {q | L q ≤ 0}
  have hconvex : Convex ℝ H := by
    -- The lifted inequality cuts out a linear half-space.
    simpa [H, L] using convex_halfSpace_le L.isLinear (0 : ℝ)
  have hsubset :
      convexHull ℝ (simple_plant_location_feasible_set m n) ⊆ H := by
    -- It is enough to check the inequality on the binary feasible vertices.
    refine convexHull_min ?_ hconvex
    intro q hq
    have hq_nonneg := simple_plant_location_x_coordinate_nonneg_of_mem_feasible_set hq i j
    simpa [H, L] using neg_nonpos.mpr hq_nonneg
  rw [simple_plant_location_polytope_eq] at hp
  have hpH : p ∈ H := hsubset hp
  simpa [H, L] using hpH

/-- Helper for Exercise 3.22: every polytope point satisfies the upper bound `y j ≤ 1`. -/
theorem simple_plant_location_y_coordinate_le_one_of_mem_polytope
    {m n : ℕ} {p : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ simple_plant_location_polytope m n) (j : Fin n) :
    simple_plant_location_y_coordinate m n j p ≤ 1 := by
  let L := simple_plant_location_y_coordinate m n j
  let H : Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := {q | L q ≤ 1}
  have hconvex : Convex ℝ H := by
    -- The facility upper bound is also a linear half-space.
    simpa [H, L] using convex_halfSpace_le L.isLinear (1 : ℝ)
  have hsubset :
      convexHull ℝ (simple_plant_location_feasible_set m n) ⊆ H := by
    -- Again it suffices to check the feasible vertices.
    refine convexHull_min ?_ hconvex
    intro q hq
    simpa [H, L] using
      simple_plant_location_y_coordinate_le_one_of_mem_feasible_set hq j
  rw [simple_plant_location_polytope_eq] at hp
  exact hsubset hp

/-- Helper for Exercise 3.22: every polytope point satisfies the linking inequality
`x i j - y j ≤ 0`. -/
theorem simple_plant_location_linking_gap_nonpos_of_mem_polytope
    {m n : ℕ} {p : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ simple_plant_location_polytope m n) (i : Fin m) (j : Fin n) :
    simple_plant_location_linking_gap m n i j p ≤ 0 := by
  let L := simple_plant_location_linking_gap m n i j
  let H : Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := {q | L q ≤ 0}
  have hconvex : Convex ℝ H := by
    -- The linking inequality is also linear in `(x, y)`.
    simpa [H, L] using convex_halfSpace_le L.isLinear (0 : ℝ)
  have hsubset :
      convexHull ℝ (simple_plant_location_feasible_set m n) ⊆ H := by
    -- It is enough to verify the inequality on the feasible vertices.
    refine convexHull_min ?_ hconvex
    intro q hq
    simpa [H, L] using
      simple_plant_location_linking_gap_nonpos_of_mem_feasible_set hq i j
  rw [simple_plant_location_polytope_eq] at hp
  exact hsubset hp

/-- Helper for Exercise 3.22: the base witness point belongs to the polytope. -/
theorem simple_plant_location_base_point_mem_polytope
    {m n : ℕ} (a : Fin n) :
    simple_plant_location_base_point m n a ∈ simple_plant_location_polytope m n := by
  -- The base point is feasible, hence it lies in the defining convex hull.
  exact simple_plant_location_mem_polytope_of_mem_feasible_set
    (simple_plant_location_base_point_mem_feasible_set a)

/-- Helper for Exercise 3.22: every reassignment witness point belongs to the polytope. -/
theorem simple_plant_location_reassign_point_mem_polytope
    {m n : ℕ} (a : Fin n) (i₀ : Fin m) (ℓ : Fin n) :
    simple_plant_location_reassign_point m n a i₀ ℓ ∈ simple_plant_location_polytope m n := by
  -- Each reassignment witness is itself a feasible binary point.
  exact simple_plant_location_mem_polytope_of_mem_feasible_set
    (simple_plant_location_reassign_point_mem_feasible_set a i₀ ℓ)

/-- Helper for Exercise 3.22: every extra-open witness point belongs to the polytope. -/
theorem simple_plant_location_extra_open_point_mem_polytope
    {m n : ℕ} (a : Fin n) (ℓ : Fin n) :
    simple_plant_location_extra_open_point m n a ℓ ∈ simple_plant_location_polytope m n := by
  -- Each extra-open witness is itself a feasible binary point.
  exact simple_plant_location_mem_polytope_of_mem_feasible_set
    (simple_plant_location_extra_open_point_mem_feasible_set a ℓ)

/-- Helper for Exercise 3.22: every feasible point has row-sum vector equal to the all-ones
function. -/
theorem simple_plant_location_rowSum_eq_one_of_mem_feasible_set
    {m n : ℕ} {p : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ simple_plant_location_feasible_set m n) :
    simple_plant_location_rowSum m n p = fun _ ↦ (1 : ℝ) := by
  -- The feasible-set definition already records the row-sum equalities.
  rw [mem_simple_plant_location_feasible_set_iff] at hp
  ext i
  exact hp.1 i

/-- Helper for Exercise 3.22: the base point has row-sum vector equal to the all-ones
function. -/
theorem simple_plant_location_rowSum_base_point
    {m n : ℕ} (a : Fin n) :
    simple_plant_location_rowSum m n (simple_plant_location_base_point m n a) =
      fun _ ↦ (1 : ℝ) := by
  -- Every row of the base point contains a single `1` at the anchor facility `a`.
  ext i
  simp [simple_plant_location_rowSum, simple_plant_location_base_point]

/-- Helper for Exercise 3.22: opening an extra facility changes only the corresponding
facility-coordinate direction. -/
theorem simple_plant_location_extra_open_vsub_base
    {m n : ℕ} (a ℓ : Fin n) (hℓa : ℓ ≠ a) :
    simple_plant_location_extra_open_point m n a ℓ - simple_plant_location_base_point m n a =
      ((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ) := by
  -- Compare the assignment and facility blocks coordinatewise.
  refine Prod.ext ?_ ?_
  · ext i j
    simp [simple_plant_location_extra_open_point, simple_plant_location_base_point]
  · ext j
    by_cases hja : j = a
    · subst hja
      simp [simple_plant_location_extra_open_point, simple_plant_location_base_point,
        simple_plant_location_y_basis, hℓa]
    · by_cases hjℓ : j = ℓ
      · subst hjℓ
        simp [simple_plant_location_extra_open_point, simple_plant_location_base_point,
          simple_plant_location_y_basis, hℓa]
      · simp [simple_plant_location_extra_open_point, simple_plant_location_base_point,
          simple_plant_location_y_basis, hja, hjℓ]

/-- Helper for Exercise 3.22: reassigning one customer produces the expected row-basis
difference together with one facility-opening direction. -/
theorem simple_plant_location_reassign_vsub_base
    {m n : ℕ} (a : Fin n) (i₀ : Fin m) (ℓ : Fin n) (hℓa : ℓ ≠ a) :
    simple_plant_location_reassign_point m n a i₀ ℓ - simple_plant_location_base_point m n a =
      (simple_plant_location_x_basis m n i₀ ℓ - simple_plant_location_x_basis m n i₀ a,
        simple_plant_location_y_basis n ℓ) := by
  -- Compare the assignment and facility blocks coordinatewise.
  refine Prod.ext ?_ ?_
  · ext i j
    by_cases hi : i = i₀
    · subst hi
      by_cases hjℓ : j = ℓ
      · subst hjℓ
        simp [simple_plant_location_reassign_point, simple_plant_location_base_point,
          simple_plant_location_x_basis, hℓa]
      · by_cases hja : j = a
        · subst hja
          simp [simple_plant_location_reassign_point, simple_plant_location_base_point,
            simple_plant_location_x_basis, hjℓ, hℓa]
        · simp [simple_plant_location_reassign_point, simple_plant_location_base_point,
            simple_plant_location_x_basis, hjℓ, hja]
    · by_cases hja : j = a
      · subst hja
        simp [simple_plant_location_reassign_point, simple_plant_location_base_point,
          simple_plant_location_x_basis, hi]
      · by_cases hjℓ : j = ℓ
        · subst hjℓ
          simp [simple_plant_location_reassign_point, simple_plant_location_base_point,
            simple_plant_location_x_basis, hi, hja, hℓa]
        · simp [simple_plant_location_reassign_point, simple_plant_location_base_point,
            simple_plant_location_x_basis, hi, hja, hjℓ]
  · ext j
    by_cases hja : j = a
    · subst hja
      simp [simple_plant_location_reassign_point, simple_plant_location_base_point,
        simple_plant_location_y_basis, hℓa]
    · by_cases hjℓ : j = ℓ
      · subst hjℓ
        simp [simple_plant_location_reassign_point, simple_plant_location_base_point,
          simple_plant_location_y_basis, hℓa]
      · simp [simple_plant_location_reassign_point, simple_plant_location_base_point,
          simple_plant_location_y_basis, hja, hjℓ]

/-- Helper for Exercise 3.22: evaluating the row-embedded assignment-basis sum at a fixed row
collapses the outer `Fin m` summation. -/
theorem simple_plant_location_row_embedding_collapse_eval
    {m n : ℕ} (a : Fin n) (c : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    ((∑ i' : Fin m, ∑ ℓ : Fin n,
        c i' ℓ •
          (simple_plant_location_x_basis m n i' ℓ -
            simple_plant_location_x_basis m n i' a)) i j) =
      ∑ ℓ : Fin n, c i ℓ •
        ((simple_plant_location_y_basis n ℓ - simple_plant_location_y_basis n a) j) := by
  -- Evaluate the outer sum at the chosen row `i`; all other row embeddings vanish.
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp [simple_plant_location_x_basis, simple_plant_location_y_basis, Pi.sub_apply, Pi.single_apply]
  · intro i' _ hi'
    simp [simple_plant_location_x_basis, Pi.sub_apply, hi']
  · intro hi
    simp at hi

/-- Helper for Exercise 3.22: summing the assignment basis over all rows leaves the column basis
at the chosen row. -/
theorem simple_plant_location_summed_x_basis_eval
    {m n : ℕ} (u : Fin n) (i : Fin m) (j : Fin n) :
    ((∑ r : Fin m, simple_plant_location_x_basis m n r u) i j) =
      simple_plant_location_y_basis n u j := by
  -- Evaluate the summed row embeddings at row `i`; only the `i`th embedding survives.
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp [simple_plant_location_x_basis, simple_plant_location_y_basis, Pi.single_apply]
  · intro r _ hri
    simp [simple_plant_location_x_basis, hri]
  · intro hi
    simp at hi

/-- Helper for Exercise 3.22: the row-summed assignment-basis difference evaluates to the
corresponding column-basis difference. -/
theorem simple_plant_location_summed_x_basis_difference_eval
    {m n : ℕ} (a b : Fin n) (i : Fin m) (j : Fin n) :
    ((∑ r : Fin m,
        (simple_plant_location_x_basis m n r b -
          simple_plant_location_x_basis m n r a)) i j) =
      ((simple_plant_location_y_basis n b - simple_plant_location_y_basis n a) j) := by
  -- Rewrite the sum of differences as the difference of the two collapsed basis sums.
  rw [Finset.sum_sub_distrib, Pi.sub_apply, Pi.sub_apply,
    simple_plant_location_summed_x_basis_eval, simple_plant_location_summed_x_basis_eval]
  rfl

/-- Helper for Exercise 3.22: changing the anchor facility changes every row by the same
row-basis difference and changes the facility block by the corresponding coordinate
difference. -/
theorem simple_plant_location_alternate_base_vsub_base
    {m n : ℕ} (a b : Fin n) (hba : b ≠ a) :
    simple_plant_location_base_point m n b - simple_plant_location_base_point m n a =
      ((∑ i : Fin m,
          (simple_plant_location_x_basis m n i b -
            simple_plant_location_x_basis m n i a)),
        simple_plant_location_y_basis n b - simple_plant_location_y_basis n a) := by
  -- Route correction: normalize the row-summed basis difference first, then compare both blocks
  -- coordinatewise against the two base-point formulas.
  refine Prod.ext ?_ ?_
  · ext i j
    change (simple_plant_location_base_point m n b - simple_plant_location_base_point m n a).1 i j =
      ((∑ r : Fin m,
          (simple_plant_location_x_basis m n r b -
            simple_plant_location_x_basis m n r a)) i j)
    rw [simple_plant_location_summed_x_basis_difference_eval]
    simp [simple_plant_location_base_point, simple_plant_location_y_basis, Pi.single_apply]
  · ext j
    have hab : a ≠ b := fun hab' ↦ hba hab'.symm
    by_cases hja : j = a
    · subst hja
      simp [simple_plant_location_base_point, simple_plant_location_y_basis, hab]
    · by_cases hjb : j = b
      · subst hjb
        simp [simple_plant_location_base_point, simple_plant_location_y_basis, hba]
      · simp [simple_plant_location_base_point, simple_plant_location_y_basis, hja, hjb]

/-- Helper for Exercise 3.22: a row vector with zero total is a linear combination of basis
differences against any chosen anchor coordinate. -/
theorem simple_plant_location_row_eq_sum_smul_basis_difference_of_sum_zero
    {n : ℕ} {r : Fin n → ℝ} (a : Fin n) (hr : ∑ j, r j = 0) :
    r = ∑ ℓ : Fin n, r ℓ • (Pi.single ℓ (1 : ℝ) - Pi.single a (1 : ℝ)) := by
  -- Route correction: normalize one row first, then lift that identity to the assignment block.
  calc
    r = ∑ ℓ : Fin n, r ℓ • Pi.single ℓ (1 : ℝ) := by
      simpa using ((Pi.basisFun ℝ (Fin n)).sum_repr r).symm
    _ = ∑ ℓ : Fin n, r ℓ • (Pi.single ℓ (1 : ℝ) - Pi.single a (1 : ℝ)) := by
      calc
        ∑ ℓ : Fin n, r ℓ • Pi.single ℓ (1 : ℝ)
            = ∑ ℓ : Fin n, r ℓ • Pi.single ℓ (1 : ℝ) -
                (∑ ℓ : Fin n, r ℓ) • Pi.single a (1 : ℝ) := by
                  rw [hr, zero_smul, sub_zero]
        _ = ∑ ℓ : Fin n, (r ℓ • Pi.single ℓ (1 : ℝ) - r ℓ • Pi.single a (1 : ℝ)) := by
              rw [Finset.sum_sub_distrib, Finset.sum_smul]
        _ = ∑ ℓ : Fin n, r ℓ • (Pi.single ℓ (1 : ℝ) - Pi.single a (1 : ℝ)) := by
              congr with ℓ
              rw [smul_sub]

/-- Helper for Exercise 3.22: an assignment block with zero row sums is a sum of row-basis
differences against any chosen anchor facility. -/
theorem simple_plant_location_eq_sum_smul_x_basis_difference_of_row_sum_zero
    {m n : ℕ} {x : Fin m → Fin n → ℝ} (a : Fin n)
    (hx : ∀ i, ∑ j, x i j = 0) :
    x = ∑ i : Fin m, ∑ ℓ : Fin n,
      x i ℓ •
        (simple_plant_location_x_basis m n i ℓ -
          simple_plant_location_x_basis m n i a) := by
  -- Lift the proved one-row decomposition through the row embeddings using the named collapse
  -- lemma, so the remaining identity is exactly the already-proved rowwise one.
  ext i j
  have hrow :
      x i = ∑ ℓ : Fin n, x i ℓ • (Pi.single ℓ (1 : ℝ) - Pi.single a (1 : ℝ)) :=
    simple_plant_location_row_eq_sum_smul_basis_difference_of_sum_zero a (hx i)
  have hcoord := congrFun hrow j
  rw [simple_plant_location_row_embedding_collapse_eval]
  simpa [simple_plant_location_y_basis] using hcoord

/-- Helper for Exercise 3.22: the facility block is the sum of its coordinate basis vectors. -/
theorem simple_plant_location_eq_sum_smul_y_basis
    {n : ℕ} (y : Fin n → ℝ) :
    y = ∑ j : Fin n, y j • simple_plant_location_y_basis n j := by
  -- This is the standard basis expansion of `Fin n → ℝ`.
  simpa [simple_plant_location_y_basis] using ((Pi.basisFun ℝ (Fin n)).sum_repr y).symm

/-- Helper for Exercise 3.22: every non-anchor facility-opening basis direction already lies in
the affine-span direction of the polytope. -/
theorem simple_plant_location_nonanchor_y_basis_mem_direction
    {m n : ℕ} (a ℓ : Fin n) (hℓa : ℓ ≠ a) :
    ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_polytope m n)).direction := by
  -- The extra-open witness differs from the base point exactly by this `y`-basis direction.
  have h_extra_aff :
      simple_plant_location_extra_open_point m n a ℓ ∈
        affineSpan ℝ (simple_plant_location_polytope m n) :=
    subset_affineSpan ℝ _ (simple_plant_location_extra_open_point_mem_polytope a ℓ)
  have h_base_aff :
      simple_plant_location_base_point m n a ∈
        affineSpan ℝ (simple_plant_location_polytope m n) :=
    subset_affineSpan ℝ _ (simple_plant_location_base_point_mem_polytope a)
  have hvsub :
      simple_plant_location_extra_open_point m n a ℓ -
          simple_plant_location_base_point m n a ∈
        (affineSpan ℝ (simple_plant_location_polytope m n)).direction :=
    AffineSubspace.vsub_mem_direction h_extra_aff h_base_aff
  simpa [simple_plant_location_extra_open_vsub_base, hℓa] using hvsub

/-- Helper for Exercise 3.22: every pure reassignment generator in the assignment block lies in
the affine-span direction of the polytope. -/
theorem simple_plant_location_pure_x_generator_mem_direction
    {m n : ℕ} (a : Fin n) (i : Fin m) (ℓ : Fin n) :
    ((((simple_plant_location_x_basis m n i ℓ -
        simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_polytope m n)).direction := by
  by_cases hℓa : ℓ = a
  · -- If `ℓ = a`, the claimed generator is just the zero vector.
    subst hℓa
    have hzero :
        ((((simple_plant_location_x_basis m n i ℓ -
            simple_plant_location_x_basis m n i ℓ), (0 : Fin n → ℝ))) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) =
          (0 : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) := by
      ext <;> simp
    rw [hzero]
    exact Submodule.zero_mem ((affineSpan ℝ (simple_plant_location_polytope m n)).direction)
  · -- Otherwise subtract the extra-open direction from the reassignment direction.
    have h_reassign_aff :
        simple_plant_location_reassign_point m n a i ℓ ∈
          affineSpan ℝ (simple_plant_location_polytope m n) :=
      subset_affineSpan ℝ _ (simple_plant_location_reassign_point_mem_polytope a i ℓ)
    have h_base_aff :
        simple_plant_location_base_point m n a ∈
          affineSpan ℝ (simple_plant_location_polytope m n) :=
      subset_affineSpan ℝ _ (simple_plant_location_base_point_mem_polytope a)
    have hpair :
        ((((simple_plant_location_x_basis m n i ℓ -
            simple_plant_location_x_basis m n i a),
            simple_plant_location_y_basis n ℓ)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
          (affineSpan ℝ (simple_plant_location_polytope m n)).direction := by
      have hvsub :
          simple_plant_location_reassign_point m n a i ℓ -
              simple_plant_location_base_point m n a ∈
            (affineSpan ℝ (simple_plant_location_polytope m n)).direction :=
        AffineSubspace.vsub_mem_direction h_reassign_aff h_base_aff
      simpa [simple_plant_location_reassign_vsub_base, hℓa] using hvsub
    have hy :
        ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
          (affineSpan ℝ (simple_plant_location_polytope m n)).direction :=
      simple_plant_location_nonanchor_y_basis_mem_direction (m := m) (n := n) a ℓ hℓa
    have hsub :
        ((((simple_plant_location_x_basis m n i ℓ -
            simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
          (affineSpan ℝ (simple_plant_location_polytope m n)).direction := by
      have := Submodule.sub_mem
        ((affineSpan ℝ (simple_plant_location_polytope m n)).direction) hpair hy
      simpa using this
    exact hsub

/-- Helper for Exercise 3.22: projecting the pair-valued pure-`x` sum separates its assignment
and facility coordinates. -/
theorem simple_plant_location_pair_projection_of_pure_x_sum
    {m n : ℕ} {x : Fin m → Fin n → ℝ} (a : Fin n) :
    Prod.fst
        (∑ i : Fin m, ∑ ℓ : Fin n,
          x i ℓ •
            ((((simple_plant_location_x_basis m n i ℓ -
                simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) =
      ∑ i : Fin m, ∑ ℓ : Fin n,
        x i ℓ •
          (simple_plant_location_x_basis m n i ℓ -
            simple_plant_location_x_basis m n i a) ∧
    Prod.snd
        (∑ i : Fin m, ∑ ℓ : Fin n,
          x i ℓ •
            ((((simple_plant_location_x_basis m n i ℓ -
                simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) =
      0 := by
  constructor
  · -- The first projection forgets the zero facility component and leaves the scalar `x` sum.
    simp [Prod.fst_sum]
  · -- The second projection sees only zero coordinates, so the whole sum vanishes.
    simp [Prod.snd_sum]

/-- Helper for Exercise 3.22: summing pairs with zero facility part packages into one pair with
zero facility coordinate. -/
theorem simple_plant_location_sum_of_pure_x_pairs_eq_packaged_sum
    {m n : ℕ} (u : Fin m → (Fin m → Fin n → ℝ)) :
    (∑ i : Fin m,
        ((((u i), (0 : Fin n → ℝ))) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) =
      ((∑ i : Fin m, u i), 0) := by
  -- Project to each coordinate so the outer pair packaging is definitionally stable.
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]

/-- Helper for Exercise 3.22: a kernel assignment block decomposes as the same double sum in the
full product space, with zero facility component. -/
theorem simple_plant_location_paired_x_decomposition_eq
    {m n : ℕ} {x : Fin m → Fin n → ℝ} (a : Fin n)
    (hx : ∀ i, ∑ j, x i j = 0) :
    (∑ i : Fin m, ∑ ℓ : Fin n,
        x i ℓ •
          ((((simple_plant_location_x_basis m n i ℓ -
              simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) =
      (x, 0) := by
  -- Route correction: first project the pair-valued sum, then reuse the already-proved scalar
  -- row-sum decomposition on the assignment coordinate.
  refine Prod.ext ?_ ?_
  · calc
      Prod.fst
          (∑ i : Fin m, ∑ ℓ : Fin n,
            x i ℓ •
              ((((simple_plant_location_x_basis m n i ℓ -
                  simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
                ((Fin m → Fin n → ℝ) × (Fin n → ℝ))))
          = ∑ i : Fin m, ∑ ℓ : Fin n,
              x i ℓ •
                (simple_plant_location_x_basis m n i ℓ -
                  simple_plant_location_x_basis m n i a) :=
            (simple_plant_location_pair_projection_of_pure_x_sum
              (m := m) (n := n) (x := x) a).1
      _ = x :=
        (simple_plant_location_eq_sum_smul_x_basis_difference_of_row_sum_zero
          (m := m) (n := n) (x := x) a hx).symm
  · -- The second coordinate is the zero sum recorded in the projection helper.
    exact
      (simple_plant_location_pair_projection_of_pure_x_sum
        (m := m) (n := n) (x := x) a).2

/-- Helper for Exercise 3.22: the facility block decomposes as the paired sum of facility basis
directions. -/
theorem simple_plant_location_paired_y_decomposition_eq
    {m n : ℕ} (y : Fin n → ℝ) :
    (∑ j : Fin n,
        y j •
          ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n j)) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) =
      ((0 : Fin m → Fin n → ℝ), y) := by
  -- Project to the two product coordinates and use the standard `y`-basis expansion.
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · simpa [Prod.snd_sum] using
      (simple_plant_location_eq_sum_smul_y_basis (n := n) y).symm

/-- Helper for Exercise 3.22: once one non-anchor `y` direction is known, the alternate-base
difference recovers the anchor `y` basis direction as well. -/
theorem simple_plant_location_anchor_y_direction_from_alternate_base
    {m n : ℕ} (a b : Fin n) (hba : b ≠ a) :
    ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n a)) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_polytope m n)).direction := by
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (simple_plant_location_polytope m n)).direction
  have hbase_b_aff :
      simple_plant_location_base_point m n b ∈
        affineSpan ℝ (simple_plant_location_polytope m n) :=
    subset_affineSpan ℝ _ (simple_plant_location_base_point_mem_polytope (m := m) (n := n) b)
  have hbase_a_aff :
      simple_plant_location_base_point m n a ∈
        affineSpan ℝ (simple_plant_location_polytope m n) :=
    subset_affineSpan ℝ _ (simple_plant_location_base_point_mem_polytope (m := m) (n := n) a)
  have h_alt :
      ((((∑ i : Fin m,
            (simple_plant_location_x_basis m n i b -
              simple_plant_location_x_basis m n i a)),
          simple_plant_location_y_basis n b -
            simple_plant_location_y_basis n a)) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
    -- The alternate base point differs from the anchor base point by the source witness vector.
    have hvsub :
        simple_plant_location_base_point m n b -
            simple_plant_location_base_point m n a ∈ D :=
      AffineSubspace.vsub_mem_direction hbase_b_aff hbase_a_aff
    simpa [D, simple_plant_location_alternate_base_vsub_base, hba] using hvsub
  have hpure_sum_raw :
      (∑ i : Fin m,
          ((((simple_plant_location_x_basis m n i b -
              simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ D := by
    -- Each reassignment generator already lies in the direction, so their sum does too.
    exact Submodule.sum_mem D fun i _ ↦
      simple_plant_location_pure_x_generator_mem_direction (m := m) (n := n) a i b
  have hpure_sum :
      ((((∑ i : Fin m,
            (simple_plant_location_x_basis m n i b -
              simple_plant_location_x_basis m n i a)),
          (0 : Fin n → ℝ))) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
    simpa [simple_plant_location_sum_of_pure_x_pairs_eq_packaged_sum] using hpure_sum_raw
  have hyb :
      ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n b)) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
    simpa [D] using
      (simple_plant_location_nonanchor_y_basis_mem_direction (m := m) (n := n) a b hba)
  have hneg_anchor :
      ((((0 : Fin m → Fin n → ℝ), -simple_plant_location_y_basis n a)) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
    -- Remove the pure `x` package and the known non-anchor `y` direction from the alternate-base
    -- witness to isolate the negative anchor basis direction.
    have hdiff :
        ((((0 : Fin m → Fin n → ℝ),
            simple_plant_location_y_basis n b -
              simple_plant_location_y_basis n a)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
      simpa using Submodule.sub_mem D h_alt hpure_sum
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Submodule.sub_mem D hdiff hyb)
  -- Negating the isolated `-(0, y_a)` direction gives the desired anchor basis direction.
  simpa [D] using Submodule.neg_mem D hneg_anchor

/-- Helper for Exercise 3.22: if a valid linear inequality is tight at one point, its equality
set coincides with the exposed set cut out by the corresponding continuous linear functional. -/
theorem simple_plant_location_eq_set_eq_toExposed_of_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} {L : E →ₗ[ℝ] ℝ} {δ : ℝ} {x₀ : E}
    (hvalid : ∀ ⦃x : E⦄, x ∈ P → L x ≤ δ)
    (hx₀ : x₀ ∈ P) (hx₀_eq : L x₀ = δ) :
    {x : E | x ∈ P ∧ L x = δ} =
      (⟨L, L.continuous_of_finiteDimensional⟩ : E →L[ℝ] ℝ).toExposed P := by
  -- Tightness at one point identifies the exposed set with the equality set.
  ext x
  constructor
  · rintro ⟨hxP, hxEq⟩
    refine ⟨hxP, fun y hyP ↦ ?_⟩
    calc
      L y ≤ δ := hvalid hyP
      _ = L x := hxEq.symm
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hx₀_le : L x₀ ≤ L x := hx.2 x₀ hx₀
    have hx_le : L x ≤ L x₀ := by
      simpa [hx₀_eq] using hvalid hx.1
    exact (le_antisymm hx_le hx₀_le).trans hx₀_eq

/-- Helper for Exercise 3.22: if every point of `F` lies on the affine level set `L = δ`, then
the direction of `affineSpan ℝ F` lies in `ker L`. -/
theorem simple_plant_location_face_direction_le_level_ker
    {m n : ℕ}
    {F : Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ))}
    {L : ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ}
    {δ : ℝ} {x₀ : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hx₀ : x₀ ∈ F)
    (hlevel : ∀ ⦃x : ((Fin m → Fin n → ℝ) × (Fin n → ℝ))⦄, x ∈ F → L x = δ) :
    (affineSpan ℝ F).direction ≤ LinearMap.ker L := by
  have hspan_level :
      (affineSpan ℝ F :
        Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ⊆ {x | L x = δ} := by
    intro x hx
    -- The level-set condition is affine, so it extends from `F` to its affine span.
    refine affineSpan_induction (k := ℝ) (s := F) (p := fun y ↦ L y = δ) hx ?_ ?_
    · intro y hy
      exact hlevel hy
    · intro c u v w hu hv hw
      simp [hu, hv, hw, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc]
  intro v hv
  have hx₀_aff : x₀ ∈ affineSpan ℝ F := subset_affineSpan ℝ _ hx₀
  rw [LinearMap.mem_ker]
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx₀_aff] at hv
  rcases hv with ⟨x, hx_aff, rfl⟩
  -- Both endpoints lie in the same level set, so their difference is annihilated by `L`.
  have hx_eq : L x = δ := hspan_level hx_aff
  have hx₀_eq : L x₀ = δ := hlevel hx₀
  simp [vsub_eq_sub, hx_eq, hx₀_eq]

/-- Helper for Exercise 3.22: with at least two facilities there is always a facility different
from a chosen `j`. -/
theorem simple_plant_location_exists_other_facility
    {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    ∃ a : Fin n, a ≠ j := by
  let zero : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  let one : Fin n := ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hn⟩
  by_cases hj : j = zero
  · refine ⟨one, ?_⟩
    intro hone
    have hval : (1 : ℕ) = 0 := by
      simpa [one, zero] using congrArg Fin.val (hone.trans hj)
    exact (by decide : (1 : ℕ) ≠ 0) hval
  · exact ⟨zero, fun hzero ↦ hj hzero.symm⟩

/-- Helper for Exercise 3.22: the affine-span direction of the simple plant location polytope is
exactly the kernel of the row-sum map. -/
theorem simple_plant_location_direction_eq_row_sum_ker
    {m n : ℕ} (hn : 3 ≤ n) :
    (affineSpan ℝ (simple_plant_location_polytope m n)).direction =
      LinearMap.ker (simple_plant_location_rowSum m n) := by
  let a : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hn⟩
  let base := simple_plant_location_base_point m n a
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (simple_plant_location_polytope m n)).direction
  let K : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
    LinearMap.ker (simple_plant_location_rowSum m n)
  let slice :
      AffineSubspace ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
    AffineSubspace.mk' base K
  have hfeas_subset_slice :
      simple_plant_location_feasible_set m n ⊆ (slice : Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
    -- Every feasible point satisfies the same row-sum equations as the base point.
    intro p hp
    change p - base ∈ K
    rw [LinearMap.mem_ker]
    have hp_row :
        simple_plant_location_rowSum m n p = fun _ ↦ (1 : ℝ) :=
      simple_plant_location_rowSum_eq_one_of_mem_feasible_set hp
    have hbase_row :
        simple_plant_location_rowSum m n base = fun _ ↦ (1 : ℝ) := by
      simpa [base] using simple_plant_location_rowSum_base_point (m := m) (n := n) a
    calc
      simple_plant_location_rowSum m n (p - base)
          = simple_plant_location_rowSum m n p - simple_plant_location_rowSum m n base := by
              rw [LinearMap.map_sub]
      _ = 0 := by rw [hp_row, hbase_row, sub_self]
  have hpoly_subset_slice :
      simple_plant_location_polytope m n ⊆ (slice : Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
    -- The row-sum slice is affine, hence convex, so it contains the convex hull of the feasible set.
    rw [simple_plant_location_polytope_eq]
    exact convexHull_min hfeas_subset_slice slice.convex
  have hupper : D ≤ K := by
    -- Passing to affine spans preserves the containment in the fixed row-sum slice.
    have h_aff :
        affineSpan ℝ (simple_plant_location_polytope m n) ≤ slice :=
      affineSpan_le_of_subset_coe hpoly_subset_slice
    simpa [D, K, slice] using AffineSubspace.direction_le h_aff
  refine le_antisymm hupper ?_
  intro v hv
  rcases v with ⟨x, y⟩
  change (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈ D)
  let b : Fin n := ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hn⟩
  have hba : b ≠ a := by
    intro hab
    have hval : (0 : ℕ) = 1 := by
      simpa [a, b] using congrArg Fin.val hab
    exact (by decide : (0 : ℕ) ≠ 1) hval
  have hvK :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈
        LinearMap.ker (simple_plant_location_rowSum m n)) := by
    simpa [K] using hv
  have hker : simple_plant_location_rowSum m n (x, y) = 0 :=
    LinearMap.mem_ker.mp hvK
  have hx : ∀ i, ∑ j, x i j = 0 := by
    -- Kernel membership says every row sum vanishes coordinatewise.
    intro i
    have hcoord := congrFun hker i
    simpa [simple_plant_location_rowSum] using hcoord
  have hx_sum_mem :
      (∑ i : Fin m, ∑ ℓ : Fin n,
          x i ℓ •
            ((((simple_plant_location_x_basis m n i ℓ -
                simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ D := by
    -- Sum the already-known pure reassignment generators with the coefficients from `x`.
    exact Submodule.sum_mem D fun i _ ↦
      Submodule.sum_mem D fun ℓ _ ↦
        Submodule.smul_mem D (x i ℓ)
          (simple_plant_location_pure_x_generator_mem_direction (m := m) (n := n) a i ℓ)
  have hx_mem :
      ((((x, (0 : Fin n → ℝ))) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ D := by
    -- Rewrite the pure-`x` generator sum to the packaged point `(x, 0)`.
    rw [← simple_plant_location_paired_x_decomposition_eq (m := m) (n := n) (x := x) a hx]
    exact hx_sum_mem
  have hanchor :
      ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n a)) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
    simpa [D] using
      (simple_plant_location_anchor_y_direction_from_alternate_base
        (m := m) (n := n) a b hba)
  have hy_sum_mem :
      (∑ j : Fin n,
          y j •
            ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n j)) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ D := by
    -- Each `y`-basis direction is in the affine direction: non-anchor indices by the extra-open
    -- witness, and the anchor index by the alternate-base argument.
    exact Submodule.sum_mem D fun j _ ↦ by
      by_cases hja : j = a
      · subst hja
        exact Submodule.smul_mem D (y a) hanchor
      · exact Submodule.smul_mem D (y j) <| by
          simpa [D] using
            (simple_plant_location_nonanchor_y_basis_mem_direction
              (m := m) (n := n) a j hja)
  have hy_mem :
      (((((0 : Fin m → Fin n → ℝ), y)) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ D := by
    -- Package the basis expansion of `y` into the product-space point `(0, y)`.
    rw [← simple_plant_location_paired_y_decomposition_eq (m := m) (n := n) y]
    exact hy_sum_mem
  -- Route correction: split the kernel vector into its pure-`x` and pure-`y` pieces, then use
  -- the source-faithful generator membership lemmas on each piece separately.
  have hsplit :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ))) =
        ((((x, (0 : Fin n → ℝ))) : ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) +
          ((((0 : Fin m → Fin n → ℝ), y)) : ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) := by
    ext <;> simp
  rw [hsplit]
  exact Submodule.add_mem D hx_mem hy_mem

/-- Part (1) of Exercise 3.22: the simple plant location polytope has affine dimension `m * n + n - m`
when `m ≥ 2` and `n ≥ 3`. -/
-- TODO: Prove the affine dimension by combining the row-sum affine-hull upper bound with an
-- explicit affinely independent family built from the base, reassignment, and extra-open witness
-- points introduced above.
theorem simple_plant_location_polytope_affine_dimension
    {m n : ℕ} (hm : 2 ≤ m) (hn : 3 ≤ n) :
    Module.finrank ℝ (affineSpan ℝ (simple_plant_location_polytope m n)).direction =
      m * n + n - m := by
  -- The affine dimension is the kernel dimension of the row-sum map.
  let a : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hn⟩
  have hdir :
      (affineSpan ℝ (simple_plant_location_polytope m n)).direction =
        LinearMap.ker (simple_plant_location_rowSum m n) :=
    simple_plant_location_direction_eq_row_sum_ker hn
  have hsurj : Function.Surjective (simple_plant_location_rowSum m n) := by
    -- Putting a row vector entirely into one facility column gives a right inverse.
    intro r
    refine ⟨((fun i j ↦ if j = a then r i else 0), 0), ?_⟩
    ext i
    simp [simple_plant_location_rowSum, a]
  have hrange_top :
      LinearMap.range (simple_plant_location_rowSum m n) = ⊤ :=
    LinearMap.range_eq_top.2 hsurj
  have hrange_finrank :
      Module.finrank ℝ (LinearMap.range (simple_plant_location_rowSum m n)) = m := by
    -- The row-sum map is onto `Fin m → ℝ`, whose finrank is `m`.
    rw [hrange_top, finrank_top, Module.finrank_fin_fun]
  have hambient_finrank :
      Module.finrank ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) = m * n + n := by
    -- The ambient space is the product of an `m`-by-`n` assignment block and an `n`-dimensional
    -- facility block.
    rw [Module.finrank_prod]
    have hx :
        Module.finrank ℝ (Fin m → Fin n → ℝ) = m * n := by
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_fin_fun]
    have hy :
        Module.finrank ℝ (Fin n → ℝ) = n := by
      rw [Module.finrank_fin_fun]
    rw [hx, hy]
  have hker_finrank :
      Module.finrank ℝ (LinearMap.ker (simple_plant_location_rowSum m n)) =
        m * n + n - m := by
    -- Rank-nullity turns surjectivity into the desired kernel-dimension formula.
    have hranknull :
        Module.finrank ℝ (LinearMap.range (simple_plant_location_rowSum m n)) +
            Module.finrank ℝ (LinearMap.ker (simple_plant_location_rowSum m n)) =
          Module.finrank ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := by
      exact LinearMap.finrank_range_add_finrank_ker (simple_plant_location_rowSum m n)
    rw [hrange_finrank, hambient_finrank] at hranknull
    have hranknull' :
        Module.finrank ℝ (LinearMap.ker (simple_plant_location_rowSum m n)) + m =
          m * n + n := by
      simpa [add_comm] using hranknull
    exact Nat.eq_sub_of_add_eq hranknull'
  rw [hdir]
  exact hker_finrank

/-- Helper for Exercise 3.22: the face `x i j = 0` is nonempty. -/
theorem simple_plant_location_x_zero_face_nonempty
    {m n : ℕ} (hn : 3 ≤ n) (i : Fin m) (j : Fin n) :
    (simple_plant_location_x_zero_face m n i j).Nonempty := by
  have hn_two : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn
  obtain ⟨a, haj⟩ := simple_plant_location_exists_other_facility hn_two j
  have hja : j ≠ a := fun hja ↦ haj hja.symm
  refine ⟨simple_plant_location_reassign_point m n j i a, ?_⟩
  refine ⟨simple_plant_location_reassign_point_mem_polytope j i a, ?_⟩
  -- Reassigning row `i` away from facility `j` forces the distinguished entry to vanish.
  simp [simple_plant_location_reassign_point, hja]

/-- Helper for Exercise 3.22: the face `y j = 1` is nonempty. -/
theorem simple_plant_location_y_one_face_nonempty
    {m n : ℕ} (j : Fin n) :
    (simple_plant_location_y_one_face m n j).Nonempty := by
  refine ⟨simple_plant_location_base_point m n j, ?_⟩
  refine ⟨simple_plant_location_base_point_mem_polytope j, ?_⟩
  -- The base point at facility `j` keeps exactly that facility open.
  simp [simple_plant_location_base_point]

/-- Helper for Exercise 3.22: the face `x i j = y j` is nonempty. -/
theorem simple_plant_location_linking_face_nonempty
    {m n : ℕ} (i : Fin m) (j : Fin n) :
    (simple_plant_location_linking_face m n i j).Nonempty := by
  refine ⟨simple_plant_location_base_point m n j, ?_⟩
  refine ⟨simple_plant_location_base_point_mem_polytope j, ?_⟩
  -- At the base point anchored at `j`, both sides of the linking equality are `1`.
  simp [simple_plant_location_base_point]

/-- Helper for Exercise 3.22: the face `x i j = 0` is exposed by maximizing `-x i j`. -/
theorem simple_plant_location_x_zero_face_isExposed
    {m n : ℕ} (hn : 3 ≤ n) (i : Fin m) (j : Fin n) :
    IsExposed ℝ (simple_plant_location_polytope m n)
      (simple_plant_location_x_zero_face m n i j) := by
  let L := -simple_plant_location_x_coordinate m n i j
  rcases simple_plant_location_x_zero_face_nonempty (m := m) (n := n) hn i j with ⟨x₀, hx₀⟩
  have hface :
      simple_plant_location_x_zero_face m n i j =
        (⟨L, L.continuous_of_finiteDimensional⟩ :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ℝ).toExposed
            (simple_plant_location_polytope m n) := by
    -- The equality set is the exposed set of the negated coordinate functional.
    have hx₀_eq : L x₀ = 0 := by
      simpa [L, simple_plant_location_x_zero_face] using hx₀.2
    simpa [simple_plant_location_x_zero_face, L, simple_plant_location_x_coordinate] using
      (simple_plant_location_eq_set_eq_toExposed_of_mem
        (L := L)
        (δ := 0)
        (x₀ := x₀)
        (by
          intro x hx
          have hx_nonneg := simple_plant_location_x_coordinate_nonneg_of_mem_polytope hx i j
          simpa [L] using neg_nonpos.mpr hx_nonneg)
        hx₀.1
        hx₀_eq)
  -- Rewriting as a `toExposed` set gives the canonical exposed-face fact.
  rw [hface]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Exercise 3.22: the face `y j = 1` is exposed by maximizing `y j`. -/
theorem simple_plant_location_y_one_face_isExposed
    {m n : ℕ} (j : Fin n) :
    IsExposed ℝ (simple_plant_location_polytope m n)
      (simple_plant_location_y_one_face m n j) := by
  let L := simple_plant_location_y_coordinate m n j
  rcases simple_plant_location_y_one_face_nonempty (m := m) (n := n) j with ⟨x₀, hx₀⟩
  have hface :
      simple_plant_location_y_one_face m n j =
        (⟨L, L.continuous_of_finiteDimensional⟩ :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ℝ).toExposed
            (simple_plant_location_polytope m n) := by
    -- The equality set is the exposed set of the facility coordinate functional.
    have hx₀_eq : L x₀ = 1 := by
      simpa [L, simple_plant_location_y_one_face] using hx₀.2
    exact simple_plant_location_eq_set_eq_toExposed_of_mem
      (L := L)
      (δ := 1)
      (x₀ := x₀)
      (by
        intro x hx
        exact simple_plant_location_y_coordinate_le_one_of_mem_polytope hx j)
      hx₀.1
      hx₀_eq
  -- Rewriting as a `toExposed` set gives the canonical exposed-face fact.
  rw [hface]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Exercise 3.22: the face `x i j = y j` is exposed by maximizing `x i j - y j`. -/
theorem simple_plant_location_linking_face_isExposed
    {m n : ℕ} (i : Fin m) (j : Fin n) :
    IsExposed ℝ (simple_plant_location_polytope m n)
      (simple_plant_location_linking_face m n i j) := by
  let L := simple_plant_location_linking_gap m n i j
  rcases simple_plant_location_linking_face_nonempty (m := m) (n := n) i j with ⟨x₀, hx₀⟩
  have hface :
      simple_plant_location_linking_face m n i j =
        (⟨L, L.continuous_of_finiteDimensional⟩ :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ℝ).toExposed
            (simple_plant_location_polytope m n) := by
    -- The equality set is the exposed set of the linking slack `x i j - y j`.
    have hx₀_eq : L x₀ = 0 := by
      simpa [L, simple_plant_location_linking_gap, simple_plant_location_x_coordinate,
        simple_plant_location_y_coordinate, sub_eq_add_neg] using sub_eq_zero.mpr hx₀.2
    simpa [simple_plant_location_linking_face, L, simple_plant_location_linking_gap,
      simple_plant_location_x_coordinate, simple_plant_location_y_coordinate, sub_eq_zero] using
      (simple_plant_location_eq_set_eq_toExposed_of_mem
        (L := L)
        (δ := 0)
        (x₀ := x₀)
        (by
          intro x hx
          exact simple_plant_location_linking_gap_nonpos_of_mem_polytope hx i j)
        hx₀.1
        hx₀_eq)
  -- Rewriting as a `toExposed` set gives the canonical exposed-face fact.
  rw [hface]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Exercise 3.22: if a linear functional takes the value `1` on some vector of a
submodule `D`, then the kernel cut `D ⊓ ker L` has codimension one inside `D`. -/
theorem simple_plant_location_finrank_inf_ker_add_one_of_eval_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (D : Submodule ℝ E) (L : E →ₗ[ℝ] ℝ) {w : E}
    (hwD : w ∈ D) (hw : L w = 1) :
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
  have hne : L.domRestrict D ≠ 0 := by
    -- Evaluating the restricted map on the chosen witness prevents it from vanishing.
    intro hzero
    have hvalue := congrArg (fun f : D →ₗ[ℝ] ℝ ↦ f ⟨w, hwD⟩) hzero
    simpa [LinearMap.domRestrict_apply, hw] using hvalue
  have hdim :
      Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) + 1 =
        Module.finrank ℝ ↥D := by
    simpa using Module.Dual.finrank_ker_add_one_of_ne_zero (f := L.domRestrict D) hne
  have hmap :
      (LinearMap.ker (L.domRestrict D)).map D.subtype = D ⊓ LinearMap.ker L := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  have hfin :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) =
        Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) := by
    -- Rewrite the ambient intersection back to the subtype pushforward, then use the standard
    -- finrank invariance of `map` along the subtype embedding.
    rw [← hmap]
    simpa using
      (Submodule.finrank_map_subtype_eq (R := ℝ) (p := D)
        (q := LinearMap.ker (L.domRestrict D)))
  -- Transport the restricted-kernel codimension statement back to the ambient submodule `D`.
  calc
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1
        = Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) + 1 := by
            rw [hfin]
    _ = Module.finrank ℝ ↥D := hdim

/-- Helper for Exercise 3.22: with facility `j` fixed open, opening a different facility gives
the corresponding `y`-basis direction inside the face direction. -/
theorem simple_plant_location_nonanchor_y_basis_mem_y_one_face_direction
    {m n : ℕ} (j ℓ : Fin n) (hℓj : ℓ ≠ j) :
    ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_y_one_face m n j)).direction := by
  let F := simple_plant_location_y_one_face m n j
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  have hbase_mem : simple_plant_location_base_point m n j ∈ F := by
    refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) j, ?_⟩
    -- The base point at `j` keeps facility `j` open.
    simp [simple_plant_location_base_point]
  have hextra_mem : simple_plant_location_extra_open_point m n j ℓ ∈ F := by
    refine ⟨simple_plant_location_extra_open_point_mem_polytope (m := m) (n := n) j ℓ, ?_⟩
    -- Adding one extra open facility leaves `y j = 1`.
    simp [simple_plant_location_extra_open_point, hℓj]
  have hbase_aff :
      simple_plant_location_base_point m n j ∈ affineSpan ℝ F :=
    subset_affineSpan ℝ _ hbase_mem
  have hextra_aff :
      simple_plant_location_extra_open_point m n j ℓ ∈ affineSpan ℝ F :=
    subset_affineSpan ℝ _ hextra_mem
  have hvsub :
      simple_plant_location_extra_open_point m n j ℓ -
          simple_plant_location_base_point m n j ∈ D :=
    AffineSubspace.vsub_mem_direction hextra_aff hbase_aff
  -- The extra-open witness differs from the base point by exactly one non-anchor `y` basis vector.
  simpa [D, simple_plant_location_extra_open_vsub_base, hℓj] using hvsub

/-- Helper for Exercise 3.22: with facility `j` fixed open, every pure reassignment direction
based at `j` lies in the face direction. -/
theorem simple_plant_location_pure_x_generator_mem_y_one_face_direction
    {m n : ℕ} (j : Fin n) (i : Fin m) (ℓ : Fin n) :
    ((((simple_plant_location_x_basis m n i ℓ -
        simple_plant_location_x_basis m n i j), (0 : Fin n → ℝ))) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_y_one_face m n j)).direction := by
  let F := simple_plant_location_y_one_face m n j
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  by_cases hℓj : ℓ = j
  · -- If `ℓ = j`, the claimed generator is just the zero vector.
    subst ℓ
    have hzero :
        ((((simple_plant_location_x_basis m n i j -
            simple_plant_location_x_basis m n i j), (0 : Fin n → ℝ))) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) =
          (0 : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) := by
      ext <;> simp
    rw [hzero]
    exact Submodule.zero_mem D
  · have hbase_mem : simple_plant_location_base_point m n j ∈ F := by
      refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) j, ?_⟩
      -- The anchor base point lies on the level set `y j = 1`.
      simp [simple_plant_location_base_point]
    have hreassign_mem : simple_plant_location_reassign_point m n j i ℓ ∈ F := by
      refine ⟨simple_plant_location_reassign_point_mem_polytope (m := m) (n := n) j i ℓ, ?_⟩
      -- Reassigning one row away from `j` still leaves facility `j` open.
      simp [simple_plant_location_reassign_point, hℓj]
    have hextra_mem : simple_plant_location_extra_open_point m n j ℓ ∈ F := by
      refine ⟨simple_plant_location_extra_open_point_mem_polytope (m := m) (n := n) j ℓ, ?_⟩
      -- Opening one extra facility also keeps `j` open.
      simp [simple_plant_location_extra_open_point, hℓj]
    have hbase_aff :
        simple_plant_location_base_point m n j ∈ affineSpan ℝ F :=
      subset_affineSpan ℝ _ hbase_mem
    have hreassign_aff :
        simple_plant_location_reassign_point m n j i ℓ ∈ affineSpan ℝ F :=
      subset_affineSpan ℝ _ hreassign_mem
    have hextra_aff :
        simple_plant_location_extra_open_point m n j ℓ ∈ affineSpan ℝ F :=
      subset_affineSpan ℝ _ hextra_mem
    have hpair :
        ((((simple_plant_location_x_basis m n i ℓ -
            simple_plant_location_x_basis m n i j),
            simple_plant_location_y_basis n ℓ)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
      -- The reassignment witness contributes the pure `x` generator together with the same
      -- extra-open `y` direction.
      have hvsub :
          simple_plant_location_reassign_point m n j i ℓ -
              simple_plant_location_base_point m n j ∈ D :=
        AffineSubspace.vsub_mem_direction hreassign_aff hbase_aff
      simpa [D, simple_plant_location_reassign_vsub_base, hℓj] using hvsub
    have hy :
        ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D :=
      simple_plant_location_nonanchor_y_basis_mem_y_one_face_direction
        (m := m) (n := n) j ℓ hℓj
    -- Subtract the shared `y`-part to isolate the pure reassignment direction.
    simpa [D] using Submodule.sub_mem D hpair hy

/-- Helper for Exercise 3.22: with at least three facilities, one can choose a facility distinct
from two prescribed ones. -/
theorem simple_plant_location_exists_third_facility
    {n : ℕ} (hn : 3 ≤ n) (a j : Fin n) :
    ∃ b : Fin n, b ≠ a ∧ b ≠ j := by
  exact Fin.exists_ne_and_ne_of_two_lt a j (by omega)

/-- Helper for Exercise 3.22: in the `x i j = 0` face, opening any non-anchor facility while
keeping the anchor different from `j` gives a valid `y`-basis direction. -/
theorem simple_plant_location_nonanchor_y_basis_mem_x_zero_face_direction
    {m n : ℕ} (i : Fin m) (j a ℓ : Fin n) (haj : a ≠ j) (hℓa : ℓ ≠ a) :
    ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_x_zero_face m n i j)).direction := by
  let F := simple_plant_location_x_zero_face m n i j
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  have hja : j ≠ a := fun hja ↦ haj hja.symm
  have hbase_mem : simple_plant_location_base_point m n a ∈ F := by
    refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) a, ?_⟩
    -- Assigning every row to `a ≠ j` forces the distinguished coordinate to vanish.
    simp [simple_plant_location_base_point, hja]
  have hextra_mem : simple_plant_location_extra_open_point m n a ℓ ∈ F := by
    refine ⟨simple_plant_location_extra_open_point_mem_polytope (m := m) (n := n) a ℓ, ?_⟩
    -- Opening an extra facility does not change the zero assignment at `(i,j)`.
    simp [simple_plant_location_extra_open_point, hja]
  have hbase_aff :
      simple_plant_location_base_point m n a ∈ affineSpan ℝ F :=
    subset_affineSpan ℝ _ hbase_mem
  have hextra_aff :
      simple_plant_location_extra_open_point m n a ℓ ∈ affineSpan ℝ F :=
    subset_affineSpan ℝ _ hextra_mem
  have hvsub :
      simple_plant_location_extra_open_point m n a ℓ -
          simple_plant_location_base_point m n a ∈ D :=
    AffineSubspace.vsub_mem_direction hextra_aff hbase_aff
  -- The extra-open witness contributes exactly the non-anchor `y` basis vector.
  simpa [D, simple_plant_location_extra_open_vsub_base, hℓa] using hvsub

/-- Helper for Exercise 3.22: in the `x i j = 0` face, every pure reassignment direction that
does not send row `i` back to facility `j` lies in the face direction. -/
theorem simple_plant_location_pure_x_generator_mem_x_zero_face_direction
    {m n : ℕ} (i : Fin m) (j a : Fin n) (r : Fin m) (ℓ : Fin n)
    (haj : a ≠ j) (hgood : r ≠ i ∨ ℓ ≠ j) :
    ((((simple_plant_location_x_basis m n r ℓ -
        simple_plant_location_x_basis m n r a), (0 : Fin n → ℝ))) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_x_zero_face m n i j)).direction := by
  let F := simple_plant_location_x_zero_face m n i j
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  have hja : j ≠ a := fun hja ↦ haj hja.symm
  by_cases hℓa : ℓ = a
  · -- If `ℓ = a`, the claimed generator is zero.
    subst ℓ
    have hzero :
        ((((simple_plant_location_x_basis m n r a -
            simple_plant_location_x_basis m n r a), (0 : Fin n → ℝ))) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) =
          (0 : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) := by
      ext <;> simp
    rw [hzero]
    exact Submodule.zero_mem D
  · have hbase_mem : simple_plant_location_base_point m n a ∈ F := by
      refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) a, ?_⟩
      -- The anchor base point keeps the distinguished assignment at zero.
      simp [simple_plant_location_base_point, hja]
    have hreassign_mem : simple_plant_location_reassign_point m n a r ℓ ∈ F := by
      refine ⟨simple_plant_location_reassign_point_mem_polytope (m := m) (n := n) a r ℓ, ?_⟩
      by_cases hri : r = i
      · have hℓj : ℓ ≠ j := by
          rcases hgood with hri' | hℓj
          · exact (hri' hri).elim
          · exact hℓj
        have hjℓ : j ≠ ℓ := fun hjℓ ↦ hℓj hjℓ.symm
        subst r
        -- Reassigning row `i` to a facility `ℓ ≠ j` preserves the face equation `x i j = 0`.
        simp [simple_plant_location_reassign_point, hja, hℓj, hjℓ]
      · -- Reassigning a different row leaves row `i` fixed at the anchor `a ≠ j`.
        have hir : i ≠ r := fun hir ↦ hri hir.symm
        simp [simple_plant_location_reassign_point, hja, hri, hir]
    have hbase_aff :
        simple_plant_location_base_point m n a ∈ affineSpan ℝ F :=
      subset_affineSpan ℝ _ hbase_mem
    have hreassign_aff :
        simple_plant_location_reassign_point m n a r ℓ ∈ affineSpan ℝ F :=
      subset_affineSpan ℝ _ hreassign_mem
    have hpair :
        ((((simple_plant_location_x_basis m n r ℓ -
            simple_plant_location_x_basis m n r a),
            simple_plant_location_y_basis n ℓ)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
      -- The reassignment witness contributes the target pure `x` direction together with the
      -- same non-anchor `y` basis vector.
      have hvsub :
          simple_plant_location_reassign_point m n a r ℓ -
              simple_plant_location_base_point m n a ∈ D :=
        AffineSubspace.vsub_mem_direction hreassign_aff hbase_aff
      simpa [D, simple_plant_location_reassign_vsub_base, hℓa] using hvsub
    have hy :
        ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D :=
      simple_plant_location_nonanchor_y_basis_mem_x_zero_face_direction
        (m := m) (n := n) i j a ℓ haj hℓa
    -- Subtract the common `y`-part to isolate the pure reassignment direction.
    simpa [D] using Submodule.sub_mem D hpair hy

/-- Helper for Exercise 3.22: inside the face `x i j = 0`, the anchor facility basis direction
also lies in the face direction once two other anchor choices are available. -/
theorem simple_plant_location_anchor_y_basis_mem_x_zero_face_direction
    {m n : ℕ} (i : Fin m) (j a b : Fin n)
    (haj : a ≠ j) (hba : b ≠ a) (hbj : b ≠ j) :
    ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n a)) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_x_zero_face m n i j)).direction := by
  let F := simple_plant_location_x_zero_face m n i j
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  have hja : j ≠ a := fun hja ↦ haj hja.symm
  have hjb : j ≠ b := fun hjb ↦ hbj hjb.symm
  have hbase_a_mem : simple_plant_location_base_point m n a ∈ F := by
    refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) a, ?_⟩
    -- The base point at `a` is in the face because `a ≠ j`.
    simp [simple_plant_location_base_point, hja]
  have hbase_b_mem : simple_plant_location_base_point m n b ∈ F := by
    refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) b, ?_⟩
    -- The alternate base point at `b ≠ j` also lies in the face.
    simp [simple_plant_location_base_point, hjb]
  have hbase_a_aff :
      simple_plant_location_base_point m n a ∈ affineSpan ℝ F :=
    subset_affineSpan ℝ _ hbase_a_mem
  have hbase_b_aff :
      simple_plant_location_base_point m n b ∈ affineSpan ℝ F :=
    subset_affineSpan ℝ _ hbase_b_mem
  have h_alt :
      ((((∑ r : Fin m,
            (simple_plant_location_x_basis m n r b -
              simple_plant_location_x_basis m n r a)),
          simple_plant_location_y_basis n b -
            simple_plant_location_y_basis n a)) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
    -- Changing the anchor from `a` to `b` is still a difference of two face points.
    have hvsub :
        simple_plant_location_base_point m n b -
            simple_plant_location_base_point m n a ∈ D :=
      AffineSubspace.vsub_mem_direction hbase_b_aff hbase_a_aff
    simpa [D, simple_plant_location_alternate_base_vsub_base, hba] using hvsub
  have hpure_sum_raw :
      (∑ r : Fin m,
          ((((simple_plant_location_x_basis m n r b -
              simple_plant_location_x_basis m n r a), (0 : Fin n → ℝ))) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ D := by
    -- Every rowwise pure reassignment to `b ≠ j` stays inside the same face.
    exact Submodule.sum_mem D fun r _ ↦
      simple_plant_location_pure_x_generator_mem_x_zero_face_direction
        (m := m) (n := n) i j a r b haj (Or.inr hbj)
  have hpure_sum :
      ((((∑ r : Fin m,
            (simple_plant_location_x_basis m n r b -
              simple_plant_location_x_basis m n r a)),
          (0 : Fin n → ℝ))) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
    simpa [simple_plant_location_sum_of_pure_x_pairs_eq_packaged_sum] using hpure_sum_raw
  have hyb :
      ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n b)) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D :=
    simple_plant_location_nonanchor_y_basis_mem_x_zero_face_direction
      (m := m) (n := n) i j a b haj hba
  have hneg_anchor :
      ((((0 : Fin m → Fin n → ℝ), -simple_plant_location_y_basis n a)) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
    -- Remove the pure `x` package and the known non-anchor `y_b` direction from the alternate
    -- base difference to isolate `-(0, y_a)`.
    have hdiff :
        ((((0 : Fin m → Fin n → ℝ),
            simple_plant_location_y_basis n b -
              simple_plant_location_y_basis n a)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
      simpa using Submodule.sub_mem D h_alt hpure_sum
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Submodule.sub_mem D hdiff hyb)
  -- Negating the isolated vector recovers the anchor `y_a` basis direction.
  simpa [D] using Submodule.neg_mem D hneg_anchor

/-- Helper for Exercise 3.22: the face `y j = 1` has direction equal to the ambient row-sum
kernel cut by the additional equation fixing the `j`th `y` coordinate. -/
theorem simple_plant_location_y_one_face_direction_eq
    {m n : ℕ} (hn : 3 ≤ n) (j : Fin n) :
    (affineSpan ℝ (simple_plant_location_y_one_face m n j)).direction =
      (affineSpan ℝ (simple_plant_location_polytope m n)).direction ⊓
        LinearMap.ker (simple_plant_location_y_coordinate m n j) := by
  let F := simple_plant_location_y_one_face m n j
  let FD : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (simple_plant_location_polytope m n)).direction
  let L := simple_plant_location_y_coordinate m n j
  have hsubset : F ⊆ simple_plant_location_polytope m n := by
    intro p hp
    exact hp.1
  have hle_poly : FD ≤ D := by
    -- Any direction of the face is automatically a direction of the ambient polytope.
    simpa [F, FD, D] using AffineSubspace.direction_le (affineSpan_mono ℝ hsubset)
  have hbase_mem : simple_plant_location_base_point m n j ∈ F := by
    refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) j, ?_⟩
    -- The base point at `j` lies on the level set `y j = 1`.
    simp [simple_plant_location_base_point]
  have hle_ker : FD ≤ LinearMap.ker L := by
    -- Every vector in the face direction keeps the fixed `y j = 1` coordinate unchanged.
    simpa [F, FD, L] using
      (simple_plant_location_face_direction_le_level_ker
        (m := m) (n := n) (F := F) (L := L) (δ := 1)
        (x₀ := simple_plant_location_base_point m n j)
        hbase_mem
        (by
          intro x hx
          exact hx.2))
  refine le_antisymm (le_inf hle_poly hle_ker) ?_
  intro v hv
  rcases v with ⟨x, y⟩
  have hvD :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈ D) := hv.1
  have hvL :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈ LinearMap.ker L) := hv.2
  have hvD' :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈
        (affineSpan ℝ (simple_plant_location_polytope m n)).direction) := by
    simpa [D] using hvD
  rw [simple_plant_location_direction_eq_row_sum_ker hn] at hvD'
  have hrow :
      simple_plant_location_rowSum m n ((x, y) :
        (Fin m → Fin n → ℝ) × (Fin n → ℝ)) = 0 :=
    LinearMap.mem_ker.mp hvD'
  have hx : ∀ r, ∑ k, x r k = 0 := by
    -- Ambient-direction membership says that every row sum vanishes.
    intro r
    have hcoord := congrFun hrow r
    simpa [simple_plant_location_rowSum] using hcoord
  have hyj : y j = 0 := by
    -- Membership in the kernel of the coordinate functional fixes the `j`th `y` entry.
    simpa [L, simple_plant_location_y_coordinate] using LinearMap.mem_ker.mp hvL
  have hx_sum_mem :
      (∑ r : Fin m, ∑ ℓ : Fin n,
          x r ℓ •
            ((((simple_plant_location_x_basis m n r ℓ -
                simple_plant_location_x_basis m n r j), (0 : Fin n → ℝ))) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ FD := by
    -- The pure reassignment generators with anchor `j` already lie in the face direction.
    exact Submodule.sum_mem FD fun r _ ↦
      Submodule.sum_mem FD fun ℓ _ ↦
        Submodule.smul_mem FD (x r ℓ)
          (simple_plant_location_pure_x_generator_mem_y_one_face_direction
            (m := m) (n := n) j r ℓ)
  have hx_mem :
      ((((x, (0 : Fin n → ℝ))) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ FD := by
    -- Package the row-sum-zero decomposition of the assignment block.
    rw [← simple_plant_location_paired_x_decomposition_eq (m := m) (n := n) (x := x) j hx]
    exact hx_sum_mem
  have hy_sum_mem :
      (∑ ℓ : Fin n,
          y ℓ •
            ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ FD := by
    -- The `y`-part uses only non-anchor openings; the anchor coefficient vanishes by the kernel
    -- condition `y j = 0`.
    exact Submodule.sum_mem FD fun ℓ _ ↦ by
      by_cases hℓj : ℓ = j
      · subst ℓ
        simpa [hyj] using (Submodule.zero_mem FD :
          (0 : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈ FD)
      · exact Submodule.smul_mem FD (y ℓ)
          (simple_plant_location_nonanchor_y_basis_mem_y_one_face_direction
            (m := m) (n := n) j ℓ hℓj)
  have hy_mem :
      (((((0 : Fin m → Fin n → ℝ), y)) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ FD := by
    -- Package the facility-block basis expansion.
    rw [← simple_plant_location_paired_y_decomposition_eq (m := m) (n := n) y]
    exact hy_sum_mem
  have hsplit :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ))) =
        ((((x, (0 : Fin n → ℝ))) : ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) +
          ((((0 : Fin m → Fin n → ℝ), y)) : ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) := by
    ext <;> simp
  -- Split the target vector into its assignment and facility parts and absorb each part into the
  -- face direction separately.
  rw [hsplit]
  exact Submodule.add_mem FD hx_mem hy_mem

/-- Helper for Exercise 3.22: the face `x i j = 0` has direction equal to the ambient row-sum
kernel cut by the additional equation `x i j = 0`. -/
theorem simple_plant_location_x_zero_face_direction_eq
    {m n : ℕ} (hn : 3 ≤ n) (i : Fin m) (j : Fin n) :
    (affineSpan ℝ (simple_plant_location_x_zero_face m n i j)).direction =
      (affineSpan ℝ (simple_plant_location_polytope m n)).direction ⊓
        LinearMap.ker (simple_plant_location_x_coordinate m n i j) := by
  let F := simple_plant_location_x_zero_face m n i j
  let FD : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (simple_plant_location_polytope m n)).direction
  let L := simple_plant_location_x_coordinate m n i j
  have hsubset : F ⊆ simple_plant_location_polytope m n := by
    intro p hp
    exact hp.1
  have hle_poly : FD ≤ D := by
    -- Any direction of the equality face is already an ambient direction of the polytope.
    simpa [F, FD, D] using AffineSubspace.direction_le (affineSpan_mono ℝ hsubset)
  rcases simple_plant_location_x_zero_face_nonempty (m := m) (n := n) hn i j with ⟨x₀, hx₀⟩
  have hle_ker : FD ≤ LinearMap.ker L := by
    -- Along the face, the distinguished assignment coordinate stays fixed at `0`.
    simpa [F, FD, L] using
      (simple_plant_location_face_direction_le_level_ker
        (m := m) (n := n) (F := F) (L := L) (δ := 0) (x₀ := x₀)
        hx₀
        (by
          intro x hx
          exact hx.2))
  have hn_two : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn
  obtain ⟨a, haj⟩ := simple_plant_location_exists_other_facility hn_two j
  obtain ⟨b, hba, hbj⟩ := simple_plant_location_exists_third_facility hn a j
  refine le_antisymm (le_inf hle_poly hle_ker) ?_
  intro v hv
  rcases v with ⟨x, y⟩
  have hvD :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈ D) := hv.1
  have hvL :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈ LinearMap.ker L) := hv.2
  have hvD' :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈
        (affineSpan ℝ (simple_plant_location_polytope m n)).direction) := by
    simpa [D] using hvD
  rw [simple_plant_location_direction_eq_row_sum_ker hn] at hvD'
  have hrow :
      simple_plant_location_rowSum m n ((x, y) :
        (Fin m → Fin n → ℝ) × (Fin n → ℝ)) = 0 :=
    LinearMap.mem_ker.mp hvD'
  have hx : ∀ r, ∑ k, x r k = 0 := by
    -- Ambient-direction membership again says that every row sum vanishes.
    intro r
    have hcoord := congrFun hrow r
    simpa [simple_plant_location_rowSum] using hcoord
  have hxij : x i j = 0 := by
    -- The extra kernel condition forces the distinguished assignment coordinate to vanish.
    simpa [L, simple_plant_location_x_coordinate] using LinearMap.mem_ker.mp hvL
  have hx_sum_mem :
      (∑ r : Fin m, ∑ ℓ : Fin n,
          x r ℓ •
            ((((simple_plant_location_x_basis m n r ℓ -
                simple_plant_location_x_basis m n r a), (0 : Fin n → ℝ))) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ FD := by
    -- The only potentially forbidden generator is the `(i,j)` one, but its coefficient is zero.
    exact Submodule.sum_mem FD fun r _ ↦
      Submodule.sum_mem FD fun ℓ _ ↦ by
        by_cases hri : r = i
        · by_cases hℓj : ℓ = j
          · subst r
            subst ℓ
            simpa [hxij] using (Submodule.zero_mem FD :
              (0 : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈ FD)
          · exact Submodule.smul_mem FD (x r ℓ)
              (simple_plant_location_pure_x_generator_mem_x_zero_face_direction
                (m := m) (n := n) i j a r ℓ haj (Or.inr hℓj))
        · exact Submodule.smul_mem FD (x r ℓ)
            (simple_plant_location_pure_x_generator_mem_x_zero_face_direction
              (m := m) (n := n) i j a r ℓ haj (Or.inl hri))
  have hx_mem :
      ((((x, (0 : Fin n → ℝ))) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ FD := by
    -- Package the row-sum-zero decomposition using the anchor `a ≠ j`.
    rw [← simple_plant_location_paired_x_decomposition_eq (m := m) (n := n) (x := x) a hx]
    exact hx_sum_mem
  have hy_sum_mem :
      (∑ ℓ : Fin n,
          y ℓ •
            ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ FD := by
    -- Non-anchor `y` directions come from extra-open witnesses, while the anchor direction is
    -- recovered from two alternate base points inside the same face.
    exact Submodule.sum_mem FD fun ℓ _ ↦ by
      by_cases hℓa : ℓ = a
      · subst ℓ
        exact Submodule.smul_mem FD (y a)
          (simple_plant_location_anchor_y_basis_mem_x_zero_face_direction
            (m := m) (n := n) i j a b haj hba hbj)
      · exact Submodule.smul_mem FD (y ℓ)
          (simple_plant_location_nonanchor_y_basis_mem_x_zero_face_direction
            (m := m) (n := n) i j a ℓ haj hℓa)
  have hy_mem :
      (((((0 : Fin m → Fin n → ℝ), y)) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) ∈ FD := by
    -- Package the facility-block decomposition into the product space.
    rw [← simple_plant_location_paired_y_decomposition_eq (m := m) (n := n) y]
    exact hy_sum_mem
  have hsplit :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ))) =
        ((((x, (0 : Fin n → ℝ))) : ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) +
          ((((0 : Fin m → Fin n → ℝ), y)) : ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))) := by
    ext <;> simp
  -- Split the target vector into its pure assignment and pure facility parts.
  rw [hsplit]
  exact Submodule.add_mem FD hx_mem hy_mem

/-- Part (2) of Exercise 3.22: for every customer `i` and facility `j`, the equality set `x i j = 0`
defines a facet of the simple plant location polytope. -/
-- TODO: Show this face is exposed by the coordinate functional `-xᵢⱼ`, then prove its affine
-- dimension is one less than the whole polytope using a witness family on the equality face.
theorem simple_plant_location_x_nonneg_facet
    {m n : ℕ} (hm : 2 ≤ m) (hn : 3 ≤ n) (i : Fin m) (j : Fin n) :
    IsFacetOf (simple_plant_location_polytope m n)
      (simple_plant_location_x_zero_face m n i j) := by
  rw [isFacetOf_iff]
  refine ⟨simple_plant_location_x_zero_face_nonempty (m := m) (n := n) hn i j, ?_, ?_⟩
  · -- Route correction: the exposed-face part is now closed separately; the remaining blocker is
    -- exactly the codimension-one affine-dimension computation inside the equality face.
    exact simple_plant_location_x_zero_face_isExposed (m := m) (n := n) hn i j
  · let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
      (affineSpan ℝ (simple_plant_location_polytope m n)).direction
    let L := simple_plant_location_x_coordinate m n i j
    have hn_two : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn
    obtain ⟨a, haj⟩ := simple_plant_location_exists_other_facility hn_two j
    have hwD :
        ((((simple_plant_location_x_basis m n i j -
            simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
      -- The witness is one of the ambient pure reassignment directions.
      simpa [D, sub_eq_add_neg, add_comm, add_left_comm] using
        (simple_plant_location_pure_x_generator_mem_direction (m := m) (n := n) a i j)
    have hw_eval :
        L ((((simple_plant_location_x_basis m n i j -
            simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) = 1 := by
      -- The chosen witness changes exactly the distinguished assignment coordinate by one unit.
      simp [L, simple_plant_location_x_coordinate, simple_plant_location_x_basis, haj]
    -- The face direction is exactly the ambient row-sum kernel cut by `x i j = 0`, so the
    -- generic codimension-one lemma applies immediately.
    calc
      Module.finrank ℝ (affineSpan ℝ (simple_plant_location_x_zero_face m n i j)).direction + 1
          = Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 := by
              rw [simple_plant_location_x_zero_face_direction_eq (m := m) (n := n) hn i j]
      _ = Module.finrank ℝ D := by
            exact simple_plant_location_finrank_inf_ker_add_one_of_eval_one D L hwD hw_eval
      _ = Module.finrank ℝ (affineSpan ℝ (simple_plant_location_polytope m n)).direction := by
            rfl

/-- Part (3) of Exercise 3.22: for every facility `j`, the equality set `y j = 1`
defines a facet of the simple plant location polytope. -/
-- TODO: Show this face is exposed by the coordinate functional `yⱼ`, then use a witness family
-- with facility `j` kept open to get the codimension-one affine-span computation.
theorem simple_plant_location_y_le_one_facet
    {m n : ℕ} (hm : 2 ≤ m) (hn : 3 ≤ n) (j : Fin n) :
    IsFacetOf (simple_plant_location_polytope m n)
      (simple_plant_location_y_one_face m n j) := by
  rw [isFacetOf_iff]
  refine ⟨simple_plant_location_y_one_face_nonempty (m := m) (n := n) j, ?_, ?_⟩
  · -- Route correction: the exposed-face part is now closed separately; the remaining blocker is
    -- the source-faithful codimension-one witness family with facility `j` fixed open.
    exact simple_plant_location_y_one_face_isExposed (m := m) (n := n) j
  · let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
      (affineSpan ℝ (simple_plant_location_polytope m n)).direction
    let L := simple_plant_location_y_coordinate m n j
    have hn_two : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn
    obtain ⟨a, haj⟩ := simple_plant_location_exists_other_facility hn_two j
    have hwD :
        ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n j)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
      -- The anchor `y_j` direction is already an ambient direction of the polytope.
      simpa [D] using
        (simple_plant_location_anchor_y_direction_from_alternate_base
          (m := m) (n := n) j a haj)
    have hw_eval :
        L ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n j)) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) = 1 := by
      -- The witness is the unit vector at the fixed facility coordinate.
      simp [L, simple_plant_location_y_coordinate, simple_plant_location_y_basis]
    -- The face direction is the ambient row-sum kernel cut by `y j = 0`.
    calc
      Module.finrank ℝ (affineSpan ℝ (simple_plant_location_y_one_face m n j)).direction + 1
          = Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 := by
              rw [simple_plant_location_y_one_face_direction_eq (m := m) (n := n) hn j]
      _ = Module.finrank ℝ D := by
            exact simple_plant_location_finrank_inf_ker_add_one_of_eval_one D L hwD hw_eval
      _ = Module.finrank ℝ (affineSpan ℝ (simple_plant_location_polytope m n)).direction := by
            rfl

/-- Helper for Exercise 3.22: inside the linking face `x i j = y j`, opening a different
facility while keeping `j` as the anchor gives the corresponding non-anchor `y` basis
direction. -/
theorem simple_plant_location_nonanchor_y_basis_mem_linking_face_direction
    {m n : ℕ} (i : Fin m) (j ℓ : Fin n) (hℓj : ℓ ≠ j) :
    ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_linking_face m n i j)).direction := by
  let F := simple_plant_location_linking_face m n i j
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  have hbase_mem : simple_plant_location_base_point m n j ∈ F := by
    refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) j, ?_⟩
    -- The base point at `j` satisfies `x i j = y j = 1`.
    simp [simple_plant_location_base_point]
  have hextra_mem : simple_plant_location_extra_open_point m n j ℓ ∈ F := by
    refine ⟨simple_plant_location_extra_open_point_mem_polytope (m := m) (n := n) j ℓ, ?_⟩
    -- Opening one extra non-anchor facility keeps the linking equality tight at `j`.
    simp [simple_plant_location_extra_open_point, hℓj]
  have hbase_aff :
      simple_plant_location_base_point m n j ∈ affineSpan ℝ F :=
    subset_affineSpan ℝ _ hbase_mem
  have hextra_aff :
      simple_plant_location_extra_open_point m n j ℓ ∈ affineSpan ℝ F :=
    subset_affineSpan ℝ _ hextra_mem
  have hvsub :
      simple_plant_location_extra_open_point m n j ℓ -
          simple_plant_location_base_point m n j ∈ D :=
    AffineSubspace.vsub_mem_direction hextra_aff hbase_aff
  -- The extra-open witness differs from the base point by exactly one non-anchor `y` basis.
  simpa [D, simple_plant_location_extra_open_vsub_base, hℓj] using hvsub

/-- Helper for Exercise 3.22: in the linking face `x i j = y j`, every pure reassignment on a
row `r ≠ i` lies in the face direction. -/
theorem simple_plant_location_off_row_pure_x_generator_mem_linking_face_direction
    {m n : ℕ} (i r : Fin m) (j ℓ : Fin n) (hri : r ≠ i) :
    ((((simple_plant_location_x_basis m n r ℓ -
        simple_plant_location_x_basis m n r j), (0 : Fin n → ℝ))) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_linking_face m n i j)).direction := by
  let F := simple_plant_location_linking_face m n i j
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  by_cases hℓj : ℓ = j
  · -- If `ℓ = j`, the claimed generator is zero.
    subst ℓ
    have hzero :
        ((((simple_plant_location_x_basis m n r j -
            simple_plant_location_x_basis m n r j), (0 : Fin n → ℝ))) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) =
          (0 : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) := by
      ext <;> simp
    rw [hzero]
    exact Submodule.zero_mem D
  · have hbase_mem : simple_plant_location_base_point m n j ∈ F := by
      refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) j, ?_⟩
      -- The base point at `j` lies on the linking face.
      simp [simple_plant_location_base_point]
    have hreassign_mem : simple_plant_location_reassign_point m n j r ℓ ∈ F := by
      refine ⟨simple_plant_location_reassign_point_mem_polytope (m := m) (n := n) j r ℓ, ?_⟩
      -- Reassigning a different row keeps row `i` anchored at `j`, so `x i j = y j = 1`.
      have hir : i ≠ r := fun hir ↦ hri hir.symm
      simp [simple_plant_location_reassign_point, hri, hir, hℓj]
    have hbase_aff :
        simple_plant_location_base_point m n j ∈ affineSpan ℝ F :=
      subset_affineSpan ℝ _ hbase_mem
    have hreassign_aff :
        simple_plant_location_reassign_point m n j r ℓ ∈ affineSpan ℝ F :=
      subset_affineSpan ℝ _ hreassign_mem
    have hpair :
        ((((simple_plant_location_x_basis m n r ℓ -
            simple_plant_location_x_basis m n r j),
            simple_plant_location_y_basis n ℓ)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
      -- The reassignment witness contributes the desired pure `x` generator plus the same
      -- non-anchor `y` direction.
      have hvsub :
          simple_plant_location_reassign_point m n j r ℓ -
              simple_plant_location_base_point m n j ∈ D :=
        AffineSubspace.vsub_mem_direction hreassign_aff hbase_aff
      simpa [D, simple_plant_location_reassign_vsub_base, hℓj] using hvsub
    have hy :
        ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D :=
      simple_plant_location_nonanchor_y_basis_mem_linking_face_direction
        (m := m) (n := n) i j ℓ hℓj
    -- Subtract the shared `y` component to isolate the pure off-row reassignment direction.
    simpa [D] using Submodule.sub_mem D hpair hy

/-- Helper for Exercise 3.22: in the linking face `x i j = y j`, the distinguished row admits
the mixed generator that couples the move to facility `j` with the `y j` direction. -/
theorem simple_plant_location_mixed_generator_mem_linking_face_direction
    {m n : ℕ} (i : Fin m) (j a : Fin n) (haj : a ≠ j) :
    ((((simple_plant_location_x_basis m n i j -
        simple_plant_location_x_basis m n i a), simple_plant_location_y_basis n j)) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_linking_face m n i j)).direction := by
  let F := simple_plant_location_linking_face m n i j
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  have hja : j ≠ a := fun hja ↦ haj hja.symm
  have hbase_mem : simple_plant_location_base_point m n a ∈ F := by
    refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) a, ?_⟩
    -- At the base point anchored at `a ≠ j`, both sides of the linking equality vanish.
    simp [simple_plant_location_base_point, hja]
  have hreassign_mem : simple_plant_location_reassign_point m n a i j ∈ F := by
    refine ⟨simple_plant_location_reassign_point_mem_polytope (m := m) (n := n) a i j, ?_⟩
    -- Reassigning row `i` to `j` opens `j` and sets `x i j = y j = 1`.
    simp [simple_plant_location_reassign_point, haj]
  have hbase_aff :
      simple_plant_location_base_point m n a ∈ affineSpan ℝ F :=
    subset_affineSpan ℝ _ hbase_mem
  have hreassign_aff :
      simple_plant_location_reassign_point m n a i j ∈ affineSpan ℝ F :=
    subset_affineSpan ℝ _ hreassign_mem
  have hvsub :
      simple_plant_location_reassign_point m n a i j -
          simple_plant_location_base_point m n a ∈ D :=
    AffineSubspace.vsub_mem_direction hreassign_aff hbase_aff
  -- This difference is exactly the mixed generator allowed by the linking equation.
  simpa [D, simple_plant_location_reassign_vsub_base, hja] using hvsub

/-- Helper for Exercise 3.22: in the linking face `x i j = y j`, row `i` admits pure
reassignment generators only toward facilities `ℓ ≠ j`. -/
theorem simple_plant_location_row_i_pure_x_generator_mem_linking_face_direction
    {m n : ℕ} (i : Fin m) (j a ℓ : Fin n) (haj : a ≠ j) (hℓj : ℓ ≠ j) :
    ((((simple_plant_location_x_basis m n i ℓ -
        simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
      ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈
      (affineSpan ℝ (simple_plant_location_linking_face m n i j)).direction := by
  let F := simple_plant_location_linking_face m n i j
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  have hja : j ≠ a := fun hja ↦ haj hja.symm
  by_cases hℓa : ℓ = a
  · -- If `ℓ = a`, the claimed generator is zero.
    subst ℓ
    have hzero :
        ((((simple_plant_location_x_basis m n i a -
            simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) =
          (0 : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) := by
      ext <;> simp
    rw [hzero]
    exact Submodule.zero_mem D
  · have hbase_mem : simple_plant_location_base_point m n a ∈ F := by
      refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) a, ?_⟩
      -- The base point anchored at `a ≠ j` satisfies `x i j = y j = 0`.
      simp [simple_plant_location_base_point, hja]
    have hreassign_mem : simple_plant_location_reassign_point m n a i ℓ ∈ F := by
      refine ⟨simple_plant_location_reassign_point_mem_polytope (m := m) (n := n) a i ℓ, ?_⟩
      -- Reassigning row `i` to a facility `ℓ ≠ j` still leaves the linking equality at zero.
      simp [simple_plant_location_reassign_point, hja, hℓj]
    have hbase_aff :
        simple_plant_location_base_point m n a ∈ affineSpan ℝ F :=
      subset_affineSpan ℝ _ hbase_mem
    have hreassign_aff :
        simple_plant_location_reassign_point m n a i ℓ ∈ affineSpan ℝ F :=
      subset_affineSpan ℝ _ hreassign_mem
    have hpair :
        ((((simple_plant_location_x_basis m n i ℓ -
            simple_plant_location_x_basis m n i a),
            simple_plant_location_y_basis n ℓ)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
      -- The row-`i` reassignment contributes the target pure `x` generator together with the
      -- corresponding non-anchor `y` basis direction.
      have hvsub :
          simple_plant_location_reassign_point m n a i ℓ -
              simple_plant_location_base_point m n a ∈ D :=
        AffineSubspace.vsub_mem_direction hreassign_aff hbase_aff
      simpa [D, simple_plant_location_reassign_vsub_base, hℓa] using hvsub
    have hy :
        ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D :=
      simple_plant_location_nonanchor_y_basis_mem_linking_face_direction
        (m := m) (n := n) i j ℓ hℓj
    -- Subtract the shared non-anchor `y` direction to isolate the pure row-`i` generator.
    simpa [D] using Submodule.sub_mem D hpair hy

/-- Helper for Exercise 3.22: the linking face `x i j = y j` has direction equal to the ambient
row-sum kernel cut by the linking-gap kernel. -/
theorem simple_plant_location_linking_face_direction_eq
    {m n : ℕ} (hn : 3 ≤ n) (i : Fin m) (j : Fin n) :
    (affineSpan ℝ (simple_plant_location_linking_face m n i j)).direction =
      (affineSpan ℝ (simple_plant_location_polytope m n)).direction ⊓
        LinearMap.ker (simple_plant_location_linking_gap m n i j) := by
  let F := simple_plant_location_linking_face m n i j
  let FD : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (simple_plant_location_polytope m n)).direction
  let L := simple_plant_location_linking_gap m n i j
  let offVec : Fin m → Fin n → ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
    fun r ℓ ↦
      ((((simple_plant_location_x_basis m n r ℓ -
          simple_plant_location_x_basis m n r j), (0 : Fin n → ℝ))) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))
  let yVec : Fin n → ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
    fun ℓ ↦
      ((((0 : Fin m → Fin n → ℝ), simple_plant_location_y_basis n ℓ)) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))
  have hsubset : F ⊆ simple_plant_location_polytope m n := by
    intro p hp
    exact hp.1
  have hle_poly : FD ≤ D := by
    -- Any direction of the equality face is already an ambient direction of the polytope.
    simpa [F, FD, D] using AffineSubspace.direction_le (affineSpan_mono ℝ hsubset)
  have hbase_mem : simple_plant_location_base_point m n j ∈ F := by
    refine ⟨simple_plant_location_base_point_mem_polytope (m := m) (n := n) j, ?_⟩
    -- The base point at `j` lies on the linking equality.
    simp [simple_plant_location_base_point]
  have hle_ker : FD ≤ LinearMap.ker L := by
    -- Every vector in the face direction preserves the fixed level set `x i j - y j = 0`.
    simpa [F, FD, L, simple_plant_location_linking_gap, simple_plant_location_x_coordinate,
      simple_plant_location_y_coordinate, sub_eq_add_neg] using
      (simple_plant_location_face_direction_le_level_ker
        (m := m) (n := n) (F := F) (L := L) (δ := 0)
        (x₀ := simple_plant_location_base_point m n j)
        hbase_mem
        (by
          intro x hx
          simpa [L, simple_plant_location_linking_gap, simple_plant_location_x_coordinate,
            simple_plant_location_y_coordinate, sub_eq_add_neg] using
            sub_eq_zero.mpr hx.2))
  have hn_two : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn
  obtain ⟨a, haj⟩ := simple_plant_location_exists_other_facility hn_two j
  let rowIVec : Fin n → ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
    fun ℓ ↦
      ((((simple_plant_location_x_basis m n i ℓ -
          simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
        ((Fin m → Fin n → ℝ) × (Fin n → ℝ)))
  refine le_antisymm (le_inf hle_poly hle_ker) ?_
  intro v hv
  rcases v with ⟨x, y⟩
  let xOff : Fin m → Fin n → ℝ := fun r ℓ ↦ if r = i then 0 else x r ℓ
  let xRow : Fin m → Fin n → ℝ := fun r ℓ ↦ if r = i then x r ℓ else 0
  let y' : Fin n → ℝ := fun ℓ ↦ if ℓ = j then x i j else y ℓ
  have hvD :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈ D) := hv.1
  have hvL :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈ LinearMap.ker L) := hv.2
  have hvD' :
      (((x, y) : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) ∈
        (affineSpan ℝ (simple_plant_location_polytope m n)).direction) := by
    simpa [D] using hvD
  rw [simple_plant_location_direction_eq_row_sum_ker hn] at hvD'
  have hrow :
      simple_plant_location_rowSum m n ((x, y) :
        (Fin m → Fin n → ℝ) × (Fin n → ℝ)) = 0 :=
    LinearMap.mem_ker.mp hvD'
  have hx : ∀ r, ∑ k, x r k = 0 := by
    -- Ambient-direction membership forces every assignment row sum to vanish.
    intro r
    have hcoord := congrFun hrow r
    simpa [simple_plant_location_rowSum] using hcoord
  have hyj : x i j = y j := by
    -- The additional kernel equation is exactly the linking equality on the direction vector.
    simpa [L, simple_plant_location_linking_gap, simple_plant_location_x_coordinate,
      simple_plant_location_y_coordinate, sub_eq_zero] using LinearMap.mem_ker.mp hvL
  have hxOff : ∀ r, ∑ k, xOff r k = 0 := by
    -- The off-row matrix keeps the original zero row sums away from row `i` and vanishes on row
    -- `i` itself.
    intro r
    by_cases hri : r = i
    · subst r
      simp [xOff]
    · simp [xOff, hri, hx r]
  have hxRow : ∀ r, ∑ k, xRow r k = 0 := by
    -- The row-`i` matrix keeps only the distinguished row, whose sum is still zero.
    intro r
    by_cases hri : r = i
    · subst r
      simp [xRow, hx i]
    · simp [xRow, hri]
  have hoff_row_sum_mem :
      (Finset.sum (Finset.univ.erase i) (fun r : Fin m ↦ ∑ ℓ : Fin n, x r ℓ • offVec r ℓ)) ∈ FD := by
    -- Every off-row generator already lies in the linking-face direction.
    exact Submodule.sum_mem FD fun r hr ↦
      Submodule.sum_mem FD fun ℓ _ ↦
        Submodule.smul_mem FD (x r ℓ)
          (simple_plant_location_off_row_pure_x_generator_mem_linking_face_direction
            (m := m) (n := n) i r j ℓ (Finset.mem_erase.mp hr).1)
  have hoff_row_eq :
      (Finset.sum (Finset.univ.erase i) (fun r : Fin m ↦ ∑ ℓ : Fin n,
          x r ℓ • offVec r ℓ)) =
        (((xOff, (0 : Fin n → ℝ))) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
    have hfull :
        (∑ r : Fin m, ∑ ℓ : Fin n, xOff r ℓ • offVec r ℓ) =
          (((xOff, (0 : Fin n → ℝ))) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
      -- Package the off-row part with the standard kernel decomposition anchored at `j`.
      simpa [offVec] using
        (simple_plant_location_paired_x_decomposition_eq (m := m) (n := n) (x := xOff) j hxOff)
    have hrewrite :
        (Finset.sum (Finset.univ.erase i) (fun r : Fin m ↦ ∑ ℓ : Fin n,
            x r ℓ • offVec r ℓ)) =
          Finset.sum (Finset.univ.erase i) (fun r : Fin m ↦ ∑ ℓ : Fin n, xOff r ℓ • offVec r ℓ) := by
      -- On rows different from `i`, the masked matrix `xOff` agrees with `x`.
      refine Finset.sum_congr rfl ?_
      intro r hr
      have hri : r ≠ i := (Finset.mem_erase.mp hr).1
      simp [xOff, hri]
    calc
      Finset.sum (Finset.univ.erase i) (fun r : Fin m ↦ ∑ ℓ : Fin n, x r ℓ • offVec r ℓ)
          = Finset.sum (Finset.univ.erase i) (fun r : Fin m ↦ ∑ ℓ : Fin n, xOff r ℓ • offVec r ℓ) := hrewrite
      _ = ∑ r : Fin m, ∑ ℓ : Fin n, xOff r ℓ • offVec r ℓ := by
            rw [← Finset.sum_erase_add (s := Finset.univ) (a := i)
              (f := fun r : Fin m ↦ ∑ ℓ : Fin n, xOff r ℓ • offVec r ℓ) (by simp : i ∈ Finset.univ)]
            simp [xOff, offVec]
      _ = (((xOff, (0 : Fin n → ℝ))) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := hfull
  have hrow_i_sum_mem :
      (Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ x i ℓ • rowIVec ℓ)) ∈ FD := by
    -- The pure row-`i` generators are allowed exactly away from facility `j`.
    exact Submodule.sum_mem FD fun ℓ hℓ ↦
      Submodule.smul_mem FD (x i ℓ)
        (simple_plant_location_row_i_pure_x_generator_mem_linking_face_direction
          (m := m) (n := n) i j a ℓ haj (Finset.mem_erase.mp hℓ).1)
  have hmixed_mem :
      x i j •
          ((((simple_plant_location_x_basis m n i j -
              simple_plant_location_x_basis m n i a), simple_plant_location_y_basis n j)) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ FD := by
    -- The distinguished mixed generator is also available in the face direction.
    exact Submodule.smul_mem FD (x i j)
      (simple_plant_location_mixed_generator_mem_linking_face_direction
        (m := m) (n := n) i j a haj)
  have hy_sum_mem :
      (Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ y ℓ • yVec ℓ)) ∈ FD := by
    -- Non-anchor facility directions remain available in the linking face.
    exact Submodule.sum_mem FD fun ℓ hℓ ↦
      Submodule.smul_mem FD (y ℓ)
        (simple_plant_location_nonanchor_y_basis_mem_linking_face_direction
          (m := m) (n := n) i j ℓ (Finset.mem_erase.mp hℓ).1)
  have hrow_i_eq :
      (x i j • rowIVec j + Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ x i ℓ • rowIVec ℓ)) =
        (((xRow, (0 : Fin n → ℝ))) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
    have hfull :
        (∑ ℓ : Fin n, x i ℓ • rowIVec ℓ) =
          (((xRow, (0 : Fin n → ℝ))) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
      -- The row-`i` part is the masked matrix `xRow`, decomposed against the anchor `a`.
      calc
        ∑ ℓ : Fin n, x i ℓ • rowIVec ℓ
            = ∑ r : Fin m, ∑ ℓ : Fin n, xRow r ℓ •
                ((((simple_plant_location_x_basis m n r ℓ -
                    simple_plant_location_x_basis m n r a), (0 : Fin n → ℝ))) :
                  ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
                  rw [Finset.sum_eq_single i]
                  · simp [rowIVec, xRow]
                  · intro r _ hri
                    simp [xRow, hri]
                  · intro hi
                    simp at hi
        _ = (((xRow, (0 : Fin n → ℝ))) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
              simpa [xRow] using
                (simple_plant_location_paired_x_decomposition_eq
                  (m := m) (n := n) (x := xRow) a hxRow)
    calc
      x i j • rowIVec j + Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ x i ℓ • rowIVec ℓ)
          = ∑ ℓ : Fin n, x i ℓ • rowIVec ℓ := by
              simpa [add_comm] using
                (Finset.sum_erase_add (s := Finset.univ)
                  (f := fun ℓ : Fin n ↦ x i ℓ • rowIVec ℓ) (by simp : j ∈ Finset.univ))
      _ = (((xRow, (0 : Fin n → ℝ))) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := hfull
  have hy_eq : y' = y := by
    -- Replacing the `j`th coordinate of `y` by `x i j` does nothing because `x i j = y j`.
    ext ℓ
    by_cases hℓj : ℓ = j
    · subst ℓ
      simpa [y'] using hyj
    · simp [y', hℓj]
  have hy_split_eq :
      (x i j • yVec j + Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ y ℓ • yVec ℓ)) =
        ((((0 : Fin m → Fin n → ℝ), y)) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
    have hfull :
        (∑ ℓ : Fin n, y' ℓ • yVec ℓ) =
          ((((0 : Fin m → Fin n → ℝ), y')) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
      -- The modified facility vector `y'` packages into the standard `y`-basis expansion.
      simpa [yVec] using simple_plant_location_paired_y_decomposition_eq (m := m) (n := n) y'
    have hrewrite :
        x i j • yVec j + Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ y ℓ • yVec ℓ) =
          x i j • yVec j + Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ y' ℓ • yVec ℓ) := by
      -- Away from `j`, the modified vector `y'` agrees with `y`.
      refine congrArg (fun z ↦ x i j • yVec j + z) ?_
      refine Finset.sum_congr rfl ?_
      intro ℓ hℓ
      have hℓj : ℓ ≠ j := (Finset.mem_erase.mp hℓ).1
      simp [y', hℓj]
    calc
      x i j • yVec j + Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ y ℓ • yVec ℓ)
          = x i j • yVec j + Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ y' ℓ • yVec ℓ) := hrewrite
      _ = ∑ ℓ : Fin n, y' ℓ • yVec ℓ := by
            simpa [y', add_comm] using
              (Finset.sum_erase_add (s := Finset.univ)
                (f := fun ℓ : Fin n ↦ y' ℓ • yVec ℓ) (by simp : j ∈ Finset.univ))
      _ = ((((0 : Fin m → Fin n → ℝ), y')) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := hfull
      _ = ((((0 : Fin m → Fin n → ℝ), y)) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
            simpa [hy_eq]
  have hrow_i_and_y_eq :
      ((x i j •
          ((((simple_plant_location_x_basis m n i j -
              simple_plant_location_x_basis m n i a), simple_plant_location_y_basis n j)) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) +
          Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ x i ℓ • rowIVec ℓ)) +
        Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ y ℓ • yVec ℓ)) =
          (((xRow, y)) : ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
    have hmixed_split :
        x i j •
            ((((simple_plant_location_x_basis m n i j -
                simple_plant_location_x_basis m n i a), simple_plant_location_y_basis n j)) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) =
          x i j • rowIVec j + x i j • yVec j := by
      -- Split the mixed generator into its pure `x` part and its `y j` part.
      ext <;> simp [rowIVec, yVec]
    calc
      (x i j •
          ((((simple_plant_location_x_basis m n i j -
              simple_plant_location_x_basis m n i a), simple_plant_location_y_basis n j)) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) +
          Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ x i ℓ • rowIVec ℓ)) +
        Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ y ℓ • yVec ℓ)
          = (x i j • rowIVec j + Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ x i ℓ • rowIVec ℓ)) +
              (x i j • yVec j + Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ y ℓ • yVec ℓ)) := by
                rw [hmixed_split]
                ac_rfl
      _ = (((xRow, (0 : Fin n → ℝ))) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) +
            ((((0 : Fin m → Fin n → ℝ), y)) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
              rw [hrow_i_eq, hy_split_eq]
      _ = (((xRow, y)) : ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
            ext <;> simp [xRow]
  have hsplit :
      (Finset.sum (Finset.univ.erase i) (fun r : Fin m ↦ ∑ ℓ : Fin n, x r ℓ • offVec r ℓ)) +
        ((x i j •
            ((((simple_plant_location_x_basis m n i j -
                simple_plant_location_x_basis m n i a), simple_plant_location_y_basis n j)) :
              ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) +
            Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ x i ℓ • rowIVec ℓ)) +
          Finset.sum (Finset.univ.erase j) (fun ℓ : Fin n ↦ y ℓ • yVec ℓ)) =
        (((x, y)) : ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) := by
    -- The off-row package plus the row-`i`/`y` package reconstruct the full vector `(x,y)`.
    rw [hoff_row_eq, hrow_i_and_y_eq]
    refine Prod.ext ?_ ?_
    · ext r ℓ
      by_cases hri : r = i
      · subst r
        simp [xOff, xRow]
      · simp [xOff, xRow, hri]
    · ext ℓ
      simp
  -- Split the target vector into the off-row, mixed-row, and non-anchor `y` pieces, each of
  -- which already lies in the linking-face direction.
  rw [← hsplit]
  exact Submodule.add_mem FD hoff_row_sum_mem <|
    Submodule.add_mem FD (Submodule.add_mem FD hmixed_mem hrow_i_sum_mem) hy_sum_mem

/-- Exercise 3.22 (4): for every customer `i` and facility `j`, the equality set
`x i j = y j` defines a facet of the simple plant location polytope. -/
-- TODO: Show this face is exposed by the functional `yⱼ - xᵢⱼ`, then build the adapted witness
-- family on the equality face to prove the codimension-one affine dimension.
theorem simple_plant_location_x_le_y_facet
    {m n : ℕ} (hm : 2 ≤ m) (hn : 3 ≤ n) (i : Fin m) (j : Fin n) :
    IsFacetOf (simple_plant_location_polytope m n)
      (simple_plant_location_linking_face m n i j) := by
  rw [isFacetOf_iff]
  refine ⟨simple_plant_location_linking_face_nonempty (m := m) (n := n) i j, ?_, ?_⟩
  · -- Route correction: the exposed-face part is now closed separately; the remaining blocker is
    -- the mixed witness-family codimension computation inside the linking equality face.
    exact simple_plant_location_linking_face_isExposed (m := m) (n := n) i j
  · let D : Submodule ℝ ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
      (affineSpan ℝ (simple_plant_location_polytope m n)).direction
    let L := simple_plant_location_linking_gap m n i j
    have hn_two : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn
    obtain ⟨a, haj⟩ := simple_plant_location_exists_other_facility hn_two j
    have hwD :
        ((((simple_plant_location_x_basis m n i j -
            simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
          ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) ∈ D := by
      -- The ambient witness is the pure reassignment generator from the global polytope
      -- direction; it need not belong to the face direction itself.
      simpa [D, sub_eq_add_neg, add_comm, add_left_comm] using
        (simple_plant_location_pure_x_generator_mem_direction (m := m) (n := n) a i j)
    have hw_eval :
        L ((((simple_plant_location_x_basis m n i j -
            simple_plant_location_x_basis m n i a), (0 : Fin n → ℝ))) :
            ((Fin m → Fin n → ℝ) × (Fin n → ℝ))) = 1 := by
      -- The witness changes `x i j` by one unit and has zero `y` component.
      simp [L, simple_plant_location_linking_gap, simple_plant_location_x_coordinate,
        simple_plant_location_y_coordinate, simple_plant_location_x_basis, haj]
    -- The linking-face direction is the ambient direction intersected with the linking-gap
    -- kernel, so the generic codimension-one lemma applies exactly as in the previous facets.
    calc
      Module.finrank ℝ (affineSpan ℝ (simple_plant_location_linking_face m n i j)).direction + 1
          = Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 := by
              rw [simple_plant_location_linking_face_direction_eq (m := m) (n := n) hn i j]
      _ = Module.finrank ℝ D := by
            exact simple_plant_location_finrank_inf_ker_add_one_of_eval_one D L hwD hw_eval
      _ = Module.finrank ℝ (affineSpan ℝ (simple_plant_location_polytope m n)).direction := by
            rfl
