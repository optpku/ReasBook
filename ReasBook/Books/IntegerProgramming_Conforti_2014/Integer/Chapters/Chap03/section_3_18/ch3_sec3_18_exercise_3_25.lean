import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment; this file uses
-- Mathlib's canonical `Set.extremePoints ℝ` API for the vertices of a convex set.

/-- The `0,1` cube in `ℝ^n`, viewed as the product set with each coordinate in `{0, 1}`. -/
def zero_one_cube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.univ.pi fun _ : Fin n ↦ ({0, 1} : Set ℝ)

/-- Membership in `zero_one_cube n` is exactly the coordinatewise `0/1` condition. -/
theorem mem_zero_one_cube_iff {n : ℕ} {x : Fin n → ℝ} :
    x ∈ zero_one_cube n ↔ ∀ i, x i = 0 ∨ x i = 1 := by
  simp [zero_one_cube]

/-- Helper for Exercise 3.25: every `0/1` vector lies in the unit box. -/
lemma zero_one_cube_subset_unit_box (n : ℕ) :
    zero_one_cube n ⊆ Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1) := by
  intro x hx
  rw [mem_zero_one_cube_iff] at hx
  rw [Set.mem_univ_pi]
  intro i
  rcases hx i with h0 | h1
  · rw [h0]
    simp
  · rw [h1]
    simp

/-- Helper for Exercise 3.25: the extreme points of the unit box are exactly the `0/1` vectors. -/
lemma extremePoints_unit_box_eq_zero_one_cube (n : ℕ) :
    (Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ = zero_one_cube n := by
  -- Compute extreme points coordinatewise and simplify the interval case to `{0, 1}`.
  rw [extremePoints_pi]
  ext x
  simp [zero_one_cube, zero_le_one]

/-- Helper for Exercise 3.25: the convex hull of a subset of the `0,1` cube stays in the unit
box. -/
lemma convexHull_subset_unit_box {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : S ⊆ zero_one_cube n) :
    convexHull ℝ S ⊆ Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1) := by
  -- Place `S` inside the unit box, then use minimality of the convex hull.
  refine convexHull_min (hS.trans (zero_one_cube_subset_unit_box n)) ?_
  -- The unit box is convex because each coordinate interval is convex.
  exact convex_pi fun _ _ ↦ convex_Icc (0 : ℝ) 1

/-- Helper for Exercise 3.25: each point of `S` is an extreme point of `convexHull ℝ S`. -/
lemma mem_extremePoints_convexHull_of_mem_zero_one_set
    {n : ℕ} {S : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hS : S ⊆ zero_one_cube n) (hx : x ∈ S) :
    x ∈ (convexHull ℝ S).extremePoints ℝ := by
  have hxHull : x ∈ convexHull ℝ S := subset_convexHull ℝ S hx
  have hxBoxExtreme :
      x ∈ (Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ
  · -- The hypothesis `x ∈ S ⊆ {0,1}^n` identifies `x` as an extreme point of the unit box.
    rw [extremePoints_unit_box_eq_zero_one_cube]
    exact hS hx
  -- Transfer extremality from the ambient unit box to the smaller convex hull.
  exact
    inter_extremePoints_subset_extremePoints_of_subset (convexHull_subset_unit_box hS)
      ⟨hxHull, hxBoxExtreme⟩

/-- Exercise 3.25. If `S` is a subset of the `0,1` cube in `ℝ^n`, then `S` is exactly the set of
vertices, i.e. extreme points, of its convex hull. -/
theorem zero_one_set_eq_extremePoints_convexHull
    {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : S ⊆ zero_one_cube n) :
    S = (convexHull ℝ S).extremePoints ℝ := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    -- A point of `S` is extreme because it is already extreme in the ambient unit box.
    exact mem_extremePoints_convexHull_of_mem_zero_one_set hS hx
  · -- Every extreme point of a convex hull comes from the original generating set.
    exact extremePoints_convexHull_subset
