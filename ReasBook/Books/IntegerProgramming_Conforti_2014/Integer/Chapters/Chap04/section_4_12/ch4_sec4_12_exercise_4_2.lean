/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_26

-- Declarations for this item will be appended below by the statement pipeline.
-- Proof rescue audit: the completed declarations below are preserved under this fresh artifact.

noncomputable section

open scoped BigOperators

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the statement below
-- was matched against the Chapter 4 `is_zero_one_vector` owner together with local `convexHull`
-- and `Fin`-indexed precedents.

/-- The support of a `0,1`-vertex of the hypercube: the coordinates where the vertex is equal to
`1`. -/
def hypercube_vertex_support {n : ℕ} (v : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ v j = 1

/-- Two hypercube vertices are adjacent when they differ in exactly one coordinate. -/
def hypercube_adjacent {n : ℕ} (u v : Fin n → ℝ) : Prop :=
  is_zero_one_vector u ∧ is_zero_one_vector v ∧
    (Finset.univ.filter fun j ↦ u j ≠ v j).card = 1

/-- The inequality associated with deleting the hypercube vertex `v`, written in terms of the
support of `v`. -/
def deleted_vertex_inequality {n : ℕ} (v x : Fin n → ℝ) : Prop :=
  Finset.sum (hypercube_vertex_support v) x -
      Finset.sum (Finset.univ \ hypercube_vertex_support v) x ≤
    ((hypercube_vertex_support v).card : ℝ) - 1

/-- Helper for Exercise 4.2: the deleted-vertex inequality is defined by a linear functional on
`ℝ^n`. -/
def deleted_vertex_linear {n : ℕ} (v : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  (∑ j ∈ hypercube_vertex_support v,
      (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)) -
    ∑ j ∈ (Finset.univ \ hypercube_vertex_support v),
      (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)

/-- Helper for Exercise 4.2: a hypercube vertex lies in the unit cube. -/
lemma hypercube_vertex_mem_unit_hypercube {n : ℕ} {v : Fin n → ℝ}
    (hv : is_zero_one_vector v) :
    v ∈ Set.Icc (0 : Fin n → ℝ) 1 := by
  -- A `0/1` vector satisfies the unit-cube bounds coordinatewise.
  constructor
  · intro i
    rcases hv i with h0 | h1
    · simp [h0]
    · simp [h1]
  · intro i
    rcases hv i with h0 | h1
    · simp [h0]
    · simp [h1]

/-- Helper for Exercise 4.2: the deleted-vertex region is the preimage of a half-line under the
associated linear functional. -/
lemma deleted_vertex_region_eq_preimage {n : ℕ} (v : Fin n → ℝ) :
    {x | deleted_vertex_inequality v x} =
      deleted_vertex_linear v ⁻¹'
        Set.Iic (((hypercube_vertex_support v).card : ℝ) - 1) := by
  -- Unfold the linear map and compare both descriptions pointwise.
  ext x
  simp [deleted_vertex_inequality, deleted_vertex_linear]

/-- Helper for Exercise 4.2: the region cut out by one deleted-vertex inequality is convex. -/
lemma deleted_vertex_region_convex {n : ℕ} (v : Fin n → ℝ) :
    Convex ℝ {x : Fin n → ℝ | deleted_vertex_inequality v x} := by
  -- Each deleted-vertex region is the preimage of a convex half-line under a linear map.
  rw [deleted_vertex_region_eq_preimage]
  simpa using (convex_Iic (((hypercube_vertex_support v).card : ℝ) - 1)).linear_preimage
    (deleted_vertex_linear v)

/-- Helper for Exercise 4.2: on the unit cube, the deleted-vertex inequality is exactly the
statement that the `ℓ¹` distance from `x` to `v` is at least `1`. -/
lemma deleted_vertex_inequality_iff_one_le_l1_distance {n : ℕ} {v x : Fin n → ℝ}
    (hv : is_zero_one_vector v) (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1) :
    deleted_vertex_inequality v x ↔ 1 ≤ ∑ j : Fin n, |x j - v j| := by
  -- Rewrite the `ℓ¹` distance by separating the coordinates where `v` is `1` from those where
  -- `v` is `0`.
  have hsupport :
      (hypercube_vertex_support v).sum (fun j ↦ |x j - v j|) =
        ((hypercube_vertex_support v).card : ℝ) -
          ((hypercube_vertex_support v).sum x) := by
    calc
      (hypercube_vertex_support v).sum (fun j ↦ |x j - v j|)
          = (hypercube_vertex_support v).sum (fun j ↦ (1 - x j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hvj : v j = 1 := (Finset.mem_filter.mp hj).2
              have hxj : x j ≤ 1 := hx.2 j
              have habs : |x j - 1| = 1 - x j := by
                have habs' : |x j - 1| = -(x j - 1) := abs_of_nonpos (sub_nonpos.mpr hxj)
                linarith
              simpa [hvj] using habs
      _ = ((hypercube_vertex_support v).sum fun _ ↦ (1 : ℝ)) -
            ((hypercube_vertex_support v).sum x) := by
            rw [Finset.sum_sub_distrib]
      _ = ((hypercube_vertex_support v).card : ℝ) -
            ((hypercube_vertex_support v).sum x) := by
            simp
  have hcomplement :
      (Finset.univ \ hypercube_vertex_support v).sum (fun j ↦ |x j - v j|) =
        (Finset.univ \ hypercube_vertex_support v).sum x := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj_not_mem : j ∉ hypercube_vertex_support v := (Finset.mem_sdiff.mp hj).2
    have hvj : v j = 0 := by
      rcases hv j with h0 | h1
      · exact h0
      · exfalso
        apply hj_not_mem
        simp [hypercube_vertex_support, h1]
    have hxj : 0 ≤ x j := hx.1 j
    rw [hvj, sub_zero]
    exact abs_of_nonneg hxj
  have hl1 :
      Finset.univ.sum (fun j : Fin n ↦ |x j - v j|) =
        ((hypercube_vertex_support v).card : ℝ) -
          ((hypercube_vertex_support v).sum x) +
            ((Finset.univ \ hypercube_vertex_support v).sum x) := by
    calc
      Finset.univ.sum (fun j : Fin n ↦ |x j - v j|)
          = (hypercube_vertex_support v).sum (fun j ↦ |x j - v j|) +
              (Finset.univ \ hypercube_vertex_support v).sum (fun j ↦ |x j - v j|) := by
                simpa [hypercube_vertex_support, Finset.sdiff_eq_filter] using
                  (Finset.sum_filter_add_sum_filter_not
                    (s := Finset.univ)
                    (f := fun j : Fin n ↦ |x j - v j|)
                    (p := fun j ↦ v j = 1)).symm
      _ = ((hypercube_vertex_support v).card : ℝ) -
            ((hypercube_vertex_support v).sum x) +
              ((Finset.univ \ hypercube_vertex_support v).sum fun j ↦ |x j - v j|) := by
            rw [hsupport]
      _ = ((hypercube_vertex_support v).card : ℝ) -
            ((hypercube_vertex_support v).sum x) +
              ((Finset.univ \ hypercube_vertex_support v).sum x) := by
            rw [hcomplement]
  -- The deleted inequality is exactly the rearranged lower bound `1 ≤ ‖x - v‖₁`.
  constructor
  · intro hineq
    unfold deleted_vertex_inequality at hineq
    rw [hl1]
    linarith
  · intro hlower
    unfold deleted_vertex_inequality
    rw [hl1] at hlower
    linarith

/-- Helper for Exercise 4.2: distinct hypercube vertices differ in at least one coordinate, so
their `ℓ¹` distance is at least `1`. -/
lemma one_le_l1_distance_of_ne_hypercube_vertices {n : ℕ} {v w : Fin n → ℝ}
    (hv : is_zero_one_vector v) (hw : is_zero_one_vector w) (hvw : w ≠ v) :
    1 ≤ ∑ j : Fin n, |w j - v j| := by
  classical
  -- Pick a coordinate where the two binary vectors differ.
  have hcoord : ∃ i : Fin n, w i ≠ v i := by
    by_contra hcoord
    apply hvw
    ext i
    by_contra hneq
    exact hcoord ⟨i, hneq⟩
  rcases hcoord with ⟨i, hi⟩
  have hi_abs : |w i - v i| = 1 := by
    rcases hw i with hwi0 | hwi1 <;> rcases hv i with hvi0 | hvi1
    · exfalso
      apply hi
      simp [hwi0, hvi0]
    · simp [hwi0, hvi1]
    · simp [hwi1, hvi0]
    · exfalso
      apply hi
      simp [hwi1, hvi1]
  have hi_mem_univ : i ∈ Finset.univ := Finset.mem_univ i
  have hi_le_sum : |w i - v i| ≤ Finset.univ.sum (fun j : Fin n ↦ |w j - v j|) := by
    simpa using
      (Finset.single_le_sum
        (fun j _ ↦ abs_nonneg (w j - v j))
        hi_mem_univ :
          |w i - v i| ≤ Finset.univ.sum (fun j : Fin n ↦ |w j - v j|))
  -- Compare the full sum with the nonzero coordinate contribution.
  have hi_one : (1 : ℝ) ≤ |w i - v i| := by
    simp [hi_abs]
  exact hi_one.trans hi_le_sum

/-- Helper for Exercise 4.2: on hypercube vertices, the deleted-vertex inequality excludes exactly
the deleted vertex itself. -/
lemma deleted_vertex_inequality_iff_ne_on_hypercube_vertices {n : ℕ} {v w : Fin n → ℝ}
    (hv : is_zero_one_vector v) (hw : is_zero_one_vector w) :
    deleted_vertex_inequality v w ↔ w ≠ v := by
  -- Specialize the `ℓ¹` reformulation to binary points.
  have hw_cube : w ∈ Set.Icc (0 : Fin n → ℝ) 1 := hypercube_vertex_mem_unit_hypercube hw
  rw [deleted_vertex_inequality_iff_one_le_l1_distance hv hw_cube]
  constructor
  · intro hineq hEq
    have : (1 : ℝ) ≤ 0 := by
      simpa [hEq] using hineq
    linarith
  · intro hne
    exact one_le_l1_distance_of_ne_hypercube_vertices hv hw hne

/-- Helper for Exercise 4.2: the deleted-vertex system is convex because it is the unit cube
intersected with deleted-vertex halfspaces. -/
lemma deleted_vertex_system_convex {n : ℕ} {V : Finset (Fin n → ℝ)} :
    Convex ℝ {x : Fin n → ℝ | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v x} := by
  -- Rewrite the feasible region as an intersection indexed by the deleted vertices.
  have hrewrite :
      {x : Fin n → ℝ | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
          ∀ v ∈ V, deleted_vertex_inequality v x} =
        Set.Icc (0 : Fin n → ℝ) 1 ∩
          ⋂ v : ↥V, {x : Fin n → ℝ | deleted_vertex_inequality (v : Fin n → ℝ) x} := by
    ext x
    simp
  rw [hrewrite]
  exact (convex_Icc (0 : Fin n → ℝ) 1).inter <|
    convex_iInter fun v ↦ deleted_vertex_region_convex (v : Fin n → ℝ)

/-- Helper for Exercise 4.2: an undeleted hypercube vertex satisfies every deleted-vertex
inequality, hence lies in the deleted-vertex system. -/
lemma undeleted_hypercube_vertex_mem_deleted_vertex_system
    {n : ℕ} {V : Finset (Fin n → ℝ)}
    (hV_vertices : ∀ ⦃v : Fin n → ℝ⦄, v ∈ V → is_zero_one_vector v)
    {w : Fin n → ℝ} (hw : is_zero_one_vector w) (hw_not_mem : w ∉ V) :
    w ∈ {x : Fin n → ℝ | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v x} := by
  -- The box constraints come from binaryness, and each deleted inequality reduces to `w ≠ v`.
  have hw_cube : w ∈ Set.Icc (0 : Fin n → ℝ) 1 := hypercube_vertex_mem_unit_hypercube hw
  have hw_deleted : ∀ v ∈ V, deleted_vertex_inequality v w := by
    intro v hv
    exact (deleted_vertex_inequality_iff_ne_on_hypercube_vertices (hV_vertices hv) hw).2
      (fun hEq ↦ hw_not_mem (hEq ▸ hv))
  exact ⟨hw_cube, hw_deleted⟩

/-- Helper for Exercise 4.2: the convex hull of the undeleted hypercube vertices is contained in
the deleted-vertex system. -/
lemma convexHull_hypercube_vertices_diff_subset_deleted_vertex_system
    {n : ℕ} {V : Finset (Fin n → ℝ)}
    (hV_vertices : ∀ ⦃v : Fin n → ℝ⦄, v ∈ V → is_zero_one_vector v) :
    convexHull ℝ ({v : Fin n → ℝ | is_zero_one_vector v} \ (V : Set (Fin n → ℝ))) ⊆
      {x : Fin n → ℝ | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
        ∀ v ∈ V, deleted_vertex_inequality v x} := by
  -- It is enough to check the generating undeleted vertices and use convexity of the target set.
  refine convexHull_min ?_ deleted_vertex_system_convex
  intro w hw
  exact undeleted_hypercube_vertex_mem_deleted_vertex_system hV_vertices hw.1 hw.2

/-- Helper for Exercise 4.2: if a deleted-vertex inequality is active at a fractional feasible
point, then the deleted vertex agrees with that point on every integral coordinate. -/
lemma active_deleted_vertex_eq_on_integral_coordinates
    {n : ℕ} {v x : Fin n → ℝ}
    (hv : is_zero_one_vector v)
    (hactive : ∑ j : Fin n, |x j - v j| = 1)
    (hfrac : ¬ is_zero_one_vector x) :
    ∀ i : Fin n, (x i = 0 ∨ x i = 1) → v i = x i := by
  classical
  -- Pick a genuinely fractional coordinate of `x`; it contributes positive `ℓ¹` distance to any
  -- binary vertex, so an integral mismatch would force the active sum strictly above `1`.
  have hfrac_coord : ∃ k : Fin n, x k ≠ 0 ∧ x k ≠ 1 := by
    by_contra hno
    apply hfrac
    intro i
    by_contra hxi
    have hxi' : x i ≠ 0 ∧ x i ≠ 1 := by
      simpa [not_or] using hxi
    exact hno ⟨i, hxi'⟩
  rcases hfrac_coord with ⟨k, hk0, hk1⟩
  intro i hxi
  by_contra hvi
  have hki : k ≠ i := by
    intro hEq
    subst hEq
    rcases hxi with hxi0 | hxi1
    · exact hk0 hxi0
    · exact hk1 hxi1
  have hk_pos : 0 < |x k - v k| := by
    rcases hv k with hvk0 | hvk1
    · rw [hvk0, sub_zero]
      exact abs_pos.mpr hk0
    · have : x k - 1 ≠ 0 := sub_ne_zero.mpr hk1
      simpa [hvk1] using abs_pos.mpr this
  have hi_abs : |x i - v i| = 1 := by
    rcases hxi with hxi0 | hxi1 <;> rcases hv i with hvi0 | hvi1
    · exfalso
      apply hvi
      simp [hxi0, hvi0]
    · simp [hxi0, hvi1]
    · simp [hxi1, hvi0]
    · exfalso
      apply hvi
      simp [hxi1, hvi1]
  have hk_le :
      |x k - v k| ≤ (Finset.univ.erase i).sum (fun j : Fin n ↦ |x j - v j|) := by
    have hk_mem : k ∈ Finset.univ.erase i := by
      simp [hki]
    exact Finset.single_le_sum
      (fun j _ ↦ abs_nonneg (x j - v j))
      hk_mem
  have hsum_gt :
      1 < ∑ j : Fin n, |x j - v j| := by
    calc
      1 = |x i - v i| := hi_abs.symm
      _ < |x i - v i| + (Finset.univ.erase i).sum (fun j : Fin n ↦ |x j - v j|) := by
        have : 0 < (Finset.univ.erase i).sum (fun j : Fin n ↦ |x j - v j|) :=
          lt_of_lt_of_le hk_pos hk_le
        linarith
      _ = ∑ j : Fin n, |x j - v j| := by
        rw [add_comm]
        exact Finset.sum_erase_add
          (s := Finset.univ)
          (a := i)
          (f := fun j : Fin n ↦ |x j - v j|)
          (Finset.mem_univ i)
  rw [hactive] at hsum_gt
  linarith

/-- Helper for Exercise 4.2: a feasible point with all but possibly one coordinate integral already
lies in the convex hull of the undeleted hypercube vertices. -/
lemma mem_convexHull_of_all_but_one_integral_coordinate
    {n : ℕ} {V : Finset (Fin n → ℝ)}
    (hV_vertices : ∀ ⦃v : Fin n → ℝ⦄, v ∈ V → is_zero_one_vector v)
    {x : Fin n → ℝ}
    (hx : x ∈ {y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v y})
    (i : Fin n)
    (hintegral : ∀ j : Fin n, j ≠ i → x j = 0 ∨ x j = 1) :
    x ∈ convexHull ℝ ({v : Fin n → ℝ | is_zero_one_vector v} \ (V : Set (Fin n → ℝ))) := by
  classical
  let S : Set (Fin n → ℝ) := {v : Fin n → ℝ | is_zero_one_vector v} \ (V : Set (Fin n → ℝ))
  let x0 : Fin n → ℝ := fun j ↦ if j = i then 0 else x j
  let x1 : Fin n → ℝ := fun j ↦ if j = i then 1 else x j
  have hx0_zero_one : is_zero_one_vector x0 := by
    -- The rounded-down endpoint keeps every other coordinate at its already integral value.
    intro j
    by_cases hji : j = i
    · simp [x0, hji]
    · simpa [x0, hji] using hintegral j hji
  have hx1_zero_one : is_zero_one_vector x1 := by
    -- The rounded-up endpoint is handled identically.
    intro j
    by_cases hji : j = i
    · simp [x1, hji]
    · simpa [x1, hji] using hintegral j hji
  have hx_binary_of_coord (hxi : x i = 0 ∨ x i = 1) : is_zero_one_vector x := by
    -- Once the `i`-th coordinate is also integral, the whole point is binary.
    intro j
    by_cases hji : j = i
    · simpa [hji] using hxi
    · exact hintegral j hji
  have hx_not_mem_of_binary (hx_binary : is_zero_one_vector x) : x ∉ V := by
    -- A feasible binary point cannot be one of the deleted vertices, because it satisfies its own
    -- deleted inequality.
    intro hxV
    have hineq : deleted_vertex_inequality x x := hx.2 x hxV
    exact
      (deleted_vertex_inequality_iff_ne_on_hypercube_vertices hx_binary hx_binary).1 hineq rfl
  have hx0_sum :
      ∑ j : Fin n, |x j - x0 j| = x i := by
    -- The rounded-down endpoint differs from `x` only in coordinate `i`.
    rw [Finset.sum_eq_single i]
    · have hxi_nonneg : 0 ≤ x i := hx.1.1 i
      simp [x0, hxi_nonneg]
    · intro j _ hji
      simp [x0, hji]
    · intro hi
      simp at hi
  have hx1_sum :
      ∑ j : Fin n, |x j - x1 j| = 1 - x i := by
    -- The rounded-up endpoint also differs only in coordinate `i`.
    rw [Finset.sum_eq_single i]
    · have hxi_le : x i ≤ 1 := hx.1.2 i
      have habs : |x i - 1| = 1 - x i := by
        have habs_neg : |x i - 1| = -(x i - 1) := abs_of_nonpos (sub_nonpos.mpr hxi_le)
        linarith
      simp [x1, habs]
    · intro j _ hji
      simp [x1, hji]
    · intro hi
      simp at hi
  by_cases hxi0 : x i = 0
  · -- If `x i = 0`, then `x` itself is the rounded-down undeleted vertex.
    have hx_binary : is_zero_one_vector x := hx_binary_of_coord (Or.inl hxi0)
    have hx_not_mem : x ∉ V := hx_not_mem_of_binary hx_binary
    have hx_eq_x0 : x = x0 := by
      ext j
      by_cases hji : j = i
      · simp [x0, hji, hxi0]
      · simp [x0, hji]
    have hx_mem_S : x ∈ S := ⟨hx_binary, hx_not_mem⟩
    rw [hx_eq_x0]
    simpa [hx_eq_x0] using subset_convexHull ℝ S hx_mem_S
  by_cases hxi1 : x i = 1
  · -- If `x i = 1`, then `x` is the rounded-up undeleted vertex.
    have hx_binary : is_zero_one_vector x := hx_binary_of_coord (Or.inr hxi1)
    have hx_not_mem : x ∉ V := hx_not_mem_of_binary hx_binary
    have hx_eq_x1 : x = x1 := by
      ext j
      by_cases hji : j = i
      · simp [x1, hji, hxi1]
      · simp [x1, hji]
    have hx_mem_S : x ∈ S := ⟨hx_binary, hx_not_mem⟩
    rw [hx_eq_x1]
    simpa [hx_eq_x1] using subset_convexHull ℝ S hx_mem_S
  have hxi_pos : 0 < x i := by
    have hxi_nonneg : 0 ≤ x i := hx.1.1 i
    exact lt_of_le_of_ne hxi_nonneg (Ne.symm hxi0)
  have hxi_lt_one : x i < 1 := by
    have hxi_le : x i ≤ 1 := hx.1.2 i
    exact lt_of_le_of_ne hxi_le hxi1
  have hx0_not_mem : x0 ∉ V := by
    -- A deleted rounded-down endpoint would sit at `ℓ¹`-distance `x i < 1` from `x`.
    intro hx0V
    have hineq : deleted_vertex_inequality x0 x := hx.2 x0 hx0V
    have hone : 1 ≤ ∑ j : Fin n, |x j - x0 j| :=
      (deleted_vertex_inequality_iff_one_le_l1_distance (hV_vertices hx0V) hx.1).1 hineq
    rw [hx0_sum] at hone
    linarith
  have hx1_not_mem : x1 ∉ V := by
    -- The same argument excludes the rounded-up endpoint.
    intro hx1V
    have hineq : deleted_vertex_inequality x1 x := hx.2 x1 hx1V
    have hone : 1 ≤ ∑ j : Fin n, |x j - x1 j| :=
      (deleted_vertex_inequality_iff_one_le_l1_distance (hV_vertices hx1V) hx.1).1 hineq
    rw [hx1_sum] at hone
    linarith
  have hx_mem_segment : x ∈ segment ℝ x0 x1 := by
    -- Express `x` as the convex combination of the two rounded endpoints with weights
    -- `1 - x i` and `x i`.
    have hweights_sum : 1 - x i + x i = (1 : ℝ) := by
      ring
    refine ⟨1 - x i, x i, sub_nonneg.mpr hx.1.2 i, hx.1.1 i, hweights_sum, ?_⟩
    ext j
    by_cases hji : j = i
    · subst hji
      simp [x0, x1]
    · simp [x0, x1, hji]
      ring
  have hx0_mem_S : x0 ∈ S := ⟨hx0_zero_one, hx0_not_mem⟩
  have hx1_mem_S : x1 ∈ S := ⟨hx1_zero_one, hx1_not_mem⟩
  exact (segment_subset_convexHull hx0_mem_S hx1_mem_S) hx_mem_segment

/-- Helper for Exercise 4.2: the `0/1` vertices of the `n`-hypercube form a finite set. -/
lemma finite_zero_one_vectors (n : ℕ) :
    ({v : Fin n → ℝ | is_zero_one_vector v} : Set (Fin n → ℝ)).Finite := by
  let vertexOfSupport : Finset (Fin n) → Fin n → ℝ := fun T i ↦ if i ∈ T then 1 else 0
  have hsubset :
      {v : Fin n → ℝ | is_zero_one_vector v} ⊆ Set.range vertexOfSupport := by
    intro v hv
    refine ⟨hypercube_vertex_support v, ?_⟩
    ext i
    by_cases hvi1 : v i = 1
    · have himem : i ∈ hypercube_vertex_support v := by
        simp [hypercube_vertex_support, hvi1]
      simp [vertexOfSupport, himem, hvi1]
    · have hvi0 : v i = 0 := by
        rcases hv i with h0 | h1
        · exact h0
        · exact (hvi1 h1).elim
      have hnot_mem : i ∉ hypercube_vertex_support v := by
        simp [hypercube_vertex_support, hvi0]
      simp [vertexOfSupport, hnot_mem, hvi0]
  exact (Set.finite_range vertexOfSupport).subset hsubset

/-- Helper for Exercise 4.2: once `x` is not binary, the negation of the one-fractional-coordinate
case yields two distinct fractional coordinates. -/
lemma exists_two_fractional_coordinates_of_not_small
    {n : ℕ} {x : Fin n → ℝ}
    (hx_nonbinary : ¬ is_zero_one_vector x)
    (hsmall : ¬ ∃ i : Fin n, ∀ j : Fin n, j ≠ i → x j = 0 ∨ x j = 1) :
    ∃ p q : Fin n, p ≠ q ∧ ¬ (x p = 0 ∨ x p = 1) ∧ ¬ (x q = 0 ∨ x q = 1) := by
  -- Start from one fractional coordinate and use `¬ hsmall` to find a second one away from it.
  have hp : ∃ p : Fin n, ¬ (x p = 0 ∨ x p = 1) := by
    by_contra hno
    apply hx_nonbinary
    intro i
    by_contra hi
    exact hno ⟨i, hi⟩
  rcases hp with ⟨p, hpfrac⟩
  have hq : ∃ q : Fin n, q ≠ p ∧ ¬ (x q = 0 ∨ x q = 1) := by
    by_contra hno
    apply hsmall
    refine ⟨p, ?_⟩
    intro j hj
    by_contra hjfrac
    exact hno ⟨j, hj, hjfrac⟩
  rcases hq with ⟨q, hqp, hqfrac⟩
  exact ⟨p, q, hqp.symm, hpfrac, hqfrac⟩

/-- Helper for sorry cleanup existing repo batch3 ch4_sec4_12_exercise_4_2: the sign of a
coordinate in the deleted-vertex linear form. -/
def deletedVertexSign {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  if v i = 1 then 1 else -1

/-- Helper for sorry cleanup existing repo batch3 ch4_sec4_12_exercise_4_2: evaluation of a
deleted-vertex linear form as a signed coordinate sum. -/
lemma deletedVertexLinear_apply {n : ℕ} {v x : Fin n → ℝ} :
    deleted_vertex_linear v x = ∑ i : Fin n, deletedVertexSign v i * x i := by
  classical
  -- Split the signed sum into the support of `v` and its complement.
  simp only [deleted_vertex_linear, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.proj_apply]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun i ↦ v i = 1)
    (f := fun i ↦ deletedVertexSign v i * x i)]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro i hi
    have hvi : v i = 1 := (Finset.mem_filter.mp hi).2
    simp [deletedVertexSign, hvi]
  · refine Finset.sum_congr ?_ ?_
    · ext i
      simp [hypercube_vertex_support, Finset.sdiff_eq_filter]
    · intro i hi
      have hvi : v i ≠ 1 := by
        simpa using (Finset.mem_filter.mp hi).2
      simp [deletedVertexSign, hvi]

/-- Helper for sorry cleanup existing repo batch3 ch4_sec4_12_exercise_4_2: on the unit cube,
the `ℓ¹` distance from a binary vertex is the support cardinality minus its deleted-vertex
linear form. -/
lemma l1Distance_eq_card_sub_deletedVertexLinear {n : ℕ} {v x : Fin n → ℝ}
    (hv : is_zero_one_vector v) (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1) :
    ∑ i : Fin n, |x i - v i| =
      ((hypercube_vertex_support v).card : ℝ) - deleted_vertex_linear v x := by
  classical
  -- Normalize each binary coordinate before summing the pointwise identity.
  calc
    ∑ i : Fin n, |x i - v i| =
        ∑ i : Fin n, ((if v i = 1 then (1 : ℝ) else 0) -
          deletedVertexSign v i * x i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rcases hv i with hvi | hvi
      · simp [hvi, deletedVertexSign, abs_of_nonneg (hx.1 i)]
      · have habs : |x i - 1| = 1 - x i := by
          have hxi_le : x i ≤ (1 : ℝ) := hx.2 i
          rw [abs_of_nonpos (sub_nonpos.mpr hxi_le)]
          ring
        simp [hvi, deletedVertexSign, habs]
    _ = (∑ i : Fin n, if v i = 1 then (1 : ℝ) else 0) -
          ∑ i : Fin n, deletedVertexSign v i * x i := by
      rw [Finset.sum_sub_distrib]
    _ = ((hypercube_vertex_support v).card : ℝ) - deleted_vertex_linear v x := by
      rw [deletedVertexLinear_apply]
      simp [hypercube_vertex_support]

/-- Helper for sorry cleanup existing repo batch3 ch4_sec4_12_exercise_4_2: a deleted-vertex
inequality is the upper bound for its associated linear form. -/
lemma deletedVertexInequality_iff_linear_le {n : ℕ} {v x : Fin n → ℝ} :
    deleted_vertex_inequality v x ↔
      deleted_vertex_linear v x ≤ ((hypercube_vertex_support v).card : ℝ) - 1 := by
  -- Both sides use the same support-minus-complement expression.
  simp [deleted_vertex_inequality, deleted_vertex_linear]

/-- Helper for sorry cleanup existing repo batch3 ch4_sec4_12_exercise_4_2: evaluating a
deleted-vertex linear form on one coordinate isolates that coordinate's sign. -/
lemma deletedVertexLinear_single {n : ℕ} {v : Fin n → ℝ} (i : Fin n) (a : ℝ) :
    deleted_vertex_linear v (Pi.single i a) = deletedVertexSign v i * a := by
  classical
  -- The signed coordinate sum has only the `i`-th nonzero term.
  rw [deletedVertexLinear_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Helper for sorry cleanup existing repo batch3 ch4_sec4_12_exercise_4_2: distinct binary
coordinates have opposite deleted-vertex signs. -/
lemma deletedVertexSign_neg_of_ne {n : ℕ} {v w : Fin n → ℝ} {i : Fin n}
    (hv : is_zero_one_vector v) (hw : is_zero_one_vector w) (hvw : v i ≠ w i) :
    deletedVertexSign w i = -deletedVertexSign v i := by
  -- There are only the two binary coordinate values.
  rcases hv i with hvi | hvi <;> rcases hw i with hwi | hwi
  · have heq : v i = w i := hvi.trans hwi.symm
    exact (hvw heq).elim
  · simp [deletedVertexSign, hvi, hwi]
  · simp [deletedVertexSign, hvi, hwi]
  · have heq : v i = w i := hvi.trans hwi.symm
    exact (hvw heq).elim

/-- Helper for sorry cleanup existing repo batch3 ch4_sec4_12_exercise_4_2: the `ℓ¹` distance
between two binary vertices counts their differing coordinates. -/
lemma l1Distance_eq_disagreementCard {n : ℕ} {v w : Fin n → ℝ}
    (hv : is_zero_one_vector v) (hw : is_zero_one_vector w) :
    ∑ i : Fin n, |v i - w i| =
      ((Finset.univ.filter fun i ↦ v i ≠ w i).card : ℝ) := by
  classical
  -- Each binary coordinate contributes either zero or one.
  calc
    ∑ i : Fin n, |v i - w i| =
        ∑ i : Fin n, if v i ≠ w i then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rcases hv i with hvi | hvi <;> rcases hw i with hwi | hwi <;>
        simp [hvi, hwi]
    _ = ((Finset.univ.filter fun i ↦ v i ≠ w i).card : ℝ) := by
      simpa using
        (Finset.sum_boole (R := ℝ) (fun i : Fin n ↦ v i ≠ w i) Finset.univ)

/-- Helper for sorry cleanup existing repo batch3 ch4_sec4_12_exercise_4_2: distinct active,
nonadjacent deleted vertices disagree at every fractional coordinate. -/
lemma activeDeletedVertices_disagreeOnFractionalCoordinate
    {n : ℕ} {v w x : Fin n → ℝ}
    (hv : is_zero_one_vector v) (hw : is_zero_one_vector w)
    (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1)
    (hv_active : deleted_vertex_linear v x =
      ((hypercube_vertex_support v).card : ℝ) - 1)
    (hw_active : deleted_vertex_linear w x =
      ((hypercube_vertex_support w).card : ℝ) - 1)
    (hvw : v ≠ w) (hnot_adjacent : ¬ hypercube_adjacent v w)
    {i : Fin n} (hi : ¬ (x i = 0 ∨ x i = 1)) :
    v i ≠ w i := by
  classical
  -- Activity makes both distances from `x` exactly one.
  have hv_distance : ∑ j : Fin n, |x j - v j| = 1 := by
    rw [l1Distance_eq_card_sub_deletedVertexLinear hv hx, hv_active]
    ring
  have hw_distance : ∑ j : Fin n, |x j - w j| = 1 := by
    rw [l1Distance_eq_card_sub_deletedVertexLinear hw hx, hw_active]
    ring
  have hcard_pos : 0 < (Finset.univ.filter fun j ↦ v j ≠ w j).card := by
    rw [Finset.card_pos]
    by_contra hempty
    apply hvw
    ext j
    by_contra hj
    exact hempty ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  have hcard_ne_one : (Finset.univ.filter fun j ↦ v j ≠ w j).card ≠ 1 := by
    intro hcard
    exact hnot_adjacent ⟨hv, hw, hcard⟩
  have hcard_ge_two : 2 ≤ (Finset.univ.filter fun j ↦ v j ≠ w j).card := by
    omega
  have hdistance_ge_two :
      (2 : ℝ) ≤ ∑ j : Fin n, |v j - w j| := by
    rw [l1Distance_eq_disagreementCard hv hw]
    exact_mod_cast hcard_ge_two
  by_contra hi_agree
  have hxi_ne_vi : x i ≠ v i := by
    intro hxi
    rcases hv i with hvi | hvi
    · exact hi (Or.inl (hxi.trans hvi))
    · exact hi (Or.inr (hxi.trans hvi))
  have hpointwise (j : Fin n) :
      |v j - w j| ≤ |x j - v j| + |x j - w j| := by
    calc
      |v j - w j| ≤ |v j - x j| + |x j - w j| :=
        abs_sub_le (v j) (x j) (w j)
      _ = |x j - v j| + |x j - w j| := by rw [abs_sub_comm (v j) (x j)]
  have hi_strict : |v i - w i| < |x i - v i| + |x i - w i| := by
    have hleft : |v i - w i| = 0 := by simp [hi_agree]
    have hright : 0 < |x i - v i| + |x i - w i| := by
      exact lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hxi_ne_vi))
        (le_add_of_nonneg_right (abs_nonneg (x i - w i)))
    linarith
  have hdistance_lt_two :
      ∑ j : Fin n, |v j - w j| < 2 := by
    have hstrict_sum :
        ∑ j : Fin n, |v j - w j| <
          ∑ j : Fin n, (|x j - v j| + |x j - w j|) := by
      exact Finset.sum_lt_sum (fun j _ ↦ hpointwise j)
        ⟨i, Finset.mem_univ i, hi_strict⟩
    rw [Finset.sum_add_distrib, hv_distance, hw_distance] at hstrict_sum
    norm_num at hstrict_sum
    exact hstrict_sum
  linarith

/-- Helper for sorry cleanup existing repo batch3 ch4_sec4_12_exercise_4_2: a feasible point
with at least two fractional coordinates has a nonzero fractional-support direction annihilated by
every active deleted-vertex linear form. -/
lemma existsFractionalActiveKernelDirection
    {n : ℕ} {V : Finset (Fin n → ℝ)}
    (hV_vertices : ∀ ⦃v : Fin n → ℝ⦄, v ∈ V → is_zero_one_vector v)
    (hV_nonadjacent : ((V : Set (Fin n → ℝ)).Pairwise fun u v ↦ ¬ hypercube_adjacent u v))
    {x : Fin n → ℝ}
    (hx : x ∈ {y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v y})
    (hx_nonbinary : ¬ is_zero_one_vector x)
    (hsmall : ¬ ∃ i : Fin n, ∀ j : Fin n, j ≠ i → x j = 0 ∨ x j = 1) :
    ∃ d : Fin n → ℝ, d ≠ 0 ∧
      (∀ i, d i ≠ 0 → 0 < x i ∧ x i < 1) ∧
      ∀ v ∈ V, deleted_vertex_linear v x =
        ((hypercube_vertex_support v).card : ℝ) - 1 → deleted_vertex_linear v d = 0 := by
  classical
  -- Fix two genuinely fractional coordinates; the direction will be supported only there.
  rcases exists_two_fractional_coordinates_of_not_small hx_nonbinary hsmall with
    ⟨p, q, hpq, hp_fractional, hq_fractional⟩
  have hp_interior : 0 < x p ∧ x p < 1 := by
    constructor
    · exact lt_of_le_of_ne (hx.1.1 p) (fun h ↦ hp_fractional (Or.inl h.symm))
    · exact lt_of_le_of_ne (hx.1.2 p) (fun h ↦ hp_fractional (Or.inr h))
  have hq_interior : 0 < x q ∧ x q < 1 := by
    constructor
    · exact lt_of_le_of_ne (hx.1.1 q) (fun h ↦ hq_fractional (Or.inl h.symm))
    · exact lt_of_le_of_ne (hx.1.2 q) (fun h ↦ hq_fractional (Or.inr h))
  by_cases hactive : ∃ v ∈ V, deleted_vertex_linear v x =
      ((hypercube_vertex_support v).card : ℝ) - 1
  · rcases hactive with ⟨v, hvV, hv_active⟩
    let d : Fin n → ℝ :=
      Pi.single p (deletedVertexSign v q) + Pi.single q (-deletedVertexSign v p)
    refine ⟨d, ?_, ?_, ?_⟩
    · -- The `p`-th coordinate is a nonzero sign, so the direction is nonzero.
      intro hd
      have hdp : d p = 0 := congrArg (fun z ↦ z p) hd
      have hsign : deletedVertexSign v q ≠ 0 := by
        unfold deletedVertexSign
        split <;> norm_num
      apply hsign
      simpa [d, Pi.single_apply, hpq, hpq.symm] using hdp
    · -- A nonzero coordinate of the direction must be one of the two fractional coordinates.
      intro i hdi
      by_cases hip : i = p
      · simpa [hip] using hp_interior
      by_cases hiq : i = q
      · simpa [hiq] using hq_interior
      exfalso
      apply hdi
      simp [d, hip, hiq]
    · intro w hwV hw_active
      have hv_binary : is_zero_one_vector v := hV_vertices hvV
      have hw_binary : is_zero_one_vector w := hV_vertices hwV
      by_cases hwv : w = v
      · subst w
        -- The two chosen coefficients cancel for the reference active vertex.
        simp [d, map_add, deletedVertexLinear_single]
        ring
      · have hvw : v ≠ w := Ne.symm hwv
        have hnot_adjacent : ¬ hypercube_adjacent v w :=
          hV_nonadjacent hvV hwV hvw
        have hp_disagree : v p ≠ w p :=
          activeDeletedVertices_disagreeOnFractionalCoordinate hv_binary hw_binary hx.1
            hv_active hw_active hvw hnot_adjacent hp_fractional
        have hq_disagree : v q ≠ w q :=
          activeDeletedVertices_disagreeOnFractionalCoordinate hv_binary hw_binary hx.1
            hv_active hw_active hvw hnot_adjacent hq_fractional
        have hp_sign : deletedVertexSign w p = -deletedVertexSign v p :=
          deletedVertexSign_neg_of_ne hv_binary hw_binary hp_disagree
        have hq_sign : deletedVertexSign w q = -deletedVertexSign v q :=
          deletedVertexSign_neg_of_ne hv_binary hw_binary hq_disagree
        -- Every other active vertex flips both selected signs, preserving cancellation.
        simp [d, map_add, deletedVertexLinear_single, hp_sign, hq_sign]
        ring
  · let d : Fin n → ℝ := Pi.single p 1
    refine ⟨d, ?_, ?_, ?_⟩
    · -- With no active inequality, one fractional coordinate direction suffices.
      intro hd
      have hdp : d p = 0 := congrArg (fun z ↦ z p) hd
      simp [d] at hdp
    · intro i hdi
      by_cases hip : i = p
      · simpa [hip] using hp_interior
      exfalso
      apply hdi
      simp [d, hip]
    · intro v hvV hv_active
      exact (hactive ⟨v, hvV, hv_active⟩).elim

/-- Helper for sorry cleanup existing repo batch3 ch4_sec4_12_exercise_4_2: a direction supported
on fractional coordinates and tangent to every active inequality admits a small feasible
perturbation in both directions. -/
lemma existsTwoSidedPerturbation_mem_deletedVertexSystem
    {n : ℕ} {V : Finset (Fin n → ℝ)} {x d : Fin n → ℝ}
    (hx : x ∈ {y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v y})
    (hd_interior : ∀ i, d i ≠ 0 → 0 < x i ∧ x i < 1)
    (hd_active : ∀ v ∈ V, deleted_vertex_linear v x =
      ((hypercube_vertex_support v).card : ℝ) - 1 → deleted_vertex_linear v d = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      x - ε • d ∈ {y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
        ∀ v ∈ V, deleted_vertex_inequality v y} ∧
      x + ε • d ∈ {y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
        ∀ v ∈ V, deleted_vertex_inequality v y} := by
  -- Each coordinate remains in the unit interval throughout a neighborhood of parameter zero.
  have hcoordinates :
      ∀ᶠ t in nhds (0 : ℝ), ∀ i : Fin n,
        0 ≤ (x + t • d) i ∧ (x + t • d) i ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hdi : d i = 0
    · refine Filter.Eventually.of_forall ?_
      intro t
      simpa [hdi] using And.intro (hx.1.1 i) (hx.1.2 i)
    · have hi_interior : x i ∈ Set.Ioo (0 : ℝ) 1 := hd_interior i hdi
      have hcontinuous : Continuous (fun t : ℝ ↦ x i + t * d i) :=
        continuous_const.add (continuous_id.mul continuous_const)
      have hzero_mem : (fun t : ℝ ↦ x i + t * d i) 0 ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa using hi_interior
      have heventually :
          ∀ᶠ t in nhds (0 : ℝ), x i + t * d i ∈ Set.Ioo (0 : ℝ) 1 :=
        hcontinuous.continuousAt.preimage_mem_nhds
          (isOpen_Ioo.mem_nhds hzero_mem)
      filter_upwards [heventually] with t ht
      constructor
      · simpa [smul_eq_mul] using ht.1.le
      · simpa [smul_eq_mul] using ht.2.le
  -- Every active inequality is constant on the line, while every inactive one remains strict near
  -- parameter zero; finiteness of `V` gives one common neighborhood.
  have hinequalities :
      ∀ᶠ t in nhds (0 : ℝ), ∀ v ∈ V, deleted_vertex_inequality v (x + t • d) := by
    rw [Filter.eventually_all_finset]
    intro v hvV
    have hx_linear : deleted_vertex_linear v x ≤
        ((hypercube_vertex_support v).card : ℝ) - 1 :=
      (deletedVertexInequality_iff_linear_le).1 (hx.2 v hvV)
    by_cases hactive : deleted_vertex_linear v x =
        ((hypercube_vertex_support v).card : ℝ) - 1
    · have hd_zero : deleted_vertex_linear v d = 0 := hd_active v hvV hactive
      refine Filter.Eventually.of_forall ?_
      intro t
      apply (deletedVertexInequality_iff_linear_le).2
      simp [map_add, map_smul, hactive, hd_zero]
    · have hstrict : deleted_vertex_linear v x <
          ((hypercube_vertex_support v).card : ℝ) - 1 :=
        lt_of_le_of_ne hx_linear hactive
      have hcontinuous : Continuous (fun t : ℝ ↦
          deleted_vertex_linear v x + t * deleted_vertex_linear v d) :=
        continuous_const.add (continuous_id.mul continuous_const)
      have hzero_mem :
          (fun t : ℝ ↦ deleted_vertex_linear v x + t * deleted_vertex_linear v d) 0 ∈
            Set.Iio (((hypercube_vertex_support v).card : ℝ) - 1) := by
        simpa using hstrict
      have heventually : ∀ᶠ t in nhds (0 : ℝ),
          deleted_vertex_linear v x + t * deleted_vertex_linear v d <
            ((hypercube_vertex_support v).card : ℝ) - 1 :=
        hcontinuous.continuousAt.preimage_mem_nhds
          (isOpen_Iio.mem_nhds hzero_mem)
      filter_upwards [heventually] with t ht
      apply (deletedVertexInequality_iff_linear_le).2
      simpa [map_add, map_smul] using ht.le
  have hfeasible : ∀ᶠ t in nhds (0 : ℝ),
      x + t • d ∈ {y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
        ∀ v ∈ V, deleted_vertex_inequality v y} := by
    filter_upwards [hcoordinates, hinequalities] with t ht_coordinates ht_inequalities
    exact ⟨⟨fun i ↦ (ht_coordinates i).1, fun i ↦ (ht_coordinates i).2⟩,
      ht_inequalities⟩
  rcases Metric.mem_nhds_iff.mp hfeasible with ⟨δ, hδ_pos, hball⟩
  let ε : ℝ := δ / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    linarith
  have hε_ball : ε ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [sub_zero, abs_of_pos hε_pos]
    dsimp [ε]
    linarith
  have hnegε_ball : -ε ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [sub_zero, abs_neg, abs_of_pos hε_pos]
    dsimp [ε]
    linarith
  refine ⟨ε, hε_pos, ?_, hball hε_ball⟩
  -- The negative line parameter is exactly the subtraction endpoint.
  simpa [sub_eq_add_neg] using hball hnegε_ball

/-- Helper for Exercise 4.2: the genuinely higher-dimensional feasible branch should be excluded by
an active-face perturbation, so points in that branch are not extreme. -/
lemma many_fractional_deleted_vertex_system_point_not_extreme
    {n : ℕ} {V : Finset (Fin n → ℝ)}
    (hV_vertices : ∀ ⦃v : Fin n → ℝ⦄, v ∈ V → is_zero_one_vector v)
    (hV_nonadjacent : ((V : Set (Fin n → ℝ)).Pairwise fun u v ↦ ¬ hypercube_adjacent u v))
    {x : Fin n → ℝ}
    (hx : x ∈ {y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v y})
    (hx_nonbinary : ¬ is_zero_one_vector x)
    (hsmall : ¬ ∃ i : Fin n, ∀ j : Fin n, j ≠ i → x j = 0 ∨ x j = 1) :
    x ∉ ({y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v y}).extremePoints ℝ := by
  -- Route correction: the higher-dimensional branch must be handled by the source-faithful
  -- active-face perturbation argument, not by another one-coordinate edge decomposition.
  -- The extra hypothesis `hx_nonbinary` is necessary: for `n = 0`, the negation of `hsmall` holds
  -- vacuously even though the unique feasible point is binary and therefore extreme.
  obtain ⟨d, hd_ne, hd_interior, hd_active⟩ :=
    existsFractionalActiveKernelDirection hV_vertices hV_nonadjacent hx hx_nonbinary hsmall
  obtain ⟨ε, hε_pos, hminus, hplus⟩ :=
    existsTwoSidedPerturbation_mem_deletedVertexSystem hx hd_interior hd_active
  intro hx_extreme
  have hsegment : x ∈ openSegment ℝ (x - ε • d) (x + ε • d) := by
    -- The original point is the midpoint of the two feasible perturbations.
    simpa using (mem_openSegment_sub_add (𝕜 := ℝ) x (ε • d))
  have hminus_eq : x - ε • d = x :=
    (mem_extremePoints_iff_left.mp hx_extreme).2
      (x - ε • d) hminus (x + ε • d) hplus hsegment
  have hsmul_zero : ε • d = 0 := sub_eq_self.mp hminus_eq
  -- Positivity of the parameter and nontriviality of the direction contradict that equality.
  exact (smul_ne_zero (ne_of_gt hε_pos) hd_ne) hsmul_zero

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_2.lean.
Formerly tracked as high delta sorry cleanup ch4 exercise 4 2 and
`sorry cleanup existing repo batch3 ch4_sec4_12_exercise_4_2`. Exercise 4.2. If `V` is a finite
family of pairwise nonadjacent vertices of the `n`-hypercube,
then the convex hull of the remaining hypercube vertices is exactly the subset of `[0,1]^n`
cut out by the support inequalities associated with the deleted vertices. -/
theorem convexHull_hypercube_vertices_diff_eq_deleted_vertex_inequalities
    {n : ℕ} {V : Finset (Fin n → ℝ)}
    (hV_vertices : ∀ ⦃v : Fin n → ℝ⦄, v ∈ V → is_zero_one_vector v)
    (hV_nonadjacent : ((V : Set (Fin n → ℝ)).Pairwise fun u v ↦ ¬ hypercube_adjacent u v)) :
    convexHull ℝ ({v : Fin n → ℝ | is_zero_one_vector v} \ (V : Set (Fin n → ℝ))) =
      {x | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧ ∀ v ∈ V, deleted_vertex_inequality v x} := by
  classical
  let S : Set (Fin n → ℝ) := {v : Fin n → ℝ | is_zero_one_vector v} \ (V : Set (Fin n → ℝ))
  let P : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
    ∀ v ∈ V, deleted_vertex_inequality v x}
  have hSP : convexHull ℝ S ⊆ P := by
    -- The easy inclusion is validity of every deleted inequality on every undeleted vertex,
    -- followed by convexity of the deleted-vertex system.
    simpa [S, P] using convexHull_hypercube_vertices_diff_subset_deleted_vertex_system hV_vertices
  have hPconvex : Convex ℝ P := by
    -- The deleted-vertex system is an intersection of the unit cube with finitely many
    -- deleted-vertex halfspaces.
    simpa [P] using (deleted_vertex_system_convex : Convex ℝ P)
  have hPclosed : IsClosed P := by
    -- Rewrite the feasible region as the unit cube intersected with closed halfspaces.
    have hrewrite :
        P = Set.Icc (0 : Fin n → ℝ) 1 ∩
          ⋂ v : ↥V, {x : Fin n → ℝ | deleted_vertex_inequality (v : Fin n → ℝ) x} := by
      ext x
      simp [P]
    rw [hrewrite]
    refine isClosed_Icc.inter ?_
    have hregionClosed (v : ↥V) :
        IsClosed {x : Fin n → ℝ | deleted_vertex_inequality (v : Fin n → ℝ) x} := by
      rw [deleted_vertex_region_eq_preimage]
      exact (isClosed_Iic).preimage
        (deleted_vertex_linear (v : Fin n → ℝ)).continuous_of_finiteDimensional
    exact isClosed_iInter hregionClosed
  have hPsubset_cube : P ⊆ Set.Icc (0 : Fin n → ℝ) 1 := by
    -- Membership in the deleted-vertex system includes the box constraints by definition.
    intro x hx
    have hx' : x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
        ∀ v ∈ V, deleted_vertex_inequality v x := by
      simpa [P] using hx
    exact hx'.1
  have hPcompact : IsCompact P := by
    -- The feasible region is a closed subset of the compact unit cube.
    exact IsCompact.of_isClosed_subset isCompact_Icc hPclosed hPsubset_cube
  have hPextreme_subset : P.extremePoints ℝ ⊆ S := by
    intro x hxext
    have hxP : x ∈ P := extremePoints_subset hxext
    have hx_deleted_system :
        x ∈ {y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
          ∀ v ∈ V, deleted_vertex_inequality v y} := by
      simpa [P] using hxP
    by_cases hx_binary : is_zero_one_vector x
    · -- A feasible binary point is an undeleted hypercube vertex, hence already belongs to `S`.
      refine ⟨hx_binary, ?_⟩
      intro hxV
      have hineq : deleted_vertex_inequality x x := by
        simpa [P] using (hxP.2 x hxV)
      exact
        (deleted_vertex_inequality_iff_ne_on_hypercube_vertices hx_binary hx_binary).1 hineq rfl
    · by_cases hsmall : ∃ i : Fin n, ∀ j : Fin n, j ≠ i → x j = 0 ∨ x j = 1
      · -- The one-fractional-coordinate branch already places `x` in the convex hull of undeleted
        -- hypercube vertices, so extremality forces `x` to be one of those vertices.
        rcases hsmall with ⟨i, hi⟩
        have hxHull : x ∈ convexHull ℝ S := by
          simpa [S, P] using
            mem_convexHull_of_all_but_one_integral_coordinate hV_vertices
              hx_deleted_system i hi
        have hxextHull : x ∈ (convexHull ℝ S).extremePoints ℝ :=
          inter_extremePoints_subset_extremePoints_of_subset hSP ⟨hxHull, hxext⟩
        exact extremePoints_convexHull_subset hxextHull
      · -- Route correction: after removing the binary case, only the genuinely higher-dimensional
        -- fractional branch remains, and that branch should be excluded by perturbation.
        exact False.elim <|
          many_fractional_deleted_vertex_system_point_not_extreme hV_vertices hV_nonadjacent
            hx_deleted_system hx_binary hsmall hxext
  have hSfinite : S.Finite := by
    -- The undeleted vertices form a subset of the finite `0/1` cube.
    refine (finite_zero_one_vectors n).subset ?_
    intro x hx
    simpa [S] using hx.1
  refine Set.Subset.antisymm hSP ?_
  intro x hx
  have hclosure : closure (convexHull ℝ (P.extremePoints ℝ)) = P :=
    closure_convexHull_extremePoints hPcompact hPconvex
  have hxClosure : x ∈ closure (convexHull ℝ (P.extremePoints ℝ)) := by
    -- Krein-Milman reduces the feasible region to the closure of the convex hull of its extreme
    -- points.
    simpa [hclosure] using hx
  have hxClosureS : x ∈ closure (convexHull ℝ S) := by
    -- Every extreme point already lies in `S`, so the same holds for their convex hull.
    exact (closure_mono (convexHull_mono hPextreme_subset)) hxClosure
  -- The undeleted vertex set is finite, so its convex hull is closed and the closure can be
  -- removed.
  simpa [(hSfinite.isClosed_convexHull ℝ).closure_eq] using hxClosureS

#print axioms convexHull_hypercube_vertices_diff_eq_deleted_vertex_inequalities
