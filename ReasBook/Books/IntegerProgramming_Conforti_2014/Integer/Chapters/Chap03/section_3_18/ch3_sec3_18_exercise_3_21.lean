/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_18
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1

open Set
open scoped BigOperators

/-
Exercise 3.21 is source-facing on the assignment polytope from Example 3.18, whose coordinates
are already indexed intrinsically by pairs `(i, j)`. This file therefore states the facet
classification directly for `assignment_polytope n` and uses the chapter's canonical facet
owner `IsFacetOf`.
-/

/-- The coordinate face of the assignment polytope cut out by the equation `x i j = 0`. -/
def assignment_coordinate_zero_face (n : ℕ) (i j : Fin n) :
    Set ((Fin n × Fin n) → ℝ) :=
  assignment_polytope n ∩ {x | x (i, j) = 0}

/-- Membership in `assignment_coordinate_zero_face n i j` means belonging to the assignment
polytope and having vanishing `(i,j)`-coordinate. -/
theorem mem_assignment_coordinate_zero_face_iff
    {n : ℕ} {i j : Fin n} {x : (Fin n × Fin n) → ℝ} :
    x ∈ assignment_coordinate_zero_face n i j ↔ x ∈ assignment_polytope n ∧ x (i, j) = 0 := by
  rfl

/-- Helper for Exercise 3.21: every point of the `2 × 2` assignment polytope is determined by its
`(0,0)`-coordinate. -/
theorem mem_assignment_polytope_two_iff {x : (Fin 2 × Fin 2) → ℝ} :
    x ∈ assignment_polytope 2 ↔
      ∃ t : ℝ,
        0 ≤ t ∧
          t ≤ 1 ∧
            x (0, 0) = t ∧
              x (0, 1) = 1 - t ∧
                x (1, 0) = 1 - t ∧
                  x (1, 1) = t := by
  rw [mem_assignment_polytope_iff]
  constructor
  · rintro ⟨hrow, hcol, hnonneg⟩
    refine ⟨x (0, 0), hnonneg 0 0, ?_, rfl, ?_, ?_, ?_⟩
    · -- The row-sum equation bounds the free parameter above by `1`.
      have hrow0 : x (0, 0) + x (0, 1) = 1 := by
        simpa [Fin.sum_univ_two] using hrow 0
      have hx01_nonneg : 0 ≤ x (0, 1) := hnonneg 0 1
      linarith
    · -- The first row fixes the upper-right entry.
      have hrow0 : x (0, 0) + x (0, 1) = 1 := by
        simpa [Fin.sum_univ_two] using hrow 0
      linarith
    · -- The first column fixes the lower-left entry.
      have hcol0 : x (0, 0) + x (1, 0) = 1 := by
        simpa [Fin.sum_univ_two] using hcol 0
      linarith
    · -- The second row then forces the lower-right entry back to `t`.
      have hrow1 : x (1, 0) + x (1, 1) = 1 := by
        simpa [Fin.sum_univ_two] using hrow 1
      have hcol0 : x (0, 0) + x (1, 0) = 1 := by
        simpa [Fin.sum_univ_two] using hcol 0
      linarith
  · rintro ⟨t, ht_nonneg, ht_le_one, hx00, hx01, hx10, hx11⟩
    refine ⟨?_, ?_, ?_⟩
    · -- The parameterization satisfies both row sums.
      intro i
      fin_cases i <;> simp [hx00, hx01, hx10, hx11]
    · -- The same parameterization satisfies both column sums.
      intro j
      fin_cases j <;> simp [hx00, hx01, hx10, hx11]
    · -- The bounds `0 ≤ t ≤ 1` are exactly the nonnegativity constraints.
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hx00, hx01, hx10, hx11, ht_nonneg, ht_le_one,
        sub_nonneg.mpr ht_le_one]

/-- Helper for Exercise 3.21: the diagonal permutation point of `assignment_polytope 2`. -/
def assignment_two_diag : (Fin 2 × Fin 2) → ℝ :=
  fun p ↦ if p.1 = p.2 then 1 else 0

/-- Helper for Exercise 3.21: the off-diagonal permutation point of `assignment_polytope 2`. -/
def assignment_two_swap : (Fin 2 × Fin 2) → ℝ :=
  fun p ↦ if p.1 = p.2 then 0 else 1

/-- Helper for Exercise 3.21: the diagonal permutation point lies in the `2 × 2` assignment
polytope. -/
theorem assignment_two_diag_mem_assignment_polytope :
    assignment_two_diag ∈ assignment_polytope 2 := by
  -- The diagonal permutation point corresponds to the parameter value `t = 1`.
  refine mem_assignment_polytope_two_iff.2 ?_
  refine ⟨1, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [assignment_two_diag]

/-- Helper for Exercise 3.21: the off-diagonal permutation point lies in the `2 × 2` assignment
polytope. -/
theorem assignment_two_swap_mem_assignment_polytope :
    assignment_two_swap ∈ assignment_polytope 2 := by
  -- The off-diagonal permutation point corresponds to the parameter value `t = 0`.
  refine mem_assignment_polytope_two_iff.2 ?_
  refine ⟨0, le_rfl, by norm_num, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [assignment_two_swap]

/-- Helper for Exercise 3.21: every coordinate-zero face of the `2 × 2` assignment polytope is one
of the two permutation vertices. -/
theorem assignment_coordinate_zero_face_eq_singleton_for_n_eq_two
    (i j : Fin 2) :
    assignment_coordinate_zero_face 2 i j =
      if i = j then {assignment_two_swap} else {assignment_two_diag} := by
  -- There are only four coordinates, so a case split reduces the face description to the
  -- one-parameter normal form above.
  fin_cases i <;> fin_cases j
  · ext x
    constructor
    · intro hx
      rcases (mem_assignment_polytope_two_iff.1 hx.1) with
        ⟨t, ht_nonneg, ht_le_one, hx00, hx01, hx10, hx11⟩
      have ht_zero : t = 0 := by simpa [hx00] using hx.2
      have hx_eq : x = assignment_two_swap := by
        ext p
        rcases p with ⟨a, b⟩
        fin_cases a <;> fin_cases b <;>
          simp [assignment_two_swap, hx00, hx01, hx10, hx11, ht_zero]
      simpa [hx_eq]
    · intro hx
      rcases Set.mem_singleton_iff.1 hx with rfl
      exact ⟨assignment_two_swap_mem_assignment_polytope, by norm_num [assignment_two_swap]⟩
  · ext x
    constructor
    · intro hx
      rcases (mem_assignment_polytope_two_iff.1 hx.1) with
        ⟨t, ht_nonneg, ht_le_one, hx00, hx01, hx10, hx11⟩
      have ht_one : t = 1 := by
        have hx01_zero : x (0, 1) = 0 := hx.2
        linarith [hx01_zero, hx01]
      have hx_eq : x = assignment_two_diag := by
        ext p
        rcases p with ⟨a, b⟩
        fin_cases a <;> fin_cases b <;>
          simp [assignment_two_diag, hx00, hx01, hx10, hx11, ht_one]
      simpa [hx_eq]
    · intro hx
      rcases Set.mem_singleton_iff.1 hx with rfl
      exact ⟨assignment_two_diag_mem_assignment_polytope, by norm_num [assignment_two_diag]⟩
  · ext x
    constructor
    · intro hx
      rcases (mem_assignment_polytope_two_iff.1 hx.1) with
        ⟨t, ht_nonneg, ht_le_one, hx00, hx01, hx10, hx11⟩
      have ht_one : t = 1 := by
        have hx10_zero : x (1, 0) = 0 := hx.2
        linarith [hx10_zero, hx10]
      have hx_eq : x = assignment_two_diag := by
        ext p
        rcases p with ⟨a, b⟩
        fin_cases a <;> fin_cases b <;>
          simp [assignment_two_diag, hx00, hx01, hx10, hx11, ht_one]
      simpa [hx_eq]
    · intro hx
      rcases Set.mem_singleton_iff.1 hx with rfl
      exact ⟨assignment_two_diag_mem_assignment_polytope, by norm_num [assignment_two_diag]⟩
  · ext x
    constructor
    · intro hx
      rcases (mem_assignment_polytope_two_iff.1 hx.1) with
        ⟨t, ht_nonneg, ht_le_one, hx00, hx01, hx10, hx11⟩
      have ht_zero : t = 0 := by
        have hx11_zero : x (1, 1) = 0 := hx.2
        linarith [hx11_zero, hx11]
      have hx_eq : x = assignment_two_swap := by
        ext p
        rcases p with ⟨a, b⟩
        fin_cases a <;> fin_cases b <;>
          simp [assignment_two_swap, hx00, hx01, hx10, hx11, ht_zero]
      simpa [hx_eq]
    · intro hx
      rcases Set.mem_singleton_iff.1 hx with rfl
      exact ⟨assignment_two_swap_mem_assignment_polytope, by norm_num [assignment_two_swap]⟩

/-- Helper for Exercise 3.21: the diagonal permutation point is exposed in the `2 × 2`
assignment polytope by maximizing the `(0,0)`-coordinate. -/
theorem assignment_two_diag_isExposed :
    IsExposed ℝ (assignment_polytope 2) ({assignment_two_diag} : Set ((Fin 2 × Fin 2) → ℝ)) := by
  let l : StrongDual ℝ ((Fin 2 × Fin 2) → ℝ) := ContinuousLinearMap.proj (0, 0)
  have hface :
      ({assignment_two_diag} : Set ((Fin 2 × Fin 2) → ℝ)) =
        l.toExposed (assignment_polytope 2) := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_singleton_iff.1 hx with rfl
      refine ⟨assignment_two_diag_mem_assignment_polytope, ?_⟩
      intro y hy
      rcases mem_assignment_polytope_two_iff.1 hy with
        ⟨t, ht_nonneg, ht_le_one, hy00, hy01, hy10, hy11⟩
      simpa [l, hy00, assignment_two_diag] using ht_le_one
    · intro hx
      have hx00_le : x (0, 0) ≤ 1 := by
        rcases mem_assignment_polytope_two_iff.1 hx.1 with
          ⟨t, ht_nonneg, ht_le_one, hx00, hx01, hx10, hx11⟩
        linarith
      have hx00_ge : 1 ≤ x (0, 0) := by
        simpa [l, assignment_two_diag] using hx.2 assignment_two_diag
          assignment_two_diag_mem_assignment_polytope
      have hx00 : x (0, 0) = 1 := le_antisymm hx00_le hx00_ge
      rcases mem_assignment_polytope_two_iff.1 hx.1 with
        ⟨t, ht_nonneg, ht_le_one, hx00', hx01, hx10, hx11⟩
      have ht_one : t = 1 := by linarith [hx00, hx00']
      have hx_eq : x = assignment_two_diag := by
        ext p
        rcases p with ⟨a, b⟩
        fin_cases a <;> fin_cases b <;>
          simp [assignment_two_diag, hx00', hx01, hx10, hx11, ht_one]
      simpa [hx_eq]
  -- Rewriting the singleton as a maximizer set turns exposedness into the canonical mathlib fact.
  rw [hface]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Exercise 3.21: the off-diagonal permutation point is exposed in the `2 × 2`
assignment polytope by minimizing the `(0,0)`-coordinate. -/
theorem assignment_two_swap_isExposed :
    IsExposed ℝ (assignment_polytope 2) ({assignment_two_swap} : Set ((Fin 2 × Fin 2) → ℝ)) := by
  let l : StrongDual ℝ ((Fin 2 × Fin 2) → ℝ) := -ContinuousLinearMap.proj (0, 0)
  have hface :
      ({assignment_two_swap} : Set ((Fin 2 × Fin 2) → ℝ)) =
        l.toExposed (assignment_polytope 2) := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_singleton_iff.1 hx with rfl
      refine ⟨assignment_two_swap_mem_assignment_polytope, ?_⟩
      intro y hy
      rcases mem_assignment_polytope_two_iff.1 hy with
        ⟨t, ht_nonneg, ht_le_one, hy00, hy01, hy10, hy11⟩
      have ht_nonpos : -t ≤ 0 := by linarith
      simpa [l, hy00, assignment_two_swap] using ht_nonpos
    · intro hx
      have hx00_nonneg : 0 ≤ x (0, 0) := by
        rcases mem_assignment_polytope_two_iff.1 hx.1 with
          ⟨t, ht_nonneg, ht_le_one, hx00, hx01, hx10, hx11⟩
        linarith [hx00]
      have hx00_nonpos : x (0, 0) ≤ 0 := by
        simpa [l, assignment_two_swap] using hx.2 assignment_two_swap
          assignment_two_swap_mem_assignment_polytope
      have hx00 : x (0, 0) = 0 := le_antisymm hx00_nonpos hx00_nonneg
      rcases mem_assignment_polytope_two_iff.1 hx.1 with
        ⟨t, ht_nonneg, ht_le_one, hx00', hx01, hx10, hx11⟩
      have ht_zero : t = 0 := by linarith [hx00, hx00']
      have hx_eq : x = assignment_two_swap := by
        ext p
        rcases p with ⟨a, b⟩
        fin_cases a <;> fin_cases b <;>
          simp [assignment_two_swap, hx00', hx01, hx10, hx11, ht_zero]
      simpa [hx_eq]
  -- Rewriting the singleton as a maximizer set turns exposedness into the canonical mathlib fact.
  rw [hface]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Exercise 3.21: each coordinate-zero face of the `2 × 2` assignment polytope is
exposed. -/
theorem assignment_coordinate_zero_face_isExposed_for_n_eq_two
    (i j : Fin 2) :
    IsExposed ℝ (assignment_polytope 2) (assignment_coordinate_zero_face 2 i j) := by
  -- The four coordinate faces are exactly the two exposed permutation vertices.
  rw [assignment_coordinate_zero_face_eq_singleton_for_n_eq_two]
  by_cases hij : i = j
  · simp [hij, assignment_two_swap_isExposed]
  · simp [hij, assignment_two_diag_isExposed]

/-- Helper for Exercise 3.21: the only extreme points of the `2 × 2` assignment polytope are the
two permutation vertices. -/
theorem mem_assignment_polytope_two_extremePoints_iff
    {x : (Fin 2 × Fin 2) → ℝ}
    (hx : x ∈ (assignment_polytope 2).extremePoints ℝ) :
    x = assignment_two_diag ∨ x = assignment_two_swap := by
  rcases (mem_extremePoints_iff_left.1 hx) with ⟨hx_mem, hx_extreme⟩
  rcases mem_assignment_polytope_two_iff.1 hx_mem with
    ⟨t, ht_nonneg, ht_le_one, hx00, hx01, hx10, hx11⟩
  by_cases ht_zero : t = 0
  · -- The parameter value `t = 0` is exactly the off-diagonal permutation vertex.
    right
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [assignment_two_swap, hx00, hx01, hx10, hx11, ht_zero]
  by_cases ht_one : t = 1
  · -- The parameter value `t = 1` is exactly the diagonal permutation vertex.
    left
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [assignment_two_diag, hx00, hx01, hx10, hx11, ht_one]
  · -- Otherwise `0 < t < 1`, so `x` lies in the open segment joining the two permutation points.
    have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht_zero)
    have ht_lt_one : t < 1 := lt_of_le_of_ne ht_le_one ht_one
    have hx_open :
        x ∈ openSegment ℝ assignment_two_diag assignment_two_swap := by
      refine ⟨t, 1 - t, ht_pos, sub_pos.mpr ht_lt_one, by linarith, ?_⟩
      ext p
      rcases p with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;>
        simp [assignment_two_diag, assignment_two_swap, hx00, hx01, hx10, hx11]
    have hdiag_eq : assignment_two_diag = x := by
      exact hx_extreme assignment_two_diag assignment_two_diag_mem_assignment_polytope
        assignment_two_swap assignment_two_swap_mem_assignment_polytope hx_open
    have ht_eq_one : t = 1 := by
      simpa [assignment_two_diag, hx00] using (congrArg (fun y ↦ y (0, 0)) hdiag_eq).symm
    exact (ht_one ht_eq_one).elim

/-- Helper for Exercise 3.21: every coordinate-zero face of the `2 × 2` assignment polytope is a
facet. -/
theorem assignment_coordinate_zero_face_isFacetOf_for_n_eq_two
    (i j : Fin 2) :
    IsFacetOf (assignment_polytope 2) (assignment_coordinate_zero_face 2 i j) := by
  refine ⟨?_, assignment_coordinate_zero_face_isExposed_for_n_eq_two i j, ?_⟩
  · -- Each coordinate face is one of the two singleton permutation vertices.
    rw [assignment_coordinate_zero_face_eq_singleton_for_n_eq_two]
    by_cases hij : i = j <;> simp [hij]
  · -- The affine span of a singleton has zero-dimensional direction, while the ambient polytope
    -- has dimension one.
    have hface_dim :
        Module.finrank ℝ (affineSpan ℝ (assignment_coordinate_zero_face 2 i j)).direction = 0 := by
      rw [assignment_coordinate_zero_face_eq_singleton_for_n_eq_two]
      by_cases hij : i = j <;> simp [hij, direction_affineSpan, vectorSpan_singleton]
    have hamb_dim :
        Module.finrank ℝ (affineSpan ℝ (assignment_polytope 2)).direction = 1 := by
      simpa using assignment_polytope_finrank_direction_affineSpan 2
    omega

/-- Helper for Exercise 3.21: when `n = 1`, the assignment polytope has no facets. -/
theorem exercise_3_21_assignment_polytope_has_no_facets_for_n_eq_one
    (F : Set ((Fin 1 × Fin 1) → ℝ)) :
    ¬ IsFacetOf (assignment_polytope 1) F := by
  intro hF
  rcases hF with ⟨hF_nonempty, hF_exposed, hcodim⟩
  have hdim :
      Module.finrank ℝ (affineSpan ℝ (assignment_polytope 1)).direction = 0 := by
    simpa using assignment_polytope_finrank_direction_affineSpan 1
  -- The codimension-one equation would force a natural number to satisfy `k + 1 = 0`.
  have : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = 0 := by
    simpa [hdim] using hcodim
  omega

/-- Helper for Exercise 3.21: when `n = 2`, the facets of the assignment polytope are exactly the
coordinate faces cut out by the inequalities `x i j ≥ 0`. -/
theorem exercise_3_21_assignment_polytope_facets_for_n_eq_two
    (F : Set ((Fin 2 × Fin 2) → ℝ)) :
    IsFacetOf (assignment_polytope 2) F ↔
      ∃ i j : Fin 2, F = assignment_coordinate_zero_face 2 i j := by
  constructor
  · intro hF
    rcases hF with ⟨hF_nonempty, hF_exposed, hF_codim⟩
    rcases hF_nonempty with ⟨x₀, hx₀F⟩
    have hamb_dim :
        Module.finrank ℝ (affineSpan ℝ (assignment_polytope 2)).direction = 1 := by
      simpa using assignment_polytope_finrank_direction_affineSpan 2
    have hF_dim :
        Module.finrank ℝ (affineSpan ℝ F).direction = 0 := by
      omega
    have hF_dir :
        (affineSpan ℝ F).direction = ⊥ := by
      simpa using (Submodule.finrank_eq_zero
        (R := ℝ) (S := (affineSpan ℝ F).direction)).1 hF_dim
    have hspan_eq :
        affineSpan ℝ F = affineSpan ℝ ({x₀} : Set ((Fin 2 × Fin 2) → ℝ)) := by
      -- Equal directions through a common point force the affine spans to coincide.
      refine (AffineSubspace.eq_iff_direction_eq_of_mem
        (mem_affineSpan ℝ hx₀F) (mem_affineSpan ℝ (Set.mem_singleton x₀))).2 ?_
      simpa [direction_affineSpan, vectorSpan_singleton] using hF_dir
    have hF_singleton : F = ({x₀} : Set ((Fin 2 × Fin 2) → ℝ)) := by
      -- Once the affine span collapses to a singleton, every point of the face equals `x₀`.
      ext x
      constructor
      · intro hx
        have hx_span : x ∈ affineSpan ℝ F := mem_affineSpan ℝ hx
        rw [hspan_eq, AffineSubspace.mem_affineSpan_singleton] at hx_span
        simpa [hx_span]
      · intro hx
        rcases Set.mem_singleton_iff.1 hx with rfl
        exact hx₀F
    have hx₀_extreme : x₀ ∈ (assignment_polytope 2).extremePoints ℝ := by
      have hsingleton_extreme : IsExtreme ℝ (assignment_polytope 2)
          ({x₀} : Set ((Fin 2 × Fin 2) → ℝ)) := by
        simpa [hF_singleton] using hF_exposed.isExtreme
      exact hsingleton_extreme.mem_extremePoints
    rcases mem_assignment_polytope_two_extremePoints_iff hx₀_extreme with hx₀_diag | hx₀_swap
    · -- The diagonal vertex is the coordinate face `x 0 1 = 0`.
      refine ⟨0, 1, ?_⟩
      calc
        F = ({assignment_two_diag} : Set ((Fin 2 × Fin 2) → ℝ)) := by
          simpa [hx₀_diag] using hF_singleton
        _ = assignment_coordinate_zero_face 2 0 1 := by
          symm
          simpa using assignment_coordinate_zero_face_eq_singleton_for_n_eq_two
            (0 : Fin 2) (1 : Fin 2)
    · -- The off-diagonal vertex is the coordinate face `x 0 0 = 0`.
      refine ⟨0, 0, ?_⟩
      calc
        F = ({assignment_two_swap} : Set ((Fin 2 × Fin 2) → ℝ)) := by
          simpa [hx₀_swap] using hF_singleton
        _ = assignment_coordinate_zero_face 2 0 0 := by
          symm
          simpa using assignment_coordinate_zero_face_eq_singleton_for_n_eq_two
            (0 : Fin 2) (0 : Fin 2)
  · rintro ⟨i, j, rfl⟩
    -- The reverse implication is exactly the coordinate-face facet lemma.
    exact assignment_coordinate_zero_face_isFacetOf_for_n_eq_two i j

/-- Helper for Exercise 3.21: the canonical tangent space for the assignment polytope is its
ambient affine-span direction. -/
abbrev assignment_tangent_space (n : ℕ) : Submodule ℝ ((Fin n × Fin n) → ℝ) :=
  (affineSpan ℝ (assignment_polytope n)).direction

/-- Helper for Exercise 3.21: when `n > 0`, the uniform doubly stochastic point with all entries
`1 / n` belongs to the assignment polytope. -/
theorem assignment_uniform_point_mem_assignment_polytope
    {n : ℕ} (hn : 0 < n) :
    (fun _ : Fin n × Fin n ↦ (1 : ℝ) / n) ∈ assignment_polytope n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa using assignment_uniform_point_mem_polytope_succ m

/-- Helper for Exercise 3.21: for positive size, the tangent space of the assignment polytope is
the kernel of the row-sum and column-sum constraint map. -/
theorem assignment_tangent_space_eq_constraint_kernel
    {n : ℕ} (hn : 0 < n) :
    assignment_tangent_space n =
      LinearMap.ker (assignment_constraint_matrix n).mulVecLin := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  refine le_antisymm ?_ ?_
  · simpa [assignment_tangent_space] using
      direction_assignment_polytope_le_kernel (m + 1)
        (fun _ ↦ (1 : ℝ) / (m + 1))
        (assignment_uniform_point_mem_polytope_succ m)
  · simpa [assignment_tangent_space] using assignment_kernel_subset_direction_succ m

/-- Helper for Exercise 3.21: the textbook witness point in the coordinate face `x (i,j) = 0`. -/
noncomputable def assignment_coordinate_zero_face_witness (n : ℕ) (i j : Fin n) :
    (Fin n × Fin n) → ℝ :=
  fun p ↦
    if p.1 = i then
      if p.2 = j then 0 else (1 : ℝ) / (n - 1)
    else if p.2 = j then
      (1 : ℝ) / (n - 1)
    else
      (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ))

/-- Helper for Exercise 3.21: the coordinate-face witness vanishes at the distinguished
coordinate. -/
theorem assignment_coordinate_zero_face_witness_apply_self
    {n : ℕ} (i j : Fin n) :
    assignment_coordinate_zero_face_witness n i j (i, j) = 0 := by
  -- The defining case split lands in the distinguished zero branch.
  simp [assignment_coordinate_zero_face_witness]

/-- Helper for Exercise 3.21: on the distinguished row away from the forced-zero coordinate, the
witness takes the value `1 / (n - 1)`. -/
theorem assignment_coordinate_zero_face_witness_apply_row
    {n : ℕ} (i j c : Fin n) (hc : c ≠ j) :
    assignment_coordinate_zero_face_witness n i j (i, c) = (1 : ℝ) / (n - 1) := by
  -- On row `i`, the only exceptional column is `j`.
  simp [assignment_coordinate_zero_face_witness, hc]

/-- Helper for Exercise 3.21: on the distinguished column away from the forced-zero coordinate,
the witness takes the value `1 / (n - 1)`. -/
theorem assignment_coordinate_zero_face_witness_apply_col
    {n : ℕ} (i j r : Fin n) (hr : r ≠ i) :
    assignment_coordinate_zero_face_witness n i j (r, j) = (1 : ℝ) / (n - 1) := by
  -- Off the distinguished row, the column `j` carries the larger compensating value.
  simp [assignment_coordinate_zero_face_witness, hr]

/-- Helper for Exercise 3.21: away from the distinguished row and column, the witness takes the
uniform background value. -/
theorem assignment_coordinate_zero_face_witness_apply_off
    {n : ℕ} (i j r c : Fin n) (hr : r ≠ i) (hc : c ≠ j) :
    assignment_coordinate_zero_face_witness n i j (r, c) =
      (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ)) := by
  -- Outside the distinguished row and column, only the background branch remains.
  simp [assignment_coordinate_zero_face_witness, hr, hc]

/-- Helper for Exercise 3.21: the canonical coordinate-face witness is feasible and strictly
positive away from the forced-zero coordinate. -/
theorem assignment_coordinate_zero_face_witness_mem
    {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    assignment_coordinate_zero_face_witness n i j ∈ assignment_coordinate_zero_face n i j ∧
      ∀ p, p ≠ (i, j) → 0 < assignment_coordinate_zero_face_witness n i j p :=
by
  have hnm1_nat_pos : 0 < n - 1 := by omega
  have hnm2_nat_pos : 0 < n - 2 := by omega
  have hnm1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnm1_nat_pos
  have hnm2_pos : (0 : ℝ) < ((n - 2 : ℕ) : ℝ) := by
    exact_mod_cast hnm2_nat_pos
  have hnm1_real_pos : 0 < (n : ℝ) - 1 := by
    simpa using hnm1_pos
  have hnm2_real_pos : 0 < (n : ℝ) - 2 := by
    simpa using hnm2_pos
  have hnm1_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have hn1 : 1 ≤ n := by omega
    norm_num [Nat.cast_sub hn1]
  have hnm2_cast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    have hn2 : 2 ≤ n := by omega
    norm_num [Nat.cast_sub hn2]
  have hnm1_ne : (n - 1 : ℝ) ≠ 0 := ne_of_gt hnm1_real_pos
  have hrow_val_pos : 0 < (1 : ℝ) / (n - 1) := by
    simpa using one_div_pos.mpr hnm1_real_pos
  have hbackground_pos :
      0 < (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ)) := by
    simpa using div_pos hnm2_real_pos (pow_pos hnm1_real_pos _)
  have hcard_erase : ∀ a : Fin n, (Finset.univ.erase a).card = n - 1 := by
    intro a
    simpa [Finset.card_univ, Fintype.card_fin] using
      Finset.card_erase (s := Finset.univ) (a := a) (Finset.mem_univ a)
  constructor
  · refine ⟨?_, assignment_coordinate_zero_face_witness_apply_self i j⟩
    rw [mem_assignment_polytope_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro r
      by_cases hr : r = i
      · subst r
        have hdecomp :
            ∑ c : Fin n, assignment_coordinate_zero_face_witness n i j (i, c) =
              Finset.sum (Finset.univ.erase j)
                (fun c ↦ assignment_coordinate_zero_face_witness n i j (i, c)) +
              assignment_coordinate_zero_face_witness n i j (i, j) := by
          simpa using
            (Finset.sum_erase_add
              (s := Finset.univ)
              (f := fun c : Fin n ↦ assignment_coordinate_zero_face_witness n i j (i, c))
              (a := j)
              (by simp)).symm
        have hsum_row :
            Finset.sum (Finset.univ.erase j)
                (fun c ↦ assignment_coordinate_zero_face_witness n i j (i, c)) =
              Finset.sum (Finset.univ.erase j) (fun _ : Fin n ↦ (1 : ℝ) / (n - 1)) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          exact assignment_coordinate_zero_face_witness_apply_row i j c
            ((Finset.mem_erase.mp hc).1)
        -- The distinguished row has `n - 1` equal positive entries and one forced zero.
        calc
          ∑ c : Fin n, assignment_coordinate_zero_face_witness n i j (i, c) = _ := hdecomp
          _ = Finset.sum (Finset.univ.erase j) (fun _ ↦ ((1 : ℝ) / (n - 1))) + 0 := by
                rw [hsum_row, assignment_coordinate_zero_face_witness_apply_self]
          _ = 1 := by
                simp [Finset.sum_const, hcard_erase j]
                field_simp [hnm1_ne]
                rw [hnm1_cast]
      · have hsum_off :
            Finset.sum (Finset.univ.erase j)
                (fun c ↦ assignment_coordinate_zero_face_witness n i j (r, c)) =
              Finset.sum (Finset.univ.erase j)
                (fun _ : Fin n ↦ (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ))) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          exact assignment_coordinate_zero_face_witness_apply_off i j r c hr
            ((Finset.mem_erase.mp hc).1)
        have hdecomp :
            ∑ c : Fin n, assignment_coordinate_zero_face_witness n i j (r, c) =
              Finset.sum (Finset.univ.erase j)
                (fun c ↦ assignment_coordinate_zero_face_witness n i j (r, c)) +
              assignment_coordinate_zero_face_witness n i j (r, j) := by
          simpa using
            (Finset.sum_erase_add
              (s := Finset.univ)
              (f := fun c : Fin n ↦ assignment_coordinate_zero_face_witness n i j (r, c))
              (a := j)
              (by simp)).symm
        -- Every other row has one compensating `1 / (n - 1)` entry in column `j`.
        calc
          ∑ c : Fin n, assignment_coordinate_zero_face_witness n i j (r, c) = _ := hdecomp
          _ = Finset.sum (Finset.univ.erase j)
                (fun _ ↦ (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ))) +
                ((1 : ℝ) / (n - 1)) := by
                  rw [hsum_off, assignment_coordinate_zero_face_witness_apply_col i j r hr]
          _ = 1 := by
                simp [Finset.sum_const, hcard_erase j]
                field_simp [hnm1_ne]
                nlinarith [hnm1_cast]
    · intro c
      by_cases hc : c = j
      · subst c
        have hdecomp :
            ∑ r : Fin n, assignment_coordinate_zero_face_witness n i j (r, j) =
              Finset.sum (Finset.univ.erase i)
                (fun r ↦ assignment_coordinate_zero_face_witness n i j (r, j)) +
              assignment_coordinate_zero_face_witness n i j (i, j) := by
          simpa using
            (Finset.sum_erase_add
              (s := Finset.univ)
              (f := fun r : Fin n ↦ assignment_coordinate_zero_face_witness n i j (r, j))
              (a := i)
              (by simp)).symm
        have hsum_col :
            Finset.sum (Finset.univ.erase i)
                (fun r ↦ assignment_coordinate_zero_face_witness n i j (r, j)) =
              Finset.sum (Finset.univ.erase i) (fun _ : Fin n ↦ (1 : ℝ) / (n - 1)) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          exact assignment_coordinate_zero_face_witness_apply_col i j r
            ((Finset.mem_erase.mp hr).1)
        -- The distinguished column is symmetric to the distinguished row.
        calc
          ∑ r : Fin n, assignment_coordinate_zero_face_witness n i j (r, j) = _ := hdecomp
          _ = Finset.sum (Finset.univ.erase i) (fun _ ↦ ((1 : ℝ) / (n - 1))) + 0 := by
                rw [hsum_col, assignment_coordinate_zero_face_witness_apply_self]
          _ = 1 := by
                simp [Finset.sum_const, hcard_erase i]
                field_simp [hnm1_ne]
                rw [hnm1_cast]
      · have hsum_off :
            Finset.sum (Finset.univ.erase i)
                (fun r ↦ assignment_coordinate_zero_face_witness n i j (r, c)) =
              Finset.sum (Finset.univ.erase i)
                (fun _ : Fin n ↦ (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ))) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          exact assignment_coordinate_zero_face_witness_apply_off i j r c
            ((Finset.mem_erase.mp hr).1) hc
        have hdecomp :
            ∑ r : Fin n, assignment_coordinate_zero_face_witness n i j (r, c) =
              Finset.sum (Finset.univ.erase i)
                (fun r ↦ assignment_coordinate_zero_face_witness n i j (r, c)) +
              assignment_coordinate_zero_face_witness n i j (i, c) := by
          simpa using
            (Finset.sum_erase_add
              (s := Finset.univ)
              (f := fun r : Fin n ↦ assignment_coordinate_zero_face_witness n i j (r, c))
              (a := i)
              (by simp)).symm
        -- Every other column has one compensating `1 / (n - 1)` entry in row `i`.
        calc
          ∑ r : Fin n, assignment_coordinate_zero_face_witness n i j (r, c) = _ := hdecomp
          _ = Finset.sum (Finset.univ.erase i)
                (fun _ ↦ (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ))) +
                ((1 : ℝ) / (n - 1)) := by
                  rw [hsum_off, assignment_coordinate_zero_face_witness_apply_row i j c hc]
          _ = 1 := by
                simp [Finset.sum_const, hcard_erase i]
                field_simp [hnm1_ne]
                nlinarith [hnm1_cast]
    · intro r c
      by_cases hr : r = i
      · subst hr
        by_cases hc : c = j
        · subst hc
          simp [assignment_coordinate_zero_face_witness]
        · -- Off the forced-zero coordinate in row `i`, the witness is the positive edge value.
          exact le_of_lt (by simpa [assignment_coordinate_zero_face_witness, hc] using hrow_val_pos)
      · by_cases hc : c = j
        · -- Off the forced-zero coordinate in column `j`, the witness is again the edge value.
          exact le_of_lt (by simpa [assignment_coordinate_zero_face_witness, hr, hc]
            using hrow_val_pos)
        · -- Everywhere else the witness takes the positive background value.
          exact le_of_lt (by
            simpa [assignment_coordinate_zero_face_witness, hr, hc] using hbackground_pos)
  · intro p hp
    rcases p with ⟨r, c⟩
    by_cases hr : r = i
    · subst hr
      have hc : c ≠ j := by
        intro hc
        apply hp
        ext <;> simp [hc]
      -- Away from the distinguished column in row `i`, the witness is `1 / (n - 1)`.
      simpa [assignment_coordinate_zero_face_witness, hc] using hrow_val_pos
    · by_cases hc : c = j
      · -- Away from the distinguished row in column `j`, the witness is also `1 / (n - 1)`.
        simpa [assignment_coordinate_zero_face_witness, hr, hc] using hrow_val_pos
      · -- Off the distinguished row and column, the witness takes the positive background value.
        simpa [assignment_coordinate_zero_face_witness, hr, hc] using hbackground_pos

/-- Helper for Exercise 3.21: every off-coordinate entry of the canonical witness is bounded below
by the background value `(n - 2) / (n - 1)^2`. -/
theorem assignment_coordinate_zero_face_witness_lower_bound
    {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) {p : Fin n × Fin n}
    (hp : p ≠ (i, j)) :
    (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ)) ≤ assignment_coordinate_zero_face_witness n i j p := by
  have hn_gt_two : (2 : ℝ) < n := by
    exact_mod_cast (show 2 < n by omega)
  have hnm1_pos : 0 < (n : ℝ) - 1 := by
    linarith
  have hbackground_le_row_or_col :
      (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ)) ≤ (1 : ℝ) / (n - 1) := by
    -- The background value is the minimum because the row/column value exceeds it by
    -- `1 / (n - 1)^2`.
    have hdiff :
        (1 : ℝ) / (n - 1) - (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ)) =
          (1 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ)) := by
      field_simp [hnm1_pos.ne']
      ring
    have hnonneg :
        0 ≤ (1 : ℝ) / (n - 1) - (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ)) := by
      rw [hdiff]
      positivity
    linarith
  rcases p with ⟨r, c⟩
  -- Away from `(i,j)`, the witness takes either the row/column value or the background value.
  by_cases hr : r = i
  · subst hr
    have hc : c ≠ j := by
      intro hc
      apply hp
      ext <;> simp [hc]
    simpa [assignment_coordinate_zero_face_witness, hc] using hbackground_le_row_or_col
  · by_cases hc : c = j
    · simpa [assignment_coordinate_zero_face_witness, hr, hc] using hbackground_le_row_or_col
    · simpa [assignment_coordinate_zero_face_witness, hr, hc]

/-- Helper for Exercise 3.21: the existential witness lemma is packaged from the explicit
canonical witness. -/
theorem assignment_coordinate_zero_face_explicit_point_mem
    {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    ∃ x0 : (Fin n × Fin n) → ℝ,
      x0 ∈ assignment_coordinate_zero_face n i j ∧
        ∀ p, p ≠ (i, j) → 0 < x0 p :=
by
  refine ⟨assignment_coordinate_zero_face_witness n i j, ?_⟩
  exact assignment_coordinate_zero_face_witness_mem hn i j

/-- Helper for Exercise 3.21: the signed `2 × 2` rectangle direction used in the tangent-space
argument. -/
def assignment_rectangle_direction
    (n : ℕ) (r₁ r₂ c₁ c₂ : Fin n) :
    (Fin n × Fin n) → ℝ :=
  Pi.single (r₁, c₁) (1 : ℝ) +
    Pi.single (r₂, c₂) (1 : ℝ) +
    Pi.single (r₁, c₂) (-1 : ℝ) +
    Pi.single (r₂, c₁) (-1 : ℝ)

/-- Helper for Exercise 3.21: summing a coordinate basis function along the columns picks out the
matching row. -/
@[simp] theorem assignment_sum_columns_single
    {n : ℕ} (r r₀ c₀ : Fin n) (a : ℝ) :
    ∑ c : Fin n, (Pi.single (r₀, c₀) a : (Fin n × Fin n) → ℝ) (r, c) =
      if r = r₀ then a else 0 := by
  by_cases hr : r = r₀
  · subst hr
    rw [Finset.sum_eq_single_of_mem c₀ (Finset.mem_univ c₀)]
    · simp
    · intro c _ hc
      simp [hc]
  · simp [hr]

/-- Helper for Exercise 3.21: summing a coordinate basis function along the rows picks out the
matching column. -/
@[simp] theorem assignment_sum_rows_single
    {n : ℕ} (c c₀ r₀ : Fin n) (a : ℝ) :
    ∑ r : Fin n, (Pi.single (r₀, c₀) a : (Fin n × Fin n) → ℝ) (r, c) =
      if c = c₀ then a else 0 := by
  by_cases hc : c = c₀
  · subst hc
    rw [Finset.sum_eq_single_of_mem r₀ (Finset.mem_univ r₀)]
    · simp
    · intro r _ hr
      simp [hr]
  · simp [hc]

/-- Helper for Exercise 3.21: every row sum of a rectangle direction is zero. -/
theorem assignment_rectangle_direction_row_sum
    {n : ℕ} (r₁ r₂ c₁ c₂ : Fin n) (hr : r₁ ≠ r₂) (hc : c₁ ≠ c₂) :
    ∀ r : Fin n,
      ∑ c : Fin n, assignment_rectangle_direction n r₁ r₂ c₁ c₂ (r, c) = 0 :=
by
  intro r
  -- The four `Pi.single` row contributions cancel pairwise on each row.
  by_cases hr₁ : r = r₁
  · subst hr₁
    simp [assignment_rectangle_direction, Finset.sum_add_distrib, assignment_sum_columns_single, hr]
  · by_cases hr₂ : r = r₂
    · subst hr₂
      simp [assignment_rectangle_direction, Finset.sum_add_distrib, assignment_sum_columns_single, hr]
    · simp [assignment_rectangle_direction, Finset.sum_add_distrib, assignment_sum_columns_single,
        hr₁, hr₂]

/-- Helper for Exercise 3.21: every column sum of a rectangle direction is zero. -/
theorem assignment_rectangle_direction_col_sum
    {n : ℕ} (r₁ r₂ c₁ c₂ : Fin n) (hr : r₁ ≠ r₂) (hc : c₁ ≠ c₂) :
    ∀ c : Fin n,
      ∑ r : Fin n, assignment_rectangle_direction n r₁ r₂ c₁ c₂ (r, c) = 0 :=
by
  intro c
  -- The symmetric column computation again cancels the four `Pi.single` contributions.
  by_cases hc₁ : c = c₁
  · subst hc₁
    simp [assignment_rectangle_direction, Finset.sum_add_distrib, assignment_sum_rows_single, hc]
  · by_cases hc₂ : c = c₂
    · subst hc₂
      simp [assignment_rectangle_direction, Finset.sum_add_distrib, assignment_sum_rows_single, hc]
    · simp [assignment_rectangle_direction, Finset.sum_add_distrib, assignment_sum_rows_single,
        hc₁, hc₂]

/-- Helper for Exercise 3.21: every coordinate of a rectangle direction lies between `-2` and `2`.
-/
theorem assignment_rectangle_direction_bounds
    {n : ℕ} (r₁ r₂ c₁ c₂ : Fin n) (p : Fin n × Fin n) :
    -2 ≤ assignment_rectangle_direction n r₁ r₂ c₁ c₂ p ∧
      assignment_rectangle_direction n r₁ r₂ c₁ c₂ p ≤ 2 :=
by
  -- Each positive `Pi.single` term lies in `[0, 1]`, and each negative one lies in `[-1, 0]`.
  have h11_nonneg : 0 ≤ (Pi.single (r₁, c₁) (1 : ℝ) : (Fin n × Fin n) → ℝ) p := by
    by_cases hp : p = (r₁, c₁)
    · subst hp
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hp]
  have h11_le : (Pi.single (r₁, c₁) (1 : ℝ) : (Fin n × Fin n) → ℝ) p ≤ 1 := by
    by_cases hp : p = (r₁, c₁)
    · subst hp
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hp]
  have h22_nonneg : 0 ≤ (Pi.single (r₂, c₂) (1 : ℝ) : (Fin n × Fin n) → ℝ) p := by
    by_cases hp : p = (r₂, c₂)
    · subst hp
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hp]
  have h22_le : (Pi.single (r₂, c₂) (1 : ℝ) : (Fin n × Fin n) → ℝ) p ≤ 1 := by
    by_cases hp : p = (r₂, c₂)
    · subst hp
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hp]
  have h12_ge : -1 ≤ (Pi.single (r₁, c₂) (-1 : ℝ) : (Fin n × Fin n) → ℝ) p := by
    by_cases hp : p = (r₁, c₂)
    · subst hp
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hp]
  have h12_nonpos : (Pi.single (r₁, c₂) (-1 : ℝ) : (Fin n × Fin n) → ℝ) p ≤ 0 := by
    by_cases hp : p = (r₁, c₂)
    · subst hp
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hp]
  have h21_ge : -1 ≤ (Pi.single (r₂, c₁) (-1 : ℝ) : (Fin n × Fin n) → ℝ) p := by
    by_cases hp : p = (r₂, c₁)
    · subst hp
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hp]
  have h21_nonpos : (Pi.single (r₂, c₁) (-1 : ℝ) : (Fin n × Fin n) → ℝ) p ≤ 0 := by
    by_cases hp : p = (r₂, c₁)
    · subst hp
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hp]
  constructor
  · -- The lower bound comes from two nonnegative positive terms and two terms bounded below by `-1`.
    change -2 ≤
      (Pi.single (r₁, c₁) (1 : ℝ) : (Fin n × Fin n) → ℝ) p +
        (Pi.single (r₂, c₂) (1 : ℝ) : (Fin n × Fin n) → ℝ) p +
        (Pi.single (r₁, c₂) (-1 : ℝ) : (Fin n × Fin n) → ℝ) p +
        (Pi.single (r₂, c₁) (-1 : ℝ) : (Fin n × Fin n) → ℝ) p
    linarith [h11_nonneg, h22_nonneg, h12_ge, h21_ge]
  · -- The upper bound is symmetric.
    change
      (Pi.single (r₁, c₁) (1 : ℝ) : (Fin n × Fin n) → ℝ) p +
        (Pi.single (r₂, c₂) (1 : ℝ) : (Fin n × Fin n) → ℝ) p +
        (Pi.single (r₁, c₂) (-1 : ℝ) : (Fin n × Fin n) → ℝ) p +
        (Pi.single (r₂, c₁) (-1 : ℝ) : (Fin n × Fin n) → ℝ) p ≤ 2
    linarith [h11_le, h22_le, h12_nonpos, h21_nonpos]

/-- Helper for Exercise 3.21: every signed rectangle direction belongs to the tangent space of the
assignment polytope. -/
theorem assignment_rectangle_direction_mem_tangent_space
    {n : ℕ} (hn : 3 ≤ n) (r₁ r₂ c₁ c₂ : Fin n)
    (hr : r₁ ≠ r₂) (hc : c₁ ≠ c₂) :
    assignment_rectangle_direction n r₁ r₂ c₁ c₂ ∈ assignment_tangent_space n :=
by
  have hn_pos : 0 < n := by omega
  have hkernel :
      assignment_rectangle_direction n r₁ r₂ c₁ c₂ ∈
        LinearMap.ker (assignment_constraint_matrix n).mulVecLin := by
    rw [LinearMap.mem_ker]
    change Matrix.mulVec (assignment_constraint_matrix n)
      (assignment_rectangle_direction n r₁ r₂ c₁ c₂) = 0
    rw [assignment_constraint_matrix_mulVec_zero_iff]
    exact ⟨assignment_rectangle_direction_row_sum r₁ r₂ c₁ c₂ hr hc,
      assignment_rectangle_direction_col_sum r₁ r₂ c₁ c₂ hr hc⟩
  simpa [assignment_tangent_space_eq_constraint_kernel hn_pos] using hkernel

/-- Helper for Exercise 3.21: for `n ≥ 3`, every coordinate-zero face contains an explicit point,
so it is nonempty. -/
theorem assignment_coordinate_zero_face_nonempty_for_n_ge_three
    {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    (assignment_coordinate_zero_face n i j).Nonempty := by
  -- The source witness from the previous lemma already lies in the coordinate face.
  rcases assignment_coordinate_zero_face_explicit_point_mem hn i j with ⟨x0, hx0, -⟩
  exact ⟨x0, hx0⟩

/-- Helper for Exercise 3.21: for `n ≥ 3`, each coordinate-zero face is exposed by minimizing the
corresponding coordinate. -/
theorem assignment_coordinate_zero_face_isExposed_for_n_ge_three
    {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    IsExposed ℝ (assignment_polytope n) (assignment_coordinate_zero_face n i j) := by
  let l : StrongDual ℝ ((Fin n × Fin n) → ℝ) := -ContinuousLinearMap.proj (i, j)
  have hface :
      assignment_coordinate_zero_face n i j = l.toExposed (assignment_polytope n) := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro y hy
      rcases mem_assignment_polytope_iff.1 hy with ⟨-, -, hy_nonneg⟩
      -- Every feasible point has nonnegative `(i,j)`-coordinate, so `-proj (i,j)` is maximized at
      -- the zero face.
      have hx_le_y : x (i, j) ≤ y (i, j) := by
        rw [hx.2]
        exact hy_nonneg i j
      simpa [l] using hx_le_y
    · intro hx
      rcases assignment_coordinate_zero_face_explicit_point_mem hn i j with ⟨x0, hx0, -⟩
      rcases mem_assignment_polytope_iff.1 hx.1 with ⟨-, -, hx_nonneg⟩
      have hx_nonpos : x (i, j) ≤ 0 := by
        -- Comparing `x` with the explicit zero-face witness forces the maximizing coordinate to
        -- vanish.
        have hx0_le : l x0 ≤ l x := hx.2 x0 hx0.1
        have hx_compare : x (i, j) ≤ x0 (i, j) := by
          simpa [l] using hx0_le
        calc
          x (i, j) ≤ x0 (i, j) := hx_compare
          _ = 0 := hx0.2
      exact ⟨hx.1, le_antisymm hx_nonpos (hx_nonneg i j)⟩
  -- Rewriting as a canonical maximizer set turns exposedness into the standard fact.
  rw [hface]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Exercise 3.21: every point of the affine span of a coordinate-zero face still has
vanishing distinguished coordinate. -/
theorem affineSpan_assignment_coordinate_zero_face_subset_coordinate_hyperplane
    {n : ℕ} (i j : Fin n) :
    (affineSpan ℝ (assignment_coordinate_zero_face n i j) : Set ((Fin n × Fin n) → ℝ)) ⊆
      {x | x (i, j) = 0} := by
  intro x hx
  refine affineSpan_induction (k := ℝ) (s := assignment_coordinate_zero_face n i j)
    (p := fun y : (Fin n × Fin n) → ℝ ↦ y (i, j) = 0) hx ?_ ?_
  · intro y hy
    exact hy.2
  · intro c u v w hu hv hw
    -- The coordinate equation is affine, so it persists across affine combinations.
    simp [hu, hv, hw]

/-- Helper for Exercise 3.21: for `n ≥ 3`, the direction of a coordinate-zero face lies in the
assignment tangent space and in the kernel of the distinguished coordinate projection. -/
theorem assignment_coordinate_zero_face_direction_le_tangent_inf_ker
    {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    (affineSpan ℝ (assignment_coordinate_zero_face n i j)).direction ≤
      assignment_tangent_space n ⊓
        LinearMap.ker (ContinuousLinearMap.proj (i, j)).toLinearMap := by
  have hsubset :
      assignment_coordinate_zero_face n i j ⊆ assignment_polytope n := by
    intro x hx
    exact hx.1
  have h_aff_le :
      affineSpan ℝ (assignment_coordinate_zero_face n i j) ≤
        affineSpan ℝ (assignment_polytope n) := by
    exact affineSpan_mono ℝ hsubset
  intro v hv
  refine ⟨(AffineSubspace.direction_le h_aff_le) hv, ?_⟩
  rcases assignment_coordinate_zero_face_nonempty_for_n_ge_three hn i j with ⟨x0, hx0⟩
  have hx0_aff : x0 ∈ affineSpan ℝ (assignment_coordinate_zero_face n i j) :=
    subset_affineSpan ℝ _ hx0
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff] at hv
  rcases hv with ⟨x, hx_aff, rfl⟩
  -- Both endpoints of the difference already lie on the coordinate hyperplane.
  have hx_zero :
      x (i, j) = 0 :=
    affineSpan_assignment_coordinate_zero_face_subset_coordinate_hyperplane i j hx_aff
  have hx0_zero : x0 (i, j) = 0 := hx0.2
  change (x - x0) (i, j) = 0
  simp [hx_zero, hx0_zero]

/-- Helper for Exercise 3.21: every coordinate absolute value is bounded by the total absolute
sum over all coordinates. -/
theorem assignment_abs_le_sum_abs
    {n : ℕ} (v : (Fin n × Fin n) → ℝ) (p : Fin n × Fin n) :
    |v p| ≤ ∑ q : Fin n × Fin n, |v q| := by
  let rest : ℝ := Finset.sum (Finset.univ.erase p) fun q ↦ |v q|
  have hsplit : ∑ q : Fin n × Fin n, |v q| = |v p| + rest := by
    simp [rest, Finset.sum_erase_add, Finset.mem_univ]
  have hrest_nonneg : 0 ≤ rest := by
    exact Finset.sum_nonneg fun q hq ↦ abs_nonneg (v q)
  linarith

/-- Helper for Exercise 3.21: a feasible point stays in the assignment polytope after a small
perturbation along a zero-row-sum and zero-column-sum direction. -/
theorem assignment_small_perturbation_mem
    {n : ℕ} {x0 v : (Fin n × Fin n) → ℝ} {ε : ℝ}
    (hx0 : x0 ∈ assignment_polytope n) (hε : 0 ≤ ε)
    (hv_row : ∀ r : Fin n, ∑ c : Fin n, v (r, c) = 0)
    (hv_col : ∀ c : Fin n, ∑ r : Fin n, v (r, c) = 0)
    (hcoord : ∀ p : Fin n × Fin n, ε * |v p| ≤ x0 p) :
    x0 + ε • v ∈ assignment_polytope n := by
  rw [mem_assignment_polytope_iff] at hx0 ⊢
  rcases hx0 with ⟨hx0_row, hx0_col, -⟩
  refine ⟨?_, ?_, ?_⟩
  · intro r
    -- The perturbation preserves row sums because the direction has zero row sums.
    calc
      ∑ c : Fin n, (x0 + ε • v) (r, c)
          = ∑ c : Fin n, x0 (r, c) + ∑ c : Fin n, (ε • v) (r, c) := by
              simp [Finset.sum_add_distrib]
      _ = ∑ c : Fin n, x0 (r, c) + ε * ∑ c : Fin n, v (r, c) := by
            simp [Finset.mul_sum]
      _ = 1 := by
            rw [hx0_row r, hv_row r]
            ring
  · intro c
    -- The same cancellation preserves column sums.
    calc
      ∑ r : Fin n, (x0 + ε • v) (r, c)
          = ∑ r : Fin n, x0 (r, c) + ∑ r : Fin n, (ε • v) (r, c) := by
              simp [Finset.sum_add_distrib]
      _ = ∑ r : Fin n, x0 (r, c) + ε * ∑ r : Fin n, v (r, c) := by
            simp [Finset.mul_sum]
      _ = 1 := by
            rw [hx0_col c, hv_col c]
            ring
  · intro r c
    -- The coordinatewise bound dominates the possible negative part of the perturbation.
    have hcoord_rc := hcoord (r, c)
    have hneg :
        -(ε * |v (r, c)|) ≤ ε * v (r, c) := by
      nlinarith [hε, neg_abs_le (v (r, c))]
    have hsum_nonneg : 0 ≤ x0 (r, c) + ε * v (r, c) := by
      linarith
    simpa using hsum_nonneg

/-- Helper for Exercise 3.21: the canonical coordinate-face witness admits a small perturbation
inside the same coordinate face along every tangent vector with `v (i,j) = 0`. -/
theorem assignment_coordinate_zero_face_witness_has_face_perturbation
    {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) {v : (Fin n × Fin n) → ℝ}
    (hv_row : ∀ r : Fin n, ∑ c : Fin n, v (r, c) = 0)
    (hv_col : ∀ c : Fin n, ∑ r : Fin n, v (r, c) = 0)
    (hvij : v (i, j) = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      assignment_coordinate_zero_face_witness n i j + ε • v ∈
        assignment_coordinate_zero_face n i j := by
  let background : ℝ := (n - 2 : ℝ) / ((n - 1 : ℝ) ^ (2 : ℕ))
  let C : ℝ := ∑ q : Fin n × Fin n, |v q|
  let ε : ℝ := background / (C + 1)
  have hnm1_nat_pos : 0 < n - 1 := by
    omega
  have hnm2_nat_pos : 0 < n - 2 := by
    omega
  have hnm1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnm1_nat_pos
  have hnm2_pos : (0 : ℝ) < ((n - 2 : ℕ) : ℝ) := by
    exact_mod_cast hnm2_nat_pos
  have hbackground_pos : 0 < background := by
    dsimp [background]
    have hnm1_real_pos : 0 < (n : ℝ) - 1 := by
      simpa using hnm1_pos
    have hnm2_real_pos : 0 < (n : ℝ) - 2 := by
      simpa using hnm2_pos
    simpa using div_pos hnm2_real_pos (pow_pos hnm1_real_pos _)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun q hq ↦ abs_nonneg (v q)
  have hC_plus_pos : 0 < C + 1 := by
    linarith
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact div_pos hbackground_pos hC_plus_pos
  have hx0_face :
      assignment_coordinate_zero_face_witness n i j ∈ assignment_coordinate_zero_face n i j :=
    (assignment_coordinate_zero_face_witness_mem hn i j).1
  have hcoord :
      ∀ p : Fin n × Fin n, ε * |v p| ≤ assignment_coordinate_zero_face_witness n i j p := by
    intro p
    by_cases hp : p = (i, j)
    · subst p
      -- The distinguished coordinate stays fixed because both the witness and the direction vanish
      -- there.
      simp [ε, assignment_coordinate_zero_face_witness_apply_self, hvij]
    · have habs : |v p| ≤ C := by
        simpa [C] using assignment_abs_le_sum_abs v p
      have hmul1 : ε * |v p| ≤ ε * C := by
        exact mul_le_mul_of_nonneg_left habs (le_of_lt hε_pos)
      have hmul2 : ε * C ≤ ε * (C + 1) := by
        have hC_le : C ≤ C + 1 := by
          linarith
        exact mul_le_mul_of_nonneg_left hC_le (le_of_lt hε_pos)
      have hε_mul : ε * (C + 1) = background := by
        dsimp [ε]
        field_simp [hC_plus_pos.ne']
      calc
        ε * |v p| ≤ ε * C := hmul1
        _ ≤ ε * (C + 1) := hmul2
        _ = background := hε_mul
        _ ≤ assignment_coordinate_zero_face_witness n i j p := by
              simpa [background] using
                assignment_coordinate_zero_face_witness_lower_bound hn i j hp
  have hmem_poly :
      assignment_coordinate_zero_face_witness n i j + ε • v ∈ assignment_polytope n := by
    -- All nonnegativity checks have been isolated into the coordinatewise bound `hcoord`.
    exact assignment_small_perturbation_mem hx0_face.1 (le_of_lt hε_pos) hv_row hv_col hcoord
  refine ⟨ε, hε_pos, ?_⟩
  refine ⟨hmem_poly, ?_⟩
  -- The forced-zero coordinate remains zero because `v (i,j) = 0`.
  simp [assignment_coordinate_zero_face_witness_apply_self, hvij]

/-- Helper for Exercise 3.21: the kernel cut inside the assignment tangent space is contained in
the direction of the corresponding coordinate-zero face. -/
theorem assignment_tangent_inf_proj_ker_le_coordinate_face_direction
    {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    assignment_tangent_space n ⊓
        LinearMap.ker (ContinuousLinearMap.proj (i, j)).toLinearMap ≤
      (affineSpan ℝ (assignment_coordinate_zero_face n i j)).direction := by
  intro v hv
  rcases hv with ⟨hv_tangent, hv_proj⟩
  have hx0_face :
      assignment_coordinate_zero_face_witness n i j ∈ assignment_coordinate_zero_face n i j :=
    (assignment_coordinate_zero_face_witness_mem hn i j).1
  have hv_kernel :
      v ∈ LinearMap.ker (assignment_constraint_matrix n).mulVecLin := by
    -- Every tangent vector of the assignment polytope has zero row and column sums.
    exact
      direction_assignment_polytope_le_kernel n
        (assignment_coordinate_zero_face_witness n i j) hx0_face.1 hv_tangent
  have hv_rowcol :
      (∀ r : Fin n, ∑ c : Fin n, v (r, c) = 0) ∧
        (∀ c : Fin n, ∑ r : Fin n, v (r, c) = 0) := by
    have hv_kernel_eq : Matrix.mulVec (assignment_constraint_matrix n) v = 0 := by
      simpa [LinearMap.mem_ker] using hv_kernel
    exact (assignment_constraint_matrix_mulVec_zero_iff).1 hv_kernel_eq
  have hvij : v (i, j) = 0 := by
    -- The second kernel condition is exactly the vanishing distinguished coordinate.
    simpa [LinearMap.mem_ker] using hv_proj
  obtain ⟨ε, hε_pos, hpert_mem⟩ :=
    assignment_coordinate_zero_face_witness_has_face_perturbation hn i j
      hv_rowcol.1 hv_rowcol.2 hvij
  have hx0_aff :
      assignment_coordinate_zero_face_witness n i j ∈
        affineSpan ℝ (assignment_coordinate_zero_face n i j) :=
    subset_affineSpan ℝ _ hx0_face
  have hpert_aff :
      assignment_coordinate_zero_face_witness n i j + ε • v ∈
        affineSpan ℝ (assignment_coordinate_zero_face n i j) :=
    subset_affineSpan ℝ _ hpert_mem
  have hscaled :
      ε • v ∈ (affineSpan ℝ (assignment_coordinate_zero_face n i j)).direction := by
    -- The perturbation point and the witness differ by the scaled direction `ε • v`.
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff]
    refine ⟨assignment_coordinate_zero_face_witness n i j + ε • v, hpert_aff, ?_⟩
    ext p
    simp [vsub_eq_sub]
  have hrescaled :
      ε⁻¹ • (ε • v) ∈ (affineSpan ℝ (assignment_coordinate_zero_face n i j)).direction := by
    exact Submodule.smul_mem _ _ hscaled
  -- Rescaling by `ε⁻¹` recovers the original tangent vector.
  simpa [smul_smul, hε_pos.ne', inv_mul_cancel] using hrescaled

/-- Helper for Exercise 3.21: for `n ≥ 3`, the direction of a coordinate-zero face is exactly the
assignment tangent space cut by the vanishing coordinate projection. -/
theorem assignment_coordinate_zero_face_direction_eq_tangent_inf_ker
    {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    (affineSpan ℝ (assignment_coordinate_zero_face n i j)).direction =
      assignment_tangent_space n ⊓
        LinearMap.ker (ContinuousLinearMap.proj (i, j)).toLinearMap := by
  -- The source route identifies a coordinate face by one tangent-space kernel cut.
  refine le_antisymm
    (assignment_coordinate_zero_face_direction_le_tangent_inf_ker hn i j)
    (assignment_tangent_inf_proj_ker_le_coordinate_face_direction hn i j)

/-- Helper for Exercise 3.21: if a linear functional takes the value `1` on some vector of a
submodule `D`, then the kernel cut `D ⊓ ker L` has codimension one inside `D`. -/
theorem submodule_finrank_inf_ker_add_one_of_eval_one
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
    -- The subtype embedding identifies the restricted kernel with the ambient kernel cut.
    rw [← hmap]
    simpa using
      (Submodule.finrank_map_subtype_eq (R := ℝ) (p := D)
        (q := LinearMap.ker (L.domRestrict D)))
  calc
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1
        = Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) + 1 := by
            rw [hfin]
    _ = Module.finrank ℝ ↥D := hdim

/-- Helper for Exercise 3.21: in `Fin n` with `n ≥ 2`, every index has a distinct companion. -/
theorem assignment_exists_distinct_index
    {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    ∃ k : Fin n, k ≠ i := by
  let k0 : Fin n := ⟨0, by omega⟩
  let k1 : Fin n := ⟨1, by omega⟩
  by_cases hi : i = k0
  · refine ⟨k1, ?_⟩
    intro hk
    have : (1 : ℕ) = 0 := by
      simpa [k0, k1] using congrArg Fin.val (hk.trans hi)
    omega
  · refine ⟨k0, ?_⟩
    intro hk
    exact hi hk.symm

/-- Helper for Exercise 3.21: for `n ≥ 3`, each coordinate-zero face of the assignment polytope
is a facet. -/
theorem assignment_coordinate_zero_face_isFacetOf_for_n_ge_three
    {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    IsFacetOf (assignment_polytope n) (assignment_coordinate_zero_face n i j) := by
  refine ⟨assignment_coordinate_zero_face_nonempty_for_n_ge_three hn i j,
    assignment_coordinate_zero_face_isExposed_for_n_ge_three hn i j, ?_⟩
  have htwo : 2 ≤ n := by
    omega
  obtain ⟨r, hr⟩ := assignment_exists_distinct_index htwo i
  obtain ⟨c, hc⟩ := assignment_exists_distinct_index htwo j
  let w : (Fin n × Fin n) → ℝ := assignment_rectangle_direction n i r j c
  have hw_mem : w ∈ assignment_tangent_space n := by
    -- A `2 × 2` rectangle move always stays inside the tangent space.
    simpa [w] using
      assignment_rectangle_direction_mem_tangent_space hn i r j c hr.symm hc.symm
  have hw_eval : w (i, j) = 1 := by
    -- The chosen rectangle move has value `1` at the distinguished coordinate.
    change assignment_rectangle_direction n i r j c (i, j) = 1
    simp [assignment_rectangle_direction, hr, hc]
  have hcodim :
      Module.finrank ℝ
          ↥(assignment_tangent_space n ⊓
            LinearMap.ker (ContinuousLinearMap.proj (i, j)).toLinearMap) + 1 =
        Module.finrank ℝ ↥(assignment_tangent_space n) := by
    exact submodule_finrank_inf_ker_add_one_of_eval_one
      (D := assignment_tangent_space n)
      (L := (ContinuousLinearMap.proj (i, j)).toLinearMap) hw_mem (by simpa using hw_eval)
  have hdir_eq := assignment_coordinate_zero_face_direction_eq_tangent_inf_ker hn i j
  -- The direction computation turns the kernel-cut codimension statement into the facet one.
  have hcodim' :
      Module.finrank ℝ ↥((affineSpan ℝ (assignment_coordinate_zero_face n i j)).direction) + 1 =
        Module.finrank ℝ ↥(assignment_tangent_space n) := by
    rw [hdir_eq]
    exact hcodim
  simpa [assignment_tangent_space] using hcodim'

/-- Helper for Exercise 3.21: a strictly positive feasible point admits symmetric feasible
perturbations along every direction with zero row and column sums. -/
theorem assignment_strictly_positive_point_has_signed_perturbation
    {n : ℕ} (hn : 0 < n) {x0 v : (Fin n × Fin n) → ℝ}
    (hx0 : x0 ∈ assignment_polytope n)
    (hx0_pos : ∀ p : Fin n × Fin n, 0 < x0 p)
    (hv_row : ∀ r : Fin n, ∑ c : Fin n, v (r, c) = 0)
    (hv_col : ∀ c : Fin n, ∑ r : Fin n, v (r, c) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ x0 + ε • v ∈ assignment_polytope n ∧ x0 - ε • v ∈ assignment_polytope n :=
by
  let p0 : Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩)
  have huniv_nonempty : (Finset.univ : Finset (Fin n × Fin n)).Nonempty := ⟨p0, by simp⟩
  let m : ℝ := Finset.inf' Finset.univ huniv_nonempty x0
  let C : ℝ := ∑ q : Fin n × Fin n, |v q|
  let ε : ℝ := m / (C + 1)
  have hm_pos : 0 < m := by
    -- The minimum of finitely many positive coordinates is still positive.
    dsimp [m]
    exact (Finset.lt_inf'_iff (s := Finset.univ) (H := huniv_nonempty) (f := x0) (a := 0)).2
      fun p hp ↦ hx0_pos p
  have hm_le : ∀ p : Fin n × Fin n, m ≤ x0 p := by
    intro p
    dsimp [m]
    exact Finset.inf'_le _ (by simp)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun q hq ↦ abs_nonneg (v q)
  have hC_plus_pos : 0 < C + 1 := by
    linarith
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact div_pos hm_pos hC_plus_pos
  have hcoord : ∀ p : Fin n × Fin n, ε * |v p| ≤ x0 p := by
    intro p
    have habs : |v p| ≤ C := by
      simpa [C] using assignment_abs_le_sum_abs v p
    have hmul1 : ε * |v p| ≤ ε * C := by
      exact mul_le_mul_of_nonneg_left habs (le_of_lt hε_pos)
    have hmul2 : ε * C ≤ ε * (C + 1) := by
      have hC_le : C ≤ C + 1 := by linarith
      exact mul_le_mul_of_nonneg_left hC_le (le_of_lt hε_pos)
    have hε_mul : ε * (C + 1) = m := by
      dsimp [ε]
      field_simp [hC_plus_pos.ne']
    calc
      ε * |v p| ≤ ε * C := hmul1
      _ ≤ ε * (C + 1) := hmul2
      _ = m := hε_mul
      _ ≤ x0 p := hm_le p
  have hplus_mem : x0 + ε • v ∈ assignment_polytope n := by
    -- The coordinatewise lower bound makes the positive perturbation feasible.
    exact assignment_small_perturbation_mem hx0 (le_of_lt hε_pos) hv_row hv_col hcoord
  have hneg_row : ∀ r : Fin n, ∑ c : Fin n, (-v) (r, c) = 0 := by
    intro r
    have hrow := congrArg Neg.neg (hv_row r)
    simpa [Finset.sum_neg_distrib] using hrow
  have hneg_col : ∀ c : Fin n, ∑ r : Fin n, (-v) (r, c) = 0 := by
    intro c
    have hcol := congrArg Neg.neg (hv_col c)
    simpa [Finset.sum_neg_distrib] using hcol
  have hminus_mem : x0 + ε • (-v) ∈ assignment_polytope n := by
    -- The negative perturbation is the same argument applied to `-v`.
    exact assignment_small_perturbation_mem hx0 (le_of_lt hε_pos) hneg_row hneg_col <| by
      intro p
      simpa using hcoord p
  refine ⟨ε, hε_pos, hplus_mem, ?_⟩
  simpa [sub_eq_add_neg] using hminus_mem

/-- Helper for Exercise 3.21: an exposed face of the assignment polytope that contains a strictly
positive point must equal the whole polytope. -/
theorem assignment_exposed_face_eq_polytope_of_strictly_positive_point
    {n : ℕ} (hn : 0 < n) {F : Set ((Fin n × Fin n) → ℝ)} {x0 : (Fin n × Fin n) → ℝ}
    (hF_exposed : IsExposed ℝ (assignment_polytope n) F)
    (hF_nonempty : F.Nonempty) (hx0F : x0 ∈ F)
    (hx0_pos : ∀ p : Fin n × Fin n, 0 < x0 p) :
    F = assignment_polytope n := by
  obtain ⟨l, hF_eq⟩ := hF_exposed hF_nonempty
  have hx0_face : x0 ∈ l.toExposed (assignment_polytope n) := by
    simpa [hF_eq] using hx0F
  have hx0_mem : x0 ∈ assignment_polytope n := hx0_face.1
  have hx0_max : ∀ y, y ∈ assignment_polytope n → l y ≤ l x0 := hx0_face.2
  -- Every feasible point differs from `x0` by a zero row-sum and zero column-sum direction.
  ext x
  constructor
  · intro hx
    exact hF_exposed.subset hx
  · intro hx
    let v : (Fin n × Fin n) → ℝ := x - x0
    rcases mem_assignment_polytope_iff.1 hx with ⟨hx_row, hx_col, -⟩
    rcases mem_assignment_polytope_iff.1 hx0_mem with ⟨hx0_row, hx0_col, -⟩
    have hv_row : ∀ r : Fin n, ∑ c : Fin n, v (r, c) = 0 := by
      intro r
      calc
        ∑ c : Fin n, v (r, c) = ∑ c : Fin n, x (r, c) - ∑ c : Fin n, x0 (r, c) := by
            simp [v, Finset.sum_sub_distrib]
        _ = 0 := by
            rw [hx_row r, hx0_row r]
            ring
    have hv_col : ∀ c : Fin n, ∑ r : Fin n, v (r, c) = 0 := by
      intro c
      calc
        ∑ r : Fin n, v (r, c) = ∑ r : Fin n, x (r, c) - ∑ r : Fin n, x0 (r, c) := by
            simp [v, Finset.sum_sub_distrib]
        _ = 0 := by
            rw [hx_col c, hx0_col c]
            ring
    obtain ⟨ε, hε_pos, hplus_mem, hminus_mem⟩ :=
      assignment_strictly_positive_point_has_signed_perturbation hn hx0_mem hx0_pos hv_row hv_col
    have hplus_le : l (x0 + ε • v) ≤ l x0 := hx0_max _ hplus_mem
    have hminus_le : l (x0 - ε • v) ≤ l x0 := hx0_max _ hminus_mem
    have hv_eval_zero : l v = 0 := by
      have hplus' : l x0 + ε * l v ≤ l x0 := by
        simpa [map_add, map_smul] using hplus_le
      have hminus' : l x0 - ε * l v ≤ l x0 := by
        simpa [sub_eq_add_neg, map_add, map_smul] using hminus_le
      have hplus'' : ε * l v ≤ 0 := by
        linarith
      have hminus'' : 0 ≤ ε * l v := by
        linarith
      have hεlv : ε * l v = 0 := le_antisymm hplus'' hminus''
      exact (mul_eq_zero.mp hεlv).resolve_left hε_pos.ne'
    have hx_eval : l x = l x0 := by
      calc
        l x = l (x0 + v) := by
          congr 1
          ext p
          simp [v]
        _ = l x0 + l v := by simp [map_add]
        _ = l x0 := by simp [hv_eval_zero]
    have hx_face : x ∈ l.toExposed (assignment_polytope n) := by
      refine ⟨hx, ?_⟩
      intro y hy
      calc
        l y ≤ l x0 := hx0_max y hy
        _ = l x := hx_eval.symm
    simpa [hF_eq] using hx_face

/-- Helper for Exercise 3.21: every facet of the assignment polytope with `n ≥ 3` forces one
coordinate to vanish on the whole facet. -/
theorem assignment_facet_exists_common_zero_coordinate
    {n : ℕ} (hn : 3 ≤ n) {F : Set ((Fin n × Fin n) → ℝ)}
    (hF : IsFacetOf (assignment_polytope n) F) :
    ∃ i j : Fin n, F ⊆ assignment_coordinate_zero_face n i j := by
  classical
  rcases hF with ⟨hF_nonempty, hF_exposed, hF_codim⟩
  obtain ⟨xF, hxF⟩ := hF_nonempty
  obtain ⟨l, hF_eq⟩ := hF_exposed ⟨xF, hxF⟩
  have hxF_face : xF ∈ l.toExposed (assignment_polytope n) := by
    simpa [hF_eq] using hxF
  have hxF_mem : xF ∈ assignment_polytope n := hxF_face.1
  have hxF_max : ∀ y, y ∈ assignment_polytope n → l y ≤ l xF := hxF_face.2
  have hn_pos : 0 < n := by
    omega
  by_contra hnone
  push Not at hnone
  have hwitness :
      ∀ p : Fin n × Fin n, ∃ x : (Fin n × Fin n) → ℝ, x ∈ F ∧ 0 < x p := by
    intro p
    rcases not_subset.mp (hnone p.1 p.2) with ⟨x, hx, hxnot⟩
    have hx_mem : x ∈ assignment_polytope n := hF_exposed.subset hx
    rcases mem_assignment_polytope_iff.1 hx_mem with ⟨-, -, hnonneg⟩
    have hx_ne_zero : x p ≠ 0 := by
      intro hx_zero
      apply hxnot
      exact ⟨hx_mem, hx_zero⟩
    exact ⟨x, hx, lt_of_le_of_ne (hnonneg p.1 p.2) (Ne.symm hx_ne_zero)⟩
  choose x hx_mem_F hxpos using hwitness
  let N : ℝ := Fintype.card (Fin n × Fin n)
  let xsum : (Fin n × Fin n) → ℝ := ∑ p : Fin n × Fin n, x p
  let xbar : (Fin n × Fin n) → ℝ := (1 / N) • xsum
  have hN_nat_pos : 0 < Fintype.card (Fin n × Fin n) := by
    exact Fintype.card_pos_iff.mpr ⟨(⟨0, hn_pos⟩, ⟨0, hn_pos⟩)⟩
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast hN_nat_pos
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hx_mem_poly : ∀ p : Fin n × Fin n, x p ∈ assignment_polytope n := by
    intro p
    exact hF_exposed.subset (hx_mem_F p)
  have hx_nonneg : ∀ p q : Fin n × Fin n, 0 ≤ x p q := by
    intro p q
    rcases mem_assignment_polytope_iff.1 (hx_mem_poly p) with ⟨-, -, hnonneg⟩
    exact hnonneg q.1 q.2
  have hxbar_mem : xbar ∈ assignment_polytope n := by
    rw [mem_assignment_polytope_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro r
      have hrow_each : ∀ p : Fin n × Fin n, ∑ c : Fin n, x p (r, c) = 1 := by
        intro p
        exact (mem_assignment_polytope_iff.1 (hx_mem_poly p)).1 r
      -- Averaging feasible points preserves the row equations.
      calc
        ∑ c : Fin n, xbar (r, c) = ∑ c : Fin n, (1 / N) * xsum (r, c) := by
            simp [xbar]
        _ = (1 / N) * ∑ c : Fin n, xsum (r, c) := by
            rw [Finset.mul_sum]
        _ = (1 / N) * ∑ c : Fin n, ∑ p : Fin n × Fin n, x p (r, c) := by
            congr 1
            simp [xsum]
        _ = (1 / N) * ∑ p : Fin n × Fin n, ∑ c : Fin n, x p (r, c) := by
            rw [Finset.sum_comm]
        _ = (1 / N) * ∑ p : Fin n × Fin n, (1 : ℝ) := by
            refine congrArg (fun t : ℝ ↦ (1 / N) * t) ?_
            refine Finset.sum_congr rfl ?_
            intro p hp
            exact hrow_each p
        _ = 1 := by
            calc
              (1 / N) * ∑ p : Fin n × Fin n, (1 : ℝ) = (1 / N) * N := by
                simp [N]
              _ = 1 := by
                field_simp [hN_ne]
    · intro c
      have hcol_each : ∀ p : Fin n × Fin n, ∑ r : Fin n, x p (r, c) = 1 := by
        intro p
        exact (mem_assignment_polytope_iff.1 (hx_mem_poly p)).2.1 c
      -- The same averaging argument preserves the column equations.
      calc
        ∑ r : Fin n, xbar (r, c) = ∑ r : Fin n, (1 / N) * xsum (r, c) := by
            simp [xbar]
        _ = (1 / N) * ∑ r : Fin n, xsum (r, c) := by
            rw [Finset.mul_sum]
        _ = (1 / N) * ∑ r : Fin n, ∑ p : Fin n × Fin n, x p (r, c) := by
            congr 1
            simp [xsum]
        _ = (1 / N) * ∑ p : Fin n × Fin n, ∑ r : Fin n, x p (r, c) := by
            rw [Finset.sum_comm]
        _ = (1 / N) * ∑ p : Fin n × Fin n, (1 : ℝ) := by
            refine congrArg (fun t : ℝ ↦ (1 / N) * t) ?_
            refine Finset.sum_congr rfl ?_
            intro p hp
            exact hcol_each p
        _ = 1 := by
            calc
              (1 / N) * ∑ p : Fin n × Fin n, (1 : ℝ) = (1 / N) * N := by
                simp [N]
              _ = 1 := by
                field_simp [hN_ne]
    · intro r c
      have hsum_nonneg : 0 ≤ xsum (r, c) := by
        simpa [xsum] using (Finset.sum_nonneg fun p hp ↦ hx_nonneg p (r, c))
      -- Coordinatewise nonnegativity is preserved by the positive average.
      simpa [xbar] using mul_nonneg (le_of_lt (one_div_pos.mpr hN_pos)) hsum_nonneg
  have hx_level : ∀ p : Fin n × Fin n, l (x p) = l xF := by
    intro p
    have hp_face : x p ∈ l.toExposed (assignment_polytope n) := by
      simpa [hF_eq] using hx_mem_F p
    exact le_antisymm (hxF_max _ hp_face.1) (hp_face.2 xF hxF_mem)
  have hxbar_level : l xbar = l xF := by
    -- All witness points maximize the same exposing functional value, so their average does too.
    calc
      l xbar = (1 / N) * l xsum := by
        simp [xbar]
      _ = (1 / N) * ∑ p : Fin n × Fin n, l (x p) := by
            simp [xsum, map_sum]
      _ = (1 / N) * ∑ p : Fin n × Fin n, l xF := by
            refine congrArg (fun t : ℝ ↦ (1 / N) * t) ?_
            refine Finset.sum_congr rfl ?_
            intro p hp
            exact hx_level p
      _ = l xF := by
            calc
              (1 / N) * ∑ p : Fin n × Fin n, l xF = (1 / N) * (N * l xF) := by
                simp [N, Finset.mul_sum]
              _ = l xF := by
                field_simp [hN_ne]
  have hxbar_pos : ∀ q : Fin n × Fin n, 0 < xbar q := by
    intro q
    have hsingle_le : x q q ≤ xsum q := by
      simpa [xsum] using
        (Finset.single_le_sum (fun p hp ↦ hx_nonneg p q) (Finset.mem_univ q) :
          x q q ≤ ∑ p : Fin n × Fin n, x p q)
    have hsum_pos : 0 < xsum q := by
      exact lt_of_lt_of_le (hxpos q) hsingle_le
    -- The `q`th witness contributes strictly positively to the `q`th average coordinate.
    simpa [xbar] using mul_pos (one_div_pos.mpr hN_pos) hsum_pos
  have hxbar_face : xbar ∈ F := by
    have hxbar_exposed : xbar ∈ l.toExposed (assignment_polytope n) := by
      refine ⟨hxbar_mem, ?_⟩
      intro y hy
      calc
        l y ≤ l xF := hxF_max y hy
        _ = l xbar := hxbar_level.symm
    simpa [hF_eq] using hxbar_exposed
  have hwhole :
      F = assignment_polytope n :=
    assignment_exposed_face_eq_polytope_of_strictly_positive_point hn_pos hF_exposed ⟨xF, hxF⟩
      hxbar_face hxbar_pos
  rw [hwhole] at hF_codim
  omega

/-- Helper for Exercise 3.21: a facet contained in a coordinate-zero face must coincide with that
coordinate face. -/
theorem assignment_facet_eq_coordinate_face_of_subset
    {n : ℕ} (hn : 3 ≤ n) {F : Set ((Fin n × Fin n) → ℝ)}
    (hF : IsFacetOf (assignment_polytope n) F) {i j : Fin n}
    (hsubset : F ⊆ assignment_coordinate_zero_face n i j) :
    F = assignment_coordinate_zero_face n i j := by
  rcases hF with ⟨hF_nonempty, hF_exposed, hF_codim⟩
  have hG :
      IsFacetOf (assignment_polytope n) (assignment_coordinate_zero_face n i j) :=
    assignment_coordinate_zero_face_isFacetOf_for_n_ge_three hn i j
  rcases hG with ⟨hG_nonempty, hG_exposed, hG_codim⟩
  obtain ⟨xF, hxF⟩ := hF_nonempty
  have hxFG : xF ∈ assignment_coordinate_zero_face n i j := hsubset hxF
  have hPdim :
      Module.finrank ℝ (affineSpan ℝ (assignment_polytope n)).direction =
        n * n - (2 * n - 1) := by
    simpa using assignment_polytope_finrank_direction_affineSpan n
  have hdim_eq :
      Module.finrank ℝ ↥((affineSpan ℝ F).direction) =
        Module.finrank ℝ ↥((affineSpan ℝ (assignment_coordinate_zero_face n i j)).direction) := by
    omega
  have h_aff_le :
      affineSpan ℝ F ≤ affineSpan ℝ (assignment_coordinate_zero_face n i j) := by
    exact affineSpan_mono ℝ hsubset
  have hdir_eq :
      (affineSpan ℝ F).direction =
        (affineSpan ℝ (assignment_coordinate_zero_face n i j)).direction := by
    exact Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le h_aff_le) hdim_eq
  have hspan_eq :
      affineSpan ℝ F = affineSpan ℝ (assignment_coordinate_zero_face n i j) := by
    -- Equal directions and a common point identify the two affine spans.
    refine (AffineSubspace.eq_iff_direction_eq_of_mem
      (subset_affineSpan ℝ _ hxF) (subset_affineSpan ℝ _ hxFG)).2 hdir_eq
  obtain ⟨l, hF_eq⟩ := hF_exposed ⟨xF, hxF⟩
  have hxF_face : xF ∈ l.toExposed (assignment_polytope n) := by
    simpa [hF_eq] using hxF
  have hxF_mem : xF ∈ assignment_polytope n := hxF_face.1
  have hxF_max : ∀ y, y ∈ assignment_polytope n → l y ≤ l xF := hxF_face.2
  have hlevel : ∀ ⦃x : (Fin n × Fin n) → ℝ⦄, x ∈ F → l x = l xF := by
    intro x hx
    have hx_face : x ∈ l.toExposed (assignment_polytope n) := by
      simpa [hF_eq] using hx
    exact le_antisymm (hxF_max x hx_face.1) (hx_face.2 xF hxF_mem)
  have hlevel_aff :
      ∀ ⦃x : (Fin n × Fin n) → ℝ⦄, x ∈ affineSpan ℝ F → l x = l xF := by
    intro x hx
    refine affineSpan_induction (k := ℝ) (s := F) (p := fun y : (Fin n × Fin n) → ℝ ↦
      l y = l xF) hx ?_ ?_
    · intro y hy
      exact hlevel hy
    · intro c u v w hu hv hw
      -- The exposing functional stays constant on the whole affine span of `F`.
      change l (c • (u - v) + w) = l xF
      calc
        l (c • (u - v) + w) = c * (l u - l v) + l w := by
            simp [map_add, map_sub]
        _ = l xF := by
            simp [hu, hv, hw]
  ext x
  constructor
  · intro hx
    exact hsubset hx
  · intro hx
    have hx_aff_face : x ∈ affineSpan ℝ F := by
      simpa [hspan_eq] using subset_affineSpan ℝ _ hx
    have hx_level : l x = l xF := hlevel_aff hx_aff_face
    have hx_exposed : x ∈ l.toExposed (assignment_polytope n) := by
      refine ⟨hx.1, ?_⟩
      intro y hy
      calc
        l y ≤ l xF := hxF_max y hy
        _ = l x := hx_level.symm
    simpa [hF_eq] using hx_exposed

/-- Exercise 3.21 (3): when `n ≥ 3`, the facets of the assignment polytope are exactly the
coordinate faces cut out by the inequalities `x i j ≥ 0`. -/
theorem exercise_3_21_assignment_polytope_facets_for_n_ge_three
    {n : ℕ} (hn : 3 ≤ n) (F : Set ((Fin n × Fin n) → ℝ)) :
    IsFacetOf (assignment_polytope n) F ↔
      ∃ i j : Fin n, F = assignment_coordinate_zero_face n i j := by
  constructor
  · intro hF
    -- Route correction: classify the forward branch by exposed-face rigidity plus a common-zero
    -- coordinate, instead of continuing the tangent-space argument inline.
    obtain ⟨i, j, hsubset⟩ := assignment_facet_exists_common_zero_coordinate hn hF
    exact ⟨i, j, assignment_facet_eq_coordinate_face_of_subset hn hF hsubset⟩
  · rintro ⟨i, j, rfl⟩
    -- The reverse implication is the coordinate-face facet theorem proved above.
    exact assignment_coordinate_zero_face_isFacetOf_for_n_ge_three hn i j
