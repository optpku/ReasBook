/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4.ch5_sec5_4_definition_5_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_stable_set_relaxations
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_3_theorem_10_10

open scoped BigOperators
open scoped LovaszSchrijverNotation

-- This exercise reuses the Section 10.3 owner API for the Lovasz-Schrijver `N` and `N₊`
-- operators, the Chapter 7 graph-relaxation owners `Q` and `K`, and the Chapter 5
-- lift-and-project closure owner.

section Exercise1011

local notation "K₅" => SimpleGraph.completeGraph (Fin 5)

/-- The one-round triangle-clique relaxation `x ≥ 0`, `x_i + x_j + x_k ≤ 1` for all pairwise
distinct `i`, `j`, `k`. -/
def exercise_10_11_triple_clique_relaxation : Set (Fin 5 → ℝ) :=
  {x : Fin 5 → ℝ |
    (∀ i : Fin 5, 0 ≤ x i) ∧
      ∀ ⦃i j k : Fin 5⦄,
        i ≠ j → i ≠ k → j ≠ k → x i + x j + x k ≤ 1}

/-- Membership in `exercise_10_11_triple_clique_relaxation` is exactly nonnegativity together
with the triangle-clique inequalities `x_i + x_j + x_k ≤ 1`. -/
theorem mem_exercise_10_11_triple_clique_relaxation_iff
    (x : Fin 5 → ℝ) :
    x ∈ exercise_10_11_triple_clique_relaxation ↔
      (∀ i : Fin 5, 0 ≤ x i) ∧
        ∀ ⦃i j k : Fin 5⦄,
          i ≠ j → i ≠ k → j ≠ k → x i + x j + x k ≤ 1 :=
  Iff.rfl

/-- Helper for Exercise 10.11: the complete-graph edge relaxation is the pairwise-inequality
system `x_i + x_j ≤ 1` for all distinct `i, j`. -/
lemma mem_completeGraphEdgeRelaxation_iff
    (x : Fin 5 → ℝ) :
    x ∈ Q(K₅) ↔
      (∀ i : Fin 5, 0 ≤ x i) ∧
        ∀ ⦃i j : Fin 5⦄, i ≠ j → x i + x j ≤ 1 := by
  rw [mem_edge_relaxation_iff]
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro i j hij
    -- On the complete graph, every distinct pair is an edge.
    exact hx.2 (by simpa [SimpleGraph.top_adj] using hij)
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro i j hij
    -- Route correction: rewrite complete-graph adjacency to inequality before applying the
    -- normalized pairwise bound.
    have hne : i ≠ j := by
      simpa [SimpleGraph.top_adj] using hij
    exact hx.2 hne

/-- Helper for Exercise 10.11: `Q(K₅)` matches the Chapter 5 pairwise-inequality polyhedron
`exercise_5_19_polyhedron 5`. -/
lemma mem_completeGraphEdgeRelaxation_eq_exercise_5_19_polyhedron_iff
    (x : Fin 5 → ℝ) :
    x ∈ Q(K₅) ↔ x ∈ exercise_5_19_polyhedron 5 := by
  rw [mem_completeGraphEdgeRelaxation_iff, mem_exercise_5_19_polyhedron_iff]
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro i j hij
    -- The Chapter 5 owner only asks for the `i < j` half of the symmetric pairwise system.
    exact hx.2 hij.ne
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij_lt | hij_gt
    · exact hx.2 hij_lt
    · simpa [add_comm] using hx.2 hij_gt

/-- Helper for Exercise 10.11: `Q(K₅)` is convex because its defining inequalities are linear. -/
lemma convex_completeGraphEdgeRelaxation :
    Convex ℝ (Q(K₅)) := by
  intro x hx y hy a b ha hb hab
  rw [mem_completeGraphEdgeRelaxation_iff] at hx hy ⊢
  refine ⟨?_, ?_⟩
  · intro i
    -- Nonnegativity is preserved by nonnegative convex weights.
    have hx' := hx.1 i
    have hy' := hy.1 i
    simpa [Pi.smul_apply, Pi.add_apply] using
      add_nonneg (mul_nonneg ha hx') (mul_nonneg hb hy')
  · intro i j hij
    -- The pairwise bounds are preserved termwise under convex combinations.
    have hsum :
        (a • x + b • y) i + (a • x + b • y) j =
          a * (x i + x j) + b * (y i + y j) := by
      calc
        (a • x + b • y) i + (a • x + b • y) j
            = (a * x i + b * y i) + (a * x j + b * y j) := by
                simp [Pi.smul_apply, Pi.add_apply]
        _ = a * (x i + x j) + b * (y i + y j) := by
              ring
    rw [hsum]
    nlinarith [hx.2 hij, hy.2 hij, ha, hb, hab]

/-- Helper for Exercise 10.11: a fixed coordinate always has a distinct comparison vertex in
`Fin 5`. -/
private def alternateVertex (i : Fin 5) : Fin 5 :=
  if i = 0 then 1 else 0

/-- Helper for Exercise 10.11: `alternateVertex i` is different from `i`. -/
private lemma alternateVertex_ne (i : Fin 5) :
    alternateVertex i ≠ i := by
  by_cases hi : i = 0
  · subst hi
    simp [alternateVertex]
  · simp [alternateVertex, hi, eq_comm]

/-- Helper for Exercise 10.11: any distinct pair of vertices in `Fin 5` admits a third vertex
different from both. -/
private lemma exists_third_vertex
    (i j : Fin 5)
    (_hij : i ≠ j) :
    ∃ k : Fin 5, k ≠ i ∧ k ≠ j := by
  simpa using Fin.exists_ne_and_ne_of_two_lt i j (by decide : 2 < 5)

/-- Helper for Exercise 10.11: every point of `Q(K₅)` already lies in the unit box `[0,1]^5`. -/
lemma completeGraphEdgeRelaxation_subset_prefixUnitBox :
    Q(K₅) ⊆ prefix_unit_box (Nat.le_refl 5) := by
  intro x hx
  rw [mem_prefix_unit_box_iff]
  rw [mem_completeGraphEdgeRelaxation_iff] at hx
  intro i
  refine ⟨hx.1 i, ?_⟩
  -- Compare `x i` with a distinct coordinate to upgrade nonnegativity to the upper bound `x i ≤ 1`.
  have hpair : x i + x (alternateVertex i) ≤ 1 := by
    exact hx.2 (alternateVertex_ne i).symm
  have halt_nonneg : 0 ≤ x (alternateVertex i) := hx.1 (alternateVertex i)
  have hi_le : x i ≤ 1 := by
    linarith
  simpa using hi_le

/-- Helper for Exercise 10.11: on the complete graph, the full clique system collapses to the
single simplex inequality `∑ i, x i ≤ 1`. -/
lemma mem_cliqueRelaxation_completeGraph_iff
    (x : Fin 5 → ℝ) :
    x ∈ K(K₅) ↔ (∀ i : Fin 5, 0 ≤ x i) ∧ ∑ i : Fin 5, x i ≤ 1 := by
  rw [mem_clique_relaxation_iff]
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hunivClique :
        (SimpleGraph.completeGraph (Fin 5)).IsClique (Finset.univ : Finset (Fin 5)) := by
      rw [SimpleGraph.isClique_iff]
      intro i hi j hj hij
      simpa [SimpleGraph.top_adj] using hij
    -- The maximal clique `Finset.univ` already yields the full simplex inequality.
    simpa using hx.2 Finset.univ hunivClique
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro K hK
    -- Every smaller clique sum is bounded by the full nonnegative sum.
    exact (Finset.sum_le_univ_sum_of_nonneg fun i ↦ hx.1 i).trans hx.2

/-- Helper for Exercise 10.11: the complete-graph clique relaxation is convex after
normalization to the simplex inequality. -/
lemma convex_cliqueRelaxation_completeGraph :
    Convex ℝ (K(K₅)) := by
  intro x hx y hy a b ha hb hab
  rw [mem_cliqueRelaxation_completeGraph_iff] at hx hy ⊢
  refine ⟨?_, ?_⟩
  · intro i
    -- Coordinatewise nonnegativity is preserved by the convex weights.
    have hx' := hx.1 i
    have hy' := hy.1 i
    simpa [Pi.smul_apply, Pi.add_apply] using
      add_nonneg (mul_nonneg ha hx') (mul_nonneg hb hy')
  · -- The full-sum inequality is linear in the point coordinates.
    have hsum :
        ∑ i : Fin 5, (a • x + b • y) i = a * ∑ i : Fin 5, x i + b * ∑ i : Fin 5, y i := by
      simp [Pi.smul_apply, Pi.add_apply, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsum]
    nlinarith [hx.2, hy.2, ha, hb, hab]

/-- Helper for Exercise 10.11: the coordinate lift-project hull of a convex set stays inside the
original set. -/
lemma coordinateLiftProjectHull_subset_of_convex
    (P : Set (Fin 5 → ℝ))
    (hP : Convex ℝ P)
    (j : Fin 5) :
    coordinate_lift_project_hull P j ⊆ P := by
  intro x hx
  rw [coordinate_lift_project_hull_def] at hx
  -- The split faces lie inside `P`, so convexity of `P` absorbs their convex hull.
  refine (convexHull_min ?_ hP) hx
  intro y hy
  rcases hy with hy | hy
  · exact hy.1
  · exact hy.1

/-- Helper for Exercise 10.11: the `i`th coordinate lift-project hull over `Q(K₅)` already
imposes the triangle inequality `x_i + x_j + x_k ≤ 1` for every distinct triple containing
`i`. -/
lemma completeGraphEdgeRelaxation_coordinateHull_triple_bound
    {x : Fin 5 → ℝ}
    {i j k : Fin 5}
    (hx : x ∈ coordinate_lift_project_hull Q(K₅) i)
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) :
    x i + x j + x k ≤ 1 := by
  have hconv :
      Convex ℝ {y : Fin 5 → ℝ | y i + y j + y k ≤ 1} := by
    intro y hy z hz a b ha hb hab
    dsimp
    have hy' : y i + y j + y k ≤ 1 := hy
    have hz' : z i + z j + z k ≤ 1 := hz
    nlinarith
  rw [coordinate_lift_project_hull_def] at hx
  have hxHalfspace :
      x ∈ {y : Fin 5 → ℝ | y i + y j + y k ≤ 1} := by
    refine (convexHull_min ?_ hconv) hx
    intro y hy
    rcases hy with ⟨hyQ, hyi⟩ | ⟨hyQ, hyi⟩
    · rw [mem_completeGraphEdgeRelaxation_iff] at hyQ
      have hyi' : y i = 0 := hyi
      have hpair : y j + y k ≤ 1 := hyQ.2 hjk
      simpa [hyi', add_assoc, add_comm, add_left_comm] using hpair
    · rw [mem_completeGraphEdgeRelaxation_iff] at hyQ
      have hyi' : y i = 1 := hyi
      have hyj_zero : y j = 0 := by
        have hpair : y i + y j ≤ 1 := hyQ.2 hij
        linarith [hyQ.1 j, hyi']
      have hyk_zero : y k = 0 := by
        have hpair : y i + y k ≤ 1 := hyQ.2 hik
        linarith [hyQ.1 k, hyi']
      simp [hyi', hyj_zero, hyk_zero]
  exact hxHalfspace

/-- Helper for Exercise 10.11: the triangle-clique relaxation stays inside the original
pairwise-inequality relaxation `Q(K₅)`. -/
lemma tripleCliqueRelaxation_subset_completeGraphEdgeRelaxation :
    exercise_10_11_triple_clique_relaxation ⊆ Q(K₅) := by
  intro x hx
  rw [mem_exercise_10_11_triple_clique_relaxation_iff] at hx
  rw [mem_completeGraphEdgeRelaxation_iff]
  refine ⟨hx.1, ?_⟩
  intro i j hij
  obtain ⟨k, hik, hkj⟩ := exists_third_vertex i j hij
  have htriple : x i + x j + x k ≤ 1 := hx.2 hij hik.symm hkj.symm
  have hk_nonneg : 0 ≤ x k := hx.1 k
  linarith

/-- Helper for Exercise 10.11: the six `0/1` points of `Q(K₅)` are exactly the origin together
with the five coordinate unit vectors. -/
noncomputable def exercise_10_11_vertices : Finset (Fin 5 → ℝ) :=
  insert 0 (Finset.univ.image fun i : Fin 5 ↦ Pi.single i (1 : ℝ))

/-- Helper for Exercise 10.11: membership in the vertex finset means being either the origin or a
coordinate unit vector. -/
lemma mem_exercise_10_11_vertices_iff
    (x : Fin 5 → ℝ) :
    x ∈ exercise_10_11_vertices ↔ x = 0 ∨ ∃ i : Fin 5, x = Pi.single i (1 : ℝ) := by
  simp [exercise_10_11_vertices, eq_comm]

/-- Helper for Exercise 10.11: the `0/1` points of `Q(K₅)` are exactly the origin and the five
coordinate unit vectors. -/
lemma mem_zeroOnePoints_completeGraph_iff
    (x : Fin 5 → ℝ) :
    x ∈ zero_one_points (Nat.le_refl 5) Q(K₅) ↔
      x = 0 ∨ ∃ i : Fin 5, x = Pi.single i (1 : ℝ) := by
  rw [mem_zero_one_points_iff]
  constructor
  · rintro ⟨hxQ, hx01⟩
    rw [mem_completeGraphEdgeRelaxation_iff] at hxQ
    by_cases hzero : ∀ i : Fin 5, x i = 0
    · left
      funext i
      exact hzero i
    · push Not at hzero
      rcases hzero with ⟨i, hi_nonzero⟩
      have hi_one : x i = 1 := by
        rcases hx01 i with hi_zero | hi_one
        · exact False.elim (hi_nonzero hi_zero)
        · exact hi_one
      right
      refine ⟨i, ?_⟩
      funext j
      by_cases hji : j = i
      · subst hji
        simp [hi_one]
      · have hpair : x i + x j ≤ 1 := hxQ.2 (by exact fun h => hji h.symm)
        rcases hx01 j with hj_zero | hj_one
        · have hxj_zero : x j = 0 := by
            simpa using hj_zero
          simp [hji, hxj_zero]
        · exfalso
          have hxj_one : x j = 1 := by
            simpa using hj_one
          linarith [hpair, hi_one, hxj_one]
  · intro hx
    rcases hx with rfl | ⟨i, rfl⟩
    · refine ⟨?_, ?_⟩
      · rw [mem_completeGraphEdgeRelaxation_iff]
        constructor
        · intro j
          simp
        · intro j k hjk
          simp
      · intro j
        simp
    · refine ⟨?_, ?_⟩
      · rw [mem_completeGraphEdgeRelaxation_iff]
        constructor
        · intro j
          by_cases hji : j = i
          · subst hji
            simp
          · simp [hji]
        · intro j k hjk
          by_cases hji : j = i
          · subst j
            by_cases hki : k = i
            · exact False.elim (hjk hki.symm)
            · simp [hki]
          · by_cases hki : k = i
            · subst k
              simp [hji]
            · simp [hji, hki]
      · intro j
        by_cases hji : j = i
        · subst hji
          simp
        · simp [hji]

/-- The first computation for Exercise 10.11 identifies the convex hull of
`S = P ∩ {0, 1}^5` is the simplex cut out by the clique inequality `∑ᵢ xᵢ ≤ 1`. -/
theorem exercise_10_11_conv_zero_one_points :
    convexHull ℝ (zero_one_points (Nat.le_refl 5) Q(K₅)) = K(K₅) :=
  by
    have hvertices :
        zero_one_points (Nat.le_refl 5) Q(K₅) = (exercise_10_11_vertices : Set (Fin 5 → ℝ)) := by
      ext x
      rw [mem_zeroOnePoints_completeGraph_iff]
      simpa using (mem_exercise_10_11_vertices_iff x).symm
    rw [hvertices]
    apply Set.Subset.antisymm
    · -- The six explicit `0/1` points all satisfy the simplex inequalities cutting out `K(K₅)`.
      refine convexHull_min ?_ convex_cliqueRelaxation_completeGraph
      intro x hx
      have hx' : x = 0 ∨ ∃ i : Fin 5, x = Pi.single i (1 : ℝ) := by
        simpa using (mem_exercise_10_11_vertices_iff x).1 hx
      clear hx
      rcases hx' with rfl | ⟨i, rfl⟩
      · rw [mem_cliqueRelaxation_completeGraph_iff]
        constructor
        · intro j
          simp
        · simp
      · rw [mem_cliqueRelaxation_completeGraph_iff]
        constructor
        · intro j
          by_cases hji : j = i
          · subst hji
            simp
          · simp [hji]
        · simp
    · intro x hx
      rw [mem_cliqueRelaxation_completeGraph_iff] at hx
      let w : (Fin 5 → ℝ) → ℝ := fun y ↦
        if y = 0 then 1 - ∑ i : Fin 5, x i
        else ∑ i : Fin 5, if y = Pi.single i (1 : ℝ) then x i else 0
      have hsingle_ne_zero :
          ∀ i : Fin 5, (Pi.single i (1 : ℝ) : Fin 5 → ℝ) ≠ 0 := by
        intro i hzero
        have hvalue := congrFun hzero i
        simp at hvalue
      have hsingle_injective :
          Function.Injective (fun i : Fin 5 ↦ (Pi.single i (1 : ℝ) : Fin 5 → ℝ)) := by
        intro i j hij
        by_cases hji : j = i
        · exact hji.symm
        · have hvalue := congrFun hij i
          simp [hji] at hvalue
      have hw_zero : w 0 = 1 - ∑ i : Fin 5, x i := by
        simp [w]
      have hw_single :
          ∀ i : Fin 5, w (Pi.single i (1 : ℝ)) = x i := by
        intro i
        have hne0 : (Pi.single i (1 : ℝ) : Fin 5 → ℝ) ≠ 0 := hsingle_ne_zero i
        simp [w, hne0, hsingle_injective.eq_iff]
      refine (Finset.mem_convexHull').2 ?_
      refine ⟨w, ?_, ?_, ?_⟩
      · intro y hy
        rw [mem_exercise_10_11_vertices_iff] at hy
        rcases hy with rfl | ⟨i, rfl⟩
        · rw [hw_zero]
          linarith [hx.2]
        · rw [hw_single]
          exact hx.1 i
      · rw [exercise_10_11_vertices]
        rw [Finset.sum_insert]
        · rw [hw_zero]
          have himage :
              ∑ y ∈ Finset.univ.image (fun i : Fin 5 ↦ Pi.single i (1 : ℝ)), w y =
                ∑ i : Fin 5, x i := by
            rw [Finset.sum_image]
            · refine Finset.sum_congr rfl ?_
              intro i hi
              exact hw_single i
            · intro i _ j _ hij
              exact hsingle_injective hij
          rw [himage]
          linarith
        · intro hy
          rcases Finset.mem_image.mp hy with ⟨i, -, hi⟩
          exact hsingle_ne_zero i hi
      · rw [exercise_10_11_vertices]
        rw [Finset.sum_insert]
        · simp only [hw_zero, smul_zero, zero_add]
          calc
            ∑ y ∈ Finset.univ.image (fun i : Fin 5 ↦ Pi.single i (1 : ℝ)), w y • y
                = ∑ i : Fin 5, x i • Pi.single i (1 : ℝ) := by
                    rw [Finset.sum_image]
                    · refine Finset.sum_congr rfl ?_
                      intro i hi
                      rw [hw_single]
                    · intro i _ j _ hij
                      exact hsingle_injective hij
            _ = x := by
                  ext i
                  simp [Pi.single_apply]
        · intro hy
          rcases Finset.mem_image.mp hy with ⟨i, -, hi⟩
          exact hsingle_ne_zero i hi

/-- Helper for Exercise 10.11: the explicit complete-graph Lovász-Schrijver witness keeps only
the first row/column and the diagonal of the lower block. -/
def completeGraphDiagonalWitness (x : Fin 5 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j ↦
    Fin.cases
      (Fin.cases 1 fun j' ↦ x j')
      (fun i' ↦ Fin.cases (x i') fun j' ↦ if i' = j' then x i' else 0)
      i j

/-- Helper for Exercise 10.11: the normalized residual point for the `i`th diagonal witness
column has the `i`th coordinate zero and rescales the remaining coordinates by `1 - x i`. -/
noncomputable def completeGraphResidualPoint (x : Fin 5 → ℝ) (i : Fin 5) : Fin 5 → ℝ :=
  fun j ↦ if j = i then 0 else x j / (1 - x i)

/-- Helper for Exercise 10.11: a homogenized-cone vector over `Q(K₅)` satisfies the coordinate
nonnegativity and pairwise complete-graph bounds of its dehomogenized point. -/
lemma homogenizedCone_completeGraphEdgeRelaxation_bounds
    {y : Fin 6 → ℝ}
    (hy : y ∈ homogenized_cone (Q(K₅))) :
    0 ≤ y 0 ∧
      (∀ i : Fin 5, 0 ≤ y i.succ) ∧
      ∀ ⦃i j : Fin 5⦄, i ≠ j → y i.succ + y j.succ ≤ y 0 := by
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hxHull, rfl⟩
  have hxQ : x ∈ Q(K₅) := by
    rwa [convexHull_eq_self.2 convex_completeGraphEdgeRelaxation] at hxHull
  rw [mem_completeGraphEdgeRelaxation_iff] at hxQ
  refine ⟨?_, ?_, ?_⟩
  · -- The top coordinate is exactly the cone scalar.
    simpa [homogenized_point] using ht
  · -- The lower coordinates inherit nonnegativity from the dehomogenized feasible point.
    intro i
    simpa [homogenized_point] using mul_nonneg ht (hxQ.1 i)
  · intro i j hij
    -- Multiply the pairwise inequality by the nonnegative cone height.
    have hscaled : t * (x i + x j) ≤ t := by
      simpa using mul_le_mul_of_nonneg_left (hxQ.2 hij) ht
    calc
      (t • homogenized_point x) i.succ + (t • homogenized_point x) j.succ
          = t * x i + t * x j := by
              simp [homogenized_point]
      _ = t * (x i + x j) := by
            ring
      _ ≤ t := hscaled
      _ = (t • homogenized_point x) 0 := by
            simp [homogenized_point]

/-- Helper for Exercise 10.11: every Lovász-Schrijver witness over `Q(K₅)` is already diagonal on
the lower `5 × 5` block away from the diagonal. -/
lemma completeGraphLovaszSchrijverWitness_offDiag_eq_zero
    {x : Fin 5 → ℝ}
    {Y : Matrix (Fin 6) (Fin 6) ℝ}
    (hY : IsLovaszSchrijverMatrix (Q(K₅)) Y)
    (hcol0 : Y.mulVec (lifted_basis (0 : Fin 6)) = homogenized_point x) :
    ∀ ⦃i j : Fin 5⦄, i ≠ j → Y i.succ j.succ = 0 := by
  rcases (isLovaszSchrijverMatrix_iff (Q(K₅)) Y).1 hY with ⟨hSymm, -, hrest, hdiag⟩
  have hYi0 : ∀ i : Fin 5, Y i.succ 0 = x i := by
    intro i
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 i.succ
  have hY0i : ∀ i : Fin 5, Y 0 i.succ = x i := by
    intro i
    calc
      Y 0 i.succ = Y i.succ 0 := by
        simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hSymm 0) i.succ).symm
      _ = x i := hYi0 i
  have hYii : ∀ i : Fin 5, Y i.succ i.succ = x i := by
    intro i
    rw [hdiag i, hYi0 i]
  intro i j hij
  have hji : j ≠ i := fun h ↦ hij h.symm
  have hconeCol : Y.mulVec (lifted_basis i.succ) ∈ homogenized_cone (Q(K₅)) := (hrest i).1
  have hbounds := homogenizedCone_completeGraphEdgeRelaxation_bounds hconeCol
  have hnonneg : 0 ≤ Y j.succ i.succ := by
    simpa [mulVec_lifted_basis] using hbounds.2.1 j
  have hpair :
      Y i.succ i.succ + Y j.succ i.succ ≤ Y 0 i.succ := by
    have hpair' : Y j.succ i.succ + Y i.succ i.succ ≤ Y 0 i.succ := by
      simpa [mulVec_lifted_basis] using hbounds.2.2 hji
    linarith
  have hji_zero : Y j.succ i.succ = 0 := by
    linarith [hpair, hYii i, hY0i i, hnonneg]
  calc
    Y i.succ j.succ = Y j.succ i.succ := by
      simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hSymm i.succ) j.succ).symm
    _ = 0 := hji_zero

/-- Helper for Exercise 10.11: the normalized residual point of the explicit diagonal witness is
feasible for `Q(K₅)` whenever the residual height `1 - x i` is positive. -/
lemma completeGraphResidualNormalized_mem_edgeRelaxation
    {x : Fin 5 → ℝ}
    (hx : x ∈ exercise_10_11_triple_clique_relaxation)
    (i : Fin 5)
    (hpos : 0 < 1 - x i) :
    completeGraphResidualPoint x i ∈ Q(K₅) := by
  rw [mem_exercise_10_11_triple_clique_relaxation_iff] at hx
  have hxQ : x ∈ Q(K₅) := tripleCliqueRelaxation_subset_completeGraphEdgeRelaxation hx
  rw [mem_completeGraphEdgeRelaxation_iff] at hxQ ⊢
  refine ⟨?_, ?_⟩
  · -- Each residual coordinate is either zero or a nonnegative rescaling of a feasible coordinate.
    intro j
    by_cases hji : j = i
    · subst hji
      simp [completeGraphResidualPoint]
    · simp [completeGraphResidualPoint, hji, div_nonneg, hx.1 j, le_of_lt hpos]
  · intro j k hjk
    by_cases hji : j = i
    · have hpair : x i + x k ≤ 1 := by
        simpa [hji] using hxQ.2 hjk
      have hki : k ≠ i := by
        intro hki
        exact hjk (hji.trans hki.symm)
      have hbound : x k ≤ 1 - x i := by
        linarith
      have hdiv : x k / (1 - x i) ≤ 1 := by
        exact (div_le_iff₀ hpos).2 (by simpa [one_mul] using hbound)
      have : 0 + x k / (1 - x i) ≤ 1 := by
        simpa using hdiv
      simpa [completeGraphResidualPoint, hji, hki] using this
    by_cases hki : k = i
    · have hpair : x i + x j ≤ 1 := by
        simpa [hki, add_comm] using hxQ.2 (fun h ↦ hjk h.symm)
      have hbound : x j ≤ 1 - x i := by
        linarith
      have hdiv : x j / (1 - x i) ≤ 1 := by
        exact (div_le_iff₀ hpos).2 (by simpa [one_mul] using hbound)
      have : x j / (1 - x i) + 0 ≤ 1 := by
        simpa using hdiv
      simpa [completeGraphResidualPoint, hji, hki] using this
    have hij : i ≠ j := fun h ↦ hji h.symm
    have hik : i ≠ k := fun h ↦ hki h.symm
    have htriple : x i + x j + x k ≤ 1 := hx.2 hij hik hjk
    have hsum_le : x j + x k ≤ 1 - x i := by
      linarith
    have hdiv : (x j + x k) / (1 - x i) ≤ 1 := by
      exact (div_le_iff₀ hpos).2 (by simpa [one_mul] using hsum_le)
    have hrewrite :
        x j / (1 - x i) + x k / (1 - x i) = (x j + x k) / (1 - x i) := by
      ring
    simpa [completeGraphResidualPoint, hji, hki, hrewrite] using hdiv

/-- Helper for Exercise 10.11: the top coordinate of the explicit witness matrix-vector product
is the affine form `v 0 + ∑ i, x i * v i.succ`. -/
lemma completeGraphDiagonalWitness_mulVec_zero
    (x : Fin 5 → ℝ)
    (v : Fin 6 → ℝ) :
    (completeGraphDiagonalWitness x).mulVec v 0 = v 0 + ∑ i : Fin 5, x i * v i.succ := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp [completeGraphDiagonalWitness]

/-- Helper for Exercise 10.11: the `i`th lower coordinate of the explicit witness matrix-vector
product is `x i * (v 0 + v i.succ)`. -/
lemma completeGraphDiagonalWitness_mulVec_succ
    (x : Fin 5 → ℝ)
    (v : Fin 6 → ℝ)
    (i : Fin 5) :
    (completeGraphDiagonalWitness x).mulVec v i.succ = x i * (v 0 + v i.succ) := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hsum :
      ∑ j : Fin 5, completeGraphDiagonalWitness x i.succ j.succ * v j.succ =
        x i * v i.succ := by
    rw [Finset.sum_eq_single i]
    · simp [completeGraphDiagonalWitness]
    · intro j _ hji
      have hij : i ≠ j := fun hij => hji hij.symm
      have hzero : completeGraphDiagonalWitness x i.succ j.succ = 0 := by
        simp [completeGraphDiagonalWitness, hij]
      simp [hzero]
    · intro hi
      exfalso
      exact hi (by simp)
  rw [hsum]
  simp [completeGraphDiagonalWitness]
  ring

/-- Helper for Exercise 10.11: the quadratic form of the explicit witness is a weighted sum of
squares with simplex slack coefficient `1 - ∑ i, x i`. -/
lemma completeGraphDiagonalWitness_dotProduct_mulVec
    (x : Fin 5 → ℝ)
    (v : Fin 6 → ℝ) :
    dotProduct v ((completeGraphDiagonalWitness x).mulVec v) =
      (1 - ∑ i : Fin 5, x i) * (v 0)^2 +
        ∑ i : Fin 5, x i * (v 0 + v i.succ)^2 := by
  rw [dotProduct, Fin.sum_univ_succ, completeGraphDiagonalWitness_mulVec_zero]
  simp_rw [completeGraphDiagonalWitness_mulVec_succ]
  have hsq :
      ∀ i : Fin 5,
        x i * (v 0 + v i.succ)^2 =
          x i * (v 0)^2 + (2 * (x i * (v 0 * v i.succ)) + x i * (v i.succ)^2) := by
    intro i
    ring
  have hleft :
      v 0 * (v 0 + ∑ i : Fin 5, x i * v i.succ) + ∑ i : Fin 5, v i.succ * (x i * (v 0 + v i.succ)) =
        v 0 ^ 2 + ∑ i : Fin 5, (2 * (x i * (v 0 * v i.succ)) + x i * (v i.succ)^2) := by
    calc
      v 0 * (v 0 + ∑ i : Fin 5, x i * v i.succ) + ∑ i : Fin 5, v i.succ * (x i * (v 0 + v i.succ))
          = v 0 * v 0 + v 0 * ∑ i : Fin 5, x i * v i.succ +
              ∑ i : Fin 5, (v i.succ * (x i * v 0) + v i.succ * (x i * v i.succ)) := by
                rw [mul_add]
                simp_rw [mul_add]
      _ = v 0 * v 0 +
            ∑ i : Fin 5,
              (v 0 * (x i * v i.succ) +
                (v i.succ * (x i * v 0) + v i.succ * (x i * v i.succ))) := by
            rw [Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
      _ = v 0 ^ 2 +
            ∑ i : Fin 5,
              (v 0 * (x i * v i.succ) +
                (v i.succ * (x i * v 0) + v i.succ * (x i * v i.succ))) := by
            ring
      _ = v 0 ^ 2 + ∑ i : Fin 5, (2 * (x i * (v 0 * v i.succ)) + x i * (v i.succ)^2) := by
            refine congrArg (fun s : ℝ => v 0 ^ 2 + s) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  have hright :
      (1 - ∑ i : Fin 5, x i) * (v 0)^2 + ∑ i : Fin 5, x i * (v 0 + v i.succ)^2 =
        v 0 ^ 2 + ∑ i : Fin 5, (2 * (x i * (v 0 * v i.succ)) + x i * (v i.succ)^2) := by
    calc
      (1 - ∑ i : Fin 5, x i) * (v 0)^2 + ∑ i : Fin 5, x i * (v 0 + v i.succ)^2
          = (1 - ∑ i : Fin 5, x i) * (v 0)^2 +
              ∑ i : Fin 5,
                (x i * (v 0)^2 + (2 * (x i * (v 0 * v i.succ)) + x i * (v i.succ)^2)) := by
                simp_rw [hsq]
      _ = (1 - ∑ i : Fin 5, x i) * (v 0)^2 +
            ∑ i : Fin 5, x i * (v 0)^2 +
              ∑ i : Fin 5, (2 * (x i * (v 0 * v i.succ)) + x i * (v i.succ)^2) := by
            rw [Finset.sum_add_distrib, add_assoc]
      _ = (1 - ∑ i : Fin 5, x i) * (v 0)^2 +
            (∑ i : Fin 5, x i) * (v 0)^2 +
              ∑ i : Fin 5, (2 * (x i * (v 0 * v i.succ)) + x i * (v i.succ)^2) := by
            rw [Finset.sum_mul]
      _ = v 0 ^ 2 + ∑ i : Fin 5, (2 * (x i * (v 0 * v i.succ)) + x i * (v i.succ)^2) := by
            ring
  exact hleft.trans hright.symm

/-- Helper for Exercise 10.11: the explicit diagonal witness is symmetric. -/
lemma completeGraphDiagonalWitness_transpose
    (x : Fin 5 → ℝ) :
    (completeGraphDiagonalWitness x).transpose = completeGraphDiagonalWitness x := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Helper for Exercise 10.11: the explicit diagonal witness satisfies the linear
Lovász-Schrijver constraints over `Q(K₅)` and has first column `(1, x)`. -/
lemma completeGraphDiagonalWitness_isLovaszSchrijverMatrix
    {x : Fin 5 → ℝ}
    (hx : x ∈ exercise_10_11_triple_clique_relaxation) :
    IsLovaszSchrijverMatrix (Q(K₅)) (completeGraphDiagonalWitness x) ∧
      (completeGraphDiagonalWitness x).mulVec (lifted_basis (0 : Fin 6)) = homogenized_point x := by
  rw [mem_exercise_10_11_triple_clique_relaxation_iff] at hx
  have hxTriple : x ∈ exercise_10_11_triple_clique_relaxation :=
    (mem_exercise_10_11_triple_clique_relaxation_iff x).2 hx
  have hQ : x ∈ Q(K₅) := tripleCliqueRelaxation_subset_completeGraphEdgeRelaxation hx
  have hIndicatorQ : ∀ i : Fin 5, (Pi.single i (1 : ℝ) : Fin 5 → ℝ) ∈ Q(K₅) := by
    intro i
    rw [mem_completeGraphEdgeRelaxation_iff]
    constructor
    · intro j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [hji]
    · intro j k hjk
      by_cases hji : j = i
      · subst j
        by_cases hki : k = i
        · exact False.elim (hjk hki.symm)
        · simp [hki]
      · by_cases hki : k = i
        · subst k
          simp [hji]
        · simp [hji, hki]
  have hzeroQ : (0 : Fin 5 → ℝ) ∈ Q(K₅) := by
    rw [mem_completeGraphEdgeRelaxation_iff]
    constructor <;> simp
  have hcol0 :
      (completeGraphDiagonalWitness x).mulVec (lifted_basis (0 : Fin 6)) = homogenized_point x := by
    -- The first column is exactly the homogenized lift `(1, x)`.
    funext j
    rw [mulVec_lifted_basis]
    refine Fin.cases ?_ ?_ j
    · rfl
    · intro j
      rfl
  refine ⟨?_, hcol0⟩
  rw [isLovaszSchrijverMatrix_iff]
  refine ⟨completeGraphDiagonalWitness_transpose x, ?_, ?_, ?_⟩
  · -- The first column is the homogenized point of `x`, and `x ∈ Q(K₅)`.
    rw [hcol0]
    exact homogenized_point_mem_homogenized_cone (Q(K₅)) (subset_convexHull ℝ (Q(K₅)) hQ)
  · intro i
    refine ⟨?_, ?_⟩
    · -- The `i`th lifted column is `x i` times the homogenized unit vector at `i`.
      rw [mem_homogenized_cone_iff]
      refine ⟨x i, hx.1 i, Pi.single i (1 : ℝ), subset_convexHull ℝ (Q(K₅)) (hIndicatorQ i), ?_⟩
      ext j
      refine Fin.cases ?_ ?_ j
      · simp [completeGraphDiagonalWitness, mulVec_lifted_basis, homogenized_point]
      · intro j
        by_cases hji : j = i
        · subst hji
          simp [completeGraphDiagonalWitness, mulVec_lifted_basis, homogenized_point]
        · simp [completeGraphDiagonalWitness, mulVec_lifted_basis, homogenized_point, hji]
    · by_cases hzero : 1 - x i = 0
      · -- When the residual height vanishes, pairwise feasibility of `x` forces the residual
        -- column itself to be zero.
        rw [mem_homogenized_cone_iff]
        refine ⟨0, le_rfl, 0, subset_convexHull ℝ (Q(K₅)) hzeroQ, ?_⟩
        ext j
        refine Fin.cases ?_ ?_ j
        · have hxi_one : x i = 1 := by
            linarith
          simp [Matrix.mulVec_sub, mulVec_lifted_basis, completeGraphDiagonalWitness, hxi_one]
        · intro j
          by_cases hji : j = i
          · subst hji
            simp [Matrix.mulVec_sub, mulVec_lifted_basis, completeGraphDiagonalWitness]
          · have hpair : x i + x j ≤ 1 := hQ.2 (fun h ↦ hji h.symm)
            have hxj_zero : x j = 0 := by
              have hxi_one : x i = 1 := by
                linarith
              linarith [hx.1 j, hpair, hxi_one]
            simp [Matrix.mulVec_sub, mulVec_lifted_basis, completeGraphDiagonalWitness,
              hxj_zero]
      · have hnonneg : 0 ≤ 1 - x i := by
          have hpair : x i + x (alternateVertex i) ≤ 1 := hQ.2 (alternateVertex_ne i).symm
          linarith [hx.1 (alternateVertex i), hpair]
        have hne : 0 ≠ 1 - x i := by
          simpa [eq_comm] using hzero
        have hpos : 0 < 1 - x i := lt_of_le_of_ne hnonneg hne
        have hresQ :
            completeGraphResidualPoint x i ∈ Q(K₅) :=
          completeGraphResidualNormalized_mem_edgeRelaxation
            hxTriple i hpos
        rw [mem_homogenized_cone_iff]
        refine ⟨1 - x i, le_of_lt hpos, completeGraphResidualPoint x i,
          subset_convexHull ℝ (Q(K₅)) hresQ, ?_⟩
        ext j
        refine Fin.cases ?_ ?_ j
        · -- The residual top coordinate is the expected slack `1 - x i`.
          simp [Matrix.mulVec_sub, mulVec_lifted_basis, completeGraphDiagonalWitness,
            homogenized_point]
        · intro j
          by_cases hji : j = i
          · subst hji
            simp [Matrix.mulVec_sub, mulVec_lifted_basis, completeGraphDiagonalWitness,
              completeGraphResidualPoint, homogenized_point]
          · have hden : (1 - x i) ≠ 0 := ne_of_gt hpos
            calc
              ((completeGraphDiagonalWitness x).mulVec
                  (lifted_basis (0 : Fin 6) - lifted_basis i.succ)) j.succ
                  = x j := by
                      simp [Matrix.mulVec_sub, mulVec_lifted_basis, completeGraphDiagonalWitness,
                        hji]
              _ = (1 - x i) * (x j / (1 - x i)) := by
                    symm
                    field_simp [hden]
              _ = ((1 - x i) • homogenized_point (completeGraphResidualPoint x i)) j.succ := by
                    simp [completeGraphResidualPoint, homogenized_point, hji]
  · intro i
    -- The witness was designed so that the diagonal matches the first column on the lower block.
    simp [completeGraphDiagonalWitness]

/-- Helper for Exercise 10.11: the explicit diagonal witness is positive semidefinite whenever
`x` satisfies the simplex inequality `∑ i, x i ≤ 1`. -/
lemma completeGraphDiagonalWitness_posSemidef
    {x : Fin 5 → ℝ}
    (hx : x ∈ K(K₅)) :
    (completeGraphDiagonalWitness x).PosSemidef := by
  rw [mem_cliqueRelaxation_completeGraph_iff] at hx
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Over `ℝ`, transpose symmetry is exactly the Hermitian condition.
    simpa using completeGraphDiagonalWitness_transpose x
  · intro v
    -- The quadratic-form normal form reduces PSD to termwise nonnegativity.
    have hv :
        star v ⬝ᵥ (completeGraphDiagonalWitness x).mulVec v =
          (1 - ∑ i : Fin 5, x i) * (v 0)^2 +
            ∑ i : Fin 5, x i * (v 0 + v i.succ)^2 := by
      simpa using completeGraphDiagonalWitness_dotProduct_mulVec x v
    rw [hv]
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (sub_nonneg.mpr hx.2) (sq_nonneg (v 0))
    · refine Finset.sum_nonneg ?_
      intro i hi
      exact mul_nonneg (hx.1 i) (sq_nonneg (v 0 + v i.succ))

/-- Helper for Exercise 10.11: the clique-relaxation simplex inequality implies all one-round
triangle inequalities. -/
lemma cliqueRelaxation_completeGraph_subset_tripleCliqueRelaxation :
    K(K₅) ⊆ exercise_10_11_triple_clique_relaxation := by
  intro x hx
  rw [mem_cliqueRelaxation_completeGraph_iff] at hx
  rw [mem_exercise_10_11_triple_clique_relaxation_iff]
  refine ⟨hx.1, ?_⟩
  intro i j k hij hik hjk
  -- The sum over any three distinct coordinates is bounded by the full nonnegative sum.
  have hsum_le :
      ({i, j, k} : Finset (Fin 5)).sum x ≤ ∑ l : Fin 5, x l := by
    exact Finset.sum_le_univ_sum_of_nonneg fun l ↦ hx.1 l
  have hsum_eq :
      ({i, j, k} : Finset (Fin 5)).sum x = x i + x j + x k := by
    simp [hij, hik, hjk, add_comm, add_left_comm]
  rw [hsum_eq] at hsum_le
  exact hsum_le.trans hx.2

/-- Helper for Exercise 10.11: every point of `N(Q(K₅))` already satisfies the one-round
triangle-clique inequalities. -/
lemma mem_tripleCliqueRelaxation_of_mem_lovaszSchrijverN
    {x : Fin 5 → ℝ}
    (hxN : x ∈ N(Q(K₅))) :
    x ∈ exercise_10_11_triple_clique_relaxation := by
  rw [mem_lovasz_schrijver_N_iff] at hxN
  rcases hxN with ⟨Y, hY, hcol0⟩
  have hxQ : x ∈ Q(K₅) := by
    exact lovasz_schrijver_N_subset (Q(K₅)) convex_completeGraphEdgeRelaxation
      ((mem_lovasz_schrijver_N_iff (Q(K₅)) x).2 ⟨Y, hY, hcol0⟩)
  rw [mem_completeGraphEdgeRelaxation_iff] at hxQ
  rw [mem_exercise_10_11_triple_clique_relaxation_iff]
  rcases (isLovaszSchrijverMatrix_iff (Q(K₅)) Y).1 hY with ⟨hSymm, -, hrest, hdiag⟩
  have hoffDiag := completeGraphLovaszSchrijverWitness_offDiag_eq_zero hY hcol0
  have hY00 : Y 0 0 = 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
  have hYi0 : ∀ i : Fin 5, Y i.succ 0 = x i := by
    intro i
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 i.succ
  have hY0i : ∀ i : Fin 5, Y 0 i.succ = x i := by
    intro i
    calc
      Y 0 i.succ = Y i.succ 0 := by
        simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hSymm 0) i.succ).symm
      _ = x i := hYi0 i
  refine ⟨hxQ.1, ?_⟩
  intro i j k hij hik hjk
  have hji : j ≠ i := fun h ↦ hij h.symm
  have hki : k ≠ i := fun h ↦ hik h.symm
  have hresidual :
      Y.mulVec (lifted_basis (0 : Fin 6) - lifted_basis i.succ) ∈ homogenized_cone (Q(K₅)) :=
    (hrest i).2
  have hbounds := homogenizedCone_completeGraphEdgeRelaxation_bounds hresidual
  have htop :
      (Y.mulVec (lifted_basis (0 : Fin 6) - lifted_basis i.succ)) 0 = 1 - x i := by
    simp [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY0i i]
  have hjcoord :
      (Y.mulVec (lifted_basis (0 : Fin 6) - lifted_basis i.succ)) j.succ = x j := by
    have hzero : Y j.succ i.succ = 0 := hoffDiag hji
    simp [Matrix.mulVec_sub, mulVec_lifted_basis, hYi0 j, hzero]
  have hkcoord :
      (Y.mulVec (lifted_basis (0 : Fin 6) - lifted_basis i.succ)) k.succ = x k := by
    have hzero : Y k.succ i.succ = 0 := hoffDiag hki
    simp [Matrix.mulVec_sub, mulVec_lifted_basis, hYi0 k, hzero]
  have hpair :
      (Y.mulVec (lifted_basis (0 : Fin 6) - lifted_basis i.succ)) j.succ +
        (Y.mulVec (lifted_basis (0 : Fin 6) - lifted_basis i.succ)) k.succ ≤
          (Y.mulVec (lifted_basis (0 : Fin 6) - lifted_basis i.succ)) 0 := by
    exact hbounds.2.2 hjk
  rw [hjcoord, hkcoord, htop] at hpair
  linarith

/-- Exercise 10.11 (2). The semidefinite Lovász-Schrijver relaxation `N₊(P)` is already the
same simplex `∑ᵢ xᵢ ≤ 1`. -/
theorem exercise_10_11_N_plus_eq_clique_relaxation :
    N₊(Q(K₅)) = K(K₅) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxN : x ∈ N(Q(K₅)) := lovasz_schrijver_N_plus_subset_N (Q(K₅)) hx
    have hxTriple : x ∈ exercise_10_11_triple_clique_relaxation :=
      mem_tripleCliqueRelaxation_of_mem_lovaszSchrijverN hxN
    rw [mem_exercise_10_11_triple_clique_relaxation_iff] at hxTriple
    rw [mem_lovasz_schrijver_N_plus_iff] at hx
    rcases hx with ⟨Y, hY, hYpsd, hcol0⟩
    rcases (isLovaszSchrijverMatrix_iff (Q(K₅)) Y).1 hY with ⟨hSymm, _, _, hdiag⟩
    have hoffDiag := completeGraphLovaszSchrijverWitness_offDiag_eq_zero hY hcol0
    have hY00 : Y 0 0 = 1 := by
      simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
    have hYi0 : ∀ i : Fin 5, Y i.succ 0 = x i := by
      intro i
      simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 i.succ
    have hY0i : ∀ i : Fin 5, Y 0 i.succ = x i := by
      intro i
      calc
        Y 0 i.succ = Y i.succ 0 := by
          simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hSymm 0) i.succ).symm
        _ = x i := hYi0 i
    have hYii : ∀ i : Fin 5, Y i.succ i.succ = x i := by
      intro i
      rw [hdiag i, hYi0 i]
    let v : Fin 6 → ℝ := Fin.cons 1 (fun _ : Fin 5 ↦ (-1 : ℝ))
    have hv_nonneg : 0 ≤ dotProduct v (Y.mulVec v) := by
      simpa using hYpsd.dotProduct_mulVec_nonneg v
    have hmul_top : (Y.mulVec v) 0 = 1 - ∑ i : Fin 5, x i := by
      -- The top coordinate sees only the first row of the witness.
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      simp [v, hY00, hY0i]
      ring
    have hmul_succ : ∀ i : Fin 5, (Y.mulVec v) i.succ = 0 := by
      intro i
      -- Each lower coordinate cancels its diagonal term, and the off-diagonal terms vanish.
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      have hrow_sum :
          ∑ j : Fin 5, Y i.succ j.succ * (-1 : ℝ) = -Y i.succ i.succ := by
        rw [Finset.sum_eq_single i]
        · ring
        · intro j _ hji
          have hzero : Y i.succ j.succ = 0 := hoffDiag (fun h ↦ hji h.symm)
          simp [hzero]
        · intro hi
          exfalso
          exact hi (by simp)
      calc
        Y i.succ 0 * v 0 + ∑ j : Fin 5, Y i.succ j.succ * v j.succ
            = Y i.succ 0 + ∑ j : Fin 5, Y i.succ j.succ * (-1 : ℝ) := by
                simp [v]
        _ = Y i.succ 0 - Y i.succ i.succ := by
              rw [hrow_sum]
              ring
        _ = 0 := by
              rw [hYi0 i, hYii i]
              ring
    rw [mem_cliqueRelaxation_completeGraph_iff]
    refine ⟨hxTriple.1, ?_⟩
    have hquad : dotProduct v (Y.mulVec v) = 1 - ∑ i : Fin 5, x i := by
      rw [dotProduct, Fin.sum_univ_succ]
      simp [v, hmul_top, hmul_succ]
    rw [hquad] at hv_nonneg
    linarith
  · intro x hx
    have hxTriple : x ∈ exercise_10_11_triple_clique_relaxation :=
      cliqueRelaxation_completeGraph_subset_tripleCliqueRelaxation hx
    obtain ⟨hY, hcol0⟩ := completeGraphDiagonalWitness_isLovaszSchrijverMatrix hxTriple
    rw [mem_lovasz_schrijver_N_plus_iff]
    refine ⟨completeGraphDiagonalWitness x, hY, ?_, hcol0⟩
    exact completeGraphDiagonalWitness_posSemidef hx

/-- The third computation for Exercise 10.11 shows that the linear Lovász-Schrijver relaxation
`N(P)` is the one-round
triangle-clique relaxation cut out by all inequalities `x_i + x_j + x_k ≤ 1`. -/
theorem exercise_10_11_N_eq_triple_clique_relaxation :
    N(Q(K₅)) = exercise_10_11_triple_clique_relaxation := by
  apply Set.Subset.antisymm
  · intro x hx
    exact mem_tripleCliqueRelaxation_of_mem_lovaszSchrijverN hx
  · intro x hx
    obtain ⟨hY, hcol0⟩ := completeGraphDiagonalWitness_isLovaszSchrijverMatrix hx
    rw [mem_lovasz_schrijver_N_iff]
    exact ⟨completeGraphDiagonalWitness x, hY, hcol0⟩

/-- The fourth computation for Exercise 10.11 identifies the full-coordinate lift-and-project
closure of `P = Q(K₅)`, namely
`lift_project_closure P Finset.univ`, equals the same triangle-clique relaxation as the linear
Lovász-Schrijver operator. -/
theorem exercise_10_11_coordinate_closure_eq_triple_clique_relaxation :
    lift_project_closure Q(K₅) Finset.univ = exercise_10_11_triple_clique_relaxation := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [mem_lift_project_closure_iff] at hx
    have hxQ : x ∈ Q(K₅) :=
      coordinateLiftProjectHull_subset_of_convex Q(K₅) convex_completeGraphEdgeRelaxation 0
        (hx 0 (by simp))
    rw [mem_completeGraphEdgeRelaxation_iff] at hxQ
    rw [mem_exercise_10_11_triple_clique_relaxation_iff]
    refine ⟨hxQ.1, ?_⟩
    intro i j k hij hik hjk
    exact completeGraphEdgeRelaxation_coordinateHull_triple_bound
      (hx i (by simp)) hij hik hjk
  · intro x hx
    have hxN : x ∈ N(Q(K₅)) := by
      rw [exercise_10_11_N_eq_triple_clique_relaxation]
      exact hx
    rw [mem_lift_project_closure_iff]
    intro j hj
    exact lovasz_schrijver_N_subset_coordinate_lift_project_hull
      (Q(K₅)) completeGraphEdgeRelaxation_subset_prefixUnitBox j hxN

end Exercise1011
