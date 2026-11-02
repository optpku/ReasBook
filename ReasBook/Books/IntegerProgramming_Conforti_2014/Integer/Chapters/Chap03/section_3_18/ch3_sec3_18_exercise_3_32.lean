import Mathlib

open Set

-- Semantic search tool `lean_leansearch` was unavailable in this environment; this file uses an
-- explicit one-dimensional family of finite subsets of `ℝ` as the Helly counterexample.

-- Declarations for this item will be appended below by the statement pipeline.

/-- A three-set family in `ℝ` witnessing the failure of Helly's theorem without convexity. -/
def helly_nonconvex_counterexample_family : Fin 3 → Set ℝ :=
  ![({0, 1} : Set ℝ), ({0, 2} : Set ℝ), ({1, 2} : Set ℝ)]

/-- Helper for Exercise 3.32: each set in the counterexample family contains two points whose
midpoint is missing from that set. -/
lemma helly_nonconvex_counterexample_midpoint_gap
    (i : Fin 3) :
    ∃ a b : ℝ,
      a ∈ helly_nonconvex_counterexample_family i ∧
      b ∈ helly_nonconvex_counterexample_family i ∧
      midpoint ℝ a b ∉ helly_nonconvex_counterexample_family i := by
  -- Normalize the finite family to the three concrete two-point sets.
  fin_cases i
  · refine ⟨0, 1, ?_, ?_, ?_⟩
    · simp [helly_nonconvex_counterexample_family]
    · simp [helly_nonconvex_counterexample_family]
    · norm_num [helly_nonconvex_counterexample_family, midpoint_eq_smul_add, smul_eq_mul]
  · refine ⟨0, 2, ?_, ?_, ?_⟩
    · simp [helly_nonconvex_counterexample_family]
    · simp [helly_nonconvex_counterexample_family]
    · norm_num [helly_nonconvex_counterexample_family, midpoint_eq_smul_add, smul_eq_mul]
  · refine ⟨1, 2, ?_, ?_, ?_⟩
    · simp [helly_nonconvex_counterexample_family]
    · simp [helly_nonconvex_counterexample_family]
    · norm_num [helly_nonconvex_counterexample_family, midpoint_eq_smul_add, smul_eq_mul]

/-- Helper for Exercise 3.32: any two distinct members of the counterexample family share an
explicit common point. -/
lemma helly_nonconvex_counterexample_common_point_of_distinct_pair
    {i j : Fin 3} (hij : i ≠ j) :
    ∃ x : ℝ,
      x ∈ helly_nonconvex_counterexample_family i ∧
      x ∈ helly_nonconvex_counterexample_family j := by
  -- Exhaust the three indices and choose the common endpoint in each off-diagonal case.
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · refine ⟨0, ?_, ?_⟩
    · simp [helly_nonconvex_counterexample_family]
    · simp [helly_nonconvex_counterexample_family]
  · refine ⟨1, ?_, ?_⟩
    · simp [helly_nonconvex_counterexample_family]
    · simp [helly_nonconvex_counterexample_family]
  · refine ⟨0, ?_, ?_⟩
    · simp [helly_nonconvex_counterexample_family]
    · simp [helly_nonconvex_counterexample_family]
  · exact (hij rfl).elim
  · refine ⟨2, ?_, ?_⟩
    · simp [helly_nonconvex_counterexample_family]
    · simp [helly_nonconvex_counterexample_family]
  · refine ⟨1, ?_, ?_⟩
    · simp [helly_nonconvex_counterexample_family]
    · simp [helly_nonconvex_counterexample_family]
  · refine ⟨2, ?_, ?_⟩
    · simp [helly_nonconvex_counterexample_family]
    · simp [helly_nonconvex_counterexample_family]
  · exact (hij rfl).elim

/-- Helper for Exercise 3.32: no real number belongs to all three members of the counterexample
family at once. -/
lemma helly_nonconvex_counterexample_not_mem_all
    (x : ℝ) :
    x ∉ ⋂ i : Fin 3, helly_nonconvex_counterexample_family i := by
  intro hx
  -- Membership in the first two sets forces `x = 0`.
  have hx0 : x ∈ helly_nonconvex_counterexample_family (0 : Fin 3) := Set.mem_iInter.mp hx 0
  have hx1 : x ∈ helly_nonconvex_counterexample_family (1 : Fin 3) := Set.mem_iInter.mp hx 1
  have hx2 : x ∈ helly_nonconvex_counterexample_family (2 : Fin 3) := Set.mem_iInter.mp hx 2
  have hx0' : x = 0 ∨ x = 1 := by
    simpa [helly_nonconvex_counterexample_family] using hx0
  have hx1' : x = 0 ∨ x = 2 := by
    simpa [helly_nonconvex_counterexample_family] using hx1
  have hx_zero : x = 0 := by
    rcases hx0' with hx0eq | hx0eq
    · exact hx0eq
    · rcases hx1' with hx1eq | hx1eq
      · exact hx1eq
      · linarith
  -- Rewriting the third membership by `x = 0` yields an impossible endpoint condition.
  rw [hx_zero] at hx2
  simp [helly_nonconvex_counterexample_family] at hx2

/-- Exercise 3.32 (1). Each member of `helly_nonconvex_counterexample_family` is nonconvex, so
Theorem 3.44's convexity hypothesis is absent in this example. -/
theorem helly_nonconvex_counterexample_not_convex
    (i : Fin 3) :
    ¬ Convex ℝ (helly_nonconvex_counterexample_family i) := by
  intro hconvex
  -- The midpoint helper produces a concrete midpoint obstruction.
  obtain ⟨a, b, ha, hb, hmidpoint_gap⟩ :=
    helly_nonconvex_counterexample_midpoint_gap i
  have hmidpoint_mem : midpoint ℝ a b ∈ helly_nonconvex_counterexample_family i :=
    hconvex.midpoint_mem ha hb
  exact hmidpoint_gap hmidpoint_mem

/-- Exercise 3.32 (2). Every two-set subfamily of `helly_nonconvex_counterexample_family` has
nonempty intersection, so the `d + 1 = 2` conclusion of Theorem 3.44 fails in dimension `d = 1`.
-/
theorem helly_nonconvex_counterexample_pairwise_intersection_nonempty
    (i j : Fin 3) (hij : i ≠ j) :
    Set.Nonempty
      (helly_nonconvex_counterexample_family i ∩ helly_nonconvex_counterexample_family j) := by
  -- Package the explicit common point from the finite case split as a point of the intersection.
  obtain ⟨x, hx_i, hx_j⟩ :=
    helly_nonconvex_counterexample_common_point_of_distinct_pair hij
  exact ⟨x, ⟨hx_i, hx_j⟩⟩

/-- Exercise 3.32 (3). The total intersection of `helly_nonconvex_counterexample_family` is
empty, giving a one-dimensional counterexample to Theorem 3.44 without convexity. -/
theorem helly_nonconvex_counterexample_total_intersection_empty :
    (⋂ i : Fin 3, helly_nonconvex_counterexample_family i) = (∅ : Set ℝ) := by
  -- Reduce emptiness to the elementwise obstruction proved above.
  rw [Set.eq_empty_iff_forall_notMem]
  intro x
  exact helly_nonconvex_counterexample_not_mem_all x
