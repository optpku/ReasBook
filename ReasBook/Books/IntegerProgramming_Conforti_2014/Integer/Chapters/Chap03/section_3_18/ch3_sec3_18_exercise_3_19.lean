import Mathlib

open scoped BigOperators

-- Semantic search tool `lean_leansearch` was not available in this environment; this file uses
-- mathlib's canonical `Set.Icc`, `affineSpan`, and `FiniteDimensional.finrank` API directly.

/-- The feasible region in Exercise 3.19, cut out by the subset inequalities
`∑_{j ∈ J} x_j + ∑_{j ∉ J} (1 - x_j) ≥ n / 2` for all subsets `J`.

The textbook box condition `x ∈ [0,1]^n` is redundant here: the inequalities already force the
unique feasible point to be the constant vector `1 / 2`. -/
def all_subset_halfspace_polytope (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ J : Finset (Fin n),
    J.sum x + (Finset.univ \ J).sum (fun j ↦ 1 - x j) ≥ (n : ℝ) / 2}

/-- Helper for Exercise 3.19: the subset inequality for `J` and the subset inequality for its
complement add up to the constant `n`. -/
lemma subset_constraint_complement_add (n : ℕ) (x : Fin n → ℝ) (J : Finset (Fin n)) :
    J.sum x + (Finset.univ \ J).sum (fun j ↦ 1 - x j) +
      ((Finset.univ \ J).sum x + J.sum (fun j ↦ 1 - x j)) =
        (n : ℝ) := by
  classical
  -- Sum the `x`-terms and the `(1 - x)`-terms separately over the partition `J ⊔ (univ \ J)`.
  have hxsum : (Finset.univ \ J).sum x + J.sum x = Finset.univ.sum x := by
    exact Finset.sum_sdiff (Finset.subset_univ J)
  let oneMinusX : Fin n → ℝ := fun j ↦ 1 - x j
  have honeMinusSum :
      (Finset.univ \ J).sum oneMinusX + J.sum oneMinusX = Finset.univ.sum oneMinusX := by
    exact Finset.sum_sdiff (Finset.subset_univ J)
  -- Reassemble the partition equalities into the complementary-constraint identity.
  calc
    J.sum x + (Finset.univ \ J).sum (fun j ↦ 1 - x j) +
        ((Finset.univ \ J).sum x + J.sum (fun j ↦ 1 - x j)) =
          ((Finset.univ \ J).sum x + J.sum x) +
            ((Finset.univ \ J).sum (fun j ↦ 1 - x j) + J.sum (fun j ↦ 1 - x j)) := by
      ring
    _ = Finset.univ.sum x + Finset.univ.sum (fun j ↦ 1 - x j) := by
      rw [hxsum]
      simpa [oneMinusX] using
        congrArg (fun t : ℝ ↦ Finset.univ.sum x + t) honeMinusSum
    _ = Finset.univ.sum (fun j ↦ x j + (1 - x j)) := by
      rw [← Finset.sum_add_distrib]
    _ = (n : ℝ) := by
      simp [Finset.card_univ]

/-- Helper for Exercise 3.19: every defining subset inequality of a feasible point is tight at
equality `n / 2`. -/
lemma feasible_constraint_eq_half {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ all_subset_halfspace_polytope n) (J : Finset (Fin n)) :
    J.sum x + (Finset.univ \ J).sum (fun j ↦ 1 - x j) = (n : ℝ) / 2 := by
  classical
  -- The inequalities for `J` and `univ \ J` meet because their sum is fixed by the helper above.
  have hJ :
      (n : ℝ) / 2 ≤ J.sum x + (Finset.univ \ J).sum (fun j ↦ 1 - x j) :=
    hx J
  have hJc :
      (n : ℝ) / 2 ≤
        (Finset.univ \ J).sum x + (J : Finset (Fin n)).sum (fun j ↦ 1 - x j) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      hx (Finset.univ \ J)
  have hsum := subset_constraint_complement_add n x J
  linarith

/-- Helper for Exercise 3.19: every feasible point has all coordinates equal to `1 / 2`. -/
lemma feasible_coordinate_eq_half {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ all_subset_halfspace_polytope n) (i : Fin n) :
    x i = (1 : ℝ) / 2 := by
  classical
  -- First tighten the empty-set and singleton constraints to equalities.
  have hEmpty :
      Finset.univ.sum (fun j : Fin n ↦ 1 - x j) = (n : ℝ) / 2 := by
    simpa using feasible_constraint_eq_half hx (∅ : Finset (Fin n))
  have hSingle :
      x i + (Finset.univ \ ({i} : Finset (Fin n))).sum (fun j : Fin n ↦ 1 - x j) =
        (n : ℝ) / 2 := by
    simpa using feasible_constraint_eq_half hx ({i} : Finset (Fin n))
  let oneMinusX : Fin n → ℝ := fun j ↦ 1 - x j
  have hDecomp :
      (Finset.univ \ ({i} : Finset (Fin n))).sum oneMinusX +
          ({i} : Finset (Fin n)).sum oneMinusX =
        Finset.univ.sum oneMinusX := by
    exact Finset.sum_sdiff (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
  -- Comparing the two equalities isolates the `i`th coordinate.
  have hDecomp' :
      (Finset.univ \ ({i} : Finset (Fin n))).sum (fun j : Fin n ↦ 1 - x j) + (1 - x i) =
        Finset.univ.sum (fun j : Fin n ↦ 1 - x j) := by
    simpa [oneMinusX] using hDecomp
  linarith

/-- The subset-inequality feasible region is the singleton consisting of the constant vector with
every coordinate equal to `1 / 2`; in particular, this also recovers the textbook polytope inside
`[0,1]^n`. -/
theorem all_subset_halfspace_polytope_eq_singleton (n : ℕ) :
    all_subset_halfspace_polytope n = ({fun _ ↦ (1 : ℝ) / 2} : Set (Fin n → ℝ)) := by
  classical
  ext x
  constructor
  · intro hx
    -- Every feasible coordinate equals `1 / 2`, so the point is the center vector.
    rw [Set.mem_singleton_iff]
    funext i
    exact feasible_coordinate_eq_half hx i
  · rintro rfl
    intro J
    -- Each term equals `1 / 2`, so the left-hand side reduces to a card-counting identity.
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hcardNat : (Finset.univ \ J).card + J.card = n := by
      simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ J)
    have hcard : ((Finset.univ \ J).card : ℝ) + (J.card : ℝ) = n := by
      exact_mod_cast hcardNat
    linarith

/-- Exercise 3.19. The polytope
`{x ∈ [0,1]^n : ∑_{j ∈ J} x_j + ∑_{j ∉ J} (1 - x_j) ≥ n / 2` for all `J ⊆ {1, …, n}}`
is a singleton, so its affine-span dimension is `0`. -/
theorem all_subset_halfspace_polytope_finrank_direction_affineSpan (n : ℕ) :
    Module.finrank ℝ (affineSpan ℝ (all_subset_halfspace_polytope n)).direction = 0 := by
  -- Rewrite the feasible set as a singleton and collapse the affine-span direction.
  rw [all_subset_halfspace_polytope_eq_singleton n, direction_affineSpan,
    vectorSpan_singleton, finrank_bot]
