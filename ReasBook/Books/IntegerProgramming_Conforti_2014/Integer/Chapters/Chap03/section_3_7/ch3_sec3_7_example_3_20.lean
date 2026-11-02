import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic search tool `lean_leansearch` was not available in this environment; this file keeps
-- the chapter's permutahedron as a source-facing owner while reusing mathlib's canonical
-- `convexHull`/`affineSpan` API.

/-- The vector in `Fin n → ℝ` with coordinates `1, 2, ..., n`. -/
def ascending_vector (n : ℕ) : Fin n → ℝ :=
  fun i ↦ ((i : ℕ) + 1 : ℝ)

/-- The vertex set of the `n`th permutahedron, obtained by permuting the coordinates of
`(1, 2, ..., n)`. -/
def permutahedron_vertices (n : ℕ) : Set (Fin n → ℝ) :=
  Set.range fun σ : Equiv.Perm (Fin n) ↦ ascending_vector n ∘ σ

/-- A point lies in the vertex set of the `n`th permutahedron exactly when it is obtained by
permuting the coordinates of `ascending_vector n`. -/
theorem mem_permutahedron_vertices_iff {n : ℕ} {x : Fin n → ℝ} :
    x ∈ permutahedron_vertices n ↔ ∃ σ : Equiv.Perm (Fin n), x = ascending_vector n ∘ σ := by
  -- Unfold the vertex set to expose the underlying range membership.
  simp [permutahedron_vertices, eq_comm]

/-- The `n`th permutahedron is the convex hull of its vertex set. -/
def permutahedron (n : ℕ) : Set (Fin n → ℝ) :=
  convexHull ℝ (permutahedron_vertices n)

/-- The `n`th permutahedron is defined as the convex hull of `permutahedron_vertices n`. -/
theorem permutahedron_eq_convexHull (n : ℕ) :
    permutahedron n = convexHull ℝ (permutahedron_vertices n) := by
  -- This is the defining equation of `permutahedron`.
  rfl

/-- The affine span of the `n`th permutahedron agrees with the affine span of its vertices. -/
theorem affineSpan_permutahedron (n : ℕ) :
    affineSpan ℝ (permutahedron n) = affineSpan ℝ (permutahedron_vertices n) := by
  -- Replace the permutahedron by its defining convex hull and use the standard affine-span lemma.
  rw [permutahedron_eq_convexHull, affineSpan_convexHull]

/-- Helper for Example 3.20: the unpermuted ascending vector is itself a vertex, hence a point of
the permutahedron. -/
lemma ascending_vector_mem_permutahedron (n : ℕ) : ascending_vector n ∈ permutahedron n := by
  -- The identity permutation gives the base vertex, and vertices lie in their convex hull.
  exact subset_convexHull ℝ (permutahedron_vertices n) ⟨Equiv.refl _, rfl⟩

private lemma sum_range_initial_segment_eq_choose (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) = (Nat.choose (n + 1) 2 : ℝ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [Nat.choose_succ_succ, Nat.choose_one_right]
      ring_nf

/-- Helper for Example 3.20: the coordinate-sum functional on `ascending_vector n` evaluates to
`\binom{n+1}{2}`. -/
lemma ascending_vector_sumCoords (n : ℕ) :
    (Pi.basisFun ℝ (Fin n)).sumCoords (ascending_vector n) = (Nat.choose (n + 1) 2 : ℝ) := by
  calc
    (Pi.basisFun ℝ (Fin n)).sumCoords (ascending_vector n) = ∑ i, ascending_vector n i := by
      simp
    _ = ∑ i ∈ Finset.range n, ((i : ℝ) + 1) := by
      simpa [ascending_vector] using
        (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ ((i : ℝ) + 1)) n)
    _ = (Nat.choose (n + 1) 2 : ℝ) := sum_range_initial_segment_eq_choose n

/-- Every point of the `n`th permutahedron lies in the hyperplane where the sum of the coordinates
is `\binom{n + 1}{2}`. -/
theorem permutahedron_subset_constant_sum_hyperplane (n : ℕ) :
    permutahedron n ⊆ {x : Fin n → ℝ | ∑ i, x i = (Nat.choose (n + 1) 2 : ℝ)} := by
  -- The target hyperplane is convex, so it is enough to check the permutahedron vertices.
  rw [permutahedron_eq_convexHull]
  refine convexHull_min ?_ ?_
  · intro x hx
    rcases mem_permutahedron_vertices_iff.mp hx with ⟨σ, rfl⟩
    -- Reindexing by a permutation preserves the coordinate sum of the ascending vector.
    have hsum :
        ∑ i, (ascending_vector n ∘ σ) i = ∑ i, ascending_vector n i := by
      simpa [Function.comp_apply] using
        (Equiv.sum_comp (e := σ) (g := fun i : Fin n ↦ ascending_vector n i))
    change ∑ i, (ascending_vector n ∘ σ) i = (Nat.choose (n + 1) 2 : ℝ)
    rw [hsum]
    simpa using ascending_vector_sumCoords n
  · -- The hyperplane is a linear preimage of a singleton, hence convex.
    simpa [Set.preimage] using
      (convex_singleton (Nat.choose (n + 1) 2 : ℝ)).linear_preimage
        ((Pi.basisFun ℝ (Fin n)).sumCoords)

/-- Helper for Example 3.20: the direction of the permutahedron affine span is contained in the
kernel of coordinate sum. -/
private lemma permutahedron_direction_le_sumCoords_ker (n : ℕ) :
    (affineSpan ℝ (permutahedron n)).direction ≤
      LinearMap.ker (Pi.basisFun ℝ (Fin n)).sumCoords := by
  let H : AffineSubspace ℝ (Fin n → ℝ) :=
    AffineSubspace.mk' (ascending_vector n) (LinearMap.ker (Pi.basisFun ℝ (Fin n)).sumCoords)
  have hperm_le_H : permutahedron n ⊆ H := by
    intro x hx
    change x ∈ H
    rw [AffineSubspace.mem_mk']
    refine LinearMap.mem_ker.2 ?_
    -- Every permutahedron point and the base vertex have the same coordinate sum.
    have hx_sum :
        (Pi.basisFun ℝ (Fin n)).sumCoords x = (Nat.choose (n + 1) 2 : ℝ) := by
      simpa using permutahedron_subset_constant_sum_hyperplane n hx
    rw [vsub_eq_sub, map_sub, hx_sum, ascending_vector_sumCoords n, sub_self]
  have h_aff_le : affineSpan ℝ (permutahedron n) ≤ H := (affineSpan_le).2 hperm_le_H
  -- Passing to directions turns affine containment into linear containment.
  simpa [H] using AffineSubspace.direction_le h_aff_le

/-- Helper for Example 3.20: every basis difference against the `0`th coordinate lies in the
direction of the permutahedron. -/
private lemma basis_difference_mem_permutahedron_direction (n : ℕ) (i : Fin (n + 1)) :
    Pi.single i (1 : ℝ) - Pi.single 0 1 ∈
      (affineSpan ℝ (permutahedron (n + 1))).direction := by
  by_cases hi : i = 0
  · -- The distinguished basis difference is zero.
    subst hi
    simp
  have hbase_mem :
      ascending_vector (n + 1) ∈ affineSpan ℝ (permutahedron (n + 1)) := by
    exact subset_affineSpan ℝ (permutahedron (n + 1))
      (ascending_vector_mem_permutahedron (n + 1))
  have hswap_perm :
      ascending_vector (n + 1) ∘ Equiv.swap 0 i ∈ permutahedron (n + 1) := by
    exact subset_convexHull ℝ (permutahedron_vertices (n + 1))
      (mem_permutahedron_vertices_iff.mpr ⟨Equiv.swap 0 i, rfl⟩)
  have hswap_mem :
      ascending_vector (n + 1) ∘ Equiv.swap 0 i ∈
        affineSpan ℝ (permutahedron (n + 1)) := by
    exact subset_affineSpan ℝ (permutahedron (n + 1)) hswap_perm
  have hdiff :
      ascending_vector (n + 1) ∘ Equiv.swap 0 i - ascending_vector (n + 1) ∈
        (affineSpan ℝ (permutahedron (n + 1))).direction := by
    -- Differences of points in the affine span belong to its direction.
    simpa using AffineSubspace.vsub_mem_direction hswap_mem hbase_mem
  have hiR : (i : ℝ) ≠ 0 := by
    have hiPos : 0 < (i : ℕ) := Fin.pos_iff_ne_zero.2 hi
    have hiPosR : 0 < (i : ℝ) := by exact_mod_cast hiPos
    exact ne_of_gt hiPosR
  have hswap :
      ascending_vector (n + 1) ∘ Equiv.swap 0 i - ascending_vector (n + 1) =
        (i : ℝ) • (Pi.single 0 (1 : ℝ) - Pi.single i 1) := by
    -- Swapping coordinates `0` and `i` changes exactly those two entries.
    ext j
    by_cases hj0 : j = 0
    · subst hj0
      simp [ascending_vector, hi, Equiv.swap_apply_left]
    · by_cases hji : j = i
      · subst hji
        simp [ascending_vector, hi, Equiv.swap_apply_right]
      · simp [Function.comp_apply, ascending_vector, hj0, hji,
          Equiv.swap_apply_of_ne_of_ne]
  have hbasic :
      Pi.single 0 (1 : ℝ) - Pi.single i 1 ∈
        (affineSpan ℝ (permutahedron (n + 1))).direction := by
    have hscaled :=
      Submodule.smul_mem (affineSpan ℝ (permutahedron (n + 1))).direction ((i : ℝ)⁻¹) hdiff
    rw [hswap] at hscaled
    -- Divide by the nonzero scalar produced by the swap computation.
    simpa [smul_smul, hiR] using hscaled
  -- Negating the previous vector gives the desired basis difference.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    Submodule.neg_mem (affineSpan ℝ (permutahedron (n + 1))).direction hbasic

/-- Helper for Example 3.20: a sum-zero vector is the finite sum of the basis differences against
the `0`th coordinate. -/
private lemma eq_sum_smul_basis_difference_of_sumCoords_zero {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : (Pi.basisFun ℝ (Fin (n + 1))).sumCoords x = 0) :
    x = ∑ i, x i • (Pi.single i (1 : ℝ) - Pi.single 0 1) := by
  have hrepr : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
    -- Expand `x` in the standard basis of `Fin (n + 1) → ℝ`.
    simpa using ((Pi.basisFun ℝ (Fin (n + 1))).sum_repr x).symm
  have hsum_zero : ∑ i, x i = 0 := by
    simpa using hx
  have hzero_term : ∑ i, x i • Pi.single 0 (1 : ℝ) = (0 : Fin (n + 1) → ℝ) := by
    -- The sum-zero hypothesis kills the common `0`th basis vector contribution.
    rw [← Finset.sum_smul, hsum_zero, zero_smul]
  calc
    x = ∑ i, x i • Pi.single i (1 : ℝ) := hrepr
    _ = ∑ i, x i • Pi.single i (1 : ℝ) - 0 := by
      simp
    _ = ∑ i, x i • Pi.single i (1 : ℝ) - ∑ i, x i • Pi.single 0 (1 : ℝ) := by
      exact congrArg
        (fun t : Fin (n + 1) → ℝ ↦ (∑ i, x i • Pi.single i (1 : ℝ)) - t)
        hzero_term.symm
    _ = ∑ i, (x i • Pi.single i (1 : ℝ) - x i • Pi.single 0 (1 : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
    _ = ∑ i, x i • (Pi.single i (1 : ℝ) - Pi.single 0 1) := by
      -- Each summand factors through the common scalar `x i`.
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [smul_sub]

/-- Helper for Example 3.20: the kernel of the coordinate-sum functional is contained in the
direction of the permutahedron affine span. -/
private lemma sumCoords_ker_le_permutahedron_direction (n : ℕ) :
    LinearMap.ker (Pi.basisFun ℝ (Fin (n + 1))).sumCoords ≤
      (affineSpan ℝ (permutahedron (n + 1))).direction := by
  intro x hx
  have hx0 : (Pi.basisFun ℝ (Fin (n + 1))).sumCoords x = 0 := by
    simpa using hx
  -- Reconstruct the vector from swap-generated basis differences.
  rw [eq_sum_smul_basis_difference_of_sumCoords_zero hx0]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _ (basis_difference_mem_permutahedron_direction n i)

/-- The direction of the affine span of the `n`th permutahedron is the hyperplane of vectors
whose coordinates sum to `0`. -/
theorem permutahedron_direction_eq_sumCoords_ker (n : ℕ) :
    (affineSpan ℝ (permutahedron n)).direction =
      LinearMap.ker (Pi.basisFun ℝ (Fin n)).sumCoords := by
  cases n with
  | zero =>
      -- In dimension zero both subspaces are forced to agree.
      refine le_antisymm ?_ ?_
      · intro x hx
        have hx0 : x = 0 := Subsingleton.elim _ _
        simp [hx0, LinearMap.mem_ker]
      · intro x hx
        have hx0 : x = 0 := Subsingleton.elim _ _
        simpa [hx0] using
          (show (0 : Fin 0 → ℝ) ∈ (affineSpan ℝ (permutahedron 0)).direction from
            Submodule.zero_mem _)
  | succ k =>
      -- Route correction: use the source-faithful hyperplane containment plus the basis-difference
      -- spanning argument, rather than searching for a direct dimension computation first.
      exact le_antisymm
        (permutahedron_direction_le_sumCoords_ker (k + 1))
        (sumCoords_ker_le_permutahedron_direction k)

/-- Helper for Example 3.20: the coordinate-sum kernel on `Fin n → ℝ` has dimension `n - 1`. -/
private lemma coordinate_sum_ker_finrank_fin (n : ℕ) :
    Module.finrank ℝ (LinearMap.ker (Pi.basisFun ℝ (Fin n)).sumCoords) = n - 1 := by
  cases n with
  | zero =>
      have hker : LinearMap.ker (Pi.basisFun ℝ (Fin 0)).sumCoords = ⊥ := by
        ext x
        have hx0 : x = 0 := Subsingleton.elim _ _
        simp [hx0, LinearMap.mem_ker]
      simp [hker]
  | succ k =>
      let f : Module.Dual ℝ (Fin (k + 1) → ℝ) := (Pi.basisFun ℝ (Fin (k + 1))).sumCoords
      have hf : f ≠ 0 := by
        -- Evaluating on a basis vector witnesses that the coordinate-sum functional is nonzero.
        intro hf
        have hzero : f (Pi.single 0 (1 : ℝ)) = 0 := by
          simp [f, hf]
        have hone : f (Pi.single 0 (1 : ℝ)) = 1 := by
          simp [f]
        exact zero_ne_one (hzero.symm.trans hone)
      have hker_add_one :
          Module.finrank ℝ (LinearMap.ker f) + 1 = k + 1 := by
        simpa [f, Module.finrank_fintype_fun_eq_card] using f.finrank_ker_add_one_of_ne_zero hf
      exact Nat.eq_sub_of_add_eq hker_add_one

/-- Example 3.20. The permutahedron `Π_n`, defined as the convex hull of the permutations of
`(1,2,\ldots,n)`, has dimension `n - 1`. -/
theorem permutahedron_finrank_direction_affineSpan (n : ℕ) :
    Module.finrank ℝ (affineSpan ℝ (permutahedron n)).direction = n - 1 := by
  -- Identify the direction with the coordinate-sum kernel, then compute the kernel dimension.
  rw [permutahedron_direction_eq_sumCoords_ker]
  exact coordinate_sum_ker_finrank_fin n
