import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13

open scoped Pointwise

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Corollary 3.14: every polytope is bounded because finite sets are bounded and
their convex hull preserves boundedness. -/
theorem Set.IsPolytope.isBounded {n : ℕ} {Q : Set (Fin n → ℝ)} (hQ : Q.IsPolytope ℝ) :
    Bornology.IsBounded Q := by
  rcases hQ with ⟨V, hV, rfl⟩
  -- Reduce to the finite vertex set and use boundedness of convex hulls.
  exact (isBounded_convexHull).2 hV.isBounded

/-- Helper for Corollary 3.14: a bounded cone in `ℝ^n` can only contain the zero vector. -/
lemma cone_eq_singleton_zero_of_isBounded
    {n : ℕ} {C : Set (Fin n → ℝ)} [IsCone C] (hC : Bornology.IsBounded C) :
    C = {0} := by
  ext x
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Set.mem_singleton_iff.mpr hx0
    · -- If a nonzero vector lay in the cone, scaling it far enough would violate boundedness.
      obtain ⟨R, hR⟩ := hC.subset_closedBall (0 : Fin n → ℝ)
      have hzero_mem : (0 : Fin n → ℝ) ∈ C := IsCone.zero_mem (R := ℝ) (C := C)
      have hR_nonneg : 0 ≤ R := by
        have hzero_ball : (0 : Fin n → ℝ) ∈ Metric.closedBall (0 : Fin n → ℝ) R := hR hzero_mem
        simpa [Metric.mem_closedBall] using hzero_ball
      have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hx_norm_ne : ‖x‖ ≠ 0 := ne_of_gt hx_norm_pos
      have ht_nonneg : 0 ≤ R / ‖x‖ + 1 := by positivity
      have htx_mem : ((R / ‖x‖ + 1) • x) ∈ C := IsCone.smul_mem' hx ht_nonneg
      have hmem_ball :
          ((R / ‖x‖ + 1) • x) ∈ Metric.closedBall (0 : Fin n → ℝ) R := hR htx_mem
      have htx_bound : ‖(R / ‖x‖ + 1) • x‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hmem_ball
      have htx_norm : ‖(R / ‖x‖ + 1) • x‖ = R + ‖x‖ := by
        calc
          ‖(R / ‖x‖ + 1) • x‖ = |R / ‖x‖ + 1| * ‖x‖ := norm_smul _ _
          _ = (R / ‖x‖ + 1) * ‖x‖ := by rw [abs_of_nonneg ht_nonneg]
          _ = (R / ‖x‖) * ‖x‖ + ‖x‖ := by rw [add_mul, one_mul]
          _ = R + ‖x‖ := by rw [div_mul_cancel₀ _ hx_norm_ne]
      have hlarge : R + ‖x‖ ≤ R := by
        simpa [htx_norm] using htx_bound
      linarith
  · intro hx
    -- Conversely, the zero vector is always in a cone.
    have hzero_mem : (0 : Fin n → ℝ) ∈ C := IsCone.zero_mem (R := ℝ) (C := C)
    have hx_zero : x = 0 := Set.mem_singleton_iff.mp hx
    subst hx_zero
    simpa using hzero_mem

/-- Helper for Corollary 3.14: if a translate of `C` sits inside a bounded set, then `C` is
bounded as well. -/
lemma bounded_translate_of_subset_minkowski_sum
    {n : ℕ} {q : Fin n → ℝ} {C P : Set (Fin n → ℝ)}
    (hsubset : ({q} + C) ⊆ P) (hP : Bornology.IsBounded P) :
    Bornology.IsBounded C := by
  -- Bound the translated copy `{q} + C` by a ball,
  -- then pull the bound back with the triangle inequality.
  obtain ⟨r, hr_pos, hrP⟩ := hP.subset_ball_lt 0 (0 : Fin n → ℝ)
  exact Bornology.IsBounded.subset
    (show Bornology.IsBounded (Metric.ball (0 : Fin n → ℝ) (r + ‖q‖)) from Metric.isBounded_ball)
    (by
      intro x hx
      have hx_sum_mem : q + x ∈ {q} + C := by
        exact ⟨q, Set.mem_singleton q, x, hx, rfl⟩
      have hxP : q + x ∈ P := hsubset hx_sum_mem
      have hx_translated : ‖q + x‖ < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hrP hxP
      have hx_decomp : x = (q + x) + (-q) := by
        ext i
        simp
      have hx_norm_le : ‖x‖ ≤ ‖q + x‖ + ‖q‖ := by
        rw [hx_decomp]
        simpa using norm_add_le (q + x) (-q)
      have hx_norm_lt : ‖x‖ < r + ‖q‖ := by
        linarith
      simpa [Metric.mem_ball, dist_eq_norm] using hx_norm_lt)

/-- Corollary 3.14. (Minkowski-Weyl Theorem for Polytopes) A set `Q ⊆ ℝ^n` is a polytope if
and only if `Q` is a bounded polyhedron. -/
theorem polytope_iff_bounded_polyhedron {n : ℕ} (Q : Set (Fin n → ℝ)) :
    Q.IsPolytope ℝ ↔ is_polyhedron Q ∧ Bornology.IsBounded Q := by
  constructor
  · intro hQ
    constructor
    · -- Use the Minkowski-Weyl decomposition with the zero cone
      -- to obtain a polyhedral presentation.
      refine
        (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).2
          ⟨Q, hQ, 0, Fin.elim0, ?_⟩
      ext x
      constructor
      · intro hx
        have hzero_mem :
            (0 : Fin n → ℝ) ∈ finitely_generated_cone (Fin.elim0 : Fin 0 → Fin n → ℝ) := by
          simp [finitely_generated_cone, cone_empty]
        exact ⟨x, hx, 0, hzero_mem, by simp⟩
      · intro hx
        rcases hx with ⟨y, hy, z, hz, hsum⟩
        have hz_zero : z = 0 := by
          have hz_mem_zero : z ∈ ({0} : Set (Fin n → ℝ)) := by
            simpa [finitely_generated_cone, cone_empty] using hz
          exact Set.mem_singleton_iff.mp hz_mem_zero
        have hy_eq_x : y = x := by
          simpa [hz_zero] using hsum
        simpa [hy_eq_x] using hy
    · -- Finite convex hulls are bounded.
      exact hQ.isBounded
  · intro hQ
    rcases hQ with ⟨hpolyhedron, hbounded⟩
    rcases (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).1 hpolyhedron with
      ⟨_, hP_polytope, q, rays, hQeq⟩
    rcases hP_polytope with ⟨V, hV_finite, hVeq⟩
    by_cases hV : V = ∅
    · -- If the polytope part is empty, then the whole Minkowski sum is empty.
      refine ⟨∅, Set.finite_empty, ?_⟩
      rw [hQeq, hVeq, hV]
      simp [convexHull_empty]
    · -- Otherwise choose a vertex `q` to expose a translated copy of the cone inside the set.
      have hV_nonempty : V.Nonempty := Set.nonempty_iff_ne_empty.mpr hV
      rcases hV_nonempty with ⟨q, hqV⟩
      have hq_conv : q ∈ convexHull ℝ V := subset_convexHull ℝ _ hqV
      have hcone_subset :
          ({q} + finitely_generated_cone rays) ⊆ convexHull ℝ V + finitely_generated_cone rays := by
        intro x hx
        rcases hx with ⟨q', hq', y, hy, hxy⟩
        have hq'_eq : q' = q := Set.mem_singleton_iff.mp hq'
        have hq'_conv : q' ∈ convexHull ℝ V := by
          simpa [hq'_eq] using hq_conv
        exact ⟨q', hq'_conv, y, hy, hxy⟩
      have hbounded_rhs :
          Bornology.IsBounded (convexHull ℝ V + finitely_generated_cone rays) := by
        simpa [hQeq, hVeq] using hbounded
      have hcone_bounded : Bornology.IsBounded (finitely_generated_cone rays) :=
        bounded_translate_of_subset_minkowski_sum hcone_subset hbounded_rhs
      have hcone_zero : finitely_generated_cone rays = {0} :=
        cone_eq_singleton_zero_of_isBounded hcone_bounded
      refine ⟨V, hV_finite, ?_⟩
      rw [hQeq, hVeq]
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, z, hz, hxyz⟩
        have hz_zero : z = 0 := by
          have hz_mem_zero : z ∈ ({0} : Set (Fin n → ℝ)) := by
            simpa [hcone_zero] using
              (show z ∈ finitely_generated_cone rays from hz)
          exact Set.mem_singleton_iff.mp hz_mem_zero
        have hy_eq_x : y = x := by
          simpa [hz_zero] using hxyz
        simpa [hy_eq_x] using hy
      · intro hx
        have hzero_mem : (0 : Fin n → ℝ) ∈ finitely_generated_cone rays := by
          simp [hcone_zero]
        exact ⟨x, hx, 0, hzero_mem, by simp⟩
