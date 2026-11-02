import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_example_3_36

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Domain sampling:
-- * primary domain: full-dimensional graph polytopes in the edge-coordinate space
-- * source-facing owner reused here: `cutPolytope`
-- * core/canonical ambient owners inspected: `affineSpan`, `Submodule.span`, `Pi.basisFun`
-- * nearby project precedent inspected: `stableSetPolytope_affineSpan_eq_top`
-- * primitive data reused here: `cutIncidenceVector`, `cutVertices`, `cutPolytope`
-- * derived bridge API reused here: `cutIncidenceVector_apply_pair`, `affineSpan_insert_zero`

-- This downstream exercise reuses the source-facing owner `cutPolytope` from Example 3.36 rather
-- than duplicating the cut-incidence model locally.

private lemma cutIncidenceVector_mem_cutPolytope {n : ℕ} (W : Finset (Fin n)) :
    cutIncidenceVector W ∈ cutPolytope n := by
  rw [cutPolytope]
  exact subset_convexHull ℝ (cutVertices n) ⟨W, rfl⟩

private lemma cutIncidenceVector_empty {n : ℕ} :
    cutIncidenceVector (∅ : Finset (Fin n)) = 0 := by
  ext e
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      rw [cutIncidenceVector_apply_pair (∅ : Finset (Fin n)) u v he]
      simp

private theorem basisFun_eq_half_singletons_sub_pair {n : ℕ} {u v : Fin n}
    (h : ¬ (s(u, v) : Sym2 (Fin n)).IsDiag) :
    Pi.basisFun ℝ (complete_graph_edges n) ⟨s(u, v), h⟩ =
      (1 / 2 : ℝ) •
        (cutIncidenceVector ({u} : Finset (Fin n)) + cutIncidenceVector ({v} : Finset (Fin n)) -
          cutIncidenceVector ({u, v} : Finset (Fin n))) := by
  have huv : u ≠ v := by
    simpa [Sym2.mk_isDiag_iff] using h
  ext e
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h x y =>
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply]
      rw [cutIncidenceVector_apply_pair ({u} : Finset (Fin n)) x y he]
      rw [cutIncidenceVector_apply_pair ({v} : Finset (Fin n)) x y he]
      rw [cutIncidenceVector_apply_pair ({u, v} : Finset (Fin n)) x y he]
      have hxy : x ≠ y := by
        simpa [Sym2.mk_isDiag_iff] using he
      by_cases hx : x ∈ ({u, v} : Finset (Fin n))
      · by_cases hy : y ∈ ({u, v} : Finset (Fin n))
        · have hx' : x = u ∨ x = v := by
            simpa using hx
          have hy' : y = u ∨ y = v := by
            simpa using hy
          have hsxy : (⟨s(x, y), he⟩ : complete_graph_edges n) = ⟨s(u, v), h⟩ := by
            apply Subtype.ext
            rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
            · cases hxy rfl
            · rfl
            · simp
            · cases hxy rfl
          rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
          · cases hxy rfl
          · norm_num [Pi.basisFun_apply, hsxy, hxy, eq_comm]
          · norm_num [Pi.basisFun_apply, hsxy, hxy, eq_comm]
          · cases hxy rfl
        · have hy' : y ≠ u ∧ y ≠ v := by
            simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using hy
          have hsxy : (⟨s(x, y), he⟩ : complete_graph_edges n) ≠ ⟨s(u, v), h⟩ := by
            intro hxy'
            have hsxy' : s(x, y) = s(u, v) := congrArg Subtype.val hxy'
            rw [Sym2.eq_iff] at hsxy'
            rcases hsxy' with hxy'' | hxy''
            · exact hy (by simp [hxy''.2])
            · exact hy (by simp [hxy''.2])
          have hx' : x = u ∨ x = v := by
            simpa using hx
          rcases hx' with rfl | rfl
          · simp [Pi.basisFun_apply, hsxy, hy'.1, hy'.2, huv]
          · simp [Pi.basisFun_apply, hsxy, hy'.1, hy'.2, huv, eq_comm]
      · by_cases hy : y ∈ ({u, v} : Finset (Fin n))
        · have hx' : x ≠ u ∧ x ≠ v := by
            simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using hx
          have hsxy : (⟨s(x, y), he⟩ : complete_graph_edges n) ≠ ⟨s(u, v), h⟩ := by
            intro hxy'
            have hsxy' : s(x, y) = s(u, v) := congrArg Subtype.val hxy'
            rw [Sym2.eq_iff] at hsxy'
            rcases hsxy' with hxy'' | hxy''
            · exact hx (by simp [hxy''.1])
            · exact hx (by simp [hxy''.1])
          have hy' : y = u ∨ y = v := by
            simpa using hy
          rcases hy' with rfl | rfl
          · simp [Pi.basisFun_apply, hsxy, hx'.1, hx'.2, huv]
          · simp [Pi.basisFun_apply, hsxy, hx'.1, hx'.2, huv, eq_comm]
        · have hx' : x ≠ u ∧ x ≠ v := by
            simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using hx
          have hy' : y ≠ u ∧ y ≠ v := by
            simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using hy
          have hsxy : (⟨s(x, y), he⟩ : complete_graph_edges n) ≠ ⟨s(u, v), h⟩ := by
            intro hxy'
            have hsxy' : s(x, y) = s(u, v) := congrArg Subtype.val hxy'
            rw [Sym2.eq_iff] at hsxy'
            rcases hsxy' with hxy'' | hxy''
            · exact hx (by simp [hxy''.1])
            · exact hx (by simp [hxy''.1])
          simp [Pi.basisFun_apply, hsxy, hx'.1, hx'.2, hy'.1, hy'.2]

private theorem basisFun_mem_span_cutPolytope {n : ℕ} (e : complete_graph_edges n) :
    Pi.basisFun ℝ (complete_graph_edges n) e ∈ Submodule.span ℝ (cutPolytope n) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      rw [basisFun_eq_half_singletons_sub_pair he]
      refine Submodule.smul_mem _ _ ?_
      have hu :
          cutIncidenceVector ({u} : Finset (Fin n)) ∈
            Submodule.span ℝ (cutPolytope n) :=
        Submodule.subset_span (cutIncidenceVector_mem_cutPolytope ({u} : Finset (Fin n)))
      have hv :
          cutIncidenceVector ({v} : Finset (Fin n)) ∈
            Submodule.span ℝ (cutPolytope n) :=
        Submodule.subset_span (cutIncidenceVector_mem_cutPolytope ({v} : Finset (Fin n)))
      have huv :
          cutIncidenceVector ({u, v} : Finset (Fin n)) ∈
            Submodule.span ℝ (cutPolytope n) :=
        Submodule.subset_span (cutIncidenceVector_mem_cutPolytope ({u, v} : Finset (Fin n)))
      exact Submodule.sub_mem _ (Submodule.add_mem _ hu hv) huv

/-- Exercise 3.20. The cut polytope from Example 3.36 is full-dimensional in its ambient space of
edge-coordinate functions. -/
theorem cutPolytope_affineSpan_eq_top (n : ℕ) :
    affineSpan ℝ (cutPolytope n) = ⊤ := by
  let P : Set (complete_graph_edges n → ℝ) := cutPolytope n
  have hzero_mem : (0 : complete_graph_edges n → ℝ) ∈ P := by
    simpa [P, cutIncidenceVector_empty] using
      cutIncidenceVector_mem_cutPolytope (∅ : Finset (Fin n))
  have h_aff :
      affineSpan ℝ P = (Submodule.span ℝ P).toAffineSubspace := by
    ext x
    rw [← Set.insert_eq_of_mem hzero_mem, Submodule.mem_toAffineSubspace]
    change x ∈ (affineSpan ℝ (insert 0 P) : Set (complete_graph_edges n → ℝ)) ↔
      x ∈ Submodule.span ℝ (insert 0 P)
    rw [affineSpan_insert_zero, Submodule.span_insert_zero]
    rfl
  have hspan : Submodule.span ℝ P = ⊤ := by
    refine top_unique ?_
    intro x _
    have hbasis :
        ∀ e : complete_graph_edges n,
          Pi.basisFun ℝ (complete_graph_edges n) e ∈ Submodule.span ℝ P := by
      intro e
      simpa [P] using basisFun_mem_span_cutPolytope e
    have hxrepr : x = ∑ e, x e • Pi.basisFun ℝ (complete_graph_edges n) e := by
      simpa using ((Pi.basisFun ℝ (complete_graph_edges n)).sum_repr x).symm
    rw [hxrepr]
    refine Submodule.sum_mem _ fun e _ ↦ ?_
    exact Submodule.smul_mem _ _ (hbasis e)
  calc
    affineSpan ℝ P = (Submodule.span ℝ P).toAffineSubspace := h_aff
    _ = (⊤ : Submodule ℝ (complete_graph_edges n → ℝ)).toAffineSubspace := by rw [hspan]
    _ = ⊤ := by
      ext x
      simp [Submodule.mem_toAffineSubspace]
