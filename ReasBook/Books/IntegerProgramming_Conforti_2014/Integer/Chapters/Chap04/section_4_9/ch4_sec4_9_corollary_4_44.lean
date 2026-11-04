/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_definition_3_15_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_lemma_4_41

open scoped BigOperators Matrix Pointwise

section Corollary444

variable {n : ℕ} {ι : Type*}

/-- Helper for Corollary 4.44: removing the empty members of a finite family does not change its
union. -/
lemma iUnion_filter_nonempty_eq_iUnion
    (s : Finset ι)
    (P : ι → Set (Fin n → ℝ))
    [DecidablePred fun i ↦ (P i).Nonempty] :
    (⋃ i ∈ s.filter (fun i ↦ (P i).Nonempty), P i) = ⋃ i ∈ s, P i := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hi, hxi⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨(Finset.mem_filter.1 hi).1, hxi⟩⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hi, hxi⟩
    have hnonempty : (P i).Nonempty := ⟨x, hxi⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_filter.2 ⟨hi, hnonempty⟩, hxi⟩⟩

/-- Helper for Corollary 4.44: the range of a function on a finite type is the finite image of
`Finset.univ`. -/
lemma range_eq_image_univ
    {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) :
    Set.range f = (Finset.univ.image f : Set β) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact Finset.mem_image.2 ⟨x, by simp, rfl⟩
  · intro hy
    rcases Finset.mem_image.1 hy with ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩

/-- Helper for Corollary 4.44: the empty set is a polyhedron, realized as the sum of the empty
polytope with any finitely generated cone. -/
lemma is_polyhedron_empty_set :
    is_polyhedron (∅ : Set (Fin n → ℝ)) := by
  have hempty_polytope : (∅ : Set (Fin n → ℝ)).IsPolytope ℝ := by
    exact ⟨∅, Set.finite_empty, by simp [convexHull_empty]⟩
  -- The backward direction of Minkowski-Weyl closes the empty-family branch immediately.
  refine (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).2 ?_
  refine ⟨∅, hempty_polytope, 0, (fun i : Fin 0 ↦ nomatch i), ?_⟩
  ext x
  simp

/-- Helper for Corollary 4.44: in a presentation `P = Q + cone(rays)`, every point of the ray cone
is a recession direction of `P`. -/
lemma finitely_generated_cone_subset_recessionCone_of_add
    {Q P : Set (Fin n → ℝ)} {q : ℕ} {rays : Fin q → Fin n → ℝ}
    (hP : P = Q + finitely_generated_cone rays) :
    finitely_generated_cone rays ⊆ recessionCone P := by
  intro r hr
  rw [mem_recessionCone_iff]
  intro x hx a ha
  rw [hP] at hx ⊢
  rcases hx with ⟨qv, hqv, y, hy, rfl⟩
  refine ⟨qv, hqv, y + a • r, finitely_generated_cone_add_smul_mem rays hy hr ha, ?_⟩
  simp [add_assoc]

/-- Corollary 4.44. If the sets `Pᵢ` form a finite family of polyhedra with identical recession
cones, then `conv (⋃ i, Pᵢ)` is a polyhedron. -/
theorem convexHull_iUnion_polyhedra_is_polyhedron_of_identical_recessionCone
    (s : Finset ι)
    (P : ι → Set (Fin n → ℝ))
    (hP_polyhedron : ∀ i ∈ s, is_polyhedron (P i))
    (hP_recession : ∀ i ∈ s, ∀ j ∈ s, recessionCone (P i) = recessionCone (P j)) :
    is_polyhedron (convexHull ℝ (⋃ i ∈ s, P i)) := by
  classical
  let t : Finset ι := s.filter (fun i ↦ (P i).Nonempty)
  by_cases ht : t.Nonempty
  · let e : Fin t.card ≃ ↥t := (Finset.equivFin t).symm
    let Pactive : Fin t.card → Set (Fin n → ℝ) := fun j ↦ P (e j).1
    have hPactive_nonempty : ∀ j : Fin t.card, (Pactive j).Nonempty := by
      intro j
      exact (Finset.mem_filter.1 (e j).2).2
    have hPactive_polyhedron : ∀ j : Fin t.card, is_polyhedron (Pactive j) := by
      intro j
      exact hP_polyhedron (e j).1 (Finset.mem_filter.1 (e j).2).1
    have hPactive_matrix :
        ∀ j : Fin t.card, ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℝ, ∃ b : Fin m → ℝ,
          Pactive j = polyhedron_le_set A b := by
      intro j
      exact hPactive_polyhedron j
    choose m A b hAb using hPactive_matrix
    have hdecomp :
        ∀ j : Fin t.card,
          ∃ Vj : Finset (Fin n → ℝ), ∃ qj : ℕ, ∃ raysj : Fin qj → Fin n → ℝ,
            Pactive j = convexHull ℝ (Vj : Set (Fin n → ℝ)) + finitely_generated_cone raysj := by
      intro j
      rcases
          (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).1 (hPactive_polyhedron j) with
        ⟨Q, hQ_polytope, qj, raysj, hreprQ⟩
      rcases hQ_polytope with ⟨V, hV_finite, hQ⟩
      let sV : Finset (Fin n → ℝ) := hV_finite.toFinset
      let eV : Fin sV.card ≃ ↥(sV : Set (Fin n → ℝ)) := (Finset.equivFin sV).symm
      let v : Fin sV.card → Fin n → ℝ := fun i ↦ (eV i).1
      have hV_range : Set.range v = V := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          simpa [sV] using (eV i).2
        · intro hx
          have hx' : x ∈ (sV : Set (Fin n → ℝ)) := by
            simpa [sV] using hx
          exact ⟨eV.symm ⟨x, hx'⟩, by simp [v]⟩
      have hsV_image : (Finset.univ.image v : Set (Fin n → ℝ)) = (sV : Set (Fin n → ℝ)) := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_image.1 hx with ⟨i, -, hix⟩
          rw [← hix]
          exact (eV i).2
        · intro hx
          exact Finset.mem_image.2 ⟨eV.symm ⟨x, hx⟩, by simp, by simp [v]⟩
      have hrepr :
          Pactive j = convexHull ℝ (sV : Set (Fin n → ℝ)) + finitely_generated_cone raysj := by
        calc
          Pactive j = Q + finitely_generated_cone raysj := hreprQ
          _ = convexHull ℝ V + finitely_generated_cone raysj := by rw [hQ]
          _ = convexHull ℝ (Set.range v) + finitely_generated_cone raysj := by rw [← hV_range]
          _ = convexHull ℝ (Finset.univ.image v : Set (Fin n → ℝ)) +
                finitely_generated_cone raysj := by
                rw [range_eq_image_univ v]
          _ = convexHull ℝ (sV : Set (Fin n → ℝ)) + finitely_generated_cone raysj := by
                rw [hsV_image]
      exact ⟨sV, qj, raysj, hrepr⟩
    choose V q rays hrepr_fg using hdecomp
    have ht_card_pos : 0 < t.card := Finset.card_pos.mpr ht
    let j0 : Fin t.card := ⟨0, ht_card_pos⟩
    let R : Fin t.card → Finset (Fin n → ℝ) := fun j ↦ Finset.univ.image (rays j)
    let Q : Set (Fin n → ℝ) := convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ))
    let C : Set (Fin n → ℝ) := recessionCone (Pactive j0)
    have hR_eq :
        ∀ j : Fin t.card,
          (PointedCone.hull ℝ (R j : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) =
            finitely_generated_cone (rays j) := by
      intro j
      calc
        (PointedCone.hull ℝ (R j : Set (Fin n → ℝ)) : Set (Fin n → ℝ))
            = cone (R j : Set (Fin n → ℝ)) := by simp [pointedCone_hull_eq_cone]
        _ = cone (Set.range (rays j)) := by rw [← range_eq_image_univ (rays j)]
        _ = finitely_generated_cone (rays j) := by rfl
    have hrepr :
        ∀ j : Fin t.card,
          Pactive j = convexHull ℝ (V j : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (R j : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
      intro j
      calc
        Pactive j = convexHull ℝ (V j : Set (Fin n → ℝ)) + finitely_generated_cone (rays j) :=
          hrepr_fg j
        _ = convexHull ℝ (V j : Set (Fin n → ℝ)) +
              (PointedCone.hull ℝ (R j : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
            rw [← hR_eq j]
    have hcone_subset_recession :
        ∀ j : Fin t.card,
          (PointedCone.hull ℝ (R j : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) ⊆
            recessionCone (Pactive j) := by
      intro j r hr
      rw [hR_eq j] at hr
      exact finitely_generated_cone_subset_recessionCone_of_add (hrepr_fg j) hr
    have hPactive_recession :
        ∀ j : Fin t.card, recessionCone (Pactive j) = C := by
      intro j
      dsimp [C, Pactive]
      exact hP_recession (e j).1 (Finset.mem_filter.1 (e j).2).1
        (e j0).1 (Finset.mem_filter.1 (e j0).2).1
    have hUnion_active :
        (⋃ j : Fin t.card, Pactive j) = ⋃ i ∈ t, P i := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨j, hxj⟩
        exact Set.mem_iUnion.2 ⟨(e j).1, Set.mem_iUnion.2 ⟨(e j).2, by simpa [Pactive] using hxj⟩⟩
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
        rcases Set.mem_iUnion.1 hx with ⟨hi, hxi⟩
        exact Set.mem_iUnion.2 ⟨e.symm ⟨i, hi⟩, by simpa [Pactive] using hxi⟩
    have hUnion_eq :
        (⋃ j : Fin t.card, Pactive j) = ⋃ i ∈ s, P i := by
      calc
        (⋃ j : Fin t.card, Pactive j) = ⋃ i ∈ t, P i := hUnion_active
        _ = ⋃ i ∈ s, P i := iUnion_filter_nonempty_eq_iUnion s P
    have hForward :
        convexHull ℝ (⋃ j : Fin t.card, Pactive j) ⊆ Q + C := by
      have hUnionSubset :
          (⋃ j : Fin t.card, Pactive j) ⊆ Q + C := by
        intro x hx
        rcases Set.mem_iUnion.1 hx with ⟨j, hxj⟩
        rw [hrepr j] at hxj
        rcases hxj with ⟨v, hv, r, hr, rfl⟩
        refine ⟨v, convexHull_subset_biUnion V j hv, r, ?_, rfl⟩
        have hr_rec : r ∈ recessionCone (Pactive j) := hcone_subset_recession j hr
        simpa [hPactive_recession j] using hr_rec
      have hConvex : Convex ℝ (Q + C) := by
        -- The common Minkowski sum is convex because both summands are convex.
        dsimp [Q, C]
        simpa using (convex_convexHull ℝ (Finset.univ.biUnion V : Set (Fin n → ℝ))).add
          (PointedCone.convex (recessionPointedCone ℝ (Pactive j0)))
      exact convexHull_min hUnionSubset hConvex
    have hReverse :
        Q + C ⊆ convexHull ℝ (⋃ j : Fin t.card, Pactive j) := by
      intro x hx
      rcases hx with ⟨qv, hqv, c, hc, rfl⟩
      rcases exists_indexed_convex_decomposition_of_mem_convexHull_biUnion
          Pactive hPactive_nonempty V R hrepr hqv with
        ⟨coeff, v, hcoeff_nonneg, hcoeff_sum, hv_mem, hqv_eq⟩
      have hterms_mem :
          ∀ j : Fin t.card, v j + c ∈ convexHull ℝ (⋃ j : Fin t.card, Pactive j) := by
        intro j
        have hvP : v j ∈ Pactive j := by
          rw [hrepr j]
          exact ⟨v j, hv_mem j, 0, by simp, by simp⟩
        have hcj : c ∈ recessionCone (Pactive j) := by
          simpa [hPactive_recession j] using hc
        have hj_mem : v j + c ∈ Pactive j := by
          -- The common recession direction can be added to every local convex-hull point.
          rw [mem_recessionCone_iff] at hcj
          simpa using hcj hvP 1 (by positivity)
        exact subset_convexHull ℝ _ (Set.mem_iUnion.2 ⟨j, hj_mem⟩)
      have hsum_mem :
          ∑ j : Fin t.card, coeff j • (v j + c) ∈ convexHull ℝ (⋃ j : Fin t.card, Pactive j) := by
        -- The direct source simplification is that the same cone vector `c` can be added in every
        -- block before taking the convex combination.
        exact (convex_convexHull ℝ _).sum_mem
          (fun j _ ↦ hcoeff_nonneg j)
          (by simpa using hcoeff_sum)
          (fun j _ ↦ hterms_mem j)
      have hsum_eq :
          ∑ j : Fin t.card, coeff j • (v j + c) = qv + c := by
        calc
          ∑ j : Fin t.card, coeff j • (v j + c)
              = ∑ j : Fin t.card, (coeff j • v j + coeff j • c) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  rw [smul_add]
          _ = (∑ j : Fin t.card, coeff j • v j) + ∑ j : Fin t.card, coeff j • c := by
                rw [Finset.sum_add_distrib]
          _ = qv + (∑ j : Fin t.card, coeff j) • c := by
                rw [hqv_eq, Finset.sum_smul]
          _ = qv + c := by simp [hcoeff_sum]
      rw [hsum_eq] at hsum_mem
      exact hsum_mem
    have hC_polyhedral : is_polyhedral_cone C := by
      have hrec_hom :
          C = {r : Fin n → ℝ | A j0 *ᵥ r ≤ 0} := by
        dsimp [C]
        simpa [hAb j0] using
          polyhedron_recessionCone_eq_homogeneous_solution_set (A j0) (b j0)
            (by simpa [hAb j0] using hPactive_nonempty j0)
      rw [hrec_hom]
      exact (is_polyhedral_cone_iff).2 ⟨m j0, A j0, rfl⟩
    have hC_fg :
        ∃ k : ℕ, ∃ commonRays : Fin k → Fin n → ℝ,
          C = finitely_generated_cone commonRays := by
      rcases (finitely_generated_cone_iff_polyhedral_cone).mpr hC_polyhedral with
        ⟨k, M, hM⟩
      refine ⟨k, fun j i ↦ M i j, ?_⟩
      calc
        C = (matrix_cone M : Set (Fin n → ℝ)) := hM
        _ = finitely_generated_cone (fun j i ↦ M i j) := by
            symm
            exact finitely_generated_cone_eq_matrix_cone (fun j i ↦ M i j)
    have hExact :
        convexHull ℝ (⋃ j : Fin t.card, Pactive j) = Q + C := by
      exact Set.Subset.antisymm hForward hReverse
    have hQ_polytope : Q.IsPolytope ℝ := by
      exact ⟨(Finset.univ.biUnion V : Set (Fin n → ℝ)),
        (Finset.univ.biUnion V).finite_toSet, rfl⟩
    have hQC_polyhedron : is_polyhedron (Q + C) := by
      -- Route correction: once the exact equality with one common cone is proved, the remaining
      -- step is the backward direction of Theorem 3.13.
      rcases hC_fg with ⟨k, commonRays, hC_eq⟩
      refine (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).2 ?_
      refine ⟨Q, hQ_polytope, k, commonRays, ?_⟩
      simp [hC_eq]
    rw [← hUnion_eq]
    rw [hExact]
    exact hQC_polyhedron
  · have ht_empty : t = ∅ := Finset.not_nonempty_iff_eq_empty.1 ht
    have hUnion_empty : (⋃ i ∈ s, P i) = (∅ : Set (Fin n → ℝ)) := by
      calc
        (⋃ i ∈ s, P i) = ⋃ i ∈ t, P i := (iUnion_filter_nonempty_eq_iUnion s P).symm
        _ = ∅ := by simp [ht_empty]
    -- With no active members, the union is empty and so is its convex hull.
    rw [hUnion_empty, convexHull_empty]
    exact is_polyhedron_empty_set

end Corollary444
