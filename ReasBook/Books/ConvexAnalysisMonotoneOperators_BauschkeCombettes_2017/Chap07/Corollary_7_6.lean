/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Example_6_43
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_45
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Proposition_7_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace Set

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [CompleteSpace 𝓗] in
private lemma normalCone_diff_singleton_nonempty_of_mem {C : Set 𝓗} {x : 𝓗} (hx : x ∈ C)
    (hN_ne : N[C] x ≠ ({0} : Set 𝓗)) :
    N[C] x \ ({0} : Set 𝓗) ≠ ∅ := by
  have hzero : (0 : 𝓗) ∈ N[C] x := by
    rw [normalCone_of_mem hx]
    simp [innerSupremumOn_eq_sSup_image]
  intro hdiff
  apply hN_ne
  refine Subset.antisymm ?_ (singleton_subset_iff.mpr hzero)
  rw [diff_eq_empty] at hdiff
  exact hdiff

/-- If a closed convex set has nonempty interior, then its support points are exactly its frontier.
-/
theorem supportPoints_eq_frontier_of_closed_convex_nonempty_interior {C : Set 𝓗}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_int_nonempty : (interior C).Nonempty) :
    spts C = frontier C := by
  refine Subset.antisymm ?_ ?_
  · intro x hx
    have hx_support : x ∈ spts C := hx
    rw [supportPoints_eq_setOf_nontrivial_normalCone] at hx
    have hxC : x ∈ C := by
      exact supportPoints_subset hx_support
    have hx_not_mem_interior : x ∉ interior C := by
      intro hx_int
      have hNx :
          N[C] x = ({0} : Set 𝓗) :=
        (mem_interior_iff_normalCone_eq_singleton_zero_of_convex hC_convex hC_int_nonempty hxC).1
          hx_int
      exact hx (by
        rw [hNx]
        simp)
    simp [frontier, hxC, hx_not_mem_interior]
  · intro x hx
    have hxC : x ∈ C := by
      simpa [frontier, hC_closed.closure_eq] using hx.1
    have hNx_ne :
        N[C] x ≠ ({0} : Set 𝓗) := by
      intro hNx
      exact hx.2 <|
        (mem_interior_iff_normalCone_eq_singleton_zero_of_convex
          hC_convex hC_int_nonempty hxC).2 hNx
    rw [supportPoints_eq_setOf_nontrivial_normalCone]
    exact normalCone_diff_singleton_nonempty_of_mem hxC hNx_ne

/-- A closed affine subspace has support points exactly at its frontier. -/
theorem supportPoints_eq_frontier_of_closed_affineSubspace {C : Set 𝓗}
    {A : AffineSubspace ℝ 𝓗} (hC_closed : IsClosed C)
    (hCA : C = (A : Set 𝓗)) :
    spts C = frontier C := by
  rcases eq_or_ne A ⊥ with hA_bot | hA_ne_bot
  · have hC_empty : C = ∅ := by simpa [hA_bot] using hCA
    simp [supportPoints, hC_empty, frontier]
  · rcases eq_or_ne A ⊤ with hA_top | hA_ne_top
    · have hC_univ : C = univ := by simpa [hA_top] using hCA
      have hconvex : Convex ℝ C := by simpa [hC_univ] using convex_univ
      have hC_int_nonempty : (interior C).Nonempty := by
        simp [hC_univ]
      simpa [hC_univ, frontier] using
        supportPoints_eq_frontier_of_closed_convex_nonempty_interior
          hC_closed hconvex hC_int_nonempty
    · have hA_nonempty : (A : Set 𝓗).Nonempty := by
        rcases eq_empty_or_nonempty (A : Set 𝓗) with hA_empty | hA_nonempty
        · exfalso
          apply hA_ne_bot
          rw [← AffineSubspace.coe_eq_bot_iff]
          exact hA_empty
        · exact hA_nonempty
      have hC_convex : Convex ℝ C := by simpa [hCA] using A.convex
      have hA_closed : IsClosed (A : Set 𝓗) := by
        simpa [← hCA] using hC_closed
      have hdir_closed : IsClosed (A.direction : Set 𝓗) := by
        exact (AffineSubspace.isClosed_direction_iff A).mpr hA_closed
      letI : IsClosed (A.direction : Set 𝓗) := hdir_closed
      letI : CompleteSpace A.direction := IsClosed.completeSpace_coe
      letI : A.direction.HasOrthogonalProjection := by
        infer_instance
      have hdir_ne_top : A.direction ≠ ⊤ := by
        intro hdir_top
        exact hA_ne_top <|
          (AffineSubspace.direction_eq_top_iff_of_nonempty hA_nonempty).mp hdir_top
      have horth_ne_bot : A.directionᗮ ≠ ⊥ := by
        intro horth_bot
        exact hdir_ne_top (Submodule.orthogonal_eq_bot_iff.mp horth_bot)
      obtain ⟨u, hu_mem, hu_ne⟩ := (Submodule.ne_bot_iff _).mp horth_ne_bot
      have hC_int_empty : interior C = ∅ := by
        refine not_nonempty_iff_eq_empty.mp ?_
        rintro ⟨x, hx_int⟩
        apply hA_ne_top
        have hconvHull_int : (interior (convexHull ℝ C)).Nonempty := by
          simpa [hC_convex.convexHull_eq] using ⟨x, hx_int⟩
        have hspan_top : affineSpan ℝ C = ⊤ :=
          affineSpan_eq_top_of_nonempty_interior hconvHull_int
        simpa [hCA, AffineSubspace.affineSpan_coe] using hspan_top
      have hspts : spts C = C := by
        ext x
        constructor
        · intro hx
          exact supportPoints_subset hx
        · intro hxC
          have hxA : x ∈ (A : Set 𝓗) := by simpa [hCA] using hxC
          rw [supportPoints_eq_setOf_nontrivial_normalCone]
          have hne :
              (((A.directionᗮ : Submodule ℝ 𝓗) : Set 𝓗) \ ({0} : Set 𝓗)) ≠ ∅ := by
            exact nonempty_iff_ne_empty.mp ⟨u, by simp [hu_mem, hu_ne]⟩
          simpa [hCA, normalCone_affineSubspace_eq_direction_orthogonal_of_mem A hxA] using hne
      have hfrontier : frontier C = C := by
        rw [frontier, hC_closed.closure_eq, hC_int_empty, diff_empty]
      rw [hspts, hfrontier]

omit [CompleteSpace 𝓗] in
/-- In finite dimension, a closed convex set has support points exactly at its frontier. -/
theorem supportPoints_eq_frontier_of_closed_convex_finiteDimensional {C : Set 𝓗}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) [FiniteDimensional ℝ 𝓗] :
    spts C = frontier C := by
  refine Subset.antisymm ?_ ?_
  · intro x hx
    have hx_support : x ∈ spts C := hx
    rw [supportPoints_eq_setOf_nontrivial_normalCone] at hx
    have hxC : x ∈ C := by
      exact supportPoints_subset hx_support
    have hx_not_mem_interior : x ∉ interior C := by
      intro hx_int
      have hNx :
          N[C] x = ({0} : Set 𝓗) :=
        (mem_interior_iff_normalCone_eq_singleton_zero_of_convex
          hC_convex ⟨x, hx_int⟩ hxC).1 hx_int
      exact hx (by
        rw [hNx]
        simp)
    simp [frontier, hxC, hx_not_mem_interior]
  · intro x hx
    have hxC : x ∈ C := by
      simpa [frontier, hC_closed.closure_eq] using hx.1
    have hNx_ne :
        N[C] x ≠ ({0} : Set 𝓗) := by
      intro hNx
      exact hx.2 <|
        (mem_interior_of_normalCone_eq_singleton_zero_of_convex_of_finiteDimensional
          hC_convex hxC hNx)
    rw [supportPoints_eq_setOf_nontrivial_normalCone]
    exact normalCone_diff_singleton_nonempty_of_mem hxC hNx_ne

-- Proof sketch: in case (i), combine the Bishop--Phelps boundary-density theorem with the
-- nonempty-interior support-point criterion to obtain both inclusions. In case (ii), identify the
-- closed affine subspace with a translate of its direction space and show each boundary point is a
-- projection point of some exterior point. In case (iii), if `interior C = ∅`, pass to the affine
-- hull of `C`, use finite dimensionality to make that hull a proper closed affine subspace, apply
-- case (ii) there, and then restrict support points back to `C`.
/-- Corollary 7.6: if `C` is a closed convex subset of a real Hilbert space and either
(i) `interior C` is nonempty, (ii) `C` is an affine subspace, or (iii) the ambient space is
finite-dimensional, then the support points of `C` are exactly the boundary of `C`. -/
theorem supportPoints_eq_frontier_of_closed_convex_of_interior_or_affine_or_finiteDimensional
    {C : Set 𝓗} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (h :
      (interior C).Nonempty ∨
        (∃ A : AffineSubspace ℝ 𝓗, C = (A : Set 𝓗)) ∨
        FiniteDimensional ℝ 𝓗) :
    spts C = frontier C := by
  rcases h with hC_int_nonempty | h_affine | hfd
  · exact supportPoints_eq_frontier_of_closed_convex_nonempty_interior
      hC_closed hC_convex hC_int_nonempty
  · rcases h_affine with ⟨A, hCA⟩
    exact supportPoints_eq_frontier_of_closed_affineSubspace hC_closed hCA
  · letI : FiniteDimensional ℝ 𝓗 := hfd
    exact supportPoints_eq_frontier_of_closed_convex_finiteDimensional hC_closed hC_convex

end Set
