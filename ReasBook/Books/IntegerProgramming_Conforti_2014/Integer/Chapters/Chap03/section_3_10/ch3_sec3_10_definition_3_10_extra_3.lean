/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_33

open scoped Matrix

-- This source-facing file reuses the earlier Chapter 3 owners `linealitySpace` and `is_pointed`.
-- In the convex-geometry owner layer, vertices are already represented by `Set.extremePoints`.

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/- Definition 3.10-extra-3. In the canonical convex-geometry API, vertices of `P` are the points
of `P.extremePoints ℝ`, so the source phrase "`P` has a vertex" is exactly
`(P.extremePoints ℝ).Nonempty`. -/
recall Set.extremePoints

section PolyhedronVertices

variable {n : ℕ} {P : Set (Fin n → ℝ)}

/-- Helper for Definition 3.10-extra-3: a nonempty subset of `Fin n → ℝ` whose affine-span
direction has dimension `0` is a singleton. -/
lemma exists_eq_singleton_of_nonempty_finrank_direction_affineSpan_eq_zero
    {s : Set (Fin n → ℝ)}
    (hs_nonempty : s.Nonempty)
    (hs_dim : Module.finrank ℝ (affineSpan ℝ s).direction = 0) :
    ∃ x, s = ({x} : Set (Fin n → ℝ)) := by
  obtain ⟨x0, hx0s⟩ := hs_nonempty
  -- Zero-dimensional direction collapses the affine span to the singleton affine span through `x0`.
  have hdir : (affineSpan ℝ s).direction = ⊥ := by
    exact Submodule.finrank_eq_zero.mp hs_dim
  have hspan_eq : affineSpan ℝ s = affineSpan ℝ ({x0} : Set (Fin n → ℝ)) := by
    refine
      (AffineSubspace.eq_iff_direction_eq_of_mem
        (mem_affineSpan ℝ hx0s)
        (mem_affineSpan ℝ (Set.mem_singleton x0))).2 ?_
    simpa [direction_affineSpan, vectorSpan_singleton] using hdir
  refine ⟨x0, ?_⟩
  ext x
  constructor
  · intro hx
    -- Every point of `s` lies in the singleton affine span, hence equals the base point.
    have hx_span : x ∈ affineSpan ℝ s := mem_affineSpan ℝ hx
    rw [hspan_eq, AffineSubspace.mem_affineSpan_singleton] at hx_span
    simpa [Set.mem_singleton_iff] using hx_span
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hx0s

theorem polyhedron_extremePoints_nonempty_iff_is_pointed
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty) :
    (P.extremePoints ℝ).Nonempty ↔ is_pointed P := by
  rcases hP_polyhedron with ⟨m, A, b, rfl⟩
  constructor
  · rintro ⟨x, hx_extreme⟩
    rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
    intro r hr
    rcases mem_extremePoints_iff_left.mp hx_extreme with ⟨hxP, hx_isExtreme⟩
    -- A lineality direction keeps both opposite translates of the extreme point
    -- inside the polyhedron.
    have hx_minus : x - r ∈ polyhedron_le_set A b := by
      simpa [sub_eq_add_neg] using (mem_linealitySpace_iff.mp hr) hxP (-1 : ℝ)
    have hx_plus : x + r ∈ polyhedron_le_set A b := by
      simpa using (mem_linealitySpace_iff.mp hr) hxP (1 : ℝ)
    have hx_open : x ∈ openSegment ℝ (x - r) (x + r) := by
      simpa using (mem_openSegment_sub_add (𝕜 := ℝ) x r)
    -- Extremality forces the left endpoint of that segment to be the extreme point itself.
    exact sub_eq_self.mp (hx_isExtreme (x - r) hx_minus (x + r) hx_plus hx_open)
  · intro hP_pointed
    have hlineality_eq_bot : linealitySubmodule (polyhedron_le_set A b) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro r hr
      exact
        (is_pointed_iff_eq_zero_of_mem_linealitySpace.mp hP_pointed) r
          (mem_linealitySubmodule_iff.mp hr)
    have hk_lineality :
        Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) ≤ 0 := by
      rw [hlineality_eq_bot]
      simp
    -- Theorem 3.33 (3) supplies a nonempty exposed face of affine dimension `0`.
    obtain ⟨F, hF_nonempty, hF_exposed, hF_dim⟩ :=
      exists_nonempty_face_of_finrank_between_linealitySpace_and_polyhedron
        A b hP_nonempty 0 hk_lineality (Nat.zero_le _)
    obtain ⟨x, hF_eq⟩ :=
      exists_eq_singleton_of_nonempty_finrank_direction_affineSpan_eq_zero
        hF_nonempty hF_dim
    have hsingleton_extreme :
        IsExtreme ℝ (polyhedron_le_set A b) ({x} : Set (Fin n → ℝ)) := by
      simpa [hF_eq] using hF_exposed.isExtreme
    -- A singleton exposed face identifies its unique point as an extreme point of the polyhedron.
    exact ⟨x, hsingleton_extreme.mem_extremePoints⟩

/-- For a nonempty polyhedron, having a vertex is equivalent to the nonemptiness of its extreme
points, and this criterion can be written as triviality of the lineality space. -/
theorem polyhedron_extremePoints_nonempty_iff_linealitySpace_eq_zero
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty) :
    (P.extremePoints ℝ).Nonempty ↔ linealitySpace P = ({0} : Set (Fin n → ℝ)) := by
  rw [← is_pointed_iff]
  exact polyhedron_extremePoints_nonempty_iff_is_pointed hP_polyhedron hP_nonempty

end PolyhedronVertices
