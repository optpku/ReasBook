import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_20
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_theorem_6_30
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.max_linear_representation

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

section Corollary631

-- This corollary keeps the source-facing "maximum of linear functionals" statement, but now
-- phrases it through the reusable Section 6.3.2 owner
-- `HasMaxLinearRepresentationOfSizeLE` on the chapter's canonical gauge and dot-product API.

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_3_2/ch6_sec6_3_2_corollary_6_31.lean: the indices of a
centered facet presentation and the facets it presents have the same cardinality. -/
lemma IsCenteredFacetPresentation.indexCard_eq_facetsNcard
    {t : ℕ} {K : Set Rq} {xbar : Rq} {normals : Fin t → Rq}
    (hpresentation : IsCenteredFacetPresentation K xbar normals) :
    t = {F : Set Rq | IsFacetOf K F}.ncard := by
  -- Enumerate the facet set by the indexed equality faces of the presentation.
  symm
  refine Set.ncard_eq_of_bijective
    (fun i hi ↦ centered_facet_face xbar K (normals ⟨i, hi⟩)) ?_ ?_ ?_
  · intro F hF
    obtain ⟨i, hi, _hiUnique⟩ := hpresentation.existsUnique_index F hF
    exact ⟨i, i.isLt, hi.symm⟩
  · intro i hi
    exact hpresentation.isFacetOf ⟨i, hi⟩
  · intro i j hi hj hij
    exact congrArg Fin.val
      ((hpresentation.existsUnique_index
        (centered_facet_face xbar K (normals ⟨i, hi⟩))
        (hpresentation.isFacetOf ⟨i, hi⟩)).unique rfl hij)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_3_2/ch6_sec6_3_2_corollary_6_31.lean: the translated gauge
of a maximal lattice-free set has a max-linear representation with at most `2 ^ q` branches. -/
lemma maximalLatticeFreeGauge_hasMaxLinearRepresentationOfSizeLE
    {B : Set Rq} {f : Rq}
    (hB : is_maximal_lattice_free B)
    (hf : f ∈ interior B) :
    HasMaxLinearRepresentationOfSizeLE (2 ^ q) (gauge {r : Rq | f + r ∈ B}) := by
  -- The interior point makes `B` full-dimensional, so the polyhedral facet API applies.
  have hfull : affineSpan ℝ B = ⊤ :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hB.convex).1 ⟨f, hf⟩
  obtain ⟨hpoly, _hfree, _hfacets⟩ :=
    (maximal_lattice_free_iff_is_polyhedron_and_facets_meet_integer_lattice hfull).1 hB
  obtain ⟨t, ht, normals, hpresentation, _hunique⟩ :=
    exists_unique_centered_facet_presentation_up_to_reindexing hpoly hB.lattice_free hf
  -- Local instance justification (finite facet family): the presentation theorem returns the
  -- nonemptiness witness explicitly, while the finite-supremum API consumes it as an instance.
  letI : NeZero t := ht
  have htBound : t ≤ 2 ^ q := by
    -- The presentation has exactly one index per facet, and Theorem 6.19 bounds those facets.
    calc
      t = {F : Set Rq | IsFacetOf B F}.ncard := hpresentation.indexCard_eq_facetsNcard
      _ ≤ 2 ^ q := maximal_lattice_free_facets_ncard_le_two_pow hfull hB
  refine HasMaxLinearRepresentationOfSizeLE.of_isMaxLinearRepresentation
    (normals := normals) htBound ?_
  -- The translated-gauge computation identifies its branches with the centered facet normals.
  intro r
  exact gaugeTranslatedCenteredPolyhedron_eq_supFacetNormals hB.lattice_free hpresentation r

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_2/ch6_sec6_3_2_corollary_6_31.lean

Corollary 6.31 (3). Every minimal valid function for `R_f` admits a max-linear representation
on `ℝ^q` using at most `2^q` linear functionals. -/
theorem minimal_valid_function_for_continuous_infinite_relaxation_has_max_linear_bound
    (f : Rq) (ψ : Rq → ℝ)
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    HasMaxLinearRepresentationOfSizeLE (2 ^ q) ψ := by
  -- Theorem 6.30 supplies the controlling maximal lattice-free set and its translated gauge.
  obtain ⟨B, hB, hf, hψB⟩ := hψ.exists_maximal_integer_free_gauge
  rw [hψB]
  exact maximalLatticeFreeGauge_hasMaxLinearRepresentationOfSizeLE hB hf

end Corollary631

#print axioms minimal_valid_function_for_continuous_infinite_relaxation_has_max_linear_bound
