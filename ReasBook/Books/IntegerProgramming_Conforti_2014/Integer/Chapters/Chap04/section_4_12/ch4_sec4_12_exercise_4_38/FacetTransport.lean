import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_1
import Mathlib.Analysis.Convex.KreinMilman

universe u

open Set

/-- Helper for Exercise 4.38: exposed faces transport through continuous linear equivalences by
pulling the exposing functional back along the inverse map. -/
lemma isExposed_image_continuousLinearEquiv
    {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F)
    {A B : Set E} (hAB : IsExposed ℝ A B) :
    IsExposed ℝ (e '' A) (e '' B) := by
  intro hB
  rcases hB with ⟨z, hz⟩
  rcases hz with ⟨x, hxB, rfl⟩
  obtain ⟨l, hl⟩ := hAB ⟨x, hxB⟩
  refine ⟨l.comp e.symm.toContinuousLinearMap, ?_⟩
  ext y
  constructor
  · intro hy
    rcases hy with ⟨u, hu, rfl⟩
    rw [hl] at hu
    refine ⟨?_, ?_⟩
    · exact ⟨u, hu.1, rfl⟩
    · intro v hv
      rcases hv with ⟨w, hwA, rfl⟩
      simpa using hu.2 w hwA
  · intro hy
    rcases hy with ⟨hyA, hyMax⟩
    rcases hyA with ⟨u, huA, rfl⟩
    have huB : u ∈ B := by
      rw [hl]
      refine ⟨huA, ?_⟩
      intro w hwA
      have hwImage : e w ∈ e '' A := ⟨w, hwA, rfl⟩
      simpa using hyMax (e w) hwImage
    exact ⟨u, huB, rfl⟩

/-- Helper for Exercise 4.38: continuous linear equivalences preserve the affine-span direction
dimension of a set. -/
lemma finrank_direction_affineSpan_image_continuousLinearEquiv
    {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃L[ℝ] F)
    (S : Set E) :
    Module.finrank ℝ (affineSpan ℝ (e '' S)).direction =
      Module.finrank ℝ (affineSpan ℝ S).direction := by
  let f : E →ᵃ[ℝ] F := e.toAffineEquiv.toAffineMap
  have hmap :
      affineSpan ℝ (e '' S) = (affineSpan ℝ S).map f := by
    symm
    simpa [f] using (AffineSubspace.map_span f S)
  rw [hmap, AffineSubspace.map_direction]
  simpa [f] using (LinearEquiv.finrank_map_eq e.toLinearEquiv (affineSpan ℝ S).direction)

/-- Helper for Exercise 4.38: facets transport through continuous linear equivalences. -/
lemma isFacetOf_image_continuousLinearEquiv
    {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃L[ℝ] F)
    {A B : Set E} :
    IsFacetOf A B ↔
      IsFacetOf ((((fun x : E ↦ (e : E → F) x) '' A) : Set F))
        ((((fun x : E ↦ (e : E → F) x) '' B) : Set F)) := by
  constructor
  · intro hB
    rcases isFacetOf_iff.mp hB with ⟨hB_nonempty, hB_exposed, hB_codim⟩
    have hcodim_image :
        Module.finrank ℝ (affineSpan ℝ (e '' B)).direction + 1 =
          Module.finrank ℝ (affineSpan ℝ (e '' A)).direction := by
      rw [finrank_direction_affineSpan_image_continuousLinearEquiv e B,
        finrank_direction_affineSpan_image_continuousLinearEquiv e A]
      exact hB_codim
    refine (isFacetOf_iff).2 ⟨?_, ?_, hcodim_image⟩
    · rcases hB_nonempty with ⟨x, hx⟩
      exact ⟨e x, ⟨x, hx, rfl⟩⟩
    · exact isExposed_image_continuousLinearEquiv e hB_exposed
  · intro hB
    rcases isFacetOf_iff.mp hB with ⟨hB_nonempty, hB_exposed, hB_codim⟩
    have hsymm_image_A : e.symm '' (e '' A) = A := by
      simp
    have hsymm_image_B : e.symm '' (e '' B) = B := by
      simp
    have hB_exposed_preimage :
        IsExposed ℝ (e.symm '' (e '' A)) (e.symm '' (e '' B)) := by
      simpa using isExposed_image_continuousLinearEquiv e.symm hB_exposed
    have hcodim_preimage :
        Module.finrank ℝ (affineSpan ℝ (e.symm '' (e '' B))).direction + 1 =
          Module.finrank ℝ (affineSpan ℝ (e.symm '' (e '' A))).direction := by
      rw [finrank_direction_affineSpan_image_continuousLinearEquiv e.symm (e '' B),
        finrank_direction_affineSpan_image_continuousLinearEquiv e.symm (e '' A)]
      exact hB_codim
    refine (isFacetOf_iff).2 ?_
    refine ⟨?_, ?_, ?_⟩
    · rcases hB_nonempty with ⟨y, hy⟩
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, hx⟩
    · simpa [hsymm_image_A, hsymm_image_B] using hB_exposed_preimage
    · rw [hsymm_image_B, hsymm_image_A] at hcodim_preimage
      exact hcodim_preimage

/-- Helper for Exercise 4.38: continuous linear equivalences send polytopes to polytopes. -/
lemma isPolytope_image_continuousLinearEquiv
    {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F)
    {Q : Set E}
    (hQ : Q.IsPolytope ℝ) :
    (e '' Q).IsPolytope ℝ := by
  rcases hQ with ⟨V, hV, hVQ⟩
  refine ⟨(e : E → F) '' V, hV.image e, ?_⟩
  calc
    e '' Q = e '' convexHull ℝ V := by rw [hVQ]
    _ = convexHull ℝ (e '' V) := by
          simpa using (LinearMap.image_convexHull e.toLinearMap V)

/-- Helper for Exercise 4.38: a compact exposed face is determined by its extreme points. -/
lemma exposed_face_eq_convexHull_extremePoints
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q F : Set E} (hQ : Q.IsPolytope ℝ) (hF : IsExposed ℝ Q F) :
    F = convexHull ℝ (F.extremePoints ℝ) := by
  rcases hQ with ⟨V, hV, hQV⟩
  have hFextreme_subset_vertices : F.extremePoints ℝ ⊆ V := by
    intro x hx
    have hxQext : x ∈ Q.extremePoints ℝ :=
      hF.isExtreme.extremePoints_subset_extremePoints hx
    rw [hQV] at hxQext
    exact extremePoints_convexHull_subset hxQext
  have hQcompact : IsCompact Q := by
    rw [hQV]
    exact hV.isCompact_convexHull ℝ
  have hFcompact : IsCompact F := hF.isCompact hQcompact
  have hFconvex : Convex ℝ F := hF.convex (by rw [hQV]; exact convex_convexHull ℝ V)
  have hclosure := closure_convexHull_extremePoints hFcompact hFconvex
  have hfinite_extreme : (F.extremePoints ℝ).Finite := hV.subset hFextreme_subset_vertices
  calc
    F = closure (convexHull ℝ (F.extremePoints ℝ)) := by simpa using hclosure.symm
    _ = convexHull ℝ (F.extremePoints ℝ) := by
      exact (hfinite_extreme.isClosed_convexHull ℝ).closure_eq

/-- Helper for Exercise 4.38: every exposed face of a polytope is itself a polytope. -/
lemma exposed_face_isPolytope
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q F : Set E} (hQ : Q.IsPolytope ℝ) (hF : IsExposed ℝ Q F) :
    F.IsPolytope ℝ := by
  rcases hQ with ⟨V, hV, hQV⟩
  refine ⟨F.extremePoints ℝ, ?_, ?_⟩
  · apply hV.subset
    intro x hx
    have hxQext : x ∈ Q.extremePoints ℝ :=
      hF.isExtreme.extremePoints_subset_extremePoints hx
    rw [hQV] at hxQext
    exact extremePoints_convexHull_subset hxQext
  · exact exposed_face_eq_convexHull_extremePoints ⟨V, hV, hQV⟩ hF

/-- Helper for Exercise 4.38: a polytope has only finitely many exposed faces. -/
lemma polytope_finite_exposed_faces
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} (hQ : Q.IsPolytope ℝ) :
    {F : Set E | IsExposed ℝ Q F}.Finite := by
  classical
  rcases hQ with ⟨V, hV, hQV⟩
  let faceVertices : {F : Set E | IsExposed ℝ Q F} → {s : Finset E // s ∈ hV.toFinset.powerset} :=
    fun F ↦
      let hFV : (F.1.extremePoints ℝ).Finite :=
        hV.subset fun x hx ↦ by
          have hxQext : x ∈ Q.extremePoints ℝ :=
            F.2.isExtreme.extremePoints_subset_extremePoints hx
          rw [hQV] at hxQext
          exact extremePoints_convexHull_subset hxQext
      have hsubset : hFV.toFinset ⊆ hV.toFinset := by
        intro x hx
        have hxF : x ∈ F.1.extremePoints ℝ := by
          simpa using hx
        have hxV : x ∈ V := by
          have hxQext : x ∈ Q.extremePoints ℝ :=
            F.2.isExtreme.extremePoints_subset_extremePoints hxF
          rw [hQV] at hxQext
          exact extremePoints_convexHull_subset hxQext
        simpa using hxV
      ⟨hFV.toFinset, Finset.mem_powerset.mpr hsubset⟩
  have hfaceVertices_inj : Function.Injective faceVertices := by
    intro F₁ F₂ hEq
    apply Subtype.ext
    have hsetEq : F₁.1.extremePoints ℝ = F₂.1.extremePoints ℝ := by
      have hFV₁ : (F₁.1.extremePoints ℝ).Finite := by
        apply hV.subset
        intro x hx
        have hxQext : x ∈ Q.extremePoints ℝ :=
          F₁.2.isExtreme.extremePoints_subset_extremePoints hx
        rw [hQV] at hxQext
        exact extremePoints_convexHull_subset hxQext
      have hFV₂ : (F₂.1.extremePoints ℝ).Finite := by
        apply hV.subset
        intro x hx
        have hxQext : x ∈ Q.extremePoints ℝ :=
          F₂.2.isExtreme.extremePoints_subset_extremePoints hx
        rw [hQV] at hxQext
        exact extremePoints_convexHull_subset hxQext
      exact hFV₁.toFinset_inj.mp (Subtype.ext_iff.mp hEq)
    calc
      F₁.1 = convexHull ℝ (F₁.1.extremePoints ℝ) :=
        exposed_face_eq_convexHull_extremePoints ⟨V, hV, hQV⟩ F₁.2
      _ = convexHull ℝ (F₂.1.extremePoints ℝ) := by rw [hsetEq]
      _ = F₂.1 :=
        (exposed_face_eq_convexHull_extremePoints ⟨V, hV, hQV⟩ F₂.2).symm
  have hfinite_subtype : Finite {F : Set E | IsExposed ℝ Q F} :=
    Finite.of_injective faceVertices hfaceVertices_inj
  -- Local instance justification (proof-local temporary datum): `Set.toFinite` requires a
  -- `Finite` instance on the subtype of exposed faces.
  letI : Finite {F : Set E | IsExposed ℝ Q F} := hfinite_subtype
  exact Set.toFinite _

/-- Helper for Exercise 4.38: a polytope has only finitely many facets. -/
lemma polytope_finite_facets
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} (hQ : Q.IsPolytope ℝ) :
    {F : Set E | IsFacetOf Q F}.Finite := by
  refine (polytope_finite_exposed_faces hQ).subset ?_
  intro F hF
  exact hF.2.1
