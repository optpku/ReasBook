/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_definition_3_15_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_lattice_free

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped MixedIntegerNotation

-- This file reuses the chapter's canonical `MixedRealPoint` / `mixed_integer_lattice` owners,
-- the generic projection API `mem_image_fst_iff`, and the `is_free_of` /
-- `is_maximal_free_of` owners from Theorem 6.18. Full-dimensionality is kept explicit via
-- `affineSpan ℝ C = ⊤`, matching the chapter's lattice-free API.

section Lemma617

variable {n p : ℕ}
variable {C : Set (MixedRealPoint p (n - p))}

/-- A set in `MixedRealPoint p (n - p)` is mixed-integer-free when its interior contains no point
of `ℤ^p × ℝ^(n - p)`. -/
def is_mixed_integer_free
    (C : Set (MixedRealPoint p (n - p))) : Prop :=
  is_free_of (ℤ^p×ℝ^(n - p)) C

/-- `is_mixed_integer_free C` unfolds to the assertion that no mixed-integer point lies in the
interior of `C`. -/
theorem is_mixed_integer_free_iff
    {C : Set (MixedRealPoint p (n - p))} :
    is_mixed_integer_free C ↔
      Disjoint (interior C) (ℤ^p×ℝ^(n - p)) :=
  Iff.rfl

/-- If `C` is mixed-integer-free, then no mixed-integer point lies in its interior. -/
theorem is_mixed_integer_free.not_mem_interior
    {C : Set (MixedRealPoint p (n - p))}
    (hC : is_mixed_integer_free C)
    {xy : MixedRealPoint p (n - p)}
    (hxy : xy ∈ ℤ^p×ℝ^(n - p)) :
    xy ∉ interior C :=
  is_free_of.not_mem_interior hC hxy

/-- A maximal mixed-integer-free convex set in `MixedRealPoint p (n - p)` is a convex
mixed-integer-free set that admits no larger convex mixed-integer-free superset. -/
def is_maximal_mixed_integer_free
    (C : Set (MixedRealPoint p (n - p))) : Prop :=
  is_maximal_free_of (ℤ^p×ℝ^(n - p)) C

/-- `is_maximal_mixed_integer_free C` unfolds to convexity, mixed-integer-freeness, and
maximality among convex mixed-integer-free supersets. -/
theorem is_maximal_mixed_integer_free_iff
    {C : Set (MixedRealPoint p (n - p))} :
    is_maximal_mixed_integer_free C ↔
      Convex ℝ C ∧
        is_mixed_integer_free C ∧
          ∀ C' : Set (MixedRealPoint p (n - p)),
            C ⊆ C' → Convex ℝ C' → is_mixed_integer_free C' → C' = C :=
  Iff.rfl

/-- A maximal mixed-integer-free set is convex. -/
theorem is_maximal_mixed_integer_free.convex
    {C : Set (MixedRealPoint p (n - p))}
    (hC : is_maximal_mixed_integer_free C) :
    Convex ℝ C :=
  is_maximal_free_of.convex hC

/-- A maximal mixed-integer-free set is mixed-integer-free. -/
theorem is_maximal_mixed_integer_free.mixed_integer_free
    {C : Set (MixedRealPoint p (n - p))}
    (hC : is_maximal_mixed_integer_free C) :
    is_mixed_integer_free C :=
  is_maximal_free_of.free hC

/-- Maximality among convex mixed-integer-free supersets gives equality with any larger convex
mixed-integer-free superset. -/
theorem is_maximal_mixed_integer_free.eq_of_subset
    {C C' : Set (MixedRealPoint p (n - p))}
    (hC : is_maximal_mixed_integer_free C)
    (hCC' : C ⊆ C')
    (hC'_convex : Convex ℝ C')
    (hC'_mixed_integer_free : is_mixed_integer_free C') :
    C' = C :=
  is_maximal_free_of.eq_of_subset hC hCC' hC'_convex hC'_mixed_integer_free

/-- Helper for Lemma 6.17: for a full-dimensional convex mixed set, the interior of the first
projection is exactly the projection of the interior. -/
lemma interior_image_fst_eq_image_fst_interior_of_fullDimensional
    (hconvC : Convex ℝ C)
    (hfull : affineSpan ℝ C = ⊤) :
    interior (Prod.fst '' C) = Prod.fst '' interior C := by
  let fstMap : MixedRealPoint p (n - p) →ₗ[ℝ] (Fin p → ℝ) :=
    LinearMap.fst ℝ (Fin p → ℝ) (Fin (n - p) → ℝ)
  have hfstOpen : IsOpenMap fstMap :=
    LinearMap.isOpenMap_of_finiteDimensional fstMap LinearMap.fst_surjective
  have hInteriorNonempty : (interior C).Nonempty :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hconvC).2 hfull
  have hImageInteriorOpen : IsOpen (Prod.fst '' interior C) := by
    -- The coordinate projection is an open map in finite dimensions.
    simpa [fstMap] using hfstOpen _ isOpen_interior
  have hImageInteriorSubset :
      Prod.fst '' interior C ⊆ interior (Prod.fst '' C) := by
    have hImageSubset : Prod.fst '' interior C ⊆ Prod.fst '' C := by
      rintro x ⟨xy, hxy, rfl⟩
      exact ⟨xy, interior_subset hxy, rfl⟩
    -- Any open subset of the projection is contained in the interior of the projection.
    intro x hx
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hImageInteriorOpen.mem_nhds hx) hImageSubset
  have hProjectionSubsetClosure :
      Prod.fst '' C ⊆ closure (Prod.fst '' interior C) := by
    -- Density of `interior C` inside `C` transfers through the continuous projection.
    have hClosureEq : closure (interior C) = closure C :=
      hconvC.closure_interior_eq_closure_of_nonempty_interior hInteriorNonempty
    intro x hx
    rcases mem_image_fst_iff.mp hx with ⟨y, hxyC⟩
    have hxyClosure : (x, y) ∈ closure (interior C) := by
      rw [hClosureEq]
      exact subset_closure hxyC
    exact
      map_mem_closure continuous_fst hxyClosure <| by
        intro xy hxy
        exact ⟨xy, hxy, rfl⟩
  have hClosureEq :
      closure (Prod.fst '' C) = closure (Prod.fst '' interior C) := by
    have hImageSubset : Prod.fst '' interior C ⊆ Prod.fst '' C := by
      rintro x ⟨xy, hxy, rfl⟩
      exact ⟨xy, interior_subset hxy, rfl⟩
    -- The projected interior is dense in the projected set.
    refine Subset.antisymm ?_ ?_
    · exact closure_minimal hProjectionSubsetClosure isClosed_closure
    · exact closure_mono hImageSubset
  have hProjectionInteriorNonempty : (interior (Prod.fst '' C)).Nonempty :=
    hInteriorNonempty.image Prod.fst |>.mono hImageInteriorSubset
  have hImageInteriorNonempty : (interior (Prod.fst '' interior C)).Nonempty := by
    -- The image of the nonempty interior stays nonempty, and this image is open.
    simpa [hImageInteriorOpen.interior_eq] using hInteriorNonempty.image Prod.fst
  have hconvProjection : Convex ℝ (Prod.fst '' C) := by
    -- Convexity is preserved by linear projection.
    simpa [fstMap] using hconvC.linear_image fstMap
  have hconvImageInterior : Convex ℝ (Prod.fst '' interior C) := by
    -- The same projection preserves convexity of the interior.
    simpa [fstMap] using hconvC.interior.linear_image fstMap
  apply Subset.antisymm
  · intro x hx
    have hxClosure :
        x ∈ interior (closure (Prod.fst '' C)) := by
      simpa [hconvProjection.interior_closure_eq_interior_of_nonempty_interior
        hProjectionInteriorNonempty] using hx
    have hxImageClosure :
        x ∈ interior (closure (Prod.fst '' interior C)) := by
      rwa [hClosureEq] at hxClosure
    have hxImageInterior :
        x ∈ interior (Prod.fst '' interior C) := by
      simpa [hconvImageInterior.interior_closure_eq_interior_of_nonempty_interior
        hImageInteriorNonempty] using hxImageClosure
    simpa [hImageInteriorOpen.interior_eq] using hxImageInterior
  · exact hImageInteriorSubset

/-- Helper for Lemma 6.17: the first-coordinate projection of a full-dimensional convex
mixed-integer-free set is lattice-free. -/
  lemma projectionLatticeFreeOfMixedIntegerFree
    (hconvC : Convex ℝ C)
    (hfull : affineSpan ℝ C = ⊤)
    (hfreeC : is_mixed_integer_free C) :
    is_lattice_free (Prod.fst '' C) := by
  rw [is_lattice_free_iff]
  intro z hzInterior
  -- Rewrite the projected interior as the projection of the interior of `C`.
  rw [interior_image_fst_eq_image_fst_interior_of_fullDimensional hconvC hfull] at hzInterior
  rcases mem_image_fst_iff.mp hzInterior with ⟨y, hzyInterior⟩
  have hzyLattice : ((Int.cast ∘ z), y) ∈ (ℤ^p×ℝ^(n - p)) := by
    rw [mem_mixed_integer_lattice_iff]
    exact (mem_integerVectors_iff).2 ⟨z, rfl⟩
  exact hfreeC.not_mem_interior hzyLattice hzyInterior

/-- Helper for Lemma 6.17: projecting the full cylinder over `K` recovers `K`. -/
lemma imageFstCylinderUnivEq
    (K : Set (Fin p → ℝ)) :
    Prod.fst '' (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))) = K := by
  ext x
  rw [mem_image_fst_iff]
  constructor
  · rintro ⟨y, hxK, -⟩
    exact hxK
  · intro hxK
    exact ⟨0, hxK, mem_univ _⟩

/-- Helper for Lemma 6.17: any convex lattice-free cylinder over a superset of the projection of a
maximal mixed-integer-free set must coincide with that set. -/
lemma eqCylinderOfProjectionSubset
    {K : Set (Fin p → ℝ)}
    (hC : is_maximal_mixed_integer_free C)
    (hproj : Prod.fst '' C ⊆ K)
    (hconvK : Convex ℝ K)
    (hfreeK : is_lattice_free K) :
    K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ)) = C := by
  have hsubset : C ⊆ K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ)) := by
    -- Every point of `C` projects into `K`, and the second coordinate is unrestricted.
    intro xy hxy
    refine ⟨?_, mem_univ _⟩
    exact hproj ⟨xy, hxy, rfl⟩
  have hconvCylinder : Convex ℝ (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))) := by
    -- Convexity of the base and the unrestricted fiber combine productwise.
    simpa using hconvK.prod convex_univ
  have hfreeCylinder :
      is_mixed_integer_free (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))) := by
    -- A mixed-integer point in the cylinder interior would project to an integer point in
    -- `interior K`, contradicting lattice-freeness of the base.
    rw [is_mixed_integer_free, is_free_of_iff]
    intro xy hxyMixed
    rw [interior_prod_eq, interior_univ]
    rintro ⟨hxInterior, -⟩
    exact hfreeK.not_mem_interior (mem_mixed_integer_lattice_iff.mp hxyMixed) hxInterior
  exact is_maximal_mixed_integer_free.eq_of_subset hC hsubset hconvCylinder hfreeCylinder

/-- Lemma 6.17 (1). Let `C` be a full-dimensional maximal `ℤ^p × ℝ^(n - p)`-free convex set and
let `Prod.fst '' C` be its orthogonal projection onto `ℝ^p`. Then this projection is a maximal
`ℤ^p`-free convex set. -/
theorem mixed_integer_projection_is_maximal_lattice_free
    (hfull : affineSpan ℝ C = ⊤)
    (hC : is_maximal_mixed_integer_free C) :
    is_maximal_lattice_free (Prod.fst '' C) := by
  have hconvC : Convex ℝ C := is_maximal_mixed_integer_free.convex hC
  have hfreeC : is_mixed_integer_free C := is_maximal_mixed_integer_free.mixed_integer_free hC
  have hconvProjection : Convex ℝ (Prod.fst '' C) := by
    -- Convexity of `C` descends to its projection.
    simpa using
      hconvC.linear_image (LinearMap.fst ℝ (Fin p → ℝ) (Fin (n - p) → ℝ))
  have hfreeProjection : is_lattice_free (Prod.fst '' C) :=
    projectionLatticeFreeOfMixedIntegerFree hconvC hfull hfreeC
  rw [is_maximal_lattice_free_iff]
  refine ⟨hconvProjection, hfreeProjection, ?_⟩
  intro K hsubset hconvK hfreeK
  -- Maximality of `C` forces equality with every larger lattice-free cylinder.
  have hCylinderEq : K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ)) = C :=
    eqCylinderOfProjectionSubset hC hsubset hconvK hfreeK
  calc
    K = Prod.fst '' (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))) := by
      symm
      exact imageFstCylinderUnivEq (n := n) (p := p) K
    _ = Prod.fst '' C := by rw [hCylinderEq]

/-- Lemma 6.17 (2). Let `C` be a full-dimensional maximal `ℤ^p × ℝ^(n - p)`-free convex set and
let `Prod.fst '' C` be its orthogonal projection onto `ℝ^p`. Then
`C = (Prod.fst '' C) × ℝ^(n - p)`, represented here as the mixed-integer cylinder over the
projection. -/
theorem eq_mixed_integer_cylinder_of_full_dimensional_maximal_mixed_integer_free
    (hfull : affineSpan ℝ C = ⊤)
    (hC : is_maximal_mixed_integer_free C) :
    C = (Prod.fst '' C) ×ˢ (Set.univ : Set (Fin (n - p) → ℝ)) := by
  have hconvC : Convex ℝ C := is_maximal_mixed_integer_free.convex hC
  have hfreeC : is_mixed_integer_free C := is_maximal_mixed_integer_free.mixed_integer_free hC
  have hconvProjection : Convex ℝ (Prod.fst '' C) := by
    -- The projection remains convex because it is a linear image.
    simpa using
      hconvC.linear_image (LinearMap.fst ℝ (Fin p → ℝ) (Fin (n - p) → ℝ))
  have hfreeProjection : is_lattice_free (Prod.fst '' C) :=
    projectionLatticeFreeOfMixedIntegerFree hconvC hfull hfreeC
  -- Apply the cylinder comparison to the actual projection of `C`.
  symm
  exact eqCylinderOfProjectionSubset hC (Subset.rfl) hconvProjection hfreeProjection

end Lemma617
