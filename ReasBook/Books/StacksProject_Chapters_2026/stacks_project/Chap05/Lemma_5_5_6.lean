module
public import Mathlib.Topology.Bases
import stacks_project.Chap05.Lemma_5_5_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace

universe u

section

variable {X : Type u}

/- Domain-style sampling for basis images under a quotient:
- primary domain: general topology of generated topologies, quotient maps, and topological bases
- owner abstractions:
  `TopologicalSpace.IsTopologicalBasis`,
  `TopologicalSpace.generateFrom`,
  `Topology.IsQuotientMap`
- same-domain declarations inspected:
  `TopologicalSpace.IsTopologicalBasis.continuous_iff`,
  `TopologicalSpace.IsTopologicalBasis.isQuotientMap`,
  `Topology.isQuotientMap_quotient_mk'`,
  `Lemma_5_5_2.isTopologicalBasis_generateFrom`

Layer triage:
- `source-facing`: existence of a target space whose basis is formed by the images of `B`
- `core/canonical`: the quotient type `Quotient` and the basis owner `IsTopologicalBasis`
- `bridge/view`: the quotient map equipped with the generated topology on image-basis sets

Primitive data is the quotient relation “same membership pattern on `B`” together with the image
family on the quotient. Openness of the image family and continuity of the quotient map are derived
from the canonical generated-topology basis API, so there is no need for a parallel public wrapper.
-/

/-- Helper for Lemma 5.5.6: the quotient relation identifying points with the same membership
pattern in all members of `B`. -/
private def basisPatternSetoid (B : Set (Set X)) : Setoid X where
  r x y := ∀ U ∈ B, x ∈ U ↔ y ∈ U
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x U hU
      rfl
    · intro x y hxy U hU
      exact (hxy U hU).symm
    · intro x y z hxy hyz U hU
      exact (hxy U hU).trans (hyz U hU)

/-- Helper for Lemma 5.5.6: the quotient map has exactly the expected preimage on each basis
member. -/
private theorem preimage_image_quotientMk_eq (B : Set (Set X)) {U : Set X} (hU : U ∈ B) :
    let q : X → Quotient (basisPatternSetoid B) := @Quotient.mk' X (basisPatternSetoid B)
    q ⁻¹' (q '' U) = U := by
  let q : X → Quotient (basisPatternSetoid B) := @Quotient.mk' X (basisPatternSetoid B)
  ext x
  constructor
  · rintro ⟨y, hyU, hyx⟩
    exact (Quotient.eq'.1 hyx U hU).1 hyU
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Lemma 5.5.6, canonical form: if a family of open sets covers `X` and every pairwise
intersection is the union of members of the family contained in it, then there exists a continuous
map whose image family has exactly the prescribed preimages and is a topological basis on the
target. Openness of the image family is derived from the basis owner. -/
theorem exists_continuousMap_with_basis_images
    {X : Type u} [TopologicalSpace X] (B : Set (Set X))
    (hopen : ∀ U ∈ B, IsOpen U) (hcover : sUnion B = univ)
    (hinter : ∀ ⦃U V : Set X⦄, U ∈ B → V ∈ B →
      U ∩ V = ⋃₀ { W : Set X | W ∈ B ∧ W ⊆ U ∩ V }) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (f : C(X, Y)),
      (∀ U ∈ B, f ⁻¹' (f '' U) = U) ∧
      IsTopologicalBasis (image (f : X → Y) '' B) := by
  -- Route correction: construct the target as the quotient by basis-membership patterns, then put
  -- the generated topology from the image family on that quotient.
  let R := basisPatternSetoid B
  let q : X → Quotient R := Quotient.mk'
  let 𝓑 : Set (Set (Quotient R)) := image q '' B
  -- The image family covers the quotient because every class has a representative in some `U ∈ B`.
  have hcover_𝓑 : sUnion 𝓑 = univ := by
    ext y
    constructor
    · intro _
      simp
    · intro _
      rcases Quotient.mk'_surjective y with ⟨x, rfl⟩
      have hx : x ∈ sUnion B := by
        rw [hcover]
        trivial
      rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
      exact mem_sUnion.2 ⟨q '' U, mem_image_of_mem _ hU, mem_image_of_mem _ hxU⟩
  -- Intersections of image-basis sets refine by pushing the source refinement through the quotient.
  have hinter_𝓑 :
      ∀ ⦃y : Quotient R⦄ ⦃U : Set (Quotient R)⦄, U ∈ 𝓑 →
        ∀ ⦃V : Set (Quotient R)⦄, V ∈ 𝓑 →
          y ∈ U ∩ V → ∃ W ∈ 𝓑, y ∈ W ∧ W ⊆ U ∩ V := by
    intro y U hU V hV hy
    rcases hU with ⟨U₀, hU₀, rfl⟩
    rcases hV with ⟨V₀, hV₀, rfl⟩
    rcases hy.1 with ⟨x, hxU₀, hxy⟩
    rcases hy.2 with ⟨z, hzV₀, hzy⟩
    have hxz : Quotient.mk' x = Quotient.mk' z := hxy.trans hzy.symm
    have hzU₀ : z ∈ U₀ := (Quotient.eq'.1 hxz U₀ hU₀).1 hxU₀
    have hzUV : z ∈ U₀ ∩ V₀ := ⟨hzU₀, hzV₀⟩
    have hzUnion : z ∈ ⋃₀ { W : Set X | W ∈ B ∧ W ⊆ U₀ ∩ V₀ } := by
      rw [← hinter hU₀ hV₀]
      exact hzUV
    rcases mem_sUnion.1 hzUnion with ⟨W, hW, hzW⟩
    refine ⟨q '' W, mem_image_of_mem _ hW.1, ⟨z, hzW, hzy⟩, ?_⟩
    intro t ht
    rcases ht with ⟨w, hwW, rfl⟩
    exact ⟨⟨w, (hW.2 hwW).1, rfl⟩, ⟨w, (hW.2 hwW).2, rfl⟩⟩
  let _ : TopologicalSpace (Quotient R) := generateFrom 𝓑
  have hBasis : IsTopologicalBasis 𝓑 := isTopologicalBasis_generateFrom 𝓑 hcover_𝓑 hinter_𝓑
  -- Continuity is checked on basis opens, whose preimages are exactly the original open sets in `B`.
  have hcontinuous : Continuous q := hBasis.continuous_iff.2 fun U hU ↦ by
    rcases hU with ⟨V, hV, rfl⟩
    have hqV : q ⁻¹' (q '' V) = V := by
      simpa [R, q] using (preimage_image_quotientMk_eq B hV)
    simpa [hqV] using (hopen V hV)
  refine ⟨Quotient R, inferInstance, ⟨q, hcontinuous⟩, ?_, hBasis⟩
  intro U hU
  simpa [R, q] using (preimage_image_quotientMk_eq B hU)

/-- Lemma 5.5.6, source-facing form: the image family in the target can be stated explicitly as
open, but this is derived from `IsTopologicalBasis`. -/
theorem exists_continuousMap_with_open_basis_images
    {X : Type u} [TopologicalSpace X] (B : Set (Set X))
    (hopen : ∀ U ∈ B, IsOpen U) (hcover : sUnion B = univ)
    (hinter : ∀ ⦃U V : Set X⦄, U ∈ B → V ∈ B →
      U ∩ V = ⋃₀ { W : Set X | W ∈ B ∧ W ⊆ U ∩ V }) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (f : C(X, Y)),
      (∀ U ∈ B, IsOpen (f '' U)) ∧
      (∀ U ∈ B, f ⁻¹' (f '' U) = U) ∧
      IsTopologicalBasis (image (f : X → Y) '' B) := by
  obtain ⟨Y, _, f, hpreimage, hBasis⟩ :=
    exists_continuousMap_with_basis_images B hopen hcover hinter
  refine ⟨Y, inferInstance, f, ?_, hpreimage, hBasis⟩
  intro U hU
  exact hBasis.isOpen (mem_image_of_mem _ hU)

end
