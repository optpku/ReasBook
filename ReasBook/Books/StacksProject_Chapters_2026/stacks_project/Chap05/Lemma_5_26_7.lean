module

public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Function Set

section

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/- Domain-style sampling for Lemma 5.26.7:
- primary domain: separation properties of Hausdorff spaces and continuous self-maps
- sampled owner declarations:
  `t2_separation`,
  `Disjoint.notMem_of_mem_left`,
  `Set.image_union_image_compl_eq_range`,
  `Function.Surjective.range_eq`
- best owner abstraction: this item is `source-facing`; its ambient canonical owner data are the
  Hausdorff separation theorem `t2_separation` together with the standard `Set` image/complement
  cover theorem, but there is no upstream project or mathlib theorem with the exact Stacks
  conclusion
- primitive data: a continuous surjective self-map `f : X → X`, the nonidentity witness
  `hne : f ≠ id`, and Hausdorff separation for two distinct points
- derived API: the constructed proper closed set `E = (U ∩ f ⁻¹' V)ᶜ` and the cover
  `E ∪ f '' E = univ`

Layer triage:
- `source-facing`: the existence of the proper closed set `E`
- `core/canonical`: `T2Space`, `t2_separation`, and standard image/preimage lemmas
- `bridge/view`: none needed here, since the full statement is not already owned upstream
-/

/-- A set is a proper closed image-cover for `f` if it is closed, proper, and together with its
image under `f` covers the whole space. -/
structure IsProperClosedImageCover (f : X → X) (E : Set X) : Prop where
  isClosed : IsClosed E
  ne_univ : E ≠ univ
  union_image_eq_univ : E ∪ f '' E = univ

-- Proof sketch: choose `p` with `f p ≠ p`, separate `p` and `f p` by disjoint open sets `U` and
-- `V`, and define `E = (U ∩ f ⁻¹' V)ᶜ`. This set is closed and proper since `p ∉ E`. For any
-- `x ∉ E`, surjectivity gives `x = f y`; if `y ∉ E` as well, then `y ∈ U ∩ f ⁻¹' V`, forcing
-- `x ∈ U ∩ V`, a contradiction. Hence `y ∈ E`, so `x ∈ f '' E`.
/-- Lemma 5.26.7: a surjective continuous nonidentity self-map of a Hausdorff space admits a
proper closed subset whose union with its image is all of `X`. -/
theorem exists_proper_closed_set_union_image_eq_univ
    {f : X → X} (hf : Continuous f) (hsurj : Surjective f) (hne : f ≠ id) :
    ∃ E : Set X, IsProperClosedImageCover f E := by
  -- First extract a point moved by `f`; otherwise `f = id` by function extensionality.
  obtain ⟨p, hp_ne⟩ : ∃ p : X, f p ≠ p := by
    by_contra h
    apply hne
    funext x
    by_contra hx
    exact h ⟨x, hx⟩
  -- Separate the two distinct points `p` and `f p` by disjoint open neighborhoods.
  obtain ⟨U, V, hU, hV, hpU, hfpV, hUV⟩ := t2_separation hp_ne.symm
  let E : Set X := (U ∩ f ⁻¹' V)ᶜ
  refine ⟨E, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- The complement of the open separator region is closed.
    exact (hU.inter (hV.preimage hf)).isClosed_compl
  · -- The point `p` lies in the separator region, so `E` is proper.
    intro hE
    have hp_mem : p ∈ E := by
      simp [hE]
    have hp_not_mem : p ∉ E := by
      simpa [E] using ⟨hpU, hfpV⟩
    exact hp_not_mem hp_mem
  · -- Any point is either already in `E`, or it is the image of a point of `E`.
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hxE : x ∈ E
    · exact Or.inl hxE
    · right
      rcases hsurj x with ⟨y, rfl⟩
      have hyE : y ∈ E := by
        -- If `y` were also in the separator region, then `f y` would lie in `U ∩ V`.
        by_contra hyNotE
        have hyUV : y ∈ U ∩ f ⁻¹' V := by
          simpa [E] using hyNotE
        have hfyV : f y ∈ V := hyUV.2
        have hfyU : f y ∈ U := by
          have hxUV : f y ∈ U ∩ f ⁻¹' V := by
            simpa [E] using hxE
          exact hxUV.1
        exact (hUV.notMem_of_mem_left hfyU) hfyV
      exact ⟨y, hyE, rfl⟩

end
