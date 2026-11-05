module

public import Mathlib.Topology.ExtremallyDisconnected

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set Homeomorph

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [ExtremallyDisconnected Y] {f : X → Y}

/-- Helper for Lemma 5.26.4: a continuous map from a compact space to a Hausdorff space is a
closed map. -/
lemma isClosedMap_of_continuous_compact_t2 (hf : Continuous f) : IsClosedMap f := by
  intro Z hZ
  -- Closed subsets of a compact space are compact.
  have hcompact : IsCompact Z := hZ.isCompact
  -- Continuous images of compact sets are compact, hence closed in a Hausdorff space.
  exact (hcompact.image hf).isClosed

/-- Helper for Lemma 5.26.4: the image of the complement of an open set is closed. -/
lemma isClosed_image_compl_of_isOpen (hf : Continuous f) {U : Set X} (hU : IsOpen U) :
    IsClosed (f '' Uᶜ) := by
  -- Apply the closed-map package to the closed set `Uᶜ`.
  exact isClosedMap_of_continuous_compact_t2 (f := f) hf _ hU.isClosed_compl

/-- Helper for Lemma 5.26.4: Lemma 5.26.2 places the image of a point in an open set inside the
closure of the complement of the image of the complementary closed set. -/
lemma mem_closure_compl_image_compl_of_mem_open
    (hf : Continuous f) (hsurj : Function.Surjective f)
    (hproper :
      ∀ Z : Set X, Z ≠ (univ : Set X) → IsClosed Z → f '' Z ≠ (univ : Set Y))
    {U : Set X} {x : X} (hU : IsOpen U) (hx : x ∈ U) :
    f x ∈ closure ((f '' Uᶜ)ᶜ) := by
  -- This is the pointwise form of Lemma 5.26.2, proved directly to avoid the universe mismatch
  -- in the owner theorem's same-universe statement.
  rw [mem_closure_iff]
  intro N hN hxN
  have hnonempty : (U ∩ f ⁻¹' N).Nonempty :=
    ⟨x, mem_inter hx (mem_preimage.mpr hxN)⟩
  have hOpen : IsOpen (U ∩ f ⁻¹' N) := hU.inter (hN.preimage hf)
  have hne_univ : f '' (U ∩ f ⁻¹' N)ᶜ ≠ (univ : Set Y) :=
    hproper _ (compl_ne_univ.mpr hnonempty) hOpen.isClosed_compl
  rcases nonempty_compl.mpr hne_univ with ⟨y, hy⟩
  have hy_compl : y ∈ (f '' Uᶜ)ᶜ := by
    intro hyU
    have hsubset : Uᶜ ⊆ (U ∩ f ⁻¹' N)ᶜ := by
      intro z hz
      simp only [mem_compl_iff, mem_inter_iff, mem_preimage]
      exact fun hz' ↦ hz hz'.1
    exact hy <| image_mono hsubset hyU
  rcases hsurj y with ⟨z, rfl⟩
  have hz_mem : z ∈ U ∩ f ⁻¹' N := by
    have hz_not : z ∉ (U ∩ f ⁻¹' N)ᶜ := by
      intro hz_compl
      exact hy ⟨z, hz_compl, rfl⟩
    simpa only [mem_compl_iff, mem_inter_iff, mem_preimage, not_not] using hz_not
  exact ⟨f z, mem_inter (mem_preimage.mp hz_mem.2) hy_compl⟩

/-- Helper for Lemma 5.26.4: in an extremally disconnected space, if two closed sets cover the
space, then the closures of their open complements are disjoint. -/
lemma disjoint_closure_compl_of_closed_cover {A B : Set Y}
    (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = univ) :
    Disjoint (closure Aᶜ) (closure Bᶜ) := by
  have hdisj : Disjoint Aᶜ Bᶜ := by
    -- The complements are disjoint because `A` and `B` already cover the space.
    rw [disjoint_iff_inter_eq_empty, ← compl_union, hcover, compl_univ]
  -- Lemma 5.26.3 upgrades disjoint open sets to disjoint closures.
  exact
    ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen hdisj hA.isOpen_compl
      hB.isOpen_compl

/-- Helper for Lemma 5.26.4: the proper-image condition on closed subsets forces injectivity. -/
lemma injective_of_surjective_of_image_proper_closed
    (hf : Continuous f) (hsurj : Function.Surjective f)
    (hproper :
      ∀ Z : Set X, Z ≠ (univ : Set X) → IsClosed Z → f '' Z ≠ (univ : Set Y)) :
    Function.Injective f := by
  intro x x' hfx
  by_contra hxx'
  -- Separate the two distinct source points by disjoint open neighborhoods.
  rcases t2_separation hxx' with ⟨U, V, hU, hV, hxU, hx'V, hUV⟩
  let T : Set Y := f '' Uᶜ
  let T' : Set Y := f '' Vᶜ
  have hTclosed : IsClosed T := by
    -- The closed-map argument shows `f (X \ U)` is closed.
    simpa [T] using isClosed_image_compl_of_isOpen (f := f) hf hU
  have hT'closed : IsClosed T' := by
    -- The same argument applies to `f (X \ V)`.
    simpa [T'] using isClosed_image_compl_of_isOpen (f := f) hf hV
  have hcover : T ∪ T' = univ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      rcases hsurj y with ⟨z, rfl⟩
      have hz : z ∈ Uᶜ ∪ Vᶜ := by
        by_cases hzU : z ∈ U
        · have hzV : z ∉ V := by
            intro hzV
            exact hUV.le_bot ⟨hzU, hzV⟩
          exact Or.inr hzV
        · exact Or.inl hzU
      rcases hz with hzU | hzV
      · exact Or.inl ⟨z, hzU, rfl⟩
      · exact Or.inr ⟨z, hzV, rfl⟩
  have hdisj : Disjoint (closure Tᶜ) (closure T'ᶜ) := by
    -- Since `T` and `T'` cover `Y`, the extremally disconnected lemma makes these closures disjoint.
    exact disjoint_closure_compl_of_closed_cover (A := T) (B := T') hTclosed hT'closed hcover
  have hxT : f x ∈ closure Tᶜ := by
    -- Lemma 5.26.2 applied to the open neighborhood `U`.
    simpa [T] using
      mem_closure_compl_image_compl_of_mem_open (f := f) hf hsurj hproper hU hxU
  have hx'T' : f x' ∈ closure T'ᶜ := by
    -- Lemma 5.26.2 applied to the open neighborhood `V`.
    simpa [T'] using
      mem_closure_compl_image_compl_of_mem_open (f := f) hf hsurj hproper hV hx'V
  exact hdisj.ne_of_mem hxT hx'T' hfx

/-- Lemma 5.26.4: a surjective continuous map from a Hausdorff quasi-compact space to an
extremally disconnected Hausdorff space is a homeomorphism if the image of every proper closed
subset of the source is a proper subset of the target. The target's quasi-compactness is automatic
from surjectivity and compactness of the source, so it is omitted from the Lean hypotheses. -/
theorem isHomeomorph_of_extremallyDisconnected_of_surjective_of_image_proper_closed
    (hf : Continuous f) (hsurj : Function.Surjective f)
    (hproper :
      ∀ Z : Set X, Z ≠ (univ : Set X) → IsClosed Z → f '' Z ≠ (univ : Set Y)) :
    IsHomeomorph f := by
  -- Follow Lemma 5.17.8: once surjectivity is given, it remains to prove injectivity.
  have hinj : Function.Injective f :=
    injective_of_surjective_of_image_proper_closed (f := f) hf hsurj hproper
  -- The compact-to-Hausdorff criterion now turns continuity and bijectivity into a homeomorphism.
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨hf, ⟨hinj, hsurj⟩⟩

end
