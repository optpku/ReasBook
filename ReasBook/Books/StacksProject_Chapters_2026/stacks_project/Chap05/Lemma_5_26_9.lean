module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Category.Stonean.Basic
import stacks_project.Chap05.Lemma_5_26_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Set
open scoped Topology

universe u

/- Domain-style sampling for Stonean presentations and minimal Stonean covers:
- primary domain: Stonean presentations and uniqueness of minimal Stonean surjections in `CompHaus`
- sampled owner declarations:
  `CompHaus.presentation`,
  `CompHaus.presentation.π`,
  `CompHaus.lift`,
  `isHomeomorph_of_extremallyDisconnected_of_surjective_of_image_proper_closed`
- best owner abstractions: `CompHaus.presentation` for the existence statement, and the chapter
  owner theorem
  `isHomeomorph_of_extremallyDisconnected_of_surjective_of_image_proper_closed` for uniqueness
- primitive data: the canonical presentation map, and a morphism over `X` together with
  surjectivity and the proper-closed-image minimality condition
- derived API: the textbook existential restatements and the resulting homeomorphism over `X`

Layer triage:
- `source-facing`: existence of a Stonean surjection onto `X`, and uniqueness up to homeomorphism
  among minimal Stonean surjections onto `X`
- `core/canonical`: `CompHaus.presentation`, `CompHaus.lift`, and the owner homeomorphism
  criterion from `Lemma_5_26_4`
- `bridge/view`: the existential and over-`X` restatements below

The minimality hypothesis is theorem-level data, not a new owner structure. This file should
therefore reuse the existing chapter owner theorem for the homeomorphism criterion rather than
re-proving a Stonean-specialized version through `ExtremallyDisconnected.homeoCompactToT2`.
-/

section

variable (X : CompHaus.{u})

-- Proof sketch: use the canonical Stonean presentation `CompHaus.presentation X`, whose structure
-- map to `X` is already an epimorphism in `CompHaus`; for compact Hausdorff spaces, epimorphisms
-- are exactly surjections.
/-- Lemma 5.26.9 (1): every quasi-compact Hausdorff space admits a continuous surjection from an
extremally disconnected quasi-compact Hausdorff space. The canonical bundled witness is the
presentation map `CompHaus.presentation.π X : X.presentation.compHaus ⟶ X`. -/
theorem presentation_pi_surjective :
    Function.Surjective (CompHaus.presentation.π X) := by
  simpa using (CompHaus.epi_iff_surjective (CompHaus.presentation.π X)).mp inferInstance

/-- Textbook existential restatement of Lemma 5.26.9 (1). -/
theorem exists_stonean_surjection :
    ∃ Y : Stonean.{u}, ∃ f : Y.compHaus ⟶ X, Function.Surjective f := by
  exact ⟨CompHaus.presentation X, CompHaus.presentation.π X, presentation_pi_surjective X⟩

end

section

variable {X : CompHaus.{u}} {Y Z : Stonean.{u}}
variable {f : Y.compHaus ⟶ X} {g : Z.compHaus ⟶ X}

-- Proof sketch: if `h : Y.compHaus ⟶ Z.compHaus` satisfies `h ≫ g = f`, then its image is closed
-- in `Z` because `Y` is compact and `Z` is Hausdorff, and it still surjects onto `X`, so
-- minimality of `g` makes `h` surjective. The same commutative-square relation shows that the
-- image of every proper closed subset of `Y` remains proper in `Z`, and the earlier chapter owner
-- theorem upgrades this to a homeomorphism.
/-- Lemma 5.26.9 (2): any morphism over `X` between two minimal Stonean surjections is a
homeomorphism. -/
theorem isHomeomorph_of_minimal_stonean_morphism_over
    (hf_surj : Function.Surjective f) (hg_surj : Function.Surjective g)
    (hf_min : ∀ E : Set Y, E ≠ (Set.univ : Set Y) → IsClosed E → f '' E ≠ (Set.univ : Set X))
    (hg_min : ∀ E : Set Z, E ≠ (Set.univ : Set Z) → IsClosed E → g '' E ≠ (Set.univ : Set X))
    {h : Y.compHaus ⟶ Z.compHaus} (hh : h ≫ g = f) :
    IsHomeomorph h := by
  let hTop : C(Y, Z) := TopCat.Hom.hom h.hom
  have hh_cont : Continuous h := by
    simpa [hTop] using hTop.continuous
  have hh_range_closed : IsClosed (Set.range h) := by
    rw [← Set.image_univ]
    exact (CompHausLike.isClosedMap h) _ isClosed_univ
  have hh_surj : Function.Surjective h := by
    rw [← Set.range_eq_univ]
    by_contra hnot
    have himage : g '' Set.range h = Set.univ := by
      refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
      rcases hf_surj x with ⟨y, rfl⟩
      refine ⟨h y, ⟨y, rfl⟩, ?_⟩
      change g (h y) = f y
      simpa using ConcreteCategory.congr_hom hh y
    exact (hg_min (Set.range h) (by simpa [Set.range_eq_univ] using hnot) hh_range_closed) himage
  refine isHomeomorph_of_extremallyDisconnected_of_surjective_of_image_proper_closed
    hh_cont hh_surj ?_
  intro E hE hE_closed h_image_univ
  have h_image : f '' E = g '' (h '' E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h y, ⟨y, hy, rfl⟩, by simpa using ConcreteCategory.congr_hom hh y⟩
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simpa using (ConcreteCategory.congr_hom hh y).symm⟩
  have : f '' E = Set.univ := by
    rw [h_image, h_image_univ]
    exact Set.image_univ_of_surjective hg_surj
  exact hf_min E hE hE_closed this

/-- Textbook restatement of Lemma 5.26.9 (2): two minimal Stonean surjections onto `X` are
homeomorphic over `X`. -/
theorem exists_homeomorph_over_of_minimal_stonean_surjections
    (hf_surj : Function.Surjective f) (hg_surj : Function.Surjective g)
    (hf_min : ∀ E : Set Y, E ≠ (Set.univ : Set Y) → IsClosed E → f '' E ≠ (Set.univ : Set X))
    (hg_min : ∀ E : Set Z, E ≠ (Set.univ : Set Z) → IsClosed E → g '' E ≠ (Set.univ : Set X)) :
    ∃ e : Y ≃ₜ Z, g ∘ e = f := by
  letI : Epi g := (CompHaus.epi_iff_surjective g).2 hg_surj
  rcases isHomeomorph_iff_exists_homeomorph.mp
      (isHomeomorph_of_minimal_stonean_morphism_over hf_surj hg_surj hf_min hg_min
        (CompHaus.lift_lifts f g)) with
    ⟨e, he⟩
  refine ⟨e, ?_⟩
  ext y
  calc
    g (e y) = g ((CompHaus.lift f g) y) := by simp [he]
    _ = f y := by
      change ((CompHaus.lift f g) ≫ g) y = f y
      exact ConcreteCategory.congr_hom (CompHaus.lift_lifts f g) y

end
