module

public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import stacks_project.Chap07.Lemma_7_26_4.HomPresheafTerminal

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- Helper for Lemma 7.26.4: the cover arrows in `Over U` generate the same covering sieve at the
terminal object `U/U` as the original cover `𝒰`. -/
theorem localized_cover_descent_cover_arrows_sieve_over_terminal
    (𝒰 : J.Cover U) :
    Sieve.overEquiv (Over.mk (𝟙 U))
      (Sieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
        (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)) =
      (𝒰 : Sieve U) := by
  -- Unpack membership in the generated slice-site sieve into a factorization through one
  -- of the chosen cover arrows, then forget the slice structure back to `C`.
  ext Z g
  rw [Sieve.overEquiv_iff, Sieve.mem_ofArrows_iff]
  constructor
  · rintro ⟨I, h, _⟩
    have hw : h.left ≫ I.f = g := by
      simpa using Over.w h
    exact hw ▸ (𝒰 : Sieve U).downward_closed I.hf h.left
  · intro hg
    let a : Over.mk (g ≫ (Over.mk (𝟙 U)).hom) ⟶ Over.mk g := Over.homMk (𝟙 Z) (by simp)
    refine ⟨⟨Z, g, hg⟩, a, ?_⟩
    ext
    simp [a]

/-- Helper for Lemma 7.26.4: the chosen cover `𝒰` induces an honest cover of the terminal object
`U/U` inside the localized site `J.over U`. -/
def localized_cover_descent_terminal_cover
    (𝒰 : J.Cover U) :
    (J.over U).Cover (Over.mk (𝟙 U)) :=
  ⟨Sieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
      (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f), by
    -- The generated slice-site sieve is exactly the original covering sieve on `U`.
    rw [J.mem_over_iff,
      localized_cover_descent_cover_arrows_sieve_over_terminal (J := J) (U := U) 𝒰]
    exact 𝒰.condition⟩

/-- Helper for Lemma 7.26.4: compatibility of sections for a family of base arrows
`f : Xᵢ ⟶ U` is equivalent to compatibility for the induced family of arrows
`Over.mk (f i) ⟶ Over.mk (𝟙 U)` in the localized site. This lets the source-compatible-family
formula talk directly to the existing slice-site sheaf API. -/
theorem localized_cover_descent_compatible_over_terminal_iff
    (P : Cᵒᵖ ⥤ Type w) {ι : Type*} {X : ι → C} (f : ∀ i, X i ⟶ U)
    (x : ∀ i, P.obj (Opposite.op (X i))) :
    Presieve.Arrows.Compatible P f x ↔
      Presieve.Arrows.Compatible ((Over.forget U).op ⋙ P)
        (fun i ↦ (show Over.mk (f i) ⟶ Over.mk (𝟙 U) from Over.homMk (f i))) x := by
  constructor
  · intro hx i j Z gi gj h
    -- Forgetting the slice equality reduces the compatibility check to the base category.
    exact hx i j Z.left gi.left gj.left (by simpa using (Over.forget U).congr_map h)
  · intro hx i j Z gi gj h
    -- Repackage the common composite `gi ≫ f i = gj ≫ f j` as an object of `Over U`.
    let Z' : Over U := Over.mk (gi ≫ f i)
    exact hx i j Z' (Over.homMk gi) (Over.homMk gj (by simpa [Z'] using h.symm)) (by
      ext
      simp [Z', h])

/-- Helper for Lemma 7.26.4: the sheaf condition for a presheaf on a family of base arrows
`f : Xᵢ ⟶ U` is equivalent to the sheaf condition for its restriction to the induced family
`Over.mk (f i) ⟶ Over.mk (𝟙 U)` in the localized site. This is the formal bridge from source-side
compatible families to the terminal-cover language used later in the proof. -/
theorem localized_cover_descent_isSheafFor_over_terminal_ofArrows_iff
    (P : Cᵒᵖ ⥤ Type w) {ι : Type*} (X : ι → C) (f : ∀ i, X i ⟶ U) :
    Presieve.IsSheafFor P (Presieve.ofArrows X f) ↔
      Presieve.IsSheafFor ((Over.forget U).op ⋙ P)
        (Presieve.ofArrows (fun i ↦ Over.mk (f i))
          (fun i ↦ (show Over.mk (f i) ⟶ Over.mk (𝟙 U) from Over.homMk (f i)))) := by
  rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible,
    Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      -- Equality of compatible families is detected pointwise on the original indices.
      apply h.1
      ext i
      exact congrFun (congrArg Subtype.val hxy) i
    · intro x
      -- Translate terminal-cover compatibility back to the base-arrow formulation, then solve
      -- the glued section using the original sheaf-condition bijection.
      obtain ⟨y, hy⟩ := h.2 ⟨x.1,
        (localized_cover_descent_compatible_over_terminal_iff
          (P := P) (f := f) x.1).2 x.2⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      ext i
      exact congrFun (congrArg Subtype.val hy) i
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      -- The reverse direction uses the same pointwise detection after passing to the slice site.
      apply h.1
      ext i
      exact congrFun (congrArg Subtype.val hxy) i
    · intro x
      -- Translate base compatibility into the terminal-cover version, glue there, and unwrap.
      obtain ⟨y, hy⟩ := h.2 ⟨x.1,
        (localized_cover_descent_compatible_over_terminal_iff
          (P := P) (f := f) x.1).1 x.2⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      ext i
      exact congrFun (congrArg Subtype.val hy) i

/-- Helper for Lemma 7.26.4: an arrow in the induced terminal cover of `U/U` comes from the
underlying arrow of the original cover `𝒰` after forgetting the slice-site packaging. -/
def localized_cover_descent_terminal_cover_arrow_base
    (𝒰 : J.Cover U)
    (I : (localized_cover_descent_terminal_cover (J := J) (U := U) 𝒰).Arrow) :
    𝒰.Arrow := by
  refine ⟨I.Y.left, I.f.left, ?_⟩
  -- Unpack the slice-site arrow as a factorization through one original cover member, then forget
  -- the slice structure to recover membership in the original covering sieve on `U`.
  have hf :
      (Sieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
        (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)) I.f := I.hf
  rw [Sieve.mem_ofArrows_iff] at hf
  rcases hf with ⟨J, a, ha⟩
  have hleft : I.f.left = a.left ≫ J.f := by
    have hfy : I.f.left = I.Y.hom := by
      simpa using Over.w I.f
    have hw : a.left ≫ J.f = I.Y.hom := by
      simpa [ha] using Over.w a
    exact hfy.trans hw.symm
  simpa [hleft] using (𝒰 : Sieve U).downward_closed J.hf a.left

/-- Helper for Lemma 7.26.4: after passing to the slice site `J.over I.Y`, the pullback cover
`𝒰.pullback I.f` induces the terminal cover of `I.Y / I.Y`. This is the cover whose one-hypercover
controls compatible local sections of `D.obj I`. -/
def localized_cover_descent_component_terminal_cover
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow) :
    ((J.over I.Y).Cover (Over.mk (𝟙 I.Y))) :=
  localized_cover_descent_terminal_cover (J := J) (U := I.Y) (𝒰.pullback I.f)

/-- Helper for Lemma 7.26.4: compatible families of sections of the component sheaf `D.obj I`
along the terminal cover induced by `𝒰.pullback I.f` are equivalent to actual sections of
`D.obj I` over `I.Y / I.Y`. This is the slice-site multiequalizer bridge needed for the component
comparison step of the glued-object construction. -/
noncomputable def localized_cover_descent_component_sections_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    ((((localized_cover_descent_component_terminal_cover
        (J := J) (U := U) 𝒰 I).oneHypercover).multicospanIndex ((D.obj I).1)).sections) ≃
      ((D.obj I).1.obj (Opposite.op (Over.mk (𝟙 I.Y)))) :=
  CategoryTheory.Limits.Multifork.IsLimit.sectionsEquiv
    (((localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).oneHypercover).isLimitMultifork (D.obj I))

/-- Helper for Lemma 7.26.4: evaluating the section reconstructed from a compatible family along
the induced terminal cover recovers the chosen local `K`-component. -/
theorem localized_cover_descent_component_sections_equiv_apply_val
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (s :
      (((localized_cover_descent_component_terminal_cover
        (J := J) (U := U) 𝒰 I).oneHypercover).multicospanIndex ((D.obj I).1)).sections)
    (K : (localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).Arrow) :
    (((localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).oneHypercover).multifork ((D.obj I).1)).ι K
      (localized_cover_descent_component_sections_equiv
        (J := J) (U := U) 𝒰 D I s) = s.val K := by
  -- The one-hypercover limit identifies the reconstructed global section by its components.
  simpa using CategoryTheory.Limits.Multifork.IsLimit.sectionsEquiv_apply_val
    (((localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).oneHypercover).isLimitMultifork (D.obj I)) s K

/-- Helper for Lemma 7.26.4: the inverse direction of the component-sections equivalence is
computed by the canonical multifork legs of the terminal cover induced by `𝒰.pullback I.f`. -/
theorem localized_cover_descent_component_sections_equiv_symm_apply_val
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (t : (D.obj I).1.obj (Opposite.op (Over.mk (𝟙 I.Y))))
    (K : (localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).Arrow) :
    ((localized_cover_descent_component_sections_equiv
      (J := J) (U := U) 𝒰 D I).symm t).val K =
      (((localized_cover_descent_component_terminal_cover
        (J := J) (U := U) 𝒰 I).oneHypercover).multifork ((D.obj I).1)).ι K t := by
  -- The inverse section is the multifork section cut out by the universal limit property.
  simpa using CategoryTheory.Limits.Multifork.IsLimit.sectionsEquiv_symm_apply_val
    (((localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).oneHypercover).isLimitMultifork (D.obj I)) t K

/-- Helper for Lemma 7.26.4: evaluating the pullback of a sheaf along `f : X ⟶ Y` at the
terminal object of `Over X` recovers the original sheaf evaluated at `Over.mk f`. -/
theorem localized_cover_descent_overMap_terminal_section_eq
    {X Y : C}
    (f : X ⟶ Y)
    (M : Sheaf (J.over Y) (Type w)) :
    (((J.overMapPullback (Type w) f).obj M).1.obj
      (Opposite.op (Over.mk (𝟙 X)))) =
      (M.1.obj (Opposite.op (Over.mk f))) := by
  -- Unfold the localized pullback and rewrite the pulled-back terminal object to `Over.mk f`.
  simp [localized_cover_descent_overMap_terminal_obj]

/-- Helper for Lemma 7.26.4: after pulling the component sheaf `D.obj I` back to `J.over T.left`,
compatible local sections on the pulled-back cover over `T` are equivalent to a section at `T`.
This is the arbitrary-`T` version of the component gluing step from the source proof. -/
abbrev localized_cover_descent_glue_component_source_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :=
  { s :
      ∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
        ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
          (Opposite.op (Over.mk K.f))) //
      Presieve.Arrows.Compatible
        (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1)
        (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
          (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f))
        s }

/-- Helper for Lemma 7.26.4: after restricting the future glued presheaf to a fixed cover member
`I`, its source-compatible-family value at `T : Over I.Y` should be compared against this
standard subtype of compatible sections of the pulled-back component sheaf. -/
noncomputable def localized_cover_descent_component_sections_equiv_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_component_source_over
      (J := J) (U := U) 𝒰 D I T ≃
      ((D.obj I).1.obj (Opposite.op T)) := by
  let P := (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1)
  let π :=
    fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
      (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f (by simp))
  have hsheaf :
      Presieve.IsSheafFor P
        (Presieve.ofArrows (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ Over.mk K.f) π) := by
    -- The pulled-back component is a sheaf on `J.over T.left`, so it satisfies the sheaf
    -- condition for the induced terminal cover coming from the pulled-back base-site cover.
    rw [Presieve.isSheafFor_iff_generate]
    simpa [P, π, localized_cover_descent_terminal_cover] using
      (Presheaf.IsSheaf.isSheafFor
        (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).2)
        ((localized_cover_descent_terminal_cover
          (J := J) (U := T.left) ((𝒰.pullback I.f).pullback T.hom)).1)
        ((localized_cover_descent_terminal_cover
          (J := J) (U := T.left) ((𝒰.pullback I.f).pullback T.hom)).condition))
  let hbij :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible P π).mp hsheaf
  let hterminal :
      (P.obj (Opposite.op (Over.mk (𝟙 T.left)))) ≃
        ((D.obj I).1.obj (Opposite.op T)) :=
    (Equiv.cast
      (by
        simpa using
          localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := T.hom) (M := D.obj I)))
  -- First use the sheaf condition on the pulled-back component sheaf, then identify the
  -- resulting terminal section with a section of `(D.obj I).1` at `T`.
  exact (Equiv.ofBijective (Presieve.Arrows.toCompatible P π) hbij).symm.trans hterminal

/-- Helper for Lemma 7.26.4: this is the named Step 2 bridge from Agent C's plan. Once the
future glued presheaf is restricted to `I`, the remaining objectwise comparison is exactly the
compatible-family equivalence already proved for the pulled-back component sheaf. -/
noncomputable def localized_cover_descent_glue_component_equiv_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_component_source_over
      (J := J) (U := U) 𝒰 D I T ≃
      ((D.obj I).1.obj (Opposite.op T)) := by
  -- This is exactly the arbitrary-`T` component gluing equivalence just established above.
  exact localized_cover_descent_component_sections_equiv_over (J := J) (U := U) 𝒰 D I T

/-- Helper for Lemma 7.26.4: specializing the arbitrary-`T` component comparison to the terminal
object of `Over I.Y` gives the exact terminal-section equivalence that will be used later when the
glued presheaf is compared with `D.obj I` on the basic cover member `I`. -/
noncomputable def localized_cover_descent_glue_component_terminal_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_glue_component_source_over
      (J := J) (U := U) 𝒰 D I (Over.mk (𝟙 I.Y)) ≃
      ((D.obj I).1.obj (Opposite.op (Over.mk (𝟙 I.Y)))) := by
  -- This is the same objectwise comparison as above, now frozen at the terminal slice object.
  simpa using
    localized_cover_descent_glue_component_equiv_over
      (J := J) (U := U) 𝒰 D I (Over.mk (𝟙 I.Y))


end

end GrothendieckTopology
end CategoryTheory
