module

public import stacks_project.Chap07.Lemma_7_17_10.Glue

@[expose] public section

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open CategoryTheory Limits Opposite
open CategoryTheory.GrothendieckTopology

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {K : Precoverage C}
variable [K.HasPullbacks] [K.IsStableUnderBaseChange]
variable [HasWeakSheafify K.toCoverage.toGrothendieck (Type (max u v))]

local notation "J" => K.toCoverage.toGrothendieck

section

variable (β : Ordinal.{max u v}) (F : Set.Iio β ⥤ Sheaf K.toCoverage.toGrothendieck (Type (max u v)))
variable (hcover : ∀ (U : C) (R : Presieve U),
  R ∈ K U → Cardinal.lift (Cardinal.mk R.uncurry) < β.cof)

include F

include hcover

/-- Helper for Lemma 7.17.10: the presheaf colimit is a sheaf for a single `K`-covering presieve
once all representatives and overlap witnesses are synchronized in one ordinal stage.

This is the source-facing local sheaf condition used in the Stacks proof: for a chosen covering
presieve `R`, sufficiently large cofinality lets us choose one common ordinal stage for all local
sections and all pairwise overlap equalities. The previous attempted proof introduced a stronger
fixed-target pullback-branch bridge; that bridge is not part of the source statement and was the
source of the bad local statement. -/
lemma presheafColimit_isSheafFor_of_coveringPresieveCardinal_lt_cof
    {U : C} {R : Presieve U} (hR : R ∈ K U) :
    Presieve.IsSheafFor (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))) R := by
  -- Route correction: reduce the local sheaf condition on `R` to an explicit arrow family indexed
  -- by `R.uncurry`, then synchronize representatives and overlap equalities exactly as in the
  -- Stacks proof.
  rw [presieve_eq_of_uncurry (β := β) (hcover := hcover) R, Presieve.isSheafFor_arrows_iff]
  intro x hx
  have hsep :
      Presieve.IsSeparatedFor
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        R :=
    presheafColimit_isSeparatedFor_of_coveringPresieveCardinal_lt_cof
      (β := β)
      (F := F)
      (hcover := hcover)
      hR
  -- Choose stagewise representatives for the given compatible family of colimit sections.
  choose b t ht using
    fun i : R.uncurry ↦
      presheafColimit_section_exists_rep
        (β := β)
        (F := F)
        i.1.1
        (x i)
  obtain ⟨a, s, hs_image⟩ :=
    presheafColimit_common_stage_of_small_sections
      (β := β)
      (F := F)
      (hcover := hcover)
      (x := x)
      (b := b)
      (t := t)
      (ht := ht)
      (hι := hcover U R hR)
  -- Choose the canonical pullback cover over each branch of `R`.
  choose T hT hTfac using
    fun i : R.uncurry ↦ K.toCoverage.pullback i.1.2 R hR
  choose rightObj grToRight rightMap hright hright_comm using
    fun q : Σ i : R.uncurry, (T i).uncurry ↦ hTfac q.1 q.2.2
  let right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry := fun q ↦
    ⟨⟨rightObj q, rightMap q⟩, hright q⟩
  let gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1 :=
    fun q ↦ grToRight q
  have hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2 := fun q ↦
    (hright_comm q).symm
  obtain ⟨d, v', hv_image, hfirst⟩ :=
    presheafColimit_common_stage_of_small_overlaps
      (β := β)
      (F := F)
      (hcover := hcover)
      (x := x)
      (hx := hx)
      (s := s)
      (hs_image := hs_image)
      (left := fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.1)
      (right := right)
      (Z := fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.1)
      (gl := fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.2)
      (gr := gr)
      (hcomm := hcomm)
      (hι :=
        coveringPresieve_small_sigma_family
          (β := β)
          (hcover := hcover)
          (hR := hR)
          T
          hT)
  -- Pull back the first-level branch covers once more so the fixed-target overlap equalities can
  -- be synchronized in one later stage.
  choose B hB hBfac using
    fun q : Σ i : R.uncurry, (T i).uncurry ↦
      K.toCoverage.pullback q.2.1.2 (T q.1) (hT q.1)
  have hκsmall :
      Cardinal.lift (Cardinal.mk (targeted_secondary_owner_index (T := T) B)) < β.cof :=
    targeted_secondary_owner_index_small
      (β := β)
      (hcover := hcover)
      (hR := hR)
      T
      hT
      B
      hB
  obtain ⟨Cbase, hCbase, baseRight, baseGr, hbaseComp, e, hde, w, hw_def, hw_image, hbase_e,
      htarget_e⟩ :=
    presheafColimit_common_stage_of_refined_target_overlap_equalities
      (β := β)
      (F := F)
      (hcover := hcover)
      (hR := hR)
      (x := x)
      (hx := hx)
      (v' := v')
      (hv_image := hv_image)
      T
      hT
      right
      gr
      hcomm
      B
      hB
      hκsmall
  have hfirst_e :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj e).1.map q.2.1.2.op) (w q.1) =
          ((F.obj e).1.map (gr q).op) (w (right q)) :=
    by
      have htransport :=
        stage_family_first_level_pullback_equalities_at_later_stage
          (β := β)
          (F := F)
          (hcover := hcover)
          T
          right
          gr
          hde
          v'
          hfirst
      intro q
      rw [hw_def q.1, hw_def (right q)]
      exact htransport q
  have hsigma_compatible :
      Presieve.Arrows.Compatible
        ((F.obj e).1)
        (fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.2 ≫ q.1.1.2)
        (fun q ↦ ((F.obj e).1.map q.2.1.2.op) (w q.1)) :=
    stage_family_sigma_refinement_compatible_of_base_cover_owner_equalities
      (β := β)
      (F := F)
      (K := K)
      (hcover := hcover)
      T
      hT
      right
      gr
      B
      hB
      w
      hfirst_e
      htarget_e
  have hsigma :
      Presieve.IsSheafFor
        ((F.obj e).1)
        (Presieve.bindOfArrows
          (fun i : R.uncurry ↦ i.1.1)
          (fun i ↦ i.1.2)
          T) :=
    stage_sheaf_isSheafFor_sigma_refinement
      (β := β)
      (F := F)
      (K := K)
      (hcover := hcover)
      (hR := hR)
      T
      hT
  rw [sigma_refinement_eq_ofArrows (β := β) (F := F) (hcover := hcover) T,
    Presieve.isSheafFor_arrows_iff] at hsigma
  obtain ⟨te, hte, _⟩ := hsigma
    (fun q : Σ i : R.uncurry, (T i).uncurry ↦ ((F.obj e).1.map q.2.1.2.op) (w q.1))
    hsigma_compatible
  have hte_base :
      ∀ i : R.uncurry, ((F.obj e).1.map i.1.2.op) te = w i :=
    sigma_refinement_stage_glue_restricts_to_base_family
      (β := β)
      (F := F)
      (K := K)
      (hcover := hcover)
      T
      hT
      w
      te
      hte
  let z :=
    ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) e).app (op U)) te
  have hz :
      ∀ i : R.uncurry,
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map i.1.2.op z = x i := by
    intro i
    -- The glued stage section maps to an amalgamation of the original colimit family.
    simpa [z] using
      presheafColimit_stage_glue_image_is_amalgamation
        (β := β)
        (F := F)
        (hcover := hcover)
        (x := x)
        (v := w)
        (hv_image := hw_image)
        (tc := te)
        (htc := hte_base)
        i
  refine ⟨z, hz, ?_⟩
  · intro z' hz'
    -- Uniqueness is exactly the separatedness of the presheaf colimit on `R`.
    apply hsep.ext
    intro Y f hf
    let i : R.uncurry := ⟨⟨Y, f⟩, hf⟩
    simpa [i] using ((hz i).trans (hz' i).symm).symm


end

end CategoryTheory
