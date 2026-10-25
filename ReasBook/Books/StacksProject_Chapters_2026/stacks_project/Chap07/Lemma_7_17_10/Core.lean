module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option backward.isDefEq.respectTransparency false

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open CategoryTheory.GrothendieckTopology

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {K : Precoverage C}
variable [K.HasPullbacks] [K.IsStableUnderBaseChange]
variable [HasWeakSheafify K.toCoverage.toGrothendieck (Type (max u v))]

local notation "J" => K.toCoverage.toGrothendieck

/- Domain-style sampling for Lemma 7.17.10:
- primary domain: filtered colimits of `Type`-valued sheaves on a site presented by a precoverage,
  specialized to ordinal-indexed diagrams and controlled by ordinal cofinality;
- sampled owner abstractions:
  `Precoverage.toCoverage.toGrothendieck`,
  `sheafFilteredColimitSectionsComparison_injective_of_quasiCompactObject`,
  `Ordinal.iSup_lt_of_lt_cof`,
  `colimit.post`;
- source/core/bridge triage:
  `source-facing`: the ordinal parameter `β` and the cardinal bound
  `Cardinal.lift (Cardinal.mk R.uncurry) < β.cof` on `K`-covering presieves;
  `core/canonical`: the section-comparison morphism
  `colimit.post F ((sheafSections J (Type (max u v))).obj (op U))` together with
  the filtered comparison owner family already isolated in Lemma 7.17.7;
  `bridge/view`: passing from the chosen precoverage `K` to the associated Grothendieck topology, and
  from a `< β.cof`-small family of local stages to one common stage of the ordinal diagram using
  cofinality.

Primitive data are only the ordinal diagram `F` and the source cardinal bound `hcover`. The
comparison morphism is derived API, and the ambient owner family in the chapter is still the
filtered-colimit comparison of Lemma 7.17.7. There is no upstream owner for the exact
small-cover cofinality condition, so that hypothesis should remain explicit rather than being
collapsed into the different quasi-compact-overlap owner from Lemma 7.17.7.
-/
-- Proof sketch: argue directly with the source small-cover hypothesis. Injectivity comes from the
-- filtered-colimit comparison for sheaf sections, while surjectivity is obtained by representing a
-- target section on a `K`-covering presieve of cardinality `< β.cof`, then using ordinal
-- cofinality to dominate all local stages by one stage of `F`. The empty-index case `β = 0`
-- remains a separate degenerate argument.

section

variable (β : Ordinal.{max u v}) (F : Set.Iio β ⥤ Sheaf K.toCoverage.toGrothendieck (Type (max u v)))
variable (hcover : ∀ (U : C) (R : Presieve U),
  R ∈ K U → Cardinal.lift (Cardinal.mk R.uncurry) < β.cof)

include F

/-- Helper for module-mode elaboration: a section of a stage sheaf, viewed as a section of the
corresponding object of the composed underlying-presheaf diagram. -/
def stageSectionAsPresheaf {a : Set.Iio β} {U : C} :
    (F.obj a).obj.obj (op U) →
      ((F ⋙ sheafToPresheaf J (Type (max u v))).obj a).obj (op U) :=
  id

/-- Helper for Lemma 7.17.10: the chosen sheaf colimit is canonically the sheafification of the
underlying presheaf colimit. -/
noncomputable def presheafColimitToSheafIso
    [hcolim : HasColimit F]
    [HasColimit (F ⋙ sheafToPresheaf J (Type (max u v)))] :
    ((presheafToSheaf J (Type (max u v))).obj
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))) ≅ @colimit _ _ _ _ F hcolim :=
  (colimit.isoColimitCocone
    ⟨Sheaf.sheafifyCocone
        (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).symm

/-- Helper for Lemma 7.17.10: the source filtered colimit of sections over `U` is the evaluation
of the presheaf-colimit comparison at `U`. -/
theorem section_colimit_post_eq_eval
    (U : C)
    [HasColimit F]
    [HasColimit (F ⋙ (sheafSections J (Type (max u v))).obj (op U))]
    [HasColimit (F ⋙ sheafToPresheaf J (Type (max u v)))] :
    colimit.post F ((sheafSections J (Type (max u v))).obj (op U)) =
      colimit.post (F ⋙ sheafToPresheaf J (Type (max u v)))
          ((evaluation Cᵒᵖ (Type (max u v))).obj (op U)) ≫
        (colimit.post F (sheafToPresheaf J (Type (max u v)))).app (op U) := by
  -- The sections functor is the composite of the forgetful functor with evaluation at `U`.
  simpa using
    (colimit.post_post F (sheafToPresheaf J (Type (max u v)))
      ((evaluation Cᵒᵖ (Type (max u v))).obj (op U))).symm

/-- Helper for Lemma 7.17.10: restriction commutes with each transition map in the ordinal-indexed
sheaf diagram. -/
theorem sheaf_transition_app_map_eq_map_app
    {i j : Set.Iio β} (f : i ⟶ j)
    {U V : C} (g : V ⟶ U) (a : (F.obj i).1.obj (op U)) :
    ((F.map f).1.app (op V)) (((F.obj i).1.map g.op) a) =
      ((F.obj j).1.map g.op) (((F.map f).1.app (op U)) a) := by
  -- This is exactly the naturality square of the underlying presheaf map.
  simpa [Function.comp] using congrFun ((F.map f).1.naturality g.op) a

include hcover

omit hcover in
/-- Helper for Lemma 7.17.10: a `< β.cof`-small family of stages in the ordinal diagram admits
one common upper stage below `β`. -/
lemma coveringPresieve_common_stage_of_small_family
    {ι : Type (max u v)} (f : ι → Ordinal.{max u v})
    (hf : ∀ i, f i < β)
    (hι : Cardinal.lift (Cardinal.mk ι) < β.cof) :
    ∃ a : Set.Iio β, ∀ i, f i ≤ a.1 := by
  -- Pass to an explicit `ULift`-indexed supremum so `Ordinal.iSup_lt_of_lt_cof` matches the
  -- source cardinal bound without any further universe transport.
  have hiSup : ⨆ i : ULift.{max u v} ι, f i.down < β := by
    have hι' : Cardinal.mk (ULift.{max u v} ι) < β.cof := by
      simpa using hι
    simpa using Ordinal.iSup_lt_of_lt_cof hι' (fun i : ULift.{max u v} ι => hf i.down)
  refine ⟨⟨⨆ i, f i, ?_⟩, ?_⟩
  · simpa using hiSup
  · intro i
    exact Ordinal.le_iSup f i

omit hcover in
/-- Helper for Lemma 7.17.10: every section of the presheaf colimit is represented by one stage of
the ordinal diagram after evaluating at a fixed object. -/
lemma presheafColimit_section_exists_rep
    (U : C)
    (x : (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op U)) :
    ∃ i : Set.Iio β, ∃ s : (F.obj i).1.obj (op U),
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i).app (op U)) s = x := by
  -- Evaluate the presheaf colimit pointwise, represent the resulting element there, and then
  -- transport the representative back through the pointwise-colimit comparison isomorphism.
  let e := asIso (colimit.post (F ⋙ sheafToPresheaf J (Type (max u v)))
    ((evaluation Cᵒᵖ (Type (max u v))).obj (op U)))
  obtain ⟨i, s, hs⟩ :=
    Concrete.colimit_exists_rep
      ((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
        (evaluation Cᵒᵖ (Type (max u v))).obj (op U))
      (e.inv x)
  refine ⟨i, s, ?_⟩
  apply_fun e.hom at hs
  have hι :
      e.hom
          ((colimit.ι
              ((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
                (evaluation Cᵒᵖ (Type (max u v))).obj (op U)) i) s) =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i).app (op U)) s := by
    change
      ((colimit.ι
            ((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
              (evaluation Cᵒᵖ (Type (max u v))).obj (op U)) i ≫
          colimit.post (F ⋙ sheafToPresheaf J (Type (max u v)))
            ((evaluation Cᵒᵖ (Type (max u v))).obj (op U))) s) =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i).app (op U)) s
    rw [colimit.ι_post]
    rfl
  have hright : e.hom (e.inv x) = x := by
    simpa using congrFun e.inv_hom_id x
  exact hι.symm.trans (hs.trans hright)

omit hcover in
/-- Helper for Lemma 7.17.10: if two sections represented at one stage become equal in the
presheaf colimit, then they already become equal after passing to a later ordinal stage. -/
lemma presheafColimit_section_eq_at_later_stage
    (U : C) {i : Set.Iio β}
    {s t : (F.obj i).1.obj (op U)}
    (h :
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i).app (op U)) s =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i).app (op U)) t) :
    ∃ j : Set.Iio β, ∃ f : i ⟶ j,
      ((F.map f).1.app (op U)) s = ((F.map f).1.app (op U)) t := by
  -- Move the equality to the pointwise colimit, use filtered-colimit equality there, and then
  -- exploit thinness of `Set.Iio β` so both comparison maps land in the same later stage.
  let e := asIso (colimit.post (F ⋙ sheafToPresheaf J (Type (max u v)))
    ((evaluation Cᵒᵖ (Type (max u v))).obj (op U)))
  have h' :
      colimit.ι
          (((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
            (evaluation Cᵒᵖ (Type (max u v))).obj (op U))) i s =
        colimit.ι
          (((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
            (evaluation Cᵒᵖ (Type (max u v))).obj (op U))) i t := by
    haveI : Nonempty (Set.Iio β) := ⟨i⟩
    have hinj : Function.Injective e.hom :=
      (ConcreteCategory.bijective_of_isIso e.hom).1
    refine hinj ?_
    have hι (a : (F.obj i).1.obj (op U)) :
        e.hom
            ((colimit.ι
                ((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
                  (evaluation Cᵒᵖ (Type (max u v))).obj (op U)) i) a) =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i).app (op U)) a := by
      change
        ((colimit.ι
              ((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
                (evaluation Cᵒᵖ (Type (max u v))).obj (op U)) i ≫
            colimit.post (F ⋙ sheafToPresheaf J (Type (max u v)))
              ((evaluation Cᵒᵖ (Type (max u v))).obj (op U))) a) =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i).app (op U)) a
      rw [colimit.ι_post]
      rfl
    simpa [hι] using h
  obtain ⟨j, f, g, hfg⟩ :=
    letI : Nonempty (Set.Iio β) := ⟨i⟩
    letI : IsDirectedOrder (Set.Iio β) :=
      ⟨by
        intro a b
        by_cases hab : a ≤ b
        · exact ⟨b, hab, le_rfl⟩
        · exact ⟨a, le_rfl, le_of_not_ge hab⟩⟩
    Concrete.colimit_exists_of_rep_eq
      (((F ⋙ sheafToPresheaf J (Type (max u v))) ⋙
        (evaluation Cᵒᵖ (Type (max u v))).obj (op U))) s t h'
  have hfg' : ((F.map f).1.app (op U)) s = ((F.map g).1.app (op U)) t := by
    simpa using hfg
  exact ⟨j, f, by simpa [Subsingleton.elim g f] using hfg'⟩

omit F in
/-- Helper for Lemma 7.17.10: the pair index of a `< β.cof`-small covering presieve is still
`< β.cof`. -/
lemma coveringPresieve_small_overlap_index
    {U : C} {R : Presieve U} (hR : R ∈ K U) :
    Cardinal.lift (Cardinal.mk (R.uncurry × R.uncurry)) < β.cof := by
  -- The source hypothesis already bounds the arrow index of the covering presieve itself.
  have hRsmall : HasCardinalLT R.uncurry β.cof := by
    simpa [HasCardinalLT] using hcover U R hR
  by_cases hne : Nonempty R.uncurry
  · -- A nonempty cover index forces `β.cof` to be infinite, so products stay small.
    have hβone : 1 < β.cof := by
      have hmk_ne_zero : Cardinal.mk R.uncurry ≠ 0 := Cardinal.mk_ne_zero_iff.mpr hne
      have hne0 : Cardinal.lift (Cardinal.mk R.uncurry) ≠ 0 := by
        simpa [Cardinal.lift_eq_zero] using hmk_ne_zero
      have hone : 1 ≤ Cardinal.lift (Cardinal.mk R.uncurry) :=
        Cardinal.one_le_iff_ne_zero.mpr hne0
      exact lt_of_le_of_lt hone (hcover U R hR)
    have hβinf : Cardinal.aleph0 ≤ β.cof := by
      exact (Ordinal.aleph0_le_cof).2 ((Ordinal.one_lt_cof_iff).1 hβone)
    have hprod : HasCardinalLT (R.uncurry × R.uncurry) β.cof :=
      hasCardinalLT_prod hβinf hRsmall hRsmall
    simpa [HasCardinalLT] using hprod
  · -- If the cover index is empty, then the pair index is empty as well.
    haveI : IsEmpty R.uncurry := not_nonempty_iff.mp hne
    haveI : IsEmpty (R.uncurry × R.uncurry) := by infer_instance
    have hβpos : 0 < β.cof := by
      simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using (hcover U R hR)
    simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using hβpos

omit F in
/-- Helper for Lemma 7.17.10: the sigma-family of first-level pullback covers chosen over a
covering presieve is still `< β.cof`. -/
lemma coveringPresieve_small_sigma_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1) :
    Cardinal.lift (Cardinal.mk (Σ i : R.uncurry, (T i).uncurry)) < β.cof := by
  by_cases hne : Nonempty R.uncurry
  · -- A nonempty cover index forces `β.cof` to be regular enough for sigma-smallness.
    have hRsmall : HasCardinalLT R.uncurry β.cof := by
      simpa [HasCardinalLT] using hcover U R hR
    have hβone : 1 < β.cof := by
      have hmk_ne_zero : Cardinal.mk R.uncurry ≠ 0 := Cardinal.mk_ne_zero_iff.mpr hne
      have hne0 : Cardinal.lift (Cardinal.mk R.uncurry) ≠ 0 := by
        simpa [Cardinal.lift_eq_zero] using hmk_ne_zero
      have hone : 1 ≤ Cardinal.lift (Cardinal.mk R.uncurry) :=
        Cardinal.one_le_iff_ne_zero.mpr hne0
      exact lt_of_le_of_lt hone (hcover U R hR)
    letI : Fact β.cof.IsRegular :=
      ⟨Cardinal.isRegular_cof ((Ordinal.one_lt_cof_iff).1 hβone)⟩
    have hTsmall : ∀ i : R.uncurry, HasCardinalLT (T i).uncurry β.cof := by
      intro i
      simpa [HasCardinalLT] using hcover i.1.1 (T i) (hT i)
    have hσ : HasCardinalLT (Σ i : R.uncurry, (T i).uncurry) β.cof :=
      hasCardinalLT_sigma (fun i : R.uncurry ↦ (T i).uncurry) β.cof hRsmall hTsmall
    simpa [HasCardinalLT] using hσ
  · -- If the original cover index is empty, then the sigma family is empty as well.
    haveI : IsEmpty R.uncurry := not_nonempty_iff.mp hne
    haveI : IsEmpty (Σ i : R.uncurry, (T i).uncurry) := by infer_instance
    have hβpos : 0 < β.cof := by
      simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using (hcover U R hR)
    simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using hβpos

omit F in
/-- Helper for Lemma 7.17.10: a `< β.cof`-small index family of `< β.cof`-small fibers has
`< β.cof`-small sigma total space. -/
lemma small_sigma_of_small_family
    {ι : Type (max u v)} (X : ι → Type (max u v))
    (hι : Cardinal.lift (Cardinal.mk ι) < β.cof)
    (hX : ∀ i, Cardinal.lift (Cardinal.mk (X i)) < β.cof) :
    Cardinal.lift (Cardinal.mk (Σ i, X i)) < β.cof := by
  by_cases hne : Nonempty ι
  · -- A nonempty small index family forces `β.cof` to be regular enough for sigma-smallness.
    have hιsmall : HasCardinalLT ι β.cof := by
      simpa [HasCardinalLT] using hι
    have hβone : 1 < β.cof := by
      have hmk_ne_zero : Cardinal.mk ι ≠ 0 := Cardinal.mk_ne_zero_iff.mpr hne
      have hne0 : Cardinal.lift (Cardinal.mk ι) ≠ 0 := by
        simpa [Cardinal.lift_eq_zero] using hmk_ne_zero
      have hone : 1 ≤ Cardinal.lift (Cardinal.mk ι) :=
        Cardinal.one_le_iff_ne_zero.mpr hne0
      exact lt_of_le_of_lt hone hι
    letI : Fact β.cof.IsRegular :=
      ⟨Cardinal.isRegular_cof ((Ordinal.one_lt_cof_iff).1 hβone)⟩
    have hXsmall : ∀ i, HasCardinalLT (X i) β.cof := by
      intro i
      simpa [HasCardinalLT] using hX i
    have hσ : HasCardinalLT (Σ i, X i) β.cof :=
      hasCardinalLT_sigma X β.cof hιsmall hXsmall
    simpa [HasCardinalLT] using hσ
  · -- If there are no indices, then the sigma family is empty as well.
    haveI : IsEmpty ι := not_nonempty_iff.mp hne
    haveI : IsEmpty (Σ i, X i) := by infer_instance
    have hβpos : 0 < β.cof := by
      simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using hι
    simpa [Cardinal.mk_eq_zero _, Cardinal.lift_zero] using hβpos

omit F in
/-- Helper for Lemma 7.17.10: once the first-level sigma family of pullback-cover branches is
`< β.cof`, any chosen secondary pullback covers over those branches still form a `< β.cof`-small
owner family. -/
lemma coveringPresieve_small_secondary_sigma_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1) :
    Cardinal.lift (Cardinal.mk (Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry)) < β.cof := by
  -- Reuse the first-level sigma bound and the original small-cover hypothesis fiberwise.
  let ι' : Type (max u v) := Σ i : R.uncurry, (T i).uncurry
  refine
    small_sigma_of_small_family
      (C := C)
      (K := K)
      (β := β)
      (hcover := hcover)
      (ι := ι')
      (X := fun q : ι' ↦ (B q).uncurry)
      (hι := coveringPresieve_small_sigma_family
        (β := β)
        (hcover := hcover)
        (hR := hR)
        T
        hT)
      ?_
  intro q
  simpa [ι'] using hcover q.2.1.1 (B q) (hB q)

omit F hcover in
/-- Helper for Lemma 7.17.10: package one retained secondary branch together with a fixed
comparison branch of the original cover `R`. -/
def targeted_secondary_owner_index
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1) :
    Type (max u v) :=
  Σ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry, R.uncurry

omit F in
/-- Helper for Lemma 7.17.10: after adjoining one original-cover branch to each retained
secondary branch, the resulting targeted owner family is still `< β.cof`. -/
lemma coveringPresieve_small_targeted_secondary_sigma_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1) :
    Cardinal.lift
        (Cardinal.mk
          (Σ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry, R.uncurry)) <
      β.cof := by
  let κ : Type (max u v) := Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry
  -- First keep the old synchronized secondary owner family small.
  refine
    small_sigma_of_small_family
      (C := C)
      (K := K)
      (β := β)
      (hcover := hcover)
      (ι := κ)
      (X := fun _ : κ ↦ R.uncurry)
      (hι := by
        simpa [κ] using
          coveringPresieve_small_secondary_sigma_family
            (β := β)
            (hcover := hcover)
            (hR := hR)
            T
            hT
            B
            hB)
      ?_
  intro _
  -- Then use the original small-cover bound for the retained comparison branch.
  simpa using hcover U R hR

omit F in
/-- Helper for Lemma 7.17.10: the targeted owner index that remembers a fixed comparison branch
of `R` is still `< β.cof`. -/
lemma targeted_secondary_owner_index_small
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1) :
    Cardinal.lift (Cardinal.mk (targeted_secondary_owner_index (T := T) B)) < β.cof := by
  -- Unfold the dedicated index packaging once, then reuse the existing targeted sigma bound
  -- without asking `simp` to normalize the large sigma type on its own.
  change
    Cardinal.lift
        (Cardinal.mk
          (Σ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry, R.uncurry)) <
      β.cof
  exact
    coveringPresieve_small_targeted_secondary_sigma_family
      (β := β)
      (hcover := hcover)
      (hR := hR)
      T
      hT
      B
      hB

omit F in
/-- Helper for Lemma 7.17.10: if each retained secondary branch carries one extra covering
presieve over its own source, the resulting sigma owner family is still `< β.cof`. -/
lemma coveringPresieve_small_targeted_secondary_pullback_owner_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (C' : ∀ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry, Presieve p.2.1.1)
    (hC' : ∀ p, C' p ∈ K p.2.1.1) :
    Cardinal.lift
        (Cardinal.mk
          (Σ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry, (C' p).uncurry)) <
      β.cof := by
  let κ : Type (max u v) := Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry
  -- Keep the already-synchronized secondary owner family small, then apply the original cover
  -- bound fiberwise to the new pullback owners.
  refine
    small_sigma_of_small_family
      (C := C)
      (K := K)
      (β := β)
      (hcover := hcover)
      (ι := κ)
      (X := fun p : κ ↦ (C' p).uncurry)
      (hι := by
        simpa [κ] using
          coveringPresieve_small_secondary_sigma_family
            (β := β)
            (hcover := hcover)
            (hR := hR)
            T
            hT
            B
            hB)
      ?_
  intro p
  simpa [κ] using hcover p.2.1.1 (C' p) (hC' p)

omit F in
/-- Helper for Lemma 7.17.10: once a fixed comparison branch `j` is adjoined to each retained
secondary owner, any further family of pullback covers over those fixed-target owners is still
`< β.cof`. -/
lemma coveringPresieve_small_fixed_target_pullback_owner_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (C' : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1)
    (hC' : ∀ p, C' p ∈ K p.1.2.1.1) :
    Cardinal.lift
        (Cardinal.mk
          (Σ p : targeted_secondary_owner_index (T := T) B, (C' p).uncurry)) <
      β.cof := by
  let κ : Type (max u v) := targeted_secondary_owner_index (T := T) B
  -- First keep the fixed-target owner family small using the earlier targeted sigma bound.
  refine
    small_sigma_of_small_family
      (C := C)
      (K := K)
      (β := β)
      (hcover := hcover)
      (ι := κ)
      (X := fun p : κ ↦ (C' p).uncurry)
      (hι := by
        simpa [κ] using
          targeted_secondary_owner_index_small
            (β := β)
            (hcover := hcover)
            (hR := hR)
            T
            hT
            B
            hB)
      ?_
  intro p
  -- Then apply the original small-cover hypothesis fiberwise to the chosen pullback cover.
  simpa [κ] using hcover p.1.2.1.1 (C' p) (hC' p)

omit F in
/-- Helper for Lemma 7.17.10: one can choose a canonical pullback cover over every fixed-target
owner, and the resulting sigma owner family is still `< β.cof`. -/
lemma targeted_secondary_owner_has_small_pullback_owner_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1) :
    ∃ C' : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1,
      (∀ p, C' p ∈ K p.1.2.1.1) ∧
      (∀ p, (C' p).FactorsThruAlong (B p.1.1) p.1.2.1.2) ∧
      Cardinal.lift
          (Cardinal.mk
            (Σ p : targeted_secondary_owner_index (T := T) B, (C' p).uncurry)) <
        β.cof := by
  let κtarget : Type (max u v) := targeted_secondary_owner_index (T := T) B
  -- Pull back the retained secondary cover along each remembered secondary branch.
  choose C' hC' hC'fac using
    fun p : κtarget ↦ K.toCoverage.pullback p.1.2.1.2 (B p.1.1) (hB p.1.1)
  refine ⟨C', hC', hC'fac, ?_⟩
  -- The earlier fixed-target smallness lemma applies to this canonical pullback family.
  simpa [κtarget] using
    coveringPresieve_small_fixed_target_pullback_owner_family
      (β := β)
      (hcover := hcover)
      (hR := hR)
      T
      hT
      B
      hB
      C'
      hC'

omit F in
/-- Helper for Lemma 7.17.10: if each retained secondary owner is equipped with an actual map to
its remembered target branch of `R`, then the corresponding family of target-side pullback covers
is still `< β.cof`.

This isolates the structural datum missing from the current blocked proof: the existing
`targeted_secondary_owner_index` remembers only the branch `j : R.uncurry`, not a morphism from the
owner source to `j.1.1`. Once that morphism is part of the index, the target-pullback smallness
step is immediate. -/
lemma targeted_secondary_owner_has_small_fixed_target_pullback_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (targetMap :
      ∀ p : targeted_secondary_owner_index (T := T) B, p.1.2.1.1 ⟶ p.2.1.1) :
    ∃ Ctarget : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1,
      (∀ p, Ctarget p ∈ K p.1.2.1.1) ∧
      (∀ p, (Ctarget p).FactorsThruAlong (T p.2) (targetMap p)) ∧
      Cardinal.lift
          (Cardinal.mk
            (Σ p : targeted_secondary_owner_index (T := T) B, (Ctarget p).uncurry)) <
        β.cof := by
  let κtarget : Type (max u v) := targeted_secondary_owner_index (T := T) B
  -- Route correction: once the source-to-target branch map is explicit, the target-side pullback
  -- family is obtained by a direct coverage pullback over each fixed target branch.
  choose Ctarget hCtarget hCtargetfac using
    fun p : κtarget ↦ K.toCoverage.pullback (targetMap p) (T p.2) (hT p.2)
  refine ⟨Ctarget, hCtarget, hCtargetfac, ?_⟩
  -- The existing fixed-target owner cardinal bound applies to any such family of pullback covers.
  simpa [κtarget] using
    coveringPresieve_small_fixed_target_pullback_owner_family
      (β := β)
      (hcover := hcover)
      (hR := hR)
      T
      hT
      B
      hB
      Ctarget
      hCtarget

omit F hcover in
/-- Helper for Lemma 7.17.10: a source-faithful fixed-target overlap witness remembers one
retained secondary owner `p`, one common source `X`, a map from `X` to the retained secondary
source `p.1.2.1.1`, one concrete branch of the pullback cover `T p.2` over the fixed target branch
`p.2`, and a map from `X` to that target-side branch source.

This is the exact datum used in the Stacks proof: pairwise overlap comparisons are performed only
after passing to a common source dominating both the retained secondary branch and the chosen fixed
target branch. -/
def targeted_secondary_target_overlap_witness
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (p : targeted_secondary_owner_index (T := T) B) :
    Type (max u v) :=
  Σ X : C,
    Σ u : X ⟶ p.1.2.1.1,
      Σ qj : (T p.2).uncurry,
        { v : X ⟶ qj.1.1 //
          u ≫ p.1.2.1.2 ≫ p.1.1.2.1.2 ≫ p.1.1.1.1.2 = v ≫ qj.1.2 ≫ p.2.1.2 }

omit F hcover in
/-- Helper for Lemma 7.17.10: the common-source branch selected in the fixed-target
comparison has the same composite to the base object as the retained secondary branch. -/
lemma pulled_back_secondary_branch_target_overlap_base_eq
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    {r j : R.uncurry} {W Y A X A₁ A₂ N : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e₀ : A ⟶ r.1.1) (he : T r e₀)
    (hie : g ≫ gr' = i ≫ e₀)
    (nmap : N ⟶ Y)
    (i₁ : N ⟶ A₁) (e₁ : A₁ ⟶ A) (he₁ : B ⟨r, ⟨⟨A, e₀⟩, he⟩⟩ e₁)
    (hi₁ : i₁ ≫ e₁ = nmap ≫ i)
    (k : X ⟶ N)
    (c : X ⟶ A₂) (e₂ : A₂ ⟶ j.1.1) (he₂ : T j e₂)
    (hc : c ≫ e₂ = k ≫ nmap ≫ g ≫ hj') :
    (k ≫ i₁) ≫ e₁ ≫ e₀ ≫ r.1.2 = c ≫ e₂ ≫ j.1.2 := by
  -- Normalize both composites to the same map to `U`, following the source proof's common-source
  -- overlap comparison.
  calc
    (k ≫ i₁) ≫ e₁ ≫ e₀ ≫ r.1.2 = k ≫ (i₁ ≫ e₁) ≫ e₀ ≫ r.1.2 := by
      simp [Category.assoc]
    _ = k ≫ (nmap ≫ i) ≫ e₀ ≫ r.1.2 := by
      simpa [Category.assoc] using congrArg (fun t ↦ k ≫ t ≫ e₀ ≫ r.1.2) hi₁
    _ = k ≫ nmap ≫ (i ≫ e₀) ≫ r.1.2 := by
      simp [Category.assoc]
    _ = k ≫ nmap ≫ (g ≫ gr') ≫ r.1.2 := by
      simpa [Category.assoc] using congrArg (fun t ↦ k ≫ nmap ≫ t ≫ r.1.2) hie.symm
    _ = k ≫ nmap ≫ g ≫ (hj' ≫ j.1.2) := by
      simpa [Category.assoc] using congrArg (fun t ↦ k ≫ nmap ≫ g ≫ t) hW
    _ = c ≫ e₂ ≫ j.1.2 := by
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ j.1.2) hc.symm
    _ = c ≫ (e₂ ≫ j.1.2) := by
      simp [Category.assoc]

omit F in
/-- Helper for Lemma 7.17.10: one concrete branch of the pulled-back secondary cover together
with one branch of the fixed-target cover determines the common-source overlap witness used in the
source proof. -/
def pulled_back_secondary_branch_target_overlap_witness
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    {r j : R.uncurry} {W Y A X A₁ A₂ N : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e₀ : A ⟶ r.1.1) (he : T r e₀)
    (hie : g ≫ gr' = i ≫ e₀)
    (nmap : N ⟶ Y)
    (i₁ : N ⟶ A₁) (e₁ : A₁ ⟶ A) (he₁ : B ⟨r, ⟨⟨A, e₀⟩, he⟩⟩ e₁)
    (hi₁ : i₁ ≫ e₁ = nmap ≫ i)
    (k : X ⟶ N)
    (c : X ⟶ A₂) (e₂ : A₂ ⟶ j.1.1) (he₂ : T j e₂)
    (hc : c ≫ e₂ = k ≫ nmap ≫ g ≫ hj') :
    targeted_secondary_target_overlap_witness
      (T := T)
      (B := B)
      ⟨⟨⟨r, ⟨⟨A, e₀⟩, he⟩⟩, ⟨⟨A₁, e₁⟩, he₁⟩⟩, j⟩ :=
  ⟨X, k ≫ i₁, ⟨⟨A₂, e₂⟩, he₂⟩,
    ⟨c,
      pulled_back_secondary_branch_target_overlap_base_eq
        (T := T)
        (B := B)
        (gr' := gr')
        (hj' := hj')
        (hW := hW)
        (g := g)
        (i := i)
        (e₀ := e₀)
        (he := he)
        (hie := hie)
        (nmap := nmap)
        (i₁ := i₁)
        (e₁ := e₁)
        (he₁ := he₁)
        (hi₁ := hi₁)
        (k := k)
        (c := c)
        (e₂ := e₂)
        (he₂ := he₂)
        (hc := hc)⟩⟩

omit F in
/-- Helper for Lemma 7.17.10: one can also choose, for every remembered secondary owner together
with a fixed branch of `R`, a canonical pullback cover of the original covering presieve along the
full composite to `U`; this keeps the total owner family `< β.cof`, but it only lands in some
branch of `R` rather than in the specifically remembered target branch. -/
lemma targeted_secondary_owner_has_small_base_cover_owner_family
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1) :
    ∃ C' : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1,
      (∀ p, C' p ∈ K p.1.2.1.1) ∧
      (∀ p,
        (C' p).FactorsThruAlong R
          (p.1.2.1.2 ≫ p.1.1.2.1.2 ≫ p.1.1.1.1.2)) ∧
      Cardinal.lift
          (Cardinal.mk
            (Σ p : targeted_secondary_owner_index (T := T) B, (C' p).uncurry)) <
        β.cof := by
  let κtarget : Type (max u v) := targeted_secondary_owner_index (T := T) B
  -- Pull back the original covering presieve along the full retained composite to the base object
  -- `U`; this is the strongest canonical owner family available from the coverage API alone.
  choose C' hC' hC'fac using
    fun p : κtarget ↦
      K.toCoverage.pullback
        (p.1.2.1.2 ≫ p.1.1.2.1.2 ≫ p.1.1.1.1.2)
        R
        hR
  refine ⟨C', hC', hC'fac, ?_⟩
  -- The previously established fixed-target cardinal bound applies to any family of covers over
  -- the remembered secondary-owner sources.
  simpa [κtarget] using
    coveringPresieve_small_fixed_target_pullback_owner_family
      (β := β)
      (hcover := hcover)
      (hR := hR)
      T
      hT
      B
      hB
      C'
      hC'

omit hcover in
/-- Helper for Lemma 7.17.10: the comparison from the presheaf colimit to the underlying presheaf
of the sheaf colimit factors through the sheafification unit and the canonical colimit
identification. -/
theorem presheaf_colimit_comparison_factorization
    [HasColimit F]
    [HasColimit (F ⋙ sheafToPresheaf J (Type (max u v)))] :
    (CategoryTheory.toSheafify J
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))) ≫
      (sheafToPresheaf J (Type (max u v))).map
        ((colimit.isoColimitCocone
          ⟨Sheaf.sheafifyCocone
              (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))),
            Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).inv) =
      colimit.post F (sheafToPresheaf J (Type (max u v))) := by
  let E := colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))
  let c := (Sheaf.sheafifyCocone E : Cocone F)
  let e :
      ((presheafToSheaf J (Type (max u v))).obj
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))) ≅
        @colimit _ _ _ _ F inferInstance :=
    (colimit.isoColimitCocone
      ⟨Sheaf.sheafifyCocone E,
        Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).symm
  -- Compare the two candidate maps after precomposing with each presheaf-colimit injection.
  refine colimit.hom_ext ?_
  intro i
  have hleft :
      colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i ≫
          CategoryTheory.toSheafify J
            (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))) ≫
            (sheafToPresheaf J (Type (max u v))).map
              e.hom =
        (c.ι.app i).hom ≫
          (sheafToPresheaf J (Type (max u v))).map
            e.hom := by
    -- The sheafified cocone leg is the presheaf-colimit leg followed by the sheafification unit.
    simpa [Category.assoc] using congrArg
      (fun f ↦ f ≫ (sheafToPresheaf J (Type (max u v))).map e.hom)
      (Sheaf.sheafifyCocone_ι_app_val E i).symm
  change
    colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i ≫
        CategoryTheory.toSheafify J
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))) ≫
          (sheafToPresheaf J (Type (max u v))).map e.hom =
      colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i ≫
        colimit.post F (sheafToPresheaf J (Type (max u v)))
  rw [hleft]
  have hmid :
      (c.ι.app i).hom ≫
        (sheafToPresheaf J (Type (max u v))).map
          e.hom =
      (colimit.ι F i).hom := by
    -- The canonical colimit isomorphism identifies the sheafified cocone with the chosen colimit.
    simpa [E, c, e, CategoryTheory.presheafColimitToSheafIso] using congrArg (fun f ↦ f.1)
      (colimit.isoColimitCocone_ι_inv
        ⟨Sheaf.sheafifyCocone E,
          Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩ i)
  rw [hmid]
  exact (colimit.ι_post F (sheafToPresheaf J (Type (max u v))) i).symm

omit hcover in
/-- Helper for Lemma 7.17.10: evaluating the section-comparison map rewrites it as the pointwise
presheaf-colimit comparison, then the sheafification unit, then the canonical colimit
identification. -/
theorem colimit_post_eq_toSheafify_comparison_app
    (U : C)
    [HasColimit F]
    [HasColimit (F ⋙ sheafToPresheaf J (Type (max u v)))]
    [HasColimit (F ⋙ (sheafSections J (Type (max u v))).obj (op U))] :
    colimit.post F ((sheafSections J (Type (max u v))).obj (op U)) =
      colimit.post (F ⋙ sheafToPresheaf J (Type (max u v)))
          ((evaluation Cᵒᵖ (Type (max u v))).obj (op U)) ≫
        (CategoryTheory.toSheafify J
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))).app (op U) ≫
        (((colimit.isoColimitCocone
          ⟨Sheaf.sheafifyCocone
              (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))),
            Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).inv).1.app (op U)) := by
  -- First rewrite the sections comparison as evaluation of the presheaf comparison.
  rw [section_colimit_post_eq_eval]
  let e :
      ((presheafToSheaf J (Type (max u v))).obj
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))) ≅
        @colimit _ _ _ _ F inferInstance :=
    (colimit.isoColimitCocone
      ⟨Sheaf.sheafifyCocone
          (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))),
        Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).symm
  -- Then evaluate the presheaf-side factorization through sheafification.
  have hfactor :
      (colimit.post F (sheafToPresheaf J (Type (max u v)))).app (op U) =
        (CategoryTheory.toSheafify J
            (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))).app (op U) ≫
          (e.hom.1.app (op U)) := by
    simpa [Category.assoc] using
      (congrArg (fun f ↦ f.app (op U))
        (presheaf_colimit_comparison_factorization β F)).symm
  rw [hfactor]
  rfl

omit F in
/-- Helper for Lemma 7.17.10: a presieve agrees with the arrow family indexed by its own
`uncurry` presentation. -/
lemma presieve_eq_of_uncurry {U : C} (R : Presieve U) :
    R = Presieve.ofArrows (fun i : R.uncurry ↦ i.1.1) (fun i ↦ i.1.2) := by
  -- Present each arrow of `R` by the corresponding point of `R.uncurry`, and conversely unpack
  -- membership in the arrow-family presentation.
  refine le_antisymm ?_ ?_
  · intro Y f hf
    let i : R.uncurry := ⟨⟨Y, f⟩, hf⟩
    exact Presieve.ofArrows.mk i
  · intro Y f hf
    obtain ⟨i⟩ := hf
    exact i.2

/-- Helper for Lemma 7.17.10: if two same-stage sections agree in the presheaf colimit after
restricting along every arrow of a covering presieve, then their colimit classes already agree
globally. -/
lemma presheafColimit_local_cover_eq_implies_colimit_eq
    {a : Set.Iio β} {Z : C} {T : Presieve Z} (hT : T ∈ K Z)
    {u v : (F.obj a).1.obj (op Z)}
    (hlocal :
      ∀ k : T.uncurry,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) u) =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) v)) :
    ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) u =
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) v := by
  by_cases hne : Nonempty T.uncurry
  · -- Synchronize the eventual overlap equalities to one later stage and then use sheaf-stage
    -- separatedness on the given covering presieve.
    choose b f hf using
      fun k : T.uncurry ↦
        presheafColimit_section_eq_at_later_stage
          (β := β)
          (F := F)
          k.1.1
          (i := a)
          (s := ((F.obj a).1.map k.1.2.op) u)
          (t := ((F.obj a).1.map k.1.2.op) v)
          (h := hlocal k)
    obtain ⟨c, hc⟩ :=
      coveringPresieve_common_stage_of_small_family
        (β := β)
        (F := F)
        (f := fun k : T.uncurry ↦ (b k).1)
        (hf := fun k ↦ (b k).2)
        (hι := hcover Z T hT)
    obtain ⟨k₀⟩ := hne
    have hac : a.1 ≤ c.1 := by
      exact le_trans (leOfHom (f k₀)) (hc k₀)
    let u' : (F.obj c).1.obj (op Z) :=
      ((F.map (homOfLE hac)).1.app (op Z)) u
    let v' : (F.obj c).1.obj (op Z) :=
      ((F.map (homOfLE hac)).1.app (op Z)) v
    have hsheafT : Presieve.IsSheafFor ((F.obj c).1) T := by
      exact
        ((Presieve.isSheaf_coverage (K := K.toCoverage) ((F.obj c).1)).1
          ((isSheaf_iff_isSheaf_of_type J ((F.obj c).1)).1 (F.obj c).2)) T hT
    have hlocal' :
        ∀ {Y : C} (g : Y ⟶ Z) (_ : T g),
          ((F.obj c).1.map g.op) u' = ((F.obj c).1.map g.op) v' := by
      intro Y g hg
      let k : T.uncurry := ⟨⟨Y, g⟩, hg⟩
      have hcomp :
          f k ≫ homOfLE (hc k) = homOfLE (le_trans (leOfHom (f k)) (hc k)) :=
        Subsingleton.elim _ _
      have hu :
          ((F.obj c).1.map g.op) u' =
            ((F.map (homOfLE (hc k))).1.app (op Y))
              (((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) u)) := by
        have h₁ :
            ((F.obj c).1.map g.op) u' =
              ((F.map (homOfLE hac)).1.app (op Y)) (((F.obj a).1.map g.op) u) := by
          simpa [u'] using
            (sheaf_transition_app_map_eq_map_app
              (β := β)
              (F := F)
              (f := homOfLE hac)
              (g := g)
              (a := u)).symm
        have h₂ :
            ((F.map (homOfLE hac)).1.app (op Y)) (((F.obj a).1.map g.op) u) =
              ((F.map (homOfLE (hc k))).1.app (op Y))
                (((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) u)) := by
          have hrewrite :
              F.map (homOfLE hac) = F.map (f k ≫ homOfLE (hc k)) := by
            exact congrArg F.map (Subsingleton.elim _ _)
          rw [hrewrite]
          simp [Functor.map_comp, Function.comp]
        exact h₁.trans h₂
      have hv :
          ((F.obj c).1.map g.op) v' =
            ((F.map (homOfLE (hc k))).1.app (op Y))
              (((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) v)) := by
        have h₁ :
            ((F.obj c).1.map g.op) v' =
              ((F.map (homOfLE hac)).1.app (op Y)) (((F.obj a).1.map g.op) v) := by
          simpa [v'] using
            (sheaf_transition_app_map_eq_map_app
              (β := β)
              (F := F)
              (f := homOfLE hac)
              (g := g)
              (a := v)).symm
        have h₂ :
            ((F.map (homOfLE hac)).1.app (op Y)) (((F.obj a).1.map g.op) v) =
              ((F.map (homOfLE (hc k))).1.app (op Y))
                (((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) v)) := by
          have hrewrite :
              F.map (homOfLE hac) = F.map (f k ≫ homOfLE (hc k)) := by
            exact congrArg F.map (Subsingleton.elim _ _)
          rw [hrewrite]
          simp [Functor.map_comp, Function.comp]
        exact h₁.trans h₂
      have hstage :
          ((F.map (homOfLE (hc k))).1.app (op Y))
              (((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) u)) =
            ((F.map (homOfLE (hc k))).1.app (op Y))
              (((F.map (f k)).1.app (op Y)) (((F.obj a).1.map g.op) v)) := by
        exact congrArg (((F.map (homOfLE (hc k))).1.app (op Y))) (hf k)
      exact hu.trans (hstage.trans hv.symm)
    have huv : u' = v' := by
      apply hsheafT.isSeparatedFor.ext
      intro Y g hg
      exact hlocal' g hg
    have hu_colim :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) u =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z)) u' := by
      -- Move the class of `u` from stage `a` to the common stage `c`.
      simpa [u'] using
        (congrFun
          (congrFun
            (congrArg NatTrans.app
              (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hac))) (op Z))
          u).symm
    have hv_colim :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) v =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z)) v' := by
      -- The same transport identifies the class of `v` with its common-stage image.
      simpa [v'] using
        (congrFun
          (congrFun
            (congrArg NatTrans.app
              (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hac))) (op Z))
          v).symm
    calc
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) u =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z)) u' := hu_colim
      _ = ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z)) v' := by
            simpa [huv]
      _ = ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op Z)) v := hv_colim.symm
  · -- If the covering presieve has no arrows, separatedness of the stage sheaf forces equality.
    have hsheafT : Presieve.IsSheafFor ((F.obj a).1) T := by
      exact
        ((Presieve.isSheaf_coverage (K := K.toCoverage) ((F.obj a).1)).1
          ((isSheaf_iff_isSheaf_of_type J ((F.obj a).1)).1 (F.obj a).2)) T hT
    have huv : u = v := by
      apply hsheafT.isSeparatedFor.ext
      intro Y g hg
      exact False.elim <| hne ⟨⟨⟨Y, g⟩, hg⟩⟩
    simpa [huv]

/-- Helper for Lemma 7.17.10: the presheaf colimit is separated for every `K`-covering presieve
under the small-cover cofinality hypothesis. -/
lemma presheafColimit_isSeparatedFor_of_coveringPresieveCardinal_lt_cof
    {U : C} {R : Presieve U} (hR : R ∈ K U) :
    Presieve.IsSeparatedFor (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))) R := by
  intro x z₁ z₂ hz₁ hz₂
  -- Represent the two candidate amalgamations in stages and move them to one common stage.
  obtain ⟨i₁, s₁, hs₁⟩ :=
    presheafColimit_section_exists_rep (β := β) (F := F) U z₁
  obtain ⟨i₂, s₂, hs₂⟩ :=
    presheafColimit_section_exists_rep (β := β) (F := F) U z₂
  by_cases h12 : i₁.1 ≤ i₂.1
  · let a : Set.Iio β := i₂
    let u : (F.obj a).1.obj (op U) := ((F.map (homOfLE h12)).1.app (op U)) s₁
    let v : (F.obj a).1.obj (op U) := s₂
    have hu :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) u = z₁ := by
      -- Transport the representative of `z₁` to the common stage.
      have hmap :
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i₁).app (op U)) s₁ =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) u := by
        simpa [a, u] using
          (congrFun
            (congrFun
              (congrArg NatTrans.app
                (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE h12))) (op U))
            s₁).symm
      exact hmap.symm.trans hs₁
    have hv :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) v = z₂ := by
      simpa [a, v] using hs₂
    have hlocal :
        ∀ k : R.uncurry,
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
              (((F.obj a).1.map k.1.2.op) u) =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
              (((F.obj a).1.map k.1.2.op) v) := by
      intro k
      -- Rewrite the local colimit classes using the two amalgamation identities on `R`.
      calc
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) u) =
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map k.1.2.op z₁ := by
            rw [← hu]
            simpa [Functor.comp_map, Category.assoc] using
              congrFun ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                k.1.2.op) u
        _ = x k.1.2 k.2 := hz₁ _ _
        _ = (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map k.1.2.op z₂ := (hz₂ _ _).symm
        _ =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) v) := by
            rw [← hv]
            simpa [Functor.comp_map, Category.assoc] using
              (congrFun ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                k.1.2.op) v).symm
    have hcolim :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) u =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) v :=
      presheafColimit_local_cover_eq_implies_colimit_eq
        (β := β)
        (F := F)
        (hcover := hcover)
        (hT := hR)
        (u := u)
        (v := v)
        hlocal
    exact hu.symm.trans (hcolim.trans hv)
  · have h21 : i₂.1 ≤ i₁.1 := le_of_not_ge h12
    let a : Set.Iio β := i₁
    let u : (F.obj a).1.obj (op U) := s₁
    let v : (F.obj a).1.obj (op U) := ((F.map (homOfLE h21)).1.app (op U)) s₂
    have hu :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) u = z₁ := by
      simpa [a, u] using hs₁
    have hv :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) v = z₂ := by
      -- Transport the representative of `z₂` to the common stage.
      have hmap :
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) i₂).app (op U)) s₂ =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) v := by
        simpa [a, v] using
          (congrFun
            (congrFun
              (congrArg NatTrans.app
                (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE h21))) (op U))
            s₂).symm
      exact hmap.symm.trans hs₂
    have hlocal :
        ∀ k : R.uncurry,
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
              (((F.obj a).1.map k.1.2.op) u) =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
              (((F.obj a).1.map k.1.2.op) v) := by
      intro k
      -- The local compatibility is again just the equality of the two amalgamations on `R`.
      calc
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) u) =
          (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map k.1.2.op z₁ := by
            rw [← hu]
            simpa [Functor.comp_map, Category.assoc] using
              congrFun ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                k.1.2.op) u
        _ = x k.1.2 k.2 := hz₁ _ _
        _ = (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map k.1.2.op z₂ := (hz₂ _ _).symm
        _ =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op k.1.1))
            (((F.obj a).1.map k.1.2.op) v) := by
            rw [← hv]
            simpa [Functor.comp_map, Category.assoc] using
              (congrFun ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                k.1.2.op) v).symm
    have hcolim :
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) u =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U)) v :=
      presheafColimit_local_cover_eq_implies_colimit_eq
        (β := β)
        (F := F)
        (hcover := hcover)
        (hT := hR)
        (u := u)
        (v := v)
        hlocal
    exact hu.symm.trans (hcolim.trans hv)

/-- Helper for Lemma 7.17.10: the image in the underlying presheaf colimit of a section
represented at one stage of the sheaf diagram. -/
noncomputable def presheafColimit_stageClass
    {a : Set.Iio β} {U : C}
    [HasColimit (F ⋙ sheafToPresheaf J (Type (max u v)))]
    (s : (F.obj a).1.obj (op U)) :
    (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op U) :=
  ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op U))
    (stageSectionAsPresheaf (β := β) (F := F) (a := a) (U := U) s)

/-- Helper for Lemma 7.17.10: any `< β.cof`-small family of stagewise representatives in the
presheaf colimit can be transported to one common ordinal stage without changing its colimit
image. -/
lemma presheafColimit_common_stage_of_small_sections
    {ι : Type (max u v)} {X : ι → C}
    (x : ∀ i, (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op (X i)))
    (b : ι → Set.Iio β)
    (t : ∀ i, (F.obj (b i)).1.obj (op (X i)))
    (ht :
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) (b i)).app (op (X i))) (t i) =
          x i)
    (hι : Cardinal.lift (Cardinal.mk ι) < β.cof) :
    ∃ a : Set.Iio β, ∃ s : ∀ i, (F.obj a).1.obj (op (X i)),
      ∀ i,
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op (X i))) (s i) = x i := by
  -- Choose one ordinal stage dominating all local representatives, then transport each section
  -- there using the colimit cocone relation.
  obtain ⟨a, ha⟩ :=
    coveringPresieve_common_stage_of_small_family
      (β := β)
      (F := F)
      (f := fun i ↦ (b i).1)
      (hf := fun i ↦ (b i).2)
      (hι := hι)
  let s : ∀ i, (F.obj a).1.obj (op (X i)) := fun i ↦
    ((F.map (homOfLE (ha i))).1.app (op (X i))) (t i)
  refine ⟨a, s, ?_⟩
  intro i
  have hmap :
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) (b i)).app (op (X i))) (t i) =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op (X i))) (s i) := by
    -- The colimit cocone identifies the old representative with its transport to the common
    -- stage.
    simpa [s] using
      (congrFun
        (congrFun
          (congrArg NatTrans.app
            (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE (ha i)))) (op (X i)))
        (t i)).symm
  exact hmap.symm.trans (ht i)

/-- Helper for Lemma 7.17.10: once a compatible family is represented in one ordinal stage, any
`< β.cof`-small family of overlap equalities can be synchronized in one later stage. -/
lemma presheafColimit_common_stage_of_small_overlaps
    {U : C} {R : Presieve U}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {a : Set.Iio β}
    (s : ∀ i : R.uncurry, (F.obj a).1.obj (op i.1.1))
    (hs_image :
      ∀ i,
        presheafColimit_stageClass (β := β) (F := F) (a := a) (U := i.1.1) (s i) = x i)
    {ι : Type (max u v)}
    (left right : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q, Z q ⟶ (left q).1.1)
    (gr : ∀ q, Z q ⟶ (right q).1.1)
    (hcomm : ∀ q, gl q ≫ (left q).1.2 = gr q ≫ (right q).1.2)
    (hι : Cardinal.lift (Cardinal.mk ι) < β.cof) :
    ∃ c : Set.Iio β, ∃ v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1),
      (∀ i,
        presheafColimit_stageClass (β := β) (F := F) (a := c) (U := i.1.1) (v i) = x i) ∧
      ∀ q,
        ((F.obj c).1.map (gl q).op) (v (left q)) =
          ((F.obj c).1.map (gr q).op) (v (right q)) := by
  by_cases hne : Nonempty ι
  · -- First upgrade each prescribed overlap equality from the colimit to some later stage.
    choose b f hf using
      fun q : ι ↦
        presheafColimit_section_eq_at_later_stage
          (β := β)
          (F := F)
          (U := Z q)
          (i := a)
          (s := ((F.obj a).1.map (gl q).op) (s (left q)))
          (t := ((F.obj a).1.map (gr q).op) (s (right q)))
          (h := by
            calc
              ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op (Z q)))
                  (((F.obj a).1.map (gl q).op) (s (left q))) =
                (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map (gl q).op (x (left q)) := by
                  rw [← hs_image (left q)]
                  simpa [Functor.comp_map, Category.assoc] using
                    congrFun
                      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                        (gl q).op)
                      (s (left q))
              _ =
                (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map (gr q).op (x (right q)) := by
                  exact hx (left q) (right q) (Z q) (gl q) (gr q) (hcomm q)
              _ =
                ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).app (op (Z q)))
                  (((F.obj a).1.map (gr q).op) (s (right q))) := by
                  rw [← hs_image (right q)]
                  have hnat :=
                    congrFun
                      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) a).naturality
                        (gr q).op)
                      (s (right q))
                  exact hnat.symm)
    -- Next dominate all witness stages by a single later stage.
    obtain ⟨c, hc⟩ :=
      coveringPresieve_common_stage_of_small_family
        (β := β)
        (F := F)
        (f := fun q : ι ↦ (b q).1)
        (hf := fun q ↦ (b q).2)
        (hι := hι)
    obtain ⟨q₀⟩ := hne
    have hac : a.1 ≤ c.1 := by
      exact le_trans (leOfHom (f q₀)) (hc q₀)
    let v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1) := fun i ↦
      ((F.map (homOfLE hac)).1.app (op i.1.1)) (s i)
    refine ⟨c, v, ?_, ?_⟩
    · intro i
      -- Transporting each representative to the common stage leaves its colimit class unchanged.
      have hmap :
          presheafColimit_stageClass (β := β) (F := F) (a := a) (U := i.1.1) (s i) =
            presheafColimit_stageClass (β := β) (F := F) (a := c) (U := i.1.1) (v i) := by
        simpa [v] using
          (congrFun
            (congrFun
              (congrArg NatTrans.app
                (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hac)))
              (op i.1.1))
            (s i)).symm
      exact hmap.symm.trans (hs_image i)
    · intro q
      -- Rewrite both sides through the stage `b q`, where the overlap equality is already valid.
      have hcomp :
          f q ≫ homOfLE (hc q) = homOfLE hac := by
        exact Subsingleton.elim _ _
      have hleft :
          ((F.obj c).1.map (gl q).op) (v (left q)) =
            ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gl q).op) (s (left q))) := by
        simpa [v] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hac)
            (g := gl q)
            (a := s (left q))).symm
      have hright :
          ((F.obj c).1.map (gr q).op) (v (right q)) =
            ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gr q).op) (s (right q))) := by
        simpa [v] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hac)
            (g := gr q)
            (a := s (right q))).symm
      have hleft' :
          ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gl q).op) (s (left q))) =
            ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gl q).op) (s (left q)))) := by
        have hrewrite :
            F.map (homOfLE hac) = F.map (f q ≫ homOfLE (hc q)) := by
          exact congrArg F.map (Subsingleton.elim _ _)
        rw [hrewrite]
        simp [Functor.map_comp, Function.comp]
      have hright' :
          ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gr q).op) (s (right q))) =
            ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gr q).op) (s (right q)))) := by
        have hrewrite :
            F.map (homOfLE hac) = F.map (f q ≫ homOfLE (hc q)) := by
          exact congrArg F.map (Subsingleton.elim _ _)
        rw [hrewrite]
        simp [Functor.map_comp, Function.comp]
      have hstage :
          ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gl q).op) (s (left q)))) =
            ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gr q).op) (s (right q)))) := by
        exact congrArg (((F.map (homOfLE (hc q))).1.app (op (Z q)))) (hf q)
      calc
        ((F.obj c).1.map (gl q).op) (v (left q)) =
            ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gl q).op) (s (left q))) := hleft
        _ =
            ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gl q).op) (s (left q)))) := hleft'
        _ =
            ((F.map (homOfLE (hc q))).1.app (op (Z q)))
              (((F.map (f q)).1.app (op (Z q)))
                (((F.obj a).1.map (gr q).op) (s (right q)))) := hstage
        _ =
            ((F.map (homOfLE hac)).1.app (op (Z q)))
              (((F.obj a).1.map (gr q).op) (s (right q))) := hright'.symm
        _ = ((F.obj c).1.map (gr q).op) (v (right q)) := hright.symm
  · -- If there are no overlap constraints, the original common stage already works.
    haveI : IsEmpty ι := not_nonempty_iff.mp hne
    refine ⟨a, s, hs_image, ?_⟩
    intro q
    exact isEmptyElim q

/-- Helper for Lemma 7.17.10: once the local family has been synchronized to one stage, any
overlap relation already holds after applying the stage injection into the presheaf colimit. -/
lemma presheafColimit_overlap_eq_in_colimit
    {U : C} {R : Presieve U}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {c : Set.Iio β}
    (v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        presheafColimit_stageClass (β := β) (F := F) (a := c) (U := i.1.1) (v i) = x i)
    {i j : R.uncurry} {Z : C}
    (gi : Z ⟶ i.1.1) (gj : Z ⟶ j.1.1)
    (hcomm : gi ≫ i.1.2 = gj ≫ j.1.2) :
    ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z))
        (((F.obj c).1.map gi.op) (v i)) =
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z))
        (((F.obj c).1.map gj.op) (v j)) := by
  -- Rewrite both stage-`c` restrictions through their prescribed colimit images and then apply the
  -- original compatibility of the family `x`.
  calc
    ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z))
        (((F.obj c).1.map gi.op) (v i)) =
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map gi.op (x i) := by
        rw [← hv_image i]
        simpa [Functor.comp_map, Category.assoc] using
          congrFun
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).naturality gi.op)
            (v i)
    _ =
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map gj.op (x j) := by
        exact hx i j Z gi gj hcomm
    _ =
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op Z))
        (((F.obj c).1.map gj.op) (v j)) := by
        rw [← hv_image j]
        simpa [Functor.comp_map, Category.assoc] using
          (congrFun
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).naturality gj.op)
            (v j)).symm

/-- Helper for Lemma 7.17.10: the sigma refinement built from the chosen pullback covers is a
covering sieve for the Grothendieck topology generated by `K`. -/
lemma sigma_refinement_generate_mem_toGrothendieck
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1) :
    Sieve.generate
        (Presieve.bindOfArrows
          (fun i : R.uncurry ↦ i.1.1)
          (fun i ↦ i.1.2)
          T) ∈ J U := by
  -- First view the base cover and each chosen pullback cover as covering sieves in `J`.
  have huncurry :
      Sieve.ofArrows (fun i : R.uncurry ↦ i.1.1) (fun i ↦ i.1.2) = Sieve.generate R := by
    refine Sieve.ext fun Y g ↦ ?_
    constructor
    · intro hg
      rw [Sieve.mem_ofArrows_iff] at hg
      rcases hg with ⟨i, a, rfl⟩
      exact ⟨i.1.1, a, i.1.2, i.2, rfl⟩
    · intro hg
      rcases hg with ⟨W, a, b, hb, rfl⟩
      rw [Sieve.mem_ofArrows_iff]
      exact ⟨⟨⟨W, b⟩, hb⟩, a, rfl⟩
  have hbase :
      Sieve.ofArrows (fun i : R.uncurry ↦ i.1.1) (fun i ↦ i.1.2) ∈ J U := by
    have hgen : Sieve.generate R ∈ J U := by
      rw [show K.toCoverage.toGrothendieck = K.toGrothendieck from
        Precoverage.toGrothendieck_toCoverage]
      exact Precoverage.generate_mem_toGrothendieck hR
    simpa [huncurry] using hgen
  have hlocal :
      ∀ i : R.uncurry, Sieve.generate (T i) ∈ J i.1.1 := by
    intro i
    rw [show K.toCoverage.toGrothendieck = K.toGrothendieck from
      Precoverage.toGrothendieck_toCoverage]
    exact Precoverage.generate_mem_toGrothendieck (hT i)
  -- Then the Grothendieck-topology bind construction promotes the whole sigma refinement.
  exact GrothendieckTopology.bindOfArrows J hbase hlocal

/-- Helper for Lemma 7.17.10: the sigma refinement factors through the original covering
presieve. -/
lemma sigma_refinement_factors_thru
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1) :
    (Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        T).FactorsThru R := by
  -- Every sigma-refinement arrow is literally a composite through one base arrow in `R`.
  intro Z g hg
  rcases hg with ⟨i, k, hk⟩
  exact ⟨i.1.1, k, i.1.2, i.2, rfl⟩

/-- Helper for Lemma 7.17.10: each chosen pullback cover factors through the sigma refinement
along its base arrow. -/
lemma pullback_cover_factors_thru_sigma_refinement
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (i : R.uncurry) :
    (T i).FactorsThruAlong
      (Presieve.bindOfArrows
        (fun j : R.uncurry ↦ j.1.1)
        (fun j ↦ j.1.2)
        T)
      i.1.2 := by
  -- Each arrow in `T i` becomes an arrow of the sigma refinement by adjoining the branch index `i`.
  intro Z g hg
  refine ⟨Z, 𝟙 Z, g ≫ i.1.2, ?_, by simp⟩
  change
    (Presieve.bindOfArrows
      (fun j : R.uncurry ↦ j.1.1)
      (fun j ↦ j.1.2)
      T)
      (g ≫ i.1.2)
  simpa using
    (Presieve.bindOfArrows.mk
      (Y := fun j : R.uncurry ↦ j.1.1)
      (f := fun j ↦ j.1.2)
      (R := T)
      i
      g
      hg)

/-- Helper for Lemma 7.17.10: the sigma refinement can be presented by the explicit family of
composite arrows indexed by the uncurry types of the branch covers. -/
lemma sigma_refinement_eq_ofArrows
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1) :
    Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        T =
      Presieve.ofArrows
        (fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.1)
        (fun q ↦ q.2.1.2 ≫ q.1.1.2) := by
  -- Rewrite each branch cover by its own `uncurry` arrow family, then apply the owner lemma for
  -- binding explicit arrow families.
  calc
    Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        T =
      Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        (fun i ↦ Presieve.ofArrows (fun j : (T i).uncurry ↦ j.1.1) (fun j ↦ j.1.2)) := by
          congr
          funext i
          simpa using (presieve_eq_of_uncurry (β := β) (hcover := hcover) (R := T i))
    _ =
      Presieve.ofArrows
        (fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.1)
        (fun q ↦ q.2.1.2 ≫ q.1.1.2) := by
          simpa using
            (Presieve.bindOfArrows_ofArrows
              (X := fun i : R.uncurry ↦ i.1.1)
              (f := fun i ↦ i.1.2)
              (Y := fun i : R.uncurry ↦ fun j : (T i).uncurry ↦ j.1.1)
              (g := fun i : R.uncurry ↦ fun j : (T i).uncurry ↦ j.1.2))

/-- Helper for Lemma 7.17.10: restricting a compatible family on the base cover along the explicit
sigma-refinement arrows preserves compatibility in the presheaf colimit. -/
lemma presheafColimit_sigma_refinement_target_compatible
    {P : Cᵒᵖ ⥤ Type (max u v)}
    {U : C} {R : Presieve U}
    {ι : Type (max u v)}
    (left : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q : ι, Z q ⟶ (left q).1.1)
    (π : ∀ q : ι, Z q ⟶ U)
    (hπ : ∀ q, π q = gl q ≫ (left q).1.2)
    (x : ∀ i : R.uncurry, P.obj (op i.1.1))
    (hx : Presieve.Arrows.Compatible P (fun i : R.uncurry ↦ i.1.2) x) :
    Presieve.Arrows.Compatible P π (fun q : ι ↦ P.map (gl q).op (x (left q))) := by
  intro q₁ q₂ W r₁ r₂ h
  -- Expand the refinement arrows into their composites with the base cover and reuse the original
  -- compatibility of `x` on `R`.
  have hbase :
      (r₁ ≫ gl q₁) ≫ (left q₁).1.2 = (r₂ ≫ gl q₂) ≫ (left q₂).1.2 := by
    simpa [hπ q₁, hπ q₂, Category.assoc] using h
  simpa [FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using
    hx (left q₁) (left q₂) W (r₁ ≫ gl q₁) (r₂ ≫ gl q₂) hbase

/-- Helper for Lemma 7.17.10: the synchronized stage family maps to the induced sigma-refinement
family in the presheaf colimit after restricting along each refinement arrow. -/
lemma presheafColimit_sigma_refinement_image
    {U : C} {R : Presieve U}
    {ι : Type (max u v)}
    (left : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q : ι, Z q ⟶ (left q).1.1)
    {c : Set.Iio β}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        presheafColimit_stageClass (β := β) (F := F) (a := c) (U := i.1.1) (v i) = x i) :
    ∀ q : ι,
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op (Z q)))
          (((F.obj c).1.map (gl q).op) (v (left q))) =
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map (gl q).op (x (left q)) := by
  intro q
  -- Rewrite the colimit class of the restricted stage section through the prescribed image of the
  -- base branch section.
  rw [← hv_image (left q)]
  simpa [Functor.comp_map, Category.assoc] using
    congrFun
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).naturality (gl q).op)
      (v (left q))

/-- Helper for Lemma 7.17.10: once a section `tc` of the stage sheaf `(F.obj c).1` glues the
synchronized family `v` on the original cover `R`, its image in the presheaf colimit amalgamates
the original family `x`. -/
lemma presheafColimit_stage_glue_image_is_amalgamation
    {U : C} {R : Presieve U}
    {c : Set.Iio β}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        presheafColimit_stageClass (β := β) (F := F) (a := c) (U := i.1.1) (v i) = x i)
    (tc : (F.obj c).1.obj (op U))
    (htc : ∀ i : R.uncurry, ((F.obj c).1.map i.1.2.op) tc = v i) :
    let z := ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).app (op U)) tc
    ∀ i : R.uncurry, (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).map i.1.2.op z = x i := by
  intro z i
  -- Evaluate the colimit class of `tc` along the `i`-th branch and then rewrite using the stage
  -- gluing identity `htc` and the prescribed colimit image `hv_image`.
  dsimp [z]
  rw [← hv_image i, ← htc i]
  simpa [Functor.comp_map, Category.assoc] using
    (congrFun
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) c).naturality i.1.2.op)
      tc).symm

/-- Helper for Lemma 7.17.10: a `< β.cof`-small family of secondary branch equalities can be
synchronized to one common later stage while preserving the prescribed colimit images of the base
family. -/
lemma presheafColimit_common_stage_of_secondary_branch_equalities
    {U : C} {R : Presieve U}
    {ι : Type (max u v)}
    (left right : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q : ι, Z q ⟶ (left q).1.1)
    (gr : ∀ q : ι, Z q ⟶ (right q).1.1)
    {c : Set.Iio β}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        presheafColimit_stageClass (β := β) (F := F) (a := c) (U := i.1.1) (v i) = x i)
    (B : ∀ q : ι, Presieve (Z q))
    (hκsmall : Cardinal.lift (Cardinal.mk (Σ q : ι, (B q).uncurry)) < β.cof)
    (hstage_witness :
      ∀ p : Σ q : ι, (B q).uncurry,
        ∃ d : Set.Iio β, ∃ f : c ⟶ d,
          ((F.map f).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gl p.1).op) (v (left p.1))) =
            ((F.map f).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gr p.1).op) (v (right p.1)))) :
    ∃ d : Set.Iio β,
      ∃ v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1),
        (∀ i,
          presheafColimit_stageClass (β := β) (F := F) (a := d) (U := i.1.1) (v' i) =
            x i) ∧
        (∀ p : Σ q : ι, (B q).uncurry,
          ((F.obj d).1.map (p.2.1.2 ≫ gl p.1).op) (v' (left p.1)) =
            ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1))) := by
  let κ : Type (max u v) := Σ q : ι, (B q).uncurry
  -- Choose one later-stage witness for each secondary branch equality.
  choose b f hf using fun p : κ ↦ hstage_witness p
  by_cases hκne : Nonempty κ
  · -- Synchronize all secondary branch equalities in one common later stage `d`.
    obtain ⟨d, hd⟩ :=
      coveringPresieve_common_stage_of_small_family
        (β := β)
        (F := F)
        (f := fun p : κ ↦ (b p).1)
        (hf := fun p ↦ (b p).2)
        (hι := by simpa [κ] using hκsmall)
    obtain ⟨p₀⟩ := hκne
    have hcd : c.1 ≤ d.1 := by
      exact le_trans (leOfHom (f p₀)) (hd p₀)
    let v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1) := fun i ↦
      ((F.map (homOfLE hcd)).1.app (op i.1.1)) (v i)
    have hbranch_d :
        ∀ p : κ,
          ((F.obj d).1.map (p.2.1.2 ≫ gl p.1).op) (v' (left p.1)) =
            ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1)) := by
      intro p
      have hcomp : f p ≫ homOfLE (hd p) = homOfLE hcd := by
        exact Subsingleton.elim _ _
      have hleft :
          ((F.obj d).1.map (p.2.1.2 ≫ gl p.1).op) (v' (left p.1)) =
            ((F.map (homOfLE hcd)).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gl p.1).op) (v (left p.1))) := by
        -- Rewrite the transported left branch by moving the restriction across the stage map.
        simpa [v'] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hcd)
            (g := p.2.1.2 ≫ gl p.1)
            (a := v (left p.1))).symm
      have hright :
          ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1)) =
            ((F.map (homOfLE hcd)).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gr p.1).op) (v (right p.1))) := by
        -- The same transport rewrite applies to the right branch.
        simpa [v'] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hcd)
            (g := p.2.1.2 ≫ gr p.1)
            (a := v (right p.1))).symm
      have hstage :
          ((F.map (homOfLE hcd)).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gl p.1).op) (v (left p.1))) =
            ((F.map (homOfLE hcd)).1.app (op p.2.1.1))
              (((F.obj c).1.map (p.2.1.2 ≫ gr p.1).op) (v (right p.1))) := by
        -- Factor the common transport through the local witness stage `b p`.
        have hrewrite :
            F.map (homOfLE hcd) = F.map (f p ≫ homOfLE (hd p)) := by
          exact congrArg F.map (Subsingleton.elim _ _)
        rw [hrewrite]
        simpa [Functor.map_comp, Function.comp] using
          congrArg (((F.map (homOfLE (hd p))).1.app (op p.2.1.1))) (hf p)
      exact hleft.trans (hstage.trans hright.symm)
    refine ⟨d, v', ?_, hbranch_d⟩
    intro i
    -- Transporting the synchronized family `v` to the common stage preserves its colimit image.
    have hmap :
        presheafColimit_stageClass (β := β) (F := F) (a := c) (U := i.1.1) (v i) =
          ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op i.1.1))
            (v' i) := by
      simpa [v'] using
        (congrFun
          (congrFun
            (congrArg NatTrans.app
              (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hcd)))
            (op i.1.1))
          (v i)).symm
    exact hmap.symm.trans (hv_image i)
  · -- If the secondary owner family is empty, the original synchronized stage already works.
    haveI : IsEmpty κ := not_nonempty_iff.mp hκne
    refine ⟨c, v, hv_image, ?_⟩
    intro p
    exact isEmptyElim p

/-- Helper for Lemma 7.17.10: a `< β.cof`-small family of already-targeted branch comparisons can
be synchronized to one later stage without introducing another descent cover, together with the
transition map from the original synchronized stage. -/
lemma presheafColimit_common_stage_of_targeted_secondary_branch_equalities
    {U : C} {R : Presieve U}
    {ι : Type (max u v)}
    (left right : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q : ι, Z q ⟶ (left q).1.1)
    (gr : ∀ q : ι, Z q ⟶ (right q).1.1)
    {c : Set.Iio β}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (v : ∀ i : R.uncurry, (F.obj c).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        presheafColimit_stageClass (β := β) (F := F) (a := c) (U := i.1.1) (v i) = x i)
    (hιsmall : Cardinal.lift (Cardinal.mk ι) < β.cof)
    (hstage_witness :
      ∀ q : ι,
        ∃ d : Set.Iio β, ∃ f : c ⟶ d,
          ((F.map f).1.app (op (Z q)))
              (((F.obj c).1.map (gl q).op) (v (left q))) =
            ((F.map f).1.app (op (Z q)))
              (((F.obj c).1.map (gr q).op) (v (right q)))) :
    ∃ d : Set.Iio β,
      ∃ hcd : c.1 ≤ d.1,
        ∃ v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1),
          (∀ i,
            v' i = ((F.map (homOfLE hcd)).1.app (op i.1.1)) (v i)) ∧
          (∀ i,
            presheafColimit_stageClass (β := β) (F := F) (a := d) (U := i.1.1) (v' i) =
              x i) ∧
          (∀ q : ι,
            ((F.obj d).1.map (gl q).op) (v' (left q)) =
              ((F.obj d).1.map (gr q).op) (v' (right q))) := by
  -- Synchronize the explicit targeted branch witnesses exactly as in the untargeted case, but
  -- with no second descent cover because the right-hand comparison branch is already part of the
  -- owner data.
  choose b f hf using hstage_witness
  by_cases hιne : Nonempty ι
  · -- One common stage dominates every targeted comparison witness.
    obtain ⟨d, hd⟩ :=
      coveringPresieve_common_stage_of_small_family
        (β := β)
        (F := F)
        (f := fun q : ι ↦ (b q).1)
        (hf := fun q ↦ (b q).2)
        (hι := hιsmall)
    obtain ⟨q₀⟩ := hιne
    have hcd : c.1 ≤ d.1 := by
      exact le_trans (leOfHom (f q₀)) (hd q₀)
    let v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1) := fun i ↦
      ((F.map (homOfLE hcd)).1.app (op i.1.1)) (v i)
    have htarget_d :
        ∀ q : ι,
          ((F.obj d).1.map (gl q).op) (v' (left q)) =
            ((F.obj d).1.map (gr q).op) (v' (right q)) := by
      intro q
      have hcomp : f q ≫ homOfLE (hd q) = homOfLE hcd := by
        exact Subsingleton.elim _ _
      have hleft :
          ((F.obj d).1.map (gl q).op) (v' (left q)) =
            ((F.map (homOfLE hcd)).1.app (op (Z q)))
              (((F.obj c).1.map (gl q).op) (v (left q))) := by
        -- Move the left restriction across the common transport to the synchronized stage.
        simpa [v'] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hcd)
            (g := gl q)
            (a := v (left q))).symm
      have hright :
          ((F.obj d).1.map (gr q).op) (v' (right q)) =
            ((F.map (homOfLE hcd)).1.app (op (Z q)))
              (((F.obj c).1.map (gr q).op) (v (right q))) := by
        -- The same transport rewrite applies to the targeted right branch.
        simpa [v'] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hcd)
            (g := gr q)
            (a := v (right q))).symm
      have hstage :
          ((F.map (homOfLE hcd)).1.app (op (Z q)))
              (((F.obj c).1.map (gl q).op) (v (left q))) =
            ((F.map (homOfLE hcd)).1.app (op (Z q)))
              (((F.obj c).1.map (gr q).op) (v (right q))) := by
        -- Factor the common transport through the witness stage chosen for this targeted branch.
        have hrewrite :
            F.map (homOfLE hcd) = F.map (f q ≫ homOfLE (hd q)) := by
          exact congrArg F.map (Subsingleton.elim _ _)
        rw [hrewrite]
        simpa [Functor.map_comp, Function.comp] using
          congrArg (((F.map (homOfLE (hd q))).1.app (op (Z q)))) (hf q)
      exact hleft.trans (hstage.trans hright.symm)
    refine ⟨d, hcd, v', ?_, ?_, htarget_d⟩
    · intro i
      rfl
    · intro i
      -- Transporting the synchronized family to the common stage preserves each colimit class.
      have hmap :
          presheafColimit_stageClass (β := β) (F := F) (a := c) (U := i.1.1) (v i) =
            ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op i.1.1))
              (v' i) := by
        simpa [v'] using
          (congrFun
            (congrFun
              (congrArg NatTrans.app
                (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hcd)))
              (op i.1.1))
            (v i)).symm
      exact hmap.symm.trans (hv_image i)
  · -- If there are no targeted comparisons, the existing synchronized stage already works.
    haveI : IsEmpty ι := not_nonempty_iff.mp hιne
    refine ⟨c, le_rfl, v, ?_, hv_image, ?_⟩
    · intro i
      simpa using
        (congrFun
          (congrArg (fun f : F.obj c ⟶ F.obj c ↦ f.1.app (op i.1.1)) (F.map_id c))
          (v i)).symm
    · intro q
      exact isEmptyElim q

end

end CategoryTheory
