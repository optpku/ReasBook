module

public import Mathlib.Order.Quotient
public import stacks_project.Chap07.Lemma_7_39_2.RequestScheduling
public import stacks_project.Chap07.Lemma_7_39_2.PackagedStages
public import stacks_project.Chap07.Lemma_7_39_2.DiagramUnionCore
public import stacks_project.Chap07.Lemma_7_39_2.DiagramUnionLimit

@[expose] public section

/-
Natural (colimit) directed union for Lemma 7.39.2.

The bespoke `refinementStageDiagramLimitStage` indexes the union by `Σ a, (A a).I`, whose
injections `i ↦ ⟨a, i⟩` are NOT a natural cocone (`⟨a,i⟩ ≠ ⟨b, (hom).k i⟩`), so a coherent chain
of refinement stages cannot contain union stages.  To be faithful to Stacks (the increasing index
sets `I_e ⊆ ⋃ I_e` with genuine inclusions), we index the union by the **directed colimit** of the
preorders `(A a).I` along the embeddings `(hom a≤b).k`; there the injections are natural.

The coherent diagram data is bundled into `DiagramData` to keep the API single-argument.
-/

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open GrothendieckTopology.Point.ofIsCofiltered

universe u v w

namespace CategoryTheory

namespace NaturalDiagramUnion

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

-- Mathlib lifts any base order to `Quotient s` (`Order/Quotient.lean`); since our `ColimitIndex`
-- is a `Quotient`, those generic instances would shadow the bespoke colimit order below.  Disable
-- them in this file so `≤` on `ColimitIndex` is our own `colimitIndexLE`.
attribute [-instance] Quotient.instLE_mathlib Quotient.instPreorder

variable {J : GrothendieckTopology C}
variable {ι : Type w} [Preorder ι]

/-- A coherent directed diagram of packaged refinement stages (the input to the union). -/
structure DiagramData (δ : Type w) [Preorder δ] {ℱ : Sheaf J (Type (max u v w))} {S' : ιᵒᵖ ⥤ C}
    (s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ) where
  obj : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s'
  hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (obj a) (obj b)
  hom_refl : ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (obj a)
  hom_comp : ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
    hom (le_trans hab hbc) = refinement_stage_hom.comp (J := J) (hom hab) (hom hbc)

namespace DiagramData

variable {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
variable {ℱ : Sheaf J (Type (max u v w))} {S' : ιᵒᵖ ⥤ C}
  {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
    (fiber.{max u v w} S').presheafFiber).obj ℱ}
variable (D : DiagramData (J := J) δ s s')

/-- A raw point of the colimit index: a stage together with an index of that stage. -/
abbrev Raw : Type w := Σ a : δ, (D.obj a).I

/-- `k`-naturality: the embedding of a composite is the composite of the embeddings. -/
theorem homk_comp {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c) (i : (D.obj a).I) :
    (D.hom (le_trans hab hbc)).k i = (D.hom hbc).k ((D.hom hab).k i) := by
  rw [D.hom_comp hab hbc]; rfl

theorem homk_refl (a : δ) (i : (D.obj a).I) : (D.hom (show a ≤ a from le_rfl)).k i = i := by
  rw [D.hom_refl a]; rfl

/-- The colimit relation: two raw points agree if they map to the same index at a common stage. -/
def colimitRel (x y : D.Raw) : Prop :=
  ∃ (c : δ) (hac : x.1 ≤ c) (hbc : y.1 ≤ c), (D.hom hac).k x.2 = (D.hom hbc).k y.2

theorem colimitRel_refl (x : D.Raw) : D.colimitRel x x := ⟨x.1, le_rfl, le_rfl, rfl⟩

theorem colimitRel_symm {x y : D.Raw} : D.colimitRel x y → D.colimitRel y x := by
  rintro ⟨c, hac, hbc, h⟩; exact ⟨c, hbc, hac, h.symm⟩

theorem colimitRel_trans {x y z : D.Raw} :
    D.colimitRel x y → D.colimitRel y z → D.colimitRel x z := by
  rintro ⟨c, hac, hyc, hxy⟩ ⟨d, hyd, hzd, hyz⟩
  obtain ⟨e, hce, hde⟩ := directed_of (· ≤ ·) c d
  refine ⟨e, le_trans hac hce, le_trans hzd hde, ?_⟩
  rw [D.homk_comp hac hce, D.homk_comp hzd hde, hxy]
  calc (D.hom hce).k ((D.hom hyc).k y.2)
      = (D.hom (le_trans hyc hce)).k y.2 := (D.homk_comp hyc hce y.2).symm
    _ = (D.hom (le_trans hyd hde)).k y.2 := by congr 1
    _ = (D.hom hde).k ((D.hom hyd).k y.2) := D.homk_comp hyd hde y.2
    _ = (D.hom hde).k ((D.hom hzd).k z.2) := by rw [hyz]

/-- The colimit-index setoid. -/
def colimitSetoid : Setoid D.Raw where
  r := D.colimitRel
  iseqv := ⟨D.colimitRel_refl, D.colimitRel_symm, D.colimitRel_trans⟩

/-- The colimit index of the directed diagram of stage indices. -/
abbrev ColimitIndex : Type w := _root_.Quotient D.colimitSetoid

/-- The natural injection of one stage's index into the colimit index. -/
def colimitι (a : δ) (i : (D.obj a).I) : D.ColimitIndex := _root_.Quotient.mk _ ⟨a, i⟩

/-- Naturality of the colimit injections: going up the diagram first does not change the class. -/
theorem colimitι_natural {a b : δ} (hab : a ≤ b) (i : (D.obj a).I) :
    D.colimitι a i = D.colimitι b ((D.hom hab).k i) := by
  apply _root_.Quotient.sound
  exact ⟨b, hab, le_rfl, by rw [D.homk_refl b]⟩

/-! ### The preorder on the colimit index. -/

/-- The raw order: comparable after mapping both to a common later stage. -/
def colimitLE (x y : D.Raw) : Prop :=
  ∃ (c : δ) (hac : x.1 ≤ c) (hbc : y.1 ≤ c), (D.hom hac).k x.2 ≤ (D.hom hbc).k y.2

/-- Transporting one side of a raw comparison further up the diagram does not change it. -/
theorem colimitLE_mono_left {x y : D.Raw} {c : δ} (hxc : x.1 ≤ c) (hyc : y.1 ≤ c)
    (h : (D.hom hxc).k x.2 ≤ (D.hom hyc).k y.2) {d : δ} (hcd : c ≤ d) :
    (D.hom (le_trans hxc hcd)).k x.2 ≤ (D.hom (le_trans hyc hcd)).k y.2 := by
  rw [D.homk_comp hxc hcd, D.homk_comp hyc hcd]
  exact (D.hom hcd).k.monotone h

theorem colimitLE_refl (x : D.Raw) : D.colimitLE x x := ⟨x.1, le_rfl, le_rfl, le_rfl⟩

theorem colimitLE_trans {x y z : D.Raw} :
    D.colimitLE x y → D.colimitLE y z → D.colimitLE x z := by
  rintro ⟨c, hxc, hyc, hxy⟩ ⟨d, hyd, hzd, hyz⟩
  obtain ⟨e, hce, hde⟩ := directed_of (· ≤ ·) c d
  refine ⟨e, le_trans hxc hce, le_trans hzd hde, ?_⟩
  -- the two middle terms `(hom _).k y.2` coincide by proof irrelevance of the `≤`-witness.
  exact le_trans (colimitLE_mono_left D hxc hyc hxy hce)
    (colimitLE_mono_left D hyd hzd hyz hde)

/-- Two `colimit`-equal raw points have equal image at any common later stage. -/
theorem colimitRel_image_eq {x x' : D.Raw} {cx : δ} (hxcx : x.1 ≤ cx) (hx'cx : x'.1 ≤ cx)
    (hxx' : (D.hom hxcx).k x.2 = (D.hom hx'cx).k x'.2) {f : δ} (hcxf : cx ≤ f)
    (hxf : x.1 ≤ f) (hx'f : x'.1 ≤ f) :
    (D.hom hxf).k x.2 = (D.hom hx'f).k x'.2 := by
  rw [Subsingleton.elim hxf (le_trans hxcx hcxf), Subsingleton.elim hx'f (le_trans hx'cx hcxf),
    D.homk_comp hxcx hcxf, D.homk_comp hx'cx hcxf, hxx']

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a colimit relation can be evaluated
at any common later diagram stage, not just at its stored witness. -/
theorem colimitRel_image_eq_of_common {x y : D.Raw} (hxy : D.colimitRel x y)
    {c : δ} (hxc : x.1 ≤ c) (hyc : y.1 ≤ c) :
    (D.hom hxc).k x.2 = (D.hom hyc).k y.2 := by
  -- Move the stored relation witness and the requested common stage to a common upper stage;
  -- injectivity of the transition embedding reflects the equality back to the requested stage.
  rcases hxy with ⟨d, hxd, hyd, hrel⟩
  obtain ⟨e, hce, hde⟩ := directed_of (· ≤ ·) c d
  have heq :
      (D.hom (le_trans hxc hce)).k x.2 =
        (D.hom (le_trans hyc hce)).k y.2 :=
    D.colimitRel_image_eq hxd hyd hrel hde (le_trans hxc hce) (le_trans hyc hce)
  rw [D.homk_comp hxc hce, D.homk_comp hyc hce] at heq
  exact (D.hom hce).k.injective heq

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the `Quotient.out` representative of a
stage injection has the same image as the original stage index at any common later stage. -/
theorem colimitRel_out_colimitι_image_eq (a : δ) (i : (D.obj a).I)
    {c : δ} (hout : (D.colimitι a i).out.1 ≤ c) (ha : a ≤ c) :
    (D.hom hout).k (D.colimitι a i).out.2 = (D.hom ha).k i := by
  -- Specialize the common-stage normal form to the quotient representative selected by `out`.
  exact D.colimitRel_image_eq_of_common
    (_root_.Quotient.exact (_root_.Quotient.out_eq (D.colimitι a i))) hout ha

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the original stage representative of a
stage injection has the same image as its `Quotient.out` representative at any common later
stage. -/
theorem colimitRel_colimitι_out_image_eq (a : δ) (i : (D.obj a).I)
    {c : δ} (ha : a ≤ c) (hout : (D.colimitι a i).out.1 ≤ c) :
    (D.hom ha).k i = (D.hom hout).k (D.colimitι a i).out.2 := by
  -- This is the symmetric orientation needed for inverse components of the stage inclusion iso.
  exact D.colimitRel_image_eq_of_common
    (D.colimitRel_symm
      (_root_.Quotient.exact (_root_.Quotient.out_eq (D.colimitι a i)))) ha hout

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: after moving a stage representative
through a diagram transition, its image still agrees with the `Quotient.out` representative at
any common later stage. -/
theorem colimitRel_out_colimitι_natural_image_eq {a b : δ} (hab : a ≤ b) (i : (D.obj a).I)
    {c : δ} (hout : (D.colimitι a i).out.1 ≤ c) (hb : b ≤ c) :
    (D.hom hout).k (D.colimitι a i).out.2 = (D.hom hb).k ((D.hom hab).k i) := by
  -- First compare `out` with the original representative at the common stage `c`, then use
  -- functoriality of the diagram transition to factor the original image through `b`.
  calc
    (D.hom hout).k (D.colimitι a i).out.2 = (D.hom (le_trans hab hb)).k i :=
      D.colimitRel_out_colimitι_image_eq a i hout (le_trans hab hb)
    _ = (D.hom hb).k ((D.hom hab).k i) := D.homk_comp hab hb i

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the transitioned stage representative
is the same as the `Quotient.out` representative after evaluating both at a common later stage. -/
theorem colimitRel_colimitι_natural_out_image_eq {a b : δ} (hab : a ≤ b) (i : (D.obj a).I)
    {c : δ} (hb : b ≤ c) (hout : (D.colimitι a i).out.1 ≤ c) :
    (D.hom hb).k ((D.hom hab).k i) = (D.hom hout).k (D.colimitι a i).out.2 := by
  -- This reverse orientation is convenient for component inverse laws and naturality rewrites.
  exact (D.colimitRel_out_colimitι_natural_image_eq hab i hout hb).symm

/-- The raw order respects the colimit relation, hence descends to the quotient. -/
theorem colimitLE_congr {x x' y y' : D.Raw} (hx : D.colimitRel x x') (hy : D.colimitRel y y') :
    D.colimitLE x y → D.colimitLE x' y' := by
  rintro ⟨c, hxc, hyc, hxy⟩
  rcases hx with ⟨cx, hxcx, hx'cx, hxx'⟩
  rcases hy with ⟨cy, hycy, hy'cy, hyy'⟩
  obtain ⟨e, hce, hcxe⟩ := directed_of (· ≤ ·) c cx
  obtain ⟨f, hef, hcyf⟩ := directed_of (· ≤ ·) e cy
  have hcf : c ≤ f := le_trans hce hef
  refine ⟨f, le_trans hx'cx (le_trans hcxe hef), le_trans hy'cy hcyf, ?_⟩
  rw [← colimitRel_image_eq D hxcx hx'cx hxx' (le_trans hcxe hef) (le_trans hxc hcf)
        (le_trans hx'cx (le_trans hcxe hef)),
      ← colimitRel_image_eq D hycy hy'cy hyy' hcyf (le_trans hyc hcf)
        (le_trans hy'cy hcyf)]
  exact colimitLE_mono_left D hxc hyc hxy hcf

/-- The order relation on the colimit index, as a (named) lift of the raw order. -/
def colimitIndexLE : D.ColimitIndex → D.ColimitIndex → Prop :=
  _root_.Quotient.lift₂ D.colimitLE
    (fun _ _ _ _ hx hy => propext ⟨colimitLE_congr D hx hy,
      colimitLE_congr D (D.colimitRel_symm hx) (D.colimitRel_symm hy)⟩)

/-- The lifted order reduces to the raw order on representatives. -/
theorem colimitIndexLE_mk {a b : D.Raw} :
    D.colimitIndexLE (_root_.Quotient.mk _ a) (_root_.Quotient.mk _ b) ↔ D.colimitLE a b := by
  unfold colimitIndexLE; rw [_root_.Quotient.lift₂_mk]

/-- The preorder on the colimit index. -/
instance : Preorder D.ColimitIndex where
  le := D.colimitIndexLE
  lt a b := D.colimitIndexLE a b ∧ ¬ D.colimitIndexLE b a
  le_refl x := by
    induction x using Quotient.ind with | _ a => exact (D.colimitIndexLE_mk).mpr (colimitLE_refl D a)
  le_trans x y z := by
    induction x using Quotient.ind with | _ a => ?_
    induction y using Quotient.ind with | _ b => ?_
    induction z using Quotient.ind with | _ c => ?_
    intro h1 h2
    exact (D.colimitIndexLE_mk).mpr
      (colimitLE_trans D ((D.colimitIndexLE_mk).mp h1) ((D.colimitIndexLE_mk).mp h2))
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the natural colimit index of a directed diagram of directed stage
indices is directed. -/
theorem colimitIndex_directed : IsDirected D.ColimitIndex (· ≤ ·) where
  directed x y := by
    -- Lift two quotient classes to a common diagram stage, then use directedness inside that
    -- stage index to find a common upper bound.
    induction x using Quotient.ind with
    | _ x =>
      induction y using Quotient.ind with
      | _ y =>
        rcases x with ⟨a, i⟩
        rcases y with ⟨b, j⟩
        obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a b
        obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) ((D.hom hac).k i) ((D.hom hbc).k j)
        refine ⟨D.colimitι c k, ?_, ?_⟩
        · exact (D.colimitIndexLE_mk).mpr ⟨c, hac, le_rfl, by
            simpa [D.homk_refl c] using hik⟩
        · exact (D.colimitIndexLE_mk).mpr ⟨c, hbc, le_rfl, by
            simpa [D.homk_refl c] using hjk⟩

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: each stage injection into the natural colimit index preserves
order. -/
theorem colimitι_le {a : δ} {i j : (D.obj a).I} (hij : i ≤ j) :
    D.colimitι a i ≤ D.colimitι a j := by
  -- Realize the comparison at the same diagram stage, where both transition maps are identities.
  exact (D.colimitIndexLE_mk).mpr ⟨a, le_rfl, le_rfl, by
    simpa [D.homk_refl a] using hij⟩

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the natural colimit injection of a fixed stage reflects order. -/
theorem le_of_colimitι_le {a : δ} {i j : (D.obj a).I}
    (hij : D.colimitι a i ≤ D.colimitι a j) : i ≤ j := by
  -- Pull the quotient comparison back to a common later stage; proof irrelevance makes the two
  -- stage maps identical, and the stage morphism's order embedding reflects the inequality.
  rcases (D.colimitIndexLE_mk).mp hij with ⟨c, hac, hac', hle⟩
  have hsame : hac' = hac := Subsingleton.elim _ _
  subst hac'
  exact (D.hom hac).k.map_rel_iff.mp hle

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: within one fixed diagram stage, the natural colimit order is exactly
the original stage order. -/
theorem colimitι_le_iff {a : δ} {i j : (D.obj a).I} :
    D.colimitι a i ≤ D.colimitι a j ↔ i ≤ j := by
  -- Combine monotonicity and order reflection of the stage injection.
  exact ⟨le_of_colimitι_le D, colimitι_le D⟩

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: each stage injection into the natural colimit index is injective. -/
theorem colimitι_injective (a : δ) : Function.Injective (D.colimitι a) := by
  intro i j hij
  -- Equality of quotient classes gives equality after mapping to a common later stage; the
  -- transition map from the fixed stage is an embedding, so equality reflects to the source.
  have hrel : D.colimitRel ⟨a, i⟩ ⟨a, j⟩ := _root_.Quotient.exact hij
  rcases hrel with ⟨c, hac, hac', hidx⟩
  have hsame : hac' = hac := Subsingleton.elim _ _
  subst hac'
  exact (D.hom hac).k.injective hidx

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: each diagram stage embeds as an ordered subindex of the natural
colimit index. -/
def colimitInclusion (a : δ) : (D.obj a).I ↪o D.ColimitIndex where
  toFun := D.colimitι a
  inj' := D.colimitι_injective a
  map_rel_iff' := fun {i j} => D.colimitι_le_iff (a := a) (i := i) (j := j)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the bundled stage inclusion has the expected underlying map. -/
theorem colimitInclusion_apply (a : δ) (i : (D.obj a).I) :
    D.colimitInclusion a i = D.colimitι a i := by
  -- This projection lemma lets later constructions rewrite through the bundled order embedding.
  simp [colimitInclusion]

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the bundled stage inclusions into the natural colimit are natural
with respect to diagram transition maps. -/
theorem colimitInclusion_natural {a b : δ} (hab : a ≤ b) (i : (D.obj a).I) :
    D.colimitInclusion a i = D.colimitInclusion b ((D.hom hab).k i) := by
  -- Reduce the bundled embedding fields to the quotient injections, where naturality is already
  -- the defining quotient relation.
  rw [D.colimitInclusion_apply a i, D.colimitInclusion_apply b ((D.hom hab).k i)]
  exact D.colimitι_natural hab i

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: natural colimit stage inclusions
compose strictly with the diagram transition embeddings. -/
theorem colimitInclusion_comp {a b : δ} (hab : a ≤ b) :
    compose_refinement_embedding (D.hom hab).k (D.colimitInclusion b) =
      D.colimitInclusion a := by
  -- The bundled embedding equality is pointwise exactly quotient naturality.
  ext i
  exact (D.colimitInclusion_natural hab i).symm

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: compatible original embeddings have the
same composite into the natural colimit index. -/
theorem originalEmbedding_colimitInclusion_eq {a b : δ} (hab : a ≤ b)
    (hcompat : (D.hom hab).original_compatible) :
    compose_refinement_embedding (D.obj a).j (D.colimitInclusion a) =
      compose_refinement_embedding (D.obj b).j (D.colimitInclusion b) := by
  -- Rewrite the later original embedding through compatibility, then consume naturality of the
  -- quotient colimit inclusion pointwise.
  rcases hcompat with ⟨hj, _⟩
  rw [hj]
  ext i
  exact D.colimitInclusion_natural hab ((D.obj a).j i)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: original embeddings into the natural
colimit agree after comparing both stages with a common later stage. -/
theorem originalEmbedding_colimitInclusion_eq_of_common {a b c : δ} (hac : a ≤ c)
    (hbc : b ≤ c)
    (hcompat : ∀ ⦃x y : δ⦄ (hxy : x ≤ y), (D.hom hxy).original_compatible) :
    compose_refinement_embedding (D.obj a).j (D.colimitInclusion a) =
      compose_refinement_embedding (D.obj b).j (D.colimitInclusion b) := by
  -- Compare both original embeddings with the common-stage embedding into the quotient colimit.
  exact (D.originalEmbedding_colimitInclusion_eq hac (hcompat hac)).trans
    (D.originalEmbedding_colimitInclusion_eq hbc (hcompat hbc)).symm

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the canonical representative selected by
`Quotient.out` is related to the stage representative of the same colimit class. -/
theorem colimitRel_out_colimitι (a : δ) (i : (D.obj a).I) :
    D.colimitRel (D.colimitι a i).out ⟨a, i⟩ := by
  -- `Quotient.out_eq` says that the chosen representative and the original representative define
  -- the same quotient class; `Quotient.exact` turns this equality into the setoid relation.
  exact _root_.Quotient.exact (_root_.Quotient.out_eq (D.colimitι a i))

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the stage representative is related to
the canonical representative selected by `Quotient.out`. -/
theorem colimitRel_colimitι_out (a : δ) (i : (D.obj a).I) :
    D.colimitRel ⟨a, i⟩ (D.colimitι a i).out := by
  -- The reverse orientation is the symmetry of the quotient-representative relation.
  exact D.colimitRel_symm (D.colimitRel_out_colimitι a i)

/-- Extract a raw comparison from a comparison of classes (via canonical representatives);
stated as an explicit `∃` so the witness components can be projected with `Exists.choose`. -/
theorem colimitLE_of_le {x y : D.ColimitIndex} (h : x ≤ y) :
    ∃ (c : δ) (hac : x.out.1 ≤ c) (hbc : y.out.1 ≤ c),
      (D.hom hac).k x.out.2 ≤ (D.hom hbc).k y.out.2 := by
  have h' : D.colimitIndexLE x y := h
  rw [← _root_.Quotient.out_eq x, ← _root_.Quotient.out_eq y] at h'
  exact (D.colimitIndexLE_mk).mp h'

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a colimit upper bound of a stage-inclusion index can be evaluated at
a genuine later diagram stage. -/
theorem colimitInclusion_le_eval {a : δ} (i : (D.obj a).I) {z : D.ColimitIndex}
    (h : D.colimitInclusion a i ≤ z) :
    ∃ b, ∃ hab : a ≤ b, ∃ hz : z.out.1 ≤ b,
      (D.hom hab).k i ≤ (D.hom hz).k z.out.2 := by
  -- First read the quotient-order comparison on chosen representatives.
  rcases D.colimitLE_of_le h with ⟨c, hxc, hzc, hle⟩
  -- Move that representative comparison to a real diagram stage also above the source stage.
  obtain ⟨b, hcb, hab⟩ := directed_of (· ≤ ·) c a
  refine ⟨b, hab, le_trans hzc hcb, ?_⟩
  have hle_b :
      (D.hom (le_trans hxc hcb)).k (D.colimitInclusion a i).out.2 ≤
        (D.hom (le_trans hzc hcb)).k z.out.2 :=
    colimitLE_mono_left D hxc hzc hle hcb
  -- The chosen representative of the stage inclusion has the same image as the original index at
  -- this later stage, so the comparison is now a statement inside `D.obj b`.
  have hleft :
      (D.hom (le_trans hxc hcb)).k (D.colimitInclusion a i).out.2 =
        (D.hom hab).k i :=
    D.colimitRel_out_colimitι_image_eq a i (le_trans hxc hcb) hab
  rwa [hleft] at hle_b

/-! ### The descended inverse system over the colimit index. -/

/-- The stalk of a raw point: the value of its stage's inverse system at its index. -/
def stalk (x : D.Raw) : C := (D.obj x.1).T.obj (Opposite.op x.2)

/-- The transition morphism between two stalks, computed at a chosen common stage `c`:
go up to `c` via the structure iso, apply the inverse-system transition, come back down. -/
noncomputable def transMapAt (x y : D.Raw) {c : δ} (hxc : x.1 ≤ c) (hyc : y.1 ≤ c)
    (hle : (D.hom hxc).k x.2 ≤ (D.hom hyc).k y.2) : D.stalk y ⟶ D.stalk x :=
  (D.hom hyc).hT.hom.app (Opposite.op y.2) ≫
    (D.obj c).T.map (Quiver.Hom.op (homOfLE hle)) ≫
      (D.hom hxc).hT.inv.app (Opposite.op x.2)

/-- The transition map of a point to itself is the identity (no witness-independence needed:
the two stage-witnesses agree by proof irrelevance and the transition becomes trivial). -/
theorem transMapAt_self (a : D.Raw) {c : δ} (hac hbc : a.1 ≤ c)
    (hle : (D.hom hac).k a.2 ≤ (D.hom hbc).k a.2) :
    D.transMapAt a a hac hbc hle = 𝟙 (D.stalk a) := by
  -- Proof irrelevance identifies the two common-stage witnesses; the middle transition is then
  -- the identity map at the same index, so the structure isomorphism cancels.
  obtain rfl : hbc = hac := Subsingleton.elim _ _
  have hmap : (D.obj c).T.map (homOfLE hle).op = 𝟙 _ := by
    convert (D.obj c).T.map_id (Opposite.op ((D.hom hbc).k a.2)) using 2
  unfold transMapAt
  calc
    (D.hom hbc).hT.hom.app (Opposite.op a.2) ≫
        (D.obj c).T.map (homOfLE hle).op ≫
          (D.hom hbc).hT.inv.app (Opposite.op a.2) =
        (D.hom hbc).hT.hom.app (Opposite.op a.2) ≫ 𝟙 _ ≫
          (D.hom hbc).hT.inv.app (Opposite.op a.2) := by
          simpa [Category.assoc] using
            congrArg
              (fun q => (D.hom hbc).hT.hom.app (Opposite.op a.2) ≫ q ≫
                (D.hom hbc).hT.inv.app (Opposite.op a.2)) hmap
    _ = 𝟙 (D.stalk a) := by
          simp only [stalk, Category.id_comp, Category.comp_id, Iso.hom_inv_id_app]

/-- Witness-independence (one step up): computing the transition map at a higher common stage `d`
gives the same morphism.  The extra `hom hcd` factors cancel by naturality of its structure iso.
(Math proof recorded in memory; the Lean mechanization is a dependent `eqToHom`/`HEq` iso-chase.) -/
theorem transMapAt_up (x y : D.Raw) {c : δ} (hxc : x.1 ≤ c) (hyc : y.1 ≤ c)
    (hle : (D.hom hxc).k x.2 ≤ (D.hom hyc).k y.2) {d : δ} (hcd : c ≤ d) :
    D.transMapAt x y (le_trans hxc hcd) (le_trans hyc hcd)
        (colimitLE_mono_left D hxc hyc hle hcd) = D.transMapAt x y hxc hyc hle := by
  -- Abstract the witness and revert it so that `hom_comp` can rewrite the two upper homs through
  -- the `∀` (otherwise the witness type blocks the motive).
  unfold transMapAt
  generalize colimitLE_mono_left D hxc hyc hle hcd = w
  revert w
  rw [D.hom_comp hxc hcd, D.hom_comp hyc hcd]
  intro w
  dsimp only [refinement_stage_hom.comp, compose_refinement_iso]
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, id_eq, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.assoc, Category.id_comp, Category.comp_id]
  -- Bridge: the `D.obj d` transition of `w` is the composite-functor map of `hle`.
  have hbridge : (homOfLE w).op =
      (D.hom hcd).k.toOrderHom.toFunctor.op.map (homOfLE hle).op := Subsingleton.elim _ _
  -- Use `erw` for the bridge + `H_cd` naturality + `hom ≫ inv` cancellation (defeq matching, to
  -- bridge the comp-obj `≫` representation introduced by the cocycle).
  erw [hbridge, ← Functor.comp_map]
  -- Core: the `hom hcd` conjugation of the `D.obj d` transition is the `D.obj c` transition.
  have core : (D.hom hcd).hT.hom.app (Opposite.op ((D.hom hyc).k y.2)) ≫
      ((D.hom hcd).k.toOrderHom.toFunctor.op ⋙ (D.obj d).T).map (homOfLE hle).op ≫
      (D.hom hcd).hT.inv.app (Opposite.op ((D.hom hxc).k x.2)) =
      (D.obj c).T.map (homOfLE hle).op :=
    NatIso.naturality_2 (D.hom hcd).hT (homOfLE hle).op
  -- Absorb the two associator identities, flatten, then rewrite the conjugated middle by `core`.
  erw [Category.comp_id, Category.id_comp, Category.assoc, reassoc_of% core]
  rfl

/-- Same-stage composition of transition maps: composing the `y→z` and `x→y` transitions computed
at a common stage `d` gives the `x→z` transition.  (No cocycle/dependent rewrite needed — the
intermediate structure iso `(hom hyd).hT` cancels and the two `T d`-transitions merge.) -/
theorem transMapAt_compose (x y z : D.Raw) {d : δ} (hxd : x.1 ≤ d) (hyd : y.1 ≤ d) (hzd : z.1 ≤ d)
    (hxy : (D.hom hxd).k x.2 ≤ (D.hom hyd).k y.2)
    (hyz : (D.hom hyd).k y.2 ≤ (D.hom hzd).k z.2)
    (hxz : (D.hom hxd).k x.2 ≤ (D.hom hzd).k z.2) :
    D.transMapAt y z hyd hzd hyz ≫ D.transMapAt x y hxd hyd hxy =
      D.transMapAt x z hxd hzd hxz := by
  -- Math: the `(hom hyd).hT` inv/hom cancel (via `erw [Iso.inv_hom_id_app_assoc]`, which works)
  -- and the two `D.obj d` transitions merge (`key` below, proven).  Final assembly is blocked by a
  -- `CategoryStruct.comp` instance-path mismatch: after the `erw` cancellation, `rw`/`simp`/`erw`
  -- (even `Category.assoc`) fail to match the resulting `≫`.  Tracked.
  have key : (D.obj d).T.map (homOfLE hyz).op ≫ (D.obj d).T.map (homOfLE hxy).op =
      (D.obj d).T.map (homOfLE hxz).op := by
    rw [← (D.obj d).T.map_comp]; congr 1
  -- Restate the (definitionally-equal) unfolded goal in *fresh* form via `show`, escaping the
  -- comp-obj `≫` representation that blocks `rw`/`simp` after the cancellation.
  show ((D.hom hzd).hT.hom.app (Opposite.op z.2) ≫ (D.obj d).T.map (homOfLE hyz).op ≫
        (D.hom hyd).hT.inv.app (Opposite.op y.2)) ≫
      ((D.hom hyd).hT.hom.app (Opposite.op y.2) ≫ (D.obj d).T.map (homOfLE hxy).op ≫
        (D.hom hxd).hT.inv.app (Opposite.op x.2)) =
      (D.hom hzd).hT.hom.app (Opposite.op z.2) ≫ (D.obj d).T.map (homOfLE hxz).op ≫
        (D.hom hxd).hT.inv.app (Opposite.op x.2)
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc (D.hom hyd).hT (Opposite.op y.2)]
  convert congrArg (fun q => (D.hom hzd).hT.hom.app (Opposite.op z.2) ≫ q ≫
    (D.hom hxd).hT.inv.app (Opposite.op x.2)) key using 2
  exact (Category.assoc ((D.obj d).T.map (homOfLE hyz).op) ((D.obj d).T.map (homOfLE hxy).op)
    ((D.hom hxd).hT.inv.app (Opposite.op x.2))).symm

/-- The canonical transition map between stalks of the chosen representatives of `x ≤ y`. -/
noncomputable def descMap {x y : D.ColimitIndex} (h : x ≤ y) :
    D.stalk y.out ⟶ D.stalk x.out :=
  D.transMapAt x.out y.out (colimitLE_of_le D h).choose_spec.choose
    (colimitLE_of_le D h).choose_spec.choose_spec.choose
    (colimitLE_of_le D h).choose_spec.choose_spec.choose_spec

/-- `descMap` equals `transMapAt` computed at *any* valid common stage (witness-independence:
both the canonical witness stage and `d` are pushed up to a common stage via `transMapAt_up`,
where the two coincide by proof irrelevance of the order witnesses). -/
theorem descMap_eq {x y : D.ColimitIndex} (h : x ≤ y) {d : δ} (hxd : x.out.1 ≤ d)
    (hyd : y.out.1 ≤ d) (hle : (D.hom hxd).k x.out.2 ≤ (D.hom hyd).k y.out.2) :
    D.descMap h = D.transMapAt x.out y.out hxd hyd hle := by
  obtain ⟨e, hse, hde⟩ := directed_of (· ≤ ·) (colimitLE_of_le D h).choose d
  rw [← transMapAt_up D x.out y.out hxd hyd hle hde]
  unfold descMap
  rw [← transMapAt_up D x.out y.out (colimitLE_of_le D h).choose_spec.choose
        (colimitLE_of_le D h).choose_spec.choose_spec.choose
        (colimitLE_of_le D h).choose_spec.choose_spec.choose_spec hse]

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the transition map computed from two
different common-stage witnesses is independent of the chosen witness. -/
theorem transMapAt_eq_of_common (x y : D.Raw) {c d : δ} (hxc : x.1 ≤ c) (hyc : y.1 ≤ c)
    (hlec : (D.hom hxc).k x.2 ≤ (D.hom hyc).k y.2)
    (hxd : x.1 ≤ d) (hyd : y.1 ≤ d)
    (hled : (D.hom hxd).k x.2 ≤ (D.hom hyd).k y.2) :
    D.transMapAt x y hxc hyc hlec = D.transMapAt x y hxd hyd hled := by
  -- Push both computations to one later common stage and use one-step witness independence on
  -- each side.
  obtain ⟨e, hce, hde⟩ := directed_of (· ≤ ·) c d
  rw [← D.transMapAt_up x y hxc hyc hlec hce]
  rw [← D.transMapAt_up x y hxd hyd hled hde]

/-- The descended inverse system over the colimit index.

The object part is the stalk of the canonical representative; the morphism part is `descMap`.
Functoriality (`map_id`, `map_comp`) rests on the witness-independence of `transMapAt` — an
`hT`-cocycle iso-chase — which is the remaining coherence obligation of the overhaul. -/
noncomputable def system : (D.ColimitIndex)ᵒᵖ ⥤ C where
  obj x := D.stalk x.unop.out
  map {x y} f := D.descMap (leOfHom f.unop)
  map_id x := by
    -- `descMap` of `𝟙` is the identity by `transMapAt_self` (no witness-independence needed).
    exact D.transMapAt_self _ _ _ _
  map_comp {x y z} f g := by
    -- Reduce all three `descMap`s to `transMapAt` at one common stage `d` (via `descMap_eq`),
    -- then compose with `transMapAt_compose`.
    obtain ⟨s1, hb1, ha1, hle1⟩ := colimitLE_of_le D (leOfHom f.unop)
    obtain ⟨s2, hc2, hb2, hle2⟩ := colimitLE_of_le D (leOfHom g.unop)
    obtain ⟨s3, hc3, ha3, hle3⟩ := colimitLE_of_le D (leOfHom (f ≫ g).unop)
    obtain ⟨s12, k1, k2⟩ := directed_of (· ≤ ·) s1 s2
    obtain ⟨d, k12, k3⟩ := directed_of (· ≤ ·) s12 s3
    have had : (Opposite.unop x).out.1 ≤ d := le_trans ha1 (le_trans k1 k12)
    have hbd : (Opposite.unop y).out.1 ≤ d := le_trans hb1 (le_trans k1 k12)
    have hcd : (Opposite.unop z).out.1 ≤ d := le_trans hc2 (le_trans k2 k12)
    have hle_ba : (D.hom hbd).k (Opposite.unop y).out.2 ≤ (D.hom had).k (Opposite.unop x).out.2 :=
      colimitLE_mono_left D hb1 ha1 hle1 (le_trans k1 k12)
    have hle_cb : (D.hom hcd).k (Opposite.unop z).out.2 ≤ (D.hom hbd).k (Opposite.unop y).out.2 :=
      colimitLE_mono_left D hc2 hb2 hle2 (le_trans k2 k12)
    have hle_ca : (D.hom hcd).k (Opposite.unop z).out.2 ≤ (D.hom had).k (Opposite.unop x).out.2 :=
      colimitLE_mono_left D hc3 ha3 hle3 k3
    show D.descMap (leOfHom (f ≫ g).unop) = D.descMap (leOfHom f.unop) ≫ D.descMap (leOfHom g.unop)
    rw [descMap_eq D (leOfHom (f ≫ g).unop) hcd had hle_ca,
        descMap_eq D (leOfHom f.unop) hbd had hle_ba,
        descMap_eq D (leOfHom g.unop) hcd hbd hle_cb]
    exact (transMapAt_compose D (Opposite.unop z).out (Opposite.unop y).out (Opposite.unop x).out
      hcd hbd had hle_cb hle_ba hle_ca).symm

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a common diagram stage witnessing that the quotient representative
of a stage-inclusion class is equivalent to the original stage index. -/
noncomputable def outColimitStage (a : δ) (i : (D.obj a).I) : δ :=
  (D.colimitRel_out_colimitι a i).choose

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the chosen quotient representative maps to the selected common
stage. -/
theorem outColimitStage_out_le (a : δ) (i : (D.obj a).I) :
    (D.colimitι a i).out.1 ≤ D.outColimitStage a i := by
  -- Project the first stage-comparison witness from the chosen quotient relation.
  exact (D.colimitRel_out_colimitι a i).choose_spec.choose

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the original stage index maps to the selected common stage. -/
theorem outColimitStage_source_le (a : δ) (i : (D.obj a).I) :
    a ≤ D.outColimitStage a i := by
  -- Project the second stage-comparison witness from the chosen quotient relation.
  exact (D.colimitRel_out_colimitι a i).choose_spec.choose_spec.choose

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: at the selected common stage, the quotient representative and the
original stage index have the same image. -/
theorem outColimitStage_image_eq (a : δ) (i : (D.obj a).I) :
    (D.hom (D.outColimitStage_out_le a i)).k (D.colimitι a i).out.2 =
      (D.hom (D.outColimitStage_source_le a i)).k i := by
  -- The equality component of the chosen quotient relation is the required image comparison.
  exact (D.colimitRel_out_colimitι a i).choose_spec.choose_spec.choose_spec

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the forward component of the canonical isomorphism from a diagram
stage to the quotient-colimit system restricted along its stage inclusion. -/
noncomputable def colimitInclusionIsoHomApp (a : δ) (i : (D.obj a).I) :
    (D.obj a).T.obj (Opposite.op i) ⟶
      D.system.obj (Opposite.op (D.colimitInclusion a i)) :=
  D.transMapAt (D.colimitι a i).out ⟨a, i⟩
    (D.outColimitStage_out_le a i)
    (D.outColimitStage_source_le a i)
    (le_of_eq (D.outColimitStage_image_eq a i))

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the inverse component of the canonical isomorphism from a diagram
stage to the quotient-colimit system restricted along its stage inclusion. -/
noncomputable def colimitInclusionIsoInvApp (a : δ) (i : (D.obj a).I) :
    D.system.obj (Opposite.op (D.colimitInclusion a i)) ⟶
      (D.obj a).T.obj (Opposite.op i) :=
  D.transMapAt ⟨a, i⟩ (D.colimitι a i).out
    (D.outColimitStage_source_le a i)
    (D.outColimitStage_out_le a i)
    (le_of_eq (D.outColimitStage_image_eq a i).symm)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the forward and inverse quotient-inclusion components compose to
the identity on the source stage. -/
theorem colimitInclusionIso_hom_inv_id_app (a : δ) (i : (D.obj a).I) :
    D.colimitInclusionIsoHomApp a i ≫ D.colimitInclusionIsoInvApp a i =
      𝟙 ((D.obj a).T.obj (Opposite.op i)) := by
  -- Compose the two transport maps at the same common stage, then reduce the resulting
  -- self-transport to the identity.
  let hout := D.outColimitStage_out_le a i
  let ha := D.outColimitStage_source_le a i
  let heq := D.outColimitStage_image_eq a i
  have hcomp := D.transMapAt_compose ⟨a, i⟩ (D.colimitι a i).out ⟨a, i⟩
    ha hout ha (le_of_eq heq.symm) (le_of_eq heq) le_rfl
  have hself := D.transMapAt_self ⟨a, i⟩ ha ha le_rfl
  simpa [colimitInclusionIsoHomApp, colimitInclusionIsoInvApp, hout, ha, heq]
    using hcomp.trans hself

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the inverse and forward quotient-inclusion components compose to
the identity on the quotient-colimit system. -/
theorem colimitInclusionIso_inv_hom_id_app (a : δ) (i : (D.obj a).I) :
    D.colimitInclusionIsoInvApp a i ≫ D.colimitInclusionIsoHomApp a i =
      𝟙 (D.system.obj (Opposite.op (D.colimitInclusion a i))) := by
  -- This is the symmetric component calculation: compose through the same common stage and
  -- finish with the self-transport identity.
  let hout := D.outColimitStage_out_le a i
  let ha := D.outColimitStage_source_le a i
  let heq := D.outColimitStage_image_eq a i
  have hcomp := D.transMapAt_compose (D.colimitι a i).out ⟨a, i⟩ (D.colimitι a i).out
    hout ha hout (le_of_eq heq) (le_of_eq heq.symm) le_rfl
  have hself := D.transMapAt_self (D.colimitι a i).out hout hout le_rfl
  simpa [colimitInclusionIsoHomApp, colimitInclusionIsoInvApp, hout, ha, heq]
    using hcomp.trans hself

omit [IsDirected δ (· ≤ ·)] in
/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: transport inside one diagram stage agrees with the original
inverse-system transition map. -/
theorem transMapAt_same_stage (a : δ) {i j : (D.obj a).I} (hij : i ≤ j) :
    D.transMapAt ⟨a, i⟩ ⟨a, j⟩ (le_rfl : a ≤ a) (le_rfl : a ≤ a)
        ((D.hom (show a ≤ a from le_rfl)).k.monotone hij) =
      (D.obj a).T.map (homOfLE hij).op := by
  -- Rewrite the reflexive diagram morphism to the identity stage morphism and normalize the
  -- two identity components of its refinement isomorphism.
  unfold transMapAt
  rw [D.hom_refl a]
  simp [refinement_stage_hom_refl, identity_refinement_iso, Functor.leftUnitor]
  convert (by simp : 𝟙 ((D.obj a).T.obj (Opposite.op j)) ≫
      (D.obj a).T.map (homOfLE hij).op ≫ 𝟙 ((D.obj a).T.obj (Opposite.op i)) =
      (D.obj a).T.map (homOfLE hij).op) using 2

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the component isomorphism identifying a diagram stage with the
restriction of the quotient-colimit system to that stage. -/
noncomputable def colimitInclusionIsoApp (a : δ) (X : (D.obj a).Iᵒᵖ) :
    (D.obj a).T.obj X ≅
      (((D.colimitInclusion a).toOrderHom.toFunctor).op ⋙ D.system).obj X where
  hom := D.colimitInclusionIsoHomApp a (Opposite.unop X)
  inv := D.colimitInclusionIsoInvApp a (Opposite.unop X)
  hom_inv_id := D.colimitInclusionIso_hom_inv_id_app a (Opposite.unop X)
  inv_hom_id := D.colimitInclusionIso_inv_hom_id_app a (Opposite.unop X)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the quotient-inclusion component isomorphisms are natural in the
stage index. -/
theorem colimitInclusionIso_naturality (a : δ) :
    ∀ {X Y : (D.obj a).Iᵒᵖ} (f : X ⟶ Y),
      (D.obj a).T.map f ≫ (D.colimitInclusionIsoApp a Y).hom =
        (D.colimitInclusionIsoApp a X).hom ≫
          (((D.colimitInclusion a).toOrderHom.toFunctor).op ⋙ D.system).map f := by
  -- After unfolding the component maps, functoriality of `D.system` and the directed transport
  -- normal forms reduce this to the construction of `transMapAt`.
  intro X Y f
  cases X using Opposite.rec
  cases Y using Opposite.rec
  rename_i i j
  let hji : j ≤ i := leOfHom f.unop
  have hf : f = (homOfLE hji).op := Subsingleton.elim _ _
  rw [hf]
  dsimp [colimitInclusionIsoApp, colimitInclusionIsoHomApp, system]
  -- Move both quotient representatives to one common diagram stage, so the naturality square
  -- becomes a single associativity statement for `transMapAt`.
  obtain ⟨d, hcid, hcjd⟩ :=
    directed_of (· ≤ ·) (D.outColimitStage a i) (D.outColimitStage a j)
  let hi : a ≤ d := le_trans (D.outColimitStage_source_le a i) hcid
  let hj : a ≤ d := le_trans (D.outColimitStage_source_le a j) hcjd
  let hoi : (D.colimitι a i).out.1 ≤ d := le_trans (D.outColimitStage_out_le a i) hcid
  let hoj : (D.colimitι a j).out.1 ≤ d := le_trans (D.outColimitStage_out_le a j) hcjd
  have hei : (D.hom hoi).k (D.colimitι a i).out.2 = (D.hom hi).k i := by
    rw [D.homk_comp (D.outColimitStage_out_le a i) hcid,
      D.homk_comp (D.outColimitStage_source_le a i) hcid,
      D.outColimitStage_image_eq]
  have hej : (D.hom hoj).k (D.colimitι a j).out.2 = (D.hom hj).k j := by
    rw [D.homk_comp (D.outColimitStage_out_le a j) hcjd,
      D.homk_comp (D.outColimitStage_source_le a j) hcjd,
      D.outColimitStage_image_eq]
  have hraw : (D.hom hj).k j ≤ (D.hom hi).k i := by
    have hh : hj = hi := Subsingleton.elim _ _
    subst hj
    exact (D.hom hi).k.monotone hji
  have hout : (D.hom hoj).k (D.colimitι a j).out.2 ≤
      (D.hom hoi).k (D.colimitι a i).out.2 := by
    rw [hej, hei]
    exact hraw
  have hout_raw_i : (D.hom hoj).k (D.colimitι a j).out.2 ≤ (D.hom hi).k i := by
    rw [hej]
    exact hraw
  let hq : D.colimitInclusion a j ≤ D.colimitInclusion a i :=
    (D.colimitInclusion a).monotone hji
  rw [D.descMap_eq hq hoj hoi hout]
  rw [← D.transMapAt_same_stage a hji]
  rw [← D.transMapAt_up ⟨a, j⟩ ⟨a, i⟩ (le_rfl : a ≤ a) (le_rfl : a ≤ a)
    ((D.hom (show a ≤ a from le_rfl)).k.monotone hji) hj]
  rw [← D.transMapAt_up (D.colimitι a j).out ⟨a, j⟩
    (D.outColimitStage_out_le a j) (D.outColimitStage_source_le a j)
    (le_of_eq (D.outColimitStage_image_eq a j)) hcjd]
  rw [← D.transMapAt_up (D.colimitι a i).out ⟨a, i⟩
    (D.outColimitStage_out_le a i) (D.outColimitStage_source_le a i)
    (le_of_eq (D.outColimitStage_image_eq a i)) hcid]
  have hleft := D.transMapAt_compose (D.colimitι a j).out ⟨a, j⟩ ⟨a, i⟩
    hoj hj hi (le_of_eq hej) hraw hout_raw_i
  have hright := D.transMapAt_compose (D.colimitι a j).out (D.colimitι a i).out ⟨a, i⟩
    hoj hoi hi hout (le_of_eq hei) hout_raw_i
  exact hleft.trans hright.symm

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: each diagram stage is naturally isomorphic to the quotient-colimit
system restricted along its canonical inclusion. -/
noncomputable def colimitInclusionIso (a : δ) :
    (D.obj a).T ≅ ((D.colimitInclusion a).toOrderHom.toFunctor).op ⋙ D.system :=
  NatIso.ofComponents (fun X => D.colimitInclusionIsoApp a X)
    (D.colimitInclusionIso_naturality a)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the original embedding chosen for the
natural quotient-limit stage. -/
def limitOriginalEmbedding (a0 : δ) : ι ↪o D.ColimitIndex :=
  compose_refinement_embedding (D.obj a0).j (D.colimitInclusion a0)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the original system is identified with
the natural quotient-limit system along the chosen original embedding. -/
noncomputable def limitOriginalIso (a0 : δ) :
    S' ≅ ((D.limitOriginalEmbedding a0).toOrderHom.toFunctor).op ⋙ D.system :=
  compose_refinement_iso (D.obj a0).j (D.colimitInclusion a0) (D.obj a0).e
    (D.colimitInclusionIso a0)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a packaged stage morphism is determined by its order embedding and
the inverse-system isomorphism carried by the morphism. -/
theorem refinementStageHom_eq_of_k_hT
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {f g : refinement_stage_hom (J := J) A B}
    (hk : f.k = g.k) (hT : HEq f.hT g.hT) : f = g := by
  -- Once the two data fields are identified, the monotonicity proofs are propositionally
  -- irrelevant, so the two packaged morphism records are equal.
  cases f with
  | mk fk fhT fmono =>
      cases g with
      | mk gk ghT gmono =>
          dsimp at hk hT
          subst gk
          cases hT
          rfl

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the original fiber map of the natural quotient-limit stage factors
through the chosen base stage and then through its canonical colimit inclusion. -/
theorem limitOriginal_presheafFiber_app (a0 : δ) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    ((refinementFiber (D.limitOriginalEmbedding a0) D.system (D.limitOriginalIso a0)
      ).presheafFiber).app F =
      ((refinementFiber (D.obj a0).j (D.obj a0).T (D.obj a0).e).presheafFiber).app F ≫
        ((refinementFiber (D.colimitInclusion a0) D.system
          (D.colimitInclusionIso a0)).presheafFiber).app F := by
  -- Expand the stored original data as the composite of the base-stage refinement with the
  -- quotient-colimit inclusion, then read the induced presheaf-fiber map as a composite.
  rw [show refinementFiber (D.limitOriginalEmbedding a0) D.system (D.limitOriginalIso a0) =
      refinementFiber (D.obj a0).j (D.obj a0).T (D.obj a0).e ≫
        refinementFiber (D.colimitInclusion a0) D.system (D.colimitInclusionIso a0) by
        exact refinementFiber_comp (D.obj a0).j (D.colimitInclusion a0)
          (D.obj a0).e (D.colimitInclusionIso a0)]
  exact refinementFiber_presheafFiber_app_comp
    (j := (D.obj a0).j) (k := D.colimitInclusion a0) (e := (D.obj a0).e)
    (e' := D.colimitInclusionIso a0) F

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: an order comparison from a stage
inclusion into the quotient colimit can be represented at a genuine later diagram stage. -/
theorem colimitInclusion_le_common_stage
    {a : δ} (i : (D.obj a).I) {z : D.ColimitIndex}
    (hiz : D.colimitInclusion a i ≤ z) :
    ∃ b, ∃ hstage : D.outColimitStage a i ≤ b, ∃ hzb : z.out.1 ≤ b,
      (D.hom (le_trans (D.outColimitStage_source_le a i) hstage)).k i ≤
        (D.hom hzb).k z.out.2 := by
  -- Start with the raw quotient-order witness between the chosen representatives.
  rcases D.colimitLE_of_le hiz with ⟨c, houtc, hzc, hle⟩
  -- Move that witness to a stage that also sees the canonical stage representative of
  -- `D.colimitInclusion a i`.
  obtain ⟨b, hcb, hdb⟩ := directed_of (· ≤ ·) c (D.outColimitStage a i)
  let houtb : (D.colimitInclusion a i).out.1 ≤ b := le_trans houtc hcb
  let hzb : z.out.1 ≤ b := le_trans hzc hcb
  have hleb :
      (D.hom houtb).k (D.colimitInclusion a i).out.2 ≤
        (D.hom hzb).k z.out.2 := by
    exact D.colimitLE_mono_left houtc hzc hle hcb
  have hout_eq :
      (D.hom houtb).k (D.colimitInclusion a i).out.2 =
        (D.hom (le_trans (D.outColimitStage_source_le a i) hdb)).k i := by
    -- Replace the bundled inclusion by the quotient injection and use the common-stage
    -- representative comparison.
    simpa [D.colimitInclusion_apply] using
      D.colimitRel_out_colimitι_image_eq a i (c := b) houtb
        (le_trans (D.outColimitStage_source_le a i) hdb)
  refine ⟨b, hdb, hzb, ?_⟩
  rwa [hout_eq] at hleb

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: after choosing a real common stage for
a quotient comparison, the quotient transition followed by the stage-inclusion inverse is the
ordinary transition inside that real stage. -/
theorem colimitInclusion_descMap_invApp_eq
    {a : δ} (i : (D.obj a).I) {z : D.ColimitIndex}
    (hiz : D.colimitInclusion a i ≤ z)
    {b : δ} (hstage : D.outColimitStage a i ≤ b) (hzb : z.out.1 ≤ b)
    (hidx :
      (D.hom (le_trans (D.outColimitStage_source_le a i) hstage)).k i ≤
        (D.hom hzb).k z.out.2) :
    (D.hom hzb).hT.inv.app (Opposite.op z.out.2) ≫ D.descMap hiz ≫
        D.colimitInclusionIsoInvApp a i =
      (D.obj b).T.map (homOfLE hidx).op ≫
        (D.hom (le_trans (D.outColimitStage_source_le a i) hstage)).hT.inv.app
          (Opposite.op i) := by
  -- Express the quotient representative of `D.colimitInclusion a i` at the same real stage `b`.
  let hab : a ≤ b := le_trans (D.outColimitStage_source_le a i) hstage
  let hout : (D.colimitInclusion a i).out.1 ≤ b := by
    simpa [D.colimitInclusion_apply] using le_trans (D.outColimitStage_out_le a i) hstage
  have hout_eq :
      (D.hom hout).k (D.colimitInclusion a i).out.2 = (D.hom hab).k i := by
    simpa [D.colimitInclusion_apply, hab, hout] using
      D.colimitRel_out_colimitι_image_eq a i (c := b) hout hab
  have hle_out :
      (D.hom hout).k (D.colimitInclusion a i).out.2 ≤
        (D.hom hzb).k z.out.2 := by
    rwa [hout_eq]
  have hdesc : D.descMap hiz =
      D.transMapAt (D.colimitInclusion a i).out z.out hout hzb hle_out :=
    D.descMap_eq hiz hout hzb hle_out
  have hinv :
      D.colimitInclusionIsoInvApp a i =
        D.transMapAt ⟨a, i⟩ (D.colimitInclusion a i).out hab hout
          (le_of_eq hout_eq.symm) := by
    -- Move the inverse component from its canonical `outColimitStage` witness to `b`.
    rw [colimitInclusionIsoInvApp]
    rw [← D.transMapAt_up ⟨a, i⟩ (D.colimitι a i).out
      (D.outColimitStage_source_le a i) (D.outColimitStage_out_le a i)
      (le_of_eq (D.outColimitStage_image_eq a i).symm) hstage]
    rfl
  have hcomp := D.transMapAt_compose ⟨a, i⟩ (D.colimitInclusion a i).out z.out
    hab hout hzb (le_of_eq hout_eq.symm) hle_out hidx
  rw [hdesc, hinv]
  erw [hcomp]
  unfold transMapAt
  erw [Iso.inv_hom_id_app_assoc (D.hom hzb).hT (Opposite.op z.out.2)]
  rfl

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: equality after applying a stage's
canonical map into the quotient-colimit fiber is already witnessed after passing to a later
diagram stage. -/
theorem colimitInclusion_presheafFiber_eq_of_eq
    (a : δ) (F : Cᵒᵖ ⥤ Type (max u v w))
    {x y : (fiber.{max u v w} (D.obj a).T).presheafFiber.obj F}
    (hxy :
      ((refinementFiber (D.colimitInclusion a) D.system
        (D.colimitInclusionIso a)).presheafFiber).app F x =
      ((refinementFiber (D.colimitInclusion a) D.system
        (D.colimitInclusionIso a)).presheafFiber).app F y) :
    ∃ b, ∃ hab : a ≤ b,
      ((refinementFiber (D.hom hab).k (D.obj b).T
        (D.hom hab).hT).presheafFiber).app F x =
      ((refinementFiber (D.hom hab).k (D.obj b).T
        (D.hom hab).hT).presheafFiber).app F y := by
  -- Reduce the source-stage elements to common presheaf-fiber generators.
  classical
  obtain ⟨j₀, _z₀, _hx₀⟩ :=
    CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
      (CategoryTheory.Limits.colimit.isColimit
        ((CategoryTheory.CategoryOfElements.π (fiber.{max u v w} (D.obj a).T)).op ⋙ F)) x
  rcases fiberMk_jointly_surjective (Opposite.unop j₀).2 with ⟨U₀, _f₀, _hf₀⟩
  letI : Nonempty (D.obj a).I := ⟨Opposite.unop U₀⟩
  obtain ⟨X, x₁, z, z', hx, hy⟩ :=
    inverse_system_presheafFiber_jointly_surjective₂ (S := (D.obj a).T) (F := F) x y
  rcases fiberMk_jointly_surjective x₁ with ⟨U, f, rfl⟩
  let i : (D.obj a).I := Opposite.unop U
  let UΛ : D.ColimitIndexᵒᵖ := Opposite.op (D.colimitInclusion a i)
  let fΛ : D.system.obj UΛ ⟶ X := (D.colimitInclusionIso a).inv.app U ≫ f
  let xΛ : (fiber.{max u v w} D.system).obj X := fiberMk fΛ
  -- The assumed equality is now an equality in the quotient-colimit presheaf fiber.
  have hlim :
      (fiber.{max u v w} D.system).toPresheafFiber X xΛ F z =
        (fiber.{max u v w} D.system).toPresheafFiber X xΛ F z' := by
    calc
      (fiber.{max u v w} D.system).toPresheafFiber X xΛ F z =
          ((refinementFiber (D.colimitInclusion a) D.system
            (D.colimitInclusionIso a)).presheafFiber).app F
            ((fiber.{max u v w} (D.obj a).T).toPresheafFiber X (fiberMk f) F z) := by
            symm
            simpa [xΛ, fΛ, UΛ, i] using
              congrFun
                (NatTrans.toPresheafFiber_presheafFiber_app
                  (η := refinementFiber (D.colimitInclusion a) D.system
                    (D.colimitInclusionIso a)) (F := F) X (fiberMk f)) z
      _ = ((refinementFiber (D.colimitInclusion a) D.system
            (D.colimitInclusionIso a)).presheafFiber).app F x := by
            rw [hx]
      _ = ((refinementFiber (D.colimitInclusion a) D.system
            (D.colimitInclusionIso a)).presheafFiber).app F y := hxy
      _ = ((refinementFiber (D.colimitInclusion a) D.system
            (D.colimitInclusionIso a)).presheafFiber).app F
            ((fiber.{max u v w} (D.obj a).T).toPresheafFiber X (fiberMk f) F z') := by
            rw [hy]
      _ = (fiber.{max u v w} D.system).toPresheafFiber X xΛ F z' := by
            simpa [xΛ, fΛ, UΛ, i] using
              congrFun
                (NatTrans.toPresheafFiber_presheafFiber_app
                  (η := refinementFiber (D.colimitInclusion a) D.system
                    (D.colimitInclusionIso a)) (F := F) X (fiberMk f)) z'
  have hid :
      (fiber.{max u v w} D.system).toPresheafFiber (D.system.obj UΛ)
          (fiberMk (𝟙 (D.system.obj UΛ))) F (F.map fΛ.op z) =
        (fiber.{max u v w} D.system).toPresheafFiber (D.system.obj UΛ)
          (fiberMk (𝟙 (D.system.obj UΛ))) F (F.map fΛ.op z') := by
    have hz :
        (fiber.{max u v w} D.system).toPresheafFiber (D.system.obj UΛ)
            (fiberMk (𝟙 (D.system.obj UΛ))) F (F.map fΛ.op z) =
          (fiber.{max u v w} D.system).toPresheafFiber X xΛ F z := by
      calc
        (fiber.{max u v w} D.system).toPresheafFiber (D.system.obj UΛ)
            (fiberMk (𝟙 (D.system.obj UΛ))) F (F.map fΛ.op z) =
            (fiber.{max u v w} D.system).toPresheafFiber X
              ((fiber.{max u v w} D.system).map fΛ (fiberMk (𝟙 (D.system.obj UΛ)))) F z := by
              simpa using
                congrFun
                  ((fiber.{max u v w} D.system).toPresheafFiber_w
                    (F := F) fΛ (fiberMk (𝟙 (D.system.obj UΛ)))) z
        _ = (fiber.{max u v w} D.system).toPresheafFiber X xΛ F z := by
              simp [xΛ, fΛ]
    have hz' :
        (fiber.{max u v w} D.system).toPresheafFiber (D.system.obj UΛ)
            (fiberMk (𝟙 (D.system.obj UΛ))) F (F.map fΛ.op z') =
          (fiber.{max u v w} D.system).toPresheafFiber X xΛ F z' := by
      calc
        (fiber.{max u v w} D.system).toPresheafFiber (D.system.obj UΛ)
            (fiberMk (𝟙 (D.system.obj UΛ))) F (F.map fΛ.op z') =
            (fiber.{max u v w} D.system).toPresheafFiber X
              ((fiber.{max u v w} D.system).map fΛ (fiberMk (𝟙 (D.system.obj UΛ)))) F z' := by
              simpa using
                congrFun
                  ((fiber.{max u v w} D.system).toPresheafFiber_w
                    (F := F) fΛ (fiberMk (𝟙 (D.system.obj UΛ)))) z'
        _ = (fiber.{max u v w} D.system).toPresheafFiber X xΛ F z' := by
              simp [xΛ, fΛ]
    exact hz.trans (hlim.trans hz'.symm)
  -- Reflect equality in the filtered colimit over the quotient index, then evaluate the quotient
  -- comparison at a real later diagram stage.
  letI : Nonempty D.ColimitIndex := ⟨D.colimitInclusion a i⟩
  letI : IsDirected D.ColimitIndex (· ≤ ·) := D.colimitIndex_directed
  have hcol :
      (inverse_system_presheafFiberCocone (S := D.system) F).ι.app (Opposite.op UΛ)
          (F.map fΛ.op z) =
        (inverse_system_presheafFiberCocone (S := D.system) F).ι.app (Opposite.op UΛ)
          (F.map fΛ.op z') := by
    simpa [inverse_system_presheafFiberCocone, UΛ] using hid
  rcases (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
      (F := D.system.op ⋙ F)
      (ht := inverse_system_presheafFiber_isColimit (S := D.system) F)
      (i := Opposite.op UΛ) (x := F.map fΛ.op z) (y := F.map fΛ.op z')).1 hcol with
    ⟨Zopop, m, hm⟩
  let Z : D.ColimitIndex := Opposite.unop (Opposite.unop Zopop)
  let hXaZ : D.colimitInclusion a i ≤ Z := leOfHom m.unop.unop
  rcases D.colimitInclusion_le_common_stage i hXaZ with ⟨b, hstage, hZb, hidx⟩
  let hab : a ≤ b := le_trans (D.outColimitStage_source_le a i) hstage
  refine ⟨b, hab, ?_⟩
  let gB : (D.obj b).T.obj (Opposite.op ((D.hom hZb).k Z.out.2)) ⟶ X :=
    (D.obj b).T.map (homOfLE hidx).op ≫ (D.hom hab).hT.inv.app U ≫ f
  have hm_eval :
      F.map ((D.hom hZb).hT.inv.app (Opposite.op Z.out.2)).op
          (F.map (D.descMap hXaZ).op
            (F.map ((D.colimitInclusionIso a).inv.app U).op (F.map f.op z))) =
        F.map ((D.hom hZb).hT.inv.app (Opposite.op Z.out.2)).op
          (F.map (D.descMap hXaZ).op
            (F.map ((D.colimitInclusionIso a).inv.app U).op (F.map f.op z'))) := by
    simpa [UΛ, Z, hXaZ, fΛ] using
      congrArg (fun q => F.map ((D.hom hZb).hT.inv.app (Opposite.op Z.out.2)).op q) hm
  have hm' : F.map gB.op z = F.map gB.op z' := by
    -- The named normal-form lemma turns the quotient transition into the concrete map through
    -- the real stage `b`.
    have hmap := D.colimitInclusion_descMap_invApp_eq i hXaZ hstage hZb hidx
    have hmapU :
        (D.hom hZb).hT.inv.app (Opposite.op Z.out.2) ≫ D.descMap hXaZ ≫
            (D.colimitInclusionIso a).inv.app U =
          (D.obj b).T.map (homOfLE hidx).op ≫ (D.hom hab).hT.inv.app U := by
      rw [show (D.colimitInclusionIso a).inv.app U = D.colimitInclusionIsoInvApp a i by
        simp [colimitInclusionIso, colimitInclusionIsoApp, i]]
      simpa [hab, i] using hmap
    have hm_eval' :
        F.map
            (((D.hom hZb).hT.inv.app (Opposite.op Z.out.2) ≫ D.descMap hXaZ ≫
                (D.colimitInclusionIso a).inv.app U) ≫ f).op z =
          F.map
            (((D.hom hZb).hT.inv.app (Opposite.op Z.out.2) ≫ D.descMap hXaZ ≫
                (D.colimitInclusionIso a).inv.app U) ≫ f).op z' := by
      simpa [FunctorToTypes.map_comp_apply, Category.assoc] using hm_eval
    have hgf :
        (((D.hom hZb).hT.inv.app (Opposite.op Z.out.2) ≫ D.descMap hXaZ ≫
            (D.colimitInclusionIso a).inv.app U) ≫ f) = gB := by
      rw [hmapU]
      simp [gB, Category.assoc]
    exact
      (congrArg (fun q => F.map q.op z) hgf).symm.trans
        (hm_eval'.trans (congrArg (fun q => F.map q.op z') hgf))
  letI : Nonempty (D.obj b).I := ⟨(D.hom hZb).k Z.out.2⟩
  have hstage_eq :
      (fiber.{max u v w} (D.obj b).T).toPresheafFiber X
          ((refinementFiber (D.hom hab).k (D.obj b).T (D.hom hab).hT).app X (fiberMk f)) F z =
        (fiber.{max u v w} (D.obj b).T).toPresheafFiber X
          ((refinementFiber (D.hom hab).k (D.obj b).T (D.hom hab).hT).app X (fiberMk f)) F z' := by
    refine (inverseSystem_toPresheafFiber_eq_iff (D.obj b).T X
      ((refinementFiber (D.hom hab).k (D.obj b).T (D.hom hab).hT).app X (fiberMk f)) z z').2 ?_
    refine ⟨(D.obj b).T.obj (Opposite.op ((D.hom hZb).k Z.out.2)), gB,
      fiberMk (𝟙 ((D.obj b).T.obj (Opposite.op ((D.hom hZb).k Z.out.2)))), ?_, hm'⟩
    simp [gB, refinementFiber_app_fiberMk]
  calc
    ((refinementFiber (D.hom hab).k (D.obj b).T (D.hom hab).hT).presheafFiber).app F x =
        ((refinementFiber (D.hom hab).k (D.obj b).T (D.hom hab).hT).presheafFiber).app F
          ((fiber.{max u v w} (D.obj a).T).toPresheafFiber X (fiberMk f) F z) := by
          rw [hx]
    _ = (fiber.{max u v w} (D.obj b).T).toPresheafFiber X
          ((refinementFiber (D.hom hab).k (D.obj b).T (D.hom hab).hT).app X (fiberMk f)) F z := by
          simpa using
            congrFun
              (NatTrans.toPresheafFiber_presheafFiber_app
                (η := refinementFiber (D.hom hab).k (D.obj b).T (D.hom hab).hT)
                (F := F) X (fiberMk f)) z
    _ = (fiber.{max u v w} (D.obj b).T).toPresheafFiber X
          ((refinementFiber (D.hom hab).k (D.obj b).T (D.hom hab).hT).app X (fiberMk f)) F z' :=
          hstage_eq
    _ = ((refinementFiber (D.hom hab).k (D.obj b).T (D.hom hab).hT).presheafFiber).app F
          ((fiber.{max u v w} (D.obj a).T).toPresheafFiber X (fiberMk f) F z') := by
          symm
          simpa using
            congrFun
              (NatTrans.toPresheafFiber_presheafFiber_app
                (η := refinementFiber (D.hom hab).k (D.obj b).T (D.hom hab).hT)
                (F := F) X (fiberMk f)) z'
    _ = ((refinementFiber (D.hom hab).k (D.obj b).T (D.hom hab).hT).presheafFiber).app F y := by
          rw [hy]

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the separation condition needed to
package the natural quotient colimit as a refinement stage. -/
abbrev limitStageSeparated (a0 : δ) : Prop :=
  ((refinementFiber (D.limitOriginalEmbedding a0) D.system (D.limitOriginalIso a0)).presheafFiber).app
      ((sheafToPresheaf J (Type (max u v w))).obj ℱ) s ≠
    ((refinementFiber (D.limitOriginalEmbedding a0) D.system (D.limitOriginalIso a0)).presheafFiber).app
      ((sheafToPresheaf J (Type (max u v w))).obj ℱ) s'

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: solved requests on the natural quotient
limit are exactly the transports of requests solved at some diagram stage. -/
def limitSolved : Set (finite_cover_lift_request J D.system) :=
  {r | ∃ (a : δ) (r0 : finite_cover_lift_request J (D.obj a).T),
      r0 ∈ (D.obj a).solved ∧
        transport_request (J := J) (D.colimitInclusion a) D.system
          (D.colimitInclusionIso a) r0 = r}

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: every request marked solved on the
natural quotient limit is realized there. -/
theorem limitSolved_realized ⦃r : finite_cover_lift_request J D.system⦄
    (hr : r ∈ D.limitSolved) : request_realized (J := J) r := by
  -- Unpack the stage where the request was already solved and transport its realization into the
  -- natural quotient-limit system.
  rcases hr with ⟨a, r0, hr0, rfl⟩
  exact request_realized_transport (J := J) (D.colimitInclusion a) D.system
    (D.colimitInclusionIso a) r0 ((D.obj a).solved_realized hr0)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the natural quotient colimit, once its
separation condition is supplied, is a packaged refinement stage. -/
noncomputable def limitStage (a0 : δ) (hsep : D.limitStageSeparated a0) :
    refinement_stage (J := J) S' (ℱ := ℱ) s s' where
  I := D.ColimitIndex
  instPreorder := inferInstance
  instDirected := D.colimitIndex_directed
  T := D.system
  j := D.limitOriginalEmbedding a0
  e := D.limitOriginalIso a0
  separated := hsep
  solved := D.limitSolved
  solved_realized := D.limitSolved_realized

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a diagram-stage solved request remains
marked solved after transporting it to the natural quotient-limit stage. -/
theorem stageHomToLimit_solved_mono (a0 : δ) (hsep : D.limitStageSeparated a0) (a : δ) :
    ∀ ⦃r : finite_cover_lift_request J (D.obj a).T⦄, r ∈ (D.obj a).solved →
      transport_request (J := J) (D.colimitInclusion a) (D.limitStage a0 hsep).T
          (D.colimitInclusionIso a) r ∈ (D.limitStage a0 hsep).solved := by
  -- The limit-stage solved set was defined precisely as the image of solved requests from all
  -- diagram stages.
  intro r hr
  exact ⟨a, r, hr, rfl⟩

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the canonical morphism from a diagram
stage into the natural quotient-limit stage. -/
noncomputable def stageHomToLimit (a0 : δ) (hsep : D.limitStageSeparated a0) (a : δ) :
    refinement_stage_hom (J := J) (D.obj a) (D.limitStage a0 hsep) where
  k := D.colimitInclusion a
  hT := D.colimitInclusionIso a
  solved_mono := D.stageHomToLimit_solved_mono a0 hsep a

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: casting a natural isomorphism along an equality of its target
functor leaves each hom component heterogeneously unchanged. -/
theorem natIsoCastTarget_hom_app_heq {K : Type w} [Category K] {F G₁ G₂ : K ⥤ C}
    (hG : G₁ = G₂) (e : F ≅ G₁) (X : K) :
    HEq ((cast (congrArg (fun G => F ≅ G) hG) e).hom.app X) (e.hom.app X) := by
  -- Eliminating the target-functor equality reduces the cast to the identity cast.
  cases hG
  rfl

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the forward component of the
quotient-colimit inclusion isomorphism is compatible with first moving along a diagram
transition and then applying the later stage's inclusion isomorphism. -/
theorem colimitInclusionIsoHomApp_comp_heq {a b : δ} (hab : a ≤ b)
    (i : (D.obj a).I) :
    HEq (D.colimitInclusionIsoHomApp a i)
      ((D.hom hab).hT.hom.app (Opposite.op i) ≫
        D.colimitInclusionIsoHomApp b ((D.hom hab).k i)) := by
  -- Normalize both sides to a transition from the source raw point to the same quotient
  -- representative of the later stage.
  let j : (D.obj b).I := (D.hom hab).k i
  let rawA : D.Raw := ⟨a, i⟩
  let rawB : D.Raw := ⟨b, j⟩
  let outA : D.Raw := (D.colimitι a i).out
  let outB : D.Raw := (D.colimitι b j).out
  let d : δ := D.outColimitStage b j
  let hb : b ≤ d := D.outColimitStage_source_le b j
  let hOutB : outB.1 ≤ d := D.outColimitStage_out_le b j
  let hA : a ≤ d := le_trans hab hb
  have hrefl : (D.hom (show b ≤ b from le_rfl)).k j = (D.hom hab).k i := by
    dsimp [j]
    rw [D.homk_refl b]
  have hrawEq : (D.hom hb).k j = (D.hom hA).k i := by
    dsimp [j, hA]
    rw [D.homk_comp hab hb]
  have hhomBase :
      (D.hom hab).hT.hom.app (Opposite.op i) =
        D.transMapAt rawB rawA (le_rfl : b ≤ b) hab (le_of_eq hrefl) := by
    -- Read the diagram transition's structure isomorphism as a `transMapAt` computed at `b`.
    unfold transMapAt
    generalize le_of_eq hrefl = hle
    revert hle
    rw [D.hom_refl b]
    intro hle
    simp [refinement_stage_hom_refl, identity_refinement_iso, Functor.leftUnitor, rawA, rawB, j]
    exact (Category.comp_id ((D.hom hab).hT.hom.app (Opposite.op i))).symm
  have hhom :
      (D.hom hab).hT.hom.app (Opposite.op i) =
        D.transMapAt rawB rawA hb hA (le_of_eq hrawEq) := by
    -- Move that transition computation from stage `b` to the common later stage `d`.
    rw [hhomBase]
    exact D.transMapAt_eq_of_common rawB rawA (le_rfl : b ≤ b) hab
      (le_of_eq hrefl) hb hA (le_of_eq hrawEq)
  have hOutRaw : (D.hom hOutB).k outB.2 = (D.hom hb).k j := by
    dsimp [outB, d, hb, hOutB, j]
    exact D.outColimitStage_image_eq b ((D.hom hab).k i)
  have hOutA : (D.hom hOutB).k outB.2 = (D.hom hA).k i := by
    rw [hOutRaw, hrawEq]
  have hcomp := D.transMapAt_compose outB rawB rawA hOutB hb hA
    (le_of_eq hOutRaw) (le_of_eq hrawEq) (le_of_eq hOutA)
  have hright :
      (D.hom hab).hT.hom.app (Opposite.op i) ≫ D.colimitInclusionIsoHomApp b j =
        D.transMapAt outB rawA hOutB hA (le_of_eq hOutA) := by
    -- Compose the stage transition with the later inclusion map and collapse the two transports.
    rw [hhom]
    dsimp [colimitInclusionIsoHomApp, outB, rawB, rawA, d, hOutB, hb, hA, j]
    exact hcomp
  have hout : outA = outB := by
    dsimp [outA, outB, j]
    exact congrArg Quotient.out (D.colimitι_natural hab i)
  let hOutAtoD : outA.1 ≤ d := by
    rw [hout]
    exact hOutB
  have hOutAeq : (D.hom hOutAtoD).k outA.2 = (D.hom hA).k i := by
    exact D.colimitRel_out_colimitι_image_eq a i hOutAtoD hA
  have hleftAtOutA :
      D.colimitInclusionIsoHomApp a i =
        D.transMapAt outA rawA hOutAtoD hA (le_of_eq hOutAeq) := by
    -- Recompute the earlier stage's inclusion component at the same later stage `d`.
    rw [colimitInclusionIsoHomApp]
    exact D.transMapAt_eq_of_common outA rawA
      (D.outColimitStage_out_le a i) (D.outColimitStage_source_le a i)
      (le_of_eq (D.outColimitStage_image_eq a i)) hOutAtoD hA (le_of_eq hOutAeq)
  have hmove :
      HEq (D.transMapAt outA rawA hOutAtoD hA (le_of_eq hOutAeq))
        (D.transMapAt outB rawA hOutB hA (le_of_eq hOutA)) := by
    -- Transport the common-stage computation across the equality of quotient representatives.
    have hgeneric : ∀ (x : D.Raw) (hx : outA = x) (hxle : x.1 ≤ d)
        (hxeq : (D.hom hxle).k x.2 = (D.hom hA).k i),
        HEq (D.transMapAt outA rawA hOutAtoD hA (le_of_eq hOutAeq))
          (D.transMapAt x rawA hxle hA (le_of_eq hxeq)) := by
      intro x hx hxle hxeq
      cases hx
      apply heq_of_eq
      exact D.transMapAt_eq_of_common outA rawA hOutAtoD hA (le_of_eq hOutAeq)
        hxle hA (le_of_eq hxeq)
    exact hgeneric outB hout hOutB hOutA
  have hleft :
      HEq (D.colimitInclusionIsoHomApp a i)
        (D.transMapAt outB rawA hOutB hA (le_of_eq hOutA)) :=
    (heq_of_eq hleftAtOutA).trans hmove
  exact hleft.trans (heq_of_eq hright.symm)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the natural quotient-colimit
identification of stage `a` agrees heterogeneously with first transitioning to a later stage `b`
and then using the quotient-colimit identification of `b`. -/
theorem colimitInclusionIso_comp_heq {a b : δ} (hab : a ≤ b) :
    HEq (D.colimitInclusionIso a)
      (compose_refinement_iso (D.hom hab).k (D.colimitInclusion b) (D.hom hab).hT
        (D.colimitInclusionIso b)) := by
  -- Align the dependent target functor by the strict equality of the two quotient inclusions,
  -- then prove the resulting `Eq` of NatIsos componentwise.
  have hk : D.colimitInclusion a =
      compose_refinement_embedding (D.hom hab).k (D.colimitInclusion b) :=
    (D.colimitInclusion_comp hab).symm
  have hG :
      ((D.colimitInclusion a).toOrderHom.toFunctor).op ⋙ D.system =
        ((compose_refinement_embedding (D.hom hab).k
            (D.colimitInclusion b)).toOrderHom.toFunctor).op ⋙ D.system :=
    congrArg (fun k : (D.obj a).I ↪o D.ColimitIndex =>
      (k.toOrderHom.toFunctor).op ⋙ D.system) hk
  have hcast :
      cast (congrArg (fun G => (D.obj a).T ≅ G) hG) (D.colimitInclusionIso a) =
        compose_refinement_iso (D.hom hab).k (D.colimitInclusion b) (D.hom hab).hT
          (D.colimitInclusionIso b) := by
    -- NatIso extensionality reduces the casted equality to the hom-component compatibility just
    -- proved above.
    ext X
    apply eq_of_heq
    have hcastHom :
        HEq
          ((cast (congrArg (fun G => (D.obj a).T ≅ G) hG)
            (D.colimitInclusionIso a)).hom.app X)
          ((D.colimitInclusionIso a).hom.app X) :=
      natIsoCastTarget_hom_app_heq hG (D.colimitInclusionIso a) X
    have hleft :
        HEq ((D.colimitInclusionIso a).hom.app X)
          (D.colimitInclusionIsoHomApp a (Opposite.unop X)) := by
      -- Unfold the component of the quotient-colimit NatIso to its named construction.
      rfl
    have hhom := D.colimitInclusionIsoHomApp_comp_heq hab (Opposite.unop X)
    let m :
        (D.obj a).T.obj X ⟶
          D.system.obj
            (Opposite.op ((D.colimitInclusion b) ((D.hom hab).k (Opposite.unop X)))) :=
      (D.hom hab).hT.hom.app X ≫
        D.colimitInclusionIsoHomApp b ((D.hom hab).k (Opposite.unop X))
    have hid :
        HEq
          ((D.hom hab).hT.hom.app X ≫
            D.colimitInclusionIsoHomApp b ((D.hom hab).k (Opposite.unop X)))
          (((D.hom hab).hT.hom.app X ≫
              D.colimitInclusionIsoHomApp b ((D.hom hab).k (Opposite.unop X))) ≫
              𝟙 (D.system.obj
                (Opposite.op ((D.colimitInclusion b) ((D.hom hab).k (Opposite.unop X)))))) := by
      apply heq_of_eq
      exact (Category.comp_id m).symm
    have hright :
        HEq
          (((D.hom hab).hT.hom.app X ≫
              D.colimitInclusionIsoHomApp b ((D.hom hab).k (Opposite.unop X))) ≫
            𝟙 (D.system.obj
              (Opposite.op ((D.colimitInclusion b) ((D.hom hab).k (Opposite.unop X))))))
          ((compose_refinement_iso (D.hom hab).k (D.colimitInclusion b) (D.hom hab).hT
            (D.colimitInclusionIso b)).hom.app X) := by
      -- The right component is the hom component of the composed refinement isomorphism.
      apply heq_of_eq
      simp [compose_refinement_iso, colimitInclusionIso, colimitInclusionIsoApp]
      calc
        (D.hom hab).hT.hom.app X ≫
            D.colimitInclusionIsoHomApp b ((D.hom hab).k (Opposite.unop X)) =
            ((D.hom hab).hT.hom.app X ≫
              D.colimitInclusionIsoHomApp b ((D.hom hab).k (Opposite.unop X))) ≫
                𝟙 (D.system.obj
                  (Opposite.op ((D.colimitInclusion b) ((D.hom hab).k (Opposite.unop X))))) := by
          simpa only [m] using (Category.comp_id m).symm
        _ = (D.hom hab).hT.hom.app X ≫
            D.colimitInclusionIsoHomApp b ((D.hom hab).k (Opposite.unop X)) ≫
              𝟙 (D.system.obj
                (Opposite.op ((D.colimitInclusion b) ((D.hom hab).k (Opposite.unop X))))) := by
          rw [Category.assoc]
    exact hcastHom.trans (hleft.trans (hhom.trans (hid.trans hright)))
  exact (cast_heq (congrArg (fun G => (D.obj a).T ≅ G) hG)
    (D.colimitInclusionIso a)).symm.trans (heq_of_eq hcast)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: compatible original data keeps the two original sections separated
after passing to the natural quotient-colimit stage. -/
theorem limitStageSeparated_of_compatible
    (hcompat : ∀ ⦃a b : δ⦄ (hab : a ≤ b), (D.hom hab).original_compatible)
    (a0 : δ) : D.limitStageSeparated a0 := by
  -- Factor the quotient-limit original fiber map through the base stage and its canonical
  -- inclusion into the quotient system.
  let Fobj : Cᵒᵖ ⥤ Type (max u v w) :=
    (sheafToPresheaf J (Type (max u v w))).obj ℱ
  let x := ((refinementFiber (D.obj a0).j (D.obj a0).T (D.obj a0).e).presheafFiber).app
    Fobj s
  let y := ((refinementFiber (D.obj a0).j (D.obj a0).T (D.obj a0).e).presheafFiber).app
    Fobj s'
  intro hlim
  have hfactor :
      ((refinementFiber (D.limitOriginalEmbedding a0) D.system
        (D.limitOriginalIso a0)).presheafFiber).app Fobj =
      ((refinementFiber (D.obj a0).j (D.obj a0).T (D.obj a0).e).presheafFiber).app Fobj ≫
        ((refinementFiber (D.colimitInclusion a0) D.system
          (D.colimitInclusionIso a0)).presheafFiber).app Fobj :=
    D.limitOriginal_presheafFiber_app a0 Fobj
  have hxy :
      ((refinementFiber (D.colimitInclusion a0) D.system
        (D.colimitInclusionIso a0)).presheafFiber).app Fobj x =
      ((refinementFiber (D.colimitInclusion a0) D.system
        (D.colimitInclusionIso a0)).presheafFiber).app Fobj y := by
    calc
      ((refinementFiber (D.colimitInclusion a0) D.system
        (D.colimitInclusionIso a0)).presheafFiber).app Fobj x =
          (((refinementFiber (D.obj a0).j (D.obj a0).T (D.obj a0).e).presheafFiber).app Fobj ≫
            ((refinementFiber (D.colimitInclusion a0) D.system
              (D.colimitInclusionIso a0)).presheafFiber).app Fobj) s := by
            rfl
      _ = ((refinementFiber (D.limitOriginalEmbedding a0) D.system
              (D.limitOriginalIso a0)).presheafFiber).app Fobj s := by
            rw [← hfactor]
      _ = ((refinementFiber (D.limitOriginalEmbedding a0) D.system
              (D.limitOriginalIso a0)).presheafFiber).app Fobj s' := hlim
      _ = (((refinementFiber (D.obj a0).j (D.obj a0).T (D.obj a0).e).presheafFiber).app Fobj ≫
            ((refinementFiber (D.colimitInclusion a0) D.system
              (D.colimitInclusionIso a0)).presheafFiber).app Fobj) s' := by
            rw [hfactor]
      _ = ((refinementFiber (D.colimitInclusion a0) D.system
          (D.colimitInclusionIso a0)).presheafFiber).app Fobj y := by
            rfl
  -- Reflect the quotient-colimit equality to a later diagram stage, then contradict that stage's
  -- separation after factoring its original map through `a0 ≤ b`.
  rcases D.colimitInclusion_presheafFiber_eq_of_eq a0 Fobj hxy with ⟨b, hb, hbxy⟩
  have hstage :
      ((refinementFiber (D.obj b).j (D.obj b).T (D.obj b).e).presheafFiber).app Fobj =
        ((refinementFiber (D.obj a0).j (D.obj a0).T (D.obj a0).e).presheafFiber).app Fobj ≫
          ((refinementFiber (D.hom hb).k (D.obj b).T (D.hom hb).hT).presheafFiber).app Fobj :=
    refinement_stage_hom.original_compatible_presheafFiber_app
      (J := J) (D.hom hb) (hcompat hb) Fobj
  have hstage_eq :
      ((refinementFiber (D.obj b).j (D.obj b).T (D.obj b).e).presheafFiber).app Fobj s =
        ((refinementFiber (D.obj b).j (D.obj b).T (D.obj b).e).presheafFiber).app Fobj s' := by
    rw [hstage]
    simpa [x, y] using hbxy
  exact (D.obj b).separated hstage_eq

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the canonical maps from diagram stages into the natural
quotient-limit stage form a strict cone over the diagram. -/
theorem stageHomToLimit_comp (a0 : δ) (hsep : D.limitStageSeparated a0)
    {a b : δ} (hab : a ≤ b) :
    D.stageHomToLimit a0 hsep a =
      refinement_stage_hom.comp (J := J) (D.hom hab) (D.stageHomToLimit a0 hsep b) := by
  -- The order-embedding field is exactly quotient-colimit naturality.  The sole remaining
  -- transport obligation is the matching HEq between the two inclusion isomorphism normal forms.
  apply refinementStageHom_eq_of_k_hT
  · exact (D.colimitInclusion_comp hab).symm
  · -- The naturality of the quotient-colimit inclusion identifies the inverse-system isomorphism
    -- field of the one-step cone map with the composed field.
    exact D.colimitInclusionIso_comp_heq hab

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the original embedding of the natural quotient-limit stage agrees
with the original embedding of any diagram stage followed by its limit map. -/
theorem stageHomToLimit_originalEmbedding_eq
    (hcompat : ∀ ⦃a b : δ⦄ (hab : a ≤ b), (D.hom hab).original_compatible)
    (a0 : δ) (hsep : D.limitStageSeparated a0) (a : δ) :
    (D.limitStage a0 hsep).j =
      compose_refinement_embedding (D.obj a).j (D.stageHomToLimit a0 hsep a).k := by
  -- Compare the base stage and the chosen source stage inside a common later diagram stage, then
  -- rewrite both composites into the quotient-colimit index.
  obtain ⟨b, ha0b, hab⟩ := directed_of (· ≤ ·) a0 a
  exact D.originalEmbedding_colimitInclusion_eq_of_common ha0b hab hcompat

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the base stage's canonical map into the natural quotient-limit
stage is compatible with the original refinement data. -/
theorem stageHomToLimit_base_original_compatible
    (a0 : δ) (hsep : D.limitStageSeparated a0) :
    (D.stageHomToLimit a0 hsep a0).original_compatible := by
  -- For the base stage used to define the limit's original data, both compatibility fields are
  -- the definitional projections of `limitStage`.
  constructor
  · ext i
    rfl
  · exact HEq.rfl

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: after a compatible diagram transition,
the original-system isomorphism transported to the quotient colimit agrees with the later stage's
original-system isomorphism transported to the same quotient colimit. -/
theorem limitOriginalIso_heq_of_le
    (hcompat : ∀ ⦃a b : δ⦄ (hab : a ≤ b), (D.hom hab).original_compatible)
    {a b : δ} (hab : a ≤ b) :
    HEq (D.limitOriginalIso a)
      (compose_refinement_iso (D.obj b).j (D.colimitInclusion b) (D.obj b).e
        (D.colimitInclusionIso b)) := by
  -- Package the quotient-inclusion data as a dependent pair, so the embedding equality carries
  -- the NatIso component without ad hoc casts.
  let Ψ :
      (Σ k : (D.obj a).I ↪o D.ColimitIndex,
        (D.obj a).T ≅ (k.toOrderHom.toFunctor).op ⋙ D.system) →
        (Σ j : ι ↪o D.ColimitIndex,
          S' ≅ (j.toOrderHom.toFunctor).op ⋙ D.system) :=
    fun p => ⟨compose_refinement_embedding (D.obj a).j p.1,
      compose_refinement_iso (D.obj a).j p.1 (D.obj a).e p.2⟩
  have hcolimPair :
      (⟨D.colimitInclusion a, D.colimitInclusionIso a⟩ :
        Σ k : (D.obj a).I ↪o D.ColimitIndex,
          (D.obj a).T ≅ (k.toOrderHom.toFunctor).op ⋙ D.system) =
      ⟨compose_refinement_embedding (D.hom hab).k (D.colimitInclusion b),
        compose_refinement_iso (D.hom hab).k (D.colimitInclusion b) (D.hom hab).hT
          (D.colimitInclusionIso b)⟩ := by
    exact Sigma.ext (D.colimitInclusion_comp hab).symm (D.colimitInclusionIso_comp_heq hab)
  have hlimitPair :
      (⟨D.limitOriginalEmbedding a, D.limitOriginalIso a⟩ :
        Σ j : ι ↪o D.ColimitIndex,
          S' ≅ (j.toOrderHom.toFunctor).op ⋙ D.system) =
      ⟨compose_refinement_embedding (D.obj a).j
          (compose_refinement_embedding (D.hom hab).k (D.colimitInclusion b)),
        compose_refinement_iso (D.obj a).j
          (compose_refinement_embedding (D.hom hab).k (D.colimitInclusion b)) (D.obj a).e
          (compose_refinement_iso (D.hom hab).k (D.colimitInclusion b) (D.hom hab).hT
            (D.colimitInclusionIso b))⟩ := by
    simpa [Ψ, limitOriginalEmbedding, limitOriginalIso] using congrArg Ψ hcolimPair
  rcases hcompat hab with ⟨hj, he⟩
  -- Push the stage-level compatibility pair forward along the later stage's quotient inclusion.
  let Φ :
      (Σ j : ι ↪o (D.obj b).I,
        S' ≅ (j.toOrderHom.toFunctor).op ⋙ (D.obj b).T) →
        (Σ j : ι ↪o D.ColimitIndex,
          S' ≅ (j.toOrderHom.toFunctor).op ⋙ D.system) :=
    fun p => ⟨compose_refinement_embedding p.1 (D.colimitInclusion b),
      compose_refinement_iso p.1 (D.colimitInclusion b) p.2 (D.colimitInclusionIso b)⟩
  have hstagePair :
      (⟨(D.obj b).j, (D.obj b).e⟩ :
        Σ j : ι ↪o (D.obj b).I,
          S' ≅ (j.toOrderHom.toFunctor).op ⋙ (D.obj b).T) =
      ⟨compose_refinement_embedding (D.obj a).j (D.hom hab).k,
        compose_refinement_iso (D.obj a).j (D.hom hab).k (D.obj a).e (D.hom hab).hT⟩ := by
    exact Sigma.ext hj he
  have hstep :
      (⟨compose_refinement_embedding (D.obj b).j (D.colimitInclusion b),
        compose_refinement_iso (D.obj b).j (D.colimitInclusion b) (D.obj b).e
          (D.colimitInclusionIso b)⟩ :
        Σ j : ι ↪o D.ColimitIndex,
          S' ≅ (j.toOrderHom.toFunctor).op ⋙ D.system) =
      ⟨compose_refinement_embedding
          (compose_refinement_embedding (D.obj a).j (D.hom hab).k) (D.colimitInclusion b),
        compose_refinement_iso
          (compose_refinement_embedding (D.obj a).j (D.hom hab).k) (D.colimitInclusion b)
          (compose_refinement_iso (D.obj a).j (D.hom hab).k (D.obj a).e (D.hom hab).hT)
          (D.colimitInclusionIso b)⟩ := by
    simpa [Φ] using congrArg Φ hstagePair
  have hassoc :
      (⟨compose_refinement_embedding
          (compose_refinement_embedding (D.obj a).j (D.hom hab).k) (D.colimitInclusion b),
        compose_refinement_iso
          (compose_refinement_embedding (D.obj a).j (D.hom hab).k) (D.colimitInclusion b)
          (compose_refinement_iso (D.obj a).j (D.hom hab).k (D.obj a).e (D.hom hab).hT)
          (D.colimitInclusionIso b)⟩ :
        Σ j : ι ↪o D.ColimitIndex,
          S' ≅ (j.toOrderHom.toFunctor).op ⋙ D.system) =
      ⟨compose_refinement_embedding (D.obj a).j
          (compose_refinement_embedding (D.hom hab).k (D.colimitInclusion b)),
        compose_refinement_iso (D.obj a).j
          (compose_refinement_embedding (D.hom hab).k (D.colimitInclusion b)) (D.obj a).e
          (compose_refinement_iso (D.hom hab).k (D.colimitInclusion b) (D.hom hab).hT
            (D.colimitInclusionIso b))⟩ := by
    -- The only remaining difference is associativity of refinement embeddings and their
    -- corresponding refinement isomorphisms.
    apply Sigma.ext
    · ext i
      rfl
    · apply heq_of_eq
      ext X
      simp [compose_refinement_iso, compose_refinement_embedding, Functor.associator]
  have hpair :
      (⟨D.limitOriginalEmbedding a, D.limitOriginalIso a⟩ :
        Σ j : ι ↪o D.ColimitIndex,
          S' ≅ (j.toOrderHom.toFunctor).op ⋙ D.system) =
      ⟨compose_refinement_embedding (D.obj b).j (D.colimitInclusion b),
        compose_refinement_iso (D.obj b).j (D.colimitInclusion b) (D.obj b).e
          (D.colimitInclusionIso b)⟩ :=
    hlimitPair.trans (hassoc.symm.trans hstep.symm)
  -- Project the NatIso component of the dependent-pair equality.
  exact ((Sigma.mk.inj_iff).1 hpair).2

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the original-system isomorphism of the
natural quotient-limit stage is heterogeneously the original-system isomorphism of any diagram
stage followed by its canonical map into the quotient limit. -/
theorem stageHomToLimit_originalIso_heq
    (hcompat : ∀ ⦃a b : δ⦄ (hab : a ≤ b), (D.hom hab).original_compatible)
    (a0 : δ) (hsep : D.limitStageSeparated a0) (a : δ) :
    HEq (D.limitStage a0 hsep).e
      (compose_refinement_iso (D.obj a).j (D.stageHomToLimit a0 hsep a).k
        (D.obj a).e (D.stageHomToLimit a0 hsep a).hT) := by
  -- Compare both original-system isomorphisms after moving them to a common later diagram stage.
  obtain ⟨b, ha0b, hab⟩ := directed_of (· ≤ ·) a0 a
  have hleft := D.limitOriginalIso_heq_of_le hcompat ha0b
  have hright := D.limitOriginalIso_heq_of_le hcompat hab
  -- The right-hand side is definitionally the limit-original iso based at `a`.
  simpa [limitStage, stageHomToLimit, limitOriginalIso] using hleft.trans hright.symm

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: every canonical map into the natural quotient-limit stage is
compatible with the original refinement data. -/
theorem stageHomToLimit_original_compatible
    (hcompat : ∀ ⦃a b : δ⦄ (hab : a ≤ b), (D.hom hab).original_compatible)
    (a0 : δ) (hsep : D.limitStageSeparated a0) (a : δ) :
    (D.stageHomToLimit a0 hsep a).original_compatible := by
  -- The embedding component is already the common-stage comparison of original embeddings; the
  -- remaining iso component is the same quotient-inclusion composition HEq needed by the strict
  -- cone law above.
  constructor
  · exact D.stageHomToLimit_originalEmbedding_eq hcompat a0 hsep a
  · -- The NatIso component is exactly the named original-data coherence through the quotient
    -- inclusion.
    exact D.stageHomToLimit_originalIso_heq hcompat a0 hsep a

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: an abstract strict limit cone for a natural directed union diagram
of packaged refinement stages.  The quotient-index construction is expected to supply this data;
downstream scheduled-prefix proofs only use the strict cone laws packaged here. -/
structure StrictLimitCone where
  top : refinement_stage (J := J) S' (ℱ := ℱ) s s'
  toLimit : ∀ a : δ, refinement_stage_hom (J := J) (D.obj a) top
  toLimit_comp :
    ∀ ⦃a b : δ⦄ (hab : a ≤ b),
      toLimit a = refinement_stage_hom.comp (J := J) (D.hom hab) (toLimit b)
  toLimit_original_compatible : ∀ a : δ, (toLimit a).original_compatible

omit [IsDirected δ (· ≤ ·)] in
  /-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a strict limit cone comparison may be read in the rewrite-friendly
  orientation from a transition followed by the later cone leg to the earlier cone leg. -/
  theorem StrictLimitCone.comp_toLimit (K : D.StrictLimitCone) {a b : δ} (hab : a ≤ b) :
      refinement_stage_hom.comp (J := J) (D.hom hab) (K.toLimit b) = K.toLimit a := by
    -- This is just the symmetric form of the strict cone law, exposed as a stable rewrite lemma.
    exact (K.toLimit_comp hab).symm

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: compatible directed natural diagrams have the strict limit-cone
interface consumed by the scheduled-prefix limit step. -/
theorem existsStrictLimitCone [Nonempty δ]
    (hcompat : ∀ ⦃a b : δ⦄ (hab : a ≤ b), (D.hom hab).original_compatible) :
    Nonempty D.StrictLimitCone := by
  -- Assemble the strict cone from the quotient-colimit refinement stage; the only nontrivial
  -- field of that stage is the named separation-reflection lemma above.
  classical
  let a0 : δ := Classical.choice inferInstance
  let hsep : D.limitStageSeparated a0 := D.limitStageSeparated_of_compatible hcompat a0
  exact ⟨{
    top := D.limitStage a0 hsep
    toLimit := D.stageHomToLimit a0 hsep
    toLimit_comp := fun {a b} hab => D.stageHomToLimit_comp a0 hsep hab
    toLimit_original_compatible := fun a =>
      D.stageHomToLimit_original_compatible hcompat a0 hsep a
  }⟩

end DiagramData

end NaturalDiagramUnion

end CategoryTheory
