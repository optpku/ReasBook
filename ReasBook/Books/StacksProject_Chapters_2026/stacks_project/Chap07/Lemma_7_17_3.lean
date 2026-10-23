module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_17_1
public import stacks_project.Chap07.Definition_7_17_4
public import stacks_project.Chap07.Lemma_7_12_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open Opposite
open CategoryTheory.SemiRepresentableFamily.Over

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology

open scoped SheafifiedRepresentable

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/-
Source/core/bridge triage for 7.17.3:
- source-facing predicate on the site side: `J.QuasiCompactObject U`
- core/canonical predicate on the sheaf side: `Sheaf.IsQuasiCompactObject`
- bridge/view object: `J.sheafifiedRepresentable U`
-/
-- Proof sketch: for `(1) → (2)`, turn a locally surjective coproduct map to `h_U^#` into a
-- covering family over `U` and then refine it to finitely many summands. For `(2) → (1)`, start
-- from a covering family of `U`, use the canonical locally surjective cover map
-- `J.sheafifiedRepresentableCoverMap`, apply the owner field
-- `Sheaf.IsQuasiCompactObject.finite_subcoproduct`, and convert the resulting finite locally
-- surjective coproduct map of sheafified representables back to a covering sieve on `U`.

/-- Helper for Lemma 7.17.3: a morphism from a sheafified representable into a coproduct of
sheaves locally factors through a single summand. -/
lemma locally_factor_coproduct_morphism_through_single_summand
    {ι : Type (max u v)} {V : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (β : h[V]^#[J] ⟶ ∐ ℱᵢ) :
    ∃ R : J.Cover V, ∀ r : R.Arrow, ∃ i : ι, ∃ τ : h[r.Y]^#[J] ⟶ ℱᵢ i,
      J.sheafifiedRepresentableMap r.f ≫ β = τ ≫ Limits.Sigma.ι ℱᵢ i := by
  classical
  let F : Discrete ι ⥤ Sheaf J (Type (max u v)) := Discrete.functor ℱᵢ
  let E : Cocone (F ⋙ sheafToPresheaf J (Type (max u v))) := colimit.cocone _
  let hE : IsColimit E := colimit.isColimit _
  let hS := Sheaf.isColimitSheafifyCocone (J := J) (D := Type (max u v)) E hE
  let e : ((presheafToSheaf J (Type (max u v))).obj E.pt) ≅ ∐ ℱᵢ := by
    simpa [Sheaf.sheafifyCocone] using hS.coconePointUniqueUpToIso (colimit.isColimit F)
  let η : E.pt ⟶ ((presheafToSheaf J (Type (max u v))).obj E.pt).obj :=
    (sheafificationAdjunction J (Type (max u v))).unit.app E.pt
  let xV : (∐ ℱᵢ).obj.obj (op V) := J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) V β
  let zV : ((presheafToSheaf J (Type (max u v))).obj E.pt).obj.obj (op V) :=
    e.inv.hom.app (op V) xV
  let R : J.Cover V := ⟨Presheaf.imageSieve η zV, Presheaf.imageSieve_mem J η zV⟩
  refine ⟨R, ?_⟩
  intro r
  let tr : E.pt.obj (op r.Y) := Presheaf.localPreimage η zV r.f r.hf
  have htr :
      η.app (op r.Y) tr =
        ((presheafToSheaf J (Type (max u v))).obj E.pt).obj.map r.f.op zV := by
    -- The chosen local preimage in the presheaf coproduct maps to the restricted section.
    simpa [η, tr] using Presheaf.app_localPreimage η zV r.f r.hf
  let ev := (evaluation Cᵒᵖ (Type (max u v))).obj (op r.Y)
  have hcol : IsColimit (ev.mapCocone E) := by
    -- Evaluate the presheaf coproduct cocone at `r.Y` so joint surjectivity is pointwise.
    exact isColimitOfPreserves ev hE
  obtain ⟨j, y, hjy⟩ := Types.jointly_surjective_of_isColimit hcol tr
  let i : ι := j.as
  let τ : h[r.Y]^#[J] ⟶ ℱᵢ i :=
    (J.uliftSheafifiedRepresentableHomEquiv (ℱᵢ i) r.Y).symm y
  refine ⟨i, τ, ?_⟩
  apply (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) r.Y).injective
  have hβ :
      (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) r.Y)
          (J.sheafifiedRepresentableMap r.f ≫ β) =
        (∐ ℱᵢ).obj.map r.f.op xV := by
    -- Restrict the original section of the coproduct along `r.f`.
    simpa [xV] using J.uliftSheafifiedRepresentableHomEquiv_naturality r.f (∐ ℱᵢ) β
  have hτ0 := J.uliftSheafifiedRepresentableHomEquiv_comp τ (Limits.Sigma.ι ℱᵢ i)
  have hy : (J.uliftSheafifiedRepresentableHomEquiv (ℱᵢ i) r.Y) τ = y := by
    exact Equiv.apply_symm_apply (J.uliftSheafifiedRepresentableHomEquiv (ℱᵢ i) r.Y) y
  have hτ :
      (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) r.Y)
          (τ ≫ Limits.Sigma.ι ℱᵢ i) =
        (Limits.Sigma.ι ℱᵢ i).hom.app (op r.Y) y := by
    -- The chosen point of the `i`-th summand induces the expected coproduct section.
    simpa [hy] using hτ0
  rw [hβ, hτ]
  have hzV : e.hom.hom.app (op V) zV = xV := by
    change e.hom.hom.app (op V) (e.inv.hom.app (op V) xV) = xV
    exact congrArg (fun f => f.hom.app (op V) xV) e.inv_hom_id
  have hright :
      e.hom.hom.app (op r.Y) (η.app (op r.Y) tr) =
        (∐ ℱᵢ).obj.map r.f.op xV := by
    rw [htr]
    -- After applying the colimit isomorphism, the chosen presheaf lift becomes the
    -- restriction of the original coproduct section.
    simpa [ConcreteCategory.comp_apply, hzV] using
      congrArg (fun f => f zV) (e.hom.hom.naturality r.f.op)
  have hη : η = CategoryTheory.toSheafify J E.pt := by
    simpa [η] using
      (CategoryTheory.sheafificationAdjunction_unit_app
        (J := J) (D := Type (max u v)) (P := E.pt))
  have hηtr :
      η.app (op r.Y) tr =
        ((Sheaf.sheafifyCocone E).ι.app j).hom.app (op r.Y) y := by
    rw [← hjy]
    have hι' : E.ι.app j ≫ η = ((Sheaf.sheafifyCocone E).ι.app j).hom := by
      rw [hη]
      simpa using
        (Sheaf.sheafifyCocone_ι_app_val (J := J) (D := Type (max u v)) E j).symm
    -- Rewrite the chosen pointwise lift through the sheafified coproduct cocone.
    exact congrArg (fun f => f.app (op r.Y) y) hι'
  have hcomp :
      (Sheaf.sheafifyCocone E).ι.app j ≫
          (by simpa [Sheaf.sheafifyCocone] using e.hom) =
        Limits.Sigma.ι ℱᵢ i := by
    -- The colimit isomorphism identifies the sheafified presheaf coproduct injections with the
    -- actual coproduct injections in `Sheaf`.
    simpa [i] using hS.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) j
  have hleft :
      e.hom.hom.app (op r.Y) (η.app (op r.Y) tr) =
        (Limits.Sigma.ι ℱᵢ i).hom.app (op r.Y) y := by
    rw [hηtr]
    exact congrArg (fun f => f.hom.app (op r.Y) y) hcomp
  exact hright.symm.trans hleft

/-- Helper for Lemma 7.17.3: downward closure for the sieve of arrows whose map to `h[U]^#`
factors through one summand of a fixed coproduct map. -/
lemma single_summand_factor_sieve_downward_closed
    {ι : Type (max u v)} {U Y Z : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (π : (∐ ℱᵢ) ⟶ h[U]^#[J]) {f : Y ⟶ U}
    (hf : ∃ i : ι, ∃ τ : h[Y]^#[J] ⟶ ℱᵢ i,
      τ ≫ Limits.Sigma.ι ℱᵢ i ≫ π = J.sheafifiedRepresentableMap f)
    (g : Z ⟶ Y) :
    ∃ i : ι, ∃ τ : h[Z]^#[J] ⟶ ℱᵢ i,
      τ ≫ Limits.Sigma.ι ℱᵢ i ≫ π = J.sheafifiedRepresentableMap (g ≫ f) := by
  rcases hf with ⟨i, τ, hτ⟩
  refine ⟨i, J.sheafifiedRepresentableMap g ≫ τ, ?_⟩
  -- Precompose the chosen factorization along `g`.
  simpa [Category.assoc, sheafifiedRepresentableMap, sheafifiedRepresentableFunctor,
    uliftSheafifiedRepresentableFunctor] using congrArg (fun k => J.sheafifiedRepresentableMap g ≫ k) hτ

/-- Helper for Lemma 7.17.3: the arrows into `U` whose map to `h[U]^#` factors through a single
summand of `π` form a sieve. -/
def singleSummandFactorSieve
    {ι : Type (max u v)} {U : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (π : (∐ ℱᵢ) ⟶ h[U]^#[J]) : Sieve U where
  arrows Y f :=
    ∃ i : ι, ∃ τ : h[Y]^#[J] ⟶ ℱᵢ i,
      τ ≫ Limits.Sigma.ι ℱᵢ i ≫ π = J.sheafifiedRepresentableMap f
  downward_closed := single_summand_factor_sieve_downward_closed (J := J) ℱᵢ π

/-- Helper for Lemma 7.17.3: a locally surjective coproduct map to `h[U]^#` yields a covering
sieve of arrows whose corresponding sheafified-representable maps already factor through one
summand. -/
lemma exists_coproduct_lift_of_image_sieve_mem_identity
    {ι : Type (max u v)} {U Y : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (π : (∐ ℱᵢ) ⟶ h[U]^#[J]) {f : Y ⟶ U}
    (hf :
      Presheaf.imageSieve π.hom
        (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))) f) :
    ∃ β : h[Y]^#[J] ⟶ ∐ ℱᵢ, β ≫ π = J.sheafifiedRepresentableMap f := by
  let xU : (h[U]^#[J]).obj.obj (op U) :=
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))
  let t : (∐ ℱᵢ).obj.obj (op Y) := Presheaf.localPreimage π.hom xU f hf
  let β : h[Y]^#[J] ⟶ ∐ ℱᵢ := (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) Y).symm t
  refine ⟨β, ?_⟩
  apply (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) Y).injective
  -- Compare both morphisms by the section of `h[U]^#` over `Y` they correspond to.
  calc
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) Y (β ≫ π) =
        π.hom.app (op Y) ((J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) Y) β) := by
          simpa using J.uliftSheafifiedRepresentableHomEquiv_comp β π
    _ = π.hom.app (op Y) t := by
      have hβt : (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) Y) β = t := by
        simpa [β, t] using
          (Equiv.apply_symm_apply (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) Y) t)
      exact congrArg (π.hom.app (op Y)) hβt
    _ = (h[U]^#[J]).obj.map f.op xU := by
      simpa [t] using Presheaf.app_localPreimage π.hom xU f hf
    _ = J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) Y
        (J.sheafifiedRepresentableMap f) := by
          simpa [xU, sheafifiedRepresentableMap] using
            (J.uliftSheafifiedRepresentableHomEquiv_naturality
              f (h[U]^#[J]) (𝟙 (h[U]^#[J]))).symm

/-- Helper for Lemma 7.17.3: once a local lift of `h[f] : h[Y]^# ⟶ h[U]^#` to the coproduct is
given, the pullback of the single-summand sieve along `f` is covering. -/
lemma pullback_singleSummandFactorSieve_mem_of_lift
    {ι : Type (max u v)} {U Y : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (π : (∐ ℱᵢ) ⟶ h[U]^#[J]) {f : Y ⟶ U} (β : h[Y]^#[J] ⟶ ∐ ℱᵢ)
    (hβ : β ≫ π = J.sheafifiedRepresentableMap f) :
    Sieve.pullback f (singleSummandFactorSieve (J := J) ℱᵢ π) ∈ J Y := by
  obtain ⟨R, hR⟩ := locally_factor_coproduct_morphism_through_single_summand
    (J := J) ℱᵢ β
  have hle : R.1 ≤ Sieve.pullback f (singleSummandFactorSieve (J := J) ℱᵢ π) := by
    intro Z g hg
    rcases hR ⟨Z, g, hg⟩ with ⟨i, τ, hτ⟩
    refine ⟨i, τ, ?_⟩
    -- Compose the local single-summand factorization with `π` and use the lift identity.
    calc
      τ ≫ Limits.Sigma.ι ℱᵢ i ≫ π = J.sheafifiedRepresentableMap g ≫ β ≫ π := by
        simpa [Category.assoc] using congrArg (fun k => k ≫ π) hτ.symm
      _ = J.sheafifiedRepresentableMap g ≫ J.sheafifiedRepresentableMap f := by
        simpa [Category.assoc] using congrArg (fun k => J.sheafifiedRepresentableMap g ≫ k) hβ
      _ = J.sheafifiedRepresentableMap (g ≫ f) := by
        simp [sheafifiedRepresentableMap, sheafifiedRepresentableFunctor,
          uliftSheafifiedRepresentableFunctor]
  -- The cover produced by local factorization refines the pullback sieve.
  exact J.superset_covering hle R.2

/-- Helper for Lemma 7.17.3: a locally surjective coproduct map to `h[U]^#` yields a covering
sieve of arrows whose corresponding sheafified-representable maps already factor through one
summand. -/
lemma singleSummandFactorSieve_mem
    {ι : Type (max u v)} {U : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (π : (∐ ℱᵢ) ⟶ h[U]^#[J]) (hπ : Sheaf.IsLocallySurjective π) :
    singleSummandFactorSieve (J := J) ℱᵢ π ∈ J U := by
  letI : Sheaf.IsLocallySurjective π := hπ
  let xU : (h[U]^#[J]).obj.obj (op U) :=
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))
  let S : Sieve U := Presheaf.imageSieve π.hom xU
  have hS : S ∈ J U := by
    -- Local surjectivity covers the identity section of `h[U]^#`.
    simpa [S, xU] using Presheaf.imageSieve_mem J π.hom xU
  -- Route correction: first cover the identity section, then refine each local lift to one
  -- summand and conclude by a single transitivity step.
  refine J.transitive hS (singleSummandFactorSieve (J := J) ℱᵢ π) ?_
  intro Y f hf
  obtain ⟨β, hβ⟩ := exists_coproduct_lift_of_image_sieve_mem_identity
    (J := J) ℱᵢ π (f := f) (by simpa [S, xU] using hf)
  -- Each arrow of the image sieve has a local lift, and that lift locally factors through one
  -- summand of the coproduct.
  exact pullback_singleSummandFactorSieve_mem_of_lift (J := J) ℱᵢ π β hβ

/-- Lemma 7.17.3: an object `U` of a site `(C, J)` is quasi-compact if and only if the sheafified
representable `h_U^#` is a quasi-compact object of the topos `Sh(C, J)`. -/
theorem quasiCompactObject_iff_isQuasiCompactObject_sheafifiedRepresentable
    (U : C) :
    J.QuasiCompactObject U ↔ (h[U]^#[J]).IsQuasiCompactObject := by
  constructor
  · intro hU
    refine ⟨?_⟩
    intro ι ℱᵢ _ π hπ
    classical
    let _ : HasColimitsOfShape (Discrete ι) (Type (max u v)) := inferInstance
    let hSingle : singleSummandFactorSieve (J := J) ℱᵢ π ∈ J U :=
      singleSummandFactorSieve_mem (J := J) ℱᵢ π hπ
    let S : J.Cover U := ⟨singleSummandFactorSieve (J := J) ℱᵢ π, hSingle⟩
    obtain ⟨T, hT, hTcover⟩ := hU S
    let κ : T → ι := fun t ↦ Classical.choose t.1.hf
    let τ : ∀ t : T, h[t.1.Y]^#[J] ⟶ ℱᵢ (κ t) :=
      fun t ↦ Classical.choose (Classical.choose_spec t.1.hf)
    have hτ :
        ∀ t : T, τ t ≫ Limits.Sigma.ι ℱᵢ (κ t) ≫ π = J.sheafifiedRepresentableMap t.1.f := by
      intro t
      exact Classical.choose_spec (Classical.choose_spec t.1.hf)
    let K : Set ι := Set.range κ
    have hK : K.Finite := by
      let _ : Fintype T := hT.fintype
      simpa [K, κ] using Set.finite_range κ
    refine ⟨K, hK, ?_⟩
    let _ : HasColimitsOfShape (Discrete T) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete T) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    let _ : HasColimitsOfShape (Discrete K) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete K) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    let σ : ∐ (fun t : T ↦ h[t.1.Y]^#[J]) ⟶ ∐ (fun k : K ↦ ℱᵢ k.1) :=
      Limits.Sigma.desc
        (fun t : T ↦
          τ t ≫ Limits.Sigma.ι (fun k : K ↦ ℱᵢ k.1) ⟨κ t, ⟨t, rfl⟩⟩)
    let μ : ∐ (fun k : K ↦ ℱᵢ k.1) ⟶ h[U]^#[J] :=
      Limits.Sigma.desc (fun k : K ↦ Limits.Sigma.ι ℱᵢ k.1 ≫ π)
    have hfac :
        Limits.Sigma.desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f) = σ ≫ μ := by
      -- The finite cover map factors through the finite subcoproduct indexed by the labels.
      apply Limits.Sigma.hom_ext
      intro t
      have hμ :
          Limits.Sigma.ι (fun k : K ↦ ℱᵢ k.1) ⟨κ t, ⟨t, rfl⟩⟩ ≫ μ =
            Limits.Sigma.ι ℱᵢ (κ t) ≫ π := by
        exact Limits.Sigma.ι_desc (fun k : K ↦ Limits.Sigma.ι ℱᵢ k.1 ≫ π) ⟨κ t, ⟨t, rfl⟩⟩
      calc
        Limits.Sigma.ι (fun t : T ↦ h[t.1.Y]^#[J]) t ≫
            Limits.Sigma.desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f) =
          J.sheafifiedRepresentableMap t.1.f := by
            exact Limits.Sigma.ι_desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f) t
        _ = τ t ≫ Limits.Sigma.ι ℱᵢ (κ t) ≫ π := (hτ t).symm
        _ = τ t ≫ Limits.Sigma.ι (fun k : K ↦ ℱᵢ k.1) ⟨κ t, ⟨t, rfl⟩⟩ ≫ μ := by
          simpa [Category.assoc] using congrArg (fun k => τ t ≫ k) hμ.symm
        _ = Limits.Sigma.ι (fun t : T ↦ h[t.1.Y]^#[J]) t ≫ σ ≫ μ := by
          have hσ :
              Limits.Sigma.ι (fun t : T ↦ h[t.1.Y]^#[J]) t ≫ σ =
                τ t ≫ Limits.Sigma.ι (fun k : K ↦ ℱᵢ k.1) ⟨κ t, ⟨t, rfl⟩⟩ := by
            exact
              Limits.Sigma.ι_desc
                (fun t : T ↦
                  τ t ≫ Limits.Sigma.ι (fun k : K ↦ ℱᵢ k.1) ⟨κ t, ⟨t, rfl⟩⟩) t
          simpa [Category.assoc] using congrArg (fun k => k ≫ μ) hσ.symm
    have hpres :
        Presheaf.IsLocallySurjective J
          (Limits.Sigma.desc
            (fun t : T ↦ CategoryTheory.uliftYoneda.{max u v}.map t.1.f)) := by
      exact
        (J.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
          (fun t : T ↦ t.1.f)).1 hTcover
    have hsheaf :
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f)) := by
      exact
        (J.isLocallySurjective_sigmaDesc_sheafifiedRepresentableMap_iff
          (fun t : T ↦ t.1.Y) (fun t ↦ t.1.f)).2 hpres
    letI :
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f)) := hsheaf
    have hfac_hom :
        σ.hom ≫ μ.hom = (Limits.Sigma.desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f)).hom :=
      congrArg (fun f => f.hom) hfac.symm
    -- Local surjectivity descends across the factorization through the finite subcoproduct.
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac_hom
  · intro hU
    intro S
    let π : ∐ (fun I : S.Arrow ↦ h[I.Y]^#[J]) ⟶ h[U]^#[J] := J.sheafifiedRepresentableCoverMap S
    have hπ : Sheaf.IsLocallySurjective π := by
      simpa [π] using sheafifiedRepresentableCoverMap_isLocallySurjective (J := J) S
    obtain ⟨T, hT, hTsurj⟩ := hU.finite_subcoproduct (fun I : S.Arrow ↦ h[I.Y]^#[J]) π hπ
    refine ⟨T, hT, ?_⟩
    let _ : HasColimitsOfShape (Discrete T) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete T) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    have hfac :
        (Limits.Sigma.desc
          (fun i : T ↦ Limits.Sigma.ι (fun I : S.Arrow ↦ h[I.Y]^#[J]) i.1 ≫ π)) =
          Limits.Sigma.desc (fun I : T ↦ J.sheafifiedRepresentableMap I.1.f) := by
      -- Identify the finite subcoproduct map coming from `finite_subcoproduct` with the usual
      -- sigma-desc map built from the chosen finite family of arrows.
      apply Limits.Sigma.hom_ext
      intro I
      have h1 :
          Limits.Sigma.ι (fun I : S.Arrow ↦ h[I.Y]^#[J]) I.1 ≫ π =
            J.sheafifiedRepresentableMap I.1.f := by
        simpa [π, sheafifiedRepresentableCoverMap] using
          (Limits.Sigma.ι_desc
            (f := fun I : S.Arrow ↦ h[I.Y]^#[J])
            (p := fun I : S.Arrow ↦ J.sheafifiedRepresentableMap I.f)
            (b := I.1))
      have h2 :
          Limits.Sigma.ι (fun I : T ↦ h[I.1.Y]^#[J]) I ≫
              Limits.Sigma.desc (fun I : T ↦ J.sheafifiedRepresentableMap I.1.f) =
            J.sheafifiedRepresentableMap I.1.f := by
        exact
          Limits.Sigma.ι_desc
            (f := fun I : T ↦ h[I.1.Y]^#[J])
            (p := fun I : T ↦ J.sheafifiedRepresentableMap I.1.f)
            (b := I)
      rw [Limits.Sigma.ι_desc]
      exact h1.trans h2.symm
    have hTsurj' :
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc (fun I : T ↦ J.sheafifiedRepresentableMap I.1.f)) := by
      simpa [hfac] using hTsurj
    have hpres :
        Presheaf.IsLocallySurjective J
          (Limits.Sigma.desc (fun I : T ↦ CategoryTheory.uliftYoneda.{max u v}.map I.1.f)) := by
      exact
        (J.isLocallySurjective_sigmaDesc_sheafifiedRepresentableMap_iff
          (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f)).1 hTsurj'
    change Sieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f) ∈ J U
    exact
      (J.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
        (fun I : T ↦ I.1.f)).2 hpres

end CategoryTheory.GrothendieckTopology
