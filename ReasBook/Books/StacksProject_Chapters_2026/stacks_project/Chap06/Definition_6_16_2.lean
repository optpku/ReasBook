module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.Topology.Sheaves.Forget
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

universe u v

section

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : TopCat.{u}}

/- Domain-style sampling for Definition 6.16.2:
- primary domain: subpresheaves, subsheaves, and injective/surjective morphism criteria for
  set-valued presheaves and sheaves on a topological space;
- inspected owner declarations:
  `CategoryTheory.Subfunctor`,
  `TopCat.Presheaf.IsSheaf`,
  `TopCat.Presheaf.IsLocallySurjective`,
  `CategoryTheory.Sheaf.isLocallyInjective_iff_injective`,
  `TopCat.Presheaf.isLocallySurjective_iff`.
- best owner abstraction: `CategoryTheory.Subfunctor` for subpresheaves, `TopCat.Presheaf.IsSheaf`
  for the subsheaf condition, `TopCat.Presheaf.IsLocallySurjective` for surjective morphisms of
  sheaves, and the categorical predicates `Mono` and `Epi` together with
  `Sheaf.IsLocallyInjective` / `Presheaf.IsLocallySurjective` for the morphism criteria;
- primitive data: a subfunctor or a morphism of presheaves/sheaves;
- derived API: objectwise injectivity/surjectivity on sections and the local-preimage condition.

Source/core/bridge triage:
- `source-facing`: the Stacks Project notions of subpresheaf, subsheaf, injective morphism, and
  surjective morphism;
- `core/canonical`: `CategoryTheory.Subfunctor`, `TopCat.Presheaf.IsSheaf`, and the categorical
  owner predicates `Mono`, `Epi`, and `TopCat.Presheaf.IsLocallySurjective`;
- `bridge/view`: the specialized sectionwise criteria below, obtained from the general owner
  theorems `NatTrans.mono_iff_mono_app`, `NatTrans.epi_iff_epi_app`,
  `CategoryTheory.mono_iff_injective`, `CategoryTheory.epi_iff_surjective`, and
  `TopCat.Presheaf.isLocallySurjective_iff`. -/

/- Definition 6.16.2: a subpresheaf of a presheaf of sets on a topological space is the canonical
mathlib structure `CategoryTheory.Subfunctor`; the companion declarations below record the
injective and surjective morphism clauses for presheaves and sheaves. -/
recall CategoryTheory.Subfunctor

/- Definition 6.16.2, subsheaf clause: for a subpresheaf `𝒢` of a sheaf of sets on `X`, the
textbook condition of being a subsheaf is exactly the canonical sheaf condition
`TopCat.Presheaf.IsSheaf 𝒢.toFunctor`. -/
recall TopCat.Presheaf.IsSheaf

/-- Definition 6.16.2, presheaf injectivity clause: a morphism of set-valued presheaves on `X`
is a monomorphism exactly when every map on sections is injective. -/
theorem presheaf_mono_iff_app_injective {ℱ 𝒢 : X.Presheaf (Type v)} (φ : ℱ ⟶ 𝒢) :
    Mono φ ↔ ∀ U : Opens X, Function.Injective (φ.app (op U)) := by
  constructor
  · intro hφ U
    exact (CategoryTheory.mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app φ).1 hφ (op U))
  · intro hφ
    exact (NatTrans.mono_iff_mono_app φ).2 fun U ↦
      (CategoryTheory.mono_iff_injective _).2 (hφ U.unop)

/-- Definition 6.16.2, presheaf surjectivity clause: a morphism of set-valued presheaves on `X`
is an epimorphism exactly when every map on sections is surjective. -/
theorem presheaf_epi_iff_app_surjective {ℱ 𝒢 : X.Presheaf (Type v)} (φ : ℱ ⟶ 𝒢) :
    Epi φ ↔ ∀ U : Opens X, Function.Surjective (φ.app (op U)) := by
  constructor
  · intro hφ U
    exact (CategoryTheory.epi_iff_surjective _).1
      ((NatTrans.epi_iff_epi_app φ).1 hφ (op U))
  · intro hφ
    exact (NatTrans.epi_iff_epi_app φ).2 fun U ↦
      (CategoryTheory.epi_iff_surjective _).2 (hφ U.unop)

/-- A morphism of sheaves of sets is injective exactly when each map on sections is injective. -/
theorem sheaf_mono_iff_app_injective {ℱ 𝒢 : X.Sheaf (Type v)} (φ : ℱ ⟶ 𝒢) :
    Mono φ ↔ ∀ U : Opens X, Function.Injective (φ.hom.app (op U)) := by
  rw [← Functor.mono_map_iff_mono (TopCat.Sheaf.forget (Type v) X) φ]
  simpa using presheaf_mono_iff_app_injective ((TopCat.Sheaf.forget (Type v) X).map φ)

/- Definition 6.16.2, surjective morphism clause: for a morphism of sheaves of sets on `X`, the
canonical owner for the textbook local-preimage notion of surjectivity is the predicate
`TopCat.Presheaf.IsLocallySurjective` on the underlying presheaf map. -/
recall TopCat.Presheaf.IsLocallySurjective

/- The same surjectivity notion is expressed in textbook local-section form by the companion
bridge theorem `TopCat.Presheaf.isLocallySurjective_iff`. -/
recall TopCat.Presheaf.isLocallySurjective_iff

end
