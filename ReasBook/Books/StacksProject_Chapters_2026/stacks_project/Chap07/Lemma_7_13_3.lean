module

public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe t u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]
variable [∀ (ℱ : Cᵒᵖ ⥤ Type t), u.op.HasLeftKanExtension ℱ]
variable [HasWeakSheafify K (Type t)]

/- Domain-style sampling for Lemma 7.13.3:
- primary domain: inverse-image/direct-image adjunctions for continuous functors of sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPullbackConstruction.sheafPullback`,
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionContinuous`;
- source/core/bridge triage:
  `source-facing`: the sheafified left Kan extension `(u_p -)^#`;
  `core/canonical`: the constructed adjunction owner
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`;
  `bridge/view`: the abstract adjunction owner `Functor.sheafAdjunctionContinuous`,
  compared via `Functor.sheafPullbackConstruction.sheafPullbackIso`.

The primitive data are continuity, left Kan extensions, and weak sheafification; the adjunction is
derived API and should be recalled directly from the owner theorem. -/
/- Lemma 7.13.3: in the situation of Lemma 7.13.2, the functor sending a sheaf `\mathcal G` on
`(\mathcal C, J)` to the sheafification `(u_p \mathcal G)^\#` on `(\mathcal D, K)` is left
adjoint to the inverse-image functor `u^s` on sheaves. -/
recall Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

end
