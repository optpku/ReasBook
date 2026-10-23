module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Presheaf
public import stacks_project.Chap07.Lemma_7_22_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe w

/- Domain-style sampling for Example 7.21.4:
- primary domain: open maps of topological spaces, the induced adjunction on categories of opens,
  and the corresponding direct-image functors on sheaves of sets;
- sampled owner API:
  `IsOpenMap.adjunction`,
  `IsOpenMap.coverPreserving`,
  `Adjunction.isCocontinuous_iff_coverPreserving`,
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`;
- source/core/bridge triage:
  `source-facing`: the open-map specialization comparing the direct image coming from
  `hf.functor : Opens X ⥤ Opens Y` with the usual sheaf pushforward along `f`;
  `core/canonical`: the opens adjunction `hf.functor ⊣ Opens.map f` and the Chapter 7 comparison
  owner for a continuous right adjoint;
  `bridge/view`: the specialization below from those owners to the open-map setting.

Primitive data are only the map `f` and the proof `hf : IsOpenMap f`. The cocontinuity of
`hf.functor` and the comparison with `TopCat.Sheaf.pushforward` are derived from the canonical
owners above, so this file should expose only the thin specialization layer rather than a parallel
local construction.
-/

namespace IsOpenMap

variable {X Y : TopCat.{w}} {f : X ⟶ Y}

/-- An open map induces a cocontinuous functor on the categories of opens. -/
instance functor_isCocontinuous (hf : IsOpenMap f) :
    hf.functor.IsCocontinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  (Adjunction.isCocontinuous_iff_coverPreserving
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) hf.adjunction).2
    (coverPreserving_opens_map f)

/-- Example 7.21.4: for an open map `f : X ⟶ Y`, the direct-image functor on sheaves of sets
arising from the cocontinuous functor `U ↦ f(U)` agrees with the usual sheaf pushforward along
`f`. -/
-- Proof sketch: use the adjunction `hf.functor ⊣ Opens.map f` on opens, identify cocontinuity of
-- `hf.functor` via the cover-preserving property of `Opens.map f`, and then compare the resulting
-- right Kan extension description of the cocontinuous pushforward with the standard pushforward by
-- precomposition along `Opens.map f`.
noncomputable def cocontinuousPushforwardIsoSheafPushforward (hf : IsOpenMap f) :
    hf.functor.sheafPushforwardCocontinuous (Type w)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) ≅
        TopCat.Sheaf.pushforward (Type w) f :=
  (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
      hf.functor (Opens.map f) (Type w) hf.adjunction).symm

-- Proof sketch: unfold the definition and observe that the only extra input is the canonical
-- cocontinuity instance `functor_isCocontinuous hf`, so the comparison isomorphism is exactly the
-- specialization of the Chapter 7 continuous-right-adjoint owner theorem.
/-- The open-map comparison isomorphism is the specialization of the continuous-right-adjoint
comparison theorem to the adjunction `hf.functor ⊣ Opens.map f`. -/
theorem cocontinuousPushforwardIsoSheafPushforward_def (hf : IsOpenMap f) :
    cocontinuousPushforwardIsoSheafPushforward hf =
      (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
        hf.functor (Opens.map f) (Type w) hf.adjunction).symm := by
  -- The specialization was defined to be exactly this symmetric owner isomorphism.
  rfl

-- Proof sketch: this is the `hom_inv_id` identity for the comparison isomorphism defined above.
/-- The forward map of `cocontinuousPushforwardIsoSheafPushforward` followed by its inverse is the
identity. -/
@[simp] theorem cocontinuousPushforwardIsoSheafPushforward_hom_inv_id (hf : IsOpenMap f) :
    (cocontinuousPushforwardIsoSheafPushforward hf).hom ≫
        (cocontinuousPushforwardIsoSheafPushforward hf).inv =
      𝟙 _ := by
  -- This is the standard `hom_inv_id` identity for the comparison isomorphism.
  exact (cocontinuousPushforwardIsoSheafPushforward hf).hom_inv_id

end IsOpenMap
