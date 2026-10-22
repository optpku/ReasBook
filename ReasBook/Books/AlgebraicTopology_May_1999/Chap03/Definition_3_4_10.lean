/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_2
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

namespace CategoryTheory.Functor

variable {B : Type u} [Groupoid.{v} B]

/-- Definition 3.4.10: a functor `T : B ⥤ Type v` is transitive if, for every object `b : B`, the
source-facing vertex group `π(B,b)` acts transitively on the fiber `T.obj b`. -/
def IsTransitive (T : B ⥤ Type v) : Prop :=
  ∀ b : B,
    letI := vertexGroupAction T b
    MulAction.IsTransitive (b ⟶ b) (T.obj b)

noncomputable section

/-- Helper for Definition 3.4.10: the source-facing transitivity condition at a fixed object. -/
private abbrev VertexGroupActionTransitive (T : B ⥤ Type v) (b : B) : Prop :=
  letI := vertexGroupAction T b
  MulAction.IsTransitive (b ⟶ b) (T.obj b)

/-- Helper for Definition 3.4.10: the `End`-based transitivity condition at a fixed object. -/
private abbrev VertexGroupMulActionTransitive (T : B ⥤ Type v) (b : B) : Prop :=
  letI := vertexGroupMulAction T b
  MulAction.IsTransitive (End b) (T.obj b)

/-- Helper for Definition 3.4.10: an equivariant equivalence of acting groups and fibers carries a
transitive action to a transitive action. -/
private theorem isTransitive_of_equivariant_equiv
    {H : Type*} [Group H] {K : Type*} [Group K]
    {X : Type*} [MulAction H X] {Y : Type*} [MulAction K Y]
    (eH : H ≃* K) (eX : X ≃ Y)
    (hcompat : ∀ g x, eX (g • x) = eH g • eX x)
    (h : MulAction.IsTransitive H X) :
    MulAction.IsTransitive K Y := by
  rcases h with ⟨hX, hpre⟩
  let f : X →ₑ[eH] Y :=
    { toFun := eX
      map_smul' := hcompat }
  have hf : Function.Bijective f := eX.bijective
  -- Move the nonemptiness and orbit condition across the equivariant bijection.
  refine ⟨hX.map eX, ?_⟩
  exact (MulAction.isPretransitive_congr eH.surjective hf).mp hpre

/-- Helper for Definition 3.4.10: a witness for the inverse-loop action produces a witness for the
direct `End`-action by inverting the loop. -/
private theorem vertexGroupMulAction_exists_of_vertexGroupAction_exists
    (T : B ⥤ Type v) (b : B) (x y : T.obj b)
    (h : ∃ g : b ⟶ b, letI := vertexGroupAction T b; g • x = y) :
    ∃ g : End b, letI := vertexGroupMulAction T b; g • x = y := by
  rcases h with ⟨g, hg⟩
  refine ⟨((g⁻¹ : b ⟶ b) : End b), ?_⟩
  letI := vertexGroupAction T b
  letI := vertexGroupMulAction T b
  -- Rewrite the source-facing action through `T.map` and transport the inverse through `T`.
  have hg' : CategoryTheory.inv (T.map g) x = y := by
    simpa [vertexGroupAction_smul_eq_map_inv] using hg
  rw [vertexGroupMulAction_smul_eq_map]
  calc
    T.map (((g⁻¹ : b ⟶ b) : End b)) x = CategoryTheory.inv (T.map g) x := by
      simpa using congrArg (fun f : T.obj b ⟶ T.obj b => f x) (Functor.map_inv T g)
    _ = y := hg'

/-- Helper for Definition 3.4.10: a witness for the direct `End`-action produces a witness for the
source-facing inverse-loop action by inverting the endomorphism. -/
private theorem vertexGroupAction_exists_of_vertexGroupMulAction_exists
    (T : B ⥤ Type v) (b : B) (x y : T.obj b)
    (h : ∃ g : End b, letI := vertexGroupMulAction T b; g • x = y) :
    ∃ g : b ⟶ b, letI := vertexGroupAction T b; g • x = y := by
  rcases h with ⟨g, hg⟩
  refine ⟨(((g⁻¹ : End b) : b ⟶ b)), ?_⟩
  letI := vertexGroupAction T b
  letI := vertexGroupMulAction T b
  -- After inverting the `End`-witness, the source action reduces to the same `T.map g`.
  have hg' : T.map g x = y := by
    simpa [vertexGroupMulAction_smul_eq_map] using hg
  rw [vertexGroupAction_smul_eq_map_inv]
  calc
    T.map (g⁻¹⁻¹) x = CategoryTheory.inv (T.map g⁻¹) x := by
      simpa using congrArg (fun f : T.obj b ⟶ T.obj b => f x) (Functor.map_inv T (g⁻¹))
    _ = T.map g x := by
      symm
      simpa using congrArg (fun f : T.obj b ⟶ T.obj b => f x) (Functor.map_inv T (g⁻¹))
    _ = y := hg'

/-- Helper for Definition 3.4.10: at a fixed object, the source-facing loop action and the
auxiliary `End`-action have the same transitivity condition. -/
theorem vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive
    (T : B ⥤ Type v) (b : B) :
    VertexGroupActionTransitive T b ↔ VertexGroupMulActionTransitive T b := by
  constructor
  · intro h
    letI := vertexGroupAction T b
    letI := vertexGroupMulAction T b
    change MulAction.IsTransitive (b ⟶ b) (T.obj b) at h
    change MulAction.IsTransitive (End b) (T.obj b)
    rw [MulAction.isTransitive_iff_nonempty_pretransitive] at h
    rcases h with ⟨hx, hpre⟩
    refine ⟨hx, ?_⟩
    obtain ⟨x₀⟩ := hx
    -- Use a chosen basepoint in the fiber and translate the orbit witnesses.
    rw [MulAction.isPretransitive_iff_base x₀] at hpre ⊢
    intro y
    exact vertexGroupMulAction_exists_of_vertexGroupAction_exists T b x₀ y (hpre y)
  · intro h
    letI := vertexGroupAction T b
    letI := vertexGroupMulAction T b
    change MulAction.IsTransitive (End b) (T.obj b) at h
    change MulAction.IsTransitive (b ⟶ b) (T.obj b)
    rw [MulAction.isTransitive_iff_nonempty_pretransitive] at h
    rcases h with ⟨hx, hpre⟩
    refine ⟨hx, ?_⟩
    obtain ⟨x₀⟩ := hx
    -- Translate orbit witnesses back by inverting the chosen endomorphism.
    rw [MulAction.isPretransitive_iff_base x₀] at hpre ⊢
    intro y
    exact vertexGroupAction_exists_of_vertexGroupMulAction_exists T b x₀ y (hpre y)

/-- Helper for Definition 3.4.10: an isomorphism of objects transports transitivity of the
`End`-based vertex-group action between the two fibers. -/
theorem vertexGroupMulAction_isTransitive_iff_of_iso
    (T : B ⥤ Type v) {b b' : B} (i : b ≅ b') :
    VertexGroupMulActionTransitive T b ↔ VertexGroupMulActionTransitive T b' := by
  letI := vertexGroupMulAction T b
  letI := vertexGroupMulAction T b'
  constructor
  · intro h
    change MulAction.IsTransitive (End b') (T.obj b')
    -- Transport both loops and points along the isomorphism `i`.
    exact isTransitive_of_equivariant_equiv i.conj (T.mapIso i).toEquiv
      (fun g x ↦ by
        change
          T.map i.hom (T.map g x) =
            T.map (i.inv ≫ g ≫ i.hom) (T.map i.hom x)
        have hi : T.map i.inv (T.map i.hom x) = x := by
          rw [← T.map_comp_apply]
          simp
        rw [T.map_comp_apply, T.map_comp_apply]
        rw [hi])
      h
  · intro h
    change MulAction.IsTransitive (End b) (T.obj b)
    -- Apply the same transport argument to the inverse isomorphism.
    exact isTransitive_of_equivariant_equiv i.symm.conj (T.mapIso i.symm).toEquiv
      (fun g x ↦ by
        change
          T.map i.inv (T.map g x) =
            T.map (i.hom ≫ g ≫ i.inv) (T.map i.inv x)
        have hi : T.map i.hom (T.map i.inv x) = x := by
          rw [← T.map_comp_apply]
          simp
        rw [T.map_comp_apply, T.map_comp_apply]
        rw [hi])
      h

/-- Helper for Definition 3.4.10: in a connected groupoid, transitivity of the `End`-action at one
object propagates to every object. -/
theorem forall_vertexGroupMulAction_isTransitive_of_isConnected [CategoryTheory.IsConnected B]
    (T : B ⥤ Type v) (b₀ : B) :
    VertexGroupMulActionTransitive T b₀ →
    ∀ b : B,
      letI := vertexGroupMulAction T b
      MulAction.IsTransitive (End b) (T.obj b) := by
  intro hb₀ b
  classical
  -- Connectedness supplies a morphism from `b₀` to `b`, hence an isomorphism in the groupoid.
  let f : b₀ ⟶ b := Classical.choice (CategoryTheory.nonempty_hom_of_preconnected_groupoid b₀ b)
  let i : b₀ ≅ b := (Groupoid.isoEquivHom _ _).symm f
  exact (vertexGroupMulAction_isTransitive_iff_of_iso T i).mp hb₀

/-- The source-facing transitivity condition is equivalent to the same condition phrased through
the auxiliary `End`-based action `vertexGroupMulAction`. -/
theorem isTransitive_iff_forall_vertexGroupMulAction_isTransitive (T : B ⥤ Type v) :
    IsTransitive T ↔
      ∀ b : B,
        letI := vertexGroupMulAction T b
        MulAction.IsTransitive (End b) (T.obj b) := by
  constructor
  · intro hT b
    -- Rewrite the defining pointwise condition through the `End`-action bridge.
    exact (vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive T b).mp (hT b)
  · intro hT b
    -- Rewrite back objectwise to recover the original source-facing condition.
    exact (vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive T b).mpr (hT b)

/-- For a connected groupoid, transitivity of a functor can be checked at a single object via the
canonical vertex-group action on that fiber. -/
-- Proof sketch: use connectedness to choose a zigzag, hence an isomorphism in the groupoid,
-- from the chosen base object `b₀` to any `b`; transport points and the orbit condition along
-- `T.map` of that isomorphism to transfer transitivity between the two fibers.
theorem isTransitive_iff_at_object [CategoryTheory.IsConnected B]
    (T : B ⥤ Type v) (b₀ : B) :
    IsTransitive T ↔
      letI := vertexGroupAction T b₀
      MulAction.IsTransitive (b₀ ⟶ b₀) (T.obj b₀) := by
  constructor
  · intro hT
    -- Specialize the global transitivity condition to `b₀` after rewriting via `End b₀`.
    have hAll :
        ∀ b : B,
          letI := vertexGroupMulAction T b
          MulAction.IsTransitive (End b) (T.obj b) :=
      (isTransitive_iff_forall_vertexGroupMulAction_isTransitive T).mp hT
    exact (vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive T b₀).mpr
      (hAll b₀)
  · intro hb₀
    -- Convert the base-object hypothesis to the `End`-action and propagate it by connectedness.
    have hb₀' :
        letI := vertexGroupMulAction T b₀
        MulAction.IsTransitive (End b₀) (T.obj b₀) :=
      (vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive T b₀).mp hb₀
    have hAll :
        ∀ b : B,
          letI := vertexGroupMulAction T b
          MulAction.IsTransitive (End b) (T.obj b) :=
      forall_vertexGroupMulAction_isTransitive_of_isConnected T b₀ hb₀'
    exact (isTransitive_iff_forall_vertexGroupMulAction_isTransitive T).mpr hAll

end

end CategoryTheory.Functor
