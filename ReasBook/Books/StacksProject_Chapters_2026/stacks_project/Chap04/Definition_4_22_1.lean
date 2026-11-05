module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.IsLimit

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open Opposite

universe uI vI uC vC uD vD

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

/- Domain-style sampling for Definition 4.22.1:
- primary domain: filtered/cofiltered diagrams, their cocones/cones, and canonical split
  section/retraction data on distinguished legs.
- inspected owner-level declarations:
  `CategoryTheory.SplitEpi`,
  `CategoryTheory.SplitMono`,
  `CategoryTheory.Limits.Cocone`,
  `CategoryTheory.Limits.Cone`.
- best owner abstraction:
  `source-facing`: the essentially constant cocone/cone predicates of this file;
  `core/canonical`: `SplitEpi` and `SplitMono` on the distinguished cocone/cone legs;
  `bridge/view`: passage between filtered cocones and cofiltered cones by `op`/`unop`.

Primitive-vs-derived split:
- primitive data: a chosen leg together with its split structure (`SplitEpi` for cocones, dually
  `SplitMono` for cones), plus the eventual factorization condition on all other legs.
- derived API: the raw textbook section/retraction formulas obtained by unpacking that split
  structure, the functoriality under `mapCocone` and `mapCone`, the universal-property owners
  `isColimit` and `isLimit`, and the cofiltered view transported through `op`. -/

/- Source/core/bridge triage for Definition 4.22.1:
- `source-facing`: the filtered-cocone notion and its textbook section/factorization unpacking.
- `core/canonical`: the use of `SplitEpi` on a cocone leg.
- `bridge/view`: the cofiltered-cone notion, obtained by applying the filtered owner to the
  opposite cone.
-/

/-- Definition 4.22.1 (1): a cocone is essentially constant with value its vertex when one leg
admits a retraction from the cocone point and every other transition map eventually factors
through that retraction and the chosen leg. This is the source-facing predicate later applied to
filtered diagrams. -/
def IsEssentiallyConstantFilteredCocone {M : I ⥤ C} (c : Cocone M) : Prop :=
  ∃ (i : I) (σ : SplitEpi (c.ι.app i)),
    ∀ j : I, ∃ (k : I) (ik : i ⟶ k) (jk : j ⟶ k),
      M.map jk = c.ι.app j ≫ σ.section_ ≫ M.map ik

/-- Unpacks Definition 4.22.1 (1) into the textbook section-and-factorization data. -/
theorem isEssentiallyConstantFilteredCocone_iff {M : I ⥤ C} (c : Cocone M) :
    IsEssentiallyConstantFilteredCocone c ↔
      ∃ (i : I) (s : c.pt ⟶ M.obj i),
        s ≫ c.ι.app i = 𝟙 c.pt ∧
          ∀ j : I,
            ∃ (k : I) (ik : i ⟶ k) (jk : j ⟶ k),
              M.map jk = c.ι.app j ≫ s ≫ M.map ik := by
  constructor
  · rintro ⟨i, σ, hσ⟩
    exact ⟨i, σ.section_, σ.id, hσ⟩
  · rintro ⟨i, s, hs, hfac⟩
    exact ⟨i, ⟨s, hs⟩, hfac⟩

namespace IsEssentiallyConstantFilteredCocone

/-- Postcomposing an essentially constant filtered cocone with a functor preserves essential
constancy. -/
theorem mapCocone {D : Type uD} [Category.{vD} D] {M : I ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) (F : C ⥤ D) :
    IsEssentiallyConstantFilteredCocone (F.mapCocone c) := by
  rcases hc with ⟨i, σ, hσ⟩
  refine ⟨i, σ.map F, ?_⟩
  intro j
  rcases hσ j with ⟨k, ik, jk, h⟩
  refine ⟨k, ik, jk, ?_⟩
  simpa using congrArg (fun f ↦ F.map f) h

theorem nonempty_isColimit {M : I ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) : Nonempty (IsColimit c) := by
  rcases hc with ⟨i, σ, hfac⟩
  refine ⟨IsColimit.mk (fun t ↦ σ.section_ ≫ t.ι.app i) ?_ ?_⟩
  · intro t j
    rcases hfac j with ⟨k, ik, jk, hjk⟩
    have h₁ :
        c.ι.app j ≫ σ.section_ ≫ t.ι.app i =
          c.ι.app j ≫ σ.section_ ≫ M.map ik ≫ t.ι.app k := by
      rw [← t.w ik]
      rfl
    have h₂ :
        c.ι.app j ≫ σ.section_ ≫ M.map ik ≫ t.ι.app k =
          M.map jk ≫ t.ι.app k := by
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ t.ι.app k) hjk.symm
    exact h₁.trans <| h₂.trans <| t.w jk
  · intro t m hm
    have hm' : (σ.section_ ≫ c.ι.app i) ≫ m = σ.section_ ≫ t.ι.app i := by
      simpa [Category.assoc] using congrArg (fun f ↦ σ.section_ ≫ f) (hm i)
    exact (by simp : m = (σ.section_ ≫ c.ι.app i) ≫ m).trans hm'

/-- An essentially constant filtered cocone is a colimit cocone. -/
noncomputable def isColimit {M : I ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) : IsColimit c := by
  classical
  exact Classical.choice (nonempty_isColimit hc)

end IsEssentiallyConstantFilteredCocone

/-- Definition 4.22.1 (2): a cone is essentially constant with value its vertex when one leg
admits a retraction to the cone point and every other transition map eventually factors through
that retraction and the chosen leg. This is the source-facing predicate later applied to
cofiltered diagrams. -/
def IsEssentiallyConstantCofilteredCone {M : I ⥤ C} (c : Cone M) : Prop :=
  IsEssentiallyConstantFilteredCocone c.op

/-- Unpacks Definition 4.22.1 (2) into the dual split-mono/factorization data on a distinguished
cone leg. This is the canonical packaging of the textbook retraction data. -/
theorem isEssentiallyConstantCofilteredCone_iff {M : I ⥤ C} (c : Cone M) :
    IsEssentiallyConstantCofilteredCone c ↔
      ∃ (i : I) (σ : SplitMono (c.π.app i)),
        ∀ j : I, ∃ (k : I) (ki : k ⟶ i) (kj : k ⟶ j),
          M.map kj = M.map ki ≫ σ.retraction ≫ c.π.app j := by
  change IsEssentiallyConstantFilteredCocone c.op ↔ _
  constructor
  · rintro ⟨i, τ, hτ⟩
    refine ⟨i.unop, ?_, ?_⟩
    · exact
        { retraction := τ.section_.unop
          id := by
            apply Quiver.Hom.op_inj
            exact τ.id }
    · intro j
      rcases hτ (op j) with ⟨k, ik, jk, hk⟩
      refine ⟨k.unop, ik.unop, jk.unop, ?_⟩
      change M.map jk.unop = M.map ik.unop ≫ τ.section_.unop ≫ c.π.app j
      simpa using congrArg Quiver.Hom.unop hk
  · rintro ⟨i, σ, hfac⟩
    refine ⟨op i, ?_, ?_⟩
    · exact
        { section_ := σ.retraction.op
          id := by
            apply Quiver.Hom.unop_inj
            exact σ.id }
    · intro j
      rcases hfac j.unop with ⟨k, ki, kj, hk⟩
      refine ⟨op k, ki.op, kj.op, ?_⟩
      change (M.map kj).op = (c.π.app j.unop).op ≫ σ.retraction.op ≫ (M.map ki).op
      simpa using congrArg Quiver.Hom.op hk

namespace IsEssentiallyConstantCofilteredCone

/-- Postcomposing an essentially constant cofiltered cone with a functor preserves essential
constancy. -/
theorem mapCone {D : Type uD} [Category.{vD} D] {M : I ⥤ C} {c : Cone M}
    (hc : IsEssentiallyConstantCofilteredCone c) (F : C ⥤ D) :
    IsEssentiallyConstantCofilteredCone (F.mapCone c) := by
  change IsEssentiallyConstantFilteredCocone ((F.mapCone c).op)
  simpa using (show IsEssentiallyConstantFilteredCocone c.op from hc).mapCocone F.op

/-- An essentially constant cofiltered cone admits a limit structure. -/
theorem nonempty_isLimit {M : I ⥤ C} {c : Cone M}
    (hc : IsEssentiallyConstantCofilteredCone c) : Nonempty (IsLimit c) := by
  rw [isEssentiallyConstantCofilteredCone_iff] at hc
  rcases hc with ⟨i, σ, hfac⟩
  refine ⟨IsLimit.mk (fun t ↦ t.π.app i ≫ σ.retraction) ?_ ?_⟩
  · intro t j
    rcases hfac j with ⟨k, ki, kj, hk⟩
    have h₁ :
        t.π.app i ≫ σ.retraction ≫ c.π.app j =
          t.π.app k ≫ M.map ki ≫ σ.retraction ≫ c.π.app j := by
      simpa [Category.assoc] using
        congrArg (fun f ↦ f ≫ σ.retraction ≫ c.π.app j) (t.w ki).symm
    have h₂ :
        t.π.app k ≫ M.map ki ≫ σ.retraction ≫ c.π.app j =
          t.π.app k ≫ M.map kj := by
      simpa [Category.assoc] using congrArg (fun f ↦ t.π.app k ≫ f) hk.symm
    simpa [Category.assoc] using h₁.trans <| h₂.trans <| t.w kj
  · intro t m hm
    have hm' : m ≫ c.π.app i ≫ σ.retraction = t.π.app i ≫ σ.retraction := by
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ σ.retraction) (hm i)
    exact (by simp : m = m ≫ c.π.app i ≫ σ.retraction).trans hm'

/-- An essentially constant cofiltered cone is a limit cone. -/
noncomputable def isLimit {M : I ⥤ C} {c : Cone M} (hc : IsEssentiallyConstantCofilteredCone c) :
    IsLimit c := by
  classical
  exact Classical.choice (nonempty_isLimit hc)

end IsEssentiallyConstantCofilteredCone
