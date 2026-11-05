module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.Lemma_6_31_7

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instConcreteCategory CategoryTheory.Types.instFunLike

noncomputable section

universe u

/-
Domain-style sampling for Remark 6.31.13:
- primary domain: sheaves of sets on a topological space, the extension-by-initial-object functor
  along an open immersion, and the canonical limit-preservation owners
  `IsTerminal`, `PreservesLimit`, and `leftExactFunctor`;
- sampled owner declarations:
  `openSubsetSheafExtensionByInitialObject`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem`,
  `IsTerminal.isTerminalObj`,
  `leftExactFunctor`,
  `leftExactFunctor_iff`,
  `preservesFiniteLimits_of_preservesTerminal_and_pullbacks`;
- owner abstraction: the public owner is the functor `j! U` together with the standard terminal and
  left-exactness owners, not a parallel local wrapper around “image of a terminal object”;
- primitive data: the open subset `U` and a point `x ∉ U`; the stalk-initial statement outside `U`
  is upstream chapter API;
- derived API: failure of terminal-object preservation and hence failure of left exactness.

Source/core/bridge triage:
- `source-facing`: the remark that `j_!` on sheaves of sets is not left exact for `U ≠ X`;
- `core/canonical`: `PreservesLimit (Functor.empty _) (j! U)` and
  `leftExactFunctor _ _ (j! U)`;
- `bridge/view`: the companion statement that the image of a terminal sheaf is not terminal.
-/

section

variable {X : TopCat.{u}}

private theorem exists_not_mem_of_ne_top (U : Opens X) (hU : U ≠ ⊤) :
    ∃ x : X, x ∉ (U : Set X) := by
  classical
  by_contra h
  push Not at h
  apply hU
  ext x
  simp [h x]

private theorem stalk_nonempty_of_isTerminal (F : X.Sheaf (Type u)) (hF : IsTerminal F) (x : X) :
    Nonempty (F.presheaf.stalk x) := by
  let η :
      Sheaf.terminal (Opens.grothendieckTopology X) Types.isTerminalPUnit ⟶ F :=
    hF.from _
  exact ⟨F.presheaf.germ ⊤ x (by simp) ((η.1).app (op ⊤) PUnit.unit)⟩

/-- For a proper open subset `U ⊊ X`, extension by the empty set on sheaves of sets does not send
a terminal object of `Sh(U)` to a terminal object of `Sh(X)`. -/
theorem openSubsetSheafExtensionByInitialObject_obj_terminal_not_isTerminal_of_ne_top
    (U : Opens X) (hU : U ≠ ⊤) :
    ¬ Nonempty (IsTerminal (((j! U :
            (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u)).obj
          (⊤_ ((extensionByZeroOpenSubsetSpace U).Sheaf (Type u)))))) := by
  let T : (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) := ⊤_ _
  intro hT
  obtain ⟨x, hx⟩ := exists_not_mem_of_ne_top U hU
  have hEmpty : IsEmpty (((j! U).obj T).presheaf.stalk x) := by
    exact Concrete.empty_of_initial_of_preserves
      (((j! U).obj T).presheaf.stalk x) ⟨by
        simpa using
          OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem U T hx⟩
  exact hEmpty.false (stalk_nonempty_of_isTerminal ((j! U).obj T) hT.some x).some

/-- For a proper open subset `U ⊊ X`, extension by the empty set on sheaves of sets does not
preserve terminal objects. -/
theorem openSubsetSheafExtensionByInitialObject_not_preservesTerminal_of_ne_top
    (U : Opens X) (hU : U ≠ ⊤) :
    ¬ (PreservesLimit (Functor.empty.{0} ((extensionByZeroOpenSubsetSpace U).Sheaf (Type u)))
        (j! U : (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u))) := by
  intro hF
  letI :
      PreservesLimit (Functor.empty.{0} ((extensionByZeroOpenSubsetSpace U).Sheaf (Type u)))
        (j! U : (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u)) :=
    hF
  exact openSubsetSheafExtensionByInitialObject_obj_terminal_not_isTerminal_of_ne_top U hU
    ⟨terminalIsTerminal.isTerminalObj (j! U :
      (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u))⟩

/-- Remark 6.31.13: if `U` is a proper open subset of `X`, then extension by the empty set
`j_! : Sh(U) ⥤ Sh(X)` on sheaves of sets is not left exact. A witness is that it does not send a
terminal object of `Sh(U)` to a terminal object of `Sh(X)`. -/
theorem openSubsetSheafExtensionByInitialObject_not_leftExact_of_ne_top
    (U : Opens X) (hU : U ≠ ⊤) :
    ¬ (leftExactFunctor ((extensionByZeroOpenSubsetSpace U).Sheaf (Type u)) (X.Sheaf (Type u))
        (j! U : (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u))) := by
  intro hF
  letI : PreservesFiniteLimits
      (j! U : (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u)) := by
    simpa [leftExactFunctor_iff] using hF
  exact openSubsetSheafExtensionByInitialObject_not_preservesTerminal_of_ne_top U hU inferInstance

end
