module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]
variable {X : C}

/- Companion recall: for a connected indexing category `J`, the forgetful functor
`Over.forget (op X)` preserves `Jᵒᵖ`-shaped limits. -/
recall Over.preservesLimitsOfShape_forget_of_isConnected

/-- Lemma 4.16.3: for a connected diagram `M : J ⥤ Under X`, the forgetful functor
`Under.forget X` preserves the colimit of `M`. Equivalently, whenever `M` has a colimit in
`Under X`, the underlying diagram in `C` has the same colimit. -/
-- Proof sketch: dualize the connected-limit statement for `Over.forget (op X)` using
-- `Over.opEquivOpUnder X` and the opposites API, then specialize the resulting
-- `PreservesColimitsOfShape` instance to the diagram `M`.
theorem under_forget_preserves_colimit_of_isConnected (M : J ⥤ Under X) [IsConnected J] :
    PreservesColimit M (Under.forget X) := by
  -- Move the opposite diagram across the over-under equivalence so the connected-limit
  -- statement for `Over.forget (op X)` applies to the transported diagram.
  have h_limit_via_over :
      PreservesLimit M.op
        (((Over.opEquivOpUnder X).symm.functor) ⋙ Over.forget (Opposite.op X)) := by
    infer_instance
  -- Identify the transported forgetful functor with the opposite of `Under.forget X`.
  have h_comparison :
      ((Over.opEquivOpUnder X).symm.functor ⋙ Over.forget (Opposite.op X)) ≅
        (Under.forget X).op := by
    refine NatIso.ofComponents (fun Y ↦ Iso.refl _) ?_
    intro Y Z f
    cases f
    simp [Over.opEquivOpUnder]
  -- Transport the preservation result across that comparison isomorphism.
  have h_limit_op : PreservesLimit M.op (Under.forget X).op := by
    letI : PreservesLimit M.op
        (((Over.opEquivOpUnder X).symm.functor) ⋙ Over.forget (Opposite.op X)) :=
      h_limit_via_over
    exact preservesLimit_of_natIso M.op h_comparison
  -- Convert the opposite-side limit preservation statement back to the desired colimit claim.
  letI : PreservesLimit M.op (Under.forget X).op := h_limit_op
  simpa using (preservesColimit_of_op M (Under.forget X))

end CategoryTheory
