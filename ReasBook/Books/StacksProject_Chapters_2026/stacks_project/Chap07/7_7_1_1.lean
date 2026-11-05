module

public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe t w v u

namespace CategoryTheory

open Opposite Limits
open Equalizer.Presieve.Arrows

variable {C : Type u} [Category.{v} C]
variable (P : Cᵒᵖ ⥤ Type w) {U : C} {I : Type t} [Small.{w} I]
variable (Ui : I → C) (π : (i : I) → Ui i ⟶ U)
variable [(Presieve.ofArrows Ui π).HasPairwisePullbacks]

/-
Layering for this item:
* source-facing: the textbook equalizer fork for a family `π i : Ui i ⟶ U`;
* core/canonical owner: `CategoryTheory.Equalizer.Presieve.Arrows`;
* primitive vs. derived: the primitive data are the family `Ui`, the arrows `π`, and the
  pairwise-pullback hypothesis; the fork and sheaf-condition statement are derived by the owner
  declarations `forkMap`, `firstMap`, `secondMap`, `w`, and `sheaf_condition`.
-/

/- 7.7.1.1: for a family of arrows `π i : Ui i ⟶ U`, the sheaf-condition diagram is the
canonical fork
`P.obj (op U) ⟶ ∏ᶜ fun i ↦ P.obj (op (Ui i)) ⇉
  ∏ᶜ fun ij : I × I ↦ P.obj (op (pullback (π ij.1) (π ij.2)))`,
with the two parallel arrows induced by the two pullback projections. -/
#check (Fork.ofι (forkMap P Ui π) (w P Ui π) : Fork (firstMap P Ui π) (secondMap P Ui π))

/- For this family presentation, the sheaf condition is exactly the statement that the canonical
fork above is an equalizer. -/
recall sheaf_condition

end CategoryTheory
