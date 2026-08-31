module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Set TopCat TopologicalSpace

universe u

noncomputable section

attribute [local instance] Classical.propDecidable

section

variable {X : TopCat.{u}} (x : X)
variable {C : Type u} [Category.{u} C] [HasTerminal C] [HasColimits C] (A : C)

/-
Domain-style sampling for Lemma 6.27.2:
- primary domain: skyscraper sheaves on a topological space and the computation of their stalks;
- sampled owner declarations:
  `skyscraperSheaf`,
  `skyscraperPresheafStalkOfSpecializes`,
  `skyscraperPresheafStalkOfNotSpecializesIsTerminal`,
  `specializes_iff_mem_closure`;
- source/core/bridge triage:
  `source-facing`: the closure-language reformulation of the stalk computation in the Stacks text;
  `core/canonical`: the mathlib stalk computations for skyscraper presheaves along specialization;
  `bridge/view`: the equivalence between `x' ∈ closure {x}` and `x ⤳ x'`.

Primitive data are only the point `x`, the value `A`, and the comparison point `x'`. The stalk
computation itself is already owned by mathlib, so this file should reuse that owner directly and
keep only the closure-based reformulation as derived API.
-/

/- The core owner for the nonvanishing stalk case is the canonical mathlib isomorphism
`skyscraperPresheafStalkOfSpecializes`. -/
recall skyscraperPresheafStalkOfSpecializes

/- The core owner for the vanishing stalk case is the canonical mathlib terminality statement
`skyscraperPresheafStalkOfNotSpecializesIsTerminal`. -/
recall skyscraperPresheafStalkOfNotSpecializesIsTerminal

/-- Lemma 6.27.2 (1): if `x'` lies in `closure {x}`, then the stalk at `x'` of the skyscraper
sheaf at `x` with value `A` is canonically isomorphic to `A`. This generic categorical statement
specializes to sets, abelian groups, algebraic structures, and sheaves of modules. This is the
closure-language restatement of `skyscraperPresheafStalkOfSpecializes`. -/
noncomputable def skyscraperSheaf_stalk_iso_of_mem_closure
    (x' : X) (h : x' ∈ closure ({x} : Set X)) :
    (skyscraperSheaf x A).presheaf.stalk x' ≅ A :=
  skyscraperPresheafStalkOfSpecializes x A (specializes_iff_mem_closure.mpr h)

-- Proof sketch: unfold `skyscraperSheaf_stalk_iso_of_mem_closure`; it was defined to be the
-- canonical specialization-based stalk isomorphism rewritten through
-- `specializes_iff_mem_closure`.
/-- Unfolding `skyscraperSheaf_stalk_iso_of_mem_closure` identifies it with the canonical
specialization-based skyscraper stalk isomorphism. -/
theorem skyscraperSheaf_stalk_iso_of_mem_closure_def
    (x' : X) (h : x' ∈ closure ({x} : Set X)) :
    skyscraperSheaf_stalk_iso_of_mem_closure x A x' h =
      skyscraperPresheafStalkOfSpecializes x A (specializes_iff_mem_closure.mpr h) := by
  -- Unfold the closure-language wrapper: it was defined to be this specialization-based stalk
  -- isomorphism.
  rfl

/-- Lemma 6.27.2 (2): if `x'` does not lie in `closure {x}`, then the stalk at `x'` of the
skyscraper sheaf at `x` with value `A` is terminal; in the case of sets this is a one-point set.
This generic categorical statement also covers abelian groups, algebraic structures, and sheaves
of modules. This is the closure-language restatement of
`skyscraperPresheafStalkOfNotSpecializesIsTerminal`. -/
def skyscraperSheaf_stalk_isTerminal_of_not_mem_closure
    (x' : X) (h : x' ∉ closure ({x} : Set X)) :
    IsTerminal ((skyscraperSheaf x A).presheaf.stalk x') :=
  skyscraperPresheafStalkOfNotSpecializesIsTerminal x A
    (fun hs ↦ h (specializes_iff_mem_closure.mp hs))

-- Proof sketch: unfold `skyscraperSheaf_stalk_isTerminal_of_not_mem_closure`; it is defined by
-- transporting the canonical non-specialization terminality statement through
-- `specializes_iff_mem_closure`.
/-- Unfolding `skyscraperSheaf_stalk_isTerminal_of_not_mem_closure` identifies it with the
canonical non-specialization terminality statement for skyscraper stalks. -/
theorem skyscraperSheaf_stalk_isTerminal_of_not_mem_closure_def
    (x' : X) (h : x' ∉ closure ({x} : Set X)) :
    skyscraperSheaf_stalk_isTerminal_of_not_mem_closure x A x' h =
      skyscraperPresheafStalkOfNotSpecializesIsTerminal x A
        (fun hs ↦ h (specializes_iff_mem_closure.mp hs)) := by
  -- Unfold the closure-language wrapper: it is defined by transporting the canonical
  -- non-specialization terminality result across the closure/specialization equivalence.
  rfl

end
