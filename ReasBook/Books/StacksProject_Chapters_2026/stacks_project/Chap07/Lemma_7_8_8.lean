module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_8_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {K K₁ K₂ : Pretopology C}
variable {P : Cᵒᵖ ⥤ Type w}

/- Domain-style sampling for Lemma 7.8.8:
- primary domain: comparison of sheaf conditions for pretopologies via common ambient covering
  classes and the induced Grothendieck topologies;
- sampled owner API:
  `isSheaf_iff_of_mutual_refinement_pretopology`,
  `Presheaf.IsSheaf.of_le`,
  `Pretopology.gi`;
- best owner abstraction: the core/canonical owner is
  `isSheaf_iff_of_mutual_refinement_pretopology`; the ambient-`K` phrasing of Lemma 7.8.8 is a
  bridge/view that packages a special way of producing the two refinement hypotheses;
- primitive data: the three pretopologies and the four comparison inequalities;
- derived API here: only the equivalence of the two sheaf predicates.

Source/core/bridge triage:
- `source-facing`: the Stacks phrasing with a common ambient pretopology `K`;
- `core/canonical`: `isSheaf_iff_of_mutual_refinement_pretopology`;
- `bridge/view`: derive the two refinement inequalities through `K` and feed them to the canonical
  owner theorem.
-/

/-- Lemma 7.8.8: let `K` be an ambient pretopology on `C`, and let `K₁, K₂ ≤ K` be two
sub-pretopologies. If every `K`-cover is already a `K₁`-cover and also already a `K₂`-cover, then
any set-valued presheaf is a `K₁`-sheaf if and only if it is a `K₂`-sheaf.

In the chapter API this is the ambient-`K` bridge case of
`isSheaf_iff_of_mutual_refinement_pretopology`: the hypotheses imply
`K₁ ≤ K₂.toGrothendieck.toPretopology` and `K₂ ≤ K₁.toGrothendieck.toPretopology` by passing
through `K` and then applying the unit map of `Pretopology.gi`. -/
theorem isSheaf_iff_of_common_ambient_pretopology
    (h₁ : K₁ ≤ K) (h₂ : K₂ ≤ K)
    (hK₁ : K ≤ K₁)
    (hK₂ : K ≤ K₂) :
    Presheaf.IsSheaf K₁.toGrothendieck P ↔
      Presheaf.IsSheaf K₂.toGrothendieck P := by
  refine isSheaf_iff_of_mutual_refinement_pretopology ?_ ?_
  · exact le_trans h₁ <| le_trans hK₂ <|
      (Pretopology.gi C).gc.le_u_l K₂
  · exact le_trans h₂ <| le_trans hK₁ <|
      (Pretopology.gi C).gc.le_u_l K₁

end

end CategoryTheory
