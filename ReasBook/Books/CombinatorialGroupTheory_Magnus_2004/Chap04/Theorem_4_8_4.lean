/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_4_8
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_8_1

universe u v w

set_option autoImplicit false

namespace Group

/-!
Primary domain: algebraically closed groups and embedding theorems for finitely generated groups
with solvable word problem.

Layer triage:
- `source-facing`: the group-level property that `G` embeds in every algebraically closed group,
  together with the theorem that solvable word problem implies that property.
- `core/canonical`: `IsAlgebraicallyClosedGroup A` from Theorem `4-8-1` is the chapter owner for
  algebraic closedness, `Group.FG` is mathlib's owner for finite generation, and
  `Group.HasSolvableWordProblem` from Theorem `4-4-8` is the project owner for solvability of the
  word problem.
- `bridge/view`: for a fixed ambient group `A`, a group embedding is a homomorphism `G →* A`
  together with `Function.Injective`.

Domain sampling:
1. `IsAlgebraicallyClosedGroup` in `Theorem_4_8_1` is the chapter owner abstraction for the
   finite-system extension property, so this file should reuse it rather than rebuilding a local
   algebraic-system API.
2. The class field `IsAlgebraicallyClosedGroup.exists_solution_of_satisfiable` in
   `Theorem_4_8_1` is the canonical elimination theorem for that owner abstraction.
3. `Group.FG` is mathlib's owner predicate for finite generation.
4. `Group.HasSolvableWordProblem` from Theorem `4-4-8` is the abstract owner for the source
   hypothesis on `G`.

Primitive vs. derived:
- primitive public data here: the source group `G` and the hypothesis `HasSolvableWordProblem G`;
- derived public data: the finite generation of `G`, exposed below as
  `HasSolvableWordProblem.fg`, and for each algebraically closed ambient group `A` an embedding
  witness `f : G →* A` together with its injectivity. Since algebraic closedness is already owned
  by the class `IsAlgebraicallyClosedGroup`, the ambient hypothesis should be carried by an
  instance binder rather than by a separate explicit argument, and the target universe should
  remain arbitrary because the textbook statement ranges over every algebraically closed group; the
  hidden variable universe used by `IsAlgebraicallyClosedGroup` should remain arbitrary as well.
-/

/-- The source-facing property that `G` embeds in every algebraically closed group. -/
def EmbedsInAllAlgebraicallyClosedGroups (G : Type u) [Group G] : Prop :=
  ∀ (A : Type v) [Group A] [IsAlgebraicallyClosedGroup.{v, w} A],
    ∃ f : G →* A, Function.Injective f

namespace HasSolvableWordProblem

/-- A group with solvable word problem is finitely generated, because the owner predicate is built
from a finite-generator presentation. -/
theorem fg {G : Type u} [Group G] (hG : Group.HasSolvableWordProblem G) : FG G := by
  rcases hG with ⟨n, R, P, _⟩
  have hfg : FG (PresentedGroup R) := by
    change FG (FreeGroup (Fin n) ⧸ Subgroup.normalClosure R)
    infer_instance
  letI : FG (PresentedGroup R) := hfg
  let f : PresentedGroup R →* G := P.toMonoidHom
  have hf : Function.Surjective f := P.surjective
  exact Group.fg_of_surjective hf

-- Proof sketch: Boone-Higman embeds `G` in a simple subgroup of a finitely presented group.
-- Interpreting the resulting finite presentation over `A` gives a finite coefficient system, and
-- the ambient algebraic-closedness owner from Theorem `4-8-1` realizes that system in `A`.
-- Simplicity then forces the induced map on the simple subgroup, hence on `G`, to be injective.
/-- Theorem 4-8-4: every finitely generated group with solvable word problem embeds in every
algebraically closed group. The finite generation in the source statement is derived by `hG.fg`.
-/
theorem embedsInAllAlgebraicallyClosedGroups {G : Type u} [Group G]
    (hG : Group.HasSolvableWordProblem G) :
    EmbedsInAllAlgebraicallyClosedGroups G := sorry

end HasSolvableWordProblem

end Group
