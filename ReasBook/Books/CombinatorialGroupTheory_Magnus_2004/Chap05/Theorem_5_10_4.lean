/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_5

universe u

set_option autoImplicit false

section

variable (H : Type u) [Group H] [Countable H]

/-!
Primary domain: embedding countable groups into two-generator overgroups with rigidity
properties coming from the Section `10` small-cancellation construction.

Layer triage:
- `source-facing`: a countable group `H`, an embedding into an ambient overgroup `G`, and the
  textbook conclusions that `G` is two-generator, complete, and Hopfian, with the additional
  finite-presentability and cohopfian refinements.
- `core/canonical`: `Function.Injective` for the embedding, `Group.FG` together with `Group.rank`
  for the two-generator conclusion, `IsHopfian` and `IsCohopfian` for the endomorphism
  conditions, `Subgroup.center G = ⊥` and `MulAut.innerAutomorphismSubgroup G = ⊤` for
  completeness, and `Group.IsFinitelyPresented` for finite presentability.
- `bridge/view`: [Theorem_5_10_5](/volume/math/AI4M/users/zcwang/bookrepo/CombinatorialGroupTheory/CombinatorialGroupTheory/Items/Chap05/Theorem_5_10_5.lean)
  provides the explicit quotient owner `SmallCancellationProduct.quotient enumerate`; the present
  theorem is the source-facing existential packaging of that explicit construction.

Domain sampling:
1. [Theorem_4_3_1](/volume/math/AI4M/users/zcwang/bookrepo/CombinatorialGroupTheory/CombinatorialGroupTheory/Items/Chap04/Theorem_4_3_1.lean)
   already fixes the project style for “`H` embeds in a two-generator overgroup”: existentially
   quantify the ambient group and embedding map, and express the generator bound through
   `Group.rank`.
2. [Proposition_1_3_5](/volume/math/AI4M/users/zcwang/bookrepo/CombinatorialGroupTheory/CombinatorialGroupTheory/Items/Chap01/Proposition_1_3_5.lean)
   provides the owner predicates `IsHopfian` and `IsCohopfian`.
3. [Proposition_1_4_5](/volume/math/AI4M/users/zcwang/bookrepo/CombinatorialGroupTheory/CombinatorialGroupTheory/Items/Chap01/Proposition_1_4_5.lean)
   provides `MulAut.innerAutomorphismSubgroup`, so completeness is stated on the canonical
   automorphism-group owner rather than by a local wrapper.
4. [Theorem_5_10_5](/volume/math/AI4M/users/zcwang/bookrepo/CombinatorialGroupTheory/CombinatorialGroupTheory/Items/Chap05/Theorem_5_10_5.lean)
   already packages the explicit Section `10` quotient and its Hopfian/complete/cohopfian
   properties, so this file should expose only the source-facing existence theorem.

Primitive vs. derived:
- primitive public data: the ambient overgroup `G` and the embedding homomorphism `f : H →* G`;
- derived public properties: injectivity of `f`, the two-generator bound `Group.rank G ≤ 2`,
  Hopfianity, completeness, finite-presentability transfer, and the cohopfian refinement under
  the Section `10` order-`5` hypothesis inherited from the explicit quotient owner.
-/

-- Proof sketch: choose a surjective enumeration of `H`, apply the explicit small-cancellation
-- quotient construction from Theorem `5-10-5`, and package its owner-level properties into the
-- source-facing existential statement. The two-generator conclusion is the rank bound coming from
-- the quotient of `C₅ * C₇`, completeness is the pair “trivial center + all automorphisms are
-- inner”, and the final two clauses are the finitely presented and cohopfian refinements of the
-- same construction, with cohopfianity inherited under the explicit order-`5` torsion exclusion.
/-- Theorem 5-10-4: every countable group embeds in a two-generator complete Hopfian group. If
`H` is finitely presented, then the ambient group can be chosen finitely presented. If `H` has no
elements of order `5`, then the ambient group can be chosen cohopfian. -/
theorem exists_embedding_into_two_generator_complete_hopfian_group :
    ∃ (G : Type u) (_ : Group G) (_ : Group.FG G) (f : H →* G),
      Function.Injective f ∧
        Group.rank G ≤ 2 ∧
        IsHopfian G ∧
        (Subgroup.center G = ⊥ ∧ MulAut.innerAutomorphismSubgroup G = ⊤) ∧
        (Group.IsFinitelyPresented H → Group.IsFinitelyPresented G) ∧
        ((∀ h : H, orderOf h ≠ 5) → IsCohopfian G) := sorry

end
