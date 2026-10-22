/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_1
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_3

-- Declarations for this item are recorded in this dedicated item file.

universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: recursive presentations of finitely generated groups and Higman-style embedding
theorems.

Layer triage:
- `source-facing`: a finitely generated group `G`, the textbook condition that `G` admit a
  recursive presentation, and the textbook conclusion that `G` embeds in some finitely presented
  group.
- `core/canonical`: `Group.FG G`, `Group.IsFinitelyPresented H`,
  `GroupPresentation.IsRecursive R`, the presentation bridge `PresentedGroup R ≃* G`, and
  injective homomorphisms `G →* H`.
- `bridge/view`: the textbook phrase “`G` can be recursively presented” is recorded by the group
  owner predicate `Group.IsRecursivelyPresented`, built directly from a finite-generator recursive
  presentation, while the embedding conclusion is stated in the chapter's direct existential style.

Domain sampling:
1. `Group.IsFinitelyPresented` is mathlib's owner predicate for finite presentability of an
   abstract group.
2. The surrounding chapter expresses embeddings source-faithfully as a homomorphism together with
   `Function.Injective`, so the group-level owner should package exactly that datum rather than a
   second wrapper object.
3. `GroupPresentation.IsRecursive R` is the project's owner predicate for recursive relator sets.
4. `PresentedGroup R ≃* G` from Definition `2-1-1` is the canonical bridge from a presentation to
   an abstract group.

Primitive vs. derived:
- primitive public data for recursive presentability: a finite generator count `n`, a relator set
  `R : Set (FreeGroup (Fin n))`, a presentation equivalence `PresentedGroup R ≃* G`, and a proof
  that `R` is recursive;
- derived API: the abstract group-level predicate `Group.IsRecursivelyPresented`, its direct
  constructor from an explicit presentation, the induced finite-generation instance
  `IsRecursivelyPresented.fg`, and the owner-side embedding consequence
  `IsRecursivelyPresented.exists_finitelyPresented_embedding`.
-/

/-- A group is recursively presented when it admits a presentation on finitely many generators
whose relator set is recursive. -/
def IsRecursivelyPresented (G : Type u) [Group G] : Prop :=
  ∃ (n : ℕ) (R : Set (FreeGroup (Fin n))) (_ : PresentedGroup R ≃* G),
    GroupPresentation.IsRecursive R

variable {G : Type u} [Group G]

/-- An explicit recursive presentation on finitely many generators induces the abstract owner
predicate `IsRecursivelyPresented G`. -/
theorem isRecursivelyPresented_of_presentation
    (n : ℕ) (R : Set (FreeGroup (Fin n))) (P : PresentedGroup R ≃* G)
    (hR : GroupPresentation.IsRecursive R) :
    IsRecursivelyPresented G := by
  exact ⟨n, R, P, hR⟩

namespace IsRecursivelyPresented

/-- A recursively presented group is finitely generated, because its chosen presentation has only
finitely many generators. -/
theorem fg (hG : IsRecursivelyPresented G) : FG G := by
  rcases hG with ⟨n, R, P, _⟩
  letI : FG (PresentedGroup R) := PresentedGroup.instFG R
  exact Group.fg_of_surjective (f := P.toMonoidHom) P.surjective

end IsRecursivelyPresented

variable (G : Type u) [Group G] [FG G]

/-- Theorem 4-7-1 (Higman Embedding Theorem): a finitely generated group embeds in some finitely
presented group if and only if it is recursively presented. -/
-- Proof sketch: if `G` embeds in a finitely presented group `H`, choose a finite presentation of
-- `H` and recursively enumerate the words whose values lie in the embedded copy of `G`; pulling
-- those relators back through the embedding yields a recursive presentation of `G`. Conversely,
-- Higman's construction uses iterated HNN extensions and amalgamated products to embed any
-- finitely generated recursively presented group in a finitely presented group.
theorem exists_finitelyPresented_embedding_iff_isRecursivelyPresented :
    (∃ (H : Type u) (_ : Group H) (_ : IsFinitelyPresented H) (f : G →* H),
      Function.Injective f) ↔ IsRecursivelyPresented G := sorry

namespace IsRecursivelyPresented

/-- A recursively presented group embeds in some finitely presented group. The ambient finite
generation required by Theorem `4-7-1` is derived from the recursive presentation itself. -/
theorem exists_finitelyPresented_embedding {G : Type u} [Group G]
    (hG : IsRecursivelyPresented G) :
    ∃ (H : Type u) (_ : Group H) (_ : IsFinitelyPresented H) (f : G →* H),
      Function.Injective f := by
  letI : FG G := hG.fg
  exact (exists_finitelyPresented_embedding_iff_isRecursivelyPresented G).2 hG

end IsRecursivelyPresented

end Group
