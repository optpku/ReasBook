/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_7_1

universe u v

set_option autoImplicit false

namespace Group

/-!
Primary domain: universal embedding theorems for recursively presented groups in the Higman
embedding section.

Layer triage:
- `source-facing`: the existence of a finitely presented group `H` into which every recursively
  presented group embeds.
- `core/canonical`: `IsRecursivelyPresented` from Theorem `4-7-1`, `IsFinitelyPresented`, and
  injective homomorphisms `G →* H`.
- `bridge/view`: the textbook proof passes through a countable free product of all finite
  presentations and then Higman's embedding theorem, but those presentation-level choices remain
  proof data rather than public API in this item.

Domain sampling:
1. `IsRecursivelyPresented` from Theorem `4-7-1` is the chapter's owner abstraction for the
   hypothesis “`G` is recursively presented”.
2. `IsRecursivelyPresented.exists_finitelyPresented_embedding` from Theorem `4-7-1` is the
   canonical per-group bridge from that owner predicate to embeddability in a finitely presented
   group.
3. `IsFinitelyPresented` is mathlib's owner predicate for finite presentability.
4. Theorems `4-3-1` and `4-7-2` confirm the chapter's source-facing style for embedding theorems:
   quantify over an ambient witness group together with a homomorphism and `Function.Injective`,
   rather than introducing a separate public wrapper for embedding data.

Primitive vs. derived:
- primitive public data: only the ambient witness group `H`;
- derived owner-side data: finite presentability of `H` and, for each recursively presented group
  `G`, an embedding `G →* H`.
-/

/-- Theorem 4-7-3: there exists a finitely presented group containing an embedded copy of every
recursively presented group. -/
-- Proof sketch: enumerate all finite presentations and take their free product, obtaining a
-- recursively presented group that contains a copy of every finitely presented group. Apply the
-- two-generator embedding theorem to place that countable group inside a recursively presented
-- two-generator group, then apply Higman's embedding theorem to embed the latter in a finitely
-- presented group `H`. Every recursively presented group embeds in some finitely presented group
-- by Theorem `4-7-1`, and those finitely presented groups already embed in `H`.
theorem exists_finitelyPresented_group_embedding_all_recursivelyPresented_groups :
    ∃ (H : Type u) (_ : Group H),
      IsFinitelyPresented H ∧
        ∀ {G : Type v} [Group G], IsRecursivelyPresented G →
          ∃ (f : G →* H), Function.Injective f := sorry

end Group
