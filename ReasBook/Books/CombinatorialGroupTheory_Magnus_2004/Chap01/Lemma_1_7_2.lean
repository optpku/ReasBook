/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Layer triage:
-- `source-facing`: a tree together with an injective infinite ray, and an orientation in which
-- every vertex has an outgoing edge.
-- `core/canonical`: `SimpleGraph.IsTree`, `Digraph.toSimpleGraphInclusive`, `Std.Asymm`, and
-- `WellFounded`.
-- `bridge/view`: the theorem packages the source orientation condition by requiring that the
-- forgetful map `D.toSimpleGraphInclusive` recover the given tree and by reading the
-- no-opposite-direction condition through the canonical relation predicate `Std.Asymm D.Adj`.
-- Domain sampling:
-- 1. `SimpleGraph.IsTree` is mathlib's owner predicate for trees.
-- 2. `Digraph.toSimpleGraphInclusive` is mathlib's owner map from digraphs to the underlying
--    unoriented simple graph.
-- 3. `Std.Asymm D.Adj` is the canonical owner predicate for the source condition that oriented
--    edges never occur in both directions.
-- 4. `SimpleGraph.fromRel_adj` shows that equality with `toSimpleGraphInclusive` expresses exactly
--    the "one of the two directions is present" part of an orientation.
-- 5. `WellFounded D.Adj` is the canonical owner predicate for the well-foundedness of the reverse
--    edge relation induced by the orientation.
-- Primitive vs. derived:
-- the primitive source data are the tree `T`, an injective ray `p : ℕ → V` with adjacent
-- consecutive vertices, and the digraph `D`; the fact that `D` orients `T` should be expressed
-- via the owner map `D.toSimpleGraphInclusive = T` rather than a parallel local orientation
-- predicate.

variable {V : Type u} {T : SimpleGraph V}

-- Proof sketch: choose a vertex on an infinite ray, orient every edge in the union of all
-- infinite rays from it away from that vertex, orient each complementary component toward its
-- unique attachment point, and then show the resulting orientation is well-founded and has no
-- maximal vertex.
/-- Lemma 1-7-2: a tree with an infinite path admits an orientation whose reverse-edge relation is
well-founded and in which every vertex has an outgoing edge. -/
theorem tree_exists_orientation_wellFounded_noMaximal
    (hT : T.IsTree)
    (h_infinite : ∃ p : ℕ → V, Function.Injective p ∧ ∀ n : ℕ, T.Adj (p n) (p (n + 1))) :
    ∃ D : Digraph V,
      D.toSimpleGraphInclusive = T ∧
      Std.Asymm D.Adj ∧
      WellFounded D.Adj ∧
      ∀ v : V, ∃ w : V, D.Adj v w := sorry
