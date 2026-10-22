/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Theorem_9_9

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 9.10: rewrite the lower semicontinuous convex envelope as the pointwise
supremum of its lower semicontinuous convex minorants. -/
private theorem lowerSemicontinuousConvexEnvelope_eq_iSup_minorants_local
    (f : H → EReal) :
    lowerSemicontinuousConvexEnvelope f =
      fun x ↦ ⨆ g : {g : H → EReal // g ∈ lowerSemicontinuousConvexMinorants f}, g.1 x := by
  funext x
  rw [lowerSemicontinuousConvexEnvelope_apply]
  apply le_antisymm
  · -- Every real-height epigraph value in the defining `sSup` comes from one indexed minorant.
    refine sSup_le fun y hy ↦ ?_
    rcases hy with ⟨g, hg, rfl⟩
    exact le_iSup_of_le ⟨g, hg⟩ le_rfl
  · -- Each indexed minorant contributes one term to the pointwise supremum.
    refine iSup_le fun g ↦ ?_
    exact le_sSup ⟨g.1, g.2, rfl⟩

/-- Helper for Corollary 9.10: the lower semicontinuous envelope still has convex epigraph when
the original epigraph is convex. -/
private theorem convex_epigraph_lowerSemicontinuousEnvelope_of_convex_epigraph
    (f : H → EReal) (hconv : Convex ℝ (epigraph f)) :
    Convex ℝ (epigraph (lowerSemicontinuousEnvelope f)) := by
  -- Lemma 1.32 identifies the hull epigraph with the closure of the original epigraph.
  rw [epi_lowerSemicontinuousHull_eq_closure_epi]
  -- Convexity survives closure in the product space.
  exact hconv.closure

/-- Helper for Corollary 9.10: once the lower semicontinuous hull is known to have convex
epigraph, maximality of the convex envelope forces the hull below it. -/
private theorem lowerSemicontinuousEnvelope_le_lowerSemicontinuousConvexEnvelope_of_convex_epigraph
    (f : H → EReal) (hconv : Convex ℝ (epigraph f)) :
    lowerSemicontinuousEnvelope f ≤ lowerSemicontinuousConvexEnvelope f := by
  have hhull_lsc : LowerSemicontinuous (lowerSemicontinuousEnvelope f) :=
    (lowerSemicontinuousHull_isGreatest f).1.1
  have hhull_le : lowerSemicontinuousEnvelope f ≤ f :=
    (lowerSemicontinuousHull_isGreatest f).1.2
  have hhull_conv : Convex ℝ (epigraph (lowerSemicontinuousEnvelope f)) :=
    convex_epigraph_lowerSemicontinuousEnvelope_of_convex_epigraph f hconv
  -- Proposition 9.8 applies once the hull is packaged as a lower semicontinuous convex minorant.
  exact
    le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
      hhull_lsc hhull_conv hhull_le

/-- Helper for Corollary 9.10: the lower semicontinuous convex envelope is always a
lower semicontinuous minorant of `f`, so it lies below the lower semicontinuous hull. -/
private theorem lowerSemicontinuousConvexEnvelope_le_lowerSemicontinuousEnvelope
    (f : H → EReal) :
    lowerSemicontinuousConvexEnvelope f ≤ lowerSemicontinuousEnvelope f := by
  -- Proposition 9.8 gives a lower semicontinuous minorant, and Lemma 1.32 makes the hull maximal.
  exact
    (lowerSemicontinuousHull_isGreatest f).2
      ⟨lowerSemicontinuous_lowerSemicontinuousConvexEnvelope f,
        lowerSemicontinuousConvexEnvelope_le f⟩

-- Proof sketch: Lemma 1.32 identifies the epigraph of the lower semicontinuous hull with
-- `closure (epigraph f)`, and Theorem 9.9 identifies the epigraph of the lower semicontinuous
-- convex envelope with the same closed epigraph when `f` is convex.
/-- Corollary 9.10: for a convex extended-real-valued function, the lower semicontinuous convex
envelope `\bar f` agrees with the lower semicontinuous envelope `\check f`. -/
theorem lowerSemicontinuousConvexEnvelope_eq_lowerSemicontinuousEnvelope_of_convex_epigraph
    (f : H → EReal) (hconv : Convex ℝ (epigraph f)) :
    lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f := by
  -- Route correction: use the two envelope maximality principles rather than the false generic
  -- characterization∗∗ in the `EReal` setting with possible `-∞` values.
  have hhull_le_env :
      lowerSemicontinuousEnvelope f ≤ lowerSemicontinuousConvexEnvelope f :=
    lowerSemicontinuousEnvelope_le_lowerSemicontinuousConvexEnvelope_of_convex_epigraph f hconv
  have henv_le_hull :
      lowerSemicontinuousConvexEnvelope f ≤ lowerSemicontinuousEnvelope f :=
    lowerSemicontinuousConvexEnvelope_le_lowerSemicontinuousEnvelope f
  -- The largest lower semicontinuous minorant and the largest lower semicontinuous convex
  -- minorant bound each other, so they coincide pointwise.
  funext x
  exact le_antisymm (henv_le_hull x) (hhull_le_env x)

end ERealFunction
