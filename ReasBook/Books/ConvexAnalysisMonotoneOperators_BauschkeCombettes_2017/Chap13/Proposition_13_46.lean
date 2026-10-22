/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Corollary_9_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_45

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem convex_epigraph_of_isConvex {f : H → EReal} (hconv : IsConvex f) :
    Convex ℝ (epigraph f) := by
  refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
  intro x y hx hy a ha0 ha1
  exact hconv ha0.le ha1.le

-- Proof sketch: rewrite `f∗∗` using Proposition 13.46, then apply the Chapter 1 hull-domain
-- inclusions.
/-- Proposition 13.46 (1), left inclusion: if the Fenchel conjugate of an extended-real-valued
function on a real Hilbert space has nonempty domain, then the domain of `f` is contained in the
domain of `f∗∗`. -/
theorem dom_subset_dom_biconjugate_of_dom_conjugate_nonempty
    {f : H → EReal} (hdom : (dom f∗).Nonempty) :
    dom f ⊆ dom f∗∗ := by
  simpa [biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty f hdom] using
    (show dom f ⊆ dom (lowerSemicontinuousConvexEnvelope f) from
      (subset_convexHull ℝ (dom f)).trans
        (convexHull_dom_subset_dom_lowerSemicontinuousConvexEnvelope f))

-- Proof sketch: rewrite `f∗∗` using Proposition 13.46, then apply the Chapter 1 hull-domain
-- closure bound.
/-- Proposition 13.46 (1), right inclusion: for a convex extended-real-valued function on a real
Hilbert space whose Fenchel conjugate has nonempty domain, the domain of `f∗∗` is contained in the
closure of the domain of `f`. -/
theorem dom_biconjugate_subset_closure_dom_of_isConvex_of_dom_conjugate_nonempty
    {f : H → EReal} (hconv : IsConvex f) (hdom : (dom f∗).Nonempty) :
    dom f∗∗ ⊆ closure (dom f) := by
  have hdom_conv : Convex ℝ (dom f) :=
    convex_dom_of_convex_epigraph f (convex_epigraph_of_isConvex hconv)
  calc
    dom f∗∗ ⊆ closure (convexHull ℝ (dom f)) := by
      simpa [biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty f hdom]
        using dom_lowerSemicontinuousConvexEnvelope_subset_closure_convexHull_dom f
    _ = closure (dom f) := by rw [hdom_conv.convexHull_eq]

-- Proof sketch: rewrite `f∗∗` via Proposition 13.45 and then use the owner-level epigraph formula
-- from Theorem 9.9; convexity identifies `convexHull ℝ (epigraph f)` with `epigraph f`.
/-- Proposition 13.46 (2): for a convex extended-real-valued function on a real Hilbert space
whose Fenchel conjugate has nonempty domain, equivalently which admits a continuous affine
minorant, the epigraph of `f∗∗` is the closure of the epigraph of `f`. -/
theorem epigraph_biconjugate_eq_closure_epigraph_of_isConvex_of_dom_conjugate_nonempty
    {f : H → EReal} (hconv : IsConvex f) (hdom : (dom f∗).Nonempty) :
    epigraph f∗∗ = closure (epigraph f) := by
  calc
    epigraph f∗∗ = epigraph (lowerSemicontinuousConvexEnvelope f) := by
      simp [biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty f hdom]
    _ = closure (convexHull ℝ (epigraph f)) :=
      epigraph_lowerSemicontinuousConvexEnvelope_eq_closure_convexHull_epigraph f
    _ = closure (epigraph f) := by
      rw [(convex_epigraph_of_isConvex hconv).convexHull_eq]

-- Proof sketch: Proposition 13.45 gives the lower semicontinuous convex envelope, Corollary 9.10
-- replaces it by the lower semicontinuous envelope for convex `f`, and Lemma 1.32 identifies that
-- envelope with `liminfAt`.
/-- Proposition 13.46 (3): for a convex extended-real-valued function on a real Hilbert space
whose Fenchel conjugate has nonempty domain, equivalently which admits a continuous affine
minorant, the Fenchel biconjugate agrees pointwise with `liminfAt f`. -/
theorem biconjugate_eq_liminfAt_of_isConvex_of_dom_conjugate_nonempty
    {f : H → EReal} (hconv : IsConvex f) (hdom : (dom f∗).Nonempty) (x : H) :
    f∗∗ x = liminfAt f x := by
  calc
    f∗∗ x = lowerSemicontinuousConvexEnvelope f x := by
      rw [biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty f hdom]
    _ = lowerSemicontinuousEnvelope f x := by
      rw [lowerSemicontinuousConvexEnvelope_eq_lowerSemicontinuousEnvelope_of_convex_epigraph f
        (convex_epigraph_of_isConvex hconv)]
    _ = liminfAt f x := lowerSemicontinuousHull_eq_liminfAt f x

end Conjugation

end ERealFunction
