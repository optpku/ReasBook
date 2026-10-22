/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_56_1_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_7

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

namespace ERealFunction

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
  [IsTopologicalAddGroup H] [ContinuousConstSMul ℝ H]

/-- Helper for Proposition 9.8: rewrite the lower semicontinuous convex envelope as the pointwise
`iSup` over its lower semicontinuous convex minorants. -/
private theorem lowerSemicontinuousConvexEnvelope_eq_iSup_minorants (f : H → EReal) :
    lowerSemicontinuousConvexEnvelope f =
      fun x ↦ ⨆ g : {g : H → EReal // g ∈ lowerSemicontinuousConvexMinorants f}, g.1 x := by
  funext x
  rw [lowerSemicontinuousConvexEnvelope_apply]
  apply le_antisymm
  · -- Every value appearing in the `sSup` image comes from one indexed minorant.
    refine sSup_le fun y hy ↦ ?_
    rcases hy with ⟨g, hg, rfl⟩
    exact le_iSup_of_le ⟨g, hg⟩ le_rfl
  · -- Each indexed minorant contributes one value to the image whose supremum defines the envelope.
    refine iSup_le fun g ↦ ?_
    exact le_sSup ⟨g.1, g.2, rfl⟩

omit [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] in
/-- Helper for Proposition 9.8: pointwise order reverses inclusion of effective domains. -/
private theorem dom_subset_dom_of_le {g h : H → EReal} (hgh : g ≤ h) :
    dom h ⊆ dom g := by
  intro x hx
  -- Finite upper bounds for `h x` remain finite for the smaller value `g x`.
  exact lt_of_le_of_lt (hgh x) hx

omit [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] in
/-- Helper for Proposition 9.8: truncating a function to `⊤` outside `C` cuts its epigraph by the
product slab `C × ℝ`. -/
private theorem epigraph_piecewise_top_eq_inter
    (C : Set H) [DecidablePred (· ∈ C)] (g : H → EReal) :
    epigraph (fun x ↦ if x ∈ C then g x else ⊤) = epigraph g ∩ (C ×ˢ Set.univ) := by
  ext p
  rcases p with ⟨x, ξ⟩
  by_cases hx : x ∈ C
  · -- On `C`, the truncation agrees with `g`, so epigraph membership is unchanged.
    constructor
    · intro hp
      rw [mem_epigraph_iff] at hp
      rw [Set.mem_inter_iff, Set.mem_prod, mem_epigraph_iff]
      exact ⟨by simpa [hx] using hp, hx, by simp⟩
    · intro hp
      rw [Set.mem_inter_iff, Set.mem_prod, mem_epigraph_iff] at hp
      rw [mem_epigraph_iff]
      simpa [hx] using hp.1
  · -- Outside `C`, the truncated value is `⊤`, which no real height can dominate.
    constructor
    · intro hp
      rw [mem_epigraph_iff] at hp
      have htop : (⊤ : EReal) ≤ (ξ : EReal) := by
        simpa [hx] using hp
      exact False.elim (EReal.coe_ne_top ξ (top_le_iff.mp htop))
    · intro hp
      rw [Set.mem_inter_iff, Set.mem_prod] at hp
      exact False.elim (hx hp.2.1)

omit [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] in
/-- Helper for Proposition 9.8: every point of the effective domain admits a real epigraph height
above it. -/
private theorem exists_mem_epigraph_of_mem_dom (f : H → EReal) {x : H} (hx : x ∈ dom f) :
    ∃ ξ : ℝ, (x, ξ) ∈ epigraph f := by
  rw [mem_dom_iff] at hx
  rcases EReal.lt_iff_exists_real_btwn.mp hx with ⟨ξ, hfx_lt_ξ, _⟩
  refine ⟨ξ, ?_⟩
  rw [mem_epigraph_iff]
  exact le_of_lt hfx_lt_ξ

omit [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] in
/-- Helper for Proposition 9.8: a real-height epigraph point has base point in the effective
domain. -/
private theorem mem_dom_of_mem_epigraph (f : H → EReal) {x : H} {ξ : ℝ}
    (hξ : (x, ξ) ∈ epigraph f) : x ∈ dom f := by
  rw [mem_epigraph_iff] at hξ
  rw [mem_dom_iff]
  exact lt_of_le_of_lt hξ (EReal.coe_lt_top ξ)

omit [TopologicalSpace H] in
/-- Helper for Proposition 9.8: convexity of the epigraph implies convexity of the effective
domain. -/
private theorem convex_dom_of_convex_epigraph_local (f : H → EReal)
    (hconv : Convex ℝ (epigraph f)) :
    Convex ℝ (dom f) := by
  have hdom_image : dom f = (LinearMap.fst ℝ H ℝ) '' epigraph f := by
    ext x
    constructor
    · intro hx
      rcases exists_mem_epigraph_of_mem_dom f hx with ⟨ξ, hξ⟩
      exact ⟨(x, ξ), hξ, rfl⟩
    · intro hx
      rcases hx with ⟨p, hp, hp_proj⟩
      rcases p with ⟨y, ξ⟩
      have hy : y ∈ dom f := mem_dom_of_mem_epigraph f hp
      simpa using hp_proj ▸ hy
  -- Project the convex epigraph to its first coordinate.
  rw [hdom_image]
  simpa using hconv.linear_image (LinearMap.fst ℝ H ℝ)

-- Proof sketch: unfold `lowerSemicontinuousConvexEnvelope` as the pointwise supremum of
-- lower semicontinuous convex minorants and use that every indexed minorant is pointwise bounded
-- above by `f`.
/-- Proposition 9.8 (1): part (i). The lower semicontinuous convex envelope is pointwise
majorized by `f`. -/
theorem lowerSemicontinuousConvexEnvelope_le (f : H → EReal) :
    lowerSemicontinuousConvexEnvelope f ≤ f := by
  intro x
  -- After reindexing the envelope as an `iSup`, every indexed minorant is bounded by `f x`.
  rw [lowerSemicontinuousConvexEnvelope_eq_iSup_minorants]
  exact iSup_le fun g ↦ ((mem_lowerSemicontinuousConvexMinorants_iff f g.1).mp g.2).2.2 x

-- Proof sketch: rewrite the envelope as a pointwise supremum of lower semicontinuous convex
-- minorants and apply the lower-semicontinuity stability of pointwise suprema.
/-- Proposition 9.8 (2): part (i). The lower semicontinuous convex envelope is lower
semicontinuous. -/
theorem lowerSemicontinuous_lowerSemicontinuousConvexEnvelope (f : H → EReal) :
    LowerSemicontinuous (lowerSemicontinuousConvexEnvelope f) := by
  -- The envelope is the supremum of lower semicontinuous minorants, so lower semicontinuity is
  -- preserved by `lowerSemicontinuous_iSup`.
  simpa [lowerSemicontinuousConvexEnvelope_eq_iSup_minorants] using
    (lowerSemicontinuous_iSup fun g :
        {g : H → EReal // g ∈ lowerSemicontinuousConvexMinorants f} ↦
      ((mem_lowerSemicontinuousConvexMinorants_iff f g.1).mp g.2).1)

-- Proof sketch: express the envelope as the pointwise supremum of convex minorants and apply the
-- convex-epigraph stability of pointwise suprema.
/-- Proposition 9.8 (3): part (i). The epigraph of the lower semicontinuous convex envelope is
convex. -/
theorem convex_epigraph_lowerSemicontinuousConvexEnvelope (f : H → EReal) :
    Convex ℝ (epigraph (lowerSemicontinuousConvexEnvelope f)) := by
  have hEq :
      (⨆ g : {g : H → EReal // g ∈ lowerSemicontinuousConvexMinorants f}, g.1) =
        fun x ↦ ⨆ g : {g : H → EReal // g ∈ lowerSemicontinuousConvexMinorants f}, g.1 x := by
    funext x
    simp [iSup_apply]
  have hconv :
      Convex ℝ
        (epigraph (⨆ g : {g : H → EReal // g ∈ lowerSemicontinuousConvexMinorants f}, g.1)) := by
    -- Rewrite the bundled supremum epigraph as an intersection of convex epigraphs.
    rw [epigraph_iSup]
    exact convex_iInter fun g ↦ ((mem_lowerSemicontinuousConvexMinorants_iff f g.1).mp g.2).2.1
  rw [lowerSemicontinuousConvexEnvelope_eq_iSup_minorants, ← hEq]
  exact hconv

-- Proof sketch: any lower semicontinuous convex minorant of `f` belongs to the family over which
-- the envelope is defined, so its pointwise values are bounded above by the defining supremum.
/-- Proposition 9.8 (4): part (i). Every lower semicontinuous convex minorant of `f` lies below
the lower semicontinuous convex envelope. -/
theorem le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
    {f g : H → EReal} (hg_lsc : LowerSemicontinuous g) (hg_conv : Convex ℝ (epigraph g))
    (hg_le : g ≤ f) :
    g ≤ lowerSemicontinuousConvexEnvelope f := by
  intro x
  -- The given minorant is one index in the defining `iSup`.
  rw [lowerSemicontinuousConvexEnvelope_eq_iSup_minorants]
  exact le_iSup_of_le
    ⟨g, (mem_lowerSemicontinuousConvexMinorants_iff f g).mpr ⟨hg_lsc, hg_conv, hg_le⟩⟩
    le_rfl

-- Proof sketch: apply the lower-semicontinuity characterization at a point to the envelope,
-- using the previous lower-semicontinuity statement.
/-- Proposition 9.8 (5): part (ii). At every point, the lower semicontinuous convex envelope
agrees with its neighborhood liminf. -/
theorem lowerSemicontinuousConvexEnvelope_eq_liminfAt (f : H → EReal) (x : H) :
    lowerSemicontinuousConvexEnvelope f x =
      liminfAt (lowerSemicontinuousConvexEnvelope f) x := by
  apply le_antisymm
  · -- Lower semicontinuity gives the forward inequality into the liminf.
    simpa [liminfAt] using
      (lowerSemicontinuous_lowerSemicontinuousConvexEnvelope f).le_liminf x
  · -- Every neighborhood image contains the point value at `x`, so the neighborhood `sInf`s stay
    -- below that value.
    rw [liminfAt_eq_sSup_nhds_sInf]
    refine sSup_le fun y hy ↦ ?_
    rcases hy with ⟨V, hV, rfl⟩
    have hxV : x ∈ V := mem_of_mem_nhds hV
    exact sInf_le ⟨x, hxV, rfl⟩

-- Proof sketch: combine lower semicontinuity of the envelope with the closed-epigraph
-- characterization of lower semicontinuity.
/-- Proposition 9.8 (6): part (iii). The epigraph of the lower semicontinuous convex envelope is
closed. -/
theorem isClosed_epigraph_lowerSemicontinuousConvexEnvelope (f : H → EReal) :
    IsClosed (epigraph (lowerSemicontinuousConvexEnvelope f)) := by
  -- Lemma 1.24 identifies lower semicontinuity with closedness of the real-height epigraph.
  exact (lowerSemicontinuous_iff_isClosed_epigraph _).mp
    (lowerSemicontinuous_lowerSemicontinuousConvexEnvelope f)

-- Proof sketch: the convex hull of `dom f` lies in the domain of every convex minorant of `f`,
-- hence in the domain of the maximal lower semicontinuous convex minorant.
/-- Proposition 9.8 (7): part (iv). The convex hull of `dom f` is contained in the domain of the
lower semicontinuous convex envelope. -/
theorem convexHull_dom_subset_dom_lowerSemicontinuousConvexEnvelope (f : H → EReal) :
    convexHull ℝ (dom f) ⊆ dom (lowerSemicontinuousConvexEnvelope f) := by
  have hdom :
      dom f ⊆ dom (lowerSemicontinuousConvexEnvelope f) :=
    dom_subset_dom_of_le (lowerSemicontinuousConvexEnvelope_le f)
  have hconv :
      Convex ℝ (dom (lowerSemicontinuousConvexEnvelope f)) :=
    convex_dom_of_convex_epigraph_local _
      (convex_epigraph_lowerSemicontinuousConvexEnvelope f)
  -- The domain of the envelope is convex and already contains `dom f`.
  exact convexHull_min hdom hconv

/-- Helper for Proposition 9.8: outside the closed convex hull of `dom f`, the lower
semicontinuous convex envelope must take the value `⊤`. -/
private theorem lowerSemicontinuousConvexEnvelope_eq_top_of_notMem_closedConvexHull_dom
    (f : H → EReal) {x : H} (hx : x ∉ closedConvexHull ℝ (dom f)) :
    lowerSemicontinuousConvexEnvelope f x = ⊤ := by
  classical
  -- Route correction: run the truncation argument on `closedConvexHull`, whose closedness and
  -- convexity are already packaged in mathlib, and defer the rewrite to `closure (convexHull _)`
  -- until the public statement.
  let C : Set H := closedConvexHull ℝ (dom f)
  let g : H → EReal := fun y ↦ if y ∈ C then lowerSemicontinuousConvexEnvelope f y else ⊤
  have hC_closed : IsClosed C := by
    -- `closedConvexHull` is closed by construction.
    simpa [C] using isClosed_closedConvexHull (𝕜 := ℝ) (s := dom f)
  have hC_convex : Convex ℝ C := by
    -- `closedConvexHull` is convex by construction.
    simpa [C] using convex_closedConvexHull (𝕜 := ℝ) (s := dom f)
  have hg_closed : IsClosed (epigraph g) := by
    -- The truncated epigraph is the intersection of the closed epigraph with the closed slab
    -- `C × ℝ`.
    rw [epigraph_piecewise_top_eq_inter (C := C) (g := lowerSemicontinuousConvexEnvelope f)]
    exact (isClosed_epigraph_lowerSemicontinuousConvexEnvelope f).inter
      (hC_closed.prod isClosed_univ)
  have hg_lsc : LowerSemicontinuous g := by
    -- Closedness of the real-height epigraph converts back to lower semicontinuity.
    exact (lowerSemicontinuous_iff_isClosed_epigraph g).mpr hg_closed
  have hg_conv : Convex ℝ (epigraph g) := by
    -- The same epigraph identity transports convexity through the intersection.
    rw [epigraph_piecewise_top_eq_inter (C := C) (g := lowerSemicontinuousConvexEnvelope f)]
    exact (convex_epigraph_lowerSemicontinuousConvexEnvelope f).inter
      (hC_convex.prod convex_univ)
  have hdom_subset_C : dom f ⊆ C := by
    intro y hy
    exact subset_closedConvexHull hy
  have hg_le_f : g ≤ f := by
    intro y
    by_cases hy : y ∈ C
    · -- Inside `C`, the truncation agrees with the envelope, which is already a minorant of `f`.
      simpa [g, hy] using (lowerSemicontinuousConvexEnvelope_le f y)
    · -- Outside `C`, domain points of `f` are impossible, so `f y = ⊤` in the order sense.
      have hy_not_dom : y ∉ dom f := fun hy_dom ↦ hy (hdom_subset_C hy_dom)
      have htop_le : (⊤ : EReal) ≤ f y := le_of_not_gt hy_not_dom
      simpa [g, hy] using htop_le
  have hg_le_envelope : g ≤ lowerSemicontinuousConvexEnvelope f :=
    le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
      hg_lsc hg_conv hg_le_f
  have htop_le : (⊤ : EReal) ≤ lowerSemicontinuousConvexEnvelope f x := by
    -- Evaluating the maximality comparison at a point outside `C` forces the value `⊤`.
    simpa [C, g, hx] using hg_le_envelope x
  exact le_antisymm le_top htop_le

-- Proof sketch: outside `closure (convexHull ℝ (dom f))`, one truncates the convex envelope to
-- `+∞`; the resulting lower semicontinuous convex minorant is still bounded by `f`, so maximality
-- forces the envelope itself to take the value `+∞` there.
/-- Proposition 9.8 (8): part (iv). The domain of the lower semicontinuous convex envelope is
contained in the closure of the convex hull of `dom f`. -/
theorem dom_lowerSemicontinuousConvexEnvelope_subset_closure_convexHull_dom (f : H → EReal) :
    dom (lowerSemicontinuousConvexEnvelope f) ⊆ closure (convexHull ℝ (dom f)) := by
  intro x hx
  -- Route correction: follow the source truncation argument outside `closure (convexHull dom f)`
  -- by first working with `closedConvexHull`, then rewriting back at the boundary.
  by_contra hx_closure
  have hx_closedConvexHull : x ∉ closedConvexHull ℝ (dom f) := by
    simpa [closedConvexHull_eq_closure_convexHull (𝕜 := ℝ) (s := dom f)] using hx_closure
  have htop :
      lowerSemicontinuousConvexEnvelope f x = ⊤ :=
    lowerSemicontinuousConvexEnvelope_eq_top_of_notMem_closedConvexHull_dom f
      hx_closedConvexHull
  have hx_not_dom : x ∉ dom (lowerSemicontinuousConvexEnvelope f) := by
    simp [mem_dom_iff, htop]
  exact hx_not_dom hx

end ERealFunction
