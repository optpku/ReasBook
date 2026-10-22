/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_3_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Theorem 5.4.8.2 lies in the chapter's logarithmic-barrier / epigraph-lifting domain.

Sampled owner declarations:
* `negLog_isSelfConcordantBarrierOnWith_nonnegativeRay` in `Example_5_3_1_3`, the scalar owner
  for the base barrier `x ↦ -log x`;
* `epigraphLogBarrier_isSelfConcordantBarrierOnWith` in `Theorem_5_3_5`, the chapter owner for
  lifting a barrier to the strict epigraph on the canonical `WithLp 2 (E × ℝ)` product;
* mathlib `WithLp 2 (ℝ × ℝ)` together with `WithLp.ofLp`, the canonical `L²` ambient owner and
  the public bridge back to the textbook raw pairs;
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` in `Chap03/Definition_3_3`, the
  chapter owner for the closed epigraph from Definition 5.4.8.5;
* `strictConstrainedEpigraph` and `epigraphLogBarrier` in `Theorem_5_3_5`, the source-facing
  strict-epigraph and lifted-barrier owners reused by the specialization below.

Best owner abstraction:
* source-facing: the interior of the closed epigraph from Definition 5.4.8.5;
* core/canonical: the lifted barrier owner
  `epigraphLogBarrier_isSelfConcordantBarrierOnWith`;
* bridge/view: the interior-identification theorem below, which rewrites the closed epigraph
  interior as the corresponding strict epigraph.

Primitive data:
* the base logarithmic barrier `x ↦ -Real.log x`;
* the closed epigraph owner
  `constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))`.

Derived API:
* the source-facing interior membership theorem;
* the specialized lifted barrier statement for the canonical epigraph logarithmic barrier.

The file therefore keeps the source-facing interior statement, but the barrier theorem is intended
to be a thin specialization of the chapter owners for the scalar `-log` barrier and epigraph
lifting, rather than a second local barrier construction. -/

local notation "Z" => WithLp 2 (ℝ × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → ℝ × ℝ)
local notation "Q₁" =>
  constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))

-- Proof sketch: the interior of the canonical closed epigraph from Definition 5.4.8.5 is
-- obtained by replacing the boundary inequality `t ≥ -\log x` with the strict inequality
-- `t > -\log x` while keeping `x > 0`.
/-- A point lies in the interior of the canonical epigraph for Definition 5.4.8.5 exactly when
`x > 0` and `t > -\log x`. -/
theorem mem_interior_constrainedEpigraph_negLog_iff {x t : ℝ} :
    (x, t) ∈ interior Q₁ ↔ 0 < x ∧ t > -Real.log x := by
  constructor
  · intro h
    have hQ : (x, t) ∈ Q₁ := interior_subset h
    rw [mem_constrainedEpigraph_negLog_iff] at hQ
    -- Interior points of the closed epigraph keep the positivity constraint `x > 0`.
    have hx : 0 < x := hQ.1
    -- Moving only downward in the second coordinate rules out the boundary case
    -- `t = -log x`.
    have ht : t > -Real.log x := by
      by_contra hnot
      have hle : t ≤ -Real.log x := le_of_not_gt hnot
      have heq : t = -Real.log x := le_antisymm hle hQ.2
      let γ : ℝ → ℝ × ℝ := fun s ↦ (x, s)
      have hγ : Continuous γ := by
        simpa [γ] using (Continuous.prodMk continuous_const continuous_id)
      have hpre : γ ⁻¹' interior Q₁ ∈ nhds t := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      have hdown : t - ε / 2 ∈ Metric.ball t ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hneg : t - ε / 2 - t < 0 := by
          linarith
        rw [abs_of_neg hneg]
        linarith
      have hmem : γ (t - ε / 2) ∈ interior Q₁ := hεsub hdown
      have hQdown : γ (t - ε / 2) ∈ Q₁ := interior_subset hmem
      rw [mem_constrainedEpigraph_negLog_iff] at hQdown
      have hbound : -Real.log x ≤ t - ε / 2 := by
        simpa [γ] using hQdown.2
      rw [heq] at hbound
      linarith
    exact ⟨hx, ht⟩
  · rintro ⟨hx, ht⟩
    let φ : ℝ × ℝ → ℝ := fun q ↦ q.2 + Real.log q.1
    -- Positivity of the first coordinate stays open around `(x, t)`.
    have hx_mem : Prod.fst ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds (x, t) :=
      continuousAt_fst.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx)
    -- The strict epigraph gap is also open because `log` is continuous on `(0, ∞)`.
    have hφ_cont : ContinuousAt φ (x, t) := by
      have hlog : ContinuousAt (fun q : ℝ × ℝ ↦ Real.log q.1) (x, t) := by
        have hxcoord : ContinuousAt (fun q : ℝ × ℝ ↦ q.1) (x, t) := continuousAt_fst
        simpa [Function.comp] using (Real.continuousAt_log hx.ne').comp hxcoord
      simpa [φ] using continuousAt_snd.add hlog
    have hφ_pos : 0 < φ (x, t) := by
      dsimp [φ]
      linarith
    have hgap : φ ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds (x, t) :=
      hφ_cont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hφ_pos)
    have hnhds : Q₁ ∈ nhds (x, t) := by
      refine Filter.mem_of_superset (Filter.inter_mem hx_mem hgap) ?_
      rintro y ⟨hyx, hygap⟩
      rw [mem_constrainedEpigraph_negLog_iff]
      refine ⟨hyx, ?_⟩
      have hygap' : 0 < y.2 + Real.log y.1 := by
        simpa [φ] using hygap
      linarith
    exact mem_interior_iff_mem_nhds.mpr hnhds

-- Proof sketch: first rewrite the interior of the canonical closed epigraph from
-- Definition 5.4.8.5 as the strict epigraph of `x ↦ -\log x` via
-- `mem_interior_constrainedEpigraph_negLog_iff`. Then specialize the scalar owner
-- `negLog_isSelfConcordantBarrierOnWith_nonnegativeRay` and the canonical epigraph-lifting owner
-- `epigraphLogBarrier_isSelfConcordantBarrierOnWith`; since the scalar barrier parameter is `1`,
-- the lifted epigraph barrier has the exact source parameter `1 + 1 = 2`.
/-- Theorem 5.4.8.2: the canonical epigraph logarithmic barrier specialized to `x ↦ -\log x`,
namely `F₁(x, t) = -\log x - \log (\log x + t)`, is a `2`-self-concordant barrier for the
canonical epigraph of Definition 5.4.8.5, viewed on the canonical `L²` product owner
`Z = WithLp 2 (ℝ × ℝ)` through `z ↦ z.ofLp`. -/
theorem epigraphLogBarrier_negLog_is_two_selfConcordantBarrier :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior Q₁)
      (2 : NNReal)
      (epigraphLogBarrier (fun x : ℝ ↦ -Real.log x) ∘ ofZ) := by
  have hQ₁ :
      interior Q₁ = strictConstrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -Real.log x) := by
    ext z
    rcases z with ⟨x, t⟩
    rw [mem_strictConstrainedEpigraph_iff]
    simpa [gt_iff_lt] using
      (show (x, t) ∈ interior Q₁ ↔ 0 < x ∧ t > -Real.log x from
        mem_interior_constrainedEpigraph_negLog_iff)
  have hν : (1 : NNReal) + 1 = 2 := by
    norm_num
  simpa [hQ₁, hν] using
    (epigraphLogBarrier_isSelfConcordantBarrierOnWith
      negLog_isSelfConcordantBarrierOnWith_nonnegativeRay)
