/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_8_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-
Theorem 5.4.8.3 lies in the Chapter 5 self-concordant-barrier / exponential-epigraph domain.

Sampled owner declarations:
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner for closed epigraphs and their membership expansion;
* `epigraphLogBarrier_negLog_is_two_selfConcordantBarrier` from `Theorem_5_4_8_2`, the chapter
  owner for the already-established `2`-self-concordant barrier on the `-log` epigraph;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the owner-level
  affine-pullback theorem for self-concordant barriers;
* `sublevelLogBarrier` from `Theorem_5_1_4`, the canonical owner for logarithmic barrier factors
  of the form `x ↦ -log (β - f x)`;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for quantitative
  self-concordant barriers;
* mathlib `WithLp 2 (ℝ × ℝ)` from `ProdL2`, together with `WithLp.ofLp`, the canonical `L²`
  ambient owner and the public bridge back to raw pairs.

Best owner abstraction:
* source-facing: the textbook exponential epigraph `Q₂` and barrier `F₂`;
* core/canonical: `IsSelfConcordantBarrierOnWith` on the canonical product owner
  `WithLp 2 (ℝ × ℝ)`;
* bridge/view: the raw-pair owners `exponentialEpigraphQ2` and `exponentialEpigraphBarrierF2`,
  together with the affine pullback `(x, t) ↦ (t, -x)` from the `-log` epigraph of
  Theorem 5.4.8.2.

Primitive data:
* the closed epigraph inequality `t ≥ exp x`;
* the canonical `-\log` epigraph barrier owner from Theorem 5.4.8.2;
* the affine involution `(x, t) ↦ (t, -x)`.

Derived API:
* the source-facing owner `exponentialEpigraphQ2`;
* the source-facing owner `exponentialEpigraphBarrierF2`;
* the companion lemmas expanding these owners into textbook formulas;
* the affine bridge to the `-log` epigraph barrier from Theorem 5.4.8.2.

This refinement keeps the source-facing names `Q₂` and `F₂`, deletes the duplicate raw
set-builder and duplicate raw logarithmic-body definition in favor of the chapter owners
`constrainedEpigraph` and `epigraphLogBarrier`, and refines the barrier theorem itself to the
correct thin affine-pullback bridge from the earlier canonical `2`-barrier result instead of
introducing a new owner-level `3`-barrier statement. -/

/-- The exponential epigraph `Q₂ = {(x, t) ∈ ℝ² | t ≥ e^x}`. -/
def exponentialEpigraphQ2 : Set (ℝ × ℝ) :=
  constrainedEpigraph (Set.univ : Set ℝ) (fun x : ℝ ↦ (Real.exp x : WithTop ℝ))

-- Proof sketch: expand the specialized constrained epigraph owner. The feasible-set clause is
-- vacuous because the base set is `Set.univ`, so only the defining inequality remains.
/-- A pair `(x, t)` lies in `exponentialEpigraphQ2` exactly when `t ≥ e^x`. -/
theorem mem_exponentialEpigraphQ2_iff {x t : ℝ} :
    (x, t) ∈ exponentialEpigraphQ2 ↔ t ≥ Real.exp x :=
  by simp [exponentialEpigraphQ2]

/-- The function `F₂(x, t) = -log t - log (log t - x)`, defined as the affine pullback of the
canonical `-\log` epigraph barrier from Theorem 5.4.8.2. -/
def exponentialEpigraphBarrierF2 : ℝ × ℝ → ℝ :=
  fun p ↦ epigraphLogBarrier (fun y : ℝ ↦ -Real.log y) (p.2, -p.1)

/-- Evaluating `exponentialEpigraphBarrierF2` at `(x, t)` recovers
`F₂(x, t) = -log t - log (log t - x)`. -/
theorem exponentialEpigraphBarrierF2_apply (x t : ℝ) :
    exponentialEpigraphBarrierF2 (x, t) = -Real.log t - Real.log (Real.log t - x) :=
  by
    simp [exponentialEpigraphBarrierF2, epigraphLogBarrier, sublevelLogBarrier,
      sub_eq_add_neg, add_comm, add_left_comm]

local notation "Z" => WithLp 2 (ℝ × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → ℝ × ℝ)
local notation "Q₁" =>
  constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))

private def exponentialEpigraphAffine : Z →ᴬ[ℝ] Z :=
  (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap.comp
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (-ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).toContinuousLinearMap)) :
      Z →L[ℝ] Z).toContinuousAffineMap

@[simp] theorem exponentialEpigraphAffine_apply (z : Z) :
    (exponentialEpigraphAffine z).ofLp = (z.ofLp.2, -z.ofLp.1) := by
  simp [exponentialEpigraphAffine]

/-- A pair `(x, t)` lies in the interior of `exponentialEpigraphQ2` exactly when `t > e^x`. -/
theorem mem_interior_exponentialEpigraphQ2_iff {x t : ℝ} :
    (x, t) ∈ interior exponentialEpigraphQ2 ↔ t > Real.exp x := by
  constructor
  · intro h
    have hmem : (x, t) ∈ exponentialEpigraphQ2 := interior_subset h
    have hge : Real.exp x ≤ t := mem_exponentialEpigraphQ2_iff.mp hmem
    by_contra hnot
    have ht : t = Real.exp x := le_antisymm (not_lt.mp hnot) hge
    rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h) with ⟨ε, hε, hεball⟩
    have hball : (x, t - ε / 2) ∈ Metric.ball (x, t) ε := by
      have hhalf : ε / 2 < ε := by
        linarith
      have hhalf_nonneg : 0 ≤ ε / 2 := by
        linarith
      change max (dist x x) (dist (t - ε / 2) t) < ε
      rw [dist_self, Real.dist_eq, sub_sub_cancel_left, abs_of_nonpos (by linarith)]
      simpa [max_eq_right hhalf_nonneg] using hhalf
    have hmem' : (x, t - ε / 2) ∈ exponentialEpigraphQ2 := hεball hball
    have hge' : Real.exp x ≤ t - ε / 2 := mem_exponentialEpigraphQ2_iff.mp hmem'
    linarith
  · intro h
    let S : Set (ℝ × ℝ) := {p | Real.exp p.1 < p.2}
    have hSopen : IsOpen S :=
      isOpen_lt (Real.continuous_exp.comp continuous_fst) continuous_snd
    have hSsubset : S ⊆ exponentialEpigraphQ2 := by
      intro p hp
      exact mem_exponentialEpigraphQ2_iff.mpr hp.le
    have hSin : (x, t) ∈ S := h
    exact mem_interior_iff_mem_nhds.mpr <|
      Filter.mem_of_superset (IsOpen.mem_nhds hSopen hSin) hSsubset

/-- The source-facing barrier `F₂` is the pullback of the `-\log` epigraph barrier along
`(x, t) ↦ (t, -x)`. -/
theorem exponentialEpigraphBarrierF2_eq_epigraphLogBarrier_negLog_comp (x t : ℝ) :
    exponentialEpigraphBarrierF2 (x, t) =
      epigraphLogBarrier (fun y : ℝ ↦ -Real.log y) (t, -x) := by
  rfl

/-- Pulling back the `-\log` epigraph domain along `(x, t) ↦ (t, -x)` recovers the exponential
epigraph domain. -/
theorem preimage_negLogEpigraphBarrierDomain_eq_exponentialEpigraphBarrierDomain :
    exponentialEpigraphAffine ⁻¹' (ofZ ⁻¹' interior Q₁) =
      ofZ ⁻¹' interior exponentialEpigraphQ2 := by
  ext z
  change (exponentialEpigraphAffine z).ofLp ∈ interior Q₁ ↔ z.ofLp ∈ interior exponentialEpigraphQ2
  rw [exponentialEpigraphAffine_apply, mem_interior_constrainedEpigraph_negLog_iff,
    mem_interior_exponentialEpigraphQ2_iff]
  constructor
  · rintro ⟨ht, hx⟩
    have hxt : z.ofLp.1 < Real.log z.ofLp.2 := by linarith
    exact (Real.lt_log_iff_exp_lt ht).mp hxt
  · intro h
    have ht : 0 < z.ofLp.2 := lt_trans (Real.exp_pos z.ofLp.1) h
    have hxt : z.ofLp.1 < Real.log z.ofLp.2 := (Real.lt_log_iff_exp_lt ht).mpr h
    constructor
    · exact ht
    · linarith

-- Proof sketch: apply the owner affine-pullback theorem from Theorem 5.3.3 to the established
-- `2`-self-concordant barrier for the `-\log` epigraph from Theorem 5.4.8.2 using the affine
-- involution `(x, t) ↦ (t, -x)`. The domain bridge identifies the pulled-back `-\log` epigraph
-- interior with `interior exponentialEpigraphQ2`, and the barrier bridge identifies the pulled-
-- back barrier with `exponentialEpigraphBarrierF2`.
/-- Theorem 5.4.8.3: the function `F₂(x, t) = -log t - log (log t - x)` is a
`2`-self-concordant barrier for the exponential epigraph
`Q₂ = {(x, t) ∈ ℝ² | t ≥ e^x}`, viewed on the canonical `L²` product owner
`Z = WithLp 2 (ℝ × ℝ)` through `z ↦ z.ofLp`. This is the affine pullback of
Theorem 5.4.8.2 along `(x, t) ↦ (t, -x)`. -/
theorem exponentialEpigraphBarrierF2_is_two_selfConcordantBarrier :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior exponentialEpigraphQ2)
      (2 : NNReal)
      (fun z : Z ↦ exponentialEpigraphBarrierF2 z.ofLp) := by
  simpa [Function.comp,
    preimage_negLogEpigraphBarrierDomain_eq_exponentialEpigraphBarrierDomain]
    using
      epigraphLogBarrier_negLog_is_two_selfConcordantBarrier.comp_continuousAffineMap
        exponentialEpigraphAffine
