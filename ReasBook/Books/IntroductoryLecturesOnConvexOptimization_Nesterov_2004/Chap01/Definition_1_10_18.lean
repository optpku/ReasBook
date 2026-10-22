/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set Topology

universe u

variable {α : Type u} [TopologicalSpace α]

/- Primary domain: barrier predicates for continuous real-valued functions on the interior of a
closed subset of a topological space.

Sampled owner-style declarations in the same domain:
* `C(interior 𝓕, ℝ)`, the canonical owner for continuous maps on the intrinsic domain;
* `TopologicalSpace.Closeds α`, the canonical mathlib owner for closed subsets;
* `liftedConeLogSumExpBarrier_restriction_isBarrierFunctionOn` in `Chap05/Theorem_5_4_7_7`,
  which expresses the same frontier growth condition after passing to the normalization-nesterovHyperplane
  relative ambient space;
* `IsSelfConcordantBarrierOnWith dom ν F` in `Chap05/Definition_5_3_2`, which keeps the owner
  function central and pushes auxiliary assumptions into parent structure data.

Best owner abstraction:
* source-facing: `IsBarrierFunctionOn 𝓕 F`;
* core/canonical: the bundled owner map `F : C(interior 𝓕, ℝ)`;
* bridge/view: the closed-set hypothesis should be carried canonically as a parent assumption,
  not repeated as a bespoke field, while the interior nonemptiness and frontier-divergence data
  remain part of the source-facing notion.

Primitive data:
* `Fact (IsClosed 𝓕)`;
* `(interior 𝓕).Nonempty`;
* the frontier growth condition for the owner map.

Derived API:
* `hF.isClosed : IsClosed 𝓕`;
* `hF.interior_ne_empty : interior 𝓕 ≠ ∅`. -/

/-- Definition 1.10.18: a barrier function for `𝓕` is a bundled continuous map
`F : C(interior 𝓕, ℝ)` on the interior of a closed set `𝓕` with nonempty interior, such that the
values of `F` along every sequence in `interior 𝓕` converging to a boundary point of `𝓕` tend to
`+∞`. The owner object is the continuous map on `interior 𝓕`; the closedness and nonempty-interior
hypotheses remain part of the public predicate because they are part of the textbook notion. -/
class IsBarrierFunctionOn (𝓕 : Set α) (F : C(interior 𝓕, ℝ)) : Prop
    extends Fact (IsClosed 𝓕) where
  interior_nonempty : (interior 𝓕).Nonempty
  tendsTo_atTop_of_tendsto_frontier (x : ℕ → interior 𝓕) {xBar : α}
      (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
      (hxBar : xBar ∈ frontier 𝓕) :
      Tendsto (fun k ↦ F (x k)) atTop atTop

attribute [instance] IsBarrierFunctionOn.toFact

namespace IsBarrierFunctionOn

theorem isClosed {𝓕 : Set α} {F : C(interior 𝓕, ℝ)}
    (hF : IsBarrierFunctionOn 𝓕 F) :
    IsClosed 𝓕 := by
  let _ : IsBarrierFunctionOn 𝓕 F := hF
  exact Fact.out

theorem interior_ne_empty {𝓕 : Set α} {F : C(interior 𝓕, ℝ)}
    (hF : IsBarrierFunctionOn 𝓕 F) :
    interior 𝓕 ≠ ∅ :=
  hF.interior_nonempty.ne_empty

end IsBarrierFunctionOn
