/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Definition 3.7: the book's relative interior is the canonical convex-geometry notion
`intrinsicInterior ℝ`.
-/
recall intrinsicInterior
recall mem_intrinsicInterior

/-
The closed-ball membership criterion below is a `bridge/view` theorem. Its `core/canonical`
owner is mathlib's `mem_intrinsicInterior`, and the theorem merely rewrites that owner statement
into the textbook metric characterization inside the affine span.
-/
/-- A point lies in the intrinsic interior of `s` exactly when it belongs to the affine hull of `s`
and some positive closed ball around it, intersected with that affine hull, is contained in `s`.
This is the textbook closed-ball characterization of relative interior. -/
theorem mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset {s : Set E} {x : E} :
    x ∈ intrinsicInterior ℝ s ↔
      x ∈ affineSpan ℝ s ∧
        ∃ ε > 0, Metric.closedBall x ε ∩ affineSpan ℝ s ⊆ s := by
  constructor
  · intro hx
    rcases mem_intrinsicInterior.1 hx with ⟨y, hy, rfl⟩
    rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy) with ⟨ε, hε, hεs⟩
    refine ⟨y.property, ε / 2, half_pos hε, ?_⟩
    intro z hz
    exact hεs <| Metric.closedBall_subset_ball (half_lt_self hε) <| by
      change (⟨z, hz.2⟩ : affineSpan ℝ s) ∈ Metric.closedBall y (ε / 2)
      simpa using hz.1
  · rintro ⟨hx, ε, hε, hεs⟩
    refine mem_intrinsicInterior.2 ?_
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    refine mem_interior_iff_mem_nhds.2 <|
      Filter.mem_of_superset (Metric.closedBall_mem_nhds _ hε) fun y hy ↦
        hεs <| by
          refine ⟨?_, y.property⟩
          simpa using hy

end
