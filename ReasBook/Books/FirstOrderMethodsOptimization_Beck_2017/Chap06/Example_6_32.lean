/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_13
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp

section

variable {ι : Type*} [Fintype ι]

local notation "E" => ι → ℝ

/-
Example 6.32 is `bridge/view` in the Chapter 6 projection domain. The core owners are the
set-valued projection map `P[...]`, the box owner `Box[ℓ,u]`, and the Chapter 1 canonical
half-space/hyperplane owners on the canonical Euclidean space `EuclideanSpace ℝ ι`,
transported back to coordinates through the bridge owners `coordinateHalfSpace` and
`coordinateHyperplane`. The scalar formulas `aᵀ y ≤ b` and `aᵀ y = b` are derived coordinate
views, so the target statements should use those owner sets directly rather than raw pullback
syntax.
-/

-- Proof sketch: if the box projection set already lies in the coordinate half-space
-- `coordinateHalfSpace a b`,
-- then all box minimizers are feasible for the smaller problem, and no point in the intersection
-- can improve the distance beyond the box minimum.
/-- Example 6.32, feasible branch: if the box projection `P[Box[ℓ,u]] x` already lies in the
coordinate closed half-space `coordinateHalfSpace a b`, then projecting onto the intersection with
the box does not change the projected set. This is the finite-index owner-level form, matching
the Chapter 1 half-space owner and the Chapter 6 box owner directly rather than a
numbered-coordinate model. -/
theorem projection_mapping_halfSpace_inter_box_eq_box_projection_mapping_of_projection_subset
    (a : E) (b : ℝ) (l u : ι → EReal)
    (x : E)
    (hfeas : P[Box[l,u]] x ⊆ coordinateHalfSpace a b) :
    P[(coordinateHalfSpace a b ∩ Box[l,u])] x =
      P[Box[l,u]] x := by
  by_cases hbox : (Box[l,u] : Set E).Nonempty
  · letI : ProperSpace E := FiniteDimensional.proper ℝ E
    have hproj_nonempty : (P[Box[l,u]] x).Nonempty :=
      projection_mapping_nonempty_of_nonempty_isClosed (Box[l,u]) hbox (isClosed_box l u) x
    simpa [Set.inter_comm] using
      projection_mapping_inter_eq_of_projection_mapping_subset
        (Box[l,u]) (coordinateHalfSpace a b) x hproj_nonempty hfeas
  · have hbox_empty : (Box[l,u] : Set E) = ∅ := Set.not_nonempty_iff_eq_empty.mp hbox
    simp [hbox_empty]

/- Example 6.32, active-constraint branch: the owner-level statement already appears as the
canonical hyperplane-box projection identity below, so this file reuses that theorem directly
rather than keeping a parallel local wrapper with a redundant positivity binder. -/
recall projection_mapping_hyperplane_inter_box_eq_shifted_box_projection_mapping

end
