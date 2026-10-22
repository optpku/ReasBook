/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)

local notation "Pₛ" => metricProjection C hC_nonempty hC_closed hC_convex

/- Theorem 6.25 is `bridge/view`: the source-facing owner is the Chapter 6 set-valued projection
map `P[C]`, while under nonempty/closed/convex hypotheses the chapter's canonical point-valued
owner is Proposition 3.12's `metricProjection`. Domain sampling for this file uses the declarations

- `projection_mapping` / `mem_projection_mapping_iff` from Theorem 6.24,
- `metricProjection` / `norm_sub_metricProjection_eq_iInf` from Proposition 3.12,
- `norm_eq_iInf_iff_real_inner_le_zero` from the Hilbert projection API.

These show that the primitive data are exactly the set `C` and its nonempty/closed/convex
hypotheses; the point-valued projection is derived API and should be reused directly rather than
reconstructed through the indicator-function proximal route. -/

-- Proof sketch: let `p = metricProjection C x`. Proposition 3.12 gives directly that `p`
-- realizes the minimum distance to `C`, hence `p ∈ P[C] x`. The owner-level convex uniqueness
-- theorem `projection_mapping_subsingleton` from Theorem 6.24 then upgrades this membership to the
-- singleton identity.
/-- Theorem 6.25: first projection theorem. If `C` is a nonempty closed convex subset of a
complete real inner product space, then the projection set `P[C] x` is the singleton
containing the canonical metric projection `P_C(x)`. -/
theorem projection_mapping_eq_singleton_of_nonempty_closed_convex
    (x : E) : P[C] x = {Pp[C, hC_nonempty, hC_closed, hC_convex] x} := by
  let p : C := Pₛ x
  have hp_eq_iInf : ‖x - p‖ = ⨅ z : C, ‖x - z‖ := by
    simpa [p] using norm_sub_metricProjection_eq_iInf C hC_nonempty hC_closed hC_convex x
  have hp_mem : Pp[C, hC_nonempty, hC_closed, hC_convex] x ∈ C := by
    change (p : E) ∈ C
    exact p.2
  have h_bdd : BddBelow (Set.range fun w : C ↦ ‖x - w‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact norm_nonneg _
  have hp_proj : (p : E) ∈ P[C] x := by
    rw [mem_projection_mapping_iff, isMinOn_iff]
    constructor
    · exact hp_mem
    · intro z hz
      have h_inf_le : (⨅ w : C, ‖x - w‖) ≤ ‖x - z‖ := by
        simpa using ciInf_le h_bdd ⟨z, hz⟩
      simpa [norm_sub_rev] using le_trans hp_eq_iInf.le h_inf_le
  exact (projection_mapping_subsingleton C hC_convex x).eq_singleton_of_mem hp_proj

end
