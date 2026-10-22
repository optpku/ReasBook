/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Definition_19_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section ParametricDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

-- Proof sketch: rewrite `v ∈ Argmin (perturbationDualObjective F)` as minimization of the dual
-- objective. Then apply Proposition 19.17(iv) to rewrite each dual objective value `F^*(0, w)` as
-- the negative of the infimum of the Lagrangian fiber over `H`, and convert minimizing
-- `F^*(0, ·)` into maximizing `w ↦ inf_x ℒ[F] x w`.
/-- Corollary 19.18: a point `v` minimizes the dual objective exactly when the infimum of the
Lagrangian
fiber `x ↦ ℒ[F] x v` equals the supremum over `w` of the infima of the fibers
`x ↦ ℒ[F] x w`. -/
theorem mem_argmin_perturbationDualObjective_iff_lagrangian_sInf_eq_sSup
    (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) :
    v ∈ Argmin (perturbationDualObjective F) ↔
      sInf (Set.range fun x ↦ ℒ[F] x v) =
        sSup (Set.range fun w ↦ sInf (Set.range fun x ↦ ℒ[F] x w)) := by
  have hsSup :
      sSup (Set.range fun w ↦ sInf (Set.range fun x ↦ ℒ[F] x w)) =
        -sInf (Set.range (perturbationDualObjective F)) := by
    have hnegImage :
        ((-·) '' Set.range (fun w ↦ -perturbationDualObjective F w)) =
          Set.range (perturbationDualObjective F) := by
      ext z
      constructor
      · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
        exact ⟨w, by simp⟩
      · rintro ⟨w, rfl⟩
        refine ⟨-perturbationDualObjective F w, ?_, by simp⟩
        exact ⟨w, by simp⟩
    rw [show
        Set.range (fun w ↦ sInf (Set.range fun x ↦ ℒ[F] x w)) =
          Set.range (fun w ↦ -perturbationDualObjective F w) by
        ext z
        constructor
        · rintro ⟨w, rfl⟩
          exact ⟨w, (lagrangian_sInf_eq_neg_perturbationDualObjective F w).symm⟩
        · rintro ⟨w, rfl⟩
          exact ⟨w, lagrangian_sInf_eq_neg_perturbationDualObjective F w⟩,
      EReal.sSup_eq_neg_sInf_image_neg, hnegImage]
  rw [mem_argmin_iff_eq_sInf]
  constructor
  · intro hv
    rw [hsSup, lagrangian_sInf_eq_neg_perturbationDualObjective F v, hv]
  · intro hv
    rw [hsSup, lagrangian_sInf_eq_neg_perturbationDualObjective F v] at hv
    have hdual :
        perturbationDualObjective F v =
          sInf (Set.range (perturbationDualObjective F)) := by
      simpa using congrArg Neg.neg hv
    exact hdual

end ParametricDuality

end ERealFunction
