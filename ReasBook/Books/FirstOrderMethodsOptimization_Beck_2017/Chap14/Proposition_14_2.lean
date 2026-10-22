/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open scoped BigOperators

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable (f : ((i : Fin p) → Ei i) → EReal)
variable (g : (i : Fin p) → Ei i → EReal)
variable (xk xNext : (i : Fin p) → Ei i) (i : Fin p)

/- Proposition 14.2 is `bridge/view`: the source-facing content is the equivalence between the
full composite block step and the displayed one-block objective. The Chapter 14 owner of the
displayed subproblem is already `alternating_minimization_composite_block_objective`, built from
the core owners `alternating_minimization_block_objective`, `composite_model_objective`, and
`separableSum`. -/

-- Proof sketch: unfold the full block slice of `composite_model_objective f (separableSum g)`,
-- split the finite sum `separableSum g` into the active term `g_i(xi)` and the erased inactive
-- sum, and simplify the mixed state away from the active block.
/-- The full block slice of the composite objective decomposes into the displayed one-block owner
from Algorithm 14.3 plus the frozen sum of the inactive penalties. -/
theorem alternating_minimization_block_objective_composite_model_eq_add_inactive_penalty :
    alternating_minimization_block_objective
        (composite_model_objective f (separableSum g))
        xk
        xNext
        i =
      fun xi ↦
        alternating_minimization_composite_block_objective f g xk xNext i xi +
          (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)) := by
  funext xi
  rw [alternating_minimization_block_objective_apply,
    composite_model_objective_apply, separableSum_apply,
    alternating_minimization_composite_block_objective_apply]
  calc
    f (alternating_minimization_partial_state xk xNext i xi) +
        ∑ j, g j (alternating_minimization_partial_state xk xNext i xi j) =
      f (alternating_minimization_partial_state xk xNext i xi) +
        (g i (alternating_minimization_partial_state xk xNext i xi i) +
          ∑ j ∈ Finset.univ.erase i,
            g j (alternating_minimization_partial_state xk xNext i xi j)) := by
          rw [show
            (∑ j, g j (alternating_minimization_partial_state xk xNext i xi j)) =
              g i (alternating_minimization_partial_state xk xNext i xi i) +
                ∑ j ∈ Finset.univ.erase i,
                  g j (alternating_minimization_partial_state xk xNext i xi j) by
                symm
                exact Finset.add_sum_erase Finset.univ
                  (fun j ↦ g j (alternating_minimization_partial_state xk xNext i xi j))
                  (Finset.mem_univ i)]
    _ =
      f (alternating_minimization_partial_state xk xNext i xi) + g i xi +
        ∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j) := by
          have hsum :
              ∑ j ∈ Finset.univ.erase i,
                g j (alternating_minimization_partial_state xk xNext i xi j) =
                ∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
                  simp [alternating_minimization_partial_state, Function.update, hji]
          rw [hsum]
          simp [alternating_minimization_partial_state, add_assoc]

-- Proof sketch: if the displayed active term at the old block and the frozen inactive penalty sum
-- are both non-`⊥`, while the mixed old state lies in the effective domain of the full composite
-- objective, then the decomposition theorem above gives a sum `< ⊤`. The inactive penalty term
-- therefore cannot be `⊤`, so it is a genuine real constant and agrees with its `toReal`
-- coercion.
/-- If the frozen inactive penalty sum is not `⊥`, the displayed active term at the old block is
not `⊥`, and the mixed old state lies in the effective domain of the full composite objective,
then the frozen inactive penalty sum is finite. -/
theorem inactive_penalty_eq_coe_toReal_of_ne_bot_of_mem_effective_domain
    (hinactive_ne_bot :
      (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)) ≠ ⊥)
    (hactive_ne_bot :
      alternating_minimization_composite_block_objective f g xk xNext i (xk i) ≠ ⊥)
    (hstate :
      alternating_minimization_partial_state xk xNext i (xk i) ∈
        effective_domain (composite_model_objective f (separableSum g))) :
    (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)) =
      (((∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)).toReal : ℝ) :
        EReal) := by
  let inactivePenalty : EReal :=
    ∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)
  have hinactive_ne_bot : inactivePenalty ≠ ⊥ := by
    simpa [inactivePenalty] using hinactive_ne_bot
  let stateOld : (j : Fin p) → Ei j := alternating_minimization_partial_state xk xNext i (xk i)
  have hdisplay_ne_bot :
      alternating_minimization_composite_block_objective f g xk xNext i (xk i) ≠ ⊥ :=
    hactive_ne_bot
  have hsum_top :
      alternating_minimization_composite_block_objective f g xk xNext i (xk i) + inactivePenalty <
        ⊤ := by
    have hstate_top :
        composite_model_objective f (separableSum g) stateOld < ⊤ :=
      mem_effective_domain.mp hstate
    calc
      alternating_minimization_composite_block_objective f g xk xNext i (xk i) + inactivePenalty =
          alternating_minimization_block_objective
            (composite_model_objective f (separableSum g))
            xk
            xNext
            i
            (xk i) := by
              simpa [inactivePenalty] using
                (congrFun
                  (alternating_minimization_block_objective_composite_model_eq_add_inactive_penalty
                    f g xk xNext i)
                  (xk i)).symm
      _ = composite_model_objective f (separableSum g) stateOld := by
        simp [alternating_minimization_block_objective_apply, stateOld]
      _ < ⊤ := hstate_top
  have hinactive_top : inactivePenalty < ⊤ := by
    refine lt_top_iff_ne_top.mpr ?_
    intro hinactive_eq_top
    exact (lt_top_iff_ne_top.mp hsum_top) <|
      by rw [hinactive_eq_top, EReal.add_top_of_ne_bot hdisplay_ne_bot]
  exact (EReal.coe_toReal (lt_top_iff_ne_top.mp hinactive_top) hinactive_ne_bot).symm

-- Proof sketch: apply the exact decomposition theorem above and replace the frozen inactive
-- penalty sum by its canonical `toReal` coercion using the explicit finiteness hypothesis. Both
-- objectives then differ by pointwise addition of the same finite constant, which
-- `EReal.addLECancellable_coe` cancels in the `IsMinOn` inequalities.
/-- Proposition 14.2: if the frozen inactive penalty sum is finite, then the full block subproblem
and the displayed one-block objective have the same minimizers. -/
theorem isMinOn_alternating_minimization_full_objective_iff_isMinOn_composite_block_objective
    (hinactive :
      (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)) =
        (((∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)).toReal : ℝ) :
          EReal))
    (xi : Ei i) :
    IsMinOn
      (alternating_minimization_block_objective
        (composite_model_objective f (separableSum g))
        xk
        xNext
        i)
        Set.univ
        xi ↔
    IsMinOn
      (alternating_minimization_composite_block_objective f g xk xNext i)
      Set.univ
      xi := by
  let inactivePenalty : EReal :=
    ∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)
  have hinactive :
      inactivePenalty = (((inactivePenalty.toReal : ℝ) : EReal)) := by
    simpa [inactivePenalty] using hinactive
  have hinactive_coe :
      (((inactivePenalty.toReal : ℝ) : EReal)) = inactivePenalty :=
    hinactive.symm
  have hfull_eval (yi : Ei i) :
      alternating_minimization_block_objective
          (composite_model_objective f (separableSum g))
          xk
          xNext
          i
          yi =
        alternating_minimization_composite_block_objective f g xk xNext i yi +
          (((inactivePenalty.toReal : ℝ) : EReal)) := by
    calc
      alternating_minimization_block_objective
          (composite_model_objective f (separableSum g))
          xk
          xNext
          i
          yi =
        alternating_minimization_composite_block_objective f g xk xNext i yi +
          inactivePenalty := by
            simpa using congrFun
              (alternating_minimization_block_objective_composite_model_eq_add_inactive_penalty
                f g xk xNext i) yi
      _ = alternating_minimization_composite_block_objective f g xk xNext i yi +
            (((inactivePenalty.toReal : ℝ) : EReal)) := by
        rw [hinactive_coe]
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro h yi hy
    have hy' := h yi hy
    rw [hfull_eval xi, hfull_eval yi] at hy'
    exact ((EReal.addLECancellable_coe inactivePenalty.toReal).add_le_add_iff_right).mp hy'
  · intro h yi hy
    have hy' :
        alternating_minimization_composite_block_objective f g xk xNext i xi +
            (((inactivePenalty.toReal : ℝ) : EReal)) ≤
          alternating_minimization_composite_block_objective f g xk xNext i yi +
            (((inactivePenalty.toReal : ℝ) : EReal)) := by
      exact ((EReal.addLECancellable_coe inactivePenalty.toReal).add_le_add_iff_right).mpr
        (h yi hy)
    rw [← hfull_eval xi, ← hfull_eval yi] at hy'
    exact hy'

end

end
