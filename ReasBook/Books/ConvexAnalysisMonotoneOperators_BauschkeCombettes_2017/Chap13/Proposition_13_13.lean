/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_5
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem real_affine_mem_gamma (c : ℝ) :
    (fun t : ℝ ↦ ((t - c : ℝ) : EReal)) ∈ gamma ℝ := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro x y a ha0 ha1
    change (((a * x + (1 - a) * y - c : ℝ) : ℝ) : EReal) ≤
      (a : EReal) * ((x - c : ℝ) : EReal) + (1 - a : EReal) * ((y - c : ℝ) : EReal)
    exact le_of_eq <| by
      have hreal : a * x + (1 - a) * y - c = a * (x - c) + (1 - a) * (y - c) := by
        ring
      exact_mod_cast hreal
  · simpa [Function.comp] using
      (continuous_coe_real_ereal.comp (continuous_id.sub continuous_const)).lowerSemicontinuous

private theorem affineDefect_mem_gamma (f : H → EReal) (x : H) :
    (fun u : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) ∈ gamma H := by
  by_cases htop : f x = ⊤
  · have hbot_const : (fun _ : H ↦ (⊥ : EReal)) ∈ gamma H := by
      rw [mem_gamma_iff]
      refine ⟨?_, ?_⟩
      · intro y z a ha0 ha1
        simp
      · simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : H ↦ (⊥ : EReal)))
    simpa [htop] using hbot_const
  by_cases hbot : f x = ⊥
  · have htop_const : (fun _ : H ↦ (⊤ : EReal)) ∈ gamma H := by
      rw [mem_gamma_iff]
      refine ⟨?_, ?_⟩
      · intro y z a ha0 ha1
        by_cases h0 : a = 0
        · subst h0
          simp
        by_cases h1 : a = 1
        · subst h1
          rw [show (1 - (1 : ℝ) : EReal) = 0 by
                simpa using
                  EReal.sub_self (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)]
          simp
        have ha_pos : 0 < a := lt_of_le_of_ne ha0 fun h ↦ h0 h.symm
        have hb_pos : 0 < 1 - a := sub_pos.mpr (lt_of_le_of_ne ha1 h1)
        rw [EReal.mul_top_of_pos (by exact_mod_cast ha_pos),
          EReal.mul_top_of_pos (by exact_mod_cast hb_pos)]
        simp
      · simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : H ↦ (⊤ : EReal)))
    simpa [hbot] using htop_const
  have hcomp :=
    mem_gamma_comp_continuousLinearMap
      (fun t : ℝ ↦ ((t - (f x).toReal : ℝ) : EReal))
      (innerSL ℝ x)
      (real_affine_mem_gamma (f x).toReal)
  have hrewrite :
      (fun u : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) =
        fun u : H ↦ ((⟪x, u⟫_ℝ - (f x).toReal : ℝ) : EReal) := by
    ext u
    rw [← EReal.coe_toReal htop hbot]
    simp
  rw [hrewrite]
  simpa [Function.comp, innerSL_apply_apply, real_inner_comm] using hcomp

-- Proof sketch: rewrite `conjugate f` as the pointwise supremum of the affine defects
-- `u ↦ ⟪x,u⟫ - f x`. Each affine defect lies in `gamma H` because it is either constant
-- `⊥`/`⊤` or a continuous affine real functional viewed in `EReal`; Proposition 9.3 then closes
-- `gamma H` under the resulting pointwise supremum.
/-- Proposition 13.13: the Fenchel conjugate of an extended-real-valued function on a real
inner-product space belongs to the textbook class `Γ(H)` of convex lower semicontinuous
functions. -/
theorem conjugate_mem_gamma (f : H → EReal) :
    f∗ ∈ gamma H := by
  simpa [conjugate_apply] using
    iSup_mem_gamma
      (fun x u ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x)
      (affineDefect_mem_gamma f)

end ERealFunction
