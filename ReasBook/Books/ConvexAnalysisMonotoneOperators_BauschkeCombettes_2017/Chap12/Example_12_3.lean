/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set
open scoped Pointwise

variable {H : Type u} [AddCommGroup H]

namespace ERealFunction

-- Proof sketch: if `x ∈ C + D`, choose a decomposition `x = c + d` with `c ∈ C` and `d ∈ D`, so
-- one admissible infimal-convolution value is `0`; if `x ∉ C + D`, every decomposition has either
-- `y ∉ C` or `z ∉ D`, forcing the summand to be `⊤`, hence the infimum is `⊤`.
/-- Example 12.3: the infimal convolution of the extended-real indicators of `C` and `D` is the
indicator of the Minkowski sum `C + D`. -/
theorem indicator_infimalConvolution_eq_indicator_add (C D : Set H) :
    infimalConvolution (fun x ↦ (ι[C] x : EReal)) (fun x ↦ (ι[D] x : EReal)) =
      (ι[C + D]).asEReal := by
  have hdom : dom (infimalConvolution (fun x ↦ (ι[C] x : EReal))
      (fun x ↦ (ι[D] x : EReal))) = C + D := by
    have h := dom_infimalConvolution (ι[C]) (ι[D])
    simpa using h
  ext x
  by_cases hx : x ∈ C + D
  · have hle : infimalConvolution (fun x ↦ (ι[C] x : EReal))
        (fun x ↦ (ι[D] x : EReal)) x ≤ 0 := by
      rcases hx with ⟨y, hy, z, hz, rfl⟩
      change (⨅ w : H, (ι[C] w : EReal) + (ι[D] (y + z - w) : EReal)) ≤ 0
      refine le_trans (iInf_le _ y) ?_
      simp [hy, hz]
    have hge : 0 ≤ infimalConvolution (fun x ↦ (ι[C] x : EReal))
        (fun x ↦ (ι[D] x : EReal)) x := by
      change 0 ≤ ⨅ y : H, (ι[C] y : EReal) + (ι[D] (x - y) : EReal)
      refine le_iInf ?_
      intro y
      by_cases hy : y ∈ C
      · by_cases hz : x - y ∈ D
        · simp [indicator, hy, hz]
        · simp [indicator, hy, hz]
      · have hD_ne_bot : ((ι[D] (x - y) : Set.Ioi (⊥ : EReal)) : EReal) ≠ ⊥ :=
          ne_of_gt (ι[D] (x - y)).property
        rw [show (ι[C] y : EReal) = ⊤ by simp [indicator, hy]]
        rw [EReal.top_add_of_ne_bot hD_ne_bot]
        simp
    have hzero : infimalConvolution (fun x ↦ (ι[C] x : EReal))
        (fun x ↦ (ι[D] x : EReal)) x = 0 :=
      le_antisymm hle hge
    simpa [indicator, hx] using hzero
  · have hx_not_dom : x ∉ dom (infimalConvolution (fun x ↦ (ι[C] x : EReal))
        (fun x ↦ (ι[D] x : EReal))) := by
      rw [hdom]
      exact hx
    have htop : infimalConvolution (fun x ↦ (ι[C] x : EReal))
        (fun x ↦ (ι[D] x : EReal)) x = ⊤ :=
      (not_mem_dom_iff _ _).1 hx_not_dom
    simpa [indicator, hx] using htop

end ERealFunction
