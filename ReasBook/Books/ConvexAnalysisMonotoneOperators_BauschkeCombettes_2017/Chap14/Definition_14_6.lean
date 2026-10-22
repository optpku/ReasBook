/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_34

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [Module ℝ H]

/-- The midpoint map on `H × H` sending `(y, z)` to `(y + z) / 2`. -/
def proximalAverageMidpointMap : H × H → H :=
  fun p ↦ (1 / 2 : ℝ) • (p.1 + p.2)

/-- Evaluating the midpoint map at `(y, z)` returns the midpoint `(y + z) / 2`. -/
@[simp] theorem proximalAverageMidpointMap_apply (p : H × H) :
    proximalAverageMidpointMap p = (1 / 2 : ℝ) • (p.1 + p.2) :=
  rfl

/-- The fiber kernel defining the proximal average:
`F(y, z) = (1 / 2) f(y) + (1 / 2) g(z) + (1 / 8) ‖y - z‖²`. -/
theorem proximalAverageKernel_value_mem_Ioi
    (f g : H → Set.Ioi (⊥ : EReal)) (p : H × H) :
    (((1 / 2 : ℝ) : EReal) * (f p.1 : EReal) +
        ((1 / 2 : ℝ) : EReal) * (g p.2 : EReal) +
        ((((1 / 8 : ℝ) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal))) ∈
      Set.Ioi (⊥ : EReal) := sorry

/-- The textbook proximal-average kernel on `H × H`. -/
def proximalAverageKernel (f g : H → Set.Ioi (⊥ : EReal)) :
    H × H → Set.Ioi (⊥ : EReal) :=
  fun p ↦
    ⟨(((1 / 2 : ℝ) : EReal) * (f p.1 : EReal) +
        ((1 / 2 : ℝ) : EReal) * (g p.2 : EReal) +
        ((((1 / 8 : ℝ) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal))),
      proximalAverageKernel_value_mem_Ioi f g p⟩

/-- Coercing the proximal-average kernel to `EReal` recovers the textbook formula for `F`. -/
@[simp] theorem proximalAverageKernel_apply
    (f g : H → Set.Ioi (⊥ : EReal)) (p : H × H) :
    (proximalAverageKernel f g p : EReal) =
      ((1 / 2 : ℝ) : EReal) * (f p.1 : EReal) +
        ((1 / 2 : ℝ) : EReal) * (g p.2 : EReal) +
        ((((1 / 8 : ℝ) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal)) :=
  rfl

/-- Definition 14.6: the proximal average is the infimal postcomposition of the textbook kernel
along the midpoint map. The single-variable infimum formula is the companion evaluation theorem
below. -/
def proximalAverage (f g : H → Set.Ioi (⊥ : EReal)) : H → EReal :=
  proximalAverageMidpointMap ▷ proximalAverageKernel f g

notation "pav(" f ", " g ")" => proximalAverage f g

/-- Evaluating `pav(f, g)` at `x` gives the single-variable infimum formula for the proximal
average. -/
@[simp] theorem proximalAverage_apply (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    pav(f, g) x =
      ((1 / 2 : ℝ) : EReal) *
        (⨅ y : H, (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) + ((‖x - y‖ ^ 2 : ℝ) : EReal)) :=
  sorry

end ERealFunction
