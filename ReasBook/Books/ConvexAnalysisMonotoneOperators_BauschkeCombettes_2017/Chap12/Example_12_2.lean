/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

open ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

namespace ERealFunction

-- Proof sketch: compare the source-faithful `EReal` infimum over `C` with the canonical
-- extended distance `Metric.infEDist`.
/-- The source-facing extended-real distance to `C` is the `EReal` infimum of the translated
norm over `C`. -/
theorem distanceToSet_eq_sInf_norm_image (C : Set H) :
    (fun x ↦ (Metric.infEDist x C : EReal)) =
      fun x ↦ sInf ((fun y : H ↦ (‖x - y‖ : EReal)) '' C) := sorry

-- Proof sketch: unfold the infimal convolution of `ι[C]` and `(fun x ↦ ‖x‖).toEReal`; points
-- outside `C` contribute `⊤`, while points in `C` contribute exactly `‖x - y‖`, so the defining
-- infimum reduces to the extended-real distance to `C`.
/-- Example 12.2: the distance to `C` is the infimal convolution of the indicator of `C` with the
norm. -/
theorem distanceToSet_eq_indicator_infimalConvolution_norm (C : Set H) :
    (fun x ↦ (Metric.infEDist x C : EReal)) = ι[C] □ scaledNormKernel (1 : NNReal) := sorry

section

variable [NormedSpace ℝ H]

-- Proof sketch: exactness at `x` would produce some `y ∈ C` that attains the distance from `x` to
-- `C`. In a real normed vector space, every point of an open set can be moved slightly along the
-- segment toward an exterior point `x` while staying in `C`, which strictly decreases the norm;
-- hence no minimizer exists outside `C` when `C` is nonempty.
/-- In a real normed vector space, if `C` is nonempty and open, then the infimal convolution of
its indicator with the norm is never exact at points outside `C`. -/
theorem indicator_infimalConvolution_norm_not_exact_of_nonempty_isOpen
    (C : Set H) (hC : C.Nonempty) (hopen : IsOpen C) {x : H} (hx : x ∉ C) :
    ¬ infimalConvolution.ExactAt (ι[C]) (scaledNormKernel (1 : NNReal)) x := sorry

end

-- Proof sketch: choose any point `c ∈ C`; then the admissible decomposition through `c` gives a
-- finite upper bound on the infimal convolution at every `x`, so every point lies in the domain.
/-- For a nonempty set, the infimal convolution of its indicator with the norm has full domain. -/
theorem dom_indicator_infimalConvolution_norm_eq_univ_of_nonempty
    (C : Set H) (hC : C.Nonempty) :
    dom (ι[C] □ scaledNormKernel (1 : NNReal)) = Set.univ := sorry

end ERealFunction
