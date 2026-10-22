/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20_Core

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- Definition 12.20: the Moreau envelope of parameter `γ ∈ ℝ_{++}` is the infimal convolution
of `f` with the quadratic kernel `x ↦ (1 / (2γ)) ‖x‖^2`. The source-facing Lean notation is
`{}^[γ] f`. -/
noncomputable abbrev moreauEnvelope {α : Type*} [CoeTC α EReal] (f : H → α)
    (γ : Set.Ioi (0 : ℝ)) :
    H → EReal :=
  f □ moreauQuadraticKernel γ

notation:max "{}^[" γ:max "]" f:max => ERealFunction.moreauEnvelope f γ

/-- The Moreau envelope is computed by infimizing the translated sums
`f y + (1 / (2γ)) ‖x - y‖^2`. -/
-- Proof sketch: unfold `moreauEnvelope`, expand the defining formula for `infimalConvolution`,
-- and rewrite the kernel term with `moreauQuadraticKernel_apply`.
theorem moreauEnvelope_apply {α : Type*} [CoeTC α EReal] (f : H → α)
    (γ : Set.Ioi (0 : ℝ)) (x : H) :
    ({}^[γ] f) x =
      ⨅ y : H, (f y : EReal) + ((((1 / (2 * (γ : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
  simp [moreauEnvelope, infimalConvolution_apply]

end ERealFunction
