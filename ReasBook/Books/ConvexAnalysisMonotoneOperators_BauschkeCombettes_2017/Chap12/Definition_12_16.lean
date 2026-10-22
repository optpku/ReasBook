/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- The scaled norm kernel `x ↦ β ‖x‖` as an `]-∞,+∞]`-valued function. -/
noncomputable def scaledNormKernel (β : NNReal) : H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ (β : ℝ) * ‖x‖).toEReal

/-- The positive-parameter view of `scaledNormKernel`. The owner abstraction remains
`scaledNormKernel`, whose coefficient may also be `0`; this bridge is for source-facing
statements that naturally use `ρ ∈ ℝ_{++}`. -/
noncomputable abbrev scaledNormKernelOfPos (ρ : Set.Ioi (0 : ℝ)) :
    H → Set.Ioi (⊥ : EReal) :=
  scaledNormKernel ⟨(ρ : ℝ), ρ.2.le⟩

/-- Coercing the scaled norm kernel to `EReal` recovers the formula `x ↦ β ‖x‖`. -/
@[simp]
theorem scaledNormKernel_apply (β : NNReal) (x : H) :
    (scaledNormKernel β x : EReal) = (((β : ℝ) * ‖x‖ : ℝ) : EReal) := by
  simp [scaledNormKernel]

/-- Coercing the positive-parameter scaled norm kernel to `EReal` yields the expected formula
`x ↦ ρ ‖x‖`. -/
@[simp]
theorem scaledNormKernelOfPos_apply (ρ : Set.Ioi (0 : ℝ)) (x : H) :
    (scaledNormKernelOfPos ρ x : EReal) = (((ρ : ℝ) * ‖x‖ : ℝ) : EReal) :=
  scaledNormKernel_apply _ x

section GammaZero

variable [NormedSpace ℝ H]

/-- The scaled norm kernel belongs to `Γ₀(H)`. -/
theorem scaledNormKernel_mem_gammaZero (β : NNReal) :
    scaledNormKernel β ∈ Γ₀(H) := sorry

/-- The positive-parameter scaled norm kernel belongs to `Γ₀(H)`. -/
theorem scaledNormKernelOfPos_mem_gammaZero (ρ : Set.Ioi (0 : ℝ)) :
    scaledNormKernelOfPos ρ ∈ Γ₀(H) :=
  scaledNormKernel_mem_gammaZero _

end GammaZero

/-- Definition 12.16: the `β`-Pasch--Hausdorff envelope of `f` is the infimal convolution of `f`
with the scaled norm `x ↦ β ‖x‖`. -/
noncomputable def paschHausdorffEnvelope {α : Type*} [CoeTC α EReal] (f : H → α) (β : NNReal) :
    H → EReal :=
  f □ scaledNormKernel β

/-- The `β`-Pasch--Hausdorff envelope is computed by infimizing the translated sums
`f y + β ‖x - y‖`. -/
-- Proof sketch: unfold `paschHausdorffEnvelope`, then expand the defining formula for
-- `infimalConvolution` and rewrite the kernel with `scaledNormKernel_apply`.
theorem paschHausdorffEnvelope_apply
    {α : Type*} [CoeTC α EReal] (f : H → α) (β : NNReal) (x : H) :
    paschHausdorffEnvelope f β x =
      ⨅ y : H, (f y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
  simp [paschHausdorffEnvelope, infimalConvolution_apply]

/-- The real-valued `β`-Lipschitz minorants of an `]-∞,+∞]`-valued function. -/
def betaLipschitzMinorants
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal) : Set (H → ℝ) :=
  {h | LipschitzWith β h ∧ h.toEReal.asEReal ≤ f.asEReal}

/-- Membership in `betaLipschitzMinorants f β` is exactly the `β`-Lipschitz minorant condition:
`h` is `β`-Lipschitz and its canonical `EReal` coercion lies below `f`. -/
theorem mem_betaLipschitzMinorants_iff
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal) (h : H → ℝ) :
    h ∈ betaLipschitzMinorants f β ↔
      LipschitzWith β h ∧ h.toEReal.asEReal ≤ f.asEReal :=
  Iff.rfl

end ERealFunction
