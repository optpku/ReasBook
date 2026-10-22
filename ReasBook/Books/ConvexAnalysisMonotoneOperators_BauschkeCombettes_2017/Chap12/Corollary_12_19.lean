/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u}

private noncomputable def zeroIoi : Set.Ioi (⊥ : EReal) := ⟨0, by simp⟩

/-- The source-facing function attached to `h : C → ℝ`, viewed as finite on `C` and equal to `+∞`
outside `C`. -/
noncomputable def extendWithTopOutside
    (C : Set H) (h : C → ℝ) : H → Set.Ioi (⊥ : EReal) :=
  pointwiseAdd (Function.extend Subtype.val h.toEReal (fun _ ↦ zeroIoi)) (ι[C])

/-- Restricting `extendWithTopOutside C h` back to `C` recovers `h`. -/
theorem extendWithTopOutside_comp_subtype
    (C : Set H) (h : C → ℝ) :
    extendWithTopOutside C h ∘ Subtype.val = h.toEReal := by
  funext x
  apply Subtype.ext
  change (extendWithTopOutside C h x : EReal) = (h.toEReal x : EReal)
  have hextend :
      Function.extend Subtype.val h.toEReal (fun _ ↦ zeroIoi) x = h.toEReal x := by
    exact congrArg (fun k : C → Set.Ioi (⊥ : EReal) ↦ k x)
      (Function.extend_comp Subtype.val_injective h.toEReal (fun _ ↦ zeroIoi))
  rw [extendWithTopOutside, pointwiseAdd_apply, hextend]
  simp [ERealFunction.indicator, x.2]

/-- Outside `C`, `extendWithTopOutside C h` takes the value `+∞`. -/
-- Proof sketch: `x ∉ C` means `x` is not in the range of `Subtype.val : C → H`, so
-- `Function.extend` falls back to the default branch.
theorem extendWithTopOutside_apply_of_not_mem
    {C : Set H} (h : C → ℝ) {x : H} (hx : x ∉ C) :
    (extendWithTopOutside C h x : EReal) = (⊤ : EReal) := by
  rw [extendWithTopOutside, pointwiseAdd_apply]
  simp [ERealFunction.indicator, hx, zeroIoi]

-- Proof sketch: let `f := extendWithTopOutside C h`. For each `x : C`, evaluating the defining
-- infimal convolution at `y = x` gives `(paschHausdorffEnvelope f β x) ≤ h x`, while the
-- `β`-Lipschitz property of `h` on `C` gives the reverse inequality against every admissible
-- `y ∈ C`; hence the envelope agrees with `h` on `C`. The nonemptiness of `C` yields a finite
-- point of `f`, so Proposition 12.17 gives a real-valued greatest `β`-Lipschitz minorant whose
-- `EReal` coercion is the envelope.
variable [NormedAddCommGroup H]

/-- Corollary 12.19: if `h : C → ℝ` is `β`-Lipschitz, then the Pasch--Hausdorff envelope of the
function equal to `h` on `C` and `+∞` outside `C` is realized by a real-valued `β`-Lipschitz
extension of `h`. -/
theorem paschHausdorffEnvelope_realizes_lipschitz_extension
    (C : Set H) (hC : C.Nonempty) (β : NNReal) (h : C → ℝ) (hh : LipschitzWith β h) :
    ∃ g : H → ℝ,
      paschHausdorffEnvelope (extendWithTopOutside C h) β = g.toEReal.asEReal ∧
      LipschitzWith β g ∧
      g ∘ Subtype.val = h := sorry

end ERealFunction
