/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

-- Proof sketch: specialize the Pasch--Hausdorff envelope formula to the norm kernel
-- `x ↦ β ‖x‖`. If `f` admits a `β`-Lipschitz minorant, compare that minorant with the defining
-- infimum to show the envelope is real-valued, `β`-Lipschitz, and maximal among such minorants.
-- If no such minorant exists, any finite envelope value would itself produce one, so the envelope
-- must be identically `-∞`. The hypothesis `hf` is the properness assumption specialized to
-- `f : H → ]-∞,+∞]`, where only the existence of a finite point remains nonredundant.
/-- Proposition 12.17: for the `β`-Pasch--Hausdorff envelope of a proper `]-∞,+∞]`-valued
function, exactly one of the following holds: (i) the envelope is the greatest `β`-Lipschitz
continuous minorant, or (ii) there is no `β`-Lipschitz continuous minorant and the envelope is
identically `-∞`. -/
theorem paschHausdorffEnvelope_greatestBetaLipschitzMinorant_or_eq_bot
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal)
    (hf : ∃ x : H, (f x : EReal) < ⊤) :
    Xor'
      (∃ h : H → ℝ,
        paschHausdorffEnvelope f β = h.toEReal.asEReal ∧
          IsGreatest (betaLipschitzMinorants f β) h)
      (¬ (betaLipschitzMinorants f β).Nonempty ∧
        paschHausdorffEnvelope f β = (⊥ : H → EReal)) := sorry

end ERealFunction
