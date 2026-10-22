/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- Corollary 12.18: a real-valued `β`-Lipschitz function coincides with its own
`β`-Pasch--Hausdorff envelope. -/
-- Proof sketch: apply Proposition 12.17(i) to `f.toEReal`; since `f` itself is a
-- `β`-Lipschitz minorant of that canonical coercion, the envelope is the largest such minorant,
-- hence must equal `f.toEReal.asEReal`.
theorem paschHausdorffEnvelope_eq_self_of_lipschitz
    (f : H → ℝ) (β : NNReal) (hf : LipschitzWith β f) :
    paschHausdorffEnvelope f β = f.toEReal.asEReal := by
  by_cases hH : Nonempty H
  · rcases hH with ⟨x₀⟩
    have hmem : f ∈ betaLipschitzMinorants f.toEReal β := by
      rw [mem_betaLipschitzMinorants_iff]
      exact ⟨hf, le_rfl⟩
    have hxor :=
      paschHausdorffEnvelope_greatestBetaLipschitzMinorant_or_eq_bot f.toEReal β
        ⟨x₀, by simp⟩
    rcases hxor with ⟨⟨g, hg_eq, hg_greatest⟩, _⟩ | ⟨hnone, _⟩
    · have hfg : f ≤ g := hg_greatest.2 hmem
      have hgf : g.toEReal.asEReal ≤ f.toEReal.asEReal :=
        (mem_betaLipschitzMinorants_iff f.toEReal β g).1 hg_greatest.1 |>.2
      have hgf' : g ≤ f := by
        intro x
        simpa using hgf x
      have h_eq : g = f := le_antisymm hgf' hfg
      simpa [h_eq] using hg_eq
    · exact (hnone.1 ⟨f, hmem⟩).elim
  · haveI : IsEmpty H := not_nonempty_iff.mp hH
    ext x
    exact (hH ⟨x⟩).elim

end ERealFunction
