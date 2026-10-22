/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ProximityOperator

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The scaled proximity operator `Prox_{γ f}`, realized as the ordinary proximity operator of the
positively scaled function `γ • f`. The source-facing Lean notation is `Prox[γ, f, hf]`. -/
noncomputable def scaledProximityOperator
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) : H → H :=
  Prox[γ • f, smul_mem_gammaZero f hf γ]

notation "Prox[" γ ", " f ", " hf "]" => scaledProximityOperator f hf γ

end ERealFunction
