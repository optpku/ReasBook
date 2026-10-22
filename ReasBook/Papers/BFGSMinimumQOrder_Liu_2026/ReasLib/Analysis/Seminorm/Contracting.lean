/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Analysis/Seminorm/Contracting.lean
-/

module

public import Mathlib.Analysis.Seminorm

public section

universe u v

namespace Seminorm

variable {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- A seminorm contracts an endomorphism below `r` when it admits a uniform coefficient
strictly smaller than `r`. -/
def IsContracting (p : Seminorm 𝕜 E) (L : Module.End 𝕜 E) (r : NNReal) : Prop :=
  ∃ c : NNReal, c < r ∧ p.comp L ≤ c • p

/-- Contraction of a seminorm expressed as a pointwise estimate. -/
theorem isContracting_iff {p : Seminorm 𝕜 E} {L : Module.End 𝕜 E} {r : NNReal} :
    p.IsContracting L r ↔
      ∃ c : NNReal, c < r ∧ ∀ x, p (L x) ≤ (c : ℝ) * p x := by
  -- Evaluate the seminorm-order bound pointwise and normalize the scalar action.
  simp only [IsContracting, le_def, comp_apply, smul_apply, NNReal.smul_def, smul_eq_mul]

end Seminorm
