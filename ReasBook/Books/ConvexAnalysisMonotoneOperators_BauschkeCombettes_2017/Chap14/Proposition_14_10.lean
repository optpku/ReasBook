/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Definition_14_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace ERealFunction

open WithLp

variable {H : Type u}

section ProximalAverage

/- Source/core/bridge triage:
- `source-facing`: Proposition 14.10 is the symmetry statement asserting that transposition on
  `H × H` commutes with the Chapter 14 proximal average.
- `core/canonical`: the owner abstractions are `transpose` from Definition 13.34 and
  `proximalAverage`/`pav` from Definition 14.6, evaluated directly on `H × H` after installing the
  textbook `ℓ²` product norm as the local owner geometry.
- `bridge/view`: no separate public bridge is needed; the `ℓ²` product instances stay local to
  this proposition. -/

variable [NormedAddCommGroup H] [Module ℝ H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.pseudoMetricSpaceMax

local instance prod_normedAddCommGroup_l2_14_10 : NormedAddCommGroup (H × H) :=
  WithLp.normedAddCommGroupToProd 2 H H

-- Proof sketch: unfold `ᵀ` and `pav`, then rewrite the defining infimum by swapping both
-- coordinates in the base point and in the integration variable.
/-- Proposition 14.10: on `H × H`, transpose `ᵀ` commutes with the proximal average computed in
the textbook `ℓ²` product geometry. -/
theorem proximalAverage_transpose
    (F G : (H × H) → Set.Ioi (⊥ : EReal)) :
    (pav(F, G))ᵀ = pav(Fᵀ, Gᵀ) := by
  ext ⟨u, x⟩
  simp only [transpose_apply, proximalAverage_apply]
  congr 1
  exact (Equiv.prodComm H H).iInf_congr fun y ↦ by
    rcases y with ⟨a, b⟩
    simp only [Equiv.prodComm_apply]
    congr 2
    change ‖(u - b, x - a)‖ ^ 2 = ‖(x - a, u - b)‖ ^ 2
    rw [show ‖(u - b, x - a)‖ = ‖toLp 2 (u - b, x - a)‖ by rfl]
    rw [show ‖(x - a, u - b)‖ = ‖toLp 2 (x - a, u - b)‖ by rfl]
    rw [prod_norm_sq_eq_of_L2, prod_norm_sq_eq_of_L2]
    simpa using add_comm (‖u - b‖ ^ 2) (‖x - a‖ ^ 2)

end ProximalAverage

end ERealFunction
