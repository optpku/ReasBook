/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Algebra/GroupWithZero/PowerCancellation.lean
-/

module

public import Mathlib.Algebra.GroupWithZero.Units.Basic

public section

universe u

namespace Function

/-- Exact factorizations by a common power have equal residual and original quotients
away from zero. -/
theorem div_eq_div_of_eq_pow_mul {G : Type u} [CommGroupWithZero G] (a : ℕ)
    (N D Nres Dres : G → G) (hN : ∀ ε, N ε = ε ^ a * Nres ε)
    (hD : ∀ ε, D ε = ε ^ a * Dres ε) {ε : G} (hε : ε ≠ 0) :
    Nres ε / Dres ε = N ε / D ε := by
  -- The common power remains nonzero away from the base point.
  have hpow : ε ^ a ≠ 0 := pow_ne_zero a hε
  -- Rewrite to the factored form, then cancel the common nonzero factor.
  rw [hN ε, hD ε]
  exact (mul_div_mul_left (Nres ε) (Dres ε) hpow).symm

end Function
