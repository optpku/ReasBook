/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

section

variable {E : Type*}

-- Source/core/bridge triage:
-- * source-facing: the bounded recent-index window and the corresponding nonmonotone Armijo
--   reference value formed from the recent objective values;
-- * core/canonical: `Finset.Icc` for the window indices and `Finset.sup'` for the finite
--   maximum;
-- * bridge/view: the membership and unfolding lemmas exposing the explicit bounded-window
--   formula from the source text.

/-- The bounded recent-index window `0, 1, ..., min k mk` used by the nonmonotone Armijo
reference value at stage `k`. -/
def nonmonotoneArmijoWindow (k mk : ℕ) : Finset ℕ :=
  Finset.Icc 0 (Nat.min k mk)

/-- Membership in `nonmonotoneArmijoWindow k mk` means exactly that the index offset lies between
`0` and both bounds `k` and `mk`. -/
theorem mem_nonmonotoneArmijoWindow {k mk j : ℕ} :
    j ∈ nonmonotoneArmijoWindow k mk ↔ j ≤ k ∧ j ≤ mk := by
  simp [nonmonotoneArmijoWindow]

/-- The nonmonotone Armijo window is nonempty because it always contains `0`. -/
theorem nonmonotoneArmijoWindow_nonempty (k mk : ℕ) :
    (nonmonotoneArmijoWindow k mk).Nonempty :=
  Finset.nonempty_Icc.mpr (Nat.zero_le (Nat.min k mk))

/-- The reference value in the nonmonotone Armijo test: the maximum of the bounded recent-value
window `f (x k), f (x (k - 1)), ..., f (x (k - min k mk))`. -/
def nonmonotoneArmijoReferenceValue
    (f : E → ℝ) (x : ℕ → E) (k mk : ℕ) : ℝ :=
  (nonmonotoneArmijoWindow k mk).sup'
    (nonmonotoneArmijoWindow_nonempty k mk)
    (fun j ↦ f (x (k - j)))

/-- Unfolding `nonmonotoneArmijoReferenceValue` recovers the bounded-window maximum over the
recent objective values. -/
theorem nonmonotoneArmijoReferenceValue_eq
    (f : E → ℝ) (x : ℕ → E) (k mk : ℕ) :
    nonmonotoneArmijoReferenceValue f x k mk =
      (nonmonotoneArmijoWindow k mk).sup'
        (nonmonotoneArmijoWindow_nonempty k mk)
        (fun j ↦ f (x (k - j))) :=
  rfl

end
