/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 8.10 is `source-facing`: the textbook introduces an explicit scalar rule for the
stepsize chosen from the current objective value, the optimal value, and the current subgradient
vector. There is no existing canonical owner in mathlib for this exact optimization-specific
formula, so the clean public API is the pointwise rule itself, with no extra wrapper around
iteration data. -/

/-- Definition 8.10: Polyak's stepsize rule assigns to a point `x` with chosen subgradient vector
`g` the stepsize `(f x - fOpt) / ‖g‖^2` when `g ≠ 0`, and the fallback value `1` when `g = 0`. -/
def polyak_stepsize (f : E → EReal) (fOpt : ℝ) (x g : E) : ℝ :=
  if ‖g‖ = 0 then 1 else ((f x).toReal - fOpt) / ‖g‖ ^ (2 : ℕ)

-- Proof sketch: unfold `polyak_stepsize`; for `g = 0` one has `‖g‖ = 0`, so the defining `if`
-- reduces immediately to its first branch.
/-- If the chosen subgradient vector is zero, Polyak's stepsize rule returns the fallback value
`1`. -/
@[simp] theorem polyak_stepsize_zero
    (f : E → EReal) (fOpt : ℝ) (x : E) :
    polyak_stepsize f fOpt x (0 : E) = 1 := by
  -- The zero vector triggers the fallback branch because its norm is zero.
  simp [polyak_stepsize]

-- Proof sketch: unfold `polyak_stepsize`; if `g ≠ 0`, then `‖g‖ ≠ 0` by `norm_ne_zero_iff`, so
-- the defining `if` reduces to the quotient branch `((f x).toReal - fOpt) / ‖g‖^2`.
/-- For a nonzero chosen subgradient vector, Polyak's stepsize rule is the quotient
`((f x).toReal - fOpt) / ‖g‖^2`. -/
theorem polyak_stepsize_of_ne_zero
    (f : E → EReal) (fOpt : ℝ) (x g : E) (hg : g ≠ 0) :
    polyak_stepsize f fOpt x g = ((f x).toReal - fOpt) / ‖g‖ ^ (2 : ℕ) := by
  -- A nonzero vector has nonzero norm, so the defining `if` takes the quotient branch.
  have hnorm : ‖g‖ ≠ 0 := by
    intro hnorm
    apply hg
    exact norm_eq_zero.mp hnorm
  simp [polyak_stepsize, hnorm]

end
