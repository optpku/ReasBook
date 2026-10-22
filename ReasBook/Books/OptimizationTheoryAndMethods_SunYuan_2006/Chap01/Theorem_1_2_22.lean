/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_28
import Mathlib.Topology.MetricSpace.Lipschitz

open Set

section Theorem122

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

-- Source/core/bridge triage:
-- * core/canonical owner: `holderRemainderBound`
-- * source-facing declaration here: the `p = 1` specialization with derivative field `fderiv ℝ F`
-- * no extra wrapper owner is introduced; the Euclidean `ℝⁿ → ℝᵐ` statement is now a specialization

/-- Chapter01 Theorem 1.2.22: if `F : E → G` is differentiable on an
open convex set `D` and `fderiv ℝ F` is `γ`-Lipschitz on `D`,
then the first-order Taylor remainder at `x + d` is bounded by `(γ / 2) * ‖d‖ ^ 2`. -/
theorem quadraticRemainderBound_of_fderiv_lipschitzOn
    (D : Set E)
    (F : E → G)
    (x d : E)
    (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hF : DifferentiableOn ℝ F D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    (hxd : x + d ∈ D) :
    ‖F (x + d) - F x - (fderiv ℝ F x) d‖ ≤ ((γ : ℝ) / 2) * ‖d‖ ^ 2 := by
  have hmain_raw :=
    holderRemainderBound F (fderiv ℝ F) hD_convex
      (fun y hy e ↦
        by
          simpa [fderivWithin_of_isOpen hD_open hy] using
            ((hF y hy).hasFDerivWithinAt.hasLineDerivWithinAt e))
      hLip.holderOnWith
      (by positivity : 0 < (1 : NNReal))
      hx
      hxd
  have htwo : (1 : ℝ) + 1 = 2 := by norm_num
  simpa [htwo, Real.rpow_natCast, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    hmain_raw

end Theorem122
