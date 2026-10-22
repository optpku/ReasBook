/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Corollary_10_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Example_10_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_15

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: Example 10.9(3) gives uniform convexity of `x ↦ ‖x‖^2` via strong convexity with
-- constant `2`. Since `p / 2 ≥ 1` when `2 ≤ p`, apply Proposition 10.15 to the nonnegative
-- function `x ↦ ‖x‖₊ ^ 2` to obtain uniform convexity of `x ↦ ‖x‖^p = (‖x‖^2)^(p/2)`, then use
-- the exact modulus provided by that proposition.
/-- Example 10.16: if `p ∈ [2,+∞[`, then the `p`-power of the norm is uniformly convex. -/
theorem norm_rpow_uniformlyConvex
    (p : ℝ) (hp : 2 ≤ p) :
    UniformlyConvex ((fun x : H ↦ ‖x‖ ^ p).toEReal)
      (exactModulusOfConvexity ((fun x : H ↦ ‖x‖ ^ p).toEReal)) := by
  have hp' : 1 ≤ p / 2 := by
    linarith
  have hnormSq :
      UniformlyConvex ((fun x : H ↦ ‖x‖ ^ (2 : ℕ)).toEReal)
      (exactModulusOfConvexity ((fun x : H ↦ ‖x‖ ^ (2 : ℕ)).toEReal)) :=
    StronglyConvex.uniformlyConvex_exactModulusOfConvexity
      (StrongConvexOn.toStronglyConvex (by norm_num) norm_sq_strongConvexOn_univ)
  have hpow :
      (fun x : H ↦ (‖x‖ ^ 2) ^ (p / 2)) = fun x : H ↦ ‖x‖ ^ p := by
    funext x
    have htwo : ((‖x‖ ^ (2 : ℕ)) : ℝ) = ‖x‖ ^ (2 : ℝ) := by
      simp
    calc
      (‖x‖ ^ 2) ^ (p / 2) = (‖x‖ ^ (2 : ℝ)) ^ (p / 2) := by rw [htwo]
      _ = ‖x‖ ^ ((2 : ℝ) * (p / 2)) := by rw [← Real.rpow_mul (norm_nonneg _)]
      _ = ‖x‖ ^ p := by ring_nf
  simpa [hpow] using
    (uniformlyConvex_nnreal_rpow (fun x : H ↦ ‖x‖₊ ^ (2 : ℕ)) (p / 2) hp'
      (by simpa using hnormSq))

end ERealFunction
