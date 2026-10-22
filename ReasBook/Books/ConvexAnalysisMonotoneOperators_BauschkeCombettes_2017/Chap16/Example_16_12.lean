/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: apply Proposition 16.10 to `halfSquaredNorm`, use Example 13.6 to
-- identify its Fenchel conjugate with itself, and then simplify the Fenchel--Young equality to
-- the identity `u = x`.
/-- Example 16.12: the subdifferential of the quadratic function `f = (1 / 2)‖·‖²` is the
identity set-valued operator, written pointwise as the singleton-valued map `x ↦ {x}`. -/
theorem subdifferential_halfSquaredNorm_eq_singleton :
    ∂ halfSquaredNorm = (fun x : H ↦ ({x} : Set H)) := by
  ext x u
  rw [Set.mem_singleton_iff]
  constructor
  · intro hu
    have hfy := (mem_subdifferential_iff_fenchel_young_eq halfSquaredNorm x u).1 hu
    rw [fenchelConjugate_halfSquaredNorm] at hfy
    norm_num [halfSquaredNorm_apply] at hfy
    have hfy' :
        (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) = ⟪x, u⟫_ℝ := by
      exact_mod_cast hfy
    have hnorm : ‖x - u‖ ^ (2 : ℕ) = 0 := by
      rw [norm_sub_sq_real]
      nlinarith [hfy', real_inner_comm x u]
    have hzero : ‖x - u‖ = 0 := sq_eq_zero_iff.mp hnorm
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  · intro hu
    subst u
    exact (mem_subdifferential_iff_fenchel_young_eq halfSquaredNorm x x).2 <| by
      rw [fenchelConjugate_halfSquaredNorm, Function.asEReal_apply, halfSquaredNorm_apply,
        real_inner_self_eq_norm_sq]
      exact_mod_cast (by ring :
        ‖x‖ ^ (2 : ℕ) / 2 + ‖x‖ ^ (2 : ℕ) / 2 = ‖x‖ ^ (2 : ℕ))

-- Proof sketch: evaluate the operator identity from
-- `subdifferential_halfSquaredNorm_eq_singleton` at `x`.
/-- The subdifferential of `x ↦ ‖x‖² / 2` at `x` is the singleton `{x}`. -/
@[simp] theorem subdifferential_halfSquaredNorm_apply (x : H) :
    (∂ halfSquaredNorm) x = ({x} : Set H) := by
  rw [subdifferential_halfSquaredNorm_eq_singleton]

end
