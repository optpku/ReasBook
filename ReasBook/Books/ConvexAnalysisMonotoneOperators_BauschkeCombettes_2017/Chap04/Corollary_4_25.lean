/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_23

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {T : H → H}

private lemma fixedPointSetOn_reflected_eq (D : Set H) (T : H → H) :
    fixedPointSetOn D (fun x ↦ (2 : ℝ) • T x - x) = fixedPointSetOn D T := by
  ext y
  rw [mem_fixedPointSetOn_iff, mem_fixedPointSetOn_iff]
  constructor
  · rintro ⟨hyD, hyfix⟩
    refine ⟨hyD, ?_⟩
    change (2 : ℝ) • T y - y = y at hyfix
    have hzero : (2 : ℝ) • (T y - y) = 0 := by
      calc
        (2 : ℝ) • (T y - y) = (2 : ℝ) • T y - (2 : ℝ) • y := by
          rw [smul_sub]
        _ = ((2 : ℝ) • T y - y) - y := by
          simp [two_smul, sub_eq_add_neg, add_assoc]
        _ = 0 := by
          rw [hyfix, sub_self]
    rcases smul_eq_zero.mp hzero with htwo | hsub
    · norm_num at htwo
    · exact sub_eq_zero.mp hsub
  · rintro ⟨hyD, hyfix⟩
    refine ⟨hyD, ?_⟩
    change (2 : ℝ) • T y - y = y
    rw [hyfix]
    simp [two_smul]

private lemma reflected_map_quasinonexpansiveOn (D : Set H) (T : H → H)
    (hT : FirmlyQuasinonexpansiveOn D T) :
    QuasinonexpansiveOn D (fun x ↦ (2 : ℝ) • T x - x) := by
  rw [firmlyQuasinonexpansiveOn_iff] at hT
  rw [quasinonexpansiveOn_iff]
  intro x hx y hy
  have hy' : y ∈ fixedPointSetOn D T := by
    simpa [fixedPointSetOn_reflected_eq D T] using hy
  have hfirm := hT x hx y hy'
  let a : H := T x - y
  let b : H := x - T x
  have hsquare : ‖a‖ ^ 2 ≤ ‖b + a‖ ^ 2 - ‖b‖ ^ 2 := by
    have hxy : ‖b + a‖ ^ 2 = ‖x - y‖ ^ 2 := by
      change ‖(x - T x) + (T x - y)‖ ^ 2 = ‖x - y‖ ^ 2
      abel_nf
    have hb : ‖b‖ ^ 2 = ‖T x - x‖ ^ 2 := by
      simp [b, norm_sub_rev]
    have ha : ‖a‖ ^ 2 = ‖T x - y‖ ^ 2 := by
      simp [a]
    nlinarith [hfirm, hxy, hb, ha]
  have hinner_nonneg : 0 ≤ ⟪b, a⟫_ℝ := by
    rw [norm_add_sq_real] at hsquare
    nlinarith
  have hsq : ‖a - b‖ ^ 2 ≤ ‖b + a‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_add_sq_real]
    nlinarith [hinner_nonneg, real_inner_comm b a]
  have hnorm : ‖a - b‖ ≤ ‖b + a‖ := by
    nlinarith [hsq, norm_nonneg (a - b), norm_nonneg (b + a)]
  simpa [a, b, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_smul] using hnorm

private lemma reflected_halfspace_iff_inner_nonpos (T : H → H) (x y : H) :
    ⟪y - ((2 : ℝ) • T x - x), x - ((2 : ℝ) • T x - x)⟫_ℝ
        ≤ (1 / 2 : ℝ) * ‖((2 : ℝ) • T x - x) - x‖ ^ 2 ↔
      ⟪y - T x, x - T x⟫_ℝ ≤ 0 := by
  let z : H := x - T x
  have hxR : x - ((2 : ℝ) • T x - x) = (2 : ℝ) • z := by
    simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_smul]
  have hyR : y - ((2 : ℝ) • T x - x) = (y - T x) + z := by
    simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_smul]
  have hRx : ((2 : ℝ) • T x - x) - x = (-2 : ℝ) • z := by
    simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_smul]
  rw [hyR, hxR, hRx]
  rw [inner_add_left, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [norm_smul]
  simp only [Real.norm_eq_abs, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  ring_nf
  constructor
  · intro h
    nlinarith [sq_nonneg ‖z‖]
  · intro h
    nlinarith [sq_nonneg ‖z‖]

/-- Corollary 4.25: if `D` is a nonempty subset of a real Hilbert space and `T` is firmly
quasinonexpansive on `D`, then the fixed points of `T` in `D` are exactly the intersection of the
half-spaces `{y ∈ D | ⟪y - T x, x - T x⟫_ℝ ≤ 0}` over all `x ∈ D`. -/
theorem fixedPointSetOn_eq_iInter_inner_nonpos_of_firmlyQuasinonexpansive
    (hD : D.Nonempty) (hT : FirmlyQuasinonexpansiveOn D T) :
    fixedPointSetOn D T =
      ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - T x, x - T x⟫_ℝ ≤ 0} := by
  let R : H → H := fun x ↦ (2 : ℝ) • T x - x
  have hRqne : QuasinonexpansiveOn D R := by
    simpa [R] using reflected_map_quasinonexpansiveOn D T hT
  have hR :
      fixedPointSetOn D R =
        ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - R x, x - R x⟫_ℝ ≤ (1 / 2 : ℝ) * ‖R x - x‖ ^ 2} := by
    exact fixedPointSetOn_eq_iInter_halfspaces_of_quasinonexpansive hD hRqne
  have hHalf :
      (⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - R x, x - R x⟫_ℝ ≤ (1 / 2 : ℝ) * ‖R x - x‖ ^ 2}) =
        ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - T x, x - T x⟫_ℝ ≤ 0} := by
    ext y
    simp only [mem_iInter, mem_setOf_eq]
    constructor
    · intro hy x hx
      exact ⟨(hy x hx).1, (reflected_halfspace_iff_inner_nonpos T x y).mp (hy x hx).2⟩
    · intro hy x hx
      exact ⟨(hy x hx).1, (reflected_halfspace_iff_inner_nonpos T x y).mpr (hy x hx).2⟩
  calc
    fixedPointSetOn D T = fixedPointSetOn D R := by
      rw [fixedPointSetOn_reflected_eq D T]
    _ = ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - R x, x - R x⟫_ℝ ≤ (1 / 2 : ℝ) * ‖R x - x‖ ^ 2} := hR
    _ = ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - T x, x - T x⟫_ℝ ≤ 0} := hHalf

end
