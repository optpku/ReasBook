/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Real.Basic

public section

/-- Proposition 1.15 (1): if `k := ⌊u / x1Star⌋` with `0 < x1Star` and `x1Star ≤ u`,
then `(k : ℝ) * x1Star > u / 2`.

This first component belongs to the item-level cleanup theorem in this file. -/
theorem floorDivMulGtHalf (u x1Star : ℝ) (hx1Star_pos : 0 < x1Star) (hxu : x1Star ≤ u) :
    u / 2 < (⌊u / x1Star⌋ : ℝ) * x1Star := by
  -- First bound the quotient below by `1` so the floor estimate applies.
  have hquot_ge_one : 1 ≤ u / x1Star := by
    simpa using (one_le_div₀ hx1Star_pos).2 hxu
  -- Then compare half the quotient with its floor.
  have hfloor : u / x1Star / 2 < (⌊u / x1Star⌋ : ℝ) := by
    simpa using Int.div_two_lt_floor (a := u / x1Star) hquot_ge_one
  -- Scaling by the positive denominator converts the quotient estimate to the target bound.
  have hscaled := mul_lt_mul_of_pos_right hfloor hx1Star_pos
  have hnormalize : (u / x1Star / 2) * x1Star = u / 2 := by
    field_simp [hx1Star_pos.ne']
  calc
    u / 2 = (u / x1Star / 2) * x1Star := hnormalize.symm
    _ < (⌊u / x1Star⌋ : ℝ) * x1Star := hscaled

/-- Proposition 1.15 (2): if `k := ⌊u / x1Star⌋` and
`u' := u - (k : ℝ) * x1Star` with `0 < x1Star` and `x1Star ≤ u`, then `u' ≤ u / 2`. -/
theorem subFloorDivMulLeHalf (u x1Star : ℝ) (hx1Star_pos : 0 < x1Star) (hxu : x1Star ≤ u) :
    u - (⌊u / x1Star⌋ : ℝ) * x1Star ≤ u / 2 := by
  -- Reuse Proposition 1.15 (1) and move terms to the other side.
  have hhalf := floorDivMulGtHalf u x1Star hx1Star_pos hxu
  linarith

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_proposition_1_15.lean
Proposition 1.15 packages both floor-division inequalities proved above. -/
theorem floorDivMulGtHalfAndSubFloorDivMulLeHalf
    (u x1Star : ℝ) (hx1Star_pos : 0 < x1Star) (hxu : x1Star ≤ u) :
    u / 2 < (⌊u / x1Star⌋ : ℝ) * x1Star ∧
      u - (⌊u / x1Star⌋ : ℝ) * x1Star ≤ u / 2 := by
  -- Package the two proved components into the item-level owner declaration.
  constructor
  · exact floorDivMulGtHalf u x1Star hx1Star_pos hxu
  · exact subFloorDivMulLeHalf u x1Star hx1Star_pos hxu

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_proposition_1_15.lean:
compatibility alias for the packaged floor-division inequalities. -/
theorem «floorDivMulGtHalf + subFloorDivMulLeHalf»
    (u x1Star : ℝ) (hx1Star_pos : 0 < x1Star) (hxu : x1Star ≤ u) :
    u / 2 < (⌊u / x1Star⌋ : ℝ) * x1Star ∧
      u - (⌊u / x1Star⌋ : ℝ) * x1Star ≤ u / 2 := by
  -- Reuse the audit-safe owner theorem without changing the packaged statement.
  exact floorDivMulGtHalfAndSubFloorDivMulLeHalf u x1Star hx1Star_pos hxu

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_e06beb21910265ea40f2"
#print axioms _root_.floorDivMulGtHalfAndSubFloorDivMulLeHalf
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_e06beb21910265ea40f2"
