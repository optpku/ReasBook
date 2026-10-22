/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_3_26

open scoped RealInnerProductSpace

-- Semantic recall hits verified for this item: the primitive pieces are closed half-spaces, with
-- canonical owner declarations `closedLowerHalfSpace` and `closedUpperHalfSpace`; convexity is
-- derived from `convex_halfSpace_le`, `convex_halfSpace_ge`, and `Convex.inter`.

local notation "Point" => EuclideanSpace ℝ (Fin 2)

private def firstCoordNormal : Point :=
  WithLp.toLp 2 (Pi.single 0 (1 : ℝ))

private def diagonalNormal : Point :=
  WithLp.toLp 2 ![1, 1]

private def diagonalDifferenceNormal : Point :=
  WithLp.toLp 2 ![1, -1]

private def firstCoord : Point →ₗ[ℝ] ℝ :=
  PiLp.projₗ 2 _ 0

private def secondCoord : Point →ₗ[ℝ] ℝ :=
  PiLp.projₗ 2 _ 1

/-- The set `D₁ = {x | x 0 + x 1 ≤ 1 ∧ 0 ≤ x 0}` from Exercise 1.14. -/
def convexUnionCounterexampleD₁ : Set Point :=
  closedLowerHalfSpace diagonalNormal 1 ∩ closedUpperHalfSpace firstCoordNormal 0

/-- The set `D₂ = {x | 0 ≤ x 0 - x 1 ∧ x 0 ≤ 0}` from Exercise 1.14. -/
def convexUnionCounterexampleD₂ : Set Point :=
  closedUpperHalfSpace diagonalDifferenceNormal 0 ∩ closedLowerHalfSpace firstCoordNormal 0

/-- Membership in `convexUnionCounterexampleD₁` is the textbook coordinate inequality pair. -/
@[simp] theorem mem_convexUnionCounterexampleD₁_iff {x : Point} :
    x ∈ convexUnionCounterexampleD₁ ↔ x 0 + x 1 ≤ 1 ∧ 0 ≤ x 0 := by
  simp [convexUnionCounterexampleD₁, diagonalNormal, firstCoordNormal, closedLowerHalfSpace,
    closedUpperHalfSpace, PiLp.inner_apply, Fin.sum_univ_two]

/-- Membership in `convexUnionCounterexampleD₂` is the textbook coordinate inequality pair. -/
@[simp] theorem mem_convexUnionCounterexampleD₂_iff {x : Point} :
    x ∈ convexUnionCounterexampleD₂ ↔ 0 ≤ x 0 - x 1 ∧ x 0 ≤ 0 := by
  simp [convexUnionCounterexampleD₂, diagonalDifferenceNormal, firstCoordNormal,
    closedUpperHalfSpace, closedLowerHalfSpace, PiLp.inner_apply, Fin.sum_univ_two]

/-- The union `D = D₁ ∪ D₂` from Exercise 1.14. -/
def convexUnionCounterexampleD : Set Point :=
  convexUnionCounterexampleD₁ ∪ convexUnionCounterexampleD₂

/-- Chapter01 Exercise 1.14 (1): the set `D₁` is convex. -/
theorem convexUnionCounterexampleD₁_convex :
    Convex ℝ convexUnionCounterexampleD₁ := by
  have hsum : Convex ℝ {x : Point | (firstCoord + secondCoord) x ≤ 1} := by
    simpa [firstCoord, secondCoord] using
      convex_halfSpace_le ((firstCoord + secondCoord).isLinear) (1 : ℝ)
  have hfst : Convex ℝ {x : Point | 0 ≤ firstCoord x} := by
    simpa [firstCoord] using convex_halfSpace_ge firstCoord.isLinear (0 : ℝ)
  convert hsum.inter hfst using 1
  ext x
  rw [mem_convexUnionCounterexampleD₁_iff]
  simp [firstCoord, secondCoord]

/-- Chapter01 Exercise 1.14 (2): the set `D₂` is convex. -/
theorem convexUnionCounterexampleD₂_convex :
    Convex ℝ convexUnionCounterexampleD₂ := by
  have hdiff : Convex ℝ {x : Point | 0 ≤ (firstCoord - secondCoord) x} := by
    simpa [firstCoord, secondCoord] using
      convex_halfSpace_ge ((firstCoord - secondCoord).isLinear) (0 : ℝ)
  have hfst : Convex ℝ {x : Point | firstCoord x ≤ 0} := by
    simpa [firstCoord] using convex_halfSpace_le firstCoord.isLinear (0 : ℝ)
  convert hdiff.inter hfst using 1
  ext x
  rw [mem_convexUnionCounterexampleD₂_iff]
  simp [firstCoord, secondCoord]

/-- Chapter01 Exercise 1.14 (3): the union `D = D₁ ∪ D₂` is not convex, so the union of
convex sets need not be convex. -/
theorem convexUnionCounterexampleD_not_convex :
    ¬ Convex ℝ convexUnionCounterexampleD := by
  intro hD
  let x : Point := WithLp.toLp 2 ![0, 1]
  let y : Point := WithLp.toLp 2 ![-2, -2]
  have hx : x ∈ convexUnionCounterexampleD₁ := by
    simp [x]
  have hy : y ∈ convexUnionCounterexampleD₂ := by
    simp [y]
  have hmid :
      (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ convexUnionCounterexampleD :=
    hD (Or.inl hx) (Or.inr hy) (by norm_num) (by norm_num) (by norm_num)
  have hxy :
      (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = WithLp.toLp 2 ![-1, -(1 / 2 : ℝ)] := by
    ext i
    fin_cases i <;> norm_num [x, y]
  have hnot : WithLp.toLp 2 ![-1, -(1 / 2 : ℝ)] ∉ convexUnionCounterexampleD := by
    intro h
    rcases h with h | h
    · norm_num at h
    · norm_num at h
  exact hnot <| hxy ▸ hmid
