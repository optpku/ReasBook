/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Lemma_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Metric

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The set `Λ_a` of primal counterparts of a dual vector `a`: the unit-ball points where the
pairing with `a` attains the operator norm. This is equivalent to the source's zero/nonzero
case split, but keeps only the canonical primitive data on the continuous dual. -/
def primalCounterparts (a : E →L[ℝ] ℝ) : Set E :=
  { x : E | ‖x‖ ≤ 1 ∧ a x = ‖a‖ }

end

-- Chapter 7 owns the public `Λ[...]` notation. Keep this chapter-specific overload private so
-- importing both chapters does not duplicate the generated global parser declaration.
local notation "Λ[" a "]" => primalCounterparts a

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Lemma 10.61: a maximizer of a real linear functional on the symmetric closed unit
ball controls the absolute value of that functional everywhere on the ball. -/
lemma norm_apply_le_of_isMaxOn_closedBall
    {a : E →L[ℝ] ℝ} {x0 x : E}
    (_hx0 : x0 ∈ closedBall (0 : E) 1)
    (hmax : IsMaxOn a (closedBall (0 : E) 1) x0)
    (hx : x ∈ closedBall (0 : E) 1) :
    ‖a x‖ ≤ a x0 := by
  rw [isMaxOn_iff] at hmax
  have hnegx : -x ∈ closedBall (0 : E) 1 := by
    -- The closed unit ball is symmetric, so `-x` stays admissible.
    rw [mem_closedBall_zero_iff] at hx ⊢
    simpa [norm_neg] using hx
  have hx_le : a x ≤ a x0 :=
    hmax x hx
  have hnegx_le : -a x ≤ a x0 := by
    -- Evaluating at `-x` converts the maximizing inequality into the opposite-sign bound.
    simpa using hmax (-x) hnegx
  have hleft : -a x0 ≤ a x := by
    linarith
  have habs_le : |a x| ≤ a x0 :=
    abs_le.mpr ⟨hleft, hx_le⟩
  simpa [Real.norm_eq_abs] using habs_le

/-- Helper for Lemma 10.61: a maximizer of a real linear functional on the closed unit ball
attains at least the operator norm of that functional. -/
lemma norm_le_apply_of_isMaxOn_closedBall
    {a : E →L[ℝ] ℝ} {x0 : E}
    (hx0 : x0 ∈ closedBall (0 : E) 1)
    (hmax : IsMaxOn a (closedBall (0 : E) 1) x0) :
    ‖a‖ ≤ a x0 := by
  rw [isMaxOn_iff] at hmax
  have hzero_mem : (0 : E) ∈ closedBall (0 : E) 1 := by
    -- The origin is in the closed unit ball, so maximality makes `a x0` nonnegative.
    simp
  have hx0_nonneg : 0 ≤ a x0 := by
    simpa using hmax 0 hzero_mem
  have hbound : ∀ x : E, ‖a x‖ ≤ a x0 * ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · -- The zero vector contributes the trivial bound.
      subst hx
      simp
    · have hnormx_ne : ‖x‖ ≠ 0 :=
        norm_ne_zero_iff.mpr hx
      let y : E := ‖x‖⁻¹ • x
      have hy_norm : ‖y‖ = 1 := by
        -- The normalized vector lies on the unit sphere.
        dsimp [y]
        calc
          ‖‖x‖⁻¹ • x‖ = ‖‖x‖⁻¹‖ * ‖x‖ := norm_smul _ _
          _ = ‖x‖⁻¹ * ‖x‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg]
            positivity
          _ = 1 := by
            rw [inv_mul_cancel₀ hnormx_ne]
      have hy_mem : y ∈ closedBall (0 : E) 1 := by
        -- Normalize `x` onto the unit sphere to use maximality on the unit ball.
        rw [mem_closedBall_zero_iff]
        exact hy_norm.le
      have hy_bound : ‖a y‖ ≤ a x0 :=
        norm_apply_le_of_isMaxOn_closedBall hx0 (isMaxOn_iff.mpr hmax) hy_mem
      have hx_eq : x = ‖x‖ • y := by
        -- Undo the normalization so the global operator-norm bound can be recovered.
        dsimp [y]
        rw [smul_smul, mul_inv_cancel₀ hnormx_ne, one_smul]
      calc
        ‖a x‖ = ‖a (‖x‖ • y)‖ := by
          exact congrArg (fun z ↦ ‖a z‖) hx_eq
        _ = ‖‖x‖ • a y‖ := by
          rw [map_smul]
        _ = ‖‖x‖‖ * ‖a y‖ := norm_smul _ _
        _ = ‖x‖ * ‖a y‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact norm_nonneg _
        _ ≤ ‖x‖ * a x0 := by
          exact mul_le_mul_of_nonneg_left hy_bound (norm_nonneg _)
        _ = a x0 * ‖x‖ := by
          rw [mul_comm]
  exact a.opNorm_le_bound hx0_nonneg hbound

-- Proof sketch: unfold `primalCounterparts`, rewrite unit-ball membership as `mem_closedBall`,
-- and express the maximizer condition by `isMaxOn_iff`. The forward implication uses the operator
-- norm bound `a v ≤ ‖a‖` on the closed unit ball. For the converse, the maximality hypothesis on
-- `aDagger` bounds `a` on every normalized vector and therefore forces `‖a‖ ≤ a aDagger`.
/-- A vector belongs to `Λ[a]` exactly when it lies in the closed unit ball and maximizes `a`
over that ball. -/
theorem mem_Λ_iff
    {a : E →L[ℝ] ℝ} {aDagger : E} :
    aDagger ∈ Λ[a] ↔
      aDagger ∈ closedBall (0 : E) 1 ∧ IsMaxOn a (closedBall (0 : E) 1) aDagger := by
  constructor
  · intro haDagger
    rcases haDagger with ⟨haDagger_norm, haDagger_eq⟩
    constructor
    · -- Rewrite the defining norm bound as closed-ball membership.
      rwa [mem_closedBall_zero_iff]
    · -- The defining norm attainment forces `aDagger` to maximize `a` on the closed unit ball.
      rw [isMaxOn_iff]
      intro x hx
      have hx_norm : ‖x‖ ≤ 1 := by
        rwa [mem_closedBall_zero_iff] at hx
      calc
        a x ≤ ‖a x‖ := le_abs_self _
        _ ≤ ‖a‖ := by
          simpa [Real.norm_eq_abs] using a.unit_le_opNorm x hx_norm
        _ = a aDagger := haDagger_eq.symm
  · rintro ⟨haDagger_ball, hmax⟩
    have haDagger_norm : ‖aDagger‖ ≤ 1 := by
      rwa [mem_closedBall_zero_iff] at haDagger_ball
    have hupper : a aDagger ≤ ‖a‖ := by
      -- The unit-ball bound gives the easy inequality `a aDagger ≤ ‖a‖`.
      have hnorm : ‖a aDagger‖ ≤ ‖a‖ :=
        a.unit_le_opNorm aDagger haDagger_norm
      exact (le_abs_self (a aDagger)).trans <| by
        simpa [Real.norm_eq_abs] using hnorm
    have hlower : ‖a‖ ≤ a aDagger :=
      norm_le_apply_of_isMaxOn_closedBall haDagger_ball hmax
    -- Combine the norm bound and maximality lower bound to recover the defining equality.
    constructor
    · exact haDagger_norm
    · exact le_antisymm hupper hlower

-- Proof sketch: unfold `primalCounterparts a`. The equality `a a† = ‖a‖` together with the
-- operator-norm inequality forces `‖a‖ ≤ ‖a‖ * ‖a†‖`; since `a ≠ 0`, the norm is positive, so
-- `1 ≤ ‖a†‖`. Combined with the defining bound `‖a†‖ ≤ 1`, this gives `‖a†‖ = 1`.
/-- Lemma 10.61 (1): if `a ≠ 0`, every primal counterpart `a† ∈ Λ_a` has norm `1`. -/
theorem norm_eq_one_of_mem_primalCounterparts
    {a : E →L[ℝ] ℝ} (ha : a ≠ 0) {aDagger : E}
    (haDagger : aDagger ∈ Λ[a]) :
    ‖aDagger‖ = 1 := by
  rcases haDagger with ⟨haDagger_norm, haDagger_eq⟩
  have hnorma_pos : 0 < ‖a‖ :=
    norm_pos_iff.mpr ha
  have hnorma_le : ‖a‖ ≤ ‖a‖ * ‖aDagger‖ := by
    -- Rewrite the norm-attainment equation into an operator-norm lower bound.
    calc
      ‖a‖ = ‖a aDagger‖ := by
        rw [haDagger_eq, Real.norm_eq_abs, abs_of_nonneg]
        exact norm_nonneg _
      _ ≤ ‖a‖ * ‖aDagger‖ := a.le_opNorm aDagger
  have hone_le : 1 ≤ ‖aDagger‖ := by
    -- Strictly shrinking `aDagger` would contradict the attained operator norm.
    by_contra hone_le
    have hlt : ‖aDagger‖ < 1 :=
      lt_of_not_ge hone_le
    have hmul_lt : ‖a‖ * ‖aDagger‖ < ‖a‖ := by
      simpa [mul_one] using mul_lt_mul_of_pos_left hlt hnorma_pos
    exact not_lt_of_ge hnorma_le hmul_lt
  exact le_antisymm haDagger_norm hone_le

-- Proof sketch: after substituting `a = 0`, the equality clause in `primalCounterparts a` becomes
-- `0 = ‖0‖`, hence is automatic. Membership therefore reduces to `‖x‖ ≤ 1`, which is
-- exactly membership in the closed unit ball `closedBall (0 : E) 1`.
/-- Lemma 10.61 (2): if `a = 0`, then `Λ_a` is the closed unit ball `B_{‖·‖}[0,1]`. -/
theorem primalCounterparts_eq_closedBall_of_eq_zero
    {a : E →L[ℝ] ℝ} (ha : a = 0) :
    Λ[a] = closedBall (0 : E) 1 := by
  ext x
  constructor
  · intro hx
    -- When `a = 0`, the owner condition keeps only the closed-ball bound.
    rw [mem_closedBall_zero_iff]
    rw [ha] at hx
    exact hx.1
  · intro hx
    -- Conversely, every point of the closed unit ball satisfies the trivial zero-functional clause.
    rw [primalCounterparts, ha]
    constructor
    · simpa [mem_closedBall_zero_iff] using hx
    · simp

-- Proof sketch: the equality `a a† = ‖a‖` is part of the defining condition of
-- `primalCounterparts a`.
/-- Lemma 10.61 (3): every primal counterpart `a† ∈ Λ_a` satisfies
`⟨a, a†⟩ = ‖a‖_*`, written here as `a a† = ‖a‖`. -/
theorem apply_eq_norm_of_mem_primalCounterparts
    {a : E →L[ℝ] ℝ} {aDagger : E}
    (haDagger : aDagger ∈ Λ[a]) :
    a aDagger = ‖a‖ := by
  -- Unfold the owner definition and read off the norm-attainment equality.
  exact haDagger.2

end
