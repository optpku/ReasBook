/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Lemma_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_42
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- This item is `source-facing`: it identifies the Fenchel conjugate of the quadratic norm
function. The `core/canonical` owners are already present upstream: `conjugate_function` from
Definition 4.1 for Fenchel conjugacy and `dualNorm` from Chapter 1 for the dual norm. The only
primitive data here are therefore the quadratic norm objective and its dual quadratic value; the
proposition is the source-facing bridge between those owner declarations. -/
recall conjugate_function
recall conjugate_function_apply
recall dualNorm
recall exists_dualNorm_eq_apply

/-- Helper for Proposition 4.22: each Fenchel objective value for
`x ↦ (1 / 2) * ‖x‖²` is bounded above by `(1 / 2) * ‖y‖_*²`. -/
lemma quadraticFenchelObjective_le_halfDualNormSq
    (y : Module.Dual ℝ E) (x : E) :
    ((y x : EReal) - ((((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal)) ≤
      ((((1 / 2 : ℝ) * dualNorm y ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- First replace the pairing by the dual-norm upper bound and finish with the scalar square
  -- inequality `(‖x‖ - ‖y‖_*)² ≥ 0`.
  have hpair : y x ≤ dualNorm y * ‖x‖ := by
    exact le_trans (le_abs_self _) (abs_apply_le_dual_norm_mul_norm y x)
  have hreal :
      y x - ((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)) ≤
        (1 / 2 : ℝ) * dualNorm y ^ (2 : ℕ) := by
    have hsq : 0 ≤ (‖x‖ - dualNorm y) ^ (2 : ℕ) := sq_nonneg (‖x‖ - dualNorm y)
    nlinarith
  rw [← EReal.coe_sub]
  exact EReal.coe_le_coe hreal

/-- Helper for Proposition 4.22: a positive dual norm is attained by a unit vector. -/
lemma existsUnitDualNormWitnessOfPos
    (y : Module.Dual ℝ E) (hy : 0 < dualNorm y) :
    ∃ u : E, ‖u‖ = 1 ∧ y u = dualNorm y := by
  obtain ⟨u, hu_ball, hu_dual⟩ := exists_dualNorm_eq_apply y
  -- A maximizing point on the closed unit ball must actually lie on the unit sphere once
  -- `dualNorm y` is positive.
  have hu_lower : 1 ≤ ‖u‖ := by
    have hbound : dualNorm y ≤ dualNorm y * ‖u‖ := by
      calc
        dualNorm y = y u := hu_dual
        _ ≤ |y u| := le_abs_self _
        _ ≤ dualNorm y * ‖u‖ := abs_apply_le_dual_norm_mul_norm y u
    nlinarith
  exact ⟨u, le_antisymm hu_ball hu_lower, hu_dual.symm⟩

/-- Helper for Proposition 4.22: the scaled unit witness `dualNorm y • u` attains the value
`(1 / 2) * ‖y‖_*²` when `u` realizes the dual norm on the unit sphere. -/
lemma quadraticFenchelObjective_eq_halfDualNormSq_atScaledWitness
    (y : Module.Dual ℝ E) {u : E} (hu_norm : ‖u‖ = 1)
    (hu_dual : y u = dualNorm y) :
    ((y (dualNorm y • u) : EReal) -
        ((((1 / 2 : ℝ) * ‖dualNorm y • u‖ ^ (2 : ℕ)) : ℝ) : EReal)) =
      ((((1 / 2 : ℝ) * dualNorm y ^ (2 : ℕ)) : ℝ) : EReal) := by
  have hdual_nonneg : 0 ≤ dualNorm y := by
    rw [dualNorm_eq_toContinuousLinearMap_norm]
    exact norm_nonneg _
  -- Evaluate both the pairing and the norm on the scaled witness before doing the scalar
  -- arithmetic in `ℝ`.
  have hpair : y (dualNorm y • u) = dualNorm y ^ (2 : ℕ) := by
    rw [map_smul, hu_dual, smul_eq_mul]
    ring
  have hnorm : ‖dualNorm y • u‖ = dualNorm y := by
    rw [norm_smul, hu_norm, Real.norm_of_nonneg hdual_nonneg, mul_one]
  rw [hpair, hnorm, ← EReal.coe_sub]
  have hscalar :
      (dualNorm y ^ (2 : ℕ) - (1 / 2 : ℝ) * dualNorm y ^ (2 : ℕ) : ℝ) =
        (1 / 2 : ℝ) * dualNorm y ^ (2 : ℕ) := by
    ring
  simpa using congrArg (fun t : ℝ ↦ (t : EReal)) hscalar

-- Proof sketch: rewrite the conjugate as the supremum of
-- `x ↦ (y x : ℝ) - (1 / 2) * ‖x‖ ^ 2`. The dual-pairing inequality gives the upper bound
-- `y x ≤ dualNorm y * ‖x‖`, reducing the problem to maximizing
-- `r ↦ dualNorm y * r - (1 / 2) * r ^ 2` over `r ≥ 0`. Equality is attained by a unit vector that
-- realizes the dual norm, scaled by `dualNorm y`.
/-- Proposition 4.22 (`prop:4.22`): for `f(x) = (1 / 2) * ‖x‖ ^ 2`, the Fenchel conjugate
`f*` is `y ↦ (1 / 2) * ‖y‖_* ^ 2`. -/
theorem half_squared_norm_conjugate_eq_half_dualNorm_sq
    (y : Module.Dual ℝ E) :
    conjugate_function (fun x : E ↦ ((((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal)) y =
      ((((1 / 2 : ℝ) * dualNorm y ^ (2 : ℕ)) : ℝ) : EReal) := by
  have hdual_nonneg : 0 ≤ dualNorm y := by
    rw [dualNorm_eq_toContinuousLinearMap_norm]
    exact norm_nonneg _
  rw [conjugate_function_apply]
  apply le_antisymm
  · -- The quadratic Fenchel objective is pointwise bounded by `(1 / 2) * ‖y‖_*²`.
    refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    exact quadraticFenchelObjective_le_halfDualNormSq y x
  · by_cases hy0 : dualNorm y = 0
    · -- When `‖y‖_* = 0`, the origin already realizes the target value.
      refine le_sSup ?_
      refine ⟨0, ?_⟩
      simp [hy0]
    · -- Otherwise, scale a unit vector that attains the dual norm.
      have hypos : 0 < dualNorm y := lt_of_le_of_ne hdual_nonneg (Ne.symm hy0)
      obtain ⟨u, hu_norm, hu_dual⟩ := existsUnitDualNormWitnessOfPos y hypos
      refine le_sSup ?_
      exact ⟨dualNorm y • u,
        quadraticFenchelObjective_eq_halfDualNormSq_atScaledWitness y hu_norm hu_dual⟩

end

section

open InnerProductSpace (toDualMap)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.22 is source-facing on the dual owner `conjugate_function`, while later
inner-product-space arguments usually consume the textbook primal surface `f∗`. The theorem below
is therefore a `bridge/view` companion obtained by evaluating the source theorem along the Riesz
map `toDualMap ℝ E`. -/
recall conjugate_function_primal

/-- Primal-space companion to Proposition 4.22: on a finite-dimensional real inner product space,
the Fenchel conjugate of `x ↦ (1 / 2) * ‖x‖ ^ 2`, viewed through `toDualMap ℝ E`, is again
`x ↦ (1 / 2) * ‖x‖ ^ 2`. -/
theorem conjugate_function_primal_half_squared_norm_eq_half_norm_sq
    (x : E) :
    ((fun z : E ↦ ((((1 / 2 : ℝ) * ‖z‖ ^ (2 : ℕ)) : ℝ) : EReal))∗) x =
      ((((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  rw [conjugate_function_primal_apply]
  have hnorm :
      ‖((toDualMap ℝ E x : StrongDual ℝ E) : Module.Dual ℝ E)‖ = ‖x‖ := by
    exact (toDualMap ℝ E).norm_map x
  simpa [dualNorm, hnorm] using
    half_squared_norm_conjugate_eq_half_dualNorm_sq
      ((toDualMap ℝ E x : StrongDual ℝ E) : Module.Dual ℝ E)

end
