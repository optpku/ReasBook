/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open InnerProductSpace (toDualMap)
open scoped Gradient

/- Proposition 3.16 is a `bridge/view` item in the chapter real-valued subdifferential API. The
owner abstraction is `subdifferentialAt`, and the source-facing scalar-slope statement is expressed
through its canonical one-dimensional vector-side bridge `euclideanSubdifferentialAt` from Theorem
3.4 rather than through an ad hoc encoding of real slopes as elements of `StrongDual ℝ ℝ`. -/
-- Semantic recall note: `lean_leansearch` found real-abs differentiability lemmas such as
-- `hasStrictDerivAt_abs` and `not_differentiableAt_abs_zero`, which support the same piecewise
-- split but do not replace this chapter-local Euclidean subdifferential statement.

recall euclideanSubdifferentialAt

-- Proof sketch: split into the cases `x > 0`, `x < 0`, and `x = 0`. For `x ≠ 0`, the function
-- `t ↦ |t|` is differentiable at `x`, so the supporting-line inequality forces the only possible
-- slope to be `Real.sign x`, and that slope indeed works. At `x = 0`, the inequality becomes
-- `|y| ≥ v * y` for all `y`; testing it on `1` and `-1` gives `-1 ≤ v ≤ 1`, and conversely every
-- `v ∈ [-1, 1]` defines a valid supporting line at the origin.
--
-- This is kept in the same piecewise shape used by nearby norm/subdifferential files, so later
-- coordinatewise sum arguments can reuse it without re-splitting on `x = 0`.
/-- Helper for Proposition 3.16: any slope `v ∈ [-1, 1]` satisfies the supporting-line inequality
`|y| ≥ v * y` at the origin. -/
lemma abs_subgradientIneq_zero_of_mem_Icc {v : ℝ} (hv : v ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ y : ℝ, |y| ≥ v * y := by
  intro y
  have hv_abs : |v| ≤ 1 := by
    exact abs_le.2 ⟨hv.1, hv.2⟩
  have hmul_abs : |v * y| ≤ |y| := by
    calc
      |v * y| = |v| * |y| := by rw [abs_mul]
      _ ≤ 1 * |y| := by
        exact mul_le_mul_of_nonneg_right hv_abs (abs_nonneg y)
      _ = |y| := by ring
  -- Compare `v * y` to `|v * y|`, then bound `|v * y|` by `|y|`.
  simpa [ge_iff_le] using le_trans (le_abs_self (v * y)) hmul_abs

/-- Helper for Proposition 3.16: at the origin, membership in the Euclidean/vector-side
subdifferential of `x ↦ |x|` is equivalent to lying in the interval `[-1, 1]`. -/
lemma mem_euclideanSubdifferentialAt_abs_zero_iff {z : ℝ} :
    z ∈ euclideanSubdifferentialAt (fun y : ℝ ↦ |y|) 0 ↔ z ∈ Set.Icc (-1 : ℝ) 1 := by
  -- Rewrite the Euclidean subgradient condition to the scalar supporting-line inequality.
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff]
  simp only [sub_zero, abs_zero, zero_add]
  have happly : ∀ y : ℝ, (toDualMap ℝ ℝ z : Module.Dual ℝ ℝ) y = z * y := by
    intro y
    simpa [InnerProductSpace.toDualMap_apply_apply] using (RCLike.inner_apply' z y)
  constructor
  · intro hz
    constructor
    · -- Testing the supporting-line inequality at `y = -1` yields the lower bound `-1 ≤ z`.
      have hneg : |(-1 : ℝ)| ≥ z * (-1 : ℝ) := by
        simpa [happly (-1)] using hz (-1)
      norm_num at hneg
      linarith
    · -- Testing the supporting-line inequality at `y = 1` yields the upper bound `z ≤ 1`.
      have hpos : |(1 : ℝ)| ≥ z * (1 : ℝ) := by
        simpa [happly 1] using hz 1
      norm_num at hpos
      linarith
  · intro hz y
    -- Every slope in `[-1, 1]` defines a valid supporting line at the origin.
    simpa [happly y] using abs_subgradientIneq_zero_of_mem_Icc hz y

/-- Helper for Proposition 3.16: the one-dimensional gradient of `x ↦ |x|` is `Real.sign x`. -/
lemma gradient_abs_eq_sign (x : ℝ) :
    ∇ (fun y : ℝ ↦ |y|) x = Real.sign x := by
  -- Route correction: normalize the gradient through `deriv`, then use the explicit one-variable
  -- derivative formulas for `|x|` instead of unfolding the gradient definition directly.
  rw [gradient_eq_deriv']
  by_cases hpos : 0 < x
  · rw [deriv_abs_pos hpos, Real.sign_of_pos hpos]
  · have hnonpos : x ≤ 0 := le_of_not_gt hpos
    by_cases hneg : x < 0
    · rw [deriv_abs_neg hneg, Real.sign_of_neg hneg]
    · have hx : x = 0 := le_antisymm hnonpos (le_of_not_gt hneg)
      subst hx
      rw [deriv_abs_zero]
      simp

/-- Proposition 3.16: for the one-dimensional function `g(x) = |x|`, the Euclidean/vector-side
subdifferential is the interval `[-1, 1]` at the origin and the singleton `{Real.sign x}` away
from the origin. The left-hand side is the canonical one-dimensional bridge
`euclideanSubdifferentialAt`, so the result is stated directly as a set of real slopes. -/
theorem euclidean_subdifferentialAt_abs_eq_piecewise
    (x : ℝ) :
    euclideanSubdifferentialAt (fun y : ℝ ↦ |y|) x =
      if x = 0 then
        Set.Icc (-1 : ℝ) 1
      else
        {Real.sign x} := by
  by_cases hx : x = 0
  · subst x
    -- At the origin, both sides reduce to the same interval-membership criterion.
    ext z
    rw [if_pos rfl]
    exact mem_euclideanSubdifferentialAt_abs_zero_iff
  · have hconvex : ConvexOn ℝ Set.univ (fun y : ℝ ↦ |y|) := by
      -- Reuse the standard convexity of the norm and rewrite `‖y‖` as `|y|` on `ℝ`.
      simpa [Real.norm_eq_abs] using
        (convexOn_univ_norm : ConvexOn ℝ Set.univ (fun y : ℝ ↦ ‖y‖))
    have hdiff : DifferentiableAt ℝ (fun y : ℝ ↦ |y|) x :=
      differentiableAt_abs hx
    -- Away from the origin, Proposition 3.14 identifies the subdifferential with the singleton
    -- containing the gradient, and the gradient simplifies to `Real.sign x`.
    rw [if_neg hx]
    simpa [gradient_abs_eq_sign x] using
      (euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt
        hconvex hdiff)

/-- Proposition 3.16 (1): for the one-dimensional function `g(x) = |x|`, the Euclidean/vector-side
subdifferential at `0` is the interval `[-1, 1]`. The left-hand side is the canonical
one-dimensional bridge `euclideanSubdifferentialAt`, so the result is stated directly as a set of
real slopes. -/
@[simp] theorem euclidean_subdifferentialAt_abs_zero :
    euclideanSubdifferentialAt (fun y : ℝ ↦ |y|) 0 = Set.Icc (-1 : ℝ) 1 := by
  simpa using euclidean_subdifferentialAt_abs_eq_piecewise 0

/-- Proposition 3.16 (2): for the one-dimensional function `g(x) = |x|`, the Euclidean/vector-side
subdifferential away from `0` is the singleton containing the slope `Real.sign x`. The left-hand
side is the canonical one-dimensional bridge `euclideanSubdifferentialAt`, so the result is stated
directly as a set of real slopes. -/
theorem euclidean_subdifferentialAt_abs_eq_singleton_sign_of_ne_zero
    {x : ℝ} (hx : x ≠ 0) :
    euclideanSubdifferentialAt (fun y : ℝ ↦ |y|) x = {Real.sign x} := by
  simpa [hx] using euclidean_subdifferentialAt_abs_eq_piecewise x

/-- Callable companion for Proposition 3.16: scalar membership in the Euclidean/vector-side
subdifferential of `x ↦ |x|` is exactly the sign condition away from `0` together with the interval
constraint `[-1, 1]` at `0`. -/
theorem mem_euclideanSubdifferentialAt_abs_iff_sign_or_bound
    {x z : ℝ} :
    z ∈ euclideanSubdifferentialAt (fun y : ℝ ↦ |y|) x ↔
      (x ≠ 0 → z = Real.sign x) ∧ (x = 0 → |z| ≤ 1) := by
  by_cases hx : x = 0
  · subst hx
    rw [euclidean_subdifferentialAt_abs_zero, Set.mem_Icc]
    constructor
    · rintro ⟨hz_left, hz_right⟩
      constructor
      · intro h
        exact (h rfl).elim
      · intro _
        exact abs_le.2 ⟨hz_left, hz_right⟩
    · rintro ⟨_, hz⟩
      exact abs_le.1 (hz rfl)
  · rw [euclidean_subdifferentialAt_abs_eq_singleton_sign_of_ne_zero hx, Set.mem_singleton_iff]
    constructor
    · intro hz
      constructor
      · intro _
        simpa using hz
      · intro hzero
        exact (hx hzero).elim
    · rintro ⟨hz, _⟩
      exact hz hx

end
