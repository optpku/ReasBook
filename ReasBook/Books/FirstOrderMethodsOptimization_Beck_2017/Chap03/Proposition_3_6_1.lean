/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

-- Declarations for this item will be appended below by the statement pipeline.

section

/- Proposition 3.6.1 is `source-facing`: it studies one concrete extended-real-valued example.
The primitive data is just the explicit function that equals `x ↦ -√x` on `[0, ∞)` and `⊤` on
`(-∞, 0)`. The proposition clauses stay at the chapter owners `is_convex_function` and
`subdifferential`, and the only extra API is the minimal pointwise evaluation interface for this
concrete source object. -/

/-- The extended-real function equal to `-√x` on the nonnegative ray and `∞` on the negative
half-line. -/
noncomputable def negative_sqrt_extension : ℝ → EReal :=
  fun x ↦ if 0 ≤ x then ((-Real.sqrt x : ℝ) : EReal) else ⊤

/-- Evaluating `negative_sqrt_extension` returns the defining piecewise formula. -/
@[simp] theorem negative_sqrt_extension_apply (x : ℝ) :
    negative_sqrt_extension x = if 0 ≤ x then ((-Real.sqrt x : ℝ) : EReal) else ⊤ :=
  rfl

/-- On the nonnegative ray, `negative_sqrt_extension` agrees with `x ↦ -√x`. -/
@[simp] theorem negative_sqrt_extension_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    negative_sqrt_extension x = ((-Real.sqrt x : ℝ) : EReal) := by
  simp [negative_sqrt_extension_apply, hx]

/-- On the negative ray, `negative_sqrt_extension` takes the value `⊤`. -/
@[simp] theorem negative_sqrt_extension_of_neg {x : ℝ} (hx : x < 0) :
    negative_sqrt_extension x = ⊤ := by
  simp [negative_sqrt_extension_apply, not_le_of_gt hx]

/-- The effective domain of `negative_sqrt_extension` is the nonnegative ray `[0, ∞)`. -/
theorem negative_sqrt_extension_effective_domain_eq :
    effective_domain negative_sqrt_extension = Set.Ici (0 : ℝ) := by
  ext x
  rw [mem_effective_domain, negative_sqrt_extension_apply]
  by_cases hx : 0 ≤ x
  · simpa [hx] using (EReal.coe_lt_top (-Real.sqrt x : ℝ))
  · simp [hx]

/-- A real number lies in the effective domain of `negative_sqrt_extension` exactly when it is
nonnegative. -/
@[simp] theorem mem_effective_domain_negative_sqrt_extension (x : ℝ) :
    x ∈ effective_domain negative_sqrt_extension ↔ 0 ≤ x := by
  rw [negative_sqrt_extension_effective_domain_eq]
  rfl

/-- Helper for Proposition 3.6.1: `negative_sqrt_extension` never takes the value `⊥` on its
effective domain. -/
lemma negativeSqrtExtension_neBotOnEffectiveDomain :
    ∀ x ∈ effective_domain negative_sqrt_extension, negative_sqrt_extension x ≠ ⊥ := by
  intro x hx
  -- On the effective domain the function is a coerced real value, hence finite and not `⊥`.
  rw [mem_effective_domain_negative_sqrt_extension] at hx
  rw [negative_sqrt_extension_of_nonneg hx]
  simp

/-- Helper for Proposition 3.6.1: on `[0, ∞)`, the real-valued restriction of
`negative_sqrt_extension` is `x ↦ -Real.sqrt x`. -/
lemma negativeSqrtExtension_toReal_eqOnIci :
    Set.EqOn (fun x ↦ (negative_sqrt_extension x).toReal) (fun x ↦ -Real.sqrt x)
      (Set.Ici (0 : ℝ)) := by
  intro x hx
  -- The nonnegative branch is a real coercion, so `toReal` recovers the original scalar.
  have hx_nonneg : 0 ≤ x := by
    simpa using hx
  simp [negative_sqrt_extension, hx_nonneg]

/-- Helper for Proposition 3.6.1: a dual vector on `ℝ` is determined by its value at `1`. -/
lemma realDual_apply_eq_mul_applyOne (g : Module.Dual ℝ ℝ) (y : ℝ) :
    g y = y * g 1 := by
  -- Rewrite `y` as a scalar multiple of `1` and use linearity once.
  calc
    g y = g (y • (1 : ℝ)) := by simp
    _ = y • g 1 := by rw [map_smul]
    _ = y * g 1 := by simp [smul_eq_mul]

/-- Helper for Proposition 3.6.1: the witness `1 / (4 * m^2)` violates the affine lower bound
with slope `m < 0`. -/
lemma negativeSqrtSmallWitness_ltLinearSlope {m : ℝ} (hm : m < 0) :
    -Real.sqrt (1 / (4 * m ^ 2)) < m * (1 / (4 * m ^ 2)) := by
  have hm_ne : m ≠ 0 := ne_of_lt hm
  have hneg_two_mul_pos : 0 < -2 * m := by
    nlinarith
  have hsquare :
      (1 / (-2 * m)) ^ 2 = 1 / (4 * m ^ 2) := by
    field_simp [hm_ne]
    ring
  have hsqrt :
      Real.sqrt (1 / (4 * m ^ 2)) = 1 / (-2 * m) := by
    -- Normalize the square root by rewriting the witness as a square of a positive number.
    rw [← hsquare, Real.sqrt_sq_eq_abs]
    have hpos : 0 < 1 / (-2 * m) := one_div_pos.mpr hneg_two_mul_pos
    exact abs_of_nonneg (le_of_lt hpos)
  have hleft :
      -Real.sqrt (1 / (4 * m ^ 2)) = 1 / (2 * m) := by
    rw [hsqrt]
    field_simp [hm_ne]
  have hright :
      m * (1 / (4 * m ^ 2)) = 1 / (4 * m) := by
    field_simp [hm_ne]
  -- After reducing both sides to rational expressions in `m`, clear denominators.
  rw [hleft, hright]
  set t : ℝ := -m with ht
  have ht_pos : 0 < t := by
    dsimp [t]
    linarith
  have hm_eq : m = -t := by
    linarith
  have h2t_pos : 0 < 2 * t := by positivity
  have h2t_lt_4t : 2 * t < 4 * t := by
    nlinarith
  have hdiv : 1 / (4 * t) < 1 / (2 * t) := by
    exact one_div_lt_one_div_of_lt h2t_pos h2t_lt_4t
  have hneg : -(1 / (2 * t)) < -(1 / (4 * t)) := by
    exact neg_lt_neg hdiv
  simpa [hm_eq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hneg

-- Proof sketch: `negative_sqrt_extension` never takes the value `⊥`, so the bridge
-- `is_convex_function_iff_convexOn_toReal` reduces the owner-level convexity claim to convexity of
-- the finite restriction on its effective domain, computed locally as `[0, ∞)`. On that ray the
-- function is `x ↦ -Real.sqrt x`, which is convex because `Real.sqrt` is concave on the
-- nonnegative ray.
/-- The convexity clause of Proposition 3.6.1: `negative_sqrt_extension` is convex. -/
theorem negative_sqrt_extension_is_convex_function :
    is_convex_function negative_sqrt_extension := by
  -- Use the Chapter 2 bridge to move convexity to the real-valued restriction on the domain.
  refine (is_convex_function_iff_convexOn_toReal
    (f := negative_sqrt_extension) negativeSqrtExtension_neBotOnEffectiveDomain).mpr ?_
  rw [negative_sqrt_extension_effective_domain_eq]
  -- Transport the claim to the canonical real function `x ↦ -Real.sqrt x` on `[0, ∞)`.
  exact (Real.strictConcaveOn_sqrt.concaveOn.neg).congr <| by
    intro x hx
    simpa using (negativeSqrtExtension_toReal_eqOnIci hx).symm

-- Proof sketch: assume `g ∈ ∂ negative_sqrt_extension(0)`. The subgradient inequality
-- then gives `-Real.sqrt y ≥ g * y` for every `y ≥ 0`. Evaluating at `y = 1` forces `g < 0`, and
-- taking `y = 1 / (2 * g ^ 2)` yields a contradiction.
/-- Proposition 3.6.1 (2): the subdifferential of `negative_sqrt_extension` at `0` is empty, so
the function is not subdifferentiable there. -/
theorem negative_sqrt_extension_subdifferential_zero :
    ∂ negative_sqrt_extension(0) = ∅ := by
  ext g
  constructor
  · intro hg
    rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hg
    rcases hg with ⟨_, hsubgrad⟩
    let m : ℝ := g 1
    have hzero : negative_sqrt_extension 0 = ((0 : ℝ) : EReal) := by
      simp
    have hone_mem : (1 : ℝ) ∈ effective_domain negative_sqrt_extension := by
      rw [mem_effective_domain_negative_sqrt_extension]
      norm_num
    have honeE : ((m : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) := by
      -- Evaluating at `y = 1` forces the scalar slope `m` to be at most `-1`.
      have hone := hsubgrad 1 hone_mem
      rw [negative_sqrt_extension_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num), hzero, sub_zero] at hone
      have hone' : ((-1 : ℝ) : EReal) ≥ ((m : ℝ) : EReal) := by
        simpa [m] using hone
      simpa [ge_iff_le] using hone'
    have hm_le : m ≤ -1 := EReal.coe_le_coe_iff.mp honeE
    have hm_neg : m < 0 := by
      linarith
    let y : ℝ := 1 / (4 * m ^ 2)
    have hy_mem : y ∈ effective_domain negative_sqrt_extension := by
      -- The contradiction witness is positive because `m < 0` implies `m^2 > 0`.
      rw [mem_effective_domain_negative_sqrt_extension]
      have hm_sq_pos : 0 < m ^ 2 := by
        nlinarith [hm_neg]
      have hden_pos : 0 < 4 * m ^ 2 := by
        nlinarith
      dsimp [y]
      exact le_of_lt (one_div_pos.mpr hden_pos)
    have hy_nonneg : 0 ≤ y := by
      exact (mem_effective_domain_negative_sqrt_extension y).mp hy_mem
    have hyE :
        ((m * y : ℝ) : EReal) ≤ ((-Real.sqrt y : ℝ) : EReal) := by
      -- Evaluating the subgradient inequality at the witness gives the scalar lower bound.
      have hy_subgrad := hsubgrad y hy_mem
      rw [negative_sqrt_extension_of_nonneg hy_nonneg, hzero, sub_zero] at hy_subgrad
      have hy_eval : g y = m * y := by
        calc
          g y = y * g 1 := realDual_apply_eq_mul_applyOne g y
          _ = y * m := by rfl
          _ = m * y := by rw [mul_comm]
      rw [hy_eval] at hy_subgrad
      have hy_subgrad' : ((-Real.sqrt y : ℝ) : EReal) ≥ ((m * y : ℝ) : EReal) := by
        simpa using hy_subgrad
      simpa [ge_iff_le] using hy_subgrad'
    have hy : m * y ≤ -Real.sqrt y := EReal.coe_le_coe_iff.mp hyE
    have hstrict : -Real.sqrt y < m * y := by
      -- The arithmetic helper shows the witness contradicts any negative affine lower bound.
      simpa [y, mul_comm] using negativeSqrtSmallWitness_ltLinearSlope hm_neg
    simpa using (not_le_of_gt hstrict) hy
  · intro hg
    exact False.elim hg

end
