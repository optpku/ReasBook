/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_8
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Definition_14_4
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Definition_14_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 14.1 is `source-facing`: it studies the distinguished line of coordinatewise minima
for the Chapter 14 counterexample objective. Domain sampling against the existing Chapter 14 API
identifies the following owner split.
- `source-facing`: Definition 14.4's real-valued owner
  `alternating_minimization_failure_ii_objective`;
- `core/canonical`: `is_coordinatewise_minimum` from Definition 14.2;
- `source-facing` companion owners: the pair section owners
  `two_block_alternating_minimization_x1_objective` and
  `two_block_alternating_minimization_x2_objective` from Algorithm 14.8;
- `bridge/view`: the canonical coercion `Function.toEReal` from Definition 9.2; and
- `bridge/view`: `two_block_alternating_minimization_objective_blocks` and
  `two_block_alternating_minimization_state` from Algorithm 14.8.

Accordingly, the objective itself is not redefined here: the file reuses Definition 14.4's owner
through its canonical `EReal` view. The primitive data kept here are only the distinguished line
of counterexample points and the resulting minimizer statements on that fixed objective. The main
coordinatewise-minimality statement therefore uses the Chapter 14 owner
`is_coordinatewise_minimum` on the canonical two-block block-vector view, while the textbook pair
sections are kept only as a thin source-facing companion theorem. -/

local notation "F" => alternating_minimization_failure_ii_objective.toEReal
local notation "g₀" => (0 : ℝ → EReal)
local notation "F₂" =>
  two_block_alternating_minimization_objective_blocks
    F
    g₀
    g₀

/-- Helper for Proposition 14.1: the real-valued counterexample objective vanishes exactly at the
origin. -/
lemma alternating_minimization_failure_ii_objective_eq_zero_iff
    (x : ℝ × ℝ) :
    alternating_minimization_failure_ii_objective x = 0 ↔ x = 0 := by
  rcases x with ⟨x₁, x₂⟩
  constructor
  · intro hx
    -- Split the vanishing sum of absolute values into vanishing linear forms.
    rw [alternating_minimization_failure_ii_objective_apply] at hx
    have h34 : |3 * x₁ + 4 * x₂| = 0 := by
      nlinarith [abs_nonneg (3 * x₁ + 4 * x₂), abs_nonneg (x₁ - 2 * x₂)]
    have h12 : |x₁ - 2 * x₂| = 0 := by
      nlinarith [abs_nonneg (3 * x₁ + 4 * x₂), abs_nonneg (x₁ - 2 * x₂)]
    have h34' : 3 * x₁ + 4 * x₂ = 0 := abs_eq_zero.mp h34
    have h12' : x₁ - 2 * x₂ = 0 := abs_eq_zero.mp h12
    -- Solve the resulting linear system to recover the origin.
    have hx₁ : x₁ = 0 := by
      linarith
    have hx₂ : x₂ = 0 := by
      linarith
    simp [hx₁, hx₂]
  · intro hx
    -- At the origin both absolute-value terms vanish definitionally.
    cases hx
    simp [alternating_minimization_failure_ii_objective_apply]

/-- Helper for Proposition 14.1: the objective value along the distinguished line
`(-4 * α, 3 * α)` is `10 * |α|`. -/
lemma alternating_minimization_counterexample_line_value
    (α : ℝ) :
    alternating_minimization_failure_ii_objective (-4 * α, 3 * α) = 10 * |α| := by
  -- Evaluate the two linear forms on the distinguished line and simplify the absolute values.
  rw [alternating_minimization_failure_ii_objective_apply]
  have h34 : 3 * (-4 * α) + 4 * (3 * α) = 0 := by
    ring
  have h12 : -4 * α - 2 * (3 * α) = -(10 * α) := by
    ring
  rw [h34, h12, abs_zero, abs_neg]
  simp only [zero_add]
  calc
    |10 * α| = |(10 : ℝ)| * |α| := abs_mul 10 α
    _ = 10 * |α| := by norm_num

/-- Helper for Proposition 14.1: with the second coordinate fixed at `3 * α`, the objective is
bounded below by `10 * |α|`. -/
lemma alternating_minimization_counterexample_x1_section_lower_bound
    (α y : ℝ) :
    10 * |α| ≤ alternating_minimization_failure_ii_objective (y, 3 * α) := by
  -- Rewrite the section so the triangle inequality sees the two shifted coordinates directly.
  rw [alternating_minimization_failure_ii_objective_apply]
  have h34 : 3 * y + 4 * (3 * α) = 3 * (y + 4 * α) := by
    ring
  have h12 : y - 2 * (3 * α) = y - 6 * α := by
    ring
  rw [h34, h12, abs_mul]
  norm_num
  have htriangle_raw : |(y + 4 * α) - (y - 6 * α)| ≤ |y + 4 * α| + |y - 6 * α| :=
    abs_sub (y + 4 * α) (y - 6 * α)
  have hdiff : (y + 4 * α) - (y - 6 * α) = 10 * α := by
    ring
  have htriangle' : |10 * α| ≤ |y + 4 * α| + |y - 6 * α| := by
    rw [← hdiff]
    exact htriangle_raw
  have htriangle : 10 * |α| ≤ |y + 4 * α| + |y - 6 * α| := by
    simpa [abs_mul] using htriangle'
  -- The extra `2 * |y + 4 * α|` term makes the section value at least this triangle bound.
  nlinarith [htriangle, abs_nonneg (y + 4 * α)]

/-- Helper for Proposition 14.1: with the first coordinate fixed at `-4 * α`, the objective is
bounded below by `10 * |α|`. -/
lemma alternating_minimization_counterexample_x2_section_lower_bound
    (α y : ℝ) :
    10 * |α| ≤ alternating_minimization_failure_ii_objective (-4 * α, y) := by
  -- Rewrite the section so the triangle inequality sees the two shifted coordinates directly.
  rw [alternating_minimization_failure_ii_objective_apply]
  have h34 : 3 * (-4 * α) + 4 * y = 4 * (y - 3 * α) := by
    ring
  have h12 : -4 * α - 2 * y = -(2 * (y + 2 * α)) := by
    ring
  rw [h34, h12, abs_mul, abs_neg]
  norm_num
  have htriangle_raw : |(y + 2 * α) - (y - 3 * α)| ≤ |y + 2 * α| + |y - 3 * α| :=
    abs_sub (y + 2 * α) (y - 3 * α)
  have hdiff : (y + 2 * α) - (y - 3 * α) = 5 * α := by
    ring
  have htriangle' : |5 * α| ≤ |y + 2 * α| + |y - 3 * α| := by
    rw [← hdiff]
    exact htriangle_raw
  have htriangle : 5 * |α| ≤ |y + 2 * α| + |y - 3 * α| := by
    simpa [abs_mul] using htriangle'
  -- The extra `2 * |y - 3 * α|` term upgrades the triangle bound to the section value.
  nlinarith [htriangle, abs_nonneg (y - 3 * α)]

-- Proof sketch: the objective is nonnegative as a sum of absolute values, and it vanishes exactly
-- when the linear system `3 x₁ + 4 x₂ = 0` and `x₁ - 2 x₂ = 0` holds, whose unique solution is
-- `(0, 0)`.
/-- First claim of Proposition 14.1: the counterexample objective has the origin as its unique
global minimizer. -/
theorem alternating_minimization_counterexample_unique_minimizer
    (x : ℝ × ℝ) :
    IsMinOn F Set.univ x ↔ x = 0 := by
  constructor
  · intro hx
    rw [isMinOn_univ_iff] at hx
    -- Compare the candidate minimizer against the origin and collapse to the zero set.
    have hle : alternating_minimization_failure_ii_objective x ≤
        alternating_minimization_failure_ii_objective 0 := by
      simpa [Function.toEReal] using hx (0 : ℝ × ℝ)
    have hnonneg : 0 ≤ alternating_minimization_failure_ii_objective x := by
      rcases x with ⟨x₁, x₂⟩
      rw [alternating_minimization_failure_ii_objective_apply]
      positivity
    have hzero : alternating_minimization_failure_ii_objective x = 0 := by
      have hzero_right : alternating_minimization_failure_ii_objective (0 : ℝ × ℝ) = 0 := by
        change alternating_minimization_failure_ii_objective (0, 0) = 0
        norm_num [alternating_minimization_failure_ii_objective_apply]
      rw [hzero_right] at hle
      exact le_antisymm hle hnonneg
    exact (alternating_minimization_failure_ii_objective_eq_zero_iff x).mp hzero
  · rintro rfl
    rw [isMinOn_univ_iff]
    intro y
    -- The origin has value `0`, and every other value is nonnegative.
    have hy_nonneg : 0 ≤ alternating_minimization_failure_ii_objective y := by
      rcases y with ⟨y₁, y₂⟩
      rw [alternating_minimization_failure_ii_objective_apply]
      positivity
    have hzero_right : alternating_minimization_failure_ii_objective (0 : ℝ × ℝ) = 0 := by
      change alternating_minimization_failure_ii_objective (0, 0) = 0
      norm_num [alternating_minimization_failure_ii_objective_apply]
    simpa [Function.toEReal, hzero_right] using hy_nonneg

/-- Proposition 14.1 (2): every point `(-4 * α, 3 * α)` on the distinguished line is a
coordinate-wise minimum of the counterexample objective in the Chapter 14 two-block owner sense. -/
theorem alternating_minimization_counterexample_is_coordinatewise_minimum
    (α : ℝ) :
    is_coordinatewise_minimum F₂ (two_block_alternating_minimization_state (-4 * α) (3 * α)) :=
  by
  refine ⟨?_, ?_⟩
  · -- The real-valued objective stays finite everywhere after coercion to `EReal`.
    rw [effective_domain]
    change two_block_alternating_minimization_objective F 0 0 (-4 * α, 3 * α) < ⊤
    simpa [two_block_alternating_minimization_objective, Function.toEReal, Pi.zero_apply] using
      (EReal.coe_lt_top (alternating_minimization_failure_ii_objective (-4 * α, 3 * α)))
  intro i
  fin_cases i
  · rw [isMinOn_univ_iff]
    intro y
    -- Normalize the block-`0` objective to the real-valued `x₁`-section and apply the lower bound.
    change alternating_minimization_block_objective
        F₂
        (two_block_alternating_minimization_state (-4 * α) (3 * α))
        (two_block_alternating_minimization_state (-4 * α) (3 * α))
        0
        (-4 * α) ≤
      alternating_minimization_block_objective
        F₂
        (two_block_alternating_minimization_state (-4 * α) (3 * α))
        (two_block_alternating_minimization_state (-4 * α) (3 * α))
        0
        y
    rw [two_block_alternating_minimization_block_objective_zero_apply,
      two_block_alternating_minimization_block_objective_zero_apply]
    calc
      two_block_alternating_minimization_x1_objective F g₀ g₀ (3 * α) (-4 * α)
          = ((10 * |α| : ℝ) : EReal) := by
            simpa [two_block_alternating_minimization_x1_objective_apply, Function.toEReal,
              Pi.zero_apply] using
              congrArg (fun r : ℝ ↦ (r : EReal))
                (alternating_minimization_counterexample_line_value α)
      _ ≤ two_block_alternating_minimization_x1_objective F g₀ g₀ (3 * α) y := by
        -- Cast the real lower bound first, then rewrite the section back to the one-block owner.
        have hbound :
            ((10 * |α| : ℝ) : EReal) ≤
              ((alternating_minimization_failure_ii_objective (y, 3 * α) : ℝ) : EReal) := by
          exact_mod_cast alternating_minimization_counterexample_x1_section_lower_bound α y
        calc
          ((10 * |α| : ℝ) : EReal) ≤
              ((alternating_minimization_failure_ii_objective (y, 3 * α) : ℝ) : EReal) := hbound
          _ = two_block_alternating_minimization_x1_objective F g₀ g₀ (3 * α) y := by
            rw [two_block_alternating_minimization_x1_objective_apply]
            change ((alternating_minimization_failure_ii_objective (y, 3 * α) : ℝ) : EReal) =
              ((alternating_minimization_failure_ii_objective (y, 3 * α) : ℝ) : EReal) +
                (0 : EReal) + (0 : EReal)
            norm_num
  · rw [isMinOn_univ_iff]
    intro y
    -- Normalize the block-`1` objective to the real-valued `x₂`-section and apply the lower bound.
    change alternating_minimization_block_objective
        F₂
        (two_block_alternating_minimization_state (-4 * α) (3 * α))
        (two_block_alternating_minimization_state (-4 * α) (3 * α))
        1
        (3 * α) ≤
      alternating_minimization_block_objective
        F₂
        (two_block_alternating_minimization_state (-4 * α) (3 * α))
        (two_block_alternating_minimization_state (-4 * α) (3 * α))
        1
        y
    rw [two_block_alternating_minimization_block_objective_one_apply,
      two_block_alternating_minimization_block_objective_one_apply]
    calc
      two_block_alternating_minimization_x2_objective F g₀ g₀ (-4 * α) (3 * α)
          = ((10 * |α| : ℝ) : EReal) := by
            simpa [two_block_alternating_minimization_x2_objective_apply, Function.toEReal,
              Pi.zero_apply] using
              congrArg (fun r : ℝ ↦ (r : EReal))
                (alternating_minimization_counterexample_line_value α)
      _ ≤ two_block_alternating_minimization_x2_objective F g₀ g₀ (-4 * α) y := by
        -- Cast the real lower bound first, then rewrite the section back to the one-block owner.
        have hbound :
            ((10 * |α| : ℝ) : EReal) ≤
              ((alternating_minimization_failure_ii_objective (-4 * α, y) : ℝ) : EReal) := by
          exact_mod_cast alternating_minimization_counterexample_x2_section_lower_bound α y
        calc
          ((10 * |α| : ℝ) : EReal) ≤
              ((alternating_minimization_failure_ii_objective (-4 * α, y) : ℝ) : EReal) := hbound
          _ = two_block_alternating_minimization_x2_objective F g₀ g₀ (-4 * α) y := by
            rw [two_block_alternating_minimization_x2_objective_apply]
            change ((alternating_minimization_failure_ii_objective (-4 * α, y) : ℝ) : EReal) =
              ((alternating_minimization_failure_ii_objective (-4 * α, y) : ℝ) : EReal) +
                (0 : EReal) + (0 : EReal)
            norm_num

/-- Source-facing companion: every point `(-4 * α, 3 * α)` on the distinguished line lies in the
effective domain of the counterexample objective. -/
theorem alternating_minimization_counterexample_line_mem_effective_domain
    (α : ℝ) :
    (-4 * α, 3 * α) ∈ effective_domain F := by
  rw [effective_domain]
  change ((alternating_minimization_failure_ii_objective (-4 * α, 3 * α) : ℝ) : EReal) < ⊤
  exact EReal.coe_lt_top _

/-- Source-facing companion: along the distinguished line, the two textbook section objectives are
globally minimized at their displayed coordinates. -/
theorem alternating_minimization_counterexample_sections_isMinOn
    (α : ℝ) :
    IsMinOn (two_block_alternating_minimization_x1_objective F g₀ g₀ (3 * α)) Set.univ
      (-4 * α) ∧
      IsMinOn (two_block_alternating_minimization_x2_objective F g₀ g₀ (-4 * α)) Set.univ
        (3 * α) := by
  constructor
  · rw [isMinOn_iff]
    intro y hy
    have h :=
      (isMinOn_iff.mp
        ((alternating_minimization_counterexample_is_coordinatewise_minimum α).isMinOn 0)) y hy
    convert h using 1
  · rw [isMinOn_iff]
    intro y hy
    have h :=
      (isMinOn_iff.mp
        ((alternating_minimization_counterexample_is_coordinatewise_minimum α).isMinOn 1)) y hy
    convert h using 1

/-- Source-facing companion: along the distinguished line, the textbook `x₁`-section of the
counterexample objective is globally minimized at `-4 * α`. -/
theorem alternating_minimization_counterexample_x1_section_isMinOn
    (α : ℝ) :
    IsMinOn (two_block_alternating_minimization_x1_objective F g₀ g₀ (3 * α)) Set.univ
      (-4 * α) :=
  (alternating_minimization_counterexample_sections_isMinOn α).1

/-- Source-facing companion: along the distinguished line, the textbook `x₂`-section of the
counterexample objective is globally minimized at `3 * α`. -/
theorem alternating_minimization_counterexample_x2_section_isMinOn
    (α : ℝ) :
    IsMinOn (two_block_alternating_minimization_x2_objective F g₀ g₀ (-4 * α)) Set.univ
      (3 * α) :=
  (alternating_minimization_counterexample_sections_isMinOn α).2
