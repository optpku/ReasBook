/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 6.11 is `source-facing` in the Chapter 6 extended-real convex-analysis API.
Domain sampling against nearby scalar/object owners shows:

- `positive_reciprocal_barrier` from Chapter 2 is the existing project pattern for a scalar
  extended-real function defined by a finite branch on a positivity domain and `⊤` elsewhere;
- `huber_function` from Definition 6.8 is the nearby Chapter 6 source-facing owner for a named
  textbook penalty, with the pointwise evaluation formula kept as derived API;
- `l1SquareVariationalSummand` from Lemma 6.69 is only a downstream use of this same quadratic-
  over-linear scalar pattern inside a simplex objective, not a second owner.

There is no upstream mathlib/project owner for this exact extended-real quadratic-over-linear
function, so the canonical owner abstraction in this chapter is the source-facing declaration
`quadratic_over_linear` itself. The primitive data are only the pair `(s, t)`; the displayed
piecewise formula is derived API. -/

/-- Definition 6.11: the extended-real quadratic-over-linear function `φ : ℝ × ℝ → EReal` given
by `φ(s, t) = s^2 / t` for `t > 0`, `φ(0, 0) = 0`, and `φ(s, t) = ∞` in all other cases. -/
def quadratic_over_linear : ℝ × ℝ → EReal :=
  fun p ↦
    if 0 < p.2 then
      ((p.1 ^ (2 : ℕ) / p.2 : ℝ) : EReal)
    else if p.1 = 0 ∧ p.2 = 0 then
      0
    else
      ⊤

@[inherit_doc] notation "φ" => quadratic_over_linear

-- Proof sketch: unfold `quadratic_over_linear`; the displayed piecewise formula is exactly the
-- defining expression specialized to the pair `(s, t)`.
/-- Evaluating `φ` at `(s, t)` gives the textbook piecewise formula. -/
@[simp] theorem quadratic_over_linear_apply (s t : ℝ) :
    φ (s, t) =
      if 0 < t then
        ((s ^ (2 : ℕ) / t : ℝ) : EReal)
      else if s = 0 ∧ t = 0 then
        0
      else
        ⊤ :=
  rfl

-- Proof sketch: this is the defining equation of `quadratic_over_linear`, so the function-level
-- identity is definitional.
/-- The notation `φ` denotes the quadratic-over-linear function written in its defining
piecewise form on `ℝ × ℝ`. -/
@[simp] theorem quadratic_over_linear_def :
    (φ : ℝ × ℝ → EReal) =
      fun p ↦
        if 0 < p.2 then
          ((p.1 ^ (2 : ℕ) / p.2 : ℝ) : EReal)
        else if p.1 = 0 ∧ p.2 = 0 then
          0
        else
          ⊤ :=
  rfl

-- Proof sketch: in the branch `0 < t`, the defining `if` in `quadratic_over_linear_apply`
-- simplifies by `if_pos ht`.
/-- On the half-plane `t > 0`, the quadratic-over-linear function agrees with its finite
quadratic branch. -/
theorem quadratic_over_linear_of_pos {s t : ℝ} (ht : 0 < t) :
    φ (s, t) = ((s ^ (2 : ℕ) / t : ℝ) : EReal) := by
  simp [quadratic_over_linear, ht]

-- Proof sketch: evaluate `quadratic_over_linear_apply` at `(0, 0)`; both `if` tests simplify to
-- the zero-zero branch.
/-- At the origin, the quadratic-over-linear function takes the value `0`. -/
@[simp] theorem quadratic_over_linear_zero_zero :
    φ (0, 0) = 0 := by
  simp [quadratic_over_linear]

-- Proof sketch: if `t ≤ 0` and `(s, t) ≠ (0, 0)`, both defining branches in
-- `quadratic_over_linear_apply` are false, so the value is `⊤`.
/-- Outside the positive-`t` branch and away from the origin, the quadratic-over-linear function
takes the value `∞`. -/
theorem quadratic_over_linear_of_nonpos_of_ne_origin {s t : ℝ} (ht : t ≤ 0)
    (hst : (s, t) ≠ (0, 0)) :
    φ (s, t) = ⊤ := by
  have hst' : ¬ (s = 0 ∧ t = 0) := by
    rintro ⟨rfl, rfl⟩
    exact hst rfl
  simp [quadratic_over_linear, ht, hst']
