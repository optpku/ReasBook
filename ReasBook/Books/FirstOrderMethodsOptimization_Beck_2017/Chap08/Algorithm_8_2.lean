/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Algorithm 8.2 is `source-facing` in the chapter descent-method API. Because the algorithm
allows an arbitrary subgradient choice at each iterate, the recursive owner below is the iterate
sequence generated from an index-dependent direction-selection rule `g : ℕ → E → E`; the source
conditions that these selected directions satisfy the Euclidean subgradient inequality at the
current iterate and that the stepsizes are positive are recorded separately by an admissibility
predicate. -/

/-- Algorithm 8.2: given an initial point `x0`, step sizes `t_k`, and an index-dependent rule `g`
that selects the current direction from the current iterate, the subgradient method generates the
iterates by the update `x^{k+1} = x^k - t_k g_k(x^k)`. -/
def subgradient_method (g : ℕ → E → E) (t : ℕ → ℝ) (x0 : E) : ℕ → E
  | 0 => x0
  | k + 1 =>
      let xk := subgradient_method g t x0 k
      xk - t k • g k xk

-- Proof sketch: unfold the recursive definition of `subgradient_method` at `0`.
/-- The subgradient-method sequence starts at the prescribed initial point. -/
theorem subgradient_method_zero (g : ℕ → E → E) (t : ℕ → ℝ) (x0 : E) :
    subgradient_method g t x0 0 = x0 := by
  -- The base case is exactly the defining value of the recursive sequence.
  rfl

-- Proof sketch: unfold the recursive definition of `subgradient_method` at `k + 1`.
/-- One step of the subgradient method subtracts the current stepsize times the selected current
direction. -/
theorem subgradient_method_succ (g : ℕ → E → E) (t : ℕ → ℝ) (x0 : E) (k : ℕ) :
    subgradient_method g t x0 (k + 1) =
      subgradient_method g t x0 k - t k • g k (subgradient_method g t x0 k) := by
  -- Unfolding the recursive clause once gives the stated update formula.
  rfl

end

open scoped RealInnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A direction-selection rule is admissible for the subgradient method on `f` when, at each
iterate, the selected direction satisfies the Euclidean subgradient inequality for `f` at the
current iterate and the current stepsize is strictly positive. -/
def subgradient_method_is_admissible
    (f : E → ℝ) (g : ℕ → E → E) (t : ℕ → ℝ) (x0 : E) : Prop :=
  ∀ k,
    let xk := subgradient_method g t x0 k;
    (∀ y, f y ≥ f xk + inner ℝ (g k xk) (y - xk)) ∧ 0 < t k

-- Proof sketch: unfold `subgradient_method_is_admissible`, set
-- `xk = subgradient_method g t x0 k`, and specialize the defining condition at the index `k`.
/-- Under the admissibility condition, the selected direction at iteration `k` satisfies the
Euclidean subgradient inequality for `f` at the current iterate. -/
theorem subgradient_method_subgradient_inequality
    {f : E → ℝ} {g : ℕ → E → E} {t : ℕ → ℝ} {x0 : E}
    (h : subgradient_method_is_admissible f g t x0) (k : ℕ) :
    ∀ y,
      f y ≥
        f (subgradient_method g t x0 k) +
          inner ℝ (g k (subgradient_method g t x0 k))
            (y - subgradient_method g t x0 k) :=
  by
  -- Specializing admissibility at `k` exposes the conjunction for the current iterate.
  exact (h k).1

-- Proof sketch: unfold `subgradient_method_is_admissible` and read off the positivity clause at
-- the index `k`.
/-- Under the admissibility condition, every stepsize in the subgradient method is strictly
positive. -/
theorem subgradient_method_stepsize_pos
    {f : E → ℝ} {g : ℕ → E → E} {t : ℕ → ℝ} {x0 : E}
    (h : subgradient_method_is_admissible f g t x0) (k : ℕ) :
    0 < t k := by
  -- The positivity clause is the second component of admissibility at index `k`.
  exact (h k).2

end
