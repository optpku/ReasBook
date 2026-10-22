/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

noncomputable section

section

variable {E : Type u} {m : ℕ}
variable [NormedAddCommGroup E]

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/- Algorithm 8.14 is `source-facing`: the textbook specifies the dual multiplier iterate `λ^k`,
the chosen primal minimizer `x^k ∈ argmin_X L(·, λ^k)`, and the normalized positive-part update
driven by the Euclidean constraint vector `g(x^k)`. The new public objects here are the explicit
constraint vector, one-step multiplier update, and recursive multiplier sequence itself, while the
Lagrangian minimization step is recorded directly through `IsMinOn` on the displayed objective. -/

/-- The constraint vector `g(x)` attached to a primal point `x`, viewed in the Euclidean
multiplier space `ℝ^m`. -/
def dual_projected_subgradient_constraint_vector
    (g : Fin m → E → ℝ) (x : E) : Λ :=
  WithLp.toLp 2 (fun i ↦ g i x)

-- Proof sketch: unfold `dual_projected_subgradient_constraint_vector`; the `i`-th coordinate is
-- definitionally the `i`-th constraint value `g i x`.
/-- Evaluating `dual_projected_subgradient_constraint_vector g x` at `i` returns `g_i(x)`. -/
@[simp] theorem dual_projected_subgradient_constraint_vector_apply
    (g : Fin m → E → ℝ) (x : E) (i : Fin m) :
    dual_projected_subgradient_constraint_vector g x i = g i x := by
  -- Unfold the constraint vector once; its coordinates are exactly the constraint values.
  rfl

/-- The positive-part multiplier update
`[λ + γ g(x) / ‖g(x)‖]_+`, written coordinatewise in `ℝ_+^m`. -/
def dual_projected_subgradient_multiplier_update
    (g : Fin m → E → ℝ) (γ : ℝ) (lam : Fin m → NNReal) (x : E) : Fin m → NNReal :=
  fun i ↦
    Real.toNNReal
      ((lam i : ℝ) +
        γ * dual_projected_subgradient_constraint_vector g x i /
          ‖dual_projected_subgradient_constraint_vector g x‖)

-- Proof sketch: unfold `dual_projected_subgradient_multiplier_update`; the `i`-th coordinate is
-- definitionally the coordinatewise positive part of
-- `(λ i : ℝ) + γ * g_i(x) / ‖g(x)‖`.
/-- The `i`-th coordinate of the multiplier update is the positive part of the normalized
subgradient step in that coordinate. -/
@[simp] theorem dual_projected_subgradient_multiplier_update_apply
    (g : Fin m → E → ℝ) (γ : ℝ) (lam : Fin m → NNReal) (x : E) (i : Fin m) :
    dual_projected_subgradient_multiplier_update g γ lam x i =
      Real.toNNReal
        ((lam i : ℝ) +
          γ * dual_projected_subgradient_constraint_vector g x i /
            ‖dual_projected_subgradient_constraint_vector g x‖) := by
  -- Unfold the update once; the `i`-th coordinate is definitionally the displayed formula.
  rfl

/-- Algorithm 8.14: given an initial multiplier `λ^0 ∈ ℝ_+^m`, positive stepsizes `γ_k`, and a
rule selecting for each multiplier `λ` a minimizer of the Lagrangian over `X`, the dual projected
subgradient method generates the multiplier sequence `λ^k`; if `g(x^k) = 0` it stays at `λ^k`,
and otherwise updates by
`λ^{k+1} = [λ^k + γ_k g(x^k) / ‖g(x^k)‖]_+`, where `x^k` is the selected Lagrangian minimizer at
`λ^k`. -/
def dual_projected_subgradient_method
    (X : Set E) (g : Fin m → E → ℝ)
    (xSel : (Fin m → NNReal) → {x // x ∈ X}) (γ : ℕ → ℝ) (lam0 : Fin m → NNReal) :
    ℕ → Fin m → NNReal
  | 0 => lam0
  | k + 1 =>
      let lamk := dual_projected_subgradient_method X g xSel γ lam0 k
      let xk := xSel lamk
      if dual_projected_subgradient_constraint_vector g (xk : E) = 0 then
        lamk
      else
        dual_projected_subgradient_multiplier_update g (γ k) lamk xk

/-- The primal point selected from `argmin_X (f + λ^T g)` at the current multiplier iterate. -/
def dual_projected_subgradient_primal_iterate
    (X : Set E) (g : Fin m → E → ℝ)
    (xSel : (Fin m → NNReal) → {x // x ∈ X}) (γ : ℕ → ℝ) (lam0 : Fin m → NNReal)
    (k : ℕ) : {x // x ∈ X} :=
  xSel (dual_projected_subgradient_method X g xSel γ lam0 k)

/-- A selection rule and stepsize sequence are admissible for the dual projected subgradient
method when every stepsize is positive and each selected point minimizes the corresponding
Lagrangian over `X`. -/
def dual_projected_subgradient_method_is_admissible
    (X : Set E) (f : E → ℝ) (g : Fin m → E → ℝ)
    (xSel : (Fin m → NNReal) → {x // x ∈ X}) (γ : ℕ → ℝ) : Prop :=
  (∀ k : ℕ, 0 < γ k) ∧
    ∀ lam : Fin m → NNReal,
      IsMinOn (fun x ↦ f x + ∑ i, (lam i : ℝ) * g i x) X (xSel lam : E)

section

variable (X : Set E) (g : Fin m → E → ℝ)
variable (xSel : (Fin m → NNReal) → {x // x ∈ X}) (γ : ℕ → ℝ) (lam0 : Fin m → NNReal)

local notation "lam[" k "]" =>
  dual_projected_subgradient_method X g xSel γ lam0 k

local notation "x[" k "]" =>
  dual_projected_subgradient_primal_iterate X g xSel γ lam0 k

-- Proof sketch: unfold the recursive definition of `dual_projected_subgradient_method` at `0`.
/-- The dual projected-subgradient multiplier sequence starts at the prescribed initial multiplier.
-/
@[simp] theorem dual_projected_subgradient_method_zero :
    lam[0] = lam0 := by
  -- The recursive definition returns the initial multiplier at the base index.
  rfl

-- Proof sketch: unfold `dual_projected_subgradient_primal_iterate`; by definition `x^k` is
-- obtained by applying the selection rule `xSel` to the current multiplier iterate `λ^k`.
/-- The primal iterate `x^k` is obtained by applying the minimizer-selection rule to `λ^k`. -/
@[simp] theorem dual_projected_subgradient_primal_iterate_eq (k : ℕ) :
    x[k] = xSel lam[k] := by
  -- By definition, the primal iterate is selected from the current multiplier iterate.
  rfl

-- Proof sketch: unfold the recursive clause of `dual_projected_subgradient_method` at `k + 1`
-- and simplify the `if` using the assumption that the current constraint vector vanishes.
/-- If the current constraint vector is zero, the multiplier iterate does not move. -/
theorem dual_projected_subgradient_method_succ_of_constraint_vector_eq_zero
    (k : ℕ)
    (hk : dual_projected_subgradient_constraint_vector g (x[k] : E) = 0) :
    lam[k + 1] = lam[k] := by
  -- Rewrite the zero-constraint hypothesis in terms of the selected point `xSel lam[k]`.
  have hk' : dual_projected_subgradient_constraint_vector g ((xSel lam[k] : {x // x ∈ X}) : E) = 0 := by
    simpa [dual_projected_subgradient_primal_iterate] using hk
  -- Unfold one recursion step and simplify the zero branch of the update rule.
  simp [dual_projected_subgradient_method, hk']

-- Proof sketch: unfold the recursive clause of `dual_projected_subgradient_method` at `k + 1`
-- and simplify the `if` using the assumption that the current constraint vector is nonzero.
/-- If the current constraint vector is nonzero, the next multiplier iterate is the normalized
positive-part update from Algorithm 8.14. -/
theorem dual_projected_subgradient_method_succ_of_constraint_vector_ne_zero
    (k : ℕ)
    (hk : dual_projected_subgradient_constraint_vector g (x[k] : E) ≠ 0) :
    lam[k + 1] =
      dual_projected_subgradient_multiplier_update g (γ k) lam[k] x[k] := by
  -- Rewrite the nonzero-constraint hypothesis in terms of the selected point `xSel lam[k]`.
  have hk' : dual_projected_subgradient_constraint_vector g ((xSel lam[k] : {x // x ∈ X}) : E) ≠ 0 := by
    simpa [dual_projected_subgradient_primal_iterate] using hk
  -- Unfold one recursion step and simplify the nonzero branch of the update rule.
  simp [dual_projected_subgradient_method, dual_projected_subgradient_primal_iterate, hk']

-- Proof sketch: unfold `dual_projected_subgradient_method_is_admissible` and read off the
-- positivity component.
/-- Under the admissibility condition, every stepsize in the dual projected subgradient method is
strictly positive. -/
theorem dual_projected_subgradient_method_stepsize_pos
    {f : E → ℝ}
    (h : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (k : ℕ) :
    0 < γ k := by
  -- The first component of admissibility is positivity of every stepsize.
  exact h.1 k

-- Proof sketch: unfold `dual_projected_subgradient_method_is_admissible`; the minimizer clause
-- applied to the current multiplier `λ^k` gives exactly the displayed `IsMinOn` statement.
/-- Under the admissibility condition, the selected primal iterate `x^k` minimizes the
Lagrangian over `X` at the current multiplier `λ^k`. -/
theorem dual_projected_subgradient_primal_iterate_isMinOn
    {f : E → ℝ}
    (h : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (k : ℕ) :
    IsMinOn (fun x ↦ f x + ∑ i, (lam[k] i : ℝ) * g i x) X (x[k] : E) := by
  -- Apply the minimizer clause of admissibility at the current multiplier iterate.
  simpa [dual_projected_subgradient_primal_iterate] using h.2 lam[k]

end

end
