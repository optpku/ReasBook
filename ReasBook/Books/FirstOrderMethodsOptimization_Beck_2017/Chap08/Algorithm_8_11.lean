/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators
open Metric
open Bornology
open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 8.11 is `source-facing`: it specializes the projected subgradient iteration to a
finite-sum objective by summing one chosen component subgradient from each summand and normalizing
the step by the norm of that aggregate. The projection owner remains `metricProjection`, but the
stepsize depends on the current iterate, so the public algorithm is most naturally given by a
direct recursive definition rather than by repackaging `projected_subgradient_method` from
Algorithm 8.3. -/

/-- The aggregate subgradient selected at iteration `k` is the sum of the chosen component
subgradients for the finite-sum objective. -/
def finite_sum_selected_subgradient {m : ℕ} {C : Set E}
    (g : ℕ → C → Fin m → E) (k : ℕ) (x : C) : E :=
  ∑ i : Fin m, g k x i

/-- The normalized stepsize used in the finite-sum projected subgradient method is
`√(2 Θ) / (‖∑ᵢ gᵢ‖ √(k + 1))`. -/
def finite_sum_projected_subgradient_stepsize {m : ℕ} {C : Set E}
    (Θ : ℝ) (g : ℕ → C → Fin m → E) (k : ℕ) (x : C) : ℝ :=
  Real.sqrt (2 * Θ) /
    (‖finite_sum_selected_subgradient g k x‖ * Real.sqrt (k + 1 : ℝ))

/-- Algorithm 8.11: for a nonempty closed convex feasible set `C`, a feasible initial point
`x0`, a constant `Θ`, and a rule selecting one component subgradient for each summand at each
current iterate, the finite-sum projected subgradient method generates the sequence
`x^{k+1} = P_C (x^k - (√(2 Θ) / (‖∑ᵢ fᵢ'(x^k)‖ √(k + 1))) ∑ᵢ fᵢ'(x^k))`. -/
def finite_sum_projected_subgradient_method {m : ℕ} (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (Θ : ℝ) (g : ℕ → C → Fin m → E) (x0 : C) : ℕ → C
  | 0 => x0
  | k + 1 =>
      -- Route correction: the canonical projection API is owned by Proposition 3.12, so the
      -- closed feasible set supplies the required completeness input through `hC_closed`.
      let xk :=
        finite_sum_projected_subgradient_method C hC_nonempty hC_closed hC_convex Θ g x0 k
      metricProjection C hC_nonempty hC_closed hC_convex
        ((xk : E) -
          finite_sum_projected_subgradient_stepsize Θ g k xk •
            finite_sum_selected_subgradient g k xk)

/-- A component-subgradient selection rule is admissible for the finite-sum projected subgradient
method when, at each iterate, every chosen component lies in the Euclidean subdifferential of the
corresponding summand and the aggregate chosen subgradient is nonzero. -/
def finite_sum_projected_subgradient_method_is_admissible {m : ℕ}
    (f : Fin m → E → ℝ) (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (Θ : ℝ) (g : ℕ → C → Fin m → E) (x0 : C) : Prop :=
  ∀ k,
    (∀ i : Fin m,
      g k (finite_sum_projected_subgradient_method C hC_nonempty hC_closed hC_convex Θ g x0 k) i ∈
        euclideanSubdifferentialAt (f i)
          (finite_sum_projected_subgradient_method C hC_nonempty hC_closed hC_convex Θ g x0 k :
            E)) ∧
    finite_sum_selected_subgradient g k
        (finite_sum_projected_subgradient_method C hC_nonempty hC_closed hC_convex Θ g x0 k) ≠ 0

section

variable {m : ℕ}
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (Θ : ℝ) (g : ℕ → C → Fin m → E) (x0 : C)

local notation "x[" k "]" =>
  finite_sum_projected_subgradient_method C hC_nonempty hC_closed hC_convex Θ g x0 k

-- Proof sketch: unfold the recursive definition of
-- `finite_sum_projected_subgradient_method` at `0`.
/-- The finite-sum projected-subgradient sequence starts at the prescribed feasible initial
point. -/
@[simp] theorem finite_sum_projected_subgradient_method_zero :
    x[0] = x0 := by
  -- The base case is exactly the `0` branch of the recursive definition.
  rfl

-- Proof sketch: unfold the recursive definition of
-- `finite_sum_projected_subgradient_method` at `k + 1`, then expand
-- `finite_sum_projected_subgradient_stepsize` and `finite_sum_selected_subgradient`.
/-- One step of the finite-sum projected subgradient method applies the metric projection onto `C`
to the current iterate minus the normalized sum of the chosen component subgradients. -/
theorem finite_sum_projected_subgradient_method_succ (k : ℕ) :
    x[k + 1] =
      metricProjection C hC_nonempty hC_closed hC_convex
        ((x[k] : E) -
          (Real.sqrt (2 * Θ) /
              (‖∑ i : Fin m, g k (x[k]) i‖ * Real.sqrt (k + 1 : ℝ))) •
            ∑ i : Fin m, g k (x[k]) i) := by
  -- Unfolding one recursive step exposes the projected update rule in textbook form.
  rfl

-- Proof sketch: unfold `finite_sum_projected_subgradient_method_is_admissible` and specialize the
-- componentwise subgradient clause at the index `k`.
/-- Under the admissibility condition, each chosen component direction at iteration `k` is a
Euclidean subgradient of the corresponding summand at the current iterate. -/
theorem finite_sum_projected_subgradient_method_component_mem
    {f : Fin m → E → ℝ}
    (h :
      finite_sum_projected_subgradient_method_is_admissible
        f C hC_nonempty hC_closed hC_convex Θ g x0)
    (k : ℕ) (i : Fin m) :
    g k (x[k]) i ∈ euclideanSubdifferentialAt (f i) (x[k] : E) := by
  -- The admissibility predicate stores componentwise subgradient membership in its first clause.
  exact (h k).1 i

-- Proof sketch: unfold `finite_sum_projected_subgradient_method_is_admissible` and read off the
-- nonvanishing clause at the index `k`.
/-- Under the admissibility condition, the aggregate chosen subgradient at iteration `k` is
nonzero, so the normalization factor in Algorithm 8.11 is well defined. -/
theorem finite_sum_projected_subgradient_method_aggregate_ne_zero
    {f : Fin m → E → ℝ}
    (h :
      finite_sum_projected_subgradient_method_is_admissible
        f C hC_nonempty hC_closed hC_convex Θ g x0)
    (k : ℕ) :
    ∑ i : Fin m, g k (x[k]) i ≠ 0 := by
  -- The admissibility predicate stores the nonvanishing aggregate subgradient as its second clause.
  exact (h k).2

end

end
