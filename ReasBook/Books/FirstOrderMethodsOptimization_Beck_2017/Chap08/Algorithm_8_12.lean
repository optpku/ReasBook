/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped BigOperators

noncomputable section

section

variable {E : Type u}

/-- A feasible point `x0 : C` canonically witnesses that the feasible set `C` is nonempty. -/
theorem set_nonempty_of_mem {C : Set E} (x0 : C) : C.Nonempty :=
  ⟨x0, x0.property⟩

end

section

variable {E : Type u} {Ω : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Source-facing note: the textbook specializes the stochastic projected subgradient method to a
finite-sum objective by sampling one component index `i_k` and then using one subgradient of the
sampled summand in the projected update. The canonical owner remains the stochastic iterate
sequence `stochastic_projected_subgradient_method` from Algorithm 8.10, while the new data are
the finite-sum bound constant `L̃_f`, the corresponding textbook stepsize, and the sampled
component-subgradient rule. The public API therefore keeps the sampled index process explicit and
realizes the algorithm as a thin specialization of that existing owner. -/

/-- The finite-sum stochastic subgradient bound constant
`L̃_f = √m * √(∑ i, L_i^2)` from Algorithm 8.12. -/
def finite_sum_stochastic_subgradient_bound_constant {m : ℕ} (L : Fin m → ℝ) : ℝ :=
  Real.sqrt (m : ℝ) * Real.sqrt (∑ i : Fin m, L i ^ (2 : ℕ))

/-- The textbook stepsize `√(2 Θ m) / (L̃_f √(k + 1))` used in Algorithm 8.12. -/
def finite_sum_stochastic_projected_subgradient_stepsize {m : ℕ}
    (Θ : ℝ) (L : Fin m → ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (2 * Θ * (m : ℝ)) /
    (finite_sum_stochastic_subgradient_bound_constant L * Real.sqrt (k + 1 : ℝ))

/-- The named Algorithm 8.12 stepsize is exactly the textbook formula
`√(2 Θ m) / (L̃_f √(k + 1))`. -/
@[simp] theorem finite_sum_stochastic_projected_subgradient_stepsize_eq {m : ℕ}
    (Θ : ℝ) (L : Fin m → ℝ) (k : ℕ) :
    finite_sum_stochastic_projected_subgradient_stepsize Θ L k =
      Real.sqrt (2 * Θ * (m : ℝ)) /
        (finite_sum_stochastic_subgradient_bound_constant L * Real.sqrt (k + 1 : ℝ)) := by
  rfl

/-- Algorithm 8.12: for a closed convex feasible set `C`, a feasible initial point `x0`,
componentwise subgradient choices `g k x j`, and a sampled index rule `i_k`, the stochastic
projected subgradient method for a finite-sum objective is the Algorithm 8.10 iteration
specialized to the sampled direction `g k x (i_k ω)` and the stepsize
`√(2 Θ m) / (L̃_f √(k + 1))`, where `L̃_f = √m * √(∑ i, L_i^2)`. -/
abbrev finite_sum_stochastic_projected_subgradient_method {m : ℕ} (C : Set E)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (Θ : ℝ) (L : Fin m → ℝ) (i : ℕ → Ω → Fin m) (g : ℕ → C → Fin m → E) (x0 : C) :
    ℕ → Ω → C :=
  stochastic_projected_subgradient_method C (set_nonempty_of_mem x0) hC_closed hC_convex
    (fun k x ω ↦ g k x (i k ω))
    (finite_sum_stochastic_projected_subgradient_stepsize Θ L)
    x0

section

variable {m : ℕ}
variable (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (Θ : ℝ) (L : Fin m → ℝ) (i : ℕ → Ω → Fin m) (g : ℕ → C → Fin m → E) (x0 : C)

local notation "x[" k "]" =>
  finite_sum_stochastic_projected_subgradient_method
    C hC_closed hC_convex Θ L i g x0 k

-- Proof sketch: specialize `stochastic_projected_subgradient_method_zero` from Algorithm 8.10 to
-- the sampled component direction `fun k x ω ↦ g k x (i k ω)` and the textbook stepsize rule.
/-- The finite-sum stochastic projected-subgradient sequence starts from the prescribed feasible
initial point at every sample `ω`. -/
@[simp] theorem finite_sum_stochastic_projected_subgradient_method_zero (ω : Ω) :
    x[0] ω = x0 := by
  simpa [finite_sum_stochastic_projected_subgradient_method] using
    (stochastic_projected_subgradient_method_zero
      C (set_nonempty_of_mem x0) hC_closed hC_convex
      (fun k x ω ↦ g k x (i k ω))
      (finite_sum_stochastic_projected_subgradient_stepsize Θ L)
      x0 ω)

-- Proof sketch: specialize `stochastic_projected_subgradient_method_succ` from Algorithm 8.10 to
-- the sampled component direction and rewrite the named stepsize with
-- `finite_sum_stochastic_projected_subgradient_stepsize_eq`.
/-- One step of Algorithm 8.12 applies the metric projection onto `C` to the current sample
iterate minus the sampled component subgradient scaled by
`√(2 Θ m) / (L̃_f √(k + 1))`. -/
theorem finite_sum_stochastic_projected_subgradient_method_succ (k : ℕ) (ω : Ω) :
    x[k + 1] ω =
      metricProjection C (set_nonempty_of_mem x0) hC_closed hC_convex
        (x[k] ω -
          (Real.sqrt (2 * Θ * (m : ℝ)) /
              (finite_sum_stochastic_subgradient_bound_constant L * Real.sqrt (k + 1 : ℝ))) •
            g k (x[k] ω) (i k ω)) := by
  simpa [finite_sum_stochastic_projected_subgradient_method] using
    (stochastic_projected_subgradient_method_succ
      C (set_nonempty_of_mem x0) hC_closed hC_convex
      (fun j x ω ↦ g j x (i j ω))
      (finite_sum_stochastic_projected_subgradient_stepsize Θ L)
      x0 k ω)

end

end
