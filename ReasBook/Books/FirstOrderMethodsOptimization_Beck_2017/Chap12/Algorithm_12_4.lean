/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/- Algorithm 12.4 is `source-facing` in the chapter's accelerated dual proximal-gradient API.

Domain sampling against the nearby project owners points to:
- `dual_proximal_gradient_primal_x_argmax` from Algorithm 12.2 as the canonical owner for the
  primal argmax step `u^k`;
- `dual_proximal_gradient_primal_y_step` from Algorithm 12.2 as the canonical owner for the
  primal-representation proximal update `y^(k+1)`;
- `fista_momentum_update` from Algorithm 10.13 as the canonical owner for the scalar recursion
  `t_(k+1) = (1 + sqrt (1 + 4 t_k^2)) / 2`;
- `DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ` from
  Algorithm 12.1 as the canonical owner of the admissible constant parameter `L`.

The new content of Algorithm 12.4 is the accelerated auxiliary sequences `w^k` and `t_k`,
including the source momentum clause
`w^(k+1) = y^(k+1) + ((t_k - 1) / t_(k+1)) (y^(k+1) - y^k)`. -/

/-- Algorithm 12.4: a quadruple of sequences `(u^k, y^k, w^k, t_k)` follows the fast dual
proximal-gradient method in primal representation when `L` is an admissible constant stepsize
parameter, equivalently `(L : ℝ) ≥ ‖A‖² / σ`, the initial conditions are `w^0 = y^0 = y0` and
`t_0 = 1`, each `u^k` maximizes
`u ↦ ⟪u, Aᵀ w^k⟫ - f(u)`, each `y^(k+1)` is obtained from the primal proximal step at `w^k`,
the scalar sequence satisfies `t_(k+1) = (1 + sqrt (1 + 4 t_k^2)) / 2`, and the momentum update
is `w^(k+1) = y^(k+1) + ((t_k - 1) / t_(k+1)) (y^(k+1) - y^k)`. -/
class IsFastDualProximalGradientPrimalTrajectory
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (σ : PosReal)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (y0 : V) (u : ℕ → E) (y w : ℕ → V) (t : ℕ → ℝ) : Prop where
  /-- The initial dual iterate is the prescribed point `y0`. -/
  y_zero : y 0 = y0
  /-- The extrapolated sequence starts from the same prescribed point `y0`. -/
  w_zero : w 0 = y0
  /-- The acceleration parameter is initialized by `t_0 = 1`. -/
  t_zero : t 0 = 1
  /-- At each step, `u^k` is a maximizer of `u ↦ ⟪u, Aᵀ w^k⟫ - f(u)`. -/
  primal_step (k : ℕ) :
    u k ∈ dual_proximal_gradient_primal_x_argmax f A (w k)
  /-- At each step, `y^(k+1)` lies in the Chapter 12 primal proximal update set based at `w^k`. -/
  dual_step (k : ℕ) :
    y (k + 1) ∈ dual_proximal_gradient_primal_y_step g A (u k) (w k) L
  /-- The acceleration scalars satisfy the Chapter 10 FISTA momentum recursion. -/
  acceleration_step (k : ℕ) :
    t (k + 1) = fista_momentum_update (t k)
  /-- For every `k`, the extrapolated iterate satisfies the source momentum recursion. -/
  momentum_step (k : ℕ) :
    w (k + 1) =
      y (k + 1) + ((t k - 1) / t (k + 1)) • (y (k + 1) - y k)

/-- Coercion from an Algorithm 12.4 primal trajectory to its bundled per-iteration update
rule. -/
instance IsFastDualProximalGradientPrimalTrajectory.instCoeFun
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (σ : PosReal)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (y0 : V) (u : ℕ → E) (y w : ℕ → V) (t : ℕ → ℝ) :
    CoeFun
      (IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t)
      (fun _ ↦
        ∀ k : ℕ,
          u k ∈ dual_proximal_gradient_primal_x_argmax f A (w k) ∧
            y (k + 1) ∈ dual_proximal_gradient_primal_y_step g A (u k) (w k) L ∧
              t (k + 1) = fista_momentum_update (t k) ∧
                w (k + 1) =
                  y (k + 1) + ((t k - 1) / t (k + 1)) • (y (k + 1) - y k))
    where
  coe h k := ⟨h.primal_step k, h.dual_step k, h.acceleration_step k, h.momentum_step k⟩

variable {f : E → EReal} {g : V → EReal} {A : E →ₗ[ℝ] V} {σ : PosReal}
variable {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
variable {y0 : V} {u : ℕ → E} {y w : ℕ → V} {t : ℕ → ℝ}

namespace IsFastDualProximalGradientPrimalTrajectory

/-- The primitive per-iteration data of an Algorithm 12.4 trajectory. -/
theorem step
    (h :
      IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t)
    (k : ℕ) :
    u k ∈ dual_proximal_gradient_primal_x_argmax f A (w k) ∧
      y (k + 1) ∈ dual_proximal_gradient_primal_y_step g A (u k) (w k) L ∧
      t (k + 1) = fista_momentum_update (t k) ∧
      w (k + 1) =
        y (k + 1) + ((t k - 1) / t (k + 1)) • (y (k + 1) - y k) := by
  exact ⟨h.primal_step k, h.dual_step k, h.acceleration_step k, h.momentum_step k⟩

section

variable {V : Type v} [AddCommGroup V] [Module ℝ V]
variable {y w : ℕ → V} {t : ℕ → ℝ}

/-- Under the initialization `t₀ = 1`, the source momentum recursion is equivalent to the split
form given by the first extrapolation identity `w¹ = y¹` and the reindexed successor clause. -/
theorem sourceMomentum_iff_shifted
    (ht_zero : t 0 = 1) :
    (∀ k : ℕ,
        w (k + 1) =
          y (k + 1) + ((t k - 1) / t (k + 1)) • (y (k + 1) - y k)) ↔
      w 1 = y 1 ∧
        ∀ k : ℕ,
          w (k + 2) =
            y (k + 2) + ((t (k + 1) - 1) / t (k + 2)) •
              (y (k + 2) - y (k + 1)) := by
  constructor
  · intro hsource
    refine ⟨?_, ?_⟩
    · simpa [ht_zero] using hsource 0
    · intro k
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsource (k + 1)
  · rintro ⟨hfirst, hsucc⟩ k
    cases k with
    | zero =>
        simpa [ht_zero]
          using hfirst
    | succ k =>
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsucc k

end

/-- Any Algorithm 12.4 trajectory satisfies the first extrapolation identity `w¹ = y¹`. -/
theorem first_momentum_step
    (htraj :
      IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t) :
    w 1 = y 1 := by
  exact ((sourceMomentum_iff_shifted htraj.t_zero).1
    htraj.momentum_step).1

/-- Any Algorithm 12.4 trajectory satisfies the correctly reindexed successor form of the source
momentum clause. -/
theorem momentumStepSucc
    (htraj :
      IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t)
    (k : ℕ) :
    w (k + 2) =
      y (k + 2) + ((t (k + 1) - 1) / t (k + 2)) •
        (y (k + 2) - y (k + 1)) := by
  exact ((sourceMomentum_iff_shifted htraj.t_zero).1
    htraj.momentum_step).2 k

/-- The acceleration field of a fast dual proximal-gradient primal trajectory expands to the
textbook scalar formula
`t_(k+1) = (1 + sqrt (1 + 4 t_k^2)) / 2`. -/
theorem acceleration_step_formula
    (h : IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t) (k : ℕ) :
    t (k + 1) = (1 + Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ))) / 2 := by
  simpa [fista_momentum_update_eq] using h.acceleration_step k

/-- The scalar sequence of a fast dual proximal-gradient primal trajectory agrees with the
canonical Chapter 10 FISTA momentum sequence. -/
theorem momentum_eqFistaSequence
    (h : IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t) :
    ∀ n : ℕ, t n = fista_momentum_sequence n := by
  intro n
  induction n with
  | zero =>
      simpa using h.t_zero
  | succ n ih =>
      simpa [ih, fista_momentum_sequence_succ] using h.acceleration_step n

end IsFastDualProximalGradientPrimalTrajectory

end
