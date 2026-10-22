/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_13.Comparison

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

noncomputable section

section

variable {p : ℕ+}

/- Algorithm 12.13 is `source-facing`: it gives the accelerated primal-representation dual block
proximal-gradient method for the finite-sum problem
`min_x {f x + ∑ i, g_i x}`.

Domain sampling against the nearby project owners identifies:
- `dual_proximal_gradient_primal_x_argmax` from Algorithm 12.2 as the canonical owner for the
  step-(a) primal argmax surface, specialized here to `A = LinearMap.id` and the aggregated block
  variable `∑ i, w_i`;
- `dual_proximal_gradient_primal_y_step` from Algorithm 12.2 as the canonical owner for the
  one-block proximal update, specialized here to `A = LinearMap.id` and the block stepsize
  `p / σ`;
- `fista_momentum_update` from Algorithm 10.13 as the canonical owner for the scalar recursion
  `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`;
- `IsFastDualProximalGradientPrimalTrajectory` from Algorithm 12.4 as the `core/canonical`
  accelerated owner after specializing the nonsmooth term to `PiLp.separableSum g` on the block
  Hilbert product and the linear map to the canonical duplication operator from Proposition 12.8.

The primitive data are therefore the explicit sequences `u`, `y`, `w`, and `t`, together with the
coordinatewise Chapter 12 one-block proximal memberships and the momentum recursion. The
source-facing class below keeps the simultaneous block update visible, while a separate bridge
connects it to the Chapter 12.4 accelerated owner. -/

/-- The effective dual-proximal stepsize in Algorithm 12.13 is the positive scalar `p / σ`. -/
def dual_block_proximal_gradient_stepsize (p : ℕ+) (σ : PosReal) : PosReal :=
  (⟨(p : ℝ), show (0 : ℝ) < (p : ℝ) from Nat.cast_pos.mpr p.2⟩ : PosReal) / σ

/-- Coercing the Algorithm 12.13 block stepsize to `ℝ` recovers the scalar `p / σ`. -/
@[simp, norm_cast] theorem dual_block_proximal_gradient_stepsize_coe
    (σ : PosReal) :
    ((dual_block_proximal_gradient_stepsize p σ : PosReal) : ℝ) = (p : ℝ) / (σ : ℝ) :=
  rfl

end

section

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℕ+}
variable (E)

/-- The block stepsize `p / σ` is an admissible Chapter 12.1 constant parameter for the diagonal
duplication operator. In the nontrivial case this is exactly Proposition 12.8; in the
subsingleton case the duplication map is zero, so the lower bound is automatic. -/
theorem dual_block_proximal_gradient_stepsize_parameter_lower_bound
    (p : ℕ+) (σ : PosReal) :
    dual_based_proximal_gradient_dual_lipschitz_constant
        (dual_block_duplication E p) σ ≤
      ((dual_block_proximal_gradient_stepsize p σ : PosReal) : ℝ) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- Local instance justification (proof-local temporary data): this branch uses the
    -- subsingleton hypothesis `hE` only to identify the duplication operator with `0`.
    letI := hE
    have hstepsize_nonneg : 0 ≤ ((dual_block_proximal_gradient_stepsize p σ : PosReal) : ℝ) := by
      rw [dual_block_proximal_gradient_stepsize_coe]
      exact div_nonneg (by exact_mod_cast Nat.zero_le p) (le_of_lt σ.2)
    have hdup : dual_block_duplication E p = 0 := by
      ext z i
      exact Subsingleton.elim _ _
    simpa [dual_based_proximal_gradient_dual_lipschitz_constant_eq, hdup] using hstepsize_nonneg
  · -- Local instance justification (proof-local temporary data): this branch specializes
    -- `dual_block_duplication_fdpg_lipschitz_constant_eq` under the branch hypothesis
    -- `hE : Nontrivial E`.
    letI := hE
    rw [dual_block_duplication_fdpg_lipschitz_constant_eq]
    have hcoe : ((dual_block_proximal_gradient_stepsize p σ : PosReal) : ℝ) = (p : ℝ) / (σ : ℝ) :=
      dual_block_proximal_gradient_stepsize_coe σ
    exact le_of_eq hcoe.symm

/-- The canonical Chapter 12.1 constant parameter for Algorithm 12.13 is the block stepsize
`p / σ` specialized to the diagonal duplication operator. -/
abbrev dual_block_proximal_gradient_stepsize_parameter
    (p : ℕ+) (σ : PosReal) :
    DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) σ :=
  ⟨dual_block_proximal_gradient_stepsize p σ,
    dual_block_proximal_gradient_stepsize_parameter_lower_bound E p σ⟩

end

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The source-facing trajectory data for Algorithm 12.13: for a strictly positive block count
`p : ℕ+`, the sequences
`(u^k, y^k, w^k, t_k)` follow the fast dual block
proximal-gradient method when `y⁰ = w⁰ = y0`, `t₀ = 1`, each `u^k` realizes the step-(a) argmax,
each block `y_i^(k+1)` satisfies the canonical Chapter 12 one-block step-(b) proximal condition,
the scalar sequence satisfies `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`, and the extrapolated blocks
satisfy the textbook momentum recursion, recorded in the equivalent public form `w¹ = y¹` and
`w^(k+2) = y^(k+2) + ((t_(k+1) - 1) / t_(k+2)) (y^(k+2) - y^(k+1))`. -/
class IsFastDualBlockProximalGradientPrimalTrajectory
    {p : ℕ+}
    (f : E → EReal) (g : Fin p → E → EReal) (σ : PosReal)
    (y0 : Fin p → E) (u : ℕ → E) (y w : ℕ → Fin p → E) (t : ℕ → ℝ) : Prop where
  /-- The initial block dual iterate is the prescribed point `y0`. -/
  y_zero : y 0 = y0
  /-- The extrapolated block sequence starts from the same prescribed point `y0`. -/
  w_zero : w 0 = y0
  /-- The acceleration parameter is initialized by `t₀ = 1`. -/
  t_zero : t 0 = 1
  /-- At each step, `u^k` realizes the step-(a) primal argmax at the current extrapolated block
  vector `w^k`. -/
  primal_step (k : ℕ) :
    u k ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id (∑ i : Fin p, w k i)
  /-- At each step and for each block `i`, the next coordinate `y_i^(k+1)` satisfies the Chapter
  12 one-block proximal update specialized to `A = LinearMap.id`, based at `(u^k, w_i^k)` and
  stepsize `p / σ`. -/
  dual_step (k : ℕ) (i : Fin p) :
    y (k + 1) i ∈
      dual_proximal_gradient_primal_y_step
        (g i)
        LinearMap.id
        (u k)
        (w k i)
        (dual_block_proximal_gradient_stepsize p σ)
  /-- The acceleration scalars satisfy the Chapter 10 FISTA momentum recursion. -/
  acceleration_step (k : ℕ) :
    t (k + 1) = fista_momentum_update (t k)
  /-- The first extrapolated block iterate is recorded explicitly as `w¹ = y¹`. -/
  first_momentum_step : w 1 = y 1
  /-- For every `k`, the later extrapolated block iterates satisfy the shifted textbook momentum
  recursion. -/
  momentum_step (k : ℕ) :
    w (k + 2) =
      y (k + 2) + ((t (k + 1) - 1) / t (k + 2)) • (y (k + 2) - y (k + 1))

variable {p : ℕ+}
variable {f : E → EReal} {g : Fin p → E → EReal} {σ : PosReal}
variable {y0 : Fin p → E} {u : ℕ → E} {y w : ℕ → Fin p → E} {t : ℕ → ℝ}

-- The companion statements below inherit the same strictly positive block count `p : ℕ+`.

/-- The acceleration field of a fast dual block proximal-gradient primal trajectory expands to the
textbook scalar formula
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`. -/
theorem IsFastDualBlockProximalGradientPrimalTrajectory.acceleration_step_formula
    (h : IsFastDualBlockProximalGradientPrimalTrajectory f g σ y0 u y w t)
    (k : ℕ) :
    t (k + 1) = (1 + Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ))) / 2 := by
  simpa [fista_momentum_update_eq] using h.acceleration_step k

end

section

variable {E : Type u}
variable [NormedAddCommGroup E]

/-- Helper for Algorithm 12.13: coordinatewise proximal memberships assemble into proximal
membership for the separable block sum on the `PiLp` product space. -/
theorem mem_prox_separableSum_of_coordinatewise
    {n : ℕ}
    {φ : Fin n → E → EReal}
    {x : PiLp (2 : ENNReal) (fun _ : Fin n ↦ E)}
    {y : Fin n → E}
    (hy : ∀ i, y i ∈ prox[φ i] (x i)) :
    WithLp.toLp 2 y ∈ prox[PiLp.separableSum φ] x := by
  -- Rewrite proximal membership as global minimization of the separable proximal objective.
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
  intro z
  have hyCoord :
      ∀ i, IsMinOn (proximal_objective (φ i) (x i)) Set.univ (y i) := by
    intro i
    exact (mem_proximal_mapping_iff.mp (hy i))
  have hyCoordLe :
      ∀ i u, proximal_objective (φ i) (x i) (y i) ≤ proximal_objective (φ i) (x i) u := by
    intro i u
    exact (isMinOn_univ_iff.mp (hyCoord i)) u
  -- Separate the product-space objective into the finite sum of coordinate objectives.
  rw [separable_proximal_objective_eq_sum_coordinate_objectives φ x (WithLp.toLp 2 y)]
  rw [separable_proximal_objective_eq_sum_coordinate_objectives φ x z]
  exact Finset.sum_le_sum (fun i _ ↦ by simpa using hyCoordLe i (z i))

end

section

variable {E : Type u}

/-- Helper for Algorithm 12.13: scaling the separable block sum by a positive scalar is the same
as scaling each block function. -/
theorem smul_separableSum_eq_separableSum_smul
    {n : ℕ}
    (g : Fin n → E → EReal)
    (L : PosReal) :
    (((L : PosReal) : EReal) • PiLp.separableSum g) =
      PiLp.separableSum (fun i ↦ (((L : PosReal) : EReal) • g i)) := by
  funext z
  -- Evaluate both sides pointwise and push the positive scalar through the finite sum.
  rw [Pi.smul_apply, PiLp.separableSum_apply, PiLp.separableSum_apply]
  simp_rw [Pi.smul_apply, smul_eq_mul]
  have hL_nonneg : (0 : EReal) ≤ ((L : PosReal) : EReal) := by
    exact_mod_cast (show (0 : ℝ) ≤ (L : ℝ) by exact le_of_lt L.2)
  have hL_ne_top : (((L : PosReal) : EReal)) ≠ ⊤ := by
    simp
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha hs =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [EReal.left_distrib_of_nonneg_of_ne_top hL_nonneg hL_ne_top, hs]

end

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ+}
variable {f : E → EReal} {g : Fin p → E → EReal} {σ : PosReal}
variable {y0 : Fin p → E} {u : ℕ → E} {y w : ℕ → Fin p → E} {t : ℕ → ℝ}

/-- Helper for Algorithm 12.13: coordinatewise block step-(b) updates assemble into the global
Chapter 12.4 primal `y`-step for the duplication operator. -/
theorem mem_dual_primal_y_step_of_coordinatewise_block_steps
    {x : E} {v yNext : Fin p → E}
    (hyNext : ∀ i,
      yNext i ∈
        dual_proximal_gradient_primal_y_step
          (g i)
          LinearMap.id
          x
          (v i)
          (dual_block_proximal_gradient_stepsize p σ)) :
    WithLp.toLp 2 yNext ∈
      dual_proximal_gradient_primal_y_step
        (PiLp.separableSum g)
        (dual_block_duplication E p).toLinearMap
        x
        (WithLp.toLp 2 v)
        (dual_block_proximal_gradient_stepsize p σ) := by
  classical
  let L := dual_block_proximal_gradient_stepsize p σ
  -- Extract the coordinate proximal witnesses from the block step memberships.
  choose q hq_mem hq_eq using
    (fun i ↦ (mem_dual_proximal_gradient_primal_y_step_iff.mp (hyNext i)))
  rw [mem_dual_proximal_gradient_primal_y_step_iff]
  refine ⟨WithLp.toLp 2 q, ?_, ?_⟩
  · -- Assemble the coordinate proximal witnesses into a global separable proximal witness.
    have hq_mem_global :
        WithLp.toLp 2 q ∈
          prox[PiLp.separableSum (fun i ↦ (((L : PosReal) : EReal) • g i))]
            (WithLp.toLp 2 (fun i ↦ x - (L : ℝ) • v i)) :=
      mem_prox_separableSum_of_coordinatewise
        (fun i ↦ by simpa [L, LinearMap.id_apply] using hq_mem i)
    have hdup :
        (dual_block_duplication E p).toLinearMap x = WithLp.toLp 2 (fun _ : Fin p ↦ x) := by
      ext i
      simp
    -- Rewrite the packaged witness into the Chapter 12.4 global step normal form.
    rw [hdup, smul_separableSum_eq_separableSum_smul]
    simpa [L, WithLp.toLp_sub, WithLp.toLp_smul] using hq_mem_global
  · -- Transport the coordinate affine update equalities through `WithLp.toLp 2`.
    ext i
    simpa [L, dual_block_duplication_apply] using hq_eq i

end

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {p : ℕ+}
variable {f : E → EReal} {g : Fin p → E → EReal} {σ : PosReal}
variable {y0 : Fin p → E} {u : ℕ → E} {y w : ℕ → Fin p → E} {t : ℕ → ℝ}

/-- Algorithm 12.13: any such trajectory canonically yields the Chapter 12.4 accelerated dual
proximal-gradient primal trajectory for the finite-sum block Hilbert-product model, with
nonsmooth term `PiLp.separableSum g`, duplication operator `dual_block_duplication E p`, and
constant parameter `p / σ`. -/
theorem IsFastDualBlockProximalGradientPrimalTrajectory.toFastDualProximalGradientPrimalTrajectory
    (h : IsFastDualBlockProximalGradientPrimalTrajectory f g σ y0 u y w t) :
    IsFastDualProximalGradientPrimalTrajectory
      f (PiLp.separableSum g) (dual_block_duplication E p).toLinearMap σ
      (dual_block_proximal_gradient_stepsize_parameter E p σ)
      (WithLp.toLp 2 y0)
      u
      (fun k ↦ WithLp.toLp 2 (y k))
      (fun k ↦ WithLp.toLp 2 (w k))
      t := by
  refine
    { y_zero := ?_
      w_zero := ?_
      t_zero := h.t_zero
      primal_step := ?_
      dual_step := ?_
      acceleration_step := h.acceleration_step
      momentum_step := ?_ }
  · -- Transport the initial block iterate to the duplicated `PiLp` model.
    simpa using congrArg (WithLp.toLp 2) h.y_zero
  · -- Transport the initial extrapolated block iterate in the same way.
    simpa using congrArg (WithLp.toLp 2) h.w_zero
  · intro k
    -- Reuse the existing argmax bridge instead of unfolding the duplication operator locally.
    exact (mem_dual_primal_x_argmax_duplication_iff).2 (h.primal_step k)
  · intro k
    -- Assemble the coordinatewise block updates into the global duplicated-model proximal step.
    simpa using
      mem_dual_primal_y_step_of_coordinatewise_block_steps
        (g := g) (σ := σ) (x := u k) (v := w k) (yNext := y (k + 1))
        (fun i ↦ h.dual_step k i)
  · -- Recover Algorithm 12.4's source momentum clause from the corrected shifted formulation.
    have hshifted :
        WithLp.toLp 2 (w 1) = WithLp.toLp 2 (y 1) ∧
          ∀ k : ℕ,
            WithLp.toLp 2 (w (k + 2)) =
              WithLp.toLp 2 (y (k + 2)) +
                ((t (k + 1) - 1) / t (k + 2)) •
                  (WithLp.toLp 2 (y (k + 2)) - WithLp.toLp 2 (y (k + 1))) := by
      refine ⟨?_, ?_⟩
      · -- The explicit `w¹ = y¹` field transports directly through `WithLp.toLp 2`.
        simpa using congrArg (WithLp.toLp 2) h.first_momentum_step
      · intro k
        -- The shifted successor identity becomes the canonical product-space momentum update
        -- after rewriting `WithLp.toLp` across addition, subtraction, and scalar multiplication.
        simpa [WithLp.toLp_add, WithLp.toLp_sub, WithLp.toLp_smul] using
          congrArg (WithLp.toLp 2) (h.momentum_step k)
    exact
      ((IsFastDualProximalGradientPrimalTrajectory.sourceMomentum_iff_shifted
          (y := fun k ↦ WithLp.toLp 2 (y k))
          (w := fun k ↦ WithLp.toLp 2 (w k))
          (t := t)
          h.t_zero).2
        hshifted)

namespace IsFastDualBlockProximalGradientPrimalTrajectory

/-- An Algorithm 12.13 trajectory induces the canonical Algorithm 12.4 accelerated trajectory on
the duplicated block-product model. -/
instance instIsFastDualProximalGradientPrimalTrajectory
    (h : IsFastDualBlockProximalGradientPrimalTrajectory f g σ y0 u y w t) :
    IsFastDualProximalGradientPrimalTrajectory
      f (PiLp.separableSum g) (dual_block_duplication E p).toLinearMap σ
      (dual_block_proximal_gradient_stepsize_parameter E p σ)
      (WithLp.toLp 2 y0)
      u
      (fun k ↦ WithLp.toLp 2 (y k))
      (fun k ↦ WithLp.toLp 2 (w k))
      t :=
  h.toFastDualProximalGradientPrimalTrajectory

end IsFastDualBlockProximalGradientPrimalTrajectory

end
