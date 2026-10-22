/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Algorithm 10.2 is `source-facing` in the Chapter 10 proximal-gradient API. The textbook
procedure is expressed through the already canonical chapter owners
`is_proximal_gradient_trajectory`, `composite_model_objective`, `prox_grad_operator`, and
`gradient_mapping`. Since the item specifies a geometric trial family `s η^i` and then chooses
the smallest accepted index, the faithful public API is a concrete trial stepsize together with a
predicate saying that an index is the first accepted backtracking trial, rather than an
existentially chosen output package. The bridge from `x ∈ effective_domain g` to the operator
domain `interior (effective_domain f)` is just the inclusion
`effective_domain g ⊆ interior (effective_domain f)`, so this file should use that inclusion
directly instead of owning a parallel point-constructor. -/

/-- A proximal-gradient backtracking decrease fraction is a positive real parameter strictly less
than `1`. -/
abbrev ProximalGradientBacktrackingDecreaseFraction := { γ : PosReal // (γ : ℝ) < 1 }

/-- A proximal-gradient backtracking growth factor is a positive real parameter strictly greater
than `1`. -/
abbrev ProximalGradientBacktrackingGrowthFactor := { η : PosReal // (1 : ℝ) < (η : ℝ) }

-- Proof sketch: `s` is positive because it is a `PosReal`, and `(η : ℝ)^i` is nonnegative; since
-- `η > 1`, in particular `η` is positive, so the whole product `s * η^i` is positive.
/-- The geometric trial curvature `s η^i` used by backtracking procedure B1 is positive. -/
theorem proximal_gradient_backtracking_trial_stepsize_pos
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor) (i : ℕ) :
    0 < (s : ℝ) * (η : ℝ) ^ i := by
  -- The starting curvature is positive because `s` is a positive real parameter.
  have hs : 0 < (s : ℝ) := s.2
  -- The growth factor is also positive because the algorithm assumes `η > 1`.
  have hη : 0 < (η : ℝ) := lt_trans zero_lt_one η.2
  -- A product of positive factors stays positive along the geometric trial family.
  exact mul_pos hs (pow_pos hη i)

/-- The `i`-th trial curvature parameter in backtracking procedure B1 is the positive real
`s η^i`. -/
def proximal_gradient_backtracking_trial_stepsize
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor) (i : ℕ) : PosReal :=
  ⟨(s : ℝ) * (η : ℝ) ^ i,
    proximal_gradient_backtracking_trial_stepsize_pos s η i⟩

-- Proof sketch: unfold `proximal_gradient_backtracking_trial_stepsize`; its underlying real value
-- is definitionally the product `(s : ℝ) * η^i`.
/-- Coercing the `i`-th B1 trial curvature to `ℝ` gives the formula `s η^i`. -/
@[simp] theorem proximal_gradient_backtracking_trial_stepsize_coe
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor) (i : ℕ) :
    (proximal_gradient_backtracking_trial_stepsize s η i : ℝ) =
      (s : ℝ) * (η : ℝ) ^ i := by
  -- The trial stepsize stores exactly the real number `s * η^i` in its carrier field.
  rfl

/-- The sufficient-decrease test used in backtracking procedure B1 accepts `L` at `x` exactly
when
`F(x) - F(T_L(x)) ≥ (γ / L) ‖G_L(x)‖²`
for the composite objective `F = f + g`, where the current iterate is the source-facing datum
`x ∈ effective_domain g` and the operators `T_L` and `G_L` are evaluated at the induced point of
`interior (effective_domain f)`. -/
def proximal_gradient_backtracking_accepts
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (γ : ProximalGradientBacktrackingDecreaseFraction) (L : PosReal)
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (x : effective_domain g) : Prop :=
  let xInterior : interior (effective_domain f) :=
    ⟨(x : E), hg_effective_domain_subset_interior_f_effective_domain x.property⟩
  ((((γ : ℝ) / (L : ℝ)) *
      ‖G[L, f, g] xInterior‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
    composite_model_objective f g (x : E) -
      composite_model_objective f g (T[L, f, g] xInterior)

-- Proof sketch: unfold `proximal_gradient_backtracking_accepts`; the statement is exactly the
-- textbook sufficient-decrease inequality written with the chapter owners `T_L` and `G_L` at the
-- interior-domain point induced by `x ∈ effective_domain g`.
/-- The B1 acceptance test is exactly the displayed sufficient-decrease inequality for the trial
parameter `L`. -/
theorem proximal_gradient_backtracking_accepts_iff
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (γ : ProximalGradientBacktrackingDecreaseFraction) (L : PosReal)
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (x : effective_domain g) :
    proximal_gradient_backtracking_accepts
      f g γ L hg_effective_domain_subset_interior_f_effective_domain x ↔
      let xInterior :=
        (⟨(x : E), hg_effective_domain_subset_interior_f_effective_domain x.property⟩ :
          interior (effective_domain f))
      ((((γ : ℝ) / (L : ℝ)) *
          ‖G[L, f, g] xInterior‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        composite_model_objective f g (x : E) -
          composite_model_objective f g (T[L, f, g] xInterior) :=
  Iff.rfl

/-- Algorithm 10.2: given parameters `s > 0`, `γ ∈ (0,1)`, and `η > 1`, an index `i_k` is a
valid output of backtracking procedure B1 at the current iterate `x^k` when the trial curvature
`s η^{i_k}` is the first geometric trial satisfying
`F(x^k) - F(T_{s η^{i_k}}(x^k)) ≥ (γ / (s η^{i_k})) ‖G_{s η^{i_k}}(x^k)‖²`. -/
class is_backtracking_procedure_B1_index
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (x : effective_domain g) (i : ℕ) : Prop where
  accepts :
    proximal_gradient_backtracking_accepts
      f g γ (proximal_gradient_backtracking_trial_stepsize s η i)
      hg_effective_domain_subset_interior_f_effective_domain x
  minimal (j : ℕ) (hj : j < i) :
    ¬ proximal_gradient_backtracking_accepts f g γ
        (proximal_gradient_backtracking_trial_stepsize s η j)
        hg_effective_domain_subset_interior_f_effective_domain x

/-- An accepted B1 backtracking index yields the corresponding acceptance fact as a `Fact`
instance. -/
instance is_backtracking_procedure_B1_index_accepts_fact
    {f g : E → EReal} [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    {s : PosReal} {γ : ProximalGradientBacktrackingDecreaseFraction}
    {η : ProximalGradientBacktrackingGrowthFactor}
    {hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f)}
    {x : effective_domain g} {i : ℕ}
    [h : is_backtracking_procedure_B1_index
      f g s γ η
      hg_effective_domain_subset_interior_f_effective_domain x i] :
    Fact
      (proximal_gradient_backtracking_accepts
        f g γ (proximal_gradient_backtracking_trial_stepsize s η i)
        hg_effective_domain_subset_interior_f_effective_domain x) :=
  ⟨h.accepts⟩

/-- A valid B1 backtracking index has an accepted trial curvature `s η^i`. -/
theorem is_backtracking_procedure_B1_index_accepts
    {f g : E → EReal} [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    {s : PosReal} {γ : ProximalGradientBacktrackingDecreaseFraction}
    {η : ProximalGradientBacktrackingGrowthFactor}
    {hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f)}
    {x : effective_domain g} {i : ℕ}
    (hi : is_backtracking_procedure_B1_index
      f g s γ η
      hg_effective_domain_subset_interior_f_effective_domain x i) :
    proximal_gradient_backtracking_accepts
      f g γ (proximal_gradient_backtracking_trial_stepsize s η i)
      hg_effective_domain_subset_interior_f_effective_domain x :=
  hi.accepts

/-- A valid B1 backtracking index is minimal among the accepted geometric trials based on `s`. -/
theorem is_backtracking_procedure_B1_index_minimal
    {f g : E → EReal} [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    {s : PosReal} {γ : ProximalGradientBacktrackingDecreaseFraction}
    {η : ProximalGradientBacktrackingGrowthFactor}
    {hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f)}
    {x : effective_domain g} {i j : ℕ}
    (hi : is_backtracking_procedure_B1_index
      f g s γ η
      hg_effective_domain_subset_interior_f_effective_domain x i)
    (hj : j < i) :
    ¬ proximal_gradient_backtracking_accepts f g γ
        (proximal_gradient_backtracking_trial_stepsize s η j)
        hg_effective_domain_subset_interior_f_effective_domain x :=
  hi.minimal j hj

/-- A prox-gradient trajectory uses backtracking procedure B1 when, at every iteration `k`, the
chosen curvature estimate `L_k` is the accepted B1 trial at the current trajectory iterate, and
that iterate is additionally known to lie in `effective_domain g` so the source-facing B1
acceptance owner applies. -/
def uses_proximal_gradient_backtracking_B1_rule
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor) : Prop :=
  ∀ k : ℕ,
    ∃ hxk : (proximal_gradient_trajectory_iterate htraj k : E) ∈ effective_domain g, ∃ i : ℕ,
    is_backtracking_procedure_B1_index
      f g s γ η
      hg_effective_domain_subset_interior_f_effective_domain
      ⟨(proximal_gradient_trajectory_iterate htraj k : E), hxk⟩ i ∧
    L k = proximal_gradient_backtracking_trial_stepsize s η i

end
