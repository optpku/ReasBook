/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Remark_2_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MaxTypeStep

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- Primary domain: constant-step minimax gradient trajectories on a closed convex feasible set in a
real inner-product space.

Owner declarations sampled for this refinement:
* `maxTypeGradientMapping` and the notation `x_f[Q | fi; L]` in `Remark_2_41_1`, the canonical
  owner exact step for the regularized affine max-type model;
* `maxTypeReducedGradient_eq_smul_sub_ofFact` in `Remark_2_41_1`, which identifies the reduced
  gradient with the residual from `x` to the exact step;
* `simpleSetGradientMethod` in `Algorithm_2_6`, the chapter pattern where the public algorithm is
  the recursive trajectory itself, with recurrence laws exposed as derived theorems;
* `optimalMinimaxMethod` in `Algorithm_2_10`, the analogous recursive owner pattern in the minimax
  domain.

Best owner abstraction:
* source-facing: the recursive trajectory `constantStepMinimaxGradientMethod`;
* core/canonical: the exact step `x_f[Q | fi; L]`, the reduced gradient `g_f[Q | fi; L]`, and the
  convexity bridge `Convex.add_smul_sub_mem`;
* bridge/view: the one-step recurrence theorems
  `constantStepMinimaxGradientMethod_zero` and `constantStepMinimaxGradientMethod_succ`.

Primitive data are the feasible set `Q`, the component family `fi`, the positive regularization
parameter `L`, the feasible initial point `x₀`, the positive step size `h`, and the feasibility
bound `h ≤ 1 / L`. The update stays in `Q` because
`x - h • g_f(x; L) = x + hL • (x_f(x; L) - x)` is a convex combination of `x` and the feasible
exact step `x_f(x; L)` whenever `0 ≤ hL ≤ 1`. The old recurrence predicate therefore belongs only
to the bridge layer, so the public API keeps only the recursive trajectory and its recurrence
theorems. -/

section

variable
    (Q : Set E)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ)

private abbrev nonemptyOfPoint (x0 : Q) : Q.Nonempty := ⟨(x0 : E), x0.property⟩

private theorem stepScale_mem_Icc {L h : NNRealˣ} (hh : (h : ℝ) ≤ 1 / (L : ℝ)) :
    (h : ℝ) * (L : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hL_pos : 0 < (L : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero L))
  refine ⟨by positivity, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hh hL_pos.le
  simpa [div_eq_inv_mul, mul_assoc, inv_mul_cancel₀ hL_pos.ne'] using hmul

/-- Algorithm 2.8: the constant-step minimax gradient method started from the feasible point `x₀`
and recursively updated by the feasible step
`xₖ₊₁ = xₖ - h • g_f(xₖ; L) = xₖ + hL • (x_f(xₖ; L) - xₖ)`, under the admissible bound
`h ≤ 1 / L`. The sequence lives directly in the feasible-set subtype `Q`. -/
noncomputable def constantStepMinimaxGradientMethod
    (L : NNRealˣ)
    (x0 : Q)
    (h : NNRealˣ)
    (hh : (h : ℝ) ≤ 1 / (L : ℝ)) :
    ℕ → Q
  | 0 => x0
  | k + 1 =>
      let xk := constantStepMinimaxGradientMethod L x0 h hh k
      let hQ_nonempty := nonemptyOfPoint Q x0
      let ht := stepScale_mem_Icc hh
      let xPlus := x_f[Q; hQ_nonempty; hQ_closed; hQ_convex | fi; L] ((xk : E))
      ⟨(xk : E) + ((h : ℝ) * (L : ℝ)) • (xPlus - xk),
        hQ_convex.add_smul_sub_mem
          xk.property
          (maxTypeGradientMapping_mem
            Q hQ_nonempty hQ_closed hQ_convex fi (xk : E) L)
          ht⟩

section Trajectory

variable (L : NNRealˣ) (x0 : Q) (h : NNRealˣ) (hh : (h : ℝ) ≤ 1 / (L : ℝ))

local notation "x" =>
  constantStepMinimaxGradientMethod Q hQ_closed hQ_convex fi L x0 h hh
local notation "hQ_nonempty" =>
  nonemptyOfPoint Q x0
local notation "xf" "(" xBar ")" =>
  x_f[Q; hQ_nonempty; hQ_closed; hQ_convex | fi; L](xBar)
local notation "gf" "(" xBar ")" =>
  g_f[Q; hQ_nonempty; hQ_closed; hQ_convex | fi; L](xBar)

/-- The recursive Algorithm 2.8 trajectory starts from the prescribed feasible point `x₀`. -/
@[simp] theorem constantStepMinimaxGradientMethod_zero :
    x 0 = x0 :=
  rfl

/-- Each recursive update agrees with the textbook reduced-gradient step
`xₖ - h • g_f(xₖ; L)`. -/
@[simp] theorem constantStepMinimaxGradientMethod_succ
    (k : ℕ) :
    (x (k + 1) : E) =
      (x k : E) - (h : ℝ) • gf((x k : E)) := by
  let xPlus : E := xf((x k : E))
  have hx : xPlus - (x k : E) = -((x k : E) - xPlus) := by
    abel
  change (x k : E) + ((h : ℝ) * (L : ℝ)) • (xPlus - x k) =
    (x k : E) - (h : ℝ) • ((L : ℝ) • ((x k : E) - xPlus))
  calc
    (x k : E) + ((h : ℝ) * (L : ℝ)) • (xPlus - x k)
      = (x k : E) + ((h : ℝ) * (L : ℝ)) • (-((x k : E) - xPlus)) := by rw [hx]
    _ = (x k : E) - ((h : ℝ) * (L : ℝ)) • ((x k : E) - xPlus) := by
      simp [smul_neg, sub_eq_add_neg]
    _ = (x k : E) - (h : ℝ) • ((L : ℝ) • ((x k : E) - xPlus)) := by
      rw [smul_smul]

end Trajectory

end

end
