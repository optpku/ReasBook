/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_9
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable (f : E → ℝ) (g : E → EReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/- Algorithm 10.14 is `source-facing` in the chapter's fast proximal-gradient API.

Domain sampling:
- `T[...]` from Definition 10.9 is already the chapter owner for the constant-curvature
  prox-gradient step `x ↦ prox_(1 / L g) (x - (1 / L) ∇ f(x))`;
- `condition_number` from Definition 10.21 is already the chapter owner for `κ = L_f / σ`;
- `fista_constant_stepsize_x` / `fista_constant_stepsize_y` from Algorithm 10.13 set the local
  chapter style for accelerated-iterate owners, while Assumption 10.31 already exports the
  regularity instances needed to use such owners directly under `[hproblem]`;
- the genuinely new data in this item are the fixed condition number `κ = L_f / σ`, the resulting
  constant momentum coefficient, and the simultaneous recursions for `x^k` and `y^k`;
- as in Algorithm 10.13, the public owners should be the concrete recursive families `x^k` and
  `y^k` themselves, not an existential trajectory package or a public wrapper state.

Since the source names both `x^k` and `y^k`, the public API keeps those two sequences explicit.
The recursive pair used to implement the mutual update stays internal, and the theorem surface is
the atomic `zero`/`succ` API for `vfista_x` and `vfista_y`. -/

/-- The fixed V-FISTA momentum coefficient
`(√κ - 1) / (√κ + 1)` determined by the chapter condition number
`κ(Lf.toNNReal, σ) = L_f / σ`. -/
def vfista_momentum (Lf σ : PosReal) : ℝ :=
  let κ := κ(PosReal.toNNReal Lf, σ)
  (Real.sqrt κ - 1) / (Real.sqrt κ + 1)

-- Proof sketch: unfold `vfista_momentum` and then expand the chapter condition number; this gives
-- the textbook coefficient `(√(L_f / σ) - 1) / (√(L_f / σ) + 1)`.
/-- Expanding `vfista_momentum` yields the textbook coefficient
`(√(L_f / σ) - 1) / (√(L_f / σ) + 1)`. -/
@[simp] theorem vfista_momentum_eq (Lf σ : PosReal) :
    vfista_momentum Lf σ =
      (Real.sqrt ((Lf : ℝ) / (σ : ℝ)) - 1) /
        (Real.sqrt ((Lf : ℝ) / (σ : ℝ)) + 1) := by
  -- Unfold the fixed momentum once and then expand the chapter condition number.
  simp [vfista_momentum, condition_number_eq, PosReal.coe_toNNReal]

/-- The internal recursive pair implementing the mutually defined V-FISTA sequences
`(x^k, y^k)`. -/
private def vfista_state
    (x0 : E) (Lf σ : PosReal) :
    ℕ → E × E
  | 0 => (x0, x0)
  | k + 1 =>
      let (xk, yk) := vfista_state x0 Lf σ k
      let xNext := T[Lf; f, g] yk
      let β := vfista_momentum Lf σ
      (xNext, xNext + β • (xNext - xk))

/-- Algorithm 10.14: the primal V-FISTA iterate family `x^k`, with `x^0 = y^0 = x0`,
`x^(k+1) = prox_(1 / L_f g) (y^k - (1 / L_f) ∇ f(y^k))`, and the companion extrapolated sequence
`y^k` defined by the fixed momentum coefficient `((√(L_f / σ) - 1) / (√(L_f / σ) + 1))`. -/
def vfista_x
    (x0 : E) (Lf σ : PosReal) (k : ℕ) : E :=
  (vfista_state f g x0 Lf σ k).1

/-- The extrapolated V-FISTA point `y^k`. -/
def vfista_y
    (x0 : E) (Lf σ : PosReal) (k : ℕ) : E :=
  (vfista_state f g x0 Lf σ k).2

-- Proof sketch: unfold the internal recursive pair at the base index `0`; the first component is
-- definitionally `x0`.
/-- The initial primal V-FISTA iterate satisfies `x^0 = x0`. -/
@[simp] theorem vfista_x_zero
    (x0 : E) (Lf σ : PosReal) :
    vfista_x f g x0 Lf σ 0 = x0 := by
  -- At index `0`, the internal state is definitionally `(x0, x0)`.
  rfl

-- Proof sketch: unfold the internal recursive pair at the base index `0`; the second component is
-- definitionally `x0`.
/-- The initial extrapolated V-FISTA point satisfies `y^0 = x^0 = x0`. -/
@[simp] theorem vfista_y_zero
    (x0 : E) (Lf σ : PosReal) :
    vfista_y f g x0 Lf σ 0 = x0 := by
  -- At index `0`, the second projection of the internal state is also `x0`.
  rfl

-- Proof sketch: unfold the internal recursive pair at `k + 1`; the first component of the
-- successor pair is definitionally the prox-gradient update at the previous extrapolated point
-- `y^k`.
/-- Each V-FISTA successor iterate satisfies
`x^(k+1) = prox_(1 / L_f g) (y^k - (1 / L_f) ∇ f(y^k))`. -/
theorem vfista_x_succ
    (x0 : E) (Lf σ : PosReal) (k : ℕ) :
    vfista_x f g x0 Lf σ (k + 1) =
      T[Lf; f, g] (vfista_y f g x0 Lf σ k) :=
  by
  -- Unfold one recursive step; the first projection is the prox-gradient update at `y^k`.
  rfl

-- Proof sketch: unfold the internal recursive pair at `k + 1`; the second component of the
-- successor pair is definitionally `x^(k+1) + β (x^(k+1) - x^k)` with
-- `β = vfista_momentum Lf σ`.
/-- Each extrapolated V-FISTA point satisfies
`y^(k+1) = x^(k+1) + ((√(L_f / σ) - 1) / (√(L_f / σ) + 1)) (x^(k+1) - x^k)`. -/
theorem vfista_y_succ
    (x0 : E) (Lf σ : PosReal) (k : ℕ) :
    vfista_y f g x0 Lf σ (k + 1) =
      vfista_x f g x0 Lf σ (k + 1) +
        vfista_momentum Lf σ •
          (vfista_x f g x0 Lf σ (k + 1) - vfista_x f g x0 Lf σ k) := by
  -- Unfold one recursive step; the second projection is exactly the affine extrapolation formula.
  rfl

end
