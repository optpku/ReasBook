/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Remark_2_35_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The primary domain here is Algorithm 2.6's projected-gradient recursion on a simple closed
convex set in a real Hilbert space.

Owner abstractions sampled for this refinement:
* `gradientMapping` from `Definition_2_35_1` owns the one-step projected-gradient point;
* `reducedGradient` from `Definition_2_35_1` owns the reduced-gradient encoding of that step;
* `HasGradientAt` from `Chap01/Definition_1_4_6`, the owner predicate asserting that the
  displayed vector `∇ f x` is the genuine gradient at `x`;
* `projectedGradientSequence_dist_le_geometric` from `Theorem_2_38`, whose source-facing
  hypotheses are the explicit projected-gradient recursion and feasible initial point.

Source/core/bridge triage:
* source-facing: `simpleSetGradientMethod`, the recursive Algorithm 2.6 trajectory in the
  positive-`γ` setting;
* core/canonical: `gradientMapping` and `reducedGradient`;
* bridge/view: the owner-facing `gradientMapping` recursion lemma together with the explicit
  recurrence data exported for `Theorem_2_38`.

Primitive data are the feasible set `Q`, objective `f`, feasible initial point `x0 ∈ Q`, and
positive parameter `γ`. The recursive trajectory is defined directly from the chapter owner step
map. Feasibility, the source-facing recursion laws, and any iteratewise hypotheses asserting that
the displayed vectors `∇ f (x_k)` are genuine gradients are derived bridge API layered on top of
that owner. This matches the chapter style where trajectory owners remain primitive and
`HasGradientAt` data are attached separately when a later theorem needs them. The textbook `ℝⁿ`
algorithm is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/

section

variable
    (Q : Set E)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ)
    (x0 : E) (hx0 : x0 ∈ Q)
    (γ : NNRealˣ)

/-- Algorithm 2.6: the simple-set gradient method produces the iterate sequence
`(x_k)_{k ≥ 0}` starting from `x₀ = x0` and recursively updating by
`xₖ₊₁ = x_Q[Q; ⟨x0, hx0⟩; hQ_closed; hQ_convex | f; γ](xₖ)`.
Equivalently, each step satisfies
`xₖ₊₁ = xₖ - γ⁻¹ • g_Q[Q; ⟨x0, hx0⟩; hQ_closed; hQ_convex | f; γ](xₖ)`.
The output-feasibility statement `(x_k) ⊆ Q` is recorded in companion theorems. -/
noncomputable def simpleSetGradientMethod
    (Q : Set E)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ)
    (x0 : E) (hx0 : x0 ∈ Q)
    (γ : NNRealˣ)
    :
    ℕ → E :=
  Nat.rec x0 fun _ xk ↦
    x_Q[Q; ⟨x0, hx0⟩; hQ_closed; hQ_convex | f; γ](xk)

local notation "x" => simpleSetGradientMethod Q hQ_closed hQ_convex f x0 hx0 γ

/-- The simple-set gradient method starts from the prescribed feasible point `x0`. -/
-- Proof sketch: unfold the recursive definition at `0`.
@[simp] theorem simpleSetGradientMethod_zero
    :
    x 0 = x0 :=
  rfl

/-- Each successor iterate also agrees with the chapter owner projected-gradient point. -/
-- Proof sketch: unfold the recursion at stage `k + 1`.
theorem simpleSetGradientMethod_succ_eq_gradientMapping
    (k : ℕ) :
    x (k + 1) = x_Q[Q; ⟨x0, hx0⟩; hQ_closed; hQ_convex | f; γ](x k) :=
  rfl

/-- Every iterate of the simple-set gradient method lies in `Q`. -/
-- Proof sketch: this is the generic projected-gradient recurrence feasibility theorem from
-- `Theorem_2_38`, specialized to the recursive trajectory `simpleSetGradientMethod`.
theorem simpleSetGradientMethod_mem
    (k : ℕ) :
    x k ∈ Q := by
  exact ProjectedGradientSequence.mem hx0
    (simpleSetGradientMethod_zero Q hQ_closed hQ_convex f x0 hx0 γ)
    (simpleSetGradientMethod_succ_eq_gradientMapping Q hQ_closed hQ_convex f x0 hx0 γ)
    k

/-- The displayed `∇ f (xₖ)` is the genuine gradient at every iterate of the simple-set gradient
method. -/
-- Proof sketch: apply the iteratewise hypothesis `hf_grad` to `x k`, using
-- `simpleSetGradientMethod_mem` to discharge feasibility.
theorem simpleSetGradientMethod_hasGradientAt
    (hf_grad : ∀ y ∈ Q, HasGradientAt f (∇ f y) y)
    (k : ℕ) :
    HasGradientAt f (∇ f (x k)) (x k) :=
  hf_grad (x k) (simpleSetGradientMethod_mem Q hQ_closed hQ_convex f x0 hx0 γ k)

/-- The objective is differentiable at every iterate of the simple-set gradient method. -/
-- Proof sketch: apply `HasGradientAt.differentiableAt` to
-- `simpleSetGradientMethod_hasGradientAt`.
theorem simpleSetGradientMethod_differentiableAt
    (hf_grad : ∀ y ∈ Q, HasGradientAt f (∇ f y) y)
    (k : ℕ) :
    DifferentiableAt ℝ f (x k) :=
  (simpleSetGradientMethod_hasGradientAt
    Q hQ_closed hQ_convex f x0 hx0 γ hf_grad k).differentiableAt

/-- The objective is within-set differentiable at every iterate of the simple-set gradient
method. -/
-- Proof sketch: first get `DifferentiableAt` from `simpleSetGradientMethod_differentiableAt`,
-- then restrict it to `Q` via `DifferentiableAt.differentiableWithinAt`.
theorem simpleSetGradientMethod_differentiableWithinAt
    (hf_grad : ∀ y ∈ Q, HasGradientAt f (∇ f y) y)
    (k : ℕ) :
    DifferentiableWithinAt ℝ f Q (x k) :=
  (simpleSetGradientMethod_differentiableAt
    Q hQ_closed hQ_convex f x0 hx0 γ hf_grad k).differentiableWithinAt

/-- The simple-set gradient method satisfies the textbook update rule
`x_{k+1} = x_k - γ⁻¹ g_Q(x_k; γ)` at each step. -/
-- Proof sketch: unfold one recursive step and rewrite it using
-- `gradientMapping_eq_point_sub_inv_smul_reducedGradient`.
@[simp] theorem simpleSetGradientMethod_succ
    (k : ℕ) :
    x (k + 1) =
      x k -
        (γ : ℝ)⁻¹ • g_Q[Q; ⟨x0, hx0⟩; hQ_closed; hQ_convex | f; γ](x k) := by
  rw [simpleSetGradientMethod_succ_eq_gradientMapping]
  simpa using
    gradientMapping_eq_point_sub_inv_smul_reducedGradient
      Q ⟨x0, hx0⟩ hQ_closed hQ_convex f (x k) γ

end

end
