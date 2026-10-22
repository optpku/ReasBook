/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: accelerated optimal-method recurrences and their canonical scalar sequences on
real Hilbert spaces.

Owner declarations sampled in this domain:
* `estimatingWeight` in `Theorem_2_19`, the source-facing recurrence `λ₀ = 1`,
  `λₖ₊₁ = (1 - αₖ) λₖ`;
* `constantStepSchemeIToOptimalMethodRecurrence` in `Algorithm_2_3`, a later bridge packaging a
  concrete recursive scheme into the owner recurrence declared here;
* `ConstantStepSchemeIIMomentumRecurrence` in `Algorithm_2_4`, the lighter type-II owner obtained
  by eliminating the auxiliary optimal-method data from the heavier recurrence below;
* `GeneralOptimalMethodScheme` in this file, the direct extension of the recurrence owner by the
  step-`(c)` descent inequality.

Layer triage for this file:
* `source-facing`: Algorithm 2.2 itself, with the displayed sequences
  `(xₖ, yₖ, vₖ, αₖ, γₖ)` and the step-`(c)` decrease bound;
* `core/canonical`: `OptimalMethodRecurrence`, which owns the recurrence data and the canonical
  estimating-sequence weight attached to it;
* `bridge/view`: `GeneralOptimalMethodScheme`, which adds only the descent inequality and should
  reuse the owner iterate view rather than duplicating it.

Primitive data:
* the recurrence sequences `x`, `y`, `v`, `alpha`, `gamma`;
* the initialization and update laws from Algorithm 2.2.

Derived API:
* the canonical weight sequence `method.weight`;
* positivity of the coefficients and weights;
* the curvature-gap identity
  `γₖ - μ = λₖ (γ₀ - μ)`;
* the iterate-sequence coercions for the owner and its descent-inequality extension. -/

/-- The common recurrence data shared by the optimal-method schemes in this chapter: the
sequences `x_k`, `y_k`, `v_k`, `alpha_k`, and `gamma_k` satisfy the initialization, coefficient
equation, curvature update, interpolation formula, and center update recurrences. -/
structure OptimalMethodRecurrence
    (f : E → ℝ) (L mu : ℝ) (x0 : E) (gamma0 : ℝ) where
  /-- The smoothness parameter is positive. -/
  L_pos : 0 < L
  /-- The strong-convexity parameter is nonnegative. -/
  mu_nonneg : 0 ≤ mu
  /-- The initial curvature parameter is positive. -/
  gamma0_pos : 0 < gamma0
  /-- The main iterate sequence. -/
  x : ℕ → E
  /-- The auxiliary interpolation points. -/
  y : ℕ → E
  /-- The estimating-sequence centers. -/
  v : ℕ → E
  /-- The interpolation coefficients `alpha_k`. -/
  alpha : ℕ → ℝ
  /-- The curvature parameters `γ_k`. -/
  gamma : ℕ → ℝ
  /-- The method starts from the prescribed initial point `x0`. -/
  x_zero : x 0 = x0
  /-- The auxiliary sequence is initialized by `v₀ = x₀`. -/
  v_zero : v 0 = x0
  /-- The curvature sequence starts from the prescribed initial value `γ₀ = gamma0`. -/
  gamma_zero : gamma 0 = gamma0
  /-- Each interpolation coefficient lies strictly between `0` and `1`. -/
  alpha_mem_Ioo : ∀ k : ℕ, alpha k ∈ Set.Ioo (0 : ℝ) 1
  /-- Each `alpha_k` satisfies Nesterov's quadratic relation from step `(a)`. -/
  alpha_equation : ∀ k : ℕ,
    L * alpha k ^ (2 : ℕ) = (1 - alpha k) * gamma k + alpha k * mu
  /-- The curvature parameter is updated by the recurrence from step `(a)`. -/
  gamma_succ : ∀ k : ℕ,
    gamma (k + 1) = (1 - alpha k) * gamma k + alpha k * mu
  /-- The point `y_k` is the weighted average from step `(b)`. -/
  y_eq : ∀ k : ℕ,
    y k =
      (1 / (gamma k + alpha k * mu)) •
        ((alpha k * gamma k) • v k + gamma (k + 1) • x k)
  /-- The auxiliary sequence is updated by the formula from step `(d)`. -/
  v_succ : ∀ k : ℕ,
    v (k + 1) =
      (1 / (gamma (k + 1))) •
        (((1 - alpha k) * gamma k) • v k +
          (alpha k * mu) • y k -
          alpha k • ∇ f (y k))

namespace OptimalMethodRecurrence

variable {f : E → ℝ} {L mu : ℝ} {x0 : E} {gamma0 : ℝ}

/-- An optimal-method recurrence can be viewed as its main iterate sequence `x_k`. -/
instance : CoeFun (OptimalMethodRecurrence f L mu x0 gamma0) (fun _ ↦ ℕ → E) where
  coe method := method.x

end OptimalMethodRecurrence

/-- Algorithm 2.2: a general optimal-method scheme for `f : E → ℝ` with inputs `L > 0`,
`mu ≥ 0`, initial point `x0`, and initial curvature parameter `gamma0 > 0` is an
`OptimalMethodRecurrence` whose next iterate also satisfies the step-`(c)` descent inequality
`f(x_{k+1}) ≤ f(y_k) - (1 / (2 * L)) * ‖∇ f(y_k)‖^2`. The source text is written on `ℝⁿ`, but
the owner abstraction only uses real-Hilbert-space structure. -/
structure GeneralOptimalMethodScheme
    (f : E → ℝ) (L mu : ℝ) (x0 : E) (gamma0 : ℝ)
    extends OptimalMethodRecurrence f L mu x0 gamma0 where
  /-- The next iterate satisfies the descent inequality from step `(c)`. -/
  x_succ_le : ∀ k : ℕ,
    f (x (k + 1)) ≤ f (y k) - (1 / (2 * L)) * ‖∇ f (y k)‖ ^ (2 : ℕ)

/-- A general optimal-method scheme reuses the iterate-sequence view of its underlying optimal
method recurrence. -/
instance {f : E → ℝ} {L mu : ℝ} {x0 : E} {gamma0 : ℝ} :
    CoeFun (GeneralOptimalMethodScheme f L mu x0 gamma0) (fun _ ↦ ℕ → E) where
  coe method := method.toOptimalMethodRecurrence

/-- A general optimal-method scheme canonically forgets to its underlying optimal-method
recurrence. -/
instance {f : E → ℝ} {L mu : ℝ} {x0 : E} {gamma0 : ℝ} :
    Coe (GeneralOptimalMethodScheme f L mu x0 gamma0)
      (OptimalMethodRecurrence f L mu x0 gamma0) where
  coe method := method.toOptimalMethodRecurrence

namespace OptimalMethodRecurrence

variable {f : E → ℝ} {L mu : ℝ} {x0 : E} {gamma0 : ℝ}

/-- The estimating-sequence weight `λₖ` canonically attached to an optimal-method recurrence. -/
def weight
    (method : OptimalMethodRecurrence f L mu x0 gamma0) :
    ℕ → ℝ
  | 0 => 1
  | k + 1 => (1 - method.alpha k) * weight method k

/-- The owner weight sequence starts from `λ₀ = 1`. -/
@[simp] theorem weight_zero
    (method : OptimalMethodRecurrence f L mu x0 gamma0) :
    method.weight 0 = 1 :=
  rfl

/-- The owner weight sequence satisfies `λₖ₊₁ = (1 - αₖ) λₖ`. -/
@[simp] theorem weight_succ
    (method : OptimalMethodRecurrence f L mu x0 gamma0) (k : ℕ) :
    method.weight (k + 1) = (1 - method.alpha k) * method.weight k :=
  rfl

section WeightedAverage

variable {F : Type*} [AddCommMonoid F] [Module ℝ F]

/-- The textbook weighted finite average attached to the owner coefficients `αᵢ` and `λᵢ`. This
is the common recurrence-side averaging operator used later for weighted sampled points and
gradient averages. -/
def weightedAverage
    (method : OptimalMethodRecurrence f L mu x0 gamma0)
    (z : ℕ → F) (k : ℕ) : F :=
  let lam := method.weight k
  (lam / (1 - lam)) •
    ∑ i ∈ Finset.range k, (method.alpha i / method.weight (i + 1)) • z i

end WeightedAverage

/-- The curvature update `γ_{k+1}` can equally be written as `L * alpha_k^2`. -/
theorem gamma_succ_eq_L_mul_sq
    (method : OptimalMethodRecurrence f L mu x0 gamma0) (k : ℕ) :
    method.gamma (k + 1) = L * method.alpha k ^ (2 : ℕ) := by
  exact (method.gamma_succ k).trans (method.alpha_equation k).symm

/-- Every interpolation coefficient in an optimal-method recurrence is positive. -/
theorem alpha_pos
    (method : OptimalMethodRecurrence f L mu x0 gamma0) (k : ℕ) :
    0 < method.alpha k := by
  exact (method.alpha_mem_Ioo k).1

/-- Every canonical estimating-sequence weight stays positive because each update factor
`1 - αₖ` lies in `(0, 1)`. -/
theorem weight_pos
    (method : OptimalMethodRecurrence f L mu x0 gamma0) (k : ℕ) :
    0 < method.weight k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [method.weight_succ]
      exact mul_pos (sub_pos.mpr (method.alpha_mem_Ioo k).2) ih

/-- The curvature gap factors through the canonical estimating-sequence weight:
`γₖ - μ = λₖ (γ₀ - μ)`. -/
theorem gamma_sub_mu_eq_weight_mul_initial_gap
    (method : OptimalMethodRecurrence f L mu x0 gamma0) (k : ℕ) :
    method.gamma k - mu = method.weight k * (gamma0 - mu) := by
  induction k with
  | zero =>
      simpa using method.gamma_zero
  | succ k ih =>
      have hsucc :
          method.gamma (k + 1) - mu =
            (1 - method.alpha k) * (method.gamma k - mu) := by
        nlinarith [method.gamma_succ k]
      calc
        method.gamma (k + 1) - mu
            = (1 - method.alpha k) * (method.gamma k - mu) := hsucc
        _ = (1 - method.alpha k) * (method.weight k * (gamma0 - mu)) := by rw [ih]
        _ = method.weight (k + 1) * (gamma0 - mu) := by
              rw [method.weight_succ]
              ring

end OptimalMethodRecurrence

end
