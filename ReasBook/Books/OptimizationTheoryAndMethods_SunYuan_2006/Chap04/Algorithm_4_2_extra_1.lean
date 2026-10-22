/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1

-- Semantic recall: `lean_leansearch` confirmed the canonical `HasGradientAt`,
-- `gradient`, and `IsMinOn` APIs. There is no dedicated mathlib owner for the
-- Fletcher-Reeves iterative scheme itself, so this item is recorded as explicit
-- iterate/gradient/direction/step data.

/-- The ambient Euclidean space `ℝ^n` for the conjugate-gradient iterative scheme. -/
abbrev ConjugateGradientPoint (n : ℕ) := EuclideanSpace ℝ (Fin n)

section FletcherReevesCoefficient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Fletcher-Reeves coefficient `‖gNext‖² / ‖gPrev‖²` in invariant norm form. -/
noncomputable def fletcherReevesCoefficient (gPrev gNext : E) : ℝ :=
  ‖gNext‖ ^ (2 : ℕ) / ‖gPrev‖ ^ (2 : ℕ)

end FletcherReevesCoefficient

/-- The quadratic-case conjugate-gradient steplength `-(gᵀ d) / (dᵀ G d)`. -/
noncomputable def quadraticConjugateGradientStepSize {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ)
    (g d : ConjugateGradientPoint n) : ℝ :=
  -dotProduct g d / dotProduct d (Matrix.toEuclideanLin G d)

/-- The common run data for a nonlinear conjugate-gradient method on a real complete
inner-product space: the initial point, iterate sequence, explicit gradient data, search
directions, step sizes, and the guarantee that each recorded gradient is a gradient of `f` at the
corresponding iterate. Method-specific update rules and stopping criteria are layered on this
owner rather than duplicating these fields. The coordinate model `ConjugateGradientPoint n = ℝ^n`
is a specialization of this owner, not its public core. -/
structure ConjugateGradientRun (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) where
  x0 : E
  x : ℕ → E
  g : ℕ → E
  d : ℕ → E
  α : ℕ → ℝ
  x_zero : x 0 = x0
  hasGradientAt : ∀ k : ℕ, HasGradientAt f (g k) (x k)

/-- A conjugate-gradient run can be used as its sequence of iterates. -/
instance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} :
    CoeFun (ConjugateGradientRun E f) (fun _ ↦ ℕ → E) where
  coe A := A.x

namespace ConjugateGradientRun

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ}

/-- Evaluating a conjugate-gradient run as a function returns its iterate sequence. -/
theorem coe_apply (A : ConjugateGradientRun E f) (k : ℕ) :
    A k = A.x k :=
  rfl

/-- The explicit gradient data in a conjugate-gradient run agrees with the canonical gradient of
`f` at each iterate. -/
theorem gradient_eq (A : ConjugateGradientRun E f) (k : ℕ) :
    gradient f (A k) = A.g k := by
  simpa using (A.hasGradientAt k).gradient

/-- If a recorded gradient vanishes, the corresponding iterate is a stationary point of `f`. -/
theorem isStationaryPoint_of_gradient_eq_zero
    (A : ConjugateGradientRun E f) {k : ℕ} (hk : A.g k = 0) :
    IsStationaryPoint f (A.x k) := by
  exact (isStationaryPoint_iff f (A.x k)).2
    ⟨by simpa [hk] using (A.hasGradientAt k).gradient,
      (A.hasGradientAt k).differentiableAt⟩

/-- `method.HasStationaryContinuation` means that once a recorded gradient vanishes, the next
iterate is fixed. This is the nonlinear Chapter 4 run-level stationary-continuation bridge,
analogous to the post-termination stationary APIs recorded on the linear and preconditioned
owners. -/
def HasStationaryContinuation (method : ConjugateGradientRun E f) : Prop :=
  ∀ k : ℕ, method.g k = 0 → method (k + 1) = method k

/-- Under stationary continuation, once a run reaches a zero gradient, every later iterate
coincides with the iterate at that stage. -/
theorem x_eq_of_gradient_eq_zero
    (A : ConjugateGradientRun E f) (hStationary : A.HasStationaryContinuation)
    {k t : ℕ} (hk : A.g k = 0) (hkt : k ≤ t) :
    A.x t = A.x k := by
  induction hkt with
  | refl =>
      rfl
  | @step t hkt ih =>
      have hGrad_t : HasGradientAt f (A.g t) (A.x k) := by
        simpa [ih] using A.hasGradientAt t
      have hGrad_k : HasGradientAt f 0 (A.x k) := by
        simpa [hk] using A.hasGradientAt k
      have hgt : A.g t = 0 := hGrad_t.unique hGrad_k
      calc
        A.x (t + 1) = A.x t := hStationary t hgt
        _ = A.x k := ih

/-- Under stationary continuation, once a recorded gradient vanishes, every later recorded
gradient also vanishes. -/
theorem g_eq_zero_of_gradient_eq_zero
    (A : ConjugateGradientRun E f) (hStationary : A.HasStationaryContinuation)
    {k t : ℕ} (hk : A.g k = 0) (hkt : k ≤ t) :
    A.g t = 0 := by
  have hxt : A.x t = A.x k :=
    A.x_eq_of_gradient_eq_zero hStationary hk hkt
  have hGrad_t : HasGradientAt f (A.g t) (A.x k) := by
    simpa [hxt] using A.hasGradientAt t
  have hGrad_k : HasGradientAt f 0 (A.x k) := by
    simpa [hk] using A.hasGradientAt k
  exact hGrad_t.unique hGrad_k

end ConjugateGradientRun

/-- Chapter04 Algorithm 4.2-extra-1: a Fletcher-Reeves conjugate-gradient iterative
scheme on a real complete inner-product space consists of iterates `x k`, explicit gradient
data `g k`, search directions `d k`, exact line-search step sizes `α k`, and Fletcher-Reeves
coefficients `β k`. The initialization is `x 0 = x₀` and `d 0 = -g 0`. For every
`k`, `g k` is a gradient of `f` at `x k`. Whenever `g k ≠ 0`, the method takes an
exact line-search step and satisfies `x (k + 1) = x k + α k • d k`. Whenever both
`g k ≠ 0` and `g (k + 1) ≠ 0`, the Fletcher-Reeves coefficient satisfies
`β k = ‖g (k + 1)‖² / ‖g k‖²` and the next direction satisfies
`d (k + 1) = -g (k + 1) + β k • d k`. This indexes the source formula `β_(k - 1)`
as `β k` for the update from step `k` to step `k + 1`. -/
structure ConjugateGradientIterativeScheme (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ)
    extends ConjugateGradientRun E f where
  β : ℕ → ℝ
  direction_zero : d 0 = -g 0
  exactLineSearch :
    ∀ k : ℕ, g k ≠ 0 →
      IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k)
  iterate_eq :
    ∀ k : ℕ, g k ≠ 0 →
      x (k + 1) = x k + α k • d k
  beta_eq :
    ∀ k : ℕ, g k ≠ 0 → g (k + 1) ≠ 0 →
      β k = fletcherReevesCoefficient (g k) (g (k + 1))
  direction_eq :
    ∀ k : ℕ, g k ≠ 0 → g (k + 1) ≠ 0 →
      d (k + 1) = -g (k + 1) + β k • d k

/-- A conjugate-gradient iterative scheme can be used as its sequence of iterates. -/
instance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} :
    CoeFun (ConjugateGradientIterativeScheme E f) (fun _ ↦ ℕ → E) where
  coe A := A.x

namespace ConjugateGradientIterativeScheme

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ}

/-- Evaluating a Fletcher-Reeves scheme as a function returns its iterate sequence. -/
theorem coe_apply (A : ConjugateGradientIterativeScheme E f) (k : ℕ) :
    A k = A.x k :=
  rfl

/-- The explicit gradient data in a Fletcher-Reeves scheme agrees with the canonical gradient of
`f` at each iterate. -/
theorem gradient_eq (A : ConjugateGradientIterativeScheme E f) (k : ℕ) :
    gradient f (A k) = A.g k :=
  A.toConjugateGradientRun.gradient_eq k

/-- A conjugate-gradient iterative scheme terminates at stage `k` when `g k = 0`. -/
def terminatedAt (A : ConjugateGradientIterativeScheme E f) (k : ℕ) : Prop :=
  A.g k = 0

/-- `terminatedAt` unfolds to the vanishing-gradient stopping condition. -/
@[simp] theorem terminatedAt_iff (A : ConjugateGradientIterativeScheme E f) (k : ℕ) :
    A.terminatedAt k ↔ A.g k = 0 :=
  Iff.rfl

/-- `A.HasStationaryContinuation` means that once a Fletcher-Reeves run reaches a zero gradient,
the next iterate is fixed. This is the scheme-level source-facing restatement of the underlying
run-level stationary-continuation bridge. -/
def HasStationaryContinuation (A : ConjugateGradientIterativeScheme E f) : Prop :=
  A.toConjugateGradientRun.HasStationaryContinuation

/-- `HasStationaryContinuation` unfolds to the underlying run-level stationary-continuation
property. -/
@[simp] theorem hasStationaryContinuation_iff
    (A : ConjugateGradientIterativeScheme E f) :
    A.HasStationaryContinuation ↔ A.toConjugateGradientRun.HasStationaryContinuation :=
  Iff.rfl

/-- A terminating Fletcher-Reeves stage is a stationary point of `f`. -/
theorem isStationaryPoint_of_terminatedAt
    (A : ConjugateGradientIterativeScheme E f) {k : ℕ} (hk : A.terminatedAt k) :
    IsStationaryPoint f (A.x k) :=
  A.toConjugateGradientRun.isStationaryPoint_of_gradient_eq_zero hk

/-- Under stationary continuation, once a Fletcher-Reeves run terminates, every later iterate
coincides with the terminating iterate. -/
theorem x_eq_of_terminatedAt
    (A : ConjugateGradientIterativeScheme E f)
    (hStationary : A.HasStationaryContinuation)
    {k t : ℕ} (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.x t = A.x k :=
  A.toConjugateGradientRun.x_eq_of_gradient_eq_zero hStationary hk hkt

/-- Under stationary continuation, once a Fletcher-Reeves run terminates, every later recorded
gradient also vanishes. -/
theorem g_eq_zero_of_terminatedAt
    (A : ConjugateGradientIterativeScheme E f)
    (hStationary : A.HasStationaryContinuation)
    {k t : ℕ} (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.g t = 0 :=
  A.toConjugateGradientRun.g_eq_zero_of_gradient_eq_zero hStationary hk hkt

/-- Under stationary continuation, termination persists at every later stage. -/
theorem terminatedAt_mono
    (A : ConjugateGradientIterativeScheme E f)
    (hStationary : A.HasStationaryContinuation)
    {k t : ℕ} (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.terminatedAt t :=
  A.g_eq_zero_of_terminatedAt hStationary hk hkt

/-- Every nonterminal Fletcher-Reeves step has a nonnegative exact line-search steplength. -/
theorem stepSize_nonneg (A : ConjugateGradientIterativeScheme E f) {k : ℕ}
    (hk : A.g k ≠ 0) :
    0 ≤ A.α k :=
  (A.exactLineSearch k hk).nonneg

/-- A nonterminal Fletcher-Reeves step carries exact line search, the iterate update, and,
whenever the next stage is also nonterminal, the textbook Fletcher-Reeves coefficient and
direction recurrences. -/
theorem nonterminalStep (A : ConjugateGradientIterativeScheme E f) {k : ℕ}
    (hk : A.g k ≠ 0) :
    IsExactLineSearchStepOnNonnegativeRay f (A.x k) (A.d k) (A.α k) ∧
      A.x (k + 1) = A.x k + A.α k • A.d k ∧
      (A.g (k + 1) ≠ 0 →
        A.β k = fletcherReevesCoefficient (A.g k) (A.g (k + 1)) ∧
          A.d (k + 1) = -A.g (k + 1) + A.β k • A.d k) := by
  refine ⟨A.exactLineSearch k hk, A.iterate_eq k hk, ?_⟩
  intro hkNext
  exact ⟨A.beta_eq k hk hkNext, A.direction_eq k hk hkNext⟩

/-- Exact line search keeps every nonterminal iterate inside the initial lower level set, while
stationary continuation keeps the run there after termination. -/
theorem x_mem_lowerLevelSetOn_univ
    (A : ConjugateGradientIterativeScheme E f)
    (hStationary : A.HasStationaryContinuation)
    (k : ℕ) :
    A.x k ∈ lowerLevelSetOn Set.univ f A.x0 := by
  induction k with
  | zero =>
      simp [lowerLevelSetOn, A.x_zero]
  | succ k ih =>
      by_cases hk : A.g k = 0
      · have hEq : A.x (k + 1) = A.x k := hStationary k hk
        simpa [hEq] using ih
      · have hfxk : f (A.x k) ≤ f A.x0 := by
          exact ((mem_lowerLevelSetOn Set.univ f A.x0 (A.x k)).1 ih).2
        have hmin :
            lineSearchObjective f (A.x k) (A.d k) (A.α k) ≤
              lineSearchObjective f (A.x k) (A.d k) 0 :=
          (A.exactLineSearch k hk).optimal (by simp)
        have hfxsucc : f (A.x (k + 1)) ≤ f (A.x k) := by
          simpa [lineSearchObjective_apply, lineSearchObjective_zero, A.iterate_eq k hk] using hmin
        exact (mem_lowerLevelSetOn Set.univ f A.x0 (A.x (k + 1))).2
          ⟨by simp, le_trans hfxsucc hfxk⟩

end ConjugateGradientIterativeScheme

section QuadraticStepSize

variable {n : ℕ}

local notation "Point" => ConjugateGradientPoint n

variable {f : Point → ℝ}

/-- For a quadratic objective, expressed here by the global affine-gradient hypothesis
`x ↦ Matrix.toEuclideanLin G x + b`, the exact line-search step size along the ray
`Set.Ici 0` has the textbook form `-(g_kᵀ d_k) / (d_kᵀ G d_k)` provided the current
search direction has positive quadratic curvature and is a descent direction, and
the current stage is nonterminal with `g k ≠ 0`, so the ray minimizer is the
interior quadratic minimizer rather than the boundary point `0`. -/
theorem quadratic_stepSize_eq
    (A : ConjugateGradientIterativeScheme Point f)
    (G : Matrix (Fin n) (Fin n) ℝ) (b : Point) {k : ℕ}
    (h_nonterminal : A.g k ≠ 0)
    (h_gradient :
      ∀ x : Point, HasGradientAt f (Matrix.toEuclideanLin G x + b) x)
    (h_curvature : 0 < dotProduct (A.d k) (Matrix.toEuclideanLin G (A.d k)))
    (h_descent : dotProduct (A.g k) (A.d k) < 0) :
    A.α k = quadraticConjugateGradientStepSize G (A.g k) (A.d k) := sorry

end QuadraticStepSize

/-- A Fletcher-Reeves conjugate-gradient method is a Fletcher-Reeves iterative scheme whose run
stays fixed after termination. This is the source-facing owner for the post-termination behavior
used in the Chapter 4.3 convergence theorems, rather than a separate bridge hypothesis on the
weaker iterative-scheme owner. -/
structure FletcherReevesMethod (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ)
    extends ConjugateGradientIterativeScheme E f where
  stationaryContinuation :
    ∀ k : ℕ, g k = 0 → x (k + 1) = x k

namespace FletcherReevesMethod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ}

/-- The source-facing stationary-continuation field upgrades a Fletcher-Reeves method to the
scheme-level eventual-constancy bridge. -/
theorem hasStationaryContinuation
    (A : FletcherReevesMethod E f) :
    A.toConjugateGradientIterativeScheme.HasStationaryContinuation := by
  intro k hk
  simpa using A.stationaryContinuation k hk

/-- A terminating Fletcher-Reeves stage is a stationary point of `f`. -/
theorem isStationaryPoint_of_terminatedAt
    (A : FletcherReevesMethod E f) {k : ℕ} (hk : A.terminatedAt k) :
    IsStationaryPoint f (A.x k) :=
  A.toConjugateGradientIterativeScheme.isStationaryPoint_of_terminatedAt hk

/-- Every iterate of a Fletcher-Reeves method stays in the initial lower level set. -/
theorem x_mem_lowerLevelSetOn_univ
    (A : FletcherReevesMethod E f) (k : ℕ) :
    A.x k ∈ lowerLevelSetOn Set.univ f A.x0 :=
  A.toConjugateGradientIterativeScheme.x_mem_lowerLevelSetOn_univ
    A.hasStationaryContinuation k

end FletcherReevesMethod
