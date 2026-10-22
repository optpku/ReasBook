/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1

noncomputable section

open scoped Gradient

-- Semantic recall: Step 2 is modeled with explicit gradient data `g k` and
-- `HasGradientAt`, matching local Chapter 3 precedent; the Hessian and exact
-- line search still use the canonical `∇ f`, `HasFDerivAt (∇ f)`, and the
-- repository's source-facing exact line-search owner on the nonnegative ray.

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- Chapter03 Algorithm 3.2.3: Newton's method with line search consists of a tolerance
`ε ≥ 0`, an initial point `x₀ : ℝⁿ`, iterates `x k`, explicit gradient data `g k`,
Newton directions `d k`, step sizes `α k`, and Hessian operators `G k` satisfying
`x 0 = x₀`. At every index `k`, `g k` is the gradient of `f` at `x k`; at every
nonterminal index with `ε < ‖g k‖`, the operator `G k` is the Hessian of `f` at `x k`,
the Newton equation `G k (d k) = -g k` is solved, `α k` is an exact line-search
minimizer of
`a ↦ f (x k + a • d k)` on `Set.Ici 0`, and the next iterate is
`x (k + 1) = x k + α k • d k`. -/
structure NewtonMethodWithLineSearch (n : ℕ) (f : Point → ℝ) where
  ε : ℝ
  x0 : Point
  x : ℕ → Point
  g : ℕ → Point
  d : ℕ → Point
  α : ℕ → ℝ
  G : ℕ → Point →L[ℝ] Point
  eps_nonneg : 0 ≤ ε
  x_zero : x 0 = x0
  hasGradientAt : ∀ k : ℕ, HasGradientAt f (g k) (x k)
  hessian : ∀ k : ℕ, ε < ‖g k‖ → HasFDerivAt (∇ f) (G k) (x k)
  linearSystem :
    ∀ k : ℕ, ε < ‖g k‖ → G k (d k) = -g k
  exactLineSearch :
    ∀ k : ℕ, ε < ‖g k‖ → IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k)
  update :
    ∀ k : ℕ, ε < ‖g k‖ →
      x (k + 1) = x k + α k • d k

/-- A Newton method with line search can be used as its iterate sequence `x`. -/
instance {f : Point → ℝ} : CoeFun (NewtonMethodWithLineSearch n f) (fun _ ↦ ℕ → Point) where
  coe A := A.x

/-- Evaluating a Newton method with line search as a function returns its iterate sequence. -/
theorem NewtonMethodWithLineSearch.coe_apply {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) (k : ℕ) :
    A k = A.x k :=
  rfl

/-- The explicit gradient data in a Newton method with line search agrees with
the canonical gradient `∇ f` at every iterate. -/
theorem NewtonMethodWithLineSearch.gradient_eq {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) (k : ℕ) :
    ∇ f (A.x k) = A.g k :=
  (A.hasGradientAt k).gradient

/-- The stopping condition for a Newton method with line search iterate is
`‖g k‖ ≤ ε`. -/
def NewtonMethodWithLineSearch.terminatedAt {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) (k : ℕ) : Prop :=
  ‖A.g k‖ ≤ A.ε

/-- `terminatedAt` unfolds to the gradient-norm stopping test from Algorithm 3.2.3. -/
theorem NewtonMethodWithLineSearch.terminatedAt_iff {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) (k : ℕ) :
    A.terminatedAt k ↔ ‖A.g k‖ ≤ A.ε :=
  Iff.rfl

/-- At a zero-tolerance terminal iterate, the recorded gradient vector vanishes. -/
theorem NewtonMethodWithLineSearch.g_eq_zero_of_terminatedAt_zeroTolerance {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) {k : ℕ}
    (hε : A.ε = 0) (hk : A.terminatedAt k) :
    A.g k = 0 := by
  rw [A.terminatedAt_iff, hε] at hk
  exact norm_eq_zero.mp <| le_antisymm hk (norm_nonneg _)

/-- At a zero-tolerance terminal iterate, the current point is stationary in the canonical
Chapter 1 sense. -/
theorem NewtonMethodWithLineSearch.isStationaryPoint_of_terminatedAt_zeroTolerance
    {f : Point → ℝ} (A : NewtonMethodWithLineSearch n f) {k : ℕ}
    (hε : A.ε = 0) (hk : A.terminatedAt k) :
    IsStationaryPoint f (A k) := by
  have hg : A.g k = 0 := A.g_eq_zero_of_terminatedAt_zeroTolerance hε hk
  simpa [IsStationaryPoint, NewtonMethodWithLineSearch.coe_apply, hg] using
    (A.hasGradientAt k).hasFDerivAt

/-- `A.IsTerminalIndex k` means that Algorithm 3.2.3 has reached its stop test at `k`
and the iterate sequence stays constant afterwards, so the recorded `ℕ`-indexed data
encodes a finite run with last generated iterate `A.x k`. -/
def NewtonMethodWithLineSearch.IsTerminalIndex {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) (k : ℕ) : Prop :=
  A.terminatedAt k ∧ ∀ t : ℕ, k ≤ t → A t = A k

/-- `A.IsTerminalIndex k` unfolds to the stop test at `k` together with a constant
iterate tail after `k`. -/
theorem NewtonMethodWithLineSearch.isTerminalIndex_iff {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) (k : ℕ) :
    A.IsTerminalIndex k ↔ A.terminatedAt k ∧ ∀ t : ℕ, k ≤ t → A t = A k :=
  Iff.rfl

/-- A finite run of Algorithm 3.2.3 has a terminal iterate `k` satisfying the stop
test, after which the iterate sequence stays constant. -/
def NewtonMethodWithLineSearch.IsFiniteSequence {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) : Prop :=
  ∃ k, A.IsTerminalIndex k

/-- `A.DoesNotTerminate` is the source-level nontermination condition that the stop test
`‖g k‖ ≤ ε` never succeeds at any index. This is stronger than merely having no constant tail,
and is therefore the right owner for theorems about genuinely nonterminating Newton runs. -/
def NewtonMethodWithLineSearch.DoesNotTerminate {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) : Prop :=
  ∀ k, ¬ A.terminatedAt k

/-- Unfolding `A.DoesNotTerminate` says that every iterate fails the source stop test. -/
theorem NewtonMethodWithLineSearch.doesNotTerminate_iff {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) :
    A.DoesNotTerminate ↔ ∀ k, ¬ A.terminatedAt k :=
  Iff.rfl

/-- A run of Algorithm 3.2.3 is infinite when it has no terminal iterate with stop test
and constant tail. -/
def NewtonMethodWithLineSearch.IsInfiniteSequence {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) : Prop :=
  ¬ A.IsFiniteSequence

/-- Unfolding `A.IsInfiniteSequence` says that `A` has no terminal iterate. -/
theorem NewtonMethodWithLineSearch.isInfiniteSequence_iff {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) :
    A.IsInfiniteSequence ↔ ∀ k, ¬ A.IsTerminalIndex k := by
  constructor
  · intro hA k hk
    exact hA ⟨k, hk⟩
  · intro hA hFinite
    rcases hFinite with ⟨k, hk⟩
    exact hA k hk

/-- A genuinely nonterminating Newton run has no terminal index, hence is infinite in the weaker
sense of having no terminal constant tail. -/
theorem NewtonMethodWithLineSearch.isInfiniteSequence_of_doesNotTerminate {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) (hNoTerminate : A.DoesNotTerminate) :
    A.IsInfiniteSequence := by
  intro hFinite
  rcases hFinite with ⟨k, hkTerminal⟩
  exact hNoTerminate k hkTerminal.1

/-- At every nonterminal stage, Algorithm 3.2.3 records the Hessian of `f`, solves the
Newton equation, performs exact line search, and updates the iterate. -/
theorem NewtonMethodWithLineSearch.step {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    HasFDerivAt (∇ f) (A.G k) (A.x k) ∧
      A.G k (A.d k) = -A.g k ∧
      IsExactLineSearchStepOnNonnegativeRay f (A.x k) (A.d k) (A.α k) ∧
      A.x (k + 1) = A.x k + A.α k • A.d k :=
  ⟨A.hessian k hNotStopped, A.linearSystem k hNotStopped,
    A.exactLineSearch k hNotStopped, A.update k hNotStopped⟩

/-- At every nonterminal stage, exact line search and the recorded iterate update force the
objective value to be nonincreasing along the Newton run. -/
theorem NewtonMethodWithLineSearch.objective_nonincreasing_step {f : Point → ℝ}
    (A : NewtonMethodWithLineSearch n f) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    f (A (k + 1)) ≤ f (A k) := by
  have hMin :
      lineSearchObjective f (A.x k) (A.d k) (A.α k) ≤
        lineSearchObjective f (A.x k) (A.d k) 0 :=
    (A.exactLineSearch k hNotStopped).optimal (by simp)
  simpa [lineSearchObjective_apply, lineSearchObjective_zero, A.update k hNotStopped] using hMin
