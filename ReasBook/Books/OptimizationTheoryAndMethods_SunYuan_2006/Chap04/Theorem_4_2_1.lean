/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_1_3
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Matrix.PosDef

open Matrix

noncomputable section

-- Domain sampling for this item:
-- * primary domain: conjugate-gradient recurrences for positive-definite quadratic objectives on
--   `ℝ^n`;
-- * inspected owner declarations in the chapter/project domain:
--   `ConjugateGradientRun`,
--   `ConjugateGradientIterativeScheme`,
--   `quadraticObjective`,
--   `posDefEigenvalues`;
-- * source/core/bridge triage:
--   `ConjugateGradientIterativeScheme` is the core/canonical owner for the common run data and
--   Fletcher-Reeves recurrence,
--   `quadraticObjective` is the canonical quadratic objective owner already used earlier in the
--   chapter,
--   and `LinearConjugateGradientMethod` is a source-facing quadratic specialization that adds
--   only the linear-system residual identification and the stronger whole-line exact line search;
-- * primitive data vs derived API:
--   the iterate, gradient, direction, step-size, and Fletcher-Reeves coefficient sequences are
--   primitive in `ConjugateGradientIterativeScheme`,
--   while the affine residual formula, whole-line exact line search, quadratic step-size and
--   coefficient formulas, and post-termination continuation are the derived/source-specific layer
--   recorded here.

section

variable {n : ℕ}

local notation "Point" => ConjugateGradientPoint n

/-- A linear conjugate-gradient method for the linear system
`Matrix.toEuclideanLin G x + b = 0` is the quadratic specialization of the chapter's
conjugate-gradient scheme owner. The primitive run data `x`, `g`, `d`, `α`, `β`, and `x₀`
come from `ConjugateGradientIterativeScheme`; this source-facing structure adds the residual
identification `g_k = G x_k + b`, the stronger exact line search on the whole affine line, the
quadratic quotient formulas, and the post-termination stationary continuation. -/
structure LinearConjugateGradientMethod
    (G : Matrix (Fin n) (Fin n) ℝ) (b : Point)
    extends ConjugateGradientIterativeScheme n (quadraticObjective G b 0) where
  gradient_eq_residual :
    ∀ k : ℕ, g k = Matrix.toEuclideanLin G (x k) + b
  exactLineSearchOnLine :
    ∀ k : ℕ, g k ≠ 0 →
      IsMinOn (lineSearchObjective (quadraticObjective G b 0) (x k) (d k)) Set.univ (α k)
  direction_ne_zero :
    ∀ k : ℕ, g k ≠ 0 → d k ≠ 0
  stepSize_denom_ne_zero :
    ∀ k : ℕ, g k ≠ 0 →
      dotProduct (d k) (Matrix.toEuclideanLin G (d k)) ≠ 0
  stepSize_eq :
    ∀ k : ℕ, g k ≠ 0 →
      α k =
        dotProduct (g k) (g k) /
          dotProduct (d k) (Matrix.toEuclideanLin G (d k))
  beta_denom_ne_zero :
    ∀ k : ℕ, g k ≠ 0 →
      dotProduct (g k) (g k) ≠ 0
  beta_eq_dotProduct :
    ∀ k : ℕ, g k ≠ 0 →
      β k =
        dotProduct (g (k + 1)) (g (k + 1)) /
          dotProduct (g k) (g k)
  direction_eq_nonterminal :
    ∀ k : ℕ, g k ≠ 0 →
      d (k + 1) = -g (k + 1) + β k • d k
  stationaryContinuation :
    ∀ k : ℕ, g k = 0 → x (k + 1) = x k
  direction_eq_zero_of_terminated :
    ∀ k : ℕ, g k = 0 → d k = 0

/-- The number of distinct real eigenvalues of a positive-definite real matrix `G`. -/
def posDefDistinctEigenvalueCount {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) : ℕ :=
  Nat.card { μ : ℝ // μ ∈ Set.range (posDefEigenvalues G hG) }

namespace LinearConjugateGradientMethod

variable {G : Matrix (Fin n) (Fin n) ℝ} {b : Point}

/-- `A.IsFirstTerminatingIndex k` means that `k` is the first stage at which the recorded
gradient/residual vanishes. -/
def IsFirstTerminatingIndex (A : LinearConjugateGradientMethod G b) (k : ℕ) : Prop :=
  A.terminatedAt k ∧ ∀ t : ℕ, t < k → ¬ A.terminatedAt t

/-- `A.IsFirstTerminatingIndex k` unfolds to termination at `k` together with nontermination at
every earlier stage. -/
theorem isFirstTerminatingIndex_iff
    (A : LinearConjugateGradientMethod G b) (k : ℕ) :
    A.IsFirstTerminatingIndex k ↔
      A.terminatedAt k ∧ ∀ t : ℕ, t < k → ¬ A.terminatedAt t :=
  Iff.rfl

/-- At stage `0`, the recorded gradient is the residual `G x₀ + b`. -/
theorem gradient_zero_eq
    (A : LinearConjugateGradientMethod G b) :
    A.g 0 = Matrix.toEuclideanLin G A.x0 + b := by
  simpa [A.x_zero] using A.gradient_eq_residual 0

/-- The source-facing stationary-continuation field is the owner-level stationary-continuation
bridge for the underlying Fletcher-Reeves scheme. -/
theorem hasStationaryContinuation
    (A : LinearConjugateGradientMethod G b) :
    A.HasStationaryContinuation := by
  intro k hk
  simpa using A.stationaryContinuation k hk

/-- The recorded gradient/residual satisfies the affine quadratic update formula. -/
theorem residual_eq
    (A : LinearConjugateGradientMethod G b) {k : ℕ} (hk : A.g k ≠ 0) :
    A.g (k + 1) = A.g k + A.α k • Matrix.toEuclideanLin G (A.d k) := sorry

/-- Once a linear conjugate-gradient method has terminated, all later stages are also
terminating stages. -/
theorem terminatedAt_mono
    (A : LinearConjugateGradientMethod G b) {k t : ℕ}
    (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.terminatedAt t :=
  A.toConjugateGradientIterativeScheme.terminatedAt_mono A.hasStationaryContinuation hk hkt

/-- After termination, the recorded gradient/residual stays equal to `0` at every later stage. -/
theorem g_eq_zero_of_terminatedAt
    (A : LinearConjugateGradientMethod G b) {k t : ℕ}
    (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.toConjugateGradientIterativeScheme.g_eq_zero_of_terminatedAt
      A.hasStationaryContinuation hk hkt :=
  A.toConjugateGradientIterativeScheme.g_eq_zero_of_terminatedAt
    A.hasStationaryContinuation hk hkt

/-- After termination, all later search directions are the zero vector. -/
theorem d_eq_zero_of_terminatedAt
    (A : LinearConjugateGradientMethod G b) {k t : ℕ}
    (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.direction_eq_zero_of_terminated t <| A.g_eq_zero_of_terminatedAt hk hkt :=
  A.direction_eq_zero_of_terminated t <| A.g_eq_zero_of_terminatedAt hk hkt

/-- After termination, the iterate sequence stays constant. -/
theorem x_eq_of_terminatedAt
    (A : LinearConjugateGradientMethod G b) {k t : ℕ}
    (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.toConjugateGradientIterativeScheme.x_eq_of_terminatedAt
      A.hasStationaryContinuation hk hkt :=
  A.toConjugateGradientIterativeScheme.x_eq_of_terminatedAt
    A.hasStationaryContinuation hk hkt

/-- The span of the first `i + 1` residuals/gradients in a linear conjugate-gradient run. -/
def residualSubspace (A : LinearConjugateGradientMethod G b) (i : ℕ) : Submodule ℝ Point :=
  Submodule.span ℝ (Set.range (fun j : Fin (i + 1) ↦ A.g j))

/-- The span of the first `i + 1` search directions in a linear conjugate-gradient run. -/
def directionSubspace (A : LinearConjugateGradientMethod G b) (i : ℕ) : Submodule ℝ Point :=
  Submodule.span ℝ (Set.range (fun j : Fin (i + 1) ↦ A.d j))

/-- A nonterminal linear conjugate-gradient step carries exact line search on the whole line, a
nonzero search direction, well-defined quadratic quotients, and the textbook updates for the next
iterate, gradient/residual, and direction. -/
theorem nonterminalStep
    (A : LinearConjugateGradientMethod G b) {k : ℕ} (hk : A.g k ≠ 0) :
    IsMinOn (lineSearchObjective (quadraticObjective G b 0) (A.x k) (A.d k))
      Set.univ (A.α k) ∧
      A.d k ≠ 0 ∧
      dotProduct (A.d k) (Matrix.toEuclideanLin G (A.d k)) ≠ 0 ∧
      A.α k =
        dotProduct (A.g k) (A.g k) /
          dotProduct (A.d k) (Matrix.toEuclideanLin G (A.d k)) ∧
      A.x (k + 1) = A.x k + A.α k • A.d k ∧
      A.g (k + 1) = A.g k + A.α k • Matrix.toEuclideanLin G (A.d k) ∧
      dotProduct (A.g k) (A.g k) ≠ 0 ∧
      A.β k =
        dotProduct (A.g (k + 1)) (A.g (k + 1)) /
          dotProduct (A.g k) (A.g k) ∧
      A.d (k + 1) = -A.g (k + 1) + A.β k • A.d k := by
  refine ⟨A.exactLineSearchOnLine k hk, A.direction_ne_zero k hk, A.stepSize_denom_ne_zero k hk,
    A.stepSize_eq k hk, A.iterate_eq k hk, A.residual_eq hk, A.beta_denom_ne_zero k hk,
    A.beta_eq_dotProduct k hk, A.direction_eq_nonterminal k hk⟩

end LinearConjugateGradientMethod

/-- The `i`-th Krylov subspace generated by `g₀, G g₀, ..., G^i g₀`. -/
def conjugateGradientKrylovSubspace
    (G : Matrix (Fin n) (Fin n) ℝ) (g0 : Point) (i : ℕ) : Submodule ℝ Point :=
  Submodule.span ℝ (Set.range (fun j : Fin (i + 1) ↦ Matrix.toEuclideanLin (G ^ (j : ℕ)) g0))

/-- A positive-definite `n × n` real matrix has at most `n` distinct eigenvalues. -/
theorem posDefDistinctEigenvalueCount_le
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) :
    posDefDistinctEigenvalueCount hG ≤ n := sorry

/-- Chapter04 Theorem 4.2.1 (1): for a positive-definite quadratic function, the linear
conjugate-gradient recurrence terminates by the canonical bound
`m := posDefDistinctEigenvalueCount hG`, where `m` is the number of distinct eigenvalues of
`G`. -/
theorem linearConjugateGradient_terminatesBy_distinctEigenvalueCount
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point)
    (A : LinearConjugateGradientMethod G b) :
    ∃ k : ℕ, k ≤ posDefDistinctEigenvalueCount hG ∧ A.IsFirstTerminatingIndex k := sorry

/- Chapter04 Theorem 4.2.1 (2): the number `m` of distinct eigenvalues of the positive-definite
matrix `G` satisfies `m ≤ n`. This is already the canonical theorem
`posDefDistinctEigenvalueCount_le`. -/
#check posDefDistinctEigenvalueCount_le

/-- Chapter04 Theorem 4.2.1 (3): for each `i ≤ m := posDefDistinctEigenvalueCount hG`, the
search direction `d i` is `G`-conjugate to every earlier direction `d j`. -/
theorem linearConjugateGradient_direction_conjugate
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point)
    (A : LinearConjugateGradientMethod G b) {i j : ℕ}
    (hi : i ≤ posDefDistinctEigenvalueCount hG) (hj : j < i) :
    dotProduct (A.d i) (Matrix.toEuclideanLin G (A.d j)) = 0 := sorry

/-- Chapter04 Theorem 4.2.1 (4): for each `i ≤ m := posDefDistinctEigenvalueCount hG`, the
gradients/residuals `g i` are orthogonal to all earlier gradients/residuals `g j`. -/
theorem linearConjugateGradient_residual_orthogonal
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point)
    (A : LinearConjugateGradientMethod G b) {i j : ℕ}
    (hi : i ≤ posDefDistinctEigenvalueCount hG) (hj : j < i) :
    dotProduct (A.g i) (A.g j) = 0 := sorry

/-- Chapter04 Theorem 4.2.1 (5): for each `i ≤ m := posDefDistinctEigenvalueCount hG`, the
current search direction satisfies `d_iᵀ g_i = -g_iᵀ g_i`. -/
theorem linearConjugateGradient_direction_dot_residual
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point)
    (A : LinearConjugateGradientMethod G b) {i : ℕ}
    (hi : i ≤ posDefDistinctEigenvalueCount hG) :
    dotProduct (A.d i) (A.g i) = -dotProduct (A.g i) (A.g i) := sorry

/-- Chapter04 Theorem 4.2.1 (6): for each `i ≤ m := posDefDistinctEigenvalueCount hG`, the span
of `g 0, ..., g i` is the Krylov subspace generated by `g 0, G g 0, ..., G^i g 0`. -/
theorem linearConjugateGradient_residualSubspace_eq_krylovSubspace
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point)
    (A : LinearConjugateGradientMethod G b) {i : ℕ}
    (hi : i ≤ posDefDistinctEigenvalueCount hG) :
    A.residualSubspace i = conjugateGradientKrylovSubspace G (A.g 0) i := sorry

/-- Chapter04 Theorem 4.2.1 (7): for each `i ≤ m := posDefDistinctEigenvalueCount hG`, the span
of `d 0, ..., d i` is the same Krylov subspace `span {g 0, G g 0, ..., G^i g 0}`. -/
theorem linearConjugateGradient_directionSubspace_eq_krylovSubspace
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point)
    (A : LinearConjugateGradientMethod G b) {i : ℕ}
    (hi : i ≤ posDefDistinctEigenvalueCount hG) :
    A.directionSubspace i = conjugateGradientKrylovSubspace G (A.g 0) i := sorry

end
