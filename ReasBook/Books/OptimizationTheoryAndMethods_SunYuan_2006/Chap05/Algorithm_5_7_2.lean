/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_7_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this refine pass:
-- * primary domain: Euclidean L-BFGS method data on Chapter 5's real Hilbert-space model;
-- * sampled owners in this domain:
--   `lbfgsTwoLoopRecursion`,
--   `LBFGSHistoryEntry`,
--   `satisfiesCurvatureCondition`,
--   `HasGradientAt`;
-- * source-facing owner kept here: `LBFGSMethod`;
-- * core/canonical owners reused here: the Algorithm 5.7.1 two-loop-recursion surface, the
--   Chapter 5 curvature owner, and the Chapter 2 Wolfe-Powell parameter owner;
-- * primitive data here: iterate / gradient / direction / line-search / secant sequences, the
--   initial Euclidean matrix, the memory bound, and the L-BFGS-specific step laws;
-- * derived API here: secant-curvature positivity, symmetry of the initial matrix, gradient
--   equality, post-termination gradient stabilization, and the nonzero scaling denominator.

/-- The scaled identity matrix `((dotProduct s y) / ‖y‖ ^ 2) • 1` used as the initial matrix
`Hₖ⁽⁰⁾` in the L-BFGS two-loop recursion after the secant pair `(s, y)` has been formed. -/
def lbfgsScalingMatrix (s y : Point) : MatrixN :=
  ((dotProduct s y) / ‖y‖ ^ 2) • (1 : MatrixN)

/-- The ordered list of stored correction pairs used by the L-BFGS two-loop recursion at stage
`k`, keeping the last `min k m` pairs from oldest to newest. -/
def lbfgsHistoryWindow
    (s y : ℕ → Point) (m k : ℕ) : List (LBFGSHistoryEntry Point) :=
  let len := Nat.min k m
  let start := k - len
  (List.range len).map fun i ↦
    let j := start + i
    { s := s j, y := y j }

/-- The matrix supplied to the L-BFGS two-loop recursion: at the initial stage it is the given
matrix `H0`, and at stage `k + 1` it is the scaled identity built from `(s k, y k)`. -/
def lbfgsInitialMatrix (H0 : MatrixN) (s y : ℕ → Point) : ℕ → MatrixN
  | 0 => H0
  | k + 1 => lbfgsScalingMatrix (s k) (y k)

/-- Chapter05 Algorithm 5.7.2: an L-BFGS method on `ℝ^n` consists of a starting point `x₀`, an
initial symmetric positive-definite matrix `H₀`, a memory parameter `m`, a positive tolerance
`ε`, iterate/gradient/direction/step-size/secant data, Wolfe-Powell line-search parameters, and
the source-faithful step relations. At every nonterminal stage with `ε < ‖g k‖`, the search
direction is computed by the two-loop recursion from `Algorithm_5_7_1` using the last
`min k m` stored pairs, the step size satisfies the Wolfe rule, the iterate update is
`x (k + 1) = x k + α k • d k`, the new secant data are
`s k = x (k + 1) - x k` and `y k = g (k + 1) - g k`, and the secant pair satisfies the
canonical Chapter 5 curvature condition. The positivity of `dotProduct (s k) (y k)` and the
nonvanishing of `‖y k‖ ^ 2`, needed to read the scaled identity
`Hₖ⁽⁰⁾ = ((dotProduct (s k) (y k)) / ‖y k‖ ^ 2) • 1`, are derived API. The intrinsic owner from
`Algorithm_5_7_1` is operator-valued, and this Euclidean matrix model is fed into it through
`Matrix.toEuclideanLin`. After the stopping test `‖g k‖ ≤ ε` is reached, the source-facing run
stays at the same iterate; equality of the next recorded gradient is derived from the uniqueness
of gradients. -/
structure LBFGSMethod (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) where
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin n)
  H0 : Matrix (Fin n) (Fin n) ℝ
  m : ℕ
  x : ℕ → EuclideanSpace ℝ (Fin n)
  g : ℕ → EuclideanSpace ℝ (Fin n)
  d : ℕ → EuclideanSpace ℝ (Fin n)
  α : ℕ → ℝ
  s : ℕ → EuclideanSpace ℝ (Fin n)
  y : ℕ → EuclideanSpace ℝ (Fin n)
  rho : ℝ
  sigma : ℝ
  wolfeParameters : WolfePowellParameters rho sigma
  epsilon_pos : 0 < ε
  x_zero : x 0 = x0
  H0_posDef : H0.PosDef
  hasGradientAt : ∀ k : ℕ, HasGradientAt f (g k) (x k)
  direction_eq :
    ∀ k : ℕ, ε < ‖g k‖ →
      d k =
        -lbfgsTwoLoopRecursion
          (lbfgsInitialMatrix H0 s y k).toEuclideanLin
          (g k)
          (lbfgsHistoryWindow s y m k)
  stepSize_pos :
    ∀ k : ℕ, ε < ‖g k‖ → 0 < α k
  update :
    ∀ k : ℕ, ε < ‖g k‖ → x (k + 1) = x k + α k • d k
  armijo :
    ∀ k : ℕ, ε < ‖g k‖ →
      f (x k + α k • d k) ≤ f (x k) + rho * α k * inner ℝ (g k) (d k)
  curvature :
    ∀ k : ℕ, ε < ‖g k‖ →
      sigma * inner ℝ (g k) (d k) ≤ inner ℝ (g (k + 1)) (d k)
  stationaryContinuation :
    ∀ k : ℕ, ‖g k‖ ≤ ε → x (k + 1) = x k
  step_eq :
    ∀ k : ℕ, ε < ‖g k‖ → s k = x (k + 1) - x k
  gradientDifference_eq :
    ∀ k : ℕ, ε < ‖g k‖ → y k = g (k + 1) - g k
  curvatureCondition :
    ∀ k : ℕ, ε < ‖g k‖ → satisfiesCurvatureCondition (s k) (y k)

/-- An L-BFGS method can be used as its iterate sequence `x`. -/
instance : CoeFun (LBFGSMethod n f) (fun _ ↦ ℕ → EuclideanSpace ℝ (Fin n)) where
  coe A := A.x

/-- The stopping condition in the L-BFGS algorithm is `‖g k‖ ≤ ε`. -/
def LBFGSMethod.terminatedAt {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : LBFGSMethod n f) (k : ℕ) : Prop :=
  ‖A.g k‖ ≤ A.ε

/-- After the stopping test `‖g k‖ ≤ ε` is reached, the next iterate stays equal to the current
iterate. -/
theorem LBFGSMethod.x_eq_succ_of_terminatedAt {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : LBFGSMethod n f) {k : ℕ} (hk : A.terminatedAt k) :
    A.x (k + 1) = A.x k :=
  A.stationaryContinuation k hk

/-- After termination, the recorded gradient also stays equal at the next stage. This is derived
from iterate constancy and uniqueness of the gradient. -/
theorem LBFGSMethod.g_eq_succ_of_terminatedAt {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : LBFGSMethod n f) {k : ℕ} (hk : A.terminatedAt k) :
    A.g (k + 1) = A.g k := by
  have hx : A.x (k + 1) = A.x k := A.x_eq_succ_of_terminatedAt hk
  have hNext : HasGradientAt f (A.g (k + 1)) (A.x k) := by
    simpa [hx] using A.hasGradientAt (k + 1)
  exact hNext.unique (A.hasGradientAt k)

/-- The explicit gradient data in an L-BFGS method agrees with the canonical gradient of `f`
at every iterate. -/
theorem LBFGSMethod.gradient_eq {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : LBFGSMethod n f) (k : ℕ) :
    gradient f (A.x k) = A.g k := by
  simpa using (A.hasGradientAt k).gradient

/-- The initial matrix of an L-BFGS method is symmetric because it is positive definite. -/
theorem LBFGSMethod.H0_isSymm {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : LBFGSMethod n f) :
    A.H0.IsSymm := by
  simpa using A.H0_posDef.isHermitian

/-- The recorded secant pair at a nonterminal stage has positive curvature. -/
theorem LBFGSMethod.secant_curvature_pos {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : LBFGSMethod n f) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    0 < dotProduct (A.s k) (A.y k) := by
  exact satisfiesCurvatureCondition_iff_dotProduct_pos.mp (A.curvatureCondition k hNotStopped)

/-- The denominator in the L-BFGS scaling matrix is nonzero at every nonterminal stage. -/
theorem LBFGSMethod.scalingDenom_ne_zero {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : LBFGSMethod n f) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    ‖A.y k‖ ^ 2 ≠ 0 := by
  have hy_ne : A.y k ≠ 0 := by
    intro hy
    have hcurv := A.secant_curvature_pos hNotStopped
    simpa [hy] using hcurv.ne'
  exact pow_ne_zero 2 <| norm_ne_zero_iff.mpr hy_ne

/-- At every nonterminal stage, an L-BFGS method computes the direction by the concrete
two-loop recursion on the last `min k m` stored pairs, chooses a positive Wolfe step size,
updates the iterate, records the source secant data `s k` and `y k`, and has positive
curvature with `‖y k‖ ^ 2 ≠ 0` for the next scaled-identity matrix. -/
theorem LBFGSMethod.stepSpec {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : LBFGSMethod n f) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    A.d k =
        -lbfgsTwoLoopRecursion
          (lbfgsInitialMatrix A.H0 A.s A.y k).toEuclideanLin
          (A.g k)
          (lbfgsHistoryWindow A.s A.y A.m k) ∧
      0 < A.α k ∧
      A.x (k + 1) = A.x k + A.α k • A.d k ∧
      f (A.x k + A.α k • A.d k) ≤
        f (A.x k) + A.rho * A.α k * inner ℝ (A.g k) (A.d k) ∧
      A.sigma * inner ℝ (A.g k) (A.d k) ≤ inner ℝ (A.g (k + 1)) (A.d k) ∧
      A.s k = A.x (k + 1) - A.x k ∧
      A.y k = A.g (k + 1) - A.g k ∧
      0 < dotProduct (A.s k) (A.y k) ∧
      ‖A.y k‖ ^ 2 ≠ 0 := by
  exact ⟨A.direction_eq k hNotStopped, A.stepSize_pos k hNotStopped, A.update k hNotStopped,
    A.armijo k hNotStopped, A.curvature k hNotStopped, A.step_eq k hNotStopped,
    A.gradientDifference_eq k hNotStopped, A.secant_curvature_pos hNotStopped,
    A.scalingDenom_ne_zero hNotStopped⟩

end
