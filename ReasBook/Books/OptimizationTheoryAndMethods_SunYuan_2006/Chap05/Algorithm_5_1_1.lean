/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_1
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

-- Domain sampling for this item:
-- * primary domain: quasi-Newton runs on real inner-product spaces;
-- * sampled declarations in the owner family:
--   `satisfiesQuasiNewtonEquation`,
--   `satisfiesQuasiNewtonEquation_toEuclideanLin_iff`,
--   `Matrix.toEuclideanLin`,
--   `HasGradientAt`;
-- * core/canonical owner: the coordinate-free quasi-Newton run data on a real Hilbert space,
--   with the inverse-form secant equation on endomorphisms as the stagewise owner relation;
-- * bridge/view: the concrete Euclidean matrix model through `Matrix.toEuclideanLin`;
-- * primitive data here: iterate, gradient, direction, step-size, and endomorphism sequences
--   together with their nonterminal update laws;
-- * derived API here: the initial-stage views `x0`, `H0`, and the matrix-model restatement of
--   the intrinsic secant equation, together with the Hessian-side matrix view
--   `A.hessian k := (A.matrix k)⁻¹`.

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Chapter05 Algorithm 5.1.1: a general quasi-Newton method consists of a nonnegative
tolerance `ε`, iterates `x k`, inverse-approximation operators `H k`, explicit gradient data
`g k`, search directions `d k`, and step sizes
`α k`. At every nonterminal stage with `ε < ‖g k‖`, the direction is given by
`d k = -H k (g k)`, the line search returns a positive step size `α k > 0`, the
iterate update is `x (k + 1) = x k + α k • d k`, and the next matrix satisfies the
inverse-form quasi-Newton equation for `H (k + 1)` and secant data `g (k + 1) - g k`,
`x (k + 1) - x k`. On the Euclidean model `E = EuclideanSpace ℝ (Fin n)`, the canonical bridge
`A.matrix k := Matrix.toEuclideanLin.symm (A.H k)` recovers the concrete textbook matrices, so
the matrix-vector equations remain available as thin downstream specializations. The source does
not fix a particular line-search rule, so the public surface records its explicit positivity
output. Once the stopping condition `‖g k‖ ≤ ε` is reached, the run stays at the same iterate;
this frozen-tail convention is primitive run data on the canonical owner rather than a
theorem-local extra hypothesis. -/
structure GeneralQuasiNewtonMethod (f : E → ℝ) where
  ε : ℝ
  x : ℕ → E
  H : ℕ → E →ₗ[ℝ] E
  g : ℕ → E
  d : ℕ → E
  α : ℕ → ℝ
  epsilon_nonneg : 0 ≤ ε
  hasGradientAt (k : ℕ) : HasGradientAt f (g k) (x k)
  direction_eq (k : ℕ) (hNotStopped : ε < ‖g k‖) :
    d k = -(H k (g k))
  stepSize_pos (k : ℕ) (hNotStopped : ε < ‖g k‖) : 0 < α k
  update (k : ℕ) (hNotStopped : ε < ‖g k‖) :
    x (k + 1) = x k + α k • d k
  stationaryContinuation (k : ℕ) (hTerminated : ‖g k‖ ≤ ε) :
    x (k + 1) = x k
  quasiNewtonEquation (k : ℕ) (hNotStopped : ε < ‖g k‖) :
    satisfiesQuasiNewtonEquation (H (k + 1)) (g (k + 1) - g k) (x (k + 1) - x k)

/-- The realized step displacement at stage `k` of a sequence `x`. In quasi-Newton files this
is used for the canonical stagewise displacement `x (k + 1) - x k`. -/
abbrev broydenStep (x : ℕ → E) (k : ℕ) : E :=
  x (k + 1) - x k

/-- The realized secant vector at stage `k` of a sequence `g`, used for the canonical gradient
difference `g (k + 1) - g k` in quasi-Newton updates. -/
abbrev broydenSecant (g : ℕ → E) (k : ℕ) : E :=
  g (k + 1) - g k

namespace GeneralQuasiNewtonMethod

/-- A general quasi-Newton method can be used as its iterate sequence `x`. -/
instance {f : E → ℝ} : CoeFun (GeneralQuasiNewtonMethod f) (fun _ ↦ ℕ → E) where
  coe A := A.x

/-- Evaluating a general quasi-Newton method as a function returns its iterate sequence. -/
theorem coe_apply {f : E → ℝ} (A : GeneralQuasiNewtonMethod f) (k : ℕ) : A k = A.x k := rfl

/-- The initial iterate of a quasi-Newton run. -/
abbrev x0 {f : E → ℝ} (A : GeneralQuasiNewtonMethod f) : E :=
  A 0

/-- The initial inverse-approximation operator of a quasi-Newton run. -/
abbrev H0 {f : E → ℝ} (A : GeneralQuasiNewtonMethod f) : E →ₗ[ℝ] E :=
  A.H 0

/-- The stopping condition in the general quasi-Newton algorithm is `‖g k‖ ≤ ε`. -/
def terminatedAt {f : E → ℝ} (A : GeneralQuasiNewtonMethod f) (k : ℕ) : Prop :=
  ‖A.g k‖ ≤ A.ε

/-- A quasi-Newton run is generated through stage `k` when every earlier stage `i < k` is
nonterminal, so all stagewise update data are available through stage `k - 1`. -/
def GeneratedThrough {f : E → ℝ} (A : GeneralQuasiNewtonMethod f) (k : ℕ) : Prop :=
  ∀ i : ℕ, i < k → A.ε < ‖A.g i‖

/-- Unfolding `GeneratedThrough A k` says exactly that every earlier stage `i < k` is
nonterminal. -/
theorem generatedThrough_iff {f : E → ℝ} {A : GeneralQuasiNewtonMethod f} {k : ℕ} :
    A.GeneratedThrough k ↔ ∀ i : ℕ, i < k → A.ε < ‖A.g i‖ :=
  Iff.rfl

/-- The explicit gradient data in a general quasi-Newton method agrees with the canonical
gradient of `f` at every iterate. -/
theorem gradient_eq {f : E → ℝ} (A : GeneralQuasiNewtonMethod f) (k : ℕ) :
    gradient f (A k) = A.g k := by
  simpa using (A.hasGradientAt k).gradient

/-- After the stopping test `‖g k‖ ≤ ε` is reached, the next iterate stays fixed. -/
theorem x_eq_succ_of_terminatedAt
    {f : E → ℝ} (A : GeneralQuasiNewtonMethod f) {k : ℕ}
    (hk : A.terminatedAt k) :
    A (k + 1) = A k :=
  A.stationaryContinuation k hk

/-- After termination, the next recorded gradient agrees with the current one. -/
theorem g_eq_succ_of_terminatedAt
    {f : E → ℝ} (A : GeneralQuasiNewtonMethod f) {k : ℕ}
    (hk : A.terminatedAt k) :
    A.g (k + 1) = A.g k := by
  have hx : A (k + 1) = A k := A.x_eq_succ_of_terminatedAt hk
  have hNext : HasGradientAt f (A.g (k + 1)) (A k) := by
    simpa [hx] using A.hasGradientAt (k + 1)
  exact hNext.unique (A.hasGradientAt k)

/-- Once a quasi-Newton run terminates, every later stage is also terminating. -/
theorem terminatedAt_mono
    {f : E → ℝ} (A : GeneralQuasiNewtonMethod f)
    {k t : ℕ} (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.terminatedAt t := by
  induction hkt with
  | refl =>
      exact hk
  | @step t hkt iht =>
      have hgt : A.g (t + 1) = A.g t := A.g_eq_succ_of_terminatedAt iht
      simpa [GeneralQuasiNewtonMethod.terminatedAt, hgt] using iht

/-- After termination, every later iterate stays equal to the terminating iterate. -/
theorem x_eq_of_terminatedAt
    {f : E → ℝ} (A : GeneralQuasiNewtonMethod f)
    {k t : ℕ} (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A t = A k := by
  induction hkt with
  | refl =>
      rfl
  | @step t hkt iht =>
      have ht : A.terminatedAt t := A.terminatedAt_mono hk hkt
      calc
        A (t + 1) = A t := A.x_eq_succ_of_terminatedAt ht
        _ = A k := iht

/-- After termination, every later recorded gradient stays equal to the terminating gradient. -/
theorem g_eq_of_terminatedAt
    {f : E → ℝ} (A : GeneralQuasiNewtonMethod f)
    {k t : ℕ} (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.g t = A.g k := by
  induction hkt with
  | refl =>
      rfl
  | @step t hkt iht =>
      have ht : A.terminatedAt t := A.terminatedAt_mono hk hkt
      calc
        A.g (t + 1) = A.g t := A.g_eq_succ_of_terminatedAt ht
        _ = A.g k := iht

/-- At every nonterminal stage, a general quasi-Newton method uses the inverse-Hessian-type
secant equation in its canonical operator-valued form. -/
theorem quasiNewtonEquation_apply
    {f : E → ℝ} (A : GeneralQuasiNewtonMethod f) {k : ℕ}
    (hNotStopped : A.ε < ‖A.g k‖) :
    A.H (k + 1) (A.g (k + 1) - A.g k) = A (k + 1) - A k :=
  A.quasiNewtonEquation k hNotStopped

/-- At every nonterminal stage, a general quasi-Newton method uses the inverse-Hessian-type
direction `-H k (g k)`, chooses a positive step size, updates the iterate by
`x (k + 1) = x k + α k • d k`, and enforces the canonical inverse secant equation; the
concrete matrix model is recovered separately by `A.matrix`. -/
theorem stepSpec {f : E → ℝ} (A : GeneralQuasiNewtonMethod f) {k : ℕ}
    (hNotStopped : A.ε < ‖A.g k‖) :
    A.d k = -(A.H k (A.g k)) ∧
      0 < A.α k ∧
      A (k + 1) = A k + A.α k • A.d k ∧
      satisfiesQuasiNewtonEquation (A.H (k + 1)) (A.g (k + 1) - A.g k) (A (k + 1) - A k) := by
  exact ⟨A.direction_eq k hNotStopped, A.stepSize_pos k hNotStopped, A.update k hNotStopped,
    A.quasiNewtonEquation k hNotStopped⟩

/-- A quasi-Newton run has exact line search on the nonnegative ray when each recorded step
size `A.α k` is a Chapter 2 exact line-search step for the one-dimensional profile
`a ↦ f (A k + a • A.d k)` on `Set.Ici 0`. -/
class HasExactLineSearchOnNonnegativeRay
    {f : E → ℝ} (A : GeneralQuasiNewtonMethod f) : Prop where
  exactLineSearch :
    ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (A k) (A.d k) (A.α k)

/-- Every stage of a quasi-Newton run with exact line search minimizes the line-search objective
`lineSearchObjective f (A k) (A.d k)` on the nonnegative ray `Set.Ici 0`. -/
theorem HasExactLineSearchOnNonnegativeRay.isMinOn
    {f : E → ℝ} {A : GeneralQuasiNewtonMethod f}
    (hA : A.HasExactLineSearchOnNonnegativeRay) (k : ℕ) :
    IsMinOn (fun a : ℝ ↦ f (A k + a • A.d k)) (Set.Ici 0) (A.α k) := by
  change IsMinOn (lineSearchObjective f (A k) (A.d k)) (Set.Ici 0) (A.α k)
  exact (hA.exactLineSearch k).isMinOn

end GeneralQuasiNewtonMethod

end

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

namespace GeneralQuasiNewtonMethod

/-- The Euclidean matrix-model representative of the inverse approximation `H k`. -/
abbrev matrix {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f) (k : ℕ) : MatrixN :=
  Matrix.toEuclideanLin.symm (A.H k)

/-- The Euclidean matrix-model representative of the initial inverse approximation `H₀`. -/
abbrev matrix0 {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f) : MatrixN :=
  A.matrix 0

/-- The Hessian-side matrix view `Bₖ = Hₖ⁻¹` of a Euclidean quasi-Newton run. This remains a
thin source-facing bridge on top of the owner-level inverse approximation `A.matrix k`. -/
abbrev hessian {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f) (k : ℕ) : MatrixN :=
  (A.matrix k)⁻¹

/-- Passing `A.matrix k` through `Matrix.toEuclideanLin` recovers the intrinsic operator
`A.H k`. -/
@[simp] theorem matrix_toEuclideanLin
    {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f) (k : ℕ) :
    (A.matrix k).toEuclideanLin = A.H k := by
  simp [GeneralQuasiNewtonMethod.matrix]

/-- Passing `A.matrix0` through `Matrix.toEuclideanLin` recovers the intrinsic initial operator
`A.H0`. -/
@[simp] theorem matrix0_toEuclideanLin
    {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f) :
    A.matrix0.toEuclideanLin = A.H0 := by
  simp [GeneralQuasiNewtonMethod.matrix0, GeneralQuasiNewtonMethod.H0]

/-- The bridge from the intrinsic owner to the Euclidean matrix model preserves the initial
stage. -/
@[simp] theorem matrix_zero
    {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f) :
    A.matrix 0 = A.matrix0 := rfl

/-- On the Euclidean matrix model, the search direction is the textbook vector
`-(A.matrix k).mulVec (A.g k)`. -/
theorem direction_eq_matrix
    {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f) {k : ℕ}
    (hNotStopped : A.ε < ‖A.g k‖) :
    A.d k = -(A.matrix k).toEuclideanLin (A.g k) := by
  simpa [GeneralQuasiNewtonMethod.matrix] using A.direction_eq k hNotStopped

/-- The canonical secant owner can be restated on the Euclidean matrix model through
`Matrix.toEuclideanLin`. -/
theorem quasiNewtonEquation_matrix
    {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f) {k : ℕ}
    (hNotStopped : A.ε < ‖A.g k‖) :
    satisfiesQuasiNewtonEquation
      (A.matrix (k + 1)).toEuclideanLin
      (A.g (k + 1) - A.g k)
      (A (k + 1) - A k) := by
  simpa [GeneralQuasiNewtonMethod.matrix] using A.quasiNewtonEquation k hNotStopped

/-- The canonical secant owner for a quasi-Newton run is exactly the concrete matrix-model
equation on `mulVec`. -/
theorem quasiNewtonEquation_mulVec
    {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f) {k : ℕ}
    (hNotStopped : A.ε < ‖A.g k‖) :
    (A.matrix (k + 1)).mulVec (A.g (k + 1) - A.g k).ofLp = (A (k + 1) - A k).ofLp :=
  satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mp (A.quasiNewtonEquation_matrix hNotStopped)

end GeneralQuasiNewtonMethod
end
