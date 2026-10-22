/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_1_extra_1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Matrix.Mul

noncomputable section

open scoped BigOperators

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "PenaltyWeights" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "∇" => @gradient ℝ Point _ _ _ _

-- Semantic recall and owner triage:
-- * core/canonical layer: `StandardPenaltyProblem` and `c⁽-⁾[problem]` are already owned by
--   Chapter 10's penalty-method API;
-- * source-facing layer: the watchdog merit function, its quadratic model, and the best-index /
--   sufficient-reduction predicates from Definition 12.5-extra-1;
-- * bridge layer: the companions below restate the watchdog formulas in the source's piecewise
--   form while reusing the earlier canonical constrained-problem owner.

namespace StandardPenaltyProblem

/-- The source penalty contribution of the `i`-th constraint in `P_σ(x)`: equality constraints
contribute `|cᵢ(x)|`, while inequality constraints contribute `|min (0, cᵢ(x))|`. -/
def watchdogPenaltyTerm
    (problem : StandardPenaltyProblem n m) (x : Point) (i : Fin m) : ℝ :=
  |c⁽-⁾[problem] x i|

/-- Unfolding `problem.watchdogPenaltyTerm x i` gives the source piecewise penalty term. -/
theorem watchdogPenaltyTerm_eq
    (problem : StandardPenaltyProblem n m) (x : Point) (i : Fin m) :
    problem.watchdogPenaltyTerm x i =
      if i.1 < problem.eqCount then
        |problem.constraint i x|
      else
        |min (0 : ℝ) (problem.constraint i x)| := by
  by_cases hi : i.1 < problem.eqCount
  · simp [watchdogPenaltyTerm, StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi]
  · simp [watchdogPenaltyTerm, StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi,
      min_comm]

/-- The affine constraint model at `xk` evaluated at `x`, namely
`cᵢ(xk) + (x - xk)ᵀ ∇ cᵢ(xk)`. -/
def watchdogLinearizedConstraintValue
    (problem : StandardPenaltyProblem n m) (xk x : Point) (i : Fin m) : ℝ :=
  problem.constraint i xk +
    dotProduct (x - xk) (∇ (problem.constraint i) xk)

/-- Unfolding `problem.watchdogLinearizedConstraintValue xk x i` gives the source affine
constraint model. -/
theorem watchdogLinearizedConstraintValue_eq
    (problem : StandardPenaltyProblem n m) (xk x : Point) (i : Fin m) :
    problem.watchdogLinearizedConstraintValue xk x i =
      problem.constraint i xk +
        dotProduct (x - xk) (∇ (problem.constraint i) xk) :=
  rfl

/-- The source penalty contribution of the linearized `i`-th constraint in `P_σ^(k)(x)`. -/
def watchdogModeledPenaltyTerm
    (problem : StandardPenaltyProblem n m) (xk x : Point) (i : Fin m) : ℝ :=
  if i.1 < problem.eqCount then
    |problem.watchdogLinearizedConstraintValue xk x i|
  else
    |min (0 : ℝ) (problem.watchdogLinearizedConstraintValue xk x i)|

/-- Unfolding `problem.watchdogModeledPenaltyTerm xk x i` gives the source piecewise penalty
term for the linearized model. -/
theorem watchdogModeledPenaltyTerm_eq
    (problem : StandardPenaltyProblem n m) (xk x : Point) (i : Fin m) :
    problem.watchdogModeledPenaltyTerm xk x i =
      if i.1 < problem.eqCount then
        |problem.watchdogLinearizedConstraintValue xk x i|
      else
        |min (0 : ℝ) (problem.watchdogLinearizedConstraintValue xk x i)| :=
  rfl

/-- Chapter12 Definition 12.5-extra-1 (1): the watchdog merit function
`P_σ(x) = f(x) + ∑ i ≤ m_e, σᵢ |cᵢ(x)| + ∑ i > m_e, σᵢ |min (0, cᵢ(x))|`. -/
def watchdogMeritFunction
    (problem : StandardPenaltyProblem n m) (σ : PenaltyWeights) : Point → ℝ :=
  fun x ↦ problem.objective x + ∑ i : Fin m, σ i * problem.watchdogPenaltyTerm x i

/-- The watchdog merit function of `problem` is written `P_[problem] σ`, so its value at `x` is
`P_[problem] σ x`. -/
scoped[StandardPenaltyProblem] notation:max "P_[" problem "]" σ =>
  watchdogMeritFunction problem σ

section

variable (problem : StandardPenaltyProblem n m)

/-- With `problem` fixed, the source watchdog merit function is written `P_σ`. -/
local notation:max "P_" σ => watchdogMeritFunction problem σ

/-- Evaluating `P_σ` gives the source formula `(12.5.3)`. -/
@[simp] theorem watchdogMeritFunction_apply
    (σ : PenaltyWeights) (x : Point) :
    (P_ σ) x =
      problem.objective x +
        ∑ i : Fin m, σ i * problem.watchdogPenaltyTerm x i :=
  rfl

/-- Chapter12 Definition 12.5-extra-1 (2): the watchdog approximate model `P_σ^(k)(x)` is the
quadratic model of `f` at `xk` plus the linearized constraint penalty terms at `xk`. -/
def watchdogMeritModel
    (problem : StandardPenaltyProblem n m)
    (σ : PenaltyWeights)
    (xk : Point)
    (Bk : MatrixN) : Point → ℝ :=
  fun x ↦
    problem.objective xk +
      dotProduct (x - xk) (∇ problem.objective xk) +
      (1 / 2 : ℝ) * dotProduct (x - xk) (Bk.mulVec (x - xk)) +
      ∑ i : Fin m, σ i * problem.watchdogModeledPenaltyTerm xk x i

/-- The watchdog merit model of `problem` at `(xk, Bk)` is written
`P_[problem] σ^(xk, Bk)`; with a fixed iterate/model pair this is locally abbreviated to the
source display `P_σ^(k)`. -/
scoped[StandardPenaltyProblem] notation:max "P_[" problem "]" σ "^(" xk ", " Bk ")" =>
  watchdogMeritModel problem σ xk Bk

open scoped StandardPenaltyProblem

section

variable (xk : Point) (Bk : MatrixN)

/-- With `problem`, `xk`, and `Bk` fixed, the source watchdog model is written `P_σ^(k)`. -/
local notation:max "P_" σ "^(k)" => watchdogMeritModel problem σ xk Bk

/-- Evaluating `P_σ^(k)` gives the source formula `(12.5.4)`. -/
@[simp] theorem watchdogMeritModel_apply
    (σ : PenaltyWeights) (x : Point) :
    (P_ σ^(k)) x =
      problem.objective xk +
        dotProduct (x - xk) (∇ problem.objective xk) +
        (1 / 2 : ℝ) * dotProduct (x - xk) (Bk.mulVec (x - xk)) +
        ∑ i : Fin m, σ i * problem.watchdogModeledPenaltyTerm xk x i :=
  rfl

end

end

/-- Chapter12 Definition 12.5-extra-1 (3): `problem.IsWatchdogBestPointIndex σ iterate l k`
means that `l` lies between `1` and `k` and realizes the minimum of `P_σ(x_i)` among the
indices `1 ≤ i ≤ k`, matching `(12.5.5)`. -/
class IsWatchdogBestPointIndex
    (problem : StandardPenaltyProblem n m)
    (σ : PenaltyWeights)
    (iterate : ℕ → Point)
    (l k : ℕ) : Prop where
  le_index : l ≤ k
  one_le_index : 1 ≤ l
  minimal :
    ∀ i : ℕ, 1 ≤ i → i ≤ k →
      (P_[problem] σ) (iterate l) ≤
        (P_[problem] σ) (iterate i)

/-- `problem.IsWatchdogBestPointIndex σ iterate l k` is a proposition, so its witnesses are
subsingleton. -/
instance isWatchdogBestPointIndexSubsingleton
    (problem : StandardPenaltyProblem n m)
    (σ : PenaltyWeights)
    (iterate : ℕ → Point)
    (l k : ℕ) :
    Subsingleton (StandardPenaltyProblem.IsWatchdogBestPointIndex problem σ iterate l k) :=
  inferInstance

/-- Unfolding `problem.IsWatchdogBestPointIndex σ iterate l k` gives the source minimizer
condition `(12.5.5)`. -/
theorem isWatchdogBestPointIndex_iff
    (problem : StandardPenaltyProblem n m)
    (σ : PenaltyWeights)
    (iterate : ℕ → Point)
    (l k : ℕ) :
    StandardPenaltyProblem.IsWatchdogBestPointIndex problem σ iterate l k ↔
      l ≤ k ∧
        1 ≤ l ∧
          ∀ i : ℕ, 1 ≤ i → i ≤ k →
            (P_[problem] σ) (iterate l) ≤
              (P_[problem] σ) (iterate i) := by
  constructor
  · intro h
    exact ⟨h.le_index, h.one_le_index, h.minimal⟩
  · rintro ⟨hle, hone, hminimal⟩
    exact ⟨hle, hone, hminimal⟩

/-- The raw watchdog sufficient-reduction inequality `(12.5.6)` comparing `x_(k + 1)` to `x_l`.
-/
def watchdogSufficientReductionIneq
    (problem : StandardPenaltyProblem n m)
    (σ : PenaltyWeights)
    (β : ℝ)
    (iterate : ℕ → Point)
    (hessianApprox : ℕ → MatrixN)
    (l k : ℕ) : Prop :=
  (P_[problem] σ) (iterate (k + 1)) ≤
    (P_[problem] σ) (iterate l) -
      β *
        ((P_[problem] σ) (iterate l) -
          (P_[problem] σ^(iterate l, hessianApprox l)) (iterate (l + 1)))

/-- Unfolding `problem.watchdogSufficientReductionIneq σ β iterate hessianApprox l k` gives the
source inequality `(12.5.6)`. -/
theorem watchdogSufficientReductionIneq_iff
    (problem : StandardPenaltyProblem n m)
    (σ : PenaltyWeights)
    (β : ℝ)
    (iterate : ℕ → Point)
    (hessianApprox : ℕ → MatrixN)
    (l k : ℕ) :
    StandardPenaltyProblem.watchdogSufficientReductionIneq
        problem σ β iterate hessianApprox l k ↔
      (P_[problem] σ) (iterate (k + 1)) ≤
        (P_[problem] σ) (iterate l) -
          β *
            ((P_[problem] σ) (iterate l) -
              (P_[problem] σ^(iterate l, hessianApprox l)) (iterate (l + 1))) :=
  Iff.rfl

/-- Chapter12 Definition 12.5-extra-1 (4): `x_(k + 1)` yields a sufficient watchdog reduction
when `β ∈ (0, 1 / 2)`, `l` is the best-point index up to iteration `k`, and the source
inequality `(12.5.6)` holds. -/
class IsWatchdogSufficientReduction
    (problem : StandardPenaltyProblem n m)
    (σ : PenaltyWeights)
    (β : ℝ)
    (iterate : ℕ → Point)
    (hessianApprox : ℕ → MatrixN) (l k : ℕ) : Prop where
  beta_mem : β ∈ Set.Ioo (0 : ℝ) ((1 / 2 : ℝ))
  bestPointIndex : StandardPenaltyProblem.IsWatchdogBestPointIndex problem σ iterate l k
  inequality :
    StandardPenaltyProblem.watchdogSufficientReductionIneq
      problem σ β iterate hessianApprox l k

/-- `problem.IsWatchdogSufficientReduction σ β iterate hessianApprox l k` is a proposition, so its
witnesses are subsingleton. -/
instance isWatchdogSufficientReductionSubsingleton
    (problem : StandardPenaltyProblem n m)
    (σ : PenaltyWeights)
    (β : ℝ)
    (iterate : ℕ → Point)
    (hessianApprox : ℕ → MatrixN)
    (l k : ℕ)
    : Subsingleton
        (StandardPenaltyProblem.IsWatchdogSufficientReduction
          problem σ β iterate hessianApprox l k) :=
  inferInstance

/-- Unfolding `problem.IsWatchdogSufficientReduction σ β iterate hessianApprox l k` gives the
source-facing sufficient-reduction condition with its standing hypotheses. -/
theorem isWatchdogSufficientReduction_iff
    (problem : StandardPenaltyProblem n m)
    (σ : PenaltyWeights)
    (β : ℝ)
    (iterate : ℕ → Point)
    (hessianApprox : ℕ → MatrixN)
    (l k : ℕ) :
    StandardPenaltyProblem.IsWatchdogSufficientReduction
        problem σ β iterate hessianApprox l k ↔
      β ∈ Set.Ioo (0 : ℝ) ((1 / 2 : ℝ)) ∧
        StandardPenaltyProblem.IsWatchdogBestPointIndex problem σ iterate l k ∧
          (P_[problem] σ) (iterate (k + 1)) ≤
            (P_[problem] σ) (iterate l) -
              β *
                ((P_[problem] σ) (iterate l) -
                  (P_[problem] σ^(iterate l, hessianApprox l)) (iterate (l + 1))) := by
  constructor
  · intro h
    exact ⟨h.beta_mem, h.bestPointIndex, h.inequality⟩
  · rintro ⟨hβ, hl, hineq⟩
    exact ⟨hβ, hl, hineq⟩

#print axioms StandardPenaltyProblem.watchdogPenaltyTerm
#print axioms StandardPenaltyProblem.watchdogLinearizedConstraintValue
#print axioms StandardPenaltyProblem.watchdogModeledPenaltyTerm
#print axioms StandardPenaltyProblem.watchdogMeritFunction
#print axioms StandardPenaltyProblem.watchdogMeritModel

end StandardPenaltyProblem

end
