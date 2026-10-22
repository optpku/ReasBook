/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Lemma_12_2_1
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Extr

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "Jacobian" => Matrix (Fin n) (Fin m) ℝ

-- Semantic recall:
-- * Chapter 12 already owns the affine linearized constraint map `linearizedConstraintValue`
--   together with its evaluation lemma `linearizedConstraintValue_apply`;
-- * the recurring source operation in this file is the coordinatewise negative part `v⁻` on
--   `ConstraintPoint`, exposed through mathlib's canonical `NegPart` notation rather than a
--   duplicate wrapper name;
-- * `IsMinOn` is the canonical minimizer predicate for the one-dimensional Cauchy-step problem;
-- * nearby Chapter 13 files model the trust-region geometry on `EuclideanSpace`, so this file
--   keeps the source-facing `CauchyStep` owner while reusing the existing affine residual API.

/-- The Euclidean constraint space carries the source coordinatewise negative-part operation
`v ↦ v⁻`. -/
instance instNegPartConstraintPoint : NegPart ConstraintPoint where
  negPart v := WithLp.toLp 2 fun i ↦ (v i)⁻

/-- Evaluating `v⁻` gives the coordinatewise negative part. -/
@[simp] theorem constraintPoint_negPart_apply
    (v : ConstraintPoint) (i : Fin m) :
    (v⁻) i = (v i)⁻ :=
  rfl

/-- Evaluating `(linearizedConstraintValue c A d)⁻` gives the negative part of each source
linearized constraint component. -/
@[simp] theorem linearizedConstraintValue_negPart_apply
    (c : ConstraintPoint) (A : Jacobian) (d : Point) (i : Fin m) :
    ((linearizedConstraintValue c A d)⁻) i =
      (linearizedConstraintValue c A d i)⁻ :=
  rfl

/-- The source negative-gradient direction `d̄ = -A c⁻` at `d = 0` for the function
`d ↦ ‖(c + Aᵀ d)⁻‖^2`. -/
def cauchyDirection
    (c : ConstraintPoint) (A : Jacobian) : Point :=
  -Matrix.toEuclideanLin A c⁻

/-- Unfolding `cauchyDirection c A` gives the source formula `-A c⁻`. -/
theorem cauchyDirection_eq
    (c : ConstraintPoint) (A : Jacobian) :
    cauchyDirection c A = -Matrix.toEuclideanLin A c⁻ :=
  rfl

/-- The one-dimensional Cauchy-step objective
`α ↦ ‖(c + Aᵀ (α d̄))⁻‖^2` along the source ray `d̄ = cauchyDirection c A`. -/
def cauchyRayObjective
    (c : ConstraintPoint) (A : Jacobian) (α : ℝ) : ℝ :=
  ‖(linearizedConstraintValue c A (α • cauchyDirection c A))⁻‖ ^ (2 : ℕ)

/-- Expanding `cauchyRayObjective c A α` gives the source formula
`‖(c + Aᵀ (α d̄))⁻‖^2`. -/
theorem cauchyRayObjective_eq
    (c : ConstraintPoint) (A : Jacobian) (α : ℝ) :
    cauchyRayObjective c A α =
      ‖(linearizedConstraintValue c A (α • cauchyDirection c A))⁻‖ ^ (2 : ℕ) :=
  rfl

/-- The feasible Cauchy-step scales are the positive ray parameters `α` whose step
`α • cauchyDirection c A` lies in the closed trust region `‖d‖ ≤ Δ`. -/
def cauchyScaleSet
    (Δ : ℝ) (c : ConstraintPoint) (A : Jacobian) : Set ℝ :=
  {α | 0 < α ∧ ‖α • cauchyDirection c A‖ ≤ Δ}

/-- Membership in `cauchyScaleSet Δ c A` is exactly the source conditions
`α > 0` and `‖α d̄‖ ≤ Δ`. -/
theorem mem_cauchyScaleSet_iff
    (Δ : ℝ) (c : ConstraintPoint) (A : Jacobian) (α : ℝ) :
    α ∈ cauchyScaleSet Δ c A ↔ 0 < α ∧ ‖α • cauchyDirection c A‖ ≤ Δ :=
  Iff.rfl

/-- Chapter13 Definition 13.3-extra-2: a Cauchy step for the linearized-constraint trust-region
subproblem is determined by a chosen scale `alpha = ᾱ_k > 0` that minimizes
`cauchyRayObjective c A` on `cauchyScaleSet Δ c A`; the associated step is
`alpha • cauchyDirection c A = ᾱ_k d̄_k`. -/
structure CauchyStep
    (Δ : ℝ) (c : ConstraintPoint) (A : Jacobian) where
  /-- The source Cauchy-step scale `ᾱ_k`. -/
  alpha : ℝ
  /-- The source condition `ᾱ_k > 0`. -/
  alpha_pos : 0 < alpha
  /-- The source trust-region bound `‖ᾱ_k d̄_k‖ ≤ Δ_k`. -/
  norm_le : ‖alpha • cauchyDirection c A‖ ≤ Δ
  /-- `ᾱ_k` minimizes the source one-dimensional problem on the feasible Cauchy ray. -/
  isMinOn :
    IsMinOn (cauchyRayObjective c A) (cauchyScaleSet Δ c A) alpha

namespace CauchyStep

/-- The step vector `d_k^CP = ᾱ_k d̄_k` determined by a chosen Cauchy scale. -/
def point
    {Δ : ℝ} {c : ConstraintPoint} {A : Jacobian}
    (s : CauchyStep Δ c A) : Point :=
  s.alpha • cauchyDirection c A

/-- A `CauchyStep` coerces to its step vector `d_k^CP`. -/
instance instCoePoint
    {Δ : ℝ} {c : ConstraintPoint} {A : Jacobian} :
    CoeOut (CauchyStep Δ c A) Point where
  coe s := s.point

/-- Expanding `s.point` gives the source formula `ᾱ_k d̄_k`. -/
theorem point_eq
    {Δ : ℝ} {c : ConstraintPoint} {A : Jacobian}
    (s : CauchyStep Δ c A) :
    s.point = s.alpha • cauchyDirection c A :=
  rfl

/-- The chosen Cauchy scale belongs to the feasible scale set of the one-dimensional problem. -/
theorem alpha_mem_cauchyScaleSet
    {Δ : ℝ} {c : ConstraintPoint} {A : Jacobian}
    (s : CauchyStep Δ c A) :
    s.alpha ∈ cauchyScaleSet Δ c A :=
  ⟨s.alpha_pos, s.norm_le⟩

/-- The chosen Cauchy step stays in the closed trust region `‖d‖ ≤ Δ`. -/
theorem norm_point_le
    {Δ : ℝ} {c : ConstraintPoint} {A : Jacobian}
    (s : CauchyStep Δ c A) :
    ‖s.point‖ ≤ Δ := by
  simpa [point_eq] using s.norm_le

end CauchyStep

#print axioms linearizedConstraintValue
#print axioms instNegPartConstraintPoint
#print axioms cauchyDirection
#print axioms cauchyRayObjective
#print axioms cauchyScaleSet
#print axioms CauchyStep.point

end
