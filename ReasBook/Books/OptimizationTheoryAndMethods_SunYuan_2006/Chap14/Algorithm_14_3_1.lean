/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.InnerProductSpace.Dual
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_6

noncomputable section

universe u

section

variable {E : Type u}

/-- The solution set `S*` of `f`, written `S⋆[f]`, is the set of global minimizers of `f` on
the ambient space. -/
def sunYuanOptimalSolutionSet (f : E → ℝ) : Set E :=
  {x | IsMinOn f Set.univ x}

notation:max "S⋆[" f "]" => sunYuanOptimalSolutionSet f

/-- Membership in `S⋆[f]` is exactly the global-minimizer condition for `f`. -/
@[simp] theorem mem_sunYuanOptimalSolutionSet_iff
    (f : E → ℝ) (x : E) :
    x ∈ S⋆[f] ↔ IsMinOn f Set.univ x :=
  Iff.rfl

/-- The optimal value `f*` of `f`, written `f⋆[f]`, is the infimum of its values on the ambient
space. -/
noncomputable def optimalValue (f : E → ℝ) : ℝ :=
  sInf (Set.range f)

notation:max "f⋆[" f "]" => optimalValue f

/-- Unfolding `f⋆[f]` gives the infimum of the range of `f`. -/
@[simp] theorem optimalValue_eq_sInf_range
    (f : E → ℝ) :
    f⋆[f] = sInf (Set.range f) :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "DualSpace" => StrongDual ℝ E

-- Layer triage:
-- * source-facing: `sunYuanOptimalSolutionSet`, `optimalValue`, `SubgradientMethod`
-- * core/canonical: the Chapter 14 convex subdifferential owner `subdifferential`
--   from `Lemma_14_1_6`
-- * bridge/view: `normalizedSubgradientDirection` and `SubgradientMethod.directionAt`

open scoped Subgradient

variable [CompleteSpace E]

/-- The normalized negative subgradient direction `-g / ‖g‖` used in Step 3 of the subgradient
method, obtained from the canonical dual subgradient via the Fréchet-Riesz map. -/
def normalizedSubgradientDirection (ξ : DualSpace) : E :=
  (-((‖ξ‖ : ℝ)⁻¹)) • (InnerProductSpace.toDual ℝ E).symm ξ

/-- Unfolding `normalizedSubgradientDirection ξ` gives the normalized negative Riesz
representative of `ξ`. -/
theorem normalizedSubgradientDirection_eq (ξ : DualSpace) :
    normalizedSubgradientDirection ξ =
      (-((‖ξ‖ : ℝ)⁻¹)) • (InnerProductSpace.toDual ℝ E).symm ξ :=
  rfl

/-- Chapter14 Algorithm 14.3.1: the subgradient method for `f : E → ℝ` starts from an initial
point `x₁`, and for each stage `k ≥ 1` records the iterate `x_k`, a chosen dual subgradient
`g_k ∈ ∂ f(x_k)`, and a positive stepsize `α_k`. Step 3 uses the Riesz representative
`(InnerProductSpace.toDual ℝ E).symm g_k`, so the update is
`x_(k + 1) = x_k + α_k • normalizedSubgradientDirection g_k`, i.e.
`x_(k + 1) = x_k - (α_k / ‖g_k‖) • (InnerProductSpace.toDual ℝ E).symm g_k`. -/
structure SubgradientMethod (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  objective : E → ℝ
  initialPoint : E
  iterate : ℕ → E
  subgradient : ℕ → StrongDual ℝ E
  stepSize : ℕ → ℝ
  iterate_one : iterate 1 = initialPoint
  subgradient_mem (k : ℕ) (_ : 1 ≤ k) :
    subgradient k ∈ ∂ objective (iterate k)
  subgradient_norm_pos (k : ℕ) (_ : 1 ≤ k) :
    0 < ‖subgradient k‖
  stepSize_pos (k : ℕ) (_ : 1 ≤ k) :
    0 < stepSize k
  iterate_succ (k : ℕ) (_ : 1 ≤ k) :
    iterate (k + 1) =
      iterate k + stepSize k • normalizedSubgradientDirection (subgradient k)

namespace SubgradientMethod

/-- A subgradient method can be evaluated at stage `k` as its iterate `x_k`. -/
instance : CoeFun (_root_.SubgradientMethod E) (fun _ ↦ ℕ → E) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply (method : _root_.SubgradientMethod E) (k : ℕ) :
    method k = method.iterate k :=
  rfl

/-- The Step-2 objective value `f(x_k)` attached to the current iterate. -/
def objectiveValueAt (method : SubgradientMethod E) (k : ℕ) : ℝ :=
  method.objective (method.iterate k)

/-- Unfolding `method.objectiveValueAt k` gives the source objective value `f(x_k)`. -/
@[simp] theorem objectiveValueAt_eq
    (method : SubgradientMethod E) (k : ℕ) :
    method.objectiveValueAt k = method.objective (method.iterate k) :=
  rfl

/-- The Step-3 direction computed from the current chosen subgradient `g_k`. -/
def directionAt (method : SubgradientMethod E) (k : ℕ) : E :=
  normalizedSubgradientDirection (method.subgradient k)

/-- Unfolding `method.directionAt k` gives the normalized negative subgradient from Step 3. -/
theorem directionAt_eq (method : SubgradientMethod E) (k : ℕ) :
    method.directionAt k = normalizedSubgradientDirection (method.subgradient k) :=
  rfl

/-- At every stage `k ≥ 1`, the chosen dual subgradient `g_k` lies in `∂ method.objective(x_k)`.
-/
theorem subgradient_mem_at
    (method : SubgradientMethod E) {k : ℕ} (hk : 1 ≤ k) :
    method.subgradient k ∈ ∂ method.objective (method.iterate k) :=
  method.subgradient_mem k hk

/-- If `k ≥ 1`, the next iterate is obtained by moving along the normalized negative
subgradient direction by the recorded positive stepsize `α_k`. -/
theorem iterate_succ_eq_add_direction
    (method : SubgradientMethod E) {k : ℕ} (hk : 1 ≤ k) :
    method.iterate (k + 1) = method.iterate k + method.stepSize k • method.directionAt k := by
  simpa [directionAt] using method.iterate_succ k hk

end SubgradientMethod

#print axioms normalizedSubgradientDirection
#print axioms sunYuanOptimalSolutionSet
#print axioms optimalValue

end
