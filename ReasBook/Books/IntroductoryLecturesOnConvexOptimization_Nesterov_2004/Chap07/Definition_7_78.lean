/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators EuclideanOrthant StandardSimplex

/-
Definition 7.78 lies in Chapter 7's orthant/simplex investment-model domain.

Sampled owner-style declarations:
- `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` in
  `Chap01/Definition_1_10_2`, the chapter owner and coordinatewise membership API for
  `ℝⁿ_+`;
- `stdSimplex` in mathlib and the Chapter 6 notation `Δ[n]` in `Chap06/Definition_6_11`, the
  canonical owner of the standard simplex;
- `LinearPackingProblem` and its `CoeFun` / feasible-set bridge API in
  `Chap07/Definition_7_41`, the local chapter style for optimization data plus derived owners.

Best owner abstraction:
- source-facing: `ElasticProductionInvestmentModel n`, carrying the period-dependent cost/price
  data and their sign assumptions;
- core/canonical: `nonnegativeOrthant n` and `Δ[n]`;
- bridge/view: the source-facing names `decisionSet` and `feasibleSet`.

Primitive data:
- the production-cost family `a_k^(i)`;
- the unit-price family `b_k^(i)`;
- the sign assumptions `a_k^(i) > 0` and `b_k^(i) ≥ 0`.

Derived API:
- the decision set `Q`, via the chapter orthant owner `nonnegativeOrthant n`;
- the feasible set `P̂`, via the Euclidean-coordinate bridge to the canonical simplex owner;
- the period return factor `ψ_k`.

Source/core/bridge triage:
- `ElasticProductionInvestmentModel` remains source-facing;
- `decisionSet` and `feasibleSet` are thin bridge/view abbreviations to existing owners;
- the return-factor API is derived directly from the model data.
-/

/-- Definition 7.78: an elastic production investment model with `n` production processes consists
of period-dependent production costs `a_k^(i) > 0` and unit prices `b_k^(i) ≥ 0`. -/
structure ElasticProductionInvestmentModel (n : ℕ) where
  /-- The production cost `a_k^(i)` of process `i` in period `k`. -/
  productionCost : ℕ → Fin n → ℝ
  /-- The unit price `b_k^(i)` of process `i` in period `k`. -/
  unitPrice : ℕ → Fin n → ℝ
  /-- Every production cost is strictly positive. -/
  productionCost_pos (k : ℕ) (i : Fin n) : 0 < productionCost k i
  /-- Every unit price is nonnegative. -/
  unitPrice_nonneg (k : ℕ) (i : Fin n) : 0 ≤ unitPrice k i

namespace ElasticProductionInvestmentModel

/-- The nonnegative orthant `Q = ℝ_+^n` of investment fraction vectors. -/
abbrev decisionSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  ℝ₊^n

/-- Membership in `decisionSet n` means that every investment fraction is nonnegative. -/
@[simp] theorem mem_decisionSet_iff {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ decisionSet n ↔ ∀ i, 0 ≤ x i := by
  simp [decisionSet]

/-- The feasible decision set `P̂ = Δ_n`, realized in Euclidean coordinates via the canonical
equivalence `EuclideanSpace ℝ (Fin n) ≃L[ℝ] Fin n → ℝ`. -/
abbrev feasibleSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Δ[n]

/-- Membership in the feasible set means belonging to the nonnegative orthant with coordinate sum
equal to `1`. -/
@[simp] theorem mem_feasibleSet_iff {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ feasibleSet n ↔ x ∈ decisionSet n ∧ ∑ i, x i = 1 := by
  simp [feasibleSet, decisionSet, stdSimplex]

/-- The return factor `ψ_k(x)` in period `k` is the weighted sum of the investment fractions with
weights `b_k^(i) / a_k^(i)`. -/
def returnFactor
    (model : ElasticProductionInvestmentModel n) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, (model.unitPrice k i / model.productionCost k i) * x i

/-- An elastic production investment model can be used as its period-dependent return-factor
function `ψ`. -/
instance : CoeFun (ElasticProductionInvestmentModel n)
    (fun _ ↦ ℕ → EuclideanSpace ℝ (Fin n) → ℝ) where
  coe model := model.returnFactor

/-- Evaluating the model as a function returns its period-dependent return factor. -/
@[simp] theorem coe_apply (model : ElasticProductionInvestmentModel n) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    model k x = model.returnFactor k x :=
  rfl

/-- Unfolding `returnFactor` gives the textbook finite-sum formula for `ψ_k(x)`. -/
theorem returnFactor_eq_sum (model : ElasticProductionInvestmentModel n) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    model.returnFactor k x = ∑ i : Fin n, (model.unitPrice k i / model.productionCost k i) * x i :=
  rfl

end ElasticProductionInvestmentModel
