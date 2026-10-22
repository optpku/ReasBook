/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_14

-- Declarations for this item will be appended below by the statement pipeline.

open EuclideanSpace (nonnegativeOrthant positiveOrthant)
open scoped BigOperators StandardSimplex

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Δₙ" => Δ[n]
local notation "P̂ₙ" => (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Δₙ

/- Algorithm 7.17 lies in the chapter's barrier-based portfolio maximization domain.

Mandatory domain-style sampling:
- `stdSimplex` together with the Chapter 6 notation `Δ[n]` in `Chap06/Definition_6_11`, the
  canonical simplex owner for portfolio weights;
- `EuclideanSpace.positiveOrthant` in `Chap01/Definition_1_10_2`, the project owner for strictly
  positive price-relative vectors in `ℝⁿ_{++}`;
- `LinearPackingProblem.feasibleSet` in `Chap07/Definition_7_41`, the nearby Chapter 7 owner
  pattern where a source-facing feasible region is kept as a set in the ambient Euclidean carrier
  instead of as a set of subtype points;
- `barrierSubgradientPenaltyWeight` in `Chap07/Algorithm_7_14`, the nearby chapter owner for the
  same positive barrier-penalty coefficient;
- mathlib `IsMaxOn`, the canonical maximizer owner used throughout nearby Chapter 7 files.

Best owner abstraction:
- source-facing: Algorithm 7.17's displayed portfolio-update objective and the resulting iterate
  sequence;
- core/canonical: the ambient Euclidean portfolio carrier `Eₙ`, the simplex owner `Δ[n]`, the
  strictly positive price-relative carrier `positiveOrthant n`,
  `barrierSubgradientPenaltyWeight`, and the feasible trajectory `ℕ → P`;
- bridge/view: the Euclidean simplex slice `P̂ₙ`, the displayed objective expansion, and the
  positivity theorem for the denominator in the relative-growth term.

Primitive data:
- a feasible set `P : Set Eₙ` of ambient portfolio vectors together with the bridge
  `P ⊆ P̂ₙ` expressing that those vectors are simplex-valued portfolio weights;
- an ambient barrier term `F : Eₙ → ℝ`, positive barrier parameter `ν : NNRealˣ`, and initial
  portfolio `x₀ : P`;
- a strictly positive price-relative sequence `cₖ : positiveOrthant n`;
- a feasible iterate sequence `x₀, x₁, x₂, ...` together with the stagewise maximizer condition.

Derived API:
- positivity of every one-period portfolio return `⟪cₖ, x⟫`;
- positivity of the denominator in the displayed relative-growth term;
- the step objective attached to a fixed history;
- coercions from a run to its underlying Euclidean iterate sequence and the induced
  simplex-feasibility/maximizer lemmas.

Source/core/bridge triage:
- source-facing: `portfolioBarrierStepObjective` and
  `BarrierPortfolioWeightUpdateAlgorithm`;
- core/canonical: `Eₙ`, `Δ[n]`, `positiveOrthant n`, `barrierSubgradientPenaltyWeight`, and
  `IsMaxOn`;
- bridge/view: `P̂ₙ`, `mem_portfolioWeightSet_iff`, `portfolioPeriodReturn_pos`,
  `portfolioBarrierDenominator_pos`, `stepObjective`, and the feasibility projection theorems.

The previous version removed the duplicate penalty-weight wheel and the nonpositive-price-relative
issue, but it still kept the public objective on `Δ[n]` while the barrier and price relatives
lived on `Eₙ`, so the displayed formula carried repeated `EuclideanSpace.equiv ... .symm`
transport noise. This refinement keeps the source mathematics on the ambient Euclidean portfolio
carrier `Eₙ`, records simplex membership only through the thin bridge `P̂ₙ`, reuses the chapter
penalty-weight owner directly, and keeps price relatives on the intrinsic strict-positive carrier
`positiveOrthant n` so the denominator in the displayed objective is canonically positive.
-/

/-- The Euclidean portfolio-weight carrier `P̂ₙ` is exactly the nonnegative orthant slice with
total mass `1`. -/
@[simp] theorem mem_portfolioWeightSet_iff {x : Eₙ} :
    x ∈ P̂ₙ ↔ x ∈ nonnegativeOrthant n ∧ ∑ i, x i = 1 := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · simpa [EuclideanSpace.mem_nonnegativeOrthant_iff, stdSimplex] using hx.1
    · simpa [stdSimplex] using hx.2
  · rintro ⟨hx_nonneg, hx_sum⟩
    refine ⟨?_, ?_⟩
    · simpa [EuclideanSpace.mem_nonnegativeOrthant_iff, stdSimplex] using hx_nonneg
    · simpa [stdSimplex] using hx_sum

/-- A strictly positive price-relative vector has strictly positive return on every simplex
portfolio. -/
theorem portfolioPeriodReturn_pos
    (c : positiveOrthant n) {x : Eₙ} (hx : x ∈ P̂ₙ) :
    0 < dotProduct (c : Eₙ) x := by
  classical
  rcases (mem_portfolioWeightSet_iff.mp hx) with ⟨hx_nonneg, hx_sum⟩
  have hx_ne_zero : ∃ i : Fin n, x i ≠ 0 := by
    by_contra hx0
    have hx_zero : ∀ i : Fin n, x i = 0 := by
      simpa using not_exists.mp hx0
    have hsum_zero : ∑ i, x i = 0 := by
      simp [hx_zero]
    linarith
  rcases hx_ne_zero with ⟨i, hi⟩
  have hpos_term : 0 < (c : Eₙ) i * x i := by
    have hx_i : 0 < x i := lt_of_le_of_ne (hx_nonneg i) (Ne.symm hi)
    exact mul_pos (c.2 i) hx_i
  rw [dotProduct]
  exact lt_of_lt_of_le hpos_term <|
    Finset.single_le_sum
      (fun j _ ↦ mul_nonneg (le_of_lt (c.2 j)) (hx_nonneg j))
      (Finset.mem_univ i)

/-- Every denominator in Algorithm 7.17's relative-growth model is positive. -/
theorem portfolioBarrierDenominator_pos
    {P : Set Eₙ} (hP : P ⊆ P̂ₙ) (c : ℕ → positiveOrthant n) (history : ℕ → P) (i : ℕ) :
    0 < dotProduct (c i : Eₙ) (history i : Eₙ) :=
  portfolioPeriodReturn_pos (c i) (hP (history i).property)

/-- The maximization objective used at iteration `k` in the barrier-based portfolio-weight update
scheme. The reciprocal denominator is positive by `portfolioBarrierDenominator_pos`. -/
def portfolioBarrierStepObjective
    {P : Set Eₙ} (F : Eₙ → ℝ) (ν : NNRealˣ) (x0 : P)
    (c : ℕ → positiveOrthant n) (history : ℕ → P)
    (k : ℕ) : Eₙ → ℝ :=
  fun x ↦
    ((1 / ((k : ℝ) + 1)) *
        ∑ i ∈ Finset.range (k + 1),
          dotProduct (c i : Eₙ) (x - (history i : Eₙ)) /
            dotProduct (c i : Eₙ) (history i : Eₙ)) -
      barrierSubgradientPenaltyWeight ν k * (F x - F x0)

/-- Evaluating `portfolioBarrierStepObjective F ν x0 c history k` at `x` recovers the objective
displayed in Algorithm 7.17. -/
theorem portfolioBarrierStepObjective_apply
    {P : Set Eₙ} (F : Eₙ → ℝ) (ν : NNRealˣ) (x0 : P)
    (c : ℕ → positiveOrthant n) (history : ℕ → P)
    (k : ℕ) (x : Eₙ) :
    portfolioBarrierStepObjective F ν x0 c history k x =
      ((1 / ((k : ℝ) + 1)) *
          ∑ i ∈ Finset.range (k + 1),
            dotProduct (c i : Eₙ) (x - (history i : Eₙ)) /
              dotProduct (c i : Eₙ) (history i : Eₙ)) -
        barrierSubgradientPenaltyWeight ν k * (F x - F x0) :=
  rfl

/-- Algorithm 7.17: given a feasible set `P` of ambient Euclidean portfolio vectors whose points
all lie in the simplex slice `P̂ₙ`, an ambient barrier term `F`, a positive parameter `ν`, an
initial feasible portfolio `x₀`, and strictly positive price-relative vectors
`cₖ ∈ ℝⁿ_{++}`, a barrier-based portfolio-weight update algorithm is a sequence
`x₀, x₁, x₂, ...` such that for each `k ≥ 0` the next iterate `xₖ₊₁` maximizes the displayed
averaged relative-growth objective with barrier penalty over `P`. Any self-concordant-barrier
hypothesis on `F` belongs to later theorem layers, not to the primitive run data. -/
structure BarrierPortfolioWeightUpdateAlgorithm
    (P : Set Eₙ) (F : Eₙ → ℝ) (ν : NNRealˣ) (x0 : P)
    (c : ℕ → positiveOrthant n) where
  /-- Every feasible point of `P` is a simplex-valued portfolio weight vector in the Euclidean
  carrier `Eₙ`. -/
  subset_portfolioWeightSet : P ⊆ P̂ₙ
  /-- The feasible iterate sequence `x₀, x₁, x₂, ...`. -/
  iterate : ℕ → P
  /-- The zeroth iterate is the prescribed feasible point `x₀`. -/
  iterate_zero : iterate 0 = x0
  /-- For every iteration `k`, the next portfolio weight vector `xₖ₊₁` maximizes the objective
  from Algorithm 7.17 over the feasible set `P`. -/
  step_isMax :
    ∀ k : ℕ,
      IsMaxOn
        (portfolioBarrierStepObjective F ν x0 c iterate k)
        P
        (iterate (k + 1) : Eₙ)

namespace BarrierPortfolioWeightUpdateAlgorithm

/-- A run of Algorithm 7.17 can be used as its underlying Euclidean iterate sequence `k ↦ xₖ`. -/
instance
    {P : Set Eₙ} {F : Eₙ → ℝ} {ν : NNRealˣ} {x0 : P}
    {c : ℕ → positiveOrthant n} :
    CoeFun (BarrierPortfolioWeightUpdateAlgorithm P F ν x0 c) (fun _ ↦ ℕ → Eₙ) where
  coe algorithm k := algorithm.iterate k

/-- The prescribed initial portfolio belongs to the feasible set `P`. -/
theorem x0_mem
    {P : Set Eₙ} {F : Eₙ → ℝ} {ν : NNRealˣ} {x0 : P}
    {c : ℕ → positiveOrthant n}
    (_algorithm : BarrierPortfolioWeightUpdateAlgorithm P F ν x0 c) :
    (x0 : Eₙ) ∈ P :=
  x0.property

/-- The prescribed initial portfolio is a simplex-valued Euclidean portfolio weight vector. -/
theorem x0_mem_portfolioWeightSet
    {P : Set Eₙ} {F : Eₙ → ℝ} {ν : NNRealˣ} {x0 : P}
    {c : ℕ → positiveOrthant n}
    (algorithm : BarrierPortfolioWeightUpdateAlgorithm P F ν x0 c) :
    (x0 : Eₙ) ∈ P̂ₙ :=
  algorithm.subset_portfolioWeightSet x0.property

/-- The zeroth iterate is the prescribed initial portfolio `x₀`. -/
@[simp] theorem coe_iterate_zero
    {P : Set Eₙ} {F : Eₙ → ℝ} {ν : NNRealˣ} {x0 : P}
    {c : ℕ → positiveOrthant n}
    (algorithm : BarrierPortfolioWeightUpdateAlgorithm P F ν x0 c) :
    algorithm 0 = x0 := by
  exact congrArg (fun x : P ↦ (x : Eₙ)) algorithm.iterate_zero

/-- The step objective attached to a run of the barrier-based portfolio-weight update at time
`k`. -/
def stepObjective
    {P : Set Eₙ} {F : Eₙ → ℝ} {ν : NNRealˣ} {x0 : P}
    {c : ℕ → positiveOrthant n}
    (algorithm : BarrierPortfolioWeightUpdateAlgorithm P F ν x0 c) (k : ℕ) :
    Eₙ → ℝ :=
  portfolioBarrierStepObjective F ν x0 c algorithm.iterate k

/-- Expanding `algorithm.stepObjective k` gives the Algorithm 7.17 objective evaluated on the
iterate history of `algorithm`. -/
theorem stepObjective_def
    {P : Set Eₙ} {F : Eₙ → ℝ} {ν : NNRealˣ} {x0 : P}
    {c : ℕ → positiveOrthant n}
    (algorithm : BarrierPortfolioWeightUpdateAlgorithm P F ν x0 c) (k : ℕ) :
    algorithm.stepObjective k =
      portfolioBarrierStepObjective F ν x0 c algorithm.iterate k :=
  rfl

/-- Every iterate generated by Algorithm 7.17 belongs to the feasible set `P`. -/
theorem iterate_mem
    {P : Set Eₙ} {F : Eₙ → ℝ} {ν : NNRealˣ} {x0 : P}
    {c : ℕ → positiveOrthant n}
    (algorithm : BarrierPortfolioWeightUpdateAlgorithm P F ν x0 c) (k : ℕ) :
    algorithm k ∈ P :=
  (algorithm.iterate k).property

/-- Every successor iterate generated by Algorithm 7.17 belongs to the feasible set `P`. -/
theorem iterates_succ_mem
    {P : Set Eₙ} {F : Eₙ → ℝ} {ν : NNRealˣ} {x0 : P}
    {c : ℕ → positiveOrthant n}
    (algorithm : BarrierPortfolioWeightUpdateAlgorithm P F ν x0 c) (k : ℕ) :
    algorithm (k + 1) ∈ P :=
  (algorithm.iterate (k + 1)).property

/-- Every iterate generated by Algorithm 7.17 is a simplex-valued Euclidean portfolio weight
vector. -/
theorem iterate_mem_portfolioWeightSet
    {P : Set Eₙ} {F : Eₙ → ℝ} {ν : NNRealˣ} {x0 : P}
    {c : ℕ → positiveOrthant n}
    (algorithm : BarrierPortfolioWeightUpdateAlgorithm P F ν x0 c) (k : ℕ) :
    algorithm k ∈ P̂ₙ :=
  algorithm.subset_portfolioWeightSet (algorithm.iterate k).property

/-- For every iteration `k`, the denominator in Algorithm 7.17's displayed relative-growth model
is positive along the iterate history of `algorithm`. -/
theorem denominator_pos
    {P : Set Eₙ} {F : Eₙ → ℝ} {ν : NNRealˣ} {x0 : P}
    {c : ℕ → positiveOrthant n}
    (algorithm : BarrierPortfolioWeightUpdateAlgorithm P F ν x0 c) (i : ℕ) :
    0 < dotProduct (c i : Eₙ) (algorithm i) :=
  portfolioPeriodReturn_pos (c i) (algorithm.iterate_mem_portfolioWeightSet i)

/-- For every iteration `k`, the successor iterate `xₖ₊₁` maximizes the Algorithm 7.17 step
objective over `P`. -/
theorem step_isMaxOn
    {P : Set Eₙ} {F : Eₙ → ℝ} {ν : NNRealˣ} {x0 : P}
    {c : ℕ → positiveOrthant n}
    (algorithm : BarrierPortfolioWeightUpdateAlgorithm P F ν x0 c) (k : ℕ) :
    IsMaxOn (algorithm.stepObjective k) P (algorithm (k + 1)) := by
  simpa [stepObjective] using algorithm.step_isMax k

end BarrierPortfolioWeightUpdateAlgorithm

end
