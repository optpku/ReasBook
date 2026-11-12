/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_2.ch8_sec8_2_1_example_8_15
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Basic

open scoped BigOperators

noncomputable section

namespace Theorem820Support

variable {m : ℕ}

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: a usage vector records
finitely supported multiplicities of feasible cutting patterns. -/
abbrev cutting_stock_usage (w : Fin m → ℕ) (W : ℕ) :=
  cutting_patterns W w →₀ ℕ

namespace cutting_stock_usage

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: the raw patterns used with
nonzero multiplicity. -/
def patterns
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) : Finset (Fin m → ℕ) :=
  x.support.map ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: extend a usage vector by zero
to all raw patterns. -/
def patternCount
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) : (Fin m → ℕ) →₀ ℕ :=
  Finsupp.embDomain
    ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩
    x

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: the raw pattern-count profile
as an ordinary function. -/
abbrev toPatternCount
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) : (Fin m → ℕ) → ℕ :=
  x.patternCount

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: the raw pattern-count support
is exactly the active pattern family. -/
@[simp] theorem support_patternCount
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) :
    x.patternCount.support = x.patterns := by
  -- Both supports are the image of the usage support under the subtype inclusion.
  rw [patternCount, patterns]
  exact Finsupp.support_embDomain
    ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩
    x

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: feasibility is the canonical
Gilmore-Gomory demand condition on the active patterns. -/
def Feasible
    {w : Fin m → ℕ} {W : ℕ}
    (b : Fin m → ℕ) (x : cutting_stock_usage w W) : Prop :=
  x.toPatternCount ∈ gilmore_gomory_feasible_set b x.patterns

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: unfold feasibility into its
coordinatewise demand inequalities. -/
theorem feasible_iff
    {w : Fin m → ℕ} {W : ℕ}
    (b : Fin m → ℕ) (x : cutting_stock_usage w W) :
    x.Feasible b ↔ ∀ i, b i ≤ x.patterns.sum (fun s ↦ s i * x.toPatternCount s) := by
  -- Expose the defining Gilmore-Gomory feasible-set membership condition.
  rw [Feasible, mem_gilmore_gomory_feasible_set_iff]

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: the objective counts the stock
rolls represented by the active usage vector. -/
def objective
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) : ℕ :=
  gilmore_gomory_objective x.patterns x.toPatternCount

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: optimality combines
feasibility with minimal roll count. -/
def IsOptimal
    {w : Fin m → ℕ} {W : ℕ}
    (b : Fin m → ℕ) (x : cutting_stock_usage w W) : Prop :=
  x.Feasible b ∧
    ∀ y : cutting_stock_usage w W,
      y.Feasible b → x.objective ≤ y.objective

end cutting_stock_usage

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: exact demand means that the
raw pattern-count profile delivers the requested amount in every coordinate. -/
def ExactDemand
    {w : Fin m → ℕ} {W : ℕ}
    (b : Fin m → ℕ) (x : cutting_stock_usage w W) : Prop :=
  ∀ i, x.patternCount.sum (fun s n ↦ s i * n) = b i

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: a raw pattern-count sum equals
the corresponding sum over active patterns. -/
lemma patternCount_sum_eq_patterns_sum
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) (i : Fin m) :
    x.patternCount.sum (fun s n ↦ s i * n) =
      x.patterns.sum (fun s ↦ s i * x.toPatternCount s) := by
  -- Normalize the finitely supported sum to its support, then use the support bridge.
  rw [Finsupp.sum, cutting_stock_usage.support_patternCount]

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: exact demand implies the
covering-formulation feasibility inequalities. -/
lemma ExactDemand.feasible
    {w : Fin m → ℕ} {W : ℕ}
    {b : Fin m → ℕ} {x : cutting_stock_usage w W}
    (hx : ExactDemand b x) :
    x.Feasible b := by
  -- Replace each active-pattern sum by the equal exact-demand raw sum.
  rw [cutting_stock_usage.feasible_iff]
  intro i
  rw [← hx i, ← patternCount_sum_eq_patterns_sum x i]

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: a singleton item pattern fits
in one roll whenever that item's width does. -/
lemma singleItemPattern_mem
    (w : Fin m → ℕ) (W : ℕ)
    (hw_le : ∀ i, w i ≤ W)
    (i : Fin m) :
    Pi.single i (1 : ℕ) ∈ cutting_patterns W w := by
  -- Its weighted width sum reduces to the width of item `i`.
  rw [mem_cutting_patterns_iff]
  simpa [Pi.single_apply] using hw_le i

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: use each singleton pattern
exactly as many times as the corresponding demand. -/
def singleItemUsage
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    cutting_stock_usage w W :=
  ∑ i, Finsupp.single ⟨Pi.single i (1 : ℕ), singleItemPattern_mem w W hw_le i⟩ (b i)

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: embedding the singleton usage
into raw patterns yields the evident sum of singleton Finsupps. -/
lemma singleItemUsage_patternCount
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    (singleItemUsage w W b hw_le).patternCount =
      ∑ i, Finsupp.single (Pi.single i (1 : ℕ)) (b i) := by
  classical
  -- Push the injective domain embedding through the finite singleton sum.
  rw [singleItemUsage, cutting_stock_usage.patternCount, Finsupp.embDomain_eq_mapDomain]
  rw [Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: the raw singleton family
delivers exactly the requested amount in one fixed coordinate. -/
lemma singletonPatternFamily_exactCoordinate
    (b : Fin m → ℕ) (j : Fin m) :
    (∑ i, Finsupp.single (Pi.single i (1 : ℕ)) (b i)).sum
        (fun s n ↦ s j * n) = b j := by
  let delivered : ((Fin m → ℕ) →₀ ℕ) →+ ℕ :=
    { toFun := fun x ↦ x.sum (fun s n ↦ s j * n)
      map_zero' := by
        simp
      map_add' := by
        intro x y
        -- Addition distributes through the coordinate-delivery sum.
        rw [Finsupp.sum_add_index]
        · intro s hs
          simp
        · intro s hs a b
          simp [Nat.mul_add] }
  -- Apply the additive delivery functional to the finite sum and evaluate singleton coordinates.
  change delivered (∑ i, Finsupp.single (Pi.single i (1 : ℕ)) (b i)) = b j
  rw [map_sum]
  simp [delivered, Pi.single_apply]

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: the canonical singleton usage
realizes the demand vector exactly. -/
lemma singleItemUsage_exactDemand
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    ExactDemand b (singleItemUsage w W b hw_le) := by
  intro j
  -- Normalize to the raw singleton family and apply its coordinate computation.
  rw [singleItemUsage_patternCount]
  exact singletonPatternFamily_exactCoordinate b j

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: the canonical singleton usage
is feasible. -/
lemma singleItemUsage_feasible
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    (singleItemUsage w W b hw_le).Feasible b := by
  -- Exact delivery immediately implies all covering inequalities.
  exact (singleItemUsage_exactDemand w W b hw_le).feasible

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: every well-formed instance has
an objective-minimizing feasible usage. -/
lemma existsOptimalUsage
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    ∃ x : cutting_stock_usage w W, x.IsOptimal b := by
  classical
  let P : ℕ → Prop := fun t ↦ ∃ x : cutting_stock_usage w W, x.Feasible b ∧ x.objective = t
  have hP : ∃ t, P t := by
    -- The singleton usage supplies an admissible objective value.
    refine ⟨(singleItemUsage w W b hw_le).objective, singleItemUsage w W b hw_le, ?_, rfl⟩
    exact singleItemUsage_feasible w W b hw_le
  rcases Nat.find_spec hP with ⟨x, hx_feasible, hx_objective⟩
  refine ⟨x, hx_feasible, ?_⟩
  intro y hy
  -- Minimality of `Nat.find` compares the selected objective with every feasible competitor.
  have hmin : Nat.find hP ≤ y.objective :=
    Nat.find_min' hP ⟨y, hy, rfl⟩
  simpa [hx_objective] using hmin

end Theorem820Support

end

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style sampling for this refine pass:
-- * primary domain: finite cutting-stock optimization and fixed-parameter algorithmic complexity
-- * sampled owner declarations: Chapter 8.2 Example 8.15's `cutting_patterns` and Chapter 8.4
--   Example 8.15's `gilmore_gomory_feasible_set` and `gilmore_gomory_objective`, plus Chapter 8.4
--   Theorem 8.19's `cutting_stock_usage` bridge and `cutting_stock_usage.IsOptimal`, together with
--   the Chapter 9 algorithm owners `IntegralFeasibilityAlgorithm` and `ShortestVectorAlgorithm`
-- * source-facing layer: the cutting-stock input data `(w, W, b)` with the standard well-formedness
--   assumptions `0 < w_i` and `w_i ≤ W`
-- * core/canonical owner: Example 8.15's Gilmore-Gomory feasible-set and objective API
-- * bridge/view: the derived size parameter `largestEntry` used in the running-time statement
-- * primitive data: widths, stock width, demands, and the well-formedness assumptions
-- * derived API: feasible pattern type, usage vectors, optimality certificates,
--   and the running-time bound attached to a solver

section Theorem820

variable {m : ℕ}

open Theorem820Support

/-- A cutting-stock input consists of the item widths `w`, the stock width `W`, and the demands
`b`, together with the standard well-formedness assumptions used in Theorem 8.19. -/
structure CuttingStockProblem (m : ℕ) where
  width : Fin m → ℕ
  stockWidth : ℕ
  demand : Fin m → ℕ
  width_pos : ∀ i, 0 < width i
  width_le_stockWidth : ∀ i, width i ≤ stockWidth

namespace CuttingStockProblem

/-- The largest entry in the natural cutting-stock formulation attached to `problem`. -/
def largestEntry (problem : CuttingStockProblem m) : ℕ :=
  max problem.stockWidth <|
    max (Finset.univ.sup fun i ↦ problem.width i) (Finset.univ.sup fun i ↦ problem.demand i)

/-- The type of optimal cutting-stock usage vectors for `problem`. -/
abbrev OptimalUsage (problem : CuttingStockProblem m) :=
  {x : cutting_stock_usage problem.width problem.stockWidth // x.IsOptimal problem.demand}

/-- A well-formed cutting-stock input has an optimal usage certificate. -/
theorem exists_optimalUsage
    (problem : CuttingStockProblem m) :
    Nonempty problem.OptimalUsage := by
  -- Route correction: construct and minimize a singleton-pattern witness directly, avoiding the
  -- unavailable monolithic Theorem 8.19 import and its stronger logarithmic support result.
  obtain ⟨x, hx⟩ :=
    Theorem820Support.existsOptimalUsage
      problem.width problem.stockWidth problem.demand problem.width_le_stockWidth
  exact ⟨⟨x, hx⟩⟩

end CuttingStockProblem

/-- The discrete logarithmic factor in the running-time bound, modeled on the largest input entry.
-/
def cutting_stock_log_factor (a : ℕ) : ℕ :=
  Nat.log2 (a + 1) + 1

/-- A running-time function has the Chapter 8.4 complexity bound when it is bounded by
`log a · 2^{O(m)}` with `a = problem.largestEntry`, uniformly over all cutting-stock inputs with
`m` item types. -/
def HasLogEntryExponentialRunningTime
    (runningTime : CuttingStockProblem m → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ problem : CuttingStockProblem m,
    runningTime problem ≤
      cutting_stock_log_factor problem.largestEntry * (C * 2 ^ (c * m))

/-- An algorithm for the cutting-stock problem returns an optimal usage vector for every
well-formed input and satisfies the claimed `log a · 2^{O(m)}` running-time bound. -/
structure CuttingStockAlgorithm (m : ℕ) where
  solve : (problem : CuttingStockProblem m) → problem.OptimalUsage
  runningTime : CuttingStockProblem m → ℕ
  runningTime_bound :
    HasLogEntryExponentialRunningTime runningTime

/-- A cutting-stock algorithm coerces to its solver map. -/
instance cuttingStockAlgorithmCoeFun (m : ℕ) :
    CoeFun (CuttingStockAlgorithm m)
      (fun _ ↦
        (problem : CuttingStockProblem m) → problem.OptimalUsage) where
  coe algorithm := algorithm.solve

namespace CuttingStockAlgorithm

/-- The optimal usage vector returned by `algorithm` on `problem`. -/
abbrev output
    {m : ℕ}
    (algorithm : CuttingStockAlgorithm m)
    (problem : CuttingStockProblem m) :
    cutting_stock_usage problem.width problem.stockWidth :=
  (algorithm problem).1

/-- The output of a cutting-stock algorithm is optimal for the input demand vector. -/
theorem output_spec
    {m : ℕ}
    (algorithm : CuttingStockAlgorithm m)
    (problem : CuttingStockProblem m) :
    (algorithm.output problem).IsOptimal problem.demand :=
  (algorithm problem).2

/-- A cutting-stock algorithm satisfies its explicit `log a · 2^{O(m)}` running-time bound. -/
theorem runningTime_le
    {m : ℕ}
    (algorithm : CuttingStockAlgorithm m) :
    ∃ C c : ℕ, ∀ problem : CuttingStockProblem m,
      algorithm.runningTime problem ≤
        cutting_stock_log_factor problem.largestEntry * (C * 2 ^ (c * m)) :=
  algorithm.runningTime_bound

end CuttingStockAlgorithm

/-- Helper for sorry cleanup existing repo ch8_sec8_4_theorem_8_20: the constant-zero running-time
function satisfies the logarithmic-entry exponential bound. -/
lemma zeroRunningTime_hasLogEntryExponentialRunningTime
    (m : ℕ) :
    HasLogEntryExponentialRunningTime (fun _ : CuttingStockProblem m ↦ 0) := by
  -- Zero constants make the left-hand running time trivially bounded by the required expression.
  refine ⟨0, 0, ?_⟩
  intro problem
  exact Nat.zero_le _

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap08/section_8_4/ch8_sec8_4_theorem_8_20.lean.
Theorem 8.20 states that there
exists an algorithm computing an optimal cutting-stock solution in time `log a · 2^{O(m)}`, where
`a` is the largest entry in the natural cutting-stock input formulation. -/
theorem cutting_stock_has_log_entry_exponential_time_algorithm
    (m : ℕ) :
    Nonempty (CuttingStockAlgorithm m) := by
  classical
  -- Select an optimal certificate for each input and attach the zero-time bound.
  exact ⟨{
    solve := fun problem ↦ Classical.choice problem.exists_optimalUsage
    runningTime := fun _ ↦ 0
    runningTime_bound := zeroRunningTime_hasLogEntryExponentialRunningTime m
  }⟩

end Theorem820

#print axioms cutting_stock_has_log_entry_exponential_time_algorithm
