/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Data.Fintype.BigOperators

public section

noncomputable section

open scoped BigOperators

namespace KKT

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type v} [Fintype ι]

/-- The Karush-Kuhn-Tucker conditions for `J`, `c`, `f`, and multipliers `μ`
consist of stationarity, dual nonnegativity, primal feasibility, and
complementarity. -/
structure IsMultiplier (J : H → ℝ) (c : ι → H → ℝ) (f : H) (μ : ι → ℝ) : Prop where
  stationarity : gradient J f = ∑ i, μ i • gradient (c i) f
  dualNonneg : ∀ i, 0 ≤ μ i
  primalFeasible : ∀ i, 0 ≤ c i f
  complementarity : ∀ i, μ i * c i f = 0

/-- Build a KKT multiplier certificate from the four defining clauses. -/
abbrev ofConditions
    {J : H → ℝ} {c : ι → H → ℝ} {f : H} {μ : ι → ℝ}
    (hStationarity : gradient J f = ∑ i, μ i • gradient (c i) f)
    (hDualNonneg : ∀ i, 0 ≤ μ i)
    (hPrimalFeasible : ∀ i, 0 ≤ c i f)
    (hComplementarity : ∀ i, μ i * c i f = 0) :
    IsMultiplier J c f μ where
  stationarity := hStationarity
  dualNonneg := hDualNonneg
  primalFeasible := hPrimalFeasible
  complementarity := hComplementarity

/-- The defining clauses of `KKT.IsMultiplier`. -/
theorem isMultiplier_iff (J : H → ℝ) (c : ι → H → ℝ) (f : H) (μ : ι → ℝ) :
    IsMultiplier J c f μ ↔
      gradient J f = ∑ i, μ i • gradient (c i) f ∧
        (∀ i, 0 ≤ μ i) ∧
        (∀ i, 0 ≤ c i f) ∧
        ∀ i, μ i * c i f = 0 := by
  constructor
  · intro h
    exact ⟨h.stationarity, h.dualNonneg, h.primalFeasible, h.complementarity⟩
  · rintro ⟨hStationarity, hDualNonneg, hPrimalFeasible, hComplementarity⟩
    exact ofConditions hStationarity hDualNonneg hPrimalFeasible hComplementarity

end KKT
