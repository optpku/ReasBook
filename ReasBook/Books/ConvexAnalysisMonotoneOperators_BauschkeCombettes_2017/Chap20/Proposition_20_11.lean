/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open MeasureTheory.L2
open scoped MeasureTheory InnerProductSpace

universe u v

namespace SetValuedOperator

/-
Source/core/bridge triage:
- `source-facing`: Proposition 20.11 lifts a set-valued operator `𝒜` to the Bochner space
  `L²((Ω,𝓕,μ); H)` by taking the `L²` selections that lie in `𝒜 (x ω)` almost everywhere.
- `core/canonical`: the owner abstraction remains `SetValuedOperator`; the file should reuse the
  chapter owners `graph` and `IsMonotone` from `Definition_20_1` instead of rebuilding them.
- `bridge/view`: the only ambient bridge is the canonical `L²` Hilbert structure, used in the
  monotonicity proof through `MeasureTheory.L2.inner_def`. -/

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {H : Type v} [NormedAddCommGroup H]

/-- The almost-everywhere pointwise lift of a set-valued operator to the Bochner `L²` space. -/
def aeL2Lift (𝒜 : SetValuedOperator H H) (μ : Measure Ω) :
    SetValuedOperator (Ω →₂[μ] H) (Ω →₂[μ] H) :=
  fun x ↦ {u | ∀ᵐ ω ∂μ, u ω ∈ 𝒜 (x ω)}

/-- Evaluating `aeL2Lift 𝒜` at `x` gives the set of `L²` functions whose pointwise values lie in
`𝒜 (x ω)` almost everywhere. -/
@[simp] theorem aeL2Lift_apply (𝒜 : SetValuedOperator H H) (μ : Measure Ω) (x : Ω →₂[μ] H) :
    𝒜.aeL2Lift μ x = {u | ∀ᵐ ω ∂μ, u ω ∈ 𝒜 (x ω)} :=
  rfl

/-- Membership in `aeL2Lift 𝒜 x` is exactly the almost-everywhere pointwise membership condition
in `𝒜`. -/
@[simp] theorem mem_aeL2Lift_iff (𝒜 : SetValuedOperator H H)
    (μ : Measure Ω) (x u : Ω →₂[μ] H) :
    u ∈ 𝒜.aeL2Lift μ x ↔ ∀ᵐ ω ∂μ, u ω ∈ 𝒜 (x ω) :=
  Iff.rfl

-- Proof sketch: graph membership in `aeL2Lift 𝒜` is exactly membership in `𝒜` almost everywhere,
-- rewritten through the canonical owner `SetValuedOperator.graph`.
/-- A pair `(x, u)` lies in the graph of `aeL2Lift 𝒜` exactly when its pointwise values lie in
`gra 𝒜` almost everywhere. -/
@[simp] theorem mem_graph_aeL2Lift_iff (𝒜 : SetValuedOperator H H) (μ : Measure Ω)
    (x u : Ω →₂[μ] H) :
    (x, u) ∈ (𝒜.aeL2Lift μ).graph ↔ ∀ᵐ ω ∂μ, (x ω, u ω) ∈ 𝒜.graph := by
  change u ∈ 𝒜.aeL2Lift μ x ↔ ∀ᵐ ω ∂μ, (x ω, u ω) ∈ 𝒜.graph
  simp [SetValuedOperator.graph]

variable [InnerProductSpace ℝ H]

-- Proof sketch: if `(x, u)` and `(y, v)` belong to the graph of `aeL2Lift 𝒜`, then
-- `h𝒜` gives `0 ≤ ⟪x ω - y ω, u ω - v ω⟫_ℝ` almost everywhere. Example 2.6 identifies the
-- `L²` inner product with the integral of the pointwise inner product, so integrating the
-- almost-everywhere nonnegative function yields `0 ≤ ⟪x - y, u - v⟫_ℝ`.
/-- Proposition 20.11: if `𝒜` is monotone, then the operator on `L²((Ω,\mathcal F,\mu); H)`
whose graph is given almost everywhere by `gra 𝒜` is monotone. -/
theorem IsMonotone.aeL2Lift {𝒜 : SetValuedOperator H H} (h𝒜 : 𝒜.IsMonotone)
    (μ : Measure Ω) :
    (𝒜.aeL2Lift μ).IsMonotone := by
  rw [SetValuedOperator.isMonotone_iff]
  intro x u y v hu hv
  have hmono := (SetValuedOperator.isMonotone_iff 𝒜).1 h𝒜
  have hu' := (mem_aeL2Lift_iff 𝒜 μ x u).1 hu
  have hv' := (mem_aeL2Lift_iff 𝒜 μ y v).1 hv
  rw [inner_def]
  exact integral_nonneg_of_ae <| by
    filter_upwards [hu', hv', Lp.coeFn_sub x y, Lp.coeFn_sub u v] with ω huω hvω hxyω huvω
    rw [hxyω, huvω]
    exact hmono huω hvω

end SetValuedOperator
