/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section

section

universe u v

variable {X : Type u} {Y : Type v}
variable [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- `LocallyLipschitzAt F x` means that `F : X → Y` is Lipschitz on some closed ball centered
at `x`. -/
class LocallyLipschitzAt (F : X → Y) (x : X) : Prop where
  /-- A positive-radius closed ball on which `F` satisfies a Lipschitz condition. -/
  exists_lipschitzOnWith_closedBall :
    ∃ ε : ℝ, (0 : ℝ) < ε ∧ ∃ K : NNReal, LipschitzOnWith K F (Metric.closedBall x ε)

/-- `LocallyLipschitzAt F x` is proposition-valued. -/
instance locallyLipschitzAt_subsingleton (F : X → Y) (x : X) :
    Subsingleton (LocallyLipschitzAt F x) := inferInstance

/-- Unfolding formula for `LocallyLipschitzAt`. -/
theorem locallyLipschitzAt_iff {F : X → Y} {x : X} :
    LocallyLipschitzAt F x ↔
      ∃ ε : ℝ, (0 : ℝ) < ε ∧ ∃ K : NNReal, LipschitzOnWith K F (Metric.closedBall x ε) := by
  constructor
  · intro h
    exact h.exists_lipschitzOnWith_closedBall
  · rintro ⟨ε, hε, K, hK⟩
    exact ⟨ε, hε, K, hK⟩

/-- A concrete Lipschitz bound on a closed ball centered at `x` gives the local Lipschitz
hypothesis at `x`. -/
theorem locallyLipschitzAt_of_closedBall
    {F : X → Y} {x : X} {K : NNReal}
    (h_lipschitz : ∃ ε : ℝ, (0 : ℝ) < ε ∧ LipschitzOnWith K F (Metric.closedBall x ε)) :
    LocallyLipschitzAt F x := by
  rcases h_lipschitz with ⟨ε, hε, hK⟩
  exact ⟨ε, hε, K, hK⟩

end
