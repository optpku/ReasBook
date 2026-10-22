/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u v

/- Definition 1.47(1): a map between metric spaces is Lipschitz continuous with constant `β`
when it is formalized by the canonical predicate `LipschitzWith β T`. -/
recall LipschitzWith

/-- Definition 1.47(2): `T` is locally Lipschitz continuous near `x` iff it is Lipschitz on
some positive-radius ball centered at `x`. The neighborhood formulation on the left is the one
used by the canonical predicate `LocallyLipschitz`. -/
theorem locallyLipschitzNear_iff_exists_lipschitzOnWith_ball {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] {T : X → Y} {x : X} :
    (∃ β : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith β T s) ↔
      ∃ ρ > 0, ∃ β : NNReal, LipschitzOnWith β T (Metric.ball x ρ) := by
  constructor
  · rintro ⟨β, s, hs, hT⟩
    rcases Metric.mem_nhds_iff.mp hs with ⟨ρ, hρ, hball⟩
    exact ⟨ρ, hρ, β, hT.mono hball⟩
  · rintro ⟨ρ, hρ, β, hT⟩
    exact ⟨β, Metric.ball x ρ, Metric.ball_mem_nhds x hρ, hT⟩

/- Definition 1.47(3) specialized to the whole space is the canonical predicate
`LocallyLipschitz T`. -/
recall LocallyLipschitz

/-- Definition 1.47(3): `T` is locally Lipschitz continuous on `C` iff every point of `C`
admits a positive-radius ambient ball on which `T` is Lipschitz. -/
theorem locallyLipschitzOnSet_iff_forall_mem_exists_lipschitzOnWith_ball {X : Type u}
    {Y : Type v} [MetricSpace X] [MetricSpace Y] {C : Set X} {T : X → Y} :
    (∀ x ∈ C, ∃ β : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith β T s) ↔
      ∀ x ∈ C, ∃ ρ > 0, ∃ β : NNReal, LipschitzOnWith β T (Metric.ball x ρ) := by
  constructor
  · intro h x hx
    exact locallyLipschitzNear_iff_exists_lipschitzOnWith_ball.mp (h x hx)
  · intro h x hx
    exact locallyLipschitzNear_iff_exists_lipschitzOnWith_ball.mpr (h x hx)

/-- In metric spaces, a map is locally Lipschitz iff each point has a positive-radius ball on
which the map is Lipschitz with some constant. -/
theorem locallyLipschitz_iff_forall_exists_lipschitzOnWith_ball {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] {T : X → Y} :
    LocallyLipschitz T ↔
      ∀ x, ∃ ρ > 0, ∃ β : NNReal, LipschitzOnWith β T (Metric.ball x ρ) := by
  simp [LocallyLipschitz, locallyLipschitzNear_iff_exists_lipschitzOnWith_ball]

/- Definition 1.47(4): Lipschitz continuity relative to `C` with constant `β` is the canonical
predicate `LipschitzOnWith β T C`. -/
recall LipschitzOnWith
