/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.Compact

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E]

namespace Set

/-- A feasible set `C` has half-squared-diameter bound `Θ` when every pair of points in `C`
satisfies `(1 / 2) * ‖x - y‖² ≤ Θ`. This is the explicit datum used in the Chapter 8 projected
subgradient rates. -/
def HasHalfSquaredDiameterBound (C : Set E) (Θ : ℝ) : Prop :=
  ∀ ⦃x y : E⦄, x ∈ C → y ∈ C → (1 / 2 : ℝ) * ‖x - y‖ ^ (2 : ℕ) ≤ Θ

/-- Specializing a half-squared-diameter bound to concrete points of `C` gives the displayed
distance estimate. -/
theorem HasHalfSquaredDiameterBound.bound
    {C : Set E} {Θ : ℝ} (hΘ : C.HasHalfSquaredDiameterBound Θ)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    (1 / 2 : ℝ) * ‖x - y‖ ^ (2 : ℕ) ≤ Θ :=
  hΘ hx hy

end Set

-- Proof sketch: the map `(x, y) ↦ (1 / 2 : ℝ) * ‖x - y‖²` is continuous on `E × E`. If `C` is
-- compact, then `C ×ˢ C` is compact as well, so this map is bounded above on `C ×ˢ C`; any such
-- upper bound is the required constant `Θ`.
/-- A compact feasible set admits a finite half-squared-diameter bound. -/
theorem exists_half_squared_diameter_bound_of_isCompact
    (C : Set E) (hC_compact : IsCompact C) :
    ∃ Θ : ℝ, C.HasHalfSquaredDiameterBound Θ := by
  let φ : E × E → ℝ := fun p ↦ (1 / 2 : ℝ) * ‖p.1 - p.2‖ ^ (2 : ℕ)
  have hdiff_cont : Continuous (fun p : E × E ↦ p.1 - p.2) :=
    continuous_fst.sub continuous_snd
  have hφ_cont : Continuous φ := by
    simpa [φ] using continuous_const.mul ((continuous_norm.comp hdiff_cont).pow 2)
  have hφ_on : ContinuousOn φ (C ×ˢ C) := hφ_cont.continuousOn
  obtain ⟨Θ, hΘ⟩ :=
    bddAbove_def.mp (IsCompact.bddAbove_image (hC_compact.prod hC_compact) hφ_on)
  refine ⟨Θ, ?_⟩
  intro x y hx hy
  have hxy : φ (x, y) ∈ φ '' (C ×ˢ C) := by
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  simpa [φ] using hΘ (φ (x, y)) hxy

-- Proof sketch: every optimal point `xStar ∈ XStar` lies in `C` by `hXStar_subset`, while the
-- initial point `x0` is a point of `C` by construction. Apply the half-squared-diameter bound to
-- the pair `((x0 : E), xStar)`.
/-- Any half-squared-diameter bound on `C` controls the initial-distance term to an optimal point,
which is the quantity appearing in projected-subgradient complexity estimates. -/
theorem half_sqdist_to_optimal_point_le_of_half_squared_diameter_bound
    (C XStar : Set E) {Θ : ℝ}
    (hXStar_subset : XStar ⊆ C)
    (hΘ : C.HasHalfSquaredDiameterBound Θ)
    (x0 : C) {xStar : E} (hxStar : xStar ∈ XStar) :
    (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) ≤ Θ :=
  hΘ.bound x0.property (hXStar_subset hxStar)

end
