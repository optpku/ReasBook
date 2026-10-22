/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The unit interval `[0, 1]` viewed as a subtype of `ℝ`. -/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- A family of events indexed by the percolation parameter `p ∈ [0, 1]`, intended to model the
event that the origin belongs to an infinite open cluster at parameter `p`. -/
abbrev OriginInfiniteClusterEvent (Ω : Type u) [MeasurableSpace Ω] := UnitInterval → Set Ω

-- Proof sketch: combine `measureReal_nonneg` with `measureReal_le_one` for the same measurable
-- event under the probability measure `P`.
/-- The real probability of an event under a probability measure belongs to `[0, 1]`. -/
theorem measureReal_mem_unitInterval (P : Measure Ω) [IsProbabilityMeasure P] (s : Set Ω) :
    P.real s ∈ UnitInterval := by
  -- Package the standard lower and upper bounds for probabilities into membership in `[0, 1]`.
  exact ⟨MeasureTheory.measureReal_nonneg, MeasureTheory.measureReal_le_one⟩

/-- The function `p ↦ θ(p)` sending a percolation parameter to the probability that the origin is
in an infinite open cluster. -/
noncomputable def originClusterPercolationProbability
    (P : Measure Ω) [IsProbabilityMeasure P] (originInfiniteClusterEvent : OriginInfiniteClusterEvent Ω) :
    UnitInterval → UnitInterval :=
  fun p ↦ ⟨P.real (originInfiniteClusterEvent p), measureReal_mem_unitInterval P _⟩

-- Proof sketch: unfold `originClusterPercolationProbability`; the function evaluates by definition
-- to the real probability of the event indexed by `p`.
/-- The origin-cluster percolation probability at `p` is the real probability of the corresponding
infinite-cluster event. -/
theorem originClusterPercolationProbability_apply
    (P : Measure Ω) [IsProbabilityMeasure P]
    (originInfiniteClusterEvent : OriginInfiniteClusterEvent Ω) (p : UnitInterval) :
    originClusterPercolationProbability P originInfiniteClusterEvent p =
      ⟨P.real (originInfiniteClusterEvent p), measureReal_mem_unitInterval P _⟩ := by
  -- Unfolding the definition shows that the probability map evaluates to this subtype element.
  rfl

-- Proof sketch: if `p ≤ q`, the monotonicity hypothesis gives
-- `originInfiniteClusterEvent p ⊆ originInfiniteClusterEvent q`; then apply monotonicity of
-- `P.real` with respect to set inclusion and package the resulting inequality in the subtype
-- order on `[0, 1]`.
/-- Theorem 2.42: the map `p ↦ θ(p)`, where `θ(p)` is the probability that the origin belongs to
an infinite open cluster, is monotone increasing on `[0, 1]`. -/
theorem originClusterPercolationProbability_monotone
    (P : Measure Ω) [IsProbabilityMeasure P]
    (originInfiniteClusterEvent : OriginInfiniteClusterEvent Ω)
    (hmono : Monotone originInfiniteClusterEvent) :
    Monotone (originClusterPercolationProbability P originInfiniteClusterEvent) := by
  intro p q hp
  -- The monotonicity hypothesis turns `p ≤ q` into inclusion of the underlying events.
  -- After unfolding `θ`, monotonicity of `P.real` on nested sets closes the goal.
  show P.real (originInfiniteClusterEvent p) ≤ P.real (originInfiniteClusterEvent q)
  exact MeasureTheory.measureReal_mono (hmono hp)
