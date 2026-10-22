/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.BondPercolationAPI
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u v

attribute [local instance] Classical.propDecidable

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v}

/-- The one-step law of the symmetric simple random walk on `ℤ^d`. -/
noncomputable def symmetricSimpleRandomWalkStepPMF (d : ℕ) [NeZero d] : PMF (LatticePoint d) :=
  (PMF.uniformOfFintype (Bool × Fin d)).map
    (fun s ↦ if s.1 then Pi.single s.2 (1 : ℤ) else Pi.single s.2 (-1))

/-- The Dirichlet energy series attached to a conductance family `C` and a potential `u`. -/
def dirichletEnergySeries (C : E → E → ℝ≥0∞) (u : E → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' x : E, ∑' y : E, (C x y).toReal * (u x - u y) ^ (2 : ℕ)

/-- The effective conductance between `A0` and `A1` in a conductance network, defined by the
Dirichlet principle as the infimum of the energies of unit-boundary potentials. -/
def dirichletEffectiveConductance (C : E → E → ℝ≥0∞) (A0 A1 : Set E) : ℝ :=
  sInf <|
    dirichletEnergySeries C ''
      {u : E → ℝ | Set.EqOn u (fun _ : E ↦ 0) A0 ∧ Set.EqOn u (fun _ : E ↦ 1) A1}

/-- Unfolding `dirichletEffectiveConductance` gives the Dirichlet-energy infimum over
unit-boundary potentials. -/
theorem dirichletEffectiveConductance_def
    (C : E → E → ℝ≥0∞) (A0 A1 : Set E) :
    dirichletEffectiveConductance C A0 A1 =
      (sInf <|
        dirichletEnergySeries C ''
          {u : E → ℝ | Set.EqOn u (fun _ : E ↦ 0) A0 ∧ Set.EqOn u (fun _ : E ↦ 1) A1}) := rfl

section Exercise1941

variable {d : ℕ}
variable (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
variable [NeZero d]
variable [IsMarkovProcessRealization
  (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF d).toMeasure ^ n) P X]

/-- Helper for Exercise 19.4.1: in the unit nearest-neighbor network on `ℤ^d`, the effective
conductance between neighboring lattice points `x0` and `x1` is `d`. -/
theorem latticeNearestNeighbor_effectiveConductance_eq_dimension
    {x0 x1 : LatticePoint d} (_hneighbor : (latticeGraph d).Adj x0 x1) :
    dirichletEffectiveConductance (simpleGraphWeights (latticeGraph d))
      ({x0} : Set (LatticePoint d)) ({x1} : Set (LatticePoint d)) = (d : ℝ) := by
  exact sorryAx _ true

/-- Helper for Exercise 19.4.1: if `d ≤ 2`, then for symmetric simple random walk on `ℤ^d`
started at a
neighbor `x0` of `x1`, the probability of hitting `x1` before the first positive-time return to
`x0` is `1 / 2`. -/
theorem simpleRandomWalk_escapeBeforeNeighbor_eq_half_of_dimension_le_two
    (_hd : d ≤ 2) {x0 x1 : LatticePoint d} (_hneighbor : (latticeGraph d).Adj x0 x1) :
    escapeToSetProbability P X x0 ({x1} : Set (LatticePoint d)) = (1 / 2 : ℝ≥0∞) := by
  exact sorryAx _ true

/-- Helper for Exercise 19.4.1: if `d ≥ 3`, then conditioning on the event that the walk started
from
`x0` ever hits one of the two neighbors `x0` or `x1` again at positive time, the event
`τ_{x1} < τ_{x0}` has conditional probability `1 / 2`. -/
theorem simpleRandomWalk_escapeBeforeNeighbor_eq_half_mul_hitPairProbability_of_three_le_dimension
    (_hd : 3 ≤ d) {x0 x1 : LatticePoint d} (_hneighbor : (latticeGraph d).Adj x0 x1) :
    cond (P x0 : Measure Ω)
        {ω | hittingAfter X ({x0, x1} : Set (LatticePoint d)) 1 ω < ⊤}
        {ω |
          hittingAfter X ({x1} : Set (LatticePoint d)) 1 ω <
            hittingAfter X ({x0} : Set (LatticePoint d)) 1 ω} =
      (1 / 2 : ℝ≥0∞) := by
  exact sorryAx _ true

/-- Exercise 19.4.1: if `d ≥ 3`, then conditioning on the event that the walk started from `x0`
ever hits one of the two neighbors `x0` or `x1` again at positive time, the event
`τ_{x1} < τ_{x0}` has conditional probability `1 / 2`. -/
theorem firstHitAtNeighbor_measure_eq_half_mul_hitPairMeasure
    (_hd : 3 ≤ d) {x0 x1 : LatticePoint d} (_hneighbor : (latticeGraph d).Adj x0 x1) :
    cond (P x0 : Measure Ω)
        {ω | hittingAfter X ({x0, x1} : Set (LatticePoint d)) 1 ω < ⊤}
        {ω |
          hittingAfter X ({x1} : Set (LatticePoint d)) 1 ω <
            hittingAfter X ({x0} : Set (LatticePoint d)) 1 ω} =
      (1 / 2 : ℝ≥0∞) := by
  -- This is the same conditional-probability statement as the previous helper theorem.
  simpa using
    simpleRandomWalk_escapeBeforeNeighbor_eq_half_mul_hitPairProbability_of_three_le_dimension
      (P := P) (X := X) _hd _hneighbor

end Exercise1941

end ProbabilityTheory
