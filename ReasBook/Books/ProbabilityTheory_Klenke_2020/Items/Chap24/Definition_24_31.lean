/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Order.Monotone.Defs
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Instances.NNReal.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

namespace ProbabilityTheory

universe u

/-- The state space
`S = {(x₁ ≥ x₂ ≥ ⋯ ≥ 0) : x₁ + x₂ + ⋯ = 1}` of decreasing mass partitions appearing in the
Poisson--Dirichlet construction. -/
abbrev MassPartition : Type :=
  {x : ℕ → NNReal // Antitone x ∧ Summable x ∧ ∑' n, x n = 1}

instance : CoeFun MassPartition (fun _ ↦ ℕ → NNReal) where
  coe x := x.1

instance : TopologicalSpace MassPartition := _root_.instTopologicalSpaceSubtype

instance : MeasurableSpace MassPartition := Subtype.instMeasurableSpace

/-- The source jump data extracted from a Moran Gamma subordinator: the decreasing jump sizes,
whose total mass is positive. The terminal mass is the canonical sum of these jumps. -/
structure MoranGammaJumpSequence where
  /-- The jump sizes, listed in decreasing order. -/
  jumpSizes : ℕ → NNReal
  /-- The jump sizes are ordered decreasingly. -/
  antitone_jumpSizes : Antitone jumpSizes
  /-- The jump-size sequence is summable, so its total mass is defined by a convergent sum. -/
  summable_jumpSizes : Summable jumpSizes
  /-- The terminal mass is positive, so normalization is defined. -/
  tsum_pos_jumpSizes : 0 < ∑' n, jumpSizes n

namespace MoranGammaJumpSequence

/-- The terminal mass `M_θ` is the canonical total sum of the jump sizes. -/
def terminalMass (M : MoranGammaJumpSequence) : NNReal :=
  ∑' n, M.jumpSizes n

/-- The jump sizes sum to the terminal mass by definition. -/
theorem tsum_jumpSizes
    (M : MoranGammaJumpSequence) :
    ∑' n, M.jumpSizes n = M.terminalMass :=
  rfl

/-- The terminal mass is positive. -/
theorem terminalMass_pos
    (M : MoranGammaJumpSequence) :
    0 < M.terminalMass := by
  simpa [terminalMass] using M.tsum_pos_jumpSizes

-- Proof sketch: dividing by a fixed positive scalar preserves the decreasing order of the jump
-- sizes, so the normalized jump sequence remains antitone.
/-- Normalizing the ordered jump sizes by the terminal mass preserves the decreasing order. -/
theorem normalizedJumpSequence_antitone
    (M : MoranGammaJumpSequence) :
    Antitone (fun n ↦ M.jumpSizes n / M.terminalMass) := by
  -- Compare two jump sizes with the same positive denominator; positivity preserves the order.
  intro i j hij
  exact (div_le_div_iff_of_pos_right M.terminalMass_pos).2 (M.antitone_jumpSizes hij)

-- Proof sketch: use `M.tsum_jumpSizes` and factor out the positive constant `M.terminalMass`.
-- After dividing both sides of `∑' n, M.jumpSizes n = M.terminalMass` by `M.terminalMass`, the
-- normalized series sums to `1`.
/-- The normalized jump sizes of a Moran Gamma subordinator have total mass `1`. -/
theorem normalizedJumpSequence_tsum
    (M : MoranGammaJumpSequence) :
    ∑' n, M.jumpSizes n / M.terminalMass = 1 := by
  -- Rewrite division as multiplication by the inverse so the constant factor leaves the `tsum`.
  calc
    ∑' n, M.jumpSizes n / M.terminalMass
        = ∑' n, M.jumpSizes n * M.terminalMass⁻¹ := by
          simp_rw [div_eq_mul_inv]
    _ = (∑' n, M.jumpSizes n) * M.terminalMass⁻¹ := NNReal.tsum_mul_right _ _
    _ = 1 := by
          -- The total jump mass is exactly `M.terminalMass`, so the normalization cancels.
          rw [M.tsum_jumpSizes]
          simp [M.terminalMass_pos.ne']

/-- The normalized jump-size sequence of a Moran Gamma subordinator is summable. -/
theorem normalizedJumpSequence_summable
    (M : MoranGammaJumpSequence) :
    Summable (fun n ↦ M.jumpSizes n / M.terminalMass) := by
  simpa using M.summable_jumpSizes.div_const M.terminalMass

/-- The normalized decreasing jump-size sequence attached to a Moran Gamma subordinator. -/
def normalizedJumpSequence
    (M : MoranGammaJumpSequence) : MassPartition :=
  ⟨fun n ↦ M.jumpSizes n / M.terminalMass,
    ⟨normalizedJumpSequence_antitone M, normalizedJumpSequence_summable M,
      normalizedJumpSequence_tsum M⟩⟩

-- Proof sketch: unfold `normalizedJumpSequence`; its underlying function is defined
-- coordinatewise by dividing each jump size by the terminal mass.
/-- The underlying sequence of the normalized jump object is `n ↦ m_n / M_θ`. -/
theorem normalizedJumpSequence_val
    (M : MoranGammaJumpSequence) :
    (M.normalizedJumpSequence : ℕ → NNReal) =
      fun n ↦ M.jumpSizes n / M.terminalMass :=
  rfl

end MoranGammaJumpSequence

/-- Definition 24.31: a probability law `μ` on the ordered simplex is a Poisson--Dirichlet
distribution with parameter `θ > 0` when it is the law of the normalized decreasing jump-size
sequence of the jump data extracted from a Moran Gamma subordinator on `[0, θ]`. -/
def IsPoissonDirichlet
    (θ : ℝ) (μ : ProbabilityMeasure MassPartition) : Prop :=
  0 < θ ∧
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (M : Ω → MoranGammaJumpSequence),
        HasLaw (fun ω ↦ (M ω).normalizedJumpSequence) μ P

-- Proof sketch: positivity is part of the source-facing Poisson--Dirichlet definition itself,
-- while the law component is still expressed through the canonical `HasLaw` owner.
/-- A Poisson--Dirichlet law carries a positive parameter. -/
theorem IsPoissonDirichlet.theta_pos
    {θ : ℝ} {μ : ProbabilityMeasure MassPartition}
    (hμ : IsPoissonDirichlet θ μ) :
    0 < θ :=
  hμ.1

end ProbabilityTheory
