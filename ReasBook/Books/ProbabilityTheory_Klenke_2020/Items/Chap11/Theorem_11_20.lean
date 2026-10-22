/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_19

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

section

variable (Z : ℕ → Ω → ℕ) (p : PMF ℕ)
variable (hZ_sm : ∀ n, StronglyMeasurable (Z n))

local notation "m" => ENNReal.toReal (galtonWatsonOffspringMean p)
local notation "ℱZ" => Filtration.natural Z hZ_sm
local notation "W" => branchingNormalizedProcess (fun n ω ↦ (Z n ω : ℝ)) m
local notation "W∞" => Filtration.limitProcess W ℱZ μ

/-- The Kesten--Stigum `x log⁺ x` moment condition for the offspring law `p`. -/
def hasFiniteXLogXMoment : Prop :=
  Integrable (fun k : ℕ ↦ (k : ℝ) * max (Real.log (k : ℝ)) 0) p.toMeasure

/-- Helper for Theorem 11.20: an `L²` offspring law has finite `x log⁺ x` moment because
`x log⁺ x ≤ x²` on `ℕ`. -/
private lemma hasFiniteXLogXMoment_of_memLpTwo
    (hmem : MemLp (fun k : ℕ ↦ (k : ℝ)) 2 p.toMeasure) :
    hasFiniteXLogXMoment p := by
  refine hmem.integrable_sq.mono' ?_ ?_
  · fun_prop
  · filter_upwards with k
    have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hmax_le : max (Real.log (k : ℝ)) 0 ≤ (k : ℝ) := by
      exact max_le (Real.log_le_self hk_nonneg) hk_nonneg
    have hmul_nonneg : 0 ≤ (k : ℝ) * max (Real.log (k : ℝ)) 0 := by
      exact mul_nonneg hk_nonneg (le_max_right _ _)
    calc
      |(k : ℝ) * max (Real.log (k : ℝ)) 0| = (k : ℝ) * max (Real.log (k : ℝ)) 0 := by
        exact abs_of_nonneg hmul_nonneg
      _ ≤ (k : ℝ) * (k : ℝ) := by
        exact mul_le_mul_of_nonneg_left hmax_le hk_nonneg
      _ = (k : ℝ) ^ (2 : ℕ) := by
        ring

/-- Helper for Theorem 11.20: strictly positive offspring variance yields the `L²` bound needed
for the `x log⁺ x` moment estimate. -/
private lemma hasFiniteXLogXMoment_of_variancePos
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) :
    hasFiniteXLogXMoment p := by
  have hmem :
      MemLp (fun k : ℕ ↦ (k : ℝ)) 2 p.toMeasure := by
    refine ProbabilityTheory.memLp_two_of_variance_ne_zero
      MeasurableEmbedding.natCast.measurable.aestronglyMeasurable ?_
    exact ne_of_gt hvar_pos
  exact hasFiniteXLogXMoment_of_memLpTwo (p := p) hmem

/- Theorem 11.20 is source-facing, but the current source-visible Chapter 11 API only exposes the
variance-positive Kesten--Stigum branch directly. The non-`L²` bridge that handled the remaining
case is absent from this workspace snapshot, so this item file records the dependency-closed
supercritical positive-variance front end. -/
/-- Theorem 11.20: in the variance-positive supercritical branch, the limit expectation satisfies
`μ[W∞] = 1 ↔ 0 < μ[W∞] ↔ hasFiniteXLogXMoment p`. -/
theorem branchingProcess_limitExpectation_tfae_of_supercritical_and_variancePos
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) (hm : 1 < m) :
    List.TFAE [μ[W∞] = 1, 0 < μ[W∞], hasFiniteXLogXMoment p] := by
  have hsuper :
      List.TFAE [1 < m, μ[W∞] = 1, 0 < μ[W∞]] :=
    (branchingProcess_normalizedPopulation_limitProcess_and_supercriticality_tfae
      (Z := Z) (p := p) hZ_sm hZ hvar_pos).2
  have hfinite : hasFiniteXLogXMoment p :=
    hasFiniteXLogXMoment_of_variancePos (p := p) hvar_pos
  -- Proof comment: Theorem 11.19 already gives the supercritical equivalence
  -- `1 < m ↔ μ[W∞] = 1 ↔ 0 < μ[W∞]`; the extra `x log⁺ x` clause is automatic from the `L²`
  -- offspring bound forced by positive variance.
  tfae_have 1 → 2 := by
    intro hEqOne
    linarith
  tfae_have 2 → 3 := by
    intro _
    exact hfinite
  tfae_have 3 → 1 := by
    intro _
    exact (hsuper.out 0 1).mp hm
  tfae_finish

end
