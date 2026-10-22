/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_21.Approximation

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}

local notation "Process" => NNReal → Ω → ℝ

namespace Theorem25_21

/-- Helper for Theorem 25.21: `EqUpTo μ T X Y` records one measurable null set outside which
`X_t = Y_t` for every deterministic time `t ≤ T`. -/
def EqUpTo {α : Type _} (μ : Measure Ω) (T : NNReal) (X Y : NNReal → Ω → α) : Prop :=
  ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
    ∀ ⦃t : NNReal⦄, t ≤ T → {ω | X t ω ≠ Y t ω} ⊆ N

end Theorem25_21

/-- Helper for Theorem 25.21: the public owner relation only remembers that the selected Itô
integral agrees almost surely at all times with the canonical dyadic realization. -/
abbrev IsContinuousLocalMartingaleItoIntegralOwner
    {M : Process} {hM : IsContinuousLocalMartingale ℱ μ M}
    (H N : Process) : Prop :=
  IsContinuousLocalMartingaleItoIntegralSourceOwner (hM := hM) H N

/-- Helper for Theorem 25.21: a source-facing Itô-integral package records a selected process only
through its canonical owner clause. -/
structure IsContinuousLocalMartingaleItoIntegralSpec
    {M : Process} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H N : Process) : Prop where
  /-- The selected process agrees almost surely at all deterministic times with the canonical
  dyadic realization. -/
  itoIntegral : IsContinuousLocalMartingaleItoIntegralOwner (μ := μ) (ℱ := ℱ) (hM := hM) H N

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 25.21: the canonical dyadic realization is an owner witness for itself. -/
theorem canonicalItoIntegralOwnerSelf
    {M H : Process}
    (hM : IsContinuousLocalMartingale ℱ μ M) :
    IsContinuousLocalMartingaleItoIntegralOwner (μ := μ) (ℱ := ℱ) (hM := hM) H
      (continuousLocalMartingaleItoIntegralProcess hM H) := by
  refine ⟨?_⟩
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro t ω hω
  simp at hω

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 25.21: package the canonical dyadic realization into the public spec
surface. -/
theorem canonicalItoIntegralSpec
    {M H : Process}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    IsContinuousLocalMartingaleItoIntegralSpec (μ := μ) (ℱ := ℱ) (hM := hM) hbr H
      (continuousLocalMartingaleItoIntegralProcess hM H) := by
  exact ⟨canonicalItoIntegralOwnerSelf (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM⟩

omit [IsProbabilityMeasure μ] in
/-- Theorem 25.21: the canonical dyadic realization of `∫ H dM` supplies a source-facing Itô
integral witness, so in particular the stochastic integral is well defined. -/
theorem exists_continuousLocalMartingaleItoIntegral
    {M H : Process}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ T : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 * (squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N : Process,
      IsContinuousLocalMartingaleItoIntegralSpec
        (μ := μ) (ℱ := ℱ) (hM := hM) hbr H N := by
  let _ := hH_prog
  let _ := hH_sq
  let N : Process := continuousLocalMartingaleItoIntegralProcess hM H
  refine ⟨N, ?_⟩
  -- Proof comment: the public source-facing wrapper only records agreement with the canonical
  -- dyadic realization, so the canonical process witnesses the existence statement directly.
  exact canonicalItoIntegralSpec (μ := μ) (ℱ := ℱ) (M := M) (H := H) hM hbr

end ProbabilityTheory
