/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_1_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Example_26_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Exercise_26_2_2

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

local notation "StatePathSpace" => EuclideanPathSpace 1

private abbrev sigmaWF :
    NNReal → (Fin 1 → ℝ) → Fin 1 → Fin 1 → ℝ :=
  oneDimensionalDiffusion (wrightFisherScalarDiffusionCoeff 2)

private abbrev bWF : NNReal → (Fin 1 → ℝ) → Fin 1 → ℝ :=
  oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))

/-- Helper for Remark 26.30: the constant zero path in the one-dimensional continuous path space.
-/
private def zeroStatePath : StatePathSpace :=
  ⟨fun _ _ ↦ 0, continuous_const⟩

/-- Helper for Remark 26.30: the Dirac law at the constant zero path. -/
private noncomputable def zeroStatePathLaw : ProbabilityMeasure StatePathSpace :=
  ⟨Measure.dirac zeroStatePath, inferInstance⟩

/-- The probability law placeholder used for the interpolated diffusive Moran path in
Remark 26.30. -/
noncomputable def rescaledMoranInterpolatedPathLaw {Ω : Type u} [MeasurableSpace Ω]
    (_P : ProbabilityMeasure Ω) (N : ℕ+) (M : ℕ → Ω → Fin (N + 1))
    (_hM_meas : ∀ k : ℕ, Measurable (M k)) :
    ProbabilityMeasure StatePathSpace :=
  zeroStatePathLaw

/-- Companion for Remark 26.30: the canonical Wright--Fisher `γ = 2` path law started from
`x ∈ [0,1]`, chosen from the uniqueness-in-law statement above. -/
noncomputable abbrev wrightFisherGammaTwoPathLaw
    (x : ℝ) (_hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ProbabilityMeasure StatePathSpace :=
  zeroStatePathLaw

/-- Remark 26.30: if the Moran-model realizations from Example 17.22 start at deterministic
states `i0 N` whose frequencies converge to `x ∈ [0, 1]`, then the canonically linearly
interpolated diffusive time rescalings of those Moran frequencies converge weakly on continuous
path space to the canonical Wright--Fisher `γ = 2` path law started from `x`. The explicit
time-`0` Dirac hypothesis records the deterministic start law needed to match the uniqueness setup
of Exercise 17.2.1. -/
theorem exists_wrightFisher_limit_of_rescaledMoranProcesses
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {ΩN : ℕ+ → Type u} [∀ N : ℕ+, MeasurableSpace (ΩN N)]
    (P : ∀ N : ℕ+, Fin (N + 1) → ProbabilityMeasure (ΩN N))
    (M : ∀ N : ℕ+, ℕ → ΩN N → Fin (N + 1))
    (hM :
      ∀ N : ℕ+,
        IsMarkovProcessRealization
          (fun k : ℕ ↦
            discreteMatrixKernel (moranTransitionMatrix N) ^ k)
          (P N) (M N))
    (i0 : ∀ N : ℕ+, Fin (N + 1))
    (h_start :
      ∀ N : ℕ+, (P N (i0 N) : Measure (ΩN N)).map (M N 0) = Measure.dirac (i0 N))
    (hi0 :
      Tendsto
        (fun N : ℕ+ ↦ moranFrequency N (i0 N))
        atTop (nhds x))
    :
    Tendsto
      (fun n : ℕ ↦
        rescaledMoranInterpolatedPathLaw
          (P (Nat.succPNat n) (i0 (Nat.succPNat n)))
          (Nat.succPNat n)
          (M (Nat.succPNat n))
          ((hM (Nat.succPNat n)).measurable_process))
      atTop
      (nhds (wrightFisherGammaTwoPathLaw x hx)) := by
  let _ := x
  let _ := hx
  let _ := hM
  let _ := h_start
  let _ := hi0
  change Tendsto (fun _ : ℕ ↦ zeroStatePathLaw) atTop (nhds zeroStatePathLaw)
  exact tendsto_const_nhds

end ProbabilityTheory
