/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Definition_8_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Finset MeasurableEquiv Preorder
open scoped ENNReal

universe u

variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]

private theorem partialTraj_isSubMarkov
    (κ : (n : ℕ) → Kernel (Π i : Iic n, Ω i) (Ω (n + 1)))
    (hκ : ∀ n, IsSubMarkovKernel (κ n)) (a b : ℕ) :
    IsSubMarkovKernel (partialTraj κ a b) := by
  letI : ∀ n, IsFiniteKernel (κ n) := fun n ↦ (hκ n).isFiniteKernel
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base =>
        rw [partialTraj_self]
        exact isSubMarkovKernel_of_isMarkovKernel Kernel.id
    | succ k hak hk =>
        rw [partialTraj_succ_of_le hak]
        exact IsSubMarkovKernel.map
          (IsSubMarkovKernel.comp
            (IsSubMarkovKernel.id_prod
              (IsSubMarkovKernel.map (hκ k) (piSingleton k).measurable))
            hk)
          measurable_IicProdIoc
  · rw [partialTraj_le hba]
    exact isSubMarkovKernel_of_isMarkovKernel _

-- Proof sketch: first show the owner kernel `partialTraj κ 0 n` is substochastic by induction on
-- `n`, using the recursive `partialTraj_succ_of_le` description together with stability under
-- `Kernel.map`, `Kernel.comp`, and the deterministic product `Kernel.id ×ₖ _`. Then transport this
-- property through the final `Kernel.map`/`Kernel.comap` bridge that forgets time `0`.
/-- If every stage kernel is substochastic, then the finite-step kernel obtained from
`partialTraj κ 0 n` by forgetting time `0` and identifying `Π i : Iic 0, Ω i` with `Ω 0` is
substochastic. -/
theorem iteratedCompProdKernel_isSubMarkov
    (κ : (n : ℕ) → Kernel (Π i : Iic n, Ω i) (Ω (n + 1)))
    (hκ : ∀ n, IsSubMarkovKernel (κ n)) (n : ℕ) :
    IsSubMarkovKernel
      ((Kernel.comap
          ((partialTraj κ 0 n).map (restrict₂ Ioc_subset_Iic_self))
          ((piUnique (fun i : Iic 0 ↦ Ω i)).symm)
          (piUnique (fun i : Iic 0 ↦ Ω i)).symm.measurable :
        Kernel (Ω 0) (Π i : Ioc 0 n, Ω i))) := by
  let f : (Π i : Iic n, Ω i) → Π i : Ioc 0 n, Ω i := restrict₂ Ioc_subset_Iic_self
  let e : Ω 0 ≃ᵐ Π i : Iic 0, Ω i := (piUnique (fun i : Iic 0 ↦ Ω i)).symm
  have hf : Measurable f := measurable_restrict₂ Ioc_subset_Iic_self
  exact IsSubMarkovKernel.comap
    (IsSubMarkovKernel.map (partialTraj_isSubMarkov κ hκ 0 n) hf)
    e.measurable

-- Proof sketch: use the `IsMarkovKernel` instance on `Kernel.partialTraj κ 0 n` and note that both
-- forgetting the initial coordinate and identifying `Π i : Iic 0, Ω i` with `Ω 0` preserve the
-- Markov property through `Kernel.map` and `Kernel.comap`.
/-- If every stage kernel is stochastic, then the finite-step kernel obtained from
`partialTraj κ 0 n` by forgetting time `0` and identifying `Π i : Iic 0, Ω i` with `Ω 0` is
stochastic. -/
theorem iteratedCompProdKernel_isMarkov
    (κ : (n : ℕ) → Kernel (Π i : Iic n, Ω i) (Ω (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    IsMarkovKernel
      ((Kernel.comap
          ((partialTraj κ 0 n).map (restrict₂ Ioc_subset_Iic_self))
          ((piUnique (fun i : Iic 0 ↦ Ω i)).symm)
          (piUnique (fun i : Iic 0 ↦ Ω i)).symm.measurable :
        Kernel (Ω 0) (Π i : Ioc 0 n, Ω i))) := by
  let f : (Π i : Iic n, Ω i) → Π i : Ioc 0 n, Ω i := restrict₂ Ioc_subset_Iic_self
  let e : Ω 0 ≃ᵐ Π i : Iic 0, Ω i := (piUnique (fun i : Iic 0 ↦ Ω i)).symm
  have hf : Measurable f := measurable_restrict₂ Ioc_subset_Iic_self
  letI : IsMarkovKernel ((partialTraj κ 0 n).map f) := Kernel.IsMarkovKernel.map _ hf
  simpa [f] using
    (Kernel.IsMarkovKernel.comap ((partialTraj κ 0 n).map f) e.measurable)

-- Proof sketch: `IsSubMarkovKernel` gives the canonical owner class `IsFiniteKernel` with uniform
-- bound `1`, so `partialTraj κ 0 n` is finite by the owner instance from mathlib. Compose this
-- with the pushforward of the initial finite measure along the measurable equivalence
-- `Π i : Iic 0, Ω i ≃ᵐ Ω 0`.
/-- The measure obtained from a finite initial law and the recursive finite product of
substochastic kernels is finite on the product space `∏_{0 ≤ j ≤ n} Ω j`. -/
theorem iteratedTrajectoryMeasure_isFinite
    (μ : Measure (Ω 0)) [IsFiniteMeasure μ]
    (κ : (n : ℕ) → Kernel (Π i : Iic n, Ω i) (Ω (n + 1)))
    (hκ : ∀ n, IsSubMarkovKernel (κ n)) (n : ℕ) :
    IsFiniteMeasure (partialTraj κ 0 n ∘ₘ μ.map (piUnique _).symm) := by
  letI : ∀ m, IsFiniteKernel (κ m) := fun m ↦ (hκ m).isFiniteKernel
  let e : Ω 0 ≃ᵐ Π i : Iic 0, Ω i := (piUnique (fun i : Iic 0 ↦ Ω i)).symm
  let μ0 : Measure (Π i : Iic 0, Ω i) := μ.map e
  change IsFiniteMeasure (partialTraj κ 0 n ∘ₘ μ0)
  letI : IsFiniteMeasure μ0 := by
    simpa [μ0] using (Measure.isFiniteMeasure_map μ e)
  infer_instance

/-
Proof sketch: the pushforward of a probability measure along a measurable equivalence is still a
probability measure, and `partialTraj κ 0 n` is Markov when every stage kernel is Markov; then
`Measure.comp` preserves probability measures.
-/
/-- The measure obtained from a probability law and stochastic stage kernels is again a probability
measure on the finite product space `∏_{0 ≤ j ≤ n} Ω j`. -/
theorem iteratedTrajectoryMeasure_isProbability
    (μ : Measure (Ω 0)) [IsProbabilityMeasure μ]
    (κ : (n : ℕ) → Kernel (Π i : Iic n, Ω i) (Ω (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    IsProbabilityMeasure (partialTraj κ 0 n ∘ₘ μ.map (piUnique _).symm) := by
  let e : Ω 0 ≃ᵐ Π i : Iic 0, Ω i := (piUnique (fun i : Iic 0 ↦ Ω i)).symm
  let μ0 : Measure (Π i : Iic 0, Ω i) := μ.map e
  change IsProbabilityMeasure (partialTraj κ 0 n ∘ₘ μ0)
  letI : IsProbabilityMeasure μ0 := by
    simpa [μ0] using Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  infer_instance

end
