/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v w

namespace ProbabilityTheory

section Evaluation

variable {E : Type u}

/-- The finite-dimensional evaluation map of a process at the time tuple `times`. -/
def finiteDimensionalEvaluation {Ω : Type*} (X : NNReal → Ω → E) {k : ℕ}
    (times : Fin k → NNReal) : Ω → Fin k → E :=
  fun ω i ↦ X (times i) ω

/-- The ordered evaluation along `times` factors through the canonical restriction-law owner on
the finite set of times appearing in the tuple. -/
theorem finiteDimensionalEvaluation_eq_restrict_comp {Ω : Type*}
    (X : NNReal → Ω → E) {k : ℕ} (times : Fin k → NNReal) :
    finiteDimensionalEvaluation X times =
      (fun x : (Finset.univ.image times) → E ↦
        fun i ↦ x ⟨times i, Finset.mem_image_of_mem times (Finset.mem_univ i)⟩) ∘
        fun ω ↦ (Finset.univ.image times).restrict (X · ω) := by
  funext ω i
  simp [finiteDimensionalEvaluation]

/-- The ordered tuple law along `times` is the pushforward of the canonical restriction law by the
map that remembers tuple order and repetitions. -/
theorem map_finiteDimensionalEvaluation_eq_map_map_restrict {Ω : Type*}
    [MeasurableSpace E] [MeasurableSpace Ω] (μ : Measure Ω) (X : NNReal → Ω → E)
    (hX : ∀ t, AEMeasurable (X t) μ) {k : ℕ} (times : Fin k → NNReal) :
    μ.map (finiteDimensionalEvaluation X times) =
      (μ.map (fun ω ↦ (Finset.univ.image times).restrict (X · ω))).map
        (fun x : (Finset.univ.image times) → E ↦
          fun i ↦ x ⟨times i, Finset.mem_image_of_mem times (Finset.mem_univ i)⟩) := by
  rw [finiteDimensionalEvaluation_eq_restrict_comp]
  symm
  refine AEMeasurable.map_map_of_aemeasurable ?_ ?_
  · exact (by
      fun_prop :
        Measurable (fun x : (Finset.univ.image times) → E ↦
          fun i ↦ x ⟨times i, Finset.mem_image_of_mem times (Finset.mem_univ i)⟩)).aemeasurable
  · exact aemeasurable_pi_lambda _ fun t ↦ hX t

end Evaluation

section Convergence

variable {E : Type u} [TopologicalSpace E] [SecondCountableTopology E]
variable [MeasurableSpace E] [OpensMeasurableSpace E]
variable {Ω : ℕ → Type v} [∀ n : ℕ, MeasurableSpace (Ω n)]
variable {Ω' : Type w} [MeasurableSpace Ω']

/-- Definition 21.35: the finite-dimensional distributions of a sequence of processes `Xn`
converge to those of `X` if, for every finite family of times in `[0, ∞)`, the corresponding
ordered tuple laws converge in distribution. This is the source-facing ordered-tuple
specialization of the canonical restriction-law owner
`P.map (fun ω ↦ J.restrict (X · ω))`. -/
def tendstoFiniteDimensionalDistributions
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n)) (ν : ProbabilityMeasure Ω')
    (Xn : (n : ℕ) → NNReal → Ω n → E) (X : NNReal → Ω' → E) : Prop :=
  ∀ k : ℕ, ∀ times : Fin k → NNReal,
    TendstoInDistribution
      (fun n ↦ finiteDimensionalEvaluation (Xn n) times) atTop
      (finiteDimensionalEvaluation X times)
      (fun n ↦ (μ n : Measure (Ω n))) (ν : Measure Ω')

scoped notation:50 "(" μ ", " Xn ")" " ⟶[fdd] " "(" ν ", " X ")" =>
  tendstoFiniteDimensionalDistributions μ ν Xn X

/-- Finite-dimensional-distribution convergence yields convergence in distribution of each fixed
finite time tuple. -/
theorem tendstoInDistribution_of_tendstoFiniteDimensionalDistributions
    {μ : (n : ℕ) → ProbabilityMeasure (Ω n)} {ν : ProbabilityMeasure Ω'}
    {Xn : (n : ℕ) → NNReal → Ω n → E} {X : NNReal → Ω' → E}
    (h : (μ, Xn) ⟶[fdd] (ν, X)) {k : ℕ} (times : Fin k → NNReal) :
    TendstoInDistribution
      (fun n ↦ finiteDimensionalEvaluation (Xn n) times) atTop
      (finiteDimensionalEvaluation X times)
      (fun n ↦ (μ n : Measure (Ω n))) (ν : Measure Ω') :=
  h k times

end Convergence

end ProbabilityTheory
