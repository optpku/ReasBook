/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Definition_8_25

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

universe u v

section DiscreteMatrix

variable {Ω₁ : Type u} {Ω₂ : Type v}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable [DiscreteMeasurableSpace Ω₁]

/-- Example 8.27 (1): For (i), a nonnegative matrix `K` on discrete measurable spaces defines the
kernel `κ(i, ·) = ∑ j, K i j • δ_j`; finite row sums then give finite total mass rowwise. -/
noncomputable def discreteMatrixKernel (K : Ω₁ → Ω₂ → ℝ≥0∞) : Kernel Ω₁ Ω₂ :=
  ⟨fun i ↦ Measure.sum fun j : Ω₂ ↦ K i j • Measure.dirac j, Measurable.of_discrete⟩

-- Proof sketch: `discreteMatrixKernel` is defined rowwise by the countable sum of weighted Dirac
-- masses coming from the matrix entries.
/-- The matrix kernel evaluates to the discrete measure represented by the corresponding row. -/
@[simp]
theorem discreteMatrixKernel_apply (K : Ω₁ → Ω₂ → ℝ≥0∞) (i : Ω₁) :
    discreteMatrixKernel K i = Measure.sum (fun j : Ω₂ ↦ K i j • Measure.dirac j) := rfl

/-- The total mass of the `i`th row of the matrix kernel is the row sum `∑' j, K i j`. -/
theorem discreteMatrixKernel_univ (K : Ω₁ → Ω₂ → ℝ≥0∞) (i : Ω₁) :
    discreteMatrixKernel K i Set.univ = ∑' j, K i j := by
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ MeasurableSet.univ]
  simp

-- Proof sketch: evaluate the row measure on `Set.univ` and identify it with the row sum
-- `∑' j, K i j` coming from the explicit sum of weighted Dirac measures.
/-- Finite row sums make the matrix kernel a finite transition kernel in the sense of
Definition 8.25. -/
theorem discreteMatrixKernel_isFiniteTransitionKernel (K : Ω₁ → Ω₂ → ℝ≥0∞)
    (hrow : ∀ i, (∑' j, K i j) < ∞) :
    IsFiniteTransitionKernel (discreteMatrixKernel K) := by
  exact fun i ↦ by
    refine ⟨?_⟩
    simpa [discreteMatrixKernel_univ] using hrow i

-- Proof sketch: the explicit formula gives `discreteMatrixKernel K i Set.univ = 1` for every `i`,
-- so each row measure is a probability measure.
/-- Unit row sums make the matrix kernel a Markov kernel. -/
theorem discreteMatrixKernel_isMarkovKernel (K : Ω₁ → Ω₂ → ℝ≥0∞)
    (hrow : ∀ i, ∑' j, K i j = 1) :
    IsMarkovKernel (discreteMatrixKernel K) := by
  refine ⟨fun i ↦ ⟨?_⟩⟩
  simpa [discreteMatrixKernel_univ] using hrow i

-- Proof sketch: the total mass of the `i`th row is the row sum `∑' j, K i j`, so the assumed
-- bound by `1` gives the substochastic estimate rowwise.
/-- Row sums bounded by `1` make the matrix kernel sub-Markov. -/
theorem discreteMatrixKernel_isSubMarkovKernel (K : Ω₁ → Ω₂ → ℝ≥0∞)
    (hrow : ∀ i, ∑' j, K i j ≤ 1) :
    IsSubMarkovKernel (discreteMatrixKernel K) := by
  exact fun i ↦ by
    simpa [discreteMatrixKernel_univ] using hrow i

end DiscreteMatrix

section ConstantKernel

variable {Ω₁ : Type u} {Ω₂ : Type v}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

-- Proof sketch: `Kernel.const Ω₁ μ₂` is the constant family with value `μ₂`, and the finiteness
-- of `μ₂` gives the required uniform bound on total mass.
/- Example 8.27 (2): For (ii), a constant family equal to a finite measure defines a finite
transition kernel. This is obtained canonically from the finite-kernel instance on `Kernel.const`
and the bridge theorem `IsFiniteKernel κ → IsFiniteTransitionKernel κ`. -/
theorem isFiniteTransitionKernel_const (μ₂ : Measure Ω₂) [IsFiniteMeasure μ₂] :
    IsFiniteTransitionKernel (Kernel.const Ω₁ μ₂) :=
  isFiniteTransitionKernel_of_isFiniteKernel (Kernel.const Ω₁ μ₂)

end ConstantKernel

section PoissonKernel

-- Proof sketch: for each measurable `A ⊆ ℕ`, the map `x ↦ poissonMeasure x A` is measurable, so
-- the family `x ↦ poissonMeasure x` is measurable as a map into measures.
private theorem measurable_poissonMeasureFamily : Measurable (fun x : NNReal ↦ poissonMeasure x) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  change Measurable (fun x : NNReal ↦ (poissonPMF x).toMeasure s)
  simp_rw [PMF.toMeasure_apply_eq_tsum]
  refine Measurable.ennreal_tsum fun n ↦ ?_
  by_cases hn : n ∈ s
  · simp [Set.indicator_of_mem hn]
    simpa [poissonPMFReal_ofReal_eq_poissonPMF] using
      (show Measurable (fun x : NNReal ↦ ENNReal.ofReal (poissonPMFReal x n)) by
        unfold poissonPMFReal
        fun_prop)
  · simp [Set.indicator_of_notMem hn]

/-- Example 8.27 (3): For (iii), the Poisson laws `x ↦ Poi_x` define a stochastic kernel from
`[0, ∞)` to `ℕ₀`, represented in Lean by a kernel `NNReal → ℕ`. -/
noncomputable def poissonMeasureKernel : Kernel NNReal ℕ :=
  ⟨fun x ↦ poissonMeasure x, measurable_poissonMeasureFamily⟩

/-- The Poisson kernel at `x` is the Poisson measure with parameter `x`. -/
@[simp]
theorem poissonMeasureKernel_apply (x : NNReal) :
    poissonMeasureKernel x = poissonMeasure x := rfl

-- Proof sketch: each value `poissonMeasure x` is a probability measure, so the rowwise
-- probability-measure condition for `IsMarkovKernel` holds for the whole family.
/-- The Poisson family is a Markov kernel. -/
theorem poissonMeasureKernel_isMarkovKernel : IsMarkovKernel poissonMeasureKernel := by
  refine ⟨fun x ↦ ?_⟩
  simpa [poissonMeasureKernel] using (inferInstance : IsProbabilityMeasure (poissonMeasure x))

/-- The Poisson kernel carries the canonical Markov-kernel instance. -/
instance : IsMarkovKernel poissonMeasureKernel :=
  poissonMeasureKernel_isMarkovKernel

end PoissonKernel

section TranslationKernel

/-- Example 8.27 (4): the translated family of an s-finite measure `μ` on `ℝ^n`, modeled in Lean
on `EuclideanSpace ℝ (Fin n)`. For a probability law, this is the textbook kernel
`x ↦ δ_x ∗ μ`. -/
noncomputable def translatedConvolutionKernel (n : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [SFinite μ] :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  let E := EuclideanSpace ℝ (Fin n)
  ((Kernel.id : Kernel E E) ×ₖ Kernel.const E μ).map fun z : E × E ↦ z.1 + z.2

-- Proof sketch: rewrite the translated measure `μ.map (fun y ↦ x + y)` using the standard
-- convolution formula for a Dirac mass on the left.
/-- At `x`, the translation kernel is the convolution of the Dirac mass at `x` with `μ`. -/
theorem translatedConvolutionKernel_apply (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [SFinite μ]
    (x : EuclideanSpace ℝ (Fin n)) :
    translatedConvolutionKernel n μ x = Measure.dirac x ∗ μ := by
  let E := EuclideanSpace ℝ (Fin n)
  change
    (((Kernel.id : Kernel E E) ×ₖ Kernel.const E μ).map fun z : E × E ↦ z.1 + z.2) x =
      Measure.dirac x ∗ μ
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
  rw [Measure.dirac_prod, Measure.map_map (by fun_prop) measurable_prodMk_left]
  simpa [Function.comp_def] using (Measure.dirac_conv x μ).symm

-- Proof sketch: translation preserves total mass, so the pushforward of a probability measure is
-- again a probability measure rowwise.
/-- A probability law on `ℝ^n` induces a Markov kernel by translation. -/
theorem translatedConvolutionKernel_isMarkovKernel (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ] :
    IsMarkovKernel (translatedConvolutionKernel n μ) := by
  let E := EuclideanSpace ℝ (Fin n)
  change IsMarkovKernel
      ((((Kernel.id : Kernel E E) ×ₖ Kernel.const E μ).map fun z : E × E ↦ z.1 + z.2))
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The translation kernel of a probability law carries the canonical Markov-kernel instance. -/
instance (n : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ] :
    IsMarkovKernel (translatedConvolutionKernel n μ) :=
  translatedConvolutionKernel_isMarkovKernel n μ

end TranslationKernel
