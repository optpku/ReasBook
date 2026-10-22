/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

-- Proof sketch: `hp` upgrades the source-facing stochastic matrix `p` to the owner abstraction
-- `IsMarkovKernel (discreteMatrixKernel p)` via `discreteMatrixKernel_isMarkovKernel`. Then apply
-- `isMarkovProcessRealization_of_oneStepKernel` to the path space `ℕ → E` and the canonical
-- coordinate process `Function.eval`; the hypothesis `hstep` is exactly the required one-step
-- conditional law.
/-- Theorem 17.17 (1): if `P x` is the path-space law on `E^ℕ` started from `x` whose canonical
coordinate process has one-step transition matrix `p`, then the canonical process is the discrete
Markov chain with transition matrix `p`. -/
theorem canonicalProcess_isMarkovProcessRealization_of_stochasticMatrix
    (p : E → E → ENNReal) (hp : IsStochasticMatrix p)
    (P : E → ProbabilityMeasure (ℕ → E))
    (hstart : ∀ x : E, (P x : Measure (ℕ → E)).map (Function.eval 0) = Measure.dirac x)
    (hstep :
      ∀ x : E, ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ n : ℕ,
        (P x)⟦Function.eval (n + 1) ⁻¹' A | generatedFiltrationSpace Function.eval n⟧ =ᵐ[
            (P x : Measure (ℕ → E))]
          fun ω ↦ ((discreteMatrixKernel p) (Function.eval n ω)).real A) :
    IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P Function.eval := by
  let _ : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hp
  -- Proof comment: once the stochastic matrix is packaged as a one-step Markov kernel, the
  -- owner theorem from Theorem 17.11 upgrades the given start law and one-step conditional law
  -- to the full realization statement for the canonical coordinates.
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := discreteMatrixKernel p)
    (P := P)
    (X := Function.eval)
    (hmeas := fun n ↦ measurable_pi_apply n)
    (hstart := hstart)
    (hstep := hstep)

section

variable {Ω : Type v} [MeasurableSpace Ω]
variable {Ω' : Type w} [MeasurableSpace Ω']

-- Proof sketch: apply `finiteDimensionalDistribution_eq_of_sameSemigroup` to the common semigroup
-- `n ↦ discreteMatrixKernel p ^ n`; this identifies all ordered finite-dimensional distributions
-- of realizations with the same transition matrix.
/-- Theorem 17.17 (2): in particular, a stochastic matrix determines the finite-dimensional
distributions of a discrete Markov chain uniquely. -/
theorem finiteDimensionalDistribution_eq_of_same_stochasticMatrix
    (p : E → E → ENNReal)
    {P : E → ProbabilityMeasure Ω} {Q : E → ProbabilityMeasure Ω'}
    {X : ℕ → Ω → E} {Y : ℕ → Ω' → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) Q Y]
    (x : E) {n : ℕ} (times : Fin (n + 1) → ℕ)
    (h_zero : times 0 = 0) (htimes : StrictMono times) :
    (P x : Measure Ω).map (fun ω i ↦ X (times i) ω) =
      (Q x : Measure Ω').map (fun ω i ↦ Y (times i) ω) := by
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  have hMarkovKernel : IsMarkovKernel (discreteMatrixKernel p) := by
    -- Proof comment: any realization of the kernel powers already carries the semigroup data, so
    -- evaluating that semigroup at time `1` recovers the required one-step Markov-kernel
    -- instance.
    simpa using hReal.semigroup.isMarkovKernel 1
  let _ : IsMarkovKernel (discreteMatrixKernel p) := hMarkovKernel
  -- Proof comment: Theorem 17.11 already proves uniqueness of finite-dimensional distributions
  -- for realizations sharing the same one-step kernel, so we specialize it to
  -- `discreteMatrixKernel p`.
  simpa using
    (ProbabilityTheory.finiteDimensionalDistribution_eq_of_same_oneStepKernel
      (κ₁ := discreteMatrixKernel p)
      (P := P) (Q := Q) (X := X) (Y := Y)
      x times h_zero htimes)

end

end ProbabilityTheory
