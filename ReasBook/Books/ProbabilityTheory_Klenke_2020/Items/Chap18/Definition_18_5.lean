/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Filter
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/-- A bivariate process with values in `E × E` is a Markov coupling for the transition matrix `p`
if each coordinate process is a Markov chain with transition matrix `p` under every starting law
`P (x, y)`. -/
class IsMarkovCoupling (p : E → E → ℝ≥0∞) (P : E × E → ProbabilityMeasure Ω)
    (Z : ℕ → Ω → E × E) : Prop where
  /-- For each fixed `y`, the first coordinate process realizes the kernel semigroup
  `n ↦ discreteMatrixKernel p ^ n`. -/
  fst_realization : ∀ y : E,
    IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n)
      (fun x ↦ P (x, y)) (fun n ω ↦ (Z n ω).1)
  /-- For each fixed `x`, the second coordinate process realizes the kernel semigroup
  `n ↦ discreteMatrixKernel p ^ n`. -/
  snd_realization : ∀ x : E,
    IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n)
      (fun y ↦ P (x, y)) (fun n ω ↦ (Z n ω).2)

/-- Definition 18.5: a coupling is successful if it is a Markov coupling for `p` and, started
from any pair `(x, y)`, the tail probability of ever seeing unequal coordinates again tends to
zero as the tail index tends to infinity. -/
class IsSuccessfulMarkovCoupling (p : E → E → ℝ≥0∞)
    (P : E × E → ProbabilityMeasure Ω) (Z : ℕ → Ω → E × E) : Prop
    extends IsMarkovCoupling p P Z where
  /-- The probability of a future disagreement after time `n` tends to zero for every initial
  pair `(x, y)`. -/
  tail_disagreement_tendsto_zero : ∀ x y : E,
    Tendsto
      (fun n ↦
        (P (x, y) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}))
      atTop (nhds 0)

/-- The transition matrix `p` admits a successful coupling if some measurable probability space
supports a successful Markov coupling for `p`. -/
class HasSuccessfulCoupling (p : E → E → ℝ≥0∞) : Prop where
  exists_successfulCoupling :
    ∃ (Ω : Type v) (_ : MeasurableSpace Ω) (P : E × E → ProbabilityMeasure Ω)
      (Z : ℕ → Ω → E × E), IsSuccessfulMarkovCoupling p P Z

end ProbabilityTheory
