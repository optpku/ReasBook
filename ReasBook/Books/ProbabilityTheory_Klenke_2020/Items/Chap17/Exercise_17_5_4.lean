/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_41
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Exercise 17.5.4: once Theorem 17.41 supplies the nonrecurrent branch in dimension `D ≥ 3`,
irreducibility upgrades the canonical lattice walk with step law `ν` to a transient chain. The
public statement is recorded for the lattice step matrix `latticeConvolutionStepMatrix ν`. -/
theorem irreducible_latticeRandomWalk_isTransient {D : ℕ}
    (_hD : 3 ≤ D)
    (ν : PMF (LatticePoint D))
    (P : LatticePoint D → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint D)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (latticeConvolutionStepMatrix ν) ^ n) P X]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint D))
      (discreteMatrixKernel (latticeConvolutionStepMatrix ν))]
    (hnotrec : ¬ IsRecurrentMarkovChain P X) :
    IsTransientMarkovChain (latticeConvolutionStepMatrix ν) P X := by
  have htransient :
      ∀ x : LatticePoint D, IsTransientState P X x := by
    rcases
        irreducibleMarkovChain_recurrent_or_transient_of_discreteMatrixKernel_isIrreducible
          (p := latticeConvolutionStepMatrix ν) (P := P) (X := X) with
      hrec | hstates
    · exact False.elim (hnotrec hrec)
    · exact hstates
  -- Proof comment: the irreducible dichotomy leaves only the transient-state branch once the
  -- recurrent alternative is ruled out, and Definition 17.30 then gives chain transience.
  exact isTransientMarkovChain_of_forall_isTransientState
    (p := latticeConvolutionStepMatrix ν) (P := P) (X := X) htransient

end ProbabilityTheory
