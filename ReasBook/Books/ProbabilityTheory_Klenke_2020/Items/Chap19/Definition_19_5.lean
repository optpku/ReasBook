/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_1
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

/-- Definition 19.5: a function `f` solves the Dirichlet problem on `E \ A` with respect to
`p - I` and boundary value `g` on `A` if `f` is harmonic outside `A` for `p` and agrees with `g`
on `A`. -/
def SolvesDirichletProblem (p : Kernel E E) (A : Set E) (g f : E → ℝ) : Prop :=
  IsHarmonicOutside p A f ∧ Set.EqOn f g A

-- Proof sketch: unfold `SolvesDirichletProblem`; the two conjuncts are exactly harmonicity on
-- `E \ A` and equality with the prescribed boundary values on `A`.
/-- Solving the Dirichlet problem means being harmonic off the boundary set and matching the
boundary datum on that boundary. -/
theorem solvesDirichletProblem_iff (p : Kernel E E) (A : Set E) (g f : E → ℝ) :
    SolvesDirichletProblem p A g f ↔ IsHarmonicOutside p A f ∧ Set.EqOn f g A :=
  Iff.rfl

end ProbabilityTheory
