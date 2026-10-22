/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_18
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_21

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/- Corollary 7.22: the real `L²(μ)` space with its canonical inner product is a Hilbert space,
expressed directly by the canonical owner type `HilbertSpace ℝ (Lp ℝ 2 μ)` built from
`L2.innerProductSpace` and `MeasureTheory.Lp.instCompleteSpace`. -/
#check (HilbertSpace ℝ (Lp ℝ 2 μ))

end
