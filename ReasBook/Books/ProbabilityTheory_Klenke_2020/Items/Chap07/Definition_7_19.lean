/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (V : Type u) [AddCommGroup V] [Module ℝ V]

/- Definition 7.19: An inner product on a real vector space `V` is modeled by
`InnerProductSpace.Core ℝ V`; over `ℝ`, mathlib's first-argument linearity convention is
equivalent to the textbook second-argument linearity by symmetry. -/
recall InnerProductSpace.Core

/- A positive semidefinite symmetric bilinear form, or semi-inner product, on `V` is modeled by
`PreInnerProductSpace.Core ℝ V`. -/
recall PreInnerProductSpace.Core

end

section

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/- A real Hilbert space structure on `V` is modeled by `HilbertSpace ℝ V`, i.e. by completeness
of the norm coming from the inner product. -/
recall HilbertSpace

end
