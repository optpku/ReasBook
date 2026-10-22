/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_43

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

/- Lemma 15.44 is `bridge/view`: the owner theorem is
`lindeberg_feller_central_limit_theorem`, and this file records only its null-array projection.
The primitive data are the array `A` together with the Lindeberg hypothesis; centering is derived
from `A.SatisfiesLindebergCondition μ` and should not remain a separate public assumption. -/
recall lindeberg_feller_central_limit_theorem

-- Proof sketch: obtain the centered instance from the Lindeberg hypothesis, apply Theorem 15.43,
-- and project to the null-array conclusion.
/-- Lemma 15.44: if the Lindeberg condition in Theorem 15.43 (i) holds for an independent centered
and normed real random-variable array, then the array is null. -/
theorem isNull_of_satisfiesLindebergCondition
    (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    [A.IsIndependent μ] [A.IsNormed μ]
    (h_lindeberg : A.SatisfiesLindebergCondition μ) :
    A.IsNull μ :=
  by
    letI : A.IsCentered μ := h_lindeberg.toIsCentered
    exact ((lindeberg_feller_central_limit_theorem A μ).1 h_lindeberg).1

end RealRandomVariableArray
