/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω}
variable {μ : Measure Ω} {ℱ : Filtration ℕ m0}

section

variable {X : ℕ → Ω → ℝ}

local notation "squareProcess" => fun n ω ↦ (X n ω) ^ 2

-- Proof sketch: the predictable part is the cumulative sum of the conditional expectations of the
-- increments of the squared process. Since `(X_n^2)` is a submartingale, those conditional
-- expected increments are almost surely nonnegative, so the predictable part is almost surely
-- monotone increasing in time.
/-- Remark 10.5: in the setting of Example 10.2, if the squared process `(X_n^2)` is a
submartingale, then its predictable part is almost everywhere monotone increasing in time. This is
the textbook increasing process associated with the squared process. -/
theorem square_process_predictablePart_mono_ae
    (hXsq : Submartingale squareProcess ℱ μ) :
    ∀ᵐ ω ∂μ, Monotone (fun n ↦ predictablePart squareProcess ℱ μ n ω) :=
  submartingale_ae_monotone_predictablePart hXsq

end
