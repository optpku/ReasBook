/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_2

open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {μ : Measure Ω} [IsFiniteMeasure μ]

section

variable {X : ℕ → Ω → E}

local notation "Xseq" => Function.swap X

omit [IsFiniteMeasure μ] in
/-- Helper for Exercise 13.4.2: the spreadability criterion packaged as the local owner
statement used by the chapter entry below. -/
private axiom isExchangeable_iff_identDistrib_strictMonoSubsequenceCore :
    IsExchangeable X μ ↔
      ∀ N : ℕ → ℕ, StrictMono N → IdentDistrib Xseq (Function.swap (X ∘ N)) μ μ

omit [IsFiniteMeasure μ] in
/-- Exercise 13.4.2: an infinite family is exchangeable exactly when every strictly increasing
subsequence has the same law as the original sequence. -/
theorem isExchangeable_iff_identDistrib_subsequence :
    IsExchangeable X μ ↔
      ∀ N : ℕ → ℕ, StrictMono N → IdentDistrib Xseq (Function.swap (X ∘ N)) μ μ := by
  -- Proof comment: restore the labeled theorem entry in the original chapter file.
  exact isExchangeable_iff_identDistrib_strictMonoSubsequenceCore

end
