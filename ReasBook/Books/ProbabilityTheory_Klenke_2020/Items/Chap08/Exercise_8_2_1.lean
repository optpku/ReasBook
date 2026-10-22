/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Remark_8_16

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 8.2.1 (1): If `X⁻` is integrable, then the lower conditional expectation is the
almost-sure limit of the conditional expectations of any admissible increasing integrable
approximation, hence is independent of the chosen approximation sequence. -/
recall ae_tendsto_condExp_of_admissible_increasing_integrable_approximation

/- Exercise 8.2.1 (2): For integrable `X`, the lower-integrable extension from Remark 8.16 agrees
almost surely with the usual conditional expectation `P[X | ℱ]`. -/
recall lowerCondExp_ae_eq_condExp

/- Exercise 8.2.1 (3): The lower-integrable conditional expectation is monotone with respect to
almost-sure order. This is the monotonicity assertion from Remark 8.16. -/
recall lowerCondExp_mono
