/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 7.2.1: Hölder's inequality for real-valued random variables on a probability space is
the canonical theorem `integral_mul_norm_le_Lp_mul_Lq`. For `ℝ`-valued functions, its norm-based
conclusion is exactly the textbook absolute-value inequality, and mathlib expresses the conjugacy
condition canonically as `p.HolderConjugate q`. -/
recall MeasureTheory.integral_mul_norm_le_Lp_mul_Lq

/- The textbook reciprocal assumption `1 < p` and `p⁻¹ + q⁻¹ = 1` is exactly the canonical
predicate `p.HolderConjugate q`. -/
recall Real.holderConjugate_iff
