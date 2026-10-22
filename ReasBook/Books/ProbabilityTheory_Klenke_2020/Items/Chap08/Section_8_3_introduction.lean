/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Section 8.3 introduction: the section introduces regular conditional distributions, i.e. the
kernel-valued object assigning to each value `x` of a random variable `X` a probability measure
interpreted as `P[· | X = x]`. -/
recall ProbabilityTheory.condDistrib

/- The section's interpretation of `P[· | X = x]` is governed by the canonical almost-sure
characterization of `condDistrib` by conditional expectation. -/
recall ProbabilityTheory.condDistrib_ae_eq_condExp
