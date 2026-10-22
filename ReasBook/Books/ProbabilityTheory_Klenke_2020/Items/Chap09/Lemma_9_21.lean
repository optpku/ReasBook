/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/- Lemma 9.21: if `σ` and `τ` are stopping times with `σ ≤ τ`, then the stopping-time
σ-algebra `𝓕_σ` is contained in `𝓕_τ`; in mathlib this is the canonical monotonicity theorem for
`IsStoppingTime.measurableSpace`. -/
recall IsStoppingTime.measurableSpace_mono
