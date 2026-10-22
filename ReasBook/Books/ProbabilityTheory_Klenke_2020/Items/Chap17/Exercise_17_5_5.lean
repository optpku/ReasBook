/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_41

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/- Exercise 17.5.5 is `source-facing`: it recalls from Theorem 17.41 the special function
`modifiedBesselI0`, its defining series, and the owner-level Green-function formula `(17.25)` for
the canonical symmetric simple random walk. The translation-invariant step-matrix theorem is only
a `bridge/view` companion there and is not the main public entry for this exercise. -/

namespace ProbabilityTheory

recall modifiedBesselI0

recall modifiedBesselI0_eq_tsum

recall symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_besselIntegral

end ProbabilityTheory
