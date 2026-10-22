/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Theorem_6_24

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 7.36 is `source-facing`: the Chapter 7 notion
`MeasureTheory.Measure.TotallyContinuous` from Definition 7.35 is compared with the finite-measure
small-set formulation of uniform integrability cited from Theorem 6.24(iii). The
`core/canonical` owner is `MeasureTheory.UniformIntegrable`, and the relevant
`bridge/view` is the owner-centered finite-measure reformulation
`uniformIntegrable_iff_isBounded_and_small_measure_integral_control`; its small-set clause has the
same quantifier pattern as `MeasureTheory.Measure.TotallyContinuous`, while the auxiliary
weight-control package from Chapter 6 stays upstream and out of the public focus here. -/
-- recall uniformIntegrable_iff_isBounded_and_small_measure_integral_control
