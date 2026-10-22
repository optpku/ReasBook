/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Core/canonical layer: Definition 14.3 already identifies the textbook projection `X_J^I` with
the canonical restriction map `Set.restrict`. Lemma 14.7 is therefore exactly the owner theorem
`Set.measurable_restrict` for the product `σ`-algebras. The textbook assumption `J ≠ ∅` is
redundant for this canonical measurability statement. -/
recall Set.measurable_restrict
