/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

-- Semantic recall note: the requested domain-sampling pass identified mathlib's canonical gauge
-- owners directly: `gauge_nonneg`, `gauge_smul_of_nonneg`, and `gauge_add_le`.

/- Lemma 6.14 is a `core/canonical` recall in the Minkowski-gauge domain.

Primitive data: the owner object is mathlib's `gauge`.
Derived API: nonnegativity, positive homogeneity, and subadditivity are already exposed by the
canonical owner theorems `gauge_nonneg`, `gauge_smul_of_nonneg`, and `gauge_add_le`.

The former file-level declarations were only specialized restatements over `Fin n → ℝ`, with the
source hypotheses `IsClosed K`, `Convex ℝ K`, and `0 ∈ interior K` either unused or only serving
to derive the canonical `Absorbent ℝ K` input required upstream. This file therefore recalls the
owner declarations directly instead of keeping parallel local wrappers. -/
recall gauge_nonneg
recall gauge_smul_of_nonneg
recall gauge_add_le
