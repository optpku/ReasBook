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
