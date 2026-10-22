/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_58
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_61

-- Declarations for this item will be appended below by the statement pipeline.

namespace SetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: Remark 20.62 records the converse Fitzpatrick contact-set descriptions of a
  maximally monotone operator.
- `core/canonical`: the owner declarations are
  `Maximal.eq_pairingEqualityOperator_conjugateTranspose_fitzpatrickFunction` and
  `Maximal.graph_eq_setOf_fitzpatrickFunction_eq_inner`, built from
  `Maximal IsMonotone A`, the Fitzpatrick owner `F[A]`, and the pairing-contact owner
  `pairingEqualityOperator`.
- `bridge/view`: the lower-bound recalls are the companion hypotheses matching the two inequality
  inputs in Theorem 20.46, not new owners.

Primitive data: maximal monotonicity `Maximal IsMonotone A` together with the canonical Fitzpatrick
owner `F[A]`.
Derived API: the contact-set graph equality and the recovered pairing-equality operator. -/

/- Remark 20.62: Proposition 20.58 and Proposition 20.61 recover a maximally monotone operator
from the Fitzpatrick contact-set descriptions, giving converses to the canonical
pairing-equality-operator construction of Theorem 20.46. -/
recall Maximal.eq_pairingEqualityOperator_conjugateTranspose_fitzpatrickFunction

/- Companion recall: Proposition 20.58 identifies the graph with the Fitzpatrick contact set. -/
recall Maximal.graph_eq_setOf_fitzpatrickFunction_eq_inner

/- Companion recall: Proposition 20.58 also supplies the Fitzpatrick lower bound hypothesis used
in Theorem 20.46. -/
recall Maximal.inner_le_fitzpatrickFunction

/- Companion recall: Proposition 20.61 supplies the swapped-conjugate lower bound hypothesis from
Theorem 20.46. -/
recall inner_le_conjugate_fitzpatrickFunction_swap

/- Companion recall: Proposition 20.61 also identifies the graph with the contact set of the
transposed Fenchel conjugate. -/
recall Maximal.graph_eq_setOf_conjugate_fitzpatrickFunction_eq_inner

end SetValuedOperator
