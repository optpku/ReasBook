module

public import Mathlib.CategoryTheory.Limits.Final.Connected
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe uI uJ uC vI vJ vC

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable [IsConnected I]

/-
Source/core/bridge triage for Lemma 4.17.6:
- `source-facing`: the colimit-existence comparison, together with the resulting canonical
  colimit comparison isomorphism, for pulling a diagram back along `Prod.snd I J`.
- `core/canonical`: `Functor.Final.hasColimit_comp_iff` and `Functor.Final.colimitIso`.
- `bridge/view`: the instance `CategoryTheory.final_snd`, obtained from `[IsConnected I]`.

Primary domain-style sampling:
- project owner recall: `Functor.Final.hasColimit_comp_iff` in `Lemma_4_17_2`;
- project source-facing bridge from explicit finality criteria:
  `Functor.final_of_connected_fibers_and_hom_lifts` in `Lemma_4_17_5`;
- mathlib owner theorem: `Functor.Final.hasColimit_comp_iff` in
  `Mathlib/CategoryTheory/Limits/Final.lean`;
- mathlib bridge/view instance: `final_snd` in
  `Mathlib/CategoryTheory/Limits/Final/Connected.lean`.
-/

/- Companion recall: if `I` is connected, then the second projection `Prod.snd I J : I × J ⥤ J`
is final. -/
recall final_snd

section

variable (M : J ⥤ C)

/- Lemma 4.17.6: if `I` is connected, then for a diagram `M : J ⥤ C` the colimit of `M` exists
if and only if the colimit of its pullback along the second projection `Prod.snd I J : I × J ⥤ J`
exists. This is exactly the specialized owner theorem `Functor.Final.hasColimit_comp_iff` for the
final functor `Prod.snd I J`; the companion entry below records the resulting canonical colimit
comparison isomorphism. -/
#check (Functor.Final.hasColimit_comp_iff (Prod.snd I J) :
  HasColimit (Prod.snd I J ⋙ M) ↔ HasColimit M)

/- The corresponding colimit comparison isomorphism is exactly the specialized owner declaration
`Functor.Final.colimitIso` for `Prod.snd I J`. -/
variable [HasColimit M]

#check (Functor.Final.colimitIso (Prod.snd I J) M :
  colimit (Prod.snd I J ⋙ M) ≅ colimit M)

end

end CategoryTheory
