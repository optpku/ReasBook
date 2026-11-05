module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Tactic.Recall
public import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Lemma 4.18.7:
- primary domain: finite colimits in `CategoryTheory.Limits`;
- sampled owner API:
  `HasFiniteColimits`,
  `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts`,
  `hasFiniteColimits_of_hasInitial_and_pushouts`,
  `has_colimits_of_hasCoequalizers_and_coproducts`;
- best owner abstraction: `HasFiniteColimits C`;
- primitive data: no new local primitive data should be introduced here; the source hypotheses are
  exactly the canonical constructor-side typeclasses `HasFiniteCoproducts C`, `HasCoequalizers C`,
  `HasInitial C`, and `HasPushouts C`;
- derived API: the two pairwise `iff` bridges and the textbook `TFAE` packaging below.

Source/core/bridge triage:
- `source-facing`: the two pairwise equivalences and the aggregate `finite_colimits_tfae`;
- `core/canonical`: the owner predicate `HasFiniteColimits C`;
- `bridge/view`: the reformulation of the owner in terms of finite coproducts plus coequalizers, or
  initial object plus pushouts.

There is no upstream theorem already exposing these exact equivalences, so this file should stay a
thin bridge to the canonical mathlib constructors rather than introducing any new wrapper owner. -/

/- Companion recall: the converse directions are already owned by the canonical constructor
theorems below. -/
recall hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
recall hasFiniteColimits_of_hasInitial_and_pushouts

/-- A category has finite coproducts and coequalizers. -/
class HasFiniteCoproductsCoequalizers : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasCoequalizers : HasCoequalizers C]

attribute [instance] HasFiniteCoproductsCoequalizers.hasFiniteCoproducts
attribute [instance] HasFiniteCoproductsCoequalizers.hasCoequalizers

/-- A category has an initial object and pushouts. -/
class HasInitialPushouts : Prop where
  [hasInitial : HasInitial C]
  [hasPushouts : HasPushouts C]

attribute [instance] HasInitialPushouts.hasInitial
attribute [instance] HasInitialPushouts.hasPushouts

/-- A category has finite colimits if and only if it has finite coproducts and coequalizers. -/
theorem finite_colimits_iff_finite_coproducts_and_coequalizers :
    HasFiniteColimits C ↔ HasFiniteCoproductsCoequalizers C := by
  constructor
  · intro h
    letI : HasFiniteColimits C := h
    exact ⟨⟩
  · intro h
    letI : HasFiniteCoproductsCoequalizers C := h
    exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

/-- A category has finite colimits if and only if it has an initial object and pushouts. -/
theorem finite_colimits_iff_initial_and_pushouts :
    HasFiniteColimits C ↔ HasInitialPushouts C := by
  constructor
  · intro h
    letI : HasFiniteColimits C := h
    exact ⟨⟩
  · intro h
    letI : HasInitialPushouts C := h
    exact hasFiniteColimits_of_hasInitial_and_pushouts

/- Lemma 4.18.7 packages the standard source-facing characterizations of `HasFiniteColimits C`:

1. finite colimits;
2. finite coproducts and coequalizers;
3. an initial object and pushouts. -/
/-- Lemma 4.18.7: for a category `C`, the following are equivalent:

1. `C` has finite colimits;
2. `C` has finite coproducts and coequalizers;
3. `C` has an initial object and pushouts. -/
-- Proof sketch: use the two direct bridge equivalences above, whose converse directions are the
-- canonical mathlib constructor theorems
-- `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts` and
-- `hasFiniteColimits_of_hasInitial_and_pushouts`.
theorem finite_colimits_tfae :
    [HasFiniteColimits C, HasFiniteCoproductsCoequalizers C,
      HasInitialPushouts C].TFAE := by
  tfae_have 1 ↔ 2 := finite_colimits_iff_finite_coproducts_and_coequalizers C
  tfae_have 1 ↔ 3 := finite_colimits_iff_initial_and_pushouts C
  tfae_finish

end CategoryTheory.Limits
