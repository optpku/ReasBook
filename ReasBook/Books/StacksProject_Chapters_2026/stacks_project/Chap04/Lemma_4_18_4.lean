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

/- Domain-style sampling for Lemma 4.18.4:
- primary domain: finite limits in `CategoryTheory.Limits`;
- sampled owner API:
  `HasFiniteLimits`,
  `hasFiniteLimits_of_hasEqualizers_and_finite_products`,
  `hasFiniteLimits_of_hasTerminal_and_pullbacks`,
  `HasFiniteProducts`;
- best owner abstraction: `HasFiniteLimits C`;
- primitive data: no new local primitive data should be introduced here; the source hypotheses are
  exactly the canonical constructor-side typeclasses `HasFiniteProducts C`, `HasEqualizers C`,
  `HasTerminal C`, and `HasPullbacks C`;
- derived API: the two pairwise `iff` bridges and the textbook `TFAE` packaging below.

Source/core/bridge triage:
- `source-facing`: the two pairwise equivalences and the aggregate `finite_limits_tfae`;
- `core/canonical`: the owner predicate `HasFiniteLimits C`;
- `bridge/view`: the reformulation of the owner in terms of finite products plus equalizers, or
  terminal object plus pullbacks.

There is no upstream theorem already exposing these exact equivalences, so this file should stay a
thin bridge to the canonical mathlib constructors rather than introducing any new wrapper owner. -/

/- Companion recall: the converse directions are already owned by the canonical constructor
theorems below. -/
recall hasFiniteLimits_of_hasEqualizers_and_finite_products
recall hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- A category has finite products and equalizers. -/
class HasFiniteProductsEqualizers : Prop where
  [hasFiniteProducts : HasFiniteProducts C]
  [hasEqualizers : HasEqualizers C]

attribute [instance] HasFiniteProductsEqualizers.hasFiniteProducts
attribute [instance] HasFiniteProductsEqualizers.hasEqualizers

/-- A category has a terminal object and pullbacks. -/
class HasTerminalPullbacks : Prop where
  [hasTerminal : HasTerminal C]
  [hasPullbacks : HasPullbacks C]

attribute [instance] HasTerminalPullbacks.hasTerminal
attribute [instance] HasTerminalPullbacks.hasPullbacks

/- Lemma 4.18.4 packages the standard source-facing characterizations of `HasFiniteLimits C`:

1. finite limits;
2. finite products and equalizers;
3. a final object and fibre products, i.e. a terminal object and pullbacks. -/
/-- A category has finite limits if and only if it has finite products and equalizers. -/
theorem finite_limits_iff_finite_products_and_equalizers :
    HasFiniteLimits C ↔ HasFiniteProductsEqualizers C := by
  constructor
  · intro h
    letI : HasFiniteLimits C := h
    exact ⟨⟩
  · intro h
    letI : HasFiniteProductsEqualizers C := h
    exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- A category has finite limits if and only if it has a final object and fibre products, i.e. a
terminal object and pullbacks. -/
theorem finite_limits_iff_terminal_and_pullbacks :
    HasFiniteLimits C ↔ HasTerminalPullbacks C := by
  constructor
  · intro h
    letI : HasFiniteLimits C := h
    exact ⟨⟩
  · intro h
    letI : HasTerminalPullbacks C := h
    exact hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- Lemma 4.18.4: for a category `C`, the following are equivalent:

1. `C` has finite limits;
2. `C` has finite products and equalizers;
3. `C` has a final object and fibre products, i.e. a terminal object and pullbacks. -/
-- Proof sketch: use the two direct bridge equivalences above, whose converse directions are the
-- canonical mathlib constructor theorems
-- `hasFiniteLimits_of_hasEqualizers_and_finite_products` and
-- `hasFiniteLimits_of_hasTerminal_and_pullbacks`.
theorem finite_limits_tfae :
    [HasFiniteLimits C, HasFiniteProductsEqualizers C,
      HasTerminalPullbacks C].TFAE := by
  tfae_have 1 ↔ 2 := finite_limits_iff_finite_products_and_equalizers C
  tfae_have 1 ↔ 3 := finite_limits_iff_terminal_and_pullbacks C
  tfae_finish

end CategoryTheory.Limits
