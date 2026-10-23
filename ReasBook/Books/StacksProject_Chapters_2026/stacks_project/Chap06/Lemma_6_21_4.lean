module

public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory TopCat

/- Domain-style sampling for Lemma 6.21.4:
- primary domain: stalks of presheaves under pullback along a continuous map;
- inspected owner declarations:
  `TopCat.Presheaf.stalkPullbackIso`,
  `TopCat.Presheaf.pullback`,
  `TopCat.Presheaf.stalk`,
  `TopCat.Sheaf.stalkPullbackIso`;
- owner abstraction: the canonical owner is `TopCat.Presheaf.stalkPullbackIso`;
- primitive data: a continuous map `f : X ⟶ Y`, a presheaf `𝒢 : Y.Presheaf (Type u)`, and a point
  `x : X`;
- derived API: none in this file beyond the direct recall of the canonical owner.

Source/core/bridge triage:
- `source-facing`: this numbered item is the set-valued specialization of the standard
  stalk-pullback comparison;
- `core/canonical`: `TopCat.Presheaf.stalkPullbackIso`;
- `bridge/view`: the sheaf-level analogue `TopCat.Sheaf.stalkPullbackIso`, treated separately in
  `Lemma_6_21_5`.

Since the textbook statement is exactly the `C := Type u` specialization of the canonical owner,
the refined file should expose that owner directly rather than keep a local wrapper. -/

/- Lemma 6.21.4: for a continuous map `f : X ⟶ Y`, a presheaf of sets `𝒢` on `Y`, and a point
`x : X`, the canonical bijection of stalks `(f_p 𝒢)_x = 𝒢_{f(x)}` is exactly the `Type u`
specialization of the canonical owner `TopCat.Presheaf.stalkPullbackIso`. -/
recall TopCat.Presheaf.stalkPullbackIso

namespace TopCat.Presheaf

section
variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒢 : Y.Presheaf (Type u)) (x : X)

/- Companion specialization of `TopCat.Presheaf.stalkPullbackIso` to set-valued presheaves. -/
#check
  (show 𝒢.stalk (f x) ≅ ((pullback (Type u) f).obj 𝒢).stalk x from
    TopCat.Presheaf.stalkPullbackIso (Type u) f 𝒢 x)

end

end TopCat.Presheaf
