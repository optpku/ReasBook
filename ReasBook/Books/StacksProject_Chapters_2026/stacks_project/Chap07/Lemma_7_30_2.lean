module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable (ℱ : Sheaf J (Type w))

/- Domain-style sampling for Lemma 7.30.2:
- primary domain: slice-category sections in a locally cartesian closed topos, specialized to the
  localization slice `Sh(C, J) / ℱ`;
- sampled owner declarations:
  `Over.sections`,
  `Over.toOverSectionsAdj`,
  `forgetAdjToOver`,
  `Over.forgetAdjStar`;
- best owner abstraction: the direct image of the localization at `ℱ` is canonically owned by the
  slice sections functor `Over.sections`, with adjunction `Over.toOverSectionsAdj`; the
  identification of the localization inverse image with `toOver ℱ` is bridge data obtained from
  the two right adjoints to `Over.forget ℱ`;
- primitive data: only the sheaf `ℱ`;
- derived API: `Over.sections`, the adjunction `Over.toOverSectionsAdj`, and the comparison
  isomorphism `toOver ℱ ≅ Over.star ℱ`.

Source/core/bridge triage:
- `source-facing`: the direct-image functor `j_{ℱ,*}` described as the sheaf of local right
  inverses to an object of the slice topos;
- `core/canonical`: `Over.sections` and `Over.toOverSectionsAdj`;
- `bridge/view`: `((Over.forgetAdjStar ℱ).rightAdjointUniq (forgetAdjToOver ℱ)).symm`, which
  identifies the slice inverse-image owner `toOver ℱ` with the localization inverse-image owner
  `Over.star ℱ`.
-/

/- Lemma 7.30.2: in the situation of Lemma 7.30.1, the direct-image functor `j_{ℱ,*}` is obtained
by specializing the canonical slice sections functor `Over.sections`; for an object
`φ : Over ℱ`, this is the sheaf of local right inverses to `φ`, expressed abstractly by the
sections object in the slice category. -/
recall Over.sections

/- Companion recall: the sections functor is canonically right adjoint to `toOver`; this
adjunction is the abstract form of the textbook local-right-inverse construction. -/
recall Over.toOverSectionsAdj

/- Companion bridge: the right-adjoint owner `toOver ℱ` used by `Over.toOverSectionsAdj`
identifies canonically with the localization inverse-image functor `Over.star ℱ`. -/
#check ((Over.forgetAdjStar ℱ).rightAdjointUniq (forgetAdjToOver ℱ)).symm
