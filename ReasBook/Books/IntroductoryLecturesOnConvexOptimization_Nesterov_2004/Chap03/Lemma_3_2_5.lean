/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_8

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.2.5 lies in the chapter's ellipsoid-method localization-containment domain.

Primary domain:
- ellipsoid-method cutting-plane recursions and the containment of the retained localization sets
  inside the ambient ellipsoid sequence.

Sampled owner-style declarations:
- `localizationSets` in `Definition_3_52`, the source-facing recursive retained-region family;
- `GeneralCuttingPlaneScheme.localizationSets_subset_localizer` in `Algorithm_3_6`, the core
  containment theorem for any cutting-plane localizer;
- `EllipsoidMethod.toGeneralCuttingPlaneScheme` in `Algorithm_3_8`, the bridge from the ellipsoid
  recursion to the cutting-plane owner abstraction;
- `EllipsoidMethod.localizationSets_subset_associatedEllipsoid` in `Algorithm_3_8`, the exact
  ellipsoid-method containment theorem.

Best owner abstraction:
- source-facing: the ellipsoid-method localization sets and associated ellipsoid sequence;
- core/canonical: `GeneralCuttingPlaneScheme.localizationSets_subset_localizer`;
- bridge/view: `EllipsoidMethod.localizationSets_subset_associatedEllipsoid`.

Primitive data:
- the ambient convex minimization problem with separation oracle;
- the initial center and radius;
- the definedness, initial-cover, and positive-definiteness hypotheses for the ellipsoid
  recursion.

Derived API:
- the canonical query/cut localization sets of the ellipsoid recursion;
- the associated ellipsoid sequence;
- the source-facing containment theorem recalled below.

The previous file kept an arbitrary induction shell on unrelated sequences `S`, `Ell`, and `i`.
That shell was not the chapter owner abstraction, and the exact source-facing ellipsoid-method
statement already exists upstream. This item is therefore recall-only and keeps the canonical
bridge theorem as its public center.
-/

recall EllipsoidMethod.localizationSets_subset_associatedEllipsoid
