/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib

/-!
Compatibility aliases for the convex-space API that moved under `Convexity` between the
Nesterov source snapshot (`v4.30.0-rc2`) and ReasBook's locked stable `v4.30.0` mathlib revision.
-/

export Convexity (StdSimplex ConvexSpace)

namespace StdSimplex

export Convexity.StdSimplex (map nonempty single)

end StdSimplex

namespace ConvexSpace

abbrev convexCombination := @Convexity.ConvexSpace.sConvexComb

end ConvexSpace

/- The release candidate provided module convex spaces by typeclass inference.  Stable `v4.30.0`
keeps the same construction as `Convexity.ConvexSpace.ofModule`, but deliberately stops making it
a global instance.  The imported source uses the former inference behavior throughout. -/
noncomputable instance legacyModuleConvexSpace
    {R M : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
    [AddCommMonoid M] [Module R M] : ConvexSpace R M :=
  Convexity.ConvexSpace.ofModule

noncomputable instance legacyIsModuleConvexSpace
    {R M : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
    [AddCommMonoid M] [Module R M] : Convexity.IsModuleConvexSpace R M :=
  Convexity.IsModuleConvexSpace.ofModule
