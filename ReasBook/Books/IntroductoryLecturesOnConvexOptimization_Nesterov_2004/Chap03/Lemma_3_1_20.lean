/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_20

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProduct
open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Lemma 3.1.20 lies in the chapter's centered-ellipsoid / support-value domain.

Sampled owner-style declarations:
- `affineEllipsoid` in `Lemma_3_2_7`, the chapter owner for the textbook ellipsoid `E(H, x̄)`;
- `isGreatest_inner_image_spdEllipsoid` in `Lemma_3_20`, the exact maximum-attainment theorem on
  that owner ellipsoid;
- `IsGreatest.csSup_eq`, the generic order-theoretic bridge from an explicit maximum statement to
  the corresponding supremum equality.

Best owner abstraction:
- source-facing/core owner: `isGreatest_inner_image_spdEllipsoid`;
- bridge/view: `hmax.csSup_eq`.

Primitive data:
- `A : Mat` with `hA : A.PosDef`;
- `c : E`.

Derived API:
- the centered ellipsoid `affineEllipsoid A⁻¹ 0`;
- the image set `((fun x : E ↦ inner ℝ c x) '' affineEllipsoid A⁻¹ 0)`;
- the companion supremum equality supplied canonically by `hmax.csSup_eq`.

Source/core/bridge triage:
- source-facing: the textbook maximum of `⟪c, x⟫` over the centered ellipsoid;
- core/canonical: the earlier owner theorem `isGreatest_inner_image_spdEllipsoid`;
- bridge/view: the generic companion `IsGreatest.csSup_eq`.

This file is recall-only: once `Lemma_3_20` is stated directly on the chapter ellipsoid owner,
there is no reason to keep a second theorem name with the exact same interface.
-/

recall isGreatest_inner_image_spdEllipsoid
    (A : Mat) (hA : A.PosDef) (c : E) :
    IsGreatest ((fun x : E ↦ inner ℝ c x) '' E(A⁻¹, (0 : E)))
      (Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c)))

/-
The supremum reformulation of Lemma 3.1.20 is the generic companion consequence of the
maximum-attainment statement
`isGreatest_inner_image_spdEllipsoid`. -/
section

variable {A : Mat} {c : E}

local notation "E₀" => E(A⁻¹, (0 : E))
local notation "supportImage" => (fun x : E ↦ inner ℝ c x) '' E₀
local notation "supportMax" => Real.sqrt (inner ℝ c ((Matrix.toEuclideanLin A⁻¹) c))

variable (hmax : IsGreatest supportImage supportMax)

/- The supremum reformulation is not a second source-facing theorem: it is the generic
order-theoretic companion `hmax.csSup_eq`. -/
#check hmax.csSup_eq

end

end
