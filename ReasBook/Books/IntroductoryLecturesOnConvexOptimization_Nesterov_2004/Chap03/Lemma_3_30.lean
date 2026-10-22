/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_53

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open EllipsoidMethod

attribute [local instance] Classical.decPred

/- Lemma 3.30 lies in the chapter's ellipsoid-method localization-containment domain.

Mandatory domain-style sampling before refinement:
- `feasibleSubsequence` and
  `feasibleSubsequence_count_eq_self_of_feasible` in `Definition_3_53`, the chapter owners for
  the source-facing feasible subsequence and counter `i(k)`;
- `localizationSets` in `Definition_3_52`, the source-facing recursive retained-region family;
- `GeneralCuttingPlaneScheme.selectedLocalizationSets_subset_localizer` in `Algorithm_3_6`, the
  canonical selected-feasible containment theorem for any cutting-plane localizer;
- `EllipsoidMethod.toGeneralCuttingPlaneScheme` in `Algorithm_3_8`, the bridge from the
  ellipsoid recursion to the generic cutting-plane owner;
- `EllipsoidMethod.associatedEllipsoid` in `Algorithm_3_8`, the ellipsoid localizer supplied by
  that bridge.

Best owner abstraction:
- source-facing: the selected-feasible localization stage
  `S_(i(k)) = localizationSets Q (feasibleSubsequence Q y)`
  `(problem.oracle ∘ feasibleSubsequence Q y) (i(k))`;
- core/canonical: `GeneralCuttingPlaneScheme.selectedLocalizationSets_subset_localizer`;
- bridge/view: the theorem below, which specializes that owner theorem to ellipsoids through
  `toGeneralCuttingPlaneScheme`.

Primitive data:
- the ambient convex minimization problem with separation oracle;
- the initial center and radius;
- the standard ellipsoid hypotheses `1 < n`, nonzero cut directions, initial ellipsoid cover, and
  positive definiteness of the shape matrices.

Derived API:
- the raw ellipsoid center sequence `y_k = center problem initialCenter radius k`;
- the feasible subsequence `feasibleSubsequence problem.feasibleSet y`;
- the selected feasible counter
  `i(k) = Nat.count (fun j ↦ y j ∈ problem.feasibleSet) k`;
- the associated ellipsoid sequence `E_k`;
- the ellipsoid specialization of the generic selected-stage containment theorem.

The previous version still owned this result at the ellipsoid layer. But the induction only uses
the generic cutting-plane localizer step, the oracle's infeasible-point half-space containment,
`feasibleSubsequence`, and `Nat.count`. This refinement therefore moves the actual owner theorem
to `GeneralCuttingPlaneScheme` and keeps Lemma 3.30 as the ellipsoid specialization through
`toGeneralCuttingPlaneScheme`: the selected localization set `S_(i(k))` built from feasible
queried centers still lies in the raw stage-`k` ellipsoid `E_k`.
-/

namespace EllipsoidMethod

section

/-- Lemma 3.30: let `y_k = center problem initialCenter radius k` be the ellipsoid-method query
sequence, let `i(k) = Nat.count (fun j ↦ y j ∈ problem.feasibleSet) k` be the canonical
selected-feasible counter from Definition 3.53, and let
`X = feasibleSubsequence problem.feasibleSet y` be the corresponding feasible subsequence. Then
the selected recursive localization stage `S_(i(k))` built from the feasible queried centers and
their oracle cuts is contained in the raw stage-`k` associated ellipsoid `E_k`. -/
theorem selectedLocalizationSets_subset_associatedEllipsoid
    (problem : ConvexMinimizationWithSeparationOracle (EuclideanSpace ℝ (Fin n)))
    (initialCenter : E) (radius : ℝ)
    (hn : 1 < n)
    (hcut_nonzero : ∀ k : ℕ, cuttingVector problem initialCenter radius k ≠ 0)
    (hE0_cover :
      problem.feasibleSet ⊆ associatedEllipsoid problem initialCenter radius 0)
    (hshape_pos : ∀ k : ℕ, (shape problem initialCenter radius k).PosDef)
    (k : ℕ) :
    let y : ℕ → E := center problem initialCenter radius
    let X : ℕ → E := feasibleSubsequence problem.feasibleSet y
    let S : ℕ → Set E := localizationSets problem.feasibleSet X (problem.oracle ∘ X)
    let i : ℕ → ℕ := Nat.count (fun j ↦ y j ∈ problem.feasibleSet)
    S (i k) ⊆ associatedEllipsoid problem initialCenter radius k := by
  -- View the ellipsoid recursion as the canonical cutting-plane scheme from Algorithm 3.8.
  let scheme :=
    toGeneralCuttingPlaneScheme problem initialCenter radius hn hcut_nonzero hE0_cover hshape_pos
  -- Specialize the generic selected-localization containment theorem to this ellipsoid scheme.
  simpa [scheme, toGeneralCuttingPlaneScheme] using
    scheme.selectedLocalizationSets_subset_localizer k

end

end EllipsoidMethod
