/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_74
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_26

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {k : ℕ}

/-
Definition 3.78 is a recall-only specialization in the chapter's sampled constrained
max-affine-model / threshold domain over a real inner-product space. The textbook `ℝⁿ` case is
recovered by instantiating `E := EuclideanSpace ℝ (Fin n)`.

Primary domain:
- sampled affine lower models for a constrained parametric max-objective and the resulting
  infimum of feasible upper bounds.

Relevant owner declarations sampled before refining:
- `sampledAffineMinorant` and `sampledAffineMinorant_apply` in `Chap03/Proposition_3_26`, the
  chapter owner for one sampled affine minorant and its pointwise formula;
- `LagrangianProblem.constrainedAuxiliaryObjective` in `Chap02/Lemma_2_21`, the earlier
  project owner for max-violation auxiliary objectives;
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the project owners for
  finite pointwise maxima and their evaluation;
- `setConstrainedParametricObjective` and `setConstrainedParametricObjective_apply`, already
  recalled in `Chap03/Definition_3_74`, the chapter owner for
  `x ↦ max (hatModel x - t) (checkModel x)`;
- `constrainedThreshold` and `constrainedThreshold_def` in `Chap03/Lemma_3_3_4`, the chapter
  owner for the infimum of feasible upper bounds `t`.

Best owner abstractions:
- `hatModel = maxTypeObjective hatMinorantFn`;
- `checkModel = maxTypeObjective checkMinorantFn`;
- `setConstrainedParametricObjective hatModel checkModel`;
- `constrainedThreshold Q hatFn checkFn () ()`.

Primitive data:
- the feasible set `Q`;
- the sampled points `x₀, …, x_k`;
- the sampled affine minorants `sampledAffineMinorant (x_j) (g_j) (f (x_j))` and
  `sampledAffineMinorant (x_j) (ḡ_j) (fBar (x_j))`.

Derived API:
- the sampled upper model `hatModel`;
- the sampled constraint model `checkModel`;
- the source-facing feasible-pair condition on `(x, t)`;
- the auxiliary threshold as the owner specialization above.

Source/core/bridge triage:
- source-facing: the sampled affine inequality system in `(x, t)` and the infimum of feasible
  upper bounds `t`;
- core/canonical: `maxTypeObjective`, `setConstrainedParametricObjective`, and
  `constrainedThreshold`;
- bridge/view: the two specialized `show ... from by ...` checks below.

Because the sampled affine data here are indexed by `Fin (k + 1)`, the exact owner for the model
families is `maxTypeObjective` applied to the canonical affine-map pieces
`sampledAffineMinorant ...`; no noncanonical extension to an `ℕ`-sequence is introduced merely to
reuse `nonsmoothModel`. The owner surface is kept at the ambient-generic real inner-product space
level because the construction only uses affine minorants and the pairing `inner ℝ`; the sampled
minorant owner already works over the weaker ambient layer `SeminormedAddCommGroup E`, so the
file does not keep the stronger standalone `NormedAddCommGroup` binder.

Definition 3.78 adds no new owner object beyond these sampled specializations, so this file keeps
no parallel public wrappers such as `sampledConstrainedAuxiliaryProblem`,
`sampledConstrainedAuxiliaryThreshold`, or named `_iff` companions.
-/

section

variable (Q : Set E)
variable (f fBar : E → ℝ)
variable (xSample gSample gBarSample : Fin (k + 1) → E)

local notation "hatMinorant" =>
  fun j : Fin (k + 1) ↦
    sampledAffineMinorant (xSample j) (gSample j) (f (xSample j))

local notation "checkMinorant" =>
  fun j : Fin (k + 1) ↦
    sampledAffineMinorant (xSample j) (gBarSample j) (fBar (xSample j))

local notation "hatMinorantFn" =>
  fun j : Fin (k + 1) ↦ (hatMinorant j : E → ℝ)

local notation "checkMinorantFn" =>
  fun j : Fin (k + 1) ↦ (checkMinorant j : E → ℝ)

local notation "hatModel" =>
  maxTypeObjective hatMinorantFn

local notation "checkModel" =>
  maxTypeObjective checkMinorantFn

local notation "hatFn" =>
  fun _ : Unit ↦ fun _ : Unit ↦ hatModel

local notation "checkFn" =>
  fun _ : Unit ↦ fun _ : Unit ↦ checkModel

/- Definition 3.78: at fixed sampled affine models, the auxiliary slice
`x ↦ max (hatModel x - t) (checkModel x)` is the direct owner specialization below. -/
#check (setConstrainedParametricObjective hatModel checkModel : ℝ → E → ℝ)

section

variable {Q f fBar xSample gSample gBarSample}
variable {x : E} {t : ℝ}

/- The owner nonpositivity condition is exactly the textbook sampled affine inequality system. -/
#check
  (show
      x ∈ Q ∧ setConstrainedParametricObjective hatModel checkModel t x ≤ 0 ↔
        x ∈ Q ∧
          (∀ j : Fin (k + 1),
            f (xSample j) + inner ℝ (gSample j) (x - xSample j) ≤ t) ∧
          ∀ j : Fin (k + 1),
            fBar (xSample j) + inner ℝ (gBarSample j) (x - xSample j) ≤ 0 from
    by
      rw [setConstrainedParametricObjective_apply, max_le_iff]
      constructor
      · rintro ⟨hxQ, hhat, hcheck⟩
        refine ⟨hxQ, ?_, ?_⟩
        · have hhat' : hatModel x ≤ t := by
            simpa [sub_le_iff_le_add, zero_add] using hhat
          simpa using (maxTypeObjective_le_iff hatMinorantFn x t).1 hhat'
        · simpa using (maxTypeObjective_le_iff checkMinorantFn x (0 : ℝ)).1 hcheck
      · rintro ⟨hxQ, hhat, hcheck⟩
        refine ⟨hxQ, ?_, ?_⟩
        · have hhat' : hatModel x ≤ t :=
            (maxTypeObjective_le_iff hatMinorantFn x t).2 <|
              by simpa using hhat
          simpa [sub_le_iff_le_add, zero_add] using hhat'
        · exact
            (maxTypeObjective_le_iff checkMinorantFn x (0 : ℝ)).2 <|
              by simpa using hcheck
  )

end

/- Definition 3.78: the auxiliary threshold is the direct sampled specialization of the chapter
owner `constrainedThreshold`. -/
#check (constrainedThreshold Q hatFn checkFn () () : EReal)

/- Unfolding the owner threshold recovers the textbook infimum of feasible upper bounds for the
sampled affine models of `f` and `fBar`. -/
#check
  (show
      constrainedThreshold Q hatFn checkFn () () =
        sInf (((↑) : ℝ → EReal) ''
          {t : ℝ | ∃ x ∈ Q,
            (∀ j : Fin (k + 1),
              f (xSample j) + inner ℝ (gSample j) (x - xSample j) ≤ t) ∧
            ∀ j : Fin (k + 1),
              fBar (xSample j) + inner ℝ (gBarSample j) (x - xSample j) ≤ 0}) from
    by
      rw [constrainedThreshold_def]
      refine congrArg sInf ?_
      ext u
      constructor
      · rintro ⟨t, ⟨x, hxQ, hhat, hcheck⟩, rfl⟩
        refine ⟨t, ⟨x, hxQ, ?_, ?_⟩, rfl⟩
        · simpa using (maxTypeObjective_le_iff hatMinorantFn x t).1 hhat
        · simpa using (maxTypeObjective_le_iff checkMinorantFn x (0 : ℝ)).1 hcheck
      · rintro ⟨t, ⟨x, hxQ, hhat, hcheck⟩, rfl⟩
        refine ⟨t, ⟨x, hxQ, ?_, ?_⟩, rfl⟩
        · exact
            (maxTypeObjective_le_iff hatMinorantFn x t).2 <|
              by simpa using hhat
        · exact
            (maxTypeObjective_le_iff checkMinorantFn x (0 : ℝ)).2 <|
              by simpa using hcheck
  )

end

end
