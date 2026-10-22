/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_74

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- This item lies in the chapter's scalar parametric max-objective / value-function domain.

Primary domain:
- set-constrained scalar max-type model-value functions specialized to sampled upper/lower models.

Relevant owner declarations sampled before refining:
- `LagrangianProblem.constrainedAuxiliaryObjective` in `Chap02/Lemma_2_21`, the earlier project
  owner shape for finite max-type constrained objectives;
- `parametricValueFunction`, already recalled in `Chap03/Definition_3_74` from the earlier
  chapter owner file `Chap03/Lemma_3_3_6`;
- `parametricValueFunction_def`, likewise recalled in `Chap03/Definition_3_74` as the canonical
  value-function expansion;
- `setConstrainedParametricObjective`, recalled in `Chap03/Definition_3_74` from
  `Chap03/Proposition_3_52`, as the pointwise bridge for the stage-`k` model.

Best owner abstraction:
- `parametricValueFunction Q (hatModel xSeq k) (checkModel xSeq k)`

Primitive data:
- feasible set `Q`
- upper model family `hatModel`
- lower model family `checkModel`
- sample sequence `xSeq`
- iteration index `k`

Derived API:
- the textbook parametric model family is
  `setConstrainedParametricObjective (hatModel xSeq k) (checkModel xSeq k)`;
- the textbook model value `\hat f_k^*(X; ·)` is
  `parametricValueFunction Q (hatModel xSeq k) (checkModel xSeq k)`;
- pointwise and value-function expansions remain the owner companion lemmas already recalled in
  `Definition_3_74`.

Source/core/bridge triage:
- source-facing: the fixed-stage textbook model family and its feasible-set infimum
- core/canonical: `parametricValueFunction Q (hatModel xSeq k) (checkModel xSeq k)`
- bridge/view: specialization of `setConstrainedParametricObjective (hatModel xSeq k)
  (checkModel xSeq k)` along `Q`, `xSeq`, and `k`

This item adds no new mathematical data beyond this fixed-stage specialization, so this
file reuses `Definition_3_74` directly and keeps no parallel public wrappers such as
`parametricFunctionModel` or `parametricFunctionModelValue`. -/

section

variable {X : Type u}
variable (Q : Set X)
variable (hatModel checkModel : (ℕ → X) → ℕ → X → ℝ) (xSeq : ℕ → X) (k : ℕ)

/- Definition 3.75: for the sampled history `X = {x_k}` and a fixed stage `k`, the corresponding
model value function `\hat f_k^*(X; ·)` is the direct specialization of the chapter owner
`parametricValueFunction` to the model pair
`(\hat f_k(X; ·), \check f_k(X; ·))`. -/
#check (parametricValueFunction Q (hatModel xSeq k) (checkModel xSeq k) : ℝ → EReal)

variable (t : ℝ)

/- At parameter `t`, the stage-`k` model value is the infimum over `Q` of the same fixed-stage
parametric model. -/
set_option linter.hashCommand false in
#check
  (show
      parametricValueFunction Q (hatModel xSeq k) (checkModel xSeq k) t =
        sInf
          (Set.range fun x : Q ↦
            (setConstrainedParametricObjective (hatModel xSeq k) (checkModel xSeq k) t x :
              EReal)) from
    parametricValueFunction_def Q (hatModel xSeq k) (checkModel xSeq k) t)

end

section

variable {X : Type u}
variable (hatModel checkModel : (ℕ → X) → ℕ → X → ℝ) (xSeq : ℕ → X) (k : ℕ)

/- The textbook parametric model `f_k(X; ·, ·)` is the direct fixed-stage specialization of the
chapter owner `setConstrainedParametricObjective`. -/
#check
  (setConstrainedParametricObjective (hatModel xSeq k) (checkModel xSeq k) : ℝ → X → ℝ)

variable {t : ℝ} {x : X}

/- Evaluating the fixed-stage owner recovers the displayed pointwise formula
`f_k(X; t, x) = max (\hat f_k(X; x) - t) (\check f_k(X; x))`. -/
set_option linter.hashCommand false in
#check
  (show
      setConstrainedParametricObjective (hatModel xSeq k) (checkModel xSeq k) t x =
        max (hatModel xSeq k x - t) (checkModel xSeq k x) from
    setConstrainedParametricObjective_apply)

end
