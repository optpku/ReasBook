/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 4.2.5 lies in the accelerated cubic-Newton / monotone step-selection domain.

Sampled owner declarations:
* `acceleratedCubicNewtonWeight` in `Algorithm_4_2_2`, the chapter owner of the coefficient
  `a_k = ((k + 1) (k + 2)) / 2`;
* `sampledAffineMinorant` in `Chap03/Proposition_3_26`, the canonical affine-model owner for
  `z ↦ f(y) + ⟪g, z - y⟫`;
* `CubicRegularizationMapping` in `Definition_4_2_12`, the chapter owner of a cubic trial map
  `T_M`;
* `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  owner for selecting the better point from a finite candidate set.

Best owner abstraction:
* source-facing: one modified accelerated cubic-Newton step;
* core/canonical: `CubicRegularizationMapping f M`, `acceleratedCubicNewtonWeight`,
  `sampledAffineMinorant`, and `argmin[{xk, step yk}] f`;
* bridge/view: the pointwise expansion of the updated estimating function.

Primitive data:
* the objective `f`;
* the chosen cubic trial-map owner `step`;
* the current points `xk`, `yk`;
* the accepted point `x̂_k`, carried directly as a point of the canonical subtype
  `argmin[{xk, step yk}] f`.

Derived API:
* for each index `k` and estimating function `ψ_k`, the updated estimating function obtained by
  adding the weighted sampled affine minorant at the trial point `T_M(y_k)`;
* the next iterate `x_{k+1} = T_M(x̂_k)`, derived from the accepted point;
* the textbook two-point choice and minimum-value identities.

The previous file packaged the accepted point in a bespoke structure and then retained a public
alias for the same canonical subtype. This refinement keeps the same mathematical semantics,
deletes that duplicate owner, and phrases the updated estimating function and next iterate directly
over the canonical accepted-point binder `xHat : argmin[{xk, step yk}] f`.
-/

section

variable (f : E → ℝ) {M : ℝ} (step : CubicRegularizationMapping f M) (xk yk : E)

/- Algorithm 4.2.5 recalls the canonical accepted-point subtype for the two-point argmin
selection between `x_k` and the cubic trial point `T_M(y_k)`. -/
set_option linter.hashCommand false in
#check ({xHat : E // xHat ∈ argmin[{xk, step yk}] f} : Type u)

end

namespace ModifiedAcceleratedCubicNewton

variable {f : E → ℝ} {M : ℝ} {step : CubicRegularizationMapping f M} {xk yk : E}

/-- The updated estimating function `ψ_{k+1}` obtained by adding the weighted affine lower model
at the trial point `T_M(y_k)`. -/
def psiNext
    (step : CubicRegularizationMapping f M) (yk : E) (k : ℕ) (psiK : E → ℝ) :
    E → ℝ :=
  fun z ↦
    psiK z +
      acceleratedCubicNewtonWeight k *
        sampledAffineMinorant (step yk) (∇ f (step yk)) (f (step yk)) z

/-- The next iterate `x_{k+1}` produced by reapplying `T_M` to the accepted point `x̂_k`. -/
def xNext
    (xHat : argmin[{xk, step yk}] f) :
    E :=
  step xHat

/-- The estimating function is updated by the affine lower model at `ŷ_k` with weight
`a_k = ((k + 1) (k + 2)) / 2`. -/
theorem psiNext_eq
    (k : ℕ) (psiK : E → ℝ) :
    psiNext step yk k psiK = fun z ↦
      psiK z +
        acceleratedCubicNewtonWeight k *
          (f (step yk) + inner ℝ (∇ f (step yk)) (z - step yk)) := by
  ext z
  rw [psiNext, sampledAffineMinorant_apply]

/-- The accepted point belongs to the candidate pair `{x_k, ŷ_k}`. -/
theorem mem_pair
    (xHat : argmin[{xk, step yk}] f) :
    (xHat : E) ∈ ({xk, step yk} : Set E) :=
  (mem_constrainedArgmin_iff.mp xHat.2).1

/-- The accepted point globally minimizes `f` on the candidate pair `{x_k, ŷ_k}`. -/
theorem isMinOn
    (xHat : argmin[{xk, step yk}] f) :
    IsMinOn f ({xk, step yk} : Set E) (xHat : E) :=
  (mem_constrainedArgmin_iff.mp xHat.2).2

/-- The accepted point is chosen from the pair `{x_k, ŷ_k}`. -/
theorem eq_xk_or_eq_trial
    (xHat : argmin[{xk, step yk}] f) :
    (xHat : E) = xk ∨ (xHat : E) = step yk := by
  simpa using mem_pair xHat

/-- The accepted point attains the smaller objective value among `x_k` and `ŷ_k`. -/
theorem value_eq
    (xHat : argmin[{xk, step yk}] f) :
    f xHat = min (f xk) (f (step yk)) := by
  have hxk : f xHat ≤ f xk := by
    simpa using (isMinOn xHat (by simp : xk ∈ ({xk, step yk} : Set E)))
  have htrial : f xHat ≤ f (step yk) := by
    simpa using
      (isMinOn xHat (by simp : step yk ∈ ({xk, step yk} : Set E)))
  rcases eq_xk_or_eq_trial xHat with hX | htrial_eq
  · simpa [hX] using (min_eq_left htrial).symm
  · simpa [htrial_eq] using (min_eq_right hxk).symm

/-- The next iterate is obtained by reapplying `T_M` to the accepted point. -/
@[simp] theorem xNext_eq
    (xHat : argmin[{xk, step yk}] f) :
    xNext xHat = step xHat :=
  rfl

end ModifiedAcceleratedCubicNewton

end
