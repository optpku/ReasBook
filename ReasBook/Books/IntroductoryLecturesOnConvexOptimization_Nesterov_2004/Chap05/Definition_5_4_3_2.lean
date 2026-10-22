/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_10_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators EuclideanOrthant

noncomputable section

variable (n : ℕ)

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => ℝ₊₊^n

noncomputable local instance instFintypeFinDefinition5432 : Fintype (Fin n) :=
  Fintype.ofFinite (Fin n)
local instance instLocalChap05_Definition_5_4_3_21 : CoeFun Xₙ (fun _ ↦ Fin n → ℝ) where
  coe x := fun i ↦ x.1 i

/- Definition 5.4.3.2 lies in the Chapter 1/5 logarithmic-barrier-on-strict-domain domain.

Sampled owner declarations in this domain:
* `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` from
  `Chap01/Definition_1_10_2`, the intrinsic strict positive orthant owner;
* `strictConstraintSet`, `logarithmicBarrier`, and `logarithmicBarrier_apply` from
  `Chap01/Proposition_1_10_17`, the canonical strict-domain logarithmic-barrier owner for finite
  continuous inequality families;
* `universalBarrier` and `universalBarrierAmbient` from `Chap05/Theorem_5_4_2_2`, the chapter
  owner/ambient-bridge split for barriers on intrinsic open domains;
* `QuadraticallyConstrainedQuadraticOptimizationProblem.epigraphLogarithmicBarrier` and
  `...Ambient` from `Chap05/Definition_5_4_3_5`, the same split for a later Chapter 5
  logarithmic barrier.

Best owner abstraction:
* source-facing: the standard logarithmic barrier on the strict positive orthant
  `positiveOrthant n`;
* core/canonical: `logarithmicBarrier` on the coordinate slack family `x ↦ -x i`;
* bridge/view: the ambient formula `standardLogarithmicBarrierAmbient : Eₙ → ℝ`.

Primitive data:
* the dimension `n`;
* the intrinsic strict positive orthant `positiveOrthant n`.

Derived API:
* the coordinate slack family `positiveOrthantConstraints n`;
* the intrinsic owner `standardLogarithmicBarrier : C(Xₙ, ℝ)`;
* the ambient bridge `standardLogarithmicBarrierAmbient : Eₙ → ℝ`.

The previous version reversed this layering by making the ambient formula the primary owner and by
adding a redundant subtype wrapper. The refined file keeps the source-facing owner on the strict
positive orthant and exposes the ambient formula only as the thin bridge needed by downstream
Chapter 5 barrier APIs. -/

private def positiveOrthantConstraints : Fin n → C(Eₙ, ℝ) :=
  fun i ↦
    { toFun := fun x ↦ -x i
      continuous_toFun := (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i).neg }

private theorem positiveOrthant_subset_strictConstraintSet_positiveOrthantConstraints :
    ℝ₊₊^n ⊆ strictConstraintSet (positiveOrthantConstraints n) := by
  intro x hx j
  exact neg_lt_zero.mpr (hx j)

@[simp] private theorem coe_inclusion_positiveOrthantConstraints (x : Xₙ) :
    ((ContinuousMap.inclusion
        (positiveOrthant_subset_strictConstraintSet_positiveOrthantConstraints n)) x :
      Eₙ) = x.1 :=
  rfl

/-- Definition 5.4.3.2: the standard logarithmic barrier for the strict positive orthant
`\mathbb{R}^n_{++}` is the canonical logarithmic barrier on that intrinsic domain. -/
abbrev standardLogarithmicBarrier : C(Xₙ, ℝ) :=
  (logarithmicBarrier (positiveOrthantConstraints n)).comp
    (ContinuousMap.inclusion
      (positiveOrthant_subset_strictConstraintSet_positiveOrthantConstraints n))

-- Proof sketch: unfold `standardLogarithmicBarrier`; this is the canonical logarithmic barrier on
-- the positive-orthant constraint family, precomposed with the subtype inclusion.
/-- Evaluating `standardLogarithmicBarrier` gives the textbook formula
`-\sum_{i=1}^n \log x^{(i)}` on the strict positive orthant. -/
@[simp] theorem standardLogarithmicBarrier_apply (x : Xₙ) :
    standardLogarithmicBarrier n x =
      -∑ i : Fin n, Real.log (x i) := by
  rw [standardLogarithmicBarrier, ContinuousMap.comp_apply, logarithmicBarrier_apply]
  simp [positiveOrthantConstraints]

/-- The ambient formula underlying `standardLogarithmicBarrier`. This is only a bridge view for
Chapter 5 APIs formulated on ambient maps `Eₙ → ℝ`. -/
def standardLogarithmicBarrierAmbient : Eₙ → ℝ :=
  fun x ↦ -∑ i : Fin n, Real.log (x i)

/-- Evaluating `standardLogarithmicBarrierAmbient` gives the textbook ambient formula
`-\sum_{i=1}^n \log x^{(i)}`. -/
@[simp] theorem standardLogarithmicBarrierAmbient_apply (x : Eₙ) :
    standardLogarithmicBarrierAmbient n x =
      -∑ i : Fin n, Real.log (x i) :=
  rfl

/-- On the strict positive orthant, the ambient bridge agrees with the intrinsic owner. -/
@[simp] theorem standardLogarithmicBarrierAmbient_eq_standardLogarithmicBarrier (x : Xₙ) :
    standardLogarithmicBarrierAmbient n x = standardLogarithmicBarrier n x := by
  simpa [standardLogarithmicBarrierAmbient] using
    (standardLogarithmicBarrier_apply n x).symm

end
