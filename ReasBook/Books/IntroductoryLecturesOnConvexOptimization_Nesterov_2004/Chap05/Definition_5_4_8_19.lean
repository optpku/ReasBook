/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RealInnerProductSpace

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℕ}

/-
Definition 5.4.8.19 lies in the Chapter 5 finite exponential-sum / separable-convex domain.

Sampled owner declarations:
* `SeparableOptimizationProblem.qFunction` from `Definition_5_4_8_1`, the chapter owner for
  finite positive weighted sums of scalar functions along affine maps;
* `SeparableOptimizationProblem.qFunction_apply` from `Definition_5_4_8_1`, the canonical
  expansion bridge for that owner;
* `logSumExp` from `Definition_5_4_7_11`, the nearby finite exponential-family owner in the same
  domain, but with an additional outer logarithm;
* `smoothMaxInnerApproximation` from `Chap07/Definition_7_42`, another project function built from
  exponentials of inner products.

Best owner abstraction:
* source-facing: `sumOfExponentials`;
* core/canonical: `SeparableOptimizationProblem.qFunction`;
* bridge/view: `sumOfExponentialsSeparableProblem` and `sumOfExponentials_eq_separableProblem`;
* derived theorem layer: `sumOfExponentials_convex`.

Primitive data:
* the real coefficient family `α₁, …, αᵣ`;
* the vectors `a₁, …, aᵣ` in a real inner product space.

Derived API:
* the source-facing function `sumOfExponentials`;
* the defining expansion `sumOfExponentials_apply`;
* the positive-weight bridge owner `sumOfExponentialsSeparableProblem`;
* the positive-weight bridge equality `sumOfExponentials_eq_separableProblem`;
* the nonnegative-coefficient convexity theorem `sumOfExponentials_convex`.

The previous version duplicated the chapter owner for finite weighted affine-composition sums as a
raw standalone formula while also exposing a coercion parameter in the source-facing function
owner. This refinement keeps the textbook function name on the primitive real coefficient data
`α : Fin r → ℝ`, and uses the existing owner `SeparableOptimizationProblem.qFunction` only on the
positive-weight bridge layer where that hypothesis is mathematically relevant. The ambient owner is
the intrinsic real inner product space carrying the inner products `⟪aⱼ, y⟫`; specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` presentation.
-/

/-- For strictly positive coefficients, the exponential sum determines a canonical separable
optimization problem with one block and no inequality constraints. -/
def sumOfExponentialsSeparableProblem (α : Fin r → Set.Ioi (0 : ℝ)) (a : Fin r → E) :
    SeparableOptimizationProblem E 0 where
  blockSize _ := r
  weight _ j := α j
  weight_pos _ j := (α j).2
  affineMap _ j := ((innerSL ℝ (a j)).toLinearMap).toAffineMap
  scalarFunction _ _ := Real.exp
  scalarFunction_convex _ _ := by
    simpa using convexOn_exp
  constraintBound := Fin.elim0

/-- Definition 5.4.8.19: for coefficients `α₁, …, αᵣ` read in `ℝ` and vectors `a₁, …, aᵣ` in a
real inner product space `E`, the exponential sum with coefficients `α` and vectors `a` is the
function `g(y) = \sum_{j=1}^r αⱼ \exp(\langle aⱼ, y \rangle)`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` formula. -/
def sumOfExponentials (α : Fin r → ℝ) (a : Fin r → E) : E → ℝ :=
  fun y ↦ ∑ j : Fin r, α j * Real.exp ⟪a j, y⟫

/-- Evaluating `sumOfExponentials α a` at `y` recovers the defining textbook formula
`g(y) = \sum_{j=1}^r αⱼ \exp(\langle aⱼ, y \rangle)`. -/
@[simp] theorem sumOfExponentials_apply (α : Fin r → ℝ) (a : Fin r → E) (y : E) :
    sumOfExponentials α a y = ∑ j : Fin r, α j * Real.exp ⟪a j, y⟫ :=
  rfl

/-- For strictly positive coefficients, the exponential sum obtained by reading `α` as a real
coefficient family is exactly the objective function of the canonical separable owner
`sumOfExponentialsSeparableProblem α a`. -/
theorem sumOfExponentials_eq_separableProblem
    (α : Fin r → Set.Ioi (0 : ℝ)) (a : Fin r → E) :
    sumOfExponentials (fun j ↦ α j) a = sumOfExponentialsSeparableProblem α a := by
  funext y
  rw [SeparableOptimizationProblem.coe_apply]
  rw [(sumOfExponentialsSeparableProblem α a).qFunction_apply 0 y]
  rfl

/-- If all coefficients are nonnegative, then `sumOfExponentials α a` is convex on the whole
ambient space. -/
theorem sumOfExponentials_convex
    (α : Fin r → ℝ) (hα : ∀ j, 0 ≤ α j) (a : Fin r → E) :
    ConvexOn ℝ Set.univ (sumOfExponentials α a) := by
  classical
  let term : Fin r → E → ℝ := fun j y ↦ α j * Real.exp ⟪a j, y⟫
  have hterm : ∀ j : Fin r, ConvexOn ℝ Set.univ (term j) := by
    intro j
    have hcomp : ConvexOn ℝ Set.univ (fun y : E ↦ Real.exp ⟪a j, y⟫) := by
      simpa using
        (convexOn_exp.comp_affineMap (((innerSL ℝ (a j)).toLinearMap).toAffineMap))
    simpa [term] using ConvexOn.smul (hα j) hcomp
  have hsum :
      ∀ s : Finset (Fin r),
        ConvexOn ℝ Set.univ (fun y ↦ s.sum (fun j ↦ term j y)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))
    · intro j s hj hs
      simpa [Finset.sum_insert hj] using (hterm j).add hs
  simpa [sumOfExponentials, term] using hsum Finset.univ

end
