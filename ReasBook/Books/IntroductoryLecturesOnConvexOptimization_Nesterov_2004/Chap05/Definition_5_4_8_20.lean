/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RealInnerProductSpace

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

/-
Definition 5.4.8.20 lies in the Chapter 5 `ℓ_p` approximation / separable-convex domain.

Sampled owner declarations:
- `SeparableOptimizationProblem.qFunction` in `Definition_5_4_8_1`, the chapter owner for finite
  positive weighted sums of scalar functions along affine maps;
- `SeparableOptimizationProblem.qFunction_apply` in `Definition_5_4_8_1`, the canonical
  expansion bridge for that owner;
- `sumOfExponentials` in `Definition_5_4_8_19`, the neighboring chapter pattern for a
  source-facing objective defined through `SeparableOptimizationProblem.qFunction`;
- `LpApproximationBoxProblem.toSetConstrainedMinimizationProblem` in `Definition_5_4_9_1`, the
  later box-constrained bridge that should reuse this owner directly rather than through a second
  local objective wrapper.

Best owner abstraction:
- source-facing: `lpApproximationObjective`, the textbook residual objective
  `x ↦ ∑ i, |⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p`;
- core/canonical: `SeparableOptimizationProblem.qFunction`;
- bridge/view: `lpApproximationSeparableProblem` and
  `lpApproximationObjective_eq_qFunction`.

Primitive data:
- the exponent `p`;
- the vectors `a₁, …, aₘ` in a real inner product space;
- the scalar targets `b⁽¹⁾, …, b⁽ᵐ⁾`.

Derived API:
- the source-facing objective `lpApproximationObjective`;
- the evaluation lemma `lpApproximationObjective_apply`;
- for `p ≥ 1`, the canonical separable-problem bridge `lpApproximationSeparableProblem` and the
  identification of the objective with its `q₀` block.

Source/core/bridge triage:
- source-facing: Definition 5.4.8.20's `ℓ_p` residual objective;
- core/canonical: the chapter owner `SeparableOptimizationProblem.qFunction`;
- bridge/view: the `SeparableOptimizationProblem E 0` realization below.

The previous version merely recalled a Euclidean raw formula owner from a later theorem file.
This refinement restores Definition 5.4.8.20 as the owner file, moves the objective to the
intrinsic real inner-product-space level, and makes the Chapter 5 separable-objective owner
explicit instead of treating the box-constrained `ℝⁿ` presentation as the core abstraction.
-/

/-- Definition 5.4.8.20: for vectors `a₁, …, aₘ` in a real inner product space `E`, targets
`b⁽¹⁾, …, b⁽ᵐ⁾ ∈ ℝ`, and exponent `p`, the `ℓ_p` approximation objective is the residual sum
`x ↦ \sum_{i=1}^m |\langle a_i, x \rangle - b^{(i)}|^p`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` presentation. -/
def lpApproximationObjective (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) : E → ℝ :=
  fun x ↦ ∑ i : Fin m, |⟪a i, x⟫ - b i| ^ p

/-- Evaluating `lpApproximationObjective p a b` at `x` recovers the defining finite sum
`\sum_{i=1}^m |\langle a_i, x \rangle - b^{(i)}|^p`. -/
@[simp] theorem lpApproximationObjective_apply
    (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (x : E) :
    lpApproximationObjective p a b x = ∑ i : Fin m, |⟪a i, x⟫ - b i| ^ p :=
  rfl

/-- For `p ≥ 1`, the `ℓ_p` approximation objective is the objective block `q₀` of a canonical
separable optimization problem with one block and no inequality constraints. -/
def lpApproximationSeparableProblem (p : Set.Ici (1 : ℝ)) (a : Fin m → E) (b : Fin m → ℝ) :
    SeparableOptimizationProblem E 0 where
  blockSize _ := m
  weight _ _ := 1
  weight_pos _ _ := zero_lt_one
  affineMap _ i := ((innerSL ℝ (a i)).toLinearMap).toAffineMap + AffineMap.const ℝ E (-b i)
  scalarFunction _ _ := fun t ↦ |t| ^ (p : ℝ)
  scalarFunction_convex _ _ := by
    have habs : ConvexOn ℝ Set.univ (fun t : ℝ ↦ |t|) := by
      simpa [Real.norm_eq_abs] using
        (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ))
    have habs_image : (fun t : ℝ ↦ |t|) '' (Set.univ : Set ℝ) = Set.Ici 0 := by
      ext t
      constructor
      · rintro ⟨x, -, rfl⟩
        exact abs_nonneg x
      · intro ht
        refine ⟨t, Set.mem_univ t, ?_⟩
        simp [abs_of_nonneg (show 0 ≤ t from ht)]
    have hpow :
        ConvexOn ℝ ((fun t : ℝ ↦ |t|) '' (Set.univ : Set ℝ)) (fun t : ℝ ↦ t ^ (p : ℝ)) := by
      simpa [habs_image] using
        (convexOn_rpow p.2 : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ ↦ t ^ (p : ℝ)))
    have hmono :
        MonotoneOn (fun t : ℝ ↦ t ^ (p : ℝ)) ((fun t : ℝ ↦ |t|) '' (Set.univ : Set ℝ)) := by
      have hp0 : 0 ≤ (p : ℝ) := le_trans zero_lt_one.le p.2
      simpa [habs_image] using
        (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hp0 :
          MonotoneOn (fun t : ℝ ↦ t ^ (p : ℝ)) (Set.Ici 0))
    simpa using hpow.comp habs hmono
  constraintBound := Fin.elim0

/-- For `p ≥ 1`, the source-facing `ℓ_p` residual objective is exactly the `q₀` block of the
canonical separable owner `lpApproximationSeparableProblem`. -/
theorem lpApproximationObjective_eq_qFunction
    (p : Set.Ici (1 : ℝ)) (a : Fin m → E) (b : Fin m → ℝ) :
    lpApproximationObjective (p : ℝ) a b =
      (lpApproximationSeparableProblem p a b).qFunction 0 := by
  funext x
  rw [lpApproximationObjective_apply, (lpApproximationSeparableProblem p a b).qFunction_apply]
  simp [lpApproximationSeparableProblem, sub_eq_add_neg]
  rfl

end
