/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_81

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v w

/- Proposition 7.35 lies in the chapter's affine-residual / strict-positivity domain.

Sampled owner-style declarations:
- `Seminorm.IsNorm` in `Chap02/Definition_2_5`, the project owner for a separated seminorm;
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the project owner for
  pointwise maxima over a nonempty finite index type;
- `StrictlyPositiveOn` in `Chap07/Definition_7_81`, the source-facing positivity predicate;
- `StrictlyPositiveOn.inequality_comp_affineMap_image_adjoint` in `Chap07/Lemma_7_16`, the
  intrinsic affine-pullback bridge on linear maps;
- `StrictlyPositiveOn.nonnegative_linear_combination` in `Chap07/Lemma_7_18`, the finite-sum
  closure pattern used by Proposition 7.35.

Best owner abstraction:
- source-facing: Proposition 7.35's strict-positivity assertions for
  `x ↦ p (A x - b)`, `x ↦ ∑ i, p (Aᵢ x - bᵢ)`, and
  `x ↦ maxᵢ p (Aᵢ x - bᵢ)`;
- core/canonical: `Seminorm.IsNorm`, `maxTypeObjective`, and `StrictlyPositiveOn`;
- bridge/view: the Euclidean matrix specialization obtained by taking
  `E := EuclideanSpace ℝ (Fin n)`, `F := EuclideanSpace ℝ (Fin m)`, and
  `Aᵢ := (Mᵢ).toEuclideanLin`.

Primitive data:
- a seminorm `p : Seminorm ℝ F`;
- linear maps `A : E →ₗ[ℝ] F` and `A : ι → E →ₗ[ℝ] F`;
- translations `b : F` and `b : ι → F`;
- a finite family index type `ι` for the aggregate cases.

Derived API:
- the direct objective expressions `fun x ↦ p (A x - b)`,
  `fun x ↦ ∑ i, p (A i x - b i)`, and
  `maxTypeObjective (fun i x ↦ p (A i x - b i))`;
- the strict-positivity theorems on `Set.univ`.

This refinement moves the public API from the over-concrete display model
`EuclideanSpace ℝ (Fin n)` with matrix families indexed by `Fin m` to the intrinsic owner layer of
real vector spaces, linear maps, and a separate finite index type. It also deletes proposition-local
wrapper definitions whose only role was to rename those direct objective expressions. The textbook
matrix formulas are now recovered by specialization rather than by a second concrete owner.
-/

section StrictPositivity

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {ι : Type w} [Fintype ι]

/-- Helper for Proposition 7.35: the coordinate-sum seminorm on a finite product is the sum of
the pulled-back coordinate seminorms. -/
def sumCoordinateSeminorm (p : Seminorm ℝ F) : Seminorm ℝ (ι → F) :=
  ∑ i : ι, p.comp (LinearMap.proj i)

/-- Helper for Proposition 7.35: evaluating the coordinate-sum seminorm gives the sum of the
coordinate seminorm values. -/
theorem sum_coordinate_seminorm_apply
    (p : Seminorm ℝ F) (z : ι → F) :
    sumCoordinateSeminorm p z = ∑ i : ι, p (z i) := by
  -- Expand the product seminorm back to the textbook coordinate sum.
  classical
  have hsum :
      ∀ s : Finset ι,
        ((s.sum fun i ↦ p.comp (LinearMap.proj i)) z) = s.sum fun i ↦ p (z i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert i s hi ih =>
        simp [hi, ih, Seminorm.comp_apply]
  simpa [sumCoordinateSeminorm] using hsum Finset.univ

/-- Helper for Proposition 7.35: if `p` is a norm, then the coordinate-sum seminorm is again a
norm. -/
theorem sum_coordinate_seminorm_isNorm
    (p : Seminorm ℝ F) [p.IsNorm] :
    (sumCoordinateSeminorm (ι := ι) p).IsNorm := by
  constructor
  intro z hz
  funext i
  apply Seminorm.IsNorm.eq_zero_of_map_eq_zero (p := p)
  have hle : p (z i) ≤ sumCoordinateSeminorm p z := by
    rw [sum_coordinate_seminorm_apply]
    exact Finset.single_le_sum (fun j _ ↦ apply_nonneg p (z j)) (by simp)
  have hz_i : p (z i) = 0 := by
    rw [hz] at hle
    exact le_antisymm hle (apply_nonneg p (z i))
  exact hz_i

/-- Helper for Proposition 7.35: pulling back a norm seminorm along an injective linear map
preserves separation. -/
theorem seminorm_isNorm_comp_of_injective
    {G : Type*} [AddCommGroup G] [Module ℝ G]
    (q : Seminorm ℝ G) [q.IsNorm]
    (L : E →ₗ[ℝ] G) (hL : Function.Injective L) :
    (q.comp L).IsNorm := by
  constructor
  intro x hx
  apply hL
  have hzero : L x = 0 := by
    apply Seminorm.IsNorm.eq_zero_of_map_eq_zero (p := q)
    simpa [Seminorm.comp_apply] using hx
  simpa using hzero

/-- If `p` is a norm, then the affine residual objective `x ↦ p (A x - b)` is strictly positive
on the whole space. -/
-- Proof sketch: identify `p` with the real-valued support function of its dual unit ball, apply
-- the support-function strict-positivity theorem on `F`, and then pull back along the affine map
-- `x ↦ A x - b` using the intrinsic affine-pullback lemma from `Lemma_7_16`.
theorem affineResidualSeminorm_strictlyPositiveOn_univ
    (p : Seminorm ℝ F) [p.IsNorm]
    (A : E →ₗ[ℝ] F) (b : F) :
    StrictlyPositiveOn Set.univ (fun x ↦ p (A x - b)) := by
  intro x y g _ _ hg
  rw [mem_subdifferentialWithin_iff] at hg
  have hsubgrad := hg.2
  have hshift : (x - (y - x)) - x = -(y - x) := by
    abel
  have htest :
      p (A (x - (y - x)) - b) ≥ p (A x - b) - inner ℝ g (y - x) := by
    -- Test the subgradient inequality at the reflected point `x - (y - x)`.
    have hraw := hsubgrad (y := x - (y - x)) (by simp)
    rw [hshift, inner_neg_right] at hraw
    exact hraw
  have htriangle :
      p (A (x - (y - x)) - b) ≤ p (A x - b) + p (A (y - x)) := by
    -- Rewrite the reflected residual as `(A x - b) - A (y - x)` and use the seminorm triangle bound.
    calc
      p (A (x - (y - x)) - b)
          = p ((A x - b) - A (y - x)) := by
              congr 1
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ ≤ p (A x - b) + p (A (y - x)) := by
        exact map_sub_le_add p (A x - b) (A (y - x))
  have hinner :
      -p (A (y - x)) ≤ inner ℝ g (y - x) := by
    linarith
  have hresidual :
      p (A (y - x)) ≤ p (A y - b) + p (A x - b) := by
    -- The difference of the two residuals controls the residual of `y - x`.
    calc
      p (A (y - x))
          = p ((A y - b) - (A x - b)) := by
              congr 1
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ ≤ p (A y - b) + p (A x - b) := by
        exact map_sub_le_add p (A y - b) (A x - b)
  -- Combine the subgradient lower bound with the triangle inequality control.
  linarith

-- Proof sketch: each summand `x ↦ p (Aᵢ x - bᵢ)` is strictly positive on `E` by
-- `affineResidualSeminorm_strictlyPositiveOn_univ`; then iterate
-- `StrictlyPositiveOn.nonnegative_linear_combination` with coefficients `1` to combine the family
-- into its finite sum.
/-- Proposition 7.35 (1): the aggregate objective
`f₁(x) = ∑ᵢ p (Aᵢ x - bᵢ)` is strictly positive on the whole space in the sense of
Definition 7.81. -/
theorem affineResidualSeminormSum_strictlyPositiveOn
    (p : Seminorm ℝ F) [p.IsNorm]
    (A : ι → E →ₗ[ℝ] F) (b : ι → F) :
    StrictlyPositiveOn Set.univ (fun x ↦ ∑ i : ι, p (A i x - b i)) := by
  let _ : (sumCoordinateSeminorm (ι := ι) p).IsNorm :=
    sum_coordinate_seminorm_isNorm (ι := ι) (p := p)
  let e : PiLp 2 (fun _ : ι ↦ F) ≃L[ℝ] (ι → F) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ F)
  let q : Seminorm ℝ (PiLp 2 (fun _ : ι ↦ F)) :=
    (sumCoordinateSeminorm (ι := ι) p).comp e.toLinearMap
  let _ : q.IsNorm :=
    seminorm_isNorm_comp_of_injective
      (q := sumCoordinateSeminorm (ι := ι) p)
      (L := e.toLinearMap) e.injective
  let Aagg : E →ₗ[ℝ] PiLp 2 (fun _ : ι ↦ F) :=
    e.symm.toLinearMap.comp (LinearMap.pi A)
  -- Package the family of affine residuals as one residual in the finite product space.
  simpa [q, e, Aagg, sum_coordinate_seminorm_apply] using
    (affineResidualSeminorm_strictlyPositiveOn_univ
      (p := q)
      (A := Aagg)
      (b := e.symm b))

variable [Nonempty ι]

/-- Helper for Proposition 7.35: the coordinate-max seminorm on a finite product is the finite
supremum of the pulled-back coordinate seminorms. -/
def maxCoordinateSeminorm (p : Seminorm ℝ F) : Seminorm ℝ (ι → F) :=
  Finset.univ.sup fun i : ι ↦ p.comp (LinearMap.proj i)

/-- Helper for Proposition 7.35: evaluating the coordinate-max seminorm gives the finite maximum
of the coordinate seminorm values. -/
theorem max_coordinate_seminorm_apply
    (p : Seminorm ℝ F) (z : ι → F) :
    maxCoordinateSeminorm p z = maxTypeObjective (fun i w ↦ p (w i)) z := by
  let q : ι → Seminorm ℝ (ι → F) := fun i ↦ p.comp (LinearMap.proj i)
  apply le_antisymm
  · -- Realize the finite seminorm supremum at an actual coordinate and compare with the max objective.
    rcases Seminorm.exists_apply_eq_finset_sup q Finset.univ_nonempty z with ⟨i, hi, hq⟩
    rw [maxTypeObjective_apply]
    calc
      maxCoordinateSeminorm p z = q i z := by
        simpa [maxCoordinateSeminorm, q] using hq
      _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ p (z j)) := by
        exact Finset.le_sup' (fun j : ι ↦ p (z j)) hi
  · -- Every coordinate value is bounded by the finite seminorm supremum.
    rw [maxTypeObjective_apply]
    rw [Finset.sup'_le_iff]
    intro i hi
    simpa [maxCoordinateSeminorm, q, Seminorm.comp_apply] using
      (Seminorm.le_finset_sup_apply (p := q) (s := Finset.univ) (x := z) (i := i) hi)

/-- Helper for Proposition 7.35: if `p` is a norm, then the coordinate-max seminorm is again a
norm. -/
theorem max_coordinate_seminorm_isNorm
    (p : Seminorm ℝ F) [p.IsNorm] :
    (maxCoordinateSeminorm (ι := ι) p).IsNorm := by
  constructor
  intro z hz
  funext i
  apply Seminorm.IsNorm.eq_zero_of_map_eq_zero (p := p)
  have hle : p (z i) ≤ maxCoordinateSeminorm p z := by
    simpa [maxCoordinateSeminorm, Seminorm.comp_apply] using
      (Seminorm.le_finset_sup_apply
        (p := fun j : ι ↦ p.comp (LinearMap.proj j))
        (s := Finset.univ) (x := z) (i := i) (by simp))
  have hz_i : p (z i) = 0 := by
    rw [hz] at hle
    exact le_antisymm hle (apply_nonneg p (z i))
  exact hz_i

-- Proof sketch: each branch `x ↦ p (Aᵢ x - bᵢ)` is strictly positive on `E` by
-- `affineResidualSeminorm_strictlyPositiveOn_univ`; then induct on the nonempty finite family and
-- use the two-branch max closure theorem at each step.
/-- Proposition 7.35 (2): the aggregate objective
`f₂(x) = maxᵢ p (Aᵢ x - bᵢ)` is strictly positive on the whole space in the sense of
Definition 7.81. -/
theorem affineResidualSeminormMax_strictlyPositiveOn
    (p : Seminorm ℝ F) [p.IsNorm]
    (A : ι → E →ₗ[ℝ] F) (b : ι → F) :
    StrictlyPositiveOn Set.univ (maxTypeObjective fun i x ↦ p (A i x - b i)) := by
  let _ : (maxCoordinateSeminorm (ι := ι) p).IsNorm :=
    max_coordinate_seminorm_isNorm (ι := ι) (p := p)
  let e : PiLp 2 (fun _ : ι ↦ F) ≃L[ℝ] (ι → F) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ F)
  let q : Seminorm ℝ (PiLp 2 (fun _ : ι ↦ F)) :=
    (maxCoordinateSeminorm (ι := ι) p).comp e.toLinearMap
  let _ : q.IsNorm :=
    seminorm_isNorm_comp_of_injective
      (q := maxCoordinateSeminorm (ι := ι) p)
      (L := e.toLinearMap) e.injective
  let Aagg : E →ₗ[ℝ] PiLp 2 (fun _ : ι ↦ F) :=
    e.symm.toLinearMap.comp (LinearMap.pi A)
  -- Package the family of affine residuals as one residual for the coordinate-max seminorm.
  simpa [q, e, Aagg, max_coordinate_seminorm_apply, maxTypeObjective_apply] using
    (affineResidualSeminorm_strictlyPositiveOn_univ
      (p := q)
      (A := Aagg)
      (b := e.symm b))

end StrictPositivity
