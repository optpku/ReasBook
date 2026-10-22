/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_42
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_33
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_35
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Theorem_7_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_35

-- Declarations for this item will be appended below by the statement pipeline.

open EuclideanSpace (nonnegativeOrthant)
open scoped BigOperators Gradient PositiveDefMatrixNorm SmoothConvex SupportFunction

noncomputable section

variable {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 7.21 lies in Chapter 7's sign-symmetric support / weighted smooth-max domain.

Sampled owner-style declarations:
- `hessian` in `Chap01/Definition_1_4_16`, the project owner for second-order derivatives;
- `ξ[Q]` and `supportFunction_apply` in `Chap03/Definition_3_9`, the chapter owner for support
  functions;
- `positiveDefMatrixNorm` and the notations `‖x‖[D]`, `‖x‖[D,*]` in `Chap07/Definition_7_23`,
  the chapter owners for the weighted norm and its dual;
- `𝓕[L, p]¹¹` and `ConvexC1SeminormSmooth.dualNorm_gradient_sub_le` in `Chap02/Theorem_2_5`,
  the canonical smoothness owner and its gradient-Lipschitz consequence;
- `Matrix.IsDiag` in mathlib's matrix diagonal API, the canonical owner for the diagonality
  needed to pass from `h` to `|h|` in the weighted norm;
- `signSymmetricConvexHull` in `Chap07/Definition_7_35`, the source-facing owner carrying the
  needed absolute-value support data;
- `smoothMaxInnerApproximation` in `Chap07/Definition_7_42`, the source-facing smoothing owner for
  finite max-inner objectives.

Best owner abstraction:
- source-facing: Proposition 7.21's Hessian and dual-gradient estimates for
  `smoothMaxInnerApproximation a μ`;
- core/canonical: `hessian`, `smoothMaxInnerApproximation a μ`, `positiveDefMatrixNorm`, and the
  Chapter 7 box-hull owner `signSymmetricConvexHull a`;
- bridge/view: the orthant support upper bound for `ξ[signSymmetricConvexHull a]`, which is the
  correct source-facing way to control the absolute pairings `|⟪aᵢ, h⟫|` entering the Hessian.

Primitive data:
- the finite family `a : ι → E`;
- the orthant hypothesis `ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n`;
- the diagonal positive-definite matrix owner `D` together with `hDdiag : D.1.IsDiag`;
- the positive smoothing parameter `μ`.

Derived API:
- the orthant support upper bound for the sign-symmetric hull;
- the Hessian quadratic-form bound;
- the Chapter 2 smooth-convex owner theorem for `smoothMaxInnerApproximation a μ`;
- the resulting weighted dual-gradient Lipschitz estimate.

Source/core/bridge triage:
- source-facing: the Hessian and weighted dual-gradient estimates below;
- core/canonical: `hessian`, `smoothMaxInnerApproximation a μ ∈ 𝓕[L, ‖·‖[D]]¹¹`,
  `signSymmetricConvexHull a`, and the weighted norm owner `‖·‖[D]`;
- bridge/view: the orthant support assumption, kept as theorem-level data rather than a duplicate
  public wrapper.

This refinement removes the orthant-restricted finite-range support hypothesis, which was too weak
for global Hessian control. Proposition 7.21 now uses the sign-symmetric hull owner that carries
the needed absolute-value layer from the surrounding Chapter 7 development.
-/

section

variable (a : ι → E)
variable (D : {D : Mat // D.PosDef}) (μ : {μ : ℝ // 0 < μ})

/-- Helper for Proposition 7.21: squaring the weighted `D`-norm recovers the associated quadratic
form. -/
private theorem positiveDefMatrixNorm_sq_eq_matrix_quadratic
    (z : E) :
    ‖z‖[D] ^ (2 : ℕ) = inner ℝ ((Matrix.toEuclideanLin D.1) z) z := by
  -- Rewrite the weighted norm through its defining square root and discharge nonnegativity using
  -- positivity of the induced linear operator.
  have hPosLin : (Matrix.toEuclideanLin D.1).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr D.2.posSemidef
  have hnonneg : 0 ≤ inner ℝ ((Matrix.toEuclideanLin D.1) z) z := by
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right z
  rw [positiveDefMatrixNorm_def]
  exact Real.sq_sqrt hnonneg

/-- Helper for Proposition 7.21: if `D` is diagonal, replacing `h` by its coordinatewise
absolute value does not change the weighted `D`-norm. -/
private theorem positiveDefMatrixNorm_pointwiseAbs_eq_of_isDiag
    (hDdiag : D.1.IsDiag) (h : E) :
    ‖pointwiseAbs h‖[D] = ‖h‖[D] := by
  -- Route correction: compare the squared weighted norms first, where diagonality turns both
  -- quadratic forms into the same diagonal sum, and only then take square roots.
  have hsq :
      ‖pointwiseAbs h‖[D] ^ (2 : ℕ) = ‖h‖[D] ^ (2 : ℕ) := by
    rw [positiveDefMatrixNorm_sq_eq_matrix_quadratic (D := D) (z := pointwiseAbs h)]
    rw [positiveDefMatrixNorm_sq_eq_matrix_quadratic (D := D) (z := h)]
    rw [hDdiag.diagonal_diag]
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_diagonal, pointwiseAbs, pow_two]
  rcases eq_or_eq_neg_of_sq_eq_sq ‖pointwiseAbs h‖[D] ‖h‖[D] hsq with hEq | hEq
  · exact hEq
  · have hleft_nonneg : 0 ≤ ‖pointwiseAbs h‖[D] := by positivity
    have hright_nonneg : 0 ≤ ‖h‖[D] := by positivity
    nlinarith

/-- Helper for Proposition 7.21: every generator belongs to the sign-symmetric hull of the
family. -/
private theorem generator_mem_signSymmetricConvexHull
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n) (i : ι) :
    a i ∈ signSymmetricConvexHull a := by
  -- The generator lies in its own symmetric box, hence in the convex hull of their union.
  rw [signSymmetricConvexHull_def]
  exact subset_convexHull ℝ <| Set.mem_iUnion.mpr <| ⟨i, by
    change ∀ j, a i j ∈ Set.Icc (-a i j) (a i j)
    intro j
    constructor
    · have haij_nonneg : 0 ≤ a i j := by
        simpa using ha_nonneg i j
      linarith
    · exact le_rfl⟩

/-- Helper for Proposition 7.21: the support function of a finite range is the attained maximum
of the corresponding inner products. -/
private theorem supportFunction_range_toReal_eq_sup_inner
    (x : E) :
    (ξ[Set.range a] x).toReal =
      Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ inner ℝ (a i) x) := by
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ inner ℝ (a i) x)
  have hupper : ξ[Set.range a] x ≤ (M : EReal) := by
    -- Every pairing in the range is bounded by the attained finite maximum.
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
    exact show (((inner ℝ (a i) x : ℝ) : EReal) ≤ (M : EReal)) by
      exact_mod_cast
        (Finset.le_sup' (f := fun j : ι ↦ inner ℝ (a j) x) (Finset.mem_univ i))
  have hlower : (M : EReal) ≤ ξ[Set.range a] x := by
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : ι ↦ inner ℝ (a j) x)
    rw [supportFunction_apply]
    have hi_mem :
        (((inner ℝ (a i) x : ℝ) : EReal)) ≤
          sSup ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) '' Set.range a) :=
      le_sSup ⟨a i, Set.mem_range_self i, rfl⟩
    have hM : (M : EReal) = (((inner ℝ (a i) x : ℝ) : EReal)) := by
      exact_mod_cast hi
    calc
      (M : EReal) = (((inner ℝ (a i) x : ℝ) : EReal)) := hM
      _ ≤ sSup ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) '' Set.range a) := hi_mem
  have hξ : ξ[Set.range a] x = (M : EReal) := le_antisymm hupper hlower
  -- Passing to `toReal` recovers the finite attained maximum.
  simpa [M] using congrArg EReal.toReal hξ

/-- Helper for Proposition 7.21: on the nonnegative orthant, the support function of the
sign-symmetric hull agrees with the support function of the finite range `Set.range a`. -/
private theorem supportFunction_signSymmetricConvexHull_eq_range_on_nonnegativeOrthant
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n)
    {x : E} (hx : x ∈ nonnegativeOrthant n) :
    (ξ[signSymmetricConvexHull a] x).toReal = (ξ[Set.range a] x).toReal := by
  have hupper : ξ[signSymmetricConvexHull a] x ≤ ξ[Set.range a] x := by
    -- Each point of each symmetric box has pairing at most the corresponding generator because
    -- the test vector `x` is coordinatewise nonnegative.
    rw [signSymmetricConvexHull_def, supportFunction_convexHull_eq, supportFunction_apply,
      supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases Set.mem_iUnion.mp hy with ⟨i, hyi⟩
    have hyi_le : inner ℝ y x ≤ inner ℝ (a i) x := by
      rw [PiLp.inner_apply, PiLp.inner_apply]
      refine Finset.sum_le_sum ?_
      intro j hj
      have hxj_nonneg : 0 ≤ x j := by
        simpa using hx j
      exact mul_le_mul_of_nonneg_right (hyi j).2 hxj_nonneg
    have hsup :
        (((inner ℝ (a i) x : ℝ) : EReal)) ≤ ξ[Set.range a] x := by
      rw [supportFunction_apply]
      exact le_sSup ⟨a i, Set.mem_range_self i, rfl⟩
    exact
      (show ((inner ℝ y x : ℝ) : EReal) ≤ ((inner ℝ (a i) x : ℝ) : EReal) by
        exact_mod_cast hyi_le).trans hsup
  have hlower : ξ[Set.range a] x ≤ ξ[signSymmetricConvexHull a] x := by
    -- The generators already lie in the sign-symmetric hull.
    refine sSup_le_sSup ?_
    rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
    exact generator_mem_signSymmetricConvexHull (a := a) ha_nonneg i
  have hξ : ξ[signSymmetricConvexHull a] x = ξ[Set.range a] x := le_antisymm hupper hlower
  exact congrArg EReal.toReal hξ

/-- Helper for Proposition 7.21: the sign-symmetric support at `pointwiseAbs h` dominates every
absolute pairing `|⟪aᵢ, h⟫|`. -/
private theorem absInner_le_signSymmetricConvexHullSupport_pointwiseAbs
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n) (i : ι) (h : E) :
    |inner ℝ (a i) h| ≤ (ξ[signSymmetricConvexHull a] (pointwiseAbs h)).toReal := by
  have hsupport :
      (ξ[signSymmetricConvexHull a] (pointwiseAbs h)).toReal =
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : ι ↦ inner ℝ (a j) (pointwiseAbs h)) := by
    -- First reduce to the range support on the nonnegative orthant, then use the finite-range
    -- support formula.
    rw [supportFunction_signSymmetricConvexHull_eq_range_on_nonnegativeOrthant
      (a := a) ha_nonneg (pointwiseAbs_mem_nonnegativeOrthant h)]
    exact supportFunction_range_toReal_eq_sup_inner (a := a) (x := pointwiseAbs h)
  have habs_inner_le :
      |inner ℝ (a i) h| ≤ ∑ j : Fin n, a i j * |h j| := by
    -- Expand the Euclidean inner product coordinatewise and bound the absolute value by the sum
    -- of coordinatewise absolute contributions.
    calc
      |inner ℝ (a i) h| = |∑ j : Fin n, a i j * h j| := by
        change |∑ j : Fin n, inner ℝ (a i j) (h j)| = |∑ j : Fin n, a i j * h j|
        simp_rw [real_inner_eq_mul]
      _ ≤ ∑ j : Fin n, |a i j * h j| := by
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun j : Fin n ↦ a i j * h j) Finset.univ)
      _ = ∑ j : Fin n, a i j * |h j| := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have haj_nonneg : 0 ≤ a i j := by
          simpa using ha_nonneg i j
        change |a i j| * |h j| = a i j * |h j|
        rw [abs_of_nonneg haj_nonneg]
  have hsum_le_support :
      ∑ j : Fin n, a i j * |h j| ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : ι ↦ inner ℝ (a j) (pointwiseAbs h)) := by
    -- The `i`-th generator pairing with `pointwiseAbs h` is one of the terms in the finite
    -- support maximum over `Set.range a`.
    calc
      ∑ j : Fin n, a i j * |h j| = inner ℝ (a i) (pointwiseAbs h) := by
          change ∑ j : Fin n, a i j * |h j| =
            ∑ j : Fin n, inner ℝ (a i j) ((pointwiseAbs h) j)
          simp_rw [pointwiseAbs_apply, real_inner_eq_mul]
      _ ≤ Finset.univ.sup' Finset.univ_nonempty
            (fun j : ι ↦ inner ℝ (a j) (pointwiseAbs h)) := by
            exact Finset.le_sup' (f := fun j : ι ↦ inner ℝ (a j) (pointwiseAbs h))
              (Finset.mem_univ i)
  -- Combine the triangle bound with the explicit finite-support representation.
  calc
    |inner ℝ (a i) h| ≤ ∑ j : Fin n, a i j * |h j| := habs_inner_le
    _ ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun j : ι ↦ inner ℝ (a j) (pointwiseAbs h)) := hsum_le_support
    _ = (ξ[signSymmetricConvexHull a] (pointwiseAbs h)).toReal := hsupport.symm

/-- Helper for Proposition 7.21: a `C²` real-valued map has a differentiable gradient field. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {F : H → ℝ} {x : H} (hF : ContDiffAt ℝ 2 F x) :
    DifferentiableAt ℝ (∇ F) x := by
  -- Read the gradient through the Riesz map and differentiate the first Fréchet derivative.
  let D : StrongDual ℝ H →L[ℝ] H :=
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ F) x := by
    exact
      (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ F y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Proposition 7.21: the unreindexed score family is a single canonical linear map to
the Chapter 6 `η` coordinate space. -/
private def scoreMapLinear : E →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (((EuclideanSpace.equiv ι ℝ).symm.toLinearMap).comp
    (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap))

/-- Helper for Proposition 7.21: the unreindexed score family as a continuous linear map. -/
private def scoreMap : E →L[ℝ] EuclideanSpace ℝ ι :=
  ⟨scoreMapLinear a, (scoreMapLinear a).continuous_of_finiteDimensional⟩

/-- Helper for Proposition 7.21: evaluating the canonical score map gives the expected inner
product score at each index. -/
@[simp] private theorem scoreMap_apply (x : E) (i : ι) :
    scoreMap a x i = inner ℝ (a i) x := by
  -- Unfold the packaged map once so later transports stay in this spelling world.
  change
    (((EuclideanSpace.equiv ι ℝ).symm
        ((LinearMap.pi fun j ↦ (innerSL ℝ (a j)).toLinearMap) x)) i =
      inner ℝ (a i) x)
  simp [scoreMap, scoreMapLinear]

/-- Helper for Proposition 7.21: the smoothing owner is exactly `η μ` precomposed with the
canonical score map, with no `equivFin` transport. -/
private theorem smoothMaxInnerApproximation_eq_eta_scoreMap :
    smoothMaxInnerApproximation a μ = η μ ∘ scoreMap a := by
  -- Route correction: freeze the score family as `scoreMap a` on the original index type `ι`.
  funext x
  rw [smoothMaxInnerApproximation_apply, eta_apply]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [scoreMap_apply]

/-- Helper for Proposition 7.21: the exponential denominator in `η μ u` is strictly positive on
the original finite index type `ι`. -/
private theorem etaScaledSum_pos
    (u : EuclideanSpace ℝ ι) :
    0 < ∑ j : ι, Real.exp (u j / (μ : ℝ)) := by
  let j0 : ι := Classical.choice ‹Nonempty ι›
  -- A single strictly positive exponential term keeps the finite sum positive.
  refine Finset.sum_pos' ?_ ?_
  · intro j hj
    exact Real.exp_nonneg (u j / (μ : ℝ))
  · exact ⟨j0, Finset.mem_univ j0, Real.exp_pos (u j0 / (μ : ℝ))⟩

/-- Helper for Proposition 7.21: the finite exponential denominator defining `η μ` is `C²` on
the original index type `ι`. -/
private theorem etaScaledSum_contDiff_two :
    ContDiff ℝ 2 (fun u : EuclideanSpace ℝ ι ↦
      ∑ j : ι, Real.exp (u j / (μ : ℝ))) := by
  -- Each summand is an exponential of a scaled coordinate functional.
  refine ContDiff.sum ?_
  intro j hj
  fun_prop

/-- Helper for Proposition 7.21: the Chapter 6 owner `η μ` is twice continuously differentiable
on the original finite coordinate space `EuclideanSpace ℝ ι`. -/
private theorem eta_contDiff_two :
    ContDiff ℝ 2 (η μ : EuclideanSpace ℝ ι → ℝ) := by
  have hlog :
      ContDiff ℝ 2 (fun u : EuclideanSpace ℝ ι ↦
        Real.log (∑ j : ι, Real.exp (u j / (μ : ℝ)))) :=
    ContDiff.log (etaScaledSum_contDiff_two (μ := μ))
      (fun u ↦ (etaScaledSum_pos (μ := μ) u).ne')
  -- Multiplying by the fixed positive parameter `μ` preserves `C²` regularity.
  simpa [η, smul_eq_mul] using (ContDiff.const_smul (μ : ℝ) hlog)

/-- Helper for Proposition 7.21: the second derivative of `t ↦ exp (c t + d)` at `0` is
`c² exp d`. -/
private theorem iteratedDeriv_two_exp_affine
    (c d : ℝ) :
    iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (c * t + d)) 0 = c ^ (2 : ℕ) * Real.exp d := by
  have hg : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.exp s) (c * 0 + d) := by
    simpa using
      (Real.contDiff_exp.contDiffAt : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.exp s) (c * 0 + d))
  have hf : ContDiffAt ℝ 2 (fun t : ℝ ↦ c * t + d) 0 := by
    fun_prop
  have hderiv_affine_fun : deriv (fun t : ℝ ↦ c * t + d) = fun _ ↦ c := by
    funext t
    rw [deriv_add_const]
    simpa using (deriv_const_mul_field (x := t) (u := c) (v := fun s : ℝ ↦ s))
  have hderiv_affine : deriv (fun t : ℝ ↦ c * t + d) 0 = c := by
    simpa using congrArg (fun f : ℝ → ℝ ↦ f 0) hderiv_affine_fun
  have hsecond_affine : iteratedDeriv 2 (fun t : ℝ ↦ c * t + d) 0 = 0 := by
    rw [iteratedDeriv_succ', hderiv_affine_fun]
    simp
  have hexp_second : iteratedDeriv 2 (fun s : ℝ ↦ Real.exp s) d = Real.exp d := by
    simpa [iteratedDeriv_eq_iterate] using
      congrArg (fun f : ℝ → ℝ ↦ f d) (Real.iter_deriv_exp 2)
  have hexp_second' : iteratedDeriv 2 (fun s : ℝ ↦ Real.exp s) (c * 0 + d) = Real.exp d := by
    simpa using hexp_second
  -- Apply the scalar second-derivative composition formula to the affine input of `exp`.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (c * t + d)) 0
        = iteratedDeriv 2 (fun s : ℝ ↦ Real.exp s) (c * 0 + d) *
            deriv (fun t : ℝ ↦ c * t + d) 0 ^ (2 : ℕ) +
            deriv (fun s : ℝ ↦ Real.exp s) (c * 0 + d) *
              iteratedDeriv 2 (fun t : ℝ ↦ c * t + d) 0 := by
            simpa [Function.comp] using
              (iteratedDeriv_comp_two
                (g := fun s : ℝ ↦ Real.exp s) (f := fun t : ℝ ↦ c * t + d)
                (x := 0) hg hf)
    _ = Real.exp d * c ^ (2 : ℕ) + Real.exp d * 0 := by
          rw [hderiv_affine, hsecond_affine, hexp_second']
          simp [Real.deriv_exp]
    _ = c ^ (2 : ℕ) * Real.exp d := by ring

/-- Helper for Proposition 7.21: the weighted mean square is bounded by the weighted second
moment for strictly positive weights summing to `1`. -/
private theorem weightedMeanSq_le_weightedSecondMoment
    (p : ι → ℝ) (v : EuclideanSpace ℝ ι)
    (hp_pos : ∀ i, 0 < p i) (hp_sum : ∑ i : ι, p i = 1) :
    (∑ i : ι, p i * v i) ^ (2 : ℕ) ≤ ∑ i : ι, p i * (v i) ^ (2 : ℕ) := by
  have htitu0 :=
    Finset.sq_sum_div_le_sum_sq_div
      (Finset.univ : Finset ι)
      (fun i ↦ p i * v i) (g := p) (fun i hi ↦ hp_pos i)
  calc
    (∑ i : ι, p i * v i) ^ (2 : ℕ)
        = ((∑ i : ι, p i * v i) ^ (2 : ℕ)) / (∑ i : ι, p i) := by
            rw [hp_sum, div_one]
    _ ≤ ∑ i : ι, (p i * v i) ^ (2 : ℕ) / p i := htitu0
    _ = ∑ i : ι, p i * (v i) ^ (2 : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hp_ne : p i ≠ 0 := (hp_pos i).ne'
          field_simp [pow_two, hp_ne]

/-- Helper for Proposition 7.21: a weighted variance on a finite family is bounded by the square
of the largest absolute coordinate. -/
private theorem weightedVariance_le_sq_supAbs
    (p : ι → ℝ) (v : EuclideanSpace ℝ ι)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    (∑ i : ι, p i * (v i) ^ (2 : ℕ)) - (∑ i : ι, p i * v i) ^ (2 : ℕ) ≤
      (Finset.univ.sup' Finset.univ_nonempty fun i : ι ↦ |v i|) ^ (2 : ℕ) := by
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty fun i : ι ↦ |v i|
  have hvar_le :
      (∑ i : ι, p i * (v i) ^ (2 : ℕ)) - (∑ i : ι, p i * v i) ^ (2 : ℕ) ≤
        ∑ i : ι, p i * (v i) ^ (2 : ℕ) := by
    nlinarith
  have hmoment_le :
      ∑ i : ι, p i * (v i) ^ (2 : ℕ) ≤ ∑ i : ι, p i * M ^ (2 : ℕ) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : |v i| ≤ M := by
      exact Finset.le_sup' (fun j : ι ↦ |v j|) (Finset.mem_univ i)
    have hM_nonneg : 0 ≤ M := by
      exact le_trans (abs_nonneg (v i)) hi_le
    have habs_sq_le : |v i| ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
      have hmul : |v i| * |v i| ≤ M * M := by
        exact mul_le_mul hi_le hi_le (abs_nonneg (v i)) hM_nonneg
      simpa [pow_two] using hmul
    have hsquare_eq : (v i) ^ (2 : ℕ) = |v i| ^ (2 : ℕ) := by
      simpa [pow_two] using (sq_abs (v i)).symm
    have hsquare_le : (v i) ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
      rw [hsquare_eq]
      exact habs_sq_le
    exact mul_le_mul_of_nonneg_left hsquare_le (hp_nonneg i)
  have hmoment_eq :
      ∑ i : ι, p i * M ^ (2 : ℕ) = M ^ (2 : ℕ) := by
    calc
      ∑ i : ι, p i * M ^ (2 : ℕ) = (∑ i : ι, p i) * M ^ (2 : ℕ) := by
        rw [Finset.sum_mul]
      _ = M ^ (2 : ℕ) := by
        rw [hp_sum, one_mul]
  -- Bound the variance by the second moment and then by the maximal squared coordinate.
  calc
    (∑ i : ι, p i * (v i) ^ (2 : ℕ)) - (∑ i : ι, p i * v i) ^ (2 : ℕ)
        ≤ ∑ i : ι, p i * (v i) ^ (2 : ℕ) := hvar_le
    _ ≤ ∑ i : ι, p i * M ^ (2 : ℕ) := hmoment_le
    _ = M ^ (2 : ℕ) := hmoment_eq

/-- Helper for Proposition 7.21: differentiating the exponential denominator of `η μ` along an
affine line gives the weighted first moment. -/
private theorem etaScaledSum_slice_hasDerivAt_zero
    (u v : EuclideanSpace ℝ ι) :
    HasDerivAt (fun t : ℝ ↦ ∑ i : ι, Real.exp (((u + t • v) i) / (μ : ℝ)))
      ((1 / (μ : ℝ)) * ∑ i : ι, Real.exp (u i / (μ : ℝ)) * v i) 0 := by
  -- Differentiate each scalar exponential branch on the line `u + t • v` and sum the results.
  simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
    (HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun i (t : ℝ) ↦ Real.exp (((u + t • v) i) / (μ : ℝ)))
      (A' := fun i ↦ (1 / (μ : ℝ)) * Real.exp (u i / (μ : ℝ)) * v i)
      (x := 0)
      (fun i hi ↦ by
        have hline : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
          simpa [one_smul, zero_smul] using
            ((((1 : ℝ →L[ℝ] ℝ)).smulRight v).hasFDerivAt).hasDerivAt.const_add u
        have hu0 :=
          (((((1 / (μ : ℝ)) : ℝ) • EuclideanSpace.proj i).hasFDerivAt).comp 0
            hline.hasFDerivAt).hasDerivAt
        have hu :
            HasDerivAt (fun t : ℝ ↦ ((u + t • v) i) / (μ : ℝ))
              ((1 / (μ : ℝ)) * v i) 0 := by
          -- This is the scalar affine score `((u + t v)_i) / μ`.
          convert hu0 using 1
          · funext t
            simp [div_eq_mul_inv, mul_comm]
          · simp [div_eq_mul_inv, mul_comm]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hu.exp))

/-- Helper for Proposition 7.21: the second derivative of the exponential denominator of `η μ`
along an affine line gives the weighted quadratic moment. -/
private theorem etaScaledSum_slice_secondDeriv_zero
    (u v : EuclideanSpace ℝ ι) :
    iteratedDeriv 2 (fun t : ℝ ↦ ∑ i : ι, Real.exp (((u + t • v) i) / (μ : ℝ))) 0 =
      ((1 / (μ : ℝ)) ^ (2 : ℕ)) *
        ∑ i : ι, (v i) ^ (2 : ℕ) * Real.exp (u i / (μ : ℝ)) := by
  have hsum :
      iteratedDeriv 2 (fun t : ℝ ↦ ∑ i : ι, Real.exp (((u + t • v) i) / (μ : ℝ))) 0 =
        ∑ i : ι, iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (((u + t • v) i) / (μ : ℝ))) 0 := by
    -- The second iterated derivative commutes with the finite sum because every summand is `C²`.
    simpa using
      (iteratedDeriv_fun_sum (n := 2) (I := Finset.univ)
        (f := fun i (t : ℝ) ↦ Real.exp (((u + t • v) i) / (μ : ℝ))) (x := 0)
        (fun i hi ↦ by
          fun_prop))
  -- Rewrite each summand as an affine exponential, use the scalar second-derivative formula, and
  -- factor out the common `((1 / μ)^2)` coefficient.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ ∑ i : ι, Real.exp (((u + t • v) i) / (μ : ℝ))) 0
        = ∑ i : ι, iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (((u + t • v) i) / (μ : ℝ))) 0 := hsum
    _ = ∑ i : ι,
          ((1 / (μ : ℝ)) ^ (2 : ℕ)) * (v i) ^ (2 : ℕ) * Real.exp (u i / (μ : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          let c : ℝ := v i / (μ : ℝ)
          let d : ℝ := u i / (μ : ℝ)
          have hsplit :
              (fun t : ℝ ↦ Real.exp (((u + t • v) i) / (μ : ℝ))) =
                fun t : ℝ ↦ Real.exp (c * t + d) := by
            -- Expand the `i`th coordinate of the line slice into the affine scalar form.
            funext t
            have harg : (((u + t • v) i) / (μ : ℝ)) = c * t + d := by
              simp [c, d, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
              ring
            rw [harg]
          calc
            iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (((u + t • v) i) / (μ : ℝ))) 0
                = iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (c * t + d)) 0 := by
                    rw [hsplit]
            _ = c ^ (2 : ℕ) * Real.exp d := iteratedDeriv_two_exp_affine c d
            _ = ((1 / (μ : ℝ)) ^ (2 : ℕ)) * (v i) ^ (2 : ℕ) * Real.exp (u i / (μ : ℝ)) := by
                  dsimp [c, d]
                  ring_nf
    _ = ((1 / (μ : ℝ)) ^ (2 : ℕ)) *
          ∑ i : ι, (v i) ^ (2 : ℕ) * Real.exp (u i / (μ : ℝ)) := by
          simpa [mul_assoc] using
            (Finset.mul_sum Finset.univ
              (fun i ↦ (v i) ^ (2 : ℕ) * Real.exp (u i / (μ : ℝ)))
              ((1 / (μ : ℝ)) ^ (2 : ℕ))).symm

/-- Helper for Proposition 7.21: the second directional derivative of `η μ` is the softmax
variance formula on the original finite index type `ι`. -/
private theorem eta_secondDirectionalDerivative_eq
    (u v : EuclideanSpace ℝ ι) :
    secondDirectionalDerivative (η μ) u v =
      (1 / (μ : ℝ)) *
        ((∑ j : ι,
            (Real.exp (u j / (μ : ℝ)) /
              (∑ k : ι, Real.exp (u k / (μ : ℝ)))) *
              (v j) ^ (2 : ℕ)) -
          (∑ j : ι,
            (Real.exp (u j / (μ : ℝ)) /
              (∑ k : ι, Real.exp (u k / (μ : ℝ)))) *
              v j) ^ (2 : ℕ)) := by
  let omegaSlice : ℝ → ℝ := fun t ↦ ∑ i : ι, Real.exp (((u + t • v) i) / (μ : ℝ))
  let moment : ℝ := ∑ i : ι, Real.exp (u i / (μ : ℝ)) * v i
  let quadraticMoment : ℝ := ∑ i : ι, (v i) ^ (2 : ℕ) * Real.exp (u i / (μ : ℝ))
  have hμ : (μ : ℝ) ≠ 0 := μ.property.ne'
  have homega_pos : 0 < ∑ i : ι, Real.exp (u i / (μ : ℝ)) := etaScaledSum_pos (μ := μ) u
  have hω_cont : ContDiffAt ℝ 2 omegaSlice 0 := by
    -- Restrict the denominator to the affine line through `u` in direction `v`.
    have hline : ContDiff ℝ 2 (fun t : ℝ ↦ u + t • v) := by
      fun_prop
    simpa [omegaSlice] using
      (etaScaledSum_contDiff_two (μ := μ)).contDiffAt.comp 0 hline.contDiffAt
  have hlog_cont : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) (omegaSlice 0) := by
    -- Positivity of the denominator keeps `log` on its smooth branch at the base point.
    simpa [omegaSlice] using (Real.contDiffAt_log.2 (etaScaledSum_pos (μ := μ) u).ne')
  have hω' : deriv omegaSlice 0 = (1 / (μ : ℝ)) * moment := by
    -- The first derivative is the softmax numerator before normalization.
    simpa [omegaSlice, moment] using
      (etaScaledSum_slice_hasDerivAt_zero (μ := μ) u v).deriv
  have hω'' : iteratedDeriv 2 omegaSlice 0 = ((1 / (μ : ℝ)) ^ (2 : ℕ)) * quadraticMoment := by
    -- The second derivative is the weighted quadratic moment before normalization.
    simpa [omegaSlice, quadraticMoment] using
      etaScaledSum_slice_secondDeriv_zero (μ := μ) u v
  have hlog₂ :
      iteratedDeriv 2 (fun t : ℝ ↦ Real.log (omegaSlice t)) 0 =
        iteratedDeriv 2 (fun s : ℝ ↦ Real.log s) (omegaSlice 0) * deriv omegaSlice 0 ^ (2 : ℕ) +
          deriv (fun s : ℝ ↦ Real.log s) (omegaSlice 0) * iteratedDeriv 2 omegaSlice 0 := by
    -- Apply the scalar second-derivative chain rule to `log ∘ omegaSlice`.
    simpa [Function.comp] using
      (iteratedDeriv_comp_two (g := fun s : ℝ ↦ Real.log s) (f := omegaSlice) (x := 0)
        hlog_cont hω_cont)
  have hlog_base :
      iteratedDeriv 2 (fun s : ℝ ↦ Real.log s) (omegaSlice 0) =
        -((∑ i : ι, Real.exp (u i / (μ : ℝ))) ^ (2 : ℕ))⁻¹ := by
    -- Differentiate `log` twice at the positive base denominator.
    calc
      iteratedDeriv 2 (fun s : ℝ ↦ Real.log s) (omegaSlice 0)
          = deriv (deriv (fun s : ℝ ↦ Real.log s)) (omegaSlice 0) := by
              simp [iteratedDeriv_succ]
      _ = deriv (fun s : ℝ ↦ s⁻¹) (omegaSlice 0) := by
            congr 1
            ext s
            rw [Real.deriv_log]
      _ = -((omegaSlice 0) ^ (2 : ℕ))⁻¹ := by
            rw [deriv_inv]
      _ = -((∑ i : ι, Real.exp (u i / (μ : ℝ))) ^ (2 : ℕ))⁻¹ := by
            simp [omegaSlice]
  have hquadratic :
      quadraticMoment / (∑ i : ι, Real.exp (u i / (μ : ℝ))) =
        ∑ i : ι,
          (Real.exp (u i / (μ : ℝ)) /
            (∑ k : ι, Real.exp (u k / (μ : ℝ)))) * (v i) ^ (2 : ℕ) := by
    -- Move the common denominator termwise inside the finite sum.
    change
      (∑ i : ι, (v i) ^ (2 : ℕ) * Real.exp (u i / (μ : ℝ))) /
          (∑ i : ι, Real.exp (u i / (μ : ℝ))) =
        ∑ i : ι,
          (Real.exp (u i / (μ : ℝ)) /
            (∑ k : ι, Real.exp (u k / (μ : ℝ)))) * (v i) ^ (2 : ℕ)
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [div_eq_mul_inv]
    ring
  have hmean :
      moment / (∑ i : ι, Real.exp (u i / (μ : ℝ))) =
        ∑ i : ι,
          (Real.exp (u i / (μ : ℝ)) /
            (∑ k : ι, Real.exp (u k / (μ : ℝ)))) * v i := by
    -- Normalize the first moment by the same common denominator.
    change
      (∑ i : ι, Real.exp (u i / (μ : ℝ)) * v i) /
          (∑ i : ι, Real.exp (u i / (μ : ℝ))) =
        ∑ i : ι,
          (Real.exp (u i / (μ : ℝ)) /
            (∑ k : ι, Real.exp (u k / (μ : ℝ)))) * v i
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [div_eq_mul_inv]
    ring
  have hconstmul :
      iteratedDeriv 2 (fun t : ℝ ↦ (μ : ℝ) * Real.log (omegaSlice t)) 0 =
        (μ : ℝ) * iteratedDeriv 2 (fun t : ℝ ↦ Real.log (omegaSlice t)) 0 := by
    simpa [smul_eq_mul] using
      (iteratedDeriv_const_smul_field (n := 2) (x := 0) (c := (μ : ℝ))
        (f := fun t : ℝ ↦ Real.log (omegaSlice t)))
  have hslice :
      directionalSlice (η μ) u v = fun t : ℝ ↦ (μ : ℝ) * Real.log (omegaSlice t) := by
    -- The directional slice of `η μ` along `v` is exactly `μ log` of the restricted denominator.
    funext t
    simp [directionalSlice, η, omegaSlice]
  -- Put the scalar `log` second-derivative formula into the moment-minus-square form.
  calc
    secondDirectionalDerivative (η μ) u v
        = iteratedDeriv 2 (fun t : ℝ ↦ (μ : ℝ) * Real.log (omegaSlice t)) 0 := by
            rw [secondDirectionalDerivative, hslice]
    _ = (μ : ℝ) * iteratedDeriv 2 (fun t : ℝ ↦ Real.log (omegaSlice t)) 0 := hconstmul
    _ = (μ : ℝ) *
          (iteratedDeriv 2 (fun s : ℝ ↦ Real.log s) (omegaSlice 0) * deriv omegaSlice 0 ^ (2 : ℕ) +
            deriv (fun s : ℝ ↦ Real.log s) (omegaSlice 0) * iteratedDeriv 2 omegaSlice 0) := by
          rw [hlog₂]
    _ = (μ : ℝ) *
          (-((∑ i : ι, Real.exp (u i / (μ : ℝ))) ^ (2 : ℕ))⁻¹ *
              (((1 / (μ : ℝ)) * moment) ^ (2 : ℕ)) +
            (∑ i : ι, Real.exp (u i / (μ : ℝ)))⁻¹ *
              (((1 / (μ : ℝ)) ^ (2 : ℕ)) * quadraticMoment)) := by
          rw [hlog_base, Real.deriv_log, hω', hω'']
          simp [omegaSlice]
    _ = (1 / (μ : ℝ)) *
          (quadraticMoment / (∑ i : ι, Real.exp (u i / (μ : ℝ))) -
            (moment / (∑ i : ι, Real.exp (u i / (μ : ℝ)))) ^ (2 : ℕ)) := by
          field_simp [hμ, homega_pos.ne']
          ring
    _ = (1 / (μ : ℝ)) *
          ((∑ j : ι,
              (Real.exp (u j / (μ : ℝ)) /
                (∑ k : ι, Real.exp (u k / (μ : ℝ)))) *
                (v j) ^ (2 : ℕ)) -
            (∑ j : ι,
              (Real.exp (u j / (μ : ℝ)) /
                (∑ k : ι, Real.exp (u k / (μ : ℝ)))) *
                v j) ^ (2 : ℕ)) := by
          rw [hquadratic, hmean]

/-- Helper for Proposition 7.21: the Hessian quadratic form of `η μ` is nonnegative and bounded
above by `(1 / μ) * (sup_j |v_j|)^2` on the original finite index type `ι`. -/
private theorem eta_hessianQuadraticForm_bounds
    (u v : EuclideanSpace ℝ ι) :
    0 ≤ inner ℝ v (hessian (η μ) u v) ∧
      inner ℝ v (hessian (η μ) u v) ≤
        (1 / (μ : ℝ)) *
          (Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |v j|)) ^ (2 : ℕ) := by
  let p : ι → ℝ := fun i ↦
    Real.exp (u i / (μ : ℝ)) / (∑ k : ι, Real.exp (u k / (μ : ℝ)))
  let variance : ℝ :=
    (∑ i : ι, p i * (v i) ^ (2 : ℕ)) - (∑ i : ι, p i * v i) ^ (2 : ℕ)
  have hcont : ContDiffAt ℝ 2 (η μ) u := (eta_contDiff_two (μ := μ)).contDiffAt
  have hdiff : DifferentiableAt ℝ (η μ) u := hcont.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ (η μ)) u :=
    differentiableAt_gradient_of_contDiffAt_two hcont
  have hω_pos : 0 < ∑ k : ι, Real.exp (u k / (μ : ℝ)) := etaScaledSum_pos (μ := μ) u
  have hp_pos : ∀ i : ι, 0 < p i := by
    intro i
    dsimp [p]
    exact div_pos (Real.exp_pos _) hω_pos
  have hp_nonneg : ∀ i : ι, 0 ≤ p i := fun i ↦ (hp_pos i).le
  have hp_sum : ∑ i : ι, p i = 1 := by
    -- The softmax weights are a positive partition of unity.
    let s : ℝ := ∑ k : ι, Real.exp (u k / (μ : ℝ))
    have hs_ne : s ≠ 0 := (etaScaledSum_pos (μ := μ) u).ne'
    dsimp [p]
    calc
      ∑ i : ι, Real.exp (u i / (μ : ℝ)) / (∑ k : ι, Real.exp (u k / (μ : ℝ)))
          = (∑ i : ι, Real.exp (u i / (μ : ℝ))) / s := by
              simp [s, div_eq_mul_inv, Finset.sum_mul]
      _ = s / s := by simp [s]
      _ = 1 := by field_simp [hs_ne]
  have hvar_nonneg : 0 ≤ variance := by
    have hmean_le :
        (∑ i : ι, p i * v i) ^ (2 : ℕ) ≤ ∑ i : ι, p i * (v i) ^ (2 : ℕ) :=
      weightedMeanSq_le_weightedSecondMoment p v hp_pos hp_sum
    dsimp [variance]
    nlinarith
  have hvar_le :
      variance ≤ (Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |v j|)) ^ (2 : ℕ) := by
    simpa [variance] using weightedVariance_le_sq_supAbs p v hp_nonneg hp_sum
  have hμinv_nonneg : 0 ≤ 1 / (μ : ℝ) := by
    exact one_div_nonneg.mpr μ.property.le
  have hformula :
      inner ℝ v (hessian (η μ) u v) = (1 / (μ : ℝ)) * variance := by
    -- Bridge the slice computation back to the Hessian only after the scalar formula is complete.
    calc
      inner ℝ v (hessian (η μ) u v) = secondDirectionalDerivative (η μ) u v := by
        exact (secondDirectionalDerivative_eq_hessian_quadratic_form hdiff hgrad).symm
      _ = (1 / (μ : ℝ)) * variance := by
        simpa [p, variance] using eta_secondDirectionalDerivative_eq (μ := μ) u v
  constructor
  · -- The softmax variance is nonnegative.
    rw [hformula]
    exact mul_nonneg hμinv_nonneg hvar_nonneg
  · -- The same variance is bounded by the maximal squared coordinate.
    rw [hformula]
    exact mul_le_mul_of_nonneg_left hvar_le hμinv_nonneg

/-- Helper for Proposition 7.21: transporting the owner-side `η μ` lower bound through the
canonical score map gives nonnegativity of the Hessian quadratic form of
`smoothMaxInnerApproximation a μ`. -/
private theorem smoothMaxInnerApproximation_hessian_quadratic_form_nonneg
    (x h : E) :
    0 ≤ inner ℝ (hessian (smoothMaxInnerApproximation a μ) x h) h := by
  have htransport :
      inner ℝ (hessian (smoothMaxInnerApproximation a μ) x h) h =
        inner ℝ (scoreMap a h) (hessian (η μ) (scoreMap a x) (scoreMap a h)) := by
    -- Route correction: transport the finished owner theorem through `scoreMap a` once.
    calc
      inner ℝ (hessian (smoothMaxInnerApproximation a μ) x h) h
          = inner ℝ h (hessian (smoothMaxInnerApproximation a μ) x h) := by
              rw [real_inner_comm]
      _ = inner ℝ (scoreMap a h) (hessian (η μ) (scoreMap a x) (scoreMap a h)) := by
            simpa [smoothMaxInnerApproximation_eq_eta_scoreMap, scoreMap] using
              (hessianQuadraticForm_comp_affine
                (f := η μ) (g := (scoreMap a).toContinuousAffineMap)
                x h ((eta_contDiff_two (μ := μ)).contDiffAt))
  rw [htransport]
  exact (eta_hessianQuadraticForm_bounds (μ := μ) (scoreMap a x) (scoreMap a h)).1

/-- Helper for Proposition 7.21: `smoothMaxInnerApproximation a μ` is `C²`, obtained by
keeping the original index type and composing `η μ` with the canonical score map. -/
private theorem smoothMaxInnerApproximation_contDiff_reindexed :
    ContDiff ℝ 2 (smoothMaxInnerApproximation a μ) := by
  -- Route correction: drop the `equivFin` transport and compose the original-index owner
  -- `η μ` directly with `scoreMap a`.
  have hsmooth : smoothMaxInnerApproximation a μ = η μ ∘ scoreMap a := by
    funext x
    rw [smoothMaxInnerApproximation_apply, eta_apply]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [scoreMap_apply]
  simpa [hsmooth] using
    (eta_contDiff_two (μ := μ)).comp (scoreMap a).contDiff

/-- Proposition 7.21: if the sign-symmetric box-hull support function of a nonnegative family
`(a i)_{i ∈ ι}` is bounded on the nonnegative orthant by `2 √n ‖·‖_D` for a diagonal
positive-definite matrix `D`, then the Hessian quadratic form of the log-sum-exp smoothing
`smoothMaxInnerApproximation a μ` is bounded by
`(4 n / μ) ‖h‖_D²`. -/
-- Proof sketch: the standard log-sum-exp Hessian estimate gives
-- `⟪∇²f_μ(x) h, h⟫ ≤ μ⁻¹ (max_i |⟪aᵢ, h⟫|)^2`. For arbitrary `h`, the nonnegative vector
-- `|h|` lies in `nonnegativeOrthant n`, and because each `aᵢ` is nonnegative one has
-- `|⟪aᵢ, h⟫| ≤ (ξ[signSymmetricConvexHull a] |h|).toReal`. Apply `hBoxSupport` at `|h|` and use
-- the diagonal-norm invariance `‖|h|‖[D] = ‖h‖[D]`.
theorem smoothMaxInnerApproximation_hessian_quadratic_form_le
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n)
    (hDdiag : D.1.IsDiag)
    (hBoxSupport :
      ∀ v : E, v ∈ nonnegativeOrthant n →
        (ξ[signSymmetricConvexHull a] v).toReal ≤ 2 * Real.sqrt n * ‖v‖[D])
    (x h : E) :
    inner ℝ (hessian (smoothMaxInnerApproximation a μ) x h) h ≤
      (4 : ℝ) * n / μ.1 * ‖h‖[D] ^ 2 := by
  let scoreSup : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ |scoreMap a h i|)
  let supportVal : ℝ := (ξ[signSymmetricConvexHull a] (pointwiseAbs h)).toReal
  have htransport :
      inner ℝ (hessian (smoothMaxInnerApproximation a μ) x h) h =
        inner ℝ (scoreMap a h) (hessian (η μ) (scoreMap a x) (scoreMap a h)) := by
    -- Transport the finished owner-side Hessian estimate through the canonical score map once.
    calc
      inner ℝ (hessian (smoothMaxInnerApproximation a μ) x h) h
          = inner ℝ h (hessian (smoothMaxInnerApproximation a μ) x h) := by
              rw [real_inner_comm]
      _ = inner ℝ (scoreMap a h) (hessian (η μ) (scoreMap a x) (scoreMap a h)) := by
            simpa [smoothMaxInnerApproximation_eq_eta_scoreMap, scoreMap] using
              (hessianQuadraticForm_comp_affine
                (f := η μ) (g := (scoreMap a).toContinuousAffineMap)
                x h ((eta_contDiff_two (μ := μ)).contDiffAt))
  have hηupper :
      inner ℝ (scoreMap a h) (hessian (η μ) (scoreMap a x) (scoreMap a h)) ≤
        (1 / (μ : ℝ)) * scoreSup ^ (2 : ℕ) := by
    simpa [scoreSup] using
      (eta_hessianQuadraticForm_bounds (μ := μ) (scoreMap a x) (scoreMap a h)).2
  have hscoreSup_le : scoreSup ≤ supportVal := by
    -- Each absolute score is bounded by the support value at `|h|`, so their finite supremum is.
    rw [Finset.sup'_le_iff]
    intro i hi
    dsimp [scoreSup, supportVal]
    simpa using
      absInner_le_signSymmetricConvexHullSupport_pointwiseAbs
        (a := a) (D := D) (μ := μ) ha_nonneg i h
  have hscoreSup_nonneg : 0 ≤ scoreSup := by
    exact le_trans (abs_nonneg (scoreMap a h (Classical.choice ‹Nonempty ι›)))
      (Finset.le_sup' (fun i : ι ↦ |scoreMap a h i|) (Finset.mem_univ _))
  have hsupport_nonneg : 0 ≤ supportVal := by
    exact le_trans hscoreSup_nonneg hscoreSup_le
  have hscoreSup_sq_le : scoreSup ^ (2 : ℕ) ≤ supportVal ^ (2 : ℕ) := by
    have hmul : scoreSup * scoreSup ≤ supportVal * supportVal := by
      exact mul_le_mul hscoreSup_le hscoreSup_le hscoreSup_nonneg hsupport_nonneg
    simpa [pow_two] using hmul
  have hsupport_le :
      supportVal ≤ 2 * Real.sqrt n * ‖pointwiseAbs h‖[D] := by
    -- Apply the source support hypothesis at the nonnegative vector `|h|`.
    simpa [supportVal] using
      hBoxSupport (pointwiseAbs h) (pointwiseAbs_mem_nonnegativeOrthant h)
  have hright_nonneg : 0 ≤ 2 * Real.sqrt n * ‖pointwiseAbs h‖[D] := by
    positivity
  have hsupport_sq_le :
      supportVal ^ (2 : ℕ) ≤ (2 * Real.sqrt n * ‖pointwiseAbs h‖[D]) ^ (2 : ℕ) := by
    have hmul : supportVal * supportVal ≤
        (2 * Real.sqrt n * ‖pointwiseAbs h‖[D]) *
          (2 * Real.sqrt n * ‖pointwiseAbs h‖[D]) := by
      exact mul_le_mul hsupport_le hsupport_le hsupport_nonneg hright_nonneg
    simpa [pow_two] using hmul
  have habsNorm :
      ‖pointwiseAbs h‖[D] = ‖h‖[D] :=
    positiveDefMatrixNorm_pointwiseAbs_eq_of_isDiag (a := a) (D := D) (μ := μ) hDdiag h
  have hbound_abs :
      (1 / (μ : ℝ)) * (2 * Real.sqrt n * ‖pointwiseAbs h‖[D]) ^ (2 : ℕ) ≤
        (4 : ℝ) * n / μ.1 * ‖h‖[D] ^ 2 := by
    -- Expand the square, simplify `√n ^ 2 = n`, and then rewrite the norm of `|h|`.
    rw [habsNorm]
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have hsqrt_sq : (Real.sqrt n) ^ (2 : ℕ) = (n : ℝ) := by
      simpa using (Real.sq_sqrt hn_nonneg)
    calc
      (1 / (μ : ℝ)) * (2 * Real.sqrt n * ‖h‖[D]) ^ (2 : ℕ)
          = (1 / (μ : ℝ)) * (4 * n * ‖h‖[D] ^ (2 : ℕ)) := by
              rw [pow_two, mul_assoc, ← mul_assoc (2 : ℝ), show (2 : ℝ) * 2 = 4 by norm_num,
                hsqrt_sq]
              ring
      _ = (4 : ℝ) * n / μ.1 * ‖h‖[D] ^ 2 := by
            field_simp [μ.property.ne']
            ring
  -- Combine the owner-side Hessian estimate with the support-function and diagonal-norm bridges.
  calc
    inner ℝ (hessian (smoothMaxInnerApproximation a μ) x h) h
        = inner ℝ (scoreMap a h) (hessian (η μ) (scoreMap a x) (scoreMap a h)) := htransport
    _ ≤ (1 / (μ : ℝ)) * scoreSup ^ (2 : ℕ) := hηupper
    _ ≤ (1 / (μ : ℝ)) * supportVal ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hscoreSup_sq_le (one_div_nonneg.mpr μ.property.le)
    _ ≤ (1 / (μ : ℝ)) * (2 * Real.sqrt n * ‖pointwiseAbs h‖[D]) ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hsupport_sq_le (one_div_nonneg.mpr μ.property.le)
    _ ≤ (4 : ℝ) * n / μ.1 * ‖h‖[D] ^ 2 := hbound_abs

-- Proof sketch: first prove the source-facing Hessian quadratic-form bound above, then combine it
-- with the `C²` regularity and convexity of `smoothMaxInnerApproximation a μ` and apply the
-- Chapter 2 owner bridge `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded`.
/-- The Chapter 2 smooth-convex owner view of Proposition 7.21 for the weighted norm `‖·‖[D]`. -/
theorem smoothMaxInnerApproximation_mem_F11_positiveDefMatrixNorm
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n)
    (hDdiag : D.1.IsDiag)
    (hBoxSupport :
      ∀ v : E, v ∈ nonnegativeOrthant n →
        (ξ[signSymmetricConvexHull a] v).toReal ≤ 2 * Real.sqrt n * ‖v‖[D]) :
    smoothMaxInnerApproximation a μ ∈
      𝓕[Real.toNNReal ((4 : ℝ) * n / μ.1), positiveDefMatrixNorm D.1 D.2]¹¹ := by
  have hcoef_nonneg : 0 ≤ ((4 : ℝ) * n / μ.1) := by
    exact div_nonneg (mul_nonneg (by positivity) (show 0 ≤ (n : ℝ) by positivity)) μ.property.le
  -- Package the regularity and two-sided Hessian bounds through the Chapter 2 owner theorem.
  refine
    (convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded
      (p := positiveDefMatrixNorm D.1 D.2)
      (L := Real.toNNReal ((4 : ℝ) * n / μ.1))
      (f := smoothMaxInnerApproximation a μ)
      (hf_C2 := smoothMaxInnerApproximation_contDiff_reindexed (a := a) (μ := μ))).2 ?_
  intro x h
  constructor
  · exact
      smoothMaxInnerApproximation_hessian_quadratic_form_nonneg
        (a := a) (μ := μ) x h
  · simpa [Real.toNNReal_of_nonneg hcoef_nonneg] using
      smoothMaxInnerApproximation_hessian_quadratic_form_le
        (a := a) (D := D) (μ := μ) ha_nonneg hDdiag hBoxSupport x h

/-- The gradient of the log-sum-exp smoothing is Lipschitz with respect to the weighted norm
`‖·‖[D]` and its dual norm `‖·‖[D,*]`, with constant `4 n / μ`, for the same diagonal
sign-symmetric support hypothesis. -/
-- Proof sketch: apply the canonical owner theorem
-- `smoothMaxInnerApproximation_mem_F11_positiveDefMatrixNorm` and then specialize the
-- `dualNorm_gradient_sub_le` consequence of `𝓕[L, p]¹¹`.
theorem smoothMaxInnerApproximation_gradient_lipschitz_diagonalWeightedNorm
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n)
    (hDdiag : D.1.IsDiag)
    (hBoxSupport :
      ∀ v : E, v ∈ nonnegativeOrthant n →
        (ξ[signSymmetricConvexHull a] v).toReal ≤ 2 * Real.sqrt n * ‖v‖[D])
    (x y : E) :
    ‖∇ (smoothMaxInnerApproximation a μ) x - ∇ (smoothMaxInnerApproximation a μ) y‖[D,*] ≤
      ((4 : ℝ) * n / μ.1) * ‖x - y‖[D] := by
  have hcoef_nonneg : 0 ≤ ((4 : ℝ) * n / μ.1) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have hμ_nonneg : 0 ≤ μ.1 := μ.property.le
    exact div_nonneg (mul_nonneg (by positivity) hn_nonneg) hμ_nonneg
  have hf :
      smoothMaxInnerApproximation a μ ∈
        𝓕[Real.toNNReal ((4 : ℝ) * n / μ.1), positiveDefMatrixNorm D.1 D.2]¹¹ :=
    smoothMaxInnerApproximation_mem_F11_positiveDefMatrixNorm
      (a := a) (D := D) (μ := μ) ha_nonneg hDdiag hBoxSupport
  -- The owner theorem immediately returns the weighted dual-gradient Lipschitz estimate.
  simpa [Real.toNNReal_of_nonneg hcoef_nonneg] using hf.dualNorm_gradient_sub_le x y

end

end
