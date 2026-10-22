/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Theorem 6.1 lies in the chapter's prox-smoothed maximization domain.

Sampled owner-style declarations:
- `smoothedPrimalObjective` in `Definition_6_30`, the chapter owner of the regularized-max
  smoothing formula;
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the canonical argmax-set owner for the
  textbook maximizer `u_μ(x)`;
- `smoothedPrimalObjective_apply` in `Definition_6_30`, the source-facing supremum formula for the
  smoothed objective;
- `smoothed_maximizer_unique` in `Proposition_6_6`, the chapter uniqueness theorem showing that
  convexity of `phiHat` together with strong convexity of `d2` is the actual structural input for
  uniqueness of the maximizer.

Best owner abstraction:
- source-facing: the prox-smoothed objective `smoothedPrimalObjective A Q 0 phiHat d2 μ` and its
  differentiability properties;
- core/canonical: `smoothedPrimalObjective` together with the pointwise argmax owner
  `smoothedPrimalObjectiveArgmax`;
- bridge/view: a choice `uMu : E₁ → E₂` recorded only through the membership hypothesis
  `uMu x ∈ smoothedPrimalObjectiveArgmax ... x`, used only when the selected maximizer itself
  appears in the conclusion.

Primitive data:
- the linear map `A`, feasible set `Q`, nonsmooth term `phiHat`, prox term `d2`, and smoothing
  parameter `μ`;
- unique existence of points in the canonical argmax set for each `x`;
- when needed for derivative-identification statements, a pointwise choice `uMu` of elements of the
  canonical argmax set.

Derived API:
- evaluation of the smoothed supremum at an argmax point;
- convexity and continuous differentiability of the smoothed objective from the source-faithful
  unique-maximizer assumption;
- derivative identification and Lipschitz control from a chosen argmax selection.

Source/core/bridge triage:
- source-facing: Theorem 6.1's five properties of the prox-smoothed objective;
- core/canonical: `smoothedPrimalObjective` and `smoothedPrimalObjectiveArgmax`;
- bridge/view: a selected map `uMu` into the argmax set.

The previous version introduced a parallel public predicate
`IsSmoothedObjectiveMaximizerSelection` and carried stronger ambient hypotheses than the owner
surface needs. This file now uses the canonical argmax owner directly while keeping the book's
unique-maximizer side condition explicit on the source-facing statements. -/

/-- Helper: any point of `smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x`
realizes the supremum defining the smoothed objective at `x`. -/
-- Proof sketch: the argmax property makes `u` an upper bound for the image of the penalized
-- maximand on `Q`, and evaluating at `u` gives the matching lower bound.
theorem smoothedPrimalObjectiveArgmax.value_eq
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {Q : Set E₂} {phiHat d2 : E₂ → ℝ} {μ : ℝ}
    {x : E₁} {u : E₂}
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x) :
    smoothedPrimalObjective A Q 0 phiHat d2 μ x =
      smoothedPrimalObjectiveMaximand A phiHat d2 μ x u := by
  -- Unpack the canonical argmax witness into feasibility and maximality on `Q`.
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q phiHat d2 μ x u).mp hu with
    ⟨hu_mem, hu_max⟩
  -- The selected maximizer yields the greatest element of the maximand image over `Q`.
  have hgreatest :
      IsGreatest
        (smoothedPrimalObjectiveMaximand A phiHat d2 μ x '' Q)
        (smoothedPrimalObjectiveMaximand A phiHat d2 μ x u) := by
    refine ⟨⟨u, hu_mem, rfl⟩, ?_⟩
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact (isMaxOn_iff.mp hu_max) v hv
  -- Rewrite the defining supremum by the attained value at the maximizer.
  rw [smoothedPrimalObjective_apply]
  rw [hgreatest.csSup_eq]
  simp [smoothedPrimalObjectiveMaximand]

/-- Auxiliary theorem: if the penalized maximand has a unique maximizer at `x`, then the smoothed
objective value at that maximizer agrees with the objective value at `x`. -/
theorem smoothedObjective_wellDefined
    [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q : Set E₂) (phiHat d2 : E₂ → ℝ) (μ : ℝ)
    (hargmax_unique : ∀ x, ∃! u, u ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x)
    (x : E₁) :
    ∃! u,
      u ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x ∧
        smoothedPrimalObjective A Q 0 phiHat d2 μ x =
          smoothedPrimalObjectiveMaximand A phiHat d2 μ x u := by
  -- Choose the unique canonical argmax point at `x`.
  rcases hargmax_unique x with ⟨u, hu, hu_unique⟩
  refine ⟨u, ⟨hu, smoothedPrimalObjectiveArgmax.value_eq hu⟩, ?_⟩
  intro v hv
  -- Uniqueness is inherited directly from the source-facing unique-maximizer hypothesis.
  exact hu_unique v hv.1

/-- Helper: for fixed `u`, the penalized maximand is affine, hence convex, as a
function of `x`. -/
-- Proof sketch: `x ↦ A x u` is exactly the continuous linear functional `A.flip u`, and the
-- remaining terms are constants in `x`.
lemma smoothedPrimalObjectiveMaximand_convexOn
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (phiHat d2 : E₂ → ℝ) (μ : ℝ) (u : E₂) :
    ConvexOn ℝ Set.univ (fun x : E₁ ↦ smoothedPrimalObjectiveMaximand A phiHat d2 μ x u) := by
  have hlinear : ConvexOn ℝ Set.univ (fun x : E₁ ↦ (A x) u) := by
    -- The dual pairing is the continuous linear functional `A.flip u`.
    simpa using (A.flip u).toLinearMap.convexOn convex_univ
  have hconst : ConvexOn ℝ Set.univ (fun _ : E₁ ↦ -phiHat u - μ * d2 u) :=
    convexOn_const _ convex_univ
  -- Rewrite the source maximand as the sum of that linear functional and a constant offset.
  convert hconst.add hlinear using 1
  ext x
  simp [smoothedPrimalObjectiveMaximand, sub_eq_add_neg, add_assoc]
  ring

/-- Auxiliary theorem: under the smoothing hypotheses, the smoothed objective is convex on all of
`E₁`. -/
-- Proof sketch: each map `x ↦ A x u - phiHat u - μ * d2 u` is affine in `x`, so the supremum
-- over `u ∈ Q` is convex once the source-level maximum is well defined at each `x` through a
-- unique argmax.
-- Semantic recall: the project owner for the source “proper closed convex” penalty hypothesis is
-- `ClosedConvexOn Q (fun u ↦ (phiHat u : WithTop ℝ))`; plain convexity is derived internally via
-- `ClosedConvexOn.convexOn_withTopRealPart`.
theorem smoothedObjective_convex
    [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q : Set E₂) (phiHat d2 : E₂ → ℝ) (μ : ℝ)
    (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (hphi_closed : ClosedConvexOn Q (fun u ↦ (phiHat u : WithTop ℝ)))
    (hd2_contDiff : ContDiffOn ℝ 1 d2 Q)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (hargmax_unique : ∀ x, ∃! u, u ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x) :
    ConvexOn ℝ Set.univ (smoothedPrimalObjective A Q 0 phiHat d2 μ) :=
by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  -- Derive the plain convexity view of `phiHat` from the closed-convex owner.
  have hphi : ConvexOn ℝ Q phiHat := by
    simpa [withTopRealPart] using hphi_closed.convexOn_withTopRealPart
  -- Evaluate the midpoint objective at its unique maximizer.
  rcases hargmax_unique z with ⟨uz, huz, _⟩
  rcases hargmax_unique x with ⟨ux, hux, _⟩
  rcases hargmax_unique y with ⟨uy, huy, _⟩
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q phiHat d2 μ z uz).mp huz with
    ⟨huz_mem, _⟩
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q phiHat d2 μ x ux).mp hux with
    ⟨_, hux_max⟩
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q phiHat d2 μ y uy).mp huy with
    ⟨_, huy_max⟩
  have hslicewise :
      smoothedPrimalObjectiveMaximand A phiHat d2 μ z uz ≤
        a * smoothedPrimalObjectiveMaximand A phiHat d2 μ x uz +
          b * smoothedPrimalObjectiveMaximand A phiHat d2 μ y uz := by
    -- The fixed-maximizer slice is affine in `x`, hence convex.
    simpa [z] using
      (smoothedPrimalObjectiveMaximand_convexOn A phiHat d2 μ uz).2
        (by simp) (by simp) ha hb hab
  have hupper_x :
      smoothedPrimalObjectiveMaximand A phiHat d2 μ x uz ≤
        smoothedPrimalObjective A Q 0 phiHat d2 μ x := by
    -- Compare the selected point `uz` with the actual maximizer at `x`.
    have hmax := (isMaxOn_iff.mp hux_max) uz huz_mem
    rw [smoothedPrimalObjectiveArgmax.value_eq hux]
    exact hmax
  have hupper_y :
      smoothedPrimalObjectiveMaximand A phiHat d2 μ y uz ≤
        smoothedPrimalObjective A Q 0 phiHat d2 μ y := by
    -- The same comparison works at `y`.
    have hmax := (isMaxOn_iff.mp huy_max) uz huz_mem
    rw [smoothedPrimalObjectiveArgmax.value_eq huy]
    exact hmax
  -- Assemble the convexity inequality from the attained-value identity at `z`.
  rw [smoothedPrimalObjectiveArgmax.value_eq huz]
  exact hslicewise.trans <| add_le_add (mul_le_mul_of_nonneg_left hupper_x ha)
    (mul_le_mul_of_nonneg_left hupper_y hb)

/-
Auxiliary declarations for Theorem 6.1: if `phiHat` is proper closed convex on `Q`, `d2` is `C¹`
and `1`-strongly convex on `Q`, and the displayed maximum has a unique maximizer at each `x`,
then the smoothed objective is convex and continuously differentiable. When a source-faithful
maximizer selection `uMu x ∈ smoothedPrimalObjectiveArgmax ... x` is fixed, the derivative is
`A.flip (uMu x)` at each `x`, and this derivative map is Lipschitz with constant
`(1 / μ) * ‖A‖^2`.
-/
section Theorem61

variable
  (A : E₁ →L[ℝ] StrongDual ℝ E₂)
  (Q : Set E₂) (phiHat d2 : E₂ → ℝ) {μ : ℝ}
  (uMu : E₁ → E₂)

/-- Helper: positive scaling upgrades the prox term from `1`-strong convexity to
`μ`-strong convexity. -/
-- Proof sketch: multiply the defining strong-convexity inequality for `d2` by the positive scalar
-- `μ` and reorganize the resulting coefficients.
lemma smoothedObjective_scaled_prox_strongConvexOn
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ) :
    StrongConvexOn Q μ (fun u ↦ μ * d2 u) := by
  refine ⟨hd2_strong.1, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Scale the unit-strong-convexity inequality by `μ > 0`.
  have hd2_ineq := hd2_strong.2 hx hy ha hb hab
  have hscaled := mul_le_mul_of_nonneg_left hd2_ineq hμ.le
  convert hscaled using 1
  · ring_nf

/-- Helper: for each fixed `x`, the slice
`u ↦ phiHat u + μ * d2 u - A x u` is `μ`-strongly convex on `Q`. -/
-- Proof sketch: combine the convex penalty `phiHat - A x` with the scaled strongly convex prox
-- term `μ d2`; the affine term `u ↦ A x u` does not change the strong-convexity modulus.
  lemma smoothedObjective_slice_strongConvexOn
    (hphi : ConvexOn ℝ Q phiHat)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (x : E₁) :
    StrongConvexOn Q μ (fun u ↦ phiHat u + μ * d2 u - A x u) := by
  have hscaled : StrongConvexOn Q μ (fun u ↦ μ * d2 u) :=
    smoothedObjective_scaled_prox_strongConvexOn Q d2 hd2_strong hμ
  have hlinear_convex : ConvexOn ℝ Q (fun u : E₂ ↦ -A x u) := by
    have hlinear_concave : ConcaveOn ℝ Q (fun u : E₂ ↦ A x u) := by
      -- The linear dual pairing is affine, so it is concave as well.
      simpa using (A x).toLinearMap.concaveOn hd2_strong.1
    exact hlinear_concave.neg
  have hperturb_convex : ConvexOn ℝ Q (fun u : E₂ ↦ phiHat u - A x u) := by
    -- Add the convex penalty to the affine perturbation.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hphi.add hlinear_convex
  -- Add the convex perturbation to the scaled prox term without changing the modulus.
  convert hscaled.add_convexOn hperturb_convex using 1
  ext u
  simp [sub_eq_add_neg, add_assoc]
  ring

variable [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]

/-- Helper for Theorem 6.1: an argmax point for the penalized dual maximand is a minimizer of the
corresponding positive slice `u ↦ phiHat u + μ * d2 u - A x u`. -/
lemma smoothedPrimalObjectiveArgmax.isMinOnSlice
    {x : E₁} {u : E₂}
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x) :
    u ∈ Q ∧ IsMinOn (fun v ↦ phiHat v + μ * d2 v - A x v) Q u := by
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q phiHat d2 μ x u).mp hu with
    ⟨hu_mem, hu_max⟩
  refine ⟨hu_mem, ?_⟩
  -- Negating the maximand converts the canonical max witness into the corresponding min witness.
  refine isMinOn_iff.mpr ?_
  intro v hv
  have hmax : smoothedPrimalObjectiveMaximand A phiHat d2 μ x v ≤
      smoothedPrimalObjectiveMaximand A phiHat d2 μ x u :=
    (isMaxOn_iff.mp hu_max) v hv
  have hu_neg :
      phiHat u + μ * d2 u - A x u =
        -smoothedPrimalObjectiveMaximand A phiHat d2 μ x u := by
    simp [smoothedPrimalObjectiveMaximand, sub_eq_add_neg]
    ring
  have hv_neg :
      phiHat v + μ * d2 v - A x v =
        -smoothedPrimalObjectiveMaximand A phiHat d2 μ x v := by
    simp [smoothedPrimalObjectiveMaximand, sub_eq_add_neg]
    ring
  rw [hu_neg, hv_neg]
  exact neg_le_neg hmax

/-- Helper for Theorem 6.1: the selected argmax map is Lipschitz with constant
`(1 / μ) * ‖A‖`. -/
lemma selectedArgmax_norm_sub_le
    (hphi : ConvexOn ℝ Q phiHat)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (huMu : ∀ x, uMu x ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x)
    (x y : E₁) :
    ‖uMu x - uMu y‖ ≤ ((1 / μ) * ‖A‖) * ‖x - y‖ := by
  rcases (smoothedPrimalObjectiveArgmax.isMinOnSlice
      (A := A) (Q := Q) (phiHat := phiHat) (d2 := d2) (μ := μ) (huMu x)) with
    ⟨hux_mem, hux_min⟩
  rcases (smoothedPrimalObjectiveArgmax.isMinOnSlice
      (A := A) (Q := Q) (phiHat := phiHat) (d2 := d2) (μ := μ) (huMu y)) with
    ⟨huy_mem, huy_min⟩
  have hstrong_x :
      StrongConvexOn Q μ (fun u ↦ phiHat u + μ * d2 u - A x u) :=
    smoothedObjective_slice_strongConvexOn A Q phiHat d2 hphi hd2_strong hμ x
  have hstrong_y :
      StrongConvexOn Q μ (fun u ↦ phiHat u + μ * d2 u - A y u) :=
    smoothedObjective_slice_strongConvexOn A Q phiHat d2 hphi hd2_strong hμ y
  -- Apply quadratic growth at the two selected minimizers and add the resulting inequalities.
  have hquad_x :
      (phiHat (uMu y) + μ * d2 (uMu y) - A x (uMu y)) ≥
        (phiHat (uMu x) + μ * d2 (uMu x) - A x (uMu x)) +
          (μ / 2) * ‖uMu y - uMu x‖ ^ (2 : ℕ) :=
    hstrong_x.quadratic_growth_of_isMinOn_of_mem hux_mem hux_min (uMu y) huy_mem
  have hquad_y :
      (phiHat (uMu x) + μ * d2 (uMu x) - A y (uMu x)) ≥
        (phiHat (uMu y) + μ * d2 (uMu y) - A y (uMu y)) +
          (μ / 2) * ‖uMu x - uMu y‖ ^ (2 : ℕ) :=
    hstrong_y.quadratic_growth_of_isMinOn_of_mem huy_mem huy_min (uMu x) hux_mem
  have hpair :
      μ * ‖uMu x - uMu y‖ ^ (2 : ℕ) ≤
        A (x - y) (uMu x - uMu y) := by
    have hadd := add_le_add hquad_x hquad_y
    have hnorm_sq :
        ‖uMu y - uMu x‖ ^ (2 : ℕ) = ‖uMu x - uMu y‖ ^ (2 : ℕ) := by
      rw [norm_sub_rev]
    have hrew :
        ((phiHat (uMu x) + μ * d2 (uMu x) - A x (uMu x)) +
            (μ / 2) * ‖uMu y - uMu x‖ ^ (2 : ℕ)) +
          ((phiHat (uMu y) + μ * d2 (uMu y) - A y (uMu y)) +
            (μ / 2) * ‖uMu x - uMu y‖ ^ (2 : ℕ)) =
        (phiHat (uMu x) + μ * d2 (uMu x) - A x (uMu x)) +
          (phiHat (uMu y) + μ * d2 (uMu y) - A y (uMu y)) +
            μ * ‖uMu x - uMu y‖ ^ (2 : ℕ) := by
      rw [hnorm_sq]
      ring
    rw [hrew] at hadd
    have hcancel :
        ((phiHat (uMu y) + μ * d2 (uMu y) - A x (uMu y)) +
            (phiHat (uMu x) + μ * d2 (uMu x) - A y (uMu x))) -
          ((phiHat (uMu x) + μ * d2 (uMu x) - A x (uMu x)) +
            (phiHat (uMu y) + μ * d2 (uMu y) - A y (uMu y))) =
        A (x - y) (uMu x - uMu y) := by
      simp [sub_eq_add_neg]
      ring
    linarith [hadd, hcancel]
  have hpair_le :
      A (x - y) (uMu x - uMu y) ≤ ‖A‖ * ‖x - y‖ * ‖uMu x - uMu y‖ := by
    -- Bound the bilinear perturbation by the operator norm of `A` and the norm of the selector
    -- displacement.
    have hfunctional :
        ‖A (x - y) (uMu x - uMu y)‖ ≤ ‖A (x - y)‖ * ‖uMu x - uMu y‖ := by
      simpa using (A (x - y)).le_opNorm (uMu x - uMu y)
    have hfunctional' :
        A (x - y) (uMu x - uMu y) ≤ ‖A (x - y)‖ * ‖uMu x - uMu y‖ :=
      le_trans (le_abs_self _) hfunctional
    exact hfunctional'.trans <| by
      gcongr
      exact A.le_opNorm (x - y)
  have hpair' :
      μ * ‖uMu x - uMu y‖ ^ (2 : ℕ) ≤
        ‖A‖ * ‖x - y‖ * ‖uMu x - uMu y‖ := by
    exact hpair.trans <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hpair_le
  by_cases hxy : uMu x = uMu y
  · simp [hxy]
    positivity
  · have hnorm_pos : 0 < ‖uMu x - uMu y‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr hxy
    have hlinear :
        μ * ‖uMu x - uMu y‖ ≤ ‖A‖ * ‖x - y‖ := by
      nlinarith [hμ, hnorm_pos, norm_nonneg (x - y), norm_nonneg A, hpair']
    have hdiv :
        ‖uMu x - uMu y‖ ≤ (‖A‖ * ‖x - y‖) / μ := by
      refine (le_div_iff₀ hμ).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hlinear
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- Helper for Theorem 6.1: after applying `A.flip`, the selected dual term is Lipschitz with
constant `(1 / μ) * ‖A‖²`. -/
lemma selectedArgmaxDualTerm_norm_sub_le
    (hphi : ConvexOn ℝ Q phiHat)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (huMu : ∀ x, uMu x ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x)
    (x y : E₁) :
    ‖A.flip (uMu x) - A.flip (uMu y)‖ ≤
      ((1 / μ) * ‖A‖ ^ (2 : ℕ)) * ‖x - y‖ := by
  calc
    ‖A.flip (uMu x) - A.flip (uMu y)‖ = ‖A.flip (uMu x - uMu y)‖ := by
      rw [← A.flip.map_sub]
    _ ≤ ‖A.flip‖ * ‖uMu x - uMu y‖ := A.flip.le_opNorm (uMu x - uMu y)
    _ = ‖A‖ * ‖uMu x - uMu y‖ := by rw [ContinuousLinearMap.opNorm_flip]
    _ ≤ ‖A‖ * (((1 / μ) * ‖A‖) * ‖x - y‖) := by
      gcongr
      exact selectedArgmax_norm_sub_le A Q phiHat d2 uMu hphi hd2_strong hμ huMu x y
    _ = ((1 / μ) * ‖A‖ ^ (2 : ℕ)) * ‖x - y‖ := by ring_nf

/-- Helper for Theorem 6.1: the first-order remainder at `x` is bounded by the quadratic
Lipschitz constant from the selector estimate. -/
lemma smoothedObjective_remainder_norm_le
    (hphi : ConvexOn ℝ Q phiHat)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (huMu : ∀ x, uMu x ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x)
    (x h : E₁) :
    ‖smoothedPrimalObjective A Q 0 phiHat d2 μ (x + h) -
        smoothedPrimalObjective A Q 0 phiHat d2 μ x -
        (A.flip (uMu x)) h‖ ≤
      ((1 / μ) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q phiHat d2 μ x (uMu x)).mp (huMu x) with
    ⟨hux_mem, hux_max⟩
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q phiHat d2 μ (x + h) (uMu (x + h))).mp
      (huMu (x + h)) with
    ⟨huh_mem, huh_max⟩
  let remainder : ℝ :=
    smoothedPrimalObjective A Q 0 phiHat d2 μ (x + h) -
      smoothedPrimalObjective A Q 0 phiHat d2 μ x -
      (A.flip (uMu x)) h
  have hshift_x :
      smoothedPrimalObjectiveMaximand A phiHat d2 μ (x + h) (uMu x) =
        smoothedPrimalObjectiveMaximand A phiHat d2 μ x (uMu x) + A h (uMu x) := by
    -- Moving from `x` to `x + h` changes the maximand only through the affine `A` term.
    simp [smoothedPrimalObjectiveMaximand, map_add, sub_eq_add_neg]
    ring
  have hshift_h :
      smoothedPrimalObjectiveMaximand A phiHat d2 μ (x + h) (uMu (x + h)) =
        smoothedPrimalObjectiveMaximand A phiHat d2 μ x (uMu (x + h)) +
          A h (uMu (x + h)) := by
    -- The same displacement identity holds for the maximizer at `x + h`.
    simp [smoothedPrimalObjectiveMaximand, map_add, sub_eq_add_neg]
    ring
  have hsup_x :
      sSup (smoothedPrimalObjectiveMaximand A phiHat d2 μ x '' Q) =
        smoothedPrimalObjectiveMaximand A phiHat d2 μ x (uMu x) := by
    simpa [smoothedPrimalObjective_apply] using
      smoothedPrimalObjectiveArgmax.value_eq (A := A) (Q := Q) (phiHat := phiHat)
        (d2 := d2) (μ := μ) (huMu x)
  have hsup_h :
      sSup (smoothedPrimalObjectiveMaximand A phiHat d2 μ (x + h) '' Q) =
        smoothedPrimalObjectiveMaximand A phiHat d2 μ (x + h) (uMu (x + h)) := by
    simpa [smoothedPrimalObjective_apply] using
      smoothedPrimalObjectiveArgmax.value_eq (A := A) (Q := Q) (phiHat := phiHat)
        (d2 := d2) (μ := μ) (huMu (x + h))
  have hnonneg : 0 ≤ remainder := by
    have hcompare :
        smoothedPrimalObjectiveMaximand A phiHat d2 μ (x + h) (uMu x) ≤
          smoothedPrimalObjectiveMaximand A phiHat d2 μ (x + h) (uMu (x + h)) :=
      (isMaxOn_iff.mp huh_max) (uMu x) hux_mem
    -- Rewrite the remainder as the selected value gap at `x + h`.
    have hremainder_eq :
        remainder =
          smoothedPrimalObjectiveMaximand A phiHat d2 μ (x + h) (uMu (x + h)) -
            smoothedPrimalObjectiveMaximand A phiHat d2 μ (x + h) (uMu x) := by
      dsimp [remainder]
      rw [hsup_h, hsup_x, hshift_x]
      ring
    rw [hremainder_eq]
    exact sub_nonneg.mpr hcompare
  have hupper :
      remainder ≤ A h (uMu (x + h) - uMu x) := by
    have hcompare :
        smoothedPrimalObjectiveMaximand A phiHat d2 μ x (uMu (x + h)) ≤
          smoothedPrimalObjectiveMaximand A phiHat d2 μ x (uMu x) :=
      (isMaxOn_iff.mp hux_max) (uMu (x + h)) huh_mem
    -- Compare the `x + h` optimizer against the `x` slice and isolate the affine discrepancy.
    have hremainder_eq :
        remainder =
          smoothedPrimalObjectiveMaximand A phiHat d2 μ x (uMu (x + h)) +
              A h (uMu (x + h)) -
            smoothedPrimalObjectiveMaximand A phiHat d2 μ x (uMu x) -
              A h (uMu x) := by
      dsimp [remainder]
      rw [hsup_h, hsup_x, hshift_h]
      ring
    rw [hremainder_eq]
    have hmap_sub : A h (uMu (x + h) - uMu x) = A h (uMu (x + h)) - A h (uMu x) := by
      rw [map_sub]
    rw [hmap_sub]
    linarith
  -- Control the scalar remainder by the operator norm of `A` and the selector Lipschitz bound.
  calc
    ‖smoothedPrimalObjective A Q 0 phiHat d2 μ (x + h) -
        smoothedPrimalObjective A Q 0 phiHat d2 μ x -
        (A.flip (uMu x)) h‖ = ‖remainder‖ := by
          dsimp [remainder]
    _ = remainder := Real.norm_of_nonneg hnonneg
    _ ≤ ‖A h (uMu (x + h) - uMu x)‖ := le_trans hupper (le_abs_self _)
    _ ≤ ‖A h‖ * ‖uMu (x + h) - uMu x‖ := by
          simpa using (A h).le_opNorm (uMu (x + h) - uMu x)
    _ ≤ (‖A‖ * ‖h‖) * ((((1 / μ) * ‖A‖) * ‖(x + h) - x‖)) := by
          gcongr
          · exact A.le_opNorm h
          · exact selectedArgmax_norm_sub_le A Q phiHat d2 uMu hphi hd2_strong hμ huMu (x + h) x
    _ = ((1 / μ) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
          simp
          ring_nf

/-- Auxiliary theorem: under the smoothing hypotheses, the derivative of the smoothed objective at
`x` is `A.flip (uMu x)`. -/
-- Proof sketch: combine the unique-maximizer form of Danskin's theorem with the canonical pairing
-- identity `(A.flip u) x = A x u`.
theorem nesterovSmoothedObjective_hasFDerivAt
    (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q)
    (hphi_closed : ClosedConvexOn Q (fun u ↦ (phiHat u : WithTop ℝ)))
    (hd2_contDiff : ContDiffOn ℝ 1 d2 Q)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (hargmax_unique : ∀ y, ∃! u, u ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ y)
    (huMu : ∀ y, uMu y ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ y)
    (x : E₁) :
    HasFDerivAt (smoothedPrimalObjective A Q 0 phiHat d2 μ) (A.flip (uMu x)) x :=
by
  have hphi : ConvexOn ℝ Q phiHat := by
    simpa [withTopRealPart] using hphi_closed.convexOn_withTopRealPart
  -- The quadratic remainder bound upgrades to a little-o estimate of order `‖h‖`.
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbigO :
      (fun h : E₁ ↦
        smoothedPrimalObjective A Q 0 phiHat d2 μ (x + h) -
          smoothedPrimalObjective A Q 0 phiHat d2 μ x -
          (A.flip (uMu x)) h) =O[nhds 0] fun h : E₁ ↦ (‖h‖ ^ (2 : ℕ) : ℝ) := by
    refine Asymptotics.IsBigO.of_bound ((1 / μ) * ‖A‖ ^ (2 : ℕ)) ?_
    filter_upwards [Filter.Eventually.of_forall fun h : E₁ ↦
      smoothedObjective_remainder_norm_le A Q phiHat d2 uMu hphi hd2_strong hμ huMu x h] with h hh
    have hpow_nonneg : 0 ≤ (‖h‖ ^ (2 : ℕ) : ℝ) := by positivity
    simpa [Real.norm_of_nonneg hpow_nonneg] using hh
  exact hbigO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

/-- Auxiliary theorem: under the smoothing hypotheses, the derivative selection
`x ↦ A.flip (uMu x)` is Lipschitz with constant `(1 / μ) * ‖A‖^2`. -/
-- Proof sketch: compare the optimality conditions at two points, use monotonicity of the convex
-- part together with convexity of `phiHat` and the `1`-strong convexity of `d2`, and bound the
-- adjoint difference by
-- `‖A‖^2 / μ`.
theorem smoothedObjective_gradient_lipschitz
    (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q)
    (hphi_closed : ClosedConvexOn Q (fun u ↦ (phiHat u : WithTop ℝ)))
    (hd2_contDiff : ContDiffOn ℝ 1 d2 Q)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (hargmax_unique : ∀ x, ∃! u, u ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x)
    (huMu : ∀ x, uMu x ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x) :
    LipschitzWith (Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ))) (fun x ↦ A.flip (uMu x)) :=
by
  have hphi : ConvexOn ℝ Q phiHat := by
    simpa [withTopRealPart] using hphi_closed.convexOn_withTopRealPart
  have hconst_nonneg : 0 ≤ (1 / μ) * ‖A‖ ^ (2 : ℕ) := by positivity
  refine LipschitzWith.of_dist_le' ?_
  intro x y
  -- Compose the selector Lipschitz estimate with the continuous linear map `A.flip`.
  simpa [dist_eq_norm, Real.toNNReal_of_nonneg hconst_nonneg] using
    selectedArgmaxDualTerm_norm_sub_le A Q phiHat d2 uMu hphi hd2_strong hμ huMu x y

/-- Auxiliary theorem: under the smoothing hypotheses, the smoothed objective is continuously
differentiable. -/
-- Proof sketch: recover the derivative field from a canonical selector given by the unique
-- maximizer hypothesis, then use the global Lipschitz estimate for that field.
theorem smoothedObjective_contDiff
    (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q)
    (hphi_closed : ClosedConvexOn Q (fun u ↦ (phiHat u : WithTop ℝ)))
    (hd2_contDiff : ContDiffOn ℝ 1 d2 Q)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (hargmax_unique : ∀ x, ∃! u, u ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x) :
    ContDiff ℝ 1 (smoothedPrimalObjective A Q 0 phiHat d2 μ) := by
  classical
  let uSel : E₁ → E₂ := fun x ↦ Classical.choose (hargmax_unique x)
  have huSel : ∀ x, uSel x ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x := by
    intro x
    exact (Classical.choose_spec (hargmax_unique x)).1
  have hgrad_lip :
      LipschitzWith (Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ))) (fun x ↦ A.flip (uSel x)) :=
    smoothedObjective_gradient_lipschitz A Q phiHat d2 uSel hQ_nonempty hQ_closed hQ_convex
      hphi_closed hd2_contDiff hd2_strong hμ hargmax_unique huSel
  -- Recover `C¹` regularity from the continuous derivative field and the pointwise derivative
  -- formula already proved for the chosen selector.
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun x ↦ A.flip (uSel x), hgrad_lip.continuous, ?_⟩
  intro x
  exact nesterovSmoothedObjective_hasFDerivAt A Q phiHat d2 uSel hQ_nonempty hQ_closed hQ_convex
    hphi_closed hd2_contDiff hd2_strong hμ hargmax_unique huSel x

-- Semantic recall: the source conclusions land naturally on the attained-value, convexity,
-- differentiability, derivative-identification, and Lipschitz owners already used in this file,
-- so the main item theorem packages those existing surfaces instead of introducing a wrapper.
/-- Theorem 6.1: let `Q` be a nonempty closed convex set, let `phiHat` be proper closed convex on
`Q`, and let `d2` be continuously differentiable and `1`-strongly convex on `Q`. For `μ > 0`, if
the penalized maximization problem defining `smoothedPrimalObjective A Q 0 phiHat d2 μ x` has a
unique maximizer for every `x` and `uMu` selects that maximizer, then the smoothed objective is
convex and continuously differentiable, its value at `x` is attained at `uMu x`, its derivative at
`x` is `A.flip (uMu x)`, and this derivative field is Lipschitz with constant
`(1 / μ) * ‖A‖^2`. -/
theorem nesterovSmoothedObjective_properties
    (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q)
    (hphi_closed : ClosedConvexOn Q (fun u ↦ (phiHat u : WithTop ℝ)))
    (hd2_contDiff : ContDiffOn ℝ 1 d2 Q)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (hargmax_unique : ∀ x, ∃! u, u ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x)
    (huMu : ∀ x, uMu x ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x) :
    (∀ x,
        smoothedPrimalObjective A Q 0 phiHat d2 μ x =
          smoothedPrimalObjectiveMaximand A phiHat d2 μ x (uMu x)) ∧
      ConvexOn ℝ Set.univ (smoothedPrimalObjective A Q 0 phiHat d2 μ) ∧
      ContDiff ℝ 1 (smoothedPrimalObjective A Q 0 phiHat d2 μ) ∧
      (∀ x, HasFDerivAt (smoothedPrimalObjective A Q 0 phiHat d2 μ) (A.flip (uMu x)) x) ∧
      LipschitzWith (Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ))) (fun x ↦ A.flip (uMu x)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    -- Evaluate the objective at the chosen source-facing maximizer.
    exact smoothedPrimalObjectiveArgmax.value_eq (huMu x)
  · -- The whole-space smoothed objective is convex.
    exact smoothedObjective_convex A Q phiHat d2 μ hQ_nonempty hQ_closed hQ_convex
      hphi_closed hd2_contDiff hd2_strong hμ hargmax_unique
  · -- The derivative field is continuous, so the smoothed objective is `C¹`.
    exact smoothedObjective_contDiff A Q phiHat d2 hQ_nonempty hQ_closed hQ_convex
      hphi_closed hd2_contDiff hd2_strong hμ hargmax_unique
  · intro x
    -- The chosen maximizer identifies the Fréchet derivative at `x`.
    exact nesterovSmoothedObjective_hasFDerivAt A Q phiHat d2 uMu hQ_nonempty hQ_closed hQ_convex
      hphi_closed hd2_contDiff hd2_strong hμ hargmax_unique huMu x
  · -- The derivative field is globally Lipschitz with the textbook constant.
    exact smoothedObjective_gradient_lipschitz A Q phiHat d2 uMu hQ_nonempty hQ_closed hQ_convex
      hphi_closed hd2_contDiff hd2_strong hμ hargmax_unique huMu

end Theorem61

end
