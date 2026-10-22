/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RelativeDirection HessianLocalNorm MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.13 lies in the Chapter 5 simplex-monomial / barrier-compatibility domain.

Sampled owner declarations:
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the chapter owner for compatibility with a
  self-concordant barrier;
* `ambientMonomialXi` and `ξ_[a]` from `Definition_5_4_7_17`, the simplex-monomial owner and its
  ambient bridge;
* `monomialXi_secondDirectionalDerivative_eq_neg_mul_quantityS2` from `Theorem_5_4_7_11`, the
  owner-level formula for `D² ξ_a`;
* `monomialXi_thirdDirectionalDerivative_eq_mul_two_S3_add_three_mean_S2` from
  `Theorem_5_4_7_12`, the owner-level formula for `D³ ξ_a`;
* `positiveOrthantLogarithmicBarrier_localNorm_eq_norm_relativeDirection` from
  `Theorem_5_4_7_8`, the bridge identifying the barrier local norm with the relative-direction
  norm.

Source/core/bridge triage:
* source-facing: the textbook `β = 1` compatibility statement for the monomial `ξ_a`;
* core/canonical: `IsBetaCompatibleWith` on `positiveOrthant n`;
* bridge/view: the derivative identities for `ξ_a` and the local-norm formula for the orthant
  logarithmic barrier.

The public statement is already at the correct owner level, so this file keeps that owner surface
and avoids introducing any parallel wrapper around the ambient monomial or the barrier.
-/

private theorem positiveOrthant_eq_preimage_piIoi :
    (Xₙ : Set Eₙ) =
      ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph) ⁻¹'
        Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ)) := by
  ext x
  simp [EuclideanSpace.positiveOrthant]

private theorem positiveOrthant_isOpen : IsOpen (Xₙ : Set Eₙ) := by
  rw [positiveOrthant_eq_preimage_piIoi]
  exact (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi).preimage
    ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.continuous)

private theorem positiveOrthant_convex : Convex ℝ (Xₙ : Set Eₙ) := by
  rw [positiveOrthant_eq_preimage_piIoi]
  exact (convex_pi fun _ _ ↦ convex_Ioi (0 : ℝ)).linear_preimage
    (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap

private theorem positiveOrthant_interior_eq : interior (Xₙ : Set Eₙ) = Xₙ :=
  positiveOrthant_isOpen.interior_eq

private theorem positiveOrthant_interior_nonempty :
    (interior (Xₙ : Set Eₙ)).Nonempty := by
  have hx : WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)) ∈ Xₙ := by
    rw [EuclideanSpace.mem_positiveOrthant_iff]
    intro j
    exact (zero_lt_one : (0 : ℝ) < 1)
  exact ⟨_, by rwa [positiveOrthant_interior_eq]⟩

private theorem ambientMonomialXi_contDiffOn_positiveOrthant (a : Δ[n]) :
    ContDiffOn ℝ 3 (ambientMonomialXi a) (Xₙ : Set Eₙ) := by
  unfold ambientMonomialXi
  refine contDiffOn_prod fun i _ ↦ ?_
  have hcoord : ContDiffOn ℝ 3 (fun x : Eₙ ↦ x i) (Xₙ : Set Eₙ) := by
    simpa using
      (show ContDiffOn ℝ 3 (fun x : Eₙ ↦ x i) (Xₙ : Set Eₙ) from
        contDiffOn_piLp_apply (2 : ENNReal))
  exact hcoord.rpow_const_of_ne fun x hx ↦
    ne_of_gt ((EuclideanSpace.mem_positiveOrthant_iff.mp hx) i)

/-- Helper for Theorem 5.4.7.13: a single coordinate-positive half-space `{x | 0 < x i}` is
open. -/
private theorem coordinatePositiveSet_isOpen (i : Fin n) :
    IsOpen {x : Eₙ | 0 < x i} := by
  exact isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i)

/-- Helper for Theorem 5.4.7.13: a single coordinate-positive half-space `{x | 0 < x i}` is
convex. -/
private theorem coordinatePositiveSet_convex (i : Fin n) :
    Convex ℝ {x : Eₙ | 0 < x i} := by
  intro x hx y hy a b ha hb hab
  have hx' : 0 < x i := hx
  have hy' : 0 < y i := hy
  have hcomb : 0 < a * x i + b * y i := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by nlinarith
      nlinarith [hy', hb1]
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos ha' hx') (mul_nonneg hb (le_of_lt hy'))
  simpa [Pi.smul_apply, Pi.add_apply] using hcomb

/-- Helper for Theorem 5.4.7.13: the coordinate logarithmic barrier `x ↦ -log (x i)` is `C³` on
`{x | 0 < x i}`. -/
private theorem coordinateNegLog_contDiffOn (i : Fin n) :
    ContDiffOn ℝ 3 (fun x : Eₙ ↦ -Real.log (x i)) {x : Eₙ | 0 < x i} := by
  have hcoord :
      ContDiffOn ℝ 3 (fun y : Eₙ ↦ y i) {y : Eₙ | 0 < y i} := by
    simpa using
      (show ContDiffOn ℝ 3 (fun y : Eₙ ↦ y i) {y : Eₙ | 0 < y i} from
        contDiffOn_piLp_apply (2 : ENNReal))
  have hlog : ContDiffOn ℝ 3 (fun z : ℝ ↦ -Real.log z) (Set.Ioi (0 : ℝ)) := by
    intro z hz
    simpa using (Real.contDiffAt_log.2 (ne_of_gt hz)).neg.contDiffWithinAt
  simpa [Function.comp] using hlog.comp hcoord (fun y hy ↦ hy)

/-- Helper for Theorem 5.4.7.13: differentiating the affine slice of `x ↦ -log (x i)` gives the
expected inverse-affine formula. -/
private theorem coordinateNegLog_directionalSlice_deriv
    (i : Fin n) (x u : Eₙ) (t : ℝ) :
    deriv (directionalSlice (fun y : Eₙ ↦ -Real.log (y i)) x u) t =
      -u i * (u i * t + x i)⁻¹ := by
  change deriv (-fun s : ℝ ↦ Real.log (x i + s * u i)) t = -u i * (u i * t + x i)⁻¹
  calc
    deriv (-fun s : ℝ ↦ Real.log (x i + s * u i)) t
        = -deriv (fun s : ℝ ↦ Real.log (x i + s * u i)) t := by
            simpa using (deriv.neg (f := fun s : ℝ ↦ Real.log (x i + s * u i)) (x := t))
    _ = -deriv (fun s : ℝ ↦ Real.log (u i * s + x i)) t := by
          congr 1
          exact congrArg (fun f : ℝ → ℝ ↦ deriv f t) <| by
            funext s
            ring
    _ = -(u i * deriv (fun s : ℝ ↦ Real.log (s + x i)) (u i * t)) := by
          congr 1
          simpa [Function.comp] using
            deriv_comp_mul_left (u i) (fun s : ℝ ↦ Real.log (s + x i)) t
    _ = -(u i * (u i * t + x i)⁻¹) := by
          rw [deriv_comp_add_const, Real.deriv_log]
    _ = -u i * (u i * t + x i)⁻¹ := by ring

/-- Helper for Theorem 5.4.7.13: the second directional derivative of `x ↦ -log (x i)` is the
reciprocal-square coordinate formula. -/
private theorem coordinateNegLog_secondDirectionalDerivative_eq
    (i : Fin n) {x u : Eₙ} (hx : 0 < x i) :
    secondDirectionalDerivative (fun y : Eₙ ↦ -Real.log (y i)) x u =
      u i ^ (2 : ℕ) / x i ^ (2 : ℕ) := by
  calc
    secondDirectionalDerivative (fun y : Eₙ ↦ -Real.log (y i)) x u
        = deriv (deriv (directionalSlice (fun y : Eₙ ↦ -Real.log (y i)) x u)) 0 := by
            simp [secondDirectionalDerivative, iteratedDeriv_succ]
    _ = deriv (fun t : ℝ ↦ -u i * (u i * t + x i)⁻¹) 0 := by
          congr 1
          funext t
          rw [coordinateNegLog_directionalSlice_deriv]
    _ = (-u i) * deriv (fun t : ℝ ↦ (u i * t + x i)⁻¹) 0 := by
          rw [deriv_const_mul_field]
    _ = (-u i) * (u i * deriv (fun t : ℝ ↦ (t + x i)⁻¹) (u i * 0)) := by
          congr 1
          simpa [Function.comp] using
            deriv_comp_mul_left (u i) (fun t : ℝ ↦ (t + x i)⁻¹) 0
    _ = (-u i) * (u i * deriv Inv.inv (x i)) := by
          rw [deriv_comp_add_const]
          simp
    _ = (-u i) * (u i * (-(x i ^ (2 : ℕ))⁻¹)) := by
          rw [deriv_inv]
    _ = u i ^ (2 : ℕ) / x i ^ (2 : ℕ) := by
          field_simp [hx.ne']

/-- Helper for Theorem 5.4.7.13: the Hessian quadratic form of `x ↦ -log (x i)` matches the
reciprocal-square coordinate formula. -/
private theorem coordinateNegLog_hessianQuadraticForm_eq
    (i : Fin n) {x u : Eₙ} (hx : 0 < x i) :
    inner ℝ u (hessian (fun y : Eₙ ↦ -Real.log (y i)) x u) =
      u i ^ (2 : ℕ) / x i ^ (2 : ℕ) := by
  have hcont : ContDiffAt ℝ 2 (fun y : Eₙ ↦ -Real.log (y i)) x := by
    exact
      ((coordinateNegLog_contDiffOn (n := n) i).of_le (by norm_num)).contDiffAt
        ((coordinatePositiveSet_isOpen (n := n) i).mem_nhds hx)
  calc
    inner ℝ u (hessian (fun y : Eₙ ↦ -Real.log (y i)) x u)
        = secondDirectionalDerivative (fun y : Eₙ ↦ -Real.log (y i)) x u := by
            symm
            exact secondDirectionalDerivative_eq_hessian_quadratic_form hcont
    _ = u i ^ (2 : ℕ) / x i ^ (2 : ℕ) :=
      coordinateNegLog_secondDirectionalDerivative_eq (n := n) i hx

/-- Helper for Theorem 5.4.7.13: the Hessian local norm of `x ↦ -log (x i)` is `|u i| / x i`. -/
private theorem coordinateNegLog_hessianLocalNorm_eq_abs_div
    (i : Fin n) {x u : Eₙ} (hx : 0 < x i) :
    ‖u‖[(fun y : Eₙ ↦ -Real.log (y i)); x] = |u i| / x i := by
  rw [hessianLocalNorm_def, coordinateNegLog_hessianQuadraticForm_eq (n := n) i hx, ← div_pow,
    Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hx]

/-- Helper for Theorem 5.4.7.13: the third directional derivative of `x ↦ -log (x i)` is the
reciprocal-cubic coordinate formula. -/
private theorem coordinateNegLog_thirdDirectionalDerivative_eq
    (i : Fin n) {x u : Eₙ} (hx : 0 < x i) :
    thirdDirectionalDerivative (fun y : Eₙ ↦ -Real.log (y i)) x u =
      -2 * u i ^ (3 : ℕ) / x i ^ (3 : ℕ) := by
  have hinv :
      iteratedDeriv 2 (fun t : ℝ ↦ (u i * t + x i)⁻¹) 0 =
        2 * u i ^ (2 : ℕ) * x i ^ (-3 : ℤ) := by
    rw [iteratedDeriv_eq_iterate]
    simpa [pow_two] using congrArg (fun f : ℝ → ℝ ↦ f 0) (iter_deriv_inv_linear 2 (u i) (x i))
  calc
    thirdDirectionalDerivative (fun y : Eₙ ↦ -Real.log (y i)) x u
        = iteratedDeriv 2 (deriv (directionalSlice (fun y : Eₙ ↦ -Real.log (y i)) x u)) 0 := by
            simp [thirdDirectionalDerivative, iteratedDeriv_succ']
    _ = iteratedDeriv 2 (fun t : ℝ ↦ -u i * (u i * t + x i)⁻¹) 0 := by
          congr 1
          funext t
          rw [coordinateNegLog_directionalSlice_deriv]
    _ = -u i * iteratedDeriv 2 (fun t : ℝ ↦ (u i * t + x i)⁻¹) 0 := by
          simp
    _ = -u i * (2 * u i ^ (2 : ℕ) * x i ^ (-3 : ℤ)) := by
          rw [hinv]
    _ = -2 * u i ^ (3 : ℕ) / x i ^ (3 : ℕ) := by
          rw [zpow_neg]
          field_simp [hx.ne']

/-- Helper for Theorem 5.4.7.13: each coordinate logarithmic barrier is standard
self-concordant on its coordinate-positive half-space. -/
private theorem coordinateNegLog_isStandardSelfConcordantOn
    (i : Fin n) :
    IsStandardSelfConcordantOn {x : Eₙ | 0 < x i} (fun x : Eₙ ↦ -Real.log (x i)) := by
  refine
    { isOpen_domain := coordinatePositiveSet_isOpen (n := n) i
      contDiffOn := coordinateNegLog_contDiffOn (n := n) i
      convexOn := ?_
      third_deriv_bound := ?_ }
  · have hC2 :
        ContDiffOn ℝ 2 (fun x : Eₙ ↦ -Real.log (x i)) {x : Eₙ | 0 < x i} :=
      (coordinateNegLog_contDiffOn (n := n) i).of_le (by norm_num)
    refine
      (convexOn_iff_hessian_quadratic_form_nonneg
        (coordinatePositiveSet_isOpen (n := n) i)
        (coordinatePositiveSet_convex (n := n) i) hC2).2 ?_
    intro x hx u
    rw [real_inner_comm, coordinateNegLog_hessianQuadraticForm_eq (n := n) i hx]
    positivity
  · intro x hx u
    rw [coordinateNegLog_thirdDirectionalDerivative_eq (n := n) i hx,
      coordinateNegLog_hessianLocalNorm_eq_abs_div (n := n) i hx]
    have hx0 : 0 < x i := hx
    have habs :
        |(-2 : ℝ) * u i ^ (3 : ℕ) / x i ^ (3 : ℕ)| = 2 * (|u i| / x i) ^ (3 : ℕ) := by
      have hx3 : 0 < x i ^ (3 : ℕ) := by positivity
      have htwo : |(-2 : ℝ)| = 2 := by norm_num
      calc
        |(-2 : ℝ) * u i ^ (3 : ℕ) / x i ^ (3 : ℕ)|
            = 2 * |u i| ^ (3 : ℕ) / x i ^ (3 : ℕ) := by
                rw [abs_div, abs_mul, htwo, abs_of_pos hx3, abs_pow]
        _ = 2 * (|u i| / x i) ^ (3 : ℕ) := by
              rw [div_pow, div_eq_mul_inv]
              ring
    rw [habs]
    simp [one_mul, mul_comm]

/-- Helper for Theorem 5.4.7.13: each coordinate logarithmic barrier is a `1`-self-concordant
barrier on its coordinate-positive half-space. -/
private theorem coordinateNegLog_isSelfConcordantBarrierOnWith
    (i : Fin n) :
    IsSelfConcordantBarrierOnWith {x : Eₙ | 0 < x i} 1 (fun x : Eₙ ↦ -Real.log (x i)) := by
  refine
    { toIsStandardSelfConcordantOn := coordinateNegLog_isStandardSelfConcordantOn (n := n) i
      barrier_parameter_bound := ?_ }
  intro x hx u
  have hdiff : DifferentiableAt ℝ (fun y : Eₙ ↦ -Real.log (y i)) x := by
    exact
      ((coordinateNegLog_contDiffOn (n := n) i).contDiffAt
        ((coordinatePositiveSet_isOpen (n := n) i).mem_nhds hx)).differentiableAt (by norm_num)
  have hgrad :
      inner ℝ (gradient (fun y : Eₙ ↦ -Real.log (y i)) x) u = -u i / x i := by
    calc
      inner ℝ (gradient (fun y : Eₙ ↦ -Real.log (y i)) x) u
          = fderiv ℝ (fun y : Eₙ ↦ -Real.log (y i)) x u := by
              rw [← inner_gradient_left (y := u) hdiff]
      _ = lineDeriv ℝ (fun y : Eₙ ↦ -Real.log (y i)) x u := by
            symm
            exact hdiff.lineDeriv_eq_fderiv
      _ = deriv (directionalSlice (fun y : Eₙ ↦ -Real.log (y i)) x u) 0 := by
            rfl
      _ = -u i / x i := by
            rw [coordinateNegLog_directionalSlice_deriv]
            simp [div_eq_mul_inv]
  have hquad :
      inner ℝ u (hessian (fun y : Eₙ ↦ -Real.log (y i)) x u) =
        u i ^ (2 : ℕ) / x i ^ (2 : ℕ) :=
    coordinateNegLog_hessianQuadraticForm_eq (n := n) i hx
  have hquad' : u i ^ (2 : ℕ) / x i ^ (2 : ℕ) = (u i / x i) ^ (2 : ℕ) := by
    rw [div_pow]
  rw [hgrad, hquad]
  rw [hquad']
  have hexpr :
      2 * (-u i / x i) - (u i / x i) ^ (2 : ℕ) = 1 - (u i / x i + 1) ^ (2 : ℕ) := by
    ring
  rw [hexpr]
  exact sub_le_self _ (sq_nonneg _)

/-- Helper for Theorem 5.4.7.13: every constant function is a `0`-self-concordant barrier on the
whole space. -/
private theorem constant_isSelfConcordantBarrierOnWith_univ
    (c : ℝ) :
    IsSelfConcordantBarrierOnWith (Set.univ : Set Eₙ) 0 (fun _ : Eₙ ↦ c) := by
  have hself :
      IsSelfConcordantOnWith (Set.univ : Set Eₙ) 0 (fun _ : Eₙ ↦ c) := by
    simpa [quadraticAffineObjective] using
      (quadraticAffineObjective_isSelfConcordantOnWith_zero
        c (0 : Eₙ) (0 : Eₙ →L[ℝ] Eₙ) ContinuousLinearMap.isPositive_zero)
  refine
    { toIsStandardSelfConcordantOn := hself.of_le (by norm_num)
      barrier_parameter_bound := ?_ }
  intro x hx u
  have hzero_selfAdjoint :
      IsSelfAdjoint (0 : Eₙ →L[ℝ] Eₙ) := by
    simp
  have hgrad :
      gradient (fun _ : Eₙ ↦ c) = fun _ : Eₙ ↦ (0 : Eₙ) := by
    simpa [quadraticAffineObjective] using
      quadraticAffineObjective_gradient_eq c (0 : Eₙ) (0 : Eₙ →L[ℝ] Eₙ) hzero_selfAdjoint
  have hhess :
      hessian (fun _ : Eₙ ↦ c) x = 0 := by
    simpa [quadraticAffineObjective] using
      quadraticAffineObjective_hessian_eq c (0 : Eₙ) (0 : Eₙ →L[ℝ] Eₙ) hzero_selfAdjoint x
  rw [hgrad, hhess]
  simp

/-- Helper for Theorem 5.4.7.13: the finite coordinate logarithmic barrier on `s` is the
weighted sum of the coordinate `-log` terms. -/
private def coordinateSubsetLogBarrier (s : Finset (Fin n)) : Eₙ → ℝ :=
  fun x : Eₙ ↦ (-1 : ℝ) * Finset.sum s (fun i : Fin n ↦ Real.log (x i))

/-- Helper for Theorem 5.4.7.13: a finite coordinate subfamily of `-log` terms gives a
`s.card`-self-concordant barrier on the corresponding coordinate-positive domain. -/
private theorem coordinateSubsetLogBarrier_isSelfConcordantBarrierOnWith
    (s : Finset (Fin n)) :
    IsSelfConcordantBarrierOnWith
      {x : Eₙ | ∀ i : Fin n, i ∈ s → 0 < x i}
      (s.card : NNReal)
      (coordinateSubsetLogBarrier (n := n) s) := by
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is the constant zero barrier on the whole space.
      have hempty :
          coordinateSubsetLogBarrier (n := n) (∅ : Finset (Fin n)) = fun _ : Eₙ ↦ (0 : ℝ) := by
        funext x
        simp [coordinateSubsetLogBarrier]
      simpa [hempty] using constant_isSelfConcordantBarrierOnWith_univ (n := n) 0
  | @insert i s hi ih =>
      have hcoord :
          IsSelfConcordantBarrierOnWith
            {x : Eₙ | 0 < x i}
            1
            (fun x : Eₙ ↦ -Real.log (x i)) := by
        -- This coordinate summand is the one-dimensional logarithmic barrier on the `i`th axis.
        exact coordinateNegLog_isSelfConcordantBarrierOnWith (n := n) i
      have hdom :
          {x : Eₙ | ∀ j : Fin n, j ∈ s → 0 < x j} ∩ {x : Eₙ | 0 < x i} =
            {x : Eₙ | ∀ j : Fin n, j ∈ insert i s → 0 < x j} := by
        -- Intersecting the prior domain with the new coordinate constraint matches `insert`.
        ext x
        constructor
        · intro hx j hj
          rcases hx with ⟨hs, hiPos⟩
          rcases Finset.mem_insert.mp hj with rfl | hj'
          · exact hiPos
          · exact hs j hj'
        · intro hx
          refine ⟨?_, ?_⟩
          · intro j hj
            exact hx j (Finset.mem_insert_of_mem hj)
          · exact hx i (Finset.mem_insert_self i s)
      have hfun :
          coordinateSubsetLogBarrier (n := n) s +
              (fun x : Eₙ ↦ -Real.log (x i)) =
            coordinateSubsetLogBarrier (n := n) (insert i s) := by
        -- Adding the new coordinate term recovers the enlarged finite sum.
        funext x
        simp [coordinateSubsetLogBarrier, Finset.sum_insert, hi]
      have hparam :
          (s.card : NNReal) + 1 = ((insert i s).card : NNReal) := by
        norm_num [Finset.card_insert_of_notMem hi]
      -- Add the new coordinate barrier to the inductive barrier family.
      simpa [hdom, hfun, hparam] using ih.add hcoord

/-- Helper for Theorem 5.4.7.13: the affine source line has derivative equal to its direction. -/
private theorem affineLineHasDerivAt
    (x h : Eₙ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
  -- Differentiate the scalar multiple first and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const h).const_add x

/-- Helper for Theorem 5.4.7.13: the affine source line has vanishing second iterated
derivative. -/
private theorem affineLineIteratedDerivTwo
    {x h : Eₙ} :
    iteratedDeriv 2 (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ (0 : Eₙ) := by
  -- Once the affine line is differentiated to a constant, one more derivative vanishes.
  funext t
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ h := by
    funext s
    exact (affineLineHasDerivAt x h s).deriv
  rw [hderiv, deriv_const]

/-- Helper for Theorem 5.4.7.13: the affine source line has vanishing third iterated
derivative. -/
private theorem affineLineIteratedDerivThree
    {x h : Eₙ} :
    iteratedDeriv 3 (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ (0 : Eₙ) := by
  -- The third iterated derivative stays zero because the second iterated derivative is already
  -- identically zero.
  funext t
  rw [iteratedDeriv_succ, affineLineIteratedDerivTwo, deriv_const]

/-- Helper for Theorem 5.4.7.13: for scalar maps on `Eₙ`, the repeated second Fréchet derivative
agrees with the scalar second directional derivative. -/
private theorem vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative
    {f : Eₙ → ℝ} {x h : Eₙ} (hf : ContDiffAt ℝ 3 f x) :
    vectorSecondDirectionalDerivative f x h = secondDirectionalDerivative f x h := by
  let line : ℝ → Eₙ := fun s ↦ x + s • h
  have hf₂ : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hline₂ : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  have hcomp :=
    iteratedDeriv_vcomp_two (g := f) (f := line) (x := 0) (by simpa [line] using hf₂) hline₂
  have hline_deriv : deriv line 0 = h := by
    simpa [line] using (affineLineHasDerivAt x h 0).deriv
  -- Compare both owners through the same affine line slice.
  rw [secondDirectionalDerivative]
  symm
  simpa [line, Function.comp, hline_deriv, affineLineIteratedDerivTwo, directionalSlice,
    vectorSecondDirectionalDerivative] using hcomp

/-- Helper for Theorem 5.4.7.13: for scalar maps on `Eₙ`, the repeated third Fréchet derivative
agrees with the scalar third directional derivative. -/
private theorem vectorThirdDirectionalDerivative_eq_thirdDirectionalDerivative
    {f : Eₙ → ℝ} {x h : Eₙ} (hf : ContDiffAt ℝ 3 f x) :
    vectorThirdDirectionalDerivative f x h = thirdDirectionalDerivative f x h := by
  let line : ℝ → Eₙ := fun s ↦ x + s • h
  have hline₃ : ContDiffAt ℝ 3 line 0 := by
    fun_prop
  have hcomp :=
    iteratedDeriv_vcomp_three (g := f) (f := line) (x := 0) (by simpa [line] using hf) hline₃
  have hline_deriv : deriv line 0 = h := by
    simpa [line] using (affineLineHasDerivAt x h 0).deriv
  have hzero_left : iteratedFDeriv ℝ 2 f x ![(0 : Eₙ), h] = 0 := by
    exact (iteratedFDeriv ℝ 2 f x).map_coord_zero 0 rfl
  have hzero_right : iteratedFDeriv ℝ 2 f x ![h, (0 : Eₙ)] = 0 := by
    exact (iteratedFDeriv ℝ 2 f x).map_coord_zero 1 rfl
  -- The cubic chain rule collapses because all higher derivatives of the affine line vanish.
  rw [thirdDirectionalDerivative]
  symm
  calc
    iteratedDeriv 3 (directionalSlice f x h) 0
        = iteratedFDeriv ℝ 3 f x (fun _ ↦ h) +
            iteratedFDeriv ℝ 2 f x ![(0 : Eₙ), h] +
            2 • iteratedFDeriv ℝ 2 f x ![h, (0 : Eₙ)] := by
          simpa [directionalSlice, line, Function.comp, hline_deriv, affineLineIteratedDerivTwo,
            affineLineIteratedDerivThree] using hcomp
    _ = vectorThirdDirectionalDerivative f x h := by
          simp [hzero_left, hzero_right, vectorThirdDirectionalDerivative]

/-- Helper for Theorem 5.4.7.13: each coordinate of the affine slice `x + t h` stays positive
for all sufficiently small `t`. -/
private theorem coordinateSliceEventuallyPos
    (x : Xₙ) (h : Eₙ) :
    ∀ᶠ t in nhds (0 : ℝ), ∀ i : Fin n, 0 < (x : Eₙ) i + t * h i := by
  -- Control each coordinate separately and intersect the finitely many neighborhoods.
  refine Filter.eventually_all.2 ?_
  intro i
  have hcont : ContinuousAt (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (x : Eₙ) i) 0).add
        (continuousAt_id.const_mul (h i)))
  exact hcont.eventually (lt_mem_nhds (by simpa using x.2 i))

/-- Helper for Theorem 5.4.7.13: near `t = 0`, the monomial directional slice equals the
exponential of the weighted logarithmic slice. -/
private theorem monomialDirectionalSlice_eventuallyEq_expLogSum
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    directionalSlice (ambientMonomialXi a) x h =ᶠ[nhds (0 : ℝ)]
      fun t : ℝ ↦ Real.exp (∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) := by
  -- Rewrite `x^a` as `exp (a • log x)` on a neighborhood where every coordinate stays positive.
  filter_upwards [coordinateSliceEventuallyPos x h] with t ht
  rw [directionalSlice, ambientMonomialXi_apply, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simpa [mul_comm, smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_left_comm, mul_assoc] using
    (Real.rpow_def_of_pos (ht i) (a i))

/-- Helper for Theorem 5.4.7.13: the affine coordinate slice is smooth to every finite order. -/
private theorem coordinateAffineSlice_contDiffAt
    (x : Xₙ) (h : Eₙ) (k : ℕ) (i : Fin n) :
    ContDiffAt ℝ k (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 := by
  -- The coordinate slice is the sum of a constant and a linear map.
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    ((contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ ↦ (x : Eₙ) i) 0).add
      (contDiffAt_id.smul_const (h i)))

/-- Helper for Theorem 5.4.7.13: each coordinate logarithmic slice is smooth to every finite
order at the base point. -/
private theorem coordinateLogSlice_contDiffAt
    (x : Xₙ) (h : Eₙ) (k : ℕ) (i : Fin n) :
    ContDiffAt ℝ k (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 := by
  -- Compose the smooth logarithm at the positive coordinate `x i` with the affine slice.
  have hlog : ContDiffAt ℝ k (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i) := by
    simpa using
      (Real.contDiffAt_log.2 (x.2 i).ne' : ContDiffAt ℝ k (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i))
  have hlog' : ContDiffAt ℝ k (fun s : ℝ ↦ Real.log s) ((fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0) := by
    simpa using hlog
  simpa using hlog'.comp 0 (coordinateAffineSlice_contDiffAt x h k i)

/-- Helper for Theorem 5.4.7.13: the affine coordinate slice has constant derivative `h i`. -/
private theorem coordinateAffineSlice_deriv
    (x : Xₙ) (h : Eₙ) (i : Fin n) :
    deriv (fun t : ℝ ↦ (x : Eₙ) i + t * h i) = fun _ : ℝ ↦ h i := by
  -- Differentiate the constant-plus-linear affine slice pointwise.
  ext t
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using
    ((((hasDerivAt_id t).mul_const (h i)).const_add ((x : Eₙ) i)).deriv)

/-- Helper for Theorem 5.4.7.13: the second iterated derivative of `log` is `-(y^2)⁻¹`. -/
private theorem logIteratedDerivTwo (y : ℝ) :
    iteratedDeriv 2 Real.log y = -((y ^ (2 : ℕ))⁻¹) := by
  -- Reduce the second iterated derivative to the derivative of inversion.
  calc
    iteratedDeriv 2 Real.log y = iteratedDeriv 1 (deriv Real.log) y := by
      rw [iteratedDeriv_succ']
    _ = deriv Inv.inv y := by
      rw [Real.deriv_log']
      rw [iteratedDeriv_one]
    _ = -((y ^ (2 : ℕ))⁻¹) := by
      rw [deriv_inv]

/-- Helper for Theorem 5.4.7.13: the third iterated derivative of `log` is `2 * (y^3)⁻¹`. -/
private theorem logIteratedDerivThree (y : ℝ) :
    iteratedDeriv 3 Real.log y = 2 * ((y ^ (3 : ℕ))⁻¹) := by
  -- Reduce to the explicit second iterated derivative of inversion.
  calc
    iteratedDeriv 3 Real.log y = iteratedDeriv 2 (deriv Real.log) y := by
      rw [iteratedDeriv_succ']
    _ = iteratedDeriv 2 Inv.inv y := by
      rw [Real.deriv_log']
    _ = deriv^[2] Inv.inv y := by
      rw [← iteratedDeriv_eq_iterate]
    _ = (-1 : ℝ) ^ 2 * (Nat.factorial 2 : ℝ) * y ^ (-1 - 2 : ℤ) := by
      simpa using (iter_deriv_inv 2 y)
    _ = 2 * ((y ^ (3 : ℕ))⁻¹) := by
      rw [show (-1 - 2 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
      norm_num

/-- Helper for Theorem 5.4.7.13: the second derivative of one coordinate logarithmic slice is the
negative square of the corresponding relative-direction coordinate. -/
private theorem coordinateLogSlice_secondDeriv
    (x : Xₙ) (h : Eₙ) (i : Fin n) :
    iteratedDeriv 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 =
      -((δ[x](h) i) ^ (2 : ℕ)) := by
  have hlog : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i) := by
    simpa using
      (Real.contDiffAt_log.2 (x.2 i).ne' : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i))
  have hlog' : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) ((fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0) := by
    simpa using hlog
  have hcomp :
      iteratedDeriv 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 =
        iteratedDeriv 2 Real.log ((x : Eₙ) i) * deriv (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 ^ (2 : ℕ) +
          deriv Real.log ((x : Eₙ) i) * iteratedDeriv 2 (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 := by
    -- Apply the scalar second-order chain rule to `log ∘ affine`.
    simpa [Function.comp] using
      (iteratedDeriv_comp_two
        (x := 0)
        (g := fun s : ℝ ↦ Real.log s)
        (f := fun t : ℝ ↦ (x : Eₙ) i + t * h i)
        hlog'
        (coordinateAffineSlice_contDiffAt x h 2 i))
  -- The affine slice has vanishing second derivative, so only the quadratic term remains.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0
        = iteratedDeriv 2 Real.log ((x : Eₙ) i) * (h i) ^ (2 : ℕ) := by
            simpa [coordinateAffineSlice_deriv x h, iteratedDeriv_succ,
              iteratedDeriv_one, mul_comm, mul_left_comm, mul_assoc] using hcomp
    _ = (-(((x : Eₙ) i ^ (2 : ℕ))⁻¹)) * (h i) ^ (2 : ℕ) := by
          rw [logIteratedDerivTwo]
    _ = -((δ[x](h) i) ^ (2 : ℕ)) := by
          rw [relativeDirection_apply, div_pow]
          field_simp [(x.2 i).ne']

/-- Helper for Theorem 5.4.7.13: the third derivative of one coordinate logarithmic slice is
twice the cube of the corresponding relative-direction coordinate. -/
private theorem coordinateLogSlice_thirdDeriv
    (x : Xₙ) (h : Eₙ) (i : Fin n) :
    iteratedDeriv 3 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 =
      2 * ((δ[x](h) i) ^ (3 : ℕ)) := by
  have hlog : ContDiffAt ℝ 3 (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i) := by
    simpa using
      (Real.contDiffAt_log.2 (x.2 i).ne' : ContDiffAt ℝ 3 (fun s : ℝ ↦ Real.log s) ((x : Eₙ) i))
  have hlog' : ContDiffAt ℝ 3 (fun s : ℝ ↦ Real.log s) ((fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0) := by
    simpa using hlog
  have hcomp :
      iteratedDeriv 3 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 =
        iteratedDeriv 3 Real.log ((x : Eₙ) i) * deriv (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 ^ (3 : ℕ) +
          3 * iteratedDeriv 2 Real.log ((x : Eₙ) i) *
            iteratedDeriv 2 (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 *
            deriv (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 +
          deriv Real.log ((x : Eₙ) i) * iteratedDeriv 3 (fun t : ℝ ↦ (x : Eₙ) i + t * h i) 0 := by
    -- Apply the scalar third-order chain rule to `log ∘ affine`.
    simpa [Function.comp] using
      (iteratedDeriv_comp_three
        (x := 0)
        (g := fun s : ℝ ↦ Real.log s)
        (f := fun t : ℝ ↦ (x : Eₙ) i + t * h i)
        hlog'
        (coordinateAffineSlice_contDiffAt x h 3 i))
  -- The affine slice has no second or third derivatives, so only the cubic first-derivative term remains.
  calc
    iteratedDeriv 3 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0
        = iteratedDeriv 3 Real.log ((x : Eₙ) i) * (h i) ^ (3 : ℕ) := by
            simpa [coordinateAffineSlice_deriv x h, iteratedDeriv_succ,
              iteratedDeriv_one, mul_comm, mul_left_comm, mul_assoc] using hcomp
    _ = (2 * (((x : Eₙ) i ^ (3 : ℕ))⁻¹)) * (h i) ^ (3 : ℕ) := by
          rw [logIteratedDerivThree]
    _ = 2 * ((δ[x](h) i) ^ (3 : ℕ)) := by
          rw [relativeDirection_apply, div_pow]
          field_simp [(x.2 i).ne']

/-- Helper for Theorem 5.4.7.13: the first derivative of the weighted logarithmic slice at `0`
is the simplex-weighted mean of the relative direction. -/
private theorem logMonomialSliceDerivAtZero
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    deriv (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0 =
      Finset.univ.centerMass a (δ[x](h)) := by
  have hterm :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt
          (fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i))
          (a i * δ[x](h) i)
          0 := by
    intro i hi
    have hmul : HasDerivAt (fun t : ℝ ↦ t * h i) (h i) 0 := by
      simpa using (hasDerivAt_id 0).mul_const (h i)
    have haff : HasDerivAt (fun t : ℝ ↦ (x : Eₙ) i + t * h i) (h i) 0 := by
      simpa [add_comm] using hmul.const_add ((x : Eₙ) i)
    have hlog0 :
        HasDerivAt
          Real.log
          (((x : Eₙ) i + 0 * h i)⁻¹)
          ((x : Eₙ) i + 0 * h i) := by
      simpa using
        (Real.hasDerivAt_log
          (show (x : Eₙ) i + 0 * h i ≠ 0 by simpa using (x.2 i).ne'))
    have hlog :
        HasDerivAt
          (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i))
          (δ[x](h) i)
          0 := by
      simpa [relativeDirection_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (hlog0.comp 0 haff)
    simpa using hlog.const_mul (a i)
  have hsum :
      HasDerivAt
        (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i))
        (∑ i : Fin n, a i * δ[x](h) i)
        0 := by
    -- Differentiate each coordinate logarithm and sum the weighted contributions.
    simpa using
      (HasDerivAt.fun_sum
        (u := Finset.univ)
        (A := fun i : Fin n ↦ fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i))
        (A' := fun i : Fin n ↦ a i * δ[x](h) i)
        (x := 0)
        hterm)
  rw [hsum.deriv]
  simpa [centerMass_relativeDirection_eq_sum]

/-- Helper for Theorem 5.4.7.13: the second derivative of the weighted logarithmic slice at `0`
is the negative weighted square sum of the relative direction coordinates. -/
private theorem logMonomialSliceSecondDerivAtZero
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    iteratedDeriv 2 (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0 =
      -(a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) := by
  have hcont :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ContDiffAt ℝ 2
          (fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i))
          0 := by
    intro i hi
    simpa [smul_eq_mul] using
      (coordinateLogSlice_contDiffAt x h 2 i).const_smul (a i)
  -- Differentiate the finite weighted sum termwise and substitute the coordinate formula.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0
        = ∑ i : Fin n,
            iteratedDeriv 2 (fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i)) 0 := by
              simpa using (iteratedDeriv_fun_sum (I := Finset.univ) hcont)
    _ = ∑ i : Fin n,
          a i * iteratedDeriv 2 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simpa using
            (iteratedDeriv_const_mul_field
              (n := 2)
              (x := 0)
              (c := a i)
              (f := fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)))
    _ = ∑ i : Fin n, a i * (-(δ[x](h) i ^ (2 : ℕ))) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [coordinateLogSlice_secondDeriv x h i]
    _ = -(a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) := by
          rw [show (∑ i : Fin n, a i * (-(δ[x](h) i ^ (2 : ℕ)))) =
              -∑ i : Fin n, a i * (δ[x](h) i ^ (2 : ℕ)) by
                simp_rw [mul_neg]
                rw [Finset.sum_neg_distrib]]
          rfl

/-- Helper for Theorem 5.4.7.13: the third derivative of the weighted logarithmic slice at `0`
is twice the weighted cube sum of the relative direction coordinates. -/
private theorem logMonomialSliceThirdDerivAtZero
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    iteratedDeriv 3 (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0 =
      2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ)) := by
  have hcont :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ContDiffAt ℝ 3
          (fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i))
          0 := by
    intro i hi
    simpa [smul_eq_mul] using
      (coordinateLogSlice_contDiffAt x h 3 i).const_smul (a i)
  -- Differentiate the finite weighted sum termwise and substitute the coordinate cubic formula.
  calc
    iteratedDeriv 3 (fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)) 0
        = ∑ i : Fin n,
            iteratedDeriv 3 (fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i)) 0 := by
              simpa using (iteratedDeriv_fun_sum (I := Finset.univ) hcont)
    _ = ∑ i : Fin n,
          a i * iteratedDeriv 3 (fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)) 0 := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simpa using
            (iteratedDeriv_const_mul_field
              (n := 3)
              (x := 0)
              (c := a i)
              (f := fun t : ℝ ↦ Real.log ((x : Eₙ) i + t * h i)))
    _ = ∑ i : Fin n, a i * (2 * (δ[x](h) i ^ (3 : ℕ))) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [coordinateLogSlice_thirdDeriv x h i]
    _ = 2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ)) := by
          calc
            ∑ i : Fin n, a i * (2 * (δ[x](h) i ^ (3 : ℕ)))
                = ∑ i : Fin n, 2 * (a i * (δ[x](h) i ^ (3 : ℕ))) := by
                    refine Finset.sum_congr rfl fun i _ ↦ ?_
                    ring
            _ = 2 * ∑ i : Fin n, a i * (δ[x](h) i ^ (3 : ℕ)) := by
                  rw [← Finset.mul_sum]
            _ = 2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i ^ (3 : ℕ))) := by
                  rfl

/-- Helper for Theorem 5.4.7.13: the weighted mean of the relative direction is bounded above by
its Euclidean norm. -/
private theorem centerMass_relativeDirection_le_norm
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    Finset.univ.centerMass a (δ[x](h)) ≤ ‖δ[x](h)‖ := by
  -- Bound each coordinate by the ambient norm and then average with nonnegative simplex weights.
  rw [centerMass_relativeDirection_eq_sum]
  calc
    ∑ i : Fin n, a i * δ[x](h) i ≤ ∑ i : Fin n, a i * ‖δ[x](h)‖ := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      refine mul_le_mul_of_nonneg_left ?_ (stdSimplex.zero_le a i)
      calc
        δ[x](h) i ≤ |δ[x](h) i| := le_abs_self _
        _ = ‖δ[x](h) i‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖δ[x](h)‖ := by simpa using (PiLp.norm_apply_le (δ[x](h)) i)
    _ = ‖δ[x](h)‖ * ∑ i : Fin n, a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    _ = ‖δ[x](h)‖ := by
      rw [stdSimplex.sum_eq_one a]
      ring

/-- Helper for Theorem 5.4.7.13: the centered cubic moment is controlled by the centered second
moment times the norm gap `‖δ[x](h)‖ - ⟪a, δ[x](h)⟫`. -/
private theorem quantityS3_le_normGap_mul_quantityS2
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    quantityS3 a x h ≤
      (‖δ[x](h)‖ - Finset.univ.centerMass a (δ[x](h))) * quantityS2 a x h := by
  let m : ℝ := Finset.univ.centerMass a (δ[x](h))
  have hpoint :
      ∀ i : Fin n,
        (δ[x](h) i - m) ^ (3 : ℕ) ≤ (‖δ[x](h)‖ - m) * (δ[x](h) i - m) ^ (2 : ℕ) := by
    intro i
    have hcoord :
        δ[x](h) i - m ≤ ‖δ[x](h)‖ - m := by
      refine sub_le_sub_right ?_ m
      calc
        δ[x](h) i ≤ |δ[x](h) i| := le_abs_self _
        _ = ‖δ[x](h) i‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖δ[x](h)‖ := by simpa using (PiLp.norm_apply_le (δ[x](h)) i)
    have hsq : 0 ≤ (δ[x](h) i - m) ^ (2 : ℕ) := by positivity
    nlinarith
  -- Compare the finite sum termwise and then factor out the common norm-gap factor.
  calc
    quantityS3 a x h = ∑ i : Fin n, a i * (δ[x](h) i - m) ^ (3 : ℕ) := by
      simp [quantityS3_eq_sum, m]
    _ ≤ ∑ i : Fin n, a i * ((‖δ[x](h)‖ - m) * (δ[x](h) i - m) ^ (2 : ℕ)) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      exact mul_le_mul_of_nonneg_left (hpoint i) (stdSimplex.zero_le a i)
    _ = (‖δ[x](h)‖ - m) * ∑ i : Fin n, a i * (δ[x](h) i - m) ^ (2 : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    _ = (‖δ[x](h)‖ - m) * quantityS2 a x h := by
      simp [quantityS2_eq_sum, m]

/-- Helper for Theorem 5.4.7.13: the simplex monomial is strictly positive on the positive
orthant. -/
private theorem ambientMonomialXi_pos
    (a : Δ[n]) (x : Xₙ) :
    0 < ξ_[a] x := by
  -- Every coordinate factor `(x i)^(a i)` is positive because each coordinate of `x` is.
  rw [monomialXi_apply]
  exact Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (x.2 i) (a i)

/-- Helper for Theorem 5.4.7.13: the local norm of the positive-orthant logarithmic barrier
agrees with the norm of the relative direction. -/
private theorem standardLogarithmicBarrierAmbient_localNorm_eq_normRelativeDirection
    (x : Xₙ) (h : Eₙ) :
    ‖h‖[standardLogarithmicBarrierAmbient n; x] = ‖δ[x](h)‖ := by
  -- Route correction: reuse the imported owner theorem instead of re-deriving the local norm.
  convert positiveOrthantLogarithmicBarrier_localNorm_eq_norm_relativeDirection (n := n) x h

/-- Helper for Theorem 5.4.7.13: summing the coordinate `-log` terms over all coordinates
recovers the ambient logarithmic barrier. -/
private theorem fullCoordinateSubsetLogBarrier_eq_standardLogarithmicBarrierAmbient :
    coordinateSubsetLogBarrier (n := n) (Finset.univ : Finset (Fin n)) =
      standardLogarithmicBarrierAmbient n := by
  -- Normalize the finite-sum barrier presentation to the ambient barrier formula pointwise.
  funext x
  unfold coordinateSubsetLogBarrier standardLogarithmicBarrierAmbient
  have hFintype : instFintypeFin_nesterov n = Fin.fintype n := by
    apply Subsingleton.elim
  have huniv :
      (@Finset.univ (Fin n) (instFintypeFin_nesterov n)) =
        (@Finset.univ (Fin n) (Fin.fintype n)) := by
    rw [hFintype]
  -- Align the imported barrier's hidden `Fintype (Fin n)` argument with the local one.
  rw [huniv]
  ring

private theorem standardLogarithmicBarrierAmbient_isSelfConcordantBarrierOn_positiveOrthant :
    IsSelfConcordantBarrierOnWith (Xₙ : Set Eₙ) (n : NNReal)
      (standardLogarithmicBarrierAmbient n) := by
  have hdom :
      {x : Eₙ | ∀ i : Fin n, i ∈ (Finset.univ : Finset (Fin n)) → 0 < x i} = (Xₙ : Set Eₙ) := by
    ext x
    simp [EuclideanSpace.mem_positiveOrthant_iff]
  have hfun :
      coordinateSubsetLogBarrier (n := n) (Finset.univ : Finset (Fin n)) =
        standardLogarithmicBarrierAmbient n :=
    fullCoordinateSubsetLogBarrier_eq_standardLogarithmicBarrierAmbient (n := n)
  -- Specialize the finite-coordinate barrier family to the full coordinate set.
  simpa [hdom, hfun, Finset.card_univ, Fintype.card_fin] using
    coordinateSubsetLogBarrier_isSelfConcordantBarrierOnWith (n := n) (s := Finset.univ)

/-- Helper for Theorem 5.4.7.13: `quantityS2` expands into the weighted square sum minus the
square of the weighted mean. -/
private theorem quantityS2_eq_weightedSquareSum_sub_centerMassSq
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    quantityS2 a x h =
      (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) -
        Finset.univ.centerMass a (δ[x](h)) ^ (2 : ℕ) := by
  let m : ℝ := Finset.univ.centerMass a (δ[x](h))
  have hm : ∑ i : Fin n, a i * δ[x](h) i = m := by
    simp [centerMass_relativeDirection_eq_sum, m]
  rw [quantityS2_eq_sum]
  calc
    ∑ i : Fin n, a i * (δ[x](h) i - m) ^ (2 : ℕ)
        = ∑ i : Fin n,
            (a i * (δ[x](h) i) ^ (2 : ℕ) - 2 * m * (a i * δ[x](h) i) + a i * m ^ (2 : ℕ)) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              ring
    _ = (∑ i : Fin n, a i * (δ[x](h) i) ^ (2 : ℕ)) -
          2 * m * (∑ i : Fin n, a i * δ[x](h) i) +
          (∑ i : Fin n, a i) * m ^ (2 : ℕ) := by
            simp_rw [sub_eq_add_neg]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
            rw [← Finset.mul_sum (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i * δ[x](h) i) (2 * m)]
            rw [← Finset.sum_mul (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i) (m ^ (2 : ℕ))]
    _ = (∑ i : Fin n, a i * (δ[x](h) i) ^ (2 : ℕ)) - m ^ (2 : ℕ) := by
          rw [hm, stdSimplex.sum_eq_one a]
          ring
    _ = (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) - m ^ (2 : ℕ) := by
          rfl

/-- Helper for Theorem 5.4.7.13: `quantityS3` expands into the weighted cubic polynomial in the
relative direction and its weighted mean. -/
private theorem
    quantityS3_eq_weightedCube_sub_threeCenterMass_mul_weightedSquare_add_twoCenterMassCubed
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    quantityS3 a x h =
      (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ)) -
        3 * Finset.univ.centerMass a (δ[x](h)) * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
        2 * Finset.univ.centerMass a (δ[x](h)) ^ (3 : ℕ) := by
  let m : ℝ := Finset.univ.centerMass a (δ[x](h))
  have hm : ∑ i : Fin n, a i * δ[x](h) i = m := by
    simp [centerMass_relativeDirection_eq_sum, m]
  rw [quantityS3_eq_sum]
  calc
    ∑ i : Fin n, a i * (δ[x](h) i - m) ^ (3 : ℕ)
        = ∑ i : Fin n,
            (a i * (δ[x](h) i) ^ (3 : ℕ) -
              3 * m * (a i * (δ[x](h) i) ^ (2 : ℕ)) +
              3 * m ^ (2 : ℕ) * (a i * δ[x](h) i) -
              a i * m ^ (3 : ℕ)) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              ring
    _ = (∑ i : Fin n, a i * (δ[x](h) i) ^ (3 : ℕ)) -
          3 * m * (∑ i : Fin n, a i * (δ[x](h) i) ^ (2 : ℕ)) +
          3 * m ^ (2 : ℕ) * (∑ i : Fin n, a i * δ[x](h) i) -
          (∑ i : Fin n, a i) * m ^ (3 : ℕ) := by
            simp_rw [sub_eq_add_neg]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.sum_neg_distrib, Finset.sum_neg_distrib]
            rw [← Finset.mul_sum (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i * (δ[x](h) i) ^ (2 : ℕ)) (3 * m)]
            rw [← Finset.mul_sum (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i * δ[x](h) i) (3 * m ^ (2 : ℕ))]
            rw [← Finset.sum_mul (Finset.univ : Finset (Fin n))
              (fun i : Fin n ↦ a i) (m ^ (3 : ℕ))]
    _ = (∑ i : Fin n, a i * (δ[x](h) i) ^ (3 : ℕ)) -
          3 * m * (∑ i : Fin n, a i * (δ[x](h) i) ^ (2 : ℕ)) +
          2 * m ^ (3 : ℕ) := by
            rw [hm, stdSimplex.sum_eq_one a]
            ring
    _ = (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ)) -
          3 * m * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
          2 * m ^ (3 : ℕ) := by
            rfl

/-- Helper for Theorem 5.4.7.13: the combination `2 * quantityS3 + 3 * m * quantityS2` equals
the cubic relative-direction polynomial appearing in the third derivative of `ξ_[a]`. -/
private theorem twoQuantityS3_add_threeMean_quantityS2_eq_cubicRelativeDirectionPolynomial
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    2 * quantityS3 a x h +
        3 * Finset.univ.centerMass a (δ[x](h)) * quantityS2 a x h =
      Finset.univ.centerMass a (δ[x](h)) ^ (3 : ℕ) -
        3 * Finset.univ.centerMass a (δ[x](h)) *
          (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
        2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ)) := by
  rw [quantityS3_eq_weightedCube_sub_threeCenterMass_mul_weightedSquare_add_twoCenterMassCubed,
    quantityS2_eq_weightedSquareSum_sub_centerMassSq]
  ring

/-- Helper for Theorem 5.4.7.13: the third directional derivative of `ξ_[a]` equals `ξ_[a](x)`
times the cubic polynomial in the weighted mean, square sum, and cube sum of the relative
direction. -/
private theorem monomialXiThirdDirectionalDerivative_eq_mulCubicRelativeDirectionPolynomial
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    thirdDirectionalDerivative (ambientMonomialXi a) x h =
      ξ_[a] x *
        (Finset.univ.centerMass a (δ[x](h)) ^ (3 : ℕ) -
          3 * Finset.univ.centerMass a (δ[x](h)) *
            (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
          2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ))) := by
  let ψ : ℝ → ℝ :=
    fun t : ℝ ↦ ∑ i : Fin n, a i * Real.log ((x : Eₙ) i + t * h i)
  have hslice :
      thirdDirectionalDerivative (ambientMonomialXi a) x h =
        iteratedDeriv 3 (fun t : ℝ ↦ Real.exp (ψ t)) 0 := by
    -- Replace the monomial slice by the exponential of the weighted log-slice near `0`.
    rw [thirdDirectionalDerivative]
    have heq :
        directionalSlice (ambientMonomialXi a) x h =ᶠ[nhds (0 : ℝ)]
          fun t : ℝ ↦ Real.exp (ψ t) := by
      simpa [ψ] using monomialDirectionalSlice_eventuallyEq_expLogSum a x h
    exact Filter.EventuallyEq.iteratedDeriv_eq 3 heq
  have hψterm :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ContDiffAt ℝ 3 (fun t : ℝ ↦ a i * Real.log ((x : Eₙ) i + t * h i)) 0 := by
    intro i hi
    simpa [smul_eq_mul] using
      (coordinateLogSlice_contDiffAt x h 3 i).const_smul (a i)
  have hψcont : ContDiffAt ℝ 3 ψ 0 := by
    -- The weighted log-slice is a finite sum of `C³` coordinate logarithmic slices.
    classical
    simpa [ψ] using ContDiffAt.sum hψterm
  have hcomp :
      iteratedDeriv 3 (fun t : ℝ ↦ Real.exp (ψ t)) 0 =
        Real.exp (ψ 0) * deriv ψ 0 ^ (3 : ℕ) +
          3 * Real.exp (ψ 0) * iteratedDeriv 2 ψ 0 * deriv ψ 0 +
          Real.exp (ψ 0) * iteratedDeriv 3 ψ 0 := by
    -- Apply the scalar third-order chain rule to `exp ∘ ψ`.
    simpa [Function.comp, iteratedDeriv_succ, Real.deriv_exp] using
      (iteratedDeriv_comp_three
        (x := 0)
        (g := fun s : ℝ ↦ Real.exp s)
        (f := ψ)
        Real.contDiff_exp.contDiffAt
        hψcont)
  have hvalue : Real.exp (ψ 0) = ξ_[a] x := by
    -- Evaluate the log-slice at the base point and recover the ambient monomial value.
    rw [show ψ 0 = ∑ i : Fin n, a i * Real.log ((x : Eₙ) i) by simp [ψ], Real.exp_sum]
    calc
      ∏ i : Fin n, Real.exp (a i * Real.log ((x : Eₙ) i))
          = ∏ i : Fin n, Real.rpow ((x : Eₙ) i) (a i) := by
              refine Finset.prod_congr rfl fun i _ ↦ ?_
              symm
              simpa [mul_comm] using (Real.rpow_def_of_pos (x.2 i) (a i))
      _ = ξ_[a] x := by
            simp
  -- Assemble the chain-rule identity with the first, second, and third log-slice derivatives.
  calc
    thirdDirectionalDerivative (ambientMonomialXi a) x h
        = iteratedDeriv 3 (fun t : ℝ ↦ Real.exp (ψ t)) 0 := hslice
    _ = Real.exp (ψ 0) * deriv ψ 0 ^ (3 : ℕ) +
          3 * Real.exp (ψ 0) * iteratedDeriv 2 ψ 0 * deriv ψ 0 +
          Real.exp (ψ 0) * iteratedDeriv 3 ψ 0 := hcomp
    _ = ξ_[a] x *
          (Finset.univ.centerMass a (δ[x](h)) ^ (3 : ℕ) -
            3 * Finset.univ.centerMass a (δ[x](h)) *
              (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
            2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ))) := by
          rw [hvalue, logMonomialSliceDerivAtZero, logMonomialSliceSecondDerivAtZero,
            logMonomialSliceThirdDerivAtZero]
          ring

private theorem monomialXi_compatibility_bound
    (a : Δ[n]) {x : Eₙ} (hx : x ∈ Xₙ) (h : Eₙ) :
    (3 * ‖h‖[standardLogarithmicBarrierAmbient n; x]) •
        (-vectorSecondDirectionalDerivative (ambientMonomialXi a) x h) -
      vectorThirdDirectionalDerivative (ambientMonomialXi a) x h ∈
        ConvexCone.positive ℝ ℝ := by
  let xPos : Xₙ := ⟨x, hx⟩
  let m : ℝ := Finset.univ.centerMass a (δ[xPos](h))
  have hcont :
      ContDiffAt ℝ 3 (ambientMonomialXi a) x := by
    -- Restrict the global `C³` statement to the current positive base point.
    exact
      (ambientMonomialXi_contDiffOn_positiveOrthant a).contDiffAt
        (positiveOrthant_isOpen.mem_nhds hx)
  have hsecond :
      -vectorSecondDirectionalDerivative (ambientMonomialXi a) x h =
        ξ_[a] xPos * quantityS2 a xPos h := by
    -- Rewrite the repeated Fréchet second derivative to the scalar second-derivative formula.
    calc
      -vectorSecondDirectionalDerivative (ambientMonomialXi a) x h
          = -secondDirectionalDerivative (ambientMonomialXi a) x h := by
              rw [vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative hcont]
      _ = -(-(ξ_[a] xPos * quantityS2 a xPos h)) := by
            simpa using
              congrArg Neg.neg
                (monomialXi_secondDirectionalDerivative_eq_neg_mul_quantityS2
                  (a := a) (x := xPos) (h := h))
      _ = ξ_[a] xPos * quantityS2 a xPos h := by
            ring
  have hthird :
      vectorThirdDirectionalDerivative (ambientMonomialXi a) x h =
        ξ_[a] xPos * (2 * quantityS3 a xPos h + 3 * m * quantityS2 a xPos h) := by
    -- Rewrite the cubic derivative through the local polynomial formula and then collapse it to
    -- the `2 * S₃ + 3 * m * S₂` shape.
    rw [vectorThirdDirectionalDerivative_eq_thirdDirectionalDerivative hcont]
    calc
      thirdDirectionalDerivative (ambientMonomialXi a) x h
          = ξ_[a] xPos *
              (m ^ (3 : ℕ) -
                3 * m * (a ⬝ᵥ fun i : Fin n ↦ (δ[xPos](h) i) ^ (2 : ℕ)) +
                2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[xPos](h) i) ^ (3 : ℕ))) := by
            simpa [m] using
              monomialXiThirdDirectionalDerivative_eq_mulCubicRelativeDirectionPolynomial
                (a := a) (x := xPos) (h := h)
      _ = ξ_[a] xPos * (2 * quantityS3 a xPos h + 3 * m * quantityS2 a xPos h) := by
            rw [← twoQuantityS3_add_threeMean_quantityS2_eq_cubicRelativeDirectionPolynomial
              (a := a) (x := xPos) (h := h)]
  have hnorm :
      ‖h‖[standardLogarithmicBarrierAmbient n; (xPos : Eₙ)] = ‖δ[xPos](h)‖ := by
    -- The orthant logarithmic barrier local norm is the norm of the relative direction.
    simpa using standardLogarithmicBarrierAmbient_localNorm_eq_normRelativeDirection (n := n) xPos h
  have hm_le : m ≤ ‖δ[xPos](h)‖ := by
    -- The simplex-weighted mean cannot exceed the ambient norm.
    simpa [m] using centerMass_relativeDirection_le_norm a xPos h
  have hgap_nonneg : 0 ≤ ‖δ[xPos](h)‖ - m := sub_nonneg.mpr hm_le
  have hS2_nonneg : 0 ≤ quantityS2 a xPos h := quantityS2_nonneg a xPos h
  have hS3_bound :
      quantityS3 a xPos h ≤ (‖δ[xPos](h)‖ - m) * quantityS2 a xPos h := by
    -- The cubic centered moment is bounded by the norm gap times the quadratic one.
    simpa [m] using quantityS3_le_normGap_mul_quantityS2 a xPos h
  have hxi_pos : 0 < ξ_[a] xPos := ambientMonomialXi_pos a xPos
  -- Scalarize the cone membership and finish by arithmetic on the normalized moment formula.
  rw [ConvexCone.mem_positive, smul_eq_mul, hnorm, hsecond, hthird]
  have hgap_mul_nonneg : 0 ≤ (‖δ[xPos](h)‖ - m) * quantityS2 a xPos h := by
    exact mul_nonneg hgap_nonneg hS2_nonneg
  have hmain :
      0 ≤ 3 * (‖δ[xPos](h)‖ - m) * quantityS2 a xPos h - 2 * quantityS3 a xPos h := by
    nlinarith
  have hfinal :
      0 ≤ ξ_[a] xPos *
        (3 * (‖δ[xPos](h)‖ - m) * quantityS2 a xPos h - 2 * quantityS3 a xPos h) := by
    exact mul_nonneg (le_of_lt hxi_pos) hmain
  have hexpr :
      3 * ‖δ[xPos](h)‖ * (ξ_[a] xPos * quantityS2 a xPos h) -
          ξ_[a] xPos * (2 * quantityS3 a xPos h + 3 * m * quantityS2 a xPos h) =
        ξ_[a] xPos *
          (3 * (‖δ[xPos](h)‖ - m) * quantityS2 a xPos h - 2 * quantityS3 a xPos h) := by
    ring
  rw [hexpr]
  exact hfinal

-- Proof sketch: use the explicit formulas for the second and third directional derivatives of the
-- monomial `x ↦ x^a`, rewrite the third derivative in terms of the centered quantities `S₂` and
-- `S₃`, bound `S₃` by `S₂ * ‖δ_x(h)‖`, and then identify `‖δ_x(h)‖` with the local norm of the
-- positive-orthant logarithmic barrier.
/-- Theorem 5.4.7.13: for `a ∈ Δₙ`, the monomial
`ξ_a(x) = x^a = ∏_{i=1}^n (x^(i))^(a^(i))` is `1`-compatible with the logarithmic barrier
`F(x) = -\sum_{i=1}^n \log x^(i)` on the strict positive orthant `\mathbb{R}^n_{++}`. -/
theorem monomial_isOneCompatibleWith_positiveOrthantLogarithmicBarrier
    (a : Δ[n]) :
    IsBetaCompatibleWith
      Xₙ
      (ConvexCone.positive ℝ ℝ)
      (standardLogarithmicBarrierAmbient n)
      (1 : NNReal)
      (ambientMonomialXi a) := by
  refine
    { convex_domain := positiveOrthant_convex
      interior_nonempty := positiveOrthant_interior_nonempty
      one_le_parameter := by norm_num
      selfConcordantBarrier := ?_
      contDiffOn := ?_
      compatibility_bound := ?_ }
  · refine ⟨(n : NNReal), ?_⟩
    simpa [positiveOrthant_interior_eq] using
      standardLogarithmicBarrierAmbient_isSelfConcordantBarrierOn_positiveOrthant
  · simpa [positiveOrthant_interior_eq] using
      ambientMonomialXi_contDiffOn_positiveOrthant a
  · intro x hx h
    simpa [one_mul, positiveOrthant_interior_eq] using
      monomialXi_compatibility_bound a (by simpa [positiveOrthant_interior_eq] using hx) h
