/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_10_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_10_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped ConstrainedArgmin EuclideanOrthant

universe u

variable {Q : Type u} [TopologicalSpace Q] {m : ℕ}

namespace LagrangianProblem

local notation "Λ" => EuclideanSpace ℝ (Fin m)

section

variable (problem : LagrangianProblem Q m) {lamStar : Λ} {ε : ℝ}

local notation "N" => Metric.closedBall lamStar ε ∩ ℝ₊^m

/- Theorem 1.10.4 lies in topological Lagrangian duality for inequality-constrained problems.

Sampled owner-style declarations:
* `LagrangianProblem.dualDomain`, `dualFeasibleSet`, `constraintVector`, and
  `lagrangianMinimizers` in `Definition_1_10_2`;
* `LagrangianProblem.dualFunction_le_affine_support_of_mem_lagrangianMinimizers` in
  `Proposition_1_10_7`;
* `LagrangianProblem.dualOptimalValue_le_primalOptimalValue` in `Proposition_1_10_8`;
* `objective_gap_ge_weighted_constraint_violation_of_lagrangian_minimizer` in `Chap03/Lemma_3_21`.

Best owner abstraction:
* the existing owner `problem : LagrangianProblem Q m` together with its derived dual-feasibility,
  constraint-vector, and Lagrangian-minimizer API.

Primitive data:
* `problem`
* the dual certificate point `lamStar`
* the radius `ε`
* the punctured orthant-neighborhood minimizer path `xPath`
* the limit point `xStar`

Derived API:
* `problem.dualDomain`
* `problem.dualFeasibleSet`
* `problem.constraintVector`
* `problem.lagrangianMinimizers`
* `problem.feasibleSet`
* `argmin[problem.feasibleSet] problem`

Source/core/bridge triage:
* source-facing: the textbook primal-optimality certificate extracted from nearby dual-feasible
  Lagrangian minimizers
* core/canonical: the owner `LagrangianProblem` and its derived APIs above
* bridge/view: the owner theorem `problem.dualFunction_eq_lagrangian`, used to recover
  neighborhood dual-domain membership from punctured-neighborhood Lagrangian minimizers

The previous statement fixed the primal ambient type to `EuclideanSpace ℝ (Fin n)` and carried
two local neighborhood aliases. The refined statement keeps the same mathematics, lowers the
primal ambient assumptions to the topological structure actually used, and phrases the
certificate directly on the orthant neighborhood because dual-domain membership there is already
derived from `hlamStar` at `lamStar` and from `hxPath` together with
`problem.dualFunction_eq_lagrangian` away from `lamStar`. -/

/-- Helper for Theorem 1.10.4: changing the multiplier changes the Lagrangian by the corresponding
constraint inner product. -/
lemma lagrangian_add_inner_sub_eq
    (x : Q) (lam₁ lam₂ : Λ) :
    problem.lagrangian x lam₁ + inner ℝ (problem.constraintVector x) (lam₂ - lam₁) =
      problem.lagrangian x lam₂ := by
  -- Rewrite the increment term against the second Lagrangian variable and simplify the affine
  -- difference in the multiplier.
  rw [LagrangianProblem.lagrangian, LagrangianProblem.lagrangian]
  have hcomm :
      inner ℝ (problem.constraintVector x) (lam₂ - lam₁) =
        inner ℝ (lam₂ - lam₁) (problem.constraintVector x) := by
    simpa using (real_inner_comm (problem.constraintVector x) (lam₂ - lam₁)).symm
  rw [hcomm, inner_sub_left]
  ring_nf

/-- Helper for Theorem 1.10.4: a forward variation in one multiplier coordinate adds the
corresponding weighted constraint value to the Lagrangian. -/
lemma lagrangian_forward_variation
    (x : Q) (lam : Λ) (j : Fin m) (t : ℝ) :
    problem.lagrangian x (lam + EuclideanSpace.single j t) =
      problem.lagrangian x lam + t * problem.constraints j x := by
  -- Expand the Lagrangian and isolate the contribution of the perturbed coordinate.
  rw [LagrangianProblem.lagrangian, LagrangianProblem.lagrangian, inner_add_left]
  simpa [problem.constraintVector_apply, mul_comm, add_assoc, add_left_comm, add_comm] using
    (congrArg
      (fun r : ℝ ↦ problem x + inner ℝ lam (problem.constraintVector x) + r)
      (EuclideanSpace.inner_single_left
        (i := j) (a := t) (v := problem.constraintVector x)))

/-- Helper for Theorem 1.10.4: a backward variation in one multiplier coordinate subtracts the
corresponding weighted constraint value from the Lagrangian. -/
lemma lagrangian_backward_variation
    (x : Q) (lam : Λ) (j : Fin m) (t : ℝ) :
    problem.lagrangian x (lam - EuclideanSpace.single j t) =
      problem.lagrangian x lam - t * problem.constraints j x := by
  -- Expand the Lagrangian and isolate the contribution of the perturbed coordinate.
  rw [LagrangianProblem.lagrangian, LagrangianProblem.lagrangian, inner_sub_left]
  simpa [problem.constraintVector_apply, mul_comm, add_assoc, add_left_comm, add_comm,
    sub_eq_add_neg] using
    (congrArg
      (fun r : ℝ ↦ problem x + inner ℝ lam (problem.constraintVector x) - r)
      (EuclideanSpace.inner_single_left
        (i := j) (a := t) (v := problem.constraintVector x)))

/-- Helper for Theorem 1.10.4: every punctured point of the orthant neighborhood lies in the dual
feasible set because the path hypothesis supplies a finite Lagrangian minimizer there. -/
lemma punctured_neighborhood_mem_dualFeasibleSet
    {lamStar : Λ} {ε : ℝ}
    (xPath : Λ → Q)
    (hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m →
          lam ≠ lamStar →
          xPath lam ∈ problem.lagrangianMinimizers lam)
    {lam : Λ} (hN : lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m) (hneq : lam ≠ lamStar) :
    lam ∈ problem.dualFeasibleSet := by
  -- The punctured-path minimizer realizes the dual value as a finite real number.
  have hx : xPath lam ∈ problem.lagrangianMinimizers lam :=
    hxPath hN hneq
  have hdualDomain : lam ∈ problem.dualDomain := by
    rw [problem.mem_dualDomain_iff, bot_lt_iff_ne_bot, problem.dualFunction_eq_lagrangian hx]
    exact EReal.coe_ne_bot _
  -- The orthant membership is already built into the neighborhood definition.
  rw [problem.mem_dualFeasibleSet_iff]
  exact ⟨hdualDomain, by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hN.2⟩

/-- Helper for Theorem 1.10.4: forward perturbations of a single multiplier coordinate force the
limiting constraint value at `xStar` to be nonpositive. -/
lemma constraint_nonpos_at_limit_of_forward_variation
    {lamStar : Λ} {ε : ℝ}
    (xPath : Λ → Q) (xStar : Q)
    (hlamStar : lamStar ∈ problem.dualFeasibleSet)
    (hmax : IsMaxOn problem.dualFunction problem.dualFeasibleSet lamStar)
    (hε : 0 < ε)
    (hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m →
          lam ≠ lamStar →
          xPath lam ∈ problem.lagrangianMinimizers lam)
    (hlim :
      Tendsto xPath
        (nhdsWithin lamStar ((Metric.closedBall lamStar ε ∩ ℝ₊^m) \ {lamStar}))
        (nhds xStar))
    (hcont : ContinuousAt problem.constraintVector xStar)
    (j : Fin m) :
    problem.constraints j xStar ≤ 0 := by
  let Nset : Set Λ := Metric.closedBall lamStar ε ∩ ℝ₊^m
  let forwardRay : ℝ → Λ := fun t ↦ lamStar + EuclideanSpace.single j t
  have hlamStar_nonneg : ∀ k : Fin m, 0 ≤ lamStar k :=
    (problem.mem_dualFeasibleSet_iff.mp hlamStar).2
  have hforwardMaps :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo 0 ε → forwardRay t ∈ Nset \ {lamStar} := by
    intro t ht
    constructor
    · constructor
      · rw [Metric.mem_closedBall, dist_eq_norm]
        simpa [forwardRay, Real.norm_eq_abs, abs_of_nonneg ht.1.le] using ht.2.le
      · rw [EuclideanSpace.mem_nonnegativeOrthant_iff]
        intro k
        by_cases hk : k = j
        · subst k
          simpa [forwardRay, EuclideanSpace.single] using add_nonneg (hlamStar_nonneg j) ht.1.le
        · simp [forwardRay, EuclideanSpace.single, hk, hlamStar_nonneg k]
    · intro hEq
      have hEq' : forwardRay t = lamStar := by simpa using hEq
      have hCoord := congrArg (fun lam : Λ ↦ lam j) hEq'
      simp [forwardRay, EuclideanSpace.single] at hCoord
      have : (0 : ℝ) < 0 := by simpa [hCoord] using ht.1
      exact this.false
  have hsingleBasis :
      ∀ t : ℝ, (EuclideanSpace.single j t : Λ) = t • (EuclideanSpace.single j (1 : ℝ) : Λ) := by
    intro t
    ext k
    by_cases hk : k = j
    · subst k
      simp [EuclideanSpace.single]
    · simp [EuclideanSpace.single, hk]
  have hforwardEq :
      forwardRay =
        fun t : ℝ ↦ lamStar + (t : ℝ) • (EuclideanSpace.single j (1 : ℝ) : Λ) := by
    funext t
    dsimp [forwardRay]
    rw [hsingleBasis]
  have hforwardContinuous : ContinuousAt forwardRay 0 := by
    rw [hforwardEq]
    have hsingle :
        Continuous fun t : ℝ ↦ (t : ℝ) • (EuclideanSpace.single j (1 : ℝ) : Λ) :=
      continuous_id.smul continuous_const
    exact (continuous_const.add hsingle).continuousAt
  have hforwardToNhds :
      Tendsto forwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
        (nhds lamStar) := by
    have hToZero :=
      hforwardContinuous.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioo 0 ε) ≤ nhds (0 : ℝ) from nhdsWithin_le_nhds)
    have hzero : forwardRay 0 = lamStar := by
      simp [forwardRay, EuclideanSpace.single]
    simpa [hzero] using hToZero
  have hforwardToPrincipal :
      Tendsto forwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
        (Filter.principal (Nset \ {lamStar})) := by
    rw [Filter.tendsto_def]
    intro s hs
    rw [Filter.mem_principal] at hs
    exact Filter.mem_of_superset self_mem_nhdsWithin fun t ht ↦ hs (hforwardMaps ht)
  have hforwardToNhdsWithin :
      Tendsto forwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
        (nhdsWithin lamStar (Nset \ {lamStar})) := by
    -- Package the ordinary convergence together with eventual membership in the punctured
    -- neighborhood.
    change Tendsto forwardRay
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
      (nhds lamStar ⊓ Filter.principal (Nset \ {lamStar}))
    simpa using hforwardToNhds.inf hforwardToPrincipal
  have hpathAlongForward :
      Tendsto (fun t : ℝ ↦ xPath (forwardRay t))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
        (nhds xStar) :=
    hlim.comp hforwardToNhdsWithin
  have hcoordCont :
      ContinuousAt (fun x : Q ↦ problem.constraintVector x j) xStar := by
    have hofLp :
        ContinuousAt (fun x : Q ↦ WithLp.ofLp (problem.constraintVector x)) xStar := by
      simpa [Function.comp] using
        ((PiLp.continuous_ofLp 2 (fun _ : Fin m ↦ ℝ)).continuousAt.comp hcont)
    simpa [Function.comp] using ((continuous_apply j).continuousAt.comp hofLp)
  have hcoordTendsto :
      Tendsto (fun t : ℝ ↦ problem.constraints j (xPath (forwardRay t)))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
        (nhds (problem.constraints j xStar)) := by
    simpa [problem.constraintVector_apply] using hcoordCont.tendsto.comp hpathAlongForward
  have hEventuallyNonpos :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioo 0 ε),
        problem.constraints j (xPath (forwardRay t)) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hmem : forwardRay t ∈ Nset \ {lamStar} := hforwardMaps ht
    have hxray : xPath (forwardRay t) ∈ problem.lagrangianMinimizers (forwardRay t) :=
      hxPath hmem.1 hmem.2
    have hmaxRay :
        problem.dualFunction (forwardRay t) ≤ problem.dualFunction lamStar :=
      (isMaxOn_iff.mp hmax) (forwardRay t)
        (problem.punctured_neighborhood_mem_dualFeasibleSet xPath hxPath hmem.1 hmem.2)
    have hsupport :
        problem.dualFunction lamStar ≤
          problem.dualFunction (forwardRay t) +
            (inner ℝ (problem.constraintVector (xPath (forwardRay t)))
              (lamStar - forwardRay t) : EReal) := by
      simpa [forwardRay] using
        (problem.dualFunction_le_affine_support_of_mem_lagrangianMinimizers
          (lam₁ := forwardRay t) (lam₂ := lamStar) (x₁ := xPath (forwardRay t)) hxray)
    have hsupport' :
        problem.dualFunction lamStar ≤
          ((problem.lagrangian (xPath (forwardRay t)) lamStar : ℝ) : EReal) := by
      calc
        problem.dualFunction lamStar ≤
            problem.dualFunction (forwardRay t) +
              (inner ℝ (problem.constraintVector (xPath (forwardRay t)))
                (lamStar - forwardRay t) : EReal) := hsupport
        _ =
            ((problem.lagrangian (xPath (forwardRay t)) lamStar : ℝ) : EReal) := by
          rw [problem.dualFunction_eq_lagrangian hxray]
          exact_mod_cast
            (problem.lagrangian_add_inner_sub_eq
              (x := xPath (forwardRay t))
              (lam₁ := forwardRay t) (lam₂ := lamStar))
    have hlagLe :
        problem.lagrangian (xPath (forwardRay t)) (forwardRay t) ≤
          problem.lagrangian (xPath (forwardRay t)) lamStar := by
      have hlagLeEReal :
          ((problem.lagrangian (xPath (forwardRay t)) (forwardRay t) : ℝ) : EReal) ≤
            ((problem.lagrangian (xPath (forwardRay t)) lamStar : ℝ) : EReal) := by
        calc
          ((problem.lagrangian (xPath (forwardRay t)) (forwardRay t) : ℝ) : EReal) =
              problem.dualFunction (forwardRay t) := by
            symm
            exact problem.dualFunction_eq_lagrangian hxray
          _ ≤ problem.dualFunction lamStar := hmaxRay
          _ ≤ ((problem.lagrangian (xPath (forwardRay t)) lamStar : ℝ) : EReal) := hsupport'
      exact_mod_cast hlagLeEReal
    have hstep :
        problem.lagrangian (xPath (forwardRay t)) (forwardRay t) =
          problem.lagrangian (xPath (forwardRay t)) lamStar +
            t * problem.constraints j (xPath (forwardRay t)) := by
      simpa [forwardRay] using
        (problem.lagrangian_forward_variation
          (x := xPath (forwardRay t)) (lam := lamStar) (j := j) (t := t))
    rw [hstep] at hlagLe
    have hmul : t * problem.constraints j (xPath (forwardRay t)) ≤ 0 := by
      linarith
    by_contra hpos
    have hpos' : 0 < problem.constraints j (xPath (forwardRay t)) := lt_of_not_ge hpos
    have : 0 < t * problem.constraints j (xPath (forwardRay t)) := mul_pos ht.1 hpos'
    linarith
  have hneBot : (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε)).NeBot := by
    apply (mem_closure_iff_nhdsWithin_neBot).mp
    rw [closure_Ioo (show (0 : ℝ) ≠ ε by linarith)]
    exact ⟨le_rfl, hε.le⟩
  exact le_of_tendsto hcoordTendsto hEventuallyNonpos

/-- Helper for Theorem 1.10.4: if a multiplier coordinate stays strictly positive at `lamStar`,
then the backward coordinate variation forces the limiting constraint value to vanish. -/
lemma constraint_eq_zero_at_limit_of_positive_multiplier
    {lamStar : Λ} {ε : ℝ}
    (xPath : Λ → Q) (xStar : Q)
    (hlamStar : lamStar ∈ problem.dualFeasibleSet)
    (hmax : IsMaxOn problem.dualFunction problem.dualFeasibleSet lamStar)
    (hε : 0 < ε)
    (hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m →
          lam ≠ lamStar →
          xPath lam ∈ problem.lagrangianMinimizers lam)
    (hlim :
      Tendsto xPath
        (nhdsWithin lamStar ((Metric.closedBall lamStar ε ∩ ℝ₊^m) \ {lamStar}))
        (nhds xStar))
    (hcont : ContinuousAt problem.constraintVector xStar)
    (j : Fin m) (hj : 0 < lamStar j) :
    problem.constraints j xStar = 0 := by
  let Nset : Set Λ := Metric.closedBall lamStar ε ∩ ℝ₊^m
  let δ : ℝ := min ε (lamStar j)
  let backwardRay : ℝ → Λ := fun t ↦ lamStar - EuclideanSpace.single j t
  have hlamStar_nonneg : ∀ k : Fin m, 0 ≤ lamStar k :=
    (problem.mem_dualFeasibleSet_iff.mp hlamStar).2
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hε hj
  have hbackwardMaps :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo 0 δ → backwardRay t ∈ Nset \ {lamStar} := by
    intro t ht
    constructor
    · constructor
      · rw [Metric.mem_closedBall, dist_eq_norm]
        have htε : t ≤ ε := by
          exact le_trans ht.2.le (min_le_left _ _)
        simpa [backwardRay, Real.norm_eq_abs, abs_of_nonneg ht.1.le] using htε
      · rw [EuclideanSpace.mem_nonnegativeOrthant_iff]
        intro k
        by_cases hk : k = j
        · subst k
          have htj : t < lamStar j := lt_of_lt_of_le ht.2 (min_le_right _ _)
          simpa [backwardRay, EuclideanSpace.single] using sub_nonneg.mpr htj.le
        · simp [backwardRay, EuclideanSpace.single, hk, hlamStar_nonneg k]
    · intro hEq
      have hEq' : backwardRay t = lamStar := by simpa using hEq
      have hCoord := congrArg (fun lam : Λ ↦ lam j) hEq'
      simp [backwardRay, EuclideanSpace.single] at hCoord
      have : (0 : ℝ) < 0 := by simpa [hCoord] using ht.1
      exact this.false
  have hsingleBasis :
      ∀ t : ℝ, (EuclideanSpace.single j t : Λ) = t • (EuclideanSpace.single j (1 : ℝ) : Λ) := by
    intro t
    ext k
    by_cases hk : k = j
    · subst k
      simp [EuclideanSpace.single]
    · simp [EuclideanSpace.single, hk]
  have hbackwardEq :
      backwardRay =
        fun t : ℝ ↦ lamStar - (t : ℝ) • (EuclideanSpace.single j (1 : ℝ) : Λ) := by
    funext t
    dsimp [backwardRay]
    rw [hsingleBasis]
  have hbackwardContinuous : ContinuousAt backwardRay 0 := by
    rw [hbackwardEq]
    have hsingle :
        Continuous fun t : ℝ ↦ (t : ℝ) • (EuclideanSpace.single j (1 : ℝ) : Λ) :=
      continuous_id.smul continuous_const
    exact (continuous_const.sub hsingle).continuousAt
  have hbackwardToNhds :
      Tendsto backwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
        (nhds lamStar) := by
    have hToZero :=
      hbackwardContinuous.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioo 0 δ) ≤ nhds (0 : ℝ) from nhdsWithin_le_nhds)
    have hzero : backwardRay 0 = lamStar := by
      simp [backwardRay, EuclideanSpace.single]
    simpa [hzero] using hToZero
  have hbackwardToPrincipal :
      Tendsto backwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
        (Filter.principal (Nset \ {lamStar})) := by
    rw [Filter.tendsto_def]
    intro s hs
    rw [Filter.mem_principal] at hs
    exact Filter.mem_of_superset self_mem_nhdsWithin fun t ht ↦ hs (hbackwardMaps ht)
  have hbackwardToNhdsWithin :
      Tendsto backwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
        (nhdsWithin lamStar (Nset \ {lamStar})) := by
    -- Package the ordinary convergence together with eventual membership in the punctured
    -- neighborhood.
    change Tendsto backwardRay
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
      (nhds lamStar ⊓ Filter.principal (Nset \ {lamStar}))
    simpa using hbackwardToNhds.inf hbackwardToPrincipal
  have hpathAlongBackward :
      Tendsto (fun t : ℝ ↦ xPath (backwardRay t))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
        (nhds xStar) :=
    hlim.comp hbackwardToNhdsWithin
  have hcoordCont :
      ContinuousAt (fun x : Q ↦ problem.constraintVector x j) xStar := by
    have hofLp :
        ContinuousAt (fun x : Q ↦ WithLp.ofLp (problem.constraintVector x)) xStar := by
      simpa [Function.comp] using
        ((PiLp.continuous_ofLp 2 (fun _ : Fin m ↦ ℝ)).continuousAt.comp hcont)
    simpa [Function.comp] using ((continuous_apply j).continuousAt.comp hofLp)
  have hcoordTendsto :
      Tendsto (fun t : ℝ ↦ problem.constraints j (xPath (backwardRay t)))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
        (nhds (problem.constraints j xStar)) := by
    simpa [problem.constraintVector_apply] using hcoordCont.tendsto.comp hpathAlongBackward
  have hEventuallyNonneg :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioo 0 δ),
        0 ≤ problem.constraints j (xPath (backwardRay t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hmem : backwardRay t ∈ Nset \ {lamStar} := hbackwardMaps ht
    have hxray : xPath (backwardRay t) ∈ problem.lagrangianMinimizers (backwardRay t) :=
      hxPath hmem.1 hmem.2
    have hmaxRay :
        problem.dualFunction (backwardRay t) ≤ problem.dualFunction lamStar :=
      (isMaxOn_iff.mp hmax) (backwardRay t)
        (problem.punctured_neighborhood_mem_dualFeasibleSet xPath hxPath hmem.1 hmem.2)
    have hsupport :
        problem.dualFunction lamStar ≤
          problem.dualFunction (backwardRay t) +
            (inner ℝ (problem.constraintVector (xPath (backwardRay t)))
              (lamStar - backwardRay t) : EReal) := by
      simpa [backwardRay] using
        (problem.dualFunction_le_affine_support_of_mem_lagrangianMinimizers
          (lam₁ := backwardRay t) (lam₂ := lamStar) (x₁ := xPath (backwardRay t)) hxray)
    have hsupport' :
        problem.dualFunction lamStar ≤
          ((problem.lagrangian (xPath (backwardRay t)) lamStar : ℝ) : EReal) := by
      calc
        problem.dualFunction lamStar ≤
            problem.dualFunction (backwardRay t) +
              (inner ℝ (problem.constraintVector (xPath (backwardRay t)))
                (lamStar - backwardRay t) : EReal) := hsupport
        _ =
            ((problem.lagrangian (xPath (backwardRay t)) lamStar : ℝ) : EReal) := by
          rw [problem.dualFunction_eq_lagrangian hxray]
          exact_mod_cast
            (problem.lagrangian_add_inner_sub_eq
              (x := xPath (backwardRay t))
              (lam₁ := backwardRay t) (lam₂ := lamStar))
    have hlagLe :
        problem.lagrangian (xPath (backwardRay t)) (backwardRay t) ≤
          problem.lagrangian (xPath (backwardRay t)) lamStar := by
      have hlagLeEReal :
          ((problem.lagrangian (xPath (backwardRay t)) (backwardRay t) : ℝ) : EReal) ≤
            ((problem.lagrangian (xPath (backwardRay t)) lamStar : ℝ) : EReal) := by
        calc
          ((problem.lagrangian (xPath (backwardRay t)) (backwardRay t) : ℝ) : EReal) =
              problem.dualFunction (backwardRay t) := by
            symm
            exact problem.dualFunction_eq_lagrangian hxray
          _ ≤ problem.dualFunction lamStar := hmaxRay
          _ ≤ ((problem.lagrangian (xPath (backwardRay t)) lamStar : ℝ) : EReal) := hsupport'
      exact_mod_cast hlagLeEReal
    have hstep :
        problem.lagrangian (xPath (backwardRay t)) (backwardRay t) =
          problem.lagrangian (xPath (backwardRay t)) lamStar -
            t * problem.constraints j (xPath (backwardRay t)) := by
      simpa [backwardRay] using
        (problem.lagrangian_backward_variation
          (x := xPath (backwardRay t)) (lam := lamStar) (j := j) (t := t))
    rw [hstep] at hlagLe
    have hmul : (-t) * problem.constraints j (xPath (backwardRay t)) ≤ 0 := by
      linarith
    by_contra hneg
    have hneg' : problem.constraints j (xPath (backwardRay t)) < 0 := lt_of_not_ge hneg
    have htneg : -t < 0 := by
      nlinarith [ht.1]
    have : 0 < (-t) * problem.constraints j (xPath (backwardRay t)) :=
      mul_pos_of_neg_of_neg htneg hneg'
    linarith
  have hneBot : (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ)).NeBot := by
    apply (mem_closure_iff_nhdsWithin_neBot).mp
    rw [closure_Ioo (show (0 : ℝ) ≠ δ by linarith [hδpos])]
    exact ⟨le_rfl, hδpos.le⟩
  have hnonneg : 0 ≤ problem.constraints j xStar :=
    ge_of_tendsto hcoordTendsto hEventuallyNonneg
  have hnonpos :
      problem.constraints j xStar ≤ 0 :=
    problem.constraint_nonpos_at_limit_of_forward_variation
      xPath xStar hlamStar hmax hε hxPath hlim hcont j
  exact le_antisymm hnonpos hnonneg

/-- Helper for Theorem 1.10.4: the coordinatewise limiting equalities and inequalities combine
into the complementary-slackness identity at `xStar`. -/
lemma complementary_slackness_at_limit
    {lamStar : Λ} {ε : ℝ}
    (xPath : Λ → Q) (xStar : Q)
    (hlamStar : lamStar ∈ problem.dualFeasibleSet)
    (hmax : IsMaxOn problem.dualFunction problem.dualFeasibleSet lamStar)
    (hε : 0 < ε)
    (hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m →
          lam ≠ lamStar →
          xPath lam ∈ problem.lagrangianMinimizers lam)
    (hlim :
      Tendsto xPath
        (nhdsWithin lamStar ((Metric.closedBall lamStar ε ∩ ℝ₊^m) \ {lamStar}))
        (nhds xStar))
    (hcont : ContinuousAt problem.constraintVector xStar)
    (j : Fin m) :
    lamStar j * problem.constraints j xStar = 0 := by
  -- Split by whether the multiplier coordinate is strictly positive or already zero.
  by_cases hj : 0 < lamStar j
  · have hzero :
        problem.constraints j xStar = 0 :=
      problem.constraint_eq_zero_at_limit_of_positive_multiplier
        xPath xStar hlamStar hmax hε hxPath hlim hcont j hj
    rw [hzero, mul_zero]
  · have hjZero : lamStar j = 0 := by
      have hjNonneg : 0 ≤ lamStar j :=
        (problem.mem_dualFeasibleSet_iff.mp hlamStar).2 j
      linarith
    rw [hjZero, zero_mul]

/-- Theorem 1.10.4: a dual-feasible maximizer of the dual function together with a convergent
family of Lagrangian minimizers on a punctured `ℝ₊^m`-neighborhood certifies that the limit
point is a globally optimal primal solution. -/
-- Proof sketch: use the affine upper-support inequality for the dual function at nearby
-- dual-feasible multipliers, vary one coordinate at a time around `λStar`, and pass to the limit
-- using continuity of the constraint map at `xStar` to deduce feasibility and complementary
-- slackness for `xStar`; the needed dual-domain membership comes from `hlamStar` at `λStar` and
-- from `problem.dualFunction_eq_lagrangian` along the punctured neighborhood. Then combine
-- `xStar ∈ X*(λStar)` with weak duality to conclude that `xStar` belongs to the canonical
-- constrained argmin set of the primal problem.
theorem globalOptimality_of_dualCertificate
    {lamStar : Λ} {ε : ℝ}
    (xPath : Λ → Q) (xStar : Q)
    (hlamStar : lamStar ∈ problem.dualFeasibleSet)
    (hmax : IsMaxOn problem.dualFunction problem.dualFeasibleSet lamStar)
    (hε : 0 < ε)
    (hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m →
          lam ≠ lamStar →
          xPath lam ∈ problem.lagrangianMinimizers lam)
    (hlim :
      Tendsto xPath
        (nhdsWithin lamStar ((Metric.closedBall lamStar ε ∩ ℝ₊^m) \ {lamStar}))
        (nhds xStar))
    (hcont : ContinuousAt problem.constraintVector xStar)
    (hxStar : xStar ∈ problem.lagrangianMinimizers lamStar) :
    xStar ∈ argmin[problem.feasibleSet] problem := by
  -- First extract feasibility and complementary slackness by the coordinate-variation argument.
  have hfeasible : xStar ∈ problem.feasibleSet := by
    rw [problem.mem_feasibleSet_iff]
    intro j
    exact problem.constraint_nonpos_at_limit_of_forward_variation
      xPath xStar hlamStar hmax hε hxPath hlim hcont j
  have hcomp :
      ∀ j : Fin m, lamStar j * problem.constraints j xStar = 0 := by
    intro j
    exact problem.complementary_slackness_at_limit
      xPath xStar hlamStar hmax hε hxPath hlim hcont j
  -- Next collapse the Lagrangian at `(xStar, lamStar)` to the primal objective value.
  have hinnerZero : inner ℝ lamStar (problem.constraintVector xStar) = 0 := by
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero ?_
    intro j _
    have hscalar :
        inner ℝ (lamStar j) (problem.constraintVector xStar j) =
          lamStar j * problem.constraintVector xStar j := by
      have hinner :
          inner ℝ (lamStar j) (problem.constraintVector xStar j) =
            problem.constraintVector xStar j * (starRingEnd ℝ) (lamStar j) :=
        RCLike.inner_apply (lamStar j) (problem.constraintVector xStar j)
      simpa [mul_comm] using hinner
    rw [hscalar, problem.constraintVector_apply, hcomp j]
  have hlagrangianEq :
      problem.lagrangian xStar lamStar = problem xStar := by
    -- Complementary slackness kills the inner-product term in the Lagrangian.
    rw [LagrangianProblem.lagrangian, hinnerZero, add_zero]
  have hdualEq :
      problem.dualFunction lamStar = (problem xStar : EReal) := by
    calc
      problem.dualFunction lamStar = (problem.lagrangian xStar lamStar : EReal) :=
        problem.dualFunction_eq_lagrangian hxStar
      _ = (problem xStar : EReal) := by
        exact_mod_cast hlagrangianEq
  -- Finally combine the dual-value identity with pointwise weak duality and the primal owner API.
  rw [mem_constrainedArgmin_iff]
  refine ⟨hfeasible, ?_⟩
  rw [isMinOn_iff]
  intro y hy
  have hlamStar_nonneg : lamStar ∈ ℝ₊^m := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using
      (problem.mem_dualFeasibleSet_iff.mp hlamStar).2
  have hdualLe :
      problem.dualFunction lamStar ≤ problem.primalOptimalValue :=
    problem.dualFunction_le_primalOptimalValue lamStar hlamStar_nonneg
  have hprimalLe :
      problem.primalOptimalValue ≤ (problem y : EReal) := by
    simpa [LagrangianProblem.primalOptimalValue] using
      problem.toSetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet hy
  have hoptimalEReal : (problem xStar : EReal) ≤ (problem y : EReal) := by
    calc
      (problem xStar : EReal) = problem.dualFunction lamStar := by
        simpa using hdualEq.symm
      _ ≤ problem.primalOptimalValue := hdualLe
      _ ≤ (problem y : EReal) := hprimalLe
  exact_mod_cast hoptimalEReal

end

end LagrangianProblem
