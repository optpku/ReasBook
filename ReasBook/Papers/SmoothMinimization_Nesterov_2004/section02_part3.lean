/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import SmoothMinimization_Nesterov_2004.section02_part2

/-- `OperatorNormDef` is nonnegative. -/
private lemma operatorNormDef_nonneg_section02 {E1 E2 : Type*} [SeminormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] [SeminormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (A : E1 →ₗ[ℝ] Module.Dual ℝ E2) : 0 ≤ OperatorNormDef A := by
  classical
  set S : Set ℝ :=
      { r : ℝ | ∃ x : E1, ∃ u : E2, ‖x‖ = 1 ∧ ‖u‖ = 1 ∧ r = DualPairing (A x) u } with hSdef
  have hOp : OperatorNormDef A = sSup S := by
    unfold OperatorNormDef
    rw [hSdef.symm]
  by_cases hS : S = ∅
  · have : OperatorNormDef A = 0 := by
      simp [hOp, hS, Real.sSup_empty]
    simp [this]
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.2 hS
    rcases hSne with ⟨r, hr⟩
    have hneg : (-r) ∈ S := by
      rcases hr with ⟨x, u, hx, hu, rfl⟩
      refine ⟨x, -u, hx, ?_, ?_⟩
      · simpa [norm_neg] using hu
      · simp [DualPairing]
    have hex : ∃ t ∈ S, 0 ≤ t := by
      by_cases hr0 : 0 ≤ r
      · exact ⟨r, hr, hr0⟩
      · have : 0 ≤ -r := by linarith
        exact ⟨-r, hneg, this⟩
    have : 0 ≤ sSup S := Real.sSup_nonneg' hex
    simpa [hOp] using this

/-- Existence of a smoothed maximizer on a closed bounded nonempty set. -/
private lemma smoothedMaximizer_exists {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ : ℝ) (x : E1) (hQ2_closed : IsClosed Q2)
    (hQ2_bdd : Bornology.IsBounded Q2) (hQ2_nonempty : Q2.Nonempty)
    (hphihat : ContinuousOn phihat Q2) (hd2 : ContinuousOn d2 Q2) :
    ∃ u, IsSmoothedMaximizer Q2 A phihat d2 μ x u := by
  have hcompact : IsCompact Q2 := by
    simpa [hQ2_closed.closure_eq] using hQ2_bdd.isCompact_closure.inter_right hQ2_closed
  let g : E2 → ℝ := fun u => A x u - phihat u - μ * d2 u
  have hμd2 : ContinuousOn (fun u => μ * d2 u) Q2 := continuousOn_const.mul hd2
  have hgcont : ContinuousOn g Q2 := by
    have hAx : ContinuousOn (fun u => A x u) Q2 := (A x).continuous.continuousOn
    exact (hAx.sub hphihat).sub hμd2
  rcases hcompact.exists_isMaxOn hQ2_nonempty hgcont with ⟨u, huQ, huMax⟩
  refine ⟨u, huQ, ?_⟩
  intro v hv
  exact huMax hv

/-- Uniqueness of the smoothed maximizer under convexity of `phihat` and strong convexity of
`d2`. -/
private lemma smoothedMaximizer_unique {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ σ2 : ℝ) (x : E1) (hμ : 0 < μ) (hσ2 : 0 < σ2)
    (hphi : ConvexOn ℝ Q2 phihat) (hconv : StrongConvexOn Q2 σ2 d2) {u v : E2}
    (hu : IsSmoothedMaximizer Q2 A phihat d2 μ x u)
    (hv : IsSmoothedMaximizer Q2 A phihat d2 μ x v) :
    u = v := by
  have huQ : u ∈ Q2 := hu.1
  have hvQ : v ∈ Q2 := hv.1
  let g : E2 → ℝ := fun w => phihat w + μ * d2 w - A x w
  have hconvμ : StrongConvexOn Q2 (μ * σ2) g := by
    rcases hconv with ⟨hQ2conv, hconvI⟩
    rcases hphi with ⟨_, hphiI⟩
    refine ⟨hQ2conv, ?_⟩
    intro u hu v hv a b ha hb hsum
    have hphiI' := hphiI hu hv ha hb hsum
    have hsc0 := hconvI hu hv
    have hsc1 := hsc0 ha hb hsum
    have hμ' : 0 ≤ μ := le_of_lt hμ
    have hsc2 :
        μ * d2 (a • u + b • v) ≤
          a * μ * d2 u + b * μ * d2 v -
            a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
      have hmul := mul_le_mul_of_nonneg_left hsc1 hμ'
      have hmul' :
          μ * (a * d2 u + b * d2 v - a * b * (σ2 / 2 * ‖u - v‖ ^ (2 : ℕ))) =
            a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
        ring
      simpa [hmul'] using hmul
    have hsum' :
        phihat (a • u + b • v) + μ * d2 (a • u + b • v) ≤
          a * phihat u + b * phihat v +
            (a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ))) := by
      exact add_le_add hphiI' hsc2
    have hlin : A x (a • u + b • v) = a * A x u + b * A x v := by
      simp [map_add, map_smul, smul_eq_mul]
    calc
      g (a • u + b • v)
          = phihat (a • u + b • v) + μ * d2 (a • u + b • v) - A x (a • u + b • v) := rfl
      _ ≤
          (a * phihat u + b * phihat v +
            (a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)))) -
            (a * A x u + b * A x v) := by
          simpa [hlin] using (sub_le_sub_right hsum' (A x (a • u + b • v)))
      _ = a * g u + b * g v - a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
          ring
  have hminu : IsMinOn g Q2 u := smoothedMaximizer_isMinOn Q2 A phihat d2 μ x u hu
  have hminv : IsMinOn g Q2 v := smoothedMaximizer_isMinOn Q2 A phihat d2 μ x v hv
  have hineq1 :=
    strongConvexOn_lower_quadratic_of_isMinOn Q2 g (μ * σ2) u hconvμ huQ hminu v hvQ
  have hineq2 :=
    strongConvexOn_lower_quadratic_of_isMinOn Q2 g (μ * σ2) v hconvμ hvQ hminv u huQ
  have hμσ : 0 < μ * σ2 := mul_pos hμ hσ2
  have htmp := add_le_add hineq1 hineq2
  have hnorm : ‖u - v‖ ^ (2 : ℕ) = ‖v - u‖ ^ (2 : ℕ) := by
    simp [norm_sub_rev]
  have hsq_zero : ‖v - u‖ ^ (2 : ℕ) = 0 := by
    nlinarith [htmp, hnorm, hμσ]
  have hnorm_zero : ‖v - u‖ = 0 := by
    nlinarith
  have hsub : v - u = 0 := norm_eq_zero.mp hnorm_zero
  have hvu : v = u := sub_eq_zero.mp hsub
  exact hvu.symm

/-- Canonical choice of the unique smoothed maximizer. -/
noncomputable def smoothedMaximizer {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ : ℝ) (hQ2_closed : IsClosed Q2)
    (hQ2_bdd : Bornology.IsBounded Q2) (hQ2_nonempty : Q2.Nonempty)
    (hphihat : ContinuousOn phihat Q2) (hd2 : ContinuousOn d2 Q2) (x : E1) : E2 :=
  Classical.choose
    (smoothedMaximizer_exists (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ)
      (x := x) hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2)

/-- The canonical selector is a smoothed maximizer. -/
lemma smoothedMaximizer_isSmoothedMaximizer {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ : ℝ) (hQ2_closed : IsClosed Q2)
    (hQ2_bdd : Bornology.IsBounded Q2) (hQ2_nonempty : Q2.Nonempty)
    (hphihat : ContinuousOn phihat Q2) (hd2 : ContinuousOn d2 Q2) (x : E1) :
    IsSmoothedMaximizer Q2 A phihat d2 μ x
      (smoothedMaximizer Q2 A phihat d2 μ hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2 x) :=
  Classical.choose_spec
    (smoothedMaximizer_exists (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ)
      (x := x) hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2)

/-- Any smoothed maximizer agrees with the canonical selector when uniqueness holds. -/
private lemma smoothedMaximizer_eq_of_isSmoothedMaximizer {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ σ2 : ℝ) (x : E1) (hμ : 0 < μ) (hσ2 : 0 < σ2)
    (hphi : ConvexOn ℝ Q2 phihat) (hconv : StrongConvexOn Q2 σ2 d2)
    (hQ2_closed : IsClosed Q2) (hQ2_bdd : Bornology.IsBounded Q2) (hQ2_nonempty : Q2.Nonempty)
    (hphihat : ContinuousOn phihat Q2) (hd2 : ContinuousOn d2 Q2) {u : E2}
    (hu : IsSmoothedMaximizer Q2 A phihat d2 μ x u) :
    smoothedMaximizer Q2 A phihat d2 μ hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2 x = u := by
  exact smoothedMaximizer_unique (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ)
    (σ2 := σ2) (x := x) hμ hσ2 hphi hconv
    (smoothedMaximizer_isSmoothedMaximizer (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2)
      (μ := μ) hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2 x)
    hu

/-- Internal compatibility lemma: differentiability of the smoothed max-function, provided the
selected maximizers realize the claimed branch derivative formula. -/
private lemma smoothedMaxFunction_hasFDerivAt_of_formula {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ : ℝ) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    (∀ x,
        HasFDerivAt (fun y => A y (uμ y) - phihat (uμ y) - μ * d2 (uμ y))
          ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x) →
    ∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
  classical
  simp only
  intro hformula
  let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
  let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp }
  intro x
  have hEq :
      fμ = fun y => A y (uμ y) - phihat (uμ y) - μ * d2 (uμ y) := by
    funext y
    exact (smoothedMaxFunction_eq_of_isSmoothedMaximizer Q2 A phihat d2 μ y (uμ y)
      (hmax y)).1
  simpa [fμ, A', hEq] using hformula x

/-- A first-order stationarity condition in the maximizer variable eliminates the derivative
contribution coming from the branch `uμ`. -/
private lemma smoothedMaxFunction_branch_hasFDerivAt_of_stationary {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ) (uμ : E1 → E2) :
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    (∀ x, DifferentiableAt ℝ uμ x) →
    (∀ x,
        HasFDerivAt (fun v => A x v - phihat v - μ * d2 v)
          (0 : E2 →L[ℝ] ℝ) (uμ x)) →
    ∀ x,
      HasFDerivAt (fun y => A y (uμ y) - phihat (uμ y) - μ * d2 (uμ y))
        ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
  intro A' huμ hstationary x
  have hmain :
      HasFDerivAt (fun y => A (y - x) (uμ y))
        ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
    have hsub : HasFDerivAt (fun y => y - x) (1 : E1 →L[ℝ] E1) x := by
      simpa [sub_eq_add_neg] using (hasFDerivAt_id x).add_const (-x)
    have hA : HasFDerivAt (fun y => A (y - x)) (A.comp (1 : E1 →L[ℝ] E1)) x := by
      exact A.hasFDerivAt.comp x hsub
    simpa [AdjointOperator, A'] using hA.clm_apply (huμ x).hasFDerivAt
  have hstat :
      HasFDerivAt (fun y => A x (uμ y) - phihat (uμ y) - μ * d2 (uμ y))
        (0 : E1 →L[ℝ] ℝ) x :=
    (hstationary x).comp x (huμ x).hasFDerivAt
  have hsplit :
      (fun y => A y (uμ y) - phihat (uμ y) - μ * d2 (uμ y)) =
        fun y => A (y - x) (uμ y) + (A x (uμ y) - phihat (uμ y) - μ * d2 (uμ y)) := by
    funext y
    rw [show y = (y - x) + x by abel]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  simpa [hsplit] using hmain.add hstat

/-- Differentiability of the smoothed max-function from explicit regularity of the selected branch
and first-order stationarity in the maximizer variable. -/
private lemma smoothedMaxFunction_hasFDerivAt_of_stationary {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ)
    (uμ : E1 → E2) (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    (∀ x, DifferentiableAt ℝ uμ x) →
    (∀ x,
        HasFDerivAt (fun v => A x v - phihat v - μ * d2 v)
          (0 : E2 →L[ℝ] ℝ) (uμ x)) →
    ∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
  classical
  simp only
  intro huμ hstationary
  let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
  let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp }
  have hformula :
      ∀ x,
        HasFDerivAt (fun y => A y (uμ y) - phihat (uμ y) - μ * d2 (uμ y))
          ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
    simpa [A'] using
      (smoothedMaxFunction_branch_hasFDerivAt_of_stationary (A := A) (phihat := phihat)
        (d2 := d2) (μ := μ) (uμ := uμ) huμ hstationary)
  simpa [fμ, A'] using
    (smoothedMaxFunction_hasFDerivAt_of_formula (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2)
      (μ := μ) (uμ := uμ) (hmax := hmax) hformula)

set_option maxHeartbeats 400000 in
/-- Internal helper: Lipschitz continuity of the smoothed max-function gradient from an abstract
coercivity inequality. -/
private lemma smoothedMaxFunction_gradient_lipschitz_of_coercivity {E1 E2 : Type*}
    [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (uμ : E1 → E2) (hμ : 0 < μ) (hσ2 : 0 < σ2) :
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    (∀ x1 x2,
        μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
          DualPairing (AdjointOperator A' (uμ x1 - uμ x2)) (x1 - x2)) →
    ∃ Lμ : ℝ,
      Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
        LipschitzWith (Real.toNNReal Lμ)
          (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
  classical
  simp only
  intro hcoercive
  let _ := Q2
  let _ := phihat
  let _ := d2
  let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp }
  let Lμ : ℝ := (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2
  have hμσ_pos : 0 < μ * σ2 := mul_pos hμ hσ2
  have hμσ_nonneg : 0 ≤ μ * σ2 := le_of_lt hμσ_pos
  have hOp_nonneg : 0 ≤ OperatorNormDef A' := operatorNormDef_nonneg_section02 (A := A')
  have hLμ_nonneg : 0 ≤ Lμ := by
    have hsq : 0 ≤ (OperatorNormDef A') ^ 2 := sq_nonneg (OperatorNormDef A')
    have hdiv : 0 ≤ 1 / (μ * σ2) := one_div_nonneg.mpr hμσ_nonneg
    exact mul_nonneg hdiv hsq
  refine ⟨Lμ, rfl, LipschitzWith.of_dist_le_mul ?_⟩
  intro x1 x2
  let du : E2 := uμ x1 - uμ x2
  let dx : E1 := x1 - x2
  have hpair_le_dual :
      DualPairing (AdjointOperator A' du) dx ≤ DualNormDef (AdjointOperator A' du) * ‖dx‖ := by
    exact dualPairing_le_dualNormDef_mul_norm_section02 (s := AdjointOperator A' du) (x := dx)
  have hdual_le :
      DualNormDef (AdjointOperator A' du) ≤ OperatorNormDef A' * ‖du‖ := by
    exact adjointOperator_dualNorm_le (A := A') du
  have hpair_upper :
      DualPairing (AdjointOperator A' du) dx ≤ OperatorNormDef A' * ‖du‖ * ‖dx‖ := by
    have hmul := mul_le_mul_of_nonneg_right hdual_le (norm_nonneg dx)
    have hupper_tmp :
        DualNormDef (AdjointOperator A' du) * ‖dx‖ ≤
          OperatorNormDef A' * ‖du‖ * ‖dx‖ := by
      calc
        DualNormDef (AdjointOperator A' du) * ‖dx‖ ≤
            (OperatorNormDef A' * ‖du‖) * ‖dx‖ := hmul
        _ = OperatorNormDef A' * ‖du‖ * ‖dx‖ := by ring
    exact le_trans hpair_le_dual hupper_tmp
  have hdu_main :
      μ * σ2 * ‖du‖ ^ (2 : ℕ) ≤ OperatorNormDef A' * ‖du‖ * ‖dx‖ := by
    exact le_trans (hcoercive x1 x2) hpair_upper
  have hdu_bound :
      μ * σ2 * ‖du‖ ≤ OperatorNormDef A' * ‖dx‖ := by
    by_cases hdu_zero : ‖du‖ = 0
    · have hrhs_nonneg : 0 ≤ OperatorNormDef A' * ‖dx‖ := mul_nonneg hOp_nonneg (norm_nonneg dx)
      simpa [hdu_zero] using hrhs_nonneg
    · have hdu_ne' : 0 ≠ ‖du‖ := by
        simpa [eq_comm] using hdu_zero
      have hdu_pos : 0 < ‖du‖ := lt_of_le_of_ne (norm_nonneg du) hdu_ne'
      have hmul :
          ‖du‖ * (μ * σ2 * ‖du‖) ≤ ‖du‖ * (OperatorNormDef A' * ‖dx‖) := by
        calc
          ‖du‖ * (μ * σ2 * ‖du‖) = μ * σ2 * ‖du‖ ^ (2 : ℕ) := by
            ring_nf
          _ ≤ OperatorNormDef A' * ‖du‖ * ‖dx‖ := hdu_main
          _ = ‖du‖ * (OperatorNormDef A' * ‖dx‖) := by ring_nf
      nlinarith
  have hu_bound :
      ‖du‖ ≤ (OperatorNormDef A' * ‖dx‖) / (μ * σ2) := by
    exact (le_div_iff₀ hμσ_pos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hdu_bound)
  have hdual_lip :
      DualNormDef (AdjointOperator A' du) ≤ Lμ * ‖dx‖ := by
    have hmul := mul_le_mul_of_nonneg_left hu_bound hOp_nonneg
    have haux :
        OperatorNormDef A' * ‖du‖ ≤
          OperatorNormDef A' * ((OperatorNormDef A' * ‖dx‖) / (μ * σ2)) := hmul
    have hrewrite :
        OperatorNormDef A' * ((OperatorNormDef A' * ‖dx‖) / (μ * σ2)) = Lμ * ‖dx‖ := by
      dsimp [Lμ]
      ring
    have haux' : OperatorNormDef A' * ‖du‖ ≤ Lμ * ‖dx‖ := haux.trans_eq hrewrite
    exact hdual_le.trans haux'
  have hnorm_sub :
      ‖((AdjointOperator A' (uμ x1)).toContinuousLinearMap -
          (AdjointOperator A' (uμ x2)).toContinuousLinearMap)‖ ≤
        Lμ * ‖dx‖ := by
    have hsub :
        ((AdjointOperator A' (uμ x1)).toContinuousLinearMap -
            (AdjointOperator A' (uμ x2)).toContinuousLinearMap) =
          (AdjointOperator A' du).toContinuousLinearMap := by
      ext z
      simp [du]
    rw [hsub]
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hLμ_nonneg (norm_nonneg dx)) ?_
    intro z
    have hpos :
        DualPairing (AdjointOperator A' du) z ≤ DualNormDef (AdjointOperator A' du) * ‖z‖ := by
      exact dualPairing_le_dualNormDef_mul_norm_section02 (s := AdjointOperator A' du) (x := z)
    have hneg :
        -DualPairing (AdjointOperator A' du) z ≤ DualNormDef (AdjointOperator A' du) * ‖z‖ := by
      simpa [DualPairing, norm_neg] using
        (dualPairing_le_dualNormDef_mul_norm_section02 (s := AdjointOperator A' du) (x := -z))
    have habs :
        |DualPairing (AdjointOperator A' du) z| ≤ DualNormDef (AdjointOperator A' du) * ‖z‖ := by
      refine abs_le.mpr ?_
      constructor
      · linarith
      · exact hpos
    calc
      ‖((AdjointOperator A' du).toContinuousLinearMap) z‖
          = |DualPairing (AdjointOperator A' du) z| := by simp [DualPairing]
      _ ≤ DualNormDef (AdjointOperator A' du) * ‖z‖ := habs
      _ ≤ (Lμ * ‖dx‖) * ‖z‖ := by
          exact mul_le_mul_of_nonneg_right hdual_lip (norm_nonneg z)
  have hdist :
      dist ((AdjointOperator A' (uμ x1)).toContinuousLinearMap)
          ((AdjointOperator A' (uμ x2)).toContinuousLinearMap) ≤
        Lμ * dist x1 x2 := by
    simpa [dist_eq_norm, dx] using hnorm_sub
  simpa [Real.toNNReal_of_nonneg hLμ_nonneg] using hdist

set_option maxHeartbeats 400000 in
/-- Key inequality for the smoothed maximizers, assuming convexity of `phihat`. -/
private lemma smoothedMaxFunction_key_inequality {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ σ2 : ℝ) (hμ : 0 < μ)
    (hconv : StrongConvexOn Q2 σ2 d2) (hphi : ConvexOn ℝ Q2 phihat) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∀ x1 x2,
      μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        DualPairing (AdjointOperator A' (uμ x1 - uμ x2)) (x1 - x2) := by
  classical
  intro A'
  have hμ' : 0 ≤ μ := le_of_lt hμ
  rcases hphi with ⟨_, hphiI⟩
  intro x1 x2
  have hu1 : uμ x1 ∈ Q2 := (hmax x1).1
  have hu2 : uμ x2 ∈ Q2 := (hmax x2).1
  let g1 : E2 → ℝ := fun u => phihat u + μ * d2 u - A x1 u
  let g2 : E2 → ℝ := fun u => phihat u + μ * d2 u - A x2 u
  have hsc1 : StrongConvexOn Q2 (μ * σ2) g1 := by
    rcases hconv with ⟨hQ2conv, hconvI⟩
    refine ⟨hQ2conv, ?_⟩
    intro u hu v hv a b ha hb hsum
    have hphiI' : phihat (a • u + b • v) ≤ a * phihat u + b * phihat v := by
      have hphiI'' := hphiI (x := u) hu (y := v) hv (a := a) (b := b) ha hb hsum
      simpa [smul_eq_mul] using hphiI''
    have hsc0 := hconvI (x := u) hu (y := v) hv
    have hsc1 := hsc0 (a := a) (b := b) ha hb hsum
    have hsc2 :
        μ * d2 (a • u + b • v) ≤
          a * μ * d2 u + b * μ * d2 v -
            a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
      have hmul := mul_le_mul_of_nonneg_left hsc1 hμ'
      -- normalize the scalar factors
      have hmul' :
          μ * (a * d2 u + b * d2 v - a * b * (σ2 / 2 * ‖u - v‖ ^ (2 : ℕ))) =
            a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
        ring
      simpa [hmul'] using hmul
    have hsum' :
        phihat (a • u + b • v) + μ * d2 (a • u + b • v) ≤
          a * phihat u + b * phihat v +
            (a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ))) := by
      exact add_le_add hphiI' hsc2
    have hlin : A x1 (a • u + b • v) = a * A x1 u + b * A x1 v := by
      simp [map_add, map_smul, smul_eq_mul]
    have hlin' : A x1 (a • u + b • v) = a * A x1 u + b * A x1 v := hlin
    calc
      g1 (a • u + b • v)
          = phihat (a • u + b • v) + μ * d2 (a • u + b • v) - A x1 (a • u + b • v) := rfl
      _ ≤
          (a * phihat u + b * phihat v +
            (a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)))) -
            (a * A x1 u + b * A x1 v) := by
          simpa [hlin'] using (sub_le_sub_right hsum' (A x1 (a • u + b • v)))
      _ = a * g1 u + b * g1 v - a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
          ring
  have hsc2 : StrongConvexOn Q2 (μ * σ2) g2 := by
    rcases hconv with ⟨hQ2conv, hconvI⟩
    refine ⟨hQ2conv, ?_⟩
    intro u hu v hv a b ha hb hsum
    have hphiI' : phihat (a • u + b • v) ≤ a * phihat u + b * phihat v := by
      have hphiI'' := hphiI (x := u) hu (y := v) hv (a := a) (b := b) ha hb hsum
      simpa [smul_eq_mul] using hphiI''
    have hsc0 := hconvI (x := u) hu (y := v) hv
    have hsc1 := hsc0 (a := a) (b := b) ha hb hsum
    have hsc2 :
        μ * d2 (a • u + b • v) ≤
          a * μ * d2 u + b * μ * d2 v -
            a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
      have hmul := mul_le_mul_of_nonneg_left hsc1 hμ'
      have hmul' :
          μ * (a * d2 u + b * d2 v - a * b * (σ2 / 2 * ‖u - v‖ ^ (2 : ℕ))) =
            a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
        ring
      simpa [hmul'] using hmul
    have hsum' :
        phihat (a • u + b • v) + μ * d2 (a • u + b • v) ≤
          a * phihat u + b * phihat v +
            (a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ))) := by
      exact add_le_add hphiI' hsc2
    have hlin : A x2 (a • u + b • v) = a * A x2 u + b * A x2 v := by
      simp [map_add, map_smul, smul_eq_mul]
    have hlin' : A x2 (a • u + b • v) = a * A x2 u + b * A x2 v := hlin
    calc
      g2 (a • u + b • v)
          = phihat (a • u + b • v) + μ * d2 (a • u + b • v) - A x2 (a • u + b • v) := rfl
      _ ≤
          (a * phihat u + b * phihat v +
            (a * μ * d2 u + b * μ * d2 v -
              a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)))) -
            (a * A x2 u + b * A x2 v) := by
          simpa [hlin'] using (sub_le_sub_right hsum' (A x2 (a • u + b • v)))
      _ = a * g2 u + b * g2 v - a * b * ((μ * σ2) / 2 * ‖u - v‖ ^ (2 : ℕ)) := by
          ring
  have hmin1 : IsMinOn g1 Q2 (uμ x1) :=
    smoothedMaximizer_isMinOn Q2 A phihat d2 μ x1 (uμ x1) (hmax x1)
  have hmin2 : IsMinOn g2 Q2 (uμ x2) :=
    smoothedMaximizer_isMinOn Q2 A phihat d2 μ x2 (uμ x2) (hmax x2)
  have hineq1 :=
    strongConvexOn_lower_quadratic_of_isMinOn Q2 g1 (μ * σ2) (uμ x1) hsc1 hu1 hmin1
  have hineq2 :=
    strongConvexOn_lower_quadratic_of_isMinOn Q2 g2 (μ * σ2) (uμ x2) hsc2 hu2 hmin2
  have hsum := add_le_add (hineq1 (uμ x2) hu2) (hineq2 (uμ x1) hu1)
  have hnorm : ‖uμ x2 - uμ x1‖ ^ (2 : ℕ) = ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) := by
    simp [norm_sub_rev]
  have hsum' :
      g1 (uμ x1) + g2 (uμ x2) + (μ * σ2) * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        g1 (uμ x2) + g2 (uμ x1) := by
    have hsum'' :
        g1 (uμ x1) + g2 (uμ x2) +
            (μ * σ2 / 2) * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) +
              (μ * σ2 / 2) * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
          g1 (uμ x2) + g2 (uμ x1) := by
      simpa [hnorm, add_comm, add_left_comm, add_assoc] using hsum
    nlinarith
  have hsum'' :
      μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        g1 (uμ x2) + g2 (uμ x1) - g1 (uμ x1) - g2 (uμ x2) := by
    linarith [hsum']
  have hcalc :
      g1 (uμ x2) + g2 (uμ x1) - g1 (uμ x1) - g2 (uμ x2) =
        A x1 (uμ x1) - A x2 (uμ x1) - (A x1 (uμ x2) - A x2 (uμ x2)) := by
    simp [g1, g2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    ring
  have hfinal :
      μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        A x1 (uμ x1) - A x2 (uμ x1) - (A x1 (uμ x2) - A x2 (uμ x2)) := by
    simpa [hcalc] using hsum''
  have hfinal' :
      μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        A (x1 - x2) (uμ x1 - uμ x2) := by
    have hrewrite :
        A (x1 - x2) (uμ x1 - uμ x2) =
          A x1 (uμ x1) - A x2 (uμ x1) - (A x1 (uμ x2) - A x2 (uμ x2)) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [hrewrite]
    exact hfinal
  change
      μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
        A (x1 - x2) (uμ x1 - uμ x2)
  exact hfinal'

-- Lipschitz continuity of the smoothed maximizer branch under strong convexity of `d2` and
-- convexity of `phihat`.
set_option maxHeartbeats 5000000 in
private lemma smoothedMaximizer_lipschitz_of_isSmoothedMaximizer {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∃ Kμ : ℝ,
      Kμ = (OperatorNormDef A') / (μ * σ2) ∧
        LipschitzWith (Real.toNNReal Kμ) uμ := by
  classical
  simp only
  let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp }
  let Kμ : ℝ := (OperatorNormDef A') / (μ * σ2)
  have hμσ_pos : 0 < μ * σ2 := mul_pos hμ hσ2
  have hOp_nonneg : 0 ≤ OperatorNormDef A' := operatorNormDef_nonneg_section02 (A := A')
  have hKμ_nonneg : 0 ≤ Kμ := by
    dsimp [Kμ]
    exact div_nonneg hOp_nonneg (le_of_lt hμσ_pos)
  have hcoercive :
      ∀ x1 x2,
        μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
          DualPairing (AdjointOperator A' (uμ x1 - uμ x2)) (x1 - x2) := by
    simpa [A'] using
      (smoothedMaxFunction_key_inequality (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2)
        (μ := μ) (σ2 := σ2) (hμ := hμ) (hconv := hconv) (hphi := hphi) (uμ := uμ)
        (hmax := hmax))
  refine ⟨Kμ, rfl, LipschitzWith.of_dist_le_mul ?_⟩
  intro x1 x2
  let du : E2 := uμ x1 - uμ x2
  let dx : E1 := x1 - x2
  have hpair_le_dual :
      DualPairing (AdjointOperator A' du) dx ≤ DualNormDef (AdjointOperator A' du) * ‖dx‖ := by
    exact dualPairing_le_dualNormDef_mul_norm_section02 (s := AdjointOperator A' du) (x := dx)
  have hdual_le :
      DualNormDef (AdjointOperator A' du) ≤ OperatorNormDef A' * ‖du‖ := by
    exact adjointOperator_dualNorm_le (A := A') du
  have hpair_upper :
      DualPairing (AdjointOperator A' du) dx ≤ OperatorNormDef A' * ‖du‖ * ‖dx‖ := by
    have hmul := mul_le_mul_of_nonneg_right hdual_le (norm_nonneg dx)
    have hupper_tmp :
        DualNormDef (AdjointOperator A' du) * ‖dx‖ ≤
          OperatorNormDef A' * ‖du‖ * ‖dx‖ := by
      calc
        DualNormDef (AdjointOperator A' du) * ‖dx‖ ≤
            (OperatorNormDef A' * ‖du‖) * ‖dx‖ := hmul
        _ = OperatorNormDef A' * ‖du‖ * ‖dx‖ := by ring
    exact le_trans hpair_le_dual hupper_tmp
  have hdu_main :
      μ * σ2 * ‖du‖ ^ (2 : ℕ) ≤ OperatorNormDef A' * ‖du‖ * ‖dx‖ := by
    exact le_trans (hcoercive x1 x2) hpair_upper
  have hdu_bound :
      μ * σ2 * ‖du‖ ≤ OperatorNormDef A' * ‖dx‖ := by
    by_cases hdu_zero : ‖du‖ = 0
    · have hrhs_nonneg : 0 ≤ OperatorNormDef A' * ‖dx‖ := mul_nonneg hOp_nonneg (norm_nonneg dx)
      simpa [hdu_zero] using hrhs_nonneg
    · have hdu_ne' : 0 ≠ ‖du‖ := by
        simpa [eq_comm] using hdu_zero
      have hdu_pos : 0 < ‖du‖ := lt_of_le_of_ne (norm_nonneg du) hdu_ne'
      have hmul :
          ‖du‖ * (μ * σ2 * ‖du‖) ≤ ‖du‖ * (OperatorNormDef A' * ‖dx‖) := by
        calc
          ‖du‖ * (μ * σ2 * ‖du‖) = μ * σ2 * ‖du‖ ^ (2 : ℕ) := by
            ring_nf
          _ ≤ OperatorNormDef A' * ‖du‖ * ‖dx‖ := hdu_main
          _ = ‖du‖ * (OperatorNormDef A' * ‖dx‖) := by ring_nf
      nlinarith
  have hu_bound :
      ‖du‖ ≤ Kμ * ‖dx‖ := by
    dsimp [Kμ]
    have htmp : ‖du‖ * (μ * σ2) ≤ ‖dx‖ * OperatorNormDef A' := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hdu_bound
    have htmp' : ‖du‖ ≤ ‖dx‖ * OperatorNormDef A' / (μ * σ2) := by
      exact (le_div_iff₀ hμσ_pos).2 htmp
    have hrewrite : ‖dx‖ * OperatorNormDef A' / (μ * σ2) = OperatorNormDef A' / (μ * σ2) * ‖dx‖ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    exact htmp'.trans_eq hrewrite
  simpa [dist_eq_norm, du, dx, Kμ, Real.toNNReal_of_nonneg hKμ_nonneg, mul_comm, mul_left_comm,
    mul_assoc] using hu_bound

-- A Danskin-style squeeze proof of the smoothed-max derivative formula, assuming only that the
-- selected maximizers are Lipschitz.
set_option maxHeartbeats 5000000 in
private lemma smoothedMaxFunction_hasFDerivAt_of_lipschitz {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ)
    (uμ : E1 → E2) (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∀ K : NNReal, LipschitzWith K uμ →
      ∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
  classical
  simp only
  intro K hLip
  let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
  let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp }
  intro x
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  let C : ℝ := (K : ℝ) * OperatorNormDef A'
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (show 0 ≤ (K : ℝ) by exact_mod_cast K.2)
      (operatorNormDef_nonneg_section02 (A := A'))
  have hbigO :
      (fun h : E1 => fμ (x + h) - fμ x -
          ((AdjointOperator A' (uμ x)).toContinuousLinearMap) h) =O[nhds (0 : E1)]
        (fun h : E1 => ‖h‖ ^ (2 : ℕ)) := by
    refine Asymptotics.IsBigO.of_bound C <| Filter.Eventually.of_forall ?_
    intro h
    let ux : E2 := uμ x
    let uh : E2 := uμ (x + h)
    have hfx :
        fμ x = A x ux - phihat ux - μ * d2 ux := by
      exact (smoothedMaxFunction_eq_of_isSmoothedMaximizer Q2 A phihat d2 μ x ux (hmax x)).1
    have hfxh :
        fμ (x + h) = A (x + h) uh - phihat uh - μ * d2 uh := by
      exact
        (smoothedMaxFunction_eq_of_isSmoothedMaximizer Q2 A phihat d2 μ (x + h) uh
          (hmax (x + h))).1
    have hux_mem : ux ∈ Q2 := (hmax x).1
    have huh_mem : uh ∈ Q2 := (hmax (x + h)).1
    have hupper_max : A x uh - phihat uh - μ * d2 uh ≤ fμ x := by
      have htmp := (hmax x).2 uh huh_mem
      simpa [ux, hfx] using htmp
    have hlower_max : A (x + h) ux - phihat ux - μ * d2 ux ≤ fμ (x + h) := by
      have htmp := (hmax (x + h)).2 ux hux_mem
      simpa [uh, hfxh] using htmp
    have hlower :
        A h ux ≤ fμ (x + h) - fμ x := by
      have hlin : A (x + h) ux = A x ux + A h ux := by
        simp [map_add]
      linarith
    have hupper :
        fμ (x + h) - fμ x ≤ A h uh := by
      have hlin : A (x + h) uh = A x uh + A h uh := by
        simp [map_add]
      linarith
    have herr_nonneg :
        0 ≤ fμ (x + h) - fμ x - ((AdjointOperator A' ux).toContinuousLinearMap) h := by
      have hderiv_eval : ((AdjointOperator A' ux).toContinuousLinearMap) h = A h ux := by
        rfl
      linarith
    have herr_le :
        fμ (x + h) - fμ x - ((AdjointOperator A' ux).toContinuousLinearMap) h ≤ A h (uh - ux) := by
      have hderiv_eval : ((AdjointOperator A' ux).toContinuousLinearMap) h = A h ux := by
        rfl
      have hlin : A h uh - A h ux = A h (uh - ux) := by
        simp [uh, ux, sub_eq_add_neg, map_add]
      have hupper' :
          fμ (x + h) - fμ x - A h ux ≤ A h uh - A h ux := by
        linarith
      rw [hderiv_eval]
      exact hupper'.trans_eq hlin
    have hpair_le_dual :
        DualPairing (AdjointOperator A' (uh - ux)) h ≤
          DualNormDef (AdjointOperator A' (uh - ux)) * ‖h‖ := by
      exact dualPairing_le_dualNormDef_mul_norm_section02
        (s := AdjointOperator A' (uh - ux)) (x := h)
    have hdual_le :
        DualNormDef (AdjointOperator A' (uh - ux)) ≤ OperatorNormDef A' * ‖uh - ux‖ := by
      exact adjointOperator_dualNorm_le (A := A') (uh - ux)
    have hpair_upper :
        A h (uh - ux) ≤ OperatorNormDef A' * ‖uh - ux‖ * ‖h‖ := by
      have hmul := mul_le_mul_of_nonneg_right hdual_le (norm_nonneg h)
      have hupper_tmp :
          DualNormDef (AdjointOperator A' (uh - ux)) * ‖h‖ ≤
            OperatorNormDef A' * ‖uh - ux‖ * ‖h‖ := by
        calc
          DualNormDef (AdjointOperator A' (uh - ux)) * ‖h‖ ≤
              (OperatorNormDef A' * ‖uh - ux‖) * ‖h‖ := hmul
          _ = OperatorNormDef A' * ‖uh - ux‖ * ‖h‖ := by ring
      change DualPairing (AdjointOperator A' (uh - ux)) h ≤
        OperatorNormDef A' * ‖uh - ux‖ * ‖h‖
      exact le_trans hpair_le_dual hupper_tmp
    have hLip_bound : ‖uh - ux‖ ≤ (K : ℝ) * ‖h‖ := by
      simpa [dist_eq_norm, uh, ux, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hLip.dist_le_mul (x + h) x
    have hmul :=
      mul_le_mul_of_nonneg_left hLip_bound
        (mul_nonneg (operatorNormDef_nonneg_section02 (A := A')) (norm_nonneg h))
    have hquad :
        OperatorNormDef A' * ‖uh - ux‖ * ‖h‖ ≤ C * ‖h‖ ^ (2 : ℕ) := by
      calc
        OperatorNormDef A' * ‖uh - ux‖ * ‖h‖ =
            (OperatorNormDef A' * ‖h‖) * ‖uh - ux‖ := by ring
        _ ≤ (OperatorNormDef A' * ‖h‖) * ((K : ℝ) * ‖h‖) := hmul
        _ = C * ‖h‖ ^ (2 : ℕ) := by
            dsimp [C]
            ring
    have herr_abs :
        |fμ (x + h) - fμ x - ((AdjointOperator A' ux).toContinuousLinearMap) h| ≤
          C * ‖h‖ ^ (2 : ℕ) := by
      calc
        |fμ (x + h) - fμ x - ((AdjointOperator A' ux).toContinuousLinearMap) h|
            = fμ (x + h) - fμ x - ((AdjointOperator A' ux).toContinuousLinearMap) h :=
              abs_of_nonneg herr_nonneg
        _ ≤ A h (uh - ux) := herr_le
        _ ≤ OperatorNormDef A' * ‖uh - ux‖ * ‖h‖ := hpair_upper
        _ ≤ C * ‖h‖ ^ (2 : ℕ) := hquad
    have hpow_nonneg : 0 ≤ ‖h‖ ^ (2 : ℕ) := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg] using herr_abs
  exact hbigO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

/-- Structural differentiability of the smoothed max-function from strong convexity of `d2`,
convexity of `phihat`, and a chosen maximizing branch. This is the general-branch helper theorem;
the paper-facing canonical interface is `smoothedMaxFunction_hasFDerivAt` below. -/
lemma smoothedMaxFunction_hasFDerivAt_of_isSmoothedMaximizer {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
  classical
  simp only
  obtain ⟨Kμ, rfl, hLip⟩ :=
    smoothedMaximizer_lipschitz_of_isSmoothedMaximizer (Q2 := Q2) (A := A)
      (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2) (hμ := hμ) (hσ2 := hσ2)
      (hconv := hconv) (hphi := hphi) (uμ := uμ) (hmax := hmax)
  exact smoothedMaxFunction_hasFDerivAt_of_lipschitz (Q2 := Q2) (A := A)
    (phihat := phihat) (d2 := d2) (μ := μ) (uμ := uμ) (hmax := hmax)
    ((OperatorNormDef
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }) / (μ * σ2)).toNNReal hLip

/-- Canonical differentiability statement for the smoothed max-function, using the unique
maximizer selected by `smoothedMaximizer`. This is the closest Lean analogue of the paper's
statement `∇ f_μ(x) = A* u_μ(x)` with `u_μ(x)` defined as the unique maximizer. -/
lemma smoothedMaxFunction_hasFDerivAt {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (hQ2_closed : IsClosed Q2)
    (hQ2_bdd : Bornology.IsBounded Q2) (hQ2_nonempty : Q2.Nonempty)
    (hphihat : ContinuousOn phihat Q2) (hd2 : ContinuousOn d2 Q2) :
    let uμ : E1 → E2 :=
      smoothedMaximizer Q2 A phihat d2 μ hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
  classical
  let uμ : E1 → E2 :=
    smoothedMaximizer Q2 A phihat d2 μ hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2
  have hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x) := by
    simpa [uμ] using
      (smoothedMaximizer_isSmoothedMaximizer (Q2 := Q2) (A := A) (phihat := phihat)
        (d2 := d2) (μ := μ) hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2)
  simpa [uμ] using
    (smoothedMaxFunction_hasFDerivAt_of_isSmoothedMaximizer (Q2 := Q2) (A := A)
      (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2) (hμ := hμ) (hσ2 := hσ2)
      (hconv := hconv) (hphi := hphi) (uμ := uμ) (hmax := hmax))

/-- Explicit derivative formula for the smoothed max-function along an abstract maximizing branch.
This packages equation `(2.6)` at the level of `fderiv`. -/
lemma smoothedMaxFunction_fderiv_of_isSmoothedMaximizer {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∀ x, fderiv ℝ fμ x = ((AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
  classical
  simp only
  intro x
  exact (smoothedMaxFunction_hasFDerivAt_of_isSmoothedMaximizer
    (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
    (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (hphi := hphi) (uμ := uμ)
    (hmax := hmax) x).fderiv

/-- Canonical explicit derivative formula for the smoothed max-function, with
`u_μ(x) := smoothedMaximizer ...`. This is the closest Lean analogue of equation `(2.6)` in the
paper. -/
lemma smoothedMaxFunction_fderiv {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (hQ2_closed : IsClosed Q2)
    (hQ2_bdd : Bornology.IsBounded Q2) (hQ2_nonempty : Q2.Nonempty)
    (hphihat : ContinuousOn phihat Q2) (hd2 : ContinuousOn d2 Q2) :
    let uμ : E1 → E2 :=
      smoothedMaximizer Q2 A phihat d2 μ hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∀ x, fderiv ℝ fμ x = ((AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
  classical
  simp only
  intro x
  exact (smoothedMaxFunction_hasFDerivAt
    (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
    (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (hphi := hphi) (hQ2_closed := hQ2_closed)
    (hQ2_bdd := hQ2_bdd) (hQ2_nonempty := hQ2_nonempty) (hphihat := hphihat) (hd2 := hd2)
    x).fderiv

/-- Equation `(eq:L_mu)` in Theorem 1.2.1: the smoothed max-function gradient is Lipschitz with
constant `(1 / (μ * σ2)) * ‖A‖_{1,2}^2`, derived from strong convexity of `d2` and convexity of
`phihat`. This is the general-branch helper theorem; the paper-facing canonical interface is
`smoothedMaxFunction_gradient_lipschitz` below. -/
lemma smoothedMaxFunction_gradient_lipschitz_of_isSmoothedMaximizer {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∃ Lμ : ℝ,
      Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
        LipschitzWith (Real.toNNReal Lμ)
          (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
  classical
  simp only
  let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp }
  have hcoercive :
      ∀ x1 x2,
        μ * σ2 * ‖uμ x1 - uμ x2‖ ^ (2 : ℕ) ≤
          DualPairing (AdjointOperator A' (uμ x1 - uμ x2)) (x1 - x2) := by
    simpa [A'] using
      (smoothedMaxFunction_key_inequality (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2)
        (μ := μ) (σ2 := σ2) (hμ := hμ) (hconv := hconv) (hphi := hphi) (uμ := uμ)
        (hmax := hmax))
  simpa [A'] using
    (smoothedMaxFunction_gradient_lipschitz_of_coercivity (Q2 := Q2) (A := A)
      (phihat := phihat)
      (d2 := d2) (μ := μ) (σ2 := σ2) (uμ := uμ) (hμ := hμ) (hσ2 := hσ2) hcoercive)

/-- Canonical gradient Lipschitz theorem using the unique smoothed maximizer selected by
`smoothedMaximizer`. This matches the paper's notation `u_μ(x)` as a distinguished optimizer. -/
lemma smoothedMaxFunction_gradient_lipschitz {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (hQ2_closed : IsClosed Q2)
    (hQ2_bdd : Bornology.IsBounded Q2) (hQ2_nonempty : Q2.Nonempty)
    (hphihat : ContinuousOn phihat Q2) (hd2 : ContinuousOn d2 Q2) :
    let uμ : E1 → E2 :=
      smoothedMaximizer Q2 A phihat d2 μ hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ∃ Lμ : ℝ,
      Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
        LipschitzWith (Real.toNNReal Lμ)
          (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
  classical
  simp only
  exact smoothedMaxFunction_gradient_lipschitz_of_isSmoothedMaximizer
    (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
    (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (hphi := hphi)
    (uμ := smoothedMaximizer Q2 A phihat d2 μ hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2)
    (hmax := smoothedMaximizer_isSmoothedMaximizer (Q2 := Q2) (A := A) (phihat := phihat)
      (d2 := d2) (μ := μ) hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2)

/-- Bundled regularity statement using an explicit derivative formula for the maximizing branch.
This is a helper theorem feeding the stronger public interfaces below. -/
private theorem smoothedMaxFunction_properties_of_formula {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (phihat d2 : E2 → ℝ) (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2)
    (hconv : StrongConvexOn Q2 σ2 d2) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ConvexOn ℝ Q2 phihat →
    (∀ x,
        HasFDerivAt (fun y => A y (uμ y) - phihat (uμ y) - μ * d2 (uμ y))
          ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x) →
    ContDiff ℝ (1 : ℕ∞) fμ ∧
      ConvexOn ℝ Set.univ fμ ∧
      (∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x) ∧
      ∃ Lμ : ℝ,
        Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
          LipschitzWith (Real.toNNReal Lμ)
            (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
  classical
  simp only
  intro hphi hformula
  let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
  let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp }
  have _ := hμ
  have _ := hσ2
  have _ := hconv
  have hconvex : ConvexOn ℝ Set.univ fμ := by
    simpa [fμ] using (smoothedMaxFunction_convexOn_univ Q2 A phihat d2 μ uμ hmax)
  have hderiv :
      ∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
    simpa [fμ, A'] using
      (smoothedMaxFunction_hasFDerivAt_of_formula (Q2 := Q2) (A := A) (phihat := phihat)
        (d2 := d2)
        (μ := μ) (uμ := uμ) (hmax := hmax) hformula)
  have hLipschitz :
      ∃ Lμ : ℝ,
        Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
          LipschitzWith (Real.toNNReal Lμ)
            (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
    simpa [A'] using
      (smoothedMaxFunction_gradient_lipschitz_of_isSmoothedMaximizer
        (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
        (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (hphi := hphi) (uμ := uμ)
        (hmax := hmax))
  have hdiff : Differentiable ℝ fμ := by
    intro x
    exact (hderiv x).differentiableAt
  have hfderiv :
      fderiv ℝ fμ = fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap := by
    funext x
    exact (hderiv x).fderiv
  rcases hLipschitz with ⟨Lμ, hLμ, hLip⟩
  have hcont_fderiv : Continuous (fderiv ℝ fμ) := by
    simpa [hfderiv] using hLip.continuous
  have hContDiff : ContDiff ℝ (1 : ℕ∞) fμ := by
    exact (contDiff_one_iff_fderiv).2 ⟨hdiff, hcont_fderiv⟩
  exact ⟨hContDiff, hconvex, hderiv, ⟨Lμ, hLμ, hLip⟩⟩

/-- A stronger bundled regularity statement where the gradient Lipschitz estimate is derived from
strong convexity of `d2` and convexity of `phihat`, while differentiability is obtained from an
explicit stationarity condition in the maximizer variable. -/
private theorem smoothedMaxFunction_properties_of_stationary {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    (∀ x, DifferentiableAt ℝ uμ x) →
    (∀ x,
        HasFDerivAt (fun v => A x v - phihat v - μ * d2 v)
          (0 : E2 →L[ℝ] ℝ) (uμ x)) →
    ContDiff ℝ (1 : ℕ∞) fμ ∧
      ConvexOn ℝ Set.univ fμ ∧
      (∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x) ∧
      ∃ Lμ : ℝ,
        Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
          LipschitzWith (Real.toNNReal Lμ)
            (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
  classical
  simp only
  intro huμ hstationary
  let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp }
  have hformula :
      ∀ x,
        HasFDerivAt (fun y => A y (uμ y) - phihat (uμ y) - μ * d2 (uμ y))
          ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
    simpa [A'] using
      (smoothedMaxFunction_branch_hasFDerivAt_of_stationary (A := A) (phihat := phihat)
        (d2 := d2) (μ := μ) (uμ := uμ) huμ hstationary)
  exact smoothedMaxFunction_properties_of_formula
    (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
    (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (uμ := uμ) (hmax := hmax)
    hphi hformula

/-- Internal bundled regularity theorem for an abstract maximizing branch.
Assume `μ > 0` and that `d2` is `σ2`-strongly convex on `Q2`. Then `f_μ` defined by (2.5) is
well-defined and continuously differentiable for all `x ∈ E1`. Moreover, `f_μ` is convex and
`∇ f_μ(x) = A* u_μ(x)` (equation (2.6)). The gradient is Lipschitz continuous with constant
`L_μ = (1/(μ σ2)) ‖A‖_{1,2}^2` (equation (eq:L_mu)). This is the general-branch helper theorem;
the paper-facing canonical interface is `smoothedMaxFunction_properties` below. -/
private theorem smoothedMaxFunction_properties_of_isSmoothedMaximizer {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ContDiff ℝ (1 : ℕ∞) fμ ∧
      ConvexOn ℝ Set.univ fμ ∧
      (∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x) ∧
      ∃ Lμ : ℝ,
        Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
          LipschitzWith (Real.toNNReal Lμ)
            (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
  classical
  simp only
  let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
  let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp }
  have hconvex : ConvexOn ℝ Set.univ fμ := by
    simpa [fμ] using (smoothedMaxFunction_convexOn_univ Q2 A phihat d2 μ uμ hmax)
  have hderiv :
      ∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x := by
    obtain ⟨Kμ, rfl, hLip⟩ :=
      smoothedMaximizer_lipschitz_of_isSmoothedMaximizer (Q2 := Q2) (A := A)
        (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2) (hμ := hμ) (hσ2 := hσ2)
        (hconv := hconv) (hphi := hphi) (uμ := uμ) (hmax := hmax)
    simpa [fμ, A'] using
      (smoothedMaxFunction_hasFDerivAt_of_lipschitz (Q2 := Q2) (A := A)
        (phihat := phihat) (d2 := d2) (μ := μ) (uμ := uμ) (hmax := hmax)
        ((OperatorNormDef A') / (μ * σ2)).toNNReal hLip)
  have hdiff : Differentiable ℝ fμ := by
    intro x
    exact (hderiv x).differentiableAt
  have hfderiv :
      fderiv ℝ fμ = fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap := by
    funext x
    exact (hderiv x).fderiv
  rcases
      (by
        simpa [A'] using
          (smoothedMaxFunction_gradient_lipschitz_of_isSmoothedMaximizer
            (Q2 := Q2) (A := A) (phihat := phihat)
            (d2 := d2) (μ := μ) (σ2 := σ2) (hμ := hμ) (hσ2 := hσ2) (hconv := hconv)
            (hphi := hphi) (uμ := uμ) (hmax := hmax)) :
        ∃ Lμ : ℝ,
          Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
            LipschitzWith (Real.toNNReal Lμ)
              (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap))
    with ⟨Lμ, hLμ, hLip⟩
  have hcont_fderiv : Continuous (fderiv ℝ fμ) := by
    simpa [hfderiv] using hLip.continuous
  have hContDiff : ContDiff ℝ (1 : ℕ∞) fμ := by
    exact (contDiff_one_iff_fderiv).2 ⟨hdiff, hcont_fderiv⟩
  exact ⟨hContDiff, hconvex, hderiv, ⟨Lμ, hLμ, hLip⟩⟩

/-- Canonical regularity theorem for the smoothed max-function using the unique optimizer
`smoothedMaximizer`. This packages the paper-facing `C^1` regularity and gradient Lipschitz bound
without any external branch assumptions. -/
theorem smoothedMaxFunction_properties {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (hQ2_closed : IsClosed Q2)
    (hQ2_bdd : Bornology.IsBounded Q2) (hQ2_nonempty : Q2.Nonempty)
    (hphihat : ContinuousOn phihat Q2) (hd2 : ContinuousOn d2 Q2) :
    let uμ : E1 → E2 :=
      smoothedMaximizer Q2 A phihat d2 μ hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    ContDiff ℝ (1 : ℕ∞) fμ ∧
      ConvexOn ℝ Set.univ fμ ∧
      (∀ x, HasFDerivAt fμ ((AdjointOperator A' (uμ x)).toContinuousLinearMap) x) ∧
      ∃ Lμ : ℝ,
        Lμ = (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 ∧
          LipschitzWith (Real.toNNReal Lμ)
            (fun x => (AdjointOperator A' (uμ x)).toContinuousLinearMap) := by
  classical
  simp only
  exact smoothedMaxFunction_properties_of_isSmoothedMaximizer
    (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
    (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (hphi := hphi)
    (uμ := smoothedMaximizer Q2 A phihat d2 μ hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2)
    (hmax := smoothedMaximizer_isSmoothedMaximizer (Q2 := Q2) (A := A) (phihat := phihat)
      (d2 := d2) (μ := μ) hQ2_closed hQ2_bdd hQ2_nonempty hphihat hd2)

/-- Continuous differentiability of the smoothed max-function along an abstract maximizing branch. -/
private theorem smoothedMaxFunction_contDiff_of_isSmoothedMaximizer {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    ContDiff ℝ (1 : ℕ∞) fμ := by
  classical
  simp only
  rcases smoothedMaxFunction_properties_of_isSmoothedMaximizer
      (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
      (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (hphi := hphi) (uμ := uμ)
      (hmax := hmax) with ⟨hContDiff, _, _, _⟩
  exact hContDiff

/-- Canonical continuous differentiability theorem for the smoothed max-function, using
`u_μ := smoothedMaximizer ...`. -/
theorem smoothedMaxFunction_contDiff {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (hQ2_closed : IsClosed Q2)
    (hQ2_bdd : Bornology.IsBounded Q2) (hQ2_nonempty : Q2.Nonempty)
    (hphihat : ContinuousOn phihat Q2) (hd2 : ContinuousOn d2 Q2) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    ContDiff ℝ (1 : ℕ∞) fμ := by
  classical
  simp only
  rcases smoothedMaxFunction_properties
      (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
      (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (hphi := hphi) (hQ2_closed := hQ2_closed)
      (hQ2_bdd := hQ2_bdd) (hQ2_nonempty := hQ2_nonempty) (hphihat := hphihat) (hd2 := hd2)
    with ⟨hContDiff, _, _, _⟩
  exact hContDiff

/-- Differentiability of the smoothed max-function along an abstract maximizing branch. -/
theorem smoothedMaxFunction_differentiable_of_isSmoothedMaximizer {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    Differentiable ℝ fμ := by
  classical
  simp only
  exact
    (smoothedMaxFunction_contDiff_of_isSmoothedMaximizer
      (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
      (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (hphi := hphi) (uμ := uμ)
      (hmax := hmax)).differentiable (by decide)

/-- Canonical differentiability theorem for the smoothed max-function, using
`u_μ := smoothedMaximizer ...`. -/
theorem smoothedMaxFunction_differentiable {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (hQ2_closed : IsClosed Q2)
    (hQ2_bdd : Bornology.IsBounded Q2) (hQ2_nonempty : Q2.Nonempty)
    (hphihat : ContinuousOn phihat Q2) (hd2 : ContinuousOn d2 Q2) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    Differentiable ℝ fμ := by
  classical
  simp only
  have hContDiff :
      ContDiff ℝ (1 : ℕ∞) (SmoothedMaxFunction Q2 A phihat d2 μ) := by
    simpa using
      (smoothedMaxFunction_contDiff
        (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
        (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (hphi := hphi)
        (hQ2_closed := hQ2_closed) (hQ2_bdd := hQ2_bdd) (hQ2_nonempty := hQ2_nonempty)
        (hphihat := hphihat) (hd2 := hd2))
  exact hContDiff.differentiable (by decide)

/-- Convexity of the smoothed max-function along an abstract maximizing branch. -/
theorem smoothedMaxFunction_convex_of_isSmoothedMaximizer {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    ConvexOn ℝ Set.univ fμ := by
  classical
  simp only
  rcases smoothedMaxFunction_properties_of_isSmoothedMaximizer
      (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
      (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (hphi := hphi) (uμ := uμ)
      (hmax := hmax) with ⟨_, hconvex, _, _⟩
  exact hconvex

/-- Canonical convexity theorem for the smoothed max-function, using
`u_μ := smoothedMaximizer ...`. -/
theorem smoothedMaxFunction_convex {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ)
    (μ σ2 : ℝ) (hμ : 0 < μ) (hσ2 : 0 < σ2) (hconv : StrongConvexOn Q2 σ2 d2)
    (hphi : ConvexOn ℝ Q2 phihat) (hQ2_closed : IsClosed Q2)
    (hQ2_bdd : Bornology.IsBounded Q2) (hQ2_nonempty : Q2.Nonempty)
    (hphihat : ContinuousOn phihat Q2) (hd2 : ContinuousOn d2 Q2) :
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    ConvexOn ℝ Set.univ fμ := by
  classical
  simp only
  rcases smoothedMaxFunction_properties
      (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ) (σ2 := σ2)
      (hμ := hμ) (hσ2 := hσ2) (hconv := hconv) (hphi := hphi) (hQ2_closed := hQ2_closed)
      (hQ2_bdd := hQ2_bdd) (hQ2_nonempty := hQ2_nonempty) (hphihat := hphihat) (hd2 := hd2)
    with ⟨_, hconvex, _, _⟩
  exact hconvex
