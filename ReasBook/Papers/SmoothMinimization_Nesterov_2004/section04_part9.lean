/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import Papers.SmoothMinimization_Nesterov_2004.section04_part8

set_option maxHeartbeats 200000

/-- Definition 1.4.3.1.
Let `E` be a finite-dimensional normed space with norm `‖·‖_1` and dual norm `‖·‖_{1,*}` on `E*`.
Let `Q ⊆ E` be bounded, closed, and convex. Let `B : E → E*` be affine with
`B w = ℬ w + b`, where `ℬ : E → E*` is linear and `b ∈ E*`, and assume the monotonicity
condition `⟪ℬ h, h⟫_1 ≥ 0` for all `h`. The associated variational inequality problem (4.18)
is to find `w* ∈ Q` such that `⟪B w*, w - w*⟫_1 ≥ 0` for all `w ∈ Q`. -/
def IsVariationalInequalitySolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (ℬ : E →ₗ[ℝ] Module.Dual ℝ E)
    (b : Module.Dual ℝ E) (wstar : E) : Prop :=
  let B : E → Module.Dual ℝ E := fun w => ℬ w + b
  wstar ∈ Q ∧ ∀ w ∈ Q, 0 ≤ B wstar (w - wstar)

/-- Definition 1.4.3.2.
Define the gap function `ψ(w) := max_{v ∈ Q} ⟪B(v), w - v⟫_1`. Consider the convex
optimization problem `min_{w ∈ Q} ψ(w)` (equation (4.19)). -/
noncomputable def variationalInequalityGap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Q : Set E) (B : E → Module.Dual ℝ E) (w : E) : ℝ :=
  sSup ((fun v => B v (w - v)) '' Q)

/-- Definition 1.4.3.2.
The optimal value of the gap minimization problem `min_{w ∈ Q} ψ(w)`. -/
noncomputable def variationalInequalityGapOptimalValue {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Q : Set E) (B : E → Module.Dual ℝ E) : ℝ :=
  sInf ((fun w => variationalInequalityGap Q B w) '' Q)

namespace variationalInequality

/-- Expanding the affine operator `B w = ℬ w + b` against a displacement. -/
lemma B_apply_sub_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℬ : E →ₗ[ℝ] Module.Dual ℝ E) (b : Module.Dual ℝ E) (v w : E) :
    let B : E → Module.Dual ℝ E := fun z => ℬ z + b
    (B v - B w) (v - w) = (ℬ (v - w)) (v - w) := by
  intro B
  have hB : B v - B w = ℬ v - ℬ w := by
    ext x
    simp [B, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  calc
    (B v - B w) (v - w) = (ℬ v - ℬ w) (v - w) := by simp [hB]
    _ = (ℬ (v - w)) (v - w) := by
      simp [map_sub]

/-- Monotonicity of `ℬ` yields pointwise nonpositivity of the gap at a VI solution. -/
lemma VI_implies_pointwise_gap_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (ℬ : E →ₗ[ℝ] Module.Dual ℝ E)
    (b : Module.Dual ℝ E) (hmono : ∀ h : E, 0 ≤ (ℬ h) h) {wstar : E} :
    let B : E → Module.Dual ℝ E := fun w => ℬ w + b
    IsVariationalInequalitySolution Q ℬ b wstar →
      ∀ v ∈ Q, B v (wstar - v) ≤ 0 := by
  intro B hVI v hv
  rcases hVI with ⟨_, hVI⟩
  have hBws : 0 ≤ B wstar (v - wstar) := hVI v hv
  have hmono' : 0 ≤ (B v - B wstar) (v - wstar) := by
    have hsub :
        (B v - B wstar) (v - wstar) = (ℬ (v - wstar)) (v - wstar) := by
      simp [B]
    have hmono_term : 0 ≤ (ℬ (v - wstar)) (v - wstar) := hmono (v - wstar)
    rw [hsub.symm] at hmono_term
    exact hmono_term
  have hBge : B wstar (v - wstar) ≤ B v (v - wstar) := by
    have h' : 0 ≤ B v (v - wstar) - B wstar (v - wstar) := by
      simpa using hmono'
    linarith
  have hBv_nonneg : 0 ≤ B v (v - wstar) := le_trans hBws hBge
  have hneg : B v (wstar - v) = -B v (v - wstar) := by
    have : wstar - v = -(v - wstar) := by
      abel
    calc
      B v (wstar - v) = B v (-(v - wstar)) := by rw [this]
      _ = -B v (v - wstar) := by
        simp
  have : -B v (v - wstar) ≤ 0 := by
    exact neg_nonpos.mpr hBv_nonneg
  simpa [hneg] using this

/-- The gap at a VI solution is zero. -/
lemma VI_implies_gap_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (ℬ : E →ₗ[ℝ] Module.Dual ℝ E)
    (b : Module.Dual ℝ E) (hmono : ∀ h : E, 0 ≤ (ℬ h) h) {wstar : E} :
    let B : E → Module.Dual ℝ E := fun w => ℬ w + b
    IsVariationalInequalitySolution Q ℬ b wstar →
      variationalInequalityGap Q B wstar = 0 := by
  intro B hVI
  have hle : ∀ v ∈ Q, B v (wstar - v) ≤ 0 := by
    simpa [B] using
      (VI_implies_pointwise_gap_le (Q := Q) (ℬ := ℬ) (b := b) hmono (wstar := wstar) hVI)
  have hne : ((fun v => B v (wstar - v)) '' Q).Nonempty := by
    rcases hVI with ⟨hwQ, _⟩
    refine ⟨B wstar (wstar - wstar), ?_⟩
    refine ⟨wstar, hwQ, by simp⟩
  have hsup_le : sSup ((fun v => B v (wstar - v)) '' Q) ≤ 0 := by
    refine csSup_le hne ?_
    rintro y ⟨v, hv, rfl⟩
    exact hle v hv
  have hbd : BddAbove ((fun v => B v (wstar - v)) '' Q) := by
    refine ⟨0, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    exact hle v hv
  have hsup_ge : 0 ≤ sSup ((fun v => B v (wstar - v)) '' Q) := by
    rcases hVI with ⟨hwQ, _⟩
    have h0 : (0 : ℝ) ∈ ((fun v => B v (wstar - v)) '' Q) := by
      refine ⟨wstar, hwQ, by simp⟩
    exact le_csSup hbd h0
  have hgap : variationalInequalityGap Q B wstar =
      sSup ((fun v => B v (wstar - v)) '' Q) := rfl
  apply le_antisymm
  · simpa [hgap] using hsup_le
  · simpa [hgap] using hsup_ge

/-- Nonnegativity of the gap at points of `Q`, assuming boundedness of the image. -/
lemma gap_nonneg_of_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) (B : E → Module.Dual ℝ E) {w : E} (hw : w ∈ Q)
    (hbd : BddAbove ((fun v => B v (w - v)) '' Q)) :
    0 ≤ variationalInequalityGap Q B w := by
  have h0 : (0 : ℝ) ∈ ((fun v => B v (w - v)) '' Q) := by
    refine ⟨w, hw, by simp⟩
  have hle : (0 : ℝ) ≤ sSup ((fun v => B v (w - v)) '' Q) := le_csSup hbd h0
  simpa [variationalInequalityGap] using hle

/-- If the gap is zero at `w*`, then `w*` minimizes the gap on `Q`. -/
lemma gap_eq_zero_implies_isMinOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) (B : E → Module.Dual ℝ E) {wstar : E}
    (hbd : ∀ w ∈ Q, BddAbove ((fun v => B v (w - v)) '' Q)) (_hw : wstar ∈ Q)
    (hgap : variationalInequalityGap Q B wstar = 0) :
    IsMinOn (variationalInequalityGap Q B) Q wstar := by
  refine (isMinOn_iff).2 ?_
  intro w hwQ
  have hnonneg : 0 ≤ variationalInequalityGap Q B w :=
    gap_nonneg_of_mem (Q := Q) (B := B) (w := w) hwQ (hbd w hwQ)
  simpa [hgap] using hnonneg

/-- A quadratic inequality with a negative linear coefficient can be made negative on `(0,1]`. -/
lemma exists_alpha_neg_quadratic {a b : ℝ} (ha : a < 0) (hb : 0 ≤ b) :
    ∃ α, 0 < α ∧ α ≤ 1 ∧ a * α + b * α ^ 2 < 0 := by
  have ha' : 0 < -a := by linarith
  obtain ⟨α1, hα1pos, hα1lt⟩ := exists_pos_mul_lt ha' b
  let α := min α1 1
  have hαpos : 0 < α := by
    have h1 : 0 < (1 : ℝ) := by norm_num
    exact (lt_min_iff).2 ⟨hα1pos, h1⟩
  have hαle : α ≤ 1 := min_le_right _ _
  have hαle' : α ≤ α1 := min_le_left _ _
  have hmul : b * α < -a := by
    have hmul_le : b * α ≤ b * α1 := by
      exact mul_le_mul_of_nonneg_left hαle' hb
    exact lt_of_le_of_lt hmul_le hα1lt
  have hsum : a + b * α < 0 := by linarith
  have hneg : a * α + b * α ^ 2 < 0 := by
    have hform : a * α + b * α ^ 2 = α * (a + b * α) := by
      ring
    have : α * (a + b * α) < 0 := mul_neg_of_pos_of_neg hαpos hsum
    simpa [hform] using this
  exact ⟨α, hαpos, hαle, hneg⟩

/-- Zero gap forces the variational inequality, using convexity and monotonicity. -/
lemma gap_eq_zero_implies_VI {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (ℬ : E →ₗ[ℝ] Module.Dual ℝ E)
    (b : Module.Dual ℝ E) (hmono : ∀ h : E, 0 ≤ (ℬ h) h) (hconv : Convex ℝ Q)
    (hbd : ∀ w ∈ Q, BddAbove ((fun v => (ℬ v + b) (w - v)) '' Q)) {wstar : E}
    (hw : wstar ∈ Q)
    (hgap : variationalInequalityGap Q (fun w => ℬ w + b) wstar = 0) :
    IsVariationalInequalitySolution Q ℬ b wstar := by
  classical
  let B : E → Module.Dual ℝ E := fun w => ℬ w + b
  refine ⟨hw, ?_⟩
  intro v hv
  by_contra hneg
  have hlt : B wstar (v - wstar) < 0 := lt_of_not_ge hneg
  have hmono_term : 0 ≤ (ℬ (v - wstar)) (v - wstar) := hmono (v - wstar)
  obtain ⟨α, hαpos, hαle, hαneg⟩ :=
    exists_alpha_neg_quadratic (a := B wstar (v - wstar)) (b := (ℬ (v - wstar)) (v - wstar)) hlt
      hmono_term
  set vα : E := wstar + α • (v - wstar)
  have hαmem : α ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hαpos, hαle⟩
  have hvα : vα ∈ Q := by
    simpa [vα] using hconv.add_smul_sub_mem hw hv hαmem
  have hbd_wstar : BddAbove ((fun u => B u (wstar - u)) '' Q) := by
    simpa [B] using hbd wstar hw
  have hle_gap : B vα (wstar - vα) ≤ variationalInequalityGap Q B wstar := by
    have hmem : B vα (wstar - vα) ∈ ((fun u => B u (wstar - u)) '' Q) := by
      exact ⟨vα, hvα, rfl⟩
    exact le_csSup hbd_wstar hmem
  have hgap_le : B vα (wstar - vα) ≤ 0 := by
    have hle_gap' := hle_gap
    rw [hgap] at hle_gap'
    exact hle_gap'
  have hgap_ge : 0 ≤ B vα (vα - wstar) := by
    have hneg' : B vα (vα - wstar) = -B vα (wstar - vα) := by
      have : vα - wstar = -(wstar - vα) := by
        abel
      calc
        B vα (vα - wstar) = B vα (-(wstar - vα)) := by rw [this]
        _ = -B vα (wstar - vα) := by
          simp
    have : 0 ≤ -B vα (wstar - vα) := neg_nonneg.mpr hgap_le
    simpa [hneg'] using this
  have hsub : vα - wstar = α • (v - wstar) := by
    simp [vα]
  have hdecomp :
      B vα (vα - wstar) =
        B wstar (vα - wstar) + (B vα - B wstar) (vα - wstar) := by
    have h' :
        B vα (vα - wstar) - B wstar (vα - wstar) =
          (B vα - B wstar) (vα - wstar) := by
      simp
    linarith
  have hsubB :
      (B vα - B wstar) (vα - wstar) = (ℬ (vα - wstar)) (vα - wstar) := by
    simp [B]
  have hcalc :
      B vα (vα - wstar) =
        α * B wstar (v - wstar) +
          α ^ 2 * (ℬ (v - wstar)) (v - wstar) := by
    calc
      B vα (vα - wstar) =
          B wstar (vα - wstar) + (ℬ (vα - wstar)) (vα - wstar) := by
            simpa [hsubB] using hdecomp
      _ =
          B wstar (α • (v - wstar)) + (ℬ (α • (v - wstar))) (α • (v - wstar)) := by
            simp [hsub]
      _ =
          α * B wstar (v - wstar) +
            α * (α * (ℬ (v - wstar)) (v - wstar)) := by
            simp [map_smul, smul_eq_mul]
      _ =
          α * B wstar (v - wstar) +
            α ^ 2 * (ℬ (v - wstar)) (v - wstar) := by
            ring
  have hcontr : ¬0 ≤ α * B wstar (v - wstar) +
      α ^ 2 * (ℬ (v - wstar)) (v - wstar) := by
    have hneg' :
        α * B wstar (v - wstar) +
            α ^ 2 * (ℬ (v - wstar)) (v - wstar) < 0 := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hαneg
    exact not_le_of_gt hneg'
  exact hcontr (by simpa [hcalc] using hgap_ge)

/-- A gap minimizer has zero gap when a zero-gap point exists in `Q`. -/
lemma isMinOn_gap_eq_zero_of_exists_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) (B : E → Module.Dual ℝ E) {wstar : E}
    (hbd : ∀ w ∈ Q, BddAbove ((fun v => B v (w - v)) '' Q)) (hw : wstar ∈ Q) :
    IsMinOn (variationalInequalityGap Q B) Q wstar →
      (∃ w0 ∈ Q, variationalInequalityGap Q B w0 = 0) →
        variationalInequalityGap Q B wstar = 0 := by
  intro hmin hzero
  rcases hzero with ⟨w0, hw0Q, hgap0⟩
  have hmin' := (isMinOn_iff.mp hmin)
  have hle : variationalInequalityGap Q B wstar ≤ variationalInequalityGap Q B w0 :=
    hmin' w0 hw0Q
  have hle0 : variationalInequalityGap Q B wstar ≤ 0 := by
    simpa [hgap0] using hle
  have hnonneg : 0 ≤ variationalInequalityGap Q B wstar :=
    gap_nonneg_of_mem (Q := Q) (B := B) (w := wstar) hw (hbd wstar hw)
  exact le_antisymm hle0 hnonneg

end variationalInequality

/-- Lemma 1.4.3.1.
A point `w*` solves the gap minimization problem `min_{w ∈ Q} ψ(w)` (4.19) if and only if it
solves the variational inequality (4.18). Moreover, for every solution `w*` of (4.18) we have
`ψ(w*) = 0`. -/
theorem variationalInequality_solution_iff_gap_minimizer {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Q : Set E)
    (ℬ : E →ₗ[ℝ] Module.Dual ℝ E) (b : Module.Dual ℝ E) (wstar : E)
    (hmono : ∀ h : E, 0 ≤ (ℬ h) h) (hconv : Convex ℝ Q)
    (hbd : ∀ w ∈ Q, BddAbove ((fun v => (ℬ v + b) (w - v)) '' Q))
    (hex : ∃ w0, IsVariationalInequalitySolution Q ℬ b w0) :
    let B : E → Module.Dual ℝ E := fun w => ℬ w + b
    (IsVariationalInequalitySolution Q ℬ b wstar ↔
        wstar ∈ Q ∧ IsMinOn (variationalInequalityGap Q B) Q wstar) ∧
      (IsVariationalInequalitySolution Q ℬ b wstar →
        variationalInequalityGap Q B wstar = 0) := by
  classical
  intro B
  refine ⟨?_, ?_⟩
  · constructor
    · intro hVI
      have hgap :
          variationalInequalityGap Q B wstar = 0 := by
        simpa [B] using
          (variationalInequality.VI_implies_gap_eq_zero (Q := Q) (ℬ := ℬ) (b := b) hmono
            (wstar := wstar) hVI)
      refine ⟨hVI.1, ?_⟩
      have hbd' : ∀ w ∈ Q, BddAbove ((fun v => B v (w - v)) '' Q) := by
        intro w hw
        simpa [B] using hbd w hw
      exact
        variationalInequality.gap_eq_zero_implies_isMinOn (Q := Q) (B := B) hbd' hVI.1 hgap
    · intro hmin
      have hbd' : ∀ w ∈ Q, BddAbove ((fun v => B v (w - v)) '' Q) := by
        intro w hw
        simpa [B] using hbd w hw
      have hzero : ∃ w0 ∈ Q, variationalInequalityGap Q B w0 = 0 := by
        rcases hex with ⟨w0, hVI0⟩
        refine ⟨w0, hVI0.1, ?_⟩
        simpa [B] using
          (variationalInequality.VI_implies_gap_eq_zero (Q := Q) (ℬ := ℬ) (b := b) hmono
            (wstar := w0) hVI0)
      have hgap : variationalInequalityGap Q B wstar = 0 := by
        exact
          variationalInequality.isMinOn_gap_eq_zero_of_exists_zero (Q := Q) (B := B) hbd' hmin.1
            hmin.2 hzero
      exact
        variationalInequality.gap_eq_zero_implies_VI (Q := Q) (ℬ := ℬ) (b := b) hmono hconv hbd'
          hmin.1 hgap
  · intro hVI
    simpa [B] using
      (variationalInequality.VI_implies_gap_eq_zero (Q := Q) (ℬ := ℬ) (b := b) hmono
        (wstar := wstar) hVI)

/-- Rearrangement of the smoothed max integrand used in Proposition 1.4.3.1. -/
lemma variationalInequality_gap_smoothedOracle_pointwise_rearrange {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℬ : E →L[ℝ] (E →L[ℝ] ℝ)) (b : Module.Dual ℝ E) (d : E → ℝ) (μ : ℝ) (x u : E) :
    ℬ x u - (b u - ℬ u u) - μ * d u = ℬ x u - μ * d u - b u + ℬ u u := by
  ring

/-- Proposition 1.4.3.1.
A primal max-structure representation of the objective `ψ` in (4.19) is obtained by taking
`E1 = E2 = E`, `Q1 = Q2 = Q`, `d1 = d2 = d`, `A = ℬ`, `fhat(x) = ⟪b,x⟫_1`, and
`phihat(u) = ⟪b,u⟫_1 + ⟪ℬ u,u⟫_1`. Then the smoothed oracle computation for `f_μ(x)` reduces to
solving `max_{u ∈ Q} {⟪ℬ x,u⟫_1 - μ d(u) - ⟪b,u⟫_1 + ⟪ℬ u,u⟫_1}` (equation (4.20)). -/
theorem variationalInequality_gap_smoothedOracle {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Q : Set E)
    (ℬ : E →L[ℝ] (E →L[ℝ] ℝ)) (b : Module.Dual ℝ E) (d : E → ℝ) (μ : ℝ) :
    let _fhat : E → ℝ := fun x => b x
    let phihat : E → ℝ := fun u => b u - ℬ u u
    let fμ : E → ℝ := SmoothedMaxFunction Q ℬ phihat d μ
    ∀ x : E,
      fμ x =
        sSup ((fun u => ℬ x u - μ * d u - b u + ℬ u u) '' Q) := by
  classical
  dsimp
  intro x
  simp [SmoothedMaxFunction, variationalInequality_gap_smoothedOracle_pointwise_rearrange]

/-- The iteration-complexity constant in Proposition 1.4.3.2 is nonnegative. -/
lemma variationalInequality_iteration_complexity_const_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (ℬ : E →ₗ[ℝ] Module.Dual ℝ E)
    {σ1 D1 ε : ℝ} (hε : 0 < ε) (hσ1 : 0 < σ1) (hD1 : 0 ≤ D1) :
    0 ≤ (4 * D1 * OperatorNormDef ℬ) / (σ1 * ε) := by
  have hOp : 0 ≤ OperatorNormDef ℬ := operatorNormDef_nonneg ℬ
  have hnum : 0 ≤ 4 * D1 * OperatorNormDef ℬ := by
    have h4 : 0 ≤ (4 : ℝ) := by norm_num
    have h4D1 : 0 ≤ (4 : ℝ) * D1 := mul_nonneg h4 hD1
    exact mul_nonneg h4D1 hOp
  have hden : 0 ≤ σ1 * ε := by
    exact mul_nonneg (le_of_lt hσ1) (le_of_lt hε)
  exact div_nonneg hnum hden

/-- Rounding a nonnegative real by the natural floor yields a nearby integer. -/
lemma exists_nat_floor_sandwich {C : ℝ} (hC : 0 ≤ C) :
    ∃ N : ℕ, (N : ℝ) ≤ C ∧ C < (N : ℝ) + 1 := by
  refine ⟨⌊C⌋₊, Nat.floor_le hC, ?_⟩
  simpa using (Nat.lt_floor_add_one C)

/-- Proposition 1.4.3.2.
Assume `fhat(x) = ⟪b, x⟫_1` in Proposition 1.4.3.1 so `M = 0`. Then Theorem 1.4.1 yields the
iteration-complexity estimate for solving the variational inequality (4.18) to accuracy
`ε > 0`:
`N ≤ (4 * D1 * ‖ℬ‖_{1,2}) / (σ1 * ε)` (equation (4.21)). -/
theorem variationalInequality_iteration_complexity {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Q : Set E)
    (ℬ : E →ₗ[ℝ] Module.Dual ℝ E) (b : Module.Dual ℝ E) (d1 : E → ℝ)
    (σ1 D1 ε : ℝ) :
    0 < ε →
    0 < σ1 →
    StrongConvexOn Q σ1 d1 →
    IsProxDiameterBound Q d1 D1 →
    0 ≤ D1 →
    ∃ N : ℕ,
      (N : ℝ) ≤ (4 * D1 * OperatorNormDef ℬ) / (σ1 * ε) ∧
        (4 * D1 * OperatorNormDef ℬ) / (σ1 * ε) < (N : ℝ) + 1 := by
  intro hε hσ1 _ _ hD1
  have hb : b = b := rfl
  have hC :
      0 ≤ (4 * D1 * OperatorNormDef ℬ) / (σ1 * ε) :=
    variationalInequality_iteration_complexity_const_nonneg (ℬ := ℬ) hε hσ1 hD1
  simpa using
    (exists_nat_floor_sandwich (C := (4 * D1 * OperatorNormDef ℬ) / (σ1 * ε)) hC)
