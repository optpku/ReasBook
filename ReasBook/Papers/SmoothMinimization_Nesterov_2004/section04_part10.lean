/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import Papers.SmoothMinimization_Nesterov_2004.section04_part9

open scoped NNReal
open scoped Pointwise
open scoped BigOperators

namespace Section04Part10

open variationalInequality

/-- Image under negation is scalar multiplication by `-1` on `ℝ`. -/
lemma image_neg_eq_smul (s : Set ℝ) : (fun x => -x) '' s = (-1 : ℝ) • s := by
  ext x; constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp⟩

/-- Push a negation through `sSup` for subsets of `ℝ`. -/
lemma sSup_image_neg_eq_neg_sInf (s : Set ℝ) :
    sSup ((fun x => -x) '' s) = - sInf s := by
  have hsup := Real.sSup_smul_of_nonpos (a := (-1 : ℝ)) (by linarith) s
  simpa [image_neg_eq_smul] using hsup

/-- Push a negation through `sInf` for subsets of `ℝ`. -/
lemma sInf_image_neg_eq_neg_sSup (s : Set ℝ) :
    sInf ((fun x => -x) '' s) = - sSup s := by
  have h := Real.sInf_smul_of_nonpos (a := (-1 : ℝ)) (by linarith) s
  simpa [image_neg_eq_smul] using h

namespace variationalInequality

/-- A saddle point with bounded images forces the minimax equality by showing both sides are
zero. -/
lemma minimax_eq_of_saddlePoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) (B : E → Module.Dual ℝ E) {w0 : E} (hw0 : w0 ∈ Q)
    (hgap_le : ∀ v ∈ Q, B v (w0 - v) ≤ 0) (hgap_ge : ∀ w ∈ Q, 0 ≤ B w0 (w - w0))
    (hbdAbove : ∀ w ∈ Q, BddAbove ((fun v => B v (w - v)) '' Q))
    (hbdBelow : ∀ v ∈ Q, BddBelow ((fun w => B v (w - v)) '' Q)) :
    sInf ((fun w => sSup ((fun v => B v (w - v)) '' Q)) '' Q) =
      sSup ((fun v => sInf ((fun w => B v (w - v)) '' Q)) '' Q) := by
  classical
  set S : Set ℝ := (fun w => sSup ((fun v => B v (w - v)) '' Q)) '' Q
  set T : Set ℝ := (fun v => sInf ((fun w => B v (w - v)) '' Q)) '' Q
  have hS_nonempty : S.Nonempty := by
    refine ⟨sSup ((fun v => B v (w0 - v)) '' Q), ?_⟩
    exact ⟨w0, hw0, rfl⟩
  have hT_nonempty : T.Nonempty := by
    refine ⟨sInf ((fun w => B w0 (w - w0)) '' Q), ?_⟩
    exact ⟨w0, hw0, rfl⟩
  have hS_nonneg : ∀ x ∈ S, (0 : ℝ) ≤ x := by
    intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    have hbd := hbdAbove w hw
    simpa [variationalInequalityGap] using
      (gap_nonneg_of_mem (Q := Q) (B := B) (w := w) hw hbd)
  have hS_inf_ge : (0 : ℝ) ≤ sInf S := by
    refine le_csInf hS_nonempty ?_
    intro x hx
    exact hS_nonneg x hx
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro x hx
    exact hS_nonneg x hx
  have hsup_w0_le : sSup ((fun v => B v (w0 - v)) '' Q) ≤ 0 := by
    have hne : ((fun v => B v (w0 - v)) '' Q).Nonempty := by
      refine ⟨B w0 (w0 - w0), ?_⟩
      exact ⟨w0, hw0, by simp⟩
    refine csSup_le hne ?_
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact hgap_le v hv
  have hS_inf_le : sInf S ≤ 0 := by
    have hmem : sSup ((fun v => B v (w0 - v)) '' Q) ∈ S := by
      exact ⟨w0, hw0, rfl⟩
    exact le_trans (csInf_le hS_bddBelow hmem) hsup_w0_le
  have hS_eq : sInf S = 0 := by
    exact le_antisymm hS_inf_le hS_inf_ge
  have hT_le_elem : ∀ x ∈ T, x ≤ 0 := by
    intro x hx
    rcases hx with ⟨v, hv, rfl⟩
    have hbd := hbdBelow v hv
    have hmem : (0 : ℝ) ∈ ((fun w => B v (w - v)) '' Q) := by
      exact ⟨v, hv, by simp⟩
    exact csInf_le hbd hmem
  have hT_le : sSup T ≤ 0 := by
    refine csSup_le hT_nonempty ?_
    intro x hx
    exact hT_le_elem x hx
  have hT_bddAbove : BddAbove T := by
    refine ⟨0, ?_⟩
    intro x hx
    exact hT_le_elem x hx
  have hT_inf_w0_ge : (0 : ℝ) ≤ sInf ((fun w => B w0 (w - w0)) '' Q) := by
    have hne : ((fun w => B w0 (w - w0)) '' Q).Nonempty := by
      refine ⟨B w0 (w0 - w0), ?_⟩
      exact ⟨w0, hw0, by simp⟩
    refine le_csInf hne ?_
    intro y hy
    rcases hy with ⟨w, hw, rfl⟩
    exact hgap_ge w hw
  have hT_sup_ge : (0 : ℝ) ≤ sSup T := by
    have hmem : sInf ((fun w => B w0 (w - w0)) '' Q) ∈ T := by
      exact ⟨w0, hw0, rfl⟩
    have hle :
        sInf ((fun w => B w0 (w - w0)) '' Q) ≤ sSup T :=
      le_csSup hT_bddAbove hmem
    exact le_trans hT_inf_w0_ge hle
  have hT_eq : sSup T = 0 := by
    exact le_antisymm hT_le hT_sup_ge
  have hmain : sInf S = sSup T := hS_eq.trans hT_eq.symm
  simpa [S, T] using hmain

/-- A VI solution yields a saddle point for the gap payoff, hence the minimax equality. -/
lemma minimax_eq_of_exists_VI_solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (ℬ : E →ₗ[ℝ] Module.Dual ℝ E)
    (b : Module.Dual ℝ E) (hmono : ∀ h : E, 0 ≤ (ℬ h) h)
    (hex : ∃ w0, IsVariationalInequalitySolution Q ℬ b w0)
    (hbdAbove : ∀ w ∈ Q, BddAbove ((fun v => (ℬ v + b) (w - v)) '' Q))
    (hbdBelow : ∀ v ∈ Q, BddBelow ((fun w => (ℬ v + b) (w - v)) '' Q)) :
    sInf ((fun w => sSup ((fun v => (ℬ v + b) (w - v)) '' Q)) '' Q) =
      sSup ((fun v => sInf ((fun w => (ℬ v + b) (w - v)) '' Q)) '' Q) := by
  classical
  rcases hex with ⟨w0, hVI⟩
  have hw0 : w0 ∈ Q := hVI.1
  have hgap_ge : ∀ w ∈ Q, 0 ≤ (ℬ w0 + b) (w - w0) := hVI.2
  have hgap_le : ∀ v ∈ Q, (ℬ v + b) (w0 - v) ≤ 0 := by
    simpa using
      (VI_implies_pointwise_gap_le (Q := Q) (ℬ := ℬ) (b := b) hmono (wstar := w0) hVI)
  exact
    minimax_eq_of_saddlePoint (Q := Q) (B := fun v => ℬ v + b) (w0 := w0) hw0 hgap_le
      hgap_ge hbdAbove hbdBelow

end variationalInequality

/-- Reformulate the inner max by flipping the sign. -/
lemma variationalInequality_sign_flip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) (B : E → Module.Dual ℝ E) :
    sSup ((fun v => sInf ((fun w => B v (w - v)) '' Q)) '' Q) =
      - sInf ((fun v => sSup ((fun w => B v (v - w)) '' Q)) '' Q) := by
  classical
  let F : E → ℝ := fun v => sInf ((fun w => B v (w - v)) '' Q)
  let G : E → ℝ := fun v => sSup ((fun w => B v (v - w)) '' Q)
  have hneg : ∀ v, G v = - F v := by
    intro v
    have himage :
        (fun w => B v (v - w)) '' Q =
          (fun t => -t) '' ((fun w => B v (w - v)) '' Q) := by
      ext x; constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨B v (w - v), ?_, ?_⟩
        · exact ⟨w, hw, rfl⟩
        · have h : v - w = -(w - v) := by abel
          symm
          calc
            B v (v - w) = B v (-(w - v)) := by rw [h]
            _ = - B v (w - v) := by
              simp
      · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
        refine ⟨w, hw, ?_⟩
        have h : v - w = -(w - v) := by abel
        calc
          B v (v - w) = B v (-(w - v)) := by rw [h]
          _ = - B v (w - v) := by
            simp
    calc
      G v = sSup ((fun w => B v (v - w)) '' Q) := by rfl
      _ = sSup ((fun t => -t) '' ((fun w => B v (w - v)) '' Q)) := by rw [himage]
      _ = - sInf ((fun w => B v (w - v)) '' Q) := by
        simpa using (sSup_image_neg_eq_neg_sInf ((fun w => B v (w - v)) '' Q))
      _ = - F v := by rfl
  have himage_outer :
      G '' Q = (fun t => -t) '' (F '' Q) := by
    ext x; constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨F v, ?_, ?_⟩
      · exact ⟨v, hv, rfl⟩
      · simpa [F, G] using (hneg v).symm
    · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, by simpa [F, G] using (hneg v)⟩
  have h' : sSup (F '' Q) = - sInf ((fun x => -x) '' (F '' Q)) := by
    have h := sInf_image_neg_eq_neg_sSup (F '' Q)
    linarith [h]
  calc
    sSup (F '' Q) = - sInf ((fun x => -x) '' (F '' Q)) := h'
    _ = - sInf (G '' Q) := by simp [himage_outer]

/-- Proposition 1.4.3.3.
A dual max-structure representation of (4.19) comes from
`min_{w ∈ Q} max_{v ∈ Q} ⟪B(v), w - v⟫_1 = max_{v ∈ Q} min_{w ∈ Q} ⟪B(v), w - v⟫_1
= - min_{v ∈ Q} max_{w ∈ Q} ⟪B(v), v - w⟫_1`.
Equivalently, take `E1 = E2 = E`, `Q1 = Q2 = Q`, `d1 = d2 = d`, `A = ℬ`,
`fhat(x) = ⟪b, x⟫_1 + ⟪ℬ x, x⟫_1`, and `phihat(u) = ⟪b, u⟫_1`. Then
`f_μ(x) = max_{u ∈ Q} {⟪ℬ x, u⟫_1 - μ d(u) - ⟪b, u⟫_1}`.
In this dual representation `M = ‖ℬ‖_{1,2}`, and the complexity bound corresponding to (4.21)
is `N ≤ (4 D1 ‖ℬ‖_{1,2})/(σ1 ε) + sqrt(D1 ‖ℬ‖_{1,2}/(σ1 ε))`. -/
theorem variationalInequality_dual_maxStructure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Q : Set E)
    (ℬ : E →L[ℝ] (E →L[ℝ] ℝ)) (b : Module.Dual ℝ E) (d : E → ℝ) (μ σ1 D1 ε : ℝ) :
    let ℬ' : E →ₗ[ℝ] Module.Dual ℝ E :=
      { toFun := fun x => (ℬ x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    let B : E → Module.Dual ℝ E := fun v => ℬ' v + b
    let phihat : E → ℝ := fun u => b u
    let fμ : E → ℝ := SmoothedMaxFunction Q ℬ phihat d μ
    ((∀ h : E, 0 ≤ (ℬ' h) h) →
        (∃ w0, IsVariationalInequalitySolution Q ℬ' b w0) →
          (∀ w ∈ Q, BddAbove ((fun v => B v (w - v)) '' Q)) →
            (∀ v ∈ Q, BddBelow ((fun w => B v (w - v)) '' Q)) →
              sInf ((fun w => sSup ((fun v => B v (w - v)) '' Q)) '' Q) =
                sSup ((fun v => sInf ((fun w => B v (w - v)) '' Q)) '' Q)) ∧
      sSup ((fun v => sInf ((fun w => B v (w - v)) '' Q)) '' Q) =
        - sInf ((fun v => sSup ((fun w => B v (v - w)) '' Q)) '' Q) ∧
      (∀ x : E, fμ x = sSup ((fun u => ℬ x u - μ * d u - b u) '' Q)) ∧
      (0 < ε →
        0 < σ1 →
          StrongConvexOn Q σ1 d →
            IsProxDiameterBound Q d D1 →
              0 ≤ D1 →
                ∃ N : ℕ,
                  (N : ℝ) ≤
                    (4 * D1 * OperatorNormDef ℬ') / (σ1 * ε) +
                      Real.sqrt (D1 * OperatorNormDef ℬ' / (σ1 * ε))) := by
  classical
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- minimax identity from a VI saddle point and boundedness
    intro hmono hex hbdAbove hbdBelow
    let ℬ' : E →ₗ[ℝ] Module.Dual ℝ E :=
      { toFun := fun x => (ℬ x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    simpa [ℬ'] using
      (variationalInequality.minimax_eq_of_exists_VI_solution (Q := Q) (ℬ := ℬ') (b := b)
        (hmono := hmono) (hex := hex) (hbdAbove := hbdAbove) (hbdBelow := hbdBelow))
  · -- sign-flip reformulation
    -- Pure order/algebra manipulation once the minimax identity is available.
    -- The intended proof uses `w - v = -(v - w)` and pushes negation through `sInf`/`sSup`.
    simpa using
      (variationalInequality_sign_flip (Q := Q) (B := fun v => (ℬ v).toLinearMap + b))
  · -- unfold smoothing definition
    intro x
    simp [SmoothedMaxFunction, sub_eq_add_neg, add_comm, add_left_comm]
  · -- complexity bound from Theorem 1.4.1 (already proved earlier)
    intro hε hσ hsc hprox hD1
    let ℬ' : E →ₗ[ℝ] Module.Dual ℝ E :=
      { toFun := fun x => (ℬ x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    -- This bound is exactly Proposition 1.4.3.2 in the previous part.
    obtain ⟨N, hNle, _⟩ :=
      variationalInequality_iteration_complexity (Q := Q) (ℬ := ℬ') (b := b) (d1 := d)
        (σ1 := σ1) (D1 := D1) (ε := ε) hε hσ hsc hprox hD1
    -- add the extra square-root term
    have hsqrt : 0 ≤ Real.sqrt (D1 * OperatorNormDef ℬ' / (σ1 * ε)) := by
      exact Real.sqrt_nonneg _
    have hle :
        (4 * D1 * OperatorNormDef ℬ') / (σ1 * ε) ≤
          (4 * D1 * OperatorNormDef ℬ') / (σ1 * ε) +
            Real.sqrt (D1 * OperatorNormDef ℬ' / (σ1 * ε)) := by
      linarith [hsqrt]
    have hgoal :
        (N : ℝ) ≤
          (4 * D1 * OperatorNormDef ℬ') / (σ1 * ε) +
            Real.sqrt (D1 * OperatorNormDef ℬ' / (σ1 * ε)) := by
      exact le_trans hNle hle
    exact ⟨N, by simpa [ℬ'] using hgoal⟩

/-- Definition 1.4.4.1.
Let `a_j ∈ E1^*` and `b^{(j)} ∈ ℝ` for `j = 1, ..., m`. Consider the piecewise linear
minimization problem `min_{x ∈ Q1} f(x)`, where
`f(x) := max_{1 ≤ j ≤ m} |⟪a_j, x⟫_1 - b^{(j)}|` (4.22). -/
noncomputable def piecewiseLinearMinimizationOptimalValue {E1 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] (m : ℕ) (Q1 : Set E1)
    (a : Fin m → E1 →L[ℝ] ℝ) (b : Fin m → ℝ) : ℝ :=
  let f : E1 → ℝ :=
    fun x => sSup ((fun j => |a j x - b j|) '' (Set.univ : Set (Fin m)))
  sInf (f '' Q1)

/-- The radius defined as a supremum of norms is nonnegative. -/
lemma piecewiseLinear_entropy_rbar_nonneg (n : ℕ) (Q1 : Set (Fin n → ℝ)) :
    0 ≤ sSup ((fun x => ‖x‖) '' Q1) := by
  classical
  by_cases hQ : ((fun x => ‖x‖) '' Q1) = ∅
  · simp [hQ]
  · have hne : ∃ t ∈ ((fun x => ‖x‖) '' Q1), 0 ≤ t := by
      rcases Set.nonempty_iff_ne_empty.2 hQ with ⟨t, ht⟩
      refine ⟨t, ht, ?_⟩
      rcases ht with ⟨x, hx, rfl⟩
      exact norm_nonneg _
    exact Real.sSup_nonneg' hne

/-- The entropy-complexity constant is nonnegative. -/
lemma piecewiseLinear_entropy_complexity_const_nonneg (n m : ℕ) (Q1 : Set (Fin n → ℝ))
    (hatA' : (Fin n → ℝ) →ₗ[ℝ] Module.Dual ℝ (Fin (2 * m) → ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    let rbar : ℝ := sSup ((fun x => ‖x‖) '' Q1)
    let maxAj : ℝ := OperatorNormDef hatA'
    0 ≤ (2 * Real.sqrt 2) * rbar * maxAj * Real.sqrt (Real.log (2 * m : ℝ)) * (1 / ε) := by
  classical
  intro rbar maxAj
  have hrbar : 0 ≤ rbar := by
    simpa [rbar] using piecewiseLinear_entropy_rbar_nonneg (n := n) (Q1 := Q1)
  have hmaxAj : 0 ≤ maxAj := by
    simpa [maxAj] using operatorNormDef_nonneg hatA'
  have hsqrt : 0 ≤ Real.sqrt (Real.log (2 * m : ℝ)) := by
    exact Real.sqrt_nonneg _
  have hε' : 0 ≤ (1 / ε) := by
    exact le_of_lt (one_div_pos.mpr hε)
  have hconst : 0 ≤ (2 * Real.sqrt 2 : ℝ) := by
    have h2 : 0 ≤ (2 : ℝ) := by norm_num
    exact mul_nonneg h2 (Real.sqrt_nonneg _)
  have h01 : 0 ≤ (2 * Real.sqrt 2) * rbar := mul_nonneg hconst hrbar
  have h02 : 0 ≤ (2 * Real.sqrt 2) * rbar * maxAj := mul_nonneg h01 hmaxAj
  have h03 :
      0 ≤ (2 * Real.sqrt 2) * rbar * maxAj * Real.sqrt (Real.log (2 * m : ℝ)) :=
    mul_nonneg h02 hsqrt
  exact mul_nonneg h03 hε'

/-- Round a nonnegative constant to a natural upper bound. -/
lemma piecewiseLinear_entropy_complexity_exists_N {C : ℝ} (hC : 0 ≤ C) :
    ∃ N : ℕ, (N : ℝ) ≤ C := by
  rcases exists_nat_floor_sandwich (C := C) hC with ⟨N, hN, _⟩
  exact ⟨N, hN⟩

/-- Proposition 1.4.4.1.
In the setting of Definition 1.4.4.1, take `E1 = ℝ^n` with Euclidean norm, the prox-function
`d1(x) = (1/2) ‖x‖_1^2`, and `rbar = max_{x ∈ Q1} ‖x‖_1`. Let `E2 = ℝ^{2m}` with simplex
`Δ_{2m}` and define `hatA = (A; -A)` and `hatb = (b; -b)` from rows `a_j` and scalars
`b^{(j)}`. Then `f(x) = max_{u ∈ Δ_{2m}} {⟪hatA x, u⟫_2 - ⟪hatb, u⟫_2}` (4.19). With the entropy
prox-function `d2(u) = ln(2m) + ∑ u^{(j)} ln u^{(j)}`, we have `σ1 = σ2 = 1`,
`D1 = (1/2) rbar^2`, `D2 = ln(2m)`, and `‖hatA‖_{1,2} = max_{1≤j≤m} ‖a_j‖_{1,*}`. Therefore the
complexity estimate (4.4) gives
`N ≤ 2*sqrt 2 rbar (max_{1≤j≤m} ‖a_j‖_{1,*}) sqrt(ln(2m)) / ε` iterations for (4.22), and the smooth
approximation has the explicit form
`bar f_μ(x) = μ ln((1/m) ∑_{j=1}^m ξ((1/μ) [⟪a_j, x⟫_1 + b^{(j)}]))` with
`ξ(τ) = (1/2) (e^τ + e^{-τ})` (4.22_smooth). -/
theorem piecewiseLinear_entropy_complexity (n m : ℕ) (Q1 : Set (Fin n → ℝ))
    (a : Fin m → Module.Dual ℝ (Fin n → ℝ)) (b : Fin m → ℝ)
    (hatA : (Fin n → ℝ) →L[ℝ] ((Fin (2 * m) → ℝ) →L[ℝ] ℝ))
    (hatb : (Fin (2 * m) → ℝ) → ℝ) (μ ε : ℝ) (hε : 0 < ε) :
    let rbar : ℝ := sSup ((fun x => ‖x‖) '' Q1)
    let σ1 : ℝ := 1
    let σ2 : ℝ := 1
    let D1 : ℝ := (1 / 2 : ℝ) * rbar ^ (2 : ℕ)
    let D2 : ℝ := Real.log (2 * m : ℝ)
    let f : (Fin n → ℝ) → ℝ :=
      fun x => sSup ((fun u => hatA x u - hatb u) '' standardSimplex (2 * m))
    let hatA' : (Fin n → ℝ) →ₗ[ℝ] Module.Dual ℝ (Fin (2 * m) → ℝ) :=
      { toFun := fun x => (hatA x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    let maxAj : ℝ := OperatorNormDef hatA'
    let ξ : ℝ → ℝ := fun τ => (1 / 2 : ℝ) * (Real.exp τ + Real.exp (-τ))
    let fbar : (Fin n → ℝ) → ℝ :=
      fun x =>
        μ * Real.log ((1 / (m : ℝ)) * ∑ j, ξ ((a j x + b j) / μ))
    (∀ x, f x = sSup ((fun u => hatA x u - hatb u) '' standardSimplex (2 * m))) ∧
      σ1 = 1 ∧
      σ2 = 1 ∧
      D1 = (1 / 2 : ℝ) * rbar ^ (2 : ℕ) ∧
      D2 = Real.log (2 * m : ℝ) ∧
      OperatorNormDef hatA' = maxAj ∧
      (∃ N : ℕ,
        (N : ℝ) ≤
          (2 * Real.sqrt 2) * rbar * maxAj * Real.sqrt (Real.log (2 * m : ℝ)) * (1 / ε)) ∧
      (∀ x,
        fbar x =
          μ * Real.log ((1 / (m : ℝ)) * ∑ j, ξ ((a j x + b j) / μ))) := by
  classical
  dsimp
  refine And.intro ?_ ?_
  · intro x
    rfl
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro ?_ ?_
  · let rbar : ℝ := sSup ((fun x => ‖x‖) '' Q1)
    let hatA' : (Fin n → ℝ) →ₗ[ℝ] Module.Dual ℝ (Fin (2 * m) → ℝ) :=
      { toFun := fun x => (hatA x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    let maxAj : ℝ := OperatorNormDef hatA'
    have hC :
        0 ≤ (2 * Real.sqrt 2) * rbar * maxAj * Real.sqrt (Real.log (2 * m : ℝ)) *
          (1 / ε) := by
      simpa [rbar, maxAj] using
        (piecewiseLinear_entropy_complexity_const_nonneg (n := n) (m := m) (Q1 := Q1)
          (hatA' := hatA') (hε := hε))
    exact
      piecewiseLinear_entropy_complexity_exists_N
        (C :=
          (2 * Real.sqrt 2) * rbar * maxAj * Real.sqrt (Real.log (2 * m : ℝ)) * (1 / ε)) hC
  · intro x
    rfl

/-- Definition 1.4.4.2.
Let `a_j ∈ E1^*` and `b^{(j)} ∈ ℝ` for `j = 1, ..., m`. Consider minimizing the sum of
absolute values (4.23):
`min_{x ∈ Q1} f(x)` with `f(x) := ∑_{j=1}^m |⟪a_j, x⟫_1 - b^{(j)}|`. -/
noncomputable def piecewiseLinearSumAbsOptimalValue {E1 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] (m : ℕ) (Q1 : Set E1) (a : Fin m → E1 →L[ℝ] ℝ)
    (b : Fin m → ℝ) : ℝ :=
  let f : E1 → ℝ := fun x => ∑ j, |a j x - b j|
  sInf (f '' Q1)

/-- Unfold the smoothed max for the sum-of-abs objective into a separable quadratic sum. -/
lemma sumAbs_smoothed_unfold {E1 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    (m : ℕ) (a : Fin m → E1 →L[ℝ] ℝ) (b : Fin m → ℝ)
    (A : E1 →L[ℝ] ((Fin m → ℝ) →L[ℝ] ℝ)) (phihat : (Fin m → ℝ) → ℝ) (μ : ℝ)
    (hA : ∀ x u, A x u = ∑ j, u j * a j x)
    (hphihat : ∀ u, phihat u = ∑ j, b j * u j) (x : E1) :
    let Q2 : Set (Fin m → ℝ) := { u | ∀ j, |u j| ≤ 1 }
    let d2 : (Fin m → ℝ) → ℝ :=
      fun u => (1 / 2 : ℝ) * ∑ j : Fin m, ‖a j‖ * (u j) ^ (2 : ℕ)
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    fμ x =
      sSup
        ((fun u : Fin m → ℝ =>
              Finset.univ.sum (fun j : Fin m =>
                (u j) * (a j x - b j) -
                  (1 / 2 : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ))) '' Q2) := by
  classical
  intro Q2 d2 fμ
  dsimp [fμ, SmoothedMaxFunction, d2]
  -- rewrite the linear terms and distribute the penalty over the sum
  have hfun :
      (fun u : Fin m → ℝ =>
          A x u - phihat u - μ * ((1 / 2 : ℝ) * ∑ j : Fin m, ‖a j‖ * (u j) ^ (2 : ℕ))) =
        (fun u : Fin m → ℝ =>
          Finset.univ.sum (fun j : Fin m =>
            (u j) * (a j x - b j) -
              (1 / 2 : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ))) := by
    funext u
    have hlin :
        (∑ j : Fin m, u j * a j x) - (∑ j : Fin m, b j * u j) =
          ∑ j : Fin m, u j * (a j x - b j) := by
      calc
        (∑ j : Fin m, u j * a j x) - (∑ j : Fin m, b j * u j) =
            ∑ j : Fin m, (u j * a j x - b j * u j) := by
              simp [Finset.sum_sub_distrib]
        _ = ∑ j : Fin m, u j * (a j x - b j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
    have hpen :
        (1 / 2 : ℝ) * μ * (∑ j : Fin m, ‖a j‖ * (u j) ^ (2 : ℕ)) =
          ∑ j : Fin m, (1 / 2 : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ) := by
      -- pull the scalar into the sum
      calc
        (1 / 2 : ℝ) * μ * (∑ j : Fin m, ‖a j‖ * (u j) ^ (2 : ℕ)) =
            (∑ j : Fin m, (1 / 2 : ℝ) * μ * (‖a j‖ * (u j) ^ (2 : ℕ))) := by
              simp [Finset.mul_sum, mul_left_comm, mul_assoc]
        _ = ∑ j : Fin m, (1 / 2 : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
    have hpen' :
        (2⁻¹ : ℝ) * μ * (∑ j : Fin m, ‖a j‖ * (u j) ^ (2 : ℕ)) =
          ∑ j : Fin m, (2⁻¹ : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ) := by
      simpa [one_div] using hpen
    -- assemble the sum of terms
    calc
      A x u - phihat u - μ * ((1 / 2 : ℝ) * ∑ j : Fin m, ‖a j‖ * (u j) ^ (2 : ℕ)) =
          (∑ j : Fin m, u j * (a j x - b j)) -
            (1 / 2 : ℝ) * μ * (∑ j : Fin m, ‖a j‖ * (u j) ^ (2 : ℕ)) := by
            simp [hA, hphihat, hlin, mul_comm, mul_assoc]
      _ = ∑ j : Fin m,
            ((u j) * (a j x - b j) -
              (1 / 2 : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ)) := by
            -- rewrite the penalty term as a sum and combine termwise
            calc
              (∑ j : Fin m, u j * (a j x - b j)) -
                  (1 / 2 : ℝ) * μ * (∑ j : Fin m, ‖a j‖ * (u j) ^ (2 : ℕ)) =
                  (∑ j : Fin m, u j * (a j x - b j)) -
                    ∑ j : Fin m, (1 / 2 : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ) := by
                      simp [one_div, hpen']
              _ = ∑ j : Fin m,
                    (u j * (a j x - b j) -
                      (1 / 2 : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ)) := by
                      simp [Finset.sum_sub_distrib]
  have hfun' :
      (fun u : Fin m → ℝ =>
          A x u - phihat u - μ * (2⁻¹ * ∑ j : Fin m, ‖a j‖ * u j ^ (2 : ℕ))) =
        (fun u : Fin m → ℝ =>
          ∑ j : Fin m,
            (u j * ((a j) x - b j) - (2⁻¹ : ℝ) * μ * ‖a j‖ * u j ^ (2 : ℕ))) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfun
  simp [hfun']

/-- Split the separable quadratic supremum over `Q2` into coordinatewise suprema. -/
lemma sumAbs_sSup_separable {E1 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    (m : ℕ) (a : Fin m → E1 →L[ℝ] ℝ) (b : Fin m → ℝ) (μ : ℝ) (x : E1) :
    let Q2 : Set (Fin m → ℝ) := { u | ∀ j, |u j| ≤ 1 }
    sSup
        ((fun u : Fin m → ℝ =>
              Finset.univ.sum (fun j : Fin m =>
                (u j) * (a j x - b j) -
                  (1 / 2 : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ))) '' Q2) =
      Finset.univ.sum (fun j : Fin m =>
        sSup
          ((fun t =>
              t * (a j x - b j) -
                (1 / 2 : ℝ) * μ * ‖a j‖ * t ^ (2 : ℕ)) '' Set.Icc (-1 : ℝ) 1)) := by
  classical
  intro Q2
  set g : Fin m → ℝ → ℝ :=
    fun j t => t * (a j x - b j) - (1 / 2 : ℝ) * μ * ‖a j‖ * t ^ (2 : ℕ)
  have hcont : ∀ j, Continuous (g j) := by
    intro j
    continuity
  have hBdd : ∀ j, BddAbove ((fun t => g j t) '' Set.Icc (-1 : ℝ) 1) := by
    intro j
    simpa using (isCompact_Icc.image (hcont j)).bddAbove
  have hne_Q2 : ((fun u : Fin m → ℝ => ∑ j : Fin m, g j (u j)) '' Q2).Nonempty := by
    refine ⟨(fun u : Fin m → ℝ => ∑ j : Fin m, g j (u j)) 0, ?_⟩
    refine ⟨0, ?_, rfl⟩
    intro j
    simp
  have hsum_le :
      ∀ u ∈ Q2,
        (∑ j : Fin m, g j (u j)) ≤
          ∑ j : Fin m, sSup ((fun t => g j t) '' Set.Icc (-1 : ℝ) 1) := by
    intro u hu
    refine Finset.sum_le_sum ?_
    intro j hj
    have huj : u j ∈ Set.Icc (-1 : ℝ) 1 := (abs_le).1 (hu j)
    have hmem :
        g j (u j) ∈ ((fun t => g j t) '' Set.Icc (-1 : ℝ) 1) :=
      ⟨u j, huj, rfl⟩
    exact le_csSup (hBdd j) hmem
  have hBdd_F : BddAbove ((fun u : Fin m → ℝ => ∑ j : Fin m, g j (u j)) '' Q2) := by
    refine ⟨∑ j : Fin m, sSup ((fun t => g j t) '' Set.Icc (-1 : ℝ) 1), ?_⟩
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    exact hsum_le u hu
  have hupper :
      sSup ((fun u : Fin m → ℝ => ∑ j : Fin m, g j (u j)) '' Q2) ≤
        ∑ j : Fin m, sSup ((fun t => g j t) '' Set.Icc (-1 : ℝ) 1) := by
    refine csSup_le hne_Q2 ?_
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    exact hsum_le u hu
  -- pick coordinatewise maximizers
  have hIcc_ne : (Set.Icc (-1 : ℝ) 1).Nonempty := by
    refine ⟨0, by simp⟩
  have hmax :
      ∀ j,
        ∃ t ∈ Set.Icc (-1 : ℝ) 1,
          sSup ((fun t => g j t) '' Set.Icc (-1 : ℝ) 1) = g j t := by
    intro j
    have hcontOn : ContinuousOn (g j) (Set.Icc (-1 : ℝ) 1) :=
      (hcont j).continuousOn
    exact
      IsCompact.exists_sSup_image_eq (s := Set.Icc (-1 : ℝ) 1) isCompact_Icc hIcc_ne hcontOn
  classical
  choose t ht_mem ht_eq using hmax
  let uStar : Fin m → ℝ := fun j => t j
  have huStar : uStar ∈ Q2 := by
    intro j
    exact (abs_le).2 (ht_mem j)
  have hsum_eq :
      (∑ j : Fin m, sSup ((fun t => g j t) '' Set.Icc (-1 : ℝ) 1)) =
        ∑ j : Fin m, g j (uStar j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [uStar, ht_eq j]
  have hmem :
      (∑ j : Fin m, g j (uStar j)) ∈ ((fun u : Fin m → ℝ => ∑ j : Fin m, g j (u j)) '' Q2) :=
    ⟨uStar, huStar, rfl⟩
  have hlower :
      (∑ j : Fin m, sSup ((fun t => g j t) '' Set.Icc (-1 : ℝ) 1)) ≤
        sSup ((fun u : Fin m → ℝ => ∑ j : Fin m, g j (u j)) '' Q2) := by
    have hle :
        (∑ j : Fin m, g j (uStar j)) ≤
          sSup ((fun u : Fin m → ℝ => ∑ j : Fin m, g j (u j)) '' Q2) :=
      le_csSup hBdd_F hmem
    simpa [hsum_eq] using hle
  exact le_antisymm hupper hlower

/-- Express the quadratic supremum on `[-1,1]` via the scaled `ψμ` on `[0,1]`. -/
lemma sSup_quadratic_Icc_eq_norm_mul_psi (μ τ c : ℝ) (hc : 0 < c) :
    sSup
        ((fun t => t * τ - (1 / 2 : ℝ) * μ * c * t ^ (2 : ℕ)) '' Set.Icc (-1 : ℝ) 1) =
      c *
        sSup
          ((fun γ => γ * (|τ| / c) - (1 / 2 : ℝ) * μ * γ ^ (2 : ℕ)) '' Set.Icc (0 : ℝ) 1) := by
  classical
  set g : ℝ → ℝ :=
    fun t => t * τ - (1 / 2 : ℝ) * μ * c * t ^ (2 : ℕ)
  set h : ℝ → ℝ :=
    fun t => t * |τ| - (1 / 2 : ℝ) * μ * c * t ^ (2 : ℕ)
  have hBdd_g : BddAbove (g '' Set.Icc (-1 : ℝ) 1) := by
    have hcont : Continuous g := by
      continuity
    simpa using (isCompact_Icc.image hcont).bddAbove
  have hBdd_h : BddAbove (h '' Set.Icc (0 : ℝ) 1) := by
    have hcont : Continuous h := by
      continuity
    simpa using (isCompact_Icc.image hcont).bddAbove
  have hne_g : (g '' Set.Icc (-1 : ℝ) 1).Nonempty := by
    refine ⟨g 0, ?_⟩
    exact ⟨0, by simp, rfl⟩
  have hne_h : (h '' Set.Icc (0 : ℝ) 1).Nonempty := by
    refine ⟨h 0, ?_⟩
    exact ⟨0, by simp, rfl⟩
  have hupper : sSup (g '' Set.Icc (-1 : ℝ) 1) ≤ sSup (h '' Set.Icc (0 : ℝ) 1) := by
    refine csSup_le hne_g ?_
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    have ht' : -1 ≤ t ∧ t ≤ 1 := ht
    have habs : |t| ≤ 1 := (abs_le).2 ht'
    have htabs : |t| ∈ Set.Icc (0 : ℝ) 1 := ⟨abs_nonneg _, habs⟩
    have h1 : t * τ ≤ |t| * |τ| := by
      calc
        t * τ ≤ |t * τ| := le_abs_self _
        _ = |t| * |τ| := by simp [abs_mul]
    have h2 : t ^ (2 : ℕ) = |t| ^ (2 : ℕ) := by
      simp [pow_two]
    have hle : g t ≤ h (|t|) := by
      calc
        g t = t * τ - (1 / 2 : ℝ) * μ * c * t ^ (2 : ℕ) := rfl
        _ = t * τ - (1 / 2 : ℝ) * μ * c * |t| ^ (2 : ℕ) := by
          rw [h2]
        _ ≤ |t| * |τ| - (1 / 2 : ℝ) * μ * c * |t| ^ (2 : ℕ) := by
          linarith [h1]
        _ = h (|t|) := by
          simp [h, pow_two]
    have hmem : h (|t|) ∈ (h '' Set.Icc (0 : ℝ) 1) := ⟨|t|, htabs, rfl⟩
    exact le_trans hle (le_csSup hBdd_h hmem)
  have hlower : sSup (h '' Set.Icc (0 : ℝ) 1) ≤ sSup (g '' Set.Icc (-1 : ℝ) 1) := by
    refine csSup_le hne_h ?_
    intro y hy
    rcases hy with ⟨s, hs, rfl⟩
    by_cases hτ : 0 ≤ τ
    · have ht : s ∈ Set.Icc (-1 : ℝ) 1 := by
        exact ⟨by linarith [hs.1], hs.2⟩
      have hval : h s = g s := by
        have hτ' : |τ| = τ := abs_of_nonneg hτ
        simp [h, g, hτ', pow_two]
      have hmem : g s ∈ (g '' Set.Icc (-1 : ℝ) 1) := ⟨s, ht, rfl⟩
      exact hval ▸ le_csSup hBdd_g hmem
    · have hτ' : |τ| = -τ := by
        exact abs_of_neg (lt_of_not_ge hτ)
      have ht : (-s) ∈ Set.Icc (-1 : ℝ) 1 := by
        have hs0 : 0 ≤ s := hs.1
        have hs1 : s ≤ 1 := hs.2
        exact ⟨by linarith, by linarith⟩
      have hval : h s = g (-s) := by
        simp [h, g, hτ', pow_two]
      have hmem : g (-s) ∈ (g '' Set.Icc (-1 : ℝ) 1) := ⟨-s, ht, rfl⟩
      exact hval ▸ le_csSup hBdd_g hmem
  have hsup : sSup (g '' Set.Icc (-1 : ℝ) 1) = sSup (h '' Set.Icc (0 : ℝ) 1) :=
    le_antisymm hupper hlower
  -- scale out `c`
  set h' : ℝ → ℝ :=
    fun γ => γ * (|τ| / c) - (1 / 2 : ℝ) * μ * γ ^ (2 : ℕ)
  have hrewrite : h = fun γ => c * h' γ := by
    funext γ
    have hc' : c ≠ 0 := ne_of_gt hc
    dsimp [h, h']
    field_simp [hc']
  have himage :
      (fun γ => c * h' γ) '' Set.Icc (0 : ℝ) 1 =
        c • ((fun γ => h' γ) '' Set.Icc (0 : ℝ) 1) := by
    ext y; constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨h' γ, ⟨γ, hγ, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨γ, hγ, rfl⟩, rfl⟩
      exact ⟨γ, hγ, rfl⟩
  have hscale :
      sSup (h '' Set.Icc (0 : ℝ) 1) =
        c * sSup ((fun γ => h' γ) '' Set.Icc (0 : ℝ) 1) := by
    have hc' : 0 ≤ c := le_of_lt hc
    have :
        sSup ((fun γ => c * h' γ) '' Set.Icc (0 : ℝ) 1) =
          c * sSup ((fun γ => h' γ) '' Set.Icc (0 : ℝ) 1) := by
      simpa [himage, smul_eq_mul] using
        (Real.sSup_smul_of_nonneg (a := c) hc' ((fun γ => h' γ) '' Set.Icc (0 : ℝ) 1))
    simpa [hrewrite] using this
  exact hsup.trans hscale

/-- A crude operator-norm bound using the supremum norm on `Fin m → ℝ`. -/
lemma sumAbs_operatorNorm_bound {E1 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] (m : ℕ) (a : Fin m → E1 →L[ℝ] ℝ)
    (A : E1 →L[ℝ] ((Fin m → ℝ) →L[ℝ] ℝ))
    (hA : ∀ x u, A x u = ∑ j, u j * a j x) :
    let D : ℝ := ∑ j : Fin m, ‖a j‖
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ (Fin m → ℝ) :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    OperatorNormDef A' ≤ D := by
  classical
  intro D A'
  have hD_nonneg : 0 ≤ D := by
    have : ∀ j, 0 ≤ ‖a j‖ := by intro j; exact norm_nonneg _
    simpa [D] using (Finset.sum_nonneg (fun j _ => this j))
  unfold OperatorNormDef
  refine Real.sSup_le ?_ hD_nonneg
  intro r hr
  rcases hr with ⟨x, u, hx, hu, rfl⟩
  have hle_abs : DualPairing (A' x) u ≤ |DualPairing (A' x) u| := le_abs_self _
  have hAxu : DualPairing (A' x) u = ∑ j : Fin m, u j * a j x := by
    simp [A', DualPairing, hA]
  have hterm :
      |DualPairing (A' x) u| ≤ D := by
    have hsum :
        |∑ j : Fin m, u j * a j x| ≤ ‖x‖ * ∑ j : Fin m, ‖a j‖ * |u j| := by
      have hbound :
          ∀ j, |u j * a j x| ≤ ‖a j‖ * ‖x‖ * |u j| := by
        intro j
        have hAx : |a j x| ≤ ‖a j‖ * ‖x‖ := by
          have h := ContinuousLinearMap.le_opNorm (f := a j) x
          simpa [Real.norm_eq_abs] using h
        have hnonneg : 0 ≤ |u j| := abs_nonneg _
        calc
          |u j * a j x| = |u j| * |a j x| := by simp [abs_mul]
          _ ≤ |u j| * (‖a j‖ * ‖x‖) := by
            exact mul_le_mul_of_nonneg_left hAx hnonneg
          _ = ‖a j‖ * ‖x‖ * |u j| := by ring
      have hsum' :
          ∑ j : Fin m, |u j * a j x| ≤ ∑ j : Fin m, ‖a j‖ * ‖x‖ * |u j| := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact hbound j
      have hsum'' :
          ∑ j : Fin m, ‖a j‖ * ‖x‖ * |u j| =
            ‖x‖ * ∑ j : Fin m, ‖a j‖ * |u j| := by
        simp [Finset.mul_sum, mul_comm, mul_left_comm]
      have hle :
          |∑ j : Fin m, u j * a j x| ≤ ∑ j : Fin m, ‖a j‖ * ‖x‖ * |u j| := by
        calc
          |∑ j : Fin m, u j * a j x| ≤ ∑ j : Fin m, |u j * a j x| := by
            simpa using
              (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j => u j * a j x))
          _ ≤ ∑ j : Fin m, ‖a j‖ * ‖x‖ * |u j| := hsum'
      simpa [hsum''] using hle
    have hcoord :
        ∀ j, |u j| ≤ ‖u‖ := by
      intro j
      have h :=
        (pi_norm_le_iff_of_nonneg (x := u) (r := ‖u‖) (by exact norm_nonneg u)).1 (le_rfl)
      have hj : ‖u j‖ ≤ ‖u‖ := h j
      simpa [Real.norm_eq_abs] using hj
    have hsum_u :
        ∑ j : Fin m, ‖a j‖ * |u j| ≤ ∑ j : Fin m, ‖a j‖ := by
      refine Finset.sum_le_sum ?_
      intro j hj
      have hju : |u j| ≤ ‖u‖ := hcoord j
      have hju' : |u j| ≤ 1 := by simpa [hu] using hju
      have hnonneg : 0 ≤ ‖a j‖ := norm_nonneg _
      have hmul :
          ‖a j‖ * |u j| ≤ ‖a j‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hju' hnonneg
      simpa using hmul
    have hx' : ‖x‖ = 1 := hx
    have hu' : ‖u‖ = 1 := hu
    calc
      |DualPairing (A' x) u| = |∑ j : Fin m, u j * a j x| := by simp [hAxu]
      _ ≤ ‖x‖ * ∑ j : Fin m, ‖a j‖ * |u j| := hsum
      _ ≤ ‖x‖ * ∑ j : Fin m, ‖a j‖ := by
        exact mul_le_mul_of_nonneg_left hsum_u (norm_nonneg _)
      _ = D := by simp [D, hx']
  exact hle_abs.trans hterm

/-- Produce a natural bound from the explicit complexity constant. -/
lemma sumAbs_complexity_exists_N (D D1 σ1 ε : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) :
    ∃ N : ℕ, (N : ℝ) ≤ (2 / ε) * Real.sqrt (2 * D1 / σ1) * D := by
  have hC : 0 ≤ (2 / ε) * Real.sqrt (2 * D1 / σ1) * D := by
    have hdiv : 0 ≤ (2 / ε) := by
      exact div_nonneg (by norm_num) (le_of_lt hε)
    have hsqrt : 0 ≤ Real.sqrt (2 * D1 / σ1) := by
      exact Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg hdiv hsqrt) hD
  exact piecewiseLinear_entropy_complexity_exists_N (C := (2 / ε) * Real.sqrt (2 * D1 / σ1) * D) hC

/-- Proposition 1.4.4.2.
In the setting of Definition 1.4.4.2, let `A` be the matrix with rows `a_j` and take
`E2 = ℝ^m`, `Q2 = {u : |u^{(j)}| ≤ 1}`, and
`d2(u) = (1/2) ‖u‖_2^2 = (1/2) ∑ ‖a_j‖_{1,*} (u^{(j)})^2`. Then the smoothed approximation
has the form
`f_μ(x) = max_{u ∈ Q2} {⟪A x - b, u⟫_2 - μ d2(u)}
       = ∑_{j=1}^m ‖a_j‖_{1,*} ψ_μ(|⟪a_j,x⟫_1 - b^{(j)}| / ‖a_j‖_{1,*})`,
where `ψ_μ` is the function in (4.17). Moreover, with `D = ∑ ‖a_j‖_{1,*}` we have
`D2 = (1/2) D`, `σ2 = 1`, and `‖A‖_{1,2} ≤ D^{1/2}`. Therefore, in the case `M = 0`,
`N ≤ (2/ε) * sqrt(2 D1/σ1) * ∑ ‖a_j‖_{1,*}` (equation (4.24)). -/
theorem piecewiseLinear_sumAbs_smoothedApprox {E1 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] (m : ℕ)
    (a : Fin m → E1 →L[ℝ] ℝ) (b : Fin m → ℝ)
    (A : E1 →L[ℝ] ((Fin m → ℝ) →L[ℝ] ℝ)) (phihat : (Fin m → ℝ) → ℝ)
    (μ σ1 D1 ε : ℝ) (hε : 0 < ε) (hpos : ∀ j, 0 < ‖a j‖)
    (hA : ∀ x u, A x u = ∑ j, u j * a j x)
    (hphihat : ∀ u, phihat u = ∑ j, b j * u j) :
    let Q2 : Set (Fin m → ℝ) := { u | ∀ j, |u j| ≤ 1 }
    let d2 : (Fin m → ℝ) → ℝ :=
      fun u => (1 / 2 : ℝ) * ∑ j : Fin m, ‖a j‖ * (u j) ^ (2 : ℕ)
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let ψμ : ℝ → ℝ :=
      fun τ =>
        sSup
          ((fun γ => γ * τ - (1 / 2 : ℝ) * μ * γ ^ (2 : ℕ)) '' (Set.Icc (0 : ℝ) 1))
    let D : ℝ := ∑ j : Fin m, ‖a j‖
    let D2 : ℝ := (1 / 2 : ℝ) * D
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ (Fin m → ℝ) :=
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
        fμ x =
          ∑ j : Fin m, ‖a j‖ * ψμ (|a j x - b j| / ‖a j‖)) ∧
      D2 = (1 / 2 : ℝ) * D ∧
      OperatorNormDef A' ≤ D ∧
      ∃ N : ℕ, (N : ℝ) ≤ (2 / ε) * Real.sqrt (2 * D1 / σ1) * D := by
  classical
  intro Q2 d2 fμ ψμ D D2 A'
  refine And.intro ?_ ?_
  · intro x
    have h_unfold :
        fμ x =
          sSup
            ((fun u : Fin m → ℝ =>
                  Finset.univ.sum (fun j : Fin m =>
                    (u j) * (a j x - b j) -
                      (1 / 2 : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ))) '' Q2) := by
      simpa [Q2, d2, fμ] using
        (sumAbs_smoothed_unfold (m := m) (a := a) (b := b) (A := A) (phihat := phihat) (μ := μ)
          (hA := hA) (hphihat := hphihat) (x := x))
    have h_sep :
        sSup
            ((fun u : Fin m → ℝ =>
                  Finset.univ.sum (fun j : Fin m =>
                    (u j) * (a j x - b j) -
                      (1 / 2 : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ))) '' Q2) =
          Finset.univ.sum (fun j : Fin m =>
            sSup
              ((fun t =>
                    t * (a j x - b j) -
                      (1 / 2 : ℝ) * μ * ‖a j‖ * t ^ (2 : ℕ)) '' Set.Icc (-1 : ℝ) 1)) := by
      simpa [Q2] using
        (sumAbs_sSup_separable (m := m) (a := a) (b := b) (μ := μ) (x := x))
    have hpsi :
        ∀ j,
          sSup
              ((fun t =>
                    t * (a j x - b j) -
                      (1 / 2 : ℝ) * μ * ‖a j‖ * t ^ (2 : ℕ)) '' Set.Icc (-1 : ℝ) 1) =
            ‖a j‖ * ψμ (|a j x - b j| / ‖a j‖) := by
      intro j
      have hc : 0 < ‖a j‖ := hpos j
      simpa [ψμ] using
        (sSup_quadratic_Icc_eq_norm_mul_psi (μ := μ) (τ := a j x - b j) (c := ‖a j‖) hc)
    calc
      fμ x =
          sSup
            ((fun u : Fin m → ℝ =>
                  Finset.univ.sum (fun j : Fin m =>
                    (u j) * (a j x - b j) -
                      (1 / 2 : ℝ) * μ * ‖a j‖ * (u j) ^ (2 : ℕ))) '' Q2) := h_unfold
      _ =
          Finset.univ.sum (fun j : Fin m =>
            sSup
              ((fun t =>
                    t * (a j x - b j) -
                      (1 / 2 : ℝ) * μ * ‖a j‖ * t ^ (2 : ℕ)) '' Set.Icc (-1 : ℝ) 1)) := h_sep
      _ = Finset.univ.sum (fun j : Fin m =>
            ‖a j‖ * ψμ (|a j x - b j| / ‖a j‖)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact hpsi j
  · refine And.intro rfl ?_
    refine And.intro ?_ ?_
    · simpa using
        (sumAbs_operatorNorm_bound (m := m) (a := a) (A := A) (hA := hA))
    · have hD_nonneg : 0 ≤ D := by
        have : ∀ j, 0 ≤ ‖a j‖ := by intro j; exact norm_nonneg _
        simpa [D] using (Finset.sum_nonneg (fun j _ => this j))
      exact sumAbs_complexity_exists_N (D := D) (D1 := D1) (σ1 := σ1) (ε := ε) hε hD_nonneg

end Section04Part10
