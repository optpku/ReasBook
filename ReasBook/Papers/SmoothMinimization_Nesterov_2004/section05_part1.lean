/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import Papers.SmoothMinimization_Nesterov_2004.section01
import Papers.SmoothMinimization_Nesterov_2004.section03
import Papers.SmoothMinimization_Nesterov_2004.section04

open scoped BigOperators

/-- Quadratic bound used in the dual pairing estimate. -/
lemma quadratic_bound (r a L : ℝ) (hL : 0 < L) :
    r * a - (1 / (2 * L)) * r ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
  have h : 0 ≤ (r - L * a) ^ (2 : ℕ) := by
    simpa [pow_two] using (sq_nonneg (r - L * a))
  have hL' : L ≠ 0 := by linarith
  field_simp [hL']
  nlinarith [h]

/-- Dual norm is positively homogeneous (≤ direction) for nonnegative scalars. -/
lemma dualNormDef_smul_le_of_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (a : ℝ) (ha : 0 ≤ a) (s : Module.Dual ℝ E) :
    DualNormDef (a • s) ≤ a * DualNormDef s := by
  classical
  set T : Set ℝ := { r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = DualPairing (a • s) x }
  have hnonneg : 0 ≤ a * DualNormDef s := by
    exact mul_nonneg ha (dualNormDef_nonneg' (s := s))
  have hle : ∀ r ∈ T, r ≤ a * DualNormDef s := by
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    have hle' : DualPairing s x ≤ DualNormDef s := by
      have h := dualPairing_le_dualNormDef_mul_norm_section02 (s := s) (x := x)
      simpa [hx, mul_comm] using h
    have hmul : a * DualPairing s x ≤ a * DualNormDef s :=
      mul_le_mul_of_nonneg_left hle' ha
    simpa [DualPairing, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hsup : sSup T ≤ a * DualNormDef s := Real.sSup_le hle hnonneg
  simpa [DualNormDef, T] using hsup

/-- Existence of a dual functional attaining the norm on a nonzero vector. -/
lemma exists_dual_norming_functional_DualNormDef {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (h : E) (hh : h ≠ 0) :
    ∃ s0 : Module.Dual ℝ E, DualNormDef s0 ≤ 1 ∧ DualPairing s0 h = ‖h‖ := by
  classical
  obtain ⟨g, hg_norm, hg_eval⟩ := exists_dual_vector ℝ h hh
  let s0 : Module.Dual ℝ E := g.toLinearMap
  have hpair : DualPairing s0 h = ‖h‖ := by
    simpa [DualPairing, s0] using hg_eval
  set S : Set ℝ := { r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = DualPairing s0 x }
  have hsup : sSup S ≤ (1 : ℝ) := by
    refine Real.sSup_le ?_ (by linarith)
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    have hle_abs : DualPairing s0 x ≤ |DualPairing s0 x| := le_abs_self _
    have hle_norm : |DualPairing s0 x| ≤ ‖g‖ * ‖x‖ := by
      simpa [DualPairing, s0, Real.norm_eq_abs] using (g.le_opNorm x)
    have hle : DualPairing s0 x ≤ ‖g‖ * ‖x‖ := hle_abs.trans hle_norm
    simpa [hx, hg_norm, s0, DualPairing] using hle
  have hdual : DualNormDef s0 ≤ 1 := by
    simpa [DualNormDef, S] using hsup
  exact ⟨s0, hdual, hpair⟩

/-- The dual norm of the zero functional is zero. -/
lemma dualNormDef_zero {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : DualNormDef (0 : Module.Dual ℝ E) = 0 := by
  classical
  set S : Set ℝ := { r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = DualPairing (0 : Module.Dual ℝ E) x }
  have hsup : sSup S ≤ 0 := by
    refine Real.sSup_le ?_ (by linarith)
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    simp [DualPairing]
  have hle : DualNormDef (0 : Module.Dual ℝ E) ≤ 0 := by
    simpa [DualNormDef, S] using hsup
  have hge : 0 ≤ DualNormDef (0 : Module.Dual ℝ E) :=
    dualNormDef_nonneg' (s := (0 : Module.Dual ℝ E))
  exact le_antisymm hle hge

/-- Pointwise upper bound for the dual quadratic payoff. -/
lemma dual_pairing_quadratic_sup_pointwise_upper {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (g : Module.Dual ℝ E) (h : E) (L : ℝ)
    (hL : 0 < L) (s : Module.Dual ℝ E) :
    DualPairing s h - (1 / (2 * L)) * (DualNormDef (s - g)) ^ (2 : ℕ) ≤
      DualPairing g h + (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) := by
  have hsplit : DualPairing s h = DualPairing g h + DualPairing (s - g) h := by
    simp [DualPairing]
  have hpair : DualPairing (s - g) h ≤ DualNormDef (s - g) * ‖h‖ := by
    simpa using (dualPairing_le_dualNormDef_mul_norm_section02 (s := s - g) (x := h))
  have hquad :
      DualNormDef (s - g) * ‖h‖ - (1 / (2 * L)) * (DualNormDef (s - g)) ^ (2 : ℕ) ≤
        (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) :=
    quadratic_bound (r := DualNormDef (s - g)) (a := ‖h‖) (L := L) hL
  have hstep :
      DualPairing (s - g) h - (1 / (2 * L)) * (DualNormDef (s - g)) ^ (2 : ℕ) ≤
        (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) := by
    linarith
  calc
    DualPairing s h - (1 / (2 * L)) * (DualNormDef (s - g)) ^ (2 : ℕ)
        = DualPairing g h +
            (DualPairing (s - g) h - (1 / (2 * L)) * (DualNormDef (s - g)) ^ (2 : ℕ)) := by
          calc
            DualPairing s h - (1 / (2 * L)) * (DualNormDef (s - g)) ^ (2 : ℕ)
                = (DualPairing g h + DualPairing (s - g) h) -
                    (1 / (2 * L)) * (DualNormDef (s - g)) ^ (2 : ℕ) := by
                      simp [hsplit]
            _ = DualPairing g h +
                (DualPairing (s - g) h - (1 / (2 * L)) * (DualNormDef (s - g)) ^ (2 : ℕ)) := by
                  ring
    _ ≤ DualPairing g h + (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_left hstep (DualPairing g h))

/-- A candidate point achieving the lower bound in the dual supremum. -/
lemma dual_pairing_quadratic_sup_attaining_point {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (g : Module.Dual ℝ E) (h : E) (L : ℝ)
    (hL : 0 < L) :
    ∃ s : Module.Dual ℝ E,
      DualPairing g h + (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) ≤
        DualPairing s h - (1 / (2 * L)) * (DualNormDef (s - g)) ^ (2 : ℕ) := by
  classical
  by_cases hzero : h = 0
  · refine ⟨g, ?_⟩
    simp [hzero, DualPairing, dualNormDef_zero]
  · obtain ⟨s0, hs0_le, hs0_pair⟩ :=
      exists_dual_norming_functional_DualNormDef (h := h) hzero
    let a : ℝ := L * ‖h‖
    have ha_nonneg : 0 ≤ a := by
      exact mul_nonneg (le_of_lt hL) (norm_nonneg h)
    let sstar : Module.Dual ℝ E := g + a • s0
    refine ⟨sstar, ?_⟩
    have hsstar_sub : sstar - g = a • s0 := by
      simp [sstar]
    have hpair : DualPairing sstar h = DualPairing g h + a * DualPairing s0 h := by
      simp [sstar, DualPairing, smul_eq_mul]
    have hpair' : DualPairing sstar h = DualPairing g h + a * ‖h‖ := by
      simpa [hs0_pair] using hpair
    have hnorm_le : DualNormDef (sstar - g) ≤ a := by
      have hle1 : DualNormDef (a • s0) ≤ a * DualNormDef s0 :=
        dualNormDef_smul_le_of_nonneg (a := a) ha_nonneg (s := s0)
      have hle2 : a * DualNormDef s0 ≤ a := by
        have hle2' := mul_le_mul_of_nonneg_left hs0_le ha_nonneg
        simpa using hle2'
      simpa [hsstar_sub] using (hle1.trans hle2)
    have hpow : (DualNormDef (sstar - g)) ^ (2 : ℕ) ≤ a ^ (2 : ℕ) := by
      have hnonneg : 0 ≤ DualNormDef (sstar - g) :=
        dualNormDef_nonneg' (s := sstar - g)
      have hmul : DualNormDef (sstar - g) * DualNormDef (sstar - g) ≤ a * a :=
        mul_self_le_mul_self hnonneg hnorm_le
      simpa [pow_two] using hmul
    have hnonpos : -(1 / (2 * L)) ≤ 0 := by
      have hpos : 0 < (1 / (2 * L)) := by
        have : 0 < 2 * L := by linarith
        exact one_div_pos.mpr this
      linarith
    have hneg_le : -(1 / (2 * L)) * a ^ (2 : ℕ) ≤
        -(1 / (2 * L)) * (DualNormDef (sstar - g)) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonpos_left hpow hnonpos
    have haux : (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) =
        a * ‖h‖ - (1 / (2 * L)) * a ^ (2 : ℕ) := by
      have hL' : L ≠ 0 := by linarith
      field_simp [a, hL']
      ring
    have hineq : (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) ≤
        a * ‖h‖ - (1 / (2 * L)) * (DualNormDef (sstar - g)) ^ (2 : ℕ) := by
      nlinarith [haux, hneg_le]
    calc
      DualPairing g h + (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ)
          ≤ DualPairing g h +
              (a * ‖h‖ - (1 / (2 * L)) * (DualNormDef (sstar - g)) ^ (2 : ℕ)) := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  (add_le_add_left hineq (DualPairing g h))
      _ = DualPairing sstar h - (1 / (2 * L)) * (DualNormDef (sstar - g)) ^ (2 : ℕ) := by
            simp [hpair', sub_eq_add_neg, add_assoc]

/-- Lemma 1.5.1.
For any `g ∈ E*`, `h ∈ E`, and `L > 0`, we have
`⟪g, h⟫_1 + (1/2) L ‖h‖_1^2 = max_{s ∈ E*} { ⟪s, h⟫_1 - (1/(2L)) ‖s - g‖_{1,*}^2 }`
(equation (eq:lem6)). -/
theorem dual_pairing_quadratic_sup {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (g : Module.Dual ℝ E) (h : E) (L : ℝ)
    (hL : 0 < L) :
    DualPairing g h + (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) =
      sSup
        ((fun s : Module.Dual ℝ E =>
            DualPairing s h -
              (1 / (2 * L)) * (DualNormDef (s - g)) ^ (2 : ℕ)) ''
          (Set.univ : Set (Module.Dual ℝ E))) := by
  classical
  let Φ : Module.Dual ℝ E → ℝ := fun s =>
    DualPairing s h - (1 / (2 * L)) * (DualNormDef (s - g)) ^ (2 : ℕ)
  let S : Set ℝ := Φ '' (Set.univ : Set (Module.Dual ℝ E))
  have hpoint : ∀ s, Φ s ≤ DualPairing g h + (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) := by
    intro s
    simpa [Φ] using dual_pairing_quadratic_sup_pointwise_upper g h L hL s
  have hBdd : BddAbove S := by
    refine ⟨DualPairing g h + (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ), ?_⟩
    rintro r ⟨s, -, rfl⟩
    exact hpoint s
  have hS_nonempty : S.Nonempty := by
    refine ⟨Φ g, ?_⟩
    refine ⟨g, by simp [Φ]⟩
  have hsup_le : sSup S ≤ DualPairing g h + (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) := by
    refine csSup_le hS_nonempty ?_
    intro r hr
    rcases hr with ⟨s, -, rfl⟩
    exact hpoint s
  obtain ⟨s, hs⟩ := dual_pairing_quadratic_sup_attaining_point g h L hL
  have hmem : Φ s ∈ S := by
    refine ⟨s, by simp [Φ]⟩
  have hle_sup : DualPairing g h + (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) ≤ sSup S := by
    have hs' : DualPairing g h + (1 / 2 : ℝ) * L * ‖h‖ ^ (2 : ℕ) ≤ Φ s := hs
    have hsup_ge : Φ s ≤ sSup S := le_csSup hBdd hmem
    exact hs'.trans hsup_ge
  exact le_antisymm hle_sup hsup_le

/-- Definition 1.5.1.
Let `xbar ∈ Δ_n` and `gbar ∈ ℝ^n`. Define the proximal subproblem value for the simplex with the
`l1`-norm by
`psi* = min_{x ∈ Δ_n} { <gbar, x - xbar>_1 + (1/2) L ‖x - xbar‖_1^2 }` (equation (5.1)). -/
noncomputable def simplexProximalValue (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ) : ℝ :=
  sInf
    ((fun x =>
        (∑ i, gbar i * (x i - xbar i)) +
          (1 / 2 : ℝ) * L * (∑ i, |x i - xbar i|) ^ (2 : ℕ)) '' standardSimplex n)

/-- On the simplex, the coordinatewise sum of a difference is zero. -/
lemma simplex_sum_sub_eq_zero {n : ℕ} {x xbar : Fin n → ℝ}
    (hx : x ∈ standardSimplex n) (hxbar : xbar ∈ standardSimplex n) :
    (∑ i, (x i - xbar i)) = 0 := by
  have hxsum : ∑ i, x i = (1 : ℝ) := by
    have hx' := hx
    simp [standardSimplex] at hx'
    exact hx'.2
  have hxbar_sum : ∑ i, xbar i = (1 : ℝ) := by
    have hxbar' := hxbar
    simp [standardSimplex] at hxbar'
    exact hxbar'.2
  calc
    ∑ i, (x i - xbar i) = (∑ i, x i) - ∑ i, xbar i := by
      simp [Finset.sum_sub_distrib]
    _ = (1 : ℝ) - 1 := by simp [hxsum, hxbar_sum]
    _ = 0 := by simp

/-- Shifting `gbar` by a constant does not change the simplex proximal value. -/
lemma simplexProximalValue_shift_gbar_const (n : ℕ) (xbar gbar : Fin n → ℝ) (L c : ℝ)
    (hxbar : xbar ∈ standardSimplex n) :
    simplexProximalValue n xbar (fun i => gbar i + c) L =
      simplexProximalValue n xbar gbar L := by
  classical
  let Φ : (Fin n → ℝ) → ℝ := fun x =>
    (∑ i, gbar i * (x i - xbar i)) +
      (1 / 2 : ℝ) * L * (∑ i, |x i - xbar i|) ^ (2 : ℕ)
  let Φ' : (Fin n → ℝ) → ℝ := fun x =>
    (∑ i, (gbar i + c) * (x i - xbar i)) +
      (1 / 2 : ℝ) * L * (∑ i, |x i - xbar i|) ^ (2 : ℕ)
  have hpoint : ∀ x ∈ standardSimplex n, Φ' x = Φ x := by
    intro x hx
    have hsum : ∑ i, (x i - xbar i) = 0 :=
      simplex_sum_sub_eq_zero (hx := hx) (hxbar := hxbar)
    have hlin :
        ∑ i, (gbar i + c) * (x i - xbar i) = ∑ i, gbar i * (x i - xbar i) := by
      calc
        ∑ i, (gbar i + c) * (x i - xbar i)
            = ∑ i, (gbar i * (x i - xbar i) + c * (x i - xbar i)) := by
                simp [add_mul]
        _ = (∑ i, gbar i * (x i - xbar i)) + (∑ i, c * (x i - xbar i)) := by
              simpa using
                (Finset.sum_add_distrib (s := Finset.univ)
                  (f := fun i => gbar i * (x i - xbar i))
                  (g := fun i => c * (x i - xbar i)))
        _ = (∑ i, gbar i * (x i - xbar i)) + c * (∑ i, (x i - xbar i)) := by
              have hsumc :
                  ∑ i, c * (x i - xbar i) = c * ∑ i, (x i - xbar i) := by
                symm
                simpa using (Finset.mul_sum (a := c) (s := Finset.univ)
                  (f := fun i => x i - xbar i))
              simp [hsumc]
        _ = ∑ i, gbar i * (x i - xbar i) := by
              simp [hsum]
    simp [Φ', Φ, hlin]
  have himage : Φ' '' standardSimplex n = Φ '' standardSimplex n := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hpoint x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hpoint x hx⟩
  have hsInf : sInf (Φ' '' standardSimplex n) = sInf (Φ '' standardSimplex n) := by
    simp [himage]
  simpa [simplexProximalValue, Φ, Φ'] using hsInf

/-- Shifting by the minimum coordinate makes the infimum zero for a finite index set. -/
lemma sInf_image_sub_sInf_eq_zero_fin (n : ℕ) (gbar : Fin n → ℝ) (hn : 0 < n) :
    let α := sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n)))
    sInf ((fun i => gbar i - α) '' (Set.univ : Set (Fin n))) = 0 := by
  classical
  intro α
  have hbdd : BddBelow ((fun i => gbar i) '' (Set.univ : Set (Fin n))) := by
    have hfin : ((fun i => gbar i) '' (Set.univ : Set (Fin n))).Finite :=
      (Set.finite_univ.image fun i => gbar i)
    exact hfin.bddBelow
  have hne : ((fun i => gbar i) '' (Set.univ : Set (Fin n))).Nonempty := by
    refine ⟨gbar ⟨0, hn⟩, ?_⟩
    exact ⟨⟨0, hn⟩, by simp, rfl⟩
  have hset :
      ((fun i => gbar i - α) '' (Set.univ : Set (Fin n))) =
        (fun x => -α + x) '' ((fun i => gbar i) '' (Set.univ : Set (Fin n))) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨gbar i, ?_, ?_⟩
      · exact ⟨i, hi, rfl⟩
      · ring
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨i, hi, rfl⟩
      exact ⟨i, hi, by ring⟩
  have hshift :
      sInf ((fun x => -α + x) '' ((fun i => gbar i) '' (Set.univ : Set (Fin n)))) =
        -α + sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n))) :=
    sInf_image_add_const (a := -α)
      (s := (fun i => gbar i) '' (Set.univ : Set (Fin n))) hbdd hne
  calc
    sInf ((fun i => gbar i - α) '' (Set.univ : Set (Fin n)))
        =
        sInf ((fun x => -α + x) '' ((fun i => gbar i) '' (Set.univ : Set (Fin n)))) := by
          rw [hset]
    _ = -α + sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n))) := hshift
    _ = 0 := by simp [α]

/-- Proposition 1.5.1.
In the setting of Definition 1.5.1, we may normalize `gbar` so that
`min_{1 ≤ i ≤ n} gbar^(i) = 0` (equation (5.2)) without changing the proximal value. -/
theorem simplexProximalValue_wlog_min_zero (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ)
    (hxbar : xbar ∈ standardSimplex n) :
    ∃ gbar' : Fin n → ℝ,
      sInf ((fun i => gbar' i) '' (Set.univ : Set (Fin n))) = 0 ∧
        simplexProximalValue n xbar gbar' L = simplexProximalValue n xbar gbar L := by
  classical
  by_cases hzero : n = 0
  · subst hzero
    exfalso
    have hsimplex0 : (standardSimplex 0 : Set (Fin 0 → ℝ)) = ∅ := by
      ext x
      simp [standardSimplex]
    simp [hsimplex0] at hxbar
  · have hn : 0 < n := Nat.pos_of_ne_zero hzero
    let α : ℝ := sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n)))
    let gbar' : Fin n → ℝ := fun i => gbar i - α
    refine ⟨gbar', ?_, ?_⟩
    · simpa [gbar', α] using
        (sInf_image_sub_sInf_eq_zero_fin (n := n) (gbar := gbar) hn)
    · simpa [gbar', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (simplexProximalValue_shift_gbar_const (n := n) (xbar := xbar) (gbar := gbar)
          (L := L) (c := -α) (hxbar := hxbar))

/-- The real sign recovers absolute value by multiplication. -/
lemma sign_mul_eq_abs (r : ℝ) : Real.sign r * r = |r| := by
  by_cases hr : r = 0
  · simp [hr]
  · by_cases hneg : r < 0
    · simp [Real.sign_of_neg hneg, abs_of_neg hneg]
    · have hpos : 0 < r := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hr)
      simp [Real.sign_of_pos hpos, abs_of_pos hpos]

/-- One-sided sign for right-derivatives of `|·|`. -/
noncomputable def simplexProximalValue_signPlus (z : ℝ) : ℝ := if z < 0 then -1 else 1

/-- One-sided sign for left-derivatives of `|·|`. -/
noncomputable def simplexProximalValue_signMinus (z : ℝ) : ℝ := if 0 < z then 1 else -1

/-- One-sided absolute value expansion for `z + t` with `t ≥ 0`. -/
lemma simplexProximalValue_abs_add_oneSided (z t : ℝ) (ht : 0 ≤ t)
    (htle : z < 0 → t ≤ -z) :
    |z + t| = |z| + simplexProximalValue_signPlus z * t := by
  by_cases hz : z < 0
  · have hzt : z + t ≤ 0 := by linarith [htle hz]
    have hsign : simplexProximalValue_signPlus z = -1 := by
      simp [simplexProximalValue_signPlus, hz]
    have habs : |z| = -z := abs_of_neg hz
    have habs2 : |z + t| = -(z + t) := abs_of_nonpos hzt
    simp [habs, habs2, hsign, add_comm]
  · have hz' : 0 ≤ z := le_of_not_gt hz
    have hzt : 0 ≤ z + t := by linarith
    have hsign : simplexProximalValue_signPlus z = 1 := by
      simp [simplexProximalValue_signPlus, hz]
    have habs : |z| = z := abs_of_nonneg hz'
    have habs2 : |z + t| = z + t := abs_of_nonneg hzt
    simp [habs, habs2, hsign]

/-- One-sided absolute value expansion for `z - t` with `t ≥ 0`. -/
lemma simplexProximalValue_abs_sub_oneSided (z t : ℝ) (ht : 0 ≤ t)
    (htle : 0 < z → t ≤ z) :
    |z - t| = |z| - simplexProximalValue_signMinus z * t := by
  by_cases hz : 0 < z
  · have hzt : 0 ≤ z - t := by linarith [htle hz]
    have hsign : simplexProximalValue_signMinus z = 1 := by
      simp [simplexProximalValue_signMinus, hz]
    have habs : |z| = z := abs_of_pos hz
    have habs2 : |z - t| = z - t := abs_of_nonneg hzt
    calc
      |z - t| = z - t := habs2
      _ = |z| - simplexProximalValue_signMinus z * t := by
        simp [habs, hsign]
  · have hz' : z ≤ 0 := le_of_not_gt hz
    have hzt : z - t ≤ 0 := by linarith [ht]
    have hsign : simplexProximalValue_signMinus z = -1 := by
      simp [simplexProximalValue_signMinus, hz]
    have habs : |z| = -z := abs_of_nonpos hz'
    have habs2 : |z - t| = -(z - t) := abs_of_nonpos hzt
    calc
      |z - t| = -(z - t) := habs2
      _ = -z + t := by ring
      _ = |z| - simplexProximalValue_signMinus z * t := by
        simp [habs, hsign, sub_eq_add_neg, add_comm]

/-- The dot product is bounded by the sup norm times the `l1` norm. -/
lemma sum_mul_le_norm_sum_abs (n : ℕ) (s h : Fin n → ℝ) :
    (∑ i, s i * h i) ≤ ‖s‖ * (∑ i, |h i|) := by
  classical
  have hsum_le : ∑ i, s i * h i ≤ ∑ i, |s i * h i| := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact le_abs_self _
  have hpoint : ∀ i, |s i * h i| ≤ ‖s‖ * |h i| := by
    intro i
    have hsi : |s i| ≤ ‖s‖ := by
      simpa using (norm_le_pi_norm (f := s) i)
    have hmul : |s i| * |h i| ≤ ‖s‖ * |h i| :=
      mul_le_mul_of_nonneg_right hsi (abs_nonneg _)
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hsum_le' : ∑ i, |s i * h i| ≤ ∑ i, ‖s‖ * |h i| := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hpoint i
  calc
    ∑ i, s i * h i ≤ ∑ i, |s i * h i| := hsum_le
    _ ≤ ∑ i, ‖s‖ * |h i| := hsum_le'
    _ = ‖s‖ * ∑ i, |h i| := by
      simpa [mul_comm] using
        (Finset.mul_sum (a := ‖s‖) (s := Finset.univ) (f := fun i => |h i|)).symm

/-- A finite-dimensional `l1`/`l∞` quadratic conjugacy identity. -/
lemma dot_l1Quadratic_eq_sSup_linf_fin (n : ℕ) (g h : Fin n → ℝ) (L : ℝ) (hL : 0 < L) :
    (∑ i, g i * h i) + (1 / 2 : ℝ) * L * (∑ i, |h i|) ^ (2 : ℕ) =
      sSup
        ((fun s : Fin n → ℝ =>
            (∑ i, (g i + s i) * h i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
          (Set.univ : Set (Fin n → ℝ))) := by
  classical
  let a : ℝ := ∑ i, |h i|
  let Φ : (Fin n → ℝ) → ℝ := fun s =>
    (∑ i, (g i + s i) * h i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)
  let S : Set ℝ := Φ '' (Set.univ : Set (Fin n → ℝ))
  have hsum :
      ∀ s : Fin n → ℝ, (∑ i, (g i + s i) * h i) = (∑ i, g i * h i) + ∑ i, s i * h i := by
    intro s
    calc
      ∑ i, (g i + s i) * h i
          = ∑ i, (g i * h i + s i * h i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [add_mul]
      _ = (∑ i, g i * h i) + ∑ i, s i * h i := by
            simpa using
              (Finset.sum_add_distrib (s := Finset.univ)
                (f := fun i => g i * h i) (g := fun i => s i * h i))
  have hpoint : ∀ s, Φ s ≤ (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
    intro s
    have hsum_le : ∑ i, s i * h i ≤ ‖s‖ * a :=
      sum_mul_le_norm_sum_abs (n := n) s h
    have hquad :
        ‖s‖ * a - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * L * a ^ (2 : ℕ) :=
      quadratic_bound (r := ‖s‖) (a := a) (L := L) hL
    have htmp :
        ∑ i, s i * h i - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
      linarith
    calc
      Φ s = (∑ i, g i * h i) +
          (∑ i, s i * h i - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) := by
            simp [Φ, hsum, sub_eq_add_neg, add_assoc]
      _ ≤ (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
            linarith
  have hBdd : BddAbove S := by
    refine ⟨(∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ), ?_⟩
    rintro r ⟨s, -, rfl⟩
    exact hpoint s
  have hS_nonempty : S.Nonempty := by
    refine ⟨Φ 0, ?_⟩
    exact ⟨0, by simp [Φ]⟩
  have hsup_le : sSup S ≤ (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
    refine csSup_le hS_nonempty ?_
    intro r hr
    rcases hr with ⟨s, -, rfl⟩
    exact hpoint s
  let sstar : Fin n → ℝ := fun i => L * a * Real.sign (h i)
  have hsum_star : ∑ i, sstar i * h i = L * a * a := by
    have hsum_sign : ∑ i, Real.sign (h i) * h i = a := by
      have hsum' : ∑ i, Real.sign (h i) * h i = ∑ i, |h i| := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [sign_mul_eq_abs]
      simpa [a] using hsum'
    calc
      ∑ i, sstar i * h i
          = ∑ i, (L * a) * (Real.sign (h i) * h i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [sstar, mul_assoc, mul_left_comm, mul_comm]
      _ = (L * a) * ∑ i, Real.sign (h i) * h i := by
            symm
            simpa using
              (Finset.mul_sum (a := L * a) (s := Finset.univ)
                (f := fun i => Real.sign (h i) * h i))
      _ = L * a * a := by simp [hsum_sign, mul_assoc]
  have hnorm_star : ‖sstar‖ = L * a := by
    have ha_nonneg : 0 ≤ a := by
      exact Finset.sum_nonneg (fun i hi => abs_nonneg _)
    have hLa_nonneg : 0 ≤ L * a := mul_nonneg (le_of_lt hL) ha_nonneg
    have hnorm_le : ‖sstar‖ ≤ L * a := by
      refine (pi_norm_le_iff_of_nonneg hLa_nonneg).2 ?_
      intro i
      have hsign_le : |Real.sign (h i)| ≤ (1 : ℝ) := by
        rcases Real.sign_apply_eq (h i) with hneg | hzero | hpos
        · simp [hneg]
        · simp [hzero]
        · simp [hpos]
      have habs : ‖sstar i‖ = |L * a| * |Real.sign (h i)| := by
        simp [sstar, Real.norm_eq_abs, abs_mul, mul_left_comm, mul_comm]
      have hle : |L * a| * |Real.sign (h i)| ≤ |L * a| * (1 : ℝ) :=
        mul_le_mul_of_nonneg_left hsign_le (abs_nonneg _)
      have hle' : |L * a| * (1 : ℝ) = L * a := by
        simp [abs_of_nonneg hLa_nonneg]
      calc
        ‖sstar i‖ = |L * a| * |Real.sign (h i)| := habs
        _ ≤ |L * a| * (1 : ℝ) := hle
        _ = L * a := hle'
    by_cases ha : a = 0
    · have ha' : a = 0 := ha
      have : sstar = 0 := by
        funext i
        simp [sstar, ha']
      simp [this, ha']
    · have hex : ∃ i, h i ≠ 0 := by
        by_contra hzero
        have hzero' : ∀ i, h i = 0 := by
          intro i
          by_contra hi
          exact hzero ⟨i, hi⟩
        have hsum_zero : a = 0 := by
          simp [a, hzero']
        exact ha hsum_zero
      rcases hex with ⟨i0, hi0⟩
      have hsign_abs : |Real.sign (h i0)| = 1 := by
        rcases Real.sign_apply_eq_of_ne_zero (h i0) hi0 with hneg | hpos
        · simp [hneg]
        · simp [hpos]
      have hnorm_ge : L * a ≤ ‖sstar‖ := by
        have hcoord : |sstar i0| = L * a := by
          have hLa : |L * a| = L * a := abs_of_nonneg hLa_nonneg
          calc
            |sstar i0| = |L * a| * |Real.sign (h i0)| := by
              simp [sstar, abs_mul, mul_left_comm, mul_comm]
            _ = |L * a| := by simp [hsign_abs]
            _ = L * a := hLa
        have hle : |sstar i0| ≤ ‖sstar‖ := by
          simpa using (norm_le_pi_norm (f := sstar) i0)
        simpa [hcoord] using hle
      exact le_antisymm hnorm_le hnorm_ge
  have hval :
      Φ sstar = (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
    have hL' : L ≠ 0 := by linarith
    calc
      Φ sstar
          = (∑ i, g i * h i) + (∑ i, sstar i * h i) -
              (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) := by
                simp [Φ, hsum, sub_eq_add_neg, add_assoc]
      _ = (∑ i, g i * h i) + (L * a * a) -
              (1 / (2 * L)) * (L * a) ^ (2 : ℕ) := by
                simp [hsum_star, hnorm_star]
      _ = (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
            field_simp [hL']
            ring
  have hle_sup : (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) ≤ sSup S := by
    have hmem : Φ sstar ∈ S := by
      exact ⟨sstar, by simp [Φ]⟩
    have hsup_ge : Φ sstar ≤ sSup S := le_csSup hBdd hmem
    simpa [hval] using hsup_ge
  have hmain := le_antisymm hle_sup hsup_le
  simpa [S, Φ, a] using hmain

/-- Rewriting the simplex proximal value as a `min-max` expression. -/
lemma simplexProximalValue_as_minimax_fin (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ) (hL : 0 < L) :
    simplexProximalValue n xbar gbar L =
      sInf
        ((fun x =>
            sSup
              ((fun s : Fin n → ℝ =>
                    (∑ i, (gbar i + s i) * (x i - xbar i)) -
                      (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
                (Set.univ : Set (Fin n → ℝ)))) '' standardSimplex n) := by
  classical
  let Φ : (Fin n → ℝ) → ℝ := fun x =>
    (∑ i, gbar i * (x i - xbar i)) +
      (1 / 2 : ℝ) * L * (∑ i, |x i - xbar i|) ^ (2 : ℕ)
  let Φ' : (Fin n → ℝ) → ℝ := fun x =>
    sSup
      ((fun s : Fin n → ℝ =>
            (∑ i, (gbar i + s i) * (x i - xbar i)) -
              (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' (Set.univ : Set (Fin n → ℝ)))
  have hpoint : ∀ x, Φ x = Φ' x := by
    intro x
    have h :=
      dot_l1Quadratic_eq_sSup_linf_fin (n := n) (g := gbar) (h := fun i => x i - xbar i)
        (L := L) hL
    simpa [Φ, Φ'] using h
  have himage : Φ '' standardSimplex n = Φ' '' standardSimplex n := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hpoint x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hpoint x⟩
  calc
    simplexProximalValue n xbar gbar L = sInf (Φ '' standardSimplex n) := by
      rfl
    _ = sInf (Φ' '' standardSimplex n) := by
      simp [himage]
    _ =
        sInf
          ((fun x =>
                sSup
                  ((fun s : Fin n → ℝ =>
                        (∑ i, (gbar i + s i) * (x i - xbar i)) -
                          (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' (Set.univ : Set (Fin n → ℝ))) ) ''
            standardSimplex n) := by
      rfl

/-- The infimum of a linear form over the simplex equals the minimum coefficient. -/
lemma dual_inner_min_over_simplex (n : ℕ) (r : Fin n → ℝ) :
    sInf ((fun x : Fin n → ℝ => ∑ i, r i * x i) '' standardSimplex n) =
      sInf (r '' (Set.univ : Set (Fin n))) := by
  simpa using (sInf_linear_standardSimplex_eq (r := r))

/-- The trivial minimax inequality (sup-inf ≤ inf-sup) for the finite simplex payoff. -/
lemma simplexProximalValue_minmax_exchange_fin_le (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ)
    (hn : 0 < n) (hL : 0 < L) :
    sSup
        ((fun s : Fin n → ℝ =>
              sInf
                ((fun x : Fin n → ℝ =>
                      (∑ i, (gbar i + s i) * (x i - xbar i)) -
                        (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' standardSimplex n)) ''
          (Set.univ : Set (Fin n → ℝ))) ≤
      sInf
        ((fun x =>
              sSup
                ((fun s : Fin n → ℝ =>
                      (∑ i, (gbar i + s i) * (x i - xbar i)) -
                        (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
                  (Set.univ : Set (Fin n → ℝ)))) '' standardSimplex n) := by
  classical
  have hne_simplex : (standardSimplex n).Nonempty := standardSimplex_nonempty_of_pos hn
  have hne_sup :
      ((fun s : Fin n → ℝ =>
            sInf
              ((fun x : Fin n → ℝ =>
                    (∑ i, (gbar i + s i) * (x i - xbar i)) -
                      (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' standardSimplex n)) ''
        (Set.univ : Set (Fin n → ℝ))).Nonempty := by
    refine ⟨(fun s : Fin n → ℝ =>
        sInf
          ((fun x : Fin n → ℝ =>
                (∑ i, (gbar i + s i) * (x i - xbar i)) -
                  (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' standardSimplex n)) 0, ?_⟩
    exact ⟨0, by simp, rfl⟩
  refine csSup_le hne_sup ?_
  intro y hy
  rcases hy with ⟨s, -, rfl⟩
  have hne_inf :
      ((fun x =>
            sSup
              ((fun s : Fin n → ℝ =>
                    (∑ i, (gbar i + s i) * (x i - xbar i)) -
                      (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
                (Set.univ : Set (Fin n → ℝ)))) '' standardSimplex n).Nonempty := by
    rcases hne_simplex with ⟨x0, hx0⟩
    exact ⟨_, ⟨x0, hx0, rfl⟩⟩
  refine le_csInf hne_inf ?_
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  let r : Fin n → ℝ := fun i => gbar i + s i
  let c : ℝ := -∑ i, r i * xbar i - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)
  have hbd_inf :
      BddBelow
        ((fun x : Fin n → ℝ =>
              (∑ i, (gbar i + s i) * (x i - xbar i)) -
                (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' standardSimplex n) := by
    refine ⟨c + sInf (r '' (Set.univ : Set (Fin n))), ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hle := sInf_coeff_le_linear_standardSimplex (r := r) x hx
    have hsum :
        ∑ i, r i * (x i - xbar i) =
          (∑ i, r i * x i) - ∑ i, r i * xbar i := by
      calc
        ∑ i, r i * (x i - xbar i) = ∑ i, (r i * x i - r i * xbar i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        _ = (∑ i, r i * x i) - ∑ i, r i * xbar i := by
          simp [Finset.sum_sub_distrib]
    have hrewrite :
        c + ∑ i, r i * x i =
          (∑ i, r i * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) := by
      calc
        c + ∑ i, r i * x i =
            (∑ i, r i * x i) - ∑ i, r i * xbar i - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) := by
              simp [c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = (∑ i, r i * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) := by
              simp [hsum]
    have hle' : c + sInf (r '' (Set.univ : Set (Fin n))) ≤ c + ∑ i, r i * x i := by
      linarith
    exact hle'.trans_eq hrewrite
  have hle_inf :
      sInf
          ((fun x : Fin n → ℝ =>
                (∑ i, (gbar i + s i) * (x i - xbar i)) -
                  (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' standardSimplex n) ≤
        (∑ i, (gbar i + s i) * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) := by
    exact csInf_le hbd_inf ⟨x, hx, rfl⟩
  let h : Fin n → ℝ := fun i => x i - xbar i
  let a : ℝ := ∑ i, |h i|
  have hsum :
      ∑ i, (gbar i + s i) * h i = (∑ i, gbar i * h i) + ∑ i, s i * h i := by
    calc
      ∑ i, (gbar i + s i) * h i = ∑ i, (gbar i * h i + s i * h i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [add_mul]
      _ = (∑ i, gbar i * h i) + ∑ i, s i * h i := by
        simpa using
          (Finset.sum_add_distrib (s := Finset.univ)
            (f := fun i => gbar i * h i) (g := fun i => s i * h i))
  have hsum_le : ∑ i, s i * h i ≤ ‖s‖ * a :=
    sum_mul_le_norm_sum_abs (n := n) s h
  have hquad :
      ‖s‖ * a - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * L * a ^ (2 : ℕ) :=
    quadratic_bound (r := ‖s‖) (a := a) (L := L) hL
  have hpoint :
      (∑ i, (gbar i + s i) * h i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) ≤
        (∑ i, gbar i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
    have htmp :
        ∑ i, s i * h i - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
      linarith [hsum_le, hquad]
    calc
      (∑ i, (gbar i + s i) * h i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) =
          (∑ i, gbar i * h i) + (∑ i, s i * h i - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) := by
            simp [hsum, sub_eq_add_neg, add_assoc]
      _ ≤ (∑ i, gbar i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
            linarith
  have hsup_eq :
      (∑ i, gbar i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) =
        sSup
          ((fun s : Fin n → ℝ =>
                (∑ i, (gbar i + s i) * h i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
            (Set.univ : Set (Fin n → ℝ))) :=
    dot_l1Quadratic_eq_sSup_linf_fin (n := n) (g := gbar) (h := h) (L := L) hL
  have hsup_eq' :
      sSup
          ((fun s : Fin n → ℝ =>
                (∑ i, (gbar i + s i) * h i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
            (Set.univ : Set (Fin n → ℝ))) =
        (∑ i, gbar i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
    simpa using hsup_eq.symm
  have hle_sup :
      (∑ i, (gbar i + s i) * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) ≤
        sSup
          ((fun s : Fin n → ℝ =>
                (∑ i, (gbar i + s i) * (x i - xbar i)) -
                  (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' (Set.univ : Set (Fin n → ℝ))) := by
    calc
      (∑ i, (gbar i + s i) * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) =
          (∑ i, (gbar i + s i) * h i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) := by
            simp [h]
      _ ≤ (∑ i, gbar i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := hpoint
      _ = sSup
          ((fun s : Fin n → ℝ =>
                (∑ i, (gbar i + s i) * (x i - xbar i)) -
                  (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' (Set.univ : Set (Fin n → ℝ))) := by
            simpa [h] using hsup_eq'.symm
  exact le_trans hle_inf hle_sup

/-- A saddle point yields `infsup ≤ supinf` for the finite simplex payoff. -/
lemma simplexProximalValue_minmax_exchange_fin_le_of_saddlePoint (n : ℕ) (xbar gbar : Fin n → ℝ)
    (L : ℝ) (hL : 0 < L)
    (hsaddle :
      ∃ xstar ∈ standardSimplex n, ∃ sstar : Fin n → ℝ,
        (∀ s : Fin n → ℝ,
              (∑ i, (gbar i + s i) * (xstar i - xbar i)) -
                  (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) ≤
                (∑ i, (gbar i + sstar i) * (xstar i - xbar i)) -
                  (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ)) ∧
          (∀ x ∈ standardSimplex n,
              (∑ i, (gbar i + sstar i) * (xstar i - xbar i)) -
                  (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) ≤
                (∑ i, (gbar i + sstar i) * (x i - xbar i)) -
                  (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ))) :
    sInf
        ((fun x =>
              sSup
                ((fun s : Fin n → ℝ =>
                      (∑ i, (gbar i + s i) * (x i - xbar i)) -
                        (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
                  (Set.univ : Set (Fin n → ℝ)))) '' standardSimplex n) ≤
      sSup
        ((fun s : Fin n → ℝ =>
              sInf
                ((fun x : Fin n → ℝ =>
                      (∑ i, (gbar i + s i) * (x i - xbar i)) -
                        (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' standardSimplex n)) ''
          (Set.univ : Set (Fin n → ℝ))) := by
  classical
  let F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun x s =>
    (∑ i, (gbar i + s i) * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)
  rcases hsaddle with ⟨xstar, hxstar, sstar, hsmax, hsmin⟩
  have hsmax' : ∀ s, F xstar s ≤ F xstar sstar := by
    intro s
    simpa [F] using hsmax s
  have hsmin' : ∀ x ∈ standardSimplex n, F xstar sstar ≤ F x sstar := by
    intro x hx
    simpa [F] using hsmin x hx
  have hbd_inf :
      ∀ s : Fin n → ℝ, BddBelow ((fun x : Fin n → ℝ => F x s) '' standardSimplex n) := by
    intro s
    let r : Fin n → ℝ := fun i => gbar i + s i
    let c : ℝ := -∑ i, r i * xbar i - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)
    refine ⟨c + sInf (r '' (Set.univ : Set (Fin n))), ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hle := sInf_coeff_le_linear_standardSimplex (r := r) x hx
    have hsum :
        ∑ i, r i * (x i - xbar i) =
          (∑ i, r i * x i) - ∑ i, r i * xbar i := by
      calc
        ∑ i, r i * (x i - xbar i) = ∑ i, (r i * x i - r i * xbar i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        _ = (∑ i, r i * x i) - ∑ i, r i * xbar i := by
          simp [Finset.sum_sub_distrib]
    have hrewrite :
        c + ∑ i, r i * x i =
          (∑ i, r i * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) := by
      calc
        c + ∑ i, r i * x i =
            (∑ i, r i * x i) - ∑ i, r i * xbar i - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) := by
              simp [c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = (∑ i, r i * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) := by
              simp [hsum]
    have hle' : c + sInf (r '' (Set.univ : Set (Fin n))) ≤ c + ∑ i, r i * x i := by
      linarith
    exact hle'.trans_eq hrewrite
  have hle_sup_point :
      ∀ x, F x sstar ≤ sSup ((fun s : Fin n → ℝ => F x s) '' (Set.univ : Set (Fin n → ℝ))) := by
    intro x
    let h : Fin n → ℝ := fun i => x i - xbar i
    let a : ℝ := ∑ i, |h i|
    have hsum :
        ∑ i, (gbar i + sstar i) * h i = (∑ i, gbar i * h i) + ∑ i, sstar i * h i := by
      calc
        ∑ i, (gbar i + sstar i) * h i = ∑ i, (gbar i * h i + sstar i * h i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [add_mul]
        _ = (∑ i, gbar i * h i) + ∑ i, sstar i * h i := by
          simpa using
            (Finset.sum_add_distrib (s := Finset.univ)
              (f := fun i => gbar i * h i) (g := fun i => sstar i * h i))
    have hsum_le : ∑ i, sstar i * h i ≤ ‖sstar‖ * a :=
      sum_mul_le_norm_sum_abs (n := n) sstar h
    have hquad :
        ‖sstar‖ * a - (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * L * a ^ (2 : ℕ) :=
      quadratic_bound (r := ‖sstar‖) (a := a) (L := L) hL
    have hpoint :
        (∑ i, (gbar i + sstar i) * h i) - (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) ≤
          (∑ i, gbar i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
      have htmp :
          ∑ i, sstar i * h i - (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) ≤
            (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
        linarith [hsum_le, hquad]
      calc
        (∑ i, (gbar i + sstar i) * h i) - (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) =
            (∑ i, gbar i * h i) + (∑ i, sstar i * h i - (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ)) := by
              simp [hsum, sub_eq_add_neg, add_assoc]
        _ ≤ (∑ i, gbar i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
              linarith
    have hsup_eq :
        (∑ i, gbar i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) =
          sSup
            ((fun s : Fin n → ℝ =>
                  (∑ i, (gbar i + s i) * h i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
              (Set.univ : Set (Fin n → ℝ))) :=
      dot_l1Quadratic_eq_sSup_linf_fin (n := n) (g := gbar) (h := h) (L := L) hL
    have hsup_eq' :
        sSup
            ((fun s : Fin n → ℝ =>
                  (∑ i, (gbar i + s i) * h i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
              (Set.univ : Set (Fin n → ℝ))) =
          (∑ i, gbar i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
      simpa using hsup_eq.symm
    calc
      F x sstar =
          (∑ i, (gbar i + sstar i) * h i) - (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) := by
            simp [F, h]
      _ ≤ (∑ i, gbar i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := hpoint
      _ = sSup ((fun s : Fin n → ℝ => F x s) '' (Set.univ : Set (Fin n → ℝ))) := by
            simpa [F, h] using hsup_eq'.symm
  have hbd_left :
      BddBelow
        ((fun x =>
              sSup ((fun s : Fin n → ℝ => F x s) '' (Set.univ : Set (Fin n → ℝ)))) ''
          standardSimplex n) := by
    refine ⟨F xstar sstar, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hle1 : F xstar sstar ≤ F x sstar := hsmin' x hx
    have hle2 : F x sstar ≤ sSup ((fun s : Fin n → ℝ => F x s) '' (Set.univ : Set (Fin n → ℝ))) :=
      hle_sup_point x
    exact hle1.trans hle2
  have hleft :
      sInf
          ((fun x =>
                sSup ((fun s : Fin n → ℝ => F x s) '' (Set.univ : Set (Fin n → ℝ)))) ''
            standardSimplex n) ≤
        sSup ((fun s : Fin n → ℝ => F xstar s) '' (Set.univ : Set (Fin n → ℝ))) := by
    exact csInf_le hbd_left ⟨xstar, hxstar, rfl⟩
  have hsup_nonempty :
      ((fun s : Fin n → ℝ => F xstar s) '' (Set.univ : Set (Fin n → ℝ))).Nonempty := by
    refine ⟨F xstar 0, ?_⟩
    exact ⟨0, by simp, rfl⟩
  have hsup_bdd :
      BddAbove ((fun s : Fin n → ℝ => F xstar s) '' (Set.univ : Set (Fin n → ℝ))) := by
    refine ⟨F xstar sstar, ?_⟩
    intro y hy
    rcases hy with ⟨s, -, rfl⟩
    exact hsmax' s
  have hsSup_eq :
      sSup ((fun s : Fin n → ℝ => F xstar s) '' (Set.univ : Set (Fin n → ℝ))) = F xstar sstar := by
    apply le_antisymm
    · refine csSup_le hsup_nonempty ?_
      intro y hy
      rcases hy with ⟨s, -, rfl⟩
      exact hsmax' s
    · exact le_csSup hsup_bdd ⟨sstar, by simp, rfl⟩
  have hleft' :
      sInf
          ((fun x =>
                sSup ((fun s : Fin n → ℝ => F x s) '' (Set.univ : Set (Fin n → ℝ)))) ''
            standardSimplex n) ≤
        F xstar sstar := by
    exact le_trans hleft (le_of_eq hsSup_eq)
  have hInf_eq :
      sInf ((fun x : Fin n → ℝ => F x sstar) '' standardSimplex n) = F xstar sstar := by
    apply le_antisymm
    · exact csInf_le (hbd_inf sstar) ⟨xstar, hxstar, rfl⟩
    · refine le_csInf ?_ ?_
      · exact ⟨F xstar sstar, ⟨xstar, hxstar, rfl⟩⟩
      · intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact hsmin' x hx
  have hbd_right :
      BddAbove
        ((fun s : Fin n → ℝ =>
              sInf ((fun x : Fin n → ℝ => F x s) '' standardSimplex n)) ''
          (Set.univ : Set (Fin n → ℝ))) := by
    refine ⟨F xstar sstar, ?_⟩
    intro y hy
    rcases hy with ⟨s, -, rfl⟩
    have hle : sInf ((fun x : Fin n → ℝ => F x s) '' standardSimplex n) ≤ F xstar s := by
      exact csInf_le (hbd_inf s) ⟨xstar, hxstar, rfl⟩
    exact hle.trans (hsmax' s)
  have hright :
      F xstar sstar ≤
        sSup
          ((fun s : Fin n → ℝ =>
                sInf ((fun x : Fin n → ℝ => F x s) '' standardSimplex n)) ''
            (Set.univ : Set (Fin n → ℝ))) := by
    have hmem :
        sInf ((fun x : Fin n → ℝ => F x sstar) '' standardSimplex n) ∈
          ((fun s : Fin n → ℝ =>
                sInf ((fun x : Fin n → ℝ => F x s) '' standardSimplex n)) ''
            (Set.univ : Set (Fin n → ℝ))) := by
      exact ⟨sstar, by simp, rfl⟩
    have hle :
        sInf ((fun x : Fin n → ℝ => F x sstar) '' standardSimplex n) ≤
          sSup
            ((fun s : Fin n → ℝ =>
                  sInf ((fun x : Fin n → ℝ => F x s) '' standardSimplex n)) ''
              (Set.univ : Set (Fin n → ℝ))) := le_csSup hbd_right hmem
    simpa [hInf_eq] using hle
  exact le_trans hleft' hright
