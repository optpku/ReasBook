/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import SmoothMinimization_Nesterov_2004.section05_part1

open scoped BigOperators

/-- A continuous objective attains its minimum on the finite simplex. -/
lemma simplexProximalValue_exists_primalMinimizer_fin (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ)
    (hn : 0 < n) :
    ∃ xstar ∈ standardSimplex n,
      IsMinOn
        (fun x =>
          (∑ i, gbar i * (x i - xbar i)) +
            (1 / 2 : ℝ) * L * (∑ i, |x i - xbar i|) ^ (2 : ℕ))
        (standardSimplex n) xstar := by
  classical
  let Φ : (Fin n → ℝ) → ℝ := fun x =>
    (∑ i, gbar i * (x i - xbar i)) +
      (1 / 2 : ℝ) * L * (∑ i, |x i - xbar i|) ^ (2 : ℕ)
  have hcont : Continuous Φ := by
    have hcont1 :
        Continuous (fun x : Fin n → ℝ => Finset.univ.sum (fun i => gbar i * (x i - xbar i))) := by
      classical
      refine continuous_finset_sum _ ?_
      intro i hi
      exact continuous_const.mul ((continuous_apply i).sub continuous_const)
    have hcont2 :
        Continuous (fun x : Fin n → ℝ => Finset.univ.sum (fun i => |x i - xbar i|)) := by
      classical
      refine continuous_finset_sum _ ?_
      intro i hi
      exact ((continuous_apply i).sub continuous_const).abs
    have hcont2' : Continuous (fun x : Fin n → ℝ => (∑ i, |x i - xbar i|) ^ (2 : ℕ)) :=
      hcont2.pow 2
    have hcont3 :
        Continuous (fun x : Fin n → ℝ =>
          ((1 / 2 : ℝ) * L) * (∑ i, |x i - xbar i|) ^ (2 : ℕ)) := by
      simpa using (continuous_const.mul hcont2')
    simpa [Φ, mul_assoc] using hcont1.add hcont3
  have hcompact : IsCompact (standardSimplex n) := by
    simpa [standardSimplex_eq_stdSimplex] using (isCompact_stdSimplex ℝ (ι := Fin n))
  have hne : (standardSimplex n).Nonempty := standardSimplex_nonempty_of_pos hn
  exact hcompact.exists_isMinOn hne hcont.continuousOn

/-- Moving mass between two coordinates preserves membership in the simplex. -/
lemma standardSimplex_mass_transfer_mem {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ standardSimplex n)
    {i j : Fin n} (hij : i ≠ j) {t : ℝ} (ht0 : 0 ≤ t) (htle : t ≤ x i) :
    (fun k =>
        if k = i then x k - t else if k = j then x k + t else x k) ∈
      standardSimplex n := by
  classical
  rcases hx with ⟨hxnonneg, hxsum⟩
  refine ⟨?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · subst hki
      simpa [hij, sub_eq_add_neg] using (sub_nonneg.mpr htle)
    · by_cases hkj : k = j
      · subst hkj
        simpa [hki] using (add_nonneg (hxnonneg k) ht0)
      · simpa [hki, hkj] using (hxnonneg k)
  · have hsum_delta :
        ∑ k, (if k = i then -t else if k = j then t else 0) = (-t) + t := by
      have hdelta :
          ∀ k,
            (if k = i then -t else if k = j then t else 0) =
              (if k = i then -t else 0) + (if k = j then t else 0) := by
        intro k
        by_cases hki : k = i
        · subst hki
          simp [hij]
        · by_cases hkj : k = j
          · subst hkj
            simp [hki]
          · simp [hki, hkj]
      calc
        ∑ k, (if k = i then -t else if k = j then t else 0) =
            ∑ k, ((if k = i then -t else 0) + (if k = j then t else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              simp [hdelta k]
        _ =
            (∑ k, (if k = i then -t else 0)) +
              ∑ k, (if k = j then t else 0) := by
              simpa using
                (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin n)))
                  (f := fun k => if k = i then -t else 0)
                  (g := fun k => if k = j then t else 0))
        _ = (-t) + t := by
              simp
    have hsum :
        ∑ k,
            (if k = i then x k - t else if k = j then x k + t else x k) =
          (∑ k, x k) + ∑ k, (if k = i then -t else if k = j then t else 0) := by
      have hpoint :
          ∀ k,
            (if k = i then x k - t else if k = j then x k + t else x k) =
              x k + (if k = i then -t else if k = j then t else 0) := by
        intro k
        by_cases hki : k = i
        · subst hki
          simp [sub_eq_add_neg]
        · by_cases hkj : k = j
          · subst hkj
            simp [hki]
          · simp [hki, hkj]
      calc
        ∑ k,
            (if k = i then x k - t else if k = j then x k + t else x k) =
            ∑ k, (x k + (if k = i then -t else if k = j then t else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              simp [hpoint k]
        _ = (∑ k, x k) + ∑ k, (if k = i then -t else if k = j then t else 0) := by
              simpa using
                (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin n)))
                  (f := fun k => x k)
                  (g := fun k => if k = i then -t else if k = j then t else 0))
    calc
      ∑ k,
          (if k = i then x k - t else if k = j then x k + t else x k) =
          (∑ k, x k) + ((-t) + t) := by
            simpa [hsum_delta] using hsum
      _ = (∑ k, x k) := by ring
      _ = (1 : ℝ) := hxsum

/-- Extract the linear coefficient from a nonnegative quadratic for small `t`. -/
lemma simplexProximalValue_small_t_linear_from_linear_quadratic {A B t0 : ℝ}
    (hB : 0 ≤ B) (ht0 : 0 < t0)
    (hineq : ∀ t, 0 < t → t ≤ t0 → 0 ≤ t * A + t ^ (2 : ℕ) * B) :
    0 ≤ A := by
  by_contra hA
  have hAneg : A < 0 := lt_of_not_ge hA
  have hApos : 0 < -A := by linarith
  have hdenpos : 0 < 2 * B + 1 := by linarith [hB]
  let t : ℝ := min t0 ((-A) / (2 * B + 1))
  have htpos : 0 < t := by
    have hpos' : 0 < (-A) / (2 * B + 1) := div_pos hApos hdenpos
    have : 0 < min t0 ((-A) / (2 * B + 1)) := (lt_min_iff).2 ⟨ht0, hpos'⟩
    simpa [t] using this
  have htle : t ≤ t0 := by
    simp [t]
  have htle' : t ≤ (-A) / (2 * B + 1) := by
    simp [t]
  have hineq_t := hineq t htpos htle
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  have hpos_div : 0 ≤ (-A) / (2 * B + 1) := le_of_lt (div_pos hApos hdenpos)
  have hB_le : B ≤ (2 * B + 1) / 2 := by linarith
  have hmul1 :
      (-A) / (2 * B + 1) * B ≤ (-A) / (2 * B + 1) * ((2 * B + 1) / 2) :=
    mul_le_mul_of_nonneg_left hB_le hpos_div
  have hmul1' :
      (-A) / (2 * B + 1) * ((2 * B + 1) / 2) = (-A) / 2 := by
    have hdenpos' : (2 * B + 1) ≠ 0 := ne_of_gt hdenpos
    field_simp [hdenpos']
  have hmul1'' : (-A) / (2 * B + 1) * B ≤ (-A) / 2 := by
    simpa [hmul1'] using hmul1
  have hmul2 : t * B ≤ (-A) / 2 := by
    have hmul0 : t * B ≤ (-A) / (2 * B + 1) * B :=
      mul_le_mul_of_nonneg_right htle' hB
    exact hmul0.trans hmul1''
  have hmul3 : t ^ (2 : ℕ) * B ≤ t * ((-A) / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hmul2 ht_nonneg
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hlt : t * A + t ^ (2 : ℕ) * B < 0 := by
    have hle :
        t * A + t ^ (2 : ℕ) * B ≤ t * A + t * ((-A) / 2) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left hmul3 (t * A))
    have hAhalf : A / 2 < 0 := by linarith [hAneg]
    have hlt' : t * A + t * ((-A) / 2) < 0 := by
      have : t * (A / 2) < 0 := mul_neg_of_pos_of_neg htpos hAhalf
      have hrewrite : t * A + t * ((-A) / 2) = t * (A / 2) := by
        ring
      simpa [hrewrite] using this
    exact lt_of_le_of_lt hle hlt'
  exact (not_le_of_gt hlt) hineq_t

/-- Primal optimality yields a transfer inequality between coordinates. -/
lemma simplexProximalValue_primal_optimality_transfer_ineq (n : ℕ) (xbar gbar xstar : Fin n → ℝ)
    (L : ℝ) (hL : 0 < L) (hxstar : xstar ∈ standardSimplex n)
    (hxmin :
      IsMinOn
        (fun x =>
          (∑ i, gbar i * (x i - xbar i)) +
            (1 / 2 : ℝ) * L * (∑ i, |x i - xbar i|) ^ (2 : ℕ))
        (standardSimplex n) xstar)
    {i j : Fin n} (hpos : 0 < xstar i) :
    let h : Fin n → ℝ := fun k => xstar k - xbar k
    let a : ℝ := ∑ k, |h k|
    gbar i + L * a * simplexProximalValue_signMinus (h i) ≤
      gbar j + L * a * simplexProximalValue_signPlus (h j) := by
  classical
  let Φ : (Fin n → ℝ) → ℝ := fun x =>
    (∑ k, gbar k * (x k - xbar k)) +
      (1 / 2 : ℝ) * L * (∑ k, |x k - xbar k|) ^ (2 : ℕ)
  let h : Fin n → ℝ := fun k => xstar k - xbar k
  let a : ℝ := ∑ k, |h k|
  by_cases hij : i = j
  · subst hij
    have ha_nonneg : 0 ≤ a := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hLa_nonneg : 0 ≤ L * a := mul_nonneg (le_of_lt hL) ha_nonneg
    have hsign : simplexProximalValue_signMinus (h i) ≤ simplexProximalValue_signPlus (h i) := by
      by_cases hpos' : 0 < h i
      · have hnotneg : ¬ h i < 0 := by linarith
        have hsm : simplexProximalValue_signMinus (h i) = 1 := by
          simp [simplexProximalValue_signMinus, hpos']
        have hsp : simplexProximalValue_signPlus (h i) = 1 := by
          simp [simplexProximalValue_signPlus, hnotneg]
        linarith [hsm, hsp]
      · by_cases hneg' : h i < 0
        · have hsm : simplexProximalValue_signMinus (h i) = -1 := by
            simp [simplexProximalValue_signMinus, hpos']
          have hsp : simplexProximalValue_signPlus (h i) = -1 := by
            simp [simplexProximalValue_signPlus, hneg']
          linarith [hsm, hsp]
        · have hzero : h i = 0 := by linarith
          have hsm : simplexProximalValue_signMinus (h i) = -1 := by
            simp [simplexProximalValue_signMinus, hzero]
          have hsp : simplexProximalValue_signPlus (h i) = 1 := by
            simp [simplexProximalValue_signPlus, hzero]
          linarith [hsm, hsp]
    have hmul :
        L * a * simplexProximalValue_signMinus (h i) ≤
          L * a * simplexProximalValue_signPlus (h i) :=
      mul_le_mul_of_nonneg_left hsign hLa_nonneg
    linarith
  · let Δ : ℝ :=
      simplexProximalValue_signPlus (h j) - simplexProximalValue_signMinus (h i)
    let A : ℝ := gbar j - gbar i + L * a * Δ
    let B : ℝ := (1 / 2 : ℝ) * L * Δ ^ (2 : ℕ)
    let t0 : ℝ :=
      min (xstar i)
        (min (if 0 < h i then h i else xstar i) (if h j < 0 then -h j else xstar i))
    have ht0_pos : 0 < t0 := by
      have hpos_hi :
          0 < (if 0 < h i then h i else xstar i) := by
        by_cases hhi : 0 < h i
        · simp [hhi]
        · simp [hhi, hpos]
      have hpos_hj :
          0 < (if h j < 0 then -h j else xstar i) := by
        by_cases hhj : h j < 0
        · have hneg : 0 < -h j := by linarith
          simp [hhj, hneg]
        · simp [hhj, hpos]
      have : 0 < min (xstar i)
          (min (if 0 < h i then h i else xstar i) (if h j < 0 then -h j else xstar i)) := by
        refine (lt_min_iff).2 ?_
        refine ⟨hpos, ?_⟩
        exact (lt_min_iff).2 ⟨hpos_hi, hpos_hj⟩
      simpa [t0] using this
    have hineq :
        ∀ t, 0 < t → t ≤ t0 → 0 ≤ t * A + t ^ (2 : ℕ) * B := by
      intro t htpos htle
      have ht_nonneg : 0 ≤ t := le_of_lt htpos
      have htle_xstar : t ≤ xstar i := by
        have ht0_le : t0 ≤ xstar i := by
          simp [t0]
        exact le_trans htle ht0_le
      have htle_hi : 0 < h i → t ≤ h i := by
        intro hhi
        have ht0_le :
            t0 ≤ min (h i) (if h j < 0 then -h j else xstar i) := by
          simp [t0, hhi]
        have ht0_le' : t0 ≤ h i := by
          exact le_trans ht0_le (min_le_left _ _)
        exact le_trans htle ht0_le'
      have htle_hj : h j < 0 → t ≤ -h j := by
        intro hhj
        have ht0_le :
            t0 ≤ min (if 0 < h i then h i else xstar i) (-h j) := by
          simp [t0, hhj]
        have ht0_le' : t0 ≤ -h j := by
          exact le_trans ht0_le (min_le_right _ _)
        exact le_trans htle ht0_le'
      let x' : Fin n → ℝ := fun k =>
        if k = i then xstar k - t else if k = j then xstar k + t else xstar k
      have hx' : x' ∈ standardSimplex n := by
        refine standardSimplex_mass_transfer_mem (hx := hxstar) (i := i) (j := j) hij
          (ht0 := ht_nonneg) ?_
        exact htle_xstar
      have hmin : Φ xstar ≤ Φ x' := (isMinOn_iff).1 hxmin x' hx'
      have hlin :
          ∑ k, gbar k * (x' k - xbar k) =
            (∑ k, gbar k * h k) + t * (gbar j - gbar i) := by
        have hpoint :
            ∀ k,
              gbar k * (x' k - xbar k) =
                gbar k * h k + gbar k *
                  (if k = i then -t else if k = j then t else 0) := by
          intro k
          by_cases hki : k = i
          · subst hki
            simp [x', h, sub_eq_add_neg, add_comm, mul_add, mul_comm]
            ring_nf
          · by_cases hkj : k = j
            · subst hkj
              simp [x', h, hki, sub_eq_add_neg, add_comm, add_assoc, mul_add, mul_comm]
            · simp [x', h, hki, hkj, sub_eq_add_neg, add_comm, mul_add, mul_comm]
        have hsum :
            ∑ k, gbar k * (x' k - xbar k) =
              ∑ k, (gbar k * h k +
                gbar k * (if k = i then -t else if k = j then t else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [hpoint k]
        have hsum' :
            ∑ k, (gbar k * h k +
                gbar k * (if k = i then -t else if k = j then t else 0)) =
              (∑ k, gbar k * h k) +
                ∑ k, gbar k * (if k = i then -t else if k = j then t else 0) := by
          simpa using
            (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin n)))
              (f := fun k => gbar k * h k)
              (g := fun k => gbar k * (if k = i then -t else if k = j then t else 0)))
        have hsum_delta :
            ∑ k, gbar k * (if k = i then -t else if k = j then t else 0) =
              gbar i * (-t) + gbar j * t := by
          classical
          have hdelta :
              ∀ k,
                gbar k * (if k = i then -t else if k = j then t else 0) =
                  (if k = i then gbar k * (-t) else 0) +
                    (if k = j then gbar k * t else 0) := by
            intro k
            by_cases hki : k = i
            · subst hki
              simp [hij]
            · by_cases hkj : k = j
              · subst hkj
                simp [hki]
              · simp [hki, hkj]
          calc
            ∑ k, gbar k * (if k = i then -t else if k = j then t else 0) =
                ∑ k, ((if k = i then gbar k * (-t) else 0) +
                  (if k = j then gbar k * t else 0)) := by
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  simp [hdelta k]
            _ =
                (∑ k, if k = i then gbar k * (-t) else 0) +
                  ∑ k, if k = j then gbar k * t else 0 := by
                  simpa using
                    (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin n)))
                      (f := fun k => if k = i then gbar k * (-t) else 0)
                      (g := fun k => if k = j then gbar k * t else 0))
            _ = gbar i * (-t) + gbar j * t := by
                  simp
        calc
          ∑ k, gbar k * (x' k - xbar k) =
              (∑ k, gbar k * h k) +
                ∑ k, gbar k * (if k = i then -t else if k = j then t else 0) := by
              simpa [hsum] using hsum'
          _ = (∑ k, gbar k * h k) + (gbar i * (-t) + gbar j * t) := by
              rw [hsum_delta]
          _ = (∑ k, gbar k * h k) + t * (gbar j - gbar i) := by
              ring
      have habs :
          ∑ k, |x' k - xbar k| =
            a + t * (simplexProximalValue_signPlus (h j) -
              simplexProximalValue_signMinus (h i)) := by
        have hpoint :
            ∀ k,
              |x' k - xbar k| =
                |h k| +
                  (if k = i then |h i - t| - |h i|
                    else if k = j then |h j + t| - |h j| else 0) := by
          intro k
          by_cases hki : k = i
          · subst hki
            simp [x', h, sub_eq_add_neg]
            ring_nf
          · by_cases hkj : k = j
            · subst hkj
              simp [x', h, hki, sub_eq_add_neg]
              ring_nf
            · simp [x', h, hki, hkj]
        have hsum :
            ∑ k, |x' k - xbar k| =
              ∑ k, (|h k| +
                (if k = i then |h i - t| - |h i|
                  else if k = j then |h j + t| - |h j| else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [hpoint k]
        have hsum' :
            ∑ k, (|h k| +
                (if k = i then |h i - t| - |h i|
                  else if k = j then |h j + t| - |h j| else 0)) =
              (∑ k, |h k|) +
                ∑ k, (if k = i then |h i - t| - |h i|
                  else if k = j then |h j + t| - |h j| else 0) := by
          simpa using
            (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin n)))
              (f := fun k => |h k|)
              (g := fun k =>
                if k = i then |h i - t| - |h i|
                else if k = j then |h j + t| - |h j| else 0))
        have hsum_delta :
            ∑ k, (if k = i then |h i - t| - |h i|
                else if k = j then |h j + t| - |h j| else 0) =
              (|h i - t| - |h i|) + (|h j + t| - |h j|) := by
          classical
          have hdelta :
              ∀ k,
                (if k = i then |h i - t| - |h i|
                  else if k = j then |h j + t| - |h j| else 0) =
                  (if k = i then |h i - t| - |h i| else 0) +
                    (if k = j then |h j + t| - |h j| else 0) := by
            intro k
            by_cases hki : k = i
            · subst hki
              simp [hij]
            · by_cases hkj : k = j
              · subst hkj
                simp [hki]
              · simp [hki, hkj]
          calc
            ∑ k, (if k = i then |h i - t| - |h i|
                else if k = j then |h j + t| - |h j| else 0) =
                ∑ k, ((if k = i then |h i - t| - |h i| else 0) +
                  (if k = j then |h j + t| - |h j| else 0)) := by
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  simp [hdelta k]
            _ =
                (∑ k, if k = i then |h i - t| - |h i| else 0) +
                  ∑ k, if k = j then |h j + t| - |h j| else 0 := by
                  simpa using
                    (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin n)))
                      (f := fun k => if k = i then |h i - t| - |h i| else 0)
                      (g := fun k => if k = j then |h j + t| - |h j| else 0))
            _ = (|h i - t| - |h i|) + (|h j + t| - |h j|) := by
                  simp
        have hsub :
            |h i - t| = |h i| - simplexProximalValue_signMinus (h i) * t := by
          refine simplexProximalValue_abs_sub_oneSided (z := h i) (t := t) ht_nonneg ?_
          exact htle_hi
        have hadd :
            |h j + t| = |h j| + simplexProximalValue_signPlus (h j) * t := by
          refine simplexProximalValue_abs_add_oneSided (z := h j) (t := t) ht_nonneg ?_
          exact htle_hj
        have hdelta :
            (|h i - t| - |h i|) + (|h j + t| - |h j|) =
              t * (simplexProximalValue_signPlus (h j) -
                simplexProximalValue_signMinus (h i)) := by
          have hsub' : |h i - t| - |h i| = -simplexProximalValue_signMinus (h i) * t := by
            linarith [hsub]
          have hadd' : |h j + t| - |h j| = simplexProximalValue_signPlus (h j) * t := by
            linarith [hadd]
          calc
            (|h i - t| - |h i|) + (|h j + t| - |h j|) =
                (-simplexProximalValue_signMinus (h i) * t) +
                  (simplexProximalValue_signPlus (h j) * t) := by
                simp [hsub', hadd']
            _ = t * (simplexProximalValue_signPlus (h j) -
                  simplexProximalValue_signMinus (h i)) := by ring
        calc
          ∑ k, |x' k - xbar k| =
              (∑ k, |h k|) +
                ∑ k, (if k = i then |h i - t| - |h i|
                  else if k = j then |h j + t| - |h j| else 0) := by
                simpa [hsum] using hsum'
          _ = (∑ k, |h k|) + ((|h i - t| - |h i|) + (|h j + t| - |h j|)) := by
                simp [hsum_delta]
          _ = a + t * (simplexProximalValue_signPlus (h j) -
                simplexProximalValue_signMinus (h i)) := by
                simp [a, hdelta]
      have hdiff :
          Φ x' - Φ xstar = t * A + t ^ (2 : ℕ) * B := by
        have hphi_x' :
            Φ x' =
              (∑ k, gbar k * h k) + t * (gbar j - gbar i) +
                (1 / 2 : ℝ) * L * (a +
                  t * (simplexProximalValue_signPlus (h j) -
                    simplexProximalValue_signMinus (h i))) ^ (2 : ℕ) := by
          simp [Φ, hlin, habs, a, h, add_comm, add_left_comm, mul_assoc]
        have hphi_xstar :
            Φ xstar = (∑ k, gbar k * h k) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
          simp [Φ, h, a]
        calc
          Φ x' - Φ xstar =
              ((∑ k, gbar k * h k) + t * (gbar j - gbar i) +
                (1 / 2 : ℝ) * L *
                  (a + t * (simplexProximalValue_signPlus (h j) -
                    simplexProximalValue_signMinus (h i))) ^ (2 : ℕ)) -
                ((∑ k, gbar k * h k) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ)) := by
              simp [hphi_x', hphi_xstar]
          _ = t * A + t ^ (2 : ℕ) * B := by
              simp [A, B, Δ]
              ring
      have hnonneg : 0 ≤ Φ x' - Φ xstar := by linarith
      simpa [hdiff] using hnonneg
    have hB_nonneg : 0 ≤ B := by
      have hΔ_nonneg : 0 ≤ Δ ^ (2 : ℕ) := by
        simpa [pow_two] using (sq_nonneg Δ)
      have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
      exact mul_nonneg (mul_nonneg hhalf_nonneg (le_of_lt hL)) hΔ_nonneg
    have hA_nonneg :=
      simplexProximalValue_small_t_linear_from_linear_quadratic (A := A) (B := B) (t0 := t0)
        hB_nonneg ht0_pos hineq
    linarith [hA_nonneg]

/-- A maximizer for the finite `l1`/`l∞` quadratic payoff,
allowing free coordinates when `h i = 0`. -/
lemma dot_l1Quadratic_argmax_fin_with_free_zero_coords (n : ℕ) (g h sstar : Fin n → ℝ)
    (L : ℝ) (hL : 0 < L)
    (hmatch : ∀ i, h i ≠ 0 → sstar i = L * (∑ i, |h i|) * Real.sign (h i))
    (hbound : ∀ i, |sstar i| ≤ L * (∑ i, |h i|)) :
    ∀ s : Fin n → ℝ,
      (∑ i, (g i + s i) * h i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) ≤
        (∑ i, (g i + sstar i) * h i) - (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) := by
  classical
  let a : ℝ := ∑ i, |h i|
  let Φ : (Fin n → ℝ) → ℝ := fun s =>
    (∑ i, (g i + s i) * h i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)
  have hsum :
      ∀ s : Fin n → ℝ,
        ∑ i, (g i + s i) * h i = (∑ i, g i * h i) + ∑ i, s i * h i := by
    intro s
    calc
      ∑ i, (g i + s i) * h i = ∑ i, (g i * h i + s i * h i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [add_mul]
      _ = (∑ i, g i * h i) + ∑ i, s i * h i := by
        simpa using
          (Finset.sum_add_distrib (s := Finset.univ)
            (f := fun i => g i * h i) (g := fun i => s i * h i))
  have hsum_star : ∑ i, sstar i * h i = L * a * a := by
    have hsum' :
        ∑ i, sstar i * h i = ∑ i, L * a * (Real.sign (h i) * h i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hi0 : h i = 0
      · simp [hi0]
      · have hdef := hmatch i hi0
        have hdef' : sstar i = L * a * Real.sign (h i) := by
          simpa [a, mul_assoc, mul_left_comm, mul_comm] using hdef
        calc
          sstar i * h i = (L * a * Real.sign (h i)) * h i := by simp [hdef']
          _ = L * a * (Real.sign (h i) * h i) := by ring
    have hsum_sign : ∑ i, Real.sign (h i) * h i = a := by
      have hsum'' : ∑ i, Real.sign (h i) * h i = ∑ i, |h i| := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [sign_mul_eq_abs]
      simpa [a] using hsum''
    calc
      ∑ i, sstar i * h i = ∑ i, L * a * (Real.sign (h i) * h i) := hsum'
      _ = (L * a) * ∑ i, Real.sign (h i) * h i := by
            symm
            simpa using
              (Finset.mul_sum (a := L * a) (s := Finset.univ)
                (f := fun i => Real.sign (h i) * h i))
      _ = L * a * a := by
            simp [hsum_sign, mul_assoc]
  have hnorm_star : ‖sstar‖ = L * a := by
    have ha_nonneg : 0 ≤ a := Finset.sum_nonneg (fun i hi => abs_nonneg _)
    have hLa_nonneg : 0 ≤ L * a := mul_nonneg (le_of_lt hL) ha_nonneg
    have hnorm_le : ‖sstar‖ ≤ L * a := by
      refine (pi_norm_le_iff_of_nonneg hLa_nonneg).2 ?_
      intro i
      simpa [Real.norm_eq_abs, a] using (hbound i)
    by_cases ha : a = 0
    · have hzero : sstar = 0 := by
        funext i
        have hle : |sstar i| ≤ 0 := by simpa [a, ha] using (hbound i)
        have h0 : |sstar i| = 0 := le_antisymm hle (abs_nonneg _)
        simpa using (abs_eq_zero.mp h0)
      simp [hzero, ha]
    · have hex : ∃ i, h i ≠ 0 := by
        by_contra hzero
        have hzero' : ∀ i, h i = 0 := by
          intro i
          by_contra hi
          exact hzero ⟨i, hi⟩
        have hsum0 : a = 0 := by simp [a, hzero']
        exact ha hsum0
      rcases hex with ⟨i0, hi0⟩
      have hsign_abs : |Real.sign (h i0)| = 1 := by
        rcases Real.sign_apply_eq_of_ne_zero (h i0) hi0 with hneg | hpos
        · simp [hneg]
        · simp [hpos]
      have hcoord : |sstar i0| = L * a := by
        have hdef := hmatch i0 hi0
        have hdef' : sstar i0 = L * a * Real.sign (h i0) := by
          simpa [a, mul_assoc, mul_left_comm, mul_comm] using hdef
        have hLa : |L * a| = L * a := abs_of_nonneg hLa_nonneg
        calc
          |sstar i0| = |L * a| * |Real.sign (h i0)| := by
            simp [hdef', abs_mul, mul_left_comm, mul_comm]
          _ = |L * a| := by simp [hsign_abs]
          _ = L * a := hLa
      have hle : L * a ≤ ‖sstar‖ := by
        have hle' : |sstar i0| ≤ ‖sstar‖ := by
          simpa using (norm_le_pi_norm (f := sstar) i0)
        simpa [hcoord] using hle'
      exact le_antisymm hnorm_le hle
  have hval :
      Φ sstar = (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
    have hL' : L ≠ 0 := by linarith
    calc
      Φ sstar =
          (∑ i, g i * h i) + (∑ i, sstar i * h i) -
            (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) := by
            simp [Φ, hsum, sub_eq_add_neg, add_assoc]
      _ = (∑ i, g i * h i) + (L * a * a) -
            (1 / (2 * L)) * (L * a) ^ (2 : ℕ) := by
            simp [hsum_star, hnorm_star]
      _ = (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
            field_simp [hL']
            ring
  have hsup :
      (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) =
        sSup (Φ '' (Set.univ : Set (Fin n → ℝ))) := by
    simpa [Φ, a] using
      (dot_l1Quadratic_eq_sSup_linf_fin (n := n) (g := g) (h := h) (L := L) hL)
  have hsup_eq :
      sSup (Φ '' (Set.univ : Set (Fin n → ℝ))) = Φ sstar := by
    calc
      sSup (Φ '' (Set.univ : Set (Fin n → ℝ))) =
          (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
            simpa using hsup.symm
      _ = Φ sstar := by simp [hval]
  intro s
  have hsum_le : ∑ i, s i * h i ≤ ‖s‖ * a :=
    sum_mul_le_norm_sum_abs (n := n) s h
  have hquad :
      ‖s‖ * a - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * L * a ^ (2 : ℕ) :=
    quadratic_bound (r := ‖s‖) (a := a) (L := L) hL
  have hpoint : Φ s ≤ (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
    have htmp :
        ∑ i, s i * h i - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
      linarith [hsum_le, hquad]
    calc
      Φ s = (∑ i, g i * h i) + (∑ i, s i * h i - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) := by
            simp [Φ, hsum s, sub_eq_add_neg, add_assoc]
      _ ≤ (∑ i, g i * h i) + (1 / 2 : ℝ) * L * a ^ (2 : ℕ) := by
            linarith
  have hle' : Φ s ≤ Φ sstar := by
    simpa [hval] using hpoint
  simpa [Φ] using hle'

/-- One-sided signs agree with `Real.sign` away from zero (right derivative). -/
lemma simplexProximalValue_signPlus_eq_real_sign_of_ne_zero {z : ℝ} (hz : z ≠ 0) :
    simplexProximalValue_signPlus z = Real.sign z := by
  by_cases hzneg : z < 0
  · simp [simplexProximalValue_signPlus, hzneg, Real.sign_of_neg hzneg]
  · have hzpos : 0 < z := lt_of_le_of_ne (le_of_not_gt hzneg) (Ne.symm hz)
    simp [simplexProximalValue_signPlus, hzneg, Real.sign_of_pos hzpos]

/-- One-sided signs agree with `Real.sign` away from zero (left derivative). -/
lemma simplexProximalValue_signMinus_eq_real_sign_of_ne_zero {z : ℝ} (hz : z ≠ 0) :
    simplexProximalValue_signMinus z = Real.sign z := by
  by_cases hzpos : 0 < z
  · simp [simplexProximalValue_signMinus, hzpos, Real.sign_of_pos hzpos]
  · have hzneg : z < 0 := lt_of_le_of_ne (le_of_not_gt hzpos) hz
    simp [simplexProximalValue_signMinus, hzpos, Real.sign_of_neg hzneg]

/-- Build a dual maximizer with coefficients constant on the simplex support. -/
lemma simplexProximalValue_exists_sstar_support_constant (n : ℕ) (xbar gbar xstar : Fin n → ℝ)
    (L : ℝ) (hL : 0 < L) (hxstar : xstar ∈ standardSimplex n)
    (hxmin :
      IsMinOn
        (fun x =>
          (∑ i, gbar i * (x i - xbar i)) +
            (1 / 2 : ℝ) * L * (∑ i, |x i - xbar i|) ^ (2 : ℕ))
        (standardSimplex n) xstar) :
    let h : Fin n → ℝ := fun i => xstar i - xbar i
    let a : ℝ := ∑ i, |h i|
    ∃ c : ℝ, ∃ sstar : Fin n → ℝ,
      (∀ i, h i ≠ 0 → sstar i = L * a * Real.sign (h i)) ∧
      (∀ i, |sstar i| ≤ L * a) ∧
      (∀ i, 0 < xstar i → gbar i + sstar i = c) ∧
      (∀ i, c ≤ gbar i + sstar i) := by
  classical
  let h : Fin n → ℝ := fun i => xstar i - xbar i
  let a : ℝ := ∑ i, |h i|
  have ha_nonneg : 0 ≤ a := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hLa_nonneg : 0 ≤ L * a := mul_nonneg (le_of_lt hL) ha_nonneg
  have hexpos : ∃ i, 0 < xstar i := by
    by_contra hnone
    have hzero : ∀ i, xstar i = 0 := by
      intro i
      have hle : xstar i ≤ 0 := by
        by_contra hpos'
        have : 0 < xstar i := lt_of_not_ge hpos'
        exact hnone ⟨i, this⟩
      exact le_antisymm hle (hxstar.1 i)
    have hsum0 : ∑ i, xstar i = 0 := by simp [hzero]
    linarith [hxstar.2, hsum0]
  let I : Finset (Fin n) := Finset.univ.filter (fun i => 0 < xstar i)
  have hI_nonempty : I.Nonempty := by
    rcases hexpos with ⟨i, hpos⟩
    refine ⟨i, ?_⟩
    simp [I, hpos]
  let ℓ : Fin n → ℝ := fun i => gbar i + L * a * simplexProximalValue_signMinus (h i)
  let u : Fin n → ℝ := fun i => gbar i + L * a * simplexProximalValue_signPlus (h i)
  let c : ℝ := I.sup' hI_nonempty ℓ
  have htransfer : ∀ i, 0 < xstar i → ∀ j, ℓ i ≤ u j := by
    intro i hpos j
    have hineq :=
      simplexProximalValue_primal_optimality_transfer_ineq (n := n) (xbar := xbar)
        (gbar := gbar) (xstar := xstar) (L := L) hL hxstar hxmin (i := i) (j := j) hpos
    simpa [h, a, ℓ, u] using hineq
  have hcle : ∀ j, c ≤ u j := by
    intro j
    have hsup : I.sup' hI_nonempty ℓ ≤ u j := by
      refine (Finset.sup'_le_iff (s := I) (H := hI_nonempty) (f := ℓ) (a := u j)).2 ?_
      intro i hi
      have hpos : 0 < xstar i := by
        simpa [I] using hi
      exact htransfer i hpos j
    simpa [c] using hsup
  let sstar : Fin n → ℝ := fun i =>
    if h i ≠ 0 then L * a * Real.sign (h i) else max (-L * a) (min (c - gbar i) (L * a))
  have hmatch : ∀ i, h i ≠ 0 → sstar i = L * a * Real.sign (h i) := by
    intro i hi
    simp [sstar, hi]
  have hbound : ∀ i, |sstar i| ≤ L * a := by
    intro i
    by_cases hi0 : h i = 0
    · have hupper : sstar i ≤ L * a := by
        have h1 : min (c - gbar i) (L * a) ≤ L * a := min_le_right _ _
        have h2 : -L * a ≤ L * a := by linarith [hLa_nonneg]
        have hmax : max (-L * a) (min (c - gbar i) (L * a)) ≤ L * a :=
          max_le_iff.mpr ⟨h2, h1⟩
        simpa [sstar, hi0] using hmax
      have hlower : -(L * a) ≤ sstar i := by
        simp [sstar, hi0]
      exact (abs_le.mpr ⟨hlower, hupper⟩)
    · have hsign_abs : |Real.sign (h i)| = 1 := by
        rcases Real.sign_apply_eq_of_ne_zero (h i) hi0 with hneg | hpos
        · simp [hneg]
        · simp [hpos]
      have habs : |sstar i| = |L * a| * |Real.sign (h i)| := by
        simp [sstar, hi0, abs_mul, mul_left_comm, mul_comm]
      have hEq : |sstar i| = L * a := by
        calc
          |sstar i| = |L * a| * |Real.sign (h i)| := habs
          _ = |L * a| := by simp [hsign_abs]
          _ = L * a := by simp [abs_of_nonneg hLa_nonneg]
      exact le_of_eq hEq
  have hle_c : ∀ i, 0 < xstar i → ℓ i ≤ c := by
    intro i hpos
    have hi_mem : i ∈ I := by
      simp [I, hpos]
    have hle : ℓ i ≤ I.sup' hI_nonempty ℓ := by
      exact Finset.le_sup' (s := I) (f := ℓ) hi_mem
    simpa [c] using hle
  have hconst : ∀ i, 0 < xstar i → gbar i + sstar i = c := by
    intro i hpos
    by_cases hi0 : h i = 0
    · have hℓ : ℓ i ≤ c := hle_c i hpos
      have hc : c ≤ u i := hcle i
      have hℓ' : gbar i - L * a ≤ c := by
        simpa [ℓ, simplexProximalValue_signMinus, hi0, sub_eq_add_neg] using hℓ
      have hc' : c ≤ gbar i + L * a := by
        simpa [u, simplexProximalValue_signPlus, hi0] using hc
      have hbetween1 : -L * a ≤ c - gbar i := by
        linarith [hℓ']
      have hbetween2 : c - gbar i ≤ L * a := by
        linarith [hc']
      have hbetween : -L * a ≤ c - gbar i ∧ c - gbar i ≤ L * a := ⟨hbetween1, hbetween2⟩
      have hmin : min (c - gbar i) (L * a) = c - gbar i := by
        exact min_eq_left hbetween.2
      have hmax : max (-(L * a)) (c - gbar i) = c - gbar i := by
        have hbetween1' : -(L * a) ≤ c - gbar i := by
          linarith [hbetween1]
        exact max_eq_right hbetween1'
      have hsstar : sstar i = c - gbar i := by
        have hs1 : sstar i = max (-L * a) (min (c - gbar i) (L * a)) := by
          simp [sstar, hi0]
        have hs2 : sstar i = max (-L * a) (c - gbar i) := by
          simpa [hmin] using hs1
        simpa [hmax] using hs2
      calc
        gbar i + sstar i = gbar i + (c - gbar i) := by simp [hsstar]
        _ = c := by ring
    · have hℓ : ℓ i ≤ c := hle_c i hpos
      have hc : c ≤ u i := hcle i
      have hminus : simplexProximalValue_signMinus (h i) = Real.sign (h i) :=
        simplexProximalValue_signMinus_eq_real_sign_of_ne_zero hi0
      have hplus : simplexProximalValue_signPlus (h i) = Real.sign (h i) :=
        simplexProximalValue_signPlus_eq_real_sign_of_ne_zero hi0
      have hℓu : ℓ i = u i := by
        simp [ℓ, u, hminus, hplus]
      have hc_le : c ≤ ℓ i := by
        simpa [hℓu] using hc
      have hceq : c = ℓ i := le_antisymm hc_le hℓ
      have hsstar : sstar i = L * a * Real.sign (h i) := hmatch i hi0
      calc
        gbar i + sstar i = gbar i + L * a * Real.sign (h i) := by simp [hsstar]
        _ = gbar i + L * a * simplexProximalValue_signMinus (h i) := by simp [hminus]
        _ = ℓ i := by simp [ℓ]
        _ = c := by simp [hceq]
  have hboundR : ∀ i, c ≤ gbar i + sstar i := by
    intro i
    by_cases hi0 : h i = 0
    · have hc : c ≤ u i := hcle i
      have hc' : c ≤ gbar i + L * a := by
        simpa [u, simplexProximalValue_signPlus, hi0] using hc
      have hmin : min (c - gbar i) (L * a) = c - gbar i := by
        have : c - gbar i ≤ L * a := by linarith
        exact min_eq_left this
      have hle : c - gbar i ≤ sstar i := by
        simp [sstar, hi0, hmin]
      have := add_le_add_left hle (gbar i)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    · have hc : c ≤ u i := hcle i
      have hplus : simplexProximalValue_signPlus (h i) = Real.sign (h i) :=
        simplexProximalValue_signPlus_eq_real_sign_of_ne_zero hi0
      have hsstar : sstar i = L * a * Real.sign (h i) := hmatch i hi0
      have : c ≤ gbar i + L * a * Real.sign (h i) := by
        simpa [u, hplus] using hc
      simpa [hsstar] using this
  exact ⟨c, sstar, hmatch, hbound, hconst, hboundR⟩

/-- If the linear coefficients are constant on the support and bounded below,
the support minimizes. -/
lemma simplex_linear_min_support_constant (n : ℕ) {xstar r : Fin n → ℝ} {c : ℝ}
    (hxstar : xstar ∈ standardSimplex n)
    (hconst : ∀ i, 0 < xstar i → r i = c)
    (hbound : ∀ i, c ≤ r i) :
    ∀ x ∈ standardSimplex n, ∑ i, r i * xstar i ≤ ∑ i, r i * x i := by
  classical
  intro x hx
  have hxnonneg : ∀ i, 0 ≤ x i := hx.1
  have hxsum : ∑ i, x i = 1 := hx.2
  have hxstarnonneg : ∀ i, 0 ≤ xstar i := hxstar.1
  have hxstarsum : ∑ i, xstar i = 1 := hxstar.2
  have hcoeff : ∀ i, r i * xstar i = c * xstar i := by
    intro i
    by_cases hpos : 0 < xstar i
    · have hr : r i = c := hconst i hpos
      simp [hr]
    · have hxzero : xstar i = 0 := by
        have hle : xstar i ≤ 0 := le_of_not_gt hpos
        exact le_antisymm hle (hxstarnonneg i)
      simp [hxzero]
  have hsum_xstar : ∑ i, r i * xstar i = c := by
    calc
      ∑ i, r i * xstar i = ∑ i, c * xstar i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hcoeff i
      _ = c * ∑ i, xstar i := by
            simpa using
              (Finset.mul_sum (a := c) (s := Finset.univ) (f := fun i => xstar i)).symm
      _ = c := by simp [hxstarsum]
  have hsum_ge : c ≤ ∑ i, r i * x i := by
    have hsum_eq : c * ∑ i, x i = ∑ i, c * x i := by
      simpa using
        (Finset.mul_sum (a := c) (s := Finset.univ) (f := fun i => x i))
    have hterm_le : ∀ i, c * x i ≤ r i * x i := by
      intro i
      have hci : c ≤ r i := hbound i
      exact mul_le_mul_of_nonneg_right hci (hxnonneg i)
    have hsum_le : ∑ i, c * x i ≤ ∑ i, r i * x i := by
      exact Finset.sum_le_sum (fun i hi => hterm_le i)
    have hsum_le' : c * ∑ i, x i ≤ ∑ i, r i * x i := by
      exact le_trans (le_of_eq hsum_eq) hsum_le
    simpa [hxsum] using hsum_le'
  calc
    ∑ i, r i * xstar i = c := hsum_xstar
    _ ≤ ∑ i, r i * x i := hsum_ge

/-- Reduce the simplex best-response to a linear minimization over the support. -/
lemma simplexProximalValue_saddlePoint_fin_hsmin (n : ℕ) (xbar xstar r : Fin n → ℝ) {c : ℝ}
    (hxstar : xstar ∈ standardSimplex n)
    (hconst : ∀ i, 0 < xstar i → r i = c)
    (hbound : ∀ i, c ≤ r i) :
    ∀ x ∈ standardSimplex n,
      ∑ i, r i * (xstar i - xbar i) ≤ ∑ i, r i * (x i - xbar i) := by
  classical
  intro x hx
  have hlin :=
    simplex_linear_min_support_constant (n := n) (xstar := xstar) (r := r) (c := c)
      hxstar hconst hbound x hx
  have hsum :
      ∀ y : Fin n → ℝ,
        ∑ i, r i * (y i - xbar i) = (∑ i, r i * y i) - ∑ i, r i * xbar i := by
    intro y
    calc
      ∑ i, r i * (y i - xbar i) = ∑ i, (r i * y i - r i * xbar i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = (∑ i, r i * y i) - ∑ i, r i * xbar i := by
        simp [Finset.sum_sub_distrib]
  have hlin' :
      (∑ i, r i * xstar i) - ∑ i, r i * xbar i ≤
        (∑ i, r i * x i) - ∑ i, r i * xbar i := by
    exact sub_le_sub_right hlin _
  simpa [hsum x, hsum xstar] using hlin'

/-- Existence of a saddle point for the finite simplex payoff. -/
lemma simplexProximalValue_saddlePoint_fin (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ)
    (hL : 0 < L) (hn : 0 < n) :
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
                (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ)) := by
  classical
  obtain ⟨xstar, hxstar, hxmin⟩ :=
    simplexProximalValue_exists_primalMinimizer_fin (n := n) (xbar := xbar) (gbar := gbar)
      (L := L) hn
  let h : Fin n → ℝ := fun i => xstar i - xbar i
  let a : ℝ := ∑ i, |h i|
  obtain ⟨c, sstar, hmatch, hbound, hconst, hboundR⟩ :=
    simplexProximalValue_exists_sstar_support_constant (n := n) (xbar := xbar) (gbar := gbar)
      (xstar := xstar) (L := L) hL hxstar hxmin
  have hmatch' :
      ∀ i, h i ≠ 0 → sstar i = L * (∑ i, |h i|) * Real.sign (h i) := by
    simpa [h, a] using hmatch
  have hbound' : ∀ i, |sstar i| ≤ L * (∑ i, |h i|) := by
    simpa [h, a] using hbound
  have hsmax :
      ∀ s : Fin n → ℝ,
          (∑ i, (gbar i + s i) * (xstar i - xbar i)) -
              (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) ≤
            (∑ i, (gbar i + sstar i) * (xstar i - xbar i)) -
              (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) := by
    intro s
    have hsmax' :=
      dot_l1Quadratic_argmax_fin_with_free_zero_coords (n := n) (g := gbar) (h := h)
        (sstar := sstar) (L := L) hL hmatch' hbound' s
    simpa [h] using hsmax'
  have hconst' : ∀ i, 0 < xstar i → gbar i + sstar i = c := by
    simpa using hconst
  have hboundR' : ∀ i, c ≤ gbar i + sstar i := by
    simpa using hboundR
  have hsmin :
      ∀ x ∈ standardSimplex n,
          (∑ i, (gbar i + sstar i) * (xstar i - xbar i)) -
              (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) ≤
            (∑ i, (gbar i + sstar i) * (x i - xbar i)) -
              (1 / (2 * L)) * ‖sstar‖ ^ (2 : ℕ) := by
    intro x hx
    have hlin :=
      simplexProximalValue_saddlePoint_fin_hsmin (n := n) (xbar := xbar) (xstar := xstar)
        (r := fun i => gbar i + sstar i) (c := c) hxstar hconst' hboundR' x hx
    linarith
  exact ⟨xstar, hxstar, sstar, hsmax, hsmin⟩

/-- Swap the `min` and `max` in the simplex proximal value (minimax step). -/
lemma simplexProximalValue_minmax_exchange_fin (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ)
    (hL : 0 < L) :
    sInf
        ((fun x =>
              sSup
                ((fun s : Fin n → ℝ =>
                      (∑ i, (gbar i + s i) * (x i - xbar i)) -
                        (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
                  (Set.univ : Set (Fin n → ℝ)))) '' standardSimplex n) =
      sSup
        ((fun s : Fin n → ℝ =>
              sInf
                ((fun x : Fin n → ℝ =>
                      (∑ i, (gbar i + s i) * (x i - xbar i)) -
                        (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
                  standardSimplex n)) '' (Set.univ : Set (Fin n → ℝ))) := by
  classical
  by_cases hn : 0 < n
  · refine le_antisymm ?_ ?_
    · have hsaddle :=
        simplexProximalValue_saddlePoint_fin (n := n) (xbar := xbar) (gbar := gbar) (L := L) hL hn
      exact
        simplexProximalValue_minmax_exchange_fin_le_of_saddlePoint (n := n) (xbar := xbar)
          (gbar := gbar) (L := L) hL hsaddle
    · simpa using
        (simplexProximalValue_minmax_exchange_fin_le (n := n) (xbar := xbar) (gbar := gbar)
          (L := L) hn hL)
  · have hzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hzero
    have hsimplex0 : (standardSimplex 0 : Set (Fin 0 → ℝ)) = ∅ := by
      simp [standardSimplex]
    simp [hsimplex0, Set.image_univ, Set.range_const]
