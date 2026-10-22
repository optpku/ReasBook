/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- Helper for Example 7.14: the nonnegative quadrant in `ℝ × ℝ`. -/
private abbrev nonnegQuadrant : Set (ℝ × ℝ) := Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)

/-- Helper for Example 7.14: the concave candidate `(x, y) ↦ (x^(1/p) + y^(1/p))^p`. -/
private abbrev nonnegRpowAddRpow (p : ℝ) (z : ℝ × ℝ) : ℝ :=
  (z.1.rpow (1 / p) + z.2.rpow (1 / p)).rpow p

/-- Helper for Example 7.14: on the nonnegative quadrant, the concave candidate vanishes exactly
at the origin. -/
private lemma nonnegRpowAddRpow_eq_zero_iff {p : ℝ} (hp : 1 < p) {z : ℝ × ℝ}
    (hz : z ∈ nonnegQuadrant) : nonnegRpowAddRpow p z = 0 ↔ z.1 = 0 ∧ z.2 = 0 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hqne : 1 / p ≠ 0 := one_div_ne_zero hpne
  have hz1 : 0 ≤ z.1 := by
    simpa [nonnegQuadrant, Set.mem_Ici] using hz.1
  have hz2 : 0 ≤ z.2 := by
    simpa [nonnegQuadrant, Set.mem_Ici] using hz.2
  have hz1q_nonneg : 0 ≤ z.1.rpow (1 / p) := Real.rpow_nonneg hz1 _
  have hz2q_nonneg : 0 ≤ z.2.rpow (1 / p) := Real.rpow_nonneg hz2 _
  constructor
  · intro hz0
    -- First push the outer `rpow` equality down to the nonnegative sum inside.
    have hsum_nonneg : 0 ≤ z.1.rpow (1 / p) + z.2.rpow (1 / p) := add_nonneg hz1q_nonneg hz2q_nonneg
    have hsum0 : z.1.rpow (1 / p) + z.2.rpow (1 / p) = 0 := by
      apply (Real.rpow_eq_zero hsum_nonneg hpne).1
      simpa [nonnegRpowAddRpow] using hz0
    have hrpow0 :
        z.1.rpow (1 / p) = 0 ∧ z.2.rpow (1 / p) = 0 := by
      exact (add_eq_zero_iff_of_nonneg hz1q_nonneg hz2q_nonneg).1 hsum0
    constructor
    · exact (Real.rpow_eq_zero hz1 hqne).1 hrpow0.1
    · exact (Real.rpow_eq_zero hz2 hqne).1 hrpow0.2
  · rintro ⟨hz1, hz2⟩
    -- The origin is sent to zero because both exponents are nonzero.
    simp [nonnegRpowAddRpow, hz1, hz2, Real.zero_rpow, hpne]

/-- Helper for Example 7.14: the Example 7.14 map is positively homogeneous on the nonnegative
quadrant. -/
private lemma nonnegRpowAddRpow_smul {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) {z : ℝ × ℝ}
    (hz : z ∈ nonnegQuadrant) :
    nonnegRpowAddRpow p (c • z) = c * nonnegRpowAddRpow p z := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hz1 : 0 ≤ z.1 := by
    simpa [nonnegQuadrant, Set.mem_Ici] using hz.1
  have hz2 : 0 ≤ z.2 := by
    simpa [nonnegQuadrant, Set.mem_Ici] using hz.2
  have hqp : (1 / p) * p = 1 := by
    field_simp [hpne]
  have hzsum_nonneg : 0 ≤ z.1.rpow (1 / p) + z.2.rpow (1 / p) := by
    exact add_nonneg (Real.rpow_nonneg hz1 _) (Real.rpow_nonneg hz2 _)
  have hmul1 : (c * z.1).rpow (1 / p) = c.rpow (1 / p) * z.1.rpow (1 / p) := by
    simpa using (Real.mul_rpow hc hz1 : (c * z.1) ^ (1 / p) = c ^ (1 / p) * z.1 ^ (1 / p))
  have hmul2 : (c * z.2).rpow (1 / p) = c.rpow (1 / p) * z.2.rpow (1 / p) := by
    simpa using (Real.mul_rpow hc hz2 : (c * z.2) ^ (1 / p) = c ^ (1 / p) * z.2 ^ (1 / p))
  have hmul3 :
      (c.rpow (1 / p) * (z.1.rpow (1 / p) + z.2.rpow (1 / p))).rpow p =
        (c.rpow (1 / p)).rpow p * (z.1.rpow (1 / p) + z.2.rpow (1 / p)).rpow p := by
    simpa using
      (Real.mul_rpow (Real.rpow_nonneg hc _) hzsum_nonneg :
        (c ^ (1 / p) * (z.1.rpow (1 / p) + z.2.rpow (1 / p))) ^ p =
          (c ^ (1 / p)) ^ p * (z.1.rpow (1 / p) + z.2.rpow (1 / p)) ^ p)
  have hpowc : (c.rpow (1 / p)).rpow p = c := by
    calc
      (c.rpow (1 / p)).rpow p = c.rpow ((1 / p) * p) := by
        simpa using (Real.rpow_mul hc (1 / p) p).symm
      _ = c.rpow 1 := by rw [hqp]
      _ = c := by simp
  -- Pull the scalar out of each coordinate and then out of the final `rpow`.
  calc
    nonnegRpowAddRpow p (c • z)
        = ((c * z.1).rpow (1 / p) + (c * z.2).rpow (1 / p)).rpow p := by
            simp [nonnegRpowAddRpow]
    _ = ((c.rpow (1 / p) * z.1.rpow (1 / p) + c.rpow (1 / p) * z.2.rpow (1 / p)).rpow p) := by
          rw [hmul1, hmul2]
    _ = (c.rpow (1 / p) * (z.1.rpow (1 / p) + z.2.rpow (1 / p))).rpow p := by
          rw [mul_add]
    _ = (c.rpow (1 / p)).rpow p * (z.1.rpow (1 / p) + z.2.rpow (1 / p)).rpow p := by
          rw [hmul3]
    _ = c * nonnegRpowAddRpow p z := by
          rw [hpowc, nonnegRpowAddRpow]

/-- Helper for Example 7.14: on the nonnegative quadrant, raising `nonnegRpowAddRpow p z` to the
power `1 / p` recovers the inner coordinate sum. -/
private lemma nonnegRpowAddRpow_rpow_one_div {p : ℝ} (hp : 1 < p) {z : ℝ × ℝ}
    (hz : z ∈ nonnegQuadrant) :
    (nonnegRpowAddRpow p z).rpow (1 / p) = z.1.rpow (1 / p) + z.2.rpow (1 / p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hz1 : 0 ≤ z.1 := by
    simpa [nonnegQuadrant, Set.mem_Ici] using hz.1
  have hz2 : 0 ≤ z.2 := by
    simpa [nonnegQuadrant, Set.mem_Ici] using hz.2
  have hsum_nonneg : 0 ≤ z.1.rpow (1 / p) + z.2.rpow (1 / p) := by
    exact add_nonneg (Real.rpow_nonneg hz1 _) (Real.rpow_nonneg hz2 _)
  have hqp : p * (1 / p) = 1 := by
    field_simp [hpne]
  -- Expand the definition once and collapse the outer `rpow` with `p * (1 / p) = 1`.
  calc
    (nonnegRpowAddRpow p z).rpow (1 / p)
        = (z.1.rpow (1 / p) + z.2.rpow (1 / p)).rpow (p * (1 / p)) := by
            simpa [nonnegRpowAddRpow] using
              (Real.rpow_mul hsum_nonneg p (1 / p)).symm
    _ = (z.1.rpow (1 / p) + z.2.rpow (1 / p)).rpow 1 := by rw [hqp]
    _ = z.1.rpow (1 / p) + z.2.rpow (1 / p) := by simp

/-- Helper for Example 7.14: the Example 7.14 map is superadditive on the nonnegative quadrant. -/
private lemma nonnegRpowAddRpow_add {p : ℝ} (hp : 1 < p) {x y : ℝ × ℝ} (hx : x ∈ nonnegQuadrant)
    (hy : y ∈ nonnegQuadrant) :
    nonnegRpowAddRpow p x + nonnegRpowAddRpow p y ≤ nonnegRpowAddRpow p (x + y) := by
  let q : ℝ := 1 / p
  let A : ℝ := nonnegRpowAddRpow p x
  let B : ℝ := nonnegRpowAddRpow p y
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hq_pos : 0 < q := by
    dsimp [q]
    exact one_div_pos.mpr hp0
  have hq_nonneg : 0 ≤ q := hq_pos.le
  have hq_le_one : q ≤ 1 := by
    dsimp [q]
    exact (one_div_le hp0 zero_lt_one).2 (by simpa using hp.le)
  have hqp : q * p = 1 := by
    dsimp [q]
    field_simp [hpne]
  have hx1 : 0 ≤ x.1 := by
    simpa [nonnegQuadrant, Set.mem_Ici] using hx.1
  have hx2 : 0 ≤ x.2 := by
    simpa [nonnegQuadrant, Set.mem_Ici] using hx.2
  have hy1 : 0 ≤ y.1 := by
    simpa [nonnegQuadrant, Set.mem_Ici] using hy.1
  have hy2 : 0 ≤ y.2 := by
    simpa [nonnegQuadrant, Set.mem_Ici] using hy.2
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, nonnegRpowAddRpow]
    exact Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg hx1 _) (Real.rpow_nonneg hx2 _)) p
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, nonnegRpowAddRpow]
    exact Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg hy1 _) (Real.rpow_nonneg hy2 _)) p
  by_cases hA0 : A = 0
  · -- If `ψ(x) = 0`, then `x = 0`, so the claim reduces to `ψ(y) ≤ ψ(y)`.
    have hx_zero : x.1 = 0 ∧ x.2 = 0 := by
      exact (nonnegRpowAddRpow_eq_zero_iff hp hx).1 (by simpa [A] using hA0)
    have hx_eq : x = (0, 0) := by
      ext <;> simp [hx_zero.1, hx_zero.2]
    rw [hx_eq]
    simp [nonnegRpowAddRpow, hpne]
  by_cases hB0 : B = 0
  · -- The symmetric zero case for `y`.
    have hy_zero : y.1 = 0 ∧ y.2 = 0 := by
      exact (nonnegRpowAddRpow_eq_zero_iff hp hy).1 (by simpa [B] using hB0)
    have hy_eq : y = (0, 0) := by
      ext <;> simp [hy_zero.1, hy_zero.2]
    rw [hy_eq]
    simp [nonnegRpowAddRpow, hpne]
  have hA_pos : 0 < A := lt_of_le_of_ne hA_nonneg (by simpa [eq_comm] using hA0)
  have hB_pos : 0 < B := lt_of_le_of_ne hB_nonneg (by simpa [eq_comm] using hB0)
  have hAB_pos : 0 < A + B := add_pos hA_pos hB_pos
  have hAB_nonneg : 0 ≤ A + B := hAB_pos.le
  have hab : A / (A + B) + B / (A + B) = 1 := by
    rw [← add_div, div_self hAB_pos.ne']
  have hx1_div : 0 ≤ x.1 / A := div_nonneg hx1 hA_pos.le
  have hx2_div : 0 ≤ x.2 / A := div_nonneg hx2 hA_pos.le
  have hy1_div : 0 ≤ y.1 / B := div_nonneg hy1 hB_pos.le
  have hy2_div : 0 ≤ y.2 / B := div_nonneg hy2 hB_pos.le
  have hAq_pos : 0 < A.rpow q := Real.rpow_pos_of_pos hA_pos q
  have hBq_pos : 0 < B.rpow q := Real.rpow_pos_of_pos hB_pos q
  have hABq_pos : 0 < (A + B).rpow q := Real.rpow_pos_of_pos hAB_pos q
  have hAq : A.rpow q = x.1.rpow q + x.2.rpow q := by
    simpa [A, q] using nonnegRpowAddRpow_rpow_one_div hp hx
  have hBq : B.rpow q = y.1.rpow q + y.2.rpow q := by
    simpa [B, q] using nonnegRpowAddRpow_rpow_one_div hp hy
  have hx1_div_rpow : (x.1 / A).rpow q = x.1.rpow q / A.rpow q := by
    simpa using (Real.div_rpow hx1 hA_pos.le q)
  have hx2_div_rpow : (x.2 / A).rpow q = x.2.rpow q / A.rpow q := by
    simpa using (Real.div_rpow hx2 hA_pos.le q)
  have hy1_div_rpow : (y.1 / B).rpow q = y.1.rpow q / B.rpow q := by
    simpa using (Real.div_rpow hy1 hB_pos.le q)
  have hy2_div_rpow : (y.2 / B).rpow q = y.2.rpow q / B.rpow q := by
    simpa using (Real.div_rpow hy2 hB_pos.le q)
  have hxy1_div_rpow :
      ((x.1 + y.1) / (A + B)).rpow q = (x.1 + y.1).rpow q / (A + B).rpow q := by
    simpa using (Real.div_rpow (add_nonneg hx1 hy1) hAB_nonneg q)
  have hxy2_div_rpow :
      ((x.2 + y.2) / (A + B)).rpow q = (x.2 + y.2).rpow q / (A + B).rpow q := by
    simpa using (Real.div_rpow (add_nonneg hx2 hy2) hAB_nonneg q)
  have hx_norm : (x.1 / A).rpow q + (x.2 / A).rpow q = 1 := by
    -- Normalize the `x`-coordinates so that their `q`-powers sum to `1`.
    calc
      (x.1 / A).rpow q + (x.2 / A).rpow q
          = (x.1.rpow q + x.2.rpow q) / A.rpow q := by
              rw [hx1_div_rpow, hx2_div_rpow, add_div]
      _ = 1 := by
            rw [← hAq, div_self hAq_pos.ne']
  have hy_norm : (y.1 / B).rpow q + (y.2 / B).rpow q = 1 := by
    -- The same normalized identity for `y`.
    calc
      (y.1 / B).rpow q + (y.2 / B).rpow q
          = (y.1.rpow q + y.2.rpow q) / B.rpow q := by
              rw [hy1_div_rpow, hy2_div_rpow, add_div]
      _ = 1 := by
            rw [← hBq, div_self hBq_pos.ne']
  -- Route correction: use concavity of `t ↦ t ^ q` on `[0, ∞)` directly on the normalized
  -- coordinates. This avoids the brittle rescaling normal form from the previous route.
  have hcoord1 :
      A / (A + B) * (x.1 / A).rpow q + B / (A + B) * (y.1 / B).rpow q ≤
        (A / (A + B) * (x.1 / A) + B / (A + B) * (y.1 / B)).rpow q := by
    simpa [smul_eq_mul] using
      (Real.concaveOn_rpow hq_nonneg hq_le_one).2
        (show x.1 / A ∈ Set.Ici (0 : ℝ) by exact hx1_div)
        (show y.1 / B ∈ Set.Ici (0 : ℝ) by exact hy1_div)
        (div_nonneg hA_pos.le hAB_nonneg) (div_nonneg hB_pos.le hAB_nonneg) hab
  have hcoord2 :
      A / (A + B) * (x.2 / A).rpow q + B / (A + B) * (y.2 / B).rpow q ≤
        (A / (A + B) * (x.2 / A) + B / (A + B) * (y.2 / B)).rpow q := by
    simpa [smul_eq_mul] using
      (Real.concaveOn_rpow hq_nonneg hq_le_one).2
        (show x.2 / A ∈ Set.Ici (0 : ℝ) by exact hx2_div)
        (show y.2 / B ∈ Set.Ici (0 : ℝ) by exact hy2_div)
        (div_nonneg hA_pos.le hAB_nonneg) (div_nonneg hB_pos.le hAB_nonneg) hab
  have hinner1 :
      A / (A + B) * (x.1 / A) + B / (A + B) * (y.1 / B) = (x.1 + y.1) / (A + B) := by
    field_simp [hA_pos.ne', hB_pos.ne', hAB_pos.ne']
  have hinner2 :
      A / (A + B) * (x.2 / A) + B / (A + B) * (y.2 / B) = (x.2 + y.2) / (A + B) := by
    field_simp [hA_pos.ne', hB_pos.ne', hAB_pos.ne']
  have hleft_group :
      A / (A + B) * (x.1 / A).rpow q + B / (A + B) * (y.1 / B).rpow q +
          (A / (A + B) * (x.2 / A).rpow q + B / (A + B) * (y.2 / B).rpow q) =
        A / (A + B) * ((x.1 / A).rpow q + (x.2 / A).rpow q) +
          B / (A + B) * ((y.1 / B).rpow q + (y.2 / B).rpow q) := by
    ring
  have hnormalized :
      1 ≤ ((x.1 + y.1) / (A + B)).rpow q + ((x.2 + y.2) / (A + B)).rpow q := by
    -- Adding the two coordinate inequalities collapses the normalized left side to `1`.
    calc
      1 = A / (A + B) * (x.1 / A).rpow q + B / (A + B) * (y.1 / B).rpow q +
            (A / (A + B) * (x.2 / A).rpow q + B / (A + B) * (y.2 / B).rpow q) := by
              rw [hleft_group, hx_norm, hy_norm, mul_one, mul_one, hab]
      _ ≤ (A / (A + B) * (x.1 / A) + B / (A + B) * (y.1 / B)).rpow q +
            (A / (A + B) * (x.2 / A) + B / (A + B) * (y.2 / B)).rpow q := by
              exact add_le_add hcoord1 hcoord2
      _ = ((x.1 + y.1) / (A + B)).rpow q + ((x.2 + y.2) / (A + B)).rpow q := by
            rw [hinner1, hinner2]
  have hnormalized' :
      1 ≤ ((x.1 + y.1).rpow q + (x.2 + y.2).rpow q) / (A + B).rpow q := by
    rw [hxy1_div_rpow, hxy2_div_rpow] at hnormalized
    have hsum_div :
        (x.1 + y.1).rpow q / (A + B).rpow q + (x.2 + y.2).rpow q / (A + B).rpow q =
          ((x.1 + y.1).rpow q + (x.2 + y.2).rpow q) / (A + B).rpow q := by
      rw [← add_div]
    exact hsum_div ▸ hnormalized
  have htarget_q :
      (A + B).rpow q ≤ (x.1 + y.1).rpow q + (x.2 + y.2).rpow q := by
    have hmul := (one_le_div hABq_pos).1 hnormalized'
    simpa using hmul
  have htarget_p :
      ((A + B).rpow q).rpow p ≤
        ((x.1 + y.1).rpow q + (x.2 + y.2).rpow q).rpow p := by
    exact Real.rpow_le_rpow (Real.rpow_nonneg hAB_nonneg q) htarget_q hp0.le
  -- Raise back to the exponent `p` and identify both sides with the target expressions.
  calc
    nonnegRpowAddRpow p x + nonnegRpowAddRpow p y = A + B := by rfl
    _ = ((A + B).rpow q).rpow p := by
          calc
            A + B = (A + B).rpow 1 := by simp
            _ = (A + B).rpow (q * p) := by rw [hqp]
            _ = ((A + B).rpow q).rpow p := by
                  simpa using (Real.rpow_mul hAB_nonneg q p)
    _ ≤ ((x.1 + y.1).rpow q + (x.2 + y.2).rpow q).rpow p := htarget_p
    _ = nonnegRpowAddRpow p (x + y) := by
          simp [nonnegRpowAddRpow, q]

/-- Helper for Example 7.14: the Example 7.14 integrand is dominated by a linear majorant on the
nonnegative quadrant. -/
private lemma nonnegRpowAddRpow_le_linear {p x y : ℝ} (hp : 1 < p) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((x.rpow (1 / p) + y.rpow (1 / p)).rpow p) ≤ (2 : ℝ) ^ (p - 1) * (x + y) := by
  let q : ℝ := 1 / p
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hqp : q * p = 1 := by
    dsimp [q]
    field_simp [hpne]
  -- This is the two-point power-mean bound specialized to `u = x^(1/p)` and `v = y^(1/p)`.
  have hmean := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := (Finset.univ : Finset (Fin 2))) (f := ![x.rpow q, y.rpow q]) hp.le
    (by
      intro i hi
      fin_cases i
      · simpa using Real.rpow_nonneg hx q
      · simpa using Real.rpow_nonneg hy q)
  have hx_pow : (x.rpow q).rpow p = x := by
    calc
      (x.rpow q).rpow p = x.rpow (q * p) := by simpa using (Real.rpow_mul hx q p).symm
      _ = x := by simp [hqp]
  have hy_pow : (y.rpow q).rpow p = y := by
    calc
      (y.rpow q).rpow p = y.rpow (q * p) := by simpa using (Real.rpow_mul hy q p).symm
      _ = y := by simp [hqp]
  have hmean' :
      (x.rpow q + y.rpow q).rpow p ≤
        (2 : ℝ) ^ (p - 1) * ((x.rpow q).rpow p + (y.rpow q).rpow p) := by
    simpa [Fin.sum_univ_two, q] using hmean
  calc
    (x.rpow (1 / p) + y.rpow (1 / p)).rpow p
        = (x.rpow q + y.rpow q).rpow p := by rfl
    _ ≤ (2 : ℝ) ^ (p - 1) * ((x.rpow q).rpow p + (y.rpow q).rpow p) := hmean'
    _ = (2 : ℝ) ^ (p - 1) * (x + y) := by rw [hx_pow, hy_pow]

/-- Helper for Example 7.14: the Jensen integrand is integrable under the standing nonnegativity
and integrability assumptions. -/
private lemma integrable_nonnegRpowAddRpow_comp {P : Measure Ω} {X Y : Ω → ℝ} {p : ℝ} (hp : 1 < p)
    (hX : Integrable X P) (hY : Integrable Y P) (hX_nonneg : 0 ≤ᵐ[P] X) (hY_nonneg : 0 ≤ᵐ[P] Y) :
    Integrable (fun ω ↦ nonnegRpowAddRpow p (X ω, Y ω)) P := by
  have hX_meas : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
  have hY_meas : AEMeasurable Y P := hY.aestronglyMeasurable.aemeasurable
  have h_meas :
      AEStronglyMeasurable (fun ω ↦ nonnegRpowAddRpow p (X ω, Y ω)) P := by
    apply AEMeasurable.aestronglyMeasurable
    simpa [nonnegRpowAddRpow] using
      (((hX_meas.pow_const (1 / p)).add (hY_meas.pow_const (1 / p))).pow_const p)
  have hmajorant : Integrable (fun ω ↦ (2 : ℝ) ^ (p - 1) * (X ω + Y ω)) P := by
    exact (hX.add hY).const_mul ((2 : ℝ) ^ (p - 1))
  have hbound :
      ∀ᵐ ω ∂P, ‖nonnegRpowAddRpow p (X ω, Y ω)‖ ≤ (2 : ℝ) ^ (p - 1) * (X ω + Y ω) := by
    filter_upwards [hX_nonneg, hY_nonneg] with ω hXω hYω
    have hpoint := nonnegRpowAddRpow_le_linear hp hXω hYω
    have hsum_nonneg : 0 ≤ (X ω).rpow (1 / p) + (Y ω).rpow (1 / p) := by
      exact add_nonneg (Real.rpow_nonneg hXω _) (Real.rpow_nonneg hYω _)
    have hnonneg : 0 ≤ ((X ω).rpow (1 / p) + (Y ω).rpow (1 / p)).rpow p :=
      Real.rpow_nonneg hsum_nonneg p
    change |((X ω).rpow (1 / p) + (Y ω).rpow (1 / p)).rpow p| ≤
      (2 : ℝ) ^ (p - 1) * (X ω + Y ω)
    rw [abs_of_nonneg hnonneg]
    exact hpoint
  exact Integrable.mono' hmajorant h_meas hbound

-- Proof sketch: this is the source-facing `ConcaveOn` formulation of the textbook claim. The
-- owner abstraction is the chapter's concavity/Jensen interface on the nonnegative quadrant, not
-- the later `lpNorm` inequality API.
/-- Companion for Example 7.14: for `p > 1`, the function
`ψ(x, y) = (x^(1/p) + y^(1/p))^p` is concave on the nonnegative quadrant
`[0, ∞) × [0, ∞)`. -/
private theorem concaveOn_nonneg_rpow_add_rpow {p : ℝ} (hp : 1 < p) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))
      (fun z : ℝ × ℝ ↦ (z.1.rpow (1 / p) + z.2.rpow (1 / p)).rpow p) := by
  -- We prove concavity from positive homogeneity and superadditivity on the cone.
  rw [concaveOn_iff_forall_pos]
  constructor
  · simpa [nonnegQuadrant] using ((convex_Ici (0 : ℝ)).prod (convex_Ici (0 : ℝ)))
  · intro x hx y hy a b ha hb hab
    have hx' : x ∈ nonnegQuadrant := by simpa [nonnegQuadrant] using hx
    have hy' : y ∈ nonnegQuadrant := by simpa [nonnegQuadrant] using hy
    have hx1 : 0 ≤ x.1 := by simpa [Set.mem_Ici] using hx.1
    have hx2 : 0 ≤ x.2 := by simpa [Set.mem_Ici] using hx.2
    have hy1 : 0 ≤ y.1 := by simpa [Set.mem_Ici] using hy.1
    have hy2 : 0 ≤ y.2 := by simpa [Set.mem_Ici] using hy.2
    have hax : a • x ∈ nonnegQuadrant := by
      exact ⟨mul_nonneg ha.le hx1, mul_nonneg ha.le hx2⟩
    have hby : b • y ∈ nonnegQuadrant := by
      exact ⟨mul_nonneg hb.le hy1, mul_nonneg hb.le hy2⟩
    simpa [nonnegRpowAddRpow] using
      (show a * nonnegRpowAddRpow p x + b * nonnegRpowAddRpow p y ≤
          nonnegRpowAddRpow p (a • x + b • y) by
        rw [← nonnegRpowAddRpow_smul hp ha.le hx', ← nonnegRpowAddRpow_smul hp hb.le hy']
        exact nonnegRpowAddRpow_add hp hax hby)

-- Proof sketch: apply the concave Jensen inequality to the random vector `ω ↦ (X ω, Y ω)` and
-- the source-facing concavity theorem above. This keeps the expectation estimate as a companion
-- consequence of the canonical `ConcaveOn` owner abstraction.
/-- Example 7.14: if `X` and `Y` are nonnegative integrable real random variables on a probability
space and `p ∈ (1, ∞)`, then Jensen's inequality for the concave map
`(x, y) ↦ (x^(1/p) + y^(1/p))^p` gives
`E[(X^(1/p) + Y^(1/p))^p] ≤ (E[X]^(1/p) + E[Y]^(1/p))^p`. -/
theorem expectation_rpow_add_le_rpow_add_expectations {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} {p : ℝ} (hp : 1 < p) (hX : Integrable X P)
    (hY : Integrable Y P) (hX_nonneg : 0 ≤ᵐ[P] X) (hY_nonneg : 0 ≤ᵐ[P] Y) :
    P[fun ω ↦ ((X ω).rpow (1 / p) + (Y ω).rpow (1 / p)).rpow p] ≤
      ((P[X]).rpow (1 / p) + (P[Y]).rpow (1 / p)).rpow p := by
  let g : ℝ × ℝ → ℝ := fun z ↦ nonnegRpowAddRpow p z
  let F : Ω → ℝ × ℝ := fun ω ↦ (X ω, Y ω)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hqnonneg : 0 ≤ 1 / p := one_div_nonneg.mpr hp0.le
  have hg_cont : Continuous g := by
    -- Continuity is global because both exponents are nonnegative.
    dsimp [g, nonnegRpowAddRpow]
    exact ((continuous_fst.rpow_const fun _ ↦ Or.inr hqnonneg).add
      (continuous_snd.rpow_const fun _ ↦ Or.inr hqnonneg)).rpow_const fun _ ↦ Or.inr hp0.le
  have hF_mem : ∀ᵐ ω ∂P, F ω ∈ nonnegQuadrant := by
    filter_upwards [hX_nonneg, hY_nonneg] with ω hXω hYω
    exact ⟨hXω, hYω⟩
  have hF_int : Integrable F P := hX.prodMk hY
  have hg_int : Integrable (g ∘ F) P := by
    simpa [Function.comp, g, F] using
      integrable_nonnegRpowAddRpow_comp hp hX hY hX_nonneg hY_nonneg
  have hJ := (concaveOn_nonneg_rpow_add_rpow hp).le_map_integral hg_cont.continuousOn
    ((isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).prod isClosed_Ici)
    (by simpa [F, nonnegQuadrant] using hF_mem) hF_int hg_int
  -- Jensen reduces immediately to the stated expectation inequality once the pair integral is
  -- rewritten componentwise.
  simpa [Function.comp, g, F, nonnegRpowAddRpow, nonnegQuadrant, integral_pair hX hY] using hJ
