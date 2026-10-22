/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Exercise 7.2.3: the bounded sign-power cutoff used to test the reverse Hölder
implication. -/
noncomputable def cutoffSignedPower (p : ℝ) (X : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (if 0 ≤ X ω then (1 : ℝ) else -1) * (min |X ω| (n : ℝ)) ^ (p - 1)

/-- Helper for Exercise 7.2.3: the truncated `p`-power controlled by the cutoff pairing. -/
noncomputable def cutoffPower (p : ℝ) (X : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (min |X ω| (n : ℝ)) ^ p

/-- Helper for Exercise 7.2.3: the sign-power cutoff is measurable and uniformly bounded. -/
lemma cutoffSignedPower_measurable_bound {p : ℝ} (hp : 1 < p) {X : Ω → ℝ} (hX : Measurable X)
    (n : ℕ) :
    Measurable (cutoffSignedPower p X n) ∧
      ∃ M : NNReal, ∀ ω, |cutoffSignedPower p X n ω| ≤ M := by
  -- The cutoff splits into a measurable sign factor and a measurable truncated power.
  have hsign : Measurable fun ω => if 0 ≤ X ω then (1 : ℝ) else -1 := by
    refine measurable_const.piecewise (hX measurableSet_Ici) measurable_const
  have hpow : Measurable fun ω => (min |X ω| (n : ℝ)) ^ (p - 1) := by
    exact (hX.abs.min measurable_const).pow_const _
  refine ⟨hsign.mul hpow, ?_⟩
  refine ⟨⟨(n : ℝ) ^ (p - 1), Real.rpow_nonneg (Nat.cast_nonneg n) _⟩, ?_⟩
  intro ω
  have hmin_nonneg : 0 ≤ min |X ω| (n : ℝ) := le_min (abs_nonneg _) (Nat.cast_nonneg n)
  have hmin_le : min |X ω| (n : ℝ) ≤ (n : ℝ) := min_le_right _ _
  have habs_sign : |if 0 ≤ X ω then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  -- The bound comes from monotonicity of `rpow` on the nonnegative cutoff.
  calc
    |cutoffSignedPower p X n ω|
        = (min |X ω| (n : ℝ)) ^ (p - 1) := by
          by_cases hω : 0 ≤ X ω
          · simp [cutoffSignedPower, hω, abs_of_nonneg (Real.rpow_nonneg hmin_nonneg _)]
          · simp [cutoffSignedPower, hω, abs_of_nonneg (Real.rpow_nonneg hmin_nonneg _)]
    _ ≤ (n : ℝ) ^ (p - 1) := by
      exact Real.rpow_le_rpow hmin_nonneg hmin_le (sub_nonneg.2 hp.le)

/-- Helper for Exercise 7.2.3: the cutoff `L^q` density matches the truncated `p`-power exactly. -/
lemma cutoffSignedPower_abs_rpow_eq_cutoffPower {p q : ℝ} (hpq : p.HolderConjugate q)
    {X : Ω → ℝ} (n : ℕ) (ω : Ω) :
    |cutoffSignedPower p X n ω| ^ q = cutoffPower p X n ω := by
  have hmin_nonneg : 0 ≤ min |X ω| (n : ℝ) := le_min (abs_nonneg _) (Nat.cast_nonneg n)
  have habs_sign : |if 0 ≤ X ω then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  -- The conjugacy identity `(p - 1) * q = p` is the normalization step.
  calc
    |cutoffSignedPower p X n ω| ^ q
        = ((min |X ω| (n : ℝ)) ^ (p - 1)) ^ q := by
          by_cases hω : 0 ≤ X ω
          · simp [cutoffSignedPower, hω, abs_of_nonneg (Real.rpow_nonneg hmin_nonneg _)]
          · simp [cutoffSignedPower, hω, abs_of_nonneg (Real.rpow_nonneg hmin_nonneg _)]
    _ = (min |X ω| (n : ℝ)) ^ ((p - 1) * q) := by
      rw [Real.rpow_mul hmin_nonneg]
    _ = (min |X ω| (n : ℝ)) ^ p := by rw [hpq.sub_one_mul_conj]
    _ = cutoffPower p X n ω := rfl

/-- Helper for Exercise 7.2.3: the cutoff pairing dominates the truncated `p`-power pointwise. -/
lemma cutoffPower_le_mul_cutoffSignedPower {p : ℝ} (hp : 1 < p) {X : Ω → ℝ} (n : ℕ) (ω : Ω) :
    cutoffPower p X n ω ≤ X ω * cutoffSignedPower p X n ω := by
  have hmin_nonneg : 0 ≤ min |X ω| (n : ℝ) := le_min (abs_nonneg _) (Nat.cast_nonneg n)
  have hpow_nonneg : 0 ≤ (min |X ω| (n : ℝ)) ^ (p - 1) := Real.rpow_nonneg hmin_nonneg _
  have hmin_le_abs : min |X ω| (n : ℝ) ≤ |X ω| := min_le_left _ _
  have hpow_split :
      (min |X ω| (n : ℝ)) ^ p =
        min |X ω| (n : ℝ) * (min |X ω| (n : ℝ)) ^ (p - 1) := by
    by_cases hmin_zero : min |X ω| (n : ℝ) = 0
    · have hp_ne_zero : p ≠ 0 := by linarith
      simp [hmin_zero, Real.zero_rpow hp_ne_zero]
    · have hmin_pos : 0 < min |X ω| (n : ℝ) := by
        exact lt_of_le_of_ne hmin_nonneg (by simpa [eq_comm] using hmin_zero)
      calc
        (min |X ω| (n : ℝ)) ^ p
            = (min |X ω| (n : ℝ)) ^ (1 + (p - 1)) := by ring_nf
        _ = (min |X ω| (n : ℝ)) ^ (1 : ℝ) * (min |X ω| (n : ℝ)) ^ (p - 1) := by
          rw [Real.rpow_add hmin_pos]
        _ = min |X ω| (n : ℝ) * (min |X ω| (n : ℝ)) ^ (p - 1) := by simp
  -- Compare the truncated power with the product after factoring out the common cutoff power.
  calc
    cutoffPower p X n ω
        = min |X ω| (n : ℝ) * (min |X ω| (n : ℝ)) ^ (p - 1) := by
          simpa [cutoffPower] using hpow_split
    _ ≤ |X ω| * (min |X ω| (n : ℝ)) ^ (p - 1) := by
      gcongr
    _ = X ω * cutoffSignedPower p X n ω := by
      by_cases hω : 0 ≤ X ω
      · simp [cutoffSignedPower, hω, abs_of_nonneg hω]
      · have hω' : X ω < 0 := lt_of_not_ge hω
        simp [cutoffSignedPower, hω, abs_of_neg hω']

/-- Helper for Exercise 7.2.3: the truncated `p`-powers increase to the full `p`-power. -/
lemma iSup_cutoffPower_eq {p : ℝ} (hp_nonneg : 0 ≤ p) {X : Ω → ℝ} (ω : Ω) :
    (⨆ n : ℕ, ENNReal.ofReal (cutoffPower p X n ω)) = ENNReal.ofReal (|X ω| ^ p) := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    exact ENNReal.ofReal_le_ofReal <|
      Real.rpow_le_rpow (le_min (abs_nonneg _) (Nat.cast_nonneg n)) (min_le_left _ _) hp_nonneg
  · obtain ⟨n, hn⟩ := exists_nat_gt (|X ω|)
    refine le_iSup_of_le n ?_
    have hmin : min |X ω| (n : ℝ) = |X ω| := by
      refine min_eq_left ?_
      exact le_of_lt (by exact_mod_cast hn)
    simp [cutoffPower, hmin]

-- Proof sketch: this is a source-facing bridge built on the canonical `MemLp`/`lpNorm` API. For
-- the forward implication, combine Hölder's inequality with the fact that a bounded measurable
-- random variable on a probability space belongs to every finite `L^q`; this gives integrability
-- of `X * Y` together with the stated bound. For the reverse implication, test the assumed
-- estimate on bounded truncations of `sgn(X) * |X|^(p - 1)` and pass to the limit.
/-- Exercise 7.2.3: if `p` and `q` are Hölder-conjugate exponents, then a real random variable on
a probability space belongs to `ℒ^p(P)` if and only if every bounded measurable real test random
variable `Y` yields an integrable product `X * Y` whose integral is uniformly controlled by a
constant multiple of the `L^q(P)` norm of `Y`. This avoids the total-expectation convention for
nonintegrable functions and matches the textbook bounded-functional interpretation. -/
theorem memLp_iff_exists_expectation_bound_of_bounded_measurable
    {P : Measure Ω} [IsProbabilityMeasure P] {p q : ℝ} {X : Ω → ℝ}
    (hpq : p.HolderConjugate q) :
    MemLp X (ENNReal.ofReal p) P ↔
      ∃ C : NNReal, ∀ ⦃Y : Ω → ℝ⦄, Measurable Y →
        (∃ M : NNReal, ∀ ω, |Y ω| ≤ M) →
        Integrable (X * Y) P ∧
          |∫ ω, X ω * Y ω ∂P| ≤ (C : ℝ) * lpNorm Y (ENNReal.ofReal q) P := by
  constructor
  · intro hX
    have hp : 1 < p := (Real.holderConjugate_iff.mp hpq).1
    have hq : 1 < q := (Real.holderConjugate_iff.mp hpq.symm).1
    have hp_nonneg : 0 ≤ p := le_of_lt (lt_trans zero_lt_one hp)
    have hq_nonneg : 0 ≤ q := le_of_lt (lt_trans zero_lt_one hq)
    refine ⟨⟨lpNorm X (ENNReal.ofReal p) P, lpNorm_nonneg⟩, ?_⟩
    intro Y hY_meas hY_bdd
    rcases hY_bdd with ⟨M, hM⟩
    -- A bounded measurable test function belongs to `L^q(P)` on a probability space.
    have hY_memLp : MemLp Y (ENNReal.ofReal q) P :=
      MemLp.of_bound hY_meas.aestronglyMeasurable M <|
        Filter.Eventually.of_forall fun ω => by
          simpa [Real.norm_eq_abs] using hM ω
    -- Hölder gives integrability of the product.
    have hXY_int : Integrable (X * Y) P := by
      letI : (ENNReal.ofReal q).HolderTriple (ENNReal.ofReal p) 1 := hpq.symm.ennrealOfReal
      simpa [mul_comm] using hY_memLp.integrable_mul hX
    refine ⟨hXY_int, ?_⟩
    -- Rewrite the Hölder bound in terms of `lpNorm`.
    calc
      |∫ ω, X ω * Y ω ∂P|
          = ‖∫ ω, X ω * Y ω ∂P‖ := by simp
      _ ≤ ∫ ω, ‖X ω * Y ω‖ ∂P := norm_integral_le_integral_norm _
      _ = ∫ ω, ‖X ω‖ * ‖Y ω‖ ∂P := by simp [norm_mul]
      _ ≤ (∫ ω, ‖X ω‖ ^ p ∂P) ^ (1 / p) * (∫ ω, ‖Y ω‖ ^ q ∂P) ^ (1 / q) :=
        integral_mul_norm_le_Lp_mul_Lq hpq hX hY_memLp
      _ = lpNorm X (ENNReal.ofReal p) P * lpNorm Y (ENNReal.ofReal q) P := by
        symm
        rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp) hX.aestronglyMeasurable,
          lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp)
            hY_meas.aestronglyMeasurable]
        simp [ENNReal.toReal_ofReal hp_nonneg, ENNReal.toReal_ofReal hq_nonneg]
      _ = ((⟨lpNorm X (ENNReal.ofReal p) P, lpNorm_nonneg⟩ : NNReal) : ℝ) *
          lpNorm Y (ENNReal.ofReal q) P := by
        rfl
  · rintro ⟨C, hC⟩
    have hp : 1 < p := (Real.holderConjugate_iff.mp hpq).1
    have hq : 1 < q := (Real.holderConjugate_iff.mp hpq.symm).1
    have hp_pos : 0 < p := lt_trans zero_lt_one hp
    have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
    have hq_nonneg : 0 ≤ q := le_of_lt (lt_trans zero_lt_one hq)
    -- Route correction: first recover `Integrable X`, then move to a measurable representative.
    have hX_int : Integrable X P := by
      have hconst :=
        hC (Y := fun _ : Ω => (1 : ℝ)) measurable_const
          ⟨1, fun _ => by norm_num⟩
      simpa using (show Integrable (fun ω => X ω * (1 : ℝ)) P from hconst.1)
    let Xm : Ω → ℝ := hX_int.aestronglyMeasurable.mk X
    have hXm_meas : Measurable Xm := hX_int.aestronglyMeasurable.measurable_mk
    have hXm_eq : X =ᵐ[P] Xm := hX_int.aestronglyMeasurable.ae_eq_mk
    -- Transport the hypothesis from `X` to the measurable representative `Xm`.
    have hCm : ∀ ⦃Y : Ω → ℝ⦄, Measurable Y →
        (∃ M : NNReal, ∀ ω, |Y ω| ≤ M) →
        Integrable (Xm * Y) P ∧
          |∫ ω, Xm ω * Y ω ∂P| ≤ (C : ℝ) * lpNorm Y (ENNReal.ofReal q) P := by
      intro Y hY_meas hY_bdd
      rcases hC hY_meas hY_bdd with ⟨hXY_int, hXY_bound⟩
      have hXmY_int : Integrable (Xm * Y) P := by
        refine hXY_int.congr ?_
        filter_upwards [hXm_eq] with ω hω
        simp [Xm, hω]
      have hIntegral_eq : ∫ ω, Xm ω * Y ω ∂P = ∫ ω, X ω * Y ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hXm_eq] with ω hω
        simp [Xm, hω]
      refine ⟨hXmY_int, ?_⟩
      rw [hIntegral_eq]
      exact hXY_bound
    -- Each cutoff test yields a finite truncated `p`-moment with a uniform bound.
    have hcutoff_int_bound : ∀ n : ℕ,
        Integrable (cutoffPower p Xm n) P ∧
          ∫ ω, cutoffPower p Xm n ω ∂P ≤ (C : ℝ) ^ p := by
      intro n
      rcases cutoffSignedPower_measurable_bound hp hXm_meas n with ⟨hYn_meas, hYn_bdd⟩
      have hYn_memLp : MemLp (cutoffSignedPower p Xm n) (ENNReal.ofReal q) P :=
        by
          rcases hYn_bdd with ⟨M, hM⟩
          refine MemLp.of_bound hYn_meas.aestronglyMeasurable (M : ℝ) ?_
          exact Filter.Eventually.of_forall fun ω => by
            simpa [Real.norm_eq_abs] using hM ω
      have hcutoff_int : Integrable (cutoffPower p Xm n) P := by
        have hnorm_int :
            Integrable
              (fun ω => ‖cutoffSignedPower p Xm n ω‖ ^ (ENNReal.ofReal q).toReal) P :=
          (integrable_norm_rpow_iff hYn_meas.aestronglyMeasurable
            (show ENNReal.ofReal q ≠ 0 by positivity) (by simp)).2 hYn_memLp
        refine hnorm_int.congr ?_
        exact Filter.Eventually.of_forall fun ω => by
          simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hq_nonneg] using
            cutoffSignedPower_abs_rpow_eq_cutoffPower hpq (X := Xm) n ω
      have hcutoff_nonneg : 0 ≤ᵐ[P] cutoffPower p Xm n :=
        Filter.Eventually.of_forall fun ω => Real.rpow_nonneg
          (le_min (abs_nonneg _) (Nat.cast_nonneg n)) _
      rcases hCm hYn_meas hYn_bdd with ⟨hpair_int, hpair_bound⟩
      have hpair_lower :
          ∫ ω, cutoffPower p Xm n ω ∂P ≤
            ∫ ω, Xm ω * cutoffSignedPower p Xm n ω ∂P := by
        refine integral_mono hcutoff_int hpair_int ?_
        intro ω
        exact cutoffPower_le_mul_cutoffSignedPower hp (X := Xm) n ω
      have hLp_eq :
          lpNorm (cutoffSignedPower p Xm n) (ENNReal.ofReal q) P =
            (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / q) := by
        calc
          lpNorm (cutoffSignedPower p Xm n) (ENNReal.ofReal q) P
              = (∫ ω, ‖cutoffSignedPower p Xm n ω‖ ^ q ∂P) ^ (1 / q) := by
                  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp)
                    hYn_meas.aestronglyMeasurable]
                  simp [ENNReal.toReal_ofReal hq_nonneg]
          _ = (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / q) := by
              congr 1
              refine integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun ω => by
                simpa [Real.norm_eq_abs] using
                  cutoffSignedPower_abs_rpow_eq_cutoffPower hpq (X := Xm) n ω
      have hmoment_le :
          ∫ ω, cutoffPower p Xm n ω ∂P ≤
            (C : ℝ) * (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / q) := by
        calc
          ∫ ω, cutoffPower p Xm n ω ∂P
              ≤ ∫ ω, Xm ω * cutoffSignedPower p Xm n ω ∂P := hpair_lower
          _ ≤ |∫ ω, Xm ω * cutoffSignedPower p Xm n ω ∂P| := le_abs_self _
          _ ≤ (C : ℝ) * lpNorm (cutoffSignedPower p Xm n) (ENNReal.ofReal q) P := hpair_bound
          _ = (C : ℝ) * (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / q) := by rw [hLp_eq]
      have hcutoff_nonneg_int : 0 ≤ ∫ ω, cutoffPower p Xm n ω ∂P :=
        integral_nonneg_of_ae hcutoff_nonneg
      refine ⟨hcutoff_int, ?_⟩
      by_cases hzero : ∫ ω, cutoffPower p Xm n ω ∂P = 0
      · simpa [hzero] using Real.rpow_nonneg (show 0 ≤ (C : ℝ) from C.2) p
      · have hpos_int : 0 < ∫ ω, cutoffPower p Xm n ω ∂P := by
          exact lt_of_le_of_ne hcutoff_nonneg_int (by simpa [eq_comm] using hzero)
        have hsplit :
            ∫ ω, cutoffPower p Xm n ω ∂P =
              (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / p) *
                (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / q) := by
          have hinv : 1 / p + 1 / q = 1 := by
            simpa [one_div] using hpq.inv_add_inv_eq_one
          calc
            ∫ ω, cutoffPower p Xm n ω ∂P
                = (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 : ℝ) := by
                    rw [Real.rpow_one]
            _ = (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / p + 1 / q) := by
                    rw [hinv]
            _ = (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / p) *
                  (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / q) := by
                    rw [Real.rpow_add hpos_int]
        have hroot_le : (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / p) ≤ (C : ℝ) := by
          have hqpow_pos :
              0 < (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / q) :=
            Real.rpow_pos_of_pos hpos_int _
          have hmul_le :
              (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / p) *
                  (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / q) ≤
                (C : ℝ) * (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / q) := by
            calc
              (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / p) *
                  (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / q)
                  = ∫ ω, cutoffPower p Xm n ω ∂P := hsplit.symm
              _ ≤ (C : ℝ) * (∫ ω, cutoffPower p Xm n ω ∂P) ^ (1 / q) := hmoment_le
          exact le_of_mul_le_mul_right hmul_le hqpow_pos
        have hroot_le' : (∫ ω, cutoffPower p Xm n ω ∂P) ^ p⁻¹ ≤ (C : ℝ) := by
          simpa [one_div] using hroot_le
        exact (Real.rpow_inv_le_iff_of_pos hcutoff_nonneg_int (show 0 ≤ (C : ℝ) from C.2)
          hp_pos).1 hroot_le'
    have hcutoff_nonneg : ∀ n : ℕ, 0 ≤ᵐ[P] cutoffPower p Xm n :=
      fun n => Filter.Eventually.of_forall fun ω =>
        Real.rpow_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg n)) _
    -- Monotone convergence upgrades the uniform cutoff bound to a full `p`-moment bound.
    have hpower_lintegral :
        ∫⁻ ω, ENNReal.ofReal (|Xm ω| ^ p) ∂P ≤ ENNReal.ofReal ((C : ℝ) ^ p) := by
      have hcutoff_meas : ∀ n : ℕ, Measurable fun ω => ENNReal.ofReal (cutoffPower p Xm n ω) :=
        fun n => by
          simpa [cutoffPower] using ((hXm_meas.abs.min measurable_const).pow_const p).ennreal_ofReal
      have hcutoff_mono :
          Monotone fun n : ℕ => fun ω => ENNReal.ofReal (cutoffPower p Xm n ω) := by
        intro n m hnm ω
        apply ENNReal.ofReal_le_ofReal
        refine Real.rpow_le_rpow (le_min (abs_nonneg _) (Nat.cast_nonneg n)) ?_ hp_nonneg
        exact min_le_min le_rfl (by exact_mod_cast hnm)
      calc
        ∫⁻ ω, ENNReal.ofReal (|Xm ω| ^ p) ∂P
            = ∫⁻ ω, ⨆ n : ℕ, ENNReal.ofReal (cutoffPower p Xm n ω) ∂P := by
                congr with ω
                symm
                exact iSup_cutoffPower_eq hp_nonneg (X := Xm) ω
        _ = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (cutoffPower p Xm n ω) ∂P := by
              rw [lintegral_iSup hcutoff_meas hcutoff_mono]
        _ ≤ ENNReal.ofReal ((C : ℝ) ^ p) := by
              refine iSup_le fun n => ?_
              have hcutoff_int := (hcutoff_int_bound n).1
              have hcutoff_bound := (hcutoff_int_bound n).2
              rw [← ofReal_integral_eq_lintegral_ofReal hcutoff_int (hcutoff_nonneg n)]
              exact ENNReal.ofReal_le_ofReal hcutoff_bound
    have hpower_lintegrable :
        Integrable (fun ω => |Xm ω| ^ p) P := by
      refine (lintegral_ofReal_ne_top_iff_integrable
        ((hXm_meas.abs.pow_const p).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)).1 ?_
      exact ne_top_of_le_ne_top (by simp) hpower_lintegral
    -- Convert the `p`-moment of the representative back into `MemLp X`.
    have hXm_memLp : MemLp Xm (ENNReal.ofReal p) P := by
      rw [← integrable_norm_rpow_iff hXm_meas.aestronglyMeasurable (by positivity) (by simp)]
      simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp_nonneg] using hpower_lintegrable
    exact (memLp_congr_ae hXm_eq).2 hXm_memLp

end MeasureTheory
