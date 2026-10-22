/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Example_20_9

open Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ProbabilityTheory

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  refine ⟨?_⟩
  simpa using
    (AddCircle.measure_univ :
      (volume : Measure UnitAddCircle) Set.univ = ENNReal.ofReal (1 : ℝ))

/-- The leading digit in the base-`p` expansion of `n`, i.e. the unique digit `d` with
`n / p ^ Nat.log p n = d`. -/
def baseLeadingDigit (p n : ℕ) : ℕ :=
  n / p ^ Nat.log p n

-- Proof sketch: `p ^ Nat.log p n ≤ n < p ^ (Nat.log p n + 1)`, so dividing by `p ^ Nat.log p n`
-- leaves a quotient strictly smaller than `p`.
/-- The leading digit of a nonzero natural number in base `p` is strictly less than `p`. -/
theorem baseLeadingDigit_lt_base {p n : ℕ} (hp : 1 < p) (_hn : n ≠ 0) :
    baseLeadingDigit p n < p := by
  rw [baseLeadingDigit]
  have hkpos : 0 < p ^ Nat.log p n := by
    simpa using (Nat.pow_pos (Nat.zero_lt_of_lt hp) : 0 < p ^ Nat.log p n)
  have hlt : n < p ^ (Nat.log p n).succ := Nat.lt_pow_succ_log_self hp n
  rw [pow_succ'] at hlt
  exact (Nat.div_lt_iff_lt_mul hkpos).2 (by simpa [Nat.mul_comm, Nat.mul_left_comm] using hlt)

/-- Helper for Exercise 20.3.2: the leading base-`p` digit of a nonzero natural number is the
quotient by the largest power `p ^ Nat.log p n` that still divides the scale of `n`. -/
lemma baseLeadingDigit_eq_selfDivPowLog {p n : ℕ} (_hp : 1 < p) (_hn : n ≠ 0) :
    baseLeadingDigit p n = n / p ^ Nat.log p n := by
  rfl

/-- Helper for Exercise 20.3.2: identifying the leading digit is equivalent to identifying the
top-scale quotient `n / p ^ Nat.log p n`. -/
lemma baseLeadingDigit_eq_iff_selfDivPowLog_eq {p n d : ℕ}
    (_hp : 1 < p) (_hn : n ≠ 0) :
    baseLeadingDigit p n = d ↔ n / p ^ Nat.log p n = d := by
  rfl

/-- Helper for Exercise 20.3.2: a leading-digit condition is equivalent to placing
`Int.fract (Real.logb p n)` in the corresponding logarithmic interval. -/
lemma baseLeadingDigit_eq_iff_fractLogb_mem_Ico {p n d : ℕ}
    (hp : 1 < p) (hn : n ≠ 0) (hd1 : 1 ≤ d) (_hd_lt : d < p) :
    baseLeadingDigit p n = d ↔
      Int.fract (Real.logb p n) ∈ Set.Ico (Real.logb p d) (Real.logb p (d + 1)) := by
  let k := Nat.log p n
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  have hp_ne_one : (p : ℝ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hp)
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hd0 : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
  have hd1' : 0 < (d + 1 : ℝ) := by positivity
  have hkpow_pos : 0 < p ^ k := Nat.pow_pos (Nat.zero_lt_of_lt hp)
  have hfract : Int.fract (Real.logb p n) = Real.logb p n - k := by
    rw [← Int.self_sub_floor, Real.floor_logb_natCast (show 0 ≤ (n : ℝ) by positivity),
      Int.log_natCast, Int.cast_natCast]
  have hquotient :
      n / p ^ k = d ↔ d * p ^ k ≤ n ∧ n < (d + 1) * p ^ k := by
    constructor
    · intro hdiv
      have hdecomp : n = d * p ^ k + n % p ^ k := by
        simpa [hdiv, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.mod_add_div n (p ^ k)).symm
      have hmod_lt : n % p ^ k < p ^ k := Nat.mod_lt _ hkpow_pos
      constructor
      · rw [hdecomp]
        exact Nat.le_add_right _ _
      · rw [hdecomp]
        have := Nat.add_lt_add_left hmod_lt (d * p ^ k)
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    · intro h
      apply le_antisymm
      · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hkpow_pos).2 h.2)
      · exact (Nat.le_div_iff_mul_le hkpow_pos).2 h.1
  rw [baseLeadingDigit_eq_iff_selfDivPowLog_eq hp hn, hfract, Set.mem_Ico]
  constructor
  · intro h
    have hbounds := hquotient.mp h
    constructor
    · have hpow_le : (p : ℝ) ^ ((k : ℝ) + Real.logb p d) ≤ n := by
        have hcast : (((d * p ^ k : ℕ) : ℝ)) ≤ n := by
          exact_mod_cast hbounds.1
        calc
          (p : ℝ) ^ ((k : ℝ) + Real.logb p d)
              = ((p : ℝ) ^ k) * d := by
                  rw [Real.rpow_add hp0, Real.rpow_natCast, Real.rpow_logb hp0 hp_ne_one hd0]
          _ = (((d * p ^ k : ℕ) : ℝ)) := by
                  norm_num [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
          _ ≤ n := hcast
      have hlog_le : (k : ℝ) + Real.logb p d ≤ Real.logb p n :=
        (Real.le_logb_iff_rpow_le (b := (p : ℝ)) (by exact_mod_cast hp) hn0).2 hpow_le
      linarith
    · have hlt_rpow : n < (p : ℝ) ^ ((k : ℝ) + Real.logb p (d + 1)) := by
        have hcast : (n : ℝ) < (((d + 1) * p ^ k : ℕ) : ℝ) := by
          exact_mod_cast hbounds.2
        calc
          (n : ℝ) < (((d + 1) * p ^ k : ℕ) : ℝ) := hcast
          _ = ((p : ℝ) ^ k) * (d + 1) := by
                norm_num [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
          _ = (p : ℝ) ^ ((k : ℝ) + Real.logb p (d + 1)) := by
                rw [Real.rpow_add hp0, Real.rpow_natCast, Real.rpow_logb hp0 hp_ne_one hd1']
      have hlog_lt : Real.logb p n < (k : ℝ) + Real.logb p (d + 1) :=
        (Real.logb_lt_iff_lt_rpow (b := (p : ℝ)) (by exact_mod_cast hp) hn0).2 hlt_rpow
      linarith
  · intro h
    have hlow : (k : ℝ) + Real.logb p d ≤ Real.logb p n := by
      linarith
    have hupp : Real.logb p n < (k : ℝ) + Real.logb p (d + 1) := by
      linarith
    have hnat_low : d * p ^ k ≤ n := by
      have hpow_le : (p : ℝ) ^ ((k : ℝ) + Real.logb p d) ≤ n :=
        (Real.le_logb_iff_rpow_le (b := (p : ℝ)) (by exact_mod_cast hp) hn0).1 hlow
      have hrewrite :
          (p : ℝ) ^ ((k : ℝ) + Real.logb p d) = (((d * p ^ k : ℕ) : ℝ)) := by
        rw [Real.rpow_add hp0, Real.rpow_natCast, Real.rpow_logb hp0 hp_ne_one hd0]
        norm_num [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
      have hcast : (((d * p ^ k : ℕ) : ℝ)) ≤ n := by
        simpa [hrewrite] using hpow_le
      exact_mod_cast hcast
    have hnat_upp : n < (d + 1) * p ^ k := by
      have hpow_lt : n < (p : ℝ) ^ ((k : ℝ) + Real.logb p (d + 1)) :=
        (Real.logb_lt_iff_lt_rpow (b := (p : ℝ)) (by exact_mod_cast hp) hn0).1 hupp
      have hrewrite :
          (p : ℝ) ^ ((k : ℝ) + Real.logb p (d + 1)) = ((((d + 1) * p ^ k : ℕ) : ℝ)) := by
        rw [Real.rpow_add hp0, Real.rpow_natCast, Real.rpow_logb hp0 hp_ne_one hd1']
        norm_num [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
      have hcast : (n : ℝ) < ((((d + 1) * p ^ k : ℕ) : ℝ)) := by
        simpa [hrewrite] using hpow_lt
      exact_mod_cast hcast
    exact hquotient.mpr ⟨hnat_low, hnat_upp⟩

/-- Helper for Exercise 20.3.2: the logarithmic step `Real.logb p q` is irrational when `p` is
squarefree and `2 ≤ q < p`. -/
lemma irrationalLogbNat_of_squarefree {p q : ℕ}
    (hpSq : Squarefree p) (hq2 : 2 ≤ q) (hq_lt : q < p) :
    Irrational (Real.logb p q) := by
  have hp : 1 < p := lt_trans hq2 hq_lt
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  have hp_ne_one : (p : ℝ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hp)
  have hq0 : 0 < (q : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hq2)
  have hlog_pos : 0 < Real.logb p q := Real.logb_pos (by exact_mod_cast hp) (by exact_mod_cast hq2)
  rw [Irrational]
  rintro ⟨r, hr⟩
  have hr_pos : 0 < (r : ℝ) := by simpa [hr] using hlog_pos
  have hr_pos_rat : 0 < r := by exact_mod_cast hr_pos
  have hnum_nonneg : 0 ≤ r.num := by
    exact le_of_lt (Rat.num_pos.mpr hr_pos_rat)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hnum_nonneg
  have hm_pos : 0 < m := by
    have hm_pos_int : (0 : ℤ) < (m : ℤ) := by
      simpa [hm] using (Rat.num_pos.mpr hr_pos_rat)
    exact Int.ofNat_lt.mp hm_pos_int
  have hr' : Real.logb p q = (m : ℝ) / r.den := by
    calc
      Real.logb p q = (r : ℝ) := by simpa using hr.symm
      _ = (r.num : ℝ) / r.den := by rw [Rat.cast_def]
      _ = (m : ℝ) / r.den := by rw [hm, Int.cast_natCast]
  have hq_eq : (p : ℝ) ^ ((m : ℝ) / r.den) = q := by
    rw [← Real.logb_eq_iff_rpow_eq hp0 hp_ne_one hq0]
    exact hr'
  have hden0 : (r.den : ℝ) ≠ 0 := by
    exact_mod_cast (Rat.den_nz r)
  have hpow_nat : q ^ r.den = p ^ m := by
    have hpow_real : (q : ℝ) ^ r.den = (p : ℝ) ^ m := by
      calc
        (q : ℝ) ^ r.den = ((p : ℝ) ^ ((m : ℝ) / r.den)) ^ r.den := by rw [hq_eq.symm]
        _ = (p : ℝ) ^ (((m : ℝ) / r.den) * r.den) := by
              rw [← Real.rpow_mul_natCast hp0.le]
        _ = (p : ℝ) ^ (m : ℝ) := by
              congr 1
              rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hden0, mul_one]
        _ = (p : ℝ) ^ m := by rw [Real.rpow_natCast]
    exact_mod_cast hpow_real
  obtain ⟨s, hsprime, hsdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hp)
  have hsfac : p.factorization s = 1 :=
    Nat.factorization_eq_one_of_squarefree hpSq hsprime hsdvd
  have hfac : r.den * q.factorization s = m * p.factorization s := by
    simpa [Nat.factorization_pow, nsmul_eq_mul] using
      congrArg (fun t : ℕ => t.factorization s) hpow_nat
  have hden_dvd_m : r.den ∣ m := by
    refine ⟨q.factorization s, ?_⟩
    simpa [hsfac, mul_comm, mul_left_comm, mul_assoc] using hfac.symm
  have hcop : m.Coprime r.den := by
    simpa [hm, Int.natAbs_natCast] using r.reduced
  have hden_eq_one : r.den = 1 := by
    exact Nat.eq_one_of_dvd_coprimes hcop hden_dvd_m (dvd_rfl : r.den ∣ r.den)
  have hq_eq_nat : q = p ^ m := by
    simpa [hden_eq_one] using hpow_nat
  have hp_le_q : p ≤ q := by
    rw [hq_eq_nat]
    cases m with
    | zero =>
        exact (Nat.not_lt_zero _ hm_pos).elim
    | succ m =>
        rw [pow_succ]
        simpa [Nat.mul_comm] using
          Nat.le_mul_of_pos_right p (by simpa using
            (Nat.pow_pos (Nat.zero_lt_of_lt hp) : 0 < p ^ m))
  exact (Nat.not_le_of_gt hq_lt) hp_le_q

section

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decPred

/-- Helper for Exercise 20.3.2: translating the `n`-th Fourier character by `α` multiplies it by
the phase at `α`. -/
lemma fourierTranslate_eq_mul {α : ℝ} (n : ℤ) (x : UnitAddCircle) :
    fourier (T := (1 : ℝ)) n (x + (α : UnitAddCircle)) =
      fourier (T := (1 : ℝ)) n (α : UnitAddCircle) * fourier (T := (1 : ℝ)) n x := by
  -- Proof comment: `fourier n` factors through `toCircle`, so it converts addition on the circle
  -- into multiplication on `ℂ`.
  rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  simp [mul_comm]

/-- Helper for Exercise 20.3.2: every nonzero Fourier mode has zero mean on `UnitAddCircle`. -/
lemma integral_fourier_eq_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ z : UnitAddCircle, fourier (T := (1 : ℝ)) n z ∂(volume : Measure UnitAddCircle) = 0 := by
  -- Proof comment: the zero-th Fourier coefficient of `fourier n` vanishes unless `n = 0`.
  have hCoeffZero : fourierCoeff (T := (1 : ℝ)) (fourier (T := (1 : ℝ)) n) 0 = 0 := by
    simpa [hn] using
      congrArg (fun φ : ℤ → ℂ => φ 0) (fourierCoeff_fourier (T := (1 : ℝ)) n)
  have hCoeff :
      ∫ z : UnitAddCircle, fourier (T := (1 : ℝ)) n z ∂AddCircle.haarAddCircle = 0 := by
    simpa [fourierCoeff, fourier_zero] using hCoeffZero
  have hHaar :
      ∫ z : UnitAddCircle, fourier (T := (1 : ℝ)) n z ∂AddCircle.haarAddCircle =
        ∫ z : UnitAddCircle, fourier (T := (1 : ℝ)) n z := by
    simpa using AddCircle.integral_haarAddCircle (T := (1 : ℝ))
      (f := fourier (T := (1 : ℝ)) n)
  simpa using hHaar.symm.trans hCoeff

/-- Helper for Exercise 20.3.2: an irrational rotation never gives the trivial phase on a nonzero
Fourier mode. -/
lemma fourierStep_ne_one_of_irrational {α : ℝ} (hα : Irrational α) {n : ℤ} (hn : n ≠ 0) :
    fourier (T := (1 : ℝ)) n (α : UnitAddCircle) ≠ 1 := by
  -- Proof comment: `fourier n (α) = 1` would force `(n : ℝ) * α` to be an integer, contradicting
  -- irrationality of `α`.
  intro hFourier
  have hExp : Complex.exp (((2 * Real.pi * Complex.I) * ((n : ℝ) * α))) = Complex.exp 0 := by
    simpa [fourier_coe_apply, mul_assoc, mul_left_comm, mul_comm] using hFourier
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hExp
  have hm' : ((n : ℝ) * α : ℂ) = m := by
    apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
    simpa [Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm] using hm
  have hmul_irr : Irrational ((n : ℝ) * α) := (irrational_intCast_mul_iff).2 ⟨hn, hα⟩
  exact hmul_irr.ne_int m (by exact_mod_cast hm')

/-- Helper for Exercise 20.3.2: iterating precomposition by a self-map evaluates along the
corresponding orbit. -/
lemma iterate_precompose_apply {τ : C(UnitAddCircle, UnitAddCircle)}
    (f : C(UnitAddCircle, ℂ)) :
    ∀ k : ℕ, ∀ x : UnitAddCircle, (((fun g : C(UnitAddCircle, ℂ) ↦ g.comp τ)^[k]) f) x =
      f ((τ^[k]) x)
  | 0, x => by
      -- Proof comment: the zeroth iterate is the identity on continuous maps.
      simp
  | k + 1, x => by
      -- Proof comment: one more precomposition step just appends one more iterate of `τ`.
      rw [Function.iterate_succ_apply', ContinuousMap.comp_apply]
      rw [iterate_precompose_apply (τ := τ) f k]
      simpa using congrArg f ((Function.Commute.self_iterate τ k).eq x).symm

/-- Helper for Exercise 20.3.2: iterating the translation `x ↦ x + α` adds `n • α` to the
starting point. -/
lemma addRightIterate_apply (α : UnitAddCircle) :
    ∀ n : ℕ, ∀ x : UnitAddCircle,
      ((fun y : UnitAddCircle ↦ y + α)^[n]) x = x + n • α
  | 0, x => by
      -- Proof comment: the zeroth iterate does not move the starting point.
      simp
  | n + 1, x => by
      -- Proof comment: each extra iterate contributes one more copy of `α`.
      rw [Function.iterate_succ_apply', addRightIterate_apply α n x]
      simp [add_assoc, add_nsmul]

/-- Helper for Exercise 20.3.2: the function-space Birkhoff averages for precomposition by `τ`
evaluate to the usual scalar Birkhoff averages along the orbit of `τ`. -/
lemma birkhoffAverage_precompose_apply {τ : C(UnitAddCircle, UnitAddCircle)}
    (f : C(UnitAddCircle, ℂ)) (n : ℕ) (x : UnitAddCircle) :
    birkhoffAverage ℂ (fun g : C(UnitAddCircle, ℂ) ↦ g.comp τ) id n f x =
      birkhoffAverage ℂ τ f n x := by
  -- Proof comment: after unfolding the two Birkhoff sums, both sides are the same finite orbit
  -- average, term by term.
  simp [birkhoffAverage, birkhoffSum, iterate_precompose_apply]

/-- Helper for Exercise 20.3.2: the scalar Fourier phase along the irrational rotation orbit
produces the expected multiplicative iterate formula. -/
lemma fourierIterate_eq_pow_mul {α : ℝ} (n : ℤ) (x : UnitAddCircle) :
    ∀ k : ℕ,
      fourier (T := (1 : ℝ)) n (((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[k]) x) =
        fourier (T := (1 : ℝ)) n (α : UnitAddCircle) ^ k * fourier (T := (1 : ℝ)) n x
  | 0 => by
      -- Proof comment: the zeroth iterate contributes the trivial power `1`.
      simp
  | k + 1 => by
      -- Proof comment: one rotation step multiplies by the fixed phase at `α`, and the induction
      -- hypothesis accumulates the remaining powers.
      rw [Function.iterate_succ_apply', fourierTranslate_eq_mul, fourierIterate_eq_pow_mul n x k,
        pow_succ]
      ring

/-- Helper for Exercise 20.3.2: Cesàro averages of a bounded nontrivial geometric progression in
`ℂ` converge to `0`. -/
lemma tendsto_geomAverage_zero_of_ne_one {ζ : ℂ} (hζ : ζ ≠ 1) (hζ_norm : ‖ζ‖ ≤ 1) :
    Tendsto
      (fun N : ℕ ↦ ((Finset.sum (Finset.range N) fun i ↦ ζ ^ i) / (N : ℂ)))
      atTop
      (𝓝 0) := by
  -- Proof comment: the geometric sum formula gives a uniform bound on the numerator, and dividing
  -- by `N` forces the average to vanish.
  refine squeeze_zero_norm (a := fun N : ℕ ↦ (2 * ‖(ζ - 1)⁻¹‖ : ℝ) / N) (fun N ↦ ?_) ?_
  · calc
      ‖((Finset.sum (Finset.range N) fun i ↦ ζ ^ i) / (N : ℂ))‖
          = ‖Finset.sum (Finset.range N) (fun i ↦ ζ ^ i)‖ / N := by
              simp [norm_div]
      _ ≤ (2 * ‖(ζ - 1)⁻¹‖) / N := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            calc
              ‖Finset.sum (Finset.range N) (fun i ↦ ζ ^ i)‖ = ‖(ζ ^ N - 1) / (ζ - 1)‖ := by
                rw [geom_sum_eq hζ N]
              _ = ‖ζ ^ N - 1‖ * ‖(ζ - 1)⁻¹‖ := by
                rw [div_eq_mul_inv, norm_mul]
              _ ≤ (‖ζ ^ N‖ + ‖(1 : ℂ)‖) * ‖(ζ - 1)⁻¹‖ := by
                gcongr
                exact norm_sub_le _ _
              _ ≤ 2 * ‖(ζ - 1)⁻¹‖ := by
                have hpow : ‖ζ ^ N‖ ≤ 1 := by
                  calc
                    ‖ζ ^ N‖ = ‖ζ‖ ^ N := by rw [norm_pow]
                    _ ≤ 1 ^ N := by
                      gcongr
                    _ = 1 := by simp
                have hone : ‖(1 : ℂ)‖ ≤ 1 := by simp
                have hsum : ‖ζ ^ N‖ + ‖(1 : ℂ)‖ ≤ 2 := by linarith
                exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  · simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ ↦ (2 * ‖(ζ - 1)⁻¹‖ : ℝ) / N) atTop (𝓝 0))

/-- Helper for Exercise 20.3.2: precomposition by the irrational rotation is linear on Birkhoff
averages with respect to the initial continuous observable. -/
lemma rotation_birkhoffAverage_add {τ : C(UnitAddCircle, UnitAddCircle)}
    (f g : C(UnitAddCircle, ℂ)) :
    ∀ n : ℕ,
      birkhoffAverage ℂ (fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ) id n (f + g) =
        birkhoffAverage ℂ (fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ) id n f +
          birkhoffAverage ℂ (fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ) id n g
  | n => by
      -- Proof comment: every iterate of the precomposition operator preserves addition, so the
      -- whole Birkhoff sum splits termwise.
      have hIterAdd :
          ∀ i : ℕ,
            ((fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ)^[i]) (f + g) =
              ((fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ)^[i]) f +
                ((fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ)^[i]) g := by
        intro i
        induction i with
        | zero =>
            rfl
        | succ i ih =>
            ext x
            simp [Function.iterate_succ_apply', ih]
      rw [birkhoffAverage, birkhoffAverage, birkhoffAverage, birkhoffSum, birkhoffSum, birkhoffSum]
      simp [smul_add, Finset.sum_add_distrib, hIterAdd]

/-- Helper for Exercise 20.3.2: precomposition by the irrational rotation is linear on Birkhoff
averages with respect to scalar multiplication of the initial continuous observable. -/
lemma rotation_birkhoffAverage_smul {τ : C(UnitAddCircle, UnitAddCircle)} (c : ℂ)
    (f : C(UnitAddCircle, ℂ)) :
    ∀ n : ℕ,
      birkhoffAverage ℂ (fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ) id n (c • f) =
        c • birkhoffAverage ℂ (fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ) id n f
  | n => by
      -- Proof comment: precomposition commutes with scalar multiplication, so the Birkhoff sum
      -- factors out the scalar.
      have hIterSmul :
          ∀ i : ℕ,
            ((fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ)^[i]) (c • f) =
              c • ((fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ)^[i]) f := by
        intro i
        induction i with
        | zero =>
            rfl
        | succ i ih =>
            ext x
            simp [Function.iterate_succ_apply', ih]
      rw [birkhoffAverage, birkhoffAverage, birkhoffSum, birkhoffSum]
      simpa [Finset.smul_sum, hIterSmul, smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 20.3.2: each Fourier mode already satisfies the rotation limit in the
continuous-map norm. -/
lemma irrationalRotation_birkhoffAverage_tendsto_of_fourierContinuousMap {α : ℝ}
    (hα : Irrational α) (n : ℤ) :
    Tendsto
      (fun N : ℕ ↦
        birkhoffAverage ℂ
          (fun f : C(UnitAddCircle, ℂ) ↦
            f.comp ⟨fun y : UnitAddCircle ↦ y + (α : UnitAddCircle), by fun_prop⟩)
          id N (fourier (T := (1 : ℝ)) n))
      atTop
      (𝓝
        (ContinuousMap.const UnitAddCircle
          ((volume : Measure UnitAddCircle)[fun z ↦ fourier (T := (1 : ℝ)) n z]))) := by
  let τ :
      C(UnitAddCircle, UnitAddCircle) :=
    ⟨fun y : UnitAddCircle ↦ y + (α : UnitAddCircle), by fun_prop⟩
  by_cases hn : n = 0
  · -- Proof comment: the zero Fourier mode is the constant function `1`, so every Birkhoff
    -- average is already equal to the mean.
    subst hn
    have hfixed :
        Function.IsFixedPt (fun f : C(UnitAddCircle, ℂ) ↦ f.comp τ) (1 : C(UnitAddCircle, ℂ)) := by
      ext x
      simp [τ]
    have hmean :
        (ContinuousMap.const UnitAddCircle
          ((volume : Measure UnitAddCircle)[fun z ↦ fourier (T := (1 : ℝ)) 0 z])) =
          (1 : C(UnitAddCircle, ℂ)) := by
      ext x
      simp
    have hFormula :
        ∀ N : ℕ,
          birkhoffAverage ℂ (fun f : C(UnitAddCircle, ℂ) ↦ f.comp τ) id N
              (fourier (T := (1 : ℝ)) 0) =
            birkhoffAverage ℂ (fun f : C(UnitAddCircle, ℂ) ↦ f.comp τ) id N (1 : C(UnitAddCircle, ℂ)) := by
      intro N
      have hFourierZero : fourier (T := (1 : ℝ)) 0 = (1 : C(UnitAddCircle, ℂ)) := by
        ext x
        simp [fourier_zero]
      simpa [hFourierZero]
    exact (tendsto_congr' (Filter.Eventually.of_forall hFormula)).2 <| by
      simpa [hmean] using hfixed.tendsto_birkhoffAverage ℂ id
  · -- Proof comment: the nonzero modes reduce to a scalar geometric average times the fixed mode.
    let ζ : ℂ := fourier (T := (1 : ℝ)) n (α : UnitAddCircle)
    have hζ : ζ ≠ 1 := fourierStep_ne_one_of_irrational hα hn
    have hζ_norm : ‖ζ‖ ≤ 1 := by
      rw [show ζ = Complex.exp (((2 * Real.pi * Complex.I) * ((n : ℝ) * α))) by
          simp [ζ, fourier_coe_apply, mul_assoc, mul_left_comm, mul_comm]]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * ((n : ℝ) * α))).le
    have hFormula :
        ∀ N : ℕ,
          birkhoffAverage ℂ (fun f : C(UnitAddCircle, ℂ) ↦ f.comp τ) id N (fourier (T := (1 : ℝ)) n) =
            (((Finset.sum (Finset.range N) fun i ↦ ζ ^ i) / (N : ℂ))) •
              fourier (T := (1 : ℝ)) n := by
      intro N
      ext x
      rw [birkhoffAverage_precompose_apply (τ := τ) (f := fourier (T := (1 : ℝ)) n) N x, birkhoffAverage,
        birkhoffSum, smul_eq_mul]
      calc
        (N : ℂ)⁻¹ *
            Finset.sum (Finset.range N)
              (fun i ↦ fourier (T := (1 : ℝ)) n (((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x))
            =
          (N : ℂ)⁻¹ * Finset.sum (Finset.range N) (fun i ↦ ζ ^ i * fourier (T := (1 : ℝ)) n x) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              simpa [ζ] using fourierIterate_eq_pow_mul (α := α) n x i
        _ = (N : ℂ)⁻¹ * ((Finset.sum (Finset.range N) fun i ↦ ζ ^ i) * fourier (T := (1 : ℝ)) n x) := by
              rw [Finset.sum_mul]
        _ = (((Finset.sum (Finset.range N) fun i ↦ ζ ^ i) / (N : ℂ))) * fourier (T := (1 : ℝ)) n x := by
              rw [div_eq_mul_inv]
              ring
        _ = ((((Finset.sum (Finset.range N) fun i ↦ ζ ^ i) / (N : ℂ))) •
              fourier (T := (1 : ℝ)) n) x := by
              simp [smul_eq_mul]
    have hZero :
        Tendsto
          (fun N : ℕ ↦
            (((Finset.sum (Finset.range N) fun i ↦ ζ ^ i) / (N : ℂ))) • fourier (T := (1 : ℝ)) n)
          atTop (𝓝 (0 : C(UnitAddCircle, ℂ))) := by
      simpa using
        (tendsto_geomAverage_zero_of_ne_one hζ hζ_norm).smul_const (fourier (T := (1 : ℝ)) n)
    have hmean_zero :
        ContinuousMap.const UnitAddCircle
          ((volume : Measure UnitAddCircle)[fun z ↦ fourier (T := (1 : ℝ)) n z]) = 0 := by
      have hIntegral : ((volume : Measure UnitAddCircle)[fun z ↦ fourier (T := (1 : ℝ)) n z]) = 0 :=
        integral_fourier_eq_zero hn
      ext x
      simpa using hIntegral
    have hZero' :
        Tendsto
          (fun N : ℕ ↦
            (((Finset.sum (Finset.range N) fun i ↦ ζ ^ i) / (N : ℂ))) • fourier (T := (1 : ℝ)) n)
          atTop
          (𝓝
            (ContinuousMap.const UnitAddCircle
              ((volume : Measure UnitAddCircle)[fun z ↦ fourier (T := (1 : ℝ)) n z]))) := by
      exact hmean_zero ▸ hZero
    exact (tendsto_congr' (Filter.Eventually.of_forall hFormula)).2 hZero'

/-- Helper for Exercise 20.3.2: the irrational rotation has the expected Cesàro limit for every
complex-valued continuous observable on `UnitAddCircle`. -/
lemma irrationalRotation_birkhoffAverage_tendsto_of_continuousComplex {α : ℝ}
    (hα : Irrational α) (f : C(UnitAddCircle, ℂ)) :
    Tendsto
      (fun N : ℕ ↦
        birkhoffAverage ℂ
          (fun h : C(UnitAddCircle, ℂ) ↦
            h.comp ⟨fun y : UnitAddCircle ↦ y + (α : UnitAddCircle), by fun_prop⟩)
          id N f)
      atTop
      (𝓝
        (ContinuousMap.const UnitAddCircle
          ((volume : Measure UnitAddCircle)[fun z ↦ f z]))) := by
  let τ :
      C(UnitAddCircle, UnitAddCircle) :=
    ⟨fun y : UnitAddCircle ↦ y + (α : UnitAddCircle), by fun_prop⟩
  let mean : C(UnitAddCircle, ℂ) → ℂ :=
    fun g ↦ (volume : Measure UnitAddCircle)[fun z ↦ g z]
  let limitMap : C(UnitAddCircle, ℂ) → C(UnitAddCircle, ℂ) :=
    fun g ↦ ContinuousMap.const UnitAddCircle (mean g)
  let good : Submodule ℂ C(UnitAddCircle, ℂ) := {
    carrier := {g | Tendsto (fun N : ℕ ↦ birkhoffAverage ℂ (fun h : C(UnitAddCircle, ℂ) ↦
        h.comp τ) id N g) atTop (𝓝 (limitMap g))}
    zero_mem' := by
      -- Proof comment: the zero function stays zero under every iterate.
      have hbirkhoff_zero :
          ∀ N : ℕ,
            birkhoffAverage ℂ (fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ) id N
              (0 : C(UnitAddCircle, ℂ)) = 0 := by
        have hIterZero :
            ∀ k : ℕ, ((fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ)^[k]) (0 : C(UnitAddCircle, ℂ)) = 0 := by
          intro k
          induction k with
          | zero =>
              rfl
          | succ k ih =>
              simpa [Function.iterate_succ_apply', ih]
        intro N
        rw [birkhoffAverage, birkhoffSum]
        by_cases hN : N = 0
        · simp [hN]
        · simp [hIterZero, hN]
      have hlimit_zero : limitMap 0 = 0 := by
        ext x
        simp [limitMap, mean]
      exact (tendsto_congr' (Filter.Eventually.of_forall hbirkhoff_zero)).2 <| by
        simpa [hlimit_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : C(UnitAddCircle, ℂ))) atTop (𝓝 0))
    add_mem' := by
      intro g h hg hh
      -- Proof comment: linearity in the initial condition lets us add convergent Birkhoff
      -- averages and the corresponding means.
      let gB : BoundedContinuousFunction UnitAddCircle ℂ := BoundedContinuousFunction.mkOfCompact g
      let hB : BoundedContinuousFunction UnitAddCircle ℂ := BoundedContinuousFunction.mkOfCompact h
      have hg_int : Integrable gB (volume : Measure UnitAddCircle) := gB.integrable (μ := volume)
      have hh_int : Integrable hB (volume : Measure UnitAddCircle) := hB.integrable (μ := volume)
      have hlimit_add : limitMap (g + h) = limitMap g + limitMap h := by
        ext x
        change mean (g + h) = mean g + mean h
        simpa [mean] using integral_add hg_int hh_int
      simpa [hlimit_add, rotation_birkhoffAverage_add] using hg.add hh
    smul_mem' := by
      intro c g hg
      -- Proof comment: scalar multiplication commutes both with the rotation operator and with the
      -- mean functional.
      have hlimit_smul : limitMap (c • g) = c • limitMap g := by
        ext x
        change mean (c • g) = c • mean g
        simpa [mean] using MeasureTheory.integral_const_mul c (fun z : UnitAddCircle ↦ g z)
      simpa [hlimit_smul, rotation_birkhoffAverage_smul] using hg.const_smul c }
  have hτ_lipschitz :
      LipschitzWith 1 (fun h : C(UnitAddCircle, ℂ) ↦ h.comp τ) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro g h
    rw [ContinuousMap.dist_le_iff_of_nonempty]
    intro x
    simpa using (ContinuousMap.dist_apply_le_dist (f := g) (g := h) (x := τ x))
  have hmean_lipschitz : LipschitzWith 1 mean := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro g h
    let gB : BoundedContinuousFunction UnitAddCircle ℂ := BoundedContinuousFunction.mkOfCompact g
    let hB : BoundedContinuousFunction UnitAddCircle ℂ := BoundedContinuousFunction.mkOfCompact h
    let diffB : BoundedContinuousFunction UnitAddCircle ℂ := BoundedContinuousFunction.mkOfCompact (g - h)
    have hg_int : Integrable gB (volume : Measure UnitAddCircle) := gB.integrable (μ := volume)
    have hh_int : Integrable hB (volume : Measure UnitAddCircle) := hB.integrable (μ := volume)
    calc
      dist (mean g) (mean h) = ‖mean g - mean h‖ := by
        rw [dist_eq_norm]
      _ = ‖∫ z, diffB z ∂(volume : Measure UnitAddCircle)‖ := by
        have hsub :
            mean g - mean h = ∫ z, diffB z ∂(volume : Measure UnitAddCircle) := by
          simpa [mean, diffB] using (integral_sub hg_int hh_int).symm
        rw [hsub]
      _ ≤ ‖diffB‖ := by
        simpa using
          (BoundedContinuousFunction.norm_integral_le_norm
            (μ := (volume : Measure UnitAddCircle)) diffB)
      _ = dist g h := by
        simpa [diffB, dist_eq_norm] using
          (BoundedContinuousFunction.norm_mkOfCompact (g - h))
      _ ≤ 1 * dist g h := by
        simpa
  have hlimit_cont : Continuous limitMap := by
    -- Proof comment: the limit function is the continuous constant-function embedding applied to
    -- the continuous mean functional.
    simpa [limitMap] using
      (ContinuousMap.continuous_const' : Continuous fun c : ℂ ↦ ContinuousMap.const UnitAddCircle c).comp
        hmean_lipschitz.continuous
  have hgood_closed : IsClosed (good : Set C(UnitAddCircle, ℂ)) := by
    -- Proof comment: the general closedness theorem applies in the ambient function space.
    simpa [good, limitMap] using
      (isClosed_setOf_tendsto_birkhoffAverage ℂ hτ_lipschitz uniformContinuous_id hlimit_cont)
  have hspan :
      Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤ good := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, rfl⟩
    simpa [good, limitMap] using irrationalRotation_birkhoffAverage_tendsto_of_fourierContinuousMap
      hα n
  have hgood_top : good = ⊤ := by
    apply top_unique
    have hclosure :
        (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure ≤ good :=
      Submodule.topologicalClosure_minimal _ hspan hgood_closed
    have hspan_top :
        (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure = ⊤ :=
      span_fourier_closure_eq_top (T := (1 : ℝ))
    simpa [hspan_top] using hclosure
  have hf_good : f ∈ good := by
    simpa [hgood_top] using (show f ∈ (⊤ : Submodule ℂ C(UnitAddCircle, ℂ)) by simp)
  -- Proof comment: the closed-submodule argument gives the desired norm convergence directly in the
  -- ambient continuous-function space.
  simpa [good, limitMap] using hf_good

/-- Helper for Exercise 20.3.2: the irrational rotation on `UnitAddCircle` has the expected
pointwise Cesàro limit for every continuous observable. -/
lemma irrationalRotation_birkhoffAverage_tendsto_of_continuous {α : ℝ}
    (hα : Irrational α) {f : UnitAddCircle → ℝ} (hf : Continuous f) :
    ∀ x : UnitAddCircle,
      Tendsto
        (birkhoffAverage ℝ (fun y : UnitAddCircle ↦ y + (α : UnitAddCircle)) f · x)
        atTop
        (𝓝 ((volume : Measure UnitAddCircle)[f])) := by
  let fC : C(UnitAddCircle, ℂ) := ⟨fun z ↦ Complex.ofReal (f z), Complex.continuous_ofReal.comp hf⟩
  have hComplex := irrationalRotation_birkhoffAverage_tendsto_of_continuousComplex hα fC
  intro x
  -- Proof comment: apply the complex-valued convergence theorem to `Complex.ofReal ∘ f`, then
  -- take real parts to return to the original real-valued observable.
  have hComplexAt :
      Tendsto
        (fun N : ℕ ↦ birkhoffAverage ℂ (fun y : UnitAddCircle ↦ y + (α : UnitAddCircle)) fC N x)
        atTop
        (𝓝 ((volume : Measure UnitAddCircle)[fun z ↦ fC z])) := by
    have hEval :
        Tendsto
          (fun N : ℕ ↦
            (birkhoffAverage ℂ
              (fun h : C(UnitAddCircle, ℂ) ↦
                h.comp ⟨fun y : UnitAddCircle ↦ y + (α : UnitAddCircle), by fun_prop⟩)
              id N fC) x)
          atTop
          (𝓝
            ((ContinuousMap.const UnitAddCircle
                ((volume : Measure UnitAddCircle)[fun z ↦ fC z])) x)) := by
      exact (((ContinuousMap.evalCLM ℂ x).continuous.tendsto _).comp hComplex)
    simpa [ContinuousMap.const_apply, birkhoffAverage_precompose_apply] using hEval
  have hRe :
      Tendsto
        (fun N : ℕ ↦
          Complex.re (birkhoffAverage ℂ (fun y : UnitAddCircle ↦ y + (α : UnitAddCircle)) fC N x))
        atTop
        (𝓝 (Complex.re ((volume : Measure UnitAddCircle)[fun z ↦ fC z]))) := by
    exact (Complex.continuous_re.tendsto _).comp hComplexAt
  have hMap :
      ∀ N : ℕ,
        Complex.re (birkhoffAverage ℂ (fun y : UnitAddCircle ↦ y + (α : UnitAddCircle)) fC N x) =
          birkhoffAverage ℝ (fun y : UnitAddCircle ↦ y + (α : UnitAddCircle)) f N x := by
    intro N
    simpa [fC] using
      (map_birkhoffAverage ℂ ℝ Complex.reAddGroupHom
        (fun y : UnitAddCircle ↦ y + (α : UnitAddCircle)) (fun z ↦ fC z) N x)
  have hMeanRe :
      Complex.re ((volume : Measure UnitAddCircle)[fun z ↦ fC z]) =
        (volume : Measure UnitAddCircle)[f] := by
    let fB : BoundedContinuousFunction UnitAddCircle ℂ := BoundedContinuousFunction.mkOfCompact fC
    have hfC_int : Integrable (fun z : UnitAddCircle ↦ fC z) (volume : Measure UnitAddCircle) := by
      simpa [fB] using (fB.integrable (μ := (volume : Measure UnitAddCircle)))
    simpa [fC] using (integral_re (μ := (volume : Measure UnitAddCircle)) hfC_int).symm
  have hReal :
      Tendsto
        (fun N : ℕ ↦ birkhoffAverage ℝ (fun y : UnitAddCircle ↦ y + (α : UnitAddCircle)) f N x)
        atTop
        (𝓝 (Complex.re ((volume : Measure UnitAddCircle)[fun z ↦ fC z]))) := by
    exact (tendsto_congr' (Filter.Eventually.of_forall fun N ↦ (hMap N).symm)).2 hRe
  simpa [hMeanRe] using hReal

/-- Helper for Exercise 20.3.2: the Birkhoff average of an indicator is the corresponding
cardinality ratio of visit times. -/
lemma birkhoffAverage_indicator_eq_cardRatio {α : ℝ} {s : Set UnitAddCircle} (n : ℕ)
    (x : UnitAddCircle) :
    birkhoffAverage ℝ (fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))
        (Set.indicator s (fun _ ↦ (1 : ℝ))) n x =
      (((Finset.range n).filter (fun i ↦
          ((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x ∈ s)).card : ℝ) / n := by
  let times : Set ℕ :=
    {i : ℕ | i < n ∧ ((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x ∈ s}
  let timesFin : times.Finite := (Set.finite_lt_nat n).subset fun _ hi ↦ hi.1
  have htimes :
      timesFin.toFinset =
        (Finset.range n).filter
          (fun i ↦ ((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x ∈ s) := by
    ext i
    simp [times]
  have hsum :
      ∑ i ∈ Finset.range n,
          Set.indicator s (fun _ ↦ (1 : ℝ))
            (((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x) =
        (times.ncard : ℝ) := by
    calc
      ∑ i ∈ Finset.range n,
          Set.indicator s (fun _ ↦ (1 : ℝ))
            (((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x) =
          (((Finset.range n).filter
              (fun i ↦
                ((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x ∈ s)).card : ℝ) := by
            simpa only [Set.indicator_apply] using
              (Finset.sum_boole
                (fun i ↦ ((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x ∈ s)
                (Finset.range n) :
                (∑ i ∈ Finset.range n,
                    if ((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x ∈ s then
                      (1 : ℝ)
                    else 0) =
                  (((Finset.range n).filter
                      (fun i ↦
                        ((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x ∈ s)).card :
                    ℝ))
      _ = (times.ncard : ℝ) := by
            rw [Set.ncard_eq_toFinset_card times timesFin, htimes]
  rw [birkhoffAverage, birkhoffSum, smul_eq_mul]
  calc
    (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n,
          Set.indicator s (fun _ ↦ (1 : ℝ))
            (((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x) =
        (n : ℝ)⁻¹ * (times.ncard : ℝ) := by
          rw [hsum]
    _ = (times.ncard : ℝ) / n := by
          rw [div_eq_mul_inv, mul_comm]
    _ = (((Finset.range n).filter (fun i ↦
          ((fun y : UnitAddCircle ↦ y + (α : UnitAddCircle))^[i]) x ∈ s)).card : ℝ) / n := by
          congr 1
          rw [Set.ncard_eq_toFinset_card times timesFin, htimes]

/-- Helper for Exercise 20.3.2: changing from the standard `Int.fract` chart to an `equivIoc`
chart away from the seam does not change membership in the interval. -/
lemma fract_mem_Ico_iff_equivIoc_mem_Ico {a b c y : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hc_lt_a : c < a) (hb_le : b ≤ c + 1) :
    Int.fract y ∈ Set.Ico a b ↔
      ((AddCircle.equivIoc (1 : ℝ) c) (y : UnitAddCircle)).1 ∈ Set.Ico a b := by
  have h0 : toIcoMod (show (0 : ℝ) < 1 by norm_num) 0 y = Int.fract y := by
    simpa using (toIcoMod_eq_fract_mul (hp := show (0 : ℝ) < 1 by norm_num) y)
  have hc :
      ((AddCircle.equivIoc (1 : ℝ) c) (y : UnitAddCircle)).1 =
        toIocMod (show (0 : ℝ) < 1 by norm_num) c y := by
    simp [AddCircle.equivIoc, QuotientAddGroup.equivIocMod_coe]
  constructor
  · intro hy
    rw [hc]
    have hy' : toIcoMod (show (0 : ℝ) < 1 by norm_num) 0 y ∈ Set.Ioc c (c + 1) := by
      rw [h0]
      exact ⟨lt_of_lt_of_le hc_lt_a hy.1, lt_of_lt_of_le hy.2 hb_le |>.le⟩
    have hEq :
        toIocMod (show (0 : ℝ) < 1 by norm_num) c y =
          toIcoMod (show (0 : ℝ) < 1 by norm_num) 0 y := by
      rw [← toIocMod_toIcoMod (hp := show (0 : ℝ) < 1 by norm_num) c 0 y]
      exact (toIocMod_eq_self (hp := show (0 : ℝ) < 1 by norm_num)).2 hy'
    simpa [h0, hEq] using hy
  · intro hy
    rw [hc] at hy
    have hy' : toIocMod (show (0 : ℝ) < 1 by norm_num) c y ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      exact ⟨ha.trans hy.1, lt_of_lt_of_le hy.2 (by simpa using hb)⟩
    have hEq :
        toIcoMod (show (0 : ℝ) < 1 by norm_num) 0 y =
          toIocMod (show (0 : ℝ) < 1 by norm_num) c y := by
      rw [← toIcoMod_toIocMod (hp := show (0 : ℝ) < 1 by norm_num) 0 c y]
      exact (toIcoMod_eq_self (hp := show (0 : ℝ) < 1 by norm_num)).2 hy'
    have hEq' : Int.fract y = toIocMod (show (0 : ℝ) < 1 by norm_num) c y := by
      simpa [h0] using hEq
    simpa [hEq'] using hy

/-- Helper for Exercise 20.3.2: evaluating a lifted thickened indicator in the `equivIoc`
chart is the same as evaluating the original thickened indicator on the chart coordinate. -/
lemma liftIocThickenedIndicator_apply_equivIoc {δ : ℝ} (hδ : 0 < δ) {E : Set ℝ} {c : ℝ}
    (z : UnitAddCircle) :
    AddCircle.liftIoc (1 : ℝ) c (fun x ↦ ((thickenedIndicator hδ E x : ℝ))) z =
      (thickenedIndicator hδ E (((AddCircle.equivIoc (1 : ℝ) c) z).1) : ℝ) := by
  -- Proof comment: move `z` to its preferred representative in `Set.Ioc c (c + 1)` and then
  -- apply the defining computation rule of `liftIoc`.
  rfl

/-- Helper for Exercise 20.3.2: if `δ` is at most the distance from `c` to the left endpoint,
then `c` does not belong to the `δ`-thickening of `Set.Icc a b`. -/
lemma leftEndpoint_notMem_thickening_Icc {a b c δ : ℝ}
    (hc_lt_a : c < a) (hδ_le : δ ≤ a - c) :
    c ∉ thickening δ (Set.Icc a b) := by
  -- Proof comment: every point of `Set.Icc a b` lies at distance at least `a - c` from `c`.
  rw [mem_thickening_iff]
  intro hmem
  rcases hmem with ⟨z, hz, hdist⟩
  have hz_gt : c < z := lt_of_lt_of_le hc_lt_a hz.1
  have hdist' : |c - z| < δ := by
    simpa [Real.dist_eq] using hdist
  have habs : |c - z| = z - c := by
    rw [abs_of_neg (sub_neg.mpr hz_gt)]
    ring
  have hgap : δ ≤ z - c := by
    linarith [hz.1, hδ_le]
  have hlt : z - c < δ := by
    linarith [habs, hdist']
  exact (not_lt_of_ge hgap) hlt

/-- Helper for Exercise 20.3.2: if `δ` is at most the distance from the right endpoint to `c + 1`,
then `c + 1` does not belong to the `δ`-thickening of `Set.Icc a b`. -/
lemma rightEndpoint_notMem_thickening_Icc {a b c δ : ℝ}
    (hb_lt : b < c + 1) (hδ_le : δ ≤ c + 1 - b) :
    c + 1 ∉ thickening δ (Set.Icc a b) := by
  -- Proof comment: every point of `Set.Icc a b` lies at distance at least `c + 1 - b` from `c + 1`.
  rw [mem_thickening_iff]
  intro hmem
  rcases hmem with ⟨z, hz, hdist⟩
  have hz_lt : z < c + 1 := lt_of_le_of_lt hz.2 hb_lt
  have hdist' : |z - (c + 1)| < δ := by
    simpa [Real.dist_eq, abs_sub_comm] using hdist
  have habs : |z - (c + 1)| = c + 1 - z := by
    rw [abs_of_neg (sub_neg.mpr hz_lt)]
    ring
  have hgap : δ ≤ c + 1 - z := by
    linarith [hz.2, hδ_le]
  have hlt : c + 1 - z < δ := by
    linarith [habs, hdist']
  exact (not_lt_of_ge hgap) hlt

/-- Helper for Exercise 20.3.2: a lifted thickened indicator is continuous once the chart seam
misses the corresponding thickening. -/
lemma liftIocThickenedIndicator_continuous_of_seamFree {δ c : ℝ} (hδ : 0 < δ) {E : Set ℝ}
    (hc_out : c ∉ thickening δ E) (hc1_out : c + 1 ∉ thickening δ E) :
    Continuous (AddCircle.liftIoc (1 : ℝ) c (fun x ↦ ((thickenedIndicator hδ E x : ℝ)))) := by
  -- Proof comment: `liftIoc_continuous` reduces continuity to matching boundary values and
  -- continuity on the chart interval; both seam values are zero off the thickening.
  refine AddCircle.liftIoc_continuous ?_ ?_
  · simp [thickenedIndicator_zero hδ E hc_out, thickenedIndicator_zero hδ E hc1_out]
  · exact (NNReal.continuous_coe.comp (thickenedIndicator hδ E).continuous).continuousOn

/-- Helper for Exercise 20.3.2: if a point lies outside `Set.Ico a b`, then it also lies outside
the `δ`-thickening of the shrunken interval `Set.Icc (a + δ) (b - δ)`. -/
lemma notMem_thickening_innerIcc_of_not_mem_Ico {a b δ x : ℝ}
    (hδ : 0 < δ) (hx : x ∉ Set.Ico a b) :
    x ∉ thickening δ (Set.Icc (a + δ) (b - δ)) := by
  -- Proof comment: a witness in the shrunken interval would force `x` to be at least `δ` away
  -- from that witness on whichever side of `Set.Ico a b` it lies.
  rw [mem_thickening_iff]
  intro hmem
  rcases hmem with ⟨z, hz, hdist⟩
  rcases lt_or_ge x a with hxa | hax
  · have hdist' : |x - z| < δ := by
      simpa [Real.dist_eq] using hdist
    have hgap : δ ≤ z - x := by
      linarith [hz.1]
    have hlt : z - x < δ := by
      have habs : |x - z| = z - x := by
        rw [abs_of_neg]
        · ring
        · have : x < z := by linarith [hz.1, hδ]
          linarith
      linarith [habs, hdist']
    exact (not_lt_of_ge hgap) hlt
  · have hbx : b ≤ x := by
      by_contra hbx
      exact hx ⟨hax, lt_of_not_ge hbx⟩
    have hdist' : |z - x| < δ := by
      simpa [Real.dist_eq, abs_sub_comm] using hdist
    have hgap : δ ≤ x - z := by
      linarith [hz.2, hbx]
    have hlt : x - z < δ := by
      have habs : |z - x| = x - z := by
        rw [abs_of_neg]
        · ring
        · have : z < x := by linarith [hz.2, hδ, hbx]
          linarith
      linarith [habs, hdist']
    exact (not_lt_of_ge hgap) hlt

/-- Helper for Exercise 20.3.2: the interval indicator is pointwise bounded above by the lifted
outer thickened indicator on any seam-free chart. -/
lemma chartIcoIndicator_apply {a b c : ℝ} (z : UnitAddCircle) :
    Set.indicator {u : UnitAddCircle | ((AddCircle.equivIoc (1 : ℝ) c) u).1 ∈ Set.Ico a b}
        (fun _ ↦ (1 : ℝ)) z =
      if ((AddCircle.equivIoc (1 : ℝ) c) z).1 ∈ Set.Ico a b then 1 else 0 := by
  -- Proof comment: the charted indicator is just an `if` on membership of the chart coordinate.
  let s : Set UnitAddCircle := {u : UnitAddCircle | ((AddCircle.equivIoc (1 : ℝ) c) u).1 ∈ Set.Ico a b}
  change Set.indicator s (fun _ ↦ (1 : ℝ)) z = if z ∈ s then 1 else 0
  by_cases hz : z ∈ s <;> simp [Set.indicator, hz]

/-- Helper for Exercise 20.3.2: the interval indicator is pointwise bounded above by the lifted
outer thickened indicator on any seam-free chart. -/
lemma indicator_le_liftIocThickenedIndicator_Icc {a b c δ : ℝ} (hδ : 0 < δ)
    (z : UnitAddCircle) :
    Set.indicator {u : UnitAddCircle | ((AddCircle.equivIoc (1 : ℝ) c) u).1 ∈ Set.Ico a b}
        (fun _ ↦ (1 : ℝ)) z
      ≤ AddCircle.liftIoc (1 : ℝ) c
          (fun x ↦ ((thickenedIndicator hδ (Set.Icc a b) x : ℝ))) z := by
  -- Proof comment: on the interval itself the outer envelope equals `1`, and off the interval the
  -- indicator already vanishes.
  by_cases hz : ((AddCircle.equivIoc (1 : ℝ) c) z).1 ∈ Set.Ico a b
  · have hone :
        AddCircle.liftIoc (1 : ℝ) c
            (fun x ↦ ((thickenedIndicator hδ (Set.Icc a b) x : ℝ))) z = 1 := by
        rw [liftIocThickenedIndicator_apply_equivIoc (c := c) hδ z]
        exact_mod_cast thickenedIndicator_one hδ (Set.Icc a b) ⟨hz.1, hz.2.le⟩
    rw [chartIcoIndicator_apply, if_pos hz]
    simpa [hone] using hone.ge
  · have hnonneg :
        0 ≤ AddCircle.liftIoc (1 : ℝ) c
          (fun x ↦ ((thickenedIndicator hδ (Set.Icc a b) x : ℝ))) z := by
      rw [liftIocThickenedIndicator_apply_equivIoc (c := c) hδ z]
      positivity
    rw [chartIcoIndicator_apply, if_neg hz]
    simpa using hnonneg

/-- Helper for Exercise 20.3.2: the lifted inner thickened indicator is pointwise bounded above by
the exact interval indicator on the chart. -/
lemma liftIocThickenedIndicator_innerIcc_le_indicator {a b c δ : ℝ} (hδ : 0 < δ)
    (z : UnitAddCircle) :
    AddCircle.liftIoc (1 : ℝ) c
        (fun x ↦ ((thickenedIndicator hδ (Set.Icc (a + δ) (b - δ)) x : ℝ))) z
      ≤ Set.indicator {u : UnitAddCircle | ((AddCircle.equivIoc (1 : ℝ) c) u).1 ∈ Set.Ico a b}
          (fun _ ↦ (1 : ℝ)) z := by
  -- Proof comment: outside the interval the inner envelope vanishes because its support stays
  -- at least `δ` away from the boundary, while inside the interval it is bounded by `1`.
  by_cases hz : ((AddCircle.equivIoc (1 : ℝ) c) z).1 ∈ Set.Ico a b
  · have hle :
        AddCircle.liftIoc (1 : ℝ) c
            (fun x ↦ ((thickenedIndicator hδ (Set.Icc (a + δ) (b - δ)) x : ℝ))) z ≤ 1 := by
        rw [liftIocThickenedIndicator_apply_equivIoc (c := c) hδ z]
        exact_mod_cast thickenedIndicator_le_one hδ (Set.Icc (a + δ) (b - δ)) _
    rw [chartIcoIndicator_apply, if_pos hz]
    simpa using hle
  · have hzero :
        AddCircle.liftIoc (1 : ℝ) c
            (fun x ↦ ((thickenedIndicator hδ (Set.Icc (a + δ) (b - δ)) x : ℝ))) z = 0 := by
        rw [liftIocThickenedIndicator_apply_equivIoc (c := c) hδ z]
        exact_mod_cast
          thickenedIndicator_zero hδ (Set.Icc (a + δ) (b - δ))
            (notMem_thickening_innerIcc_of_not_mem_Ico (a := a) (b := b) hδ hz)
    rw [chartIcoIndicator_apply, if_neg hz]
    simpa [hzero] using hzero.le

/-- Helper for Exercise 20.3.2: shrinking radii tending to `0` gives interval integrals of
thickened indicators converging to the interval length on a seam-free chart. -/
lemma intervalIntegral_thickenedIndicator_Icc_tendsto_length_of_tendsto_zero
    {a b c : ℝ} {δ : ℕ → ℝ} (hδ_pos : ∀ k, 0 < δ k)
    (hδ_tendsto : Tendsto δ atTop (𝓝 0)) (hc_lt_a : c < a) (hab : a < b) (hb_lt : b < c + 1) :
    Tendsto
      (fun k : ℕ ↦
        ∫ x in c..c + 1, ((thickenedIndicator (hδ_pos k) (Set.Icc a b) x : ℝ)))
      atTop
      (𝓝 (b - a)) := by
  -- Proof comment: the closed interval already sits inside `Set.Ioc c (c + 1)`, so the general
  -- thickened-indicator convergence theorem reduces immediately to the interval length.
  let F : Set ℝ := Set.Icc a b
  have hF_closed : IsClosed F := isClosed_Icc
  have hT :=
    tendsto_integral_thickenedIndicator_of_isClosed
      (μ := volume.restrict (Set.Ioc c (c + 1))) hF_closed hδ_pos hδ_tendsto
  have hMeas : MeasurableSet F := hF_closed.measurableSet
  have hsub : F ⊆ Set.Ioc c (c + 1) := by
    intro x hx
    exact ⟨lt_of_lt_of_le hc_lt_a hx.1, (lt_of_le_of_lt hx.2 hb_lt).le⟩
  have hMeasure :
      (volume.restrict (Set.Ioc c (c + 1))).real F = b - a := by
    rw [Measure.real_def, Measure.restrict_apply hMeas, Set.inter_eq_left.mpr hsub,
      Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have hcc : c ≤ c + 1 := by linarith
  simpa [F, intervalIntegral.integral_of_le hcc, hMeasure] using hT

/-- Helper for Exercise 20.3.2: the expectation of the lifted inner thickened indicator is at
least the length of the interval minus the two boundary strips of width `δ`. -/
lemma lowerLiftIocThickenedIndicator_Icc_integral_ge {a b c δ : ℝ} (hδ : 0 < δ)
    (hc_lt_a : c < a) (hb_lt : b < c + 1) (hinner : a + δ ≤ b - δ) :
    b - a - 2 * δ ≤
      ∫ x : UnitAddCircle,
        AddCircle.liftIoc (1 : ℝ) c
          (fun x ↦ ((thickenedIndicator hδ (Set.Icc (a + δ) (b - δ)) x : ℝ))) x
          ∂(volume : Measure UnitAddCircle) := by
  -- Proof comment: the inner interval lies inside the chart interval, and the thickened indicator
  -- dominates the exact indicator of that inner interval.
  let Finner : Set ℝ := Set.Icc (a + δ) (b - δ)
  have hFinner_closed : IsClosed Finner := isClosed_Icc
  have hFinner_sub : Finner ⊆ Set.Ioc c (c + 1) := by
    intro x hx
    constructor
    · have hcx : c < x := by
        have hax : a < x := by linarith [hx.1, hδ]
        exact lt_trans hc_lt_a hax
      exact hcx
    · have hxb : x < b := by linarith [hx.2, hδ]
      exact (lt_trans hxb hb_lt).le
  have hRestrict :
      b - a - 2 * δ ≤
        ∫ x, ((thickenedIndicator hδ Finner x : ℝ)) ∂(volume.restrict (Set.Ioc c (c + 1))) := by
    calc
      b - a - 2 * δ = volume.real Finner := by
        rw [show Finner = Set.Icc (a + δ) (b - δ) by rfl, Real.volume_real_Icc_of_le hinner]
        ring
      _ = (volume.restrict (Set.Ioc c (c + 1))).real Finner := by
        simp [Finner, Measure.real_def, Measure.restrict_apply hFinner_closed.measurableSet,
          Set.inter_eq_left.mpr hFinner_sub]
      _ = ∫ x, (Finner.indicator (fun _ ↦ (1 : ℝ))) x ∂(volume.restrict (Set.Ioc c (c + 1))) := by
        symm
        exact integral_indicator_one hFinner_closed.measurableSet
      _ ≤ ∫ x, ((thickenedIndicator hδ Finner x : ℝ)) ∂(volume.restrict (Set.Ioc c (c + 1))) := by
        refine integral_mono ?_ (integrable_thickenedIndicator _ _) ?_
        · exact
            (integrable_indicator_iff hFinner_closed.measurableSet).mpr
              (integrable_const _).integrableOn
        · intro x
          by_cases hx : x ∈ Finner
          · have hone : thickenedIndicator hδ Finner x = 1 :=
              thickenedIndicator_one hδ Finner hx
            norm_num [hx, hone]
          · have hzero : Finner.indicator (fun _ ↦ (1 : ℝ)) x = 0 := by
              simp [hx]
            have hnonneg : 0 ≤ (thickenedIndicator hδ Finner x : ℝ) := by
              positivity
            simpa [hzero] using hnonneg
  have hcc : c ≤ c + 1 := by linarith
  have hLift :
      ∫ x : UnitAddCircle,
          AddCircle.liftIoc (1 : ℝ) c
            (fun x ↦ ((thickenedIndicator hδ Finner x : ℝ))) x ∂(volume : Measure UnitAddCircle) =
        ∫ x in c..c + 1, ((thickenedIndicator hδ Finner x : ℝ)) := by
    simpa [Finner] using
      (AddCircle.integral_liftIoc_eq_intervalIntegral
        (T := (1 : ℝ)) (t := c)
        (f := fun x ↦ ((thickenedIndicator hδ Finner x : ℝ))))
  calc
    b - a - 2 * δ ≤
        ∫ x, ((thickenedIndicator hδ Finner x : ℝ)) ∂(volume.restrict (Set.Ioc c (c + 1))) :=
      hRestrict
    _ = ∫ x in c..c + 1, ((thickenedIndicator hδ Finner x : ℝ)) := by
      simp [intervalIntegral.integral_of_le hcc]
    _ = ∫ x : UnitAddCircle,
          AddCircle.liftIoc (1 : ℝ) c
            (fun x ↦ ((thickenedIndicator hδ Finner x : ℝ))) x ∂(volume : Measure UnitAddCircle) := by
      simpa [Finner] using hLift.symm

/-- Helper for Exercise 20.3.2: the positive-time irrational orbit visits an interval in a seam-free
chart with asymptotic frequency equal to its length. -/
lemma irrationalRotation_chart_Ico_frequency_tendsto {α a b c : ℝ}
    (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b) (hc_lt_a : c < a) (hb_lt : b < c + 1) :
    Tendsto
      (fun n : ℕ ↦
        (((Finset.range n).filter (fun i : ℕ ↦
            ((AddCircle.equivIoc (1 : ℝ) c) ((((i + 1 : ℕ) : ℝ) * α : ℝ) : UnitAddCircle)).1 ∈
              Set.Ico a b)).card : ℝ) / n)
      atTop
      (𝓝 (b - a)) := by
  let τ : UnitAddCircle → UnitAddCircle := fun y ↦ y + (α : UnitAddCircle)
  let x₀ : UnitAddCircle := (α : UnitAddCircle)
  let margin : ℝ := min (a - c) (c + 1 - b)
  have hmargin_pos : 0 < margin := by
    refine lt_min ?_ ?_
    · linarith
    · linarith
  let δ : ℕ → ℝ := fun k ↦ margin / (k + 2)
  have hδ_pos : ∀ k, 0 < δ k := by
    intro k
    dsimp [δ]
    positivity
  have hδ_lt_margin : ∀ k, δ k < margin := by
    intro k
    dsimp [δ]
    have hk : 0 < (k : ℝ) + 2 := by positivity
    rw [div_lt_iff₀ hk]
    nlinarith
  have hδ_tendsto : Tendsto δ atTop (𝓝 0) := by
    convert ((tendsto_const_div_atTop_nhds_zero_nat margin).comp (tendsto_add_atTop_nat 2)) using 1
    ext n
    simp [δ]
  have hUpperInt :
      Tendsto
        (fun k : ℕ ↦
          ∫ x in c..c + 1, ((thickenedIndicator (hδ_pos k) (Set.Icc a b) x : ℝ)))
        atTop
        (𝓝 (b - a)) := by
    exact intervalIntegral_thickenedIndicator_Icc_tendsto_length_of_tendsto_zero
      hδ_pos hδ_tendsto hc_lt_a hab hb_lt
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hUpperEvent :
      ∀ᶠ k : ℕ in atTop,
        ∫ x in c..c + 1, ((thickenedIndicator (hδ_pos k) (Set.Icc a b) x : ℝ)) < b - a + ε / 2 :=
    hUpperInt.eventually (Iio_mem_nhds (by linarith : b - a < b - a + ε / 2))
  rcases Filter.mem_atTop_sets.1 hUpperEvent with ⟨K, hK⟩
  let k := max K (Nat.ceil (max (4 * margin / ε) (4 * margin / (b - a))))
  have hkUpper : ∫ x in c..c + 1, ((thickenedIndicator (hδ_pos k) (Set.Icc a b) x : ℝ)) <
      b - a + ε / 2 :=
    hK k (le_max_left _ _)
  have hkInner : 2 * δ k < ε / 2 := by
    have hkceil_nat : Nat.ceil (max (4 * margin / ε) (4 * margin / (b - a))) ≤ k :=
      le_max_right _ _
    have hkceil : 4 * margin / ε ≤ (k : ℝ) := by
      exact le_trans (le_max_left _ _) <|
        le_trans (Nat.le_ceil _) (by exact_mod_cast hkceil_nat)
    have hε0 : 0 < ε := hε
    have hden : 0 < (k : ℝ) + 2 := by positivity
    dsimp [δ]
    have hk' : 4 * margin / ε < (k : ℝ) + 2 := by
      have : (4 * margin / ε : ℝ) ≤ k := hkceil
      linarith
    have hk'' : δ k < ε / 4 := by
      have hmul :=
        mul_lt_mul_of_pos_left hk' (show 0 < ε / 4 by positivity)
      have hbound : margin < (ε / 4) * ((k : ℝ) + 2) := by
        have hleft : (ε / 4) * (4 * margin / ε) = margin := by
          field_simp [hε.ne']
        simpa [hleft] using hmul
      exact (div_lt_iff₀ hden).2 hbound
    linarith
  let Finner : Set ℝ := Set.Icc (a + δ k) (b - δ k)
  have hFinner_closed : IsClosed Finner := isClosed_Icc
  have hFinner_nonempty : a + δ k ≤ b - δ k := by
    have hkceil_nat : Nat.ceil (max (4 * margin / ε) (4 * margin / (b - a))) ≤ k :=
      le_max_right _ _
    have hkceil : 4 * margin / (b - a) ≤ (k : ℝ) := by
      exact le_trans (le_max_right _ _) <|
        le_trans (Nat.le_ceil _) (by exact_mod_cast hkceil_nat)
    have hba_pos : 0 < b - a := sub_pos.mpr hab
    have hden : 0 < (k : ℝ) + 2 := by positivity
    dsimp [δ]
    have hk' : 4 * margin / (b - a) < (k : ℝ) + 2 := by
      have : 4 * margin / (b - a) ≤ (k : ℝ) := hkceil
      linarith
    have hk'' : margin / ((k : ℝ) + 2) < (b - a) / 4 := by
      have hmul :=
        mul_lt_mul_of_pos_left hk' (show 0 < (b - a) / 4 by positivity)
      have hbound : margin < ((b - a) / 4) * ((k : ℝ) + 2) := by
        have hleft : ((b - a) / 4) * (4 * margin / (b - a)) = margin := by
          have hba_ne : (b - a) ≠ 0 := sub_ne_zero.mpr hab.ne'
          field_simp [hba_ne]
        simpa [hleft] using hmul
      exact (div_lt_iff₀ hden).2 hbound
    have : 2 * δ k < b - a := by
      linarith
    linarith
  let upper : UnitAddCircle → ℝ := AddCircle.liftIoc (1 : ℝ) c
    (fun x ↦ ((thickenedIndicator (hδ_pos k) (Set.Icc a b) x : ℝ)))
  let lower : UnitAddCircle → ℝ :=
    AddCircle.liftIoc (1 : ℝ) c (fun x ↦ ((thickenedIndicator (hδ_pos k) Finner x : ℝ)))
  have hUpperMean :
      (volume : Measure UnitAddCircle)[upper] =
        ∫ x in c..c + 1, ((thickenedIndicator (hδ_pos k) (Set.Icc a b) x : ℝ)) := by
    simpa [upper] using
      (AddCircle.integral_liftIoc_eq_intervalIntegral
        (T := (1 : ℝ)) (t := c)
        (f := fun x ↦ ((thickenedIndicator (hδ_pos k) (Set.Icc a b) x : ℝ))))
  have hUpperCont : Continuous upper := by
    -- Proof comment: continuity comes from the general seam-free lifting lemma.
    refine liftIocThickenedIndicator_continuous_of_seamFree (c := c) (hδ := hδ_pos k) ?_ ?_
    · exact leftEndpoint_notMem_thickening_Icc hc_lt_a
        (le_trans (hδ_lt_margin k).le (min_le_left _ _))
    · exact rightEndpoint_notMem_thickening_Icc hb_lt
        (le_trans (hδ_lt_margin k).le (min_le_right _ _))
  have hLowerCont : Continuous lower := by
    -- Route correction: keep the same Birkhoff squeeze, but pay the seam proof cost once in a
    -- dedicated helper instead of inside the main chart theorem.
    refine liftIocThickenedIndicator_continuous_of_seamFree (c := c) (hδ := hδ_pos k) ?_ ?_
    · exact leftEndpoint_notMem_thickening_Icc (a := a + δ k) (b := b - δ k) (c := c)
        (by linarith [hc_lt_a, hδ_pos k]) (by linarith [hc_lt_a])
    · exact rightEndpoint_notMem_thickening_Icc (a := a + δ k) (b := b - δ k) (c := c)
        (by linarith [hb_lt, hδ_pos k]) (by linarith [hb_lt])
  have hUpperLimit :=
    irrationalRotation_birkhoffAverage_tendsto_of_continuous hα hUpperCont x₀
  have hLowerLimit :=
    irrationalRotation_birkhoffAverage_tendsto_of_continuous hα hLowerCont x₀
  have hLowerIntegral :
      b - a - ε / 2 <
        ∫ x : UnitAddCircle, lower x ∂(volume : Measure UnitAddCircle) := by
    have hInnerMeasure :
        b - a - 2 * δ k ≤ ∫ x : UnitAddCircle, lower x ∂(volume : Measure UnitAddCircle) := by
      simpa [lower, Finner] using
        lowerLiftIocThickenedIndicator_Icc_integral_ge (a := a) (b := b) (c := c)
          (δ := δ k) (hδ := hδ_pos k) hc_lt_a hb_lt hFinner_nonempty
    linarith
  have hEventuallyUpper :
      ∀ᶠ n : ℕ in atTop,
        birkhoffAverage ℝ τ upper n x₀ < b - a + ε := by
    have hkUpperMean : (volume : Measure UnitAddCircle)[upper] < b - a + ε / 2 := by
      simpa [hUpperMean] using hkUpper
    exact hUpperLimit.eventually (Iio_mem_nhds (by linarith [hkUpperMean]))
  have hEventuallyLower :
      ∀ᶠ n : ℕ in atTop,
        b - a - ε < birkhoffAverage ℝ τ lower n x₀ := by
    exact hLowerLimit.eventually (Ioi_mem_nhds (by linarith [hLowerIntegral]))
  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        dist
            ((((Finset.range n).filter (fun i : ℕ ↦
                ((AddCircle.equivIoc (1 : ℝ) c) ((((i + 1 : ℕ) : ℝ) * α : ℝ) :
                    UnitAddCircle)).1 ∈ Set.Ico a b)).card : ℝ) / n)
            (b - a) < ε := by
    filter_upwards [hEventuallyUpper, hEventuallyLower] with n hnUpper hnLower
    let s : Set UnitAddCircle :=
      {z | ((AddCircle.equivIoc (1 : ℝ) c) z).1 ∈ Set.Ico a b}
    have hCard :
        (((Finset.range n).filter (fun i : ℕ ↦
            ((AddCircle.equivIoc (1 : ℝ) c) ((((i + 1 : ℕ) : ℝ) * α : ℝ) : UnitAddCircle)).1 ∈
              Set.Ico a b)).card : ℝ) / n =
          birkhoffAverage ℝ τ (Set.indicator s (fun _ ↦ (1 : ℝ))) n x₀ := by
      have hFilter :
          (Finset.range n).filter (fun i : ℕ ↦
              ((AddCircle.equivIoc (1 : ℝ) c) ((((i + 1 : ℕ) : ℝ) * α : ℝ) : UnitAddCircle)).1 ∈
                Set.Ico a b) =
            (Finset.range n).filter (fun i ↦ x₀ + i • (α : UnitAddCircle) ∈ s) := by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_filter.mp hi with ⟨hiRange, hiMem⟩
          refine Finset.mem_filter.mpr ⟨hiRange, ?_⟩
          have horbit :
              ((((i + 1 : ℕ) : ℝ) * α : ℝ) : UnitAddCircle) = x₀ + i • (α : UnitAddCircle) := by
            calc
              ((((i + 1 : ℕ) : ℝ) * α : ℝ) : UnitAddCircle)
                  = ((((i + 1) • α : ℝ)) : UnitAddCircle) := by simp [nsmul_eq_mul]
              _ = (i + 1) • (α : UnitAddCircle) := by
                  simpa using (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := i + 1) (x := α))
              _ = x₀ + i • (α : UnitAddCircle) := by
                  simp [x₀, add_assoc, add_left_comm, add_comm, add_nsmul]
          rw [horbit] at hiMem
          simpa [s] using hiMem
        · intro hi
          rcases Finset.mem_filter.mp hi with ⟨hiRange, hiMem⟩
          refine Finset.mem_filter.mpr ⟨hiRange, ?_⟩
          have horbit :
              ((((i + 1 : ℕ) : ℝ) * α : ℝ) : UnitAddCircle) = x₀ + i • (α : UnitAddCircle) := by
            calc
              ((((i + 1 : ℕ) : ℝ) * α : ℝ) : UnitAddCircle)
                  = ((((i + 1) • α : ℝ)) : UnitAddCircle) := by simp [nsmul_eq_mul]
              _ = (i + 1) • (α : UnitAddCircle) := by
                  simpa using (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := i + 1) (x := α))
              _ = x₀ + i • (α : UnitAddCircle) := by
                  simp [x₀, add_assoc, add_left_comm, add_comm, add_nsmul]
          rw [← horbit] at hiMem
          simpa [s] using hiMem
      symm
      calc
        birkhoffAverage ℝ τ (Set.indicator s (fun _ ↦ (1 : ℝ))) n x₀ =
            (((Finset.range n).filter (fun i ↦ x₀ + i • (α : UnitAddCircle) ∈ s)).card : ℝ) / n := by
              calc
                birkhoffAverage ℝ τ (Set.indicator s (fun _ ↦ (1 : ℝ))) n x₀ =
                    (((Finset.range n).filter (fun i ↦ (τ^[i]) x₀ ∈ s)).card : ℝ) / n := by
                      simpa [τ] using
                        (birkhoffAverage_indicator_eq_cardRatio (α := α) (s := s) n x₀)
                _ = (((Finset.range n).filter (fun i ↦ x₀ + i • (α : UnitAddCircle) ∈ s)).card : ℝ) / n := by
                      exact congrArg (fun t : Finset ℕ => (t.card : ℝ) / n) <| by
                        ext i
                        simp [τ, addRightIterate_apply]
        _ = (((Finset.range n).filter (fun i : ℕ ↦
              ((AddCircle.equivIoc (1 : ℝ) c) ((((i + 1 : ℕ) : ℝ) * α : ℝ) : UnitAddCircle)).1 ∈
                Set.Ico a b)).card : ℝ) / n := by
              exact congrArg (fun t : Finset ℕ => (t.card : ℝ) / n) hFilter.symm
    have hLowerLe :
        birkhoffAverage ℝ τ lower n x₀ ≤
          birkhoffAverage ℝ τ (Set.indicator s (fun _ ↦ (1 : ℝ))) n x₀ := by
      rw [birkhoffAverage, birkhoffAverage, birkhoffSum, birkhoffSum, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Finset.sum_le_sum ?_
      intro i hi
      simpa [lower, s] using
        liftIocThickenedIndicator_innerIcc_le_indicator (a := a) (b := b) (c := c)
          (δ := δ k) (hδ := hδ_pos k) ((τ^[i]) x₀)
    have hUpperLe :
        birkhoffAverage ℝ τ (Set.indicator s (fun _ ↦ (1 : ℝ))) n x₀ ≤
          birkhoffAverage ℝ τ upper n x₀ := by
      rw [birkhoffAverage, birkhoffAverage, birkhoffSum, birkhoffSum, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Finset.sum_le_sum ?_
      intro i hi
      simpa [upper, s] using
        indicator_le_liftIocThickenedIndicator_Icc (a := a) (b := b) (c := c)
          (δ := δ k) (hδ := hδ_pos k) ((τ^[i]) x₀)
    have hMain :
        |(((Finset.range n).filter (fun i : ℕ ↦
            ((AddCircle.equivIoc (1 : ℝ) c) ((((i + 1 : ℕ) : ℝ) * α : ℝ) : UnitAddCircle)).1 ∈
              Set.Ico a b)).card : ℝ) / n - (b - a)| < ε := by
      rw [hCard]
      have h1 : b - a - ε <
          birkhoffAverage ℝ τ (Set.indicator s (fun _ ↦ (1 : ℝ))) n x₀ :=
        lt_of_lt_of_le hnLower hLowerLe
      have h2 :
          birkhoffAverage ℝ τ (Set.indicator s (fun _ ↦ (1 : ℝ))) n x₀ < b - a + ε :=
        lt_of_le_of_lt hUpperLe hnUpper
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    simpa [Real.dist_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hMain
  exact Filter.mem_atTop_sets.1 hEventually

/-- Helper for Exercise 20.3.2: an irrational rotation visits an interval in `[0, 1)` with
asymptotic frequency equal to its length. -/
lemma irrationalRotation_Ico_frequency_tendsto {α a b : ℝ}
    (hα : Irrational α) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hnot_full : a ≠ 0 ∨ b ≠ 1) :
    Tendsto
      (fun n : ℕ ↦
        (((Finset.Icc 1 n).filter (fun i : ℕ ↦
            Int.fract ((i : ℝ) * α) ∈ Set.Ico a b)).card : ℝ) / n)
      atTop
      (𝓝 (b - a)) := by
  let c : ℝ := (a + b - 1) / 2
  have hc_lt_a : c < a := by
    by_contra hca
    have ha_le : a ≤ c := le_of_not_gt hca
    have hineq : a + 1 ≤ b := by
      dsimp [c] at ha_le
      linarith
    have ha_eq : a = 0 := by
      linarith [ha, hb, hineq]
    have hb_eq : b = 1 := by
      linarith [hb, hineq, ha_eq]
    exact hnot_full.elim (fun h0 ↦ h0 ha_eq) (fun h1 ↦ h1 hb_eq)
  have hb_lt : b < c + 1 := by
    by_contra hbc
    have hc_le : c + 1 ≤ b := le_of_not_gt hbc
    have hineq : a + 1 ≤ b := by
      dsimp [c] at hc_le
      linarith
    have ha_eq : a = 0 := by
      linarith [ha, hb, hineq]
    have hb_eq : b = 1 := by
      linarith [hb, hineq, ha_eq]
    exact hnot_full.elim (fun h0 ↦ h0 ha_eq) (fun h1 ↦ h1 hb_eq)
  have hChart :=
    irrationalRotation_chart_Ico_frequency_tendsto (α := α) (a := a) (b := b) (c := c)
      hα ha hab hc_lt_a hb_lt
  have hEventually :
      (fun n : ℕ ↦
        (((Finset.Icc 1 n).filter (fun i : ℕ ↦
            Int.fract ((i : ℝ) * α) ∈ Set.Ico a b)).card : ℝ) / n)
      =ᶠ[atTop]
        fun n : ℕ ↦
          (((Finset.range n).filter (fun i : ℕ ↦
              ((AddCircle.equivIoc (1 : ℝ) c) ((((i + 1 : ℕ) : ℝ) * α : ℝ) : UnitAddCircle)).1 ∈
                Set.Ico a b)).card : ℝ) / n := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hCard :
        ((Finset.Icc 1 n).filter (fun i : ℕ ↦ Int.fract ((i : ℝ) * α) ∈ Set.Ico a b)).card =
          ((Finset.range n).filter (fun i : ℕ ↦
            Int.fract (((i + 1 : ℕ) : ℝ) * α) ∈ Set.Ico a b)).card := by
      have hImage :
          (Finset.Icc 1 n).filter (fun i : ℕ ↦ Int.fract ((i : ℝ) * α) ∈ Set.Ico a b) =
            ((Finset.range n).filter (fun i : ℕ ↦
                Int.fract (((i + 1 : ℕ) : ℝ) * α) ∈ Set.Ico a b)).image Nat.succ := by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_filter.mp hi with ⟨hiIcc, hiMem⟩
          have hiIcc' := Finset.mem_Icc.mp hiIcc
          have hi_pos : 0 < i := by
            exact lt_of_lt_of_le Nat.zero_lt_one hiIcc'.1
          refine Finset.mem_image.mpr ?_
          refine ⟨i - 1, ?_, by omega⟩
          refine Finset.mem_filter.mpr ?_
          constructor
          · have hsub_lt_i : i - 1 < i := by omega
            have hsub_lt_n : i - 1 < n := lt_of_lt_of_le hsub_lt_i hiIcc'.2
            simpa [Finset.mem_range] using hsub_lt_n
          · have hi_sub : i - 1 + 1 = i := by omega
            simpa [hi_sub] using hiMem
        · intro hi
          rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
          rcases Finset.mem_filter.mp hj with ⟨hjRange, hjMem⟩
          refine Finset.mem_filter.mpr ?_
          constructor
          · have hjRange' : j < n := by simpa [Finset.mem_range] using hjRange
            simp [Finset.mem_Icc, hjRange', Nat.succ_le_iff]
          · simpa using hjMem
      rw [hImage]
      exact Finset.card_image_of_injective _ Nat.succ_injective
    have hFilter :
        (Finset.range n).filter (fun i : ℕ ↦ Int.fract (((i + 1 : ℕ) : ℝ) * α) ∈ Set.Ico a b) =
          (Finset.range n).filter (fun i : ℕ ↦
            ((AddCircle.equivIoc (1 : ℝ) c) ((((i + 1 : ℕ) : ℝ) * α : ℝ) : UnitAddCircle)).1 ∈
              Set.Ico a b) := by
      ext i
      constructor
      · intro hi
        rcases Finset.mem_filter.mp hi with ⟨hiRange, hiMem⟩
        refine Finset.mem_filter.mpr ⟨hiRange, ?_⟩
        exact (fract_mem_Ico_iff_equivIoc_mem_Ico
          (a := a) (b := b) (c := c) (y := (((i + 1 : ℕ) : ℝ) * α)) ha hb hc_lt_a hb_lt.le).1 hiMem
      · intro hi
        rcases Finset.mem_filter.mp hi with ⟨hiRange, hiMem⟩
        refine Finset.mem_filter.mpr ⟨hiRange, ?_⟩
        exact (fract_mem_Ico_iff_equivIoc_mem_Ico
          (a := a) (b := b) (c := c) (y := (((i + 1 : ℕ) : ℝ) * α)) ha hb hc_lt_a hb_lt.le).2 hiMem
    exact (congrArg (fun m : ℕ => (m : ℝ) / n) hCard).trans
      (congrArg (fun t : Finset ℕ => (t.card : ℝ) / n) hFilter)
  exact (tendsto_congr' hEventually).2 hChart

/-- Helper for Exercise 20.3.2: on every finite prefix, the leading-digit condition for `q ^ i`
is exactly the logarithmic interval condition for `i * logb p q`. -/
lemma leadingDigit_filter_eq_fractLogb_filter {p q d n : ℕ}
    (hp : 1 < p) (hq : q ≠ 0) (hd1 : 1 ≤ d) (hd_lt : d < p) :
    (Finset.Icc 1 n).filter (fun i : ℕ ↦ baseLeadingDigit p (q ^ i) = d) =
      (Finset.Icc 1 n).filter (fun i : ℕ ↦
        Int.fract ((i : ℝ) * Real.logb p q) ∈ Set.Ico (Real.logb p d) (Real.logb p (d + 1))) := by
  -- Proof comment: this is the finite-prefix version of the digit/logarithm bridge specialized
  -- to powers of `q`.
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc, and_congr_right_iff]
  intro _hi
  have hpow_ne : q ^ i ≠ 0 := pow_ne_zero _ hq
  have hlogb_pow : Real.logb (p : ℝ) ((q ^ i : ℕ) : ℝ) = (i : ℝ) * Real.logb p q := by
    rw [Nat.cast_pow, Real.logb_pow]
  rw [baseLeadingDigit_eq_iff_fractLogb_mem_Ico hp hpow_ne hd1 hd_lt, hlogb_pow]

-- Proof sketch: write the leading base-`p` digit of `q^i` as the indicator of the interval
-- `[log d / log p, log (d + 1) / log p)` for the fractional parts of `i * log q / log p`, then
-- apply equidistribution on the circle using the squarefreeness hypothesis on `p`.
/-- Exercise 20.3.2: for squarefree `p` and `2 ≤ q < p`, the leading base-`p` digits of `q^n`
satisfy Benford's law with logarithmic frequencies. -/
theorem powers_leading_digit_benford
    {p q d : ℕ} (hpSq : Squarefree p) (hq2 : 2 ≤ q) (hq_lt : q < p)
    (hd1 : 1 ≤ d) (hd_lt : d < p) :
    Tendsto
      (fun n : ℕ ↦
        (((Finset.Icc 1 n).filter (fun i : ℕ ↦
            baseLeadingDigit p (q ^ i) = d)).card : ℝ) / n)
      atTop
      (𝓝 ((Real.log (d + 1) - Real.log d) / Real.log p)) := by
  let α : ℝ := Real.logb p q
  have hp : 1 < p := lt_trans hq2 hq_lt
  have hp_real : (1 : ℝ) < p := by
    exact_mod_cast hp
  have hα : Irrational α := irrationalLogbNat_of_squarefree hpSq hq2 hq_lt
  have ha_nonneg : 0 ≤ Real.logb p d := by
    exact Real.logb_nonneg hp_real (by exact_mod_cast hd1)
  have hb_le_one : Real.logb p (d + 1) ≤ 1 := by
    have hdp : (d + 1 : ℕ) ≤ p := Nat.succ_le_of_lt hd_lt
    have hcast : ((d + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hdp
    have hle :=
      (Real.logb_le_logb (b := (p : ℝ)) hp_real
        (by exact_mod_cast Nat.succ_pos d) (by exact_mod_cast (lt_trans Nat.zero_lt_one hp))).2 hcast
    simpa [Real.logb_self_eq_one hp_real] using hle
  have hab : Real.logb p d < Real.logb p (d + 1) := by
    exact
      Real.logb_lt_logb (b := (p : ℝ)) hp_real
        (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1))
        (by exact_mod_cast Nat.lt_succ_self d)
  have hnot_full :
      Real.logb p d ≠ 0 ∨ Real.logb p (d + 1) ≠ 1 := by
    by_contra h
    push Not at h
    have hd_eq_one : d = 1 := by
      have hd0 : 0 < (d : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
      have hd_eq_one_real : (d : ℝ) = 1 :=
        Real.eq_one_of_pos_of_logb_eq_zero (b := (p : ℝ)) hp_real hd0 h.1
      exact_mod_cast hd_eq_one_real
    have hdp_eq : d + 1 = p := by
      have hlog_eq : Real.logb (p : ℝ) ((d + 1 : ℕ) : ℝ) = Real.logb (p : ℝ) (p : ℝ) := by
        simpa [Real.logb_self_eq_one hp_real] using h.2
      have hd1_pos : 0 < (d + 1 : ℝ) := by positivity
      have hp_pos : 0 < (p : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
      have hdp_eq_real : ((d + 1 : ℕ) : ℝ) = (p : ℝ) :=
        (Real.strictMonoOn_logb (b := (p : ℝ)) hp_real).injOn
          (by simpa using hd1_pos) (by simpa using hp_pos) hlog_eq
      exact_mod_cast hdp_eq_real
    have hp_eq_two : p = 2 := by omega
    exact (Nat.not_lt_of_ge hq2) (by simpa [hp_eq_two] using hq_lt)
  have horbit :
      Tendsto
        (fun n : ℕ ↦
          (((Finset.Icc 1 n).filter (fun i : ℕ ↦
              Int.fract ((i : ℝ) * α) ∈
                Set.Ico (Real.logb p d) (Real.logb p (d + 1)))).card : ℝ) / n)
        atTop
        (𝓝 (Real.logb p (d + 1) - Real.logb p d)) :=
    irrationalRotation_Ico_frequency_tendsto hα ha_nonneg hab hb_le_one hnot_full
  have hEventually :
      (fun n : ℕ ↦
        (((Finset.Icc 1 n).filter (fun i : ℕ ↦
            baseLeadingDigit p (q ^ i) = d)).card : ℝ) / n)
      =ᶠ[atTop]
        fun n : ℕ ↦
          (((Finset.Icc 1 n).filter (fun i : ℕ ↦
              Int.fract ((i : ℝ) * α) ∈
                Set.Ico (Real.logb p d) (Real.logb p (d + 1)))).card : ℝ) / n := by
    refine Filter.Eventually.of_forall ?_
    intro n
    simpa [α] using congrArg (fun t : Finset ℕ => (t.card : ℝ) / n)
      (leadingDigit_filter_eq_fractLogb_filter (n := n) hp (by omega) hd1 hd_lt)
  have hlimit :
      Real.logb p (d + 1) - Real.logb p d =
        (Real.log (d + 1) - Real.log d) / Real.log p := by
    rw [Real.logb, Real.logb, div_eq_mul_inv, div_eq_mul_inv]
    ring
  simpa [hlimit] using (tendsto_congr' hEventually).2 horbit

end
