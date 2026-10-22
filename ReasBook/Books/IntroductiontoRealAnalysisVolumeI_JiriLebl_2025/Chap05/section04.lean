/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap05
section Section04

open Set Filter

/-- Proposition 5.4.1. There exists a unique function `L : (0,∞) → ℝ` such that
`(i)` `L 1 = 0`; `(ii)` `L` is differentiable with derivative `1/x`; `(iii)`
`L` is strictly increasing, bijective, and `L x → -∞` as `x → 0⁺` while
`L x → ∞` as `x → ∞`; `(iv)` `L (x*y) = L x + L y` for `x,y > 0`; `(v)` for
rational `q` and `x > 0`, `L (x^q) = q * L x`. -/
def LogAxioms (L : ℝ → ℝ) : Prop :=
  L 1 = 0 ∧
    (∀ x > 0, HasDerivAt L (1 / x) x) ∧
    StrictMonoOn L (Set.Ioi 0) ∧
    Function.Surjective (fun x : Set.Ioi (0 : ℝ) => L x) ∧
    Tendsto L (nhdsWithin 0 (Set.Ioi 0)) atBot ∧
    Tendsto L atTop atTop ∧
    (∀ {x y}, 0 < x → 0 < y → L (x * y) = L x + L y) ∧
    (∀ {q : ℚ} {x}, 0 < x → L (Real.rpow x q) = (q : ℝ) * L x)

/-- `\log` from mathlib satisfies the axioms characterizing the logarithm. -/
lemma log_satisfies_LogAxioms : LogAxioms Real.log := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro x hx
    have hx' : x ≠ 0 := ne_of_gt hx
    simpa [one_div] using (Real.hasDerivAt_log hx')
  · simpa using Real.strictMonoOn_log
  · intro y
    refine ⟨⟨Real.exp y, Real.exp_pos y⟩, ?_⟩
    simp
  · simpa using Real.tendsto_log_nhdsGT_zero
  · simpa using Real.tendsto_log_atTop
  · intro x y hx hy
    simpa using (Real.log_mul (ne_of_gt hx) (ne_of_gt hy))
  · intro q x hx
    simpa using (Real.log_rpow (x := x) (y := (q : ℝ)) hx)

lemma logAxioms_eq_log_on_pos {L : ℝ → ℝ} (hL : LogAxioms L) {x : ℝ} (hx : 0 < x) :
    L x = Real.log x := by
  rcases hL with ⟨hL1, hderiv, -, -, -, -, -, -⟩
  have hypos_of_mem : ∀ y ∈ Set.uIcc (1 : ℝ) x, 0 < y := by
    intro y hy
    rcases le_total 1 x with hle | hge
    · have hy' : y ∈ Set.Icc (1 : ℝ) x := by
        simpa [Set.uIcc_of_le hle] using hy
      exact lt_of_lt_of_le zero_lt_one hy'.1
    · have hy' : y ∈ Set.Icc x 1 := by
        simpa [Set.uIcc_of_ge hge] using hy
      exact lt_of_lt_of_le hx hy'.1
  have hderiv' : ∀ y ∈ Set.uIcc (1 : ℝ) x, HasDerivAt L (1 / y) y := by
    intro y hy
    exact hderiv y (hypos_of_mem y hy)
  have hne : ∀ y : ℝ, y ∈ Set.uIcc (1 : ℝ) x → y ≠ 0 := by
    intro y hy
    exact ne_of_gt (hypos_of_mem y hy)
  have hint :
      IntervalIntegrable (fun y : ℝ => 1 / y) MeasureTheory.volume (1 : ℝ) x := by
    simpa using
      (intervalIntegral.intervalIntegrable_one_div (μ := MeasureTheory.volume) (a := (1 : ℝ))
        (b := x) (f := fun y => y) hne continuousOn_id)
  have hInt : ∫ y in (1 : ℝ)..x, (1 / y) = L x - L 1 := by
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (1 : ℝ)) (b := x) (f := L)
        (f' := fun y => 1 / y) hderiv' hint)
  have hInt' : L x - L 1 = ∫ y in (1 : ℝ)..x, (1 / y) := by
    simpa using hInt.symm
  have hInt'' : L x = (∫ y in (1 : ℝ)..x, (1 / y)) + L 1 := by
    calc
      L x = L x - L 1 + L 1 := (sub_add_cancel (L x) (L 1)).symm
      _ = (∫ y in (1 : ℝ)..x, (1 / y)) + L 1 := by simp [hInt']
  have hlog : ∫ y in (1 : ℝ)..x, (1 / y) = Real.log x := by
    simpa using (integral_one_div_of_pos (a := (1 : ℝ)) (b := x) (ha := zero_lt_one) (hb := hx))
  calc
    L x = (∫ y in (1 : ℝ)..x, (1 / y)) + L 1 := hInt''
    _ = ∫ y in (1 : ℝ)..x, (1 / y) := by simp [hL1]
    _ = Real.log x := hlog

lemma logAxioms_unique_on_pos {L₁ L₂ : ℝ → ℝ} (hL₁ : LogAxioms L₁) (hL₂ : LogAxioms L₂)
    {x : ℝ} (hx : 0 < x) : L₁ x = L₂ x := by
  calc
    L₁ x = Real.log x := logAxioms_eq_log_on_pos hL₁ hx
    _ = L₂ x := (logAxioms_eq_log_on_pos hL₂ hx).symm

/-- There exists a function `(0,∞) → ℝ` satisfying the logarithm axioms, unique on `(0,∞)`. -/
theorem exists_unique_log_function :
    ∃ L : ℝ → ℝ, LogAxioms L ∧ ∀ L', LogAxioms L' → ∀ {x}, 0 < x → L' x = L x := by
  refine ⟨Real.log, log_satisfies_LogAxioms, ?_⟩
  intro L' hL' x hx
  exact logAxioms_eq_log_on_pos hL' hx

/-- Proposition 5.4.2. There exists a unique function `E : ℝ → (0,∞)` such that
`(i)` `E 0 = 1`; `(ii)` `E` is differentiable with derivative `E x`; `(iii)`
`E` is strictly increasing, bijective onto `(0,∞)`, `E x → 0` as `x → -∞`,
and `E x → ∞` as `x → ∞`; `(iv)` `E (x + y) = E x * E y`; `(v)` for rational
`q`, `E (q * x) = (E x)^q`. -/
def ExpAxioms (E : ℝ → ℝ) : Prop :=
  E 0 = 1 ∧
    (∀ x, HasDerivAt E (E x) x) ∧
    StrictMono E ∧
    (∀ y, 0 < y → ∃ x, E x = y) ∧
    Tendsto E atBot (nhds 0) ∧
    Tendsto E atTop atTop ∧
    (∀ x y, E (x + y) = E x * E y) ∧
    (∀ (q : ℚ) (x : ℝ), E (q * x) = Real.rpow (E x) q)

/-- `Real.exp` satisfies the axioms characterizing the exponential. -/
lemma exp_satisfies_ExpAxioms : ExpAxioms Real.exp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro x
    simpa using Real.hasDerivAt_exp x
  · simpa using Real.exp_strictMono
  · intro y hy
    refine ⟨Real.log y, ?_⟩
    simpa using Real.exp_log hy
  · simpa using Real.tendsto_exp_atBot
  · simpa using Real.tendsto_exp_atTop
  · intro x y
    simpa using Real.exp_add x y
  · intro q x
    simpa [mul_comm] using (Real.exp_mul x (q : ℝ))

/-- There exists a unique function `ℝ → (0,∞)` satisfying the exponential axioms. -/
theorem exists_unique_exp_function : ∃! E : ℝ → ℝ, ExpAxioms E := by
  refine ⟨Real.exp, exp_satisfies_ExpAxioms, ?_⟩
  intro E hE
  ext x
  rcases hE with ⟨hE0, hderiv, -, -, -, -, hmul, -⟩
  have hne : ∀ z, E z ≠ 0 := by
    intro z hz
    have : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = E 0 := by simp [hE0]
        _ = E (z + -z) := by simp
        _ = E z * E (-z) := by simpa using hmul z (-z)
        _ = 0 := by simp [hz]
    exact one_ne_zero this
  have hpos : ∀ z, 0 < E z := by
    intro z
    have hne' : E (z / 2) ≠ 0 := hne (z / 2)
    have hmul' : E z = E (z / 2) * E (z / 2) := by
      simpa [add_halves] using hmul (z / 2) (z / 2)
    have hpos' : 0 < E (z / 2) * E (z / 2) := mul_self_pos.2 hne'
    simpa [hmul'] using hpos'
  have hderiv_log : ∀ z, HasDerivAt (fun t => Real.log (E t)) 1 z := by
    intro z
    have hne' : E z ≠ 0 := hne z
    have hlog' : HasDerivAt Real.log (1 / E z) (E z) := by
      simpa [one_div] using (Real.hasDerivAt_log hne')
    simpa [one_div, hne'] using hlog'.comp z (hderiv z)
  have hInt : ∫ t in (0 : ℝ)..x, (1 : ℝ) = Real.log (E x) - Real.log (E 0) := by
    have hderiv' : ∀ t ∈ Set.uIcc (0 : ℝ) x, HasDerivAt (fun s => Real.log (E s)) 1 t := by
      intro t ht
      exact hderiv_log t
    have hint :
        IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume (0 : ℝ) x := by
      simp
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
        (f := fun s => Real.log (E s)) (f' := fun _ => (1 : ℝ)) hderiv' hint)
  have hlogE : Real.log (E x) = x := by
    have hx : x = Real.log (E x) - Real.log (E 0) := by
      calc
        x = ∫ t in (0 : ℝ)..x, (1 : ℝ) := by simp
        _ = Real.log (E x) - Real.log (E 0) := hInt
    have hx' : x + Real.log (E 0) = Real.log (E x) := (eq_sub_iff_add_eq).1 hx
    have hlogE0 : Real.log (E 0) = 0 := by simp [hE0]
    simpa [hlogE0] using hx'.symm
  have hxpos : 0 < E x := hpos x
  calc
    E x = Real.exp (Real.log (E x)) := by simpa using (Real.exp_log hxpos).symm
    _ = Real.exp x := by simp [hlogE]

/-- Proposition 5.4.3. Let `x, y ∈ ℝ`. (i) `exp (x*y) = (exp x)^y`.
(ii) If `x > 0`, then `ln (x^y) = y * ln x`. -/
lemma exp_mul_rpow (x y : ℝ) : Real.exp (x * y) = (Real.exp x) ^ y := by
  simpa using Real.exp_mul x y

/-- See Proposition 5.4.3 (ii). If `x > 0`, then `ln (x^y) = y * ln x`. -/
lemma log_rpow_pos (x y : ℝ) (hx : 0 < x) : Real.log (x ^ y) = y * Real.log x := by
  simpa using (Real.log_rpow (x := x) (y := y) hx)

end Section04
end Chap05
