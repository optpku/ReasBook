/-
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap05
section Section01

/-- Definition 5.1.1: Let L > 0. A function f : ℝ → ℂ is periodic with period L
if for every x : ℝ, one has f (x + L) = f x. -/
def IsPeriodicWithPeriod (L : ℝ) (f : ℝ → ℂ) : Prop :=
  0 < L ∧ Function.Periodic f L

/-- Definition 5.1.2 (ℤ-periodic and Lℤ-periodic):
A function `f : ℝ → ℂ` is ℤ-periodic iff it is `1`-periodic, i.e.
`f (x + 1) = f x` for all `x : ℝ`. -/
def IsZPeriodic (f : ℝ → ℂ) : Prop :=
  Function.Periodic f 1

/-- A function is Lℤ-periodic when it is periodic with positive period `L`. -/
abbrev IsLZPeriodic (L : ℝ) (f : ℝ → ℂ) : Prop :=
  IsPeriodicWithPeriod L f

/-- Definition 5.1.3 (Integer part and fractional part): for `x : ℝ`, `[x]` is the unique
integer `k : ℤ` such that `k ≤ x < k + 1`. -/
noncomputable def integerPart (x : ℝ) : ℤ :=
  Int.floor x

/-- The fractional part of `x : ℝ`, defined by `{x} = x - [x]`. -/
noncomputable def fractionalPart (x : ℝ) : ℝ :=
  x - (integerPart x : ℝ)

/-- Helper for Example 5.1.2: periodicity is preserved when viewing a real-valued periodic function
as complex-valued via coercion. -/
lemma helperForExample_5_1_2_realToComplex_periodic
    {g : ℝ → ℝ} {T : ℝ} (hg : Function.Periodic g T) :
    Function.Periodic (fun x : ℝ => (g x : ℂ)) T := by
  intro x
  exact congrArg (fun y : ℝ => (y : ℂ)) (hg x)

/-- Helper for Example 5.1.2: base `2π`-periodicity for `sin`, `cos`, and `x ↦ exp(ix)` in the
`ℝ → ℂ` setting. -/
lemma helperForExample_5_1_2_base_periodic_trig_exp :
    Function.Periodic (fun x : ℝ => (Real.sin x : ℂ)) (2 * Real.pi) ∧
    Function.Periodic (fun x : ℝ => (Real.cos x : ℂ)) (2 * Real.pi) ∧
    Function.Periodic (fun x : ℝ => Complex.exp (x * Complex.I)) (2 * Real.pi) := by
  constructor
  · exact helperForExample_5_1_2_realToComplex_periodic Real.sin_periodic
  constructor
  · exact helperForExample_5_1_2_realToComplex_periodic Real.cos_periodic
  · intro x
    have hExp := Complex.exp_mul_I_periodic (x : ℂ)
    simpa using hExp

/-- Helper for Example 5.1.2: if `f` is `L`-periodic, then it is periodic with period `Lk` for
every integer `k`. -/
lemma helperForExample_5_1_2_periodic_mul_int_right
    {f : ℝ → ℂ} {L : ℝ} (hf : Function.Periodic f L) :
    ∀ k : ℤ, Function.Periodic f (L * (k : ℝ)) := by
  intro k
  simpa [mul_comm] using (hf.int_mul k)

/-- Helper for Example 5.1.2: the identity map `x ↦ x` (viewed as `ℝ → ℂ`) is not periodic with
any positive period. -/
lemma helperForExample_5_1_2_identity_not_periodic_with_positive_period :
    ¬ ∃ L : ℝ, IsPeriodicWithPeriod L (fun x : ℝ => (x : ℂ)) := by
  intro h
  rcases h with ⟨L, hL⟩
  rcases hL with ⟨hLpos, hper⟩
  have hNotInj : ¬ Function.Injective (fun x : ℝ => (x : ℂ)) :=
    Function.Periodic.not_injective hper (ne_of_gt hLpos)
  exact hNotInj Complex.ofReal_injective

/-- Helper for Example 5.1.2: the constant function `1` is periodic with every positive period. -/
lemma helperForExample_5_1_2_constant_one_isPeriodicWithPeriod
    (L : ℝ) (hL : 0 < L) : IsPeriodicWithPeriod L (fun _ : ℝ => (1 : ℂ)) := by
  refine ⟨hL, ?_⟩
  intro x
  rfl

/-- Example 5.1.2: sin x, cos x, and exp(ix) are 2π-periodic, hence periodic with period 2πk for
every integer k; the identity function is not periodic with positive period, while the constant
function 1 is L-periodic for every L > 0. -/
theorem periodicity_examples_basic :
    IsPeriodicWithPeriod (2 * Real.pi) (fun x : ℝ => (Real.sin x : ℂ)) ∧
    IsPeriodicWithPeriod (2 * Real.pi) (fun x : ℝ => (Real.cos x : ℂ)) ∧
    IsPeriodicWithPeriod (2 * Real.pi) (fun x : ℝ => Complex.exp (x * Complex.I)) ∧
    (∀ k : ℤ, Function.Periodic (fun x : ℝ => (Real.sin x : ℂ)) ((2 * Real.pi) * (k : ℝ))) ∧
    (∀ k : ℤ, Function.Periodic (fun x : ℝ => (Real.cos x : ℂ)) ((2 * Real.pi) * (k : ℝ))) ∧
    (∀ k : ℤ, Function.Periodic (fun x : ℝ => Complex.exp (x * Complex.I)) ((2 * Real.pi) * (k : ℝ))) ∧
    (¬ ∃ L : ℝ, IsPeriodicWithPeriod L (fun x : ℝ => (x : ℂ))) ∧
    (∀ L : ℝ, 0 < L → IsPeriodicWithPeriod L (fun _ : ℝ => (1 : ℂ))) := by
  have h2pi : 0 < 2 * Real.pi := by
    positivity
  rcases helperForExample_5_1_2_base_periodic_trig_exp with ⟨hSin2pi, hCos2pi, hExp2pi⟩
  refine ⟨?_, ?_⟩
  · exact ⟨h2pi, hSin2pi⟩
  · refine ⟨?_, ?_⟩
    · exact ⟨h2pi, hCos2pi⟩
    · refine ⟨?_, ?_⟩
      · exact ⟨h2pi, hExp2pi⟩
      · refine ⟨?_, ?_⟩
        · intro k
          exact helperForExample_5_1_2_periodic_mul_int_right hSin2pi k
        · refine ⟨?_, ?_⟩
          · intro k
            exact helperForExample_5_1_2_periodic_mul_int_right hCos2pi k
          · refine ⟨?_, ?_⟩
            · intro k
              exact helperForExample_5_1_2_periodic_mul_int_right hExp2pi k
            · refine ⟨?_, ?_⟩
              · exact helperForExample_5_1_2_identity_not_periodic_with_positive_period
              · intro L hL
                exact helperForExample_5_1_2_constant_one_isPeriodicWithPeriod L hL

/-- Helper for Corollary 5.1.1: integer multiples of a period are also periods. -/
lemma helperForCorollary_5_1_1_intShift_ofPeriodic
    {L : ℝ} {f : ℝ → ℂ} (hLper : Function.Periodic f L) :
    ∀ x : ℝ, ∀ k : ℤ, f (x + (k : ℝ) * L) = f x := by
  intro x k
  have hIntPer : Function.Periodic f ((k : ℝ) * L) := by
    simpa [mul_comm] using hLper.int_mul k
  exact hIntPer x

/-- Helper for Corollary 5.1.1: `IsPeriodicWithPeriod` implies integer-shift invariance by `L`. -/
lemma helperForCorollary_5_1_1_intShift_ofIsPeriodicWithPeriod
    {L : ℝ} {f : ℝ → ℂ} (hIsPer : IsPeriodicWithPeriod L f) :
    ∀ x : ℝ, ∀ k : ℤ, f (x + (k : ℝ) * L) = f x := by
  rcases hIsPer with ⟨_, hLper⟩
  exact helperForCorollary_5_1_1_intShift_ofPeriodic hLper

/-- Helper for Corollary 5.1.1: specialization to unit period gives `k`-shift invariance. -/
lemma helperForCorollary_5_1_1_unitPeriodSpecialization
    {f : ℝ → ℂ} (hIsPer1 : IsPeriodicWithPeriod 1 f) :
    ∀ x : ℝ, ∀ k : ℤ, f (x + (k : ℝ)) = f x := by
  intro x k
  simpa [mul_one] using helperForCorollary_5_1_1_intShift_ofIsPeriodicWithPeriod hIsPer1 x k

/-- Corollary 5.1.1 (kL-shift invariance): If f : ℝ → ℂ is L-periodic, then
f (x + kL) = f x for all x : ℝ and k : ℤ. In particular, if f is 1-periodic,
then f (x + k) = f x for all k : ℤ. -/
theorem periodic_integer_shift_invariance :
    (∀ {L : ℝ} {f : ℝ → ℂ}, IsPeriodicWithPeriod L f →
      ∀ x : ℝ, ∀ k : ℤ, f (x + (k : ℝ) * L) = f x) ∧
    (∀ {f : ℝ → ℂ}, IsPeriodicWithPeriod 1 f →
      ∀ x : ℝ, ∀ k : ℤ, f (x + (k : ℝ)) = f x) := by
  refine ⟨?_, ?_⟩
  · intro L f hIsPer x k
    exact helperForCorollary_5_1_1_intShift_ofIsPeriodicWithPeriod hIsPer x k
  · intro f hIsPer1 x k
    exact helperForCorollary_5_1_1_unitPeriodSpecialization hIsPer1 x k

/-- The square-wave function on `ℝ`, defined by its fractional part: value `1` on the first
half of each unit interval and `0` on the second half. -/
noncomputable def squareWave : ℝ → ℂ :=
  fun x => if x - (Int.floor x : ℝ) < (1 / 2 : ℝ) then (1 : ℂ) else 0

/-- Example 5.1.4: For `n : ℤ`, the functions `x ↦ cos(2πnx)`, `x ↦ sin(2πnx)`, and
`x ↦ exp(2πinx)` are all `ℤ`-periodic (equivalently `1`-periodic). Another `ℤ`-periodic
function is the square wave. -/
theorem zPeriodic_trig_modes_and_squareWave (n : ℤ) :
    IsZPeriodic (fun x : ℝ => (Real.cos (2 * Real.pi * (n : ℝ) * x) : ℂ)) ∧
    IsZPeriodic (fun x : ℝ => (Real.sin (2 * Real.pi * (n : ℝ) * x) : ℂ)) ∧
    IsZPeriodic (fun x : ℝ => Complex.exp (2 * Real.pi * (n : ℝ) * x * Complex.I)) ∧
    IsZPeriodic squareWave := by
  rcases helperForExample_5_1_2_base_periodic_trig_exp with ⟨hSinBase, hCosBase, hExpBase⟩
  have hCosIntMul :
      Function.Periodic (fun t : ℝ => (Real.cos t : ℂ)) ((n : ℝ) * (2 * Real.pi)) := by
    simpa [mul_comm] using hCosBase.int_mul n
  have hSinIntMul :
      Function.Periodic (fun t : ℝ => (Real.sin t : ℂ)) ((n : ℝ) * (2 * Real.pi)) := by
    simpa [mul_comm] using hSinBase.int_mul n
  have hExpIntMul :
      Function.Periodic (fun t : ℝ => Complex.exp (t * Complex.I)) ((n : ℝ) * (2 * Real.pi)) := by
    simpa [mul_comm] using hExpBase.int_mul n
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    have hArg :
        2 * Real.pi * (n : ℝ) * (x + 1) =
          (2 * Real.pi * (n : ℝ) * x) + ((n : ℝ) * (2 * Real.pi)) := by
      ring
    calc
      (Real.cos (2 * Real.pi * (n : ℝ) * (x + 1)) : ℂ)
          = (Real.cos ((2 * Real.pi * (n : ℝ) * x) + ((n : ℝ) * (2 * Real.pi))) : ℂ) := by
              rw [hArg]
      _ = (Real.cos (2 * Real.pi * (n : ℝ) * x) : ℂ) := by
            exact hCosIntMul (2 * Real.pi * (n : ℝ) * x)
  · intro x
    have hArg :
        2 * Real.pi * (n : ℝ) * (x + 1) =
          (2 * Real.pi * (n : ℝ) * x) + ((n : ℝ) * (2 * Real.pi)) := by
      ring
    calc
      (Real.sin (2 * Real.pi * (n : ℝ) * (x + 1)) : ℂ)
          = (Real.sin ((2 * Real.pi * (n : ℝ) * x) + ((n : ℝ) * (2 * Real.pi))) : ℂ) := by
              rw [hArg]
      _ = (Real.sin (2 * Real.pi * (n : ℝ) * x) : ℂ) := by
            exact hSinIntMul (2 * Real.pi * (n : ℝ) * x)
  · intro x
    simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
      (hExpIntMul (2 * Real.pi * (n : ℝ) * x))
  · intro x
    have hFloorCast : (Int.floor (x + 1) : ℝ) = (Int.floor x : ℝ) + 1 := by
      simp [Int.cast_add, Int.floor_add_one]
    unfold squareWave
    rw [hFloorCast]
    have hFrac : x + 1 - ((Int.floor x : ℝ) + 1) = x - (Int.floor x : ℝ) := by
      ring
    rw [hFrac]

/-- Helper for Lemma 5.1.5a: a continuous `ℤ`-periodic function has bounded range. -/
lemma helperForLemma_5_1_5a_boundedRange_of_continuous_periodic
    {f : ℝ → ℂ} (hf_cont : Continuous f) (hf_per : IsZPeriodic f) :
    Bornology.IsBounded (Set.range f) := by
  exact Function.Periodic.isBounded_of_continuous hf_per one_ne_zero hf_cont

/-- Helper for Lemma 5.1.5a: bounded range gives a uniform bound on values. -/
lemma helperForLemma_5_1_5a_exists_uniform_norm_bound_of_boundedRange
    {f : ℝ → ℂ} (hbounded : Bornology.IsBounded (Set.range f)) :
    ∃ C : ℝ, ∀ x : ℝ, ‖f x‖ ≤ C := by
  rcases hbounded.exists_norm_le with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x
  have hx : f x ∈ Set.range f := ⟨x, rfl⟩
  exact hC (f x) hx

/-- Lemma 5.1.5a (Basic properties of `C(ℝ/ℤ;ℂ)` (a), Boundedness): if
`f : ℝ → ℂ` is continuous and `ℤ`-periodic, then `f` is bounded. -/
lemma isZPeriodic_continuous_bounded
    {f : ℝ → ℂ} (hf_cont : Continuous f) (hf_per : IsZPeriodic f) :
    ∃ C : ℝ, ∀ x : ℝ, ‖f x‖ ≤ C := by
  have hbounded : Bornology.IsBounded (Set.range f) :=
    helperForLemma_5_1_5a_boundedRange_of_continuous_periodic hf_cont hf_per
  exact helperForLemma_5_1_5a_exists_uniform_norm_bound_of_boundedRange hbounded

/-- Helper for Lemma 5.1.5b: closure of continuous `ℤ`-periodic functions under addition. -/
lemma helperForLemma_5_1_5b_add_closed
    {f g : ℝ → ℂ} (hf : Continuous f ∧ IsZPeriodic f) (hg : Continuous g ∧ IsZPeriodic g) :
    Continuous (f + g) ∧ IsZPeriodic (f + g) := by
  rcases hf with ⟨hf_cont, hf_per⟩
  rcases hg with ⟨hg_cont, hg_per⟩
  constructor
  · exact hf_cont.add hg_cont
  · simpa [IsZPeriodic] using hf_per.add hg_per

/-- Helper for Lemma 5.1.5b: closure of continuous `ℤ`-periodic functions under subtraction. -/
lemma helperForLemma_5_1_5b_sub_closed
    {f g : ℝ → ℂ} (hf : Continuous f ∧ IsZPeriodic f) (hg : Continuous g ∧ IsZPeriodic g) :
    Continuous (f - g) ∧ IsZPeriodic (f - g) := by
  rcases hf with ⟨hf_cont, hf_per⟩
  rcases hg with ⟨hg_cont, hg_per⟩
  constructor
  · exact hf_cont.sub hg_cont
  · simpa [IsZPeriodic] using hf_per.sub hg_per

/-- Helper for Lemma 5.1.5b: closure of continuous `ℤ`-periodic functions under multiplication. -/
lemma helperForLemma_5_1_5b_mul_closed
    {f g : ℝ → ℂ} (hf : Continuous f ∧ IsZPeriodic f) (hg : Continuous g ∧ IsZPeriodic g) :
    Continuous (f * g) ∧ IsZPeriodic (f * g) := by
  rcases hf with ⟨hf_cont, hf_per⟩
  rcases hg with ⟨hg_cont, hg_per⟩
  constructor
  · exact hf_cont.mul hg_cont
  · simpa [IsZPeriodic] using hf_per.mul hg_per

/-- Helper for Lemma 5.1.5b: closure of continuous `ℤ`-periodic functions under scalar multiplication. -/
lemma helperForLemma_5_1_5b_smul_closed
    {f : ℝ → ℂ} (c : ℂ) (hf : Continuous f ∧ IsZPeriodic f) :
    Continuous (c • f) ∧ IsZPeriodic (c • f) := by
  rcases hf with ⟨hf_cont, hf_per⟩
  constructor
  · exact hf_cont.const_smul c
  · simpa [IsZPeriodic] using hf_per.smul c

/-- Lemma 5.1.5b (Basic properties of `C(ℝ/ℤ;ℂ)` (b), vector space and algebra properties):
if `f, g : ℝ → ℂ` are continuous and `ℤ`-periodic, then `f + g`, `f - g`, and `f * g`
are continuous and `ℤ`-periodic; and for any scalar `c : ℂ`, `c • f` is continuous and
`ℤ`-periodic. -/
lemma isZPeriodic_continuous_add_sub_mul_smul
    {f g : ℝ → ℂ} (hf : Continuous f ∧ IsZPeriodic f) (hg : Continuous g ∧ IsZPeriodic g)
    (c : ℂ) :
    (Continuous (f + g) ∧ IsZPeriodic (f + g)) ∧
    (Continuous (f - g) ∧ IsZPeriodic (f - g)) ∧
    (Continuous (f * g) ∧ IsZPeriodic (f * g)) ∧
    (Continuous (c • f) ∧ IsZPeriodic (c • f)) := by
  constructor
  · exact helperForLemma_5_1_5b_add_closed hf hg
  constructor
  · exact helperForLemma_5_1_5b_sub_closed hf hg
  constructor
  · exact helperForLemma_5_1_5b_mul_closed hf hg
  · exact helperForLemma_5_1_5b_smul_closed c hf

/-- Helper for Lemma 5.1.5c: a uniform limit of eventually continuous maps is continuous. -/
lemma helperForLemma_5_1_5c_continuous_of_uniform_limit
    {f : ℝ → ℂ} {u : ℕ → ℝ → ℂ}
    (hlim : TendstoUniformly u f Filter.atTop)
    (hcont : ∀ n : ℕ, Continuous (u n)) :
    Continuous f := by
  exact hlim.continuous (Filter.Frequently.of_forall hcont)

/-- Helper for Lemma 5.1.5c: periodicity of each approximant gives eventual equality
of shifted evaluation sequences. -/
lemma helperForLemma_5_1_5c_eventuallyEq_shifted_sequence
    {u : ℕ → ℝ → ℂ}
    (hper : ∀ n : ℕ, IsZPeriodic (u n))
    (x : ℝ) :
    (fun n : ℕ => u n (x + 1)) =ᶠ[Filter.atTop] (fun n : ℕ => u n x) := by
  refine Filter.Eventually.of_forall ?_
  intro n
  simpa [IsZPeriodic] using (hper n x)

/-- Helper for Lemma 5.1.5c: the uniform limit inherits the unit-shift identity. -/
lemma helperForLemma_5_1_5c_shift_eq_of_uniform_limit
    {f : ℝ → ℂ} {u : ℕ → ℝ → ℂ}
    (hlim : TendstoUniformly u f Filter.atTop)
    (hper : ∀ n : ℕ, IsZPeriodic (u n))
    (x : ℝ) :
    f (x + 1) = f x := by
  have hTendstoShift :
      Filter.Tendsto (fun n : ℕ => u n (x + 1)) Filter.atTop (nhds (f (x + 1))) :=
    hlim.tendsto_at (x + 1)
  have hTendstoBase :
      Filter.Tendsto (fun n : ℕ => u n x) Filter.atTop (nhds (f x)) :=
    hlim.tendsto_at x
  have hEventuallyEq :
      (fun n : ℕ => u n (x + 1)) =ᶠ[Filter.atTop] (fun n : ℕ => u n x) :=
    helperForLemma_5_1_5c_eventuallyEq_shifted_sequence hper x
  exact tendsto_nhds_unique_of_eventuallyEq hTendstoShift hTendstoBase hEventuallyEq

/-- Helper for Lemma 5.1.5c: a uniform limit of `ℤ`-periodic functions is `ℤ`-periodic. -/
lemma helperForLemma_5_1_5c_isZPeriodic_of_uniform_limit
    {f : ℝ → ℂ} {u : ℕ → ℝ → ℂ}
    (hlim : TendstoUniformly u f Filter.atTop)
    (hper : ∀ n : ℕ, IsZPeriodic (u n)) :
    IsZPeriodic f := by
  intro x
  exact helperForLemma_5_1_5c_shift_eq_of_uniform_limit hlim hper x

/-- Lemma 5.1.5c (Basic properties of C(ℝ/ℤ;ℂ) (c), closure under uniform limits):
if (fₙ) is a sequence of continuous ℤ-periodic functions converging uniformly to f,
then f is continuous and ℤ-periodic. -/
lemma isZPeriodic_continuous_of_tendstoUniformly
    {f : ℝ → ℂ} {u : ℕ → ℝ → ℂ}
    (hcont : ∀ n : ℕ, Continuous (u n))
    (hper : ∀ n : ℕ, IsZPeriodic (u n))
    (hlim : TendstoUniformly u f Filter.atTop) :
    Continuous f ∧ IsZPeriodic f := by
  have hContF : Continuous f :=
    helperForLemma_5_1_5c_continuous_of_uniform_limit hlim hcont
  have hPerF : IsZPeriodic f :=
    helperForLemma_5_1_5c_isZPeriodic_of_uniform_limit hlim hper
  exact ⟨hContF, hPerF⟩

end Section01
end Chap05
