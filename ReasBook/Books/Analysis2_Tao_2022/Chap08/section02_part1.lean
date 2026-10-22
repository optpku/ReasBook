/-
Authors: Zichen Wang, Wanli Ma, Min Cui, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap08
section Section02

/-- Definition 8.5 (Majorization): for functions `f, g : Ω → ℝ`, `f` majorizes `g`
(equivalently, `g` minorizes `f`) iff `∀ x : Ω, f x ≥ g x`. -/
def Majorizes {Ω : Type*} (f g : Ω → ℝ) : Prop :=
  ∀ x : Ω, f x ≥ g x

/-- Integral of a nonnegative function over a set,
encoded via an indicator on the ambient space. -/
noncomputable def integralOver {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (Ω : Set X) (f : X → ENNReal) : ENNReal :=
  ∫⁻ x, Set.indicator Ω f x ∂μ

/-- Rewrite the indicator-based set integral as a restricted lintegral. -/
lemma helperForProposition_8_3_1_integralOver_eq_setLIntegral {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) {Ω : Set X} (hΩ : MeasurableSet Ω) (f : X → ENNReal) :
    integralOver μ Ω f = ∫⁻ x in Ω, f x ∂μ := by
  unfold integralOver
  simpa using MeasureTheory.lintegral_indicator hΩ f

/-- A restricted lintegral vanishes iff the function vanishes almost
everywhere on the set. -/
lemma helperForProposition_8_3_1_setLIntegral_eq_zero_iff_aeOn {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) {Ω : Set X} (hΩ : MeasurableSet Ω) {f : X → ENNReal}
    (hf : Measurable f) :
    (∫⁻ x in Ω, f x ∂μ = 0) ↔ ∀ᵐ x ∂μ, x ∈ Ω → f x = 0 := by
  simpa using MeasureTheory.setLIntegral_eq_zero_iff (μ := μ) (s := Ω) hΩ hf

/-- The integral over a set is bounded between `0` and `⊤`. -/
lemma helperForProposition_8_3_1_integralOver_nonneg_le_top {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (Ω : Set X) (f : X → ENNReal) :
    0 ≤ integralOver μ Ω f ∧ integralOver μ Ω f ≤ ⊤ := by
  constructor
  · exact bot_le
  · exact le_top

/-- Bridge restricted-measure a.e. and ambient a.e.-on-set
formulations. -/
lemma helperForProposition_8_3_1_aeOn_restrict_bridge {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) {Ω : Set X} (hΩ : MeasurableSet Ω) (f : X → ENNReal) :
    (∀ᵐ x ∂μ.restrict Ω, f x = 0) ↔ ∀ᵐ x ∂μ, x ∈ Ω → f x = 0 := by
  simpa using (MeasureTheory.ae_restrict_iff' (μ := μ) (s := Ω) (p := fun x => f x = 0) hΩ)

/-- Proposition 8.3.1: for a measurable set `Ω` and measurable `f : X → [0, ∞]`, the
indicator-based integral over `Ω` is in `[0, ∞]`, and it is zero iff `f = 0` for
`μ`-almost every `x ∈ Ω`. -/
theorem proposition_8_3_1 {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    {Ω : Set X} (hΩ : MeasurableSet Ω) {f : X → ENNReal} (hf : Measurable f) :
    (0 ≤ integralOver μ Ω f ∧ integralOver μ Ω f ≤ ⊤) ∧
      (integralOver μ Ω f = 0 ↔ ∀ᵐ x ∂μ, x ∈ Ω → f x = 0) := by
  constructor
  · exact helperForProposition_8_3_1_integralOver_nonneg_le_top μ Ω f
  · simpa [helperForProposition_8_3_1_integralOver_eq_setLIntegral
      (μ := μ) (hΩ := hΩ) (f := f)] using
      (helperForProposition_8_3_1_setLIntegral_eq_zero_iff_aeOn
        (μ := μ) (hΩ := hΩ) (f := f) hf)

/-- Proposition 8.3.2: for a measurable set `Ω` and measurable `f : X → [0, ∞]`,
if `c > 0` then integrating `cf` over `Ω` scales the integral by `c`. -/
theorem proposition_8_3_2 {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    {Ω : Set X} (hΩ : MeasurableSet Ω) {f : X → ENNReal} (hf : Measurable f)
    (c : ENNReal) (hc : 0 < c) :
    integralOver μ Ω (fun x => c * f x) = c * integralOver μ Ω f := by
  unfold integralOver
  calc
    ∫⁻ x, Set.indicator Ω (fun x => c * f x) x ∂μ
        = ∫⁻ x, c * Set.indicator Ω f x ∂μ := by
            congr with x
            by_cases hx : x ∈ Ω <;> simp [hx]
    _ = c * ∫⁻ x, Set.indicator Ω f x ∂μ := by
          simpa using MeasureTheory.lintegral_const_mul c (hf.indicator hΩ)

/-- Extension by zero from `Ω` to the ambient space. -/
noncomputable def extendByZero {X : Type*} (Ω : Set X) (f : Ω → ENNReal) : X → ENNReal :=
  letI : DecidablePred (fun x => x ∈ Ω) := Classical.decPred (fun x => x ∈ Ω)
  fun x => if hx : x ∈ Ω then f ⟨x, hx⟩ else 0

/-- Proposition 8.3.3: if `f, g : Ω → [0, ∞]` are measurable and `f x ≤ g x` for all
`x ∈ Ω`, then the indicator-defined integral over `Ω` is monotone after extending by zero:
`∫_Ω f dμ ≤ ∫_Ω g dμ`. -/
theorem proposition_8_3_3 {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    {Ω : Set X} (hΩ : MeasurableSet Ω) {f g : Ω → ENNReal} (hf : Measurable f)
    (hg : Measurable g) (hfg : ∀ x : Ω, f x ≤ g x) :
    integralOver μ Ω (extendByZero Ω f) ≤ integralOver μ Ω (extendByZero Ω g) := by
  unfold integralOver
  refine MeasureTheory.lintegral_mono ?_
  intro x
  by_cases hx : x ∈ Ω
  · simp [hx, extendByZero, hfg ⟨x, hx⟩]
  · simp [hx]

/-- Helper for Proposition 8.3.4: convert a.e.-on-`Ω` equality into a.e. equality of
indicator integrands. -/
lemma helperForProposition_8_3_4_ae_indicator_congr {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) {Ω : Set X} {u v : X → ENNReal}
    (huv : ∀ᵐ x ∂μ, x ∈ Ω → u x = v x) :
    ∀ᵐ x ∂μ, Set.indicator Ω u x = Set.indicator Ω v x := by
  filter_upwards [huv] with x hx
  by_cases hmem : x ∈ Ω
  · simp [hmem, hx hmem]
  · simp [hmem]

/-- Helper for Proposition 8.3.4: a.e.-on-`Ω` equality implies equality of
indicator-defined integrals over `Ω`. -/
lemma helperForProposition_8_3_4_integralOver_congr_aeOn {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (Ω : Set X) {u v : X → ENNReal}
    (huv : ∀ᵐ x ∂μ, x ∈ Ω → u x = v x) :
    integralOver μ Ω u = integralOver μ Ω v := by
  unfold integralOver
  exact MeasureTheory.lintegral_congr_ae
    (helperForProposition_8_3_4_ae_indicator_congr μ huv)

/-- Proposition 8.3.4: let `Ω` be measurable and let `f, g : Ω → [0, ∞]` be measurable.
If `f = g` for `μ`-almost every `x ∈ Ω`, then their indicator-defined integrals over `Ω`
are equal. -/
theorem proposition_8_3_4 {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    {Ω : Set X} (hΩ : MeasurableSet Ω) {f g : Ω → ENNReal} (hf : Measurable f)
    (hg : Measurable g)
    (hfg : ∀ᵐ x ∂μ, x ∈ Ω → extendByZero Ω f x = extendByZero Ω g x) :
    integralOver μ Ω (extendByZero Ω f) = integralOver μ Ω (extendByZero Ω g) := by
  exact helperForProposition_8_3_4_integralOver_congr_aeOn μ Ω hfg

/-- Helper for Proposition 8.3.5: collapsing nested indicators when `Ω' ⊆ Ω`. -/
lemma helperForProposition_8_3_5_indicator_collapse_under_subset {X : Type*}
    {Ω Ω' : Set X} (hΩ'sub : Ω' ⊆ Ω) (u : X → ENNReal) :
    Set.indicator Ω (Set.indicator Ω' u) = Set.indicator Ω' u := by
  funext x
  by_cases hxΩ : x ∈ Ω
  · by_cases hxΩ' : x ∈ Ω'
    · simp [hxΩ, hxΩ']
    · simp [hxΩ, hxΩ']
  · have hxΩ' : x ∉ Ω' := by
      intro hx
      exact hxΩ (hΩ'sub hx)
    simp [hxΩ, hxΩ']

/-- Helper for Proposition 8.3.5: rewriting the `Ω'`-integral as an `Ω`-integral of
an indicator-restricted integrand. -/
lemma helperForProposition_8_3_5_integralOver_indicator_eq {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) {Ω Ω' : Set X} (hΩ'sub : Ω' ⊆ Ω) (u : X → ENNReal) :
    integralOver μ Ω' u = integralOver μ Ω (Set.indicator Ω' u) := by
  unfold integralOver
  rw [helperForProposition_8_3_5_indicator_collapse_under_subset hΩ'sub u]

/-- Helper for Proposition 8.3.5: monotonicity of `integralOver` under set inclusion. -/
lemma helperForProposition_8_3_5_integralOver_mono_subset {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) {Ω Ω' : Set X} (hΩ'sub : Ω' ⊆ Ω) (u : X → ENNReal) :
    integralOver μ Ω' u ≤ integralOver μ Ω u := by
  unfold integralOver
  refine MeasureTheory.lintegral_mono ?_
  intro x
  by_cases hxΩ : x ∈ Ω
  · by_cases hxΩ' : x ∈ Ω'
    · simp [hxΩ, hxΩ']
    · simp [hxΩ, hxΩ']
  · have hxΩ' : x ∉ Ω' := by
      intro hx
      exact hxΩ (hΩ'sub hx)
    simp [hxΩ, hxΩ']

/-- Proposition 8.3.5: for measurable `Ω' ⊆ Ω` and measurable `f : Ω → [0, ∞]`,
the integral over `Ω'` equals the integral over `Ω` of `extendByZero Ω f` multiplied by
`χ_{Ω'}`, and this quantity is at most the integral over `Ω` of `extendByZero Ω f`. -/
theorem proposition_8_3_5 {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    {Ω Ω' : Set X} (hΩ : MeasurableSet Ω) (hΩ' : MeasurableSet Ω') (hΩ'sub : Ω' ⊆ Ω)
    {f : Ω → ENNReal} (hf : Measurable f) :
    integralOver μ Ω' (extendByZero Ω f) =
      integralOver μ Ω (Set.indicator Ω' (extendByZero Ω f)) ∧
      integralOver μ Ω (Set.indicator Ω' (extendByZero Ω f)) ≤
        integralOver μ Ω (extendByZero Ω f) := by
  constructor
  · exact helperForProposition_8_3_5_integralOver_indicator_eq μ hΩ'sub (extendByZero Ω f)
  · calc
      integralOver μ Ω (Set.indicator Ω' (extendByZero Ω f))
          = integralOver μ Ω' (extendByZero Ω f) := by
              symm
              exact
                helperForProposition_8_3_5_integralOver_indicator_eq μ hΩ'sub
                  (extendByZero Ω f)
      _ ≤ integralOver μ Ω (extendByZero Ω f) :=
        helperForProposition_8_3_5_integralOver_mono_subset μ hΩ'sub (extendByZero Ω f)

/-- A non-negative simple function on `Ω` is a finite sum of non-negative coefficients times
indicators of measurable subsets of `Ω`. -/
def IsNonnegativeSimpleFunctionOn {n : ℕ} (Ω : Set (Fin n → ℝ))
    (s : (Fin n → ℝ) → ENNReal) : Prop :=
  ∃ (m : ℕ) (a : Fin m → NNReal) (E : Fin m → Set (Fin n → ℝ)),
    (∀ k : Fin m, MeasurableSet (E k)) ∧
      (∀ k : Fin m, E k ⊆ Ω) ∧
      s = fun x =>
        ∑ k : Fin m, (a k : ENNReal) * Set.indicator (E k) (fun _ => (1 : ENNReal)) x

/-- Integral formula for a represented non-negative simple function. -/
noncomputable def nonnegativeSimpleFunctionIntegral {n : ℕ}
    (m : ℕ) (a : Fin m → NNReal) (E : Fin m → Set (Fin n → ℝ)) : ENNReal :=
  ∑ k : Fin m, (a k : ENNReal) * MeasureTheory.volume (E k)

/-- For a represented simple function, integration over `Ω` matches the coefficient-measure sum. -/
theorem lintegral_eq_nonnegativeSimpleFunctionIntegral {n : ℕ}
    (Ω : Set (Fin n → ℝ))
    (m : ℕ) (a : Fin m → NNReal) (E : Fin m → Set (Fin n → ℝ))
    (hE_meas : ∀ k : Fin m, MeasurableSet (E k))
    (hE_sub : ∀ k : Fin m, E k ⊆ Ω) :
    (∫⁻ x in Ω,
        (∑ k : Fin m, (a k : ENNReal) * Set.indicator (E k) (fun _ => (1 : ENNReal)) x)
          ∂MeasureTheory.volume)
      = nonnegativeSimpleFunctionIntegral (n := n) m a E := by
  have hIndicatorIntegral :
      ∀ k : Fin m,
        (∫⁻ x in Ω, Set.indicator (E k) (fun _ => (1 : ENNReal)) x ∂MeasureTheory.volume) =
          MeasureTheory.volume (E k) := by
    intro k
    calc
      (∫⁻ x in Ω, Set.indicator (E k) (fun _ => (1 : ENNReal)) x ∂MeasureTheory.volume)
          = ∫⁻ x in E k ∩ Ω, (1 : ENNReal) ∂MeasureTheory.volume := by
              simpa using
                (MeasureTheory.setLIntegral_indicator (μ := MeasureTheory.volume)
                  (s := E k) (t := Ω) (f := fun _ : Fin n → ℝ => (1 : ENNReal)) (hE_meas k))
      _ = MeasureTheory.volume (E k ∩ Ω) := by
            simpa using
              (MeasureTheory.setLIntegral_one (μ := MeasureTheory.volume) (s := E k ∩ Ω))
      _ = MeasureTheory.volume (E k) := by
            rw [Set.inter_eq_left.mpr (hE_sub k)]
  have hScaledIntegral :
      ∀ k : Fin m,
        (∫⁻ x in Ω,
            (a k : ENNReal) * Set.indicator (E k) (fun _ => (1 : ENNReal)) x
              ∂MeasureTheory.volume) =
          (a k : ENNReal) * MeasureTheory.volume (E k) := by
    intro k
    calc
      (∫⁻ x in Ω,
          (a k : ENNReal) * Set.indicator (E k) (fun _ => (1 : ENNReal)) x
            ∂MeasureTheory.volume)
          = (a k : ENNReal) *
              (∫⁻ x in Ω, Set.indicator (E k) (fun _ => (1 : ENNReal)) x
                ∂MeasureTheory.volume) := by
                  simpa using
                    (MeasureTheory.lintegral_const_mul (a k : ENNReal)
                      ((measurable_one.indicator (hE_meas k))))
      _ = (a k : ENNReal) * MeasureTheory.volume (E k) := by
            rw [hIndicatorIntegral k]
  have hSummandMeasurable :
      ∀ k : Fin m,
        Measurable
          (fun x : Fin n → ℝ =>
            (a k : ENNReal) * Set.indicator (E k) (fun _ => (1 : ENNReal)) x) := by
    intro k
    exact measurable_const.mul (measurable_one.indicator (hE_meas k))
  calc
    (∫⁻ x in Ω,
        (∑ k : Fin m, (a k : ENNReal) * Set.indicator (E k) (fun _ => (1 : ENNReal)) x)
          ∂MeasureTheory.volume)
        =
          ∑ k : Fin m,
            ∫⁻ x in Ω,
              (a k : ENNReal) * Set.indicator (E k) (fun _ => (1 : ENNReal)) x
                ∂MeasureTheory.volume := by
                  simpa using
                    (MeasureTheory.lintegral_finset_sum
                      (s := Finset.univ)
                      (f := fun k x =>
                        (a k : ENNReal) *
                          Set.indicator (E k) (fun _ => (1 : ENNReal)) x)
                      (μ := MeasureTheory.volume.restrict Ω)
                      (fun k hk => hSummandMeasurable k))
    _ = ∑ k : Fin m, (a k : ENNReal) * MeasureTheory.volume (E k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact hScaledIntegral k
    _ = nonnegativeSimpleFunctionIntegral (n := n) m a E := by
          rfl

/-- Supremum over non-negative simple functions bounded above by `f` on `Ω`. -/
noncomputable def lebesgueIntegralNonnegSup {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ENNReal) : ENNReal :=
  ⨆ (s : (Fin n → ℝ) → ENNReal) (_hs : IsNonnegativeSimpleFunctionOn Ω s)
      (_hdom : ∀ x ∈ Ω, s x ≤ f x), ∫⁻ x in Ω, s x ∂MeasureTheory.volume

/-- Definition 8.6 (Lebesgue integral for non-negative functions): define `∫_Ω f dx` by the
restricted Lebesgue integral. -/
noncomputable def lebesgueIntegralNonneg {n : ℕ}
    (Ω : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ENNReal) : ENNReal :=
  ∫⁻ x in Ω, f x ∂MeasureTheory.volume

/-- Lemma 8.5 (Interchange of addition and integration): if `Ω ⊆ ℝ^n` is measurable and
`f, g : Ω → [0, ∞]` are measurable, then integrating `f + g` over `Ω` equals the sum of
the integrals of `f` and `g` over `Ω`. -/
theorem lintegral_add_on_measurableSet_subtype
    {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    {f g : Ω → ENNReal} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x : Ω, (f x + g x) ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) =
      (∫⁻ x : Ω, f x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ)))) +
        (∫⁻ x : Ω, g x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ)))) := by
  simpa using MeasureTheory.lintegral_add_left hf g

/-- Lemma 8.6 (Fatou's lemma): if `Ω ⊆ ℝ^n` is measurable and
`f_n : Ω → [0, ∞]` is measurable for each `n`, then
`∫_Ω liminf_{n→∞} f_n ≤ liminf_{n→∞} ∫_Ω f_n`. -/
theorem lintegral_liminf_le_liminf_lintegral_subtype
    {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (f : ℕ → Ω → ENNReal) (hf : ∀ k : ℕ, Measurable (f k)) :
    ∫⁻ x : Ω, Filter.liminf (fun k => f k x) Filter.atTop
      ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) ≤
      Filter.liminf
        (fun k : ℕ =>
          ∫⁻ x : Ω, f k x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))))
        Filter.atTop := by
  simpa using MeasureTheory.lintegral_liminf_le (μ := MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ)))
    (f := f) hf

/-- A non-negative simple function on `Ω` vanishes outside `Ω`. -/
lemma isNonnegativeSimpleFunctionOn_eq_zero_outside {n : ℕ}
    {Ω : Set (Fin n → ℝ)} {s : (Fin n → ℝ) → ENNReal}
    (hs : IsNonnegativeSimpleFunctionOn Ω s) :
    ∀ x ∉ Ω, s x = 0 := by
  intro x hxΩ
  rcases hs with ⟨m, a, E, hE_meas, hE_sub, hs_repr⟩
  rw [hs_repr]
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hxE : x ∉ E k := by
    intro hxEk
    exact hxΩ (hE_sub k hxEk)
  simp [Set.indicator_of_notMem, hxE]

/-- An admissible non-negative simple minorant is bounded by the restricted integral of `f`. -/
lemma lintegral_le_of_isNonnegativeSimpleFunctionOn_minorized {n : ℕ}
    {Ω : Set (Fin n → ℝ)} {f s : (Fin n → ℝ) → ENNReal}
    (hs : IsNonnegativeSimpleFunctionOn Ω s)
    (hdom : ∀ x ∈ Ω, s x ≤ f x) :
    (∫⁻ x in Ω, s x ∂MeasureTheory.volume) ≤
      (∫⁻ x in Ω, f x ∂MeasureTheory.volume) := by
  refine MeasureTheory.lintegral_mono ?_
  intro x
  by_cases hx : x ∈ Ω
  · exact hdom x hx
  · have hsx : s x = 0 := isNonnegativeSimpleFunctionOn_eq_zero_outside hs x hx
    simpa [hsx] using (bot_le (f x))

/-- Restricting an `NNReal` simple function to measurable `t ⊆ Ω` yields an admissible
non-negative simple function on `Ω` after coercion to `ENNReal`. -/
lemma isNonnegativeSimpleFunctionOn_of_restricted_nnreal_simpleFunc {n : ℕ}
    {Ω t : Set (Fin n → ℝ)} (ht : MeasurableSet t) (htΩ : t ⊆ Ω)
    (φ : MeasureTheory.SimpleFunc (Fin n → ℝ) NNReal) :
    IsNonnegativeSimpleFunctionOn Ω
      (fun x => ((φ.restrict t).map ((↑) : NNReal → ENNReal)) x) := by
  classical
  let m : ℕ := φ.range.card
  let e : Fin m ≃ φ.range := (Finset.equivFin φ.range).symm
  refine ⟨m, (fun k => (e k).1), (fun k => t ∩ (φ ⁻¹' {(e k).1})), ?_, ?_, ?_⟩
  · intro k
    exact ht.inter (φ.measurableSet_preimage _)
  · intro k
    intro x hx
    exact htΩ hx.1
  · funext x
    by_cases hx : x ∈ t
    · have hsum_reindex :
          (∑ k : Fin m,
            ((e k).1 : ENNReal) *
              Set.indicator (t ∩ φ ⁻¹' {(e k).1}) (fun _ => (1 : ENNReal)) x) =
            ∑ r : φ.range,
              (r.1 : ENNReal) *
                Set.indicator (t ∩ φ ⁻¹' {r.1}) (fun _ => (1 : ENNReal)) x := by
          exact Fintype.sum_equiv e
            (fun k =>
              ((e k).1 : ENNReal) *
                Set.indicator (t ∩ φ ⁻¹' {(e k).1}) (fun _ => (1 : ENNReal)) x)
            (fun r =>
              (r.1 : ENNReal) *
                Set.indicator (t ∩ φ ⁻¹' {r.1}) (fun _ => (1 : ENNReal)) x)
            (by
              intro k
              rfl)
      have hsum_indicator :
          (∑ r : φ.range,
            (r.1 : ENNReal) *
              Set.indicator (t ∩ φ ⁻¹' {r.1}) (fun _ => (1 : ENNReal)) x) =
            ∑ r : φ.range, if φ x = r.1 then (r.1 : ENNReal) else 0 := by
          refine Fintype.sum_congr
            (fun r : φ.range =>
              (r.1 : ENNReal) *
                Set.indicator (t ∩ φ ⁻¹' {r.1}) (fun _ => (1 : ENNReal)) x)
            (fun r : φ.range => if φ x = r.1 then (r.1 : ENNReal) else 0) ?_
          intro r
          by_cases hxr : φ x = r.1
          · have hxmem : x ∈ t ∩ φ ⁻¹' {r.1} := by
              exact ⟨hx, by simpa [Set.mem_preimage] using hxr⟩
            simp [Set.indicator_of_mem, hxmem, hxr]
          · have hxnmem : x ∉ t ∩ φ ⁻¹' {r.1} := by
              intro hxint
              exact hxr (by simpa [Set.mem_preimage] using hxint.2)
            simp [Set.indicator_of_notMem, hxnmem, hxr]
      have hsum_single :
          (∑ r : φ.range, if φ x = r.1 then (r.1 : ENNReal) else 0) = (φ x : ENNReal) := by
        let r0 : φ.range := ⟨φ x, φ.mem_range_self x⟩
        calc
          (∑ r : φ.range, if φ x = r.1 then (r.1 : ENNReal) else 0)
              = if φ x = r0.1 then (r0.1 : ENNReal) else 0 := by
                  exact Fintype.sum_eq_single r0 (by
                    intro r hr
                    by_cases hxr : φ x = r.1
                    · exfalso
                      apply hr
                      apply Subtype.ext
                      simpa [r0] using hxr.symm
                    · simp [hxr])
          _ = (φ x : ENNReal) := by
                simp [r0]
      calc
        ((φ.restrict t).map ((↑) : NNReal → ENNReal)) x = (φ x : ENNReal) := by
          simp [MeasureTheory.SimpleFunc.map_apply, MeasureTheory.SimpleFunc.restrict_apply, ht, hx]
        _ = ∑ r : φ.range, if φ x = r.1 then (r.1 : ENNReal) else 0 := by
              symm
              exact hsum_single
        _ = ∑ r : φ.range,
              (r.1 : ENNReal) *
                Set.indicator (t ∩ φ ⁻¹' {r.1}) (fun _ => (1 : ENNReal)) x := by
              symm
              exact hsum_indicator
        _ = ∑ k : Fin m,
              ((e k).1 : ENNReal) *
                Set.indicator (t ∩ φ ⁻¹' {(e k).1}) (fun _ => (1 : ENNReal)) x := by
              symm
              exact hsum_reindex
    · calc
        ((φ.restrict t).map ((↑) : NNReal → ENNReal)) x = 0 := by
          simp [MeasureTheory.SimpleFunc.map_apply, MeasureTheory.SimpleFunc.restrict_apply, ht, hx]
        _ = ∑ k : Fin m,
              ((e k).1 : ENNReal) *
                Set.indicator (t ∩ φ ⁻¹' {(e k).1}) (fun _ => (1 : ENNReal)) x := by
              symm
              simp [hx]

/-- Under measurability assumptions on `Ω` and `f`, the restricted lintegral agrees with the
supremum over non-negative simple functions bounded by `f` on `Ω`. -/
theorem lebesgueIntegralNonneg_eq_iSup_simple {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ENNReal)
    (hΩ : MeasureTheory.NullMeasurableSet Ω MeasureTheory.volume)
    (hf : AEMeasurable f (MeasureTheory.volume.restrict Ω)) :
    lebesgueIntegralNonneg Ω f = lebesgueIntegralNonnegSup Ω f := by
  classical
  rcases hΩ.exists_measurable_subset_ae_eq with ⟨t, ht_sub, ht_meas, ht_ae⟩
  have hrestrict : MeasureTheory.volume.restrict Ω = MeasureTheory.volume.restrict t := by
    simpa using (MeasureTheory.Measure.restrict_congr_set (μ := MeasureTheory.volume) ht_ae.symm)
  have h_sup_le : lebesgueIntegralNonnegSup Ω f ≤ lebesgueIntegralNonneg Ω f := by
    unfold lebesgueIntegralNonnegSup lebesgueIntegralNonneg
    refine iSup_le ?_
    intro s
    refine iSup_le ?_
    intro hs
    refine iSup_le ?_
    intro hdom
    exact lintegral_le_of_isNonnegativeSimpleFunctionOn_minorized (Ω := Ω) (f := f) hs hdom
  have h_integral_le_sup : lebesgueIntegralNonneg Ω f ≤ lebesgueIntegralNonnegSup Ω f := by
    unfold lebesgueIntegralNonneg
    calc
      (∫⁻ x in Ω, f x ∂MeasureTheory.volume)
          = ⨆ (φ : MeasureTheory.SimpleFunc (Fin n → ℝ) NNReal)
              (_hφ : ∀ x, (φ x : ENNReal) ≤ f x),
              (φ.map ((↑) : NNReal → ENNReal)).lintegral (MeasureTheory.volume.restrict Ω) := by
                simpa using (MeasureTheory.lintegral_eq_nnreal f (MeasureTheory.volume.restrict Ω))
      _ ≤ lebesgueIntegralNonnegSup Ω f := by
        refine iSup_le ?_
        intro φ
        refine iSup_le ?_
        intro hφ
        let sfun : (Fin n → ℝ) → ENNReal :=
          fun x => ((φ.restrict t).map ((↑) : NNReal → ENNReal)) x
        have hs_simple : IsNonnegativeSimpleFunctionOn Ω sfun := by
          exact isNonnegativeSimpleFunctionOn_of_restricted_nnreal_simpleFunc
            (Ω := Ω) (t := t) ht_meas ht_sub φ
        have hs_dom : ∀ x ∈ Ω, sfun x ≤ f x := by
          intro x hxΩ
          by_cases hxt : x ∈ t
          · change ((φ.restrict t).map ((↑) : NNReal → ENNReal)) x ≤ f x
            calc
              ((φ.restrict t).map ((↑) : NNReal → ENNReal)) x = (φ x : ENNReal) := by
                simp [MeasureTheory.SimpleFunc.map_apply, MeasureTheory.SimpleFunc.restrict_apply,
                  ht_meas, hxt]
              _ ≤ f x := hφ x
          · change ((φ.restrict t).map ((↑) : NNReal → ENNReal)) x ≤ f x
            have hsx : ((φ.restrict t).map ((↑) : NNReal → ENNReal)) x = 0 := by
              simp [MeasureTheory.SimpleFunc.map_apply, MeasureTheory.SimpleFunc.restrict_apply,
                ht_meas, hxt]
            simpa [hsx] using (show (0 : ENNReal) ≤ f x from bot_le)
        have hs_restrict_self :
            (((φ.restrict t).map ((↑) : NNReal → ENNReal)).restrict t) =
              ((φ.restrict t).map ((↑) : NNReal → ENNReal)) := by
          ext x
          by_cases hxt : x ∈ t
          · simp [MeasureTheory.SimpleFunc.restrict_apply, ht_meas, hxt]
          · simp [MeasureTheory.SimpleFunc.restrict_apply, ht_meas, hxt]
        have hterm_eq :
            (φ.map ((↑) : NNReal → ENNReal)).lintegral (MeasureTheory.volume.restrict Ω) =
              ∫⁻ x in Ω, sfun x ∂MeasureTheory.volume := by
          have h_to_t :
              (φ.map ((↑) : NNReal → ENNReal)).lintegral (MeasureTheory.volume.restrict Ω) =
                (((φ.restrict t).map ((↑) : NNReal → ENNReal))).lintegral MeasureTheory.volume := by
            calc
              (φ.map ((↑) : NNReal → ENNReal)).lintegral (MeasureTheory.volume.restrict Ω)
                  = (φ.map ((↑) : NNReal → ENNReal)).lintegral (MeasureTheory.volume.restrict t) := by
                      rw [hrestrict]
              _ = ((φ.map ((↑) : NNReal → ENNReal)).restrict t).lintegral MeasureTheory.volume := by
                    symm
                    exact MeasureTheory.SimpleFunc.restrict_lintegral_eq_lintegral_restrict
                      (μ := MeasureTheory.volume) (φ.map ((↑) : NNReal → ENNReal)) ht_meas
              _ = (((φ.restrict t).map ((↑) : NNReal → ENNReal))).lintegral MeasureTheory.volume := by
                    rw [← MeasureTheory.SimpleFunc.map_coe_ennreal_restrict]
          have h_from_t :
              (((φ.restrict t).map ((↑) : NNReal → ENNReal))).lintegral MeasureTheory.volume =
                (((φ.restrict t).map ((↑) : NNReal → ENNReal))).lintegral
                  (MeasureTheory.volume.restrict Ω) := by
            calc
              (((φ.restrict t).map ((↑) : NNReal → ENNReal))).lintegral MeasureTheory.volume
                  = ((((φ.restrict t).map ((↑) : NNReal → ENNReal)).restrict t)).lintegral
                      MeasureTheory.volume := by
                        simpa [hs_restrict_self]
              _ = (((φ.restrict t).map ((↑) : NNReal → ENNReal))).lintegral
                    (MeasureTheory.volume.restrict t) := by
                      exact MeasureTheory.SimpleFunc.restrict_lintegral_eq_lintegral_restrict
                        (μ := MeasureTheory.volume)
                        (((φ.restrict t).map ((↑) : NNReal → ENNReal))) ht_meas
              _ = (((φ.restrict t).map ((↑) : NNReal → ENNReal))).lintegral
                    (MeasureTheory.volume.restrict Ω) := by
                      rw [← hrestrict]
          calc
            (φ.map ((↑) : NNReal → ENNReal)).lintegral (MeasureTheory.volume.restrict Ω)
                = (((φ.restrict t).map ((↑) : NNReal → ENNReal))).lintegral MeasureTheory.volume :=
                  h_to_t
            _ = (((φ.restrict t).map ((↑) : NNReal → ENNReal))).lintegral
                  (MeasureTheory.volume.restrict Ω) :=
                  h_from_t
            _ = ∫⁻ x in Ω, sfun x ∂MeasureTheory.volume := by
                  change (((φ.restrict t).map ((↑) : NNReal → ENNReal))).lintegral
                      (MeasureTheory.volume.restrict Ω) =
                    ∫⁻ x, sfun x ∂(MeasureTheory.volume.restrict Ω)
                  symm
                  exact MeasureTheory.SimpleFunc.lintegral_eq_lintegral
                    (((φ.restrict t).map ((↑) : NNReal → ENNReal)))
                    (MeasureTheory.volume.restrict Ω)
        exact le_iSup_of_le sfun (le_iSup_of_le hs_simple (le_iSup_of_le hs_dom (le_of_eq hterm_eq)))
  exact le_antisymm h_integral_le_sup h_sup_le

/-- Helper for Theorem 8.1: rewrite `lebesgueIntegralNonneg` as a subtype-domain integral. -/
lemma helperForTheorem_8_1_subtypeIntegral_repr {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : MeasurableSet Ω) (g : (Fin n → ℝ) → ENNReal) :
    lebesgueIntegralNonneg Ω g
      = ∫⁻ x : Ω, g x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) := by
  unfold lebesgueIntegralNonneg
  symm
  simpa using MeasureTheory.lintegral_subtype_comap
    (μ := MeasureTheory.volume) (s := Ω) hΩ g

/-- Helper for Theorem 8.1: pointwise monotonicity on `Ω` as monotonicity over the subtype. -/
lemma helperForTheorem_8_1_subtypePointwiseMonotone {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f : ℕ → (Fin n → ℝ) → ENNReal)
    (hmono : ∀ x ∈ Ω, Monotone (fun k => f k x)) :
    Monotone (fun k => fun x : Ω => f k x) := by
  intro i j hij x
  exact (hmono x.1 x.2) hij

/-- Helper for Theorem 8.1: monotonicity of subtype integrals for a pointwise monotone sequence. -/
lemma helperForTheorem_8_1_subtypeIntegral_monotone {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f : ℕ → (Fin n → ℝ) → ENNReal)
    (hmono : ∀ x ∈ Ω, Monotone (fun k => f k x)) :
    Monotone
      (fun k =>
        ∫⁻ x : Ω, f k x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ)))) := by
  intro i j hij
  exact MeasureTheory.lintegral_mono
    ((helperForTheorem_8_1_subtypePointwiseMonotone f hmono) hij)

/-- Helper for Theorem 8.1: subtype-domain monotone convergence identity. -/
lemma helperForTheorem_8_1_subtype_mct_identity {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f : ℕ → (Fin n → ℝ) → ENNReal)
    (hf_meas : ∀ n, Measurable (fun x : Ω => f n x))
    (hmono : ∀ x ∈ Ω, Monotone (fun k => f k x)) :
    ∫⁻ x : Ω, (⨆ k, f k x) ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) =
      ⨆ k, ∫⁻ x : Ω, f k x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) := by
  exact MeasureTheory.lintegral_iSup hf_meas
    (helperForTheorem_8_1_subtypePointwiseMonotone f hmono)

/-- Theorem 8.1 (Lebesgue monotone convergence theorem): if `Ω ⊆ ℝ^n` is measurable and
`f : ℕ → (Fin n → ℝ) → ENNReal` is pointwise monotone on `Ω` (so `f 0, f 1, ...` models
`f₁, f₂, ...`), then the restricted integrals are monotone and
`∫_Ω (⨆ n, f n) = ⨆ n, ∫_Ω f n`. -/
theorem lebesgue_monotone_convergence {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : MeasurableSet Ω) (f : ℕ → (Fin n → ℝ) → ENNReal)
    (hf_meas : ∀ n, Measurable (fun x : Ω => f n x))
    (hmono : ∀ x ∈ Ω, Monotone (fun n => f n x)) :
    (0 ≤ lebesgueIntegralNonneg Ω (f 0) ∧
      Monotone (fun n => lebesgueIntegralNonneg Ω (f n))) ∧
      lebesgueIntegralNonneg Ω (fun x => ⨆ n, f n x) =
        ⨆ n, lebesgueIntegralNonneg Ω (f n) := by
  have hnonneg : 0 ≤ lebesgueIntegralNonneg Ω (f 0) := by
    exact bot_le
  have hmonoSubtypeIntegral :
      Monotone
        (fun k =>
          ∫⁻ x : Ω, f k x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ)))) :=
    helperForTheorem_8_1_subtypeIntegral_monotone f hmono
  have hmonoIntegral : Monotone (fun n => lebesgueIntegralNonneg Ω (f n)) := by
    intro i j hij
    calc
      lebesgueIntegralNonneg Ω (f i)
          = ∫⁻ x : Ω, f i x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) :=
            helperForTheorem_8_1_subtypeIntegral_repr hΩ (f i)
      _ ≤ ∫⁻ x : Ω, f j x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) :=
            hmonoSubtypeIntegral hij
      _ = lebesgueIntegralNonneg Ω (f j) := by
            symm
            exact helperForTheorem_8_1_subtypeIntegral_repr hΩ (f j)
  have hMCTSubtype :
      ∫⁻ x : Ω, (⨆ k, f k x) ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) =
        ⨆ k, ∫⁻ x : Ω, f k x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) :=
    helperForTheorem_8_1_subtype_mct_identity f hf_meas hmono
  constructor
  · exact ⟨hnonneg, hmonoIntegral⟩
  · calc
      lebesgueIntegralNonneg Ω (fun x => ⨆ n, f n x)
          = ∫⁻ x : Ω, (⨆ k, f k x) ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) :=
            helperForTheorem_8_1_subtypeIntegral_repr hΩ (fun x => ⨆ n, f n x)
      _ = ⨆ k, ∫⁻ x : Ω, f k x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) :=
            hMCTSubtype
      _ = ⨆ n, lebesgueIntegralNonneg Ω (f n) := by
            refine iSup_congr ?_
            intro k
            symm
            exact helperForTheorem_8_1_subtypeIntegral_repr hΩ (f k)

/-- Helper for Theorem 8.2: each shifted term `x ↦ g (k + 1) x` is measurable. -/
lemma helperForTheorem_8_2_shiftedFamily_measurable
    {n : ℕ} {Ω : Set (Fin n → ℝ)} (g : ℕ → Ω → ENNReal)
    (hg : ∀ k : ℕ, Measurable (g (k + 1))) :
    ∀ k : ℕ, Measurable (fun x : Ω => g (k + 1) x) := by
  intro k
  simpa using hg k

/-- Helper for Theorem 8.2: the shifted pointwise series is measurable. -/
lemma helperForTheorem_8_2_tsum_measurable
    {n : ℕ} {Ω : Set (Fin n → ℝ)} (g : ℕ → Ω → ENNReal)
    (hg : ∀ k : ℕ, Measurable (g (k + 1))) :
    Measurable (fun x : Ω => ∑' k : ℕ, g (k + 1) x) := by
  exact Measurable.ennreal_tsum (helperForTheorem_8_2_shiftedFamily_measurable g hg)

/-- Helper for Theorem 8.2: each shifted term is a.e.-measurable for the subtype measure. -/
lemma helperForTheorem_8_2_shiftedFamily_aemeasurable
    {n : ℕ} {Ω : Set (Fin n → ℝ)} (g : ℕ → Ω → ENNReal)
    (hg : ∀ k : ℕ, Measurable (g (k + 1))) :
    ∀ k : ℕ,
      AEMeasurable (fun x : Ω => g (k + 1) x)
        (MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) := by
  intro k
  exact (helperForTheorem_8_2_shiftedFamily_measurable g hg k).aemeasurable

/-- Helper for Theorem 8.2: lintegral of the shifted series equals the series of lintegrals. -/
lemma helperForTheorem_8_2_lintegral_tsum
    {n : ℕ} {Ω : Set (Fin n → ℝ)} (g : ℕ → Ω → ENNReal)
    (hg : ∀ k : ℕ, Measurable (g (k + 1))) :
    (∫⁻ x : Ω, (∑' k : ℕ, g (k + 1) x)
        ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ)))) =
      ∑' k : ℕ, ∫⁻ x : Ω, g (k + 1) x
        ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) := by
  exact MeasureTheory.lintegral_tsum
    (helperForTheorem_8_2_shiftedFamily_aemeasurable g hg)

/-- Theorem 8.2: for a measurable set `Ω ⊆ ℝ^n` and measurable
`g_n : Ω → [0,∞]`, define `G(x) = ∑' n, g (n + 1) x` (series indexed by `n ≥ 1`).
Then `G` is measurable and integrating `G` over `Ω` equals the sum of the integrals
of the `g_n`, with values in `[0,∞]`. -/
theorem lintegral_tsum_subtype_eq_tsum_lintegral_subtype
    {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (g : ℕ → Ω → ENNReal) (hg : ∀ k : ℕ, Measurable (g (k + 1))) :
    Measurable (fun x : Ω => ∑' k : ℕ, g (k + 1) x) ∧
      (∫⁻ x : Ω, (∑' k : ℕ, g (k + 1) x)
          ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ)))) =
        ∑' k : ℕ, ∫⁻ x : Ω, g (k + 1) x
          ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) := by
  constructor
  · exact helperForTheorem_8_2_tsum_measurable g hg
  · exact helperForTheorem_8_2_lintegral_tsum g hg

/-- Proposition 8.4: for a measure space `(Ω, 𝓕, μ)` and a measurable function
`f : Ω → [0, +∞]`, if `∫⁻ ω, f ω ∂μ < +∞`, then `f ω < +∞` for `μ`-almost every `ω`. -/
theorem proposition_8_4_ae_lt_top_of_lintegral_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {f : Ω → ENNReal}
    (hf : Measurable f) (hfin : (∫⁻ ω, f ω ∂μ) < ⊤) :
    ∀ᵐ ω ∂μ, f ω < ⊤ := by
  simpa using MeasureTheory.ae_lt_top hf hfin.ne

/-- Lemma 8.7: if `Ω ⊆ ℝ^n` is measurable and `f : Ω → [0, +∞]` is measurable with
`∫_Ω f dx < +∞`, then `f x < +∞` for almost every `x ∈ Ω`
(equivalently, `|{x ∈ Ω : f x = +∞}| = 0`). -/
theorem lemma_8_7_ae_lt_top_on_measurable_set
    {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) {f : Ω → ENNReal}
    (hf : Measurable f)
    (hfin :
      (∫⁻ x : Ω, f x
        ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ)))) < ⊤) :
    ∀ᵐ x : Ω ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))), f x < ⊤ := by
  exact proposition_8_4_ae_lt_top_of_lintegral_lt_top
    (μ := MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) hf hfin

/-- Proposition 8.5: if `Ω ⊆ ℝ^n` is measurable and `f, g : Ω → [0,+∞]` are measurable,
then `∫ (f + g) ≥ ∫ f + ∫ g` over `Ω` (with respect to Lebesgue measure on the subtype). -/
theorem proposition_8_5_lintegral_add_ge
    {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    {f g : Ω → ENNReal} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x : Ω, (f x + g x) ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ))) ≥
      (∫⁻ x : Ω, f x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ)))) +
        (∫⁻ x : Ω, g x ∂(MeasureTheory.volume.comap ((↑) : Ω → (Fin n → ℝ)))) := by
  exact le_of_eq (lintegral_add_on_measurableSet_subtype hΩ hf hg).symm

/-- Lemma 8.8 (Borel--Cantelli): for measurable sets `Ω₁, Ω₂, ... ⊆ ℝ^n`, if
`∑' k, volume (Ω k) < ∞`, then the limsup set
`⋂ N, ⋃ k ≥ N, Ω k` has Lebesgue measure zero. -/
theorem lemma_8_8_borel_cantelli
    {n : ℕ} (Ω : ℕ → Set (Fin n → ℝ))
    (hmeas : ∀ k : ℕ, MeasurableSet (Ω k))
    (hsum : (∑' k : ℕ, MeasureTheory.volume (Ω k)) < ⊤) :
    MeasureTheory.volume (⋂ N : ℕ, ⋃ k ≥ N, Ω k) = 0 := by
  let _ := hmeas
  simpa [Filter.limsup_eq_iInf_iSup_of_nat] using
    (MeasureTheory.measure_limsup_atTop_eq_zero (μ := MeasureTheory.volume) (s := Ω) hsum.ne)

/-- Helper for Proposition 8.6: exact equality with a positive-denominator natural ratio gives a
rational real. -/
lemma helperForProposition_8_6_rational_of_exists_exact_ratio
    {x : ℝ}
    (h : ∃ aq : ℕ × ℕ, 0 < aq.2 ∧ x = (aq.1 : ℝ) / (aq.2 : ℝ)) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  rcases h with ⟨⟨a, q⟩, hq, rfl⟩
  refine ⟨(a : ℚ) / q, ?_⟩
  simp [Rat.cast_div]

/-- Helper for Proposition 8.6: for `x ∈ [0,1]`, admissible pairs with denominator bounded by `N`
form a finite set. -/
lemma helperForProposition_8_6_finite_pairs_if_denominator_bounded
    {p c x : ℝ} (hp : 2 < p) (hc : 0 < c) (hx01 : x ∈ Set.Icc (0 : ℝ) 1) {N : ℕ} :
    ({aq : ℕ × ℕ |
      0 < aq.1 ∧ 0 < aq.2 ∧ aq.2 ≤ N ∧
      |x - (aq.1 : ℝ) / (aq.2 : ℝ)| ≤ c / (aq.2 : ℝ) ^ p}).Finite := by
  let M : ℕ := Nat.ceil ((N : ℝ) * (1 + c))
  refine ((Set.finite_Icc (1 : ℕ) M).prod (Set.finite_Icc (1 : ℕ) N)).subset ?_
  intro aq haq
  rcases haq with ⟨ha_pos, hq_pos, hq_leN, hdist⟩
  refine ⟨?_, ?_⟩
  · refine ⟨Nat.succ_le_iff.2 ha_pos, ?_⟩
    have hqposR : (0 : ℝ) < (aq.2 : ℝ) := by exact_mod_cast hq_pos
    have hqge1R : (1 : ℝ) ≤ (aq.2 : ℝ) := by exact_mod_cast (Nat.succ_le_iff.2 hq_pos)
    have hp_nonneg : (0 : ℝ) ≤ p := by linarith
    have hqpow_ge1 : (1 : ℝ) ≤ (aq.2 : ℝ) ^ p := by
      simpa using Real.rpow_le_rpow_of_exponent_le hqge1R hp_nonneg
    have hqpow_pos : (0 : ℝ) < (aq.2 : ℝ) ^ p := by
      exact Real.rpow_pos_of_pos hqposR p
    have hc_le : c / (aq.2 : ℝ) ^ p ≤ c := by
      have hmul : c ≤ c * ((aq.2 : ℝ) ^ p) := by nlinarith [le_of_lt hc, hqpow_ge1]
      exact (div_le_iff₀ hqpow_pos).2 hmul
    have hsub : (aq.1 : ℝ) / (aq.2 : ℝ) - x ≤ |x - (aq.1 : ℝ) / (aq.2 : ℝ)| := by
      have htmp : -(x - (aq.1 : ℝ) / (aq.2 : ℝ)) ≤ |x - (aq.1 : ℝ) / (aq.2 : ℝ)| :=
        neg_le_abs (x - (aq.1 : ℝ) / (aq.2 : ℝ))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htmp
    have hratio_le : (aq.1 : ℝ) / (aq.2 : ℝ) ≤ 1 + c := by
      have hx_le1 : x ≤ 1 := hx01.2
      have h1 : (aq.1 : ℝ) / (aq.2 : ℝ) ≤ x + c / (aq.2 : ℝ) ^ p := by
        linarith
      have h2 : x + c / (aq.2 : ℝ) ^ p ≤ 1 + c := by
        nlinarith [hx_le1, hc_le]
      exact le_trans h1 h2
    have hmul_le : ((aq.1 : ℝ) / (aq.2 : ℝ)) * (aq.2 : ℝ) ≤ (1 + c) * (aq.2 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hratio_le hqposR.le
    have hqne : (aq.2 : ℝ) ≠ 0 := ne_of_gt hqposR
    have ha_le_q : (aq.1 : ℝ) ≤ (1 + c) * (aq.2 : ℝ) := by
      calc
        (aq.1 : ℝ) = ((aq.1 : ℝ) / (aq.2 : ℝ)) * (aq.2 : ℝ) := by field_simp [hqne]
        _ ≤ (1 + c) * (aq.2 : ℝ) := hmul_le
    have hq_leN_R : (aq.2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hq_leN
    have h1c_nonneg : (0 : ℝ) ≤ 1 + c := by linarith
    have hmul_qN : (1 + c) * (aq.2 : ℝ) ≤ (1 + c) * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hq_leN_R h1c_nonneg
    have ha_le_NR : (aq.1 : ℝ) ≤ (N : ℝ) * (1 + c) := by
      calc
        (aq.1 : ℝ) ≤ (1 + c) * (aq.2 : ℝ) := ha_le_q
        _ ≤ (1 + c) * (N : ℝ) := hmul_qN
        _ = (N : ℝ) * (1 + c) := by ring
    have ha_le_ceil : (aq.1 : ℝ) ≤ (Nat.ceil ((N : ℝ) * (1 + c)) : ℝ) :=
      le_trans ha_le_NR (Nat.le_ceil _)
    exact_mod_cast ha_le_ceil
  · exact ⟨Nat.succ_le_iff.2 hq_pos, hq_leN⟩

/-- Helper for Proposition 8.6: for nonrational `x ∈ [0,1]`, infinitely many admissible pairs
imply `LiouvilleWith p x`. -/
lemma helperForProposition_8_6_liouvilleWith_of_infinite_pairs_nonrational
    {p c x : ℝ} (hp : 2 < p) (hc : 0 < c) (hx01 : x ∈ Set.Icc (0 : ℝ) 1)
    (hx_nonrat : x ∉ Set.range ((↑) : ℚ → ℝ))
    (hInf : Set.Infinite
      {aq : ℕ × ℕ |
        0 < aq.1 ∧ 0 < aq.2 ∧ |x - (aq.1 : ℝ) / (aq.2 : ℝ)| ≤ c / (aq.2 : ℝ) ^ p}) :
    LiouvilleWith p x := by
  let S : Set (ℕ × ℕ) :=
    {aq : ℕ × ℕ |
      0 < aq.1 ∧ 0 < aq.2 ∧ |x - (aq.1 : ℝ) / (aq.2 : ℝ)| ≤ c / (aq.2 : ℝ) ^ p}
  have hSInf : S.Infinite := by
    simpa [S] using hInf
  let T : Set ℕ :=
    {q : ℕ | ∃ a : ℕ, 0 < a ∧ 0 < q ∧ |x - (a : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ p}
  have hTInf : T.Infinite := by
    by_contra hTFinite
    have hTF : T.Finite := Set.not_infinite.mp hTFinite
    rcases hTF.bddAbove with ⟨N, hN⟩
    have hSsubset : S ⊆
        {aq : ℕ × ℕ |
          0 < aq.1 ∧ 0 < aq.2 ∧ aq.2 ≤ N ∧
            |x - (aq.1 : ℝ) / (aq.2 : ℝ)| ≤ c / (aq.2 : ℝ) ^ p} := by
      intro aq haq
      rcases haq with ⟨ha_pos, hq_pos, hdist⟩
      have hq_mem_T : aq.2 ∈ T := by
        exact ⟨aq.1, ha_pos, hq_pos, hdist⟩
      exact ⟨ha_pos, hq_pos, hN hq_mem_T, hdist⟩
    have hSF : S.Finite :=
      (helperForProposition_8_6_finite_pairs_if_denominator_bounded
        (hp := hp) (hc := hc) (hx01 := hx01) (N := N)).subset hSsubset
    exact hSInf hSF
  refine ⟨c + 1, ?_⟩
  refine (Nat.frequently_atTop_iff_infinite.2 hTInf).mono ?_
  intro q hqT
  rcases hqT with ⟨a, ha_pos, hq_pos, hle⟩
  refine ⟨(a : ℤ), ?_, ?_⟩
  · intro hEq
    apply hx_nonrat
    refine helperForProposition_8_6_rational_of_exists_exact_ratio ?_
    refine ⟨(a, q), hq_pos, ?_⟩
    simpa using hEq
  · have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
    have hqpow_pos : (0 : ℝ) < (q : ℝ) ^ p := Real.rpow_pos_of_pos hqposR p
    have hltc : c < c + 1 := by linarith
    have hlt_div : c / (q : ℝ) ^ p < (c + 1) / (q : ℝ) ^ p := by
      exact div_lt_div_of_pos_right hltc hqpow_pos
    have hle' : |x - ((a : ℤ) : ℝ) / (q : ℝ)| ≤ c / (q : ℝ) ^ p := by
      simpa using hle
    exact lt_of_le_of_lt hle' hlt_div

/-- Helper for Proposition 8.6: the fixed-exponent Liouville set has measure zero when
`p > 2`. -/
lemma helperForProposition_8_6_volume_setOf_liouvilleWith_zero
    {p : ℝ} (hp : 2 < p) :
    MeasureTheory.volume {x : ℝ | LiouvilleWith p x} = 0 := by
  have hsubset : {x : ℝ | LiouvilleWith p x} ⊆
      ⋃ r : ℝ, ⋃ (_hr : 2 < r), {x : ℝ | LiouvilleWith r x} := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, hx⟩⟩
  exact MeasureTheory.measure_mono_null hsubset volume_iUnion_setOf_liouvilleWith

/-- Proposition 8.6: let `p > 2` and `c > 0`, and define
`E = {x ∈ [0,1] : |x - a / q| ≤ c / q^p for infinitely many positive integer pairs (a,q)}`.
Then `E` has Lebesgue measure zero. -/
theorem proposition_8_6_measure_zero_of_infinitely_many_rational_approximations
    {p c : ℝ} (hp : 2 < p) (hc : 0 < c) :
    MeasureTheory.volume
      {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
          Set.Infinite
            {aq : ℕ × ℕ |
              0 < aq.1 ∧ 0 < aq.2 ∧
                |x - (aq.1 : ℝ) / (aq.2 : ℝ)| ≤ c / (aq.2 : ℝ) ^ p}} = 0 := by
  let E : Set ℝ :=
    {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
        Set.Infinite
          {aq : ℕ × ℕ |
            0 < aq.1 ∧ 0 < aq.2 ∧
              |x - (aq.1 : ℝ) / (aq.2 : ℝ)| ≤ c / (aq.2 : ℝ) ^ p}}
  let R : Set ℝ := Set.range ((↑) : ℚ → ℝ)
  have hEsubset : E ⊆ R ∪ {x : ℝ | LiouvilleWith p x} := by
    intro x hxE
    rcases hxE with ⟨hx01, hInf⟩
    by_cases hxRat : x ∈ R
    · exact Or.inl hxRat
    · exact Or.inr
        (helperForProposition_8_6_liouvilleWith_of_infinite_pairs_nonrational
          (hp := hp) (hc := hc) (hx01 := hx01) (hx_nonrat := hxRat) (hInf := hInf))
  have hRnull : MeasureTheory.volume R = 0 := by
    exact Set.Countable.measure_zero (Set.countable_range ((↑) : ℚ → ℝ)) MeasureTheory.volume
  have hLnull : MeasureTheory.volume {x : ℝ | LiouvilleWith p x} = 0 := by
    exact helperForProposition_8_6_volume_setOf_liouvilleWith_zero (hp := hp)
  have hUnionNull : MeasureTheory.volume (R ∪ {x : ℝ | LiouvilleWith p x}) = 0 := by
    rw [MeasureTheory.measure_union_null hRnull hLnull]
  exact MeasureTheory.measure_mono_null hEsubset hUnionNull

/-- Helper for Theorem 8.3: `x` has a uniform Diophantine lower bound with exponent `τ`
over positive natural denominators. -/
def helperForTheorem_8_3_diophantineExponent (τ : ℝ) (x : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ p : ℤ, ∀ q : ℕ, 0 < q →
      |x - (p : ℝ) / (q : ℝ)| ≥ c / (q : ℝ) ^ τ

/-- Helper for Theorem 8.3: increasing the exponent preserves the Diophantine lower-bound
property. -/
lemma helperForTheorem_8_3_monotone_in_exponent
    {τ τ' x : ℝ} (hτ : τ ≤ τ') :
    helperForTheorem_8_3_diophantineExponent τ x →
      helperForTheorem_8_3_diophantineExponent τ' x := by
  intro hx
  rcases hx with ⟨c, hc, hbound⟩
  refine ⟨c, hc, ?_⟩
  intro p q hq
  have hqge1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.2 hq)
  have hqpow : (q : ℝ) ^ τ ≤ (q : ℝ) ^ τ' := by
    exact Real.rpow_le_rpow_of_exponent_le hqge1 hτ
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hqpow_pos : 0 < (q : ℝ) ^ τ := by
    exact Real.rpow_pos_of_pos hqpos τ
  have hdiv : c / (q : ℝ) ^ τ' ≤ c / (q : ℝ) ^ τ := by
    exact div_le_div_of_nonneg_left hc.le hqpow_pos hqpow
  calc
    |x - (p : ℝ) / (q : ℝ)| ≥ c / (q : ℝ) ^ τ := hbound p q hq
    _ ≥ c / (q : ℝ) ^ τ' := hdiv

/-- Helper for Theorem 8.3: adding a nonnegative increment to the exponent preserves the
Diophantine lower-bound property. -/
lemma helperForTheorem_8_3_monotone_in_exponent_add_nonneg
    {τ δ x : ℝ} (hδ : 0 ≤ δ) :
    helperForTheorem_8_3_diophantineExponent τ x →
      helperForTheorem_8_3_diophantineExponent (τ + δ) x := by
  intro hx
  have hle : τ ≤ τ + δ := by
    linarith
  exact helperForTheorem_8_3_monotone_in_exponent
    (τ := τ) (τ' := τ + δ) (x := x) hle hx

/-- Helper for Theorem 8.3: a Diophantine lower bound at exponent `τ` also gives one at
exponent `τ + 1`. -/
lemma helperForTheorem_8_3_diophantineExponent_succ
    {τ x : ℝ} :
    helperForTheorem_8_3_diophantineExponent τ x →
      helperForTheorem_8_3_diophantineExponent (τ + 1) x := by
  intro hx
  have hnonneg_one : (0 : ℝ) ≤ 1 := by
    norm_num
  exact helperForTheorem_8_3_monotone_in_exponent_add_nonneg
    (τ := τ) (δ := 1) (x := x) hnonneg_one hx

/-- Helper for Theorem 8.3: strict exponent increase preserves the Diophantine lower-bound
property. -/
lemma helperForTheorem_8_3_monotone_in_exponent_strict
    {τ τ' x : ℝ} (hτ : τ < τ') :
    helperForTheorem_8_3_diophantineExponent τ x →
      helperForTheorem_8_3_diophantineExponent τ' x := by
  intro hx
  exact helperForTheorem_8_3_monotone_in_exponent
    (τ := τ) (τ' := τ') (x := x) (le_of_lt hτ) hx

/-- Helper for Theorem 8.3: for natural denominators, the side condition `0 < q` is
equivalent to `q ≠ 0` in the Diophantine exponent formulation. -/
lemma helperForTheorem_8_3_diophantineExponent_iff_denominator_ne_zero
    {τ x : ℝ} :
    helperForTheorem_8_3_diophantineExponent τ x ↔
      ∃ c : ℝ, 0 < c ∧
        ∀ p : ℤ, ∀ q : ℕ, q ≠ 0 →
          |x - (p : ℝ) / (q : ℝ)| ≥ c / (q : ℝ) ^ τ := by
  constructor
  · intro hx
    rcases hx with ⟨c, hc, hbound⟩
    refine ⟨c, hc, ?_⟩
    intro p q hq
    exact hbound p q (Nat.pos_of_ne_zero hq)
  · intro hx
    rcases hx with ⟨c, hc, hbound⟩
    refine ⟨c, hc, ?_⟩
    intro p q hq
    exact hbound p q (Nat.ne_of_gt hq)

/-- Helper for Theorem 8.3: a non-strict Diophantine lower bound can be upgraded to a
strict lower bound by shrinking the constant. -/
lemma helperForTheorem_8_3_diophantineExponent_strict_of_non_strict
    {τ x : ℝ} :
    helperForTheorem_8_3_diophantineExponent τ x →
      ∃ c : ℝ, 0 < c ∧
        ∀ p : ℤ, ∀ q : ℕ, 0 < q →
          |x - (p : ℝ) / (q : ℝ)| > c / (q : ℝ) ^ τ := by
  intro hx
  rcases hx with ⟨c, hc, hbound⟩
  refine ⟨c / 2, by linarith, ?_⟩
  intro p q hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqpow_pos : (0 : ℝ) < (q : ℝ) ^ τ := Real.rpow_pos_of_pos hqpos τ
  have hhalf_lt : (c / 2) / (q : ℝ) ^ τ < c / (q : ℝ) ^ τ := by
    have hlt : c / 2 < c := by linarith
    exact div_lt_div_of_pos_right hlt hqpow_pos
  exact lt_of_lt_of_le hhalf_lt (hbound p q hq)

/-- Definition 8.7: a real number `x` is diophantine if there exist constants
`p > 0` and `C > 0` such that `|x - a/q| > C / |q|^p` for every nonzero integer
`q` and every integer `a`. -/
def IsDiophantineReal (x : ℝ) : Prop :=
  ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
    ∀ q : ℤ, q ≠ 0 → ∀ a : ℤ,
      |x - (a : ℝ) / (q : ℝ)| > C / (Int.natAbs q : ℝ) ^ p

/-- Helper for Theorem 8.3: strict integer-denominator Diophantine bounds imply the
corresponding non-strict bounds. -/
lemma helperForTheorem_8_3_exists_non_strict_parameters_of_IsDiophantineReal
    {x : ℝ} (hx : IsDiophantineReal x) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ q : ℤ, q ≠ 0 → ∀ a : ℤ,
        |x - (a : ℝ) / (q : ℝ)| ≥ C / (Int.natAbs q : ℝ) ^ p := by
  rcases hx with ⟨p, C, hp, hC, hbound⟩
  refine ⟨p, C, hp, hC, ?_⟩
  intro q hq a
  exact le_of_lt (hbound q hq a)

/-- Helper for Theorem 8.3: non-strict integer-denominator Diophantine bounds imply
`IsDiophantineReal` after shrinking the constant. -/
lemma helperForTheorem_8_3_isDiophantineReal_of_exists_non_strict_parameters
    {x : ℝ}
    (hx : ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ q : ℤ, q ≠ 0 → ∀ a : ℤ,
        |x - (a : ℝ) / (q : ℝ)| ≥ C / (Int.natAbs q : ℝ) ^ p) :
    IsDiophantineReal x := by
  rcases hx with ⟨p, C, hp, hC, hbound⟩
  have hC_half_pos : 0 < C / 2 := by
    linarith
  refine ⟨p, C / 2, hp, hC_half_pos, ?_⟩
  intro q hq a
  have hnatAbs_pos : 0 < Int.natAbs q := Int.natAbs_pos.2 hq
  have hnatAbs_real_pos : (0 : ℝ) < (Int.natAbs q : ℝ) := by
    exact_mod_cast hnatAbs_pos
  have hpow_pos : (0 : ℝ) < (Int.natAbs q : ℝ) ^ p := by
    exact Real.rpow_pos_of_pos hnatAbs_real_pos p
  have hhalf_lt :
      (C / 2) / (Int.natAbs q : ℝ) ^ p < C / (Int.natAbs q : ℝ) ^ p := by
    have hC_half_lt : C / 2 < C := by
      linarith
    exact div_lt_div_of_pos_right hC_half_lt hpow_pos
  exact lt_of_lt_of_le hhalf_lt (hbound q hq a)

/-- Helper for Theorem 8.3: `IsDiophantineReal` is equivalent to the existence of
positive-parameter non-strict integer-denominator Diophantine bounds. -/
lemma helperForTheorem_8_3_isDiophantineReal_iff_exists_non_strict_parameters
    {x : ℝ} :
    IsDiophantineReal x ↔
      ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
        ∀ q : ℤ, q ≠ 0 → ∀ a : ℤ,
          |x - (a : ℝ) / (q : ℝ)| ≥ C / (Int.natAbs q : ℝ) ^ p := by
  constructor
  · intro hx
    exact helperForTheorem_8_3_exists_non_strict_parameters_of_IsDiophantineReal hx
  · intro hx
    exact helperForTheorem_8_3_isDiophantineReal_of_exists_non_strict_parameters hx

/-- Helper for Theorem 8.3: rewrite an integer-denominator rational into a
positive-denominator one using `Int.sign` and `Int.natAbs`. -/
lemma helperForTheorem_8_3_signed_numerator_div_natAbs_eq_div_int
    (a q : ℤ) (hq : q ≠ 0) :
    ((a * Int.sign q : ℤ) : ℝ) / (Int.natAbs q : ℝ) = (a : ℝ) / (q : ℝ) := by
  rcases lt_or_gt_of_ne hq with hqneg | hqpos
  · have hsign : Int.sign q = -1 := Int.sign_eq_neg_one_of_neg hqneg
    have hqreal_neg : (q : ℝ) < 0 := by
      exact_mod_cast hqneg
    have habs : |(q : ℝ)| = -(q : ℝ) := by
      simp [abs_of_neg hqreal_neg]
    have hnatAbs : (Int.natAbs q : ℝ) = -(q : ℝ) := by
      simpa [habs] using (Nat.cast_natAbs (α := ℝ) q)
    calc
      ((a * Int.sign q : ℤ) : ℝ) / (Int.natAbs q : ℝ)
          = (-(a : ℝ)) / (-(q : ℝ)) := by
              simp [hsign, hnatAbs]
      _ = (a : ℝ) / (q : ℝ) := by simp
  · have hsign : Int.sign q = 1 := Int.sign_eq_one_of_pos hqpos
    have hqreal_pos : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast hqpos
    have habs : |(q : ℝ)| = (q : ℝ) := by
      simp [abs_of_pos hqreal_pos]
    have hnatAbs : (Int.natAbs q : ℝ) = (q : ℝ) := by
      simpa [habs] using (Nat.cast_natAbs (α := ℝ) q)
    simp [hsign, hnatAbs]

/-- Helper for Theorem 8.3: an `IsDiophantineReal` number satisfies the
natural-denominator Diophantine lower-bound formulation at some positive exponent. -/
lemma helperForTheorem_8_3_exists_exponent_with_diophantineExponent_of_IsDiophantineReal
    {x : ℝ} (hx : IsDiophantineReal x) :
    ∃ τ : ℝ, 0 < τ ∧ helperForTheorem_8_3_diophantineExponent τ x := by
  rcases hx with ⟨τ, C, hτ_pos, hC_pos, hbound⟩
  refine ⟨τ, hτ_pos, ?_⟩
  refine ⟨C, hC_pos, ?_⟩
  intro p q hq_pos
  have hq_int_ne : (q : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq_pos)
  have hbound_int :
      |x - (p : ℝ) / ((q : ℤ) : ℝ)| > C / ((Int.natAbs (q : ℤ) : ℕ) : ℝ) ^ τ := by
    simpa using hbound (q : ℤ) hq_int_ne p
  have hbound_nat : |x - (p : ℝ) / (q : ℝ)| > C / (q : ℝ) ^ τ := by
    simpa [Int.natAbs_natCast] using hbound_int
  exact le_of_lt hbound_nat

/-- Helper for Theorem 8.3: a positive-exponent natural-denominator Diophantine
lower bound implies `IsDiophantineReal`. -/
lemma helperForTheorem_8_3_isDiophantineReal_of_diophantineExponent
    {x τ : ℝ} (hτ : 0 < τ)
    (hx : helperForTheorem_8_3_diophantineExponent τ x) :
    IsDiophantineReal x := by
  rcases helperForTheorem_8_3_diophantineExponent_strict_of_non_strict
      (τ := τ) (x := x) hx with ⟨C, hC_pos, hstrict⟩
  refine ⟨τ, C, hτ, hC_pos, ?_⟩
  intro q hq a
  have hnatAbs_pos : 0 < Int.natAbs q := Int.natAbs_pos.2 hq
  have hstrict_natAbs :
      |x - ((a * Int.sign q : ℤ) : ℝ) / (Int.natAbs q : ℝ)| >
        C / (Int.natAbs q : ℝ) ^ τ := by
    exact hstrict (a * Int.sign q) (Int.natAbs q) hnatAbs_pos
  have hrewrite :
      ((a * Int.sign q : ℤ) : ℝ) / (Int.natAbs q : ℝ) = (a : ℝ) / (q : ℝ) := by
    exact helperForTheorem_8_3_signed_numerator_div_natAbs_eq_div_int a q hq
  rw [← hrewrite]
  exact hstrict_natAbs

/-- Helper for Theorem 8.3: a natural-denominator Diophantine lower bound at an exponent
strictly greater than `1` implies `IsDiophantineReal`. -/
lemma helperForTheorem_8_3_isDiophantineReal_of_diophantineExponent_gt_one
    {x τ : ℝ} (hτ : 1 < τ)
    (hx : helperForTheorem_8_3_diophantineExponent τ x) :
    IsDiophantineReal x := by
  have hτ_pos : 0 < τ := by
    linarith
  exact helperForTheorem_8_3_isDiophantineReal_of_diophantineExponent hτ_pos hx

/-- Helper for Theorem 8.3: the integer-denominator and positive-natural-denominator
Diophantine formulations are equivalent. -/
lemma helperForTheorem_8_3_isDiophantineReal_iff_exists_positive_exponent
    {x : ℝ} :
    IsDiophantineReal x ↔
      ∃ τ : ℝ, 0 < τ ∧ helperForTheorem_8_3_diophantineExponent τ x := by
  constructor
  · intro hx
    exact helperForTheorem_8_3_exists_exponent_with_diophantineExponent_of_IsDiophantineReal hx
  · intro hx
    rcases hx with ⟨τ, hτ, hbound⟩
    exact helperForTheorem_8_3_isDiophantineReal_of_diophantineExponent hτ hbound

/-- Helper for Theorem 8.3: any `IsDiophantineReal` number admits a
natural-denominator Diophantine lower bound at some exponent strictly greater
than `1`. -/
lemma helperForTheorem_8_3_exists_exponent_gt_one_of_IsDiophantineReal
    {x : ℝ} (hx : IsDiophantineReal x) :
    ∃ τ : ℝ, 1 < τ ∧ helperForTheorem_8_3_diophantineExponent τ x := by
  rcases helperForTheorem_8_3_exists_exponent_with_diophantineExponent_of_IsDiophantineReal hx with
    ⟨τ, hτ_pos, hτ_bound⟩
  refine ⟨τ + 1, ?_, ?_⟩
  · linarith
  · exact helperForTheorem_8_3_diophantineExponent_succ (τ := τ) (x := x) hτ_bound

/-- Helper for Theorem 8.3: existence of a strict-`> 1` natural-denominator
Diophantine lower bound implies `IsDiophantineReal`. -/
lemma helperForTheorem_8_3_isDiophantineReal_of_exists_exponent_gt_one
    {x : ℝ}
    (hx : ∃ τ : ℝ, 1 < τ ∧ helperForTheorem_8_3_diophantineExponent τ x) :
    IsDiophantineReal x := by
  rcases hx with ⟨τ, hτ_one, hτ_bound⟩
  exact helperForTheorem_8_3_isDiophantineReal_of_diophantineExponent_gt_one hτ_one hτ_bound

/-- Helper for Theorem 8.3: `IsDiophantineReal` is equivalent to existence of a
natural-denominator Diophantine lower bound at an exponent `> 1`. -/
lemma helperForTheorem_8_3_isDiophantineReal_iff_exists_exponent_gt_one
    {x : ℝ} :
    IsDiophantineReal x ↔
      ∃ τ : ℝ, 1 < τ ∧ helperForTheorem_8_3_diophantineExponent τ x := by
  constructor
  · intro hx
    exact helperForTheorem_8_3_exists_exponent_gt_one_of_IsDiophantineReal hx
  · intro hx
    exact helperForTheorem_8_3_isDiophantineReal_of_exists_exponent_gt_one hx

/-- Helper for Theorem 8.3: if `IsDiophantineReal` holds almost everywhere, then
almost every point admits an exponent `τ > 1` with a natural-denominator
Diophantine lower bound. -/
lemma helperForTheorem_8_3_ae_exists_exponent_gt_one_of_ae_isDiophantineReal
    (hae : ∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x) :
    ∀ᵐ x : ℝ ∂MeasureTheory.volume,
      ∃ τ : ℝ, 1 < τ ∧ helperForTheorem_8_3_diophantineExponent τ x := by
  filter_upwards [hae] with x hx
  exact (helperForTheorem_8_3_isDiophantineReal_iff_exists_exponent_gt_one (x := x)).1 hx

/-- Helper for Theorem 8.3: if almost every point admits an exponent `τ > 1` with a
natural-denominator Diophantine lower bound, then `IsDiophantineReal` holds
almost everywhere. -/
lemma helperForTheorem_8_3_ae_isDiophantineReal_of_ae_exists_exponent_gt_one
    (hae : ∀ᵐ x : ℝ ∂MeasureTheory.volume,
      ∃ τ : ℝ, 1 < τ ∧ helperForTheorem_8_3_diophantineExponent τ x) :
    ∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x := by
  filter_upwards [hae] with x hx
  exact (helperForTheorem_8_3_isDiophantineReal_iff_exists_exponent_gt_one (x := x)).2 hx

/-- Helper for Theorem 8.3: almost-everywhere `IsDiophantineReal` is equivalent to
almost-everywhere existence of an exponent `τ > 1` with the natural-denominator
Diophantine lower bound. -/
lemma helperForTheorem_8_3_ae_isDiophantineReal_iff_ae_exists_exponent_gt_one
    : (∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x) ↔
        (∀ᵐ x : ℝ ∂MeasureTheory.volume,
          ∃ τ : ℝ, 1 < τ ∧ helperForTheorem_8_3_diophantineExponent τ x) := by
  constructor
  · intro hae
    exact helperForTheorem_8_3_ae_exists_exponent_gt_one_of_ae_isDiophantineReal hae
  · intro hae
    exact helperForTheorem_8_3_ae_isDiophantineReal_of_ae_exists_exponent_gt_one hae

/-- Helper for Theorem 8.3: `IsDiophantineReal` is equivalent to the existence of an
exponent `τ > 1` and a constant `c > 0` giving the natural-denominator lower bound. -/
lemma helperForTheorem_8_3_isDiophantineReal_iff_exists_exponent_gt_one_and_constant
    {x : ℝ} :
    IsDiophantineReal x ↔
      ∃ τ c : ℝ, 1 < τ ∧ 0 < c ∧
        ∀ p : ℤ, ∀ q : ℕ, 0 < q →
          |x - (p : ℝ) / (q : ℝ)| ≥ c / (q : ℝ) ^ τ := by
  constructor
  · intro hx
    rcases helperForTheorem_8_3_exists_exponent_gt_one_of_IsDiophantineReal hx with
      ⟨τ, hτ, hτbound⟩
    rcases hτbound with ⟨c, hc, hbound⟩
    exact ⟨τ, c, hτ, hc, hbound⟩
  · intro hx
    rcases hx with ⟨τ, c, hτ, hc, hbound⟩
    have hτbound : helperForTheorem_8_3_diophantineExponent τ x := by
      exact ⟨c, hc, hbound⟩
    exact helperForTheorem_8_3_isDiophantineReal_of_diophantineExponent_gt_one hτ hτbound

/-- Helper for Theorem 8.3: `IsDiophantineReal` is equivalent to an exponent `τ > 1` and
a constant `c > 0` with the lower bound quantified over all nonzero natural denominators. -/
lemma helperForTheorem_8_3_isDiophantineReal_iff_exists_exponent_gt_one_and_constant_ne_zero
    {x : ℝ} :
    IsDiophantineReal x ↔
      ∃ τ c : ℝ, 1 < τ ∧ 0 < c ∧
        ∀ p : ℤ, ∀ q : ℕ, q ≠ 0 →
          |x - (p : ℝ) / (q : ℝ)| ≥ c / (q : ℝ) ^ τ := by
  constructor
  · intro hx
    rcases helperForTheorem_8_3_exists_exponent_gt_one_of_IsDiophantineReal hx with
      ⟨τ, hτ, hτbound⟩
    rcases helperForTheorem_8_3_diophantineExponent_iff_denominator_ne_zero.mp hτbound with
      ⟨c, hc, hbound⟩
    exact ⟨τ, c, hτ, hc, hbound⟩
  · intro hx
    rcases hx with ⟨τ, c, hτ, hc, hbound⟩
    have hτbound : helperForTheorem_8_3_diophantineExponent τ x := by
      exact helperForTheorem_8_3_diophantineExponent_iff_denominator_ne_zero.mpr
        ⟨c, hc, hbound⟩
    exact helperForTheorem_8_3_isDiophantineReal_of_diophantineExponent_gt_one hτ hτbound

/-- Helper for Theorem 8.3: for Lebesgue measure on `ℝ`, an almost-everywhere
Diophantine lower bound is equivalent to the complement having measure zero. -/
lemma helperForTheorem_8_3_ae_iff_volume_complement_zero
    {τ : ℝ} :
    (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x) ↔
      MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 := by
  simpa [MeasureTheory.ae_iff]

/-- Helper for Theorem 8.3: measure-zero complement implies the almost-everywhere
Diophantine lower bound formulation. -/
lemma helperForTheorem_8_3_ae_of_volume_complement_zero
    {τ : ℝ}
    (hnull : MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0) :
    ∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x := by
  exact (helperForTheorem_8_3_ae_iff_volume_complement_zero (τ := τ)).2 hnull

/-- Helper for Theorem 8.3: an almost-everywhere fixed-exponent Diophantine lower
bound implies the complement has Lebesgue measure zero. -/
lemma helperForTheorem_8_3_volume_complement_zero_of_ae
    {τ : ℝ}
    (hae : ∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x) :
    MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 := by
  exact (helperForTheorem_8_3_ae_iff_volume_complement_zero (τ := τ)).1 hae

/-- Helper for Theorem 8.3: a null complement yields both the null-complement and
almost-everywhere formulations in one conjunction. -/
lemma helperForTheorem_8_3_full_measure_pair_of_volume_complement_zero
    {τ : ℝ}
    (hnull : MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0) :
    MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x) := by
  refine ⟨hnull, ?_⟩
  exact helperForTheorem_8_3_ae_of_volume_complement_zero (τ := τ) hnull

/-- Helper for Theorem 8.3: proving the full-measure pair is equivalent to proving
just the null-complement statement. -/
lemma helperForTheorem_8_3_full_measure_pair_iff_volume_complement_zero
    {τ : ℝ} :
    (MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) ↔
      MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 := by
  constructor
  · intro hpair
    exact hpair.1
  · intro hnull
    exact helperForTheorem_8_3_full_measure_pair_of_volume_complement_zero (τ := τ) hnull


end Section02
end Chap08
