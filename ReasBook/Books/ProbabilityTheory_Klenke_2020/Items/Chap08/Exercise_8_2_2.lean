/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Remark_8_16

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal MeasureTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/- Part (1) is a `source-facing` interval statement for the canonical owner `condExp`. Part (2)
uses the chapter's signed bridge `lowerCondExp`; the underlying nonnegative `condLExp`
counterexample is kept only as private support. -/

section FiniteMeasure

variable {P : Measure[mΩ] Ω} [IsFiniteMeasure P]

/-- Helper for Exercise 8.2.2: conditional expectation stays almost surely inside a closed convex
real set that already contains `X` almost surely. -/
private lemma condExp_mem_closedConvex_ae {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) {J : Set ℝ}
    (hJ_closed : IsClosed J) (hJ_convex : Convex ℝ J) {X : Ω → ℝ} (hX : Integrable X P)
    (hXJ : ∀ᵐ ω ∂P, X ω ∈ J) :
    ∀ᵐ ω ∂P, P[X | ℱ] ω ∈ J := by
  -- Use the closed-convex owner theorem directly once the interval case has been normalized.
  exact hJ_convex.condExp_mem hℱ hX hJ_closed hXJ

/-- Helper for Exercise 8.2.2: if `X` stays strictly above `c` almost surely, then its
conditional expectation cannot equal `c` on a set of positive measure. -/
private lemma condExp_ne_const_of_ae_gt {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) {X : Ω → ℝ}
    (hX : Integrable X P) {c : ℝ} (hcX : ∀ᵐ ω ∂P, c < X ω) :
    ∀ᵐ ω ∂P, P[X | ℱ] ω ≠ c := by
  let A : Set Ω := {ω | P[X | ℱ] ω = c}
  have hAℱ : @MeasurableSet Ω ℱ A := by
    -- The equality event is `ℱ`-measurable because conditional expectation is `ℱ`-measurable.
    simpa [A] using
      measurableSet_eq_fun (stronglyMeasurable_condExp (μ := P) (m := ℱ) (f := X)).measurable
        measurable_const
  have hA : @MeasurableSet Ω mΩ A := hℱ A hAℱ
  have hsub_pos : ∀ᵐ ω ∂P.restrict A, 0 < X ω - c := by
    -- Restrict the strict lower bound to the equality event.
    exact (ae_restrict_iff' hA).2 <|
      hcX.mono fun ω hω hωA ↦ by
        linarith
  have hsub_nonneg : 0 ≤ᵐ[ P.restrict A] fun ω ↦ X ω - c :=
    hsub_pos.mono fun ω hω ↦ le_of_lt hω
  have hsub_int : IntegrableOn (fun ω ↦ X ω - c) A P :=
    (hX.sub (integrable_const c)).integrableOn
  have hcond_zero : ∀ᵐ ω ∂P.restrict A, P[(fun ω ↦ X ω - c) | ℱ] ω = 0 := by
    -- On `A`, the conditional expectation of `X - c` vanishes because `P[X | ℱ] = c`.
    exact (ae_restrict_iff' hA).2 <|
      (condExp_sub hX (integrable_const c) ℱ).mono fun ω hω hωA ↦ by
        rw [condExp_const hℱ c] at hω
        change P[X | ℱ] ω = c at hωA
        simpa [hωA] using hω
  have hset_zero : ∫ ω in A, (X ω - c) ∂P = 0 := by
    -- The restricted integral agrees with the conditional expectation,
    -- and the latter is zero on `A`.
    calc
      ∫ ω in A, (X ω - c) ∂P = ∫ ω in A, P[(fun ω ↦ X ω - c) | ℱ] ω ∂P := by
        symm
        exact setIntegral_condExp hℱ (hX.sub (integrable_const c)) hAℱ
      _ = ∫ ω, 0 ∂P.restrict A := by
        exact integral_congr_ae hcond_zero
      _ = 0 := by simp
  have hsub_zero : (fun ω ↦ X ω - c) =ᵐ[P.restrict A] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae hsub_nonneg hsub_int).1 hset_zero
  have hfalse : ∀ᵐ ω ∂P.restrict A, False := by
    -- A point in `A` would force `X ω - c` to be both positive and zero.
    filter_upwards [hsub_pos, hsub_zero] with ω hωpos hωzero
    have : (0 : ℝ) < 0 := by
      simp [hωzero] at hωpos
    exact (lt_irrefl (0 : ℝ)) this
  have hnotA : ∀ᵐ ω ∂P, ω ∉ A := by
    have hnotA' : ∀ᵐ ω ∂P, ω ∈ A → False := (ae_restrict_iff' hA).1 hfalse
    simpa using hnotA'
  simpa [A] using hnotA

/-- Helper for Exercise 8.2.2: if `X` stays strictly below `c` almost surely, then its
conditional expectation cannot equal `c` on a set of positive measure. -/
private lemma condExp_ne_const_of_ae_lt {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) {X : Ω → ℝ}
    (hX : Integrable X P) {c : ℝ} (hXc : ∀ᵐ ω ∂P, X ω < c) :
    ∀ᵐ ω ∂P, P[X | ℱ] ω ≠ c := by
  have hneg : ∀ᵐ ω ∂P, -c < -X ω := by
    -- Negating swaps a strict upper bound into a strict lower bound.
    filter_upwards [hXc] with ω hω
    linarith
  have hne_neg : ∀ᵐ ω ∂P, P[-X | ℱ] ω ≠ -c :=
    condExp_ne_const_of_ae_gt (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ) hℱ hX.neg hneg
  -- Translate the exclusion statement back through `condExp_neg`.
  filter_upwards [condExp_neg (μ := P) (m := ℱ) X, hne_neg] with ω hω hωne hωeq
  apply hωne
  simpa [hωeq] using hω

-- Proof sketch: write an interval in `ℝ` as an order-convex set, then prove separately that
-- conditional expectation preserves almost-sure lower and upper bounds by combining
-- `condExp_mono` with `condExp_const`. Intersect the two half-line bounds to recover membership
-- in the whole interval.
/-- Exercise 8.2.2 (1): If an integrable real-valued random variable `X` takes values almost surely
in an interval `I ⊆ ℝ`, then its conditional expectation with respect to `ℱ` also takes values
almost surely in `I`. The canonical owner is `condExp`, and the finite-measure hypothesis is the
minimal ambient assumption needed by the upstream conditional-expectation API used here. -/
theorem condExp_mem_interval_ae {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) {I : Set ℝ}
    (hI : Set.OrdConnected I) {X : Ω → ℝ} (hX : Integrable X P)
    (hXI : ∀ᵐ ω ∂P, X ω ∈ I) :
    ∀ᵐ ω ∂P, P[X | ℱ] ω ∈ I := by
  -- Route correction: instead of rebuilding interval preservation from monotonicity alone,
  -- normalize `I` to a standard interval shape and use the closed-convex owner theorem first.
  rcases hI.isPreconnected.mem_intervals with hI | hI | hI | hI | hI | hI | hI | hI | hI | hI
  · -- Closed bounded intervals are handled directly by the closed-convex lemma.
    rw [hI] at hXI ⊢
    exact condExp_mem_closedConvex_ae (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ)
      hℱ isClosed_Icc (convex_Icc _ _) hX hXI
  · -- For `[a, b)`, first stay inside `[a, b]`, then exclude the open upper endpoint.
    rw [hI] at hXI ⊢
    have hclosed : ∀ᵐ ω ∂P, P[X | ℱ] ω ∈ Set.Icc (sInf I) (sSup I) :=
      condExp_mem_closedConvex_ae (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ)
        hℱ isClosed_Icc (convex_Icc _ _) hX <|
        hXI.mono fun ω hω ↦ ⟨hω.1, le_of_lt hω.2⟩
    have hlt : ∀ᵐ ω ∂P, X ω < sSup I := hXI.mono fun ω hω ↦ hω.2
    have hne : ∀ᵐ ω ∂P, P[X | ℱ] ω ≠ sSup I :=
      condExp_ne_const_of_ae_lt (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ) hℱ hX hlt
    filter_upwards [hclosed, hne] with ω hω_closed hω_ne
    exact ⟨hω_closed.1, lt_of_le_of_ne hω_closed.2 fun hEq ↦ hω_ne hEq⟩
  · -- For `(a, b]`, use `[a, b]` as the closed hull and exclude the lower endpoint.
    rw [hI] at hXI ⊢
    have hclosed : ∀ᵐ ω ∂P, P[X | ℱ] ω ∈ Set.Icc (sInf I) (sSup I) :=
      condExp_mem_closedConvex_ae (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ)
        hℱ isClosed_Icc (convex_Icc _ _) hX <|
        hXI.mono fun ω hω ↦ ⟨le_of_lt hω.1, hω.2⟩
    have hgt : ∀ᵐ ω ∂P, sInf I < X ω := hXI.mono fun ω hω ↦ hω.1
    have hne : ∀ᵐ ω ∂P, P[X | ℱ] ω ≠ sInf I :=
      condExp_ne_const_of_ae_gt (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ) hℱ hX hgt
    filter_upwards [hclosed, hne] with ω hω_closed hω_ne
    exact ⟨lt_of_le_of_ne hω_closed.1 fun hEq ↦ hω_ne hEq.symm, hω_closed.2⟩
  · -- For `(a, b)`, use `[a, b]` as the closed hull and exclude both endpoints.
    rw [hI] at hXI ⊢
    have hclosed : ∀ᵐ ω ∂P, P[X | ℱ] ω ∈ Set.Icc (sInf I) (sSup I) :=
      condExp_mem_closedConvex_ae (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ)
        hℱ isClosed_Icc (convex_Icc _ _) hX <|
        hXI.mono fun ω hω ↦ ⟨le_of_lt hω.1, le_of_lt hω.2⟩
    have hgt : ∀ᵐ ω ∂P, sInf I < X ω := hXI.mono fun ω hω ↦ hω.1
    have hlt : ∀ᵐ ω ∂P, X ω < sSup I := hXI.mono fun ω hω ↦ hω.2
    have hne_low : ∀ᵐ ω ∂P, P[X | ℱ] ω ≠ sInf I :=
      condExp_ne_const_of_ae_gt (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ) hℱ hX hgt
    have hne_high : ∀ᵐ ω ∂P, P[X | ℱ] ω ≠ sSup I :=
      condExp_ne_const_of_ae_lt (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ) hℱ hX hlt
    filter_upwards [hclosed, hne_low, hne_high] with ω hω_closed hω_low hω_high
    exact ⟨lt_of_le_of_ne hω_closed.1 fun hEq ↦ hω_low hEq.symm,
      lt_of_le_of_ne hω_closed.2 fun hEq ↦ hω_high hEq⟩
  · -- Closed upper rays are already closed and convex.
    rw [hI] at hXI ⊢
    exact condExp_mem_closedConvex_ae (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ)
      hℱ isClosed_Ici (convex_Ici _) hX hXI
  · -- For open upper rays, use the closed hull `Ici` and exclude the lower endpoint.
    rw [hI] at hXI ⊢
    have hclosed : ∀ᵐ ω ∂P, P[X | ℱ] ω ∈ Set.Ici (sInf I) :=
      condExp_mem_closedConvex_ae (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ)
        hℱ isClosed_Ici (convex_Ici _) hX <|
        hXI.mono fun ω hω ↦ by simpa using le_of_lt hω
    have hgt : ∀ᵐ ω ∂P, sInf I < X ω := hXI
    have hne : ∀ᵐ ω ∂P, P[X | ℱ] ω ≠ sInf I :=
      condExp_ne_const_of_ae_gt (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ) hℱ hX hgt
    filter_upwards [hclosed, hne] with ω hω_closed hω_ne
    exact lt_of_le_of_ne hω_closed fun hEq ↦ hω_ne hEq.symm
  · -- Closed lower rays are also direct applications of the closed-convex lemma.
    rw [hI] at hXI ⊢
    exact condExp_mem_closedConvex_ae (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ)
      hℱ isClosed_Iic (convex_Iic _) hX hXI
  · -- For open lower rays, use the closed hull `Iic` and exclude the upper endpoint.
    rw [hI] at hXI ⊢
    have hclosed : ∀ᵐ ω ∂P, P[X | ℱ] ω ∈ Set.Iic (sSup I) :=
      condExp_mem_closedConvex_ae (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ)
        hℱ isClosed_Iic (convex_Iic _) hX <|
        hXI.mono fun ω hω ↦ by simpa using le_of_lt hω
    have hlt : ∀ᵐ ω ∂P, X ω < sSup I := hXI
    have hne : ∀ᵐ ω ∂P, P[X | ℱ] ω ≠ sSup I :=
      condExp_ne_const_of_ae_lt (Ω := Ω) (mΩ := mΩ) (P := P) (ℱ := ℱ) hℱ hX hlt
    filter_upwards [hclosed, hne] with ω hω_closed hω_ne
    exact lt_of_le_of_ne hω_closed fun hEq ↦ hω_ne hEq
  · -- The whole line needs no work.
    rw [hI]
    simp
  · -- If `I = ∅`, the hypothesis already says the exceptional set has full measure zero.
    rw [hI] at hXI ⊢
    simpa using hXI

end FiniteMeasure

private theorem counterexample_data :
    ∃ (P : Measure (ULift.{u} ℕ)) (_ : IsProbabilityMeasure P)
      (Xenn : ULift.{u} ℕ → ℝ≥0∞) (X : ULift.{u} ℕ → ℝ),
      (∀ᵐ n ∂P, Xenn n ∈ Set.Iio (∞ : ℝ≥0∞)) ∧
      (P⁻[Xenn|⊥] = fun _ ↦ ∞) ∧
      (lowerCondExp P ⊥ X = fun _ ↦ (⊤ : EReal)) ∧
      Integrable (fun n ↦ (X n)⁻) P := by
  let Ω' := ULift.{u} ℕ
  letI : MeasurableSpace Ω' := ⊤
  let harm : Ω' → ℝ≥0∞ := fun n ↦ ENNReal.ofReal ((1 : ℝ) / (n.down : ℝ))
  let f : Ω' → ℝ≥0∞ := fun n ↦ harm n * harm n
  have htsum_f :
      (∑' n : Ω', f n) = ∑' n : ℕ, ENNReal.ofReal ((1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) := by
    simpa [Ω', f, harm, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (Equiv.tsum_eq Equiv.ulift
        (fun n : ℕ ↦ ENNReal.ofReal ((1 : ℝ) / (n : ℝ) ^ (2 : ℕ))))
  have hf0 : (∑' n, f n) ≠ 0 := by
    rw [htsum_f]
    let g : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal ((1 : ℝ) / (n : ℝ) ^ (2 : ℕ))
    have h1 : 0 < g 1 := by
      simp [g]
    have hle : g 1 ≤ ∑' n : ℕ, g n := ENNReal.le_tsum 1
    intro hzero
    rw [hzero] at hle
    exact (not_lt_of_ge hle) h1
  have hf_top : (∑' n, f n) ≠ ∞ := by
    rw [htsum_f]
    simpa using hasSum_zeta_two.summable.tsum_ofReal_ne_top
  let p : PMF Ω' := PMF.normalize f hf0 hf_top
  let P : Measure Ω' := p.toMeasure
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  let Xenn : Ω' → ℝ≥0∞ := fun n ↦ n.down
  let X : Ω' → ℝ := fun n ↦ n.down
  let c : ℝ≥0∞ := (∑' n, f n)⁻¹
  have hsingle (n : Ω') : P {n} = p n := by
    simpa [P] using (PMF.toMeasure_apply_singleton p n (MeasurableSet.singleton n))
  have hcancel (n : Ω') (hn : n.down ≠ 0) : Xenn n * harm n = 1 := by
    have hn' : (n.down : ℝ) ≠ 0 := by
      exact_mod_cast hn
    change ((n.down : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((1 : ℝ) / (n.down : ℝ)) = 1
    rw [show ((n.down : ℕ) : ℝ≥0∞) = ENNReal.ofReal (n.down : ℝ) by simp,
      ← ENNReal.ofReal_mul]
    · field_simp [hn']
      simp
    · positivity
  have hterm (n : Ω') : Xenn n * P {n} = harm n * c := by
    rw [hsingle, PMF.normalize_apply]
    rcases eq_or_ne n.down 0 with hzero | hn
    · have : n = ⟨0⟩ := by
        cases n
        simp_all
      subst this
      simp [Xenn, harm, f, c]
    · calc
        Xenn n * (f n * c) = (Xenn n * f n) * c := by ac_rfl
        _ = ((Xenn n * harm n) * harm n) * c := by simp [f, mul_assoc]
        _ = harm n * c := by simp [hcancel n hn]
  have hharm_top_nat : (∑' n : ℕ, ENNReal.ofReal ((1 : ℝ) / (n : ℝ))) = ∞ := by
    by_contra htop
    have hs : Summable (fun n : ℕ ↦ (ENNReal.ofReal ((1 : ℝ) / (n : ℝ))).toReal) :=
      ENNReal.summable_toReal htop
    have hs' : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)) := by
      simpa using hs
    exact Real.not_summable_one_div_natCast hs'
  have htsum_harm :
      (∑' n : Ω', harm n) = ∑' n : ℕ, ENNReal.ofReal ((1 : ℝ) / (n : ℝ)) := by
    simpa [Ω', harm] using
      (Equiv.tsum_eq Equiv.ulift (fun n : ℕ ↦ ENNReal.ofReal ((1 : ℝ) / (n : ℝ))))
  have hharm_top : (∑' n : Ω', harm n) = ∞ := by
    rw [htsum_harm]
    exact hharm_top_nat
  have hc0 : c ≠ 0 := by
    simp [c, hf_top]
  have hX_top : ∫⁻ n, Xenn n ∂P = ∞ := by
    calc
      ∫⁻ n, Xenn n ∂P = ∑' n, Xenn n * P {n} := by
        simpa [Xenn] using
          (lintegral_countable' Xenn : ∫⁻ n, Xenn n ∂P = ∑' n, Xenn n * P {n})
      _ = ∑' n, harm n * c := by
        exact tsum_congr hterm
      _ = (∑' n, harm n) * c := by
        rw [ENNReal.tsum_mul_right]
      _ = ∞ := by
        simp [hharm_top, hc0]
  have hcond_top : P⁻[Xenn|⊥] = fun _ ↦ ∞ := by
    simpa [hX_top] using (condLExp_bot P Xenn)
  have hXenn_finite : ∀ᵐ n ∂P, Xenn n ∈ Set.Iio (∞ : ℝ≥0∞) := by
    filter_upwards with n
    simp [Xenn]
  have hpos_eq : (fun n ↦ ENNReal.ofReal (X n)) = Xenn := by
    funext n
    simp [X, Xenn]
  have hneg_zero : (fun n ↦ ENNReal.ofReal (-X n)) = (0 : Ω' → ℝ≥0∞) := by
    funext n
    simp [X]
  have hlower_top : lowerCondExp P ⊥ X = fun _ ↦ (⊤ : EReal) := by
    ext n
    rw [lowerCondExp, hpos_eq, hcond_top, hneg_zero, condLExp_zero]
    simp
  have hXneg : Integrable (fun n ↦ (X n)⁻) P := by
    simp [X]
  exact ⟨P, ‹IsProbabilityMeasure P›, Xenn, X, hXenn_finite, hcond_top, hlower_top, hXneg⟩

private theorem not_condLExp_mem_interval_ae_aux :
    ¬ ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {ℱ : MeasurableSpace Ω} {I : Set ℝ≥0∞} {X : Ω → ℝ≥0∞},
        ℱ ≤ mΩ →
        Set.OrdConnected I →
        (∀ x ∈ I, x < ∞) →
        (∀ᵐ ω ∂P, X ω ∈ I) →
        ∀ᵐ ω ∂P, P⁻[X|ℱ] ω ∈ I := by
  intro h
  obtain ⟨P, hP, X, _, hX_finite, hcond_top, _, _⟩ := counterexample_data
  letI : IsProbabilityMeasure P := hP
  have hbad :
      ∀ᵐ n ∂P, P⁻[X|⊥] n ∈ Set.Iio (∞ : ℝ≥0∞) :=
    h P bot_le Set.ordConnected_Iio (fun _ hx ↦ hx) hX_finite
  rw [hcond_top] at hbad
  have hzero : P = 0 := by
    simpa using hbad
  exact NeZero.ne P hzero

-- Proof sketch: reuse the same heavy-tailed nonnegative counterexample as in the private
-- `condLExp` helper, but view it as a real-valued random variable. Then `X⁻ = 0`, so the
-- source-facing `lowerCondExp` is defined, yet conditioning on the trivial σ-algebra still gives
-- the constant value `⊤`, which leaves the interval `Set.Ioo ⊥ ⊤` of genuine real values.
/-- Exercise 8.2.2 (2): The interval-preservation statement from part (1) fails if one weakens
integrability to the one-sided hypothesis `X⁻ ∈ L¹` and replaces `condExp` by the lower
conditional expectation from Remark 8.16. A nonnegative real-valued `X` can satisfy `X⁻ = 0`
almost surely while `lowerCondExp P ℱ X` still takes the value `⊤`. -/
theorem not_lowerCondExp_mem_interval_ae :
    ¬ ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {ℱ : MeasurableSpace Ω} {I : Set EReal} {X : Ω → ℝ},
        ℱ ≤ mΩ →
        Set.OrdConnected I →
        Integrable (fun ω ↦ (X ω)⁻) P →
        (∀ᵐ ω ∂P, (X ω : EReal) ∈ I) →
        ∀ᵐ ω ∂P, lowerCondExp P ℱ X ω ∈ I := by
  intro h
  obtain ⟨P, hP, _, X, _, _, hlower_top, hXneg⟩ := counterexample_data
  letI : IsProbabilityMeasure P := hP
  have hXI : ∀ᵐ n ∂P, (X n : EReal) ∈ Set.Ioo (⊥ : EReal) ⊤ := by
    filter_upwards with n
    simp
  have hbad :
      ∀ᵐ n ∂P, lowerCondExp P ⊥ X n ∈ Set.Ioo (⊥ : EReal) ⊤ :=
    h P bot_le Set.ordConnected_Ioo hXneg hXI
  rw [hlower_top] at hbad
  have hzero : P = 0 := by
    simpa using hbad
  exact NeZero.ne P hzero
