/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure[mΩ] Ω}

/-- An admissible increasing integrable approximation of `X` is an increasing sequence of
integrable functions bounded below by `-X⁻` that converges pointwise to `X`. -/
def is_admissible_increasing_integrable_approximation {m : MeasurableSpace Ω} (P : Measure[m] Ω)
    (X : Ω → ℝ) (Xn : ℕ → Ω → ℝ) : Prop :=
  (∀ n, Integrable (Xn n) P) ∧
    (∀ n ω, -(X ω)⁻ ≤ Xn n ω) ∧
    Monotone Xn ∧
    ∀ ω, Tendsto (fun n ↦ Xn n ω) atTop (nhds (X ω))

/-- The lower-integrable conditional expectation is the canonical `EReal`-valued extension of
`P[X | ℱ]`, obtained from the conditional Lebesgue expectations of the positive and negative
parts. For `X⁻ ∈ L¹(P)`, it takes values in `(-∞, ∞]` almost surely. -/
/-
`MeasureTheory.condLExp` is the owner abstraction for conditional Lebesgue expectation of
nonnegative functions. `lowerCondExp` is the source-facing signed bridge used in Remark 8.16.
-/
noncomputable def lowerCondExp {m : MeasurableSpace Ω} (P : Measure[m] Ω) (ℱ : MeasurableSpace Ω)
    (X : Ω → ℝ) : Ω → EReal :=
  fun ω ↦ (P⁻[fun ω ↦ ENNReal.ofReal (X ω) | ℱ] ω : EReal) -
    P⁻[fun ω ↦ ENNReal.ofReal (-X ω) | ℱ] ω

section Probability

variable [IsProbabilityMeasure P] {ℱ : MeasurableSpace Ω}

/-- Helper for Remark 8.16: for a nonnegative integrable real-valued random variable, the
`EReal` coercion of the usual conditional expectation agrees almost surely with the conditional
Lebesgue expectation. -/
lemma ae_coe_condExp_eq_condLExp_of_nonneg
    {Y : Ω → ℝ} (hY_nonneg : 0 ≤ᵐ[P] Y) (hY : Integrable Y P) :
    (fun ω ↦ ((P[Y | ℱ] ω : ℝ) : EReal)) =ᵐ[P]
      fun ω ↦ (P⁻[fun ω ↦ ENNReal.ofReal (Y ω) | ℱ] ω : EReal) := by
  -- Proof comment: first compare `condExp` with the `toReal` of `condLExp`.
  have hlintegral :
      ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P ≠ ⊤ := by
    rw [MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hY.aestronglyMeasurable hY_nonneg]
    exact hY
  have htoReal :
      (fun ω ↦ (P⁻[fun ω ↦ ENNReal.ofReal (Y ω) | ℱ] ω).toReal) =ᵐ[P]
        P[fun ω ↦ (ENNReal.ofReal (Y ω)).toReal | ℱ] :=
    MeasureTheory.toReal_condLExp ℱ hY.aestronglyMeasurable.aemeasurable.ennreal_ofReal hlintegral
  -- Proof comment: the nonnegativity hypothesis identifies `((ENNReal.ofReal (Y ω)).toReal)` with
  -- `Y ω`, so the previous identity upgrades to the desired `EReal` statement.
  have htoReal_input : (fun ω ↦ (ENNReal.ofReal (Y ω)).toReal) =ᵐ[P] Y := by
    filter_upwards [hY_nonneg] with ω hω
    simp [ENNReal.toReal_ofReal hω]
  have hcond_toReal : P[fun ω ↦ (ENNReal.ofReal (Y ω)).toReal | ℱ] =ᵐ[P] P[Y | ℱ] :=
    MeasureTheory.condExp_congr_ae htoReal_input
  have hfinite :
      ∀ᵐ ω ∂P, P⁻[fun ω ↦ ENNReal.ofReal (Y ω) | ℱ] ω ≠ ⊤ :=
    MeasureTheory.condLExp_ne_top hlintegral
  filter_upwards [htoReal, hcond_toReal, hfinite] with ω hω_toReal hω_cond hω_fin
  have hω_coe :
      (((P⁻[fun ω ↦ ENNReal.ofReal (Y ω) | ℱ] ω).toReal : ℝ) : EReal) =
        (P⁻[fun ω ↦ ENNReal.ofReal (Y ω) | ℱ] ω : EReal) := by
    exact EReal.coe_ennreal_toReal hω_fin
  rw [← hω_cond]
  simpa [hω_coe] using congrArg (fun x : ℝ ↦ (x : EReal)) hω_toReal.symm

-- Proof sketch: `P⁻[fun ω ↦ ENNReal.ofReal (-X ω) | ℱ]` is finite almost surely when `X⁻` is
-- integrable, so the difference defining `lowerCondExp P ℱ X` cannot be `⊥` except on a
-- `P`-null set.
/-- If `X⁻` is integrable, then the lower conditional expectation takes values in `(-∞, ∞]`
almost surely. -/
theorem lowerCondExp_ne_bot_ae (hℱ : ℱ ≤ mΩ)
    {X : Ω → ℝ} (hXneg : Integrable (fun ω ↦ (X ω)⁻) P) :
    ∀ᵐ ω ∂P, lowerCondExp P ℱ X ω ≠ ⊥ := by
  -- Proof comment: finiteness of the negative-part `condLExp` term rules out the only way the
  -- defining subtraction could hit `⊥`.
  have hlintegral :
      ∫⁻ ω, ENNReal.ofReal ((X ω)⁻) ∂P ≠ ⊤ := by
    rw [MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hXneg.aestronglyMeasurable]
    · exact hXneg
    · exact Filter.Eventually.of_forall fun ω ↦ le_max_right (-X ω) 0
  have hfinite :
      ∀ᵐ ω ∂P, P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] ω ≠ ⊤ :=
    MeasureTheory.condLExp_ne_top hlintegral
  have hcongr :
      P⁻[fun ω ↦ ENNReal.ofReal (-X ω) | ℱ] =ᵐ[P]
        P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] := by
    apply MeasureTheory.condLExp_congr_ae
    filter_upwards with ω
    by_cases hω : 0 ≤ -X ω
    · simp [negPart, max_eq_left hω, hω]
    · have hω' : -X ω ≤ 0 := le_of_not_ge hω
      simp [negPart, max_eq_right hω', ENNReal.ofReal_eq_zero.2 hω']
  filter_upwards [hfinite, hcongr] with ω hω_fin hω_congr
  rw [lowerCondExp, hω_congr]
  let a : EReal := (P⁻[fun ω ↦ ENNReal.ofReal (X ω) | ℱ] ω : EReal)
  let b : EReal := (P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] ω : EReal)
  have ha_ne_bot : a ≠ ⊥ := by
    simp [a]
  have hb_ne_top : b ≠ ⊤ := by
    simpa [b] using hω_fin
  have hsum_ne_bot :
      a + -b ≠ ⊥ := by
    intro hbot
    rw [EReal.add_eq_bot_iff] at hbot
    rcases hbot with hbad | hbad
    · exact ha_ne_bot hbad
    · exact hb_ne_top ((EReal.neg_eq_bot_iff).1 hbad)
  simpa [a, b, sub_eq_add_neg] using hsum_ne_bot

/-- Helper for Remark 8.16: the conditional Lebesgue expectations of an increasing sequence
converging pointwise identify the almost-sure `iSup` candidate with the conditional Lebesgue
expectation of the limit. -/
lemma ae_eq_iSup_condLExp_of_nonneg_monotone_limit
    (hℱ : ℱ ≤ mΩ) {Yn : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hYn : ∀ n, Integrable (Yn n) P) (hnonneg : ∀ n, 0 ≤ᵐ[P] Yn n) (hmono : Monotone Yn)
    (hlim : ∀ ω, Tendsto (fun n ↦ Yn n ω) atTop (nhds (Y ω))) :
    (fun ω ↦ ⨆ n, P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω) =ᵐ[P]
      fun ω ↦ P⁻[fun ω ↦ ENNReal.ofReal (Y ω) | ℱ] ω := by
  -- Route correction: isolate the native `ℝ≥0∞` conditional-Lebesgue limit first, and only use
  -- the signed `EReal` layer later in the main theorem.
  let f : ℕ → Ω → ENNReal := fun n ω ↦ ENNReal.ofReal (Yn n ω)
  let Z : Ω → ENNReal := fun ω ↦ ⨆ n, P⁻[f n | ℱ] ω
  have hZ_meas :
      Measurable[ℱ] Z := by
    -- Proof comment: the `iSup` candidate is `ℱ`-measurable because every `condLExp` term is.
    refine Measurable.iSup fun n ↦ ?_
    simpa [f] using MeasureTheory.measurable_condLExp ℱ P (f n)
  have hcond_step :
      ∀ n, ∀ᵐ ω ∂P, P⁻[f n | ℱ] ω ≤ P⁻[f n.succ | ℱ] ω := by
    -- Proof comment: monotonicity of the underlying sequence passes through `condLExp`.
    intro n
    exact MeasureTheory.condLExp_mono <|
      Filter.Eventually.of_forall fun ω ↦ ENNReal.ofReal_le_ofReal (hmono (Nat.le_succ n) ω)
  have hf_iSup :
      (fun ω ↦ ⨆ n, f n ω) =ᵐ[P] fun ω ↦ ENNReal.ofReal (Y ω) := by
    -- Proof comment: pointwise monotone convergence identifies the `iSup` of the lifted sequence.
    filter_upwards with ω
    have hmonoω : Monotone fun n ↦ f n ω := fun m n hmn ↦
      ENNReal.ofReal_le_ofReal (hmono hmn ω)
    simpa [f] using iSup_eq_of_tendsto hmonoω (ENNReal.tendsto_ofReal (hlim ω))
  refine MeasureTheory.ae_eq_condLExp hℱ (P := P) (X := fun ω ↦ ENNReal.ofReal (Y ω)) hZ_meas
    ?_
  intro s hs
  -- Proof comment: compute the set integral of `Z` by monotone convergence, then replace each
  -- term with the defining set integral of the corresponding `condLExp`.
  calc
    ∫⁻ ω in s, Z ω ∂P
        = ⨆ n, ∫⁻ ω in s, P⁻[f n | ℱ] ω ∂P := by
            rw [show ∫⁻ ω in s, Z ω ∂P = ∫⁻ ω, Z ω ∂P.restrict s by rfl]
            simp only [Z]
            simpa using
              (MeasureTheory.lintegral_iSup_ae (μ := P.restrict s)
                (f := fun n ω ↦ P⁻[f n | ℱ] ω)
                (fun n ↦ (MeasureTheory.measurable_condLExp ℱ P (f n)).mono hℱ le_rfl)
                (fun n ↦ MeasureTheory.ae_restrict_of_ae (hcond_step n)))
    _ = ⨆ n, ∫⁻ ω in s, f n ω ∂P := by
          congr with n
          exact MeasureTheory.setLIntegral_condLExp hℱ P (f n) hs
    _ = ∫⁻ ω in s, ENNReal.ofReal (Y ω) ∂P := by
          rw [show ∫⁻ ω in s, ENNReal.ofReal (Y ω) ∂P =
              ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P.restrict s by rfl]
          rw [← MeasureTheory.lintegral_congr_ae (Filter.EventuallyEq.restrict hf_iSup)]
          simpa [f] using
            (MeasureTheory.lintegral_iSup' (μ := P.restrict s) (f := f)
              (fun n ↦ ((hYn n).aestronglyMeasurable.aemeasurable.ennreal_ofReal).restrict)
              (MeasureTheory.ae_restrict_of_ae <|
                Filter.Eventually.of_forall fun ω ↦
                  (show Monotone (fun n ↦ f n ω) from fun m n hmn ↦
                    ENNReal.ofReal_le_ofReal (hmono hmn ω)))).symm

/-- Helper for Remark 8.16: the conditioned nonnegative sequence converges almost surely to the
conditional Lebesgue expectation of the pointwise limit. -/
lemma ae_tendsto_condLExp_of_nonneg_monotone_limit
    (hℱ : ℱ ≤ mΩ) {Yn : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hYn : ∀ n, Integrable (Yn n) P) (hnonneg : ∀ n, 0 ≤ᵐ[P] Yn n) (hmono : Monotone Yn)
    (hlim : ∀ ω, Tendsto (fun n ↦ Yn n ω) atTop (nhds (Y ω))) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω) atTop
        (nhds (P⁻[fun ω ↦ ENNReal.ofReal (Y ω) | ℱ] ω)) := by
  have hiSup_eq :=
    ae_eq_iSup_condLExp_of_nonneg_monotone_limit (mΩ := mΩ) (P := P) (ℱ := ℱ) hℱ hYn hnonneg
      hmono hlim
  have hmono_cond :
      ∀ᵐ ω ∂P,
        Monotone fun n ↦ P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω := by
    -- Proof comment: the conditional expectations are monotone almost surely because each
    -- pair `(m,n)` inherits the pointwise order of the source sequence.
    change ∀ᵐ ω ∂P, ∀ m n, m ≤ n →
      P⁻[fun ω ↦ ENNReal.ofReal (Yn m ω) | ℱ] ω ≤
        P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω
    rw [MeasureTheory.ae_all_iff]
    intro m
    rw [MeasureTheory.ae_all_iff]
    intro n
    by_cases hmn : m ≤ n
    · filter_upwards
        [MeasureTheory.condLExp_mono <|
          Filter.Eventually.of_forall fun ω ↦ ENNReal.ofReal_le_ofReal (hmono hmn ω)]
        with ω hω _ using hω
    · exact MeasureTheory.ae_of_all _ fun ω hω ↦ False.elim (hmn hω)
  filter_upwards [hiSup_eq, hmono_cond] with ω hω_eq hω_mono
  -- Proof comment: once the almost-sure `iSup` is identified with the limit, monotone
  -- convergence in the order topology gives the desired pointwise `Tendsto`.
  simpa [hω_eq] using (tendsto_atTop_iSup hω_mono)

/-- Helper for Remark 8.16: coercing the monotone `condLExp` convergence from `ℝ≥0∞` to
`EReal` preserves the almost-sure limit. -/
lemma ae_tendsto_coe_condLExp_of_nonneg_monotone_limit
    (hℱ : ℱ ≤ mΩ) {Yn : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hYn : ∀ n, Integrable (Yn n) P) (hnonneg : ∀ n, 0 ≤ᵐ[P] Yn n) (hmono : Monotone Yn)
    (hlim : ∀ ω, Tendsto (fun n ↦ Yn n ω) atTop (nhds (Y ω))) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ (P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω : EReal)) atTop
        (nhds ((P⁻[fun ω ↦ ENNReal.ofReal (Y ω) | ℱ] ω : ENNReal) : EReal)) := by
  -- Proof comment: the coercion `ENNReal → EReal` is continuous, so it preserves the limit.
  exact
    (ae_tendsto_condLExp_of_nonneg_monotone_limit (mΩ := mΩ) (P := P) (ℱ := ℱ) hℱ hYn hnonneg
      hmono hlim).mono fun ω hω ↦
        (continuous_coe_ennreal_ereal.tendsto _).comp hω

/-- Helper for Remark 8.16: `lowerCondExp` is almost surely the positive-part `condLExp` minus
the negative-part `condLExp`. -/
lemma lowerCondExp_posPartNegPart_ae {X : Ω → ℝ} :
    lowerCondExp P ℱ X =ᵐ[P] fun ω ↦
      (P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : EReal) -
        P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] ω := by
  have hpos_congr :
      P⁻[fun ω ↦ ENNReal.ofReal (X ω) | ℱ] =ᵐ[P]
        P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] := by
    -- Proof comment: rewrite the first `condLExp` term to the genuine positive part.
    apply MeasureTheory.condLExp_congr_ae
    filter_upwards with ω
    by_cases hω : 0 ≤ X ω
    · simp [posPart, max_eq_left hω, hω]
    · have hω' : X ω ≤ 0 := le_of_not_ge hω
      simp [posPart, hω, hω', ENNReal.ofReal_eq_zero.2 hω']
  have hneg_congr :
      P⁻[fun ω ↦ ENNReal.ofReal (-X ω) | ℱ] =ᵐ[P]
        P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] := by
    -- Proof comment: rewrite the second `condLExp` term to the genuine negative part.
    apply MeasureTheory.condLExp_congr_ae
    filter_upwards with ω
    by_cases hω : 0 ≤ -X ω
    · simp [negPart, hω]
    · have hω' : -X ω ≤ 0 := le_of_not_ge hω
      simp [negPart, hω, hω', ENNReal.ofReal_eq_zero.2 hω']
  filter_upwards [hpos_congr, hneg_congr] with ω hω_pos hω_neg
  -- Proof comment: after the two pointwise congruences, `lowerCondExp` already has the desired
  -- positive/negative decomposition.
  rw [lowerCondExp, hω_pos, hω_neg]

/-- Helper for Remark 8.16: after shifting by `X⁻`, the signed conditional expectation of `Xn`
is almost surely the nonnegative conditional-Lebesgue expectation of the shifted sequence minus
the fixed `X⁻` correction. -/
lemma shiftedCondExpSubCorrection_ae
    {X : Ω → ℝ} (hXneg : Integrable (fun ω ↦ (X ω)⁻) P) {Xn : ℕ → Ω → ℝ}
    (hXn : is_admissible_increasing_integrable_approximation P X Xn) :
    let Yn : ℕ → Ω → ℝ := fun n ω ↦ Xn n ω + (X ω)⁻
    ∀ᵐ ω ∂P, ∀ n,
      ((P[Xn n | ℱ] ω : ℝ) : EReal) =
        (P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω : EReal) -
          ((P[fun ω ↦ (X ω)⁻ | ℱ] ω : ℝ) : EReal) := by
  let Yn : ℕ → Ω → ℝ := fun n ω ↦ Xn n ω + (X ω)⁻
  have hYn_int : ∀ n, Integrable (Yn n) P := fun n ↦ (hXn.1 n).add hXneg
  have hYn_nonneg : ∀ n, 0 ≤ᵐ[P] Yn n := by
    -- Proof comment: the admissibility lower bound becomes nonnegativity after shifting by `X⁻`.
    intro n
    filter_upwards with ω
    have hω := hXn.2.1 n ω
    dsimp [Yn]
    linarith
  have hYn_cond :
      ∀ᵐ ω ∂P, ∀ n,
        ((P[Yn n | ℱ] ω : ℝ) : EReal) =
          (P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω : EReal) := by
    -- Proof comment: each shifted term is nonnegative, so its real-valued `condExp` matches
    -- the native nonnegative `condLExp`.
    rw [MeasureTheory.ae_all_iff]
    intro n
    exact @ae_coe_condExp_eq_condLExp_of_nonneg Ω mΩ P _ ℱ (Yn n) (hYn_nonneg n) (hYn_int n)
  have hshift_add :
      ∀ᵐ ω ∂P, ∀ n,
        P[Yn n | ℱ] ω = P[Xn n | ℱ] ω + P[fun ω ↦ (X ω)⁻ | ℱ] ω := by
    -- Proof comment: linearity of `condExp` isolates the fixed `X⁻` correction term.
    rw [MeasureTheory.ae_all_iff]
    intro n
    simpa [Yn] using (condExp_add (hXn.1 n) hXneg ℱ :
      P[fun ω ↦ Xn n ω + (X ω)⁻ | ℱ] =ᵐ[P]
        P[Xn n | ℱ] + P[fun ω ↦ (X ω)⁻ | ℱ])
  filter_upwards [hYn_cond, hshift_add] with ω hω_cond hω_add
  intro n
  have hω_real :
      P[Xn n | ℱ] ω = P[Yn n | ℱ] ω - P[fun ω ↦ (X ω)⁻ | ℱ] ω := by
    linarith [hω_add n]
  -- Proof comment: coerce the real subtraction to `EReal`, then replace the shifted
  -- conditional expectation by its `condLExp` form.
  calc
    ((P[Xn n | ℱ] ω : ℝ) : EReal)
        = (((P[Yn n | ℱ] ω : ℝ) : EReal) -
            ((P[fun ω ↦ (X ω)⁻ | ℱ] ω : ℝ) : EReal)) := by
              simpa [EReal.coe_sub] using congrArg (fun t : ℝ ↦ (t : EReal)) hω_real
    _ = (P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω : EReal) -
          ((P[fun ω ↦ (X ω)⁻ | ℱ] ω : ℝ) : EReal) := by
            rw [hω_cond n]

-- Proof sketch: apply monotone convergence to the nonnegative conditional expectations of the
-- shifted truncations `Xn + X⁻`, identify the limiting positive and negative parts via `condLExp`,
-- and then subtract the common `condLExp` term coming from `X⁻`.
/-- Remark 8.16: if `X⁻ ∈ L¹(P)`, then the lower conditional expectation of `X` with respect to
`ℱ` is the almost-sure monotone limit of the conditional expectations of any admissible increasing
integrable approximation of `X`. Consequently, this limit does not depend on the chosen
approximation sequence. -/
theorem ae_tendsto_condExp_of_admissible_increasing_integrable_approximation
    (hℱ : ℱ ≤ mΩ) {X : Ω → ℝ} (hXneg : Integrable (fun ω ↦ (X ω)⁻) P) {Xn : ℕ → Ω → ℝ}
    (hXn : is_admissible_increasing_integrable_approximation P X Xn) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (P[Xn n | ℱ] ω : EReal)) atTop
      (nhds (lowerCondExp P ℱ X ω)) := by
  let Yn : ℕ → Ω → ℝ := fun n ω ↦ Xn n ω + (X ω)⁻
  have hYn_int : ∀ n, Integrable (Yn n) P := fun n ↦ (hXn.1 n).add hXneg
  have hYn_nonneg : ∀ n, 0 ≤ᵐ[P] Yn n := by
    -- Proof comment: the lower bound `-X⁻ ≤ Xn n` turns the shifted sequence nonnegative.
    intro n
    filter_upwards with ω
    have hω := hXn.2.1 n ω
    dsimp [Yn]
    linarith
  have hYn_mono : Monotone Yn := by
    -- Proof comment: adding the fixed shift `X⁻` preserves monotonicity.
    intro m n hmn ω
    dsimp [Yn]
    exact add_le_add (hXn.2.2.1 hmn ω) le_rfl
  have hYn_lim : ∀ ω, Tendsto (fun n ↦ Yn n ω) atTop (nhds ((X ω)⁺)) := by
    -- Route correction: keep the convergence proof in the nonnegative shifted world and only
    -- subtract the fixed correction after the native `condLExp` limit is known.
    intro ω
    have hω_add :
        Tendsto (fun n ↦ Xn n ω + (X ω)⁻) atTop (nhds (X ω + (X ω)⁻)) :=
      (hXn.2.2.2 ω).add tendsto_const_nhds
    have hω_pos : X ω + (X ω)⁻ = (X ω)⁺ := by
      linarith [posPart_sub_negPart (X ω)]
    simpa [Yn, hω_pos] using hω_add
  have hcond_limit :
      ∀ᵐ ω ∂P,
        Tendsto (fun n ↦ (P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω : EReal)) atTop
          (nhds ((P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : ENNReal) : EReal)) :=
    ae_tendsto_coe_condLExp_of_nonneg_monotone_limit (mΩ := mΩ) (P := P) (ℱ := ℱ) hℱ hYn_int
      hYn_nonneg hYn_mono hYn_lim
  have hshift :
      ∀ᵐ ω ∂P, ∀ n,
        ((P[Xn n | ℱ] ω : ℝ) : EReal) =
          (P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω : EReal) -
            ((P[fun ω ↦ (X ω)⁻ | ℱ] ω : ℝ) : EReal) :=
    shiftedCondExpSubCorrection_ae (mΩ := mΩ) (P := P) (ℱ := ℱ) hXneg hXn
  have hneg_cond :
      (fun ω ↦ ((P[fun ω ↦ (X ω)⁻ | ℱ] ω : ℝ) : EReal)) =ᵐ[P]
        fun ω ↦ (P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] ω : EReal) :=
    @ae_coe_condExp_eq_condLExp_of_nonneg Ω mΩ P _ ℱ (fun ω ↦ (X ω)⁻)
      (Filter.Eventually.of_forall fun ω ↦ negPart_nonneg (X ω)) hXneg
  have hlower :
      lowerCondExp P ℱ X =ᵐ[P] fun ω ↦
        (P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : EReal) -
          P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] ω :=
    lowerCondExp_posPartNegPart_ae (mΩ := mΩ) (P := P) (ℱ := ℱ)
  filter_upwards [hcond_limit, hshift, hneg_cond, hlower] with ω hω_limit hω_shift hω_neg hω_lower
  let c : ℝ := P[fun ω ↦ (X ω)⁻ | ℱ] ω
  have hsub_limit :
      Tendsto
        (fun n ↦ (P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω : EReal) - (c : EReal)) atTop
        (nhds
          (((P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : ENNReal) : EReal) - (c : EReal))) := by
    have hpair :
        Tendsto
          (fun n ↦ ((P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω : EReal), ((-c : ℝ) : EReal)))
          atTop
          (nhds
            ((((P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : ENNReal) : EReal),
              ((-c : ℝ) : EReal)))) :=
      by
        have hconst :
            Tendsto (fun _ : ℕ ↦ ((-c : ℝ) : EReal)) atTop
              (nhds (((-c : ℝ) : EReal))) :=
          tendsto_const_nhds
        rw [nhds_prod_eq]
        exact hω_limit.prodMk hconst
    have hadd_limit :
        Tendsto
          (fun n ↦ (P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω : EReal) +
            ((-c : ℝ) : EReal)) atTop
          (nhds
            (((P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : ENNReal) : EReal) +
              ((-c : ℝ) : EReal))) := by
      exact
        (EReal.continuousAt_add (p := (((P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : ENNReal) :
            EReal), ((-c : ℝ) : EReal)))
          (Or.inr (EReal.coe_ne_bot (-c))) (Or.inr (EReal.coe_ne_top (-c)))).tendsto.comp hpair
    simpa [c, sub_eq_add_neg] using hadd_limit
  have htarget :
      (((P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : ENNReal) : EReal) - (c : EReal)) =
        lowerCondExp P ℱ X ω := by
    calc
      (((P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : ENNReal) : EReal) - (c : EReal))
          = (((P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : ENNReal) : EReal) -
              P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] ω) := by
                rw [show (c : EReal) =
                  (P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] ω : EReal) by simpa [c] using hω_neg]
      _ = lowerCondExp P ℱ X ω := hω_lower.symm
  have hseq :
      (fun n ↦ (P[Xn n | ℱ] ω : EReal)) =
        fun n ↦ (P⁻[fun ω ↦ ENNReal.ofReal (Yn n ω) | ℱ] ω : EReal) - (c : EReal) := by
    funext n
    simpa [c] using hω_shift n
  -- Proof comment: the shifted nonnegative sequence converges by the native `condLExp` theorem,
  -- and continuity of addition with a finite real constant transports that limit back to the
  -- original signed conditional expectations.
  simpa [hseq, htarget] using hsub_limit

-- Proof sketch: decompose `X = X⁺ - X⁻`, identify the two pieces with `condLExp` through
-- `toReal_condLExp`, and use linearity of `condExp` on the integrable positive and negative parts.
/-- For integrable `X`, the lower-integrable extension agrees almost surely with the usual
conditional expectation from Definition 8.11. -/
theorem lowerCondExp_ae_eq_condExp (hℱ : ℱ ≤ mΩ) {X : Ω → ℝ} (hX : Integrable X P) :
    lowerCondExp P ℱ X =ᵐ[P] fun ω ↦ (P[X | ℱ] ω : EReal) := by
  have hpos_congr :
      P⁻[fun ω ↦ ENNReal.ofReal (X ω) | ℱ] =ᵐ[P]
        P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] := by
    -- Proof comment: rewrite the positive `condLExp` term to the actual positive part.
    apply MeasureTheory.condLExp_congr_ae
    filter_upwards with ω
    by_cases hω : 0 ≤ X ω
    · simp [posPart, max_eq_left hω, hω]
    · have hω' : X ω ≤ 0 := le_of_not_ge hω
      simp [posPart, hω, hω', ENNReal.ofReal_eq_zero.2 hω']
  have hneg_congr :
      P⁻[fun ω ↦ ENNReal.ofReal (-X ω) | ℱ] =ᵐ[P]
        P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] := by
    -- Proof comment: rewrite the negative `condLExp` term to the actual negative part.
    apply MeasureTheory.condLExp_congr_ae
    filter_upwards with ω
    by_cases hω : 0 ≤ -X ω
    · simp [negPart, hω]
    · have hω' : -X ω ≤ 0 := le_of_not_ge hω
      simp [negPart, hω, hω', ENNReal.ofReal_eq_zero.2 hω']
  have hpos_cond :
      (fun ω ↦ ((P[fun ω ↦ (X ω)⁺ | ℱ] ω : ℝ) : EReal)) =ᵐ[P]
        fun ω ↦ (P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : EReal) :=
    @ae_coe_condExp_eq_condLExp_of_nonneg Ω mΩ P _ ℱ (fun ω ↦ (X ω)⁺)
      (Filter.Eventually.of_forall fun ω ↦ posPart_nonneg (X ω)) hX.pos_part
  have hneg_cond :
      (fun ω ↦ ((P[fun ω ↦ (X ω)⁻ | ℱ] ω : ℝ) : EReal)) =ᵐ[P]
        fun ω ↦ (P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] ω : EReal) :=
    @ae_coe_condExp_eq_condLExp_of_nonneg Ω mΩ P _ ℱ (fun ω ↦ (X ω)⁻)
      (Filter.Eventually.of_forall fun ω ↦ negPart_nonneg (X ω)) hX.neg_part
  have hX_decomp : (fun ω ↦ (X ω)⁺ - (X ω)⁻) = X := by
    funext ω
    exact posPart_sub_negPart (X ω)
  have hcond_sub :
      P[fun ω ↦ (X ω)⁺ - (X ω)⁻ | ℱ] =ᵐ[P]
        fun ω ↦ P[fun ω ↦ (X ω)⁺ | ℱ] ω - P[fun ω ↦ (X ω)⁻ | ℱ] ω :=
    condExp_sub hX.pos_part hX.neg_part ℱ
  have hcond_X :
      P[fun ω ↦ (X ω)⁺ - (X ω)⁻ | ℱ] =ᵐ[P] P[X | ℱ] :=
    MeasureTheory.condExp_congr_ae <| Filter.Eventually.of_forall <| congrFun hX_decomp
  filter_upwards [hpos_congr, hneg_congr, hpos_cond, hneg_cond, hcond_sub, hcond_X] with ω
      hω_pos hω_neg hω_pos_cond hω_neg_cond hω_sub hω_X
  -- Proof comment: after rewriting both `condLExp` terms and using linearity of `condExp`,
  -- the remaining identity is just the real equality `X = X⁺ - X⁻` viewed in `EReal`.
  rw [lowerCondExp, hω_pos, hω_neg, ← hω_pos_cond, ← hω_neg_cond]
  have hω_real :
      P[fun ω ↦ (X ω)⁺ | ℱ] ω - P[fun ω ↦ (X ω)⁻ | ℱ] ω = P[X | ℱ] ω :=
    hω_sub.symm.trans hω_X
  simpa [EReal.coe_sub] using congrArg (fun t : ℝ ↦ (t : EReal)) hω_real


-- Proof sketch: if `X ≤ Y` almost surely and `X⁻ ∈ L¹(P)`, then also `Y⁻ ∈ L¹(P)`. Compare the
-- positive and negative `condLExp` terms using `condLExp_mono` and subtract the common finite
-- negative-part correction.
/-- The lower-integrable extension of conditional expectation is monotone with respect to
almost-sure order. -/
theorem lowerCondExp_mono (hℱ : ℱ ≤ mΩ)
    {X Y : Ω → ℝ} (hXneg : Integrable (fun ω ↦ (X ω)⁻) P) (hXY : X ≤ᵐ[P] Y) :
    lowerCondExp P ℱ X ≤ᵐ[P] lowerCondExp P ℱ Y := by
  -- Proof comment: compare the positive parts and the negative parts separately, then use the
  -- monotonicity of subtraction in `EReal`.
  have hXpos_congr :
      P⁻[fun ω ↦ ENNReal.ofReal (X ω) | ℱ] =ᵐ[P]
        P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] := by
    apply MeasureTheory.condLExp_congr_ae
    filter_upwards with ω
    by_cases hω : 0 ≤ X ω
    · simp [posPart, max_eq_left hω, hω]
    · have hω' : X ω ≤ 0 := le_of_not_ge hω
      simp [posPart, hω, hω', ENNReal.ofReal_eq_zero.2 hω']
  have hXneg_congr :
      P⁻[fun ω ↦ ENNReal.ofReal (-X ω) | ℱ] =ᵐ[P]
        P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] := by
    apply MeasureTheory.condLExp_congr_ae
    filter_upwards with ω
    by_cases hω : 0 ≤ -X ω
    · simp [negPart, hω]
    · have hω' : -X ω ≤ 0 := le_of_not_ge hω
      simp [negPart, hω, hω', ENNReal.ofReal_eq_zero.2 hω']
  have hYpos_congr :
      P⁻[fun ω ↦ ENNReal.ofReal (Y ω) | ℱ] =ᵐ[P]
        P⁻[fun ω ↦ ENNReal.ofReal ((Y ω)⁺) | ℱ] := by
    apply MeasureTheory.condLExp_congr_ae
    filter_upwards with ω
    by_cases hω : 0 ≤ Y ω
    · simp [posPart, max_eq_left hω, hω]
    · have hω' : Y ω ≤ 0 := le_of_not_ge hω
      simp [posPart, hω, hω', ENNReal.ofReal_eq_zero.2 hω']
  have hYneg_congr :
      P⁻[fun ω ↦ ENNReal.ofReal (-Y ω) | ℱ] =ᵐ[P]
        P⁻[fun ω ↦ ENNReal.ofReal ((Y ω)⁻) | ℱ] := by
    apply MeasureTheory.condLExp_congr_ae
    filter_upwards with ω
    by_cases hω : 0 ≤ -Y ω
    · simp [negPart, hω]
    · have hω' : -Y ω ≤ 0 := le_of_not_ge hω
      simp [negPart, hω, hω', ENNReal.ofReal_eq_zero.2 hω']
  have hpos :
      (fun ω ↦ ENNReal.ofReal ((X ω)⁺)) ≤ᵐ[P] fun ω ↦ ENNReal.ofReal ((Y ω)⁺) := by
    filter_upwards [hXY] with ω hω
    exact ENNReal.ofReal_le_ofReal (max_le_max hω le_rfl)
  have hneg :
      (fun ω ↦ ENNReal.ofReal ((Y ω)⁻)) ≤ᵐ[P] fun ω ↦ ENNReal.ofReal ((X ω)⁻) := by
    filter_upwards [hXY] with ω hω
    exact ENNReal.ofReal_le_ofReal (max_le_max (neg_le_neg hω) le_rfl)
  have hcond_pos := MeasureTheory.condLExp_mono (mΩ := ℱ) hpos
  have hcond_neg := MeasureTheory.condLExp_mono (mΩ := ℱ) hneg
  filter_upwards [hcond_pos, hcond_neg, hXpos_congr, hXneg_congr, hYpos_congr, hYneg_congr] with ω
      hω_pos hω_neg hω_Xpos hω_Xneg hω_Ypos hω_Yneg
  have hω_pos' :
      (P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁺) | ℱ] ω : EReal) ≤
        (P⁻[fun ω ↦ ENNReal.ofReal ((Y ω)⁺) | ℱ] ω : EReal) := by
    exact_mod_cast hω_pos
  have hω_neg' :
      (P⁻[fun ω ↦ ENNReal.ofReal ((Y ω)⁻) | ℱ] ω : EReal) ≤
        (P⁻[fun ω ↦ ENNReal.ofReal ((X ω)⁻) | ℱ] ω : EReal) := by
    exact_mod_cast hω_neg
  rw [lowerCondExp, lowerCondExp, hω_Xpos, hω_Xneg, hω_Ypos, hω_Yneg]
  exact EReal.sub_le_sub hω_pos' hω_neg'

end Probability
