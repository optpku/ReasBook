/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Definition_4_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 4.21: an almost-everywhere lower bound for every term of a sequence
propagates to an almost-everywhere lower bound for the pointwise `liminf`. -/
private theorem ae_le_liminf_of_forall_ae_le
    (μ : Measure Ω) {f : Ω → EReal} {fSeq : ℕ → Ω → EReal}
    (h_lower : ∀ n, f ≤ᵐ[μ] fSeq n) :
    f ≤ᵐ[μ] fun ω ↦ liminf (fun n ↦ fSeq n ω) atTop := by
  -- Pass from the countable family of a.e. bounds to a single a.e. pointwise bound on every term.
  have h_all : ∀ᵐ ω ∂μ, ∀ n, f ω ≤ fSeq n ω := by
    rw [ae_all_iff]
    exact h_lower
  -- Pointwise, the lower bound dominates the tail infima and hence the liminf.
  refine h_all.mono ?_
  intro ω hω
  exact le_trans (le_iInf hω) Filter.iInf_le_liminf

private theorem erealIntegralDefined_liminf
    (μ : Measure Ω) {f : Ω → EReal} {fSeq : ℕ → Ω → EReal}
    (hf : erealIntegrable f μ)
    (hfSeq_meas : ∀ n, Measurable (fSeq n)) (h_lower : ∀ n, f ≤ᵐ[μ] fSeq n) :
    erealIntegralDefined (fun ω ↦ liminf (fun n ↦ fSeq n ω) atTop) μ := by
  -- The liminf is measurable, and the integrable lower bound `f` keeps the negative part finite.
  exact erealIntegralDefined_of_ae_le hf (Measurable.liminf hfSeq_meas)
    (ae_le_liminf_of_forall_ae_le μ h_lower)

/-- Helper for Theorem 4.21: transporting `liminf` through addition of a finite real constant in
`EReal`. -/
private theorem liminf_const_add_real_ereal (u : ℕ → EReal) (c : ℝ) :
    liminf (fun n ↦ (c : EReal) + u n) atTop = (c : EReal) + liminf u atTop := by
  -- The finite constant sequence supplies the upper/lower side conditions in the `EReal` liminf
  -- inequalities, so we get equality by squeezing.
  apply le_antisymm
  · simpa [Function.comp_def, Filter.limsup_const] using
      (EReal.liminf_add_le (u := fun _ : ℕ ↦ (c : EReal)) (v := u) (f := atTop)
        (Or.inl (by simp)) (Or.inl (by simp)))
  · simpa [Filter.liminf_const] using
      (EReal.le_liminf_add (u := fun _ : ℕ ↦ (c : EReal)) (v := u) (f := atTop))

/-- Helper for Theorem 4.21: coercion from `ENNReal` to `EReal` commutes with `liminf`. -/
private theorem coe_ereal_liminf_ennreal (a : ℕ → ENNReal) :
    liminf (fun n ↦ ((a n : ENNReal) : EReal)) atTop = ((liminf a atTop : ENNReal) : EReal) := by
  -- The coercion `ENNReal → EReal` is continuous and monotone, so it preserves `liminf`.
  simpa [Function.comp_def] using
    (Monotone.map_liminf_of_continuousAt (F := atTop)
      (fun _ _ h ↦ by exact_mod_cast h) a continuous_coe_ennreal_ereal.continuousAt).symm

/-- Helper for Theorem 4.21: `toENNReal` commutes with `liminf` on `EReal`. -/
private theorem liminf_toENNReal (u : ℕ → EReal) :
    liminf (fun n ↦ (u n).toENNReal) atTop = (liminf u atTop).toENNReal := by
  -- The map `EReal.toENNReal` is continuous and monotone, so it preserves `liminf`.
  simpa [Function.comp_def] using
    (Monotone.map_liminf_of_continuousAt (F := atTop)
      (fun _ _ h ↦ EReal.toENNReal_le_toENNReal h) u
      (ContinuousAt.ereal_toENNReal (f := fun x : EReal ↦ x) continuousAt_id)).symm

/-- Helper for Theorem 4.21: pointwise, the positive/negative-part bookkeeping for a lower bounded
pair `x ≤ y` matches the nonnegative gap `y - x`. -/
private theorem gap_balance_real (x y : ℝ) (hxy : x ≤ y) :
    ENNReal.ofReal y + ENNReal.ofReal (-x) =
      ((y : EReal) - x).toENNReal + (ENNReal.ofReal x + ENNReal.ofReal (-y)) := by
  -- Rewrite the `ENNReal` equality in `EReal`, where it becomes the usual decomposition into
  -- positive and negative parts of a real.
  apply EReal.coe_ennreal_eq_coe_ennreal_iff.mp
  simp [EReal.coe_toENNReal_eq_max]
  have hy' : max y 0 - max (-y) 0 = y := by
    have hy0 := max_zero_sub_eq_self y
    simpa [max_comm] using hy0
  have hx' : max x 0 - max (-x) 0 = x := by
    have hx0 := max_zero_sub_eq_self x
    simpa [max_comm] using hx0
  have hreal :
      max y 0 + max (-x) 0 = max 0 (y - x) + (max x 0 + max (-y) 0) := by
    rw [max_eq_right (sub_nonneg.mpr hxy)]
    linarith
  have hrealE :
      (((max y 0 + max (-x) 0 : ℝ) : EReal)) =
        ((max 0 (y - x) + (max x 0 + max (-y) 0) : ℝ) : EReal) := by
    exact_mod_cast hreal
  simpa [EReal.coe_add, add_assoc] using hrealE

/-- Helper for Theorem 4.21: the positive/negative-part balance identity extends from reals to
`EReal`. -/
private theorem gap_balance (x y : EReal) (hxy : x ≤ y) :
    y.toENNReal + (-x).toENNReal = (y - x).toENNReal + (x.toENNReal + (-y).toENNReal) := by
  -- All non-real cases collapse by simplification; the real case is the previous lemma.
  cases x <;> cases y <;> simp at hxy ⊢
  exact gap_balance_real _ _ hxy

/-- Helper for Theorem 4.21: the lower-bounded gap sequence has the expected `liminf` after
subtracting the a.e.-finite lower bound. -/
private theorem liminf_gap_toENNReal_ae
    (μ : Measure Ω) {f : Ω → EReal} {fSeq : ℕ → Ω → EReal}
    (hf : erealIntegrable f μ)
    (h_lower : ∀ n, f ≤ᵐ[μ] fSeq n) :
    ∀ᵐ ω ∂μ,
      liminf (fun n ↦ (fSeq n ω - f ω).toENNReal) atTop =
        (liminf (fun n ↦ fSeq n ω) atTop - f ω).toENNReal := by
  -- The pointwise lower bound is available simultaneously for all indices almost everywhere.
  have h_all : ∀ᵐ ω ∂μ, ∀ n, f ω ≤ fSeq n ω := by
    rw [ae_all_iff]
    exact h_lower
  -- Integrability makes the lower bound finite almost everywhere, so we may lift it to a real.
  have h_fin_pos : ∀ᵐ ω ∂μ, (f ω).toENNReal < ∞ := by
    exact ae_lt_top (hf.1.ereal_toENNReal) (by
      simpa [hasFiniteIntegral_def] using hf.hasFiniteIntegral_toENNReal.ne)
  have h_fin_neg : ∀ᵐ ω ∂μ, (-f ω).toENNReal < ∞ := by
    exact ae_lt_top ((hf.1.neg).ereal_toENNReal) (by
      simpa [hasFiniteIntegral_def] using hf.hasFiniteIntegral_neg_toENNReal.ne)
  filter_upwards [h_all, h_fin_pos, h_fin_neg] with ω hω hpos hneg
  have hne_top : f ω ≠ ⊤ := by
    intro htop
    simp [htop] at hpos
  have hne_bot : f ω ≠ ⊥ := by
    intro hbot
    simp [hbot] at hneg
  lift f ω to ℝ using ⟨hne_top, hne_bot⟩ with r hr
  have hmain :
      liminf (fun n ↦ (fSeq n ω - (r : EReal)).toENNReal) atTop =
        (liminf (fun n ↦ fSeq n ω) atTop - (r : EReal)).toENNReal := by
    -- First move `liminf` through `toENNReal`, then through subtraction of the finite real `r`.
    calc
      liminf (fun n ↦ (fSeq n ω - (r : EReal)).toENNReal) atTop
          = (liminf (fun n ↦ fSeq n ω - (r : EReal)) atTop).toENNReal := by
              exact liminf_toENNReal _
      _ = (liminf (fun n ↦ fSeq n ω) atTop - (r : EReal)).toENNReal := by
        rw [show (fun n ↦ fSeq n ω - (r : EReal)) =
            fun n ↦ ((-r : ℝ) : EReal) + fSeq n ω by
              funext n
              rw [sub_eq_add_neg, EReal.coe_neg, add_comm]]
        rw [liminf_const_add_real_ereal (u := fun n ↦ fSeq n ω) (-r)]
        simp [sub_eq_add_neg, EReal.coe_neg, add_comm]
  simpa [hr] using hmain

/-- Helper for Theorem 4.21: subtracting a finite real from an `EReal` is unchanged after adding
the same finite real to both sides. -/
private theorem ereal_alg_aux (c d : ℝ) :
    (c : EReal) - ((d : ℝ) + (c : ℝ)) = (-d : EReal) := by
  -- This is the `EReal` cancellation identity `c - (c + d) = -d`, with the inner sum reordered.
  simpa [add_comm] using (EReal.sub_add_cancel_left (a := (d : EReal)) (b := c))

/-- Helper for Theorem 4.21: shift a subtraction by a finite real constant on both sides. -/
private theorem ereal_sub_shift (A : EReal) (c d : ℝ) :
    A - d = (A + c) - (d + c) := by
  -- Expand the right-hand side and collapse the inner finite subtraction.
  rw [add_sub_assoc, ereal_alg_aux, sub_eq_add_neg]

/-- Helper for Theorem 4.21: shift the right-hand subtraction past a finite translated term. -/
private theorem ereal_sub_shift_right (F : EReal) (c d : ℝ) :
    (F + d) - (d + c) = F - c := by
  -- This is the previous shift identity, read from right to left with `c` and `d` swapped.
  simpa [add_comm] using (ereal_sub_shift (A := F) (c := d) (d := c)).symm

/-- Helper for Theorem 4.21: subtracting the lifted real `c : NNReal` agrees with subtracting the
corresponding finite `ENNReal` cast in `EReal`. -/
private theorem ereal_sub_right_of_lifted_nnreal
    (A : EReal) (c : NNReal) (a : ENNReal) (hc : (c : ENNReal) = a) :
    A - (c : ℝ) = A - (a : EReal) := by
  -- Rewrite the lifted real constant as the same finite value viewed through `ENNReal`.
  rw [← hc, EReal.coe_nnreal_eq_coe_real]

/-- Helper for Theorem 4.21: rewriting the textbook extended-real integral using the integrable
lower bound plus the nonnegative gap integral. -/
private theorem erealIntegral_eq_add_gap_of_ae_le
    (μ : Measure Ω) {f g : Ω → EReal}
    (hf : erealIntegrable f μ) (hg_meas : Measurable g) (hfg : f ≤ᵐ[μ] g) :
    erealIntegral g μ (erealIntegralDefined_of_ae_le hf hg_meas hfg) =
      erealIntegral f μ hf.defined + ((∫⁻ ω, (g ω - f ω).toENNReal ∂μ) : EReal) := by
  have hf_neg_meas : Measurable (fun ω ↦ (-f ω).toENNReal) := (hf.1.neg).ereal_toENNReal
  have hg_neg_meas : Measurable (fun ω ↦ (-g ω).toENNReal) := (hg_meas.neg).ereal_toENNReal
  have hgap_meas : Measurable (fun ω ↦ (g ω - f ω).toENNReal) := (hg_meas.sub hf.1).ereal_toENNReal
  have hg_neg_fin : ∫⁻ ω, (-g ω).toENNReal ∂μ ≠ ∞ := by
    -- The negative part of `g` is controlled by the negative part of the integrable lower bound `f`.
    refine ne_top_of_le_ne_top
      (by simpa [hasFiniteIntegral_def] using hf.hasFiniteIntegral_neg_toENNReal.ne) ?_
    exact lintegral_mono_ae (hfg.mono fun ω hω ↦ EReal.toENNReal_le_toENNReal <| by
      simpa using EReal.neg_le_neg_iff.2 hω)
  have h_balance_ae :
      (fun ω ↦ (g ω).toENNReal + (-f ω).toENNReal) =ᵐ[μ]
        fun ω ↦ (g ω - f ω).toENNReal + ((f ω).toENNReal + (-g ω).toENNReal) := by
    -- The pointwise balance identity is valid wherever the lower bound `f ≤ g` holds.
    exact hfg.mono fun ω hω ↦ gap_balance (x := f ω) (y := g ω) hω
  have h_balance_int :
      (∫⁻ ω, (g ω).toENNReal ∂μ) + ∫⁻ ω, (-f ω).toENNReal ∂μ =
        (∫⁻ ω, (g ω - f ω).toENNReal ∂μ) +
          ((∫⁻ ω, (f ω).toENNReal ∂μ) + ∫⁻ ω, (-g ω).toENNReal ∂μ) := by
    -- Integrate the pointwise balance identity and separate the resulting nonnegative sums.
    calc
      (∫⁻ ω, (g ω).toENNReal ∂μ) + ∫⁻ ω, (-f ω).toENNReal ∂μ
          = ∫⁻ ω, (g ω).toENNReal + (-f ω).toENNReal ∂μ := by
              symm
              exact lintegral_add_right _ hf_neg_meas
      _ = ∫⁻ ω, (g ω - f ω).toENNReal + ((f ω).toENNReal + (-g ω).toENNReal) ∂μ := by
            exact lintegral_congr_ae h_balance_ae
      _ = (∫⁻ ω, (g ω - f ω).toENNReal ∂μ) +
            ∫⁻ ω, (f ω).toENNReal + (-g ω).toENNReal ∂μ := by
            exact lintegral_add_left hgap_meas _
      _ = (∫⁻ ω, (g ω - f ω).toENNReal ∂μ) +
            ((∫⁻ ω, (f ω).toENNReal ∂μ) + ∫⁻ ω, (-g ω).toENNReal ∂μ) := by
            rw [lintegral_add_right _ hg_neg_meas]
  rw [erealIntegral_spec, erealIntegral_spec]
  have hC_ne_top : ∫⁻ ω, (-f ω).toENNReal ∂μ ≠ ∞ := by
    simpa [hasFiniteIntegral_def] using hf.hasFiniteIntegral_neg_toENNReal.ne
  lift (∫⁻ ω, (-f ω).toENNReal ∂μ) to NNReal using hC_ne_top with c hc
  lift (∫⁻ ω, (-g ω).toENNReal ∂μ) to NNReal using hg_neg_fin with d hd
  have h_balance_EReal :
      ((∫⁻ ω, (g ω).toENNReal ∂μ : ENNReal) : EReal) + (c : ℝ) =
        ((∫⁻ ω, (g ω - f ω).toENNReal ∂μ : ENNReal) : EReal) +
          (((∫⁻ ω, (f ω).toENNReal ∂μ : ENNReal) : EReal) + (d : ℝ)) := by
    -- Coercing the ENNReal equality to EReal turns the finite negative-part integrals into real
    -- constants.
    simpa [EReal.coe_ennreal_add, add_assoc] using
      congrArg (fun t : ENNReal => (t : EReal)) h_balance_int
  -- Move the finite negative-part constants to the right and recover the textbook integral of `f`.
  calc
    (((∫⁻ ω, (g ω).toENNReal ∂μ : ENNReal) : EReal) - (d : ℝ))
        = ((((∫⁻ ω, (g ω).toENNReal ∂μ : ENNReal) : EReal) + (c : ℝ)) - ((d : ℝ) + (c : ℝ))) := by
            simpa using ereal_sub_shift
              (((∫⁻ ω, (g ω).toENNReal ∂μ : ENNReal) : EReal)) (c : ℝ) (d : ℝ)
    _ = (((∫⁻ ω, (g ω - f ω).toENNReal ∂μ : ENNReal) : EReal) +
          ((((∫⁻ ω, (f ω).toENNReal ∂μ : ENNReal) : EReal) + (d : ℝ))) - ((d : ℝ) + (c : ℝ))) := by
            rw [h_balance_EReal]
    _ = (((∫⁻ ω, (g ω - f ω).toENNReal ∂μ : ENNReal) : EReal) +
          ((((∫⁻ ω, (f ω).toENNReal ∂μ : ENNReal) : EReal) - (c : ℝ)))) := by
            rw [add_sub_assoc, ereal_sub_shift_right]
    _ = ((((∫⁻ ω, (f ω).toENNReal ∂μ : ENNReal) : EReal) - (c : ℝ)) +
          (((∫⁻ ω, (g ω - f ω).toENNReal ∂μ : ENNReal) : EReal))) := by
            rw [add_comm]

-- Proof sketch: subtract the integrable lower bound `f` to reduce to the nonnegative sequence
-- `fSeq n - f`, apply mathlib's nonnegative Fatou lemma to the measurable positive parts, and then
-- translate the resulting inequality back through the textbook definition of the extended-real
-- integral as the difference of the lower integrals of the positive and negative parts.
/-- Theorem 4.21: Fatou's lemma for extended-real integrals. If `f ∈ ℒ¹(μ)` and each measurable
`f_n` is bounded below almost everywhere by `f`, then the textbook extended-real integral of the
pointwise `liminf` is at most the `liminf` of the corresponding extended-real integrals of
`f_n`. -/
theorem erealIntegral_liminf_le_liminf_erealIntegral
    (μ : Measure Ω) {f : Ω → EReal} {fSeq : ℕ → Ω → EReal}
    (hf : erealIntegrable f μ)
    (hfSeq_meas : ∀ n, Measurable (fSeq n)) (h_lower : ∀ n, f ≤ᵐ[μ] fSeq n) :
    erealIntegral (fun ω ↦ liminf (fun n ↦ fSeq n ω) atTop) μ
        (erealIntegralDefined_liminf μ hf hfSeq_meas h_lower) ≤
      liminf
        (fun n ↦ erealIntegral (fSeq n) μ
          (erealIntegralDefined_of_ae_le hf (hfSeq_meas n) (h_lower n)))
        atTop := by
  let gap : ℕ → Ω → ENNReal := fun n ω ↦ (fSeq n ω - f ω).toENNReal
  let limf : Ω → EReal := fun ω ↦ liminf (fun n ↦ fSeq n ω) atTop
  have hgap_meas : ∀ n, Measurable (gap n) := by
    -- Each gap is measurable because it is the `toENNReal` of a measurable `EReal` difference.
    intro n
    exact (hfSeq_meas n).sub hf.1 |>.ereal_toENNReal
  have hfatou_gap := MeasureTheory.lintegral_liminf_le (μ := μ) hgap_meas
  have hgap_liminf :
      ∫⁻ ω, liminf (fun n ↦ gap n ω) atTop ∂μ =
        ∫⁻ ω, (limf ω - f ω).toENNReal ∂μ := by
    -- The gap sequence has the expected pointwise liminf almost everywhere.
    refine lintegral_congr_ae ?_
    simpa [gap, limf] using liminf_gap_toENNReal_ae μ hf h_lower
  have hlim_lower : f ≤ᵐ[μ] limf := ae_le_liminf_of_forall_ae_le μ h_lower
  have hlim_bridge :
      erealIntegral limf μ (erealIntegralDefined_liminf μ hf hfSeq_meas h_lower) =
        erealIntegral f μ hf.defined + ((∫⁻ ω, (limf ω - f ω).toENNReal ∂μ) : EReal) := by
    -- Rewrite the integral of the liminf as the integral of the lower bound plus the nonnegative
    -- gap above that lower bound.
    simpa [limf] using
      erealIntegral_eq_add_gap_of_ae_le μ hf (Measurable.liminf hfSeq_meas) hlim_lower
  have hseq_bridge :
      ∀ n,
        erealIntegral (fSeq n) μ (erealIntegralDefined_of_ae_le hf (hfSeq_meas n) (h_lower n)) =
          erealIntegral f μ hf.defined + ((∫⁻ ω, gap n ω ∂μ) : EReal) := by
    -- Each sequence term has the same lower-bound-plus-gap decomposition.
    intro n
    simpa [gap] using
      erealIntegral_eq_add_gap_of_ae_le μ hf (hfSeq_meas n) (h_lower n)
  have hpos_fin : ∫⁻ ω, (f ω).toENNReal ∂μ ≠ ∞ := by
    simpa [hasFiniteIntegral_def] using hf.hasFiniteIntegral_toENNReal.ne
  have hneg_fin : ∫⁻ ω, (-f ω).toENNReal ∂μ ≠ ∞ := by
    simpa [hasFiniteIntegral_def] using hf.hasFiniteIntegral_neg_toENNReal.ne
  lift (∫⁻ ω, (f ω).toENNReal ∂μ) to NNReal using hpos_fin with p hp
  lift (∫⁻ ω, (-f ω).toENNReal ∂μ) to NNReal using hneg_fin with q hq
  have hf_const :
      erealIntegral f μ hf.defined = (((p : ℝ) - (q : ℝ)) : EReal) := by
    -- Integrability makes both positive and negative parts finite, so the textbook integral is a
    -- genuine real constant.
    rw [erealIntegral_spec, ← hp, ← hq]
    rfl
  have hconst_liminf (c : ℝ) (a : ℕ → ENNReal) :
      liminf (fun n ↦ (c : EReal) + ((a n : ENNReal) : EReal)) atTop =
        (c : EReal) + ((liminf a atTop : ENNReal) : EReal) := by
    -- First move `liminf` across addition of the finite real constant, then across the coercion
    -- `ENNReal → EReal`.
    rw [liminf_const_add_real_ereal]
    rw [coe_ereal_liminf_ennreal]
  have hseq_bridge_const :
      ∀ n,
        ((((p : ℝ) - (q : ℝ)) : EReal) + ((∫⁻ ω, gap n ω ∂μ : ENNReal) : EReal)) =
          erealIntegral (fSeq n) μ
            (erealIntegralDefined_of_ae_le hf (hfSeq_meas n) (h_lower n)) := by
    -- Rewrite the fixed lower-bound integral to the explicit finite real constant once and for all.
    intro n
    simpa only [hf_const] using (hseq_bridge n).symm
  -- Put the liminf integral into the lower-bound-plus-gap form.
  have hfatou_gap_EReal :
      ((∫⁻ ω, liminf (fun n ↦ gap n ω) atTop ∂μ : ENNReal) : EReal) ≤
        ((liminf (fun n ↦ ∫⁻ ω, gap n ω ∂μ) atTop : ENNReal) : EReal) := by
    exact_mod_cast hfatou_gap
  calc
    erealIntegral limf μ (erealIntegralDefined_liminf μ hf hfSeq_meas h_lower)
        = (((p : ℝ) - (q : ℝ)) : EReal) +
            ((∫⁻ ω, (limf ω - f ω).toENNReal ∂μ : ENNReal) : EReal) := by
              rw [hlim_bridge, hf_const]
    _ = (((p : ℝ) - (q : ℝ)) : EReal) +
          ((∫⁻ ω, liminf (fun n ↦ gap n ω) atTop ∂μ : ENNReal) : EReal) := by
            rw [hgap_liminf]
    _ ≤ (((p : ℝ) - (q : ℝ)) : EReal) +
          ((liminf (fun n ↦ ∫⁻ ω, gap n ω ∂μ) atTop : ENNReal) : EReal) := by
            -- Apply the nonnegative Fatou inequality to the gap sequence and add back the finite
            -- lower-bound integral.
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hfatou_gap_EReal ((((p : ℝ) - (q : ℝ)) : EReal))
    _ = liminf
          (fun n ↦ (((p : ℝ) - (q : ℝ)) : EReal) +
            ((∫⁻ ω, gap n ω ∂μ : ENNReal) : EReal)) atTop := by
              symm
              exact hconst_liminf (((p : ℝ) - (q : ℝ))) (fun n ↦ ∫⁻ ω, gap n ω ∂μ)
    _ = liminf
          (fun n ↦ erealIntegral (fSeq n) μ
            (erealIntegralDefined_of_ae_le hf (hfSeq_meas n) (h_lower n))) atTop := by
              exact Filter.liminf_congr <|
                Filter.Eventually.of_forall hseq_bridge_const
