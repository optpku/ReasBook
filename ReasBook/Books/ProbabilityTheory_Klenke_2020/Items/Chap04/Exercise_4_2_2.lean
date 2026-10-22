/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Helper for Exercise 4.2.2: an almost-everywhere limit of nonnegative functions is
nonnegative almost everywhere. -/
lemma ae_nonneg_limit
    {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hfSeq_nonneg : ∀ n, 0 ≤ᵐ[μ] fSeq n)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ fSeq n x) atTop (𝓝 (f x))) :
    0 ≤ᵐ[μ] f := by
  -- Put all pointwise nonnegativity facts on one full-measure set before passing to the limit.
  have h_nonneg_all : ∀ᵐ x ∂μ, ∀ n, 0 ≤ fSeq n x := by
    rw [ae_all_iff]
    intro n
    exact hfSeq_nonneg n
  -- Closedness of `[0, ∞)` lets the pointwise limit remain nonnegative.
  filter_upwards [h_nonneg_all, h_tendsto] with x hx_nonneg hx_tendsto
  exact isClosed_Ici.mem_of_tendsto hx_tendsto (Filter.Eventually.of_forall hx_nonneg)

/-- Helper for Exercise 4.2.2: Fatou's lemma gives finiteness of
`∫⁻ x, ENNReal.ofReal (f x) ∂μ` from the convergence of the nonnegative integrals of `fSeq n`. -/
lemma lintegral_ofReal_limit_ne_top
    {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ} {I : ℝ}
    (hfSeq_int : ∀ n, Integrable (fSeq n) μ)
    (hfSeq_nonneg : ∀ n, 0 ≤ᵐ[μ] fSeq n)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ fSeq n x) atTop (𝓝 (f x)))
    (h_integral_tendsto : Tendsto (fun n ↦ ∫ x, fSeq n x ∂μ) atTop (𝓝 I)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤ := by
  -- Fatou compares the lower integral of the limit with the liminf of the lower integrals.
  have h_fatou :
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
        liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (fSeq n x) ∂μ) atTop := by
    calc
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ =
          ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (fSeq n x)) atTop ∂μ := by
            refine lintegral_congr_ae ?_
            filter_upwards [h_tendsto] with x hx
            exact ((ENNReal.continuous_ofReal.tendsto (f x)).comp hx).liminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (fSeq n x) ∂μ) atTop := by
        refine MeasureTheory.lintegral_liminf_le' ?_
        intro n
        exact (hfSeq_int n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  -- The assumed real convergence gives an eventual finite upper bound on the lower integrals.
  have h_eventually_bound_real :
      ∀ᶠ n in atTop, ∫ x, fSeq n x ∂μ ≤ |I| + 1 := by
    filter_upwards [h_integral_tendsto.eventually (Metric.ball_mem_nhds I zero_lt_one)] with n hn
    have h_triangle :
        |∫ x, fSeq n x ∂μ| ≤ |∫ x, fSeq n x ∂μ - I| + |I| := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (abs_add_le (∫ x, fSeq n x ∂μ - I) I)
    exact le_of_lt <| calc
      ∫ x, fSeq n x ∂μ ≤ |∫ x, fSeq n x ∂μ| := le_abs_self _
      _ ≤ |∫ x, fSeq n x ∂μ - I| + |I| := h_triangle
      _ < 1 + |I| := by
        simpa [Real.dist_eq] using add_lt_add_right hn |I|
      _ = |I| + 1 := by ring
  have h_eventually_bound_lintegral :
      ∀ᶠ n in atTop, ∫⁻ x, ENNReal.ofReal (fSeq n x) ∂μ ≤ ENNReal.ofReal (|I| + 1) := by
    filter_upwards [h_eventually_bound_real] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal (hfSeq_int n) (hfSeq_nonneg n)]
    exact ENNReal.ofReal_le_ofReal hn
  have h_liminf_ne_top :
      liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (fSeq n x) ∂μ) atTop ≠ ⊤ := by
    have h_liminf_le :
        liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (fSeq n x) ∂μ) atTop ≤ ENNReal.ofReal (|I| + 1) :=
      Filter.liminf_le_of_frequently_le' h_eventually_bound_lintegral.frequently
    exact ne_top_of_le_ne_top (b := ENNReal.ofReal (|I| + 1)) ENNReal.ofReal_ne_top h_liminf_le
  exact ne_top_of_le_ne_top h_liminf_ne_top h_fatou

/-- Helper for Exercise 4.2.2: the dominated convergence theorem applies to
`x ↦ min (fSeq n x) (f x)`. -/
lemma tendsto_integral_min
    {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hfSeq_int : ∀ n, Integrable (fSeq n) μ)
    (hfSeq_nonneg : ∀ n, 0 ≤ᵐ[μ] fSeq n)
    (hf_nonneg : 0 ≤ᵐ[μ] f)
    (hf_int : Integrable f μ)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ fSeq n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ ∫ x, min (fSeq n x) (f x) ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  -- The pointwise `min` tends to `f` because the second argument is already the limit.
  have h_min_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ min (fSeq n x) (f x)) atTop (𝓝 (f x)) := by
    filter_upwards [h_tendsto] with x hx
    have h_const : Tendsto (fun _ : ℕ ↦ f x) atTop (𝓝 (f x)) := tendsto_const_nhds
    simpa using Tendsto.min hx h_const
  -- The nonnegative limit `f` dominates `min (fSeq n) f`.
  have h_min_bound : ∀ n, ∀ᵐ x ∂μ, ‖min (fSeq n x) (f x)‖ ≤ f x := by
    intro n
    filter_upwards [hfSeq_nonneg n, hf_nonneg] with x hxSeq hxF
    have h_min_nonneg : 0 ≤ min (fSeq n x) (f x) := le_min hxSeq hxF
    rw [Real.norm_of_nonneg h_min_nonneg]
    exact min_le_right _ _
  -- Dominated convergence now yields convergence of the integrals of the minima.
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    f
    (fun n ↦
      ((hfSeq_int n).aestronglyMeasurable.aemeasurable.min
        hf_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
    hf_int
    h_min_bound
    h_min_tendsto

/-- Helper for Exercise 4.2.2: for nonnegative real numbers, `|a - b|` can be rewritten using
`min a b`. -/
lemma abs_sub_eq_add_sub_two_mul_min {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    |a - b| = a + b - 2 * min a b := by
  -- Rewrite `|a - b|` as `max a b - min a b` and then replace `max a b` by `a + b - min a b`.
  have hmax : max a b = a + b - min a b := by
    linarith [min_add_max a b]
  calc
    |a - b| = max a b - min a b := by
      simpa using (max_sub_min_eq_abs' a b).symm
    _ = (a + b - min a b) - min a b := by rw [hmax]
    _ = a + b - 2 * min a b := by ring

-- Proof sketch: apply Fatou's lemma to the nonnegative functions `f - min (f_n) f` and
-- `f_n - min (f_n) f` to identify the limit of the integrals of `min (f_n) f`, deduce that `f`
-- is integrable from the assumed convergence of `∫ f_n`, and then rewrite `‖f_n - f‖` using the
-- decomposition through `min (f_n) f`.
/-- Exercise 4.2.2: if nonnegative integrable functions `f_n` converge almost everywhere to a
function `f` and the integrals `∫ f_n dμ` converge to `I`, then `f` is integrable and the
`L¹`-distance to `f` has limit `I - ∫ f dμ`. -/
theorem scheffe_of_nonnegative_ae_tendsto
    {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ} {I : ℝ}
    (hfSeq_int : ∀ n, Integrable (fSeq n) μ)
    (hfSeq_nonneg : ∀ n, 0 ≤ᵐ[μ] fSeq n)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ fSeq n x) atTop (𝓝 (f x)))
    (h_integral_tendsto : Tendsto (fun n ↦ ∫ x, fSeq n x ∂μ) atTop (𝓝 I)) :
    Integrable f μ ∧
      Tendsto (fun n ↦ ∫ x, ‖fSeq n x - f x‖ ∂μ) atTop
        (𝓝 (I - ∫ x, f x ∂μ)) := by
  -- Recover the two structural facts about the almost-everywhere limit `f`.
  have hf_aestrong : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (hfSeq_int n).aestronglyMeasurable) h_tendsto
  have hf_nonneg : 0 ≤ᵐ[μ] f := ae_nonneg_limit hfSeq_nonneg h_tendsto
  -- Fatou upgrades the a.e. limit to an integrable function.
  have hf_lintegral_ne_top :
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤ :=
    lintegral_ofReal_limit_ne_top hfSeq_int hfSeq_nonneg h_tendsto h_integral_tendsto
  have hf_int : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf_aestrong hf_nonneg).1 hf_lintegral_ne_top
  -- Dominated convergence identifies the limit of the integrals of `min (fSeq n) f`.
  have h_integral_min_tendsto :
      Tendsto (fun n ↦ ∫ x, min (fSeq n x) (f x) ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
    tendsto_integral_min hfSeq_int hfSeq_nonneg hf_nonneg hf_int h_tendsto
  -- Rewrite the `L¹`-distance using the scalar identity `|a-b| = a + b - 2 * min a b`.
  have h_integral_abs_eq :
      ∀ n, ∫ x, ‖fSeq n x - f x‖ ∂μ =
        ∫ x, fSeq n x ∂μ + ∫ x, f x ∂μ - 2 * ∫ x, min (fSeq n x) (f x) ∂μ := by
    intro n
    have h_min_int : Integrable (fun x ↦ min (fSeq n x) (f x)) μ := by
      refine Integrable.mono_nonneg hf_int
        (((hfSeq_int n).aestronglyMeasurable.aemeasurable.min
          hf_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable) ?_ ?_
      · filter_upwards [hfSeq_nonneg n, hf_nonneg] with x hxSeq hxF
        exact le_min hxSeq hxF
      · exact Filter.Eventually.of_forall fun x ↦ min_le_right _ _
    have h_pointwise :
        (fun x ↦ ‖fSeq n x - f x‖) =ᵐ[μ]
          fun x ↦ fSeq n x + f x - 2 * min (fSeq n x) (f x) := by
      filter_upwards [hfSeq_nonneg n, hf_nonneg] with x hxSeq hxF
      rw [Real.norm_eq_abs, abs_sub_eq_add_sub_two_mul_min hxSeq hxF]
    calc
      ∫ x, ‖fSeq n x - f x‖ ∂μ = ∫ x, (fSeq n x + f x - 2 * min (fSeq n x) (f x)) ∂μ := by
        exact integral_congr_ae h_pointwise
      _ = ∫ x, (fSeq n x + f x) ∂μ - ∫ x, 2 * min (fSeq n x) (f x) ∂μ := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (integral_sub ((hfSeq_int n).add hf_int) (h_min_int.const_mul 2) :
            ∫ x, (fSeq n x + f x) - 2 * min (fSeq n x) (f x) ∂μ =
              ∫ x, (fSeq n x + f x) ∂μ - ∫ x, 2 * min (fSeq n x) (f x) ∂μ)
      _ = ∫ x, fSeq n x ∂μ + ∫ x, f x ∂μ - ∫ x, 2 * min (fSeq n x) (f x) ∂μ := by
        rw [integral_add (hfSeq_int n) hf_int]
      _ = ∫ x, fSeq n x ∂μ + ∫ x, f x ∂μ - 2 * ∫ x, min (fSeq n x) (f x) ∂μ := by
        rw [integral_const_mul]
  let Φ : ℝ × ℝ → ℝ := fun z ↦ z.1 + ∫ x, f x ∂μ - 2 * z.2
  -- The final limit is just the image of the pair of convergent integral sequences under `Φ`.
  have h_rhs_tendsto :
      Tendsto
        (fun n ↦ ∫ x, fSeq n x ∂μ + ∫ x, f x ∂μ - 2 * ∫ x, min (fSeq n x) (f x) ∂μ)
        atTop
        (𝓝 (I + ∫ x, f x ∂μ - 2 * ∫ x, f x ∂μ)) := by
    have h_pair :
        Tendsto (fun n ↦ (∫ x, fSeq n x ∂μ, ∫ x, min (fSeq n x) (f x) ∂μ)) atTop
          (𝓝 (I, ∫ x, f x ∂μ)) := by
      simpa [nhds_prod_eq] using h_integral_tendsto.prodMk h_integral_min_tendsto
    have hΦ_cont : Continuous Φ := by
      continuity
    simpa [Φ] using (hΦ_cont.tendsto (I, ∫ x, f x ∂μ)).comp h_pair
  have h_abs_tendsto :
      Tendsto (fun n ↦ ∫ x, ‖fSeq n x - f x‖ ∂μ) atTop
        (𝓝 (I + ∫ x, f x ∂μ - 2 * ∫ x, f x ∂μ)) := by
    have h_seq_eq :
        (fun n ↦ ∫ x, ‖fSeq n x - f x‖ ∂μ) =
          fun n ↦ ∫ x, fSeq n x ∂μ + ∫ x, f x ∂μ - 2 * ∫ x, min (fSeq n x) (f x) ∂μ := by
      funext n
      exact h_integral_abs_eq n
    exact h_seq_eq ▸ h_rhs_tendsto
  have h_limit_eq : I + ∫ x, f x ∂μ - 2 * ∫ x, f x ∂μ = I - ∫ x, f x ∂μ := by
    ring
  exact ⟨hf_int, h_limit_eq ▸ h_abs_tendsto⟩
