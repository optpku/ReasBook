/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped Topology
open scoped Interval

section Chap03
section Section06

/-- Helper for Theorem 3.6: uniform convergence on `Set.Icc` gives a uniform bound on `Set.uIoc`. -/
lemma helperForTheorem_3_6_eventually_norm_sub_le_on_uIoc
    {a b : ℝ} (hab : a < b) {fseq : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h_unif : TendstoUniformlyOn fseq f Filter.atTop (Set.Icc a b)) :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop, ∀ x ∈ Set.uIoc a b, ‖fseq n x - f x‖ ≤ ε := by
  intro ε hε
  have h := (Metric.tendstoUniformlyOn_iff).1 h_unif ε hε
  refine h.mono ?_
  intro n hn x hx
  have hx' : x ∈ Set.Icc a b := by
    have hx'' : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hx
    simpa [Set.uIcc_of_lt hab] using hx''
  have hdist : dist (f x) (fseq n x) < ε := hn x hx'
  have hdist' : ‖fseq n x - f x‖ < ε := by
    simpa [dist_eq_norm, norm_sub_rev] using hdist
  exact le_of_lt hdist'

/-- Helper for Theorem 3.6: almost everywhere pointwise convergence on `Set.uIoc`. -/
lemma helperForTheorem_3_6_ae_tendsto_on_uIoc
    {a b : ℝ} (hab : a < b) {fseq : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h_unif : TendstoUniformlyOn fseq f Filter.atTop (Set.Icc a b)) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      Filter.Tendsto (fun n => fseq n x) Filter.atTop (𝓝 (f x)) := by
  have hforall :
      ∀ x ∈ Set.uIoc a b, Filter.Tendsto (fun n => fseq n x) Filter.atTop (𝓝 (f x)) := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      have hx'' : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hx
      simpa [Set.uIcc_of_lt hab] using hx''
    exact h_unif.tendsto_at hx'
  exact
    MeasureTheory.ae_restrict_of_forall_mem (μ := MeasureTheory.volume) (s := Set.uIoc a b)
      measurableSet_uIoc hforall

/-- Helper for Theorem 3.6: the uniform limit is interval integrable. -/
lemma helperForTheorem_3_6_intervalIntegrable_limit
    {a b : ℝ} (hab : a < b) {fseq : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h_integrable : ∀ n, IntervalIntegrable (fseq n) (μ := MeasureTheory.volume) a b)
    (h_unif : TendstoUniformlyOn fseq f Filter.atTop (Set.Icc a b)) :
    IntervalIntegrable f (μ := MeasureTheory.volume) a b := by
  have h_ae_tendsto :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
        Filter.Tendsto (fun n => fseq n x) Filter.atTop (𝓝 (f x)) :=
    helperForTheorem_3_6_ae_tendsto_on_uIoc hab h_unif
  have h_aesm :
      MeasureTheory.AEStronglyMeasurable f
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
      (f := fun n x => fseq n x) (g := f)
      (hf := fun n => (h_integrable n).def'.aestronglyMeasurable) h_ae_tendsto
  have h_eventually :
      ∀ᶠ n in Filter.atTop, ∀ x ∈ Set.uIoc a b, ‖fseq n x - f x‖ ≤ (1 : ℝ) :=
    helperForTheorem_3_6_eventually_norm_sub_le_on_uIoc hab h_unif 1 (by norm_num)
  rcases (Filter.eventually_atTop.mp h_eventually) with ⟨N, hN⟩
  have hN' : ∀ x ∈ Set.uIoc a b, ‖fseq N x - f x‖ ≤ (1 : ℝ) := by
    intro x hx
    exact hN N (le_rfl) x hx
  have hbound : ∀ x ∈ Set.uIoc a b, ‖f x‖ ≤ ‖fseq N x‖ + 1 := by
    intro x hx
    have hdiff : ‖fseq N x - f x‖ ≤ (1 : ℝ) := hN' x hx
    have hdiff' : ‖f x - fseq N x‖ ≤ (1 : ℝ) := by
      simpa [norm_sub_rev] using hdiff
    have htriangle : ‖f x‖ ≤ ‖f x - fseq N x‖ + ‖fseq N x‖ := by
      have h := norm_add_le (f x - fseq N x) (fseq N x)
      simpa [sub_add_cancel] using h
    have hsum : ‖f x - fseq N x‖ + ‖fseq N x‖ ≤ (1 : ℝ) + ‖fseq N x‖ :=
      add_le_add_left hdiff' _
    calc
      ‖f x‖ ≤ ‖f x - fseq N x‖ + ‖fseq N x‖ := htriangle
      _ ≤ (1 : ℝ) + ‖fseq N x‖ := hsum
      _ = ‖fseq N x‖ + 1 := by simp [add_comm]
  have hbound_ae :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
        ‖f x‖ ≤ ‖fseq N x‖ + 1 :=
    MeasureTheory.ae_restrict_of_forall_mem (μ := MeasureTheory.volume) (s := Set.uIoc a b)
      measurableSet_uIoc hbound
  have h_intN :
      MeasureTheory.Integrable (fseq N)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    (h_integrable N).def'
  have h_int_norm :
      MeasureTheory.Integrable (fun x => ‖fseq N x‖)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    h_intN.norm
  have h_vol_ne_top : MeasureTheory.volume (Set.uIoc a b) ≠ ⊤ := by
    have hlt : MeasureTheory.volume (Set.uIoc a b) < ⊤ := by
      have hle : a ≤ b := le_of_lt hab
      simp [Set.uIoc_of_le hle]
    exact ne_of_lt hlt
  have h_const :
      MeasureTheory.Integrable (fun _ => (1 : ℝ))
        (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    have h_const_on :
        MeasureTheory.IntegrableOn (fun _ => (1 : ℝ)) (Set.uIoc a b)
          (MeasureTheory.volume) :=
      MeasureTheory.integrableOn_const (μ := MeasureTheory.volume) (s := Set.uIoc a b)
        (C := (1 : ℝ)) h_vol_ne_top
    simpa [MeasureTheory.IntegrableOn] using h_const_on
  have h_dom :
      MeasureTheory.Integrable (fun x => ‖fseq N x‖ + 1)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    simpa using h_int_norm.add h_const
  have h_int_f :
      MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    MeasureTheory.Integrable.mono' h_dom h_aesm hbound_ae
  have h_int_on :
      MeasureTheory.IntegrableOn f (Set.uIoc a b) (MeasureTheory.volume) :=
    h_int_f
  exact (intervalIntegrable_iff (μ := MeasureTheory.volume) (a := a) (b := b) (f := f)).2 h_int_on

/-- Helper for Theorem 3.6: convergence of interval integrals under uniform convergence. -/
lemma helperForTheorem_3_6_tendsto_intervalIntegral
    {a b : ℝ} (hab : a < b) {fseq : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h_integrable : ∀ n, IntervalIntegrable (fseq n) (μ := MeasureTheory.volume) a b)
    (h_unif : TendstoUniformlyOn fseq f Filter.atTop (Set.Icc a b))
    (hf_int : IntervalIntegrable f (μ := MeasureTheory.volume) a b) :
    Filter.Tendsto (fun n => ∫ x in a..b, fseq n x) Filter.atTop
      (𝓝 (∫ x in a..b, f x)) := by
  refine (Metric.tendsto_atTop.mpr ?_)
  intro ε hε
  have hpos : 0 < |b - a| := by
    have hne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
    exact (abs_pos).2 hne
  set δ : ℝ := (ε / 2) / |b - a|
  have hδpos : 0 < δ := by
    have hε2 : 0 < ε / 2 := half_pos hε
    simpa [δ] using (div_pos hε2 hpos)
  have h_eventually :
      ∀ᶠ n in Filter.atTop, ∀ x ∈ Set.uIoc a b, ‖fseq n x - f x‖ ≤ δ :=
    helperForTheorem_3_6_eventually_norm_sub_le_on_uIoc hab h_unif δ hδpos
  rcases (Filter.eventually_atTop.mp h_eventually) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hbound_n : ∀ x ∈ Set.uIoc a b, ‖fseq n x - f x‖ ≤ δ := by
    intro x hx
    exact hN n hn x hx
  have h_norm_le :
      ‖∫ x in a..b, fseq n x - f x‖ ≤ δ * |b - a| := by
    simpa using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
        (f := fun x => fseq n x - f x) hbound_n)
  have hsub :
      ∫ x in a..b, fseq n x - f x =
        (∫ x in a..b, fseq n x) - (∫ x in a..b, f x) := by
    simpa using
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := a) (b := b)
        (f := fseq n) (g := f) (hf := h_integrable n) (hg := hf_int))
  have hdist_le :
      dist (∫ x in a..b, fseq n x) (∫ x in a..b, f x) ≤ δ * |b - a| := by
    calc
      dist (∫ x in a..b, fseq n x) (∫ x in a..b, f x)
          = ‖(∫ x in a..b, fseq n x) - (∫ x in a..b, f x)‖ := by
              simp [dist_eq_norm]
      _ = ‖∫ x in a..b, fseq n x - f x‖ := by
              simp [hsub]
      _ ≤ δ * |b - a| := h_norm_le
  have hmul : δ * |b - a| = ε / 2 := by
    dsimp [δ]
    calc
      (ε / 2) / |b - a| * |b - a| = (ε / 2) * |b - a| / |b - a| := by
        simp [div_mul_eq_mul_div]
      _ = ε / 2 := by
        have hne : |b - a| ≠ 0 := ne_of_gt hpos
        simpa using (mul_div_cancel_right₀ (ε / 2) hne)
  have hdist_le' :
      dist (∫ x in a..b, fseq n x) (∫ x in a..b, f x) ≤ ε / 2 := by
    simpa [hmul] using hdist_le
  have hdist_lt :
      dist (∫ x in a..b, fseq n x) (∫ x in a..b, f x) < ε := by
    exact lt_of_le_of_lt hdist_le' (half_lt_self hε)
  simpa using hdist_lt

/-- Theorem 3.6: Let `a < b` be real numbers. For each integer `n ≥ 1`, let
`f^{(n)} : [a,b] → ℝ` be Riemann integrable, and assume that `f^{(n)} → f` uniformly
on `[a,b]`. Then `f` is Riemann integrable and
`lim_{n→∞} ∫_{[a,b]} f^{(n)} = ∫_{[a,b]} f`. -/
theorem uniformLimit_intervalIntegral
    {a b : ℝ} (_hab : a < b) {fseq : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h_integrable : ∀ n, IntervalIntegrable (fseq n) (μ := MeasureTheory.volume) a b)
    (h_unif : TendstoUniformlyOn fseq f Filter.atTop (Set.Icc a b)) :
    IntervalIntegrable f (μ := MeasureTheory.volume) a b ∧
      Filter.Tendsto (fun n => ∫ x in a..b, fseq n x) Filter.atTop
        (𝓝 (∫ x in a..b, f x)) := by
  have hab : a < b := _hab
  have hf_int :
      IntervalIntegrable f (μ := MeasureTheory.volume) a b :=
    helperForTheorem_3_6_intervalIntegrable_limit hab h_integrable h_unif
  have htend :
      Filter.Tendsto (fun n => ∫ x in a..b, fseq n x) Filter.atTop
        (𝓝 (∫ x in a..b, f x)) :=
    helperForTheorem_3_6_tendsto_intervalIntegral hab h_integrable h_unif hf_int
  exact And.intro hf_int htend

/-- Theorem 3.7: [Interchange of limit and integral under uniform convergence]
Let `[a,b]` be a compact interval in `ℝ`. If `f^{(n)}` are Riemann-integrable on `[a,b]`
and converge uniformly to `f` on `[a,b]`, then `f` is Riemann-integrable and
`lim_{n→∞} ∫_a^b f^{(n)} = ∫_a^b f`. -/
theorem uniformLimit_intervalIntegral_interchange
    {a b : ℝ} (_hab : a ≤ b) {fseq : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h_integrable : ∀ n, IntervalIntegrable (fseq n) (μ := MeasureTheory.volume) a b)
    (h_unif : TendstoUniformlyOn fseq f Filter.atTop (Set.Icc a b)) :
    IntervalIntegrable f (μ := MeasureTheory.volume) a b ∧
      Filter.Tendsto (fun n => ∫ x in a..b, fseq n x) Filter.atTop
        (𝓝 (∫ x in a..b, f x)) := by
  rcases lt_or_eq_of_le _hab with hablt | hEq
  · simpa using
      (uniformLimit_intervalIntegral (a := a) (b := b) hablt h_integrable h_unif)
  · subst hEq
    have hf_int :
        IntervalIntegrable f (μ := MeasureTheory.volume) a a := by
      simp [IntervalIntegrable]
    have htend :
        Filter.Tendsto (fun n => ∫ x in a..a, fseq n x) Filter.atTop
          (𝓝 (∫ x in a..a, f x)) := by
      simp
    exact And.intro hf_int htend

/-- Helper for Theorem 3.8: partial sums are interval integrable. -/
lemma helperForTheorem_3_8_intervalIntegrable_partialSums
    {a b : ℝ} {fseq : ℕ → ℝ → ℝ}
    (h_integrable : ∀ n, IntervalIntegrable (fseq n) (μ := MeasureTheory.volume) a b) :
    ∀ n,
      IntervalIntegrable
        (fun x => (Finset.range n).sum (fun i => fseq i x))
        (μ := MeasureTheory.volume) a b := by
  intro n
  have h :
      ∀ i ∈ Finset.range n,
        IntervalIntegrable (fseq i) (μ := MeasureTheory.volume) a b := by
    intro i _hi
    exact h_integrable i
  have hsum :
      IntervalIntegrable (∑ i ∈ Finset.range n, fseq i)
        (μ := MeasureTheory.volume) a b :=
    IntervalIntegrable.sum (s := Finset.range n) (f := fseq) h
  simpa [Finset.sum_fn] using hsum

/-- Helper for Theorem 3.8: interval integral of a partial sum is the sum of integrals. -/
lemma helperForTheorem_3_8_intervalIntegral_partialSums
    {a b : ℝ} {fseq : ℕ → ℝ → ℝ}
    (h_integrable : ∀ n, IntervalIntegrable (fseq n) (μ := MeasureTheory.volume) a b) :
    ∀ n,
      (∫ x in a..b, (Finset.range n).sum (fun i => fseq i x)) =
        (Finset.range n).sum (fun i => ∫ x in a..b, fseq i x) := by
  intro n
  have h :
      ∀ i ∈ Finset.range n,
        IntervalIntegrable (fseq i) (μ := MeasureTheory.volume) a b := by
    intro i _hi
    exact h_integrable i
  have hsum :
      (∫ x in a..b, ∑ i ∈ Finset.range n, fseq i x) =
        ∑ i ∈ Finset.range n, ∫ x in a..b, fseq i x := by
    simpa using
      (intervalIntegral.integral_finset_sum (μ := MeasureTheory.volume) (a := a) (b := b)
        (s := Finset.range n) (f := fseq) h)
  simpa using hsum

/-- Helper for Theorem 3.8: rewrite `Tendsto` after identifying two sequences. -/
lemma helperForTheorem_3_8_tendsto_integral_partials
    {a b : ℝ} {fseq : ℕ → ℝ → ℝ} {s : ℝ → ℝ} {partials : ℕ → ℝ → ℝ}
    (hrewrite :
      ∀ n,
        (∫ x in a..b, partials n x) =
          (Finset.range n).sum (fun i => ∫ x in a..b, fseq i x))
    (htend :
      Filter.Tendsto (fun n => ∫ x in a..b, partials n x) Filter.atTop
        (𝓝 (∫ x in a..b, s x))) :
    Filter.Tendsto
      (fun n => (Finset.range n).sum (fun i => ∫ x in a..b, fseq i x))
      Filter.atTop (𝓝 (∫ x in a..b, s x)) := by
  have hrewrite' :
      (fun n => ∫ x in a..b, partials n x) =
        (fun n => (Finset.range n).sum (fun i => ∫ x in a..b, fseq i x)) := by
    funext n
    exact hrewrite n
  simpa [hrewrite'] using htend

/-- Helper for Theorem 3.8: convert `Tendsto` of range partial sums to conditional `HasSum`. -/
lemma helperForTheorem_3_8_hasSumConditional_of_tendsto_range
    {g : ℕ → ℝ} {L : ℝ}
    (h :
      Filter.Tendsto (fun n => (Finset.range n).sum g) Filter.atTop (𝓝 L)) :
    HasSum g L (L := SummationFilter.conditional ℕ) := by
  unfold HasSum
  have h' :
      Filter.Tendsto
        ((fun s : Finset ℕ => ∑ b ∈ s, g b) ∘ Finset.range)
        Filter.atTop (𝓝 L) := by
    simpa [Function.comp] using h
  have h'' :
      Filter.Tendsto (fun s : Finset ℕ => ∑ b ∈ s, g b)
        (Filter.map Finset.range Filter.atTop) (𝓝 L) :=
    (Filter.tendsto_map' h')
  rw [SummationFilter.conditional_filter_eq_map_range]
  exact h''

/-- Helper for Theorem 3.8: conditional summation of integrals from uniform convergence. -/
lemma helperForTheorem_3_8_intervalIntegral_hasSumConditional
    {a b : ℝ} (hab : a < b) {fseq : ℕ → ℝ → ℝ} {s : ℝ → ℝ}
    (h_integrable : ∀ n, IntervalIntegrable (fseq n) (μ := MeasureTheory.volume) a b)
    (h_unif :
      TendstoUniformlyOn
        (fun n x => (Finset.range n).sum (fun i => fseq i x))
        s Filter.atTop (Set.Icc a b)) :
    IntervalIntegrable s (μ := MeasureTheory.volume) a b ∧
      HasSum (fun n => ∫ x in a..b, fseq n x) (∫ x in a..b, s x)
        (L := SummationFilter.conditional ℕ) := by
  set partials : ℕ → ℝ → ℝ := fun n x => (Finset.range n).sum (fun i => fseq i x)
  have hpartials_int :
      ∀ n, IntervalIntegrable (partials n) (μ := MeasureTheory.volume) a b := by
    intro n
    have h :=
      helperForTheorem_3_8_intervalIntegrable_partialSums
        (a := a) (b := b) (fseq := fseq) h_integrable n
    simpa [partials] using h
  have h_unif' :
      TendstoUniformlyOn partials s Filter.atTop (Set.Icc a b) := by
    simpa [partials] using h_unif
  have hmain :=
    uniformLimit_intervalIntegral (a := a) (b := b) hab hpartials_int h_unif'
  rcases hmain with ⟨hs_int, htend⟩
  have htend' :
      Filter.Tendsto
        (fun n => (Finset.range n).sum (fun i => ∫ x in a..b, fseq i x))
        Filter.atTop (𝓝 (∫ x in a..b, s x)) := by
    have hrewrite :
        ∀ n,
          (∫ x in a..b, partials n x) =
            (Finset.range n).sum (fun i => ∫ x in a..b, fseq i x) := by
      intro n
      have h :=
        helperForTheorem_3_8_intervalIntegral_partialSums
          (a := a) (b := b) (fseq := fseq) h_integrable n
      simpa [partials] using h
    exact
      helperForTheorem_3_8_tendsto_integral_partials
        (a := a) (b := b) (fseq := fseq) (s := s) (partials := partials)
        hrewrite htend
  have h_hasSum_conditional :
      HasSum (fun n => ∫ x in a..b, fseq n x) (∫ x in a..b, s x)
        (L := SummationFilter.conditional ℕ) := by
    exact helperForTheorem_3_8_hasSumConditional_of_tendsto_range htend'
  exact And.intro hs_int h_hasSum_conditional

/-- Helper for Theorem 3.8: upgrade conditional `HasSum` to unconditional under unconditional
summability. -/
lemma helperForTheorem_3_8_hasSum_of_summable_unconditional
    {f : ℕ → ℝ} {L : ℝ}
    (h_cond : HasSum f L (L := SummationFilter.conditional ℕ))
    (h_summable : Summable f) :
    HasSum f L := by
  have htsum_cond :
      (∑'[SummationFilter.conditional ℕ] n, f n) = L := h_cond.tsum_eq
  have htsum_eq :
      (∑'[SummationFilter.conditional ℕ] n, f n) = (∑' n, f n) := by
    simpa using
      (tsum_eq_of_summable_unconditional
        (L := SummationFilter.conditional ℕ) (f := f) h_summable)
  have hsum_uncond : (∑' n, f n) = L := by
    calc
      (∑' n, f n) = (∑'[SummationFilter.conditional ℕ] n, f n) := by
        simpa using htsum_eq.symm
      _ = L := htsum_cond
  have h_hasSum_uncond : HasSum f (∑' n, f n) := Summable.hasSum (f := f) h_summable
  simpa [hsum_uncond] using h_hasSum_uncond

/-- Theorem 3.8: Let `a < b` and let `f^{(n)}` be Riemann-integrable on `[a,b]`.
Assume the series `∑ f^{(n)}(x)` converges uniformly on `[a,b]` to `s(x)`. Then `s`
is Riemann-integrable on `[a,b]` and
`∫_{[a,b]} s = ∑_{n=1}^∞ ∫_{[a,b]} f^{(n)}`. -/
theorem uniformSeries_intervalIntegral
    {a b : ℝ} (hab : a < b) {fseq : ℕ → ℝ → ℝ} {s : ℝ → ℝ}
    (h_integrable : ∀ n, IntervalIntegrable (fseq n) (μ := MeasureTheory.volume) a b)
    (h_unif :
      TendstoUniformlyOn
        (fun n x => (Finset.range n).sum (fun i => fseq i x))
        s Filter.atTop (Set.Icc a b)) :
    IntervalIntegrable s (μ := MeasureTheory.volume) a b ∧
      HasSum (fun n => ∫ x in a..b, fseq n x) (∫ x in a..b, s x)
        (L := SummationFilter.conditional ℕ) := by
  exact
    helperForTheorem_3_8_intervalIntegral_hasSumConditional
      (a := a) (b := b) hab h_integrable h_unif

/-- Helper for Example 3.6.3 : the series `∑ r^n / n` sums to `-log(1-r)` for `0 < r < 1`. -/
lemma helperForExample_3_6_3_hasSum_power_div
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasSum (fun n : ℕ ↦ r ^ n / n) (-Real.log (1 - r)) := by
  have hr_norm : ‖(r : ℂ)‖ < 1 := by
    simpa [RCLike.norm_ofReal, abs_of_pos hr0] using hr1
  have hcomplex :
      HasSum (fun n : ℕ ↦ (r : ℂ) ^ n / n) (-Complex.log (1 - (r : ℂ))) :=
    Complex.hasSum_taylorSeries_neg_log (z := (r : ℂ)) hr_norm
  have hpos : 0 ≤ 1 - r := (sub_pos.mpr hr1).le
  have hlog : Complex.log (1 - (r : ℂ)) = ((Real.log (1 - r) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log (x := (1 - r)) hpos).symm
  have hlog' :
      -Complex.log (1 - (r : ℂ)) = ((-Real.log (1 - r) : ℝ) : ℂ) := by
    calc
      -Complex.log (1 - (r : ℂ)) = -((Real.log (1 - r) : ℝ) : ℂ) := by
        rw [hlog]
      _ = ((-Real.log (1 - r) : ℝ) : ℂ) := by simp
  have hcomplex' :
      HasSum (fun n : ℕ ↦ ((r ^ n / n : ℝ) : ℂ))
        ((-Real.log (1 - r) : ℝ) : ℂ) := by
    simpa [hlog'] using hcomplex
  exact (Complex.hasSum_ofReal).1 hcomplex'

/-- Helper for Example 3.6.3 : shift the index in `∑ r^n / n`. -/
lemma helperForExample_3_6_3_tsum_shift_pow_div
    {r : ℝ} (h : Summable (fun n : ℕ ↦ r ^ n / n)) :
    (∑' n : ℕ, r ^ (n + 1) / (n + 1)) = ∑' n : ℕ, r ^ n / n := by
  have hsum := (Summable.sum_add_tsum_nat_add 1 h)
  simpa [Finset.sum_range_one] using hsum

/-- Example 3.6.3 : For every real number `r` with `0 < r < 1`, the identity
`-log(1-r) = ∑_{n=0}^∞ r^{n+1}/(n+1)` holds. -/
theorem log_one_sub_eq_tsum_power_div
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    -Real.log (1 - r) = ∑' n : ℕ, r ^ (n + 1) / (n + 1) := by
  have hsum : HasSum (fun n : ℕ ↦ r ^ n / n) (-Real.log (1 - r)) :=
    helperForExample_3_6_3_hasSum_power_div (r := r) hr0 hr1
  have hshift :
      (∑' n : ℕ, r ^ (n + 1) / (n + 1)) = ∑' n : ℕ, r ^ n / n :=
    helperForExample_3_6_3_tsum_shift_pow_div (r := r) hsum.summable
  calc
    -Real.log (1 - r) = ∑' n : ℕ, r ^ n / n := by
      simpa using hsum.tsum_eq.symm
    _ = ∑' n : ℕ, r ^ (n + 1) / (n + 1) := by
      simpa using hshift.symm

end Section06
end Chap03
