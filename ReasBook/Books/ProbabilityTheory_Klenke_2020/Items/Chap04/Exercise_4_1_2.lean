/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]

/-- Helper for Exercise 4.1.2: if `1 ≤ p' < p < ∞`, then one can choose a real exponent `β`
strictly between the reciprocal thresholds `1 / p.toReal` and `1 / p'.toReal`. -/
lemma existsSeparatingExponent {p' p : ENNReal}
    (hp' : 1 ≤ p') (hpp : p' < p) (hp_ne_top : p ≠ ⊤) :
    ∃ β : ℝ, 1 < β * p.toReal ∧ β * p'.toReal < 1 := by
  have hp'_ne_top : p' ≠ ⊤ := by
    intro hp'_eq_top
    simpa [hp'_eq_top] using hpp
  have hp'_ne_zero : p' ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp')
  have hp_ne_zero : p ≠ 0 := ne_of_gt ((lt_of_lt_of_le zero_lt_one hp').trans hpp)
  have hp'_toReal_pos : 0 < p'.toReal := ENNReal.toReal_pos hp'_ne_zero hp'_ne_top
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have htoReal : p'.toReal < p.toReal :=
    (ENNReal.toReal_lt_toReal hp'_ne_top hp_ne_top).2 hpp
  have hrecip : 1 / p.toReal < 1 / p'.toReal :=
    one_div_lt_one_div_of_lt hp'_toReal_pos htoReal
  refine ⟨((1 / p.toReal) + (1 / p'.toReal)) / 2, ?_, ?_⟩
  · -- The midpoint lies strictly above `1 / p.toReal`, so multiplying by `p.toReal` gives the
    -- lower threshold `1 < β * p.toReal`.
    field_simp [hp_toReal_pos.ne', hp'_toReal_pos.ne']
    nlinarith
  · -- The same midpoint lies strictly below `1 / p'.toReal`, so multiplying by `p'.toReal` gives
    -- the upper threshold `β * p'.toReal < 1`.
    field_simp [hp_toReal_pos.ne', hp'_toReal_pos.ne']
    nlinarith

/-- Helper for Exercise 4.1.2: a sigma-finite non-finite measure has a strict subsequence of
`spanningSets μ` whose successive finite-measure increments all have mass greater than `1`. -/
lemma existsLargeBlockSubsequence (hμ : ¬ IsFiniteMeasure μ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      1 < μ (spanningSets μ (ψ 0)) ∧
      (∀ n, μ (spanningSets μ (ψ n)) + 1 < μ (spanningSets μ (ψ (n + 1)))) := by
  have huniv : μ Set.univ = (⊤ : ENNReal) := by
    simpa [not_isFiniteMeasure_iff] using hμ
  have hlarge : ∀ r : ENNReal, r < (⊤ : ENNReal) → ∃ n, r < μ (spanningSets μ n) := by
    intro r hr
    have hr_univ : r < μ Set.univ := by simpa [huniv] using hr
    rw [← Measure.iSup_restrict_spanningSets (μ := μ) Set.univ] at hr_univ
    rw [lt_iSup_iff] at hr_univ
    rcases hr_univ with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [Measure.restrict_apply, measurableSet_spanningSets, Set.inter_univ] using hn
  have hnext :
      ∀ N : ℕ, ∃ n, N < n ∧ μ (spanningSets μ N) + 1 < μ (spanningSets μ n) := by
    intro N
    have htarget : μ (spanningSets μ N) + 1 < (⊤ : ENNReal) := by
      exact ENNReal.add_lt_top.2 ⟨measure_spanningSets_lt_top μ N, by simp⟩
    rcases hlarge (μ (spanningSets μ N) + 1) htarget with ⟨n, hn⟩
    have hgt : N < n := by
      by_contra hnot
      have hle : n ≤ N := Nat.not_lt.mp hnot
      have hmono : μ (spanningSets μ n) ≤ μ (spanningSets μ N) :=
        measure_mono (monotone_spanningSets μ hle)
      exact (not_lt_of_ge (hmono.trans (le_add_of_nonneg_right bot_le))) hn
    exact ⟨n, hgt, hn⟩
  choose φ hφgt hφmeasure using hnext
  let ψ : ℕ → ℕ := Nat.rec (φ 0) fun _ m => φ m
  have hψsucc : ∀ n, ψ n < ψ (n + 1) := by
    intro n
    -- Each recursive step applies the precomputed jump map `φ`, so the indices strictly increase.
    simpa [ψ] using hφgt (ψ n)
  have hψmono : StrictMono ψ := strictMono_nat_of_lt_succ hψsucc
  have hψzero_aux : μ (spanningSets μ 0) + 1 < μ (spanningSets μ (ψ 0)) := by
    -- The initial index already satisfies the same `+1` growth requirement.
    simpa [ψ] using hφmeasure 0
  have hψzero : 1 < μ (spanningSets μ (ψ 0)) := by
    -- Since measures are nonnegative, the initial `+1` jump already puts the first chosen set
    -- above mass `1`.
    have hbase : (1 : ENNReal) ≤ μ (spanningSets μ 0) + 1 := by
      simpa [add_comm] using
        (le_add_of_nonneg_left (show 0 ≤ μ (spanningSets μ 0) by exact bot_le) :
          (1 : ENNReal) ≤ μ (spanningSets μ 0) + 1)
    exact lt_of_le_of_lt hbase hψzero_aux
  refine ⟨ψ, hψmono, hψzero, ?_⟩
  intro n
  -- Reapplying the same jump estimate at the previously chosen index gives the inductive step.
  simpa [ψ] using hφmeasure (ψ n)

/-- Helper for Exercise 4.1.2: from the large-growth subsequence of `spanningSets μ`, one gets an
increasing measurable exhaustion whose disjoint blocks all have measure strictly larger than `1`
and still finite. -/
lemma existsLargeBlockExhaustion (hμ : ¬ IsFiniteMeasure μ) :
    ∃ F : ℕ → Set Ω, Monotone F ∧
      (∀ n, MeasurableSet (F n)) ∧
      ((⋃ n, F n) = Set.univ) ∧
      Pairwise (fun i j ↦ Disjoint (disjointed F i) (disjointed F j)) ∧
      (∀ n, 1 < μ (disjointed F n)) ∧
      (∀ n, μ (disjointed F n) < ⊤) := by
  obtain ⟨ψ, hψmono, hψzero, hψstep⟩ := existsLargeBlockSubsequence (μ := μ) hμ
  let F : ℕ → Set Ω := fun n ↦ spanningSets μ (ψ n)
  have hFmono : Monotone F := by
    intro m n hmn
    exact monotone_spanningSets μ (hψmono.monotone hmn)
  have hFmeas : ∀ n, MeasurableSet (F n) := by
    intro n
    simpa [F] using measurableSet_spanningSets (μ := μ) (i := ψ n)
  have hFuniv : (⋃ n, F n) = Set.univ := by
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      rw [← iUnion_spanningSets (μ := μ)] at hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      exact (monotone_spanningSets μ (hψmono.id_le n)) hn
  have hFpairwise : Pairwise (fun i j ↦ Disjoint (disjointed F i) (disjointed F j)) :=
    disjoint_disjointed F
  have hFfinite : ∀ n, μ (disjointed F n) < ⊤ := by
    intro n
    have htop : μ (F n) < ⊤ := by
      simpa [F] using measure_spanningSets_lt_top μ (ψ n)
    exact (measure_mono (disjointed_subset F n)).trans_lt htop
  have hFlarge : ∀ n, 1 < μ (disjointed F n) := by
    intro n
    cases n with
    | zero =>
        -- The first disjoint block is the first chosen spanning set itself.
        simpa [F] using hψzero
    | succ n =>
        have hdisj : Disjoint (disjointed F (n + 1)) (F n) := by
          rw [show disjointed F n.succ = F n.succ \ F n by
            simpa using hFmono.disjointed_succ (i := n) (by exact not_isMax n)]
          refine Set.disjoint_left.2 ?_
          intro x hx hx'
          exact hx.2 hx'
        have hsplit : μ (F (n + 1)) = μ (disjointed F (n + 1)) + μ (F n) := by
          -- Splitting the next exhaustion stage into its new disjoint block and the previous stage
          -- turns the growth estimate into a lower bound on the block measure.
          have hsup : disjointed F (n + 1) ∪ F n = F (n + 1) := by
            simpa [Nat.succ_eq_add_one] using hFmono.disjointed_succ_sup n
          rw [← hsup, measure_union hdisj (hFmeas n)]
        have hstep : μ (F n) + 1 < μ (F (n + 1)) := by
          simpa [F] using hψstep n
        have hnot_le : ¬ μ (disjointed F (n + 1)) ≤ 1 := by
          intro hle
          have : μ (F (n + 1)) ≤ μ (F n) + 1 := by
            calc
              μ (F (n + 1)) = μ (disjointed F (n + 1)) + μ (F n) := hsplit
              _ ≤ μ (F n) + 1 := by
                simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hle (μ (F n))
          exact (not_lt_of_ge this) hstep
        exact lt_of_not_ge hnot_le
  exact ⟨F, hFmono, hFmeas, hFuniv, hFpairwise, hFlarge, hFfinite⟩

/-- Helper for Exercise 4.1.2: a measurable exhaustion of `Ω` yields a measurable index map whose
fibers are exactly the disjoint blocks `disjointed F n`. -/
lemma existsMeasurableIndexOfExhaustion (F : ℕ → Set Ω)
    (hFmeas : ∀ n, MeasurableSet (F n)) (hFuniv : (⋃ n, F n) = Set.univ) :
    ∃ K : Ω → ℕ, Measurable K ∧ ∀ n : ℕ, K ⁻¹' {n} = disjointed F n := by
  classical
  have hcover : ∀ x, ∃ n, x ∈ F n := by
    intro x
    have hx : x ∈ ⋃ n, F n := by simpa [hFuniv]
    simpa using Set.mem_iUnion.mp hx
  refine ⟨fun x ↦ Nat.find (hcover x), measurable_find hcover hFmeas, ?_⟩
  intro n
  -- The chosen minimal index has singleton fibers equal to the disjointed partition pieces.
  simpa [hcover] using (preimage_find_eq_disjointed F hcover n)

/-- Helper for Exercise 4.1.2: integrating a nonnegative function that only depends on a measurable
Nat-valued index reduces to a weighted countable sum over its singleton fibers. -/
lemma lintegral_comp_index_eq_tsum (B : ℕ → Set Ω) (K : Ω → ℕ)
    (hKmeas : Measurable K) (hKfib : ∀ n : ℕ, Set.preimage K {n} = B n) (w : ℕ → ENNReal) :
    ∫⁻ x, w (K x) ∂μ = ∑' n, μ (B n) * w n := by
  -- First move the integral to the pushforward measure on `ℕ`, then expand it over singletons.
  erw [lintegral_comp measurable_from_nat hKmeas]
  rw [lintegral_countable']
  congr with n
  rw [Measure.map_apply hKmeas (by simp), hKfib n, mul_comm]

-- Proof sketch: decompose the sigma-finite non-finite measure into countably many measurable
-- pieces of positive finite measure, then choose coefficients so that the resulting simple
-- function has finite `p`-seminorm but infinite `p'`-seminorm. The canonical `Lp` formulation is
-- a witness in the `AEEqFun`-based `L^p` space whose class does not belong to `L^{p'}`; the
-- textbook raw-function statement is the immediate representative-level corollary.
/-- Exercise 4.1.2, canonical `Lp`-space form: if `1 ≤ p' < p ≤ ∞` and `μ` is sigma-finite but not
finite, then there exists an `L^p(μ)` class that does not belong to `L^{p'}(μ)`. -/
theorem exists_mem_Lp_not_mem_Lp_of_sigmaFinite_not_isFiniteMeasure {p' p : ENNReal}
    (hp' : 1 ≤ p') (hpp : p' < p) (hμ : ¬ IsFiniteMeasure μ) :
    ∃ f : Ω →ₘ[μ] ℝ, f ∈ Lp ℝ p μ ∧ f ∉ Lp ℝ p' μ := by
  by_cases hp_top : p = ⊤
  · have hp'_ne_top : p' ≠ ⊤ := by
      intro hp'_eq_top
      simpa [hp'_eq_top, hp_top] using hpp
    -- In the `p = ∞` branch, the constant function `1` is essentially bounded but not in
    -- `L^{p'}` because `μ` is not finite.
    let hOne : MemLp (fun _ : Ω ↦ (1 : ℝ)) ⊤ μ := memLp_top_const (μ := μ) (1 : ℝ)
    let fLp : Lp ℝ ⊤ μ := MemLp.toLp (fun _ : Ω ↦ (1 : ℝ)) hOne
    refine ⟨fLp, ?_, ?_⟩
    · simpa [hp_top] using fLp.2
    · intro hconst
      have hfinite : μ Set.univ < ⊤ := by
        have hconst_mem : MemLp (fun _ : Ω ↦ (1 : ℝ)) p' μ := by
          exact
            (memLp_congr_ae (MemLp.coeFn_toLp hOne)).1
              ((Lp.mem_Lp_iff_memLp).1 hconst)
        rcases (memLp_const_iff (p := p') (c := (1 : ℝ)) (by positivity) hp'_ne_top).1
            hconst_mem with hzero | hfinite
        · norm_num at hzero
        · exact hfinite
      exact hμ ((MeasureTheory.isFiniteMeasure_iff μ).2 hfinite)
  · have hp_ne_zero : p ≠ 0 := by
      exact ne_of_gt ((lt_of_lt_of_le zero_lt_one hp').trans hpp)
    have hp'_ne_zero : p' ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp')
    have hp'_ne_top : p' ≠ ⊤ := by
      intro hp'_eq_top
      simpa [hp'_eq_top] using hpp
    -- Route correction: the finite-`p` branch uses a weighted block function on a strict
    -- subsequence of `spanningSets μ`, rather than trying to sum directly in `Lp`.
    obtain ⟨β, hβp, hβp'⟩ := existsSeparatingExponent hp' hpp hp_top
    obtain ⟨F, hFmono, hFmeas, hFuniv, hFpairwise, hFlarge, hFfinite⟩ :=
      existsLargeBlockExhaustion (μ := μ) hμ
    let B : ℕ → Set Ω := disjointed F
    obtain ⟨K, hKmeas, hKfib⟩ := existsMeasurableIndexOfExhaustion (F := F) hFmeas hFuniv
    let blockMass : ℕ → ℝ := fun n ↦ (μ (B n)).toReal
    let coeff : ℕ → ℝ := fun n ↦ blockMass n ^ (-(1 / p.toReal)) * (n + 1 : ℝ) ^ (-β)
    let f : Ω → ℝ := fun x ↦ coeff (K x)
    have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    have hp'_toReal_pos : 0 < p'.toReal := ENNReal.toReal_pos hp'_ne_zero hp'_ne_top
    have hp'_toReal_lt : p'.toReal < p.toReal :=
      (ENNReal.toReal_lt_toReal hp'_ne_top hp_top).2 hpp
    have hratio_lt_one : p'.toReal / p.toReal < 1 := by
      exact (div_lt_one hp_toReal_pos).2 hp'_toReal_lt
    have hone_sub_pos : 0 < 1 - p'.toReal / p.toReal := by
      exact sub_pos.mpr hratio_lt_one
    have hblockMass_pos : ∀ n, 0 < blockMass n := by
      intro n
      exact ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one (hFlarge n))) (hFfinite n).ne
    have hblockMass_one_lt : ∀ n, 1 < blockMass n := by
      intro n
      exact (ENNReal.toReal_lt_toReal (by simp) (hFfinite n).ne).2 (hFlarge n)
    have hcoeff_nonneg : ∀ n, 0 ≤ coeff n := by
      intro n
      -- Both factors in the coefficient sequence are nonnegative real powers.
      positivity
    have hcoeff_rpow : ∀ q : ℝ, ∀ n,
        coeff n ^ q =
          blockMass n ^ (-(q / p.toReal)) * (n + 1 : ℝ) ^ (-(β * q)) := by
      intro q n
      calc
        coeff n ^ q
            = (blockMass n ^ (-(1 / p.toReal)) * (n + 1 : ℝ) ^ (-β)) ^ q := by
              rfl
        _ = (blockMass n ^ (-(1 / p.toReal))) ^ q * ((n + 1 : ℝ) ^ (-β)) ^ q := by
              rw [Real.mul_rpow (by positivity) (by positivity)]
        _ = blockMass n ^ (-(1 / p.toReal) * q) * (n + 1 : ℝ) ^ (-β * q) := by
              rw [← Real.rpow_mul (le_of_lt (hblockMass_pos n)),
                ← Real.rpow_mul (show 0 ≤ (n + 1 : ℝ) by positivity)]
        _ = blockMass n ^ (-(q / p.toReal)) * (n + 1 : ℝ) ^ (-(β * q)) := by
              congr 1 <;> ring
    have hcoeff_p : ∀ n : ℕ,
        coeff n ^ p.toReal =
          (blockMass n)⁻¹ * (n + 1 : ℝ) ^ (-(β * p.toReal)) := by
      intro n
      simpa [hcoeff_rpow, hp_toReal_pos.ne', Real.rpow_neg_one] using
        hcoeff_rpow p.toReal n
    have hterm_p : ∀ n : ℕ,
        μ (B n) * ENNReal.ofReal (coeff n ^ p.toReal) =
          ENNReal.ofReal ((n + 1 : ℝ) ^ (-(β * p.toReal))) := by
      intro n
      have hmass_eq : ENNReal.ofReal (blockMass n) = μ (B n) := by
        simp [blockMass, B, (hFfinite n).ne]
      -- The block-mass factor cancels exactly at exponent `p`.
      calc
        μ (B n) * ENNReal.ofReal (coeff n ^ p.toReal)
            = ENNReal.ofReal (blockMass n) * ENNReal.ofReal (coeff n ^ p.toReal) := by
                rw [hmass_eq]
        _ = ENNReal.ofReal (blockMass n * coeff n ^ p.toReal) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal ((n + 1 : ℝ) ^ (-(β * p.toReal))) := by
              rw [hcoeff_p n]
              have hcancel :
                  blockMass n * ((blockMass n)⁻¹ * (n + 1 : ℝ) ^ (-(β * p.toReal))) =
                    (n + 1 : ℝ) ^ (-(β * p.toReal)) := by
                rw [← mul_assoc, mul_inv_cancel₀ (hblockMass_pos n).ne', one_mul]
              exact congrArg ENNReal.ofReal hcancel
    have hf_meas : Measurable f := by
      simpa [f, Function.comp] using ((measurable_from_nat (f := coeff)).comp hKmeas)
    have hsummable_p :
        Summable (fun n : ℕ ↦ (n + 1 : ℝ) ^ (-(β * p.toReal))) := by
      have hs :=
        (Real.summable_one_div_nat_add_rpow 1 (β * p.toReal)).2 hβp
      refine hs.congr ?_
      intro n
      have hn_pos : 0 < (n : ℝ) + 1 := by positivity
      rw [Real.rpow_neg (le_of_lt hn_pos)]
      simp [one_div, abs_of_pos hn_pos]
    have hmem_f_p : MemLp f p μ := by
      refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_top]
      -- The integrand only depends on `K`, so the shared countable rewrite applies.
      have hnorm_p :
          ∀ x, ‖f x‖ₑ ^ p.toReal = ENNReal.ofReal (coeff (K x) ^ p.toReal) := by
        intro x
        have hnonneg : 0 ≤ coeff (K x) := hcoeff_nonneg (K x)
        calc
          ‖f x‖ₑ ^ p.toReal = (ENNReal.ofReal (coeff (K x))) ^ p.toReal := by
            rw [show f x = coeff (K x) by rfl, Real.enorm_eq_ofReal hnonneg]
          _ = ENNReal.ofReal (coeff (K x) ^ p.toReal) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hnonneg ENNReal.toReal_nonneg]
      calc
        ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ
            = ∫⁻ x, ENNReal.ofReal (coeff (K x) ^ p.toReal) ∂μ := by
                exact lintegral_congr_ae (Filter.Eventually.of_forall hnorm_p)
        _ = ∑' n, μ (B n) * ENNReal.ofReal (coeff n ^ p.toReal) := by
              simpa [f] using
                lintegral_comp_index_eq_tsum (B := B) (K := K) hKmeas hKfib
                  (fun n ↦ ENNReal.ofReal (coeff n ^ p.toReal))
        _ = ∑' n : ℕ, ENNReal.ofReal ((n + 1 : ℝ) ^ (-(β * p.toReal))) := by
              simp_rw [hterm_p]
        _ < ⊤ := hsummable_p.tsum_ofReal_lt_top
    have hnot_summable_p' :
        ¬ Summable (fun n : ℕ ↦ (n + 1 : ℝ) ^ (-(β * p'.toReal))) := by
      intro hs
      have hs' :
          Summable (fun n : ℕ ↦ 1 / |n + (1 : ℝ)| ^ (β * p'.toReal)) := by
        refine hs.congr ?_
        intro n
        have hn_pos : 0 < (n : ℝ) + 1 := by positivity
        rw [Real.rpow_neg (le_of_lt hn_pos)]
        simp [one_div, abs_of_pos hn_pos]
      have : 1 < β * p'.toReal :=
        (Real.summable_one_div_nat_add_rpow 1 (β * p'.toReal)).1 hs'
      linarith
    have hnot_mem_f_p' : ¬ MemLp f p' μ := by
      intro hf_p'
      have hcoeff_p' : ∀ n,
          coeff n ^ p'.toReal =
            blockMass n ^ (-(p'.toReal / p.toReal)) *
              (n + 1 : ℝ) ^ (-(β * p'.toReal)) := by
        intro n
        simpa [hcoeff_rpow] using hcoeff_rpow p'.toReal n
      have hterm_p' : ∀ n : ℕ,
          μ (B n) * ENNReal.ofReal (coeff n ^ p'.toReal) =
            ENNReal.ofReal
              (blockMass n ^ (1 - p'.toReal / p.toReal) *
                (n + 1 : ℝ) ^ (-(β * p'.toReal))) := by
        intro n
        have hmass_eq : ENNReal.ofReal (blockMass n) = μ (B n) := by
          simp [blockMass, B, (hFfinite n).ne]
        -- At exponent `p'`, one power of the block mass survives.
        calc
          μ (B n) * ENNReal.ofReal (coeff n ^ p'.toReal)
              = ENNReal.ofReal (blockMass n) * ENNReal.ofReal (coeff n ^ p'.toReal) := by
                  rw [hmass_eq]
          _ = ENNReal.ofReal (blockMass n * coeff n ^ p'.toReal) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal
                (blockMass n ^ (1 - p'.toReal / p.toReal) *
                  (n + 1 : ℝ) ^ (-(β * p'.toReal))) := by
                rw [hcoeff_p' n]
                have hfactor :
                    blockMass n * blockMass n ^ (-(p'.toReal / p.toReal)) =
                      blockMass n ^ (1 - p'.toReal / p.toReal) := by
                  calc
                    blockMass n * blockMass n ^ (-(p'.toReal / p.toReal))
                        = blockMass n ^ (1 : ℝ) * blockMass n ^ (-(p'.toReal / p.toReal)) := by
                            rw [Real.rpow_one]
                    _ = blockMass n ^ (1 - p'.toReal / p.toReal) := by
                          rw [← Real.rpow_add (hblockMass_pos n)]
                          ring
                calc
                  ENNReal.ofReal
                      (blockMass n *
                        (blockMass n ^ (-(p'.toReal / p.toReal)) *
                          (n + 1 : ℝ) ^ (-(β * p'.toReal))))
                      =
                        ENNReal.ofReal
                          ((blockMass n * blockMass n ^ (-(p'.toReal / p.toReal))) *
                            (n + 1 : ℝ) ^ (-(β * p'.toReal))) := by
                              rw [← mul_assoc]
                  _ = ENNReal.ofReal
                        (blockMass n ^ (1 - p'.toReal / p.toReal) *
                          (n + 1 : ℝ) ^ (-(β * p'.toReal))) := by
                              rw [hfactor]
      have hterm_p'_lower : ∀ n : ℕ,
          ENNReal.ofReal ((n + 1 : ℝ) ^ (-(β * p'.toReal))) ≤
            μ (B n) * ENNReal.ofReal (coeff n ^ p'.toReal) := by
        intro n
        rw [hterm_p' n]
        refine ENNReal.ofReal_le_ofReal ?_
        have hfactor_ge_one :
            1 ≤ blockMass n ^ (1 - p'.toReal / p.toReal) :=
          Real.one_le_rpow (le_of_lt (hblockMass_one_lt n)) hone_sub_pos.le
        exact le_mul_of_one_le_left (by positivity) hfactor_ge_one
      have hlintegral_p' :
          ∫⁻ x, ‖f x‖ₑ ^ p'.toReal ∂μ =
            ∑' n, μ (B n) * ENNReal.ofReal (coeff n ^ p'.toReal) := by
        -- The same fiberwise rewrite reduces the `p'`-power integral to a countable sum.
        have hnorm_p' :
            ∀ x, ‖f x‖ₑ ^ p'.toReal = ENNReal.ofReal (coeff (K x) ^ p'.toReal) := by
          intro x
          have hnonneg : 0 ≤ coeff (K x) := hcoeff_nonneg (K x)
          calc
            ‖f x‖ₑ ^ p'.toReal = (ENNReal.ofReal (coeff (K x))) ^ p'.toReal := by
              rw [show f x = coeff (K x) by rfl, Real.enorm_eq_ofReal hnonneg]
            _ = ENNReal.ofReal (coeff (K x) ^ p'.toReal) := by
              rw [ENNReal.ofReal_rpow_of_nonneg hnonneg ENNReal.toReal_nonneg]
        calc
          ∫⁻ x, ‖f x‖ₑ ^ p'.toReal ∂μ
              = ∫⁻ x, ENNReal.ofReal (coeff (K x) ^ p'.toReal) ∂μ := by
                  exact lintegral_congr_ae (Filter.Eventually.of_forall hnorm_p')
          _ = ∑' n, μ (B n) * ENNReal.ofReal (coeff n ^ p'.toReal) := by
                simpa [f] using
                  lintegral_comp_index_eq_tsum (B := B) (K := K) hKmeas hKfib
                    (fun n ↦ ENNReal.ofReal (coeff n ^ p'.toReal))
      have hsum_lt :
          ∑' n, μ (B n) * ENNReal.ofReal (coeff n ^ p'.toReal) < ⊤ := by
        rw [← hlintegral_p']
        exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp'_ne_zero hp'_ne_top).1 hf_p'.2
      have hcomparison_lt :
          ∑' n : ℕ, ENNReal.ofReal ((n + 1 : ℝ) ^ (-(β * p'.toReal))) < ⊤ := by
        exact lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm_p'_lower) hsum_lt
      have hsummable_p' :
          Summable (fun n : ℕ ↦ (n + 1 : ℝ) ^ (-(β * p'.toReal))) := by
        have hweight_nonneg_p' : ∀ n : ℕ, 0 ≤ (n + 1 : ℝ) ^ (-(β * p'.toReal)) := by
          intro n
          positivity
        let weightP' : ℕ → NNReal := fun n ↦
          Real.toNNReal ((n + 1 : ℝ) ^ (-(β * p'.toReal)))
        have hweightP'_eq : ∀ n : ℕ,
            (weightP' n : ENNReal) =
              ENNReal.ofReal ((n + 1 : ℝ) ^ (-(β * p'.toReal))) := by
          intro n
          simpa [weightP', ENNReal.ofReal, Real.toNNReal_of_nonneg (hweight_nonneg_p' n)]
        have hcoe_ne_top :
            (∑' n : ℕ, (weightP' n : ENNReal)) ≠ ⊤ := by
          simpa [hweightP'_eq] using hcomparison_lt.ne
        have hsummable_toNNReal :
            Summable (fun n : ℕ ↦ (weightP' n : ℝ)) :=
          (ENNReal.tsum_coe_ne_top_iff_summable_coe).1 hcoe_ne_top
        convert hsummable_toNNReal using 1 with n
        simp [weightP', Real.toNNReal_of_nonneg, hweight_nonneg_p']
      exact hnot_summable_p' hsummable_p'
    let fLp : Lp ℝ p μ := MemLp.toLp f hmem_f_p
    refine ⟨fLp, ?_, ?_⟩
    · exact fLp.2
    · intro hfLp'
      have hf_p' : MemLp f p' μ := by
        exact
          (memLp_congr_ae (MemLp.coeFn_toLp hmem_f_p)).1
            ((Lp.mem_Lp_iff_memLp).1 hfLp')
      exact hnot_mem_f_p' hf_p'

/-- Exercise 4.1.2 in textbook representative form: if `1 ≤ p' < p ≤ ∞` and `μ` is sigma-finite
but not finite, then there exists a real-valued function in `ℒ^p(μ)` that does not belong to
`ℒ^{p'}(μ)`. -/
theorem exists_memLp_not_memLp_of_sigmaFinite_not_isFiniteMeasure {p' p : ENNReal}
    (hp' : 1 ≤ p') (hpp : p' < p) (hμ : ¬ IsFiniteMeasure μ) :
    ∃ f : Ω → ℝ, MemLp f p μ ∧ ¬ MemLp f p' μ := by
  rcases exists_mem_Lp_not_mem_Lp_of_sigmaFinite_not_isFiniteMeasure hp' hpp hμ with
    ⟨f, hf, hf'⟩
  refine ⟨f, (Lp.mem_Lp_iff_memLp).1 hf, ?_⟩
  intro hfp'
  exact hf' <| (Lp.mem_Lp_iff_memLp).2 hfp'
