/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Exercise_11_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

section

variable {X : ℕ → Ω → ℝ}

local notation "incrementSupNorm" =>
  fun ω ↦ ⨆ n : ℕ, ENNReal.ofReal |X (n + 1) ω - X n ω|
local notation "Converges" =>
  fun ω ↦ ∃ c : ℝ, Tendsto (fun n ↦ X n ω) atTop (𝓝 c)
local notation "PathBddAbove" =>
  fun ω ↦ BddAbove (Set.range fun n ↦ X n ω)
local notation "PathBddBelow" =>
  fun ω ↦ BddBelow (Set.range fun n ↦ X n ω)

/- Exercise 11.2.6 is `source-facing`: it upgrades Exercise 11.2.5 from uniformly bounded
increments to the weaker hypothesis that the pathwise increment envelope has finite expectation.
Its `core/canonical` owner layer is still the martingale convergence API around `Martingale`,
`Submartingale.ae_tendsto_limitProcess`, and the pathwise boundedness/convergence predicates
isolated in Exercise 11.2.5. The increment envelope is only a local `bridge/view` quantity, so it
should not survive as a separate public owner-level definition here. -/

-- Proof sketch: for each level `K`, stop the martingale at a suitable time `ρ_K` before the
-- increment envelope exceeds `K`; the stopped martingale then has uniformly bounded increments, so
-- Exercise 11.2.5 and the martingale convergence theorem apply to it. Letting `K → ∞` and using
-- the integrability of `sup_n |X_{n+1} - X_n|` shows that the stopping events exhaust almost every
-- sample path, yielding the claimed three-way equivalence almost surely.
/-- Helper for Exercise 11.2.6: finite expectation of the increment envelope gives an almost-sure
real-valued bound on every deterministic increment. -/
lemma ae_increment_le_incrementSupNormToReal
    (hX : Martingale X ℱ μ)
    (hinc : (∫⁻ ω, incrementSupNorm ω ∂μ) < (⊤ : ENNReal)) :
    ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ (incrementSupNorm ω).toReal := by
  have hmeasTerm : ∀ n, Measurable (fun ω ↦ ENNReal.ofReal |X (n + 1) ω - X n ω|) := by
    intro n
    exact ((((hX.stronglyMeasurable (n + 1)).mono (ℱ.le (n + 1))).measurable.sub
      (((hX.stronglyMeasurable n).mono (ℱ.le n)).measurable)).abs.ennreal_ofReal)
  have hmeas : Measurable incrementSupNorm := by
    change Measurable (fun ω ↦ ⨆ n : ℕ, ENNReal.ofReal |X (n + 1) ω - X n ω|)
    exact Measurable.iSup hmeasTerm
  have hfinite : ∀ᵐ ω ∂μ, incrementSupNorm ω < ⊤ :=
    ae_lt_top hmeas hinc.ne
  -- Proof comment: once the envelope is finite, each summand sits below its `iSup`, so taking
  -- `toReal` yields the desired deterministic-time real inequality.
  filter_upwards [hfinite] with ω hω n
  have hle : ENNReal.ofReal |X (n + 1) ω - X n ω| ≤ incrementSupNorm ω := by
    exact le_iSup (fun m : ℕ ↦ ENNReal.ofReal |X (m + 1) ω - X m ω|) n
  exact (ENNReal.ofReal_le_iff_le_toReal hω.ne).1 hle

/-- Helper for Exercise 11.2.6: a centered path stopped above `r` overshoots the barrier by at
most one increment bound. -/
lemma stoppedAbove_le_barrier_add_bound
    {f : ℕ → Ω → ℝ} {r B : ℝ} {ω : Ω}
    (hr : 0 ≤ r) (hf0 : f 0 ω = 0)
    (hbdd : ∀ n, |f (n + 1) ω - f n ω| ≤ B) :
    ∀ n, MeasureTheory.stoppedAbove f r n ω ≤ r + B := by
  intro i
  let τ : ℕ∞ := MeasureTheory.leastGE f r ω
  rw [MeasureTheory.stoppedAbove, stoppedProcess, ENat.some_eq_coe]
  change f (min (i : ℕ∞) τ).untopA ω ≤ r + B
  by_cases h_zero : (min (i : ℕ∞) (MeasureTheory.leastGE f r ω)).untopA = 0
  · have hB_nonneg : 0 ≤ B := by
      exact (show 0 ≤ |f 1 ω - f 0 ω| by positivity).trans (hbdd 0)
    have hval : f (min (i : ℕ∞) τ).untopA ω = 0 := by
      simpa [τ, h_zero] using hf0
    -- Proof comment: if the stopped index is `0`, the centered path is still at the origin.
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h_zero
  have hval : f (min (i : ℕ∞) τ).untopA ω = f (k + 1) ω := by
    simpa [τ, hk]
  have hlt_hit : (k : ℕ∞) < τ := by
    suffices (k : ℕ∞) < min (i : ℕ∞) τ from
      this.trans_le (min_le_right _ _)
    have htop : min (i : ℕ∞) τ ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (min_le_left _ _)
    lift min (i : ℕ∞) τ to ℕ using htop with p hp
    have hpuntop : (min (i : ℕ∞) τ).untopA = p := by
      rw [hp.symm, WithTop.untopA_eq_untop (show (p : ℕ∞) ≠ ⊤ by simp)]
      rfl
    have hp' : p = k + 1 := hpuntop.symm.trans hk
    have hklt_nat : k < p := by
      rw [hp']
      exact Nat.lt_succ_self k
    have hklt_p : (k : ℕ∞) < (p : ℕ∞) := by
      exact_mod_cast hklt_nat
    simpa [hp] using hklt_p
  have hlt_barrier : f k ω < r := by
    have hnotMem := notMem_of_lt_hittingAfter
      (u := f) (s := Set.Ici r) (n := 0) (ω := ω) hlt_hit
    simpa [MeasureTheory.leastGE, Set.mem_Ici] using hnotMem
  -- Proof comment: before the hitting time the path lies below `r`, so the next value can exceed
  -- `r` by at most the size of that final increment.
  have hstep : f (k + 1) ω - r ≤ B := by
    have hsub : f (k + 1) ω - r < f (k + 1) ω - f k ω := by
      exact sub_lt_sub_left hlt_barrier _
    exact hsub.le.trans ((le_abs_self _).trans (hbdd k))
  linarith

/-- Helper for Exercise 11.2.6: every deterministic upper barrier yields an almost surely
convergent stopped centered martingale. -/
lemma centeredStoppedAbove_aeTendsto
    (hX : Martingale X ℱ μ)
    (hinc : (∫⁻ ω, incrementSupNorm ω ∂μ) < (⊤ : ENNReal))
    (K : ℕ) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ,
      Tendsto (fun n ↦ MeasureTheory.stoppedAbove (centeredProcess X) K n ω) atTop (𝓝 c) := by
  let Y : ℕ → Ω → ℝ := centeredProcess X
  have hY : Martingale Y ℱ μ := centeredProcess_martingale (μ := μ) (ℱ := ℱ) hX
  have hmeasTerm : ∀ n, Measurable (fun ω ↦ ENNReal.ofReal |X (n + 1) ω - X n ω|) := by
    intro n
    exact ((((hX.stronglyMeasurable (n + 1)).mono (ℱ.le (n + 1))).measurable.sub
      (((hX.stronglyMeasurable n).mono (ℱ.le n)).measurable)).abs.ennreal_ofReal)
  have hmeas : Measurable incrementSupNorm := by
    change Measurable (fun ω ↦ ⨆ n : ℕ, ENNReal.ofReal |X (n + 1) ω - X n ω|)
    exact Measurable.iSup hmeasTerm
  have hEnvInt : Integrable (fun ω ↦ (incrementSupNorm ω).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hinc.ne
  have hYbdd : ∀ᵐ ω ∂μ, ∀ n, |Y (n + 1) ω - Y n ω| ≤ (incrementSupNorm ω).toReal := by
    filter_upwards [ae_increment_le_incrementSupNormToReal (X := X) hX hinc] with ω hω n
    have hstep : Y (n + 1) ω - Y n ω = X (n + 1) ω - X n ω := by
      simpa [Y] using congrFun (centeredProcess_sub_eq X n) ω
    simpa [hstep] using hω n
  have hpos :
      BddAbove (Set.range fun n ↦ μ[fun ω ↦ (MeasureTheory.stoppedAbove Y K n ω)⁺]) := by
    refine ⟨∫ ω, ((K : ℝ) + (incrementSupNorm ω).toReal) ∂μ, ?_⟩
    rintro x ⟨n, rfl⟩
    have hStoppedInt : Integrable (MeasureTheory.stoppedAbove Y K n) μ :=
      (hY.submartingale.stoppedAbove K).integrable n
    have hbound :
        ∀ᵐ ω ∂μ,
          (MeasureTheory.stoppedAbove Y K n ω)⁺ ≤ K + (incrementSupNorm ω).toReal := by
      -- Proof comment: combine the pathwise overshoot estimate with the nonnegativity of the
      -- envelope to dominate the positive part of the stopped process.
      filter_upwards [hYbdd] with ω hω
      have hstop :
          MeasureTheory.stoppedAbove Y K n ω ≤ K + (incrementSupNorm ω).toReal :=
        stoppedAbove_le_barrier_add_bound
          (f := Y) (r := K) (ω := ω) (show 0 ≤ (K : ℝ) by exact_mod_cast Nat.zero_le K)
          (by simpa [Y] using congrFun (centeredProcess_zero X) ω) (hω) n
      have hnonneg : 0 ≤ K + (incrementSupNorm ω).toReal := by positivity
      by_cases hproc : 0 ≤ MeasureTheory.stoppedAbove Y K n ω
      · rwa [posPart_eq_self.2 hproc]
      · rw [posPart_eq_zero.2 (le_of_not_ge hproc)]
        exact hnonneg
    exact integral_mono_ae hStoppedInt.pos_part ((integrable_const (K : ℝ)).add hEnvInt) hbound
  have hconv :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n ↦ MeasureTheory.stoppedAbove Y K n ω) atTop
          (𝓝 (ℱ.limitProcess (MeasureTheory.stoppedAbove Y K) μ ω)) :=
    (submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
      (X := MeasureTheory.stoppedAbove Y K) (hY.submartingale.stoppedAbove K) hpos).2
  -- Proof comment: Theorem 11.4 applies to the stopped centered submartingale because the
  -- overshoot estimate gives a uniform bound on the expectations of its positive parts.
  filter_upwards [hconv] with ω hω
  exact ⟨ℱ.limitProcess (MeasureTheory.stoppedAbove Y K) μ ω, hω⟩

/-- Helper for Exercise 11.2.6: an almost surely upper-bounded path converges almost surely. -/
lemma ae_exists_tendsto_of_pathBddAbove
    (hX : Martingale X ℱ μ)
    (hinc : (∫⁻ ω, incrementSupNorm ω ∂μ) < (⊤ : ENNReal)) :
    ∀ᵐ ω ∂μ, PathBddAbove ω → Converges ω := by
  let Y : ℕ → Ω → ℝ := centeredProcess X
  have hStoppedAll :
      ∀ᵐ ω ∂μ, ∀ K : ℕ, ∃ c : ℝ,
        Tendsto (fun n ↦ MeasureTheory.stoppedAbove Y K n ω) atTop (𝓝 c) := by
    rw [ae_all_iff]
    intro K
    simpa [Y] using centeredStoppedAbove_aeTendsto (X := X) hX hinc K
  filter_upwards [hStoppedAll] with ω hω hBddAbove
  have hCenteredBdd : BddAbove (Set.range fun n ↦ Y n ω) := by
    rcases hBddAbove with ⟨b, hb⟩
    refine ⟨b + |X 0 ω|, ?_⟩
    -- Proof comment: subtracting the deterministic initial value preserves upper boundedness.
    rintro y ⟨n, rfl⟩
    have hx : X n ω ≤ b := hb (Set.mem_range.2 ⟨n, rfl⟩)
    calc
      Y n ω = X n ω - X 0 ω := by simp [Y, centeredProcess]
      _ ≤ b + |X 0 ω| := by linarith [hx, neg_le_abs (X 0 ω)]
  rcases hCenteredBdd with ⟨b, hb⟩
  obtain ⟨K, hK⟩ := exists_nat_gt b
  have hlt : ∀ n, Y n ω < K := by
    intro n
    exact lt_of_le_of_lt (hb (Set.mem_range.2 ⟨n, rfl⟩)) hK
  have hEq : ∀ n, MeasureTheory.stoppedAbove Y K n ω = Y n ω := by
    intro n
    -- Proof comment: choosing `K` above the whole centered path forces the stopping time to be
    -- `⊤`, so the stopped process is the original centered process.
    rw [MeasureTheory.stoppedAbove, stoppedProcess, MeasureTheory.leastGE,
      hittingAfter_eq_top_iff.mpr]
    · simp only [le_top, inf_of_le_left]
      congr
    · simp [Set.mem_Ici, hlt]
  have hCenteredConv : ∃ c : ℝ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 c) := by
    rcases hω K with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    refine Tendsto.congr' ?_ hc
    exact Filter.Eventually.of_forall hEq
  exact (centeredProcess_exists_tendsto_iff X ω).1 hCenteredConv

/-- Exercise 11.2.6: if a real-valued martingale has finite expectation of the supremum of its
absolute increments, then almost every sample path satisfies the same three-way equivalence between
convergence and one-sided boundedness as in Exercise 11.2.5. -/
theorem martingale_convergence_tfae_of_integrable_increment_sup
    (hX : Martingale X ℱ μ)
    (hinc : (∫⁻ ω, incrementSupNorm ω ∂μ) < (⊤ : ENNReal)) :
    ∀ᵐ ω ∂μ,
      List.TFAE [Converges ω, PathBddAbove ω, PathBddBelow ω] := by
  classical
  have hAbove :
      ∀ᵐ ω ∂μ, PathBddAbove ω → Converges ω :=
    ae_exists_tendsto_of_pathBddAbove (X := X) hX hinc
  have hBelow :
      ∀ᵐ ω ∂μ, PathBddBelow ω → Converges ω := by
    have hnegEnvelope :
        (fun ω ↦ ⨆ n : ℕ, ENNReal.ofReal
          |(fun n ω ↦ -X n ω) (n + 1) ω - (fun n ω ↦ -X n ω) n ω|) =
          incrementSupNorm := by
      funext ω
      change (⨆ n : ℕ, ENNReal.ofReal |-X (n + 1) ω - -X n ω|) =
        ⨆ n : ℕ, ENNReal.ofReal |X (n + 1) ω - X n ω|
      congr with n
      exact congrArg ENNReal.ofReal <|
        by simpa [sub_eq_add_neg, add_comm] using abs_sub_comm (X n ω) (X (n + 1) ω)
    have hnegInc :
        (∫⁻ ω, (⨆ n : ℕ, ENNReal.ofReal
          |(fun n ω ↦ -X n ω) (n + 1) ω - (fun n ω ↦ -X n ω) n ω|) ∂μ) < (⊤ : ENNReal) := by
      rw [hnegEnvelope]
      exact hinc
    have hNegAbove :
        ∀ᵐ ω ∂μ,
          BddAbove (Set.range fun n ↦ (fun n ω ↦ -X n ω) n ω) →
            ∃ c : ℝ, Tendsto (fun n ↦ (fun n ω ↦ -X n ω) n ω) atTop (𝓝 c) :=
      ae_exists_tendsto_of_pathBddAbove (X := fun n ω ↦ -X n ω) hX.neg hnegInc
    filter_upwards [hNegAbove] with ω hω hBddBelow
    have hNegBdd : BddAbove (Set.range fun n ↦ -X n ω) := by
      rcases hBddBelow with ⟨b, hb⟩
      refine ⟨-b, ?_⟩
      rintro y ⟨n, rfl⟩
      have hx : b ≤ X n ω := hb (Set.mem_range.2 ⟨n, rfl⟩)
      linarith
    rcases hω hNegBdd with ⟨c, hc⟩
    refine ⟨-c, ?_⟩
    convert hc.neg using 1 <;> simp
  filter_upwards [hAbove, hBelow] with ω hAboveω hBelowω
  tfae_have 1 ↔ 2 := by
    constructor
    · rintro ⟨c, hc⟩
      exact hc.bddAbove_range
    · intro hBddAbove
      exact hAboveω hBddAbove
  tfae_have 1 ↔ 3 := by
    constructor
    · rintro ⟨c, hc⟩
      exact hc.bddBelow_range
    · intro hBddBelow
      exact hBelowω hBddBelow
  tfae_finish

end
