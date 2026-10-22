/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Definition_10_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Exercise_10_2_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ENNReal ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

section

variable {X : ℕ → Ω → ℝ}

local notation "squareProcess" => fun n ω ↦ X n ω ^ 2

/-- Helper for Theorem 11.14: square-integrability of each martingale stage gives integrability of
its squared process. -/
private lemma integrable_squareProcess_of_memLpTwo
    (hX2 : ∀ n, MemLp (X n) 2 μ) :
    ∀ n, Integrable (squareProcess n) μ := by
  intro n
  -- Proof comment: real-valued `L²` membership is exactly integrability of the square.
  exact (memLp_two_iff_integrable_sq (hX2 n).1).1 (hX2 n)

/-- Helper for Theorem 11.14: the threshold stopping time records the first index `n` whose
shifted square variation `⟨X⟩[ℱ, μ] (n + 1)` reaches the level `K`. -/
noncomputable def squareVariationHit (K : ℕ) : Ω → ℕ∞ :=
  hittingAfter (fun n ω ↦ ⟨X⟩[ℱ, μ] (n + 1) ω) (Set.Ici (K : ℝ)) 0

/-- Helper for Theorem 11.14: truncate an `ℕ∞`-valued stopping time by the deterministic horizon
`n` and view the result as an `ℕ`-valued stopping time. -/
noncomputable def boundedStoppingTimeToNat (τ : Ω → ℕ∞) (n : ℕ) : Ω → ℕ :=
  fun ω ↦
    if h : τ ω ≤ n then
      (τ ω).untop (ne_top_of_le_ne_top (show (n : ℕ∞) ≠ ⊤ by simp) h)
    else n

/-- Helper for Theorem 11.14: casting the truncated natural stopping time back to `ℕ∞` recovers
the bounded stopping time `ω ↦ min (n : ℕ∞) (τ ω)`. -/
private lemma boundedStoppingTimeToNat_cast_eq_min (τ : Ω → ℕ∞) (n : ℕ) :
    (fun ω ↦ (boundedStoppingTimeToNat τ n ω : ℕ∞)) = fun ω ↦ min (n : ℕ∞) (τ ω) := by
  -- Route correction: separate the `ℕ`/`ℕ∞` coercion normalization once, so downstream proofs can
  -- rewrite bounded finite truncations without reopening the `if`/`untop` definition.
  funext ω
  by_cases h : τ ω ≤ n
  · -- On the finite branch, `untop` followed by the coercion back to `ℕ∞` recovers `τ ω`.
    cases hτ : τ ω with
    | top =>
        exfalso
        simpa [hτ] using h
    | coe m =>
        have hmn : m ≤ n := by
          simpa [hτ] using h
        rw [boundedStoppingTimeToNat, dif_pos h]
        have hbranch :
            (((WithTop.untop (m : ℕ∞) (show (m : ℕ∞) ≠ ⊤ by simp)) : ℕ) : ℕ∞) =
              min (n : ℕ∞) (m : ℕ∞) := by
          calc
            (((WithTop.untop (m : ℕ∞) (show (m : ℕ∞) ≠ ⊤ by simp)) : ℕ) : ℕ∞) = (m : ℕ∞) := by
              exact WithTop.coe_untop _ (show (m : ℕ∞) ≠ ⊤ by simp)
            _ = min (n : ℕ∞) (m : ℕ∞) := by
              simpa using (min_eq_right hmn).symm
        simpa [hτ] using hbranch
  · -- Off the finite branch, the truncation is the deterministic cap `n`.
    simp [boundedStoppingTimeToNat, h, le_of_not_ge h]

/-- Helper for Theorem 11.14: evaluating `stoppedValue` at the bounded natural truncation agrees
with the canonical stopped process at horizon `n`. -/
private lemma stoppedValue_boundedStoppingTimeToNat_eq_stoppedProcess
    {β : Type*} (u : ℕ → Ω → β) (τ : Ω → ℕ∞) (n : ℕ) :
    stoppedValue u (fun ω ↦ (boundedStoppingTimeToNat τ n ω : ℕ∞)) = stoppedProcess u τ n := by
  -- Proof comment: rewrite the truncated natural stop back to `min n τ`, then use the canonical
  -- `stoppedProcess` normalization.
  ext ω
  rw [stoppedProcess_eq_stoppedValue_apply]
  exact congrArg (fun s ↦ stoppedValue u s ω) (boundedStoppingTimeToNat_cast_eq_min τ n)

/-- Helper for Theorem 11.14: the threshold time `squareVariationHit K` is an `ℱ`-stopping time.
-/
private lemma squareVariationHit_isStoppingTime (K : ℕ) :
    IsStoppingTime ℱ (squareVariationHit (X := X) (ℱ := ℱ) (μ := μ) K) := by
  have hadapt : Adapted ℱ (fun n ω ↦ ⟨X⟩[ℱ, μ] (n + 1) ω) := by
    intro n
    simpa using squareVariation_predictable.measurable_add_one n
  -- Proof comment: the shifted square-variation process is adapted, so its hitting time is a
  -- stopping time.
  simpa [squareVariationHit] using
    hadapt.isStoppingTime_hittingAfter (s := Set.Ici (K : ℝ)) measurableSet_Ici

/-- Helper for Theorem 11.14: each deterministic stage of the canonical square variation is
integrable. -/
private lemma integrable_squareVariation
    (hX : Martingale X ℱ μ) (hX2 : ∀ n, MemLp (X n) 2 μ) :
    ∀ n, Integrable (⟨X⟩[ℱ, μ] n) μ := by
  let hXsq : ∀ n, Integrable (squareProcess n) μ :=
    integrable_squareProcess_of_memLpTwo (X := X) hX2
  intro k
  have hSum_int :
      Integrable
        (fun ω ↦
          ∑ i ∈ Finset.range k,
            μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω) μ := by
    -- Proof comment: the deterministic square-variation formula is a finite sum of integrable
    -- conditional expectations.
    exact integrable_finset_sum (Finset.range k) fun i _ ↦
      (integrable_condExp : Integrable
        (μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i]) μ)
  exact hSum_int.congr (squareVariation_eq_sum_condExp_sq_increment hX hXsq k).symm

/-- Helper for Theorem 11.14: the stopped canonical square variation at the threshold `K` never
exceeds `K`. -/
private lemma stoppedSquareVariation_le_threshold (K n : ℕ) :
    ∀ ω, stoppedProcess (⟨X⟩[ℱ, μ])
      (squareVariationHit (X := X) (ℱ := ℱ) (μ := μ) K) n ω ≤ K := by
  intro ω
  let τK := squareVariationHit (X := X) (ℱ := ℱ) (μ := μ) K
  let m := boundedStoppingTimeToNat τK n ω
  have hEval :
      stoppedProcess (⟨X⟩[ℱ, μ]) τK n ω = ⟨X⟩[ℱ, μ] m ω := by
    -- Proof comment: the bounded truncation turns the stopped process into deterministic
    -- evaluation at the finite index `m`.
    have hStop :
        stoppedValue (⟨X⟩[ℱ, μ]) (fun ω ↦ (boundedStoppingTimeToNat τK n ω : ℕ∞)) =
          stoppedProcess (⟨X⟩[ℱ, μ]) τK n :=
      stoppedValue_boundedStoppingTimeToNat_eq_stoppedProcess
        (u := ⟨X⟩[ℱ, μ]) (τ := τK) (n := n)
    have hEval' :
        stoppedValue (⟨X⟩[ℱ, μ]) (fun ω ↦ (boundedStoppingTimeToNat τK n ω : ℕ∞)) ω =
          ⟨X⟩[ℱ, μ] m ω := by
      simpa [m] using
        (congrFun
          (stoppedValue_coe_eq_eval (⟨X⟩[ℱ, μ]) (boundedStoppingTimeToNat τK n)) ω)
    simpa [hStop] using hEval'
  cases hm : m with
  | zero =>
      -- Proof comment: the square variation starts from `0`, so the zero truncation is trivial.
      rw [hEval, hm, squareVariation_zero]
      positivity
  | succ k =>
      have hcast :
          ((Nat.succ k : ℕ) : ℕ∞) = min (n : ℕ∞) (τK ω) := by
        simpa [m, hm] using
          congrFun (boundedStoppingTimeToNat_cast_eq_min (τ := τK) n) ω
      have hk_lt_min : (k : ℕ∞) < min (n : ℕ∞) (τK ω) := by
        rw [← hcast]
        exact_mod_cast Nat.lt_succ_self k
      have hk_lt_tau : (k : ℕ∞) < τK ω :=
        lt_of_lt_of_le hk_lt_min (min_le_right (n : ℕ∞) (τK ω))
      have hNotMem :
          ⟨X⟩[ℱ, μ] (k + 1) ω ∉ Set.Ici (K : ℝ) := by
        -- Proof comment: if the process had already reached `K` at time `k + 1`, then the hit
        -- would have occurred no later than `k`.
        simpa [squareVariationHit, Set.mem_Ici] using
          (notMem_of_lt_hittingAfter
            (u := fun j ω ↦ ⟨X⟩[ℱ, μ] (j + 1) ω)
            (s := Set.Ici (K : ℝ)) (n := 0) (ω := ω) hk_lt_tau (by simp))
      have hlt : ⟨X⟩[ℱ, μ] (k + 1) ω < K := by
        simpa [Set.mem_Ici, not_le] using hNotMem
      rw [hEval, hm]
      exact le_of_lt hlt

/-- Helper for Theorem 11.14: for real-valued `L²` functions, the `eLpNorm` at exponent `2` is
the square root of the second moment. -/
private lemma eLpNormTwo_eq_ofReal_sqrt_secondMoment
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (μ[fun ω ↦ f ω ^ 2])) := by
  -- Proof comment: pass from `eLpNorm` to `lpNorm`, then use the `p = 2` norm formula.
  calc
    eLpNorm f 2 μ = ENNReal.ofReal (ENNReal.toReal (eLpNorm f 2 μ)) := by
      exact (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm
    _ = ENNReal.ofReal (lpNorm f 2 μ) := by
      rw [toReal_eLpNorm hf.aestronglyMeasurable]
    _ = ENNReal.ofReal (Real.sqrt (μ[fun ω ↦ f ω ^ 2])) := by
      rw [lpNorm_two_eq_sqrt_integral_sq hf]

/-- Helper for Theorem 11.14: the martingale stopped at the threshold `K` has uniformly bounded
second moments. -/
private lemma localizedSecondMomentBound
    (hX : Martingale X ℱ μ) (hX2 : ∀ n, MemLp (X n) 2 μ) (K : ℕ) :
    ∃ C : ℝ,
      ∀ n, μ[fun ω ↦
        (stoppedProcess X (squareVariationHit (X := X) (ℱ := ℱ) (μ := μ) K) n ω) ^ 2] ≤ C := by
  let hXsq : ∀ n, Integrable (squareProcess n) μ :=
    integrable_squareProcess_of_memLpTwo (X := X) hX2
  let τK : Ω → ℕ∞ := squareVariationHit (X := X) (ℱ := ℱ) (μ := μ) K
  have hτK : IsStoppingTime ℱ τK :=
    squareVariationHit_isStoppingTime (X := X) (ℱ := ℱ) (μ := μ) K
  have hSquareVariation_int :
      ∀ n, Integrable (⟨X⟩[ℱ, μ] n) μ :=
    integrable_squareVariation (X := X) (ℱ := ℱ) (μ := μ) hX hX2
  refine ⟨2 * K + 2 * μ[fun ω ↦ X 0 ω ^ 2], fun n ↦ ?_⟩
  let τKn : Ω → ℕ := boundedStoppingTimeToNat τK n
  have hτKn : IsStoppingTime ℱ (fun ω ↦ (τKn ω : ℕ∞)) := by
    -- Proof comment: the bounded truncation is exactly `min τK n` viewed as an `ℕ∞`-valued stop.
    simpa [τKn, boundedStoppingTimeToNat_cast_eq_min, min_comm] using hτK.min_const n
  have hτKn_le : ∀ ω, (τKn ω : ℕ∞) ≤ n := by
    intro ω
    have hcast := congrFun (boundedStoppingTimeToNat_cast_eq_min (τ := τK) n) ω
    rw [hcast]
    exact min_le_left (n : ℕ∞) (τK ω)
  have hStoppedSquareVariation_int :
      Integrable (stoppedValue (⟨X⟩[ℱ, μ]) (fun ω ↦ (τKn ω : ℕ∞))) μ := by
    exact integrable_stoppedValue ℕ hτKn hSquareVariation_int hτKn_le
  have hStoppedSquareVariation_int' :
      Integrable (stoppedProcess (⟨X⟩[ℱ, μ]) τK n) μ := by
    simpa [τKn, stoppedValue_boundedStoppingTimeToNat_eq_stoppedProcess] using
      hStoppedSquareVariation_int
  have hCenteredEq :
      μ[fun ω ↦ (stoppedProcess X τK n ω - X 0 ω) ^ 2] =
        μ[stoppedProcess (⟨X⟩[ℱ, μ]) τK n] := by
    -- Proof comment: the finite truncation theorem applies to `τKn`, and the transport bridge
    -- rewrites both stopped values back to the canonical stopped process.
    simpa [τK, τKn, stoppedValue_boundedStoppingTimeToNat_eq_stoppedProcess] using
      (expectation_stopped_sq_sub_eq_expectation_stopped_squareVariation
        (τ := τKn) (hX := hX) (hXsq := hXsq) (hτ := hτKn)
        (hSquareVariationτ := hStoppedSquareVariation_int))
  have hStoppedSquareVariation_le :
      μ[stoppedProcess (⟨X⟩[ℱ, μ]) τK n] ≤ (K : ℝ) := by
    have hBound :
        stoppedProcess (⟨X⟩[ℱ, μ]) τK n ≤ᵐ[μ] fun _ ↦ (K : ℝ) :=
      Filter.Eventually.of_forall
        (stoppedSquareVariation_le_threshold (X := X) (ℱ := ℱ) (μ := μ) K n)
    calc
      μ[stoppedProcess (⟨X⟩[ℱ, μ]) τK n] ≤ μ[fun _ : Ω ↦ (K : ℝ)] := by
        exact integral_mono_ae hStoppedSquareVariation_int' (integrable_const (K : ℝ)) hBound
      _ = (K : ℝ) := by simp
  have hCentered_le :
      μ[fun ω ↦ (stoppedProcess X τK n ω - X 0 ω) ^ 2] ≤ (K : ℝ) := by
    calc
      μ[fun ω ↦ (stoppedProcess X τK n ω - X 0 ω) ^ 2] =
          μ[stoppedProcess (⟨X⟩[ℱ, μ]) τK n] := hCenteredEq
      _ ≤ (K : ℝ) := hStoppedSquareVariation_le
  have hStopped_memLp : MemLp (stoppedProcess X τK n) 2 μ := by
    have hMem : MemLp (stoppedValue X (fun ω ↦ (τKn ω : ℕ∞))) 2 μ :=
      memLp_stoppedValue hτKn hX2 hτKn_le
    simpa [τKn, stoppedValue_boundedStoppingTimeToNat_eq_stoppedProcess] using hMem
  have hStopped_sq_int :
      Integrable (fun ω ↦ (stoppedProcess X τK n ω) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hStopped_memLp.1).1 hStopped_memLp
  have hCentered_memLp :
      MemLp (fun ω ↦ stoppedProcess X τK n ω - X 0 ω) 2 μ :=
    hStopped_memLp.sub (hX2 0)
  have hCentered_sq_int :
      Integrable (fun ω ↦ (stoppedProcess X τK n ω - X 0 ω) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hCentered_memLp.1).1 hCentered_memLp
  have hMajorized :
      ∀ᵐ ω ∂μ,
        (stoppedProcess X τK n ω) ^ 2 ≤
          (2 : ℝ) * (stoppedProcess X τK n ω - X 0 ω) ^ 2 +
            (2 : ℝ) * (X 0 ω) ^ 2 := by
    -- Proof comment: expand `stoppedProcess X = (stoppedProcess X - X 0) + X 0` and apply the
    -- elementary inequality `(a + b)^2 ≤ 2 a^2 + 2 b^2`.
    filter_upwards [] with ω
    let a : ℝ := stoppedProcess X τK n ω - X 0 ω
    let b : ℝ := X 0 ω
    have hab :
        (a + b) ^ 2 ≤ (2 : ℝ) * a ^ 2 + (2 : ℝ) * b ^ 2 := by
      nlinarith [sq_nonneg (a - b)]
    simpa [a, b, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hab
  have hUpper_int :
      Integrable
        (fun ω ↦
          (2 : ℝ) * (stoppedProcess X τK n ω - X 0 ω) ^ 2 +
            (2 : ℝ) * (X 0 ω) ^ 2) μ := by
    exact (hCentered_sq_int.const_mul (2 : ℝ)).add ((hXsq 0).const_mul (2 : ℝ))
  calc
    μ[fun ω ↦ (stoppedProcess X τK n ω) ^ 2]
        ≤ μ[fun ω ↦
            (2 : ℝ) * (stoppedProcess X τK n ω - X 0 ω) ^ 2 +
              (2 : ℝ) * (X 0 ω) ^ 2] := by
          exact integral_mono_ae hStopped_sq_int hUpper_int hMajorized
    _ = (2 : ℝ) * μ[fun ω ↦ (stoppedProcess X τK n ω - X 0 ω) ^ 2] +
          (2 : ℝ) * μ[fun ω ↦ (X 0 ω) ^ 2] := by
          rw [integral_add (hCentered_sq_int.const_mul (2 : ℝ)) ((hXsq 0).const_mul (2 : ℝ)),
            integral_const_mul, integral_const_mul]
    _ ≤ (2 : ℝ) * K + (2 : ℝ) * μ[fun ω ↦ (X 0 ω) ^ 2] := by
          linarith

/-- Helper for Theorem 11.14: every threshold-localized martingale converges almost surely. -/
private lemma localizedAeTendstoExists
    (hX : Martingale X ℱ μ) (hX2 : ∀ n, MemLp (X n) 2 μ) (K : ℕ) :
    ∀ᵐ ω ∂μ, ∃ c,
      Tendsto
        (fun n ↦ stoppedProcess X
          (squareVariationHit (X := X) (ℱ := ℱ) (μ := μ) K) n ω)
        atTop (𝓝 c) := by
  let τK : Ω → ℕ∞ := squareVariationHit (X := X) (ℱ := ℱ) (μ := μ) K
  have hτK : IsStoppingTime ℱ τK :=
    squareVariationHit_isStoppingTime (X := X) (ℱ := ℱ) (μ := μ) K
  have hStoppedMartingale : Martingale (stoppedProcess X τK) ℱ μ := by
    -- Proof comment: the stopped process is a martingale because both the submartingale and
    -- supermartingale halves are preserved under stopping.
    rw [martingale_iff]
    refine ⟨?_, hX.submartingale.stoppedProcess hτK⟩
    have hStoppedNegSub : Submartingale (stoppedProcess (-X) τK) ℱ μ :=
      hX.neg.submartingale.stoppedProcess hτK
    have hStoppedNegEq : stoppedProcess (-X) τK = -(stoppedProcess X τK) := by
      funext n ω
      simp [stoppedProcess]
    simpa [hStoppedNegEq] using hStoppedNegSub.neg
  obtain ⟨C, hC⟩ :=
    localizedSecondMomentBound (X := X) (ℱ := ℱ) (μ := μ) hX hX2 K
  have hp : 1 < (2 : ℝ) := by
    norm_num
  have hLpBound : ∃ R : NNReal, ∀ n, eLpNorm (stoppedProcess X τK n) 2 μ ≤ R := by
    refine ⟨⟨Real.sqrt (max C 0), Real.sqrt_nonneg _⟩, fun n ↦ ?_⟩
    let τKn : Ω → ℕ := boundedStoppingTimeToNat τK n
    have hτKn : IsStoppingTime ℱ (fun ω ↦ (τKn ω : ℕ∞)) := by
      simpa [τKn, boundedStoppingTimeToNat_cast_eq_min, min_comm] using hτK.min_const n
    have hτKn_le : ∀ ω, (τKn ω : ℕ∞) ≤ n := by
      intro ω
      have hcast := congrFun (boundedStoppingTimeToNat_cast_eq_min (τ := τK) n) ω
      rw [hcast]
      exact min_le_left (n : ℕ∞) (τK ω)
    have hStopped_memLp : MemLp (stoppedProcess X τK n) 2 μ := by
      have hMem : MemLp (stoppedValue X (fun ω ↦ (τKn ω : ℕ∞))) 2 μ :=
        memLp_stoppedValue hτKn hX2 hτKn_le
      simpa [τKn, stoppedValue_boundedStoppingTimeToNat_eq_stoppedProcess] using hMem
    -- Proof comment: rewrite the `L²` norm through the second moment and insert the uniform
    -- scalar bound from `localizedSecondMomentBound`.
    rw [eLpNormTwo_eq_ofReal_sqrt_secondMoment hStopped_memLp]
    simpa using
      (ENNReal.ofReal_le_ofReal
        (Real.sqrt_le_sqrt (le_trans (hC n) (le_max_left C 0))))
  have hLpBound' :
      ∃ R : NNReal, ∀ n, eLpNorm (stoppedProcess X τK n) (ENNReal.ofReal (2 : ℝ)) μ ≤ R := by
    simpa using hLpBound
  obtain ⟨_, _, hAe, _⟩ :=
    martingale_convergence_to_memLp_limitProcess_of_lp_bounded
      (X := stoppedProcess X τK) (ℱ := ℱ) (μ := μ) (p := 2) hStoppedMartingale hp hLpBound'
  filter_upwards [hAe] with ω hω
  exact ⟨ℱ.limitProcess (stoppedProcess X τK) μ ω, hω⟩

/-- Helper for Theorem 11.14: the terminal filtration `⨆ n, ℱ n` is a sub-σ-algebra of the
ambient measurable space. -/
private lemma sSupFiltration_le : (⨆ n, ℱ n) ≤ ‹MeasurableSpace Ω› := by
  -- Proof comment: every stage `ℱ n` already sits inside the ambient measurable space.
  refine sSup_le ?_
  rintro _ ⟨n, rfl⟩
  exact ℱ.le n

/-- Helper for Theorem 11.14: almost-sure boundedness of the canonical square variation implies
pathwise convergence of the martingale. -/
private lemma ae_exists_limit_of_ae_bddAboveSquareVariation
    (hX : Martingale X ℱ μ) (hX2 : ∀ n, MemLp (X n) 2 μ)
    (h_bddSquareVariation : ∀ᵐ ω ∂μ, BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω)) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n ↦ X n ω) atTop (𝓝 c) := by
  have hLocalized :
      ∀ᵐ ω ∂μ,
        ∀ K : ℕ, ∃ c,
          Tendsto
            (fun n ↦ stoppedProcess X
              (squareVariationHit (X := X) (ℱ := ℱ) (μ := μ) K) n ω)
            atTop (𝓝 c) := by
    rw [ae_all_iff]
    intro K
    exact localizedAeTendstoExists (X := X) (ℱ := ℱ) (μ := μ) hX hX2 K
  filter_upwards [hLocalized, h_bddSquareVariation] with ω hLocalizedω hBddω
  obtain ⟨a, ha⟩ := hBddω
  obtain ⟨K, hK⟩ := exists_nat_gt a
  have hHitTop :
      squareVariationHit (X := X) (ℱ := ℱ) (μ := μ) K ω = ⊤ := by
    -- Proof comment: choosing `K` above the pathwise square-variation bound means the threshold
    -- is never reached, so the hitting time is infinite on this sample path.
    refine (hittingAfter_eq_top_iff
      (u := fun n ω ↦ ⟨X⟩[ℱ, μ] (n + 1) ω)
      (s := Set.Ici (K : ℝ)) (n := 0) (ω := ω)).2 ?_
    intro j _
    have hja : ⟨X⟩[ℱ, μ] (j + 1) ω ≤ a := by
      exact ha ⟨j + 1, rfl⟩
    have hjK : ⟨X⟩[ℱ, μ] (j + 1) ω < K := lt_of_le_of_lt hja hK
    simpa [Set.mem_Ici, not_le] using hjK
  obtain ⟨c, hc⟩ := hLocalizedω K
  refine ⟨c, ?_⟩
  -- Proof comment: once the hitting time is `⊤`, the stopped process agrees pointwise with `X`.
  have hStoppedEq :
      (fun n ↦
        stoppedProcess X (squareVariationHit (X := X) (ℱ := ℱ) (μ := μ) K) n ω) =
        fun n ↦ X n ω := by
    funext n
    exact stoppedProcess_eq_of_le (ω := ω) (i := n) <|
      by
        rw [hHitTop]
        exact le_top
  simpa [hStoppedEq] using hc

/-- Helper for Theorem 11.14: the existence-of-limit event is measurable on the terminal
σ-algebra, so a `μ`-a.e. existence statement transfers to the trimmed measure on `⨆ n, ℱ n`. -/
private lemma ae_exists_limit_trim_of_ae_exists_limit
    (hX : Martingale X ℱ μ)
    (hAe : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n ↦ X n ω) atTop (𝓝 c)) :
    ∀ᵐ ω ∂μ.trim (sSupFiltration_le (Ω := Ω) (ℱ := ℱ)),
      ∃ c, Tendsto (fun n ↦ X n ω) atTop (𝓝 c) := by
  letI := (⨆ n, ℱ n)
  rw [ae_iff, trim_measurableSet_eq]
  · exact hAe
  · -- Proof comment: measurability of the limit-existence event follows from measurability of
    -- every martingale stage on the terminal filtration.
    exact MeasurableSet.compl <| measurableSet_exists_tendsto fun n =>
      (hX.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩) le_rfl

/- Theorem 11.14 is `source-facing`: it is a convergence criterion for a square-integrable
martingale under pathwise boundedness of its square variation. Its `core/canonical` owner layers
are the chapter's square-variation notion from Chapter 10 and mathlib's martingale convergence API
around `ℱ.limitProcess`. The statement below reuses the chapter owner notation `⟨X⟩[ℱ, μ]` and
avoids introducing a parallel wrapper around those owners. -/

-- Proof sketch: for each `K > 0`, stop `X` at the first time when the canonical square variation
-- reaches `K`; the stopped martingale then has uniformly bounded square variation, so Corollary
-- 11.11 gives almost-sure convergence of the stopped process. On the event where the stopping time
-- is infinite, the stopped process agrees with `X`, and these events exhaust almost all sample
-- points because the square variation is almost surely bounded above.
/-- Theorem 11.14: if a square-integrable discrete-time martingale has almost surely bounded
canonical square variation `⟨X⟩[ℱ, μ]`, equivalently `sup_n ⟨X⟩_n < ∞` almost surely, then
the martingale converges almost surely to its canonical limit process. -/
theorem square_integrable_martingale_ae_tendsto_limitProcess_of_ae_bddAbove_squareVariation
    (hX : Martingale X ℱ μ) (hX2 : ∀ n, MemLp (X n) 2 μ)
    (h_bddSquareVariation : ∀ᵐ ω ∂μ, BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω)) := by
  classical
  suffices
      ∃ g, StronglyMeasurable[⨆ n, ℱ n] g ∧
        ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (g ω)) by
    -- Proof comment: once a terminal-filtration measurable limit is available, the owner API
    -- identifies it with `ℱ.limitProcess X μ`.
    rw [Filtration.limitProcess, dif_pos this]
    exact (Classical.choose_spec this).2
  set g' : Ω → ℝ := fun ω ↦
    if h : ∃ c, Tendsto (fun n ↦ X n ω) atTop (𝓝 c) then h.choose else 0
  have hle : (⨆ n, ℱ n) ≤ ‹MeasurableSpace Ω› := sSupFiltration_le (Ω := Ω) (ℱ := ℱ)
  have hAe :
      ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n ↦ X n ω) atTop (𝓝 c) :=
    ae_exists_limit_of_ae_bddAboveSquareVariation
      (X := X) (ℱ := ℱ) (μ := μ) hX hX2 h_bddSquareVariation
  have hg' : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n ↦ X n ω) atTop (𝓝 (g' ω)) := by
    -- Proof comment: on the trimmed full-measure existence event, `g'` picks the pathwise limit.
    filter_upwards [ae_exists_limit_trim_of_ae_exists_limit
      (X := X) (ℱ := ℱ) (μ := μ) hX hAe] with ω hω
    simp_rw [g', dif_pos hω]
    exact hω.choose_spec
  have hg'm : AEStronglyMeasurable[⨆ n, ℱ n] g' (μ.trim hle) :=
    (@aemeasurable_of_tendsto_metrizable_ae' _ _ (⨆ n, ℱ n) _ _ _ _ _ _ _
      (fun n =>
        ((hX.stronglyMeasurable n).measurable.mono
          (le_sSup ⟨n, rfl⟩ : ℱ n ≤ ⨆ n, ℱ n) le_rfl).aemeasurable) hg').aestronglyMeasurable
  obtain ⟨g, hgm, hae⟩ := hg'm
  have hg : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n ↦ X n ω) atTop (𝓝 (g ω)) := by
    -- Proof comment: replace the a.e.-measurable selector `g'` by a strongly measurable version.
    filter_upwards [hae, hg'] with ω hω hg'ω
    exact hω ▸ hg'ω
  exact ⟨g, hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩

end
