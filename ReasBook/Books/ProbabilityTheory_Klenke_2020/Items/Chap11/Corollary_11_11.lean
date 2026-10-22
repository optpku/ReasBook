/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
variable {X : ℕ → Ω → ℝ}

local notation "squareProcess" => fun n ω ↦ X n ω ^ 2

/-- Helper for Corollary 11.11: square-integrability of each martingale stage gives integrability
of its squared process. -/
private lemma integrable_squareProcess_of_memLpTwo
    (hX2 : ∀ n, MemLp (X n) 2 μ) :
    ∀ n, Integrable (squareProcess n) μ := by
  intro n
  -- Proof comment: `L²` membership is exactly the integrability of the square for real-valued
  -- functions.
  exact (memLp_two_iff_integrable_sq (hX2 n).1).1 (hX2 n)

/-- Helper for Corollary 11.11: every second moment `μ[(X n)^2]` is nonnegative. -/
private lemma secondMoment_nonneg (n : ℕ) :
    0 ≤ μ[squareProcess n] := by
  -- Proof comment: integrate the pointwise nonnegative square.
  exact integral_nonneg_of_ae <| Filter.Eventually.of_forall fun ω ↦ sq_nonneg (X n ω)

/-- Helper for Corollary 11.11: the expectation of the square variation is the terminal second
moment minus the initial second moment. -/
private lemma squareVariationExpectation_eq_secondMomentDiff
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) (n : ℕ) :
    μ[⟨X⟩[ℱ, μ] n] = μ[squareProcess n] - μ[squareProcess 0] := by
  -- Proof comment: combine the Chapter 10 square-variation/variance identity with the variance
  -- expansion for the terminal increment.
  calc
    μ[⟨X⟩[ℱ, μ] n] = Var[fun ω ↦ X n ω - X 0 ω; μ] :=
      squareVariation_expectation_eq_variance hX hXsq n
    _ = μ[squareProcess n] - μ[squareProcess 0] :=
      variance_terminalIncrement_eq_sqMomentDiff hX hXsq n

/-- Helper for Corollary 11.11: the second moments of a square-integrable martingale form a
monotone sequence. -/
private lemma martingaleSecondMomentMonotone
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) :
    Monotone (fun n ↦ μ[squareProcess n]) := by
  intro n m hnm
  induction hnm with
  | refl => exact le_rfl
  | @step k _ hk =>
      have hStep :
          μ[squareProcess (k + 1)] - μ[squareProcess k] =
            μ[fun ω ↦ (X (k + 1) ω - X k ω) ^ 2] := by
        symm
        exact integral_sqIncrement_eq_sqMomentDiff hX hXsq k
      have hNonneg :
          0 ≤ μ[fun ω ↦ (X (k + 1) ω - X k ω) ^ 2] := by
        exact integral_nonneg_of_ae <|
          Filter.Eventually.of_forall fun ω ↦ sq_nonneg (X (k + 1) ω - X k ω)
      have hSucc : μ[squareProcess k] ≤ μ[squareProcess (k + 1)] := by
        linarith
      exact le_trans hk hSucc

/-- Helper for Corollary 11.11: the squared norm of the `L²` representative is the corresponding
second moment. -/
private lemma toLpNormSqEqIntegralSq
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = μ[fun ω ↦ f ω ^ 2] := by
  -- Proof comment: rewrite the `L²` norm through the inner product of the class with itself.
  calc
    ‖hf.toLp f‖ ^ 2 = inner ℝ (hf.toLp f) (hf.toLp f) := by simp
    _ = μ[fun ω ↦ f ω * f ω] := by
      rw [inner_toLp_eq_integral_mul hf hf]
    _ = μ[fun ω ↦ f ω ^ 2] := by
      simp [sq]

/-- Helper for Corollary 11.11: for real-valued `L²` functions, the `eLpNorm` at exponent `2`
is the square root of the second moment. -/
private lemma eLpNormTwo_eq_ofReal_sqrt_secondMoment
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (μ[fun ω ↦ f ω ^ 2])) := by
  -- Proof comment: pass from `eLpNorm` to `lpNorm`, then use the Chapter 7 `p = 2` formula.
  calc
    eLpNorm f 2 μ = ENNReal.ofReal (ENNReal.toReal (eLpNorm f 2 μ)) := by
      exact (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm
    _ = ENNReal.ofReal (lpNorm f 2 μ) := by
      rw [toReal_eLpNorm hf.aestronglyMeasurable]
    _ = ENNReal.ofReal (Real.sqrt (μ[fun ω ↦ f ω ^ 2])) := by
      rw [lpNorm_two_eq_sqrt_integral_sq hf]

/-- Helper for Corollary 11.11: a uniform second-moment bound yields the `L²` seminorm bound
required by Theorem 11.10. -/
private lemma lpTwoBound_of_uniformSecondMomentBound
    (hX2 : ∀ n, MemLp (X n) 2 μ)
    (hbounded : ∃ C : ℝ, ∀ n, μ[squareProcess n] ≤ C) :
    ∃ R : NNReal, ∀ n, eLpNorm (X n) 2 μ ≤ R := by
  rcases hbounded with ⟨C, hC⟩
  refine ⟨⟨Real.sqrt (max C 0), Real.sqrt_nonneg _⟩, fun n ↦ ?_⟩
  -- Proof comment: rewrite the `L²` seminorm as `sqrt (E[X_n^2])` and bound the second moment.
  rw [eLpNormTwo_eq_ofReal_sqrt_secondMoment (hX2 n)]
  simpa using
    (ENNReal.ofReal_le_ofReal
      (Real.sqrt_le_sqrt (le_trans (hC n) (le_max_left C 0))))

/-- Helper for Corollary 11.11: an `L²`-convergent sequence has uniformly bounded second
moments. -/
private lemma uniformSecondMomentBound_of_tendstoInLpTwo
    {L : Ω → ℝ} (hLp : TendstoInLp 2 μ X L) :
    ∃ C : ℝ, ∀ n, μ[squareProcess n] ≤ C := by
  have hNormTendsto :
      Tendsto (fun n ↦ ‖(hLp.memLpSeq n).toLp (X n)‖) atTop
        (𝓝 ‖hLp.memLp.toLp L‖) := by
    -- Proof comment: the owner `TendstoInLp` theorem gives norm convergence in the canonical `Lp`
    -- space.
    simpa using hLp.tendsto_toLp.norm
  rcases hNormTendsto.bddAbove_range with ⟨R, hR⟩
  refine ⟨R ^ 2, fun n ↦ ?_⟩
  have hR_nonneg : 0 ≤ R := by
    exact le_trans (norm_nonneg _) (hR <| Set.mem_range_self 0)
  have hnorm_le : ‖(hLp.memLpSeq n).toLp (X n)‖ ≤ R := hR <| Set.mem_range_self n
  -- Proof comment: bound the norm in `Lp` and rewrite it back to the scalar second moment.
  calc
    μ[squareProcess n] = ‖(hLp.memLpSeq n).toLp (X n)‖ ^ 2 := by
      symm
      exact toLpNormSqEqIntegralSq (hLp.memLpSeq n)
    _ ≤ R ^ 2 := by
      have hsq :
          ‖(hLp.memLpSeq n).toLp (X n)‖ * ‖(hLp.memLpSeq n).toLp (X n)‖ ≤ R * R :=
        mul_le_mul hnorm_le hnorm_le (norm_nonneg _) hR_nonneg
      simpa [sq] using hsq

-- Proof sketch: use Theorem 10.4 to identify the expectations of the canonical square variation
-- with the variances of the martingale increments via
-- `squareVariation_expectation_eq_variance`, so (i) and (ii) are equivalent. Then apply the
-- owner martingale convergence theorem
-- `MeasureTheory.martingale_convergence_to_memLp_limitProcess_of_lp_bounded` at `p = 2` to pass
-- from uniform `L²` boundedness to almost-sure and `L²` convergence, while the implications
-- `(iv) → (iii) → (i)` are immediate.
/-- Corollary 11.11: for a square-integrable discrete-time martingale with canonical square
variation process `⟨X⟩[ℱ, μ]`, the following are equivalent:
(i) the second moments `μ[(X n)^2]` are uniformly bounded;
(ii) the expectations of the square variation converge to a finite limit;
(iii) the martingale converges in `L²` to the canonical limit `ℱ.limitProcess X μ`;
(iv) the martingale converges almost surely and in `L²` to `ℱ.limitProcess X μ`. -/
theorem square_integrable_martingale_tfae {X : ℕ → Ω → ℝ}
    (hX : Martingale X ℱ μ) (hX2 : ∀ n, MemLp (X n) 2 μ) :
    let squareVariation : ℕ → Ω → ℝ := predictablePart (fun n ω ↦ X n ω ^ 2) ℱ μ
    let uniformlyBoundedSecondMoments : Prop :=
      Exists fun C : ℝ ↦ ∀ n, μ[fun ω ↦ X n ω ^ 2] ≤ C
    let convergentSquareVariationExpectation : Prop :=
      Exists fun a : ℝ ↦ Tendsto (fun n ↦ μ[squareVariation n]) atTop (𝓝 a)
    List.TFAE [
      uniformlyBoundedSecondMoments,
      convergentSquareVariationExpectation,
      TendstoInLp 2 μ X (ℱ.limitProcess X μ),
      (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
        TendstoInLp 2 μ X (ℱ.limitProcess X μ)
    ] := by
  classical
  let hXsq : ∀ n, Integrable (fun ω ↦ X n ω ^ 2) μ :=
    integrable_squareProcess_of_memLpTwo (X := X) hX2
  -- Proof comment: after unfolding the three local abbreviations, the theorem is a four-way TFAE
  -- whose nontrivial ingredients are the scalar square-variation identity and Theorem 11.10 at
  -- `p = 2`.
  dsimp
  tfae_have 1 ↔ 2 := by
    constructor
    · rintro ⟨C, hC⟩
      let secondMoment : ℕ → ℝ := fun n ↦ μ[fun ω ↦ X n ω ^ 2]
      have hMono : Monotone secondMoment :=
        martingaleSecondMomentMonotone (X := X) hX hXsq
      have hBdd : BddAbove (Set.range secondMoment) := by
        refine ⟨C, ?_⟩
        rintro _ ⟨n, rfl⟩
        exact hC n
      refine ⟨iSup secondMoment - secondMoment 0, ?_⟩
      have hSecondMomentTendsto :
          Tendsto secondMoment atTop (𝓝 (iSup secondMoment)) :=
        tendsto_atTop_ciSup hMono hBdd
      have hRewrite :
          (fun n ↦ μ[⟨X⟩[ℱ, μ] n]) = fun n ↦ secondMoment n - secondMoment 0 := by
        funext n
        exact squareVariationExpectation_eq_secondMomentDiff (X := X) hX hXsq n
      -- Proof comment: rewrite the square-variation expectation as a translated monotone scalar
      -- sequence.
      rw [hRewrite]
      exact hSecondMomentTendsto.sub tendsto_const_nhds
    · rintro ⟨a, ha⟩
      let secondMoment : ℕ → ℝ := fun n ↦ μ[fun ω ↦ X n ω ^ 2]
      have hSecondMomentTendsto :
          Tendsto secondMoment atTop (𝓝 (a + secondMoment 0)) := by
        -- Proof comment: add back the fixed initial second moment as an explicitly typed constant
        -- sequence.
        have hAdd :
            Tendsto (fun n ↦ μ[⟨X⟩[ℱ, μ] n] + secondMoment 0) atTop
              (𝓝 (a + secondMoment 0)) := by
          exact ha.add
            (tendsto_const_nhds :
              Tendsto (fun _ : ℕ ↦ secondMoment 0) atTop (𝓝 (secondMoment 0)))
        refine Tendsto.congr' ?_ hAdd
        exact Filter.Eventually.of_forall fun n ↦ by
          calc
            μ[⟨X⟩[ℱ, μ] n] + secondMoment 0 = (secondMoment n - secondMoment 0) + secondMoment 0 := by
              rw [squareVariationExpectation_eq_secondMomentDiff (X := X) hX hXsq n]
            _ = secondMoment n := by ring
      rcases hSecondMomentTendsto.bddAbove_range with ⟨C, hC⟩
      exact ⟨C, fun n ↦ hC (Set.mem_range_self n)⟩
  tfae_have 1 → 4 := by
    intro hBound
    have hp : 1 < (2 : ℝ) := by
      norm_num
    obtain ⟨R, hR⟩ :=
      lpTwoBound_of_uniformSecondMomentBound (X := X) hX2 hBound
    have hR' : ∀ n, eLpNorm (X n) (ENNReal.ofReal (2 : ℝ)) μ ≤ R := by
      -- Proof comment: the owner theorem is stated with the real exponent `p`, so we align the
      -- `p = 2` spelling once here.
      simpa using hR
    obtain ⟨_, _, hAe, hLp⟩ :=
      MeasureTheory.martingale_convergence_to_memLp_limitProcess_of_lp_bounded
        (X := X) (ℱ := ℱ) (μ := μ) (p := 2) hX hp ⟨R, hR'⟩
    -- Proof comment: Theorem 11.10 gives both almost-sure convergence and the owner `L²`
    -- convergence to the canonical limit process.
    exact ⟨by simpa using hAe, by simpa using hLp⟩
  tfae_have 4 → 3 := by
    intro h
    exact h.2
  tfae_have 3 → 1 := by
    intro hLp
    -- Proof comment: a convergent sequence in the canonical `Lp` space has bounded norms, hence
    -- bounded second moments at exponent `2`.
    exact uniformSecondMomentBound_of_tendstoInLpTwo (X := X) hLp
  tfae_finish
