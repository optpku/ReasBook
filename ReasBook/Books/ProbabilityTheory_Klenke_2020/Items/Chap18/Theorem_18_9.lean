/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/-- Helper for Theorem 18.9: the time-`n` law of a Markov-process realization evaluates
expectations by integrating against the `n`-step kernel row. -/
lemma markovRealization_integral_comp_transition_eq
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {g : E → ℝ} (x : E) (n : ℕ) :
    (P x : Measure Ω)[fun ω ↦ g (X n ω)] =
      ∫ z, g z ∂((discreteMatrixKernel p ^ n) x) := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hXn : Measurable (X n) := hReal.measurable_process n
  -- Move the observable to the one-time marginal of the realization, then rewrite that marginal
  -- with the prescribed `n`-step transition law.
  rw [← hReal.transition_eq x n, integral_map]
  · exact hXn.aemeasurable
  · exact (Measurable.of_discrete : Measurable g).aestronglyMeasurable

/-- Helper for Theorem 18.9: a bounded harmonic function for `discreteMatrixKernel p` is fixed by
every kernel power. -/
lemma harmonicIntegral_pow_eq
    {p : E → E → ℝ≥0∞} [IsMarkovKernel (discreteMatrixKernel p)]
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) :
    ∀ n : ℕ, ∀ x : E, ∫ z, f z ∂((discreteMatrixKernel p ^ n) x) = f x := by
  let κ : Kernel E E := discreteMatrixKernel p
  rcases hf_harmonic with ⟨_, hharmonic⟩
  obtain ⟨R₀, hR₀⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range f) hf_bdd
  let R : ℝ := max R₀ 1
  have hRbound : ∀ z : E, |f z| ≤ R := by
    intro z
    exact (hR₀ (f z) ⟨z, rfl⟩).trans (le_max_left _ _)
  intro n
  induction n with
  | zero =>
      intro x
      -- At time `0`, the kernel power is `Kernel.id`, so the integral is evaluation at `x`.
      change ∫ z, f z ∂(Kernel.id x) = f x
      simpa [Kernel.id_apply] using (integral_dirac f x)
  | succ n ih =>
      intro x
      have hint : Integrable f ((κ ^ (n + 1)) x) := by
        let _ : IsFiniteMeasure ((κ ^ (n + 1)) x) := by infer_instance
        refine Integrable.of_bound
          ((Measurable.of_discrete : Measurable f).aestronglyMeasurable) R ?_
        exact ae_of_all _ fun z ↦ hRbound z
      have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
      have hintComp : Integrable f ((κ ∘ₖ (κ ^ n)) x) := by
        simpa [hpow] using hint
      -- Rewrite the `n + 1` step average as one more kernel application, then use the
      -- one-step harmonicity identity pointwise.
      calc
        ∫ z, f z ∂((κ ^ (n + 1)) x)
          = ∫ z, f z ∂((κ ∘ₖ (κ ^ n)) x) := by
              rw [hpow]
        _ = ∫ y, ∫ z, f z ∂κ y ∂((κ ^ n) x) := by
              simpa using
                (ProbabilityTheory.Kernel.integral_comp
                  (η := κ) (κ := κ ^ n) (a := x) hintComp)
        _ = ∫ y, f y ∂((κ ^ n) x) := by
              refine integral_congr_ae ?_
              exact ae_of_all _ fun y ↦ (hharmonic y).symm
        _ = f x := ih x

/-- Helper for Theorem 18.9: along any realization of the kernel powers, the expectation of a
bounded harmonic function stays equal to its starting value. -/
lemma harmonicExpectation_eq_start_of_realization
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) (x : E) :
    ∀ n : ℕ, (P x : Measure Ω)[fun ω ↦ f (X n ω)] = f x := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hMarkov : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  let _ : IsMarkovKernel (discreteMatrixKernel p) := hMarkov
  intro n
  -- Route correction: instead of the broken martingale import, rewrite the realization
  -- expectation through the `n`-step kernel row and use harmonic invariance under kernel powers.
  calc
    (P x : Measure Ω)[fun ω ↦ f (X n ω)]
      = ∫ z, f z ∂((discreteMatrixKernel p ^ n) x) := by
          simpa using
            (markovRealization_integral_comp_transition_eq
              (p := p) (P := P) (X := X) (g := f) x n)
    _ = f x := harmonicIntegral_pow_eq (p := p) (f := f) hf_bdd hf_harmonic n x

/-- Helper for Theorem 18.9: under a successful coupling, the probability of disagreement at a
fixed time tends to `0`. -/
lemma successfulCoupling_disagreementProb_tendsto_zero
    {p : E → E → ℝ≥0∞}
    {P : E × E → ProbabilityMeasure Ω} {Z : ℕ → Ω → E × E}
    (hsuccess : IsSuccessfulMarkovCoupling p P Z) (x y : E) :
    Tendsto
      (fun n ↦ (P (x, y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2})
      atTop (nhds 0) := by
  let μ : Measure Ω := (P (x, y) : Measure Ω)
  let tailDisagreement : ℕ → Set Ω :=
    fun n ↦ ⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}
  have hmono :
      ∀ n, μ {ω | (Z n ω).1 ≠ (Z n ω).2} ≤ μ (tailDisagreement n) := by
    intro n
    refine measure_mono ?_
    intro ω hω
    exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨le_rfl, hω⟩⟩
  -- The time-`n` disagreement event sits inside the tail event by choosing the witness `m = n`,
  -- so the fixed-time probabilities are squeezed by the tail probabilities that already converge.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hsuccess.tail_disagreement_tendsto_zero x y) (fun n ↦ zero_le _) ?_
  intro n
  simpa [μ, tailDisagreement] using hmono n

/-- Helper for Theorem 18.9: a bounded observable can differ only on the disagreement event of
two processes, and its expected absolute difference is controlled by that event's probability. -/
lemma integral_abs_coordDifference_le_twoMul_disagreementProb
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : E → ℝ} {X Y : Ω → E} {R : ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hR : 0 ≤ R)
    (hbound : ∀ z : E, |f z| ≤ R)
    (hintegrable : Integrable (fun ω ↦ f (X ω) - f (Y ω)) μ) :
    μ[fun ω ↦ |f (X ω) - f (Y ω)|] ≤ (2 * R) * μ.real {ω | X ω ≠ Y ω} := by
  let supportSet : Set Ω := {ω | f (X ω) - f (Y ω) ≠ 0}
  have hsupportSet : MeasurableSet supportSet := by
    have hdiffMeas : Measurable fun ω ↦ f (X ω) - f (Y ω) :=
      ((Measurable.of_discrete : Measurable f).comp hX).sub
        ((Measurable.of_discrete : Measurable f).comp hY)
    have hzeroSet : MeasurableSet {ω | f (X ω) - f (Y ω) = 0} :=
      measurableSet_eq_fun hdiffMeas measurable_const
    convert hzeroSet.compl using 1
  have hindicator :
      Integrable (supportSet.indicator (fun _ : Ω ↦ (2 * R : ℝ))) μ :=
    (integrable_const (2 * R)).indicator hsupportSet
  have hsupport_subset : supportSet ⊆ {ω | X ω ≠ Y ω} := by
    intro ω hω
    by_contra hxy
    have hXY : X ω = Y ω := by simpa using hxy
    exact hω (by simp [hXY])
  have hpointwise :
      ∀ ω, |f (X ω) - f (Y ω)| ≤ supportSet.indicator (fun _ : Ω ↦ (2 * R : ℝ)) ω := by
    intro ω
    by_cases hω : f (X ω) - f (Y ω) ≠ 0
    · -- On the support of the difference, bound the difference by the sum of the two uniform
      -- bounds.
      simp [supportSet, hω]
      calc
        |f (X ω) - f (Y ω)| ≤ |f (X ω)| + |f (Y ω)| := by
          simpa [sub_eq_add_neg, abs_neg] using (norm_add_le (f (X ω)) (-f (Y ω)))
        _ ≤ R + R := add_le_add (hbound (X ω)) (hbound (Y ω))
        _ = 2 * R := by ring
    · -- Off the support, the absolute difference already vanishes.
      simp [supportSet, not_not.mp hω]
  have hsupportReal_le :
      μ.real supportSet ≤ μ.real {ω | X ω ≠ Y ω} := by
    exact ENNReal.toReal_mono (measure_ne_top μ {ω | X ω ≠ Y ω}) (measure_mono hsupport_subset)
  -- Compare the absolute difference with the indicator bound pointwise, then integrate the
  -- indicator explicitly.
  calc
    μ[fun ω ↦ |f (X ω) - f (Y ω)|]
      ≤ ∫ ω, supportSet.indicator (fun _ : Ω ↦ (2 * R : ℝ)) ω ∂μ := by
          exact integral_mono_ae hintegrable.norm hindicator (Filter.Eventually.of_forall hpointwise)
    _ = (2 * R) * μ.real supportSet := by
          rw [integral_indicator_const (2 * R) hsupportSet, smul_eq_mul]
          ring
    _ ≤ (2 * R) * μ.real {ω | X ω ≠ Y ω} := by
          exact mul_le_mul_of_nonneg_left hsupportReal_le (by positivity)

-- Proof sketch: choose a successful Markov coupling `Z` from `HasSuccessfulCoupling p`. For
-- each pair of starting states `x` and `y`, rewrite the expectations of `f ((Z n).1)` and
-- `f ((Z n).2)` through the realized `n`-step kernel rows and then use harmonicity to show that
-- both expectations stay fixed at `f x` and `f y`. The tail-disagreement hypothesis bounds the
-- time-`n` disagreement event, and boundedness forces `|f x - f y|` to vanish.
/-- Theorem 18.9: if the discrete Markov chain with transition matrix `p` admits a successful
coupling, then every bounded harmonic function for `p` is constant. -/
theorem bounded_harmonicFunction_constant_of_hasSuccessfulCoupling
    {p : E → E → ℝ≥0∞}
    (hcoupling : HasSuccessfulCoupling p)
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) :
    ∀ x y : E, f x = f y := by
  intro x y
  rcases hcoupling.exists_successfulCoupling with ⟨Ω, _, P, Z, hsuccess⟩
  obtain ⟨R₀, hR₀⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range f) hf_bdd
  let R : ℝ := max R₀ 1
  have hRpos : 0 < R := by
    simp [R]
  let μ : Measure Ω := (P (x, y) : Measure Ω)
  let X₁ : ℕ → Ω → E := fun n ω ↦ (Z n ω).1
  let X₂ : ℕ → Ω → E := fun n ω ↦ (Z n ω).2
  let disagreement : ℕ → Set Ω := fun n ↦ {ω | X₁ n ω ≠ X₂ n ω}
  have hbound : ∀ z : E, |f z| ≤ R := by
    intro z
    exact (hR₀ (f z) ⟨z, rfl⟩).trans (le_max_left _ _)
  have hreal₁ :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (fun x' ↦ P (x', y)) X₁ := by
    simpa [X₁] using hsuccess.fst_realization y
  have hreal₂ :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (fun y' ↦ P (x, y')) X₂ := by
    simpa [X₂] using hsuccess.snd_realization x
  have hexpect₁ : ∀ n, μ[fun ω ↦ f (X₁ n ω)] = f x := by
    let _ :
        IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n)
          (fun x' ↦ P (x', y)) X₁ := hreal₁
    -- Route correction: replace the unavailable martingale API by the direct realization
    -- expectation identity for harmonic functions.
    simpa [μ, X₁] using
      (harmonicExpectation_eq_start_of_realization
        (p := p) (P := fun x' ↦ P (x', y)) (X := X₁)
        (f := f) hf_bdd hf_harmonic x)
  have hexpect₂ : ∀ n, μ[fun ω ↦ f (X₂ n ω)] = f y := by
    let _ :
        IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n)
          (fun y' ↦ P (x, y')) X₂ := hreal₂
    simpa [μ, X₂] using
      (harmonicExpectation_eq_start_of_realization
        (p := p) (P := fun y' ↦ P (x, y')) (X := X₂)
        (f := f) hf_bdd hf_harmonic y)
  have hprob :
      Tendsto (fun n ↦ μ (disagreement n)) atTop (nhds 0) := by
    simpa [μ, disagreement, X₁, X₂] using
      (successfulCoupling_disagreementProb_tendsto_zero
        (Ω := Ω) (p := p) (P := P) (Z := Z) hsuccess x y)
  have hprobReal :
      Tendsto (fun n ↦ μ.real (disagreement n)) atTop (nhds 0) := by
    simpa [Measure.real] using
      ((ENNReal.tendsto_toReal_zero_iff
        (fun n ↦ measure_ne_top μ (disagreement n))).2 hprob)
  have hscaled :
      Tendsto (fun n ↦ (2 * R) * μ.real (disagreement n)) atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul (2 * R) hprobReal
  have hineq :
      ∀ n, |f x - f y| ≤ (2 * R) * μ.real (disagreement n) := by
    intro n
    have hmeas₁ : Measurable (X₁ n) := hreal₁.measurable_process n
    have hmeas₂ : Measurable (X₂ n) := hreal₂.measurable_process n
    have hcoordInt₁ : Integrable (fun ω ↦ f (X₁ n ω)) μ := by
      refine Integrable.of_bound
        (((Measurable.of_discrete : Measurable f).comp hmeas₁).aestronglyMeasurable) R ?_
      exact ae_of_all _ fun ω ↦ hbound (X₁ n ω)
    have hcoordInt₂ : Integrable (fun ω ↦ f (X₂ n ω)) μ := by
      refine Integrable.of_bound
        (((Measurable.of_discrete : Measurable f).comp hmeas₂).aestronglyMeasurable) R ?_
      exact ae_of_all _ fun ω ↦ hbound (X₂ n ω)
    have hdiffInt :
        Integrable (fun ω ↦ f (X₁ n ω) - f (X₂ n ω)) μ :=
      hcoordInt₁.sub hcoordInt₂
    -- Rewrite the difference of initial values as the expectation of the coordinate difference,
    -- then bound that expectation by the disagreement probability estimate.
    calc
      |f x - f y|
          = |μ[fun ω ↦ f (X₁ n ω)] - μ[fun ω ↦ f (X₂ n ω)]| := by
              rw [hexpect₁ n, hexpect₂ n]
      _ = |μ[fun ω ↦ f (X₁ n ω) - f (X₂ n ω)]| := by
            rw [integral_sub hcoordInt₁ hcoordInt₂]
      _ ≤ μ[fun ω ↦ |f (X₁ n ω) - f (X₂ n ω)|] := by
            simpa using
              (norm_integral_le_integral_norm (fun ω ↦ f (X₁ n ω) - f (X₂ n ω)) : _)
      _ ≤ (2 * R) * μ.real (disagreement n) := by
            simpa [disagreement] using
              (integral_abs_coordDifference_le_twoMul_disagreementProb
                (μ := μ) (f := f) (X := X₁ n) (Y := X₂ n) hmeas₁ hmeas₂
                (le_of_lt hRpos) hbound hdiffInt)
  have habs_le_zero : |f x - f y| ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hscaled hineq
  have habs_eq_zero : |f x - f y| = 0 :=
    le_antisymm habs_le_zero (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs_eq_zero)

end ProbabilityTheory
