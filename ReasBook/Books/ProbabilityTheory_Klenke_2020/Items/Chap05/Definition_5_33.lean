/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Definition 5.33: a Poisson process with intensity `α` under `μ` is a stochastic
nondecreasing counting process that starts at `0`, has independent increments, and whose
increments over `(s,t]` have Poisson law with parameter `α * (t - s)`. For an `ℕ`-valued process,
the monotonicity field makes the increment `N t - N s` the genuine interval count on `(s,t]`,
rather than truncated subtraction. -/
/-- A process on `[0,∞)` is Poisson with intensity `α` under `μ` if it is stochastic, starts at
`0`, is nondecreasing, has independent increments, and every increment over `(s,t]` has Poisson
law with parameter `α * (t - s)`. -/
class IsPoissonProcess (α : NNReal) (μ : Measure Ω) (N : NNReal → Ω → ℕ) : Prop where
  /-- A Poisson process is, in particular, a stochastic process. -/
  stochastic : IsStochasticProcess N
  /-- A Poisson process starts at `0`. -/
  zero : N 0 = 0
  /-- A Poisson process is a nondecreasing counting process. -/
  mono : Monotone N
  /-- Poisson processes have independent increments. -/
  indepIncrements : HasIndepIncrements N μ
  /-- Every increment over `(s,t]` has the expected Poisson law. -/
  poisson_increment :
    ∀ ⦃s t : NNReal⦄, s ≤ t →
      HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (α * (t - s))) μ

/- Definition 5.33: the chapter's canonical notion of a Poisson process with intensity `α` under
`μ` is `IsPoissonProcess α μ N`. The companion declarations below restate the textbook
`N 0 = 0` + monotone counting-process + independent increments + strict Poisson increment-law
formulation in terms of this canonical API. -/
recall IsPoissonProcess

namespace IsPoissonProcess

/-- Any Poisson process is defined over a probability measure, since each positive-time increment
has Poisson law. -/
theorem isProbabilityMeasure
    {N : NNReal → Ω → ℕ} {μ : Measure Ω} {α : NNReal} (hN : IsPoissonProcess α μ N) :
    IsProbabilityMeasure μ := by
  let hLaw :
      HasLaw (fun ω ↦ N 1 ω - N 0 ω) (poissonMeasure (α * (1 - 0))) μ :=
    hN.poisson_increment (show (0 : NNReal) ≤ 1 by norm_num)
  exact hLaw.isProbabilityMeasure

/-- The textbook strict-increment formulation is an immediate corollary of the `s ≤ t` increment
law. -/
theorem poisson_increment_of_lt
    {N : NNReal → Ω → ℕ} {μ : Measure Ω} {α : NNReal}
    (hN : IsPoissonProcess α μ N) {s t : NNReal} (hst : s < t) :
    HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (α * (t - s))) μ :=
  hN.poisson_increment (le_of_lt hst)

/-- The marginal law at time `t` is the Poisson law with parameter `α t`. -/
theorem poisson_law
    {N : NNReal → Ω → ℕ} {μ : Measure Ω} {α : NNReal}
    (hN : IsPoissonProcess α μ N) (t : NNReal) :
    HasLaw (N t) (poissonMeasure (α * t)) μ := by
  letI := hN.isProbabilityMeasure
  simpa [hN.zero] using
    (show HasLaw (fun ω ↦ N t ω - N 0 ω) (poissonMeasure (α * (t - 0))) μ from
      hN.poisson_increment (show (0 : NNReal) ≤ t from bot_le))

end IsPoissonProcess

/-- Helper for Definition 5.33: independent increments already force the ambient measure to be a
probability measure. -/
lemma hasIndepIncrementsIsProbabilityMeasure
    {N : NNReal → Ω → ℕ} {μ : Measure Ω} (hindep : HasIndepIncrements N μ) :
    IsProbabilityMeasure μ := by
  -- Proof comment: apply the increment-independence axiom to the constant time grid `t_i = 0`.
  exact (hindep.nat (t := fun _ : ℕ ↦ (0 : NNReal)) fun _ _ _ ↦ le_rfl).isProbabilityMeasure

/-- Helper for Definition 5.33: the Poisson measure at rate `r` has singleton mass
`poissonPMFReal r n` at `n`. -/
private lemma poissonMeasure_apply_singleton (r : NNReal) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Proof comment: rewrite `poissonMeasure` as the measure associated to the Poisson PMF.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

/-- Helper for Definition 5.33: the zero-rate Poisson law is the Dirac mass at `0`. -/
lemma poissonMeasureZeroEqDirac :
    (poissonMeasure (0 : NNReal) : Measure ℕ) = Measure.dirac 0 := by
  -- Proof comment: on `ℕ`, it suffices to compare singleton masses.
  refine Measure.ext_of_singleton fun n ↦ ?_
  by_cases hn : n = 0
  · subst hn
    simp [poissonMeasure_apply_singleton, poissonPMFReal]
  · simp [poissonMeasure_apply_singleton, poissonPMFReal, hn, zero_pow hn]

/-- Helper for Definition 5.33: under a probability measure, the constant zero random variable has
the zero-rate Poisson law. -/
lemma hasLawZeroPoissonMeasureZero
    {μ : Measure Ω} [IsProbabilityMeasure μ] :
    HasLaw (fun _ : Ω ↦ (0 : ℕ)) (poissonMeasure 0) μ := by
  refine ⟨measurable_const.aemeasurable, ?_⟩
  -- Proof comment: mapping a probability measure through a constant gives the matching Dirac mass.
  rw [Measure.map_const]
  simp [poissonMeasureZeroEqDirac]

/-- Helper for Definition 5.33: the constant zero process has independent increments. -/
lemma zeroProcessHasIndepIncrements
    {μ : Measure Ω} [IsProbabilityMeasure μ] :
    HasIndepIncrements (fun _ _ ↦ (0 : ℕ) : NNReal → Ω → ℕ) μ := by
  refine HasIndepIncrements.of_nat (X := (fun _ _ ↦ (0 : ℕ) : NNReal → Ω → ℕ)) ?_
  intro t ht htconst
  -- Proof comment: every increment is the constant zero random variable, so each measurable event
  -- is either `∅` or `univ`, and the independence identity is tautological.
  simpa using
    (show iIndepFun (fun _ (_ : Ω) ↦ (0 : ℕ)) μ from by
      rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
      intro s sets hsets
      classical
      by_cases hempty : ∃ i ∈ s, (0 : ℕ) ∉ sets i
      · rcases hempty with ⟨i, hi, hnot⟩
        have hpreimage_empty :
            (fun _ : Ω ↦ (0 : ℕ)) ⁻¹' sets i = ∅ := by
          ext ω
          simp [hnot]
        have hinter : (⋂ j ∈ s, (fun _ : Ω ↦ (0 : ℕ)) ⁻¹' sets j) = ∅ := by
          rw [Set.iInter₂_eq_empty_iff]
          intro ω
          refine ⟨i, hi, ?_⟩
          simp [hnot]
        have hprod_zero : ∏ j ∈ s, μ ((fun _ : Ω ↦ (0 : ℕ)) ⁻¹' sets j) = 0 := by
          exact Finset.prod_eq_zero hi (by simp [hpreimage_empty])
        rw [hinter, measure_empty]
        rw [hprod_zero]
      · have hmem : ∀ i ∈ s, (0 : ℕ) ∈ sets i := by
          intro i hi
          by_contra hnot
          exact hempty ⟨i, hi, hnot⟩
        have hpreimage_univ :
            ∀ i ∈ s, (fun _ : Ω ↦ (0 : ℕ)) ⁻¹' sets i = Set.univ := by
          intro i hi
          ext ω
          simp [hmem i hi]
        have hinter : (⋂ j ∈ s, (fun _ : Ω ↦ (0 : ℕ)) ⁻¹' sets j) = Set.univ := by
          refine Set.eq_univ_iff_forall.2 fun ω ↦ ?_
          exact Set.mem_iInter₂.2 fun i hi ↦ by simp [hmem i hi]
        have hprod_one : ∏ j ∈ s, μ ((fun _ : Ω ↦ (0 : ℕ)) ⁻¹' sets j) = 1 := by
          refine Finset.prod_eq_one fun i hi ↦ ?_
          rw [hpreimage_univ i hi]
          exact measure_univ
        rw [hinter, hprod_one]
        simp)

/-- Definition 5.33, source-facing bridge: a stochastic nondecreasing counting process that starts
at `0`, has independent increments, and whose strict increments have Poisson laws is a Poisson
process in the chapter's canonical sense. -/
theorem isPoissonProcess_of_textbook
    {N : NNReal → Ω → ℕ} {μ : Measure Ω} {α : NNReal}
    (hstochastic : IsStochasticProcess N)
    (hzero : N 0 = 0)
    (hmono : Monotone N)
    (hindep : HasIndepIncrements N μ)
    (hpoisson : ∀ ⦃s t : NNReal⦄, s < t →
      HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (α * (t - s))) μ) :
    IsPoissonProcess α μ N := by
  refine
    { stochastic := hstochastic
      zero := hzero
      mono := hmono
      indepIncrements := hindep
      poisson_increment := ?_ }
  intro s t hst
  letI : IsProbabilityMeasure μ := hasIndepIncrementsIsProbabilityMeasure hindep
  -- Proof comment: split the nonstrict endpoint case into the strict textbook case and the
  -- degenerate zero-length increment.
  rcases lt_or_eq_of_le hst with hlt | rfl
  · exact hpoisson hlt
  · simpa using (hasLawZeroPoissonMeasureZero (μ := μ) (Ω := Ω))

/-- The constant zero counting process is a Poisson process with intensity `0`. -/
instance (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsPoissonProcess 0 μ (fun _ _ ↦ 0) := by
  -- Proof comment: the zero process satisfies the textbook axioms, and the bridge theorem handles
  -- the endpoint `s = t` case uniformly.
  refine isPoissonProcess_of_textbook
    (hstochastic := isStochasticProcess_const 0)
    (hzero := rfl)
    (hmono := monotone_const)
    (hindep := zeroProcessHasIndepIncrements (μ := μ))
    (hpoisson := ?_)
  intro s t hst
  -- Proof comment: every strict increment of the zero process is constant `0`, so its law is the
  -- zero-rate Poisson law.
  simpa using (hasLawZeroPoissonMeasureZero (μ := μ) (Ω := Ω))
