/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_4_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Pointwise Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

local notation "nonnegativeLebesgue" => volume.restrict (Set.Ici (0 : ℝ))
attribute [local instance] Classical.propDecidable

section BrownianMotionExercise

variable [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {B : NNReal → Ω → ℝ}

/-- Helper for Exercise 21.2.1: every fixed Brownian marginal has mean `0`. -/
lemma brownianEval_expectation_eq_zero (hB : IsBrownianMotion μ B) (t : NNReal) :
    ∫ ω, B t ω ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  by_cases ht : t = 0
  · -- At time `0`, the Brownian path is identically zero.
    subst ht
    simp [hB.zero]
  · -- For positive times, transport the Gaussian mean through the marginal law.
    have ht_pos : 0 < t := pos_iff_ne_zero.mpr ht
    have hLaw : HasLaw (B t) (gaussianReal 0 t) μ := hB.gaussian_marginal ht_pos
    simpa using hLaw.integral_eq

/-- Helper for Exercise 21.2.1: every fixed Brownian marginal has variance equal to the time
parameter. -/
lemma brownianEval_variance_eq (hB : IsBrownianMotion μ B) (t : NNReal) :
    Var[B t; μ] = t := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  by_cases ht : t = 0
  · -- At time `0`, the marginal is constant and has variance `0`.
    subst ht
    simp [hB.zero]
  · -- Positive-time marginals are centered Gaussians with variance `t`.
    have ht_pos : 0 < t := pos_iff_ne_zero.mpr ht
    have hLaw : HasLaw (B t) (gaussianReal 0 t) μ := hB.gaussian_marginal ht_pos
    simpa using hLaw.variance_eq

/-- Helper for Exercise 21.2.1: Brownian increments over ordered times belong to `L²`. -/
lemma brownianIncrement_memLp_two (hB : IsBrownianMotion μ B) {s t : NNReal} (_hst : s ≤ t) :
    MemLp (fun ω ↦ B t ω - B s ω) 2 μ := by
  -- Proof comment: `L²` is stable under subtraction on a probability space, so no extra Gaussian
  -- calculation is needed here.
  exact (brownianEval_memLp_two hB t).sub (brownianEval_memLp_two hB s)

/-- Helper for Exercise 21.2.1: the covariance kernel of Brownian motion is `s ⊓ t`. -/
lemma brownianCovariance_eq_min (hB : IsBrownianMotion μ B) (s t : NNReal) :
    cov[B s, B t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Route correction: keep the covariance proof local so this file no longer depends on the later
  -- Brownian-owner module.
  wlog hst : s ≤ t generalizing s t with hswap
  · rw [covariance_comm, inf_comm]
    exact hswap t s (le_of_not_ge hst)
  have hs_mem : MemLp (B s) 2 μ := brownianEval_memLp_two (μ := μ) (X := B) hB s
  have hInc_mem : MemLp (fun ω ↦ B t ω - B s ω) 2 μ :=
    brownianIncrement_memLp_two (μ := μ) (B := B) hB hst
  have hIndep :
      (B s) ⟂ᵢ[μ] (fun ω ↦ B t ω - B s ω) :=
    hB.indepIncrements.indepFun_eval_sub (show (0 : NNReal) ≤ s by simp) hst
      (Filter.Eventually.of_forall fun ω ↦ by simp [hB.zero])
  have hSplit :
      B t = fun ω ↦ B s ω + (B t ω - B s ω) := by
    funext ω
    ring
  have hVarS : Var[B s; μ] = (s : ℝ) := by
    simpa using brownianEval_variance_eq (μ := μ) (B := B) hB s
  rw [hSplit]
  change cov[B s, B s + (fun ω ↦ B t ω - B s ω); μ] = ((s ⊓ t : NNReal) : ℝ)
  rw [covariance_add_right hs_mem hs_mem hInc_mem, hIndep.covariance_eq_zero hs_mem hInc_mem,
    covariance_self hs_mem.aemeasurable, hVarS]
  simp [inf_eq_left.mpr hst]

/-- Helper for Exercise 21.2.1: covariance is unchanged by almost-everywhere replacement of either
argument. -/
private lemma covariance_congr_ae {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  -- Proof comment: rewrite both expectations by almost-sure equality, then rewrite the covariance
  -- integrand pointwise.
  have hIntX : μ[X] = μ[X'] := integral_congr_ae hX
  have hIntY : μ[Y] = μ[Y'] := integral_congr_ae hY
  rw [covariance, covariance]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for Exercise 21.2.1: every positive-time Brownian marginal hits `0` with probability
zero. -/
lemma brownianFixedTime_zero_prob_eq_zero (hB : IsBrownianMotion μ B) {t : ℝ} (ht : 0 < t) :
    μ {ω | B (Real.toNNReal t) ω = 0} = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have ht_nnreal_pos : 0 < Real.toNNReal t := by
    exact Real.toNNReal_pos.mpr ht
  have hLaw : HasLaw (B (Real.toNNReal t)) (gaussianReal 0 (Real.toNNReal t)) μ :=
    hB.gaussian_marginal ht_nnreal_pos
  have hMeas : Measurable (B (Real.toNNReal t)) := (hB.stronglyMeasurable _).measurable
  calc
    μ {ω | B (Real.toNNReal t) ω = 0}
        = μ.map (B (Real.toNNReal t)) ({0} : Set ℝ) := by
            symm
            rw [Measure.map_apply hMeas (MeasurableSet.singleton 0)]
            rfl
    _ = gaussianReal 0 (Real.toNNReal t) ({0} : Set ℝ) := by rw [hLaw.map_eq]
    _ = 0 := by
          exact (noAtoms_gaussianReal (ne_of_gt ht_nnreal_pos)).measure_singleton 0

/-- Helper for Exercise 21.2.1: the deterministic covariance kernel average
`∫₀¹ (s - s^2 / 2) ds` equals `1 / 3`. -/
lemma brownianAverageKernelIntegral_eq_one_third :
    ∫ s in (0 : ℝ)..1, (s - s ^ 2 / 2 : ℝ) = 1 / 3 := by
  -- This is the polynomial antiderivative left after integrating `min(s,t)` in one variable.
  norm_num [integral_pow]

/-- Helper for Exercise 21.2.1: the deterministic centered-variance integral
`∫₀¹ t^2 / 2 dt` equals `1 / 6`. -/
lemma brownianCenteredVarianceIntegral_eq_one_six :
    ∫ t in (0 : ℝ)..1, (t ^ 2 / 2 : ℝ) = 1 / 6 := by
  -- This is the one-variable polynomial integral used in part `(iii)`.
  norm_num [integral_pow]

/-- Helper for Exercise 21.2.1: the centered variance polynomial `t ^ 2 - t + 1 / 3` integrates
to `1 / 6` on `[0,1]`. -/
lemma brownianCenteredVariancePolynomialIntegral_eq_one_six :
    ∫ t in (0 : ℝ)..1, (t ^ 2 - t + 1 / 3 : ℝ) = 1 / 6 := by
  -- Proof comment: the linear and constant terms combine with `∫₀¹ t²/2 dt = 1/6`.
  norm_num [integral_pow]

/-- Helper for Exercise 21.2.1: after the symmetric kernel-square reduction to the triangular
region, the remaining polynomial integral equals `1 / 180`. -/
lemma centeredAverageKernelTriangleIntegral_eq_one_over_ninety :
    ∫ s in (0 : ℝ)..1,
      ((7 / 15 : ℝ) * s ^ 5 - (4 / 3 : ℝ) * s ^ 4 + (13 / 9 : ℝ) * s ^ 3 -
        (2 / 3 : ℝ) * s ^ 2 + (1 / 9 : ℝ) * s) = 1 / 180 := by
  -- Proof comment: once the stochastic kernel has already been reduced to this explicit
  -- polynomial, the remaining work is still just deterministic calculus.
  have hpowInt (n : ℕ) : IntervalIntegrable (fun s : ℝ ↦ s ^ n) volume 0 1 := by
    exact (continuous_id.pow n).intervalIntegrable 0 1
  have h54 :
      IntervalIntegrable
        (fun s : ℝ ↦ (7 / 15 : ℝ) * s ^ 5 - (4 / 3 : ℝ) * s ^ 4) volume 0 1 := by
    exact ((hpowInt 5).const_mul (7 / 15 : ℝ)).sub ((hpowInt 4).const_mul (4 / 3 : ℝ))
  have h543 :
      IntervalIntegrable
        (fun s : ℝ ↦
          ((7 / 15 : ℝ) * s ^ 5 - (4 / 3 : ℝ) * s ^ 4) + (13 / 9 : ℝ) * s ^ 3) volume 0 1 := by
    exact h54.add ((hpowInt 3).const_mul (13 / 9 : ℝ))
  have h5432 :
      IntervalIntegrable
        (fun s : ℝ ↦
          (((7 / 15 : ℝ) * s ^ 5 - (4 / 3 : ℝ) * s ^ 4) + (13 / 9 : ℝ) * s ^ 3) -
            (2 / 3 : ℝ) * s ^ 2) volume 0 1 := by
    exact h543.sub ((hpowInt 2).const_mul (2 / 3 : ℝ))
  have h1 :
      IntervalIntegrable (fun s : ℝ ↦ (1 / 9 : ℝ) * s) volume 0 1 := by
    exact continuous_id.intervalIntegrable 0 1 |>.const_mul (1 / 9 : ℝ)
  have hid : ∫ s in (0 : ℝ)..1, (s : ℝ) = 1 / 2 := by
    norm_num [integral_pow]
  rw [intervalIntegral.integral_add h5432 h1]
  rw [intervalIntegral.integral_sub h543 ((hpowInt 2).const_mul (2 / 3 : ℝ))]
  rw [intervalIntegral.integral_add h54 ((hpowInt 3).const_mul (13 / 9 : ℝ))]
  rw [intervalIntegral.integral_sub ((hpowInt 5).const_mul (7 / 15 : ℝ))
    ((hpowInt 4).const_mul (4 / 3 : ℝ))]
  have hLast : ∫ s in (0 : ℝ)..1, (1 / 9 : ℝ) * s = 1 / 18 := by
    rw [intervalIntegral.integral_const_mul, hid]
    norm_num
  rw [hLast]
  norm_num [integral_pow, intervalIntegral.integral_const_mul]

/-- Helper for Exercise 21.2.1: the bad continuity set of the Brownian sample paths. -/
def brownianDiscontinuitySet (_hB : IsBrownianMotion μ B) : Set Ω :=
  {ω | ¬ Continuous (fun t : NNReal ↦ B t ω)}

/-- Helper for Exercise 21.2.1: the Brownian discontinuity set is null. -/
lemma brownianDiscontinuitySet_null (hB : IsBrownianMotion μ B) :
    μ (brownianDiscontinuitySet (μ := μ) (B := B) hB) = 0 := by
  -- Proof comment: almost-sure continuity says precisely that the complement of the bad set has
  -- full measure.
  have hcont_ae : ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ B t ω) := by
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hB.continuous_paths
  simpa [brownianDiscontinuitySet] using (ae_iff.mp hcont_ae)

/-- Helper for Exercise 21.2.1: choose a measurable null superset of the discontinuity set so the
patched process can be defined without measurability issues. -/
lemma brownianContinuousVersionExceptionSet_exists (hB : IsBrownianMotion μ B) :
    ∃ N : Set Ω,
      brownianDiscontinuitySet (μ := μ) (B := B) hB ⊆ N ∧ MeasurableSet N ∧ μ N = 0 := by
  -- Proof comment: enlarge the null bad set to a measurable null set once and for all.
  exact exists_measurable_superset_of_null (brownianDiscontinuitySet_null (μ := μ) (B := B) hB)

/-- Helper for Exercise 21.2.1: the measurable null exceptional set used to patch the Brownian
paths. -/
def brownianContinuousVersionExceptionSet (hB : IsBrownianMotion μ B) : Set Ω :=
  Classical.choose (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)

/-- Helper for Exercise 21.2.1: the discontinuity set is contained in the chosen exceptional set.
-/
lemma brownianDiscontinuitySet_subset_exceptionSet (hB : IsBrownianMotion μ B) :
    brownianDiscontinuitySet (μ := μ) (B := B) hB ⊆
      brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB :=
  (Classical.choose_spec (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).1

/-- Helper for Exercise 21.2.1: the chosen exceptional set is measurable. -/
lemma brownianContinuousVersionExceptionSet_measurable (hB : IsBrownianMotion μ B) :
    MeasurableSet (brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB) :=
  (Classical.choose_spec (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).2.1

/-- Helper for Exercise 21.2.1: the chosen exceptional set is null. -/
lemma brownianContinuousVersionExceptionSet_null (hB : IsBrownianMotion μ B) :
    μ (brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB) = 0 :=
  (Classical.choose_spec (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).2.2

/-- Helper for Exercise 21.2.1: patch the Brownian motion by setting it equal to `0` on the
measurable null exceptional set. -/
def brownianContinuousVersion (hB : IsBrownianMotion μ B) : NNReal → Ω → ℝ :=
  fun t ω ↦
    if ω ∈ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB then 0 else B t ω

/-- Helper for Exercise 21.2.1: each time slice of the patched process is measurable. -/
lemma brownianContinuousVersion_measurable (hB : IsBrownianMotion μ B) :
    ∀ t, Measurable (brownianContinuousVersion (μ := μ) (B := B) hB t) := by
  -- Proof comment: the patch is a measurable piecewise combination of the constant zero slice and
  -- the original measurable Brownian slice.
  intro t
  change Measurable
    (fun ω ↦
      if ω ∈ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB then (0 : ℝ) else B t ω)
  exact Measurable.ite
    (brownianContinuousVersionExceptionSet_measurable (μ := μ) (B := B) hB)
    measurable_const ((hB.stronglyMeasurable t).measurable)

/-- Helper for Exercise 21.2.1: every sample path of the patched process is continuous. -/
lemma brownianContinuousVersion_continuous (hB : IsBrownianMotion μ B) :
    ∀ ω, Continuous (fun t ↦ brownianContinuousVersion (μ := μ) (B := B) hB t ω) := by
  -- Proof comment: outside the exceptional set the path is the original Brownian path; inside the
  -- exceptional set the patch is the constant zero path.
  classical
  intro ω
  by_cases hω :
      ω ∈ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB
  · simpa [brownianContinuousVersion, hω] using
      (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  · have hcont : Continuous (fun t : NNReal ↦ B t ω) := by
      by_contra hnot
      exact hω <|
        brownianDiscontinuitySet_subset_exceptionSet (μ := μ) (B := B) hB
          (by simpa [brownianDiscontinuitySet] using hnot)
    simpa [brownianContinuousVersion, hω] using hcont

/-- Helper for Exercise 21.2.1: outside the exceptional set, the patched process agrees with the
original Brownian motion at every time. -/
lemma brownianContinuousVersion_ae_eq (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      brownianContinuousVersion (μ := μ) (B := B) hB t ω = B t ω := by
  -- Proof comment: the patch only modifies paths on the measurable null exceptional set.
  have hN_ae :
      ∀ᵐ ω ∂μ,
        ω ∉ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB := by
    exact compl_mem_ae_iff.mpr
      (brownianContinuousVersionExceptionSet_null (μ := μ) (B := B) hB)
  filter_upwards [hN_ae] with ω hω t
  change
    (if ω ∈ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB then (0 : ℝ) else B t ω) =
      B t ω
  simp [hω]

/-- Helper for Exercise 21.2.1: the patched process is a modification of the original Brownian
motion. -/
lemma brownianContinuousVersion_areModifications (hB : IsBrownianMotion μ B) :
    AreModifications μ B (brownianContinuousVersion (μ := μ) (B := B) hB) := by
  -- Proof comment: `AreModifications` is fixed-time almost-everywhere equality, which follows from
  -- the pointwise-off-null equality of the patch.
  intro t
  filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  simpa using (hω t).symm

/-- Helper for Exercise 21.2.1: package the patch as an everywhere continuous measurable
modification of the original Brownian motion. -/
lemma brownianContinuousVersion_spec (hB : IsBrownianMotion μ B) :
    (∀ t, Measurable (brownianContinuousVersion (μ := μ) (B := B) hB t)) ∧
      (∀ ω, Continuous (fun t ↦ brownianContinuousVersion (μ := μ) (B := B) hB t ω)) ∧
      AreModifications μ B (brownianContinuousVersion (μ := μ) (B := B) hB) := by
  -- Proof comment: this is the stable interface used later for the Fubini/Tonelli arguments.
  exact
    ⟨brownianContinuousVersion_measurable (μ := μ) (B := B) hB,
      brownianContinuousVersion_continuous (μ := μ) (B := B) hB,
      brownianContinuousVersion_areModifications (μ := μ) (B := B) hB⟩

/-- Helper for Exercise 21.2.1: the unit-interval path integral of the patched process agrees
almost surely with the original Brownian path integral. -/
lemma brownianContinuousVersion_average_ae_eq (hB : IsBrownianMotion μ B) :
    (fun ω ↦ ∫ t in (0 : ℝ)..1,
      brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω) =ᵐ[μ]
      fun ω ↦ ∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω := by
  -- Proof comment: off the exceptional set the two integrands agree for every time, so the whole
  -- interval integrals agree pathwise.
  classical
  filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  refine intervalIntegral.integral_congr_ae <| Filter.Eventually.of_forall fun t ht ↦ ?_
  simpa using hω (Real.toNNReal t)

/-- Helper for Exercise 21.2.1: the one-dimensional box integral over the lifted unit interval is
the usual real integral over `[0,1]`. -/
private lemma liftedUnitIntervalIntegral_eq (f : ℝ → ℝ) :
    (∫ y in Set.Icc ![(0 : ℝ)] ![1], f (y 0) ∂volume) = ∫ x in Set.Icc (0 : ℝ) 1, f x ∂volume := by
  let g : (Fin 1 → ℝ) → ℝ := fun y ↦ f (y 0)
  have hTransport : ∀ (u v : Fin 1 → ℝ) (h : (Fin 1 → ℝ) → ℝ),
      ∫ y in Set.Icc u v, h y ∂volume = ∫ x in Set.Icc (u 0) (v 0), h (fun _ ↦ x) ∂volume :=
    fun u v h ↦ by
      -- Proof comment: the unique-coordinate measurable equivalence sends the one-dimensional box
      -- interval to the corresponding real interval without changing Lebesgue measure.
      convert
        (((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _).setIntegral_preimage_emb
          (MeasurableEquiv.measurableEmbedding _) h _).symm
      exact ((OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Icc u v).symm
  simpa [g] using hTransport ![(0 : ℝ)] ![1] g

/-- Helper for Exercise 21.2.1: the lattice points of the lifted unit interval with mesh `1 / m`
are exactly the points `k / m` for `k : Fin (m + 1)`. -/
private lemma liftedUnitIntervalTsum_eq_sum (f : ℝ → ℝ) (m : ℕ) [NeZero m] :
    (∑' y : ↑(Set.Icc ![(0 : ℝ)] ![1] ∩
        ((m : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 1))))), f (y.1 0)) =
      ∑ k : Fin (m + 1), f ((k : ℝ) / (m : ℝ)) := by
  let s : Set (Fin 1 → ℝ) :=
    Set.Icc ![(0 : ℝ)] ![1] ∩
      ((m : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 1))))
  let meshPoint : Fin (m + 1) → s := fun k ↦
    ⟨fun _ ↦ (k : ℝ) / (m : ℝ), by
      constructor
      · -- Proof comment: the point `k / m` lies in `[0,1]` because `0 ≤ k ≤ m`.
        constructor <;> intro i <;> fin_cases i
        · exact div_nonneg (by positivity) (by positivity)
        · have hk_le : (k : ℝ) ≤ m := by
            exact_mod_cast Nat.le_of_lt_succ k.2
          have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero m)
          have hdiv : (k : ℝ) / (m : ℝ) ≤ 1 := by
            refine (div_le_iff₀ hm_pos).2 ?_
            simpa using hk_le
          simpa using hdiv
      · -- Proof comment: multiplying the unique coordinate by `m` recovers the integer tag `k`.
        simpa using
          (BoxIntegral.unitPartition.mem_smul_span_iff
            (n := m) (v := fun _ : Fin 1 ↦ (k : ℝ) / (m : ℝ))).2
            (by
              intro i
              fin_cases i
              refine ⟨(k : ℤ), ?_⟩
              change ((k : ℤ) : ℝ) = (m : ℝ) * ((k : ℝ) / (m : ℝ))
              field_simp [Nat.cast_ne_zero.mpr (NeZero.ne m)]
              norm_num)⟩
  have hMeshInjective : Function.Injective meshPoint := by
    intro k₁ k₂ hk
    apply Fin.ext
    have hcoord := congrArg (fun y : s ↦ y.1 0) hk
    simpa [meshPoint] using (div_left_inj' (Nat.cast_ne_zero.mpr (NeZero.ne m))).mp hcoord
  have hMeshSurjective : Function.Surjective meshPoint := by
    intro y
    have hyIcc : y.1 ∈ Set.Icc ![(0 : ℝ)] ![1] := y.2.1
    have hySpan :
        y.1 ∈ ((m : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 1)))) := y.2.2
    let a : ℤ := BoxIntegral.unitPartition.index m y.1 0 + 1
    have hcoord :
        ((a : ℝ) / (m : ℝ)) = y.1 0 := by
      have htag :=
        congrArg (fun x : Fin 1 → ℝ ↦ x 0)
          (BoxIntegral.unitPartition.tag_index_eq_self_of_mem_smul_span (n := m) hySpan)
      simpa [a, BoxIntegral.unitPartition.tag_apply] using htag
    have hy0_nonneg : 0 ≤ y.1 0 := by
      simpa [Set.mem_Icc, Pi.le_def] using hyIcc.1 0
    have hy0_le_one : y.1 0 ≤ 1 := by
      simpa [Set.mem_Icc, Pi.le_def] using hyIcc.2 0
    have hmul : (a : ℝ) = y.1 0 * (m : ℝ) := by
      exact (div_eq_iff (Nat.cast_ne_zero.mpr (NeZero.ne m))).mp (by simpa [mul_comm] using hcoord)
    have ha_nonneg : 0 ≤ a := by
      have hreal : (0 : ℝ) ≤ a := by
        nlinarith [hmul, hy0_nonneg]
      exact_mod_cast hreal
    have ha_le : a ≤ m := by
      have hreal : (a : ℝ) ≤ m := by
        nlinarith [hmul, hy0_le_one]
      exact_mod_cast hreal
    have hkInt : (Int.toNat a : ℤ) ≤ m := by
      rw [Int.toNat_of_nonneg ha_nonneg]
      exact ha_le
    have hk_le : Int.toNat a ≤ m := by
      exact_mod_cast hkInt
    have hk_lt : Int.toNat a < m + 1 := lt_of_le_of_lt hk_le (Nat.lt_succ_self m)
    have hToNatCast : ((Int.toNat a : ℕ) : ℝ) = a := by
      exact_mod_cast (Int.toNat_of_nonneg ha_nonneg)
    refine ⟨⟨Int.toNat a, hk_lt⟩, ?_⟩
    apply Subtype.ext
    ext i
    fin_cases i
    calc
      ((Int.toNat a : ℕ) : ℝ) / (m : ℝ) = (a : ℝ) / (m : ℝ) := by
        rw [hToNatCast]
      _ = y.1 0 := hcoord
  let e : Fin (m + 1) ≃ s := Equiv.ofBijective meshPoint ⟨hMeshInjective, hMeshSurjective⟩
  letI : Fintype s := Fintype.ofEquiv (Fin (m + 1)) e
  -- Proof comment: after identifying the lattice subtype with `Fin (m + 1)`, the infinite sum is
  -- just the corresponding finite sum over the mesh points `k / m`.
  calc
    ∑' y : s, f (y.1 0) = ∑ y : s, f (y.1 0) := by simp
    _ = ∑ k : Fin (m + 1), f ((e k).1 0) := by
          simpa using (e.sum_comp fun y : s ↦ f (y.1 0)).symm
    _ = ∑ k : Fin (m + 1), f ((k : ℝ) / (m : ℝ)) := by
          simp [e, meshPoint]

/-- Helper for Exercise 21.2.1: the endpoint Riemann sums of a continuous scalar function on
`[0,1]` converge to its interval integral. -/
private lemma endpointRiemannSums_tendsto_intervalIntegral
    (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto
      (fun n : ℕ ↦ (1 / (n + 1 : ℝ)) * ∑ k : Fin (n + 2), f ((k : ℝ) / (n + 1 : ℝ)))
      atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  let g : (Fin 1 → ℝ) → ℝ := fun y ↦ f (y 0)
  have hg : Continuous g := by
    -- Proof comment: lift the scalar test function to the one-dimensional box by evaluation at
    -- the unique coordinate.
    simpa [g] using hf.comp (continuous_apply 0)
  have hbox :
      Tendsto
        (fun m : ℕ ↦
          (∑' y : ↑(Set.Icc ![(0 : ℝ)] ![1] ∩
              ((m : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 1))))), g y) /
            m ^ Fintype.card (Fin 1))
        atTop
        (𝓝 (∫ y in Set.Icc ![(0 : ℝ)] ![1], g y ∂volume)) := by
    -- Proof comment: apply the one-dimensional unit-partition lattice convergence theorem on
    -- the lifted interval.
    refine tendsto_tsum_div_pow_atTop_integral
      (s := Set.Icc ![(0 : ℝ)] ![1]) (F := g) hg ?_ ?_ ?_
    · simpa using (isCompact_Icc : IsCompact (Set.Icc ![(0 : ℝ)] ![1])).isBounded
    · simp only [measurableSet_Icc]
    · simpa using
        (Set.OrdConnected.null_frontier
          (Set.ordConnected_Icc :
            Set.OrdConnected (Set.Icc ![(0 : ℝ)] ![1] : Set (Fin 1 → ℝ))))
  have hshift := hbox.comp (tendsto_add_atTop_nat 1)
  -- Proof comment: shift from `m` to `n + 1` so the denominator is never zero and the mesh
  -- matches the endpoint sums used throughout this exercise.
  convert hshift using 1
  · ext n
    simp [Function.comp, g, pow_one, div_eq_mul_inv, mul_comm, liftedUnitIntervalTsum_eq_sum]
  · exact
      (congrArg 𝓝 <| by
        calc
          ∫ y in Set.Icc ![(0 : ℝ)] ![1], g y ∂volume
              = ∫ x in Set.Icc (0 : ℝ) 1, f x ∂volume := by
                  simpa [g] using liftedUnitIntervalIntegral_eq f
          _ = ∫ x in Set.Ioc (0 : ℝ) 1, f x ∂volume := by
                rw [integral_Icc_eq_integral_Ioc]
          _ = ∫ t in (0 : ℝ)..1, f t := by
                symm
                exact intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)).symm

/-- Helper for Exercise 21.2.1: the endpoint Riemann sums of the patched Brownian path converge to
its unit-interval average. -/
lemma brownianContinuousVersion_averageRiemannSums_tendsto (hB : IsBrownianMotion μ B) (ω : Ω) :
    Tendsto
      (fun n : ℕ ↦
        (1 / (n + 1 : ℝ)) *
          ∑ k : Fin (n + 2),
            brownianContinuousVersion (μ := μ) (B := B) hB
              (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))) ω)
      atTop
      (𝓝 (∫ t in (0 : ℝ)..1,
        brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω)) := by
  let f : ℝ → ℝ := fun t ↦
    brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω
  have hf : Continuous f := by
    -- Proof comment: compose the continuous patched `NNReal`-time path with `Real.toNNReal`.
    simpa [f] using
      (brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω).comp
        continuous_real_toNNReal
  -- Proof comment: this is exactly the generic endpoint Riemann-sum lemma applied to the patched
  -- Brownian sample path.
  simpa [f] using endpointRiemannSums_tendsto_intervalIntegral f hf

/-- Helper for Exercise 21.2.1: the explicit endpoint Riemann-sum approximants for the unit-
interval Brownian average. -/
def brownianUnitIntervalAverageRiemannApprox (B : NNReal → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦
    (1 / (n + 1 : ℝ)) * ∑ k : Fin (n + 2),
      B (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))) ω

/-- Helper for Exercise 21.2.1: the Brownian endpoint Riemann sums converge almost surely to the
unit-interval average. -/
lemma brownianUnitIntervalAverageRiemannApprox_tendsto_ae (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ ↦ brownianUnitIntervalAverageRiemannApprox (B := B) n ω)
        atTop
        (𝓝 (∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω)) := by
  filter_upwards
    [brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB,
      brownianContinuousVersion_average_ae_eq (μ := μ) (B := B) hB] with ω hω hAvg
  have hpatched :=
    brownianContinuousVersion_averageRiemannSums_tendsto (μ := μ) (B := B) hB ω
  have hpatched' :
      Tendsto (fun n : ℕ ↦ brownianUnitIntervalAverageRiemannApprox (B := B) n ω) atTop
        (𝓝 (∫ t in (0 : ℝ)..1,
          brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω)) := by
    refine Tendsto.congr' ?_ hpatched
    exact Filter.Eventually.of_forall fun n ↦ by
      simp [brownianUnitIntervalAverageRiemannApprox, hω]
  simpa [hAvg] using hpatched'

/-- Helper for Exercise 21.2.1: every Brownian endpoint Riemann approximation of the unit-interval
average has a Gaussian law. -/
lemma brownianUnitIntervalAverageRiemannApprox_hasGaussianLaw
    (hB : IsBrownianMotion μ B) (n : ℕ) :
    HasGaussianLaw (brownianUnitIntervalAverageRiemannApprox (B := B) n) μ := by
  let hGaussian : IsGaussianProcess B μ := IsBrownianMotion.isGaussianProcess hB
  let mesh : Fin (n + 2) → NNReal := fun k ↦
    Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))
  let coeff : Fin (n + 2) → ℝ := fun _ ↦ 1 / (n + 1 : ℝ)
  have hMesh : IsGaussianProcess (fun k ω ↦ B (mesh k) ω) μ := hGaussian.comp_right mesh
  have hScaled :
      IsGaussianProcess (fun k ω ↦ coeff k * B (mesh k) ω) μ :=
    ProbabilityTheory.IsGaussianProcess.smul coeff hMesh
  have hEq :
      (fun ω ↦ ∑ k : Fin (n + 2), coeff k * B (mesh k) ω) =
        brownianUnitIntervalAverageRiemannApprox (B := B) n := by
    funext ω
    simp [brownianUnitIntervalAverageRiemannApprox, coeff, mesh, Finset.mul_sum]
  -- Proof comment: the approximant is a finite sum of jointly Gaussian Brownian evaluations.
  simpa [hEq] using
    hScaled.hasGaussianLaw_fun_sum (I := Finset.univ)

/-- Helper for Exercise 21.2.1: every Brownian endpoint Riemann approximation of the unit-
interval average is centered. -/
lemma brownianUnitIntervalAverageRiemannApprox_expectation_eq_zero
    (hB : IsBrownianMotion μ B) (n : ℕ) :
    ∫ ω, brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hone_le_two : (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
  -- Proof comment: the endpoint average is a finite linear combination of centered Brownian
  -- marginals.
  simp only [brownianUnitIntervalAverageRiemannApprox]
  rw [integral_const_mul]
  rw [integral_finset_sum]
  · simp [brownianEval_expectation_eq_zero]
  · intro k hk
    exact (brownianEval_memLp_two (μ := μ) (X := B) hB
      (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ)))).integrable hone_le_two

/-- Helper for Exercise 21.2.1: the affine Brownian-average endpoint approximants used for the
Gaussian limit step. -/
def brownianCenteredAffineRiemannApprox
    (B : NNReal → Ω → ℝ) (s t a b c : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦
    a * B (Real.toNNReal s) ω + b * B (Real.toNNReal t) ω -
      c * brownianUnitIntervalAverageRiemannApprox (B := B) n ω

/-- Helper for Exercise 21.2.1: every affine endpoint approximation
`a * B_s + b * B_t - c * Aₙ` is Gaussian. -/
lemma brownianCenteredAffineRiemannApprox_hasGaussianLaw
    (hB : IsBrownianMotion μ B) (s t a b c : ℝ) (n : ℕ) :
    HasGaussianLaw (brownianCenteredAffineRiemannApprox (B := B) s t a b c n) μ := by
  let hGaussian : IsGaussianProcess B μ := IsBrownianMotion.isGaussianProcess hB
  let coord : Fin (n + 4) → NNReal :=
    Fin.cases (Real.toNNReal s)
      (Fin.cases (Real.toNNReal t)
        (fun k ↦ Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))))
  let weight : Fin (n + 4) → ℝ :=
    Fin.cases a (Fin.cases b (fun _ ↦ -(c / (n + 1 : ℝ))))
  have hCoord : IsGaussianProcess (fun i ω ↦ B (coord i) ω) μ := hGaussian.comp_right coord
  have hWeighted : IsGaussianProcess (fun i ω ↦ weight i * B (coord i) ω) μ :=
    ProbabilityTheory.IsGaussianProcess.smul weight hCoord
  have hSum :
      HasGaussianLaw (fun ω ↦ ∑ i : Fin (n + 4), weight i * B (coord i) ω) μ := by
    simpa using (hWeighted.hasGaussianLaw_fun_sum (I := Finset.univ))
  refine hSum.congr ?_
  -- Proof comment: unfold the first two distinguished coordinates and the remaining uniform mesh.
  filter_upwards with ω
  simp [brownianCenteredAffineRiemannApprox, brownianUnitIntervalAverageRiemannApprox,
    coord, weight, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_add, add_mul, mul_comm]
  rw [← Finset.mul_sum]
  ring

/-- Helper for Exercise 21.2.1: the affine Gaussian endpoint approximants converge almost surely
to the exact affine Brownian-average functional. -/
lemma brownianCenteredAffineRiemannApprox_tendsto_ae
    (hB : IsBrownianMotion μ B) (s t a b c : ℝ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ ↦ brownianCenteredAffineRiemannApprox (B := B) s t a b c n ω)
        atTop
        (𝓝 (a * B (Real.toNNReal s) ω + b * B (Real.toNNReal t) ω -
          c * (∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω))) := by
  filter_upwards
    [brownianUnitIntervalAverageRiemannApprox_tendsto_ae (μ := μ) (B := B) hB] with ω hω
  -- Proof comment: only the Brownian average depends on `n`, so continuity of affine maps
  -- transfers the endpoint-sum convergence to the full affine functional.
  simpa [brownianCenteredAffineRiemannApprox, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_comm, mul_left_comm, mul_assoc] using
    (hω.const_mul (-c)).const_add (a * B (Real.toNNReal s) ω + b * B (Real.toNNReal t) ω)

/-- Helper for Exercise 21.2.1: the affine Brownian-average endpoint approximants are centered. -/
lemma brownianCenteredAffineRiemannApprox_expectation_eq_zero
    (hB : IsBrownianMotion μ B) (s t a b c : ℝ) (n : ℕ) :
    ∫ ω, brownianCenteredAffineRiemannApprox (B := B) s t a b c n ω ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hone_le_two : (1 : ENNReal) ≤ (2 : ENNReal) := by
    norm_num
  have hs_int : Integrable (fun ω ↦ a * B (Real.toNNReal s) ω) μ :=
    ((brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal s)).integrable hone_le_two)
      |>.const_mul a
  have ht_int : Integrable (fun ω ↦ b * B (Real.toNNReal t) ω) μ :=
    ((brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal t)).integrable hone_le_two)
      |>.const_mul b
  have hA_mem :
      MemLp (brownianUnitIntervalAverageRiemannApprox (B := B) n) 2 μ :=
    (brownianUnitIntervalAverageRiemannApprox_hasGaussianLaw (μ := μ) (B := B) hB n).memLp_two
  have hA_int : Integrable (fun ω ↦ c * brownianUnitIntervalAverageRiemannApprox (B := B) n ω) μ :=
    (hA_mem.integrable hone_le_two) |>.const_mul c
  have hnegA_int :
      Integrable (fun ω ↦ -(c * brownianUnitIntervalAverageRiemannApprox (B := B) n ω)) μ :=
    hA_int.neg
  have hdecomp :
      (fun ω ↦
        a * B (Real.toNNReal s) ω + b * B (Real.toNNReal t) ω -
          c * brownianUnitIntervalAverageRiemannApprox (B := B) n ω) =
        (fun ω ↦ a * B (Real.toNNReal s) ω + b * B (Real.toNNReal t) ω) +
          fun ω ↦ -(c * brownianUnitIntervalAverageRiemannApprox (B := B) n ω) := by
    funext ω
    simp [Pi.add_apply]
    ring
  -- Proof comment: each affine summand is integrable, so the expectation is computed by linearity
  -- and the previously proved centered endpoint and average expectations.
  simp_rw [brownianCenteredAffineRiemannApprox]
  rw [hdecomp]
  have hSplit :
      ∫ ω,
        (((fun ω ↦ a * B (Real.toNNReal s) ω + b * B (Real.toNNReal t) ω) +
          fun ω ↦ -(c * brownianUnitIntervalAverageRiemannApprox (B := B) n ω)) ω) ∂μ =
        ∫ ω, (a * B (Real.toNNReal s) ω + b * B (Real.toNNReal t) ω) ∂μ +
          ∫ ω, -(c * brownianUnitIntervalAverageRiemannApprox (B := B) n ω) ∂μ := by
    simpa using integral_add (hs_int.add ht_int) hnegA_int
  rw [hSplit, integral_add hs_int ht_int]
  rw [integral_neg, integral_const_mul,
    brownianEval_expectation_eq_zero (μ := μ) (B := B) hB (Real.toNNReal s)]
  rw [integral_const_mul,
    brownianEval_expectation_eq_zero (μ := μ) (B := B) hB (Real.toNNReal t)]
  rw [integral_const_mul,
    brownianUnitIntervalAverageRiemannApprox_expectation_eq_zero (μ := μ) (B := B) hB n]
  ring

/-- Helper for Exercise 21.2.1: off the exceptional set, the Brownian zero set on `[0, ∞)` agrees
with the zero set of the patched continuous version. -/
lemma brownianContinuousVersion_zeroSet_ae_eq (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ,
      {t : ℝ | brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω = 0} =
        {t : ℝ | B (Real.toNNReal t) ω = 0} := by
  -- Proof comment: the patch only changes values on the exceptional set of sample points, not on
  -- any time slice of a good path.
  classical
  filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  ext t
  simp [hω (Real.toNNReal t)]

/-- Helper for Exercise 21.2.1: the patched Brownian motion is jointly measurable after composing
with `Real.toNNReal` on the time coordinate. -/
lemma brownianContinuousVersion_real_uncurry_measurable (hB : IsBrownianMotion μ B) :
    Measurable (fun z : ℝ × Ω ↦
      brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2) := by
  -- Proof comment: first use right-continuous joint measurability on `NNReal` time.
  have h_uncurry :
      Measurable (Function.uncurry (brownianContinuousVersion (μ := μ) (B := B) hB)) := by
    refine MeasureTheory.measurable_uncurry_of_measurable_rightContinuous
      (brownianContinuousVersion_measurable (μ := μ) (B := B) hB) ?_
    intro ω t
    exact (brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω).continuousWithinAt
  -- Proof comment: precompose the jointly measurable `NNReal × Ω` map with
  -- `(t, ω) ↦ (Real.toNNReal t, ω)` to move back to real time.
  simpa [Function.uncurry] using h_uncurry.comp
    ((measurable_fst.real_toNNReal).prodMk measurable_snd)

/-- Helper for Exercise 21.2.1: if a jointly measurable field is almost surely nonzero at almost
every time, then almost every sample path has zero set of outer measure zero. -/
private lemma zeroSetSectionMeasure_eq_zero_ae_of_ae
    {ν : Measure ℝ} [SFinite μ] [SFinite ν] {f : ℝ × Ω → ℝ} (hf : Measurable f)
    (hzero : ∀ᵐ t ∂ν, ∀ᵐ ω ∂μ, f (t, ω) ≠ 0) :
    ∀ᵐ ω ∂μ, ν {t : ℝ | f (t, ω) = 0} = 0 := by
  have hzeroSetMeas :
      MeasurableSet {z : ℝ × Ω | f z = 0} := by
    simpa using hf.stronglyMeasurable.measurableSet_eq_fun stronglyMeasurable_const
  have hnonzeroSetMeas :
      MeasurableSet {z : ℝ × Ω | f (z.1, z.2) ≠ 0} := by
    change MeasurableSet ({z : ℝ × Ω | f z = 0}ᶜ)
    exact hzeroSetMeas.compl
  have hnonzero' :
      ∀ᵐ ω ∂μ, ∀ᵐ t ∂ν, f (t, ω) ≠ 0 := by
    -- Proof comment: swap the Tonelli order on the measurable nonzero event once and reuse it.
    exact
      (Measure.ae_ae_comm (μ := ν) (ν := μ) (p := fun t ω ↦ f (t, ω) ≠ 0)
        hnonzeroSetMeas).1 hzero
  filter_upwards [hnonzero'] with ω hω
  -- Proof comment: for a fixed sample path, almost-everywhere nonvanishing is equivalent to the
  -- pathwise zero set having zero `ν`-measure.
  rw [ae_iff] at hω
  simpa using hω

/-- Helper for Exercise 21.2.1: on every finite interval `(0, T]`, the zero set of the patched
Brownian motion has Lebesgue measure zero almost surely. -/
lemma brownianContinuousVersion_zeroSet_measureOnIoc_eq_zero_ae
    (hB : IsBrownianMotion μ B) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂μ,
      (volume.restrict (Set.Ioc (0 : ℝ) T))
        {t : ℝ | brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω = 0} = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  let f : ℝ × Ω → ℝ := fun z ↦
    brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2
  have hzero :
      ∀ᵐ t ∂ν, ∀ᵐ ω ∂μ, f (t, ω) ≠ 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with t ht
    have ht_pos : 0 < t := ht.1
    have horiginal :
        ∀ᵐ ω ∂μ, B (Real.toNNReal t) ω ≠ 0 := by
      rw [ae_iff]
      simpa using brownianFixedTime_zero_prob_eq_zero (μ := μ) (B := B) hB ht_pos
    -- Proof comment: fixed-time null events are unchanged by the continuous-version modification.
    filter_upwards
      [horiginal,
        brownianContinuousVersion_areModifications (μ := μ) (B := B) hB (Real.toNNReal t)] with
      ω hω hpatch
    simpa [f, hpatch] using hω
  -- Proof comment: apply the general section-measure lemma to the jointly measurable patched
  -- field on `(0,T] × Ω`.
  simpa [ν, f] using
    zeroSetSectionMeasure_eq_zero_ae_of_ae (μ := μ)
      (ν := ν)
      (f := f)
      (brownianContinuousVersion_real_uncurry_measurable (μ := μ) (B := B) hB)
      hzero

/-- Helper for Exercise 21.2.1: every fixed-time marginal of the patched process still has mean
`0`. -/
lemma brownianContinuousVersion_eval_expectation_eq_zero (hB : IsBrownianMotion μ B) (t : NNReal) :
    ∫ ω, brownianContinuousVersion (μ := μ) (B := B) hB t ω ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: the patch changes only a null set of sample points, so fixed-time
  -- expectations are unchanged.
  calc
    ∫ ω, brownianContinuousVersion (μ := μ) (B := B) hB t ω ∂μ
        = ∫ ω, B t ω ∂μ := by
            exact integral_congr_ae
              (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t).symm
    _ = 0 := brownianEval_expectation_eq_zero (μ := μ) (B := B) hB t

/-- Helper for Exercise 21.2.1: every fixed-time marginal of the patched process has second
moment equal to the time parameter. -/
lemma brownianContinuousVersion_eval_secondMoment_eq (hB : IsBrownianMotion μ B) (t : NNReal) :
    ∫ ω, (brownianContinuousVersion (μ := μ) (B := B) hB t ω) ^ 2 ∂μ = t := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: first transport the second moment through the modification.
  have h_secondMoment_original : ∫ ω, B t ω ^ 2 ∂μ = t := by
    -- Proof comment: variance equals second moment for centered Brownian marginals.
    have hVarSub :
        Var[B t; μ] = ∫ ω, B t ω ^ 2 ∂μ - (∫ ω, B t ω ∂μ) ^ 2 := by
      simpa using
        (ProbabilityTheory.variance_eq_sub
          (brownianEval_memLp_two (μ := μ) (X := B) hB t))
    rw [brownianEval_variance_eq (μ := μ) (B := B) hB t] at hVarSub
    rw [brownianEval_expectation_eq_zero (μ := μ) (B := B) hB t] at hVarSub
    simpa using hVarSub.symm
  calc
    ∫ ω, (brownianContinuousVersion (μ := μ) (B := B) hB t ω) ^ 2 ∂μ
        = ∫ ω, B t ω ^ 2 ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards
              [brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t] with ω hω
            simp [hω]
    _ = t := h_secondMoment_original

/-- Helper for Exercise 21.2.1: every fixed-time marginal of the patched Brownian motion still
belongs to `L²`. -/
lemma brownianContinuousVersion_eval_memLp_two (hB : IsBrownianMotion μ B) (t : NNReal) :
    MemLp (brownianContinuousVersion (μ := μ) (B := B) hB t) 2 μ := by
  -- Proof comment: the patch is an almost-everywhere modification of the original Brownian
  -- marginal, so the `L²` norm is unchanged.
  refine (brownianEval_memLp_two (μ := μ) (X := B) hB t).congr_norm
    ((brownianContinuousVersion_measurable (μ := μ) (B := B) hB t).aestronglyMeasurable) ?_
  filter_upwards
    [brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t] with ω hω
  simp [hω]

/-- Helper for Exercise 21.2.1: the patched Brownian motion has strip square mass `1 / 2` on
`(0,1] × Ω`. -/
lemma brownianContinuousVersion_unitStrip_lintegral_sq_eq_half (hB : IsBrownianMotion μ B) :
    ∫⁻ z : ℝ × Ω,
      ENNReal.ofReal
        ((brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2) ^ 2)
        ∂(((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ)) =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let X : ℝ × Ω → ℝ := fun z ↦
    brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2
  have hX_meas : Measurable X :=
    brownianContinuousVersion_real_uncurry_measurable (μ := μ) (B := B) hB
  have hsq_meas : Measurable (fun z : ℝ × Ω ↦ X z ^ 2) := by
    simpa [pow_two] using hX_meas.mul hX_meas
  rw [lintegral_prod _ hsq_meas.ennreal_ofReal.aemeasurable]
  have hslice :
      (fun t : ℝ ↦ ∫⁻ ω, ENNReal.ofReal (X (t, ω) ^ 2) ∂μ)
        =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun t ↦ ENNReal.ofReal t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht_nonneg : 0 ≤ t := le_of_lt ht.1
    have hsq_int :
        Integrable
          (fun ω ↦
            (brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω) ^ 2) μ :=
      (brownianContinuousVersion_eval_memLp_two (μ := μ) (B := B) hB (Real.toNNReal t)).integrable_sq
    have hsq_nonneg :
        0 ≤ᵐ[μ] fun ω ↦
          (brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω) ^ 2 :=
      Filter.Eventually.of_forall fun _ ↦ sq_nonneg _
    -- Proof comment: each time slice is the known second moment `E[X_t²] = t`, now rewritten in
    -- `lintegral` form because the square is nonnegative.
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hsq_int hsq_nonneg]
    rw [brownianContinuousVersion_eval_secondMoment_eq (μ := μ) (B := B) hB (Real.toNNReal t),
      Real.toNNReal_of_nonneg ht_nonneg]
    simp
  rw [lintegral_congr_ae hslice]
  have hOuterInt :
      Integrable (fun t : ℝ ↦ t) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    -- Proof comment: the identity function is continuous, hence interval-integrable on `[0,1]`.
    simpa [IntegrableOn] using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)).1
        (continuous_id.intervalIntegrable 0 1)
  have hOuterNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun t : ℝ ↦ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact le_of_lt ht.1
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hOuterInt hOuterNonneg]
  have hOuterEval :
      ∫ t, t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = (1 / 2 : ℝ) := by
    -- Proof comment: this is the deterministic integral `∫₀¹ t dt = 1/2`.
    simpa [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      (by norm_num [integral_pow] : ∫ t in (0 : ℝ)..1, (t : ℝ) = (1 / 2 : ℝ))
  rw [hOuterEval]

/-- Helper for Exercise 21.2.1: the patched Brownian motion belongs to `L²` on the unit strip
`(0,1] × Ω`. -/
lemma brownianContinuousVersion_unitStrip_memLp_two (hB : IsBrownianMotion μ B) :
    MemLp
      (fun z : ℝ × Ω ↦
        brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2)
      2 (((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ)) := by
  let ν : Measure (ℝ × Ω) := ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ)
  have hsq_meas :
      AEStronglyMeasurable
        (fun z : ℝ × Ω ↦
          (brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2) ^ 2) ν := by
    have hmeas :
        Measurable
          (fun z : ℝ × Ω ↦
            (brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2) ^ 2) := by
      simpa [pow_two] using
        (brownianContinuousVersion_real_uncurry_measurable (μ := μ) (B := B) hB).mul
          (brownianContinuousVersion_real_uncurry_measurable (μ := μ) (B := B) hB)
    exact hmeas.aestronglyMeasurable
  have hsq_nonneg :
      0 ≤ᵐ[ν] fun z : ℝ × Ω ↦
        (brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2) ^ 2 :=
    Filter.Eventually.of_forall fun _ ↦ sq_nonneg _
  have hsq_finite :
      HasFiniteIntegral
        (fun z : ℝ × Ω ↦
          (brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2) ^ 2) ν := by
    -- Proof comment: the strip square mass was computed explicitly as `1 / 2`.
    rw [hasFiniteIntegral_iff_ofReal hsq_nonneg]
    rw [brownianContinuousVersion_unitStrip_lintegral_sq_eq_half (μ := μ) (B := B) hB]
    simp
  exact
    (memLp_two_iff_integrable_sq
      (brownianContinuousVersion_real_uncurry_measurable (μ := μ) (B := B) hB).aestronglyMeasurable).2
      ⟨hsq_meas, hsq_finite⟩

/-- Helper for Exercise 21.2.1: the mixed second moment of one Brownian marginal against the
unit-interval average is `t - t^2 / 2`. -/
lemma brownianEval_mulUnitIntervalAverage_eq (hB : IsBrownianMotion μ B) {t : ℝ}
    (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) :
    ∫ ω, B (Real.toNNReal t) ω * (∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ∂μ =
      t - t ^ 2 / 2 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Bt : Ω → ℝ := B (Real.toNNReal t)
  let X : ℝ → Ω → ℝ := fun s ω ↦
    Bt ω * brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s) ω
  have hBt_prod :
      MemLp (fun z : ℝ × Ω ↦ Bt z.2) 2 (((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ)) := by
    -- Proof comment: the fixed Brownian marginal becomes a strip function by ignoring the time
    -- coordinate.
    simpa [Bt] using
      (brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal t)).comp_snd
        (volume.restrict (Set.Ioc (0 : ℝ) 1))
  have hProdInt :
      Integrable (Function.uncurry X) (((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod μ)) := by
    -- Proof comment: Hölder on the unit strip gives the product integrability needed for Fubini.
    simpa [Bt, X, Function.uncurry, Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      hBt_prod.integrable_mul (brownianContinuousVersion_unitStrip_memLp_two (μ := μ) (B := B) hB)
  have hswap :=
    MeasureTheory.intervalIntegral_integral_swap
      (μ := μ) (f := X) hProdInt
  have hKernel :
      ∫ s in (0 : ℝ)..1,
        ((((Real.toNNReal t) ⊓ (Real.toNNReal s) : NNReal) : ℝ)) =
          t - t ^ 2 / 2 := by
    have hmin_cont : Continuous fun s : ℝ => min t s := continuous_const.min continuous_id
    have hToMin :
        ∫ s in (0 : ℝ)..1, ((((Real.toNNReal t) ⊓ (Real.toNNReal s) : NNReal) : ℝ)) =
          ∫ s in (0 : ℝ)..1, min t s := by
      -- Proof comment: on `[0,1]`, the `NNReal` kernel is literally the real-valued minimum.
      refine intervalIntegral.integral_congr_ae (μ := volume) (a := (0 : ℝ)) (b := 1) ?_
      filter_upwards with s hs
      have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hs
      have hs_nonneg : 0 ≤ s := le_of_lt hs'.1
      simp [Real.toNNReal_of_nonneg ht_nonneg, Real.toNNReal_of_nonneg hs_nonneg]
    have hsplit :
        (∫ s in (0 : ℝ)..t, min t s) + ∫ s in t..1, min t s =
          ∫ s in (0 : ℝ)..1, min t s := by
      -- Proof comment: split the deterministic minimum kernel at the threshold `s = t`.
      simpa using
        (intervalIntegral.integral_add_adjacent_intervals
          (hmin_cont.intervalIntegrable 0 t)
          (hmin_cont.intervalIntegrable t 1))
    have hleft :
        ∫ s in (0 : ℝ)..t, min t s = ∫ s in (0 : ℝ)..t, (s : ℝ) := by
      -- Proof comment: on `(0,t]`, the minimum is the time variable itself.
      refine intervalIntegral.integral_congr_ae (μ := volume) (a := (0 : ℝ)) (b := t) ?_
      filter_upwards with s hs
      have hs' : s ∈ Set.Ioc (0 : ℝ) t := by
        simpa [Set.uIoc_of_le ht_nonneg] using hs
      exact min_eq_right hs'.2
    have hright :
        ∫ s in t..1, min t s = ∫ s in t..1, (t : ℝ) := by
      -- Proof comment: on `(t,1]`, the minimum is the constant value `t`.
      refine intervalIntegral.integral_congr_ae (μ := volume) (a := t) (b := 1) ?_
      filter_upwards with s hs
      have hs' : s ∈ Set.Ioc t 1 := by
        simpa [Set.uIoc_of_le ht_le_one] using hs
      exact min_eq_left (le_of_lt hs'.1)
    have hleft_eval : ∫ s in (0 : ℝ)..t, (s : ℝ) = t ^ 2 / 2 := by
      norm_num [integral_pow]
    have hright_eval : ∫ s in t..1, (t : ℝ) = t * (1 - t) := by
      rw [intervalIntegral.integral_const]
      change (1 - t) * t = t * (1 - t)
      ring
    rw [hToMin, ← hsplit, hleft, hright, hleft_eval, hright_eval]
    ring
  calc
    ∫ ω, B (Real.toNNReal t) ω * (∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ∂μ
        = ∫ ω, B (Real.toNNReal t) ω *
            (∫ s in (0 : ℝ)..1,
              brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s) ω) ∂μ := by
              -- Proof comment: first replace the average by the patched continuous version.
              refine integral_congr_ae ?_
              filter_upwards [brownianContinuousVersion_average_ae_eq (μ := μ) (B := B) hB] with
                ω hω
              simp [hω]
    _ = ∫ ω, (∫ s in (0 : ℝ)..1, X s ω) ∂μ := by
          -- Proof comment: move the fixed Brownian marginal inside the interval integral.
          refine integral_congr_ae ?_
          filter_upwards with ω
          simpa [Bt, X] using
            (intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 1)
              (r := B (Real.toNNReal t) ω)
              (f := fun s ↦
                brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s) ω)).symm
    _ = ∫ s in (0 : ℝ)..1, ∫ ω, X s ω ∂μ := by
          simpa using hswap.symm
    _ = ∫ s in (0 : ℝ)..1, ((((Real.toNNReal t) ⊓ (Real.toNNReal s) : NNReal) : ℝ)) := by
          -- Proof comment: the inner expectation is the Brownian covariance kernel.
          refine intervalIntegral.integral_congr_ae (μ := volume) (a := (0 : ℝ)) (b := 1) ?_
          filter_upwards with s hs
          have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := by
            simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hs
          have hs_nonneg : 0 ≤ s := le_of_lt hs'.1
          have hBt_mem : MemLp (B (Real.toNNReal t)) 2 μ :=
            brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal t)
          have hs_mem :
              MemLp (brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s)) 2 μ :=
            brownianContinuousVersion_eval_memLp_two (μ := μ) (B := B) hB (Real.toNNReal s)
          have hCov :
              cov[B (Real.toNNReal t),
                brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s); μ] =
                ∫ ω, B (Real.toNNReal t) ω *
                  brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s) ω ∂μ := by
            rw [covariance_eq_sub hBt_mem hs_mem,
              brownianEval_expectation_eq_zero (μ := μ) (B := B) hB (Real.toNNReal t),
              brownianContinuousVersion_eval_expectation_eq_zero (μ := μ) (B := B) hB
                (Real.toNNReal s),
              zero_mul, sub_zero]
            simp [Pi.mul_apply]
          calc
            ∫ ω, X s ω ∂μ
                = cov[B (Real.toNNReal t),
                    brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s); μ] := by
                      simpa [X, Bt] using hCov.symm
            _ = cov[B (Real.toNNReal t), B (Real.toNNReal s); μ] := by
                  rw [covariance_congr_ae (μ := μ) (Filter.EventuallyEq.rfl)
                    (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB
                      (Real.toNNReal s)).symm]
            _ = ((((Real.toNNReal t) ⊓ (Real.toNNReal s) : NNReal) : ℝ)) := by
                  simpa using brownianCovariance_eq_min (μ := μ) (B := B) hB
                    (Real.toNNReal t) (Real.toNNReal s)
    _ = t - t ^ 2 / 2 := hKernel

/-- Helper for Exercise 21.2.1: integrating an `L²` field over a finite real-measure fiber keeps
the remaining variable in `L²` on an `s`-finite sample space. -/
lemma memLpTwo_integral_restrict_of_memLpTwo_prod {ν : Measure ℝ} [IsFiniteMeasure ν]
    [SFinite μ]
    {X : ℝ × Ω → ℝ} (hX : MemLp X 2 (ν.prod μ)) :
    MemLp (fun ω ↦ ∫ t, X (t, ω) ∂ν) 2 μ := by
  let Xswap : Ω × ℝ → ℝ := fun z ↦ X (z.2, z.1)
  let Q : Ω → ℝ := fun ω ↦ ∫ t, Xswap (ω, t) ∂ν
  have hX_sq_int : Integrable (fun z : ℝ × Ω ↦ X z ^ (2 : ℕ)) (ν.prod μ) := hX.integrable_sq
  have hXswap_meas : AEStronglyMeasurable Xswap (μ.prod ν) := by
    -- Proof comment: swap the product coordinates once so every section theorem runs over
    -- `(ω, t)` instead of repeated ad hoc transports.
    simpa [Xswap, Function.comp] using hX.aestronglyMeasurable.prod_swap
  have hXswap_sq_int : Integrable (fun z : Ω × ℝ ↦ Xswap z ^ (2 : ℕ)) (μ.prod ν) := by
    -- Proof comment: the same coordinate swap preserves integrability of the square field.
    simpa [Xswap] using hX_sq_int.swap
  have hQ_meas : AEStronglyMeasurable Q μ := by
    -- Proof comment: Bochner integration in the time variable preserves a.e.-measurability of the
    -- resulting sample-point map.
    simpa [Q, Xswap] using hXswap_meas.integral_prod_right'
  have hSectionMeas :
      ∀ᵐ ω ∂μ, AEStronglyMeasurable (fun t : ℝ ↦ Xswap (ω, t)) ν := by
    -- Proof comment: almost every time section inherits strong measurability from the product
    -- field after the one-time coordinate swap.
    simpa [Xswap] using hXswap_meas.prodMk_left
  have hSectionSqInt :
      ∀ᵐ ω ∂μ, Integrable (fun t : ℝ ↦ Xswap (ω, t) ^ (2 : ℕ)) ν := by
    have hSectionSqHfi :
        ∀ᵐ ω ∂μ, HasFiniteIntegral (fun t : ℝ ↦ Xswap (ω, t) ^ (2 : ℕ)) ν := by
      -- Proof comment: finite square mass on the product gives finite square mass on almost every
      -- time section.
      exact
        ((hasFiniteIntegral_prod_iff'
          (f := fun z : Ω × ℝ ↦ Xswap z ^ (2 : ℕ))
          (hXswap_sq_int.aestronglyMeasurable)).mp hXswap_sq_int.hasFiniteIntegral).1
    filter_upwards [hSectionMeas, hSectionSqHfi] with ω hω_meas hω_hfi
    exact ⟨hω_meas.pow 2, hω_hfi⟩
  have hSqBound :
      ∀ᵐ ω ∂μ, Q ω ^ (2 : ℕ) ≤ ν.real Set.univ * (∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν) := by
    filter_upwards [hSectionMeas, hSectionSqInt] with ω hω_meas hω_sq
    have hω_mem : MemLp (fun t : ℝ ↦ Xswap (ω, t)) 2 ν :=
      (memLp_two_iff_integrable_sq hω_meas).2 hω_sq
    have hω_abs_mem : MemLp (fun t : ℝ ↦ |Xswap (ω, t)|) (ENNReal.ofReal (2 : ℝ)) ν := by
      simpa [Real.norm_eq_abs] using hω_mem.norm
    have hOne_mem : MemLp (fun _ : ℝ ↦ (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) ν := by
      simpa using (memLp_const (μ := ν) (p := ENNReal.ofReal (2 : ℝ)) (1 : ℝ))
    have hNorm :
        |Q ω| ≤ ∫ t, |Xswap (ω, t)| ∂ν := by
      -- Proof comment: dominate the absolute value of the time integral by the integral of the
      -- pointwise absolute value.
      simpa [Q, Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm (f := fun t : ℝ ↦ Xswap (ω, t)))
    have hHolder :
        ∫ t, |Xswap (ω, t)| * (1 : ℝ) ∂ν ≤
          (∫ t, |Xswap (ω, t)| ^ (2 : ℝ) ∂ν) ^ ((2 : ℝ)⁻¹) *
            (∫ t, (1 : ℝ) ^ (2 : ℝ) ∂ν) ^ ((2 : ℝ)⁻¹) := by
      -- Proof comment: Cauchy-Schwarz upgrades each section from `L¹` to `L²`, with the finite
      -- mass of `ν` supplying the extra factor.
      simpa using
        (MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν) (p := (2 : ℝ))
          (q := (2 : ℝ)) Real.HolderConjugate.two_two
          (f := fun t : ℝ ↦ |Xswap (ω, t)|) (g := fun _ : ℝ ↦ (1 : ℝ))
          (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
          (Filter.Eventually.of_forall fun _ ↦ by positivity)
          hω_abs_mem hOne_mem)
    have hAbsSq :
        ∫ t, |Xswap (ω, t)| ^ (2 : ℝ) ∂ν = ∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν := by
      refine integral_congr_ae ?_
      filter_upwards with t
      calc
        |Xswap (ω, t)| ^ (2 : ℝ) = |Xswap (ω, t)| ^ (2 : ℕ) := by
          norm_num
        _ = Xswap (ω, t) ^ (2 : ℕ) := by
          simpa using abs_sq (Xswap (ω, t))
    have hMass : ∫ t, (1 : ℝ) ^ (2 : ℝ) ∂ν = ν.real Set.univ := by
      rw [show (fun t : ℝ ↦ (1 : ℝ) ^ (2 : ℝ)) = fun _ : ℝ ↦ (1 : ℝ) by
        funext t
        norm_num]
      simp [Measure.real]
    have hSqNonneg : 0 ≤ ∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν := by
      exact integral_nonneg fun _ ↦ sq_nonneg _
    have hMassNonneg : 0 ≤ ν.real Set.univ := by
      simp [Measure.real]
    have hL2Bound :
        |Q ω| ≤
          (∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν) ^ ((2 : ℝ)⁻¹) *
            (ν.real Set.univ) ^ ((2 : ℝ)⁻¹) := by
      calc
        |Q ω| ≤ ∫ t, |Xswap (ω, t)| ∂ν := hNorm
        _ = ∫ t, |Xswap (ω, t)| * (1 : ℝ) ∂ν := by simp
        _ ≤
            (∫ t, |Xswap (ω, t)| ^ (2 : ℝ) ∂ν) ^ ((2 : ℝ)⁻¹) *
              (∫ t, (1 : ℝ) ^ (2 : ℝ) ∂ν) ^ ((2 : ℝ)⁻¹) := hHolder
        _ =
            (∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν) ^ ((2 : ℝ)⁻¹) *
              (ν.real Set.univ) ^ ((2 : ℝ)⁻¹) := by
                rw [hAbsSq, hMass]
    have hsq :
        |Q ω| ^ (2 : ℕ) ≤
          (((∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν) ^ ((2 : ℝ)⁻¹) *
              (ν.real Set.univ) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ)) := by
      exact sq_le_sq.mpr <| by
        simpa [abs_of_nonneg (abs_nonneg _),
          abs_of_nonneg
            (mul_nonneg (Real.rpow_nonneg hSqNonneg _) (Real.rpow_nonneg hMassNonneg _))] using
          hL2Bound
    have hpow :
        (((∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν) ^ ((2 : ℝ)⁻¹) *
            (ν.real Set.univ) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ)) =
          ν.real Set.univ * (∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν) := by
      have hPowSq :
          (((∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ)) =
            ∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hSqNonneg]
        norm_num
      have hPowMass :
          (((ν.real Set.univ) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ)) = ν.real Set.univ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hMassNonneg]
        norm_num
      rw [mul_pow, hPowSq, hPowMass]
      ring
    simpa [sq_abs, mul_comm, mul_left_comm, mul_assoc] using hsq.trans_eq hpow
  have hMajorant :
      Integrable (fun ω ↦ ν.real Set.univ * (∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν)) μ := by
    -- Proof comment: the section-square majorant is integrable because it is exactly the Fubini
    -- integral of the product square field, up to the finite mass factor of `ν`.
    simpa [Xswap] using (hXswap_sq_int.integral_prod_left.const_mul (ν.real Set.univ))
  have hQSqInt : Integrable (fun ω ↦ Q ω ^ (2 : ℕ)) μ := by
    -- Proof comment: combine the pointwise Cauchy-Schwarz majorant with the integrable Fubini
    -- majorant to place the fiber integral in `L²`.
    refine Integrable.mono' hMajorant (hQ_meas.pow 2) ?_
    filter_upwards [hSqBound] with ω hω
    have hQSqNonneg : 0 ≤ Q ω ^ (2 : ℕ) := by positivity
    have hMajorantNonneg : 0 ≤ ν.real Set.univ * (∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν) := by
      exact mul_nonneg (by simp [Measure.real]) (integral_nonneg fun _ ↦ sq_nonneg _)
    exact
      (by
        simpa [Q, Xswap, Real.norm_eq_abs, abs_of_nonneg hQSqNonneg,
          abs_of_nonneg hMajorantNonneg] using hω : ‖Q ω ^ (2 : ℕ)‖ ≤
            ν.real Set.univ * (∫ t, Xswap (ω, t) ^ (2 : ℕ) ∂ν))
  simpa [Q, Xswap] using (memLp_two_iff_integrable_sq hQ_meas).2 hQSqInt

/-- Helper for Exercise 21.2.1: the unit-interval average of the patched Brownian motion belongs
to `L²`. -/
lemma brownianContinuousVersion_unitIntervalAverage_memLp_two (hB : IsBrownianMotion μ B) :
    MemLp
      (fun ω ↦ ∫ t,
        brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      2 μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let X : ℝ × Ω → ℝ := fun z ↦
    brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2
  letI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    simp [ν]
  -- Route correction: replace the earlier theorem-local Hölder/Fubini churn with the reusable
  -- strip-to-average `L²` bridge proved just above.
  simpa [ν, X] using
    memLpTwo_integral_restrict_of_memLpTwo_prod (μ := μ) (ν := ν)
      (X := X) (brownianContinuousVersion_unitStrip_memLp_two (μ := μ) (B := B) hB)

-- Proof sketch: write the average as a centered Gaussian linear functional of the Brownian path.
-- Fubini and the Brownian covariance kernel `min(s,t)` give expectation `0` and covariance
-- integral `∫₀¹∫₀¹ min(s,t) ds dt = 1/3`; the expectation statement is the first moment
-- computation.
/-- For Exercise 21.2.1, item (i), the expectation of the Brownian sample-path average over
`[0,1]` is zero. -/
theorem brownianUnitIntervalAverage_expectation (hB : IsBrownianMotion μ B) :
    ∫ ω, (∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω) ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  letI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    simp
  have hone_le_two : (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
  have hstripInt :
      Integrable
        (Function.uncurry fun t ω ↦
          brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω)
        (((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod μ)) := by
    -- Route correction: the missing measurability issue is already resolved by the patched
    -- continuous version, so the real input here is the unit-strip `L²` package.
    simpa [Function.uncurry, Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      ((brownianContinuousVersion_unitStrip_memLp_two (μ := μ) (B := B) hB).integrable
        hone_le_two)
  have hswap :=
    MeasureTheory.intervalIntegral_integral_swap
      (μ := μ)
      (f := fun t ω ↦ brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω)
      hstripInt
  have hpatched :
      ∫ ω, (∫ t in (0 : ℝ)..1,
        brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω) ∂μ = 0 := by
    calc
      ∫ ω, (∫ t in (0 : ℝ)..1,
          brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω) ∂μ
          = ∫ t in (0 : ℝ)..1, ∫ ω,
              brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω ∂μ := by
                simpa using hswap.symm
      _ = ∫ t in (0 : ℝ)..1, (0 : ℝ) := by
            -- Proof comment: every fixed-time marginal of the patched process is still centered.
            refine intervalIntegral.integral_congr_ae <|
              Filter.Eventually.of_forall fun t _ ↦
              brownianContinuousVersion_eval_expectation_eq_zero (μ := μ) (B := B) hB
                (Real.toNNReal t)
      _ = 0 := by simp
  calc
    ∫ ω, (∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω) ∂μ
        = ∫ ω, (∫ t in (0 : ℝ)..1,
            brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω) ∂μ := by
              exact integral_congr_ae
                (brownianContinuousVersion_average_ae_eq (μ := μ) (B := B) hB).symm
    _ = 0 := hpatched

-- Proof sketch: the same covariance computation as in part (i) shows that
-- `Var[∫₀¹ B_s ds] = ∫₀¹∫₀¹ min(s,t) ds dt = 1/3`.
/-- For Exercise 21.2.1, item (i), the variance of the Brownian sample-path average over `[0,1]`
is `1 / 3`. -/
theorem brownianUnitIntervalAverage_variance (hB : IsBrownianMotion μ B) :
    Var[fun ω ↦ ∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω; μ] = 1 / 3 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let Ac : Ω → ℝ := fun ω ↦ ∫ t,
    brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω ∂ν
  let X : ℝ × Ω → ℝ := fun z ↦
    brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2
  letI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    simp [ν]
  have hone_le_two : (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
  have hAc_mem :
      MemLp Ac 2 μ := by
    -- Proof comment: reuse the dedicated `L²` helper for the patched average.
    simpa [Ac, ν] using
      brownianContinuousVersion_unitIntervalAverage_memLp_two (μ := μ) (B := B) hB
  have hX_mem : MemLp X 2 (ν.prod μ) := by
    -- Proof comment: the strip function is square-integrable on the unit strip.
    simpa [ν, X] using
      brownianContinuousVersion_unitStrip_memLp_two (μ := μ) (B := B) hB
  have hXInt :
      Integrable X (ν.prod μ) := by
    -- Proof comment: the strip function is in `L²`, hence also integrable on the unit strip.
    exact hX_mem.integrable hone_le_two
  have hAc_original :
      Ac =ᵐ[μ] fun ω ↦ ∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω := by
    -- Proof comment: the patched and original averages agree almost surely.
    filter_upwards [brownianContinuousVersion_average_ae_eq (μ := μ) (B := B) hB] with ω hω
    simpa [Ac, ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hω
  have hAc_mean : ∫ ω, Ac ω ∂μ = 0 := by
    -- Proof comment: transfer the already proved mean-zero statement from the original average.
    calc
      ∫ ω, Ac ω ∂μ = ∫ ω, (∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω) ∂μ := by
        exact integral_congr_ae hAc_original
      _ = 0 := brownianUnitIntervalAverage_expectation (μ := μ) (B := B) hB
  have hProdInt :
      Integrable (fun z : ℝ × Ω ↦ X z * Ac z.2) (ν.prod μ) := by
    -- Proof comment: on the strip, multiply the `L²` Brownian field with the `L²` average lifted
    -- to the second coordinate.
    have hAcProd : MemLp (fun z : ℝ × Ω ↦ Ac z.2) 2 (ν.prod μ) := hAc_mem.comp_snd ν
    simpa [X] using MemLp.integrable_mul hX_mem hAcProd
  have hSecondMoment :
      ∫ ω, Ac ω ^ 2 ∂μ = 1 / 3 := by
    have hFubini :
        ∫ z, X z * Ac z.2 ∂(ν.prod μ) = ∫ ω, Ac ω ^ 2 ∂μ := by
      calc
        ∫ z, X z * Ac z.2 ∂(ν.prod μ)
            = ∫ ω, ∫ t, X (t, ω) * Ac ω ∂ν ∂μ := by
                simpa [X] using
                  (MeasureTheory.integral_prod_symm (μ := ν) (ν := μ)
                    (f := fun z : ℝ × Ω ↦ X z * Ac z.2) hProdInt)
        _ = ∫ ω, Ac ω ^ 2 ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards [hXInt.prod_left_ae] with ω hω
              rw [integral_mul_const]
              simpa [Ac, X, pow_two] using rfl
    have hInner :
        (fun t : ℝ ↦ ∫ ω, X (t, ω) * Ac ω ∂μ) =ᵐ[ν] fun t ↦ t - t ^ 2 / 2 := by
      refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
      filter_upwards with t ht
      have ht_nonneg : 0 ≤ t := le_of_lt ht.1
      have ht_le_one : t ≤ 1 := ht.2
      calc
        ∫ ω, X (t, ω) * Ac ω ∂μ
            = ∫ ω, B (Real.toNNReal t) ω * Ac ω ∂μ := by
                refine integral_congr_ae ?_
                filter_upwards
                  [brownianContinuousVersion_areModifications (μ := μ) (B := B) hB
                    (Real.toNNReal t)] with ω hω
                simp [X, hω]
        _ = ∫ ω, B (Real.toNNReal t) ω * (∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards [hAc_original] with ω hω
              simp [hω]
        _ = t - t ^ 2 / 2 :=
              brownianEval_mulUnitIntervalAverage_eq (μ := μ) (B := B) hB ht_nonneg ht_le_one
    calc
      ∫ ω, Ac ω ^ 2 ∂μ = ∫ z, X z * Ac z.2 ∂(ν.prod μ) := hFubini.symm
      _ = ∫ t, ∫ ω, X (t, ω) * Ac ω ∂μ ∂ν := by
            simpa [X] using
              (MeasureTheory.integral_prod (μ := ν) (ν := μ)
                (f := fun z : ℝ × Ω ↦ X z * Ac z.2) hProdInt)
      _ = ∫ t, (t - t ^ 2 / 2 : ℝ) ∂ν := by
            exact integral_congr_ae hInner
      _ = 1 / 3 := by
            simpa [ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
              brownianAverageKernelIntegral_eq_one_third
  have hVarAc :
      Var[Ac; μ] = 1 / 3 := by
    -- Proof comment: variance is second moment minus squared mean on a probability space.
    simpa [hAc_mean, hSecondMoment] using
      (ProbabilityTheory.variance_eq_sub (μ := μ) hAc_mem)
  calc
    Var[fun ω ↦ ∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω; μ] = Var[Ac; μ] := by
      exact ProbabilityTheory.variance_congr hAc_original.symm
    _ = 1 / 3 := hVarAc

-- Proof sketch: almost every Brownian sample path is continuous, so its zero set is closed. A
-- nontrivial interval of zeros would force a constant segment and hence violate the Gaussian
-- increment law; cover the zero set by intervals on which oscillation is small and conclude it has
-- Lebesgue measure zero.
/-- For Exercise 21.2.1, item (ii), almost every Brownian sample path has zero set of Lebesgue
measure zero on `[0, ∞)`, modeled here by Lebesgue measure on `ℝ` restricted to `Set.Ici 0`. -/
theorem brownianZeroSet_volume_eq_zero_ae (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, nonnegativeLebesgue {t : ℝ | B (Real.toNNReal t) ω = 0} = 0 := by
  let Zp : Ω → Set ℝ := fun ω ↦
    {t : ℝ | brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω = 0}
  let Zo : Ω → Set ℝ := fun ω ↦ {t : ℝ | B (Real.toNNReal t) ω = 0}
  have hFinite :
      ∀ᵐ ω ∂μ, ∀ n : ℕ,
        (volume.restrict (Set.Ioc (0 : ℝ) (n + 1 : ℝ))) (Zp ω) = 0 := by
    rw [ae_all_iff]
    intro n
    exact
      brownianContinuousVersion_zeroSet_measureOnIoc_eq_zero_ae
        (μ := μ) (B := B) hB (show (0 : ℝ) < (n + 1 : ℝ) by positivity)
  filter_upwards [brownianContinuousVersion_zeroSet_ae_eq (μ := μ) (B := B) hB, hFinite] with ω hEq hFiniteω
  have hZp_meas : MeasurableSet (Zp ω) := by
    have hcont :
        Continuous
          (fun t : ℝ ↦ brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω) := by
      simpa [Function.comp] using
        (brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω).comp continuous_real_toNNReal
    exact (isClosed_eq hcont continuous_const).measurableSet
  have hSingletonNull : volume (Zp ω ∩ ({0} : Set ℝ)) = 0 := by
    exact
      measure_mono_null
        (by
          intro x hx
          exact hx.2)
        (by simpa using (MeasureTheory.measure_singleton (μ := volume) 0))
  have hIntervalsNull :
      ∀ n : ℕ, volume (Zp ω ∩ Set.Ioc (0 : ℝ) (n + 1 : ℝ)) = 0 := by
    intro n
    rw [← Measure.restrict_apply hZp_meas]
    exact hFiniteω n
  have hUnionNull :
      volume (⋃ n : ℕ, Zp ω ∩ Set.Ioc (0 : ℝ) (n + 1 : ℝ)) = 0 :=
    measure_iUnion_null hIntervalsNull
  have hCover :
      Zp ω ∩ Set.Ici (0 : ℝ) ⊆
        (Zp ω ∩ ({0} : Set ℝ)) ∪ ⋃ n : ℕ, Zp ω ∩ Set.Ioc (0 : ℝ) (n + 1 : ℝ) := by
    intro t ht
    rcases ht with ⟨htZp, ht_nonneg⟩
    by_cases ht0 : t = 0
    · left
      simpa [ht0] using htZp
    · right
      have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht0)
      obtain ⟨n, hn⟩ := exists_nat_gt t
      have ht_le : t ≤ (n + 1 : ℝ) := by
        have ht_lt : t < (n + 1 : ℝ) := by
          calc
            t < n := hn
            _ < (n + 1 : ℝ) := by exact_mod_cast Nat.lt_succ_self n
        exact le_of_lt ht_lt
      exact Set.mem_iUnion.2 ⟨n, ⟨htZp, ⟨ht_pos, ht_le⟩⟩⟩
  have hZpNull :
      nonnegativeLebesgue (Zp ω) = 0 := by
    rw [show nonnegativeLebesgue = volume.restrict (Set.Ici (0 : ℝ)) by rfl]
    rw [Measure.restrict_apply hZp_meas]
    exact measure_mono_null hCover (measure_union_null hSingletonNull hUnionNull)
  simpa [Zp, Zo, hEq] using hZpNull

-- Proof sketch: expand the square, use linearity of expectation, and evaluate the resulting
-- covariance integrals for `B_t` and the path average. This yields
-- `∫₀¹ E[(B_t - ∫₀¹ B_s ds)^2] dt = 1/6`.
/-- For Exercise 21.2.1, item (iii), the expectation of the integrated squared deviation from the
unit-interval Brownian average is `1 / 6`. -/
theorem brownianUnitIntervalCenteredQuadraticDeviation_expectation (hB : IsBrownianMotion μ B) :
    ∫ ω, (∫ t in (0 : ℝ)..1,
      (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2) ∂μ = 1 / 6 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let Ac : Ω → ℝ := fun ω ↦
    ∫ s, brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s) ω ∂ν
  let Z : ℝ → Ω → ℝ := fun t ω ↦
    brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω - Ac ω
  let Zstrip : ℝ × Ω → ℝ := fun z ↦ Z z.1 z.2
  letI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    simp [ν]
  have hAc_mem : MemLp Ac 2 μ := by
    simpa [Ac, ν] using
      brownianContinuousVersion_unitIntervalAverage_memLp_two (μ := μ) (B := B) hB
  have hAc_original :
      Ac =ᵐ[μ] fun ω ↦ ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω := by
    simpa [Ac, ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      brownianContinuousVersion_average_ae_eq (μ := μ) (B := B) hB
  have hAc_mean : ∫ ω, Ac ω ∂μ = 0 := by
    calc
      ∫ ω, Ac ω ∂μ = ∫ ω, (∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ∂μ := by
        exact integral_congr_ae hAc_original
      _ = 0 := brownianUnitIntervalAverage_expectation (μ := μ) (B := B) hB
  have hAc_secondMoment : ∫ ω, Ac ω ^ 2 ∂μ = 1 / 3 := by
    have hVarAc : Var[Ac; μ] = 1 / 3 := by
      calc
        Var[Ac; μ] = Var[fun ω ↦ ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω; μ] := by
          exact ProbabilityTheory.variance_congr hAc_original
        _ = 1 / 3 := brownianUnitIntervalAverage_variance (μ := μ) (B := B) hB
    rw [← ProbabilityTheory.variance_of_integral_eq_zero hAc_mem.aestronglyMeasurable.aemeasurable
      hAc_mean]
    exact hVarAc
  have hStripB_mem :
      MemLp
        (fun z : ℝ × Ω ↦
          brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2)
        2 (ν.prod μ) := by
    simpa [ν] using
      brownianContinuousVersion_unitStrip_memLp_two (μ := μ) (B := B) hB
  have hAc_prod_mem : MemLp (fun z : ℝ × Ω ↦ Ac z.2) 2 (ν.prod μ) := hAc_mem.comp_snd ν
  have hZstrip_mem : MemLp Zstrip 2 (ν.prod μ) := by
    simpa [Zstrip, Z] using hStripB_mem.sub hAc_prod_mem
  have hZstrip_sq_int :
      Integrable (fun z : ℝ × Ω ↦ Zstrip z ^ 2) (ν.prod μ) := by
    simpa [Zstrip] using hZstrip_mem.integrable_sq
  have hswap :=
    MeasureTheory.intervalIntegral_integral_swap
      (a := 0) (b := 1)
      (μ := μ) (f := fun t ω ↦ Z t ω ^ 2)
      (by
        simpa [Zstrip, Z, Function.uncurry, ν, Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
          hZstrip_sq_int)
  have hInner :
      (fun t : ℝ ↦ ∫ ω, Z t ω ^ 2 ∂μ) =ᵐ[ν] fun t ↦ t ^ 2 - t + 1 / 3 := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with t ht
    have ht_nonneg : 0 ≤ t := le_of_lt ht.1
    have ht_le_one : t ≤ 1 := ht.2
    let Bt : Ω → ℝ :=
      brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t)
    have hBt_mem : MemLp Bt 2 μ :=
      brownianContinuousVersion_eval_memLp_two (μ := μ) (B := B) hB (Real.toNNReal t)
    have hBt_sq_int : Integrable (fun ω ↦ Bt ω ^ 2) μ := hBt_mem.integrable_sq
    have hCross_int : Integrable (fun ω ↦ Bt ω * Ac ω) μ := hBt_mem.integrable_mul hAc_mem
    have hCross_eq :
        ∫ ω, Bt ω * Ac ω ∂μ = t - t ^ 2 / 2 := by
      calc
        ∫ ω, Bt ω * Ac ω ∂μ
            = ∫ ω,
                brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω *
                  (∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ∂μ := by
                    refine integral_congr_ae ?_
                    filter_upwards [hAc_original] with ω hω
                    simp [Bt, hω]
        _ = ∫ ω, B (Real.toNNReal t) ω *
              (∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ∂μ := by
                refine integral_congr_ae ?_
                filter_upwards
                  [brownianContinuousVersion_areModifications (μ := μ) (B := B) hB
                    (Real.toNNReal t)] with ω hω
                simp [Bt, hω]
        _ = t - t ^ 2 / 2 :=
              brownianEval_mulUnitIntervalAverage_eq (μ := μ) (B := B) hB ht_nonneg ht_le_one
    have hExpand :
        ∫ ω, Z t ω ^ 2 ∂μ =
          ∫ ω, Bt ω ^ 2 ∂μ - 2 * ∫ ω, Bt ω * Ac ω ∂μ + ∫ ω, Ac ω ^ 2 ∂μ := by
      have hCross_int' : Integrable (fun ω ↦ 2 * (Bt ω * Ac ω)) μ := hCross_int.const_mul 2
      have hIntegralSplit :
          ∫ ω, ((Bt ω ^ 2 - 2 * (Bt ω * Ac ω)) + Ac ω ^ 2) ∂μ =
            ∫ ω, (Bt ω ^ 2 - 2 * (Bt ω * Ac ω)) ∂μ + ∫ ω, Ac ω ^ 2 ∂μ := by
        exact
          integral_add
            (f := fun ω ↦ Bt ω ^ 2 - 2 * (Bt ω * Ac ω))
            (g := fun ω ↦ Ac ω ^ 2)
            (hBt_sq_int.sub hCross_int')
            hAc_mem.integrable_sq
      calc
        ∫ ω, Z t ω ^ 2 ∂μ
            = ∫ ω, (Bt ω ^ 2 - 2 * (Bt ω * Ac ω) + Ac ω ^ 2) ∂μ := by
                refine integral_congr_ae ?_
                filter_upwards with ω
                simp [Z, Bt]
                ring
        _ = ∫ ω, (Bt ω ^ 2 - 2 * (Bt ω * Ac ω)) ∂μ + ∫ ω, Ac ω ^ 2 ∂μ := hIntegralSplit
        _ = (∫ ω, Bt ω ^ 2 ∂μ - ∫ ω, 2 * (Bt ω * Ac ω) ∂μ) + ∫ ω, Ac ω ^ 2 ∂μ := by
              rw [integral_sub hBt_sq_int hCross_int']
        _ = ∫ ω, Bt ω ^ 2 ∂μ - 2 * ∫ ω, Bt ω * Ac ω ∂μ + ∫ ω, Ac ω ^ 2 ∂μ := by
              rw [integral_const_mul]
    rw [hExpand, brownianContinuousVersion_eval_secondMoment_eq (μ := μ) (B := B) hB
      (Real.toNNReal t), hCross_eq, hAc_secondMoment]
    have hcoe : (((Real.toNNReal t : NNReal) : ℝ)) = t := by
      simp [Real.toNNReal_of_nonneg ht_nonneg]
    rw [hcoe]
    ring
  calc
    ∫ ω, (∫ t in (0 : ℝ)..1,
        (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2) ∂μ
        = ∫ ω, (∫ t in (0 : ℝ)..1, Z t ω ^ 2) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [hAc_original, brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB] with
              ω hω hω_patch
            simp [Z, hω, hω_patch]
    _ = ∫ t in (0 : ℝ)..1, ∫ ω, Z t ω ^ 2 ∂μ := by
          simpa using hswap.symm
    _ = ∫ t in (0 : ℝ)..1, (t ^ 2 - t + 1 / 3 : ℝ) := by
          simpa [ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
            integral_congr_ae hInner
    _ = 1 / 6 := by
          exact brownianCenteredVariancePolynomialIntegral_eq_one_six

/-- Helper for Exercise 21.2.1: on `[0,1]`, the centered Brownian-average process has the explicit
covariance kernel `min s t - s - t + s² / 2 + t² / 2 + 1 / 3`. -/
lemma brownianCenteredCovarianceKernel_eq (hB : IsBrownianMotion μ B) {s t : ℝ}
    (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1) (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) :
    cov[
      (fun ω ↦ B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω),
      (fun ω ↦ B (Real.toNNReal t) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω); μ] =
      min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let Ac : Ω → ℝ := fun ω ↦
    ∫ u, brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal u) ω ∂ν
  have hs_mem : MemLp (B (Real.toNNReal s)) 2 μ :=
    brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal s)
  have ht_mem : MemLp (B (Real.toNNReal t)) 2 μ :=
    brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal t)
  have hAc_mem : MemLp Ac 2 μ := by
    simpa [Ac, ν] using
      brownianContinuousVersion_unitIntervalAverage_memLp_two (μ := μ) (B := B) hB
  have hAc_original :
      Ac =ᵐ[μ] fun ω ↦ ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω := by
    simpa [Ac, ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      brownianContinuousVersion_average_ae_eq (μ := μ) (B := B) hB
  have hAc_mean : ∫ ω, Ac ω ∂μ = 0 := by
    -- Proof comment: the patched and original averages agree almost surely, so they share the
    -- expectation from part `(i)`.
    calc
      ∫ ω, Ac ω ∂μ = ∫ ω, (∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ∂μ := by
          exact integral_congr_ae hAc_original
      _ = 0 := brownianUnitIntervalAverage_expectation (μ := μ) (B := B) hB
  have hCov_sAc : cov[B (Real.toNNReal s), Ac; μ] = s - s ^ 2 / 2 := by
    -- Proof comment: both variables are centered, so covariance reduces to the mixed second
    -- moment already computed against the unit-interval average.
    rw [covariance_eq_sub hs_mem hAc_mem,
      brownianEval_expectation_eq_zero (μ := μ) (B := B) hB (Real.toNNReal s), hAc_mean,
      zero_mul, sub_zero]
    calc
      ∫ ω, B (Real.toNNReal s) ω * Ac ω ∂μ
          = ∫ ω, B (Real.toNNReal s) ω *
              (∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ∂μ := by
                refine integral_congr_ae ?_
                filter_upwards [hAc_original] with ω hω
                simp [hω]
      _ = s - s ^ 2 / 2 :=
            brownianEval_mulUnitIntervalAverage_eq (μ := μ) (B := B) hB hs_nonneg hs_le_one
  have hCov_tAc : cov[B (Real.toNNReal t), Ac; μ] = t - t ^ 2 / 2 := by
    -- Proof comment: the same mixed-moment identity applies at the second endpoint.
    rw [covariance_eq_sub ht_mem hAc_mem,
      brownianEval_expectation_eq_zero (μ := μ) (B := B) hB (Real.toNNReal t), hAc_mean,
      zero_mul, sub_zero]
    calc
      ∫ ω, B (Real.toNNReal t) ω * Ac ω ∂μ
          = ∫ ω, B (Real.toNNReal t) ω *
              (∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ∂μ := by
                refine integral_congr_ae ?_
                filter_upwards [hAc_original] with ω hω
                simp [hω]
      _ = t - t ^ 2 / 2 :=
            brownianEval_mulUnitIntervalAverage_eq (μ := μ) (B := B) hB ht_nonneg ht_le_one
  have hCov_Ac_t : cov[Ac, B (Real.toNNReal t); μ] = t - t ^ 2 / 2 := by
    -- Proof comment: swap the covariance factors and reuse the centered mixed-moment identity.
    rw [covariance_comm]
    exact hCov_tAc
  have hCov_Ac_Ac : cov[Ac, Ac; μ] = 1 / 3 := by
    -- Proof comment: the average covariance on the diagonal is its variance, already computed in
    -- part `(i)`.
    rw [covariance_self hAc_mem.aestronglyMeasurable.aemeasurable]
    calc
      Var[Ac; μ]
          = Var[fun ω ↦ ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω; μ] := by
              exact ProbabilityTheory.variance_congr hAc_original
      _ = 1 / 3 := brownianUnitIntervalAverage_variance (μ := μ) (B := B) hB
  have hCentered_congr :
      cov[
        (fun ω ↦ B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω),
        (fun ω ↦ B (Real.toNNReal t) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω); μ] =
        cov[
          (fun ω ↦ B (Real.toNNReal s) ω - Ac ω),
          (fun ω ↦ B (Real.toNNReal t) ω - Ac ω); μ] := by
    -- Proof comment: move once to the patched-average spelling, where the `L²` control is already
    -- available earlier in the file.
    refine covariance_congr_ae (μ := μ) ?_ ?_
    · filter_upwards [hAc_original] with ω hω
      simp [hω]
    · filter_upwards [hAc_original] with ω hω
      simp [hω]
  have hSubLeft :
      cov[fun ω ↦ B (Real.toNNReal s) ω - Ac ω, fun ω ↦ B (Real.toNNReal t) ω - Ac ω; μ] =
        cov[B (Real.toNNReal s), fun ω ↦ B (Real.toNNReal t) ω - Ac ω; μ] -
          cov[Ac, fun ω ↦ B (Real.toNNReal t) ω - Ac ω; μ] := by
    simpa using
      (covariance_sub_left hs_mem hAc_mem (ht_mem.sub hAc_mem) :
        cov[fun ω ↦ B (Real.toNNReal s) ω - Ac ω,
          fun ω ↦ B (Real.toNNReal t) ω - Ac ω; μ] =
          cov[B (Real.toNNReal s), fun ω ↦ B (Real.toNNReal t) ω - Ac ω; μ] -
            cov[Ac, fun ω ↦ B (Real.toNNReal t) ω - Ac ω; μ])
  have hSubRightBs :
      cov[B (Real.toNNReal s), fun ω ↦ B (Real.toNNReal t) ω - Ac ω; μ] =
        cov[B (Real.toNNReal s), B (Real.toNNReal t); μ] -
          cov[B (Real.toNNReal s), Ac; μ] := by
    simpa using
      (covariance_sub_right hs_mem ht_mem hAc_mem :
        cov[B (Real.toNNReal s), fun ω ↦ B (Real.toNNReal t) ω - Ac ω; μ] =
          cov[B (Real.toNNReal s), B (Real.toNNReal t); μ] - cov[B (Real.toNNReal s), Ac; μ])
  have hSubRightAc :
      cov[Ac, fun ω ↦ B (Real.toNNReal t) ω - Ac ω; μ] =
        cov[Ac, B (Real.toNNReal t); μ] - cov[Ac, Ac; μ] := by
    simpa using
      (covariance_sub_right hAc_mem ht_mem hAc_mem :
        cov[Ac, fun ω ↦ B (Real.toNNReal t) ω - Ac ω; μ] =
          cov[Ac, B (Real.toNNReal t); μ] - cov[Ac, Ac; μ])
  -- Proof comment: after the one-time transport to the patched average, bilinearity and the
  -- already-computed mixed moments finish the kernel formula.
  calc
    cov[
        (fun ω ↦ B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω),
        (fun ω ↦ B (Real.toNNReal t) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω); μ]
        = cov[
            (fun ω ↦ B (Real.toNNReal s) ω - Ac ω),
            (fun ω ↦ B (Real.toNNReal t) ω - Ac ω); μ] := hCentered_congr
    _ = cov[B (Real.toNNReal s), B (Real.toNNReal t); μ] -
          cov[B (Real.toNNReal s), Ac; μ] -
            cov[Ac, B (Real.toNNReal t); μ] +
              cov[Ac, Ac; μ] := by
            rw [hSubLeft, hSubRightBs, hSubRightAc]
            ring
    _ = min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 := by
          rw [brownianCovariance_eq_min (μ := μ) (B := B) hB (Real.toNNReal s) (Real.toNNReal t),
            hCov_sAc, hCov_Ac_t, hCov_Ac_Ac]
          simp [Real.toNNReal_of_nonneg hs_nonneg, Real.toNNReal_of_nonneg ht_nonneg]
          ring

/-- Helper for Exercise 21.2.1: the kernel integral `∫₀¹ min r u du` equals `r - r² / 2` on
`[0,1]`. -/
private lemma unitIntervalIntegral_min_eq {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_le_one : r ≤ 1) :
    ∫ u in (0 : ℝ)..1, min r u = r - r ^ 2 / 2 := by
  have hmin_cont : Continuous fun u : ℝ ↦ min r u := continuous_const.min continuous_id
  have hsplit :
      (∫ u in (0 : ℝ)..r, min r u) + ∫ u in r..1, min r u =
        ∫ u in (0 : ℝ)..1, min r u := by
    -- Proof comment: split the integral once at the threshold where the minimum changes form.
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (hmin_cont.intervalIntegrable 0 r)
        (hmin_cont.intervalIntegrable r 1))
  have hleft :
      ∫ u in (0 : ℝ)..r, min r u = ∫ u in (0 : ℝ)..r, (u : ℝ) := by
    -- Proof comment: on `(0,r]`, the minimum is the integration variable.
    refine intervalIntegral.integral_congr_ae (μ := volume) (a := (0 : ℝ)) (b := r) ?_
    filter_upwards with u hu
    have hu' : u ∈ Set.Ioc (0 : ℝ) r := by
      simpa [Set.uIoc_of_le hr_nonneg] using hu
    exact min_eq_right hu'.2
  have hright :
      ∫ u in r..1, min r u = ∫ u in r..1, (r : ℝ) := by
    -- Proof comment: on `(r,1]`, the minimum is the constant endpoint `r`.
    refine intervalIntegral.integral_congr_ae (μ := volume) (a := r) (b := 1) ?_
    filter_upwards with u hu
    have hu' : u ∈ Set.Ioc r 1 := by
      simpa [Set.uIoc_of_le hr_le_one] using hu
    exact min_eq_left (le_of_lt hu'.1)
  have hleft_eval : ∫ u in (0 : ℝ)..r, (u : ℝ) = r ^ 2 / 2 := by
    norm_num [integral_pow]
  have hright_eval : ∫ u in r..1, (r : ℝ) = (1 - r) * r := by
    simpa [smul_eq_mul] using (intervalIntegral.integral_const (a := r) (b := 1) (c := r))
  rw [← hsplit, hleft, hright, hleft_eval, hright_eval]
  ring

/-- Helper for Exercise 21.2.1: the mixed second moment against the endpoint average approximation
is the explicit endpoint mesh sum of the Brownian kernel. -/
lemma brownianEval_mulUnitIntervalAverageRiemannApprox_eq_meshSum
    (hB : IsBrownianMotion μ B) {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_le_one : r ≤ 1) (n : ℕ) :
    ∫ ω,
      B (Real.toNNReal r) ω * brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ =
        (1 / (n + 1 : ℝ)) *
          ∑ k : Fin (n + 2), min r ((k : ℝ) / (n + 1 : ℝ)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hBr_mem : MemLp (B (Real.toNNReal r)) 2 μ :=
    brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal r)
  have hExpand :
      (fun ω ↦ B (Real.toNNReal r) ω * brownianUnitIntervalAverageRiemannApprox (B := B) n ω) =
        fun ω ↦
          (1 / (n + 1 : ℝ)) *
            ∑ k : Fin (n + 2),
              B (Real.toNNReal r) ω *
                B (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))) ω := by
    -- Proof comment: unfold the endpoint approximant once and push the fixed Brownian factor
    -- through the finite sum.
    funext ω
    simp [brownianUnitIntervalAverageRiemannApprox, Finset.mul_sum, mul_assoc, mul_left_comm,
      mul_comm]
  rw [hExpand, integral_const_mul, integral_finset_sum]
  · refine congrArg (fun x : ℝ ↦ (1 / (n + 1 : ℝ)) * x) ?_
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hk_nonneg : 0 ≤ (k : ℝ) / (n + 1 : ℝ) := by positivity
    have hBk_mem :
        MemLp (B (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ)))) 2 μ :=
      brownianEval_memLp_two (μ := μ) (X := B) hB
        (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ)))
    have hCov :
        cov[B (Real.toNNReal r), B (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))); μ] =
          ∫ ω,
            B (Real.toNNReal r) ω *
              B (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))) ω ∂μ := by
      -- Proof comment: both Brownian coordinates are centered, so the covariance is exactly the
      -- mixed second moment.
      rw [covariance_eq_sub hBr_mem hBk_mem,
        brownianEval_expectation_eq_zero (μ := μ) (B := B) hB (Real.toNNReal r),
        brownianEval_expectation_eq_zero (μ := μ) (B := B) hB
          (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))),
        zero_mul, sub_zero]
      simp [Pi.mul_apply]
    calc
      ∫ ω,
          B (Real.toNNReal r) ω *
            B (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))) ω ∂μ
          =
          cov[B (Real.toNNReal r), B (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))); μ] :=
        hCov.symm
      _ = min r ((k : ℝ) / (n + 1 : ℝ)) := by
            simpa [Real.toNNReal_of_nonneg hr_nonneg, Real.toNNReal_of_nonneg hk_nonneg] using
              brownianCovariance_eq_min (μ := μ) (B := B) hB
                (Real.toNNReal r) (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ)))
  · intro k _
    have hBk_mem :
        MemLp (B (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ)))) 2 μ :=
      brownianEval_memLp_two (μ := μ) (X := B) hB
        (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ)))
    exact hBr_mem.integrable_mul hBk_mem

/-- Helper for Exercise 21.2.1: the mixed moments against the endpoint average approximations
converge to the exact mixed moment `r - r² / 2`. -/
lemma brownianEval_mulUnitIntervalAverageRiemannApprox_tendsto
    (hB : IsBrownianMotion μ B) {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_le_one : r ≤ 1) :
    Tendsto
      (fun n : ℕ ↦
        ∫ ω, B (Real.toNNReal r) ω *
          brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ)
      atTop
      (𝓝 (r - r ^ 2 / 2)) := by
  have hMesh :
      (fun n : ℕ ↦
        ∫ ω, B (Real.toNNReal r) ω *
          brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ) =
        fun n : ℕ ↦
          (1 / (n + 1 : ℝ)) * ∑ k : Fin (n + 2), min r ((k : ℝ) / (n + 1 : ℝ)) := by
    -- Proof comment: replace the stochastic mixed moment by the deterministic endpoint mesh sum
    -- once and keep that normal form for the limit.
    funext n
    exact brownianEval_mulUnitIntervalAverageRiemannApprox_eq_meshSum
      (μ := μ) (B := B) hB hr_nonneg hr_le_one n
  have hMinCont : Continuous (fun u : ℝ ↦ min r u) := continuous_const.min continuous_id
  rw [hMesh]
  simpa [unitIntervalIntegral_min_eq hr_nonneg hr_le_one] using
    endpointRiemannSums_tendsto_intervalIntegral (f := fun u : ℝ ↦ min r u) hMinCont

/-- Helper for Exercise 21.2.1: the casted arithmetic sum `∑_{j < m} j` has the usual closed
form. -/
private lemma sumRangeIdCast (m : ℕ) :
    Finset.sum (Finset.range m) (fun j ↦ (j : ℝ)) = ((m * (m - 1) / 2 : ℕ) : ℝ) := by
  -- Proof comment: cast the standard nat-valued arithmetic-series identity once so later
  -- polynomial simplifications stay in `ℝ`.
  simpa using congrArg (fun t : ℕ ↦ (t : ℝ)) (Finset.sum_range_id m)

/-- Helper for Exercise 21.2.1: the casted quadratic sum `∑_{k=0}^N k²` has its standard closed
form. -/
private lemma sumRangeSquareCast (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ) ^ (2 : ℕ)) =
      (N : ℝ) * (N + 1) * (2 * N + 1) / 6 := by
  -- Proof comment: a short induction is enough once the range endpoint is written as `N + 1`.
  induction N with
  | zero =>
      norm_num
  | succ N hN =>
      rw [Finset.sum_range_succ, hN]
      norm_num [pow_two]
      ring_nf

/-- Helper for Exercise 21.2.1: the endpoint-rule mesh sum for
`j ↦ min (m / (n + 1)) (j / (n + 1))` has the closed form given by the continuum kernel plus the
trapezoidal correction term. -/
private lemma endpointMeshMin_sum_nat_eq_gridCorrection (n m : ℕ) (hm : m ≤ n + 1) :
    (1 / (n + 1 : ℝ)) *
        Finset.sum (Finset.range (n + 2))
          (fun j ↦ min ((m : ℝ) / (n + 1 : ℝ)) ((j : ℝ) / (n + 1 : ℝ))) =
      ((m : ℝ) / (n + 1 : ℝ)) - (((m : ℝ) / (n + 1 : ℝ)) ^ 2) / 2 +
        ((m : ℝ) / (n + 1 : ℝ)) / (2 * (n + 1 : ℝ)) := by
  set N : ℕ := n + 1
  have hmN : m ≤ N := by simpa [N] using hm
  have hmN' : m ≤ N + 1 := Nat.le_succ_of_le hmN
  have hN_pos : 0 < (N : ℝ) := by positivity
  suffices hmain :
      (1 / (N : ℝ)) *
          Finset.sum (Finset.range (N + 1))
            (fun j ↦ min ((m : ℝ) / N) ((j : ℝ) / N)) =
        ((m : ℝ) / N) - (((m : ℝ) / N) ^ 2) / 2 + ((m : ℝ) / N) / (2 * N) by
    simpa [N] using hmain
  have hleft :
      Finset.sum (Finset.range m) (fun j ↦ min ((m : ℝ) / N) ((j : ℝ) / N)) =
        Finset.sum (Finset.range m) (fun j ↦ (j : ℝ) / N) := by
    -- Proof comment: below the split point `m`, the minimum is just the varying mesh index.
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj_le : (j : ℝ) ≤ m := by
      exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hj)
    have hdiv : (j : ℝ) / N ≤ (m : ℝ) / N := by
      gcongr
    exact min_eq_right hdiv
  have hright :
      Finset.sum (Finset.Ico m (N + 1)) (fun j ↦ min ((m : ℝ) / N) ((j : ℝ) / N)) =
        ((Finset.Ico m (N + 1)).card : ℝ) * ((m : ℝ) / N) := by
    -- Proof comment: on the tail `[m, N]`, the minimum is the constant endpoint value `m / N`.
    calc
      Finset.sum (Finset.Ico m (N + 1)) (fun j ↦ min ((m : ℝ) / N) ((j : ℝ) / N))
          = Finset.sum (Finset.Ico m (N + 1)) (fun _j ↦ ((m : ℝ) / N)) := by
              refine Finset.sum_congr rfl fun j hj ↦ ?_
              have hj_ge : m ≤ j := (Finset.mem_Ico.mp hj).1
              have hdiv : (m : ℝ) / N ≤ (j : ℝ) / N := by
                gcongr
              exact min_eq_left hdiv
      _ = ((Finset.Ico m (N + 1)).card : ℝ) * ((m : ℝ) / N) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_range_add_sum_Ico _ hmN', hleft, hright]
  have hsum :
      Finset.sum (Finset.range m) (fun j ↦ (j : ℝ) / N) = ((m * (m - 1) / 2 : ℕ) : ℝ) / N := by
    -- Proof comment: the lower block is a scalar multiple of the arithmetic sum `∑_{j < m} j`.
    calc
      Finset.sum (Finset.range m) (fun j ↦ (j : ℝ) / N)
          = (Finset.sum (Finset.range m) (fun j ↦ (j : ℝ))) / N := by
              rw [Finset.sum_div]
      _ = ((m * (m - 1) / 2 : ℕ) : ℝ) / N := by rw [sumRangeIdCast]
  rw [hsum]
  have hcard : ((Finset.Ico m (N + 1)).card : ℝ) = (N + 1 - m : ℕ) := by
    simp [hmN']
  rw [hcard]
  have hNatSub : ((N + 1 - m : ℕ) : ℝ) = (N : ℝ) + 1 - m := by
    norm_num [Nat.cast_sub hmN']
  rw [hNatSub]
  cases m with
  | zero =>
      simp
  | succ m =>
      have hsum_twice :
          (((Nat.succ m * (Nat.succ m - 1) / 2 : ℕ) : ℝ) * 2) = (Nat.succ m : ℝ) * (m : ℝ) := by
        have hnat :
            (Finset.sum (Finset.range (Nat.succ m)) fun i : ℕ ↦ (i : ℝ)) * 2 =
              (Nat.succ m : ℝ) * (m : ℝ) := by
          simpa using
            congrArg (fun t : ℕ ↦ (t : ℝ)) (Finset.sum_range_id_mul_two (Nat.succ m))
        rw [sumRangeIdCast] at hnat
        simpa using hnat
      have hsum_half :
          (((Nat.succ m * (Nat.succ m - 1) / 2 : ℕ) : ℝ)) = (Nat.succ m : ℝ) * (m : ℝ) / 2 := by
        linarith [hsum_twice]
      field_simp [hN_pos.ne']
      rw [hsum_half]
      norm_num [Nat.cast_add]
      nlinarith

private lemma endpointMeshMin_sum_eq_gridCorrection (n : ℕ) (k : Fin (n + 2)) :
    (1 / (n + 1 : ℝ)) *
        ∑ j : Fin (n + 2), min ((k : ℝ) / (n + 1 : ℝ)) ((j : ℝ) / (n + 1 : ℝ)) =
      ((k : ℝ) / (n + 1 : ℝ)) - (((k : ℝ) / (n + 1 : ℝ)) ^ 2) / 2 +
        ((k : ℝ) / (n + 1 : ℝ)) / (2 * (n + 1 : ℝ)) := by
  let m : ℕ := k.1
  have hm_le : m ≤ n + 1 := Nat.le_of_lt_succ k.2
  -- Proof comment: convert the `Fin` mesh sum to the nat-indexed helper, where the split point
  -- and the arithmetic-series normalization are stable.
  have hsumRange :
      (∑ j : Fin (n + 2), min ((k : ℝ) / (n + 1 : ℝ)) ((j : ℝ) / (n + 1 : ℝ))) =
        Finset.sum (Finset.range (n + 2))
          (fun j ↦ min ((m : ℝ) / (n + 1 : ℝ)) ((j : ℝ) / (n + 1 : ℝ))) := by
    simpa [m] using
      (Fin.sum_univ_eq_sum_range
        (f := fun j : ℕ ↦ min ((m : ℝ) / (n + 1 : ℝ)) ((j : ℝ) / (n + 1 : ℝ)))
        (n + 2))
  rw [hsumRange]
  exact endpointMeshMin_sum_nat_eq_gridCorrection n m hm_le

/-- Helper for Exercise 21.2.1: at a uniform mesh point `k / (n + 1)`, the mixed moment against
the endpoint average approximant differs from the continuum kernel value only by the endpoint-rule
correction `r / (2 (n + 1))`. -/
private lemma brownianEval_mulUnitIntervalAverageRiemannApprox_eq_gridValue
    (hB : IsBrownianMotion μ B) (n : ℕ) (k : Fin (n + 2)) :
    ∫ ω, B (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))) ω *
      brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ =
        ((k : ℝ) / (n + 1 : ℝ)) - (((k : ℝ) / (n + 1 : ℝ)) ^ 2) / 2 +
          ((k : ℝ) / (n + 1 : ℝ)) / (2 * (n + 1 : ℝ)) := by
  have hk_nonneg : 0 ≤ ((k : ℝ) / (n + 1 : ℝ)) := by positivity
  have hk_le_one : ((k : ℝ) / (n + 1 : ℝ)) ≤ 1 := by
    have hk_le : (k : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast (Nat.le_of_lt_succ k.2)
    exact (div_le_one (by positivity : (0 : ℝ) < n + 1)).2 hk_le
  -- Proof comment: the stochastic identity has already been reduced to the deterministic endpoint
  -- mesh sum, so only the finite arithmetic normalization remains here.
  rw [brownianEval_mulUnitIntervalAverageRiemannApprox_eq_meshSum
      (μ := μ) (B := B) (r := (k : ℝ) / (n + 1 : ℝ)) hB hk_nonneg hk_le_one]
  exact endpointMeshMin_sum_eq_gridCorrection n k

/-- Helper for Exercise 21.2.1: the second moment of the endpoint-average approximant is the
deterministic one-sum grid correction. -/
lemma brownianUnitIntervalAverageRiemannApprox_secondMoment_eq_gridSum
    (hB : IsBrownianMotion μ B) (n : ℕ) :
    ∫ ω, (brownianUnitIntervalAverageRiemannApprox (B := B) n ω) ^ (2 : ℕ) ∂μ =
      (1 / (n + 1 : ℝ)) *
        ∑ k : Fin (n + 2),
          (((k : ℝ) / (n + 1 : ℝ)) - (((k : ℝ) / (n + 1 : ℝ)) ^ 2) / 2 +
            ((k : ℝ) / (n + 1 : ℝ)) / (2 * (n + 1 : ℝ))) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let A : Ω → ℝ := brownianUnitIntervalAverageRiemannApprox (B := B) n
  have hExpand :
      (fun ω ↦ A ω ^ (2 : ℕ)) =
        fun ω ↦
          (1 / (n + 1 : ℝ)) *
            ∑ k : Fin (n + 2),
              B (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ))) ω * A ω := by
    funext ω
    simp [A, brownianUnitIntervalAverageRiemannApprox, pow_two, Finset.mul_sum, mul_assoc,
      mul_left_comm, mul_comm]
  rw [hExpand, integral_const_mul, integral_finset_sum]
  · refine congrArg (fun x : ℝ ↦ (1 / (n + 1 : ℝ)) * x) ?_
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simpa [A] using
      brownianEval_mulUnitIntervalAverageRiemannApprox_eq_gridValue (μ := μ) (B := B) hB n k
  · intro k _
    have hBk_mem :
        MemLp (B (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ)))) 2 μ :=
      brownianEval_memLp_two (μ := μ) (X := B) hB
        (Real.toNNReal ((k : ℝ) / (n + 1 : ℝ)))
    have hA_mem :
        MemLp A 2 μ :=
      (brownianUnitIntervalAverageRiemannApprox_hasGaussianLaw (μ := μ) (B := B) hB n).memLp_two
    exact hBk_mem.integrable_mul hA_mem

/-- Helper for Exercise 21.2.1: the endpoint-average approximant second moment simplifies to a
closed rational function of the mesh size. -/
lemma brownianUnitIntervalAverageRiemannApprox_secondMoment_eq_closedForm
    (hB : IsBrownianMotion μ B) (n : ℕ) :
    ∫ ω, (brownianUnitIntervalAverageRiemannApprox (B := B) n ω) ^ (2 : ℕ) ∂μ =
      1 / 3 + 1 / (2 * (n + 1 : ℝ)) + 1 / (6 * (n + 1 : ℝ) ^ (2 : ℕ)) := by
  set N : ℕ := n + 1
  have hgrid :=
    brownianUnitIntervalAverageRiemannApprox_secondMoment_eq_gridSum
      (μ := μ) (B := B) hB n
  have hgridRange :
      ∑ k : Fin (n + 2),
          (((k : ℝ) / (n + 1 : ℝ)) - (((k : ℝ) / (n + 1 : ℝ)) ^ 2) / 2 +
            ((k : ℝ) / (n + 1 : ℝ)) / (2 * (n + 1 : ℝ))) =
        Finset.sum (Finset.range (N + 1))
          (fun k ↦ ((k : ℝ) / N) - (((k : ℝ) / N) ^ 2) / 2 + ((k : ℝ) / N) / (2 * N)) := by
    simpa [N] using
      (Fin.sum_univ_eq_sum_range
        (f := fun k : ℕ ↦ ((k : ℝ) / N) - (((k : ℝ) / N) ^ 2) / 2 + ((k : ℝ) / N) / (2 * N))
        (N + 1))
  have hsumLinear :
      Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ)) = (N : ℝ) * (N + 1) / 2 := by
    -- Proof comment: rewrite the casted arithmetic sum in the `range (N + 1)` spelling used by
    -- the endpoint grid.
    induction N with
    | zero =>
        norm_num
    | succ N hN =>
        rw [Finset.sum_range_succ, hN]
        norm_num [Nat.cast_add]
        ring
  have hsumSquare :
      Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ) ^ (2 : ℕ)) =
        (N : ℝ) * (N + 1) * (2 * N + 1) / 6 := by
    simpa using sumRangeSquareCast N
  have hN_pos : 0 < (N : ℝ) := by positivity
  have hsumLinearDiv :
      Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ) / N) =
        Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ)) / N := by
    rw [Finset.sum_div]
  have hsumSquareDiv :
      Finset.sum (Finset.range (N + 1)) (fun k ↦ ((k : ℝ) / N) ^ 2 / 2) =
        Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ) ^ (2 : ℕ)) / (2 * N ^ (2 : ℕ)) := by
    calc
      Finset.sum (Finset.range (N + 1)) (fun k ↦ ((k : ℝ) / N) ^ 2 / 2)
          = Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ) ^ (2 : ℕ) / (2 * N ^ (2 : ℕ))) := by
              refine Finset.sum_congr rfl fun k hk ↦ ?_
              field_simp [hN_pos.ne']
      _ = Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ) ^ (2 : ℕ)) / (2 * N ^ (2 : ℕ)) := by
            rw [Finset.sum_div]
  have hsumCorrectionDiv :
      Finset.sum (Finset.range (N + 1)) (fun k ↦ ((k : ℝ) / N) / (2 * N)) =
        Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ)) / (2 * N ^ (2 : ℕ)) := by
    calc
      Finset.sum (Finset.range (N + 1)) (fun k ↦ ((k : ℝ) / N) / (2 * N))
          = Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ) / (2 * N ^ (2 : ℕ))) := by
              refine Finset.sum_congr rfl fun k hk ↦ ?_
              field_simp [hN_pos.ne']
      _ = Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ)) / (2 * N ^ (2 : ℕ)) := by
            rw [Finset.sum_div]
  have hsplit :
      Finset.sum (Finset.range (N + 1))
          (fun k ↦ ((k : ℝ) / N) - (((k : ℝ) / N) ^ 2) / 2 + ((k : ℝ) / N) / (2 * N)) =
        Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ)) / N -
          Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ) ^ (2 : ℕ)) / (2 * N ^ (2 : ℕ)) +
          Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ)) / (2 * N ^ (2 : ℕ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsumLinearDiv, hsumSquareDiv,
      hsumCorrectionDiv]
  -- Proof comment: after expanding the grid-correction formula, only the standard `∑ k` and
  -- `∑ k²` identities remain.
  calc
    ∫ ω, (brownianUnitIntervalAverageRiemannApprox (B := B) n ω) ^ (2 : ℕ) ∂μ
        = (1 / (N : ℝ)) *
            ∑ k : Fin (n + 2),
              (((k : ℝ) / (n + 1 : ℝ)) - (((k : ℝ) / (n + 1 : ℝ)) ^ 2) / 2 +
                ((k : ℝ) / (n + 1 : ℝ)) / (2 * (n + 1 : ℝ))) := by
              simpa [N] using hgrid
    _ = (1 / (N : ℝ)) *
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ ((k : ℝ) / N) - (((k : ℝ) / N) ^ 2) / 2 + ((k : ℝ) / N) / (2 * N)) := by
              rw [hgridRange]
    _ = (1 / (N : ℝ)) *
          ((Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ)) / N) -
            (Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ) ^ (2 : ℕ)) / (2 * N ^ (2 : ℕ))) +
            (Finset.sum (Finset.range (N + 1)) (fun k ↦ (k : ℝ)) / (2 * N ^ (2 : ℕ)))) := by
              rw [hsplit]
    _ = (1 / (N : ℝ)) *
          (((N : ℝ) * (N + 1) / 2) / N -
            ((N : ℝ) * (N + 1) * (2 * N + 1) / 6) / (2 * N ^ (2 : ℕ)) +
            ((N : ℝ) * (N + 1) / 2) / (2 * N ^ (2 : ℕ))) := by
              simpa [hsumLinear, hsumSquare]
    _ = 1 / 3 + 1 / (2 * (n + 1 : ℝ)) + 1 / (6 * (n + 1 : ℝ) ^ (2 : ℕ)) := by
          subst N
          have hn_pos : 0 < (n + 1 : ℝ) := by positivity
          field_simp [hn_pos.ne']
          norm_num [Nat.cast_add]
          ring

/-- Helper for Exercise 21.2.1: the endpoint-average approximant variances converge to the exact
average variance `1 / 3`. -/
lemma brownianUnitIntervalAverageRiemannApprox_variance_tendsto
    (hB : IsBrownianMotion μ B) :
    Tendsto
      (fun n : ℕ ↦ Var[brownianUnitIntervalAverageRiemannApprox (B := B) n; μ])
      atTop
      (𝓝 (1 / 3)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let A : ℕ → Ω → ℝ := fun n ↦ brownianUnitIntervalAverageRiemannApprox (B := B) n
  have hVarEq :
      ∀ n, Var[A n; μ] =
        1 / 3 + 1 / (2 * (n + 1 : ℝ)) + 1 / (6 * (n + 1 : ℝ) ^ (2 : ℕ)) := by
    intro n
    have hA_mem : MemLp (A n) 2 μ :=
      (brownianUnitIntervalAverageRiemannApprox_hasGaussianLaw (μ := μ) (B := B) hB n).memLp_two
    -- Proof comment: the endpoint average is centered, so its variance is exactly its second
    -- moment, which has already been reduced to a scalar closed form.
    rw [ProbabilityTheory.variance_of_integral_eq_zero hA_mem.aemeasurable]
    · simpa [A] using
        brownianUnitIntervalAverageRiemannApprox_secondMoment_eq_closedForm
          (μ := μ) (B := B) hB n
    · simpa [A] using
        brownianUnitIntervalAverageRiemannApprox_expectation_eq_zero (μ := μ) (B := B) hB n
  have hnat :
      Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop :=
    by
      have hnatComp :
          Tendsto ((fun m : ℕ ↦ (m : ℝ)) ∘ fun n : ℕ ↦ n + 1) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
      exact hnatComp.congr' <| Filter.Eventually.of_forall fun n ↦ by
        simp [Function.comp, Nat.cast_add]
  have hinv :
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)) atTop (𝓝 0) :=
    by simpa using tendsto_inv_atTop_zero.comp hnat
  have hinvSq :
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹) ^ (2 : ℕ)) atTop (𝓝 0) :=
    by simpa using hinv.pow 2
  have hhalf :
      Tendsto (fun n : ℕ ↦ 1 / (2 * (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      Tendsto.const_mul (1 / 2 : ℝ) hinv
  have hsixth :
      Tendsto (fun n : ℕ ↦ 1 / (6 * (n + 1 : ℝ) ^ (2 : ℕ))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      Tendsto.const_mul (1 / 6 : ℝ) hinvSq
  have hclosed :
      Tendsto
        (fun n : ℕ ↦ 1 / 3 + 1 / (2 * (n + 1 : ℝ)) + 1 / (6 * (n + 1 : ℝ) ^ (2 : ℕ)))
        atTop
        (𝓝 (1 / 3)) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      Tendsto.const_add (1 / 3 : ℝ) (hhalf.add hsixth)
  -- Proof comment: once the closed form is explicit, the limit is a purely scalar `1 / (n + 1)`
  -- decay estimate.
  exact hclosed.congr' <| Filter.Eventually.of_forall fun n ↦ by
    simpa [A] using (hVarEq n).symm

/-- Helper for Exercise 21.2.1: the affine endpoint approximant variance expands into the Brownian
kernel part, the two mixed moments with the average, and the average variance itself. -/
lemma brownianCenteredAffineRiemannApprox_variance_eq_mixedMomentForm
    (hB : IsBrownianMotion μ B) {s t : ℝ}
    (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1) (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1)
    (a b c : ℝ) (n : ℕ) :
    Var[brownianCenteredAffineRiemannApprox (B := B) s t a b c n; μ] =
      a ^ 2 * s + b ^ 2 * t + 2 * a * b * min s t -
        2 * a * c *
          (∫ ω, B (Real.toNNReal s) ω *
            brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ) -
        2 * b * c *
          (∫ ω, B (Real.toNNReal t) ω *
            brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ) +
        c ^ 2 * Var[brownianUnitIntervalAverageRiemannApprox (B := B) n; μ] := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Bs : Ω → ℝ := fun ω ↦ B (Real.toNNReal s) ω
  let Bt : Ω → ℝ := fun ω ↦ B (Real.toNNReal t) ω
  let A : Ω → ℝ := brownianUnitIntervalAverageRiemannApprox (B := B) n
  let L : Ω → ℝ := fun ω ↦ a * Bs ω + b * Bt ω
  have hBs_mem : MemLp Bs 2 μ :=
    brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal s)
  have hBt_mem : MemLp Bt 2 μ :=
    brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal t)
  have hA_mem : MemLp A 2 μ :=
    (brownianUnitIntervalAverageRiemannApprox_hasGaussianLaw (μ := μ) (B := B) hB n).memLp_two
  have hL_mem : MemLp L 2 μ := (hBs_mem.const_mul a).add (hBt_mem.const_mul b)
  have hCovBsA :
      cov[Bs, A; μ] = ∫ ω, Bs ω * A ω ∂μ := by
    -- Proof comment: both factors are centered, so the covariance is the mixed second moment.
    rw [covariance_eq_sub hBs_mem hA_mem,
      brownianEval_expectation_eq_zero (μ := μ) (B := B) hB (Real.toNNReal s),
      brownianUnitIntervalAverageRiemannApprox_expectation_eq_zero (μ := μ) (B := B) hB n,
      zero_mul, sub_zero]
    simp [Bs, A]
  have hCovBtA :
      cov[Bt, A; μ] = ∫ ω, Bt ω * A ω ∂μ := by
    -- Proof comment: the same centeredness reduction applies at time `t`.
    rw [covariance_eq_sub hBt_mem hA_mem,
      brownianEval_expectation_eq_zero (μ := μ) (B := B) hB (Real.toNNReal t),
      brownianUnitIntervalAverageRiemannApprox_expectation_eq_zero (μ := μ) (B := B) hB n,
      zero_mul, sub_zero]
    simp [Bt, A]
  have hVarL :
      Var[L; μ] = a ^ 2 * s + 2 * a * b * min s t + b ^ 2 * t := by
    -- Proof comment: first isolate the two Brownian evaluation terms, then use the Brownian
    -- covariance kernel to evaluate the quadratic form exactly.
    calc
      Var[L; μ]
          = Var[fun ω ↦ a * Bs ω; μ] +
              2 * cov[fun ω ↦ a * Bs ω, fun ω ↦ b * Bt ω; μ] +
                Var[fun ω ↦ b * Bt ω; μ] := by
              simpa [L, Pi.add_apply] using variance_add (hBs_mem.const_mul a) (hBt_mem.const_mul b)
      _ = a ^ 2 * Var[Bs; μ] + 2 * (a * (b * cov[Bs, Bt; μ])) + b ^ 2 * Var[Bt; μ] := by
            rw [variance_const_mul, covariance_const_mul_left, covariance_const_mul_right,
              variance_const_mul]
      _ = a ^ 2 * s + 2 * (a * (b * min s t)) + b ^ 2 * t := by
            rw [brownianEval_variance_eq (μ := μ) (B := B) hB (Real.toNNReal s),
              brownianEval_variance_eq (μ := μ) (B := B) hB (Real.toNNReal t),
              brownianCovariance_eq_min (μ := μ) (B := B) hB (Real.toNNReal s) (Real.toNNReal t)]
            simp [Bs, Bt, Real.toNNReal_of_nonneg hs_nonneg, Real.toNNReal_of_nonneg ht_nonneg]
      _ = a ^ 2 * s + 2 * a * b * min s t + b ^ 2 * t := by ring
  have hCovLA :
      cov[L, A; μ] =
        a * (∫ ω, Bs ω * A ω ∂μ) + b * (∫ ω, Bt ω * A ω ∂μ) := by
    -- Proof comment: bilinearity pushes the covariance with the average onto the two Brownian
    -- evaluation coordinates.
    calc
      cov[L, A; μ]
          = cov[fun ω ↦ a * Bs ω, A; μ] + cov[fun ω ↦ b * Bt ω, A; μ] := by
              simpa [L, Pi.add_apply] using
                covariance_add_left (hBs_mem.const_mul a) (hBt_mem.const_mul b) hA_mem
      _ = a * cov[Bs, A; μ] + b * cov[Bt, A; μ] := by
            rw [covariance_const_mul_left, covariance_const_mul_left]
      _ = a * (∫ ω, Bs ω * A ω ∂μ) + b * (∫ ω, Bt ω * A ω ∂μ) := by
            rw [hCovBsA, hCovBtA]
  -- Proof comment: the affine approximant is `L - c A`, so one application of the variance
  -- subtraction identity reduces the proof to the explicit `L` variance and `L/A` covariance.
  calc
    Var[brownianCenteredAffineRiemannApprox (B := B) s t a b c n; μ]
        = Var[L; μ] - 2 * cov[L, fun ω ↦ c * A ω; μ] + Var[fun ω ↦ c * A ω; μ] := by
            simpa [brownianCenteredAffineRiemannApprox, Bs, Bt, A, L, Pi.sub_apply] using
              variance_sub hL_mem (hA_mem.const_mul c)
    _ = Var[L; μ] - 2 * (c * cov[L, A; μ]) + c ^ 2 * Var[A; μ] := by
          rw [covariance_const_mul_right, variance_const_mul]
    _ = a ^ 2 * s + b ^ 2 * t + 2 * a * b * min s t -
          2 * a * c * (∫ ω, Bs ω * A ω ∂μ) -
          2 * b * c * (∫ ω, Bt ω * A ω ∂μ) +
          c ^ 2 * Var[A; μ] := by
            rw [hVarL, hCovLA]
            ring
    _ = a ^ 2 * s + b ^ 2 * t + 2 * a * b * min s t -
          2 * a * c *
            (∫ ω, B (Real.toNNReal s) ω *
              brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ) -
          2 * b * c *
            (∫ ω, B (Real.toNNReal t) ω *
              brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ) +
          c ^ 2 * Var[brownianUnitIntervalAverageRiemannApprox (B := B) n; μ] := by
            simp [Bs, Bt, A]

/-- Helper for Exercise 21.2.1: the deterministic decomposition of the affine endpoint
approximation variances. -/
private def brownianCenteredAffineVarianceApprox
    (μ : Measure Ω) (B : NNReal → Ω → ℝ) (s t a b c : ℝ) (n : ℕ) : ℝ :=
  (a ^ 2 * s + b ^ 2 * t + 2 * a * b * min s t) +
    ((-2 * a * c) *
        (∫ ω, B (Real.toNNReal s) ω *
          brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ) +
      ((-2 * b * c) *
          (∫ ω, B (Real.toNNReal t) ω *
            brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ) +
        c ^ 2 * Var[brownianUnitIntervalAverageRiemannApprox (B := B) n; μ]))

/-- Helper for Exercise 21.2.1: the limiting centered Brownian-average covariance kernel for the
affine approximants. -/
private def brownianCenteredAffineVarianceLimit (s t a b c : ℝ) : ℝ :=
  a ^ 2 * s + b ^ 2 * t + 2 * a * b * min s t -
    2 * a * c * (s - s ^ 2 / 2) - 2 * b * c * (t - t ^ 2 / 2) + c ^ 2 / 3

/-- Helper for Exercise 21.2.1: the affine endpoint-approximation variances converge to the
explicit centered Brownian-average kernel. -/
lemma brownianCenteredAffineRiemannApprox_variance_tendsto
    (hB : IsBrownianMotion μ B) {s t : ℝ}
    (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1) (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1)
    (a b c : ℝ) :
    Tendsto
      (fun n : ℕ ↦ Var[brownianCenteredAffineRiemannApprox (B := B) s t a b c n; μ])
      atTop
      (𝓝 (brownianCenteredAffineVarianceLimit s t a b c)) := by
  have hRewrite :
      (fun n : ℕ ↦ Var[brownianCenteredAffineRiemannApprox (B := B) s t a b c n; μ]) =
        fun n : ℕ ↦ brownianCenteredAffineVarianceApprox μ B s t a b c n := by
    -- Proof comment: first move every variance term into the stable mixed-moment normal form.
    funext n
    rw [brownianCenteredAffineRiemannApprox_variance_eq_mixedMomentForm
      (μ := μ) (B := B) hB hs_nonneg hs_le_one ht_nonneg ht_le_one a b c n]
    simp [brownianCenteredAffineVarianceApprox]
    ring
  have hsMix :
      Tendsto
        (fun n : ℕ ↦
          (-2 * a * c) *
            (∫ ω, B (Real.toNNReal s) ω *
              brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ))
        atTop
        (𝓝 ((-2 * a * c) * (s - s ^ 2 / 2))) :=
    Tendsto.const_mul (-2 * a * c) <|
      brownianEval_mulUnitIntervalAverageRiemannApprox_tendsto
        (μ := μ) (B := B) hB hs_nonneg hs_le_one
  have htMix :
      Tendsto
        (fun n : ℕ ↦
          (-2 * b * c) *
            (∫ ω, B (Real.toNNReal t) ω *
              brownianUnitIntervalAverageRiemannApprox (B := B) n ω ∂μ))
        atTop
        (𝓝 ((-2 * b * c) * (t - t ^ 2 / 2))) :=
    Tendsto.const_mul (-2 * b * c) <|
      brownianEval_mulUnitIntervalAverageRiemannApprox_tendsto
        (μ := μ) (B := B) hB ht_nonneg ht_le_one
  have hVar :
      Tendsto
        (fun n : ℕ ↦ c ^ 2 * Var[brownianUnitIntervalAverageRiemannApprox (B := B) n; μ])
        atTop
        (𝓝 (c ^ 2 * (1 / 3 : ℝ))) :=
    Tendsto.const_mul (c ^ 2) <|
      brownianUnitIntervalAverageRiemannApprox_variance_tendsto (μ := μ) (B := B) hB
  rw [hRewrite]
  have hLimit :
      brownianCenteredAffineVarianceLimit s t a b c =
        a ^ 2 * s +
          (b ^ 2 * t +
            (2 * a * b * min s t +
              (-(2 * a * c * (s - s ^ 2 / 2)) + (-(2 * b * c * (t - t ^ 2 / 2)) + c ^ 2 * 3⁻¹)))) := by
    unfold brownianCenteredAffineVarianceLimit
    ring
  have hAffineClosed :=
    Tendsto.const_add (a ^ 2 * s + b ^ 2 * t + 2 * a * b * min s t) (hsMix.add (htMix.add hVar))
  rw [hLimit]
  -- Proof comment: the three moving scalar pieces now converge independently, so the affine limit
  -- is a single flat `Tendsto` assembly.
  simpa [brownianCenteredAffineVarianceApprox, add_assoc, add_left_comm, add_comm] using hAffineClosed

/-- Helper for Exercise 21.2.1: every affine functional
`a * B_s + b * B_t - c * ∫₀¹ B_u du` is Gaussian. -/
lemma brownianCenteredAffine_hasGaussianLaw
    (hB : IsBrownianMotion μ B) {s t : ℝ}
    (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1) (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1)
    (a b c : ℝ) :
    HasGaussianLaw
      (fun ω ↦
        a * B (Real.toNNReal s) ω + b * B (Real.toNNReal t) ω -
          c * (∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω))
      μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Xn : ℕ → Ω → ℝ := fun n ω ↦ brownianCenteredAffineRiemannApprox (B := B) s t a b c n ω
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let Ac : Ω → ℝ := fun ω ↦
    ∫ u, brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal u) ω ∂ν
  let Yc : Ω → ℝ := fun ω ↦
    a * B (Real.toNNReal s) ω + b * B (Real.toNNReal t) ω - c * Ac ω
  let Y : Ω → ℝ := fun ω ↦
    a * B (Real.toNNReal s) ω + b * B (Real.toNNReal t) ω -
      c * (∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω)
  let v : ℝ :=
    a ^ 2 * s + b ^ 2 * t + 2 * a * b * min s t -
      2 * a * c * (s - s ^ 2 / 2) - 2 * b * c * (t - t ^ 2 / 2) + c ^ 2 / 3
  have hAc_meas : Measurable Ac := by
    simpa [Ac, ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      (MeasureTheory.measurable_intervalIntegral_of_continuous_paths
        (brownianContinuousVersion_measurable (μ := μ) (B := B) hB)
        (brownianContinuousVersion_continuous (μ := μ) (B := B) hB)
        (show (0 : NNReal) < 1 by norm_num))
  have hYc_meas : Measurable Yc := by
    simpa [Yc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      ((hB.stronglyMeasurable (Real.toNNReal s)).measurable.const_mul a).add
        (((hB.stronglyMeasurable (Real.toNNReal t)).measurable.const_mul b).sub
          (hAc_meas.const_mul c))
  have hAc_original :
      Ac =ᵐ[μ] fun ω ↦ ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω := by
    simpa [Ac, ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      brownianContinuousVersion_average_ae_eq (μ := μ) (B := B) hB
  have hY_eq : Y =ᵐ[μ] Yc := by
    filter_upwards [hAc_original] with ω hω
    simp [Y, Yc, hω]
  have hY_meas : AEMeasurable Y μ := hYc_meas.aemeasurable.congr hY_eq.symm
  have hXn_meas : ∀ n, AEStronglyMeasurable (Xn n) μ := fun n ↦
    ((brownianCenteredAffineRiemannApprox_hasGaussianLaw
      (μ := μ) (B := B) hB s t a b c n).aemeasurable).aestronglyMeasurable
  have hXn_tendsto :
      TendstoInMeasure μ Xn atTop Y := by
    refine tendstoInMeasure_of_tendsto_ae hXn_meas ?_
    simpa [Xn, Y] using
      brownianCenteredAffineRiemannApprox_tendsto_ae (μ := μ) (B := B) hB s t a b c
  have hDist : TendstoInDistribution Xn atTop Y (fun _ ↦ μ) μ :=
    hXn_tendsto.tendstoInDistribution (fun n ↦ (hXn_meas n).aemeasurable)
  have hVarSeq :
      Tendsto (fun n : ℕ ↦ Var[Xn n; μ]) atTop (𝓝 v) := by
    simpa [Xn, v] using
      brownianCenteredAffineRiemannApprox_variance_tendsto
        (μ := μ) (B := B) hB hs_nonneg hs_le_one ht_nonneg ht_le_one a b c
  have hv_nonneg : 0 ≤ v := by
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hVarSeq (fun n ↦ variance_nonneg (Xn n) μ)
  have hLaw_n :
      ∀ n, HasLaw (Xn n) (gaussianReal 0 (Real.toNNReal (Var[Xn n; μ]))) μ := by
    intro n
    have hGaussian :
        HasGaussianLaw (Xn n) μ :=
      brownianCenteredAffineRiemannApprox_hasGaussianLaw (μ := μ) (B := B) hB s t a b c n
    have hMean : ∫ ω, Xn n ω ∂μ = 0 := by
      simpa [Xn] using
        brownianCenteredAffineRiemannApprox_expectation_eq_zero
          (μ := μ) (B := B) hB s t a b c n
    refine ⟨hGaussian.aemeasurable, ?_⟩
    calc
      μ.map (Xn n) = gaussianReal ((μ.map (Xn n))[id]) Var[id; μ.map (Xn n)].toNNReal := by
        simpa using
          (ProbabilityTheory.IsGaussian.eq_gaussianReal
            (μ := μ.map (Xn n)) hGaussian.isGaussian_map)
      _ = gaussianReal (μ[Xn n]) Var[Xn n; μ].toNNReal := by
        congr 1
        · simpa using
            (integral_map hGaussian.aemeasurable aestronglyMeasurable_id :
              ∫ x : ℝ, id x ∂Measure.map (Xn n) μ = ∫ ω, id (Xn n ω) ∂μ)
        · exact
            congrArg Real.toNNReal <|
              (by
                simpa [Function.comp] using
                  (variance_map aemeasurable_id hGaussian.aemeasurable :
                    Var[id; μ.map (Xn n)] = Var[id ∘ Xn n; μ]))
      _ = gaussianReal 0 (Real.toNNReal (Var[Xn n; μ])) := by
        simp [hMean]
  let μn : ℕ → ProbabilityMeasure ℝ := fun n ↦
    ⟨μ.map (Xn n),
      Measure.isProbabilityMeasure_map
        ((brownianCenteredAffineRiemannApprox_hasGaussianLaw
          (μ := μ) (B := B) hB s t a b c n).aemeasurable)⟩
  have hLawGauss :
      Tendsto
        (fun n ↦ μn n)
        atTop
        (𝓝 (⟨gaussianReal 0 (Real.toNNReal v), inferInstance⟩ : ProbabilityMeasure ℝ)) := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 ?_
    intro u
    let g : ℝ → ℂ := fun x ↦ Complex.exp (-x * u ^ 2 / 2)
    have hg : Continuous g := by
      fun_prop
    have hChar :
        (fun n ↦ charFun (((μn n : ProbabilityMeasure ℝ) : Measure ℝ)) u) =
          fun n ↦ g (Var[Xn n; μ]) := by
      funext n
      calc
        charFun (((μn n : ProbabilityMeasure ℝ) : Measure ℝ)) u
            = charFun (gaussianReal 0 (Real.toNNReal (Var[Xn n; μ]))) u := by
                simpa [μn] using congrArg (fun m : Measure ℝ => charFun m u) (hLaw_n n).map_eq
        _ = g (Var[Xn n; μ]) := by
              rw [charFun_gaussianReal]
              simp [g, Real.toNNReal_of_nonneg (variance_nonneg (Xn n) μ), neg_div, mul_assoc,
                mul_left_comm, mul_comm]
    have hBase : Tendsto (fun n ↦ g (Var[Xn n; μ])) atTop (𝓝 (g v)) :=
      hg.continuousAt.tendsto.comp hVarSeq
    rw [hChar]
    have hGaussChar : charFun (gaussianReal 0 (Real.toNNReal v)) u = g v := by
      rw [charFun_gaussianReal]
      simp [g, Real.toNNReal_of_nonneg hv_nonneg, neg_div, mul_assoc, mul_left_comm, mul_comm]
    simpa [hGaussChar] using hBase
  have hMapEq :
      μ.map Y = gaussianReal 0 (Real.toNNReal v) := by
    apply Measure.ext_of_charFun
    funext u
    have hMapChar :
        Tendsto
          (fun n ↦ charFun (((μn n : ProbabilityMeasure ℝ) : Measure ℝ)) u)
          atTop
          (𝓝 (charFun (μ.map Y) u)) := by
      simpa [μn] using
        (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hDist.tendsto) u
    have hGaussChar :
        Tendsto
          (fun n ↦ charFun (((μn n : ProbabilityMeasure ℝ) : Measure ℝ)) u)
          atTop
          (𝓝 (charFun (gaussianReal 0 (Real.toNNReal v)) u)) := by
      simpa using
        (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hLawGauss) u
    exact tendsto_nhds_unique hMapChar hGaussChar
  exact ⟨by rw [hMapEq]; infer_instance⟩

/-- Helper for Exercise 21.2.1: a standard Gaussian variable has fourth moment `3`. -/
lemma gaussianReal_fourthMoment_eq_three {Y : Ω → ℝ}
    (hY : HasLaw Y (gaussianReal 0 1) μ) :
    ∫ ω, Y ω ^ (4 : ℕ) ∂μ = 3 := by
  letI : IsProbabilityMeasure (μ.map Y) := by
    rw [hY.map_eq]
    infer_instance
  letI : IsProbabilityMeasure μ := μ.isProbabilityMeasure_of_map Y
  have hStdId : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    { aemeasurable := measurable_id'.aemeasurable
      map_eq := by simp }
  have hStdFourth :
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 1 = 3 := by
    -- Proof comment: the standard Gaussian fourth moment is the even-moment formula at `k = 2`.
    have hMoment :=
      (gaussianReal_even_moments_eq_factorial_ratio
        (P' := gaussianReal 0 1) (Y := id) hStdId 2)
    norm_num at hMoment
    exact hMoment
  -- Proof comment: transport the quartic moment of `Y` to the canonical Gaussian owner measure.
  exact
    (hY.integral_comp
      (f := fun x : ℝ ↦ x ^ (4 : ℕ))
      ((continuous_pow 4).aestronglyMeasurable)).trans hStdFourth

/-- Helper for Exercise 21.2.1: a centered Gaussian random variable has fourth moment
`3 * Var[Y]^2`. -/
lemma centeredGaussianFourthMoment_eq_three_mul_variance_sq
    {Y : Ω → ℝ} (hY : HasGaussianLaw Y μ) (hY_mean : ∫ ω, Y ω ∂μ = 0) :
    ∫ ω, Y ω ^ (4 : ℕ) ∂μ = 3 * Var[Y; μ] ^ (2 : ℕ) := by
  letI : IsProbabilityMeasure μ := hY.isProbabilityMeasure
  let v : NNReal := Var[Y; μ].toNNReal
  have hLaw :
      HasLaw Y (gaussianReal (∫ ω, Y ω ∂μ) v) μ := by
    refine ⟨hY.aemeasurable, ?_⟩
    calc
      μ.map Y = gaussianReal ((μ.map Y)[id]) Var[id; μ.map Y].toNNReal := by
        exact ProbabilityTheory.IsGaussian.eq_gaussianReal (μ := μ.map Y) hY.isGaussian_map
      _ = gaussianReal (∫ ω, Y ω ∂μ) v := by
        -- Proof comment: rewrite the Gaussian owner parameters back in terms of the original
        -- random variable.
        congr 1
        · simpa using
            (integral_map hY.aemeasurable measurable_id'.aestronglyMeasurable :
              ∫ x : ℝ, id x ∂Measure.map Y μ = ∫ ω, id (Y ω) ∂μ)
        · simpa [v] using
            congrArg Real.toNNReal
              (variance_map measurable_id'.aemeasurable hY.aemeasurable :
                Var[id; μ.map Y] = Var[id ∘ Y; μ])
  have hLaw0 :
      HasLaw Y (gaussianReal 0 v) μ := by
    refine ⟨hY.aemeasurable, ?_⟩
    -- Proof comment: the centered hypothesis identifies the Gaussian mean parameter with `0`.
    simpa [v, hY_mean] using hLaw.map_eq
  let c : ℝ := Real.sqrt (v : ℝ)
  have hStdId : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    { aemeasurable := measurable_id'.aemeasurable
      map_eq := by simp }
  have hStdFourth :
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 1 = 3 := by
    -- Proof comment: reuse the standard Gaussian quartic moment before scaling.
    simpa using gaussianReal_fourthMoment_eq_three (μ := gaussianReal 0 1) hStdId
  have hScaleLaw :
      HasLaw (fun x : ℝ ↦ c * x) (gaussianReal 0 v) (gaussianReal 0 1) := by
    -- Proof comment: `N(0, v)` is the image of the standard Gaussian under multiplication by
    -- `sqrt v`.
    simpa [c, sq_abs, Real.sq_sqrt] using
      (gaussianReal_const_mul
        (P := gaussianReal 0 1) (X := id) (μ := (0 : ℝ)) (v := (1 : NNReal)) hStdId c)
  have hFourthBase :
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 v = 3 * ((v : ℝ) ^ (2 : ℕ)) := by
    calc
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 v
          = ∫ x : ℝ, (c * x) ^ (4 : ℕ) ∂gaussianReal 0 1 := by
              symm
              simpa [Function.comp] using
                (hScaleLaw.integral_comp
                  (f := fun x : ℝ ↦ x ^ (4 : ℕ))
                  ((continuous_pow 4).aestronglyMeasurable))
      _ = ∫ x : ℝ, c ^ (4 : ℕ) * x ^ (4 : ℕ) ∂gaussianReal 0 1 := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [mul_pow]
      _ = c ^ (4 : ℕ) * ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 1 := by
            rw [integral_const_mul]
      _ = c ^ (4 : ℕ) * 3 := by
            rw [hStdFourth]
      _ = 3 * ((v : ℝ) ^ (2 : ℕ)) := by
            have hv_nonneg : 0 ≤ (v : ℝ) := by
              exact_mod_cast v.2
            have hsq : c ^ (2 : ℕ) = (v : ℝ) := by
              simp [c, Real.sq_sqrt, hv_nonneg]
            have hpow : c ^ (4 : ℕ) = (v : ℝ) ^ (2 : ℕ) := by
              rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
            rw [hpow, mul_comm]
  calc
    ∫ ω, Y ω ^ (4 : ℕ) ∂μ = 3 * ((v : ℝ) ^ (2 : ℕ)) := by
      -- Proof comment: move the quartic moment to the Gaussian owner side and evaluate it there.
      exact
        ((hLaw0.integral_comp
          (f := fun x : ℝ ↦ x ^ (4 : ℕ))
          ((continuous_pow 4).aestronglyMeasurable)).trans hFourthBase)
    _ = 3 * Var[Y; μ] ^ (2 : ℕ) := by
          have hv : (v : ℝ) = Var[Y; μ] := by
            simp [v, variance_nonneg Y μ]
          rw [hv]

/-- Helper for Exercise 21.2.1: centered Gaussian variables satisfy
`cov[Y², Z²] = 2 * cov[Y, Z]^2` once the sum and difference are Gaussian as well. -/
lemma centeredGaussianSquareCovariance_eq_two_mul_covariance_sq_of_add_sub
    {Y Z : Ω → ℝ} (hY : HasGaussianLaw Y μ) (hZ : HasGaussianLaw Z μ)
    (hAdd : HasGaussianLaw (fun ω ↦ Y ω + Z ω) μ)
    (hSub : HasGaussianLaw (fun ω ↦ Y ω - Z ω) μ)
    (hY_mean : ∫ ω, Y ω ∂μ = 0) (hZ_mean : ∫ ω, Z ω ∂μ = 0) :
    cov[(fun ω ↦ Y ω ^ 2), (fun ω ↦ Z ω ^ 2); μ] = 2 * cov[Y, Z; μ] ^ (2 : ℕ) := by
  letI : IsProbabilityMeasure μ := hY.isProbabilityMeasure
  have hY_mem_two : MemLp Y 2 μ := hY.memLp_two
  have hZ_mem_two : MemLp Z 2 μ := hZ.memLp_two
  have hY_mem_four : MemLp Y 4 μ := by simpa using hY.memLp (p := 4) (by norm_num)
  have hZ_mem_four : MemLp Z 4 μ := by simpa using hZ.memLp (p := 4) (by norm_num)
  have hAdd_mem_four : MemLp (fun ω ↦ Y ω + Z ω) 4 μ := by
    simpa using hAdd.memLp (p := 4) (by norm_num)
  have hSub_mem_four : MemLp (fun ω ↦ Y ω - Z ω) 4 μ := by
    simpa using hSub.memLp (p := 4) (by norm_num)
  have hFourthIntegrable :
      ∀ {W : Ω → ℝ}, MemLp W 4 μ → Integrable (fun ω ↦ W ω ^ (4 : ℕ)) μ := by
    intro W hW
    have hInt : Integrable (fun ω ↦ |W ω| ^ (4 : ℕ)) μ := by
      simpa [Real.norm_eq_abs] using hW.integrable_norm_pow (p := 4)
    refine hInt.congr ?_
    filter_upwards with ω
    calc
      |W ω| ^ (4 : ℕ) = (|W ω| ^ (2 : ℕ)) ^ (2 : ℕ) := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = (W ω ^ (2 : ℕ)) ^ (2 : ℕ) := by
            congr 1
            simpa [pow_two] using abs_sq (W ω)
      _ = W ω ^ (4 : ℕ) := by
            symm
            rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  have hSquareMemLpTwo :
      ∀ {W : Ω → ℝ}, HasGaussianLaw W μ →
        MemLp (fun ω ↦ W ω ^ (2 : ℕ)) 2 μ := by
    intro W hW
    have hW_mem_four : MemLp W 4 μ := by simpa using hW.memLp (p := 4) (by norm_num)
    refine (memLp_two_iff_integrable_sq (hW.aemeasurable.aestronglyMeasurable.pow 2)).2 ?_
    have hInt : Integrable (fun ω ↦ |W ω| ^ (4 : ℕ)) μ := by
      simpa [Real.norm_eq_abs] using hW_mem_four.integrable_norm_pow (p := 4)
    refine hInt.congr ?_
    filter_upwards with ω
    calc
      |W ω| ^ (4 : ℕ) = (|W ω| ^ (2 : ℕ)) ^ (2 : ℕ) := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = (W ω ^ (2 : ℕ)) ^ (2 : ℕ) := by
            congr 1
            simpa [pow_two] using abs_sq (W ω)
      _ = ((fun ω ↦ W ω ^ (2 : ℕ)) ω) ^ (2 : ℕ) := by rfl
  have hYsq_mem : MemLp (fun ω ↦ Y ω ^ (2 : ℕ)) 2 μ := hSquareMemLpTwo hY
  have hZsq_mem : MemLp (fun ω ↦ Z ω ^ (2 : ℕ)) 2 μ := hSquareMemLpTwo hZ
  have hYZsq_int : Integrable (fun ω ↦ Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ)) μ :=
    hYsq_mem.integrable_mul hZsq_mem
  have hY_fourth :
      ∫ ω, Y ω ^ (4 : ℕ) ∂μ = 3 * Var[Y; μ] ^ (2 : ℕ) :=
    centeredGaussianFourthMoment_eq_three_mul_variance_sq (μ := μ) hY hY_mean
  have hZ_fourth :
      ∫ ω, Z ω ^ (4 : ℕ) ∂μ = 3 * Var[Z; μ] ^ (2 : ℕ) :=
    centeredGaussianFourthMoment_eq_three_mul_variance_sq (μ := μ) hZ hZ_mean
  have hAdd_mean : ∫ ω, (Y ω + Z ω) ∂μ = 0 := by
    rw [integral_add (hY_mem_two.integrable (by norm_num)) (hZ_mem_two.integrable (by norm_num))]
    simp [hY_mean, hZ_mean]
  have hSub_mean : ∫ ω, (Y ω - Z ω) ∂μ = 0 := by
    rw [integral_sub (hY_mem_two.integrable (by norm_num)) (hZ_mem_two.integrable (by norm_num))]
    simp [hY_mean, hZ_mean]
  have hAdd_fourth :
      ∫ ω, (Y ω + Z ω) ^ (4 : ℕ) ∂μ =
        3 * Var[fun ω ↦ Y ω + Z ω; μ] ^ (2 : ℕ) :=
    centeredGaussianFourthMoment_eq_three_mul_variance_sq (μ := μ) hAdd hAdd_mean
  have hSub_fourth :
      ∫ ω, (Y ω - Z ω) ^ (4 : ℕ) ∂μ =
        3 * Var[fun ω ↦ Y ω - Z ω; μ] ^ (2 : ℕ) :=
    centeredGaussianFourthMoment_eq_three_mul_variance_sq (μ := μ) hSub hSub_mean
  have hSecondY : ∫ ω, Y ω ^ (2 : ℕ) ∂μ = Var[Y; μ] := by
    rw [← ProbabilityTheory.variance_of_integral_eq_zero hY.aemeasurable hY_mean]
  have hSecondZ : ∫ ω, Z ω ^ (2 : ℕ) ∂μ = Var[Z; μ] := by
    rw [← ProbabilityTheory.variance_of_integral_eq_zero hZ.aemeasurable hZ_mean]
  have hMixedFourth :
      ∫ ω, Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ) ∂μ =
        Var[Y; μ] * Var[Z; μ] + 2 * cov[Y, Z; μ] ^ (2 : ℕ) := by
    have hPoly :
        (fun ω ↦ (Y ω + Z ω) ^ (4 : ℕ) + (Y ω - Z ω) ^ (4 : ℕ)) =
          fun ω ↦
            2 * Y ω ^ (4 : ℕ) + 12 * (Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ)) + 2 * Z ω ^ (4 : ℕ) := by
      funext ω
      ring
    have hPolyInt :
        ∫ ω, ((Y ω + Z ω) ^ (4 : ℕ) + (Y ω - Z ω) ^ (4 : ℕ)) ∂μ =
          ∫ ω, (2 * Y ω ^ (4 : ℕ) + 12 * (Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ)) +
            2 * Z ω ^ (4 : ℕ)) ∂μ := by
      refine integral_congr_ae ?_
      exact Filter.Eventually.of_forall <| congrFun hPoly
    have hVarAdd :
        Var[fun ω ↦ Y ω + Z ω; μ] = Var[Y; μ] + 2 * cov[Y, Z; μ] + Var[Z; μ] := by
      simpa using variance_add hY_mem_two hZ_mem_two
    have hVarSub :
        Var[fun ω ↦ Y ω - Z ω; μ] = Var[Y; μ] - 2 * cov[Y, Z; μ] + Var[Z; μ] := by
      simpa using variance_sub hY_mem_two hZ_mem_two
    have hEq :
        3 * Var[fun ω ↦ Y ω + Z ω; μ] ^ (2 : ℕ) +
            3 * Var[fun ω ↦ Y ω - Z ω; μ] ^ (2 : ℕ) =
          2 * (3 * Var[Y; μ] ^ (2 : ℕ)) +
            12 * (∫ ω, Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ) ∂μ) +
            2 * (3 * Var[Z; μ] ^ (2 : ℕ)) := by
      have hPolySplit₁ :
          ∫ ω, 2 * Y ω ^ (4 : ℕ) + 12 * (Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ)) +
              2 * Z ω ^ (4 : ℕ) ∂μ =
            ∫ ω, 2 * Y ω ^ (4 : ℕ) ∂μ +
              ∫ ω, 12 * (Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ)) + 2 * Z ω ^ (4 : ℕ) ∂μ := by
        simpa [add_assoc] using
          (integral_add
            (f := fun ω ↦ 2 * Y ω ^ (4 : ℕ))
            (g := fun ω ↦ 12 * (Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ)) + 2 * Z ω ^ (4 : ℕ))
            ((hFourthIntegrable hY_mem_four).const_mul 2)
            ((hYZsq_int.const_mul 12).add ((hFourthIntegrable hZ_mem_four).const_mul 2)))
      have hPolySplit₂ :
          ∫ ω, 12 * (Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ)) + 2 * Z ω ^ (4 : ℕ) ∂μ =
            ∫ ω, 12 * (Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ)) ∂μ +
              ∫ ω, 2 * Z ω ^ (4 : ℕ) ∂μ := by
        exact
          integral_add
            (f := fun ω ↦ 12 * (Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ)))
            (g := fun ω ↦ 2 * Z ω ^ (4 : ℕ))
            (hYZsq_int.const_mul 12)
            ((hFourthIntegrable hZ_mem_four).const_mul 2)
      calc
        3 * Var[fun ω ↦ Y ω + Z ω; μ] ^ (2 : ℕ) +
            3 * Var[fun ω ↦ Y ω - Z ω; μ] ^ (2 : ℕ)
            = ∫ ω, (Y ω + Z ω) ^ (4 : ℕ) ∂μ + ∫ ω, (Y ω - Z ω) ^ (4 : ℕ) ∂μ := by
                rw [hAdd_fourth, hSub_fourth]
        _ = ∫ ω, ((Y ω + Z ω) ^ (4 : ℕ) + (Y ω - Z ω) ^ (4 : ℕ)) ∂μ := by
              rw [← integral_add (hFourthIntegrable hAdd_mem_four) (hFourthIntegrable hSub_mem_four)]
        _ = ∫ ω,
              (2 * Y ω ^ (4 : ℕ) + 12 * (Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ)) +
                2 * Z ω ^ (4 : ℕ)) ∂μ := hPolyInt
        _ = 2 * (3 * Var[Y; μ] ^ (2 : ℕ)) +
              12 * (∫ ω, Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ) ∂μ) +
              2 * (3 * Var[Z; μ] ^ (2 : ℕ)) := by
                rw [hPolySplit₁, hPolySplit₂]
                rw [integral_const_mul, integral_const_mul, integral_const_mul, hY_fourth, hZ_fourth]
                ring
    rw [hVarAdd, hVarSub] at hEq
    nlinarith
  rw [covariance_eq_sub hYsq_mem hZsq_mem, hSecondY, hSecondZ]
  rw [show (∫ ω, ((fun ω ↦ Y ω ^ (2 : ℕ)) * fun ω ↦ Z ω ^ (2 : ℕ)) ω ∂μ) =
      ∫ ω, Y ω ^ (2 : ℕ) * Z ω ^ (2 : ℕ) ∂μ by
      rfl]
  rw [hMixedFourth]
  ring

/-- Helper for Exercise 21.2.1: for fixed `s ∈ [0,1]`, the inner kernel-square integral is an
explicit quartic polynomial in `s`. -/
private lemma centeredAverageKernelSquareIntegral_inner {s : ℝ}
    (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1) :
    ∫ t in (0 : ℝ)..1,
      (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2 =
        -(1 / 3 : ℝ) * s ^ 4 + (2 / 3 : ℝ) * s ^ 3 - (1 / 3 : ℝ) * s ^ 2 + 1 / 45 := by
  have hmin : Continuous fun t : ℝ ↦ min s t := continuous_const.min continuous_id
  have hbase :
      Continuous fun t : ℝ ↦ (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) := by
    -- Proof comment: the kernel is piecewise polynomial, hence continuous, so the interval split
    -- at `t = s` is legitimate.
    continuity
  have hcont :
      Continuous fun t : ℝ ↦
        (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2 :=
    hbase.pow 2
  have hsplit :
      (∫ t in (0 : ℝ)..s,
          (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2) +
        ∫ t in s..1,
          (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2 =
      ∫ t in (0 : ℝ)..1,
        (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2 := by
    -- Proof comment: split the inner integral at the threshold where `min s t` changes shape.
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable 0 s)
        (hcont.intervalIntegrable s 1))
  have hleft :
      ∫ t in (0 : ℝ)..s,
        (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2 =
          (7 / 15 : ℝ) * s ^ 5 - (4 / 3 : ℝ) * s ^ 4 + (13 / 9 : ℝ) * s ^ 3 -
            (2 / 3 : ℝ) * s ^ 2 + (1 / 9 : ℝ) * s := by
    let A : ℝ := s ^ 2 / 2 - s + 1 / 3
    have hrewrite :
        ∫ t in (0 : ℝ)..s,
          (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2 =
        ∫ t in (0 : ℝ)..s, (A ^ 2 + (A * t ^ 2 + (1 / 4 : ℝ) * t ^ 4)) := by
      -- Proof comment: on `(0, s]`, the kernel simplifies to a quadratic polynomial in `t`.
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with t ht
      have ht' : t ∈ Set.Ioc (0 : ℝ) s := by
        simpa [Set.uIoc_of_le hs_nonneg] using ht
      have hmin' : min s t = t := min_eq_right ht'.2
      simp [A, hmin']
      ring
    rw [hrewrite]
    have hAInt : IntervalIntegrable (fun _ : ℝ ↦ (A ^ 2 : ℝ)) volume 0 s := by
      simp
    have hA2Int : IntervalIntegrable (fun t : ℝ ↦ A * t ^ 2) volume 0 s := by
      simp [A]
    have hA4Int : IntervalIntegrable (fun t : ℝ ↦ (1 / 4 : ℝ) * t ^ 4) volume 0 s := by
      simp
    rw [intervalIntegral.integral_add hAInt (hA2Int.add hA4Int)]
    rw [intervalIntegral.integral_add hA2Int hA4Int]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    norm_num [A, integral_pow]
    ring
  have hright :
      ∫ t in s..1,
        (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2 =
          -(7 / 15 : ℝ) * s ^ 5 + s ^ 4 - (7 / 9 : ℝ) * s ^ 3 + (1 / 3 : ℝ) * s ^ 2 -
            (1 / 9 : ℝ) * s + 1 / 45 := by
    let A : ℝ := s ^ 2 / 2 + 1 / 3
    have hrewrite :
        ∫ t in s..1,
          (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2 =
        ∫ t in s..1,
          (A ^ 2 + (-(2 * A * t) + (((A + 1) * t ^ 2) + (-(t ^ 3) + ((1 / 4 : ℝ) * t ^ 4))))) := by
      -- Proof comment: on `[s, 1]`, the same kernel becomes a different polynomial in `t`.
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with t ht
      have ht' : t ∈ Set.Ioc s 1 := by
        simpa [Set.uIoc_of_le hs_le_one] using ht
      have hmin' : min s t = s := min_eq_left (le_of_lt ht'.1)
      simp [A, hmin']
      ring
    rw [hrewrite]
    have hAInt : IntervalIntegrable (fun _ : ℝ ↦ (A ^ 2 : ℝ)) volume s 1 := by
      simp
    have hA1Int : IntervalIntegrable (fun t : ℝ ↦ -(2 * A * t)) volume s 1 := by
      simpa [neg_mul, mul_assoc] using
        ((continuous_id.intervalIntegrable s 1).const_mul (2 * A)).neg
    have hA2Int : IntervalIntegrable (fun t : ℝ ↦ (A + 1) * t ^ 2) volume s 1 := by
      simp [A]
    have hA3Int : IntervalIntegrable (fun t : ℝ ↦ -(t ^ 3)) volume s 1 := by
      simpa using ((continuous_id.pow 3).intervalIntegrable s 1).neg
    have hA4Int : IntervalIntegrable (fun t : ℝ ↦ (1 / 4 : ℝ) * t ^ 4) volume s 1 := by
      simp
    rw [intervalIntegral.integral_add hAInt (hA1Int.add (hA2Int.add (hA3Int.add hA4Int)))]
    rw [intervalIntegral.integral_add hA1Int (hA2Int.add (hA3Int.add hA4Int))]
    rw [intervalIntegral.integral_add hA2Int (hA3Int.add hA4Int)]
    rw [intervalIntegral.integral_add hA3Int hA4Int]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
    norm_num [A, integral_pow]
    ring
  -- Proof comment: add the two explicit polynomial pieces and simplify the resulting quartic.
  rw [← hsplit, hleft, hright]
  ring

/-- Helper for Exercise 21.2.1: the square of the centered covariance kernel integrates to
`1 / 90` over the unit square. -/
lemma centeredAverageKernelSquareIntegral_eq_one_over_ninety :
    ∫ s in (0 : ℝ)..1,
      ∫ t in (0 : ℝ)..1,
        (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2 = 1 / 90 := by
  -- Proof comment: rewrite the inner integral by the explicit quartic formula from the previous
  -- helper, then the outer integral is again a deterministic polynomial computation.
  calc
    ∫ s in (0 : ℝ)..1,
        ∫ t in (0 : ℝ)..1,
          (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2
        =
        ∫ s in (0 : ℝ)..1,
          (-(1 / 3 : ℝ) * s ^ 4 + (2 / 3 : ℝ) * s ^ 3 - (1 / 3 : ℝ) * s ^ 2 + 1 / 45) := by
            exact intervalIntegral.integral_congr_ae <|
              Filter.Eventually.of_forall fun s hs ↦ by
                have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := by
                  simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hs
                simpa using
                  centeredAverageKernelSquareIntegral_inner (le_of_lt hs'.1) hs'.2
    _ = 1 / 90 := by
          have hpoly :
              (fun s : ℝ ↦
                -(1 / 3 : ℝ) * s ^ 4 + (2 / 3 : ℝ) * s ^ 3 - (1 / 3 : ℝ) * s ^ 2 + 1 / 45) =
                fun s : ℝ ↦
                  (-((1 / 3 : ℝ) * s ^ 4)) +
                    (((2 / 3 : ℝ) * s ^ 3) + ((-((1 / 3 : ℝ) * s ^ 2)) + (1 / 45 : ℝ))) := by
            funext s
            ring
          rw [hpoly]
          have h4 : IntervalIntegrable (fun s : ℝ ↦ -((1 / 3 : ℝ) * s ^ 4)) volume 0 1 := by
            simpa using (((continuous_id.pow 4).intervalIntegrable 0 1).const_mul (1 / 3 : ℝ)).neg
          have h3 : IntervalIntegrable (fun s : ℝ ↦ (2 / 3 : ℝ) * s ^ 3) volume 0 1 := by
            simp
          have h2 : IntervalIntegrable (fun s : ℝ ↦ -((1 / 3 : ℝ) * s ^ 2)) volume 0 1 := by
            simpa using (((continuous_id.pow 2).intervalIntegrable 0 1).const_mul (1 / 3 : ℝ)).neg
          have h0 : IntervalIntegrable (fun _ : ℝ ↦ (1 / 45 : ℝ)) volume 0 1 := by
            simp
          rw [intervalIntegral.integral_add h4 (h3.add (h2.add h0))]
          rw [intervalIntegral.integral_add h3 (h2.add h0)]
          rw [intervalIntegral.integral_add h2 h0]
          rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_neg,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
          norm_num [integral_pow]

/-- Helper for Exercise 21.2.1: the original unit-interval Brownian average belongs to `L²`. -/
lemma brownianUnitIntervalAverage_memLp_two_original (hB : IsBrownianMotion μ B) :
    MemLp (fun ω ↦ ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) 2 μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let Ac : Ω → ℝ := fun ω ↦
    ∫ s, brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s) ω ∂ν
  have hAc_mem : MemLp Ac 2 μ := by
    -- Proof comment: the patched average already has the required `L²` estimate.
    simpa [Ac, ν] using
      brownianContinuousVersion_unitIntervalAverage_memLp_two (μ := μ) (B := B) hB
  have hAc_original :
      Ac =ᵐ[μ] fun ω ↦ ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω := by
    -- Proof comment: the patched and original averages agree almost surely on the unit interval.
    simpa [Ac, ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      brownianContinuousVersion_average_ae_eq (μ := μ) (B := B) hB
  -- Proof comment: `L²` is invariant under almost-everywhere replacement of the random variable.
  refine hAc_mem.congr_norm ?_ ?_
  · exact hAc_mem.aestronglyMeasurable.congr hAc_original
  · filter_upwards [hAc_original] with ω hω
    simp [hω]

-- Proof sketch: specialize the generic centered-Gaussian square-covariance identity to the
-- centered Brownian-average field `X_t = B_t - ∫₀¹ B_u du`, using the explicit covariance kernel
-- already computed above.
/-- Helper for Exercise 21.2.1: the square covariance of the centered Brownian-average field is
`2 * K(s,t)^2` on `[0,1]^2`. -/
lemma brownianCenteredSquareCovariance_eq_two_mul_kernel_sq
    (hB : IsBrownianMotion μ B) {s t : ℝ}
    (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1) (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) :
    cov[
      (fun ω ↦
        (B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ^ (2 : ℕ)),
      (fun ω ↦
        (B (Real.toNNReal t) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ^ (2 : ℕ)); μ] =
      2 * (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3) ^ (2 : ℕ) := by
  let hY :
      HasGaussianLaw
        (fun ω ↦ B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) μ := by
    simpa [one_mul, zero_mul, zero_add] using
      brownianCenteredAffine_hasGaussianLaw (μ := μ) (B := B) hB
        hs_nonneg hs_le_one hs_nonneg hs_le_one 1 0 1
  let hZ :
      HasGaussianLaw
        (fun ω ↦ B (Real.toNNReal t) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) μ := by
    simpa [one_mul, zero_mul, zero_add] using
      brownianCenteredAffine_hasGaussianLaw (μ := μ) (B := B) hB
        ht_nonneg ht_le_one ht_nonneg ht_le_one 1 0 1
  let hAdd :
      HasGaussianLaw
        (fun ω ↦
          B (Real.toNNReal s) ω + B (Real.toNNReal t) ω -
            2 * (∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω))
        μ := by
    simpa [two_mul, one_mul, zero_mul, zero_add, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm, mul_assoc, mul_left_comm, mul_comm] using
      brownianCenteredAffine_hasGaussianLaw (μ := μ) (B := B) hB
        hs_nonneg hs_le_one ht_nonneg ht_le_one 1 1 2
  let hSub :
      HasGaussianLaw
        (fun ω ↦ B (Real.toNNReal s) ω - B (Real.toNNReal t) ω)
        μ := by
    simpa [one_mul, zero_mul, zero_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      brownianCenteredAffine_hasGaussianLaw (μ := μ) (B := B) hB
        hs_nonneg hs_le_one ht_nonneg ht_le_one 1 (-1) 0
  have hY_mean :
      ∫ ω, (B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ∂μ = 0 :=
    by
      letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
      have hAverage_mem :
          MemLp (fun ω ↦ ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) 2 μ :=
        brownianUnitIntervalAverage_memLp_two_original (μ := μ) (B := B) hB
      rw [integral_sub]
      · rw [brownianEval_expectation_eq_zero (μ := μ) (B := B) hB (Real.toNNReal s),
          brownianUnitIntervalAverage_expectation (μ := μ) (B := B) hB]
        ring
      · exact (brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal s)).integrable
          (by norm_num)
      · exact hAverage_mem.integrable (by norm_num)
  have hZ_mean :
      ∫ ω, (B (Real.toNNReal t) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ∂μ = 0 :=
    by
      letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
      have hAverage_mem :
          MemLp (fun ω ↦ ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) 2 μ :=
        brownianUnitIntervalAverage_memLp_two_original (μ := μ) (B := B) hB
      rw [integral_sub]
      · rw [brownianEval_expectation_eq_zero (μ := μ) (B := B) hB (Real.toNNReal t),
          brownianUnitIntervalAverage_expectation (μ := μ) (B := B) hB]
        ring
      · exact (brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal t)).integrable
          (by norm_num)
      · exact hAverage_mem.integrable (by norm_num)
  have hCov :
      cov[
        (fun ω ↦ B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω),
        (fun ω ↦ B (Real.toNNReal t) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω); μ] =
          min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 :=
    brownianCenteredCovarianceKernel_eq (μ := μ) (B := B) hB
      hs_nonneg hs_le_one ht_nonneg ht_le_one
  have hAdd' :
      HasGaussianLaw
        (fun ω ↦
          (B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) +
            (B (Real.toNNReal t) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω))
        μ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, two_mul] using hAdd
  have hSub' :
      HasGaussianLaw
        (fun ω ↦
          (B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) -
            (B (Real.toNNReal t) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω))
        μ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub
  simpa [hCov] using
    centeredGaussianSquareCovariance_eq_two_mul_covariance_sq_of_add_sub
      (μ := μ) hY hZ hAdd' hSub' hY_mean hZ_mean

/-- Helper for Exercise 21.2.1: the centered Brownian field has mean `0` at each time in
`[0,1]`. -/
lemma brownianCenteredEval_expectation_eq_zero
    (hB : IsBrownianMotion μ B) {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) :
    ∫ ω, (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hAverage_mem :
      MemLp (fun ω ↦ ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) 2 μ :=
    brownianUnitIntervalAverage_memLp_two_original (μ := μ) (B := B) hB
  -- Proof comment: both the fixed-time Brownian marginal and the unit-interval average are
  -- centered.
  rw [integral_sub]
  · rw [brownianEval_expectation_eq_zero (μ := μ) (B := B) hB (Real.toNNReal t),
      brownianUnitIntervalAverage_expectation (μ := μ) (B := B) hB]
    ring
  · exact (brownianEval_memLp_two (μ := μ) (X := B) hB (Real.toNNReal t)).integrable
      (by norm_num)
  · exact hAverage_mem.integrable (by norm_num)

/-- Helper for Exercise 21.2.1: on the diagonal, the centered Brownian field has variance
`t ^ 2 - t + 1 / 3`. -/
lemma brownianCenteredEval_variance_eq_kernelDiag
    (hB : IsBrownianMotion μ B) {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) :
    Var[fun ω ↦ B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω; μ] =
      t ^ 2 - t + 1 / 3 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hAverage_mem :
      MemLp (fun ω ↦ ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) 2 μ :=
    brownianUnitIntervalAverage_memLp_two_original (μ := μ) (B := B) hB
  have hCentered_aemeas :
      AEMeasurable
        (fun ω ↦ B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) μ := by
    -- Proof comment: the centered field is the difference of the Brownian evaluation and the
    -- square-integrable average.
    exact
      (hB.stronglyMeasurable (Real.toNNReal t)).aemeasurable.sub
        hAverage_mem.aestronglyMeasurable.aemeasurable
  rw [← covariance_self hCentered_aemeas]
  calc
    cov[fun ω ↦ B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω,
        fun ω ↦ B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω; μ]
        = min t t - t - t + t ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 := by
            simpa using
              brownianCenteredCovarianceKernel_eq (μ := μ) (B := B) hB
                (s := t) (t := t) ht_nonneg ht_le_one ht_nonneg ht_le_one
    _ = t ^ 2 - t + 1 / 3 := by
          rw [min_eq_left le_rfl]
          ring

/-- Helper for Exercise 21.2.1: at every time in `[0,1]`, the squared centered Brownian-average
field belongs to `L²`. -/
lemma brownianCenteredSquare_eval_memLp_two
    (hB : IsBrownianMotion μ B) {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) :
    MemLp
      (fun ω ↦
        (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ (2 : ℕ))
      2 μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hCentered_gauss :
      HasGaussianLaw
        (fun ω ↦ B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) μ := by
    -- Route correction: obtain `L⁴` of the centered field from its Gaussian law instead of
    -- routing through the variance of the squared field.
    simpa [one_mul, zero_mul, zero_add] using
      brownianCenteredAffine_hasGaussianLaw (μ := μ) (B := B) hB
        ht_nonneg ht_le_one ht_nonneg ht_le_one 1 0 1
  have hCentered_mem_four :
      MemLp
        (fun ω ↦ B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω)
        4 μ := by
    -- Proof comment: Gaussian variables have finite fourth moments.
    simpa using hCentered_gauss.memLp (p := 4) (by norm_num)
  have hSquare_aestronglyMeasurable :
      AEStronglyMeasurable
        (fun ω ↦
          (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ (2 : ℕ))
        μ := by
    -- Proof comment: squaring preserves strong measurability of the centered field.
    exact hCentered_gauss.aemeasurable.aestronglyMeasurable.pow 2
  -- Proof comment: `X ∈ L⁴` implies `X² ∈ L²` by rewriting the square of `X²` as `X⁴`.
  refine (memLp_two_iff_integrable_sq hSquare_aestronglyMeasurable).2 ?_
  have hFourthInt :
      Integrable
        (fun ω ↦
          |B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω| ^ (4 : ℕ))
        μ := by
    simpa [Real.norm_eq_abs] using hCentered_mem_four.integrable_norm_pow (p := 4)
  refine hFourthInt.congr ?_
  filter_upwards with ω
  have hAbsSq :
      |B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω| ^ (2 : ℕ) =
        (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ (2 : ℕ) := by
    simpa using abs_sq (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω)
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hAbsSq]

/-- Helper for Exercise 21.2.1: on the diagonal, the mean of the squared centered Brownian-average
field is the diagonal covariance kernel `t² - t + 1 / 3`. -/
lemma brownianCenteredSquareExpectation_eq_kernelDiag
    (hB : IsBrownianMotion μ B) {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) :
    ∫ ω,
      (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ (2 : ℕ) ∂μ =
        t ^ 2 - t + 1 / 3 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hAverage_mem :
      MemLp (fun ω ↦ ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) 2 μ :=
    brownianUnitIntervalAverage_memLp_two_original (μ := μ) (B := B) hB
  have hCentered_aemeas :
      AEMeasurable
        (fun ω ↦ B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) μ := by
    -- Proof comment: the centered field is the difference of the Brownian marginal and the
    -- square-integrable average.
    exact
      (hB.stronglyMeasurable (Real.toNNReal t)).aemeasurable.sub
        hAverage_mem.aestronglyMeasurable.aemeasurable
  -- Proof comment: centeredness turns the second moment into the variance, then the diagonal
  -- covariance formula evaluates that variance explicitly.
  rw [← ProbabilityTheory.variance_of_integral_eq_zero hCentered_aemeas
    (brownianCenteredEval_expectation_eq_zero (μ := μ) (B := B) hB ht_nonneg ht_le_one)]
  exact brownianCenteredEval_variance_eq_kernelDiag (μ := μ) (B := B) hB ht_nonneg ht_le_one

/-- Helper for Exercise 21.2.1: the centered Brownian-average field has fourth moment
`3 * K(t,t)^2` on `[0,1]`. -/
lemma brownianCenteredFourthMoment_eq_three_mul_kernel_diag_sq
    (hB : IsBrownianMotion μ B) {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) :
    ∫ ω,
      (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ (4 : ℕ) ∂μ =
        3 * (t ^ 2 - t + 1 / 3) ^ (2 : ℕ) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hCentered_gauss :
      HasGaussianLaw
        (fun ω ↦ B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) μ := by
    -- Route correction: use the single-variable centered Gaussian moment formula directly instead
    -- of rebuilding the fourth moment through `Var[X²]`.
    simpa [one_mul, zero_mul, zero_add] using
      brownianCenteredAffine_hasGaussianLaw (μ := μ) (B := B) hB
        ht_nonneg ht_le_one ht_nonneg ht_le_one 1 0 1
  -- Proof comment: the centered Gaussian fourth-moment theorem applies once the mean and variance
  -- of the diagonal field are recorded separately.
  rw [centeredGaussianFourthMoment_eq_three_mul_variance_sq (μ := μ) hCentered_gauss
      (brownianCenteredEval_expectation_eq_zero (μ := μ) (B := B) hB ht_nonneg ht_le_one)]
  rw [brownianCenteredEval_variance_eq_kernelDiag (μ := μ) (B := B) hB ht_nonneg ht_le_one]

/-- Helper for Exercise 21.2.1: swapping the two interval variables leaves the centered
kernel-square double integral unchanged. -/
private lemma centeredAverageKernelSquareIntegral_swap_eq_one_over_ninety :
    ∫ t in (0 : ℝ)..1,
      ∫ s in (0 : ℝ)..1,
        (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ) = 1 / 90 := by
  have hSymm :
      ∫ t in (0 : ℝ)..1,
        ∫ s in (0 : ℝ)..1,
          (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ) =
        ∫ t in (0 : ℝ)..1,
          ∫ s in (0 : ℝ)..1,
            (min t s - t - s + t ^ 2 / 2 + s ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ) := by
    -- Proof comment: the centered covariance kernel is symmetric in `s` and `t`.
    refine intervalIntegral.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun t _ ↦ by
      refine intervalIntegral.integral_congr_ae ?_
      exact Filter.Eventually.of_forall fun s _ ↦ by
        rw [min_comm]
        ring
  rw [hSymm]
  simpa using centeredAverageKernelSquareIntegral_eq_one_over_ninety

/-- Helper for Exercise 21.2.1: the inner interval integral splits into the kernel-square term and
the centered variance polynomial term. -/
private lemma centeredSquareInnerIntegral_split (t : ℝ) :
    ∫ s in (0 : ℝ)..1,
      (2 * (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ) +
        (t ^ 2 - t + 1 / 3) * (s ^ 2 - s + 1 / 3)) =
      2 * (∫ s in (0 : ℝ)..1,
        (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ)) +
        (t ^ 2 - t + 1 / 3) * (1 / 6 : ℝ) := by
  have hInt₁ :
      IntervalIntegrable
        (fun s : ℝ ↦
          2 * (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ))
        volume 0 1 := by
    have hCont :
        Continuous fun s : ℝ ↦
          2 * (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ) := by
      fun_prop
    exact hCont.intervalIntegrable 0 1
  have hInt₂ :
      IntervalIntegrable
        (fun s : ℝ ↦ (t ^ 2 - t + 1 / 3 : ℝ) * (s ^ 2 - s + 1 / 3))
        volume 0 1 := by
    have hCont :
        Continuous fun s : ℝ ↦ (t ^ 2 - t + 1 / 3 : ℝ) * (s ^ 2 - s + 1 / 3) := by
      fun_prop
    exact hCont.intervalIntegrable 0 1
  -- Proof comment: both summands are deterministic continuous functions, so linearity of the
  -- interval integral isolates the scalar mean polynomial.
  rw [intervalIntegral.integral_add hInt₁ hInt₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, brownianCenteredVariancePolynomialIntegral_eq_one_six]

/-- Helper for Exercise 21.2.1: integrating the split inner formula over the outer interval leaves
the kernel-square double integral and the squared mean term. -/
private lemma centeredSquareOuterIntegral_split :
    ∫ t in (0 : ℝ)..1,
      (2 * (∫ s in (0 : ℝ)..1,
        (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ)) +
        (t ^ 2 - t + 1 / 3) * (1 / 6 : ℝ)) =
      2 * (∫ s in (0 : ℝ)..1,
        ∫ t in (0 : ℝ)..1,
          (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ)) +
        (1 / 6 : ℝ) ^ (2 : ℕ) := by
  have hOuter₁ :
      IntervalIntegrable
        (fun t : ℝ ↦
          2 * (∫ s in (0 : ℝ)..1,
            (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ)))
        volume 0 1 := by
    have hCont :
        Continuous fun t : ℝ ↦
          2 * (∫ s in (0 : ℝ)..1,
            (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ)) := by
      fun_prop
    exact hCont.intervalIntegrable 0 1
  have hOuter₂ :
      IntervalIntegrable (fun t : ℝ ↦ (t ^ 2 - t + 1 / 3 : ℝ) * (1 / 6 : ℝ))
        volume 0 1 := by
    have hCont : Continuous fun t : ℝ ↦ (t ^ 2 - t + 1 / 3 : ℝ) * (1 / 6 : ℝ) := by
      fun_prop
    exact hCont.intervalIntegrable 0 1
  -- Proof comment: the remaining outer integral is again deterministic; rewrite the swapped
  -- kernel-square integral and the mean polynomial by their closed forms.
  rw [intervalIntegral.integral_add hOuter₁ hOuter₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const, brownianCenteredVariancePolynomialIntegral_eq_one_six,
    centeredAverageKernelSquareIntegral_swap_eq_one_over_ninety,
    centeredAverageKernelSquareIntegral_eq_one_over_ninety]
  norm_num

lemma brownianCenteredQuadraticDeviation_variance_eq_two_mul_kernelSquareIntegral
    (hB : IsBrownianMotion μ B) :
    Var[fun ω ↦ ∫ t in (0 : ℝ)..1,
      (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2; μ] =
        2 * (∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1,
            (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let Ac : Ω → ℝ := fun ω ↦
    ∫ s, brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s) ω ∂ν
  let Z : ℝ → Ω → ℝ := fun t ω ↦
    brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal t) ω - Ac ω
  let S : ℝ × Ω → ℝ := fun z ↦ Z z.1 z.2 ^ (2 : ℕ)
  let Qc : Ω → ℝ := fun ω ↦ ∫ t, S (t, ω) ∂ν
  letI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    simp [ν]
  have hAc_mem : MemLp Ac 2 μ := by
    simpa [Ac, ν] using
      brownianContinuousVersion_unitIntervalAverage_memLp_two (μ := μ) (B := B) hB
  have hAc_original :
      Ac =ᵐ[μ] fun ω ↦ ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω := by
    simpa [Ac, ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      brownianContinuousVersion_average_ae_eq (μ := μ) (B := B) hB
  have hStripB_mem :
      MemLp
        (fun z : ℝ × Ω ↦
          brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal z.1) z.2)
        2 (ν.prod μ) := by
    simpa [ν] using
      brownianContinuousVersion_unitStrip_memLp_two (μ := μ) (B := B) hB
  have hAc_prod_mem : MemLp (fun z : ℝ × Ω ↦ Ac z.2) 2 (ν.prod μ) := hAc_mem.comp_snd ν
  have hZstrip_mem :
      MemLp (fun z : ℝ × Ω ↦ Z z.1 z.2) 2 (ν.prod μ) := by
    simpa [Z] using hStripB_mem.sub hAc_prod_mem
  have hS_meas : AEStronglyMeasurable S (ν.prod μ) := by
    simpa [S] using hZstrip_mem.aestronglyMeasurable.pow 2
  have hSectionFourth :
      (fun t : ℝ ↦ ∫ ω, S (t, ω) ^ (2 : ℕ) ∂μ) =ᵐ[ν]
        fun t ↦ 3 * (t ^ 2 - t + 1 / 3) ^ (2 : ℕ) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with t ht
    have ht_nonneg : 0 ≤ t := le_of_lt ht.1
    have ht_le_one : t ≤ 1 := ht.2
    have hPatchEq :
        (fun ω ↦ S (t, ω) ^ (2 : ℕ)) =ᵐ[μ]
          fun ω ↦
            ((B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ (2 : ℕ)) ^
              (2 : ℕ) := by
      filter_upwards
        [hAc_original,
          brownianContinuousVersion_areModifications (μ := μ) (B := B) hB (Real.toNNReal t)] with
          ω hω_avg hω_mod
      simp [S, Z, hω_avg, hω_mod]
    calc
      ∫ ω, S (t, ω) ^ (2 : ℕ) ∂μ
          = ∫ ω,
              ((B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ (2 : ℕ)) ^
                (2 : ℕ) ∂μ := by
                exact integral_congr_ae hPatchEq
      _ = ∫ ω,
            (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ (4 : ℕ) ∂μ := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun ω ↦ by
              ring_nf
      _ = 3 * (t ^ 2 - t + 1 / 3) ^ (2 : ℕ) := by
            exact
              brownianCenteredFourthMoment_eq_three_mul_kernel_diag_sq
                (μ := μ) (B := B) hB ht_nonneg ht_le_one
  have hS_sq_int : Integrable (fun z : ℝ × Ω ↦ S z ^ (2 : ℕ)) (ν.prod μ) := by
    have hSsq_meas : AEStronglyMeasurable (fun z : ℝ × Ω ↦ S z ^ (2 : ℕ)) (ν.prod μ) := by
      exact hS_meas.pow 2
    refine (integrable_prod_iff hSsq_meas).2 ?_
    refine ⟨?_, ?_⟩
    · refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
      filter_upwards with t ht
      have ht_nonneg : 0 ≤ t := le_of_lt ht.1
      have ht_le_one : t ≤ 1 := ht.2
      have hOrig_mem :
          MemLp
            (fun ω ↦
              (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ (2 : ℕ))
            2 μ :=
        brownianCenteredSquare_eval_memLp_two (μ := μ) (B := B) hB ht_nonneg ht_le_one
      have hSectionEq :
          (fun ω ↦ S (t, ω)) =ᵐ[μ]
            fun ω ↦
              (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ (2 : ℕ) := by
        filter_upwards
          [hAc_original,
            brownianContinuousVersion_areModifications (μ := μ) (B := B) hB (Real.toNNReal t)] with
            ω hω_avg hω_mod
        simp [S, Z, hω_avg, hω_mod]
      have hPatch_mem :
          MemLp (fun ω ↦ S (t, ω)) 2 μ := by
        refine hOrig_mem.congr_norm ?_ ?_
        · exact hOrig_mem.aestronglyMeasurable.congr hSectionEq.symm
        · filter_upwards [hSectionEq] with ω hω
          simp [hω]
      exact hPatch_mem.integrable_sq
    · have hOuterEq :
          (fun t : ℝ ↦ ∫ ω, ‖S (t, ω) ^ (2 : ℕ)‖ ∂μ) =ᵐ[ν]
            fun t ↦ 3 * (t ^ 2 - t + 1 / 3) ^ (2 : ℕ) := by
        have hSectionFourth' :
            ∀ᵐ t ∂ν, ∫ ω, S (t, ω) ^ (2 : ℕ) ∂μ = 3 * (t ^ 2 - t + 1 / 3) ^ (2 : ℕ) :=
          hSectionFourth
        filter_upwards [hSectionFourth'] with t ht
        have hNonneg : ∀ ω : Ω, 0 ≤ S (t, ω) ^ (2 : ℕ) := fun ω ↦ sq_nonneg _
        rw [show (∫ ω, ‖S (t, ω) ^ (2 : ℕ)‖ ∂μ) = ∫ ω, S (t, ω) ^ (2 : ℕ) ∂μ by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun ω ↦ by simp [Real.norm_of_nonneg (hNonneg ω)]]
        exact ht
      have hPolyInt :
          Integrable (fun t : ℝ ↦ 3 * (t ^ 2 - t + 1 / 3) ^ (2 : ℕ)) ν := by
        have hCont : Continuous fun t : ℝ ↦ 3 * (t ^ 2 - t + 1 / 3) ^ (2 : ℕ) := by
          fun_prop
        have hInterval :
            IntervalIntegrable (fun t : ℝ ↦ 3 * (t ^ 2 - t + 1 / 3) ^ (2 : ℕ)) volume 0 1 :=
          hCont.intervalIntegrable 0 1
        rw [show ν = volume.restrict (Set.Ioc (0 : ℝ) 1) by rfl]
        simpa [IntegrableOn, Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
          (intervalIntegrable_iff_integrableOn_Ioc_of_le
            (μ := volume)
            (f := fun t : ℝ ↦ 3 * (t ^ 2 - t + 1 / 3) ^ (2 : ℕ))
            (show (0 : ℝ) ≤ 1 by norm_num)).1 hInterval
      exact hPolyInt.congr hOuterEq.symm
  have hS_mem : MemLp S 2 (ν.prod μ) := (memLp_two_iff_integrable_sq hS_meas).2 hS_sq_int
  have hQc_mem : MemLp Qc 2 μ := memLpTwo_integral_restrict_of_memLpTwo_prod (μ := μ) hS_mem
  have hQc_original :
      Qc =ᵐ[μ] fun ω ↦ ∫ t in (0 : ℝ)..1,
        (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2 := by
    filter_upwards [hAc_original, brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB] with
      ω hω hω_patch
    simp [Qc, S, Z, hω, hω_patch, ν, intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)]
  have hQc_mean : ∫ ω, Qc ω ∂μ = 1 / 6 := by
    calc
      ∫ ω, Qc ω ∂μ
          = ∫ ω, (∫ t in (0 : ℝ)..1,
              (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2) ∂μ := by
                exact integral_congr_ae hQc_original
      _ = 1 / 6 := brownianUnitIntervalCenteredQuadraticDeviation_expectation (μ := μ) (B := B) hB
  have hProdInt :
      Integrable (fun z : ℝ × Ω ↦ S z * Qc z.2) (ν.prod μ) := by
    exact hS_mem.integrable_mul (hQc_mem.comp_snd ν)
  have hSecondMoment :
      ∫ ω, Qc ω ^ (2 : ℕ) ∂μ =
        2 * (∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1,
            (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2) + (1 / 6) ^ (2 : ℕ) := by
    have hFubini :
        ∫ z, S z * Qc z.2 ∂(ν.prod μ) = ∫ ω, Qc ω ^ (2 : ℕ) ∂μ := by
      calc
        ∫ z, S z * Qc z.2 ∂(ν.prod μ)
            = ∫ ω, ∫ t, S (t, ω) * Qc ω ∂ν ∂μ := by
                simpa [S] using
                  (MeasureTheory.integral_prod_symm
                    (μ := ν) (ν := μ) (f := fun z : ℝ × Ω ↦ S z * Qc z.2) hProdInt)
        _ = ∫ ω, Qc ω ^ (2 : ℕ) ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards [hProdInt.prod_left_ae] with ω hω
              rw [integral_mul_const]
              simp [Qc, pow_two]
    have hInner :
        (fun t : ℝ ↦ ∫ ω, S (t, ω) * Qc ω ∂μ) =ᵐ[ν]
          fun t ↦
            ∫ s in (0 : ℝ)..1,
              2 * (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ) +
                (t ^ 2 - t + 1 / 3) * (s ^ 2 - s + 1 / 3) := by
      refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
      filter_upwards with t ht
      have ht_nonneg : 0 ≤ t := le_of_lt ht.1
      have ht_le_one : t ≤ 1 := ht.2
      let Sto : Ω → ℝ := fun ω ↦
        (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ (2 : ℕ)
      have hSto_mem : MemLp Sto 2 μ :=
        brownianCenteredSquare_eval_memLp_two (μ := μ) (B := B) hB ht_nonneg ht_le_one
      have hSto_eq :
          (fun ω ↦ S (t, ω)) =ᵐ[μ] Sto := by
        filter_upwards
          [hAc_original,
            brownianContinuousVersion_areModifications (μ := μ) (B := B) hB (Real.toNNReal t)] with
            ω hω_avg hω_mod
        simp [S, Z, Sto, hω_avg, hω_mod]
      have hStripProd :
          Integrable (fun z : ℝ × Ω ↦ Sto z.2 * S z) (ν.prod μ) := by
        exact (hSto_mem.comp_snd ν).integrable_mul hS_mem
      calc
        ∫ ω, S (t, ω) * Qc ω ∂μ = ∫ ω, Sto ω * Qc ω ∂μ := by
            exact integral_congr_ae <| hSto_eq.mul (Filter.EventuallyEq.rfl)
        _ = ∫ z, Sto z.2 * S z ∂(ν.prod μ) := by
              calc
                ∫ ω, Sto ω * Qc ω ∂μ
                    = ∫ ω, ∫ s, Sto ω * S (s, ω) ∂ν ∂μ := by
                        refine integral_congr_ae ?_
                        filter_upwards [hStripProd.prod_left_ae] with ω hω
                        rw [integral_const_mul]
                _ = ∫ z, Sto z.2 * S z ∂(ν.prod μ) := by
                      simpa [Function.uncurry] using
                        (MeasureTheory.integral_integral_symm
                          (μ := μ) (ν := ν)
                          (f := fun ω s ↦ Sto ω * S (s, ω))
                          (by simpa [Function.uncurry] using hStripProd.swap))
        _ = ∫ s in (0 : ℝ)..1,
              ∫ ω,
                Sto ω *
                  ((brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s) ω - Ac ω) ^
                    (2 : ℕ)) ∂μ := by
              simpa [S, Z, ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
                (MeasureTheory.integral_prod
                  (μ := ν) (ν := μ)
                  (f := fun z : ℝ × Ω ↦ Sto z.2 * S z) hStripProd)
        _ = ∫ s in (0 : ℝ)..1,
              (2 * (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ) +
                (t ^ 2 - t + 1 / 3) * (s ^ 2 - s + 1 / 3)) := by
              refine intervalIntegral.integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun s hs ↦ by
                have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := by
                  simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hs
                have hs_nonneg : 0 ≤ s := le_of_lt hs'.1
                have hs_le_one : s ≤ 1 := hs'.2
                let Sso : Ω → ℝ := fun ω ↦
                  (B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ^ (2 : ℕ)
                have hSso_mem : MemLp Sso 2 μ :=
                  brownianCenteredSquare_eval_memLp_two (μ := μ) (B := B) hB hs_nonneg hs_le_one
                have hSso_eq :
                    (fun ω ↦
                      (brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s) ω - Ac ω) ^
                        (2 : ℕ)) =ᵐ[μ] Sso := by
                  filter_upwards
                    [hAc_original,
                      brownianContinuousVersion_areModifications (μ := μ) (B := B) hB
                        (Real.toNNReal s)] with ω hω_avg hω_mod
                  simp [Sso, hω_avg, hω_mod]
                have hProdEq :
                    ∫ ω,
                      Sto ω *
                        ((brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s) ω -
                          Ac ω) ^ (2 : ℕ)) ∂μ =
                      ∫ ω, Sto ω * Sso ω ∂μ := by
                  exact integral_congr_ae <| Filter.EventuallyEq.rfl.mul hSso_eq
                have hSto_expect : ∫ ω, Sto ω ∂μ = t ^ 2 - t + 1 / 3 :=
                  brownianCenteredSquareExpectation_eq_kernelDiag (μ := μ) (B := B) hB
                    ht_nonneg ht_le_one
                have hSso_expect : ∫ ω, Sso ω ∂μ = s ^ 2 - s + 1 / 3 :=
                  brownianCenteredSquareExpectation_eq_kernelDiag (μ := μ) (B := B) hB
                    hs_nonneg hs_le_one
                have hCov :
                    cov[Sto, Sso; μ] =
                      2 * (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ) :=
                  by
                    have hCov0 :
                        cov[Sto, Sso; μ] =
                          2 * (min t s - t - s + t ^ 2 / 2 + s ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ) := by
                      simpa [Sto, Sso] using
                        brownianCenteredSquareCovariance_eq_two_mul_kernel_sq (μ := μ) (B := B) hB
                          ht_nonneg ht_le_one hs_nonneg hs_le_one
                    simpa [sub_eq_add_neg, min_comm, add_assoc, add_left_comm, add_comm] using hCov0
                calc
                  ∫ ω,
                      Sto ω *
                        ((brownianContinuousVersion (μ := μ) (B := B) hB (Real.toNNReal s) ω -
                          Ac ω) ^ (2 : ℕ)) ∂μ
                      = ∫ ω, Sto ω * Sso ω ∂μ := hProdEq
                  _ = cov[Sto, Sso; μ] + (∫ ω, Sto ω ∂μ) * (∫ ω, Sso ω ∂μ) := by
                        rw [covariance_eq_sub hSto_mem hSso_mem]
                        simp [Pi.mul_apply]
                  _ = 2 * (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ) +
                        (t ^ 2 - t + 1 / 3) * (s ^ 2 - s + 1 / 3) := by
                          rw [hCov, hSto_expect, hSso_expect]
    calc
      ∫ ω, Qc ω ^ (2 : ℕ) ∂μ = ∫ z, S z * Qc z.2 ∂(ν.prod μ) := hFubini.symm
      _ = ∫ t in (0 : ℝ)..1, ∫ ω, S (t, ω) * Qc ω ∂μ := by
            simpa [Qc, S, ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
              (MeasureTheory.integral_prod
                (μ := ν) (ν := μ) (f := fun z : ℝ × Ω ↦ S z * Qc z.2) hProdInt)
      _ = ∫ t in (0 : ℝ)..1,
            (∫ s in (0 : ℝ)..1,
              2 * (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ) +
                (t ^ 2 - t + 1 / 3) * (s ^ 2 - s + 1 / 3)) := by
              simpa [ν, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
                integral_congr_ae hInner
      _ = ∫ t in (0 : ℝ)..1,
            (2 * (∫ s in (0 : ℝ)..1,
              (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ)) +
              (t ^ 2 - t + 1 / 3) * (1 / 6 : ℝ)) := by
              refine intervalIntegral.integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun t _ ↦ centeredSquareInnerIntegral_split t
      _ = 2 * (∫ s in (0 : ℝ)..1,
            ∫ t in (0 : ℝ)..1,
              (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ)) +
            (1 / 6) ^ (2 : ℕ) := centeredSquareOuterIntegral_split
  have hVarQc :
      Var[Qc; μ] = 2 * (∫ s in (0 : ℝ)..1,
        ∫ t in (0 : ℝ)..1,
          (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ)) := by
    rw [ProbabilityTheory.variance_eq_sub (μ := μ) hQc_mem]
    rw [hQc_mean]
    have hSecondMoment' := hSecondMoment
    norm_num [pow_two] at hSecondMoment' ⊢
    linarith
  calc
    Var[fun ω ↦ ∫ t in (0 : ℝ)..1,
        (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2; μ]
        = Var[Qc; μ] := by
            exact ProbabilityTheory.variance_congr hQc_original.symm
    _ = 2 * (∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1,
            (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ)) := hVarQc
    _ = 2 * (∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1,
            (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ 2) := by
          simp

-- Proof sketch: expand `Var[Q] = E[Q^2] - E[Q]^2` for
-- `Q = ∫₀¹ (B_t - ∫₀¹ B_s ds)^2 dt`, then use Tonelli/Fubini to rewrite the two terms as the
-- double integral of the square-field covariance.
/-- Helper for Exercise 21.2.1: the variance of the integrated centered square is the double
integral of the pointwise square covariance. -/
lemma brownianCenteredQuadraticDeviation_variance_eq_doubleIntegralCovariance
    (hB : IsBrownianMotion μ B) :
    Var[fun ω ↦ ∫ t in (0 : ℝ)..1,
      (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2; μ] =
      ∫ s in (0 : ℝ)..1,
        ∫ t in (0 : ℝ)..1,
          cov[
            (fun ω ↦
              (B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ^ (2 : ℕ)),
            (fun ω ↦
              (B (Real.toNNReal t) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ^ (2 : ℕ)); μ] := by
  let K : ℝ → ℝ → ℝ := fun s t ↦
    (min s t - s - t + s ^ 2 / 2 + t ^ 2 / 2 + 1 / 3 : ℝ) ^ (2 : ℕ)
  let C : ℝ → ℝ → ℝ := fun s t ↦
    cov[
      (fun ω ↦
        (B (Real.toNNReal s) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ^ (2 : ℕ)),
      (fun ω ↦
        (B (Real.toNNReal t) ω - ∫ u in (0 : ℝ)..1, B (Real.toNNReal u) ω) ^ (2 : ℕ)); μ]
  rw [brownianCenteredQuadraticDeviation_variance_eq_two_mul_kernelSquareIntegral
      (μ := μ) (B := B) hB]
  rw [← intervalIntegral.integral_const_mul (r := (2 : ℝ))
    (f := fun s : ℝ ↦ ∫ t in (0 : ℝ)..1, K s t)]
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun s hs ↦ by
    have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hs
    have hs_nonneg : 0 ≤ s := le_of_lt hs'.1
    have hs_le_one : s ≤ 1 := hs'.2
    rw [← intervalIntegral.integral_const_mul (r := (2 : ℝ)) (f := fun t : ℝ ↦ K s t)]
    refine intervalIntegral.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun t ht ↦ by
      have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
      have ht_nonneg : 0 ≤ t := le_of_lt ht'.1
      have ht_le_one : t ≤ 1 := ht'.2
      -- Proof comment: the explicit `ℝ`-valued aliases keep the interval-integral codomain
      -- fixed while the pointwise covariance formula rewrites the integrand.
      simp [K, C,
        brownianCenteredSquareCovariance_eq_two_mul_kernel_sq
          (μ := μ) (B := B) hB hs_nonneg hs_le_one ht_nonneg ht_le_one]
-- Proof sketch: the centered process `t ↦ B_t - ∫₀¹ B_s ds` is Gaussian with explicit covariance
-- kernel. For a centered Gaussian process, the variance of the integrated square is
-- `2 ∫₀¹∫₀¹ K(s,t)^2 ds dt`, and evaluating this kernel integral gives `1/45`.
/-- Exercise 21.2.1 (5): item (iii), the variance of the integrated squared deviation from the
unit-interval Brownian average is `1 / 45`. -/
theorem brownianUnitIntervalCenteredQuadraticDeviation_variance (hB : IsBrownianMotion μ B) :
    Var[fun ω ↦ ∫ t in (0 : ℝ)..1,
      (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2; μ] = 1 / 45 := by
  -- Proof comment: the stochastic part is packaged in the preceding bridge, so the main theorem
  -- now closes by the deterministic kernel-square integral.
  rw [brownianCenteredQuadraticDeviation_variance_eq_two_mul_kernelSquareIntegral
      (μ := μ) (B := B) hB, centeredAverageKernelSquareIntegral_eq_one_over_ninety]
  norm_num

end BrownianMotionExercise

end ProbabilityTheory
