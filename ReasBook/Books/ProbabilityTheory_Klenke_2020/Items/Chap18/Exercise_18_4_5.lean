/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.TotalVariation
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory ZMod

noncomputable section

namespace ProbabilityTheory

private theorem fin_pos {N : ℕ} (i : Fin N) : 0 < N :=
  lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.succ_le_of_lt i.2)

private theorem pos_of_two_le {N : ℕ} (hN : 2 ≤ N) : 0 < N :=
  lt_of_lt_of_le (by decide : 0 < 2) hN

/-- The transition matrix of the cyclic lazy walk on `Fin N`: from `i` the chain jumps to the
cyclic successor `finRotate N i` with probability `r` and stays put with probability `1 - r`. The
sum form handles the degenerate one-point cycle as well. -/
def cyclicLazyWalkTransitionMatrix (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Fin N → Fin N → ℝ≥0∞ :=
  fun i j ↦
    (if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
      (if j = i then ENNReal.ofReal (1 - (r : ℝ)) else 0)

/-- The Markov kernel associated with the cyclic lazy walk transition matrix. -/
abbrev cyclicLazyWalkKernel (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Kernel (Fin N) (Fin N) :=
  discreteMatrixKernel (cyclicLazyWalkTransitionMatrix N r)

/-- The uniform probability distribution on the finite cyclic state space `Fin N`. -/
def cyclicLazyWalkInvariantDistribution (N : ℕ) (hN : 0 < N) : ProbabilityMeasure (Fin N) :=
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  ⟨(PMF.uniformOfFintype (Fin N)).toMeasure, inferInstance⟩

/-- The explicit spectral radius of the largest nontrivial Fourier mode of the cyclic lazy walk. -/
def cyclicLazyWalkExponentialRate (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : ℝ :=
  if _ : N ≤ 1 then 0 else Real.sqrt (1 - 4 * r * (1 - r) * Real.sin (Real.pi / N) ^ 2)

/-- Helper for Exercise 18.4.5: the Fourier eigenvalue attached to the mode `k` of the cyclic lazy
walk on `Fin N`. -/
private def cyclicLazyWalkFourierEigenvalue
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (k : Fin N) : ℂ :=
  ((1 - (r : ℝ)) : ℂ) +
    ((r : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * (k : ℝ) / N) : ℝ) * Complex.I)

/-- Helper for Exercise 18.4.5: the squared modulus of the Fourier eigenvalue is the standard
trigonometric expression `1 - 4 r (1 - r) sin(π k / N)^2`. -/
private theorem cyclicLazyWalkFourierEigenvalue_normSq
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (k : Fin N) :
    Complex.normSq (cyclicLazyWalkFourierEigenvalue N r k) =
      1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi * (k : ℝ) / N) ^ 2 := by
  let θ : ℝ := 2 * Real.pi * (k : ℝ) / N
  let φ : ℝ := Real.pi * (k : ℝ) / N
  have hθ : θ = 2 * φ := by
    simp [θ, φ]
    ring
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    simpa [add_comm] using (Real.sin_sq_add_cos_sq θ)
  have heig :
      cyclicLazyWalkFourierEigenvalue N r k =
        (((1 - (r : ℝ)) : ℂ) + ((r : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) := by
    simp [cyclicLazyWalkFourierEigenvalue, θ]
  have hre : (Complex.exp (θ * Complex.I)).re = Real.cos θ := by
    simp
  have him : (Complex.exp (θ * Complex.I)).im = Real.sin θ := by
    simp
  -- Proof comment: compute the real and imaginary parts of the eigenvalue explicitly, then reduce
  -- the resulting norm square using `cos (2 φ) = 1 - 2 sin φ^2`.
  calc
    Complex.normSq (cyclicLazyWalkFourierEigenvalue N r k)
      = (((1 - (r : ℝ)) + (r : ℝ) * Real.cos θ) ^ 2 + ((r : ℝ) * Real.sin θ) ^ 2) := by
          rw [heig, Complex.normSq_apply]
          simp [hre, him]
          ring
    _ = (1 - (r : ℝ)) ^ 2 + (r : ℝ) ^ 2 + 2 * (r : ℝ) * (1 - (r : ℝ)) * Real.cos θ := by
          nlinarith [htrig]
    _ = (1 - (r : ℝ)) ^ 2 + (r : ℝ) ^ 2 +
          2 * (r : ℝ) * (1 - (r : ℝ)) * (1 - 2 * Real.sin φ ^ 2) := by
          rw [hθ, Real.cos_two_mul_eq_one_sub]
    _ = 1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin φ ^ 2 := by
          ring
    _ = 1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi * (k : ℝ) / N) ^ 2 := by
          simp [φ]

-- Proof sketch: this is immediate from the definition of
-- `cyclicLazyWalkTransitionMatrix`.
/-- The cyclic lazy walk matrix is the sum of the jump-to-successor and hold contributions. -/
theorem cyclicLazyWalkTransitionMatrix_apply
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (i j : Fin N) :
    cyclicLazyWalkTransitionMatrix N r i j =
      (if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
        (if j = i then ENNReal.ofReal (1 - (r : ℝ)) else 0) := rfl

-- Proof sketch: evaluate `cyclicLazyWalkKernel N r i` on the singleton `{j}`, expand the defining
-- sum of Dirac measures, and keep only the `j`-th summand.
/-- Evaluating the cyclic lazy walk kernel at a singleton recovers the corresponding matrix entry.
-/
theorem cyclicLazyWalkKernel_apply_singleton
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (i j : Fin N) :
    cyclicLazyWalkKernel N r i {j} = cyclicLazyWalkTransitionMatrix N r i j := by
  -- Proof comment: evaluate the discrete matrix kernel on the singleton `{j}` and keep the unique
  -- Dirac mass that survives.
  rw [cyclicLazyWalkKernel, discreteMatrixKernel_apply]
  rw [Measure.sum_apply _ (measurableSet_singleton j)]
  simp_rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton j)]
  rw [tsum_eq_single j]
  · simp
  · intro b hb
    simp [hb]

-- Proof sketch: for each row, only the successor and holding terms can contribute; their masses
-- are nonnegative and add up to `1`.
/-- The cyclic lazy walk transition matrix is stochastic. -/
theorem cyclicLazyWalkTransitionMatrix_isStochastic
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) :
    IsStochasticMatrix (cyclicLazyWalkTransitionMatrix N r) := by
  intro i
  -- Proof comment: the row sum splits into the jump contribution and the hold contribution, and
  -- each is concentrated on exactly one state.
  rw [tsum_fintype]
  simp_rw [cyclicLazyWalkTransitionMatrix_apply]
  rw [Finset.sum_add_distrib]
  have hsucc :
      ∑ y : Fin N, (if y = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) =
        ENNReal.ofReal (r : ℝ) := by
    simpa using
      (Finset.sum_eq_single_of_mem
        (f := fun y : Fin N ↦ if y = finRotate N i then ENNReal.ofReal (r : ℝ) else 0)
        (finRotate N i) (Finset.mem_univ _) (by
          intro y _ hy
          exact if_neg hy))
  have hstay :
      ∑ y : Fin N, (if y = i then ENNReal.ofReal (1 - (r : ℝ)) else 0) =
        ENNReal.ofReal (1 - (r : ℝ)) := by
    simpa using
      (Finset.sum_eq_single_of_mem
        (f := fun y : Fin N ↦ if y = i then ENNReal.ofReal (1 - (r : ℝ)) else 0)
        i (Finset.mem_univ _) (by
          intro y _ hy
          exact if_neg hy))
  calc
    (∑ y : Fin N, if y = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
        (∑ y : Fin N, if y = i then ENNReal.ofReal (1 - (r : ℝ)) else 0) =
      ENNReal.ofReal (r : ℝ) + ENNReal.ofReal (1 - (r : ℝ)) := by rw [hsucc, hstay]
    _ = 1 := by
      rw [← ENNReal.ofReal_add]
      · norm_num
      · exact le_of_lt r.2.1
      · linarith [r.2.2]

/-- The cyclic lazy walk kernel is Markov. -/
instance cyclicLazyWalkKernel.instIsMarkovKernel
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) :
    IsMarkovKernel (cyclicLazyWalkKernel N r) := by
  simpa [cyclicLazyWalkKernel] using
    (discreteMatrixKernel_isMarkovKernel
      (cyclicLazyWalkTransitionMatrix N r)
      (cyclicLazyWalkTransitionMatrix_isStochastic N r))

/-- Helper for Exercise 18.4.5: every iterate of the cyclic lazy walk kernel is again a Markov
kernel. -/
private instance cyclicLazyWalkKernelPow.instIsMarkovKernel
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    IsMarkovKernel (cyclicLazyWalkKernel N r ^ n) := by
  induction n with
  | zero =>
      simpa using (inferInstance : IsMarkovKernel (Kernel.id : Kernel (Fin N) (Fin N)))
  | succ n ih =>
      haveI := ih
      simpa [pow_succ] using
        (inferInstance :
          IsMarkovKernel
            ((cyclicLazyWalkKernel N r ^ n) ∘ₖ cyclicLazyWalkKernel N r))

/-- Helper for Exercise 18.4.5: the deterministic all-forward path has positive mass after every
number of steps. -/
private theorem cyclicLazyWalkForwardIterate_pos
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) :
    ∀ n : ℕ, ∀ i : Fin N,
      0 < ((cyclicLazyWalkKernel N r) ^ n) i {((finRotate N)^[n]) i} :=
  fun n ↦ by
    induction n with
    | zero =>
        intro i
        -- Proof comment: at time `0` the kernel is the identity, so the start state already
        -- carries mass `1`.
        simpa [pow_zero] using
          (show 0 < ((Kernel.id : Kernel (Fin N) (Fin N)) i) {i} by simp [Kernel.id_apply])
    | succ n ih =>
        intro i
        -- Proof comment: expand the `(n + 1)`-step kernel by Chapman-Kolmogorov and keep the
        -- contribution from the deterministic forward predecessor `((finRotate N)^[n]) i`.
        rw [Kernel.pow_succ_apply_eq_lintegral (cyclicLazyWalkKernel N r) n i
          (measurableSet_singleton (((finRotate N)^[n + 1]) i))]
        rw [MeasureTheory.lintegral_fintype]
        let y : Fin N := ((finRotate N)^[n]) i
        have hy_pos :
            0 < (cyclicLazyWalkKernel N r ^ n) i {y} := by
          simpa [y] using ih i
        have hstep_pos :
            0 < cyclicLazyWalkKernel N r y {((finRotate N)^[n + 1]) i} := by
          have hr_pos : 0 < ENNReal.ofReal (r : ℝ) := ENNReal.ofReal_pos.mpr r.2.1
          have hkernel :
              cyclicLazyWalkKernel N r y {((finRotate N)^[n + 1]) i} =
                cyclicLazyWalkTransitionMatrix N r y (((finRotate N)^[n + 1]) i) :=
            cyclicLazyWalkKernel_apply_singleton N r y (((finRotate N)^[n + 1]) i)
          have hs :
              ((finRotate N)^[n + 1]) i = finRotate N y := by
            simpa [y] using (Function.iterate_succ_apply' (f := finRotate N) n i)
          have hle :
              ENNReal.ofReal (r : ℝ) ≤
                cyclicLazyWalkTransitionMatrix N r y (((finRotate N)^[n + 1]) i) := by
            rw [cyclicLazyWalkTransitionMatrix_apply]
            by_cases hfix : ((finRotate N)^[n + 1]) i = ((finRotate N)^[n]) i
            · rw [if_pos hs, if_pos hfix]
              exact le_add_of_nonneg_right bot_le
            · rw [if_pos hs, if_neg hfix]
              simp
          rw [hkernel]
          exact lt_of_lt_of_le hr_pos hle
        have hterm_pos :
            0 <
              cyclicLazyWalkKernel N r y {((finRotate N)^[n + 1]) i} *
                ((cyclicLazyWalkKernel N r ^ n) i) {y} :=
          ENNReal.mul_pos hstep_pos.ne' hy_pos.ne'
        have hsum_pos :
            0 <
              ∑ u : Fin N,
                cyclicLazyWalkKernel N r u {((finRotate N)^[n + 1]) i} *
                  ((cyclicLazyWalkKernel N r ^ n) i) {u} := by
          refine lt_of_lt_of_le hterm_pos ?_
          simpa using
            (Finset.single_le_sum
              (f := fun u : Fin N ↦
                cyclicLazyWalkKernel N r u {((finRotate N)^[n + 1]) i} *
                  ((cyclicLazyWalkKernel N r ^ n) i) {u})
              (fun _ _ ↦ by positivity)
              (Finset.mem_univ y))
        simpa [y]
          using hsum_pos

/-- Helper for Exercise 18.4.5: every state is reached from every starting point in finitely many
steps with positive probability. -/
private theorem cyclicLazyWalkPositiveSingletonReachability
    (N : ℕ) (hN : 0 < N) (r : Set.Ioo (0 : ℝ) 1) (i j : Fin N) :
    ∃ n : ℕ, 0 < ((cyclicLazyWalkKernel N r) ^ n) i {j} := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  -- Proof comment: moving forward `(j - i).1` times lands exactly at `j`, so the positive
  -- all-forward path from the previous lemma gives the required singleton mass.
  refine ⟨(j - i).1, ?_⟩
  have hiterate : ((finRotate N)^[((j - i).1)]) i = j := by
    rw [← finCycle_eq_finRotate_iterate (k := j - i)]
    simp
  simpa [hiterate] using
    cyclicLazyWalkForwardIterate_pos N r ((j - i).1) i

-- Proof sketch: positive forward-step probability lets the chain reach every state by repeated
-- cyclic increments, so every state communicates with every other.
/-- The cyclic lazy walk is irreducible as soon as the forward jump probability is positive. -/
theorem cyclicLazyWalk_isIrreducible
    (N : ℕ) (hN : 0 < N) (r : Set.Ioo (0 : ℝ) 1) :
    Kernel.IsIrreducible (Measure.count : Measure (Fin N)) (cyclicLazyWalkKernel N r) := by
  classical
  constructor
  intro A hA hApos x
  -- Proof comment: a positive counting-mass set contains a point; reaching that singleton is
  -- enough because singleton mass is monotone under set inclusion.
  obtain ⟨y, hyA⟩ : A.Nonempty :=
    MeasureTheory.nonempty_of_measure_ne_zero (μ := Measure.count) (ne_of_gt hApos)
  rcases cyclicLazyWalkPositiveSingletonReachability N hN r x y with ⟨n, hn⟩
  refine ⟨n, lt_of_lt_of_le hn ?_⟩
  exact measure_mono (Set.singleton_subset_iff.mpr hyA)

-- Proof sketch: each state has a positive one-step return probability through the holding move,
-- so the period of every state is `1`.
/-- The positive holding probability makes the cyclic lazy walk aperiodic. -/
theorem cyclicLazyWalk_isAperiodic
    (N : ℕ) (_hN : 0 < N) (r : Set.Ioo (0 : ℝ) 1) :
    IsAperiodic (cyclicLazyWalkKernel N r) := by
  intro i
  -- Proof comment: the one-step holding move gives a positive return time `1`, so the only
  -- possible period is `1`.
  have hself : 1 ∈ positiveTransitionStepSet (cyclicLazyWalkKernel N r) i i := by
    rw [mem_positiveTransitionStepSet_iff]
    have hstay : 0 < ENNReal.ofReal (1 - (r : ℝ)) :=
      ENNReal.ofReal_pos.mpr (sub_pos.mpr r.2.2)
    have hle :
        ENNReal.ofReal (1 - (r : ℝ)) ≤ cyclicLazyWalkKernel N r i {i} := by
      rw [cyclicLazyWalkKernel_apply_singleton]
      by_cases hfi : i = finRotate N i
      · have :
            ENNReal.ofReal (1 - (r : ℝ)) ≤
              ENNReal.ofReal (r : ℝ) + ENNReal.ofReal (1 - (r : ℝ)) :=
          le_add_of_nonneg_left bot_le
        rw [cyclicLazyWalkTransitionMatrix_apply]
        rw [if_pos hfi, if_pos rfl]
        exact this
      · simp [cyclicLazyWalkTransitionMatrix, hfi]
    simpa [pow_one] using lt_of_lt_of_le hstay hle
  exact Nat.dvd_one.mp
    (statePeriod_dvd_of_mem_positiveTransitionStepSet (cyclicLazyWalkKernel N r) i hself)

-- Proof sketch: the uniform PMF on `Fin N` gives every state the same mass, namely the reciprocal
-- of the cardinality of `Fin N`.
/-- The uniform invariant distribution assigns mass `N⁻¹` to each singleton of `Fin N`. -/
theorem cyclicLazyWalkInvariantDistribution_apply_singleton
    (N : ℕ) (i : Fin N) :
    (cyclicLazyWalkInvariantDistribution N (fin_pos i) : Measure (Fin N)) {i} =
      (N : ℝ≥0∞)⁻¹ := by
  let _ : NeZero N := ⟨Nat.ne_of_gt (fin_pos i)⟩
  -- Proof comment: unfold the uniform distribution and evaluate the underlying PMF on the
  -- singleton `{i}`.
  change ((PMF.uniformOfFintype (Fin N)).toMeasure) {i} = (N : ℝ≥0∞)⁻¹
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i), PMF.uniformOfFintype_apply]
  simp [Fintype.card_fin]

/-- Helper for Exercise 18.4.5: every column of the cyclic lazy walk transition matrix has total
mass `1`, so the matrix is doubly stochastic on the finite cycle. -/
private theorem cyclicLazyWalkTransitionMatrix_columnSum
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (j : Fin N) :
    ∑ i : Fin N, cyclicLazyWalkTransitionMatrix N r i j = 1 := by
  -- Proof comment: the incoming mass at `j` consists of the predecessor jump and the holding
  -- mass at `j` itself.
  simp_rw [cyclicLazyWalkTransitionMatrix_apply]
  rw [Finset.sum_add_distrib]
  have hpred :
      ∑ i : Fin N, (if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) =
        ENNReal.ofReal (r : ℝ) := by
    simpa using
      (Finset.sum_eq_single_of_mem
        (f := fun i : Fin N ↦ if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0)
        ((finRotate N).symm j) (Finset.mem_univ _) (by
          intro i _ hi
          by_cases hij : j = finRotate N i
          · exfalso
            apply hi
            exact ((finRotate N).symm_apply_eq.mpr hij).symm
          · simp [hij]))
  have hstay :
      ∑ i : Fin N, (if j = i then ENNReal.ofReal (1 - (r : ℝ)) else 0) =
        ENNReal.ofReal (1 - (r : ℝ)) := by
    simpa using
      (Finset.sum_eq_single_of_mem
        (f := fun i : Fin N ↦ if j = i then ENNReal.ofReal (1 - (r : ℝ)) else 0)
        j (Finset.mem_univ _) (by
          intro i _ hi
          exact if_neg hi))
  calc
    (∑ i : Fin N, if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
        (∑ i : Fin N, if j = i then ENNReal.ofReal (1 - (r : ℝ)) else 0) =
      ENNReal.ofReal (r : ℝ) + ENNReal.ofReal (1 - (r : ℝ)) := by rw [hpred, hstay]
    _ = 1 := by
      rw [← ENNReal.ofReal_add]
      · norm_num
      · exact le_of_lt r.2.1
      · linarith [r.2.2]

-- Proof sketch: the transition matrix is circulant, so averaging over all starting states is
-- preserved by one step; equivalently, the uniform law is a left eigenvector with eigenvalue `1`.
/-- The uniform distribution on `Fin N` is invariant for the cyclic lazy walk. -/
theorem cyclicLazyWalkInvariantDistribution_isInvariant
    (N : ℕ) (hN : 0 < N) (r : Set.Ioo (0 : ℝ) 1) :
    Kernel.Invariant (cyclicLazyWalkKernel N r)
      (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)) := by
  rw [Kernel.Invariant]
  refine Measure.ext_of_singleton ?_
  intro j
  -- Proof comment: compare singleton masses and rewrite the kernel action as a finite sum over
  -- the incoming column at `j`.
  rw [Measure.bind_apply (measurableSet_singleton j) (Kernel.aemeasurable _)]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [cyclicLazyWalkKernel_apply_singleton]
  have hunif :
      ∀ i : Fin N,
        (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)) {i} =
          (N : ℝ≥0∞)⁻¹ := fun i ↦ cyclicLazyWalkInvariantDistribution_apply_singleton N i
  simp_rw [hunif]
  have hmass :
      ∑ i : Fin N, cyclicLazyWalkTransitionMatrix N r i j * (N : ℝ≥0∞)⁻¹ =
        (N : ℝ≥0∞)⁻¹ := by
    calc
    ∑ i : Fin N, cyclicLazyWalkTransitionMatrix N r i j * (N : ℝ≥0∞)⁻¹ =
        (∑ i : Fin N, cyclicLazyWalkTransitionMatrix N r i j) * (N : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_mul]
    _ = 1 * (N : ℝ≥0∞)⁻¹ := by
          rw [cyclicLazyWalkTransitionMatrix_columnSum]
    _ = (N : ℝ≥0∞)⁻¹ := by simp
  simp [hmass]

-- Proof sketch: the nontrivial Fourier eigenvalues are `1 - r + r ζ` with `ζ^N = 1` and
-- `ζ ≠ 1`; for `2 ≤ N`, their moduli are strictly less than `1`, and the largest
-- one is the declared rate.
/-- The explicit spectral rate of the cyclic lazy walk is strictly smaller than `1` in the
nontrivial lazy regime. -/
theorem cyclicLazyWalkExponentialRate_lt_one
    (N : ℕ) (hN : 2 ≤ N) (r : Set.Ioo (0 : ℝ) 1) :
    cyclicLazyWalkExponentialRate N r < 1 := by
  have hNpos : 0 < N := pos_of_two_le hN
  have hnot : ¬ N ≤ 1 := by omega
  have hNreal_pos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hone_lt_N : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N from lt_of_lt_of_le (by decide : 1 < 2) hN)
  have hpi_div_pos : 0 < Real.pi / N := by
    exact div_pos Real.pi_pos hNreal_pos
  have hpi_div_lt_pi : Real.pi / N < Real.pi := by
    exact (div_lt_iff₀ hNreal_pos).2 (by nlinarith [Real.pi_pos, hone_lt_N])
  have hsin_pos : 0 < Real.sin (Real.pi / N) :=
    Real.sin_pos_of_pos_of_lt_pi hpi_div_pos hpi_div_lt_pi
  have hsin_sq_pos : 0 < Real.sin (Real.pi / N) ^ 2 := by
    nlinarith [hsin_pos]
  have hcoeff_pos : 0 < 4 * (r : ℝ) * (1 - (r : ℝ)) := by
    nlinarith [r.2.1, r.2.2]
  have hweight_pos : 0 < 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2 := by
    nlinarith [hcoeff_pos, hsin_sq_pos]
  have hweight_le_one : 4 * (r : ℝ) * (1 - (r : ℝ)) ≤ 1 := by
    nlinarith [sq_nonneg (2 * (r : ℝ) - 1)]
  have hsin_sq_le_one : Real.sin (Real.pi / N) ^ 2 ≤ 1 := by
    have hsin_mem : Real.sin (Real.pi / N) ∈ Set.Icc (-1 : ℝ) 1 :=
      Real.sin_mem_Icc (Real.pi / N)
    nlinarith [hsin_mem.1, hsin_mem.2]
  have hrad_nonneg :
      0 ≤ 1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2 := by
    have hmul_le_one :
        4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2 ≤ 1 := by
      nlinarith [hweight_le_one, hsin_sq_le_one]
    nlinarith
  have hrad_lt_one :
      1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2 < 1 := by
    nlinarith
  have hsqrt_lt_one :
      Real.sqrt (1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2) < 1 := by
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2) :=
      Real.sqrt_nonneg _
    have hsq :
        (Real.sqrt (1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2)) ^ 2 =
          1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2 := by
      rw [Real.sq_sqrt hrad_nonneg]
    nlinarith
  -- Proof comment: for `N ≥ 2` the `if` branch defining the rate is the explicit square root,
  -- and the preceding bounds put that square root strictly below `1`.
  simpa [cyclicLazyWalkExponentialRate, hnot] using hsqrt_lt_one

/-- Helper for Exercise 18.4.5: for `N ≥ 2`, the declared exponential rate is given by the
explicit square-root branch. -/
private theorem cyclicLazyWalkExponentialRate_eq_sqrt
    (N : ℕ) (hN : 2 ≤ N) (r : Set.Ioo (0 : ℝ) 1) :
    cyclicLazyWalkExponentialRate N r =
      Real.sqrt (1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2) := by
  have hnot : ¬ N ≤ 1 := by omega
  -- Proof comment: the lower bound `2 ≤ N` rules out the degenerate `if` branch in the
  -- definition of the rate, so only the explicit square-root formula remains.
  simp [cyclicLazyWalkExponentialRate, hnot]

/-- Helper for Exercise 18.4.5: the explicit rate is always nonnegative. -/
private theorem cyclicLazyWalkExponentialRate_nonneg
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) :
    0 ≤ cyclicLazyWalkExponentialRate N r := by
  by_cases hN : N ≤ 1
  · -- Proof comment: on the small-state branch the rate is defined to be `0`.
    simp [cyclicLazyWalkExponentialRate, hN]
  · -- Proof comment: otherwise the rate is a square root, hence nonnegative.
    simp [cyclicLazyWalkExponentialRate, hN, Real.sqrt_nonneg]

/-- Helper for Exercise 18.4.5: every power of the explicit rate is nonnegative. -/
private theorem cyclicLazyWalkExponentialRate_pow_nonneg
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    0 ≤ (cyclicLazyWalkExponentialRate N r) ^ n := by
  -- Proof comment: powers preserve nonnegativity once the base rate is known to be nonnegative.
  exact pow_nonneg (cyclicLazyWalkExponentialRate_nonneg N r) n

/-- Helper for Exercise 18.4.5: every nonzero Fourier mode has sine square at least that of the
first mode. -/
private theorem cyclicLazyWalkSinSq_firstMode_le
    (N : ℕ) (hN : 2 ≤ N) {k : Fin N} (hk : (k : ℕ) ≠ 0) :
    Real.sin (Real.pi / N) ^ 2 ≤ Real.sin (Real.pi * (k : ℝ) / N) ^ 2 := by
  letI : NeZero N := ⟨Nat.ne_of_gt (pos_of_two_le hN)⟩
  have hNpos : 0 < N := pos_of_two_le hN
  have hNreal_pos : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  have hone_lt_N : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N from lt_of_lt_of_le (by decide : 1 < 2) hN)
  have hk_pos : 0 < (k : ℕ) := by
    exact Nat.pos_iff_ne_zero.mpr hk
  have hk_one_le : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hk_pos
  let t : ℝ := Real.pi * (k : ℝ) / N
  have hpi_div_pos : 0 < Real.pi / N := by
    exact div_pos Real.pi_pos hNreal_pos
  have hpi_div_lt_pi : Real.pi / N < Real.pi := by
    exact (div_lt_iff₀ hNreal_pos).2 (by nlinarith [Real.pi_pos, hone_lt_N])
  have hsin_first_nonneg : 0 ≤ Real.sin (Real.pi / N) := by
    exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi hpi_div_pos hpi_div_lt_pi)
  have hk_real_lt_N : (k : ℝ) < N := by
    exact_mod_cast k.2
  have ht_lower : Real.pi / N ≤ t := by
    dsimp [t]
    refine (div_le_iff₀ hNreal_pos).2 ?_
    have hmul : Real.pi * (1 : ℝ) ≤ Real.pi * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hk_one_le (le_of_lt Real.pi_pos)
    simpa using hmul
  have ht_upper :
      t ≤ Real.pi - Real.pi / N := by
    dsimp [t]
    refine (div_le_iff₀ hNreal_pos).2 ?_
    have hk_nat_le : (k : ℕ) ≤ N - 1 := Nat.le_pred_of_lt k.2
    have hk_le' : (k : ℝ) + 1 ≤ N := by
      exact_mod_cast Nat.succ_le_of_lt k.2
    have hk_le : (k : ℝ) ≤ (N : ℝ) - 1 := by
      nlinarith
    have hmul : Real.pi * (k : ℝ) ≤ Real.pi * ((N : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hk_le (le_of_lt Real.pi_pos)
    have hrewrite : (Real.pi - Real.pi / N) * N = Real.pi * ((N : ℝ) - 1) := by
      field_simp [ne_of_gt hNreal_pos]
    rwa [hrewrite]
  by_cases ht_half : t ≤ Real.pi / 2
  · -- Proof comment: on the first half of the circle, `sin` is monotone, so the first mode is
    -- the smallest nonzero one.
    have hsin_le :
        Real.sin (Real.pi / N) ≤ Real.sin t := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith [Real.pi_pos]
      · exact ht_half
      · exact ht_lower
    have hsin_t_nonneg : 0 ≤ Real.sin t := le_trans hsin_first_nonneg hsin_le
    nlinarith [hsin_first_nonneg, hsin_t_nonneg, hsin_le]
  · -- Proof comment: on the second half of the circle, reflect across `π / 2` and use
    -- `sin (π - t) = sin t` to return to the monotone branch.
    let u : ℝ := Real.pi - t
    have hu_lower : Real.pi / N ≤ u := by
      dsimp [u]
      linarith
    have hu_upper : u ≤ Real.pi / 2 := by
      dsimp [u]
      linarith
    have hsin_le :
        Real.sin (Real.pi / N) ≤ Real.sin u := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith [Real.pi_pos]
      · exact hu_upper
      · exact hu_lower
    have hsin_u_nonneg : 0 ≤ Real.sin u := le_trans hsin_first_nonneg hsin_le
    have hsin_eq : Real.sin u = Real.sin t := by
      simp [u, Real.sin_pi_sub]
    nlinarith [hsin_first_nonneg, hsin_u_nonneg, hsin_le, hsin_eq]

/-- Helper for Exercise 18.4.5: every nontrivial Fourier eigenvalue is bounded by the declared
spectral rate. -/
private theorem cyclicLazyWalkFourierEigenvalue_norm_le_rate
    (N : ℕ) (hN : 2 ≤ N) (r : Set.Ioo (0 : ℝ) 1) {k : Fin N} (hk : (k : ℕ) ≠ 0) :
    ‖cyclicLazyWalkFourierEigenvalue N r k‖ ≤ cyclicLazyWalkExponentialRate N r := by
  letI : NeZero N := ⟨Nat.ne_of_gt (pos_of_two_le hN)⟩
  let oneMode : Fin N := ⟨1, by omega⟩
  have hcoeff_nonneg : 0 ≤ 4 * (r : ℝ) * (1 - (r : ℝ)) := by
    nlinarith [r.2.1, sub_pos.mpr r.2.2]
  have hsinSq :
      Real.sin (Real.pi / N) ^ 2 ≤ Real.sin (Real.pi * (k : ℝ) / N) ^ 2 :=
    cyclicLazyWalkSinSq_firstMode_le N hN hk
  have hrad_nonneg :
      0 ≤ 1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2 := by
    simpa [cyclicLazyWalkFourierEigenvalue_normSq, oneMode] using
      (Complex.normSq_nonneg (cyclicLazyWalkFourierEigenvalue N r oneMode))
  have hnormSq_le :
      Complex.normSq (cyclicLazyWalkFourierEigenvalue N r k) ≤
        (cyclicLazyWalkExponentialRate N r) ^ 2 := by
    rw [cyclicLazyWalkFourierEigenvalue_normSq, cyclicLazyWalkExponentialRate_eq_sqrt N hN r,
      Real.sq_sqrt hrad_nonneg]
    nlinarith [hcoeff_nonneg, hsinSq]
  have hsq :
      ‖cyclicLazyWalkFourierEigenvalue N r k‖ ^ 2 ≤
        (cyclicLazyWalkExponentialRate N r) ^ 2 := by
    simpa [Complex.normSq_eq_norm_sq] using hnormSq_le
  exact (sq_le_sq₀ (norm_nonneg _) (cyclicLazyWalkExponentialRate_nonneg N r)).mp hsq

/-- Helper for Exercise 18.4.5: the uniform invariant law stays fixed under every power of the
cyclic lazy walk kernel. -/
private theorem cyclicLazyWalkInvariantDistribution_pow_comp_eq_self
    (N : ℕ) (hN : 0 < N) (r : Set.Ioo (0 : ℝ) 1) :
    ∀ n : ℕ,
      ((cyclicLazyWalkKernel N r) ^ n) ∘ₘ
          (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)) =
        (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the zero-th power is the identity kernel, so it fixes every measure.
      rw [pow_zero]
      exact Measure.id_comp
  | succ n ih =>
      -- Proof comment: rewrite the `(n + 1)`-step law through composition, then use the one-step
      -- invariance of the uniform law followed by the induction hypothesis.
      calc
        ((cyclicLazyWalkKernel N r) ^ (n + 1)) ∘ₘ
            (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)) =
          ((cyclicLazyWalkKernel N r) ^ n) ∘ₘ
            ((cyclicLazyWalkKernel N r) ∘ₘ
              (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N))) := by
              simpa [pow_succ] using
                (MeasureTheory.Measure.comp_assoc
                  (μ := (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)))
                  (κ := cyclicLazyWalkKernel N r)
                  (η := (cyclicLazyWalkKernel N r) ^ n)).symm
      _ = ((cyclicLazyWalkKernel N r) ^ n) ∘ₘ
            (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)) := by
              rw [cyclicLazyWalkInvariantDistribution_isInvariant N hN r]
      _ = (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)) := ih

/-- Helper for Exercise 18.4.5: the singleton masses of the invariant distribution do not depend
on which proof of `0 < N` is used to build the uniform law. -/
private theorem cyclicLazyWalkInvariantDistribution_apply_singleton_of_pos
    (N : ℕ) (hN : 0 < N) (i : Fin N) :
    (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)) {i} =
      (N : ℝ≥0∞)⁻¹ := by
  -- Proof comment: the construction of the uniform law only uses `hN` to supply `NeZero N`, so
  -- the singleton-mass formula from the canonical proof specializes unchanged.
  simpa [cyclicLazyWalkInvariantDistribution] using
    cyclicLazyWalkInvariantDistribution_apply_singleton N i

/-- Helper for Exercise 18.4.5: the real singleton mass of the invariant distribution is `N⁻¹`.
-/
private theorem cyclicLazyWalkInvariantDistribution_realSingleton_eq_inv
    (N : ℕ) (hN : 0 < N) (j : Fin N) :
    ((cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)).real {j}) = (N : ℝ)⁻¹ := by
  -- Proof comment: convert the previously established singleton formula from `ℝ≥0∞` to `ℝ`.
  rw [measureReal_def, cyclicLazyWalkInvariantDistribution_apply_singleton_of_pos N hN j,
    ENNReal.toReal_inv]
  simp

/-- Helper for Exercise 18.4.5: a bounded real test function on a discrete finite-measure space is
integrable. -/
private theorem integrableDiscreteFinite_of_norm_le_one
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ 1) :
    Integrable f μ := by
  -- Proof comment: on a discrete finite-measure space, the uniform `|f| ≤ 1` bound is enough for
  -- integrability.
  refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 1 ?_
  exact ae_of_all _ hf_bound

/-- Helper for Exercise 18.4.5: the `n`-step law started from `x`, reindexed along
`Fin N ≃ ZMod N` and viewed as a complex-valued row function. -/
private def cyclicLazyWalkRow
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (x : Fin N) (n : ℕ) :
    ZMod N → ℂ :=
  fun z ↦ ((((cyclicLazyWalkKernel N r ^ n) x).real {(ZMod.finEquiv N).symm z} : ℝ) : ℂ)

/-- Helper for Exercise 18.4.5: subtracting `1` on `ZMod N` matches the predecessor under
`finRotate`. -/
private theorem cyclicLazyWalkRow_predecessor
    (N : ℕ) [NeZero N] (z : ZMod N) :
    (ZMod.finEquiv N).symm (z - 1) =
      (finRotate N).symm ((ZMod.finEquiv N).symm z) := by
  -- Proof comment: transport the predecessor identity through `ZMod.finEquiv N` and use the
  -- canonical `Fin` predecessor formula for `finRotate`.
  apply (ZMod.finEquiv N).injective
  simp [finRotate_succ_symm_apply]

/-- Helper for Exercise 18.4.5: the reindexed time-zero row is the Dirac mass at the starting
state. -/
private theorem cyclicLazyWalkRow_zero
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (x : Fin N) (z : ZMod N) :
    cyclicLazyWalkRow N r x 0 z =
      if z = (ZMod.finEquiv N) x then 1 else 0 := by
  -- Proof comment: the zero-th kernel iterate is the identity kernel, so only the starting state
  -- contributes to the singleton mass.
  by_cases hz : z = (ZMod.finEquiv N) x
  · subst hz
    have hid : ((1 : Kernel (Fin N) (Fin N)) x) = Measure.dirac x := by
      simpa using (Kernel.id_apply x)
    rw [cyclicLazyWalkRow, pow_zero, hid, measureReal_def]
    simp
  · have hxz : (ZMod.finEquiv N).symm z ≠ x := by
      intro h
      apply hz
      simpa using congrArg (ZMod.finEquiv N) h
    have hid : ((1 : Kernel (Fin N) (Fin N)) x) = Measure.dirac x := by
      simpa using (Kernel.id_apply x)
    rw [cyclicLazyWalkRow, pow_zero, hid, measureReal_def]
    simp [hz, hxz]

/-- Helper for Exercise 18.4.5: translating a row function by `-1` multiplies its discrete Fourier
transform by the standard character at `-k`. -/
private theorem cyclicLazyWalkDft_subOne
    (N : ℕ) [NeZero N] (Φ : ZMod N → ℂ) (k : ZMod N) :
    𝓕 (fun z ↦ Φ (z - 1)) k = ZMod.stdAddChar (-k) * 𝓕 Φ k := by
  -- Proof comment: reindex the DFT sum by `z ↦ z + 1`, then peel off the extra character factor.
  rw [ZMod.dft_apply, ZMod.dft_apply]
  calc
    ∑ z : ZMod N, ZMod.stdAddChar (-(z * k)) * Φ (z - 1)
      = ∑ z : ZMod N, ZMod.stdAddChar (-((z + 1) * k)) * Φ z := by
          refine Fintype.sum_equiv (Equiv.addRight (-1 : ZMod N)) _ _ ?_
          intro z
          simp [sub_eq_add_neg, add_left_comm, add_comm]
    _ = ∑ z : ZMod N, ZMod.stdAddChar (-k) * (ZMod.stdAddChar (-(z * k)) * Φ z) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          have hchar :
              ZMod.stdAddChar (-((z + 1) * k)) =
                ZMod.stdAddChar (-k) * ZMod.stdAddChar (-(z * k)) := by
            calc
              ZMod.stdAddChar (-((z + 1) * k))
                  = ZMod.stdAddChar (-(z * k) + -k) := by
                      congr 1
                      rw [add_mul, one_mul]
                      abel
              _ = ZMod.stdAddChar (-(z * k)) * ZMod.stdAddChar (-k) := by
                      rw [AddChar.map_add_eq_mul]
              _ = ZMod.stdAddChar (-k) * ZMod.stdAddChar (-(z * k)) := by
                      rw [mul_comm]
          rw [hchar]
          simp [mul_assoc]
    _ = ZMod.stdAddChar (-k) * ∑ z : ZMod N, ZMod.stdAddChar (-(z * k)) * Φ z := by
          rw [Finset.mul_sum]

/-- Helper for Exercise 18.4.5: the singleton mass at time `n + 1` is the sum of the holding
mass at `j` and the predecessor jump mass into `j`. -/
private theorem cyclicLazyWalkSingletonMass_succ_real
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (x j : Fin N) (n : ℕ) :
    (((cyclicLazyWalkKernel N r ^ (n + 1)) x).real {j}) =
      (1 - (r : ℝ)) * (((cyclicLazyWalkKernel N r ^ n) x).real {j}) +
        (r : ℝ) * (((cyclicLazyWalkKernel N r ^ n) x).real {(finRotate N).symm j}) := by
  let μn : Measure (Fin N) := (cyclicLazyWalkKernel N r ^ n) x
  -- Proof comment: expand the `(n + 1)`-step singleton mass by Chapman-Kolmogorov and collapse
  -- the finite sum to the only two states that can enter `j`.
  rw [measureReal_def, Kernel.pow_succ_apply_eq_lintegral (cyclicLazyWalkKernel N r) n x
    (measurableSet_singleton j)]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [cyclicLazyWalkKernel_apply_singleton, cyclicLazyWalkTransitionMatrix_apply, add_mul]
  rw [Finset.sum_add_distrib]
  have hjump :
      ∑ y : Fin N,
          (if j = finRotate N y then ENNReal.ofReal (r : ℝ) else 0) * μn {y} =
        ENNReal.ofReal (r : ℝ) * μn {(finRotate N).symm j} := by
    simpa [μn] using
      (Finset.sum_eq_single_of_mem
        (f := fun y : Fin N ↦
          (if j = finRotate N y then ENNReal.ofReal (r : ℝ) else 0) * μn {y})
        ((finRotate N).symm j) (Finset.mem_univ _) (by
          intro y _ hy
          have hij : j ≠ finRotate N y := by
            intro h
            apply hy
            exact ((finRotate N).symm_apply_eq.mpr h).symm
          simp [hij]))
  have hstay :
      ∑ y : Fin N,
          (if j = y then ENNReal.ofReal (1 - (r : ℝ)) else 0) * μn {y} =
        ENNReal.ofReal (1 - (r : ℝ)) * μn {j} := by
    simpa [μn] using
      (Finset.sum_eq_single_of_mem
        (f := fun y : Fin N ↦
          (if j = y then ENNReal.ofReal (1 - (r : ℝ)) else 0) * μn {y})
        j (Finset.mem_univ _) (by
          intro y _ hy
          have hne : j ≠ y := by simpa [eq_comm] using hy
          simp [hne]))
  have hstay_finite :
      ENNReal.ofReal (1 - (r : ℝ)) * μn {j} ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μn _)
  have hjump_finite :
      ENNReal.ofReal (r : ℝ) * μn {(finRotate N).symm j} ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μn _)
  rw [hjump, hstay, add_comm]
  rw [ENNReal.toReal_add hstay_finite hjump_finite, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal, ENNReal.toReal_ofReal, measureReal_def, measureReal_def]
  · exact le_of_lt r.2.1
  · linarith [r.2.2]

/-- Helper for Exercise 18.4.5: after reindexing `Fin N ≃ ZMod N`, the singleton-mass recursion
becomes a translation recursion on the row function. -/
private theorem cyclicLazyWalkRow_reindexed_succ
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (x : Fin N) (n : ℕ) (z : ZMod N) :
    cyclicLazyWalkRow N r x (n + 1) z =
      ((1 - (r : ℝ)) : ℂ) * cyclicLazyWalkRow N r x n z +
        ((r : ℝ) : ℂ) * cyclicLazyWalkRow N r x n (z - 1) := by
  have hmass :=
    congrArg (fun t : ℝ ↦ (t : ℂ))
      (cyclicLazyWalkSingletonMass_succ_real N r x ((ZMod.finEquiv N).symm z) n)
  -- Proof comment: convert the real singleton recursion to `ℂ` and rewrite the predecessor index
  -- using the `Fin N ≃ ZMod N` compatibility from `cyclicLazyWalkRow_predecessor`.
  simpa [cyclicLazyWalkRow, cyclicLazyWalkRow_predecessor, mul_assoc, mul_left_comm, mul_comm]
    using hmass

/-- Helper for Exercise 18.4.5: `ZMod.stdAddChar (-k)` can be rewritten using the canonical `Fin N`
representative of `-k`. -/
private theorem zmodFinEquivSymmNatCast_eq
    (N : ℕ) [NeZero N] (k : ZMod N) :
    ((((ZMod.finEquiv N).symm k : Fin N) : ℕ) : ZMod N) = k := by
  -- Proof comment: `ZMod.finEquiv` is definitionally the identity in the positive-modulus case, so
  -- the canonical `Fin N` representative reduces to `k.val` and `ZMod.natCast_zmod_val` closes the
  -- transport.
  cases N with
  | zero =>
      cases NeZero.ne 0 rfl
  | succ n =>
      -- Proof comment: in the positive-modulus branch, `ZMod.finEquiv` is `RingEquiv.refl`, so
      -- the transported representative is exactly `k.val`.
      change ((k.val : ZMod (n + 1)) = k)
      exact ZMod.natCast_zmod_val k

/-- Helper for Exercise 18.4.5: `ZMod.stdAddChar (-k)` can be rewritten using the canonical `Fin N`
representative of `-k`. -/
private theorem cyclicLazyWalkStdAddChar_finEquivNeg
    (N : ℕ) [NeZero N] (k : ZMod N) :
    ZMod.stdAddChar (-k) =
      ZMod.stdAddChar ((((ZMod.finEquiv N).symm (-k) : Fin N) : ZMod N)) := by
  -- Route correction: prove the transport in the nat-cast coercion world first, then lift it
  -- through `ZMod.stdAddChar` instead of rewriting with `apply_symm_apply`.
  -- Proof comment: the canonical `Fin N` representative of `-k` maps back to the same `ZMod N`
  -- class, so `stdAddChar` takes the same value on both sides.
  exact (congrArg ZMod.stdAddChar (zmodFinEquivSymmNatCast_eq N (-k))).symm

/-- Helper for Exercise 18.4.5: the Fourier multiplier in the `ZMod` row recursion is the same
mode written earlier as `cyclicLazyWalkFourierEigenvalue`. -/
private theorem cyclicLazyWalkDftMode_eq_fourierEigenvalue
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (k : ZMod N) :
    ((1 - (r : ℝ)) : ℂ) + ((r : ℝ) : ℂ) * ZMod.stdAddChar (-k) =
      cyclicLazyWalkFourierEigenvalue N r ((ZMod.finEquiv N).symm (-k)) := by
  -- Proof comment: after transporting the character to the canonical `Fin N` representative of
  -- `-k`, the eigenvalue definition is the same scalar.
  rw [cyclicLazyWalkStdAddChar_finEquivNeg]
  simpa [cyclicLazyWalkFourierEigenvalue, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    congrArg
      (fun z : ℂ => ((1 - (r : ℝ)) : ℂ) + ((r : ℝ) : ℂ) * z)
      (ZMod.stdAddChar_coe (((ZMod.finEquiv N).symm (-k) : Fin N)))

/-- Helper for Exercise 18.4.5: every Fourier mode of the reindexed row evolves by multiplying by
the corresponding cyclic lazy-walk eigenvalue. -/
private theorem cyclicLazyWalkRow_dft_closedForm
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (x : Fin N) :
    ∀ n : ℕ, ∀ k : ZMod N,
      𝓕 (cyclicLazyWalkRow N r x n) k =
        ZMod.stdAddChar (-((ZMod.finEquiv N) x * k)) *
          ((((1 - (r : ℝ)) : ℂ) + ((r : ℝ) : ℂ) * ZMod.stdAddChar (-k)) ^ n) := by
  intro n
  induction n with
  | zero =>
      intro k
      -- Proof comment: at time `0`, the row is the Dirac mass at the starting point, so its DFT
      -- is the standard character evaluated at that point.
      rw [ZMod.dft_apply]
      simp [cyclicLazyWalkRow_zero, mul_comm]
  | succ n ih =>
      intro k
      let row : ZMod N → ℂ := cyclicLazyWalkRow N r x n
      let a : ℂ := ((1 - (r : ℝ)) : ℂ)
      let b : ℂ := ((r : ℝ) : ℂ)
      let eig : ℂ := a + b * ZMod.stdAddChar (-k)
      have hrec :
          cyclicLazyWalkRow N r x (n + 1) =
            fun z ↦ a * row z + b * row (z - 1) := by
        funext z
        simp [row, a, b, cyclicLazyWalkRow_reindexed_succ]
      have hsplit :
          (fun z ↦ a * row z + b * row (z - 1)) =
            (fun z ↦ a * row z) + fun z ↦ b * row (z - 1) := by
        funext z
        simp
      -- Proof comment: linearity of the DFT and the translation lemma turn the recursion into a
      -- scalar recurrence on each Fourier mode.
      rw [hrec, hsplit, LinearEquiv.map_add, ZMod.dft_const_mul, ZMod.dft_const_mul]
      simp only [Pi.add_apply]
      rw [cyclicLazyWalkDft_subOne]
      rw [ih]
      calc
        a * (ZMod.stdAddChar (-((ZMod.finEquiv N) x * k)) * eig ^ n) +
            b * (ZMod.stdAddChar (-k) *
              (ZMod.stdAddChar (-((ZMod.finEquiv N) x * k)) * eig ^ n))
          = ZMod.stdAddChar (-((ZMod.finEquiv N) x * k)) * (a * eig ^ n) +
              ZMod.stdAddChar (-((ZMod.finEquiv N) x * k)) *
                ((b * ZMod.stdAddChar (-k)) * eig ^ n) := by
              ac_rfl
        _ = ZMod.stdAddChar (-((ZMod.finEquiv N) x * k)) *
              ((a * eig ^ n) + ((b * ZMod.stdAddChar (-k)) * eig ^ n)) := by
              rw [← mul_add]
        _ = ZMod.stdAddChar (-((ZMod.finEquiv N) x * k)) *
              ((a + b * ZMod.stdAddChar (-k)) * eig ^ n) := by
              rw [← add_mul]
        _ = ZMod.stdAddChar (-((ZMod.finEquiv N) x * k)) * eig ^ (n + 1) := by
              simp [eig, pow_succ, mul_assoc, mul_comm]

/-- Helper for Exercise 18.4.5: the Fourier summand that appears in the inverse-DFT expansion of
the cyclic lazy walk singleton mass. -/
private def cyclicLazyWalkFourierTerm
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (x j : Fin N) (n : ℕ) :
    ZMod N → ℂ :=
  fun k ↦
    ZMod.stdAddChar (((ZMod.finEquiv N) j) * k) *
      (ZMod.stdAddChar (-((ZMod.finEquiv N) x * k)) *
        ((((1 - (r : ℝ)) : ℂ) + ((r : ℝ) : ℂ) * ZMod.stdAddChar (-k)) ^ n))

/-- Helper for Exercise 18.4.5: inverse discrete Fourier transform reconstructs the singleton mass
from the row Fourier coefficients using the normalized Fourier summand. -/
private theorem cyclicLazyWalkSingletonMass_fourierExpansion
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (x j : Fin N) (n : ℕ) :
    ((((cyclicLazyWalkKernel N r ^ n) x).real {j} : ℝ) : ℂ) =
      (N : ℂ)⁻¹ * ∑ k : ZMod N, cyclicLazyWalkFourierTerm N r x j n k := by
  let zj : ZMod N := (ZMod.finEquiv N) j
  have hinv :
      (𝓕⁻ (𝓕 (cyclicLazyWalkRow N r x n))) zj = cyclicLazyWalkRow N r x n zj := by
    simpa [zj] using
      congrArg (fun Φ : ZMod N → ℂ => Φ zj)
        (LinearEquiv.symm_apply_apply (ZMod.dft (N := N) (E := ℂ)) (cyclicLazyWalkRow N r x n))
  -- Proof comment: evaluate the inverse-DFT identity at the reindexed target state and substitute
  -- the closed form of each Fourier mode.
  simpa [cyclicLazyWalkRow, zj, ZMod.invDFT_apply, cyclicLazyWalkRow_dft_closedForm, smul_eq_mul,
    cyclicLazyWalkFourierTerm, mul_assoc, mul_left_comm, mul_comm] using hinv.symm

/-- Helper for Exercise 18.4.5: the zero Fourier mode of the singleton-mass summand contributes
exactly `1`. -/
private theorem cyclicLazyWalkFourierTerm_zero
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (x j : Fin N) (n : ℕ) :
    cyclicLazyWalkFourierTerm N r x j n (0 : ZMod N) = 1 := by
  -- Proof comment: at Fourier mode `0`, both characters are trivial and the eigenvalue factor is
  -- exactly `1 ^ n`.
  simp [cyclicLazyWalkFourierTerm]

/-- Helper for Exercise 18.4.5: the nonzero-mode remainder is the erased Fourier sum that
measures the singleton-mass deviation from the uniform law. -/
private def cyclicLazyWalkFourierRemainder
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (x j : Fin N) (n : ℕ) : ℂ :=
  Finset.sum (Finset.univ.erase (0 : ZMod N)) (cyclicLazyWalkFourierTerm N r x j n)

/-- Helper for Exercise 18.4.5: the phase characters in a Fourier summand have unit norm, so the
summand norm equals the norm of the eigenvalue power alone. -/
private theorem cyclicLazyWalkFourierTerm_norm_eq_modeNorm
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (x j : Fin N) (n : ℕ) (k : ZMod N) :
    ‖cyclicLazyWalkFourierTerm N r x j n k‖ =
      ‖((((1 - (r : ℝ)) : ℂ) + ((r : ℝ) : ℂ) * ZMod.stdAddChar (-k)) ^ n)‖ := by
  -- Proof comment: both character factors have norm `1`, so only the eigenvalue factor remains
  -- after taking norms.
  simp [cyclicLazyWalkFourierTerm, norm_mul, AddChar.norm_apply]

/-- Helper for Exercise 18.4.5: every nonzero Fourier summand is bounded by the spectral rate
power because the character factors have unit norm. -/
private theorem cyclicLazyWalkFourierTerm_norm_le_ratePow
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (r : Set.Ioo (0 : ℝ) 1) (x j : Fin N) (n : ℕ)
    {k : ZMod N} (hk : k ≠ 0) :
    ‖cyclicLazyWalkFourierTerm N r x j n k‖ ≤ (cyclicLazyWalkExponentialRate N r) ^ n := by
  have hkfin : (((ZMod.finEquiv N).symm (-k) : Fin N) : ℕ) ≠ 0 := by
    intro hk0
    have hfin : ((ZMod.finEquiv N).symm (-k) : Fin N) = 0 := by
      apply Fin.ext
      simpa using hk0
    have hz : (-k : ZMod N) = 0 := by
      simpa using congrArg (ZMod.finEquiv N) hfin
    exact hk (by simpa using hz)
  -- Proof comment: rewrite the mode factor as the explicit eigenvalue, then bound its norm power
  -- by the already established spectral estimate for nonzero modes.
  rw [cyclicLazyWalkFourierTerm_norm_eq_modeNorm, cyclicLazyWalkDftMode_eq_fourierEigenvalue,
    norm_pow]
  exact pow_le_pow_left₀
    (norm_nonneg _)
    (cyclicLazyWalkFourierEigenvalue_norm_le_rate N hN r hkfin) n

/-- Helper for Exercise 18.4.5: the full Fourier sum splits into its zero mode and the erased
nonzero remainder. -/
private theorem cyclicLazyWalkFourierSum_eq_zeroMode_add_remainder
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (x j : Fin N) (n : ℕ) :
    ∑ k : ZMod N, cyclicLazyWalkFourierTerm N r x j n k =
      cyclicLazyWalkFourierTerm N r x j n (0 : ZMod N) +
        cyclicLazyWalkFourierRemainder N r x j n := by
  -- Proof comment: isolate the zero Fourier mode once so later remainder arguments consume a
  -- fixed erased-sum normal form.
  rw [cyclicLazyWalkFourierRemainder]
  simpa [add_comm] using
    (Finset.sum_erase_add
      (s := (Finset.univ : Finset (ZMod N)))
      (a := (0 : ZMod N))
      (f := cyclicLazyWalkFourierTerm N r x j n)
      (by simp)).symm

/-- Helper for Exercise 18.4.5: subtracting the uniform singleton mass isolates the nonzero
Fourier modes in the inverse-DFT expansion. -/
private theorem cyclicLazyWalkSingletonMass_remainderEq
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) (x j : Fin N) (n : ℕ) :
    ((((cyclicLazyWalkKernel N r ^ n) x).real {j} : ℝ) : ℂ) - ((N : ℝ)⁻¹ : ℂ) =
      (N : ℂ)⁻¹ * cyclicLazyWalkFourierRemainder N r x j n := by
  -- Proof comment: use the inverse-DFT formula, split off the zero mode, and cancel the resulting
  -- uniform contribution against `(N : ℝ)⁻¹`.
  calc
    ((((cyclicLazyWalkKernel N r ^ n) x).real {j} : ℝ) : ℂ) - ((N : ℝ)⁻¹ : ℂ)
      = (N : ℂ)⁻¹ *
          (cyclicLazyWalkFourierTerm N r x j n (0 : ZMod N) +
            cyclicLazyWalkFourierRemainder N r x j n) -
          ((N : ℝ)⁻¹ : ℂ) := by
            rw [cyclicLazyWalkSingletonMass_fourierExpansion,
              cyclicLazyWalkFourierSum_eq_zeroMode_add_remainder]
    _ = (N : ℂ)⁻¹ * (1 + cyclicLazyWalkFourierRemainder N r x j n) - ((N : ℝ)⁻¹ : ℂ) := by
          rw [cyclicLazyWalkFourierTerm_zero]
    _ = (N : ℂ)⁻¹ * cyclicLazyWalkFourierRemainder N r x j n := by
          rw [mul_add, mul_one]
          have hInv : ((N : ℂ)⁻¹) = ((N : ℝ)⁻¹ : ℂ) := by
            simp
          rw [hInv]
          ring

/-- Helper for Exercise 18.4.5: the nonzero Fourier remainder is bounded by the number of
nontrivial modes times the spectral rate. -/
private theorem cyclicLazyWalkFourierRemainder_norm_le
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (r : Set.Ioo (0 : ℝ) 1) (x j : Fin N) (n : ℕ) :
    ‖cyclicLazyWalkFourierRemainder N r x j n‖ ≤
      (N - 1 : ℝ) * (cyclicLazyWalkExponentialRate N r) ^ n := by
  -- Proof comment: bound the erased Fourier sum by the sum of the term norms, then use the
  -- uniform nonzero-mode estimate on each summand and count the remaining modes.
  rw [cyclicLazyWalkFourierRemainder]
  calc
    ‖Finset.sum (Finset.univ.erase (0 : ZMod N)) (cyclicLazyWalkFourierTerm N r x j n)‖
      ≤ Finset.sum (Finset.univ.erase (0 : ZMod N))
          (fun k ↦ ‖cyclicLazyWalkFourierTerm N r x j n k‖) := by
          simpa using
            (norm_sum_le
              (s := Finset.univ.erase (0 : ZMod N))
              (f := cyclicLazyWalkFourierTerm N r x j n))
    _ ≤ Finset.sum (Finset.univ.erase (0 : ZMod N))
          (fun _k ↦ (cyclicLazyWalkExponentialRate N r) ^ n) := by
          refine Finset.sum_le_sum ?_
          intro k hk_mem
          exact cyclicLazyWalkFourierTerm_norm_le_ratePow N hN r x j n
            ((Finset.mem_erase.mp hk_mem).1)
    _ = ((Finset.univ.erase (0 : ZMod N)).card : ℝ) * (cyclicLazyWalkExponentialRate N r) ^ n := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (N - 1 : ℝ) * (cyclicLazyWalkExponentialRate N r) ^ n := by
          have hOneLe : (1 : ℕ) ≤ N := by omega
          rw [Finset.card_erase_of_mem (s := (Finset.univ : Finset (ZMod N))) (a := (0 : ZMod N))
            (by simp), Finset.card_univ, ZMod.card, Nat.cast_sub hOneLe]
          norm_num

/-- Helper for Exercise 18.4.5: the `n`-step singleton mass from a fixed start differs from the
uniform mass by at most `((N - 1) / N) * rate^n`. -/
private theorem cyclicLazyWalkSingletonMass_uniformBound
    (N : ℕ) (hN : 2 ≤ N) (r : Set.Ioo (0 : ℝ) 1) :
    ∀ x j : Fin N, ∀ n : ℕ,
      |(((cyclicLazyWalkKernel N r ^ n) x).real {j} - (N : ℝ)⁻¹)|
        ≤ ((N - 1 : ℝ) / N) * (cyclicLazyWalkExponentialRate N r) ^ n := by
  letI : NeZero N := ⟨Nat.ne_of_gt (pos_of_two_le hN)⟩
  intro x j n
  -- Route correction: instead of chasing singleton masses directly in `ℝ`, first rewrite the
  -- gap as one complex remainder term and then apply the finite Fourier bound.
  calc
    |(((cyclicLazyWalkKernel N r ^ n) x).real {j} - (N : ℝ)⁻¹)|
      = ‖((((cyclicLazyWalkKernel N r ^ n) x).real {j} : ℝ) : ℂ) - ((N : ℝ)⁻¹ : ℂ)‖ := by
          have hcast :
              ((((cyclicLazyWalkKernel N r ^ n) x).real {j} - (N : ℝ)⁻¹ : ℝ) : ℂ) =
                ((((cyclicLazyWalkKernel N r ^ n) x).real {j} : ℝ) : ℂ) - ((N : ℝ)⁻¹ : ℂ) := by
            simp
          calc
            |(((cyclicLazyWalkKernel N r ^ n) x).real {j} - (N : ℝ)⁻¹)| =
                ‖((((cyclicLazyWalkKernel N r ^ n) x).real {j} - (N : ℝ)⁻¹ : ℝ) : ℂ)‖ := by
              rw [Complex.norm_real, Real.norm_eq_abs]
            _ = ‖((((cyclicLazyWalkKernel N r ^ n) x).real {j} : ℝ) : ℂ) - ((N : ℝ)⁻¹ : ℂ)‖ := by
              rw [hcast]
    _ = ‖(N : ℂ)⁻¹ * cyclicLazyWalkFourierRemainder N r x j n‖ := by
          rw [cyclicLazyWalkSingletonMass_remainderEq]
    _ ≤ ‖(N : ℂ)⁻¹‖ * ‖cyclicLazyWalkFourierRemainder N r x j n‖ := by
          simpa [norm_mul] using
            (norm_mul_le ((N : ℂ)⁻¹) (cyclicLazyWalkFourierRemainder N r x j n))
    _ ≤ ‖(N : ℂ)⁻¹‖ *
          ((N - 1 : ℝ) * (cyclicLazyWalkExponentialRate N r) ^ n) := by
          gcongr
          exact cyclicLazyWalkFourierRemainder_norm_le N hN r x j n
    _ = ((N - 1 : ℝ) / N) * (cyclicLazyWalkExponentialRate N r) ^ n := by
          rw [show ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ by simp]
          rw [div_eq_mul_inv]
          ring

/-- Helper for Exercise 18.4.5: on a finite discrete state space, composing a Markov kernel with
an initial law turns singleton masses into the corresponding finite weighted row sum. -/
private theorem finiteStateCompMeasure_realSingleton_eq_sum
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (κ : Kernel E E) [IsMarkovKernel κ] (μ : ProbabilityMeasure E) (y : E) :
    (κ ∘ₘ (μ : Measure E)).real {y} =
      ∑ x : E, (μ : Measure E).real {x} * (κ x).real {y} := by
  have hsingleton_le_one : ∀ x : E, κ x {y} ≤ 1 := by
    intro x
    simpa using (measure_mono (by simp : ({y} : Set E) ⊆ Set.univ) : κ x {y} ≤ κ x Set.univ)
  have hsingleton_finite : ∀ᵐ x ∂(μ : Measure E), κ x {y} < ∞ := by
    exact ae_of_all _ fun x ↦ lt_of_le_of_lt (hsingleton_le_one x) (by simp)
  have hrow_integrable : Integrable (fun x : E ↦ (κ x).real {y}) (μ : Measure E) := by
    -- Proof comment: singleton masses stay in `[0,1]`, so the row-mass function is integrable.
    refine integrableDiscreteFinite_of_norm_le_one (μ := (μ : Measure E)) ?_
    intro x
    simpa [Real.norm_eq_abs, abs_of_nonneg MeasureTheory.measureReal_nonneg] using
      (MeasureTheory.measureReal_le_one (μ := κ x) (s := ({y} : Set E)))
  -- Proof comment: evaluate the composed law on `{y}` and rewrite the resulting integral as a
  -- finite sum over the discrete initial distribution.
  calc
    (κ ∘ₘ (μ : Measure E)).real {y}
      = (∫⁻ x, κ x {y} ∂(μ : Measure E)).toReal := by
          rw [measureReal_def, Measure.bind_apply (measurableSet_singleton y)
            (Kernel.aemeasurable _)]
    _ = ∫ x, (κ x).real {y} ∂(μ : Measure E) := by
          symm
          simpa [measureReal_def] using
            (integral_toReal (Measurable.of_discrete.aemeasurable) hsingleton_finite)
    _ = ∑ x : E, (μ : Measure E).real {x} * (κ x).real {y} := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_fintype
              (μ := (μ : Measure E)) (f := fun x : E ↦ (κ x).real {y}) hrow_integrable)

/-- Helper for Exercise 18.4.5: the real singleton masses of a probability measure on a finite
discrete space sum to `1`. -/
private theorem finiteStateProbabilityMeasure_realSingleton_sum_eq_one
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (μ : ProbabilityMeasure E) :
    ∑ x : E, (μ : Measure E).real {x} = 1 := by
  -- Proof comment: summing singleton masses is the integral of the constant function `1`.
  calc
    ∑ x : E, (μ : Measure E).real {x}
      = ∫ x, (1 : ℝ) ∂(μ : Measure E) := by
          symm
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_fintype
              (μ := (μ : Measure E)) (f := fun _ : E ↦ (1 : ℝ)) (integrable_const 1))
    _ = 1 := by simp

/-- Helper for Exercise 18.4.5: subtracting the target singleton mass from a convex combination of
row singleton masses distributes termwise across the finite weights. -/
private theorem finiteStateCompMeasure_singletonGap_sum_eq
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (κ : Kernel E E) (μ π : ProbabilityMeasure E) (y : E) :
    (∑ x : E, (μ : Measure E).real {x} * (κ x).real {y}) - (π : Measure E).real {y} =
      ∑ x : E, (μ : Measure E).real {x} * ((κ x).real {y} - (π : Measure E).real {y}) := by
  have hweights_sum :
      ∑ x : E, (μ : Measure E).real {x} = 1 :=
    finiteStateProbabilityMeasure_realSingleton_sum_eq_one (μ := μ)
  -- Proof comment: rewrite the target singleton mass using the same weights and then distribute
  -- the subtraction through the finite sum.
  calc
    (∑ x : E, (μ : Measure E).real {x} * (κ x).real {y}) - (π : Measure E).real {y}
      = (∑ x : E, (μ : Measure E).real {x} * (κ x).real {y}) -
          ∑ x : E, (μ : Measure E).real {x} * (π : Measure E).real {y} := by
            have hconst :
                ∑ x : E, (μ : Measure E).real {x} * (π : Measure E).real {y} =
                  (π : Measure E).real {y} * ∑ x : E, (μ : Measure E).real {x} := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
            rw [hconst, hweights_sum, mul_one]
    _ = ∑ x : E,
          ((μ : Measure E).real {x} * (κ x).real {y} -
            (μ : Measure E).real {x} * (π : Measure E).real {y}) := by
            rw [← Finset.sum_sub_distrib]
    _ = ∑ x : E, (μ : Measure E).real {x} * ((κ x).real {y} - (π : Measure E).real {y}) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring

/-- Helper for Exercise 18.4.5: on a finite discrete state space, a row-wise singleton-gap bound
persists after averaging over the starting law. -/
private theorem finiteStateCompMeasure_singletonGap_le_of_rowBound
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (κ : Kernel E E) [IsMarkovKernel κ] (μ π : ProbabilityMeasure E) (A : ℝ)
    (hpoint :
      ∀ x y : E, |((κ x).real {y} - (π : Measure E).real {y})| ≤ A) :
    ∀ y : E, |((κ ∘ₘ (μ : Measure E)).real {y} - (π : Measure E).real {y})| ≤ A := by
  intro y
  -- Proof comment: the evolved singleton deviation is a convex combination of the row deviations,
  -- so the row-wise bound survives averaging unchanged.
  calc
    |((κ ∘ₘ (μ : Measure E)).real {y}) - (π : Measure E).real {y}|
      = |∑ x : E, (μ : Measure E).real {x} * ((κ x).real {y} - (π : Measure E).real {y})| := by
          rw [finiteStateCompMeasure_realSingleton_eq_sum (κ := κ) (μ := μ) y,
            finiteStateCompMeasure_singletonGap_sum_eq (κ := κ) (μ := μ) (π := π) y]
    _ ≤ ∑ x : E, |(μ : Measure E).real {x} * ((κ x).real {y} - (π : Measure E).real {y})| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (s := (Finset.univ : Finset E))
              (f := fun x : E ↦
                (μ : Measure E).real {x} * ((κ x).real {y} - (π : Measure E).real {y})))
    _ = ∑ x : E, (μ : Measure E).real {x} * |(κ x).real {y} - (π : Measure E).real {y}| := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [abs_mul, abs_of_nonneg MeasureTheory.measureReal_nonneg]
    _ ≤ ∑ x : E, (μ : Measure E).real {x} * A := by
          refine Finset.sum_le_sum ?_
          intro x hx
          gcongr
          exact hpoint x y
    _ = A * ∑ x : E, (μ : Measure E).real {x} := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
    _ = A := by
          rw [finiteStateProbabilityMeasure_realSingleton_sum_eq_one (μ := μ), mul_one]

/-- Helper for Exercise 18.4.5: on a finite discrete state space, the difference of two bounded
expectations is the singleton-wise weighted sum of the measure gaps. -/
private theorem finiteStateIntegralDiff_eq_singletonSum
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (ρ π : ProbabilityMeasure E) {f : E → ℝ}
    (hρ_int : Integrable f (ρ : Measure E)) (hπ_int : Integrable f (π : Measure E)) :
    ∫ x, f x ∂(ρ : Measure E) - ∫ x, f x ∂(π : Measure E) =
      ∑ y : E, (((ρ : Measure E).real {y} - (π : Measure E).real {y}) * f y) := by
  -- Proof comment: on a finite discrete space, both expectations are finite singleton sums, so
  -- their difference is the termwise difference of those sums.
  rw [MeasureTheory.integral_fintype (μ := (ρ : Measure E)) (f := f) hρ_int,
    MeasureTheory.integral_fintype (μ := (π : Measure E)) (f := f) hπ_int]
  simp_rw [smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro y hy
  ring

/-- Helper for Exercise 18.4.5: every bounded measurable test function is controlled by a uniform
singleton-gap estimate on a finite discrete state space. -/
private theorem finiteStateBoundedTestFunction_gap_le
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (ρ π : ProbabilityMeasure E) (A : ℝ)
    (hsingleton :
      ∀ y : E, |((ρ : Measure E).real {y} - (π : Measure E).real {y})| ≤ A)
    {f : E → ℝ} (hf_meas : Measurable f) (hf_bound : ∀ x, ‖f x‖ ≤ 1) :
    ∫ x, f x ∂(ρ : Measure E) - ∫ x, f x ∂(π : Measure E) ≤ (Fintype.card E : ℝ) * A := by
  have hρ_int : Integrable f (ρ : Measure E) :=
    integrableDiscreteFinite_of_norm_le_one (μ := (ρ : Measure E)) hf_bound
  have hπ_int : Integrable f (π : Measure E) :=
    integrableDiscreteFinite_of_norm_le_one (μ := (π : Measure E)) hf_bound
  -- Proof comment: expand the integral difference into a singleton sum, then use `‖f‖ ≤ 1` and
  -- the uniform singleton-gap bound on each summand.
  calc
    ∫ x, f x ∂(ρ : Measure E) - ∫ x, f x ∂(π : Measure E)
      = ∑ y : E, (((ρ : Measure E).real {y} - (π : Measure E).real {y}) * f y) := by
          rw [finiteStateIntegralDiff_eq_singletonSum (ρ := ρ) (π := π) hρ_int hπ_int]
    _ ≤ ∑ y : E, |(((ρ : Measure E).real {y} - (π : Measure E).real {y}) * f y)| := by
          refine le_trans (le_abs_self _) ?_
          simpa using
            (Finset.abs_sum_le_sum_abs
              (s := (Finset.univ : Finset E))
              (f := fun y : E ↦ ((ρ : Measure E).real {y} - (π : Measure E).real {y}) * f y))
    _ = ∑ y : E, |((ρ : Measure E).real {y} - (π : Measure E).real {y})| * ‖f y‖ := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [abs_mul, Real.norm_eq_abs]
    _ ≤ ∑ y : E, |((ρ : Measure E).real {y} - (π : Measure E).real {y})| * 1 := by
          refine Finset.sum_le_sum ?_
          intro y hy
          gcongr
          exact hf_bound y
    _ ≤ ∑ y : E, A * 1 := by
          refine Finset.sum_le_sum ?_
          intro y hy
          gcongr
          exact hsingleton y
    _ = (Fintype.card E : ℝ) * A := by
          simp [mul_comm]

/-- Helper for Exercise 18.4.5: on a finite discrete state space, a uniform singleton-gap
estimate yields a total-variation estimate through the chapter dual formula. -/
private theorem finiteStateTotalVariation_le_of_singletonGap
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (ρ π : ProbabilityMeasure E) (A : ℝ)
    (hsingleton :
      ∀ y : E, |((ρ : Measure E).real {y} - (π : Measure E).real {y})| ≤ A) :
    totalVariationDistance ρ π ≤ (Fintype.card E : ℝ) * A / 2 := by
  let S : Set ℝ := {r : ℝ | ∃ f : E → ℝ,
    Measurable f ∧ (∀ x, ‖f x‖ ≤ 1) ∧
      r = ∫ x, f x ∂(ρ : Measure E) - ∫ x, f x ∂(π : Measure E)}
  have hzero_mem : 0 ∈ S := by
    -- Proof comment: the zero test function is always admissible in the dual description.
    exact ⟨fun _ : E ↦ 0, measurable_const, by intro x; simp, by simp [S]⟩
  have hupper : ∀ r ∈ S, r ≤ (Fintype.card E : ℝ) * A := by
    intro r hr
    rcases hr with ⟨f, hf_meas, hf_bound, rfl⟩
    exact finiteStateBoundedTestFunction_gap_le
      (ρ := ρ) (π := π) (A := A) hsingleton hf_meas hf_bound
  have hS_nonempty : S.Nonempty := ⟨0, hzero_mem⟩
  have hsSup_le : sSup S ≤ (Fintype.card E : ℝ) * A := by
    exact csSup_le hS_nonempty fun r hr ↦ hupper r hr
  -- Proof comment: the chapter dual formula divides the admissible supremum by `2`.
  rw [totalVariationDistance_eq_sSup_bounded_measurable]
  change sSup S / 2 ≤ (Fintype.card E : ℝ) * A / 2
  nlinarith

/-- Helper for Exercise 18.4.5: a uniform singleton-mass bound for all Dirac starts passes to the
law evolved from an arbitrary initial distribution. -/
private theorem cyclicLazyWalkCompMeasure_singleton_uniformBound
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (μ : ProbabilityMeasure (Fin N))
    (A : ℕ → ℝ)
    (hpoint :
      ∀ x j : Fin N, ∀ n : ℕ,
        |(((cyclicLazyWalkKernel N r ^ n) x).real {j} - (N : ℝ)⁻¹)| ≤ A n) :
    ∀ j : Fin N, ∀ n : ℕ,
      |((((cyclicLazyWalkKernel N r ^ n) ∘ₘ (μ : Measure (Fin N))).real {j}) - (N : ℝ)⁻¹)|
        ≤ A n := by
  have hNpos : 0 < N := by
    obtain ⟨i, -⟩ :
        (Set.univ : Set (Fin N)).Nonempty :=
      MeasureTheory.nonempty_of_measure_ne_zero (μ := (μ : Measure (Fin N))) (by simp)
    exact fin_pos i
  intro j n
  -- Proof comment: rewrite the target singleton mass as the uniform invariant singleton mass
  -- before applying the generic finite-state averaging lemma.
  simpa [cyclicLazyWalkInvariantDistribution_realSingleton_eq_inv N hNpos j] using
    (finiteStateCompMeasure_singletonGap_le_of_rowBound
      (κ := cyclicLazyWalkKernel N r ^ n)
      (μ := μ)
      (π := cyclicLazyWalkInvariantDistribution N hNpos)
      (A := A n)
      (hpoint := fun x y ↦ by
        rw [cyclicLazyWalkInvariantDistribution_realSingleton_eq_inv N hNpos y]
        exact hpoint x y n)
      j)

/-- Helper for Exercise 18.4.5: on the finite state space `Fin N`, a uniform singleton-mass
estimate yields a total-variation estimate by testing against bounded measurable functions. -/
private theorem cyclicLazyWalk_totalVariation_le_of_singletonUniformBound
    (N : ℕ) (ρ π : ProbabilityMeasure (Fin N)) (A : ℝ)
    (hsingleton :
      ∀ j : Fin N,
        |((ρ : Measure (Fin N)).real {j} - (π : Measure (Fin N)).real {j})| ≤ A) :
    totalVariationDistance ρ π ≤ (N : ℝ) * A / 2 := by
  -- Proof comment: invoke the generic finite-state total-variation bridge specialized to `Fin N`.
  simpa [Fintype.card_fin] using
    (finiteStateTotalVariation_le_of_singletonGap
      (ρ := ρ) (π := π) (A := A) hsingleton)

-- Proof sketch: diagonalize the circulant kernel by the Fourier basis on `Fin N`; the nontrivial
-- eigenvalues are `1 - r + r ζ`, so their largest modulus is
-- `cyclicLazyWalkExponentialRate N r`; then translate the spectral estimate to the chapter-owner
-- kernel iterate law.
/-- Exercise 18.4.5: for the lazy cyclic random walk on `Fin N` with forward-jump probability
`r ∈ (0,1)`, the walk is irreducible and aperiodic, the uniform distribution is invariant, and the
convergence to equilibrium is exponential with explicit rate
`cyclicLazyWalkExponentialRate N r`. -/
theorem cyclicLazyWalk_exponentialConvergence
    (N : ℕ) (hN : 2 ≤ N) (r : Set.Ioo (0 : ℝ) 1)
    (μ : ProbabilityMeasure (Fin N)) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ n : ℕ,
          let κn : Kernel (Fin N) (Fin N) := cyclicLazyWalkKernel N r ^ n
          totalVariationDistance
            (⟨κn ∘ₘ (μ : Measure (Fin N)), inferInstance⟩ :
              ProbabilityMeasure (Fin N))
            (cyclicLazyWalkInvariantDistribution N (pos_of_two_le hN))
            ≤ C * (cyclicLazyWalkExponentialRate N r) ^ n := by
  have hNpos : 0 < N := pos_of_two_le hN
  refine ⟨(N - 1 : ℝ) / 2, by
    have hNreal_one_le : (1 : ℝ) ≤ N := by
      exact_mod_cast (show 1 ≤ N from Nat.succ_le_of_lt hNpos)
    nlinarith, ?_⟩
  intro n
  let κn : Kernel (Fin N) (Fin N) := cyclicLazyWalkKernel N r ^ n
  let A : ℝ := ((N - 1 : ℝ) / N) * (cyclicLazyWalkExponentialRate N r) ^ n
  have hA_nonneg : 0 ≤ A := by
    -- Proof comment: both the prefactor `((N - 1) / N)` and the spectral rate power are
    -- nonnegative.
    refine mul_nonneg ?_ (cyclicLazyWalkExponentialRate_pow_nonneg N r n)
    have hNreal_pos : 0 < (N : ℝ) := by exact_mod_cast hNpos
    have hNreal_one_le : (1 : ℝ) ≤ N := by
      exact_mod_cast (show 1 ≤ N from Nat.succ_le_of_lt hNpos)
    exact div_nonneg (sub_nonneg.mpr hNreal_one_le) hNreal_pos.le
  have hsingletons :
      ∀ j : Fin N,
        |((κn ∘ₘ (μ : Measure (Fin N))).real {j} -
            (cyclicLazyWalkInvariantDistribution N hNpos : Measure (Fin N)).real {j})| ≤ A := by
    intro j
    have havg :=
      cyclicLazyWalkCompMeasure_singleton_uniformBound N r μ
        (A := fun m : ℕ ↦
          ((N - 1 : ℝ) / N) * (cyclicLazyWalkExponentialRate N r) ^ m)
        (hpoint := cyclicLazyWalkSingletonMass_uniformBound N hN r)
        j n
    simpa [κn, A, measureReal_def, cyclicLazyWalkInvariantDistribution_apply_singleton_of_pos
      N hNpos j] using havg
  have htv :
      totalVariationDistance
          (⟨κn ∘ₘ (μ : Measure (Fin N)), inferInstance⟩ : ProbabilityMeasure (Fin N))
          (cyclicLazyWalkInvariantDistribution N hNpos)
        ≤ (N : ℝ) * A / 2 :=
    cyclicLazyWalk_totalVariation_le_of_singletonUniformBound
      N
      (ρ := ⟨κn ∘ₘ (μ : Measure (Fin N)), inferInstance⟩)
      (π := cyclicLazyWalkInvariantDistribution N hNpos)
      A hsingletons
  have hNreal_ne : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hNpos
  -- Proof comment: substitute the explicit singleton constant `A` to recover the textbook
  -- convergence factor with prefactor `((N - 1) / 2)`.
  calc
    totalVariationDistance
        (⟨κn ∘ₘ (μ : Measure (Fin N)), inferInstance⟩ : ProbabilityMeasure (Fin N))
        (cyclicLazyWalkInvariantDistribution N hNpos)
      ≤ (N : ℝ) * A / 2 := htv
    _ = ((N - 1 : ℝ) / 2) * (cyclicLazyWalkExponentialRate N r) ^ n := by
          dsimp [A]
          field_simp [hNreal_ne]

end ProbabilityTheory
