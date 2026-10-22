/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Theorem_18_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Theorem_18_9
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/- Layering for Corollary 18.10:
- source-facing conclusion: every bounded harmonic function for an irreducible lattice random walk
  is constant;
- core/canonical owner: the increment law `ν : PMF (LatticePoint d)` and its convolution kernel
  `dirac_convolution_kernel ν.toMeasure`;
- bridge/view: a translation-invariant lattice transition matrix `p`, whose row at the origin
  encodes the common increment law. -/

/-- Helper for Corollary 18.10: the singleton-mass matrix attached to a lattice step law is
translation invariant. -/
lemma diracConvolutionKernel_isTranslationInvariantStepMatrix
    {d : ℕ} (ν : PMF (LatticePoint d)) :
    IsTranslationInvariantStepMatrix
      (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) := by
  intro x y
  -- Both singleton masses are the value of `ν` at the increment `y - x`.
  change dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint d)) =
    dirac_convolution_kernel ν.toMeasure 0 ({y - x} : Set (LatticePoint d))
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage :
      (fun z : LatticePoint d ↦ x + z) ⁻¹' ({y} : Set (LatticePoint d)) = {y - x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hz)
    · intro hz
      exact by simpa [add_comm] using (eq_sub_iff_add_eq.mp hz)
  rw [hpreimage]
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (y - x))]
  simp

/-- Helper for Corollary 18.10: in a translation-invariant stochastic lattice walk, the singleton
transition from `x` to `y` is the origin-row mass at increment `y - x`. -/
lemma translationInvariantOriginRow_step_eq {d : ℕ}
    (p : LatticePoint d → LatticePoint d → ENNReal) (hp : IsStochasticMatrix p)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [IsMarkovKernel (discreteMatrixKernel p)] (x y : LatticePoint d) :
    dirac_convolution_kernel ((discreteMatrixKernel p 0).toPMF.toMeasure) x {y} = p x y := by
  -- Rewrite the translated singleton back to the increment from `x` to `y`.
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage :
      (fun z : LatticePoint d ↦ x + z) ⁻¹' ({y} : Set (LatticePoint d)) = {y - x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hz)
    · intro hz
      exact by simpa [add_comm] using (eq_sub_iff_add_eq.mp hz)
  rw [hpreimage, Measure.toPMF_toMeasure]
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton (y - x))]
  rw [tsum_eq_single (y - x)]
  · simpa [htranslation x y]
  · intro z hz
    simp [Measure.smul_apply, Measure.dirac_apply', Pi.single_apply, hz]

/-- Helper for Corollary 18.10: a translation-invariant discrete lattice kernel is the convolution
kernel driven by its row at the origin. -/
lemma translationInvariantDiscreteKernel_eq_diracConvolutionKernel
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (hp : IsStochasticMatrix p) (htranslation : IsTranslationInvariantStepMatrix p)
    [IsMarkovKernel (discreteMatrixKernel p)] :
    dirac_convolution_kernel ((discreteMatrixKernel p 0).toPMF.toMeasure) =
      discreteMatrixKernel p := by
  ext x s hs
  have hrow :
      dirac_convolution_kernel ((discreteMatrixKernel p 0).toPMF.toMeasure) x =
        discreteMatrixKernel p x := by
    refine Measure.ext_of_singleton ?_
    intro y
    rw [translationInvariantOriginRow_step_eq p hp htranslation x y]
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    rw [tsum_eq_single y]
    · simp
    · intro z hz
      simp [Measure.smul_apply, Measure.dirac_apply', Pi.single_apply, hz]
  exact congrArg (fun μ ↦ μ s) hrow

-- Proof sketch: realize the walk through the canonical convolution kernel determined by the step
-- law `ν`, build the successful coupling at the preceding theorem level, and then apply the
-- bounded-harmonic-function rigidity theorem to conclude that the values at any two starting
-- points coincide.

/-- Helper for Corollary 18.10: `lazyStepMatrix p` adds a one-step self-loop of mass `1 / 2` and
keeps the original step with the remaining mass `1 / 2`. -/
def lazyStepMatrix {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal) :
    LatticePoint d → LatticePoint d → ENNReal :=
  fun x y ↦
    (1 / 2 : ENNReal) * (if y = x then 1 else 0) +
      (1 / 2 : ENNReal) * p x y

/-- Helper for Corollary 18.10: evaluating the lazy row measure on a singleton recovers the
corresponding lazy matrix entry. -/
lemma lazyStepMatrix_row_apply_singleton {d : ℕ}
    (p : LatticePoint d → LatticePoint d → ENNReal)
    (x y : LatticePoint d) :
    (((1 / 2 : ENNReal) • Measure.dirac x) +
      ((1 / 2 : ENNReal) • discreteMatrixKernel p x)) ({y} : Set (LatticePoint d)) =
        lazyStepMatrix p x y := by
  -- Evaluate the two pieces of the convex combination on the singleton `{y}`.
  have hadd :
      (((1 / 2 : ENNReal) • Measure.dirac x) +
        ((1 / 2 : ENNReal) • discreteMatrixKernel p x)) ({y} : Set (LatticePoint d)) =
        ((1 / 2 : ENNReal) • Measure.dirac x) ({y} : Set (LatticePoint d)) +
          ((1 / 2 : ENNReal) • discreteMatrixKernel p x) ({y} : Set (LatticePoint d)) :=
    Measure.add_apply _ _ ({y} : Set (LatticePoint d))
  rw [hadd, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton y),
    discreteMatrixKernel_apply_singleton]
  by_cases hyx : y = x
  · simp [lazyStepMatrix, hyx]
  · simp [lazyStepMatrix, hyx]

/-- Helper for Corollary 18.10: the row of the lazy matrix is the convex combination of the
Dirac mass at the current state and the original row measure. -/
lemma lazyStepMatrix_row_eq {d : ℕ}
    (p : LatticePoint d → LatticePoint d → ENNReal) (x : LatticePoint d) :
    discreteMatrixKernel (lazyStepMatrix p) x =
      (1 / 2 : ENNReal) • Measure.dirac x +
        (1 / 2 : ENNReal) • discreteMatrixKernel p x :=
by
  -- Compare both row measures on singleton sets and use singleton extensionality.
  refine Measure.ext_of_singleton ?_
  intro y
  rw [discreteMatrixKernel_apply_singleton, lazyStepMatrix_row_apply_singleton]

/-- Helper for Corollary 18.10: lazifying a stochastic matrix preserves stochasticity. -/
lemma lazyStepMatrix_isStochastic {d : ℕ}
    (p : LatticePoint d → LatticePoint d → ENNReal) (hp : IsStochasticMatrix p) :
    IsStochasticMatrix (lazyStepMatrix p) := by
  intro x
  -- Evaluate the row identity on `Set.univ`; the two half-masses add back up to `1`.
  have huniv :=
    congrArg (fun μ : Measure (LatticePoint d) ↦ μ Set.univ) (lazyStepMatrix_row_eq p x)
  have hhalf :
      ∑' y : LatticePoint d, lazyStepMatrix p x y = (1 / 2 : ENNReal) + (1 / 2 : ENNReal) := by
    simpa [Measure.add_apply, Measure.smul_apply, hp x] using huniv
  have hsum : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
    simpa [one_div] using ENNReal.inv_two_add_inv_two
  exact hhalf.trans hsum

/-- Helper for Corollary 18.10: lazifying a translation-invariant step matrix keeps translation
invariance. -/
lemma lazyStepMatrix_isTranslationInvariantStepMatrix {d : ℕ}
    (p : LatticePoint d → LatticePoint d → ENNReal)
    (htranslation : IsTranslationInvariantStepMatrix p) :
    IsTranslationInvariantStepMatrix (lazyStepMatrix p) := by
  intro x y
  -- Rewrite the original step part with translation invariance; the added hold term depends only
  -- on whether the increment is `0`.
  rw [lazyStepMatrix, lazyStepMatrix, htranslation x y]
  by_cases hyx : y = x
  · subst hyx
    simp
  · simp [hyx, sub_eq_zero]

/-- Helper for Corollary 18.10: every `n`-step singleton mass of `p` survives in the lazy walk,
up to the factor `(1 / 2)^n`. -/
lemma lazyStepMatrix_pow_apply_singleton_ge {d : ℕ}
    (p : LatticePoint d → LatticePoint d → ENNReal) :
    ∀ n : ℕ, ∀ x y : LatticePoint d,
      ((1 / 2 : ENNReal) ^ n) *
          ((discreteMatrixKernel p ^ n) x ({y} : Set (LatticePoint d))) ≤
        ((discreteMatrixKernel (lazyStepMatrix p) ^ n) x ({y} : Set (LatticePoint d))) := by
  let κ : Kernel (LatticePoint d) (LatticePoint d) := discreteMatrixKernel p
  let η : Kernel (LatticePoint d) (LatticePoint d) := discreteMatrixKernel (lazyStepMatrix p)
  intro n
  induction n with
  | zero =>
      intro x y
      -- At time `0`, both kernels are `Kernel.id`, so the comparison is equality.
      simp [κ, η]
  | succ n ih =>
      intro x y
      have hκ :
          (κ ^ (n + 1)) x ({y} : Set (LatticePoint d)) =
            ∑' z : LatticePoint d, κ z ({y} : Set (LatticePoint d)) *
              (κ ^ n) x ({z} : Set (LatticePoint d)) := by
        rw [Kernel.pow_succ_apply_eq_lintegral κ n x (measurableSet_singleton y)]
        simpa [MeasureTheory.lintegral_countable', mul_comm]
      have hη :
          (η ^ (n + 1)) x ({y} : Set (LatticePoint d)) =
            ∑' z : LatticePoint d, η z ({y} : Set (LatticePoint d)) *
              (η ^ n) x ({z} : Set (LatticePoint d)) := by
        rw [Kernel.pow_succ_apply_eq_lintegral η n x (measurableSet_singleton y)]
        simpa [MeasureTheory.lintegral_countable', mul_comm]
      -- Rewrite both `n + 1` step masses as countable sums over the intermediate state and
      -- compare the summands pointwise.
      calc
        ((1 / 2 : ENNReal) ^ (n + 1)) * (κ ^ (n + 1)) x ({y} : Set (LatticePoint d))
          = ((1 / 2 : ENNReal) ^ (n + 1)) *
              ∑' z : LatticePoint d, κ z ({y} : Set (LatticePoint d)) *
                (κ ^ n) x ({z} : Set (LatticePoint d)) := by
              rw [hκ]
        _ = ∑' z : LatticePoint d,
              ((1 / 2 : ENNReal) * κ z ({y} : Set (LatticePoint d))) *
                (((1 / 2 : ENNReal) ^ n) *
                  (κ ^ n) x ({z} : Set (LatticePoint d))) := by
              rw [← ENNReal.tsum_mul_left]
              refine tsum_congr fun z ↦ ?_
              simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ ∑' z : LatticePoint d, η z ({y} : Set (LatticePoint d)) *
              (η ^ n) x ({z} : Set (LatticePoint d)) := by
              refine ENNReal.tsum_le_tsum ?_
              intro z
              have hstep :
                  (1 / 2 : ENNReal) * κ z ({y} : Set (LatticePoint d)) ≤
                    η z ({y} : Set (LatticePoint d)) := by
                rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
                by_cases hyz : y = z <;> simp [lazyStepMatrix, hyz]
              exact mul_le_mul' hstep (ih x z)
        _ = (η ^ (n + 1)) x ({y} : Set (LatticePoint d)) := by
              rw [hη]

/-- Helper for Corollary 18.10: the lazy walk has a strictly positive one-step self-loop at every
state. -/
lemma lazyStepMatrix_selfLoop_pos {d : ℕ}
    (p : LatticePoint d → LatticePoint d → ENNReal) (x : LatticePoint d) :
    0 < (discreteMatrixKernel (lazyStepMatrix p)) x ({x} : Set (LatticePoint d)) := by
  -- Evaluating the singleton mass at the current state exposes the added hold probability `1 / 2`.
  rw [discreteMatrixKernel_apply_singleton]
  have hhalf : 0 < (1 / 2 : ENNReal) := by norm_num
  exact lt_of_lt_of_le hhalf (by simp [lazyStepMatrix])

/-- Helper for Corollary 18.10: bounded harmonicity for `p` is preserved by lazification. -/
lemma isHarmonic_lazyStepMatrix_of_isHarmonic {d : ℕ}
    (p : LatticePoint d → LatticePoint d → ENNReal) (hp : IsStochasticMatrix p)
    {f : LatticePoint d → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) :
    IsHarmonic (discreteMatrixKernel (lazyStepMatrix p)) f := by
  let η : Kernel (LatticePoint d) (LatticePoint d) := discreteMatrixKernel (lazyStepMatrix p)
  have hηmarkov : IsMarkovKernel η := by
    simpa [η] using
      (discreteMatrixKernel_isMarkovKernel
        (lazyStepMatrix p) (lazyStepMatrix_isStochastic p hp))
  let _ : IsMarkovKernel η := hηmarkov
  obtain ⟨R₀, hR₀⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range f) hf_bdd
  let R : ℝ := max R₀ 1
  have hRbound : ∀ z : LatticePoint d, |f z| ≤ R := by
    intro z
    exact (hR₀ (f z) ⟨z, rfl⟩).trans (le_max_left _ _)
  rcases hf_harmonic with ⟨hint, hharmonic⟩
  refine ⟨?_, ?_⟩
  · intro x
    let _ : IsFiniteMeasure (η x) := by infer_instance
    -- Boundedness controls the integral against the lazy row, which is a probability measure.
    refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) R ?_
    exact ae_of_all _ fun z ↦ hRbound z
  · intro x
    have hdirac :
        Integrable f (((1 / 2 : ENNReal) • Measure.dirac x)) := by
      exact (integrable_dirac (a := x) (f := f) (by simp)).smul_measure (by simp)
    have hkernel :
        Integrable f (((1 / 2 : ENNReal) • discreteMatrixKernel p x)) := by
      exact (hint x).smul_measure (by simp)
    -- Rewrite the lazy row as the sum of the Dirac and original pieces, then use the harmonic
    -- identity for the original walk.
    calc
      f x = (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * ∫ y, f y ∂(discreteMatrixKernel p x) := by
              rw [hharmonic x]
              ring
      _ = ((1 / 2 : ENNReal).toReal • f x) +
            ((1 / 2 : ENNReal).toReal • ∫ y, f y ∂(discreteMatrixKernel p x)) := by
              norm_num [smul_eq_mul]
      _ = ∫ y, f y ∂((1 / 2 : ENNReal) • Measure.dirac x) +
            ∫ y, f y ∂((1 / 2 : ENNReal) • discreteMatrixKernel p x) := by
              rw [integral_smul_measure, integral_smul_measure, integral_dirac]
      _ = ∫ y, f y ∂(((1 / 2 : ENNReal) • Measure.dirac x) +
            ((1 / 2 : ENNReal) • discreteMatrixKernel p x)) := by
              rw [integral_add_measure hdirac hkernel]
      _ = ∫ y, f y ∂(discreteMatrixKernel (lazyStepMatrix p) x) := by
              rw [lazyStepMatrix_row_eq]

/-- Helper for Corollary 18.10: the singleton-mass matrix attached to
`dirac_convolution_kernel ν.toMeasure` recovers the kernel itself. -/
lemma ownerStepMatrix_kernel_eq {d : ℕ} (ν : PMF (LatticePoint d)) :
    discreteMatrixKernel (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) =
      dirac_convolution_kernel ν.toMeasure := by
  -- On the discrete lattice, equality of kernels is determined by singleton masses.
  ext x s hs
  have hrow :
      discreteMatrixKernel (fun a b ↦ dirac_convolution_kernel ν.toMeasure a {b}) x =
        dirac_convolution_kernel ν.toMeasure x := by
    refine Measure.ext_of_singleton ?_
    intro y
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    rw [tsum_eq_single y]
    · simp
    · intro z hz
      simp [Measure.smul_apply, Measure.dirac_apply', hz]
  exact congrArg (fun μ ↦ μ s) hrow

/-- Helper for Corollary 18.10: the singleton-mass matrix of `dirac_convolution_kernel ν.toMeasure`
is stochastic. -/
lemma ownerStepMatrix_isStochastic {d : ℕ} (ν : PMF (LatticePoint d)) :
    IsStochasticMatrix (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) := by
  intro x
  -- The row sum is the total mass of the corresponding kernel row, which is `1`.
  calc
    ∑' y : LatticePoint d, dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint d)) =
        discreteMatrixKernel (fun a b ↦ dirac_convolution_kernel ν.toMeasure a {b}) x Set.univ := by
          exact
            (discreteMatrixKernel_univ
              (K := fun a b ↦ dirac_convolution_kernel ν.toMeasure a {b}) x).symm
    _ = dirac_convolution_kernel ν.toMeasure x Set.univ := by
          rw [ownerStepMatrix_kernel_eq]
    _ = 1 := by
          rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
          rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
          simp

/-- Helper for Corollary 18.10: the lazy owner matrix attached to `ν` admits a successful
coupling once the underlying random walk is irreducible. -/
lemma ownerLazyStepMatrix_hasSuccessfulCoupling
    {d : ℕ} (ν : PMF (LatticePoint d))
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)] :
    HasSuccessfulCoupling
      (lazyStepMatrix (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})) := by
  have hownerKernel :
      discreteMatrixKernel (fun x y ↦ (Measure.dirac x ∗ ν.toMeasure) {y}) =
        dirac_convolution_kernel ν.toMeasure := by
    simpa using ownerStepMatrix_kernel_eq ν
  letI :
      Kernel.IsIrreducible
        (Measure.count : Measure (LatticePoint d))
        (discreteMatrixKernel (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})) := by
    -- Transport irreducibility through the singleton-mass presentation of the owner kernel.
    simpa [hownerKernel] using
      (inferInstance :
        Kernel.IsIrreducible
          (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure))
  letI :
      Kernel.IsIrreducible
        (Measure.count : Measure (LatticePoint d))
        (discreteMatrixKernel
          (lazyStepMatrix (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}))) := by
    constructor
    intro A _ hApos x
    obtain ⟨y, hyA⟩ : A.Nonempty :=
      MeasureTheory.nonempty_of_measure_ne_zero (μ := Measure.count) (ne_of_gt hApos)
    rcases (inferInstance :
        Kernel.IsIrreducible
          (Measure.count : Measure (LatticePoint d))
          (discreteMatrixKernel (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}))).irreducible
        (A := ({y} : Set (LatticePoint d))) (measurableSet_singleton y) (by simp) x with
      ⟨n, hn⟩
    have hhalfpow : (1 / 2 : ENNReal) ^ n ≠ 0 := by
      exact pow_ne_zero n (by norm_num : (1 / 2 : ENNReal) ≠ 0)
    have hscaled :
        0 < ((1 / 2 : ENNReal) ^ n) *
          ((discreteMatrixKernel (fun a b ↦ dirac_convolution_kernel ν.toMeasure a {b}) ^ n)
            x ({y} : Set (LatticePoint d))) := by
      exact ENNReal.mul_pos hhalfpow hn.ne'
    have hlazySingleton :
        0 <
          ((discreteMatrixKernel
              (lazyStepMatrix (fun a b ↦ dirac_convolution_kernel ν.toMeasure a {b})) ^ n)
            x ({y} : Set (LatticePoint d))) := by
      exact lt_of_lt_of_le hscaled
        (lazyStepMatrix_pow_apply_singleton_ge
          (p := fun a b ↦ dirac_convolution_kernel ν.toMeasure a {b}) n x y)
    -- A positive singleton mass inside `A` is enough to reach the whole target set.
    refine ⟨n, lt_of_lt_of_le hlazySingleton ?_⟩
    exact measure_mono (Set.singleton_subset_iff.mpr hyA)
  have haperiodic :
      IsAperiodic
        (discreteMatrixKernel
          (lazyStepMatrix (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}))) := by
    intro x
    -- The lazy walk has a positive one-step self-loop, so every state period divides `1`.
    have hself :
        1 ∈ positiveTransitionStepSet
          (discreteMatrixKernel
            (lazyStepMatrix (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}))) x x := by
      rw [mem_positiveTransitionStepSet_iff]
      simpa [pow_one] using
        lazyStepMatrix_selfLoop_pos
          (p := fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) x
    exact Nat.dvd_one.mp
      (statePeriod_dvd_of_mem_positiveTransitionStepSet
        (discreteMatrixKernel
          (lazyStepMatrix (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}))) x hself)
  -- Route correction: keep the lazy owner matrix explicit in the Theorem 18.8 call so the
  -- transition matrix argument never becomes underconstrained.
  exact translationInvariant_exists_successfulCoupling_of_aperiodic_irreducible_latticeRandomWalk
    (p := lazyStepMatrix (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}))
    (lazyStepMatrix_isStochastic
      (p := fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})
      (ownerStepMatrix_isStochastic ν))
    (lazyStepMatrix_isTranslationInvariantStepMatrix
      (p := fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})
      (diracConvolutionKernel_isTranslationInvariantStepMatrix ν))
    haperiodic

/-- Corollary 18.10 at the owner layer: for an irreducible random walk on `ℤ^d` with increment
law `ν`, every bounded harmonic function for `dirac_convolution_kernel ν.toMeasure` is constant.
-/
theorem bounded_harmonicFunction_constant_of_irreducible_latticeRandomWalk
    {d : ℕ} (ν : PMF (LatticePoint d))
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)]
    {f : LatticePoint d → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (dirac_convolution_kernel ν.toMeasure) f) :
    ∀ x y : LatticePoint d, f x = f y :=
by
  have hownerKernel :
      discreteMatrixKernel (fun x y ↦ (Measure.dirac x ∗ ν.toMeasure) {y}) =
        dirac_convolution_kernel ν.toMeasure := by
    simpa using ownerStepMatrix_kernel_eq ν
  have hownerHarmonic :
      IsHarmonic
        (discreteMatrixKernel (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})) f := by
    -- Rewrite harmonicity through the singleton-mass presentation of the owner kernel.
    simpa [hownerKernel] using hf_harmonic
  have hlazyHarmonic :
      IsHarmonic
        (discreteMatrixKernel
          (lazyStepMatrix (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}))) f := by
    -- Transport bounded harmonicity from the owner walk to its lazy version.
    exact isHarmonic_lazyStepMatrix_of_isHarmonic
      (p := fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})
      (ownerStepMatrix_isStochastic ν) hf_bdd hownerHarmonic
  have hcoupling :
      HasSuccessfulCoupling.{0}
        (lazyStepMatrix (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})) :=
    ownerLazyStepMatrix_hasSuccessfulCoupling.{0} (ν := ν)
  -- Route correction: apply Theorem 18.9 directly to the explicit lazy owner matrix and use the
  -- dedicated coupling helper to keep the theorem argument `p` pinned.
  exact bounded_harmonicFunction_constant_of_hasSuccessfulCoupling
    (p := lazyStepMatrix (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}))
    (hcoupling := hcoupling)
    (f := f) hf_bdd hlazyHarmonic

-- Proof sketch: for a translation-invariant stochastic transition matrix `p`, the common
-- increment law is encoded by the row at the origin,
-- so the owner theorem above applies after reading the walk through that intrinsic law.
/-- Bridge form of Corollary 18.10: for an irreducible translation-invariant stochastic lattice
transition matrix `p`, every bounded harmonic function for `discreteMatrixKernel p` is
constant. -/
theorem translationInvariant_bounded_harmonicFunction_constant_of_irreducible_latticeRandomWalk
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (hp : IsStochasticMatrix p)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    {f : LatticePoint d → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) :
    ∀ x y : LatticePoint d, f x = f y := by
  letI : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hp
  let ν : PMF (LatticePoint d) := (discreteMatrixKernel p 0).toPMF
  have hkernel : discreteMatrixKernel p = dirac_convolution_kernel ν.toMeasure := by
    -- The row at the origin encodes the common increment law of a translation-invariant walk.
    simpa [ν] using
      (translationInvariantDiscreteKernel_eq_diracConvolutionKernel (p := p) hp htranslation).symm
  letI :
      Kernel.IsIrreducible
        (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure) := by
    simpa [hkernel] using
      (inferInstance :
        Kernel.IsIrreducible
          (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p))
  have hf_owner : IsHarmonic (dirac_convolution_kernel ν.toMeasure) f := by
    simpa [hkernel] using hf_harmonic
  -- After rewriting the translation-invariant matrix as its owner convolution kernel, the owner
  -- form of the corollary applies directly.
  simpa [hkernel] using
    bounded_harmonicFunction_constant_of_irreducible_latticeRandomWalk
      (ν := ν) hf_bdd hf_owner

end ProbabilityTheory
