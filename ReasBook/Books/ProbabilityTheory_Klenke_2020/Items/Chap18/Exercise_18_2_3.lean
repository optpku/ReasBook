/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Lemma_2_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_31
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Example_18_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Exercise_18_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Lemma_18_3
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory RealInnerProductSpace ComplexConjugate

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ω' : Type v} [MeasurableSpace Ω']

/-- Helper for Exercise 18.2.3: use `ℕ+` as a discrete counting index for iterated entrances. -/
local instance instMeasurableSpacePNatExercise1823 : MeasurableSpace ℕ+ := ⊤

/-- Helper for Exercise 18.2.3: the counting index `ℕ+` carries the discrete measurable
structure. -/
local instance instDiscreteMeasurableSpacePNatExercise1823 : DiscreteMeasurableSpace ℕ+ where
  forall_measurableSet := by
    intro s
    trivial

/-- Helper for Exercise 18.2.3: the local finite-prefix normalization uses classical equality. -/
local instance instDecidableEqExercise1823 {α : Type*} : DecidableEq α := Classical.decEq α

/-- Helper for Exercise 18.2.3: the canonical embedding of the lattice `ℤ^d` into `ℝ^d`. -/
abbrev latticeEmbedding {d : ℕ} (x : LatticePoint d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ (x i : ℝ))

/- Layering for Exercise 18.2.3:
- source-facing conclusion: for an aperiodic irreducible recurrent lattice random walk, the
  independent coalescent coupling succeeds from every starting pair;
- core/canonical owner: the increment law `ν : PMF (LatticePoint d)` with owner kernel
  `dirac_convolution_kernel ν.toMeasure`;
- bridge/view: a translation-invariant lattice transition matrix `p`, whose row at the origin
  encodes the common increment law. -/

-- Proof sketch: let the two coordinates evolve independently until they meet, and consider their
-- difference process on `ℤ^d`. Translation invariance makes this difference a recurrent random
-- walk, so it hits `0` almost surely from every initial displacement. Once the independent
-- coalescent reaches the diagonal, `independentCoalescentMatrix` keeps the two coordinates
-- together forever, which is exactly the success criterion from Definition 18.5.
/-- Helper for Exercise 18.2.3: the open cube `(-ε, ε)^d` in the Euclidean frequency space
attached to `ℤ^d`. -/
def latticeOpenCube (ε : ℝ) (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {t | ∀ i, |t i| < ε}

/-- Helper for Exercise 18.2.3: membership in `latticeOpenCube ε d` is the defining
coordinatewise bound. -/
theorem mem_latticeOpenCube_iff {ε : ℝ} {d : ℕ} {t : EuclideanSpace ℝ (Fin d)} :
    t ∈ latticeOpenCube ε d ↔ ∀ i, |t i| < ε := by
  -- Proof comment: `latticeOpenCube` was defined by these coordinate inequalities.
  rfl

/-- Helper for Exercise 18.2.3: two lattice points disagree exactly when their difference is
nonzero. -/
theorem latticePoint_ne_iff_sub_ne_zero {d : ℕ} {x y : LatticePoint d} :
    x ≠ y ↔ x - y ≠ 0 := by
  constructor
  · intro hxy hsub
    apply hxy
    exact sub_eq_zero.mp hsub
  · intro hsub hxy
    apply hsub
    exact sub_eq_zero.mpr hxy

/-- Success criterion for Exercise 18.2.3: a Markov coupling is successful when its tail
disagreement probabilities vanish from every starting pair. -/
class IsSuccessfulMarkovCoupling {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (p : E → E → ℝ≥0∞) (P : E × E → ProbabilityMeasure Ω')
    (Z : ℕ → Ω' → E × E) : Prop extends IsMarkovCoupling p P Z where
  /-- The probability of a future disagreement after time `n` tends to zero for every start
  pair `(x, y)`. -/
  tail_disagreement_tendsto_zero : ∀ x y : E,
    Tendsto
      (fun n ↦
        (P (x, y) : Measure Ω') (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}))
      atTop (nhds 0)

/-- Helper for Exercise 18.2.3: the coalescent disagreement event at time `n` is the event that
the difference process is nonzero. -/
theorem coalescentDisagreementEvent_eq_differenceEvent {d : ℕ}
    (Z : ℕ → Ω' → LatticePoint d × LatticePoint d) (n : ℕ) :
    {ω | (Z n ω).1 ≠ (Z n ω).2} =
      {ω | (Z n ω).1 - (Z n ω).2 ≠ 0} := by
  -- Proof comment: rewrite disagreement of the two coordinates as nonvanishing of their
  -- difference and then simplify pointwise.
  ext ω
  change (Z n ω).1 ≠ (Z n ω).2 ↔ (Z n ω).1 - (Z n ω).2 ≠ 0
  exact latticePoint_ne_iff_sub_ne_zero

/-- Helper for Exercise 18.2.3: the tail disagreement event from time `n` onward is exactly the
corresponding tail event for the difference process. -/
theorem coalescentTailDisagreementEvent_eq_differenceTailEvent {d : ℕ}
    (Z : ℕ → Ω' → LatticePoint d × LatticePoint d) (n : ℕ) :
    (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}) =
      ⋃ m ≥ n, {ω | (Z m ω).1 - (Z m ω).2 ≠ 0} := by
  -- Proof comment: rewrite each time-slice event through
  -- `coalescentDisagreementEvent_eq_differenceEvent` and then simplify the indexed union.
  ext ω
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨m, hm, hω⟩
    exact ⟨m, hm, by
      exact latticePoint_ne_iff_sub_ne_zero.mp hω⟩
  · rintro ⟨m, hm, hω⟩
    exact ⟨m, hm, by
      exact latticePoint_ne_iff_sub_ne_zero.mpr hω⟩

/-- Helper for Exercise 18.2.3: the disagreement tail probabilities can be rewritten as the
corresponding tail probabilities of the difference process. -/
theorem coalescentTailDisagreementProb_eq_differenceTailProb {d : ℕ}
    (Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω')
    (Z : ℕ → Ω' → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d) (n : ℕ) :
    (Pcouple (x, y) : Measure Ω') (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}) =
      (Pcouple (x, y) : Measure Ω') (⋃ m ≥ n, {ω | (Z m ω).1 - (Z m ω).2 ≠ 0}) := by
  -- Proof comment: once the underlying sets agree, the corresponding tail probabilities agree as
  -- well.
  rw [coalescentTailDisagreementEvent_eq_differenceTailEvent (Z := Z) n]

/-- Helper for Exercise 18.2.3: the singleton-mass kernel attached to a lattice step law is
translation invariant. -/
lemma diracConvolutionKernel_isTranslationInvariantStepMatrix
    {d : ℕ} (ν : PMF (LatticePoint d)) :
    IsTranslationInvariantStepMatrix
      (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) := by
  intro x y
  -- Proof comment: both singleton masses are the value of `ν` at the same increment `y - x`.
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

/-- Helper for Exercise 18.2.3: the coordinatewise lattice embedding into `ℝ^d` is additive. -/
def latticeEmbeddingAddMonoidHom (d : ℕ) :
    LatticePoint d →+ EuclideanSpace ℝ (Fin d) where
  toFun := latticeEmbedding
  map_zero' := by
    -- Proof comment: the lattice embedding is defined coordinatewise, so the zero vector is
    -- preserved componentwise.
    ext i
    simp [latticeEmbedding]
  map_add' x y := by
    -- Proof comment: additivity is again coordinatewise under the embedding.
    ext i
    simp [latticeEmbedding]

/-- Helper for Exercise 18.2.3: the origin row of a translation-invariant lattice step matrix
reconstructs every singleton transition probability after translation. -/
lemma translationInvariantOriginRow_step_eq
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [IsMarkovKernel (discreteMatrixKernel p)]
    (x y : LatticePoint d) :
    dirac_convolution_kernel ((discreteMatrixKernel p 0).toPMF.toMeasure) x {y} =
      p x y := by
  -- Proof comment: rewrite the convolution row as a translated origin law and identify the unique
  -- preimage point of `{y}` under addition by `x`.
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

/-- Helper for Exercise 18.2.3: a translation-invariant discrete lattice kernel is the
convolution kernel driven by its row at the origin. -/
lemma translationInvariantDiscreteKernel_eq_diracConvolutionKernel
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [IsMarkovKernel (discreteMatrixKernel p)] :
    dirac_convolution_kernel ((discreteMatrixKernel p 0).toPMF.toMeasure) =
      discreteMatrixKernel p := by
  ext x s hs
  have hrow :
      dirac_convolution_kernel ((discreteMatrixKernel p 0).toPMF.toMeasure) x =
        discreteMatrixKernel p x := by
    refine Measure.ext_of_singleton ?_
    intro y
    -- Proof comment: equality on the discrete lattice is determined by singleton masses, and the
    -- previous lemma already identifies those masses.
    rw [translationInvariantOriginRow_step_eq (p := p) htranslation x y]
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    rw [tsum_eq_single y]
    · simp
    · intro z hz
      simp [Measure.smul_apply, Measure.dirac_apply', Pi.single_apply, hz]
  exact congrArg (fun μ ↦ μ s) hrow

/-- Helper for Exercise 18.2.3: the free difference increment law is the distribution of
`U - V` for two independent `ν`-distributed lattice increments. -/
def differenceStepPMF {d : ℕ} (ν : PMF (LatticePoint d)) : PMF (LatticePoint d) :=
  let μ : Measure (LatticePoint d × LatticePoint d) := ν.toMeasure.prod ν.toMeasure
  letI : IsProbabilityMeasure μ := by infer_instance
  letI : IsProbabilityMeasure (μ.map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2)) := by
    exact Measure.isProbabilityMeasure_map (μ := μ) (by fun_prop)
  (μ.map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2)).toPMF

/-- Helper for Exercise 18.2.3: the canonical free difference walk attached to `ν` is again a
translation-invariant lattice step matrix. -/
def differenceStepMatrix {d : ℕ} (ν : PMF (LatticePoint d)) :
    LatticePoint d → LatticePoint d → ENNReal :=
  fun x y ↦ dirac_convolution_kernel (differenceStepPMF ν).toMeasure x {y}

/-- Helper for Exercise 18.2.3: the canonical free difference walk is translation invariant. -/
lemma differenceStepMatrix_isTranslationInvariantStepMatrix
    {d : ℕ} (ν : PMF (LatticePoint d)) :
    IsTranslationInvariantStepMatrix (differenceStepMatrix ν) := by
  intro x y
  -- Proof comment: unfold the owner matrix once and reuse the translation-invariance lemma for
  -- singleton-mass convolution kernels.
  change dirac_convolution_kernel (differenceStepPMF ν).toMeasure x ({y} : Set (LatticePoint d)) =
    dirac_convolution_kernel (differenceStepPMF ν).toMeasure 0 ({y - x} : Set (LatticePoint d))
  exact diracConvolutionKernel_isTranslationInvariantStepMatrix (ν := differenceStepPMF ν) x y

/-- Helper for Exercise 18.2.3: the discrete kernel built from `differenceStepMatrix ν` is the
owner convolution kernel of the difference step law. -/
lemma differenceStepMatrix_kernel_eq_diracConvolutionKernel
    {d : ℕ} (ν : PMF (LatticePoint d)) :
    discreteMatrixKernel (differenceStepMatrix ν) =
      dirac_convolution_kernel (differenceStepPMF ν).toMeasure := by
  -- Proof comment: on the discrete lattice, equality of kernels is determined by singleton
  -- masses, and `differenceStepMatrix` was defined from exactly those singleton masses.
  ext x s hs
  have hrow :
      discreteMatrixKernel (differenceStepMatrix ν) x =
        dirac_convolution_kernel (differenceStepPMF ν).toMeasure x := by
    refine Measure.ext_of_singleton ?_
    intro y
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    rw [tsum_eq_single y]
    · simp [differenceStepMatrix]
    · intro z hz
      simp [Measure.smul_apply, Measure.dirac_apply', hz]
  exact congrArg (fun μ ↦ μ s) hrow

/-- Helper for Exercise 18.2.3: the free difference step matrix is stochastic. -/
lemma differenceStepMatrix_isStochastic
    {d : ℕ} (ν : PMF (LatticePoint d)) :
    IsStochasticMatrix (differenceStepMatrix ν) := by
  intro x
  -- Proof comment: the row sum is the total mass of the corresponding convolution-kernel row,
  -- which is `1` because the difference step law is a probability measure.
  calc
    ∑' y : LatticePoint d, differenceStepMatrix ν x y =
        discreteMatrixKernel (differenceStepMatrix ν) x Set.univ := by
          simpa [discreteMatrixKernel_univ]
    _ = dirac_convolution_kernel (differenceStepPMF ν).toMeasure x Set.univ := by
      rw [differenceStepMatrix_kernel_eq_diracConvolutionKernel]
    _ = 1 := by
      simp

/-- Helper for Exercise 18.2.3: the difference step law is the convolution of `ν` with the
reflected law `x ↦ -x`. -/
lemma differenceStepPMF_toMeasure_eq_conv_map_neg
    {d : ℕ} (ν : PMF (LatticePoint d)) :
    (differenceStepPMF ν).toMeasure =
      ν.toMeasure ∗ (ν.toMeasure.map (fun x : LatticePoint d ↦ -x)) := by
  -- Proof comment: rewrite `(u, v) ↦ u - v` as addition after negating the second coordinate,
  -- then identify the pushed-forward product measure with the corresponding convolution.
  rw [differenceStepPMF, Measure.toPMF_toMeasure]
  calc
    (ν.toMeasure.prod ν.toMeasure).map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2) =
        ((ν.toMeasure.prod ν.toMeasure).map
          (Prod.map id (fun x : LatticePoint d ↦ -x))).map
          (fun s : LatticePoint d × LatticePoint d ↦ s.1 + s.2) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
    _ =
        (ν.toMeasure.prod (ν.toMeasure.map (fun x : LatticePoint d ↦ -x))).map
          (fun s : LatticePoint d × LatticePoint d ↦ s.1 + s.2) := by
            congr 1
            simpa [Measure.map_id] using
              (Measure.map_prod_map
                (μa := ν.toMeasure) (μc := ν.toMeasure)
                (f := id) (g := fun x : LatticePoint d ↦ -x)
                (by fun_prop) (by fun_prop)).symm
    _ = ν.toMeasure ∗ (ν.toMeasure.map (fun x : LatticePoint d ↦ -x)) := by
          rfl

/-- Helper for Exercise 18.2.3: the characteristic function of the difference step law is
`φ(t) * conj φ(t)` for the base characteristic function `φ`. -/
lemma differenceStepPMF_charFun_eq_mul_conj
    {d : ℕ} (ν : PMF (LatticePoint d))
    (t : EuclideanSpace ℝ (Fin d)) :
    charFun ((differenceStepPMF ν).toMeasure.map latticeEmbedding) t =
      charFun (ν.toMeasure.map latticeEmbedding) t *
        conj (charFun (ν.toMeasure.map latticeEmbedding) t) := by
  have hnegMap :
      ((ν.toMeasure.map (fun x : LatticePoint d ↦ -x)).map latticeEmbedding) =
        ((ν.toMeasure.map latticeEmbedding).map fun x : EuclideanSpace ℝ (Fin d) ↦ (-1 : ℝ) • x) := by
    -- Proof comment: negating a lattice point and then embedding is the same as embedding first
    -- and then scaling by `-1` in the Euclidean target.
    have hcomp :
        latticeEmbedding ∘ (fun x : LatticePoint d ↦ -x) =
          (fun x : EuclideanSpace ℝ (Fin d) ↦ (-1 : ℝ) • x) ∘ latticeEmbedding := by
      funext x
      ext i
      simp [latticeEmbedding]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rw [hcomp]
  -- Proof comment: transport the convolution identity through the additive lattice embedding,
  -- then use `charFun_conv` and identify the reflected factor with the complex conjugate.
  rw [differenceStepPMF_toMeasure_eq_conv_map_neg]
  have hmapconv :
      Measure.map latticeEmbedding (ν.toMeasure ∗ Measure.map (fun x : LatticePoint d ↦ -x) ν.toMeasure) =
        (Measure.map latticeEmbedding ν.toMeasure) ∗
          Measure.map latticeEmbedding (Measure.map (fun x : LatticePoint d ↦ -x) ν.toMeasure) := by
    simpa [latticeEmbeddingAddMonoidHom] using
      (Measure.map_conv_addMonoidHom
        (μ := ν.toMeasure)
        (ν := Measure.map (fun x : LatticePoint d ↦ -x) ν.toMeasure)
        (latticeEmbeddingAddMonoidHom d) (by fun_prop))
  rw [hmapconv]
  rw [MeasureTheory.charFun_conv]
  congr 1
  calc
    charFun (((ν.toMeasure.map (fun x : LatticePoint d ↦ -x)).map latticeEmbedding)) t =
        charFun
          (((ν.toMeasure.map latticeEmbedding).map
            fun x : EuclideanSpace ℝ (Fin d) ↦ (-1 : ℝ) • x)) t := by
              rw [hnegMap]
    _ = charFun (ν.toMeasure.map latticeEmbedding) ((-1 : ℝ) • t) := by
          simpa using
            (MeasureTheory.charFun_map_smul
              (μ := ν.toMeasure.map latticeEmbedding) (-1) t)
    _ = charFun (ν.toMeasure.map latticeEmbedding) (-t) := by
          simp
    _ = conj (charFun (ν.toMeasure.map latticeEmbedding) t) := by
          exact MeasureTheory.charFun_neg t

/-- Helper for Exercise 18.2.3: composing `dirac_convolution_kernel ν` with a measure `μ`
recovers the additive convolution `μ ∗ ν`. -/
lemma diracConvolutionKernel_comp_measure_eq_conv {d : ℕ}
    (μ ν : Measure (LatticePoint d)) [SFinite μ] [SFinite ν] :
    dirac_convolution_kernel ν ∘ₘ μ = μ ∗ ν := by
  -- Proof comment: evaluate the kernel-level constant-composition identity at the origin row.
  have hconst :=
    congrArg
      (fun κ : Kernel (LatticePoint d) (LatticePoint d) ↦ κ (0 : LatticePoint d))
      (dirac_convolution_kernel_comp_const_eq_const_conv (μ := μ) (ν := ν))
  simpa [Kernel.comp_apply] using hconst


/-- Helper for Exercise 18.2.3: after `n` steps, the row of a translation kernel is the
translation of the `n`-step law started from the origin. -/
lemma diracConvolutionKernel_pow_apply_eq_diracConv_origin
    {d : ℕ} (μ : Measure (LatticePoint d)) :
    ∀ n : ℕ, ∀ x : LatticePoint d,
      ((dirac_convolution_kernel μ ^ n) x) =
        (Measure.dirac x) ∗ ((dirac_convolution_kernel μ ^ n) (0 : LatticePoint d)) :=
  fun n ↦ by
    induction n with
    | zero =>
        intro x
        -- Proof comment: the zero-step law is the starting Dirac mass.
        change Measure.dirac x = Measure.dirac x ∗ Measure.dirac (0 : LatticePoint d)
        simp
    | succ n ih =>
        intro x
        let κ : Kernel (LatticePoint d) (LatticePoint d) := dirac_convolution_kernel μ
        have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
          simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
        -- Proof comment: evolve the translated `n`-step law by one more convolution step and
        -- reassociate the convolution product.
        calc
          (κ ^ (n + 1)) x = κ ∘ₘ ((κ ^ n) x) := by
            rw [hpow, Kernel.comp_apply]
          _ = ((κ ^ n) x) ∗ μ := by
            simpa [κ] using
              (diracConvolutionKernel_comp_measure_eq_conv
                (μ := (κ ^ n) x) (ν := μ))
          _ = (Measure.dirac x ∗ ((κ ^ n) (0 : LatticePoint d))) ∗ μ := by
            rw [ih x]
          _ = Measure.dirac x ∗ (((κ ^ n) (0 : LatticePoint d)) ∗ μ) := by
            rw [Measure.conv_assoc]
          _ = Measure.dirac x ∗ ((κ ^ (n + 1)) (0 : LatticePoint d)) := by
            congr 1
            calc
              ((κ ^ n) (0 : LatticePoint d)) ∗ μ = κ ∘ₘ ((κ ^ n) (0 : LatticePoint d)) := by
                symm
                simpa [κ] using
                  (diracConvolutionKernel_comp_measure_eq_conv
                    (μ := (κ ^ n) (0 : LatticePoint d)) (ν := μ))
              _ = (κ ∘ₖ (κ ^ n)) (0 : LatticePoint d) := by
                rw [Kernel.comp_apply]
              _ = (κ ^ (n + 1)) (0 : LatticePoint d) := by
                rw [← hpow]

/-- Helper for Exercise 18.2.3: the `n`-step singleton mass of a translation kernel depends only
on the displacement `y - x`. -/
lemma diracConvolutionKernel_pow_apply_singleton_eq_originMass
    {d : ℕ} (μ : Measure (LatticePoint d)) (n : ℕ)
    (x y : LatticePoint d) :
    ((dirac_convolution_kernel μ ^ n) x) ({y} : Set (LatticePoint d)) =
      ((dirac_convolution_kernel μ ^ n) (0 : LatticePoint d)) ({y - x} : Set (LatticePoint d)) := by
  -- Proof comment: rewrite the `x`-row as a translated origin law and compute the singleton
  -- preimage under addition by `x`.
  rw [diracConvolutionKernel_pow_apply_eq_diracConv_origin (μ := μ) n x]
  rw [Measure.dirac_conv]
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

/-- Helper for Exercise 18.2.3: one more step of a translation kernel convolves the current
origin law with the step measure. -/
lemma diracConvolutionKernel_pow_apply_origin_succ
    {d : ℕ} (μ : Measure (LatticePoint d)) (n : ℕ) :
    ((dirac_convolution_kernel μ ^ (n + 1)) (0 : LatticePoint d)) =
      ((dirac_convolution_kernel μ ^ n) (0 : LatticePoint d)) ∗ μ := by
  let κ : Kernel (LatticePoint d) (LatticePoint d) := dirac_convolution_kernel μ
  have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
    simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
  -- Proof comment: one more kernel step composes the current origin law with the common step
  -- measure, which is exactly convolution by `μ`.
  calc
    ((κ ^ (n + 1)) (0 : LatticePoint d)) = κ ∘ₘ ((κ ^ n) (0 : LatticePoint d)) := by
      rw [hpow, Kernel.comp_apply]
    _ = ((κ ^ n) (0 : LatticePoint d)) ∗ μ := by
      simpa [κ] using
        (diracConvolutionKernel_comp_measure_eq_conv
          (μ := (κ ^ n) (0 : LatticePoint d)) (ν := μ))

/-- Helper for Exercise 18.2.3: the `n`-step origin law of the free difference walk is the
convolution of the base `n`-step origin law with its reflected image. -/
lemma differenceKernelPow_origin_eq_conv_originLaw
    {d : ℕ} (ν : PMF (LatticePoint d)) :
    ∀ n : ℕ,
      ((dirac_convolution_kernel (differenceStepPMF ν).toMeasure ^ n) (0 : LatticePoint d)) =
        ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint d)) ∗
          (((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint d)).map
            (fun x : LatticePoint d ↦ -x)) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: at time `0`, both the free difference walk and the base walk start from
      -- the origin Dirac mass.
      change Measure.dirac (0 : LatticePoint d) =
        Measure.dirac (0 : LatticePoint d) ∗
          (Measure.dirac (0 : LatticePoint d)).map (fun x : LatticePoint d ↦ -x)
      simp
  | succ n ih =>
      let μn : Measure (LatticePoint d) :=
        ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint d))
      let negHom : LatticePoint d →+ LatticePoint d :=
        { toFun := fun x ↦ -x
          map_zero' := by simp
          map_add' := by
            intro x y
            simpa using neg_add x y }
      have hmap :
          (μn ∗ ν.toMeasure).map (fun x : LatticePoint d ↦ -x) =
            (μn.map (fun x : LatticePoint d ↦ -x)) ∗
              (ν.toMeasure.map (fun x : LatticePoint d ↦ -x)) := by
        -- Proof comment: reflection is an additive homomorphism, so it distributes over
        -- convolution.
        simpa [μn, negHom] using
          (Measure.map_conv_addMonoidHom
            (μ := μn) (ν := ν.toMeasure) negHom (by fun_prop))
      have hbaseSucc :
          ((dirac_convolution_kernel ν.toMeasure ^ (n + 1)) (0 : LatticePoint d)) =
            μn ∗ ν.toMeasure := by
        -- Proof comment: one extra base step convolves the `n`-step origin law with `ν`.
        simpa [μn] using
          (diracConvolutionKernel_pow_apply_origin_succ (μ := ν.toMeasure) n)
      -- Proof comment: evolve both independent coordinates by one more `ν`-step and regroup the
      -- resulting convolution factors into the reflected `(n + 1)`-step origin law.
      calc
        ((dirac_convolution_kernel (differenceStepPMF ν).toMeasure ^ (n + 1))
            (0 : LatticePoint d)) =
            (μn ∗ (μn.map (fun x : LatticePoint d ↦ -x))) ∗
              (ν.toMeasure ∗ (ν.toMeasure.map (fun x : LatticePoint d ↦ -x))) := by
              rw [diracConvolutionKernel_pow_apply_origin_succ, ih,
                differenceStepPMF_toMeasure_eq_conv_map_neg]
        _ = μn ∗ ((μn.map (fun x : LatticePoint d ↦ -x)) ∗
              (ν.toMeasure ∗ (ν.toMeasure.map (fun x : LatticePoint d ↦ -x)))) := by
              rw [Measure.conv_assoc]
        _ = μn ∗ (((μn.map (fun x : LatticePoint d ↦ -x)) ∗ ν.toMeasure) ∗
              (ν.toMeasure.map (fun x : LatticePoint d ↦ -x))) := by
              congr 1
              rw [← Measure.conv_assoc]
        _ = μn ∗ (((ν.toMeasure ∗ (μn.map (fun x : LatticePoint d ↦ -x)))) ∗
              (ν.toMeasure.map (fun x : LatticePoint d ↦ -x))) := by
              congr 1
              rw [Measure.conv_comm (μn.map (fun x : LatticePoint d ↦ -x)) ν.toMeasure]
        _ = ((μn ∗ ν.toMeasure) ∗
              (μn.map (fun x : LatticePoint d ↦ -x))) ∗
              (ν.toMeasure.map (fun x : LatticePoint d ↦ -x)) := by
              rw [← Measure.conv_assoc, ← Measure.conv_assoc]
        _ = (μn ∗ ν.toMeasure) ∗
              ((μn.map (fun x : LatticePoint d ↦ -x)) ∗
                (ν.toMeasure.map (fun x : LatticePoint d ↦ -x))) := by
              rw [Measure.conv_assoc]
        _ = (μn ∗ ν.toMeasure) ∗ ((μn ∗ ν.toMeasure).map (fun x : LatticePoint d ↦ -x)) := by
              rw [← hmap]
        _ = ((dirac_convolution_kernel ν.toMeasure ^ (n + 1)) (0 : LatticePoint d)) ∗
              (((dirac_convolution_kernel ν.toMeasure ^ (n + 1)) (0 : LatticePoint d)).map
                (fun x : LatticePoint d ↦ -x)) := by
              rw [hbaseSucc]

/-- Helper for Exercise 18.2.3: a translation-invariant lattice kernel is irreducible once every
displacement can reach `0` with positive probability in finitely many steps. -/
lemma translationInvariant_isIrreducible_of_reachesZero
    {d : ℕ} (q : LatticePoint d → LatticePoint d → ENNReal)
    (htranslation : IsTranslationInvariantStepMatrix q)
    [IsMarkovKernel (discreteMatrixKernel q)]
    (hzero :
      ∀ z : LatticePoint d,
        ∃ n : ℕ, 0 < n ∧ 0 < (discreteMatrixKernel q ^ n) z ({0} : Set (LatticePoint d))) :
    Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel q) := by
  let ν : Measure (LatticePoint d) := ((discreteMatrixKernel q 0).toPMF.toMeasure)
  have hkernel :
      discreteMatrixKernel q = dirac_convolution_kernel ν := by
    -- Proof comment: a translation-invariant discrete kernel is determined by its origin row.
    symm
    simpa [ν] using
      translationInvariantDiscreteKernel_eq_diracConvolutionKernel
        (p := q) htranslation
  refine ⟨?_⟩
  intro A hA hApos x
  rcases MeasureTheory.nonempty_of_measure_ne_zero
      (μ := (Measure.count : Measure (LatticePoint d))) (ne_of_gt hApos) with ⟨y, hyA⟩
  rcases hzero (x - y) with ⟨n, hnpos, hreach⟩
  have hxy :
      ((dirac_convolution_kernel ν ^ n) x) ({y} : Set (LatticePoint d)) =
        ((dirac_convolution_kernel ν ^ n) (x - y)) ({0} : Set (LatticePoint d)) := by
    -- Proof comment: both singleton masses are the same translated origin mass.
    calc
      ((dirac_convolution_kernel ν ^ n) x) ({y} : Set (LatticePoint d)) =
          ((dirac_convolution_kernel ν ^ n) (0 : LatticePoint d)) ({y - x} : Set (LatticePoint d)) := by
            simpa using
              diracConvolutionKernel_pow_apply_singleton_eq_originMass
                (μ := ν) n x y
      _ =
          ((dirac_convolution_kernel ν ^ n) (x - y)) ({0} : Set (LatticePoint d)) := by
            symm
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
              diracConvolutionKernel_pow_apply_singleton_eq_originMass
                (μ := ν) n (x - y) (0 : LatticePoint d)
  have hreach' :
      0 < ((dirac_convolution_kernel ν ^ n) (x - y)) ({0} : Set (LatticePoint d)) := by
    simpa [hkernel] using hreach
  have hy_singleton_pos :
      0 < ((discreteMatrixKernel q ^ n) x) ({y} : Set (LatticePoint d)) := by
    have hy_singleton_pos' :
        0 < ((dirac_convolution_kernel ν ^ n) x) ({y} : Set (LatticePoint d)) := by
      rw [hxy]
      exact hreach'
    simpa [hkernel] using hy_singleton_pos'
  refine ⟨n, lt_of_lt_of_le hy_singleton_pos ?_⟩
  exact measure_mono (show ({y} : Set (LatticePoint d)) ⊆ A from Set.singleton_subset_iff.2 hyA)

/-- Helper for Exercise 18.2.3: aperiodicity forces every sufficiently large time to carry
positive mass from `0` to any fixed state. -/
lemma aperiodicEventuallyPositiveTimeToState
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    [IsMarkovKernel (discreteMatrixKernel p)]
    [Kernel.IsIrreducible (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    (haperiodic : IsAperiodic (discreteMatrixKernel p))
    (z : LatticePoint d) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < (discreteMatrixKernel p ^ n) (0 : LatticePoint d) ({z} : Set (LatticePoint d)) := by
  let κ : Kernel (LatticePoint d) (LatticePoint d) := discreteMatrixKernel p
  rcases exists_eventual_period_residue (κ := κ) (0 : LatticePoint d) z with
    ⟨L, hLlt, hLeventual⟩
  have hperiod :
      statePeriod κ (0 : LatticePoint d) = 1 := haperiodic (0 : LatticePoint d)
  have hLzero : L = 0 := by
    have hLle0 : L ≤ 0 := Nat.lt_succ_iff.mp (by simpa [hperiod] using hLlt)
    exact Nat.eq_zero_of_le_zero hLle0
  rcases (hasEventualPeriodResidue_iff κ (0 : LatticePoint d) z L).1 hLeventual with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hmem :
      n * statePeriod κ (0 : LatticePoint d) + L ∈ positiveTransitionStepSet κ (0 : LatticePoint d) z :=
    hN n hn
  simpa [κ, hperiod, hLzero, mem_positiveTransitionStepSet_iff] using hmem

/-- Helper for Exercise 18.2.3: the free difference walk attached to the origin row of `p`
reaches `0` from every displacement with positive finite-time probability. -/
lemma differenceStepMatrix_reachesZero
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    [IsMarkovKernel (discreteMatrixKernel p)]
    [Kernel.IsIrreducible (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    (htranslation : IsTranslationInvariantStepMatrix p)
    (haperiodic : IsAperiodic (discreteMatrixKernel p)) :
    ∀ z : LatticePoint d,
      ∃ n : ℕ, 0 < n ∧ 0 < (discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^ n) z
        ({0} : Set (LatticePoint d)) := by
  intro z
  let ν0 : PMF (LatticePoint d) := (discreteMatrixKernel p 0).toPMF
  let μn : ℕ → Measure (LatticePoint d) :=
    fun n ↦ ((discreteMatrixKernel p ^ n) (0 : LatticePoint d))
  rcases aperiodicEventuallyPositiveTimeToState (p := p) haperiodic (0 : LatticePoint d) with
    ⟨N0, hN0⟩
  rcases aperiodicEventuallyPositiveTimeToState (p := p) haperiodic z with ⟨Nz, hNz⟩
  let n : ℕ := max N0 Nz + 1
  have hn_pos : 0 < n := by
    exact Nat.succ_pos _
  have hn_ge_zero : N0 ≤ n := by
    exact le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
  have hn_ge_z : Nz ≤ n := by
    exact le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  have hmass_zero :
      0 < μn n ({0} : Set (LatticePoint d)) := by
    exact hN0 n hn_ge_zero
  have hmass_z :
      0 < μn n ({z} : Set (LatticePoint d)) := by
    exact hNz n hn_ge_z
  have hμn :
      ((dirac_convolution_kernel ν0.toMeasure ^ n) (0 : LatticePoint d)) = μn n := by
    -- Proof comment: the base kernel agrees with the convolution kernel driven by the origin row,
    -- so their `n`-step origin laws coincide.
    simpa [ν0, μn] using
      congrArg
        (fun κ : Kernel (LatticePoint d) (LatticePoint d) ↦
          (κ ^ n) (0 : LatticePoint d))
        (translationInvariantDiscreteKernel_eq_diracConvolutionKernel
          (p := p) htranslation)
  have htranslate :
      ((discreteMatrixKernel (differenceStepMatrix ν0) ^ n) z) ({0} : Set (LatticePoint d)) =
        ((discreteMatrixKernel (differenceStepMatrix ν0) ^ n) (0 : LatticePoint d))
          ({-z} : Set (LatticePoint d)) := by
    -- Proof comment: translation invariance of the difference walk lets us move the target `0`
    -- back to the origin row and record only the displacement `-z`.
    rw [differenceStepMatrix_kernel_eq_diracConvolutionKernel]
    simpa using
      diracConvolutionKernel_pow_apply_singleton_eq_originMass
        (μ := (differenceStepPMF ν0).toMeasure) n z (0 : LatticePoint d)
  have hconv :
      (μn n ∗ (μn n).map (fun x : LatticePoint d ↦ -x)) ({-z} : Set (LatticePoint d)) =
        ∑' w : LatticePoint d,
          dirac_convolution_kernel ((μn n).map (fun x : LatticePoint d ↦ -x)) w
              ({-z} : Set (LatticePoint d)) *
            μn n ({w} : Set (LatticePoint d)) := by
    -- Proof comment: evaluate the convolution at `{-z}` and expand the kernel integral into the
    -- singleton-mass series over the lattice.
    rw [← diracConvolutionKernel_comp_measure_eq_conv
      (μ := μn n) (ν := (μn n).map (fun x : LatticePoint d ↦ -x))]
    rw [Measure.bind_apply (measurableSet_singleton (-z)) (Kernel.aemeasurable _)]
    simpa [mul_comm] using
      (MeasureTheory.lintegral_countable'
        (μ := μn n)
        (f := fun w : LatticePoint d ↦
          dirac_convolution_kernel ((μn n).map (fun x : LatticePoint d ↦ -x)) w
            ({-z} : Set (LatticePoint d))))
  have hreflect_zero :
      dirac_convolution_kernel ((μn n).map (fun x : LatticePoint d ↦ -x))
          (0 : LatticePoint d) ({-z} : Set (LatticePoint d)) =
        μn n ({z} : Set (LatticePoint d)) := by
    -- Proof comment: at the origin, the reflected law assigns mass to `{-z}` exactly when the
    -- original law assigns mass to `{z}`.
    rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (-z))]
    have hpreimage_add :
        (fun x : LatticePoint d ↦ (0 : LatticePoint d) + x) ⁻¹' ({-z} : Set (LatticePoint d)) =
          ({-z} : Set (LatticePoint d)) := by
      ext x
      simp
    rw [hpreimage_add]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (-z))]
    have hpreimage_neg :
        (fun x : LatticePoint d ↦ -x) ⁻¹' ({-z} : Set (LatticePoint d)) =
          ({z} : Set (LatticePoint d)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact neg_injective hx
      · intro hx
        simpa [hx]
    simpa [hpreimage_neg]
  have hterm_pos :
      0 <
        dirac_convolution_kernel ((μn n).map (fun x : LatticePoint d ↦ -x))
            (0 : LatticePoint d) ({-z} : Set (LatticePoint d)) *
          μn n ({0} : Set (LatticePoint d)) := by
    rw [hreflect_zero]
    exact ENNReal.mul_pos hmass_z.ne' hmass_zero.ne'
  have hterm_le :
      dirac_convolution_kernel ((μn n).map (fun x : LatticePoint d ↦ -x))
          (0 : LatticePoint d) ({-z} : Set (LatticePoint d)) *
        μn n ({0} : Set (LatticePoint d)) ≤
      ∑' w : LatticePoint d,
        dirac_convolution_kernel ((μn n).map (fun x : LatticePoint d ↦ -x)) w
            ({-z} : Set (LatticePoint d)) *
          μn n ({w} : Set (LatticePoint d)) := by
    exact ENNReal.le_tsum (0 : LatticePoint d)
  refine ⟨n, hn_pos, ?_⟩
  -- Proof comment: the positive `w = 0` summand survives in the convolution formula for the
  -- `{-z}` origin mass of the difference walk.
  rw [htranslate, differenceStepMatrix_kernel_eq_diracConvolutionKernel]
  rw [differenceKernelPow_origin_eq_conv_originLaw (ν := ν0) n, hμn, hconv]
  exact lt_of_lt_of_le hterm_pos hterm_le

/-- Helper for Exercise 18.2.3: the free difference walk is irreducible once the aperiodic base
walk can reach `0` from every displacement. -/
lemma differenceStepMatrix_isIrreducible_of_aperiodic
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    [IsMarkovKernel (discreteMatrixKernel p)]
    [Kernel.IsIrreducible (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    (htranslation : IsTranslationInvariantStepMatrix p)
    (haperiodic : IsAperiodic (discreteMatrixKernel p)) :
    Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d))
      (discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF))) := by
  let ν : PMF (LatticePoint d) := (discreteMatrixKernel p 0).toPMF
  letI : IsMarkovKernel (discreteMatrixKernel (differenceStepMatrix ν)) :=
    discreteMatrixKernel_isMarkovKernel _ (differenceStepMatrix_isStochastic (ν := ν))
  -- Proof comment: the difference walk is translation invariant, and the positive-hit-to-zero
  -- lemma upgrades that communication property to irreducibility.
  exact
    translationInvariant_isIrreducible_of_reachesZero
      (q := differenceStepMatrix ν)
      (differenceStepMatrix_isTranslationInvariantStepMatrix (ν := ν))
      (differenceStepMatrix_reachesZero (p := p) htranslation haperiodic)

/-- Helper for Exercise 18.2.3: a strictly positive singleton transition mass gives a positive
ever-hit probability. -/
lemma everHitsProbability_pos_of_positiveStepMass
    {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {Ω : Type*} [MeasurableSpace Ω]
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X]
    {x y : E} {n : ℕ}
    (hn : 0 < n) (hmass : 0 < (κ n) x ({y} : Set E)) :
    0 < (F[P, X]) x y := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hitEvent : Set Ω := {ω | ∃ m : ℕ, 0 < m ∧ X m ω = y}
  have hpreimage :
      {ω | X n ω = y} = X n ⁻¹' ({y} : Set E) := by
    ext ω
    simp
  have hmass_le :
      (κ n) x ({y} : Set E) ≤ (P x : Measure Ω) hitEvent := by
    calc
      (κ n) x ({y} : Set E) = (P x : Measure Ω) {ω | X n ω = y} := by
        rw [hpreimage]
        rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton y)]
        rw [hReal.transition_eq x n]
      _ ≤ (P x : Measure Ω) hitEvent := by
        refine measure_mono ?_
        intro ω hω
        exact ⟨n, hn, hω⟩
  have hhit_ne_zero : (P x : Measure Ω) hitEvent ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le hmass hmass_le)
  have hhit_real_ne_zero :
      (P x : Measure Ω).real hitEvent ≠ 0 := by
    exact (MeasureTheory.measureReal_ne_zero_iff (measure_ne_top _ _)).2 hhit_ne_zero
  -- Proof comment: the positive-time singleton transition event is contained in the ever-hit
  -- event, so the ever-hit probability is positive as well.
  exact lt_of_le_of_ne MeasureTheory.measureReal_nonneg <| by
    simpa [everHitsProbability_def, hitEvent] using hhit_real_ne_zero.symm

/-- Helper for Exercise 18.2.3: the free-difference return mass at the origin is the square-sum
of the base `n`-step origin-row singleton masses. -/
private lemma differenceReturnMass_toReal_eq_squareSum
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [IsMarkovKernel (discreteMatrixKernel p)]
    (n : ℕ) :
    (((discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^ n)
      (0 : LatticePoint d) ({0} : Set (LatticePoint d))).toReal) =
      ∑' z : LatticePoint d,
        ((((discreteMatrixKernel p ^ n) (0 : LatticePoint d) ({z} : Set (LatticePoint d))).toReal) ^ 2) := by
  let ν0 : PMF (LatticePoint d) := (discreteMatrixKernel p 0).toPMF
  let μn : Measure (LatticePoint d) := ((discreteMatrixKernel p ^ n) (0 : LatticePoint d))
  have hμn :
      ((dirac_convolution_kernel ν0.toMeasure ^ n) (0 : LatticePoint d)) = μn := by
    -- Proof comment: translation invariance identifies the whole base kernel with the
    -- convolution kernel driven by its origin row, so their `n`-step origin laws coincide.
    simpa [ν0, μn] using
      congrArg
        (fun κ : Kernel (LatticePoint d) (LatticePoint d) ↦
          (κ ^ n) (0 : LatticePoint d))
        (translationInvariantDiscreteKernel_eq_diracConvolutionKernel
          (p := p) htranslation)
  have hconv :
      (μn ∗ (μn.map (fun x : LatticePoint d ↦ -x))) ({0} : Set (LatticePoint d)) =
        ∑' z : LatticePoint d,
          dirac_convolution_kernel (μn.map (fun x : LatticePoint d ↦ -x)) z
              ({0} : Set (LatticePoint d)) *
            μn ({z} : Set (LatticePoint d)) := by
    -- Proof comment: evaluate the convolution as kernel composition and then expand the kernel
    -- integral into the countable singleton-mass series.
    rw [← diracConvolutionKernel_comp_measure_eq_conv
      (μ := μn) (ν := μn.map (fun x : LatticePoint d ↦ -x))]
    rw [Measure.bind_apply (measurableSet_singleton (0 : LatticePoint d)) (Kernel.aemeasurable _)]
    simpa [mul_comm] using
      (MeasureTheory.lintegral_countable'
        (μ := μn)
        (f := fun z : LatticePoint d ↦
          dirac_convolution_kernel (μn.map (fun x : LatticePoint d ↦ -x)) z
            ({0} : Set (LatticePoint d))))
  have hreflected :
      ∀ z : LatticePoint d,
        dirac_convolution_kernel (μn.map (fun x : LatticePoint d ↦ -x)) z
            ({0} : Set (LatticePoint d)) =
          μn ({z} : Set (LatticePoint d)) := by
    intro z
    -- Proof comment: the reflected law assigns mass to `{-z}` exactly when the original law
    -- assigns mass to `{z}`.
    rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : LatticePoint d))]
    have hpreimage_add :
        (fun x : LatticePoint d ↦ z + x) ⁻¹' ({0} : Set (LatticePoint d)) =
          ({-z} : Set (LatticePoint d)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hx)
      · intro hx
        exact by simpa [add_comm] using (eq_neg_iff_add_eq_zero.mp hx)
    rw [hpreimage_add]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (-z))]
    have hpreimage_neg :
        (fun x : LatticePoint d ↦ -x) ⁻¹' ({-z} : Set (LatticePoint d)) =
          ({z} : Set (LatticePoint d)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact neg_injective hx
      · intro hx
        simpa [hx]
    rw [hpreimage_neg]
  rw [differenceStepMatrix_kernel_eq_diracConvolutionKernel]
  rw [differenceKernelPow_origin_eq_conv_originLaw (ν := ν0) n]
  rw [hμn, hconv]
  rw [ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun z ↦ ?_
    rw [hreflected z, ENNReal.toReal_mul]
    ring
  · intro z
    rw [hreflected z]
    exact ENNReal.mul_ne_top
      (measure_ne_top μn ({z} : Set (LatticePoint d)))
      (measure_ne_top μn ({z} : Set (LatticePoint d)))

/-- Helper for Exercise 18.2.3: the `n`-step singleton mass of a translation-invariant lattice
kernel only depends on the displacement `y - x`. -/
private lemma translationInvariantDiscreteKernel_pow_apply_singleton_eq_originMass
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [IsMarkovKernel (discreteMatrixKernel p)]
    (n : ℕ) (x y : LatticePoint d) :
    ((discreteMatrixKernel p ^ n) x) ({y} : Set (LatticePoint d)) =
      ((discreteMatrixKernel p ^ n) (0 : LatticePoint d)) ({y - x} : Set (LatticePoint d)) := by
  let ν : Measure (LatticePoint d) := ((discreteMatrixKernel p 0).toPMF.toMeasure)
  have hkernel : discreteMatrixKernel p = dirac_convolution_kernel ν := by
    -- Proof comment: a translation-invariant discrete kernel is determined by its origin row.
    symm
    simpa [ν] using
      (translationInvariantDiscreteKernel_eq_diracConvolutionKernel
        (p := p) htranslation)
  -- Proof comment: rewrite the kernel as the convolution kernel of the origin row and then use
  -- the already-proved translation formula for powers of convolution kernels.
  rw [hkernel]
  simpa [ν] using
    diracConvolutionKernel_pow_apply_singleton_eq_originMass (μ := ν) n x y

/-- Helper for Exercise 18.2.3: on a countable discrete state space, integrating singleton rows of
a kernel is the same as summing the singleton masses against the source measure. -/
private lemma lintegralKernelApplySingleton_eq_tsum
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (κ : Kernel S S) (μ : Measure S) (w : S) :
    ∫⁻ c, κ c ({w} : Set S) ∂μ =
      ∑' c : S, κ c ({w} : Set S) * μ ({c} : Set S) := by
  -- Proof comment: on a countable discrete space, `lintegral_countable'` turns the kernel
  -- integral into the singleton-mass series directly.
  simpa [mul_comm] using
    (MeasureTheory.lintegral_countable' (μ := μ)
      (f := fun c : S ↦ κ c ({w} : Set S)))

/-- Helper for Exercise 18.2.3: reindexing a lattice series by negation preserves its sum. -/
private lemma tsum_comp_neg
    {d : ℕ} {f : LatticePoint d → ℝ} :
    ∑' z : LatticePoint d, f (-z) = ∑' z : LatticePoint d, f z := by
  -- Proof comment: negation is a bijection of the lattice, so reindexing by `z ↦ -z` preserves
  -- the sum.
  simpa using ((Equiv.neg (LatticePoint d)).tsum_eq (f := f)).symm

/-- Helper for Exercise 18.2.3: the `n`-step singleton masses of the independent product pair
kernel factor into the corresponding singleton masses of the two coordinates. -/
private lemma independentProductPairKernelPow_apply_singleton
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    [IsMarkovKernel (discreteMatrixKernel p)]
    (n : ℕ)
    (x₁ y₁ x₂ y₂ : LatticePoint d) :
    (((discreteMatrixKernel p ∥ₖ discreteMatrixKernel p) ^ n) (x₁, y₁))
        ({(x₂, y₂)} : Set (LatticePoint d × LatticePoint d)) =
      ((discreteMatrixKernel p ^ n) x₁) ({x₂} : Set (LatticePoint d)) *
        ((discreteMatrixKernel p ^ n) y₁) ({y₂} : Set (LatticePoint d)) := by
  let κ : Kernel (LatticePoint d) (LatticePoint d) := discreteMatrixKernel p
  let κq : Kernel (LatticePoint d × LatticePoint d) (LatticePoint d × LatticePoint d) := κ ∥ₖ κ
  have hpow : ∀ m : ℕ, κq ^ m = (κ ^ m) ∥ₖ (κ ^ m) := by
    intro m
    induction m with
    | zero =>
        -- Proof comment: the zero-step kernel on the product state space is the product identity.
        change (Kernel.id : Kernel (LatticePoint d × LatticePoint d)
            (LatticePoint d × LatticePoint d)) =
          (Kernel.id : Kernel (LatticePoint d) (LatticePoint d)) ∥ₖ Kernel.id
        exact Kernel.id_parallelComp_id.symm
    | succ m ihm =>
        -- Proof comment: powers of a parallel kernel stay parallel because composition commutes
        -- with `∥ₖ` coordinatewise.
        calc
          κq ^ (m + 1) = κq ∘ₖ (κq ^ m) := by
            simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κq 1 m)
          _ = (κ ∥ₖ κ) ∘ₖ ((κ ^ m) ∥ₖ (κ ^ m)) := by rw [ihm]
          _ = (κ ∘ₖ (κ ^ m)) ∥ₖ (κ ∘ₖ (κ ^ m)) := by
            rw [Kernel.parallelComp_comp_parallelComp]
          _ = (κ ^ (m + 1)) ∥ₖ (κ ^ (m + 1)) := by
            congr 1 <;> symm <;>
              simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 m)
  have hsingleton :
      ({((x₂, y₂) : LatticePoint d × LatticePoint d)} :
          Set (LatticePoint d × LatticePoint d)) =
        ({x₂} : Set (LatticePoint d)) ×ˢ ({y₂} : Set (LatticePoint d)) := by
    ext t
    simp
  -- Proof comment: once the `n`-step product kernel is identified with the parallel composition
  -- of the `n`-step coordinate kernels, the singleton mass factorizes immediately.
  rw [hpow n, hsingleton, Kernel.parallelComp_apply_prod]

/-- Helper for Exercise 18.2.3: splitting an origin return mass at times `m` and `k` gives a
real-valued cross-sum over intermediate lattice points. -/
private lemma baseReturnMassSplit_toReal_eq_crossSum
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [IsMarkovKernel (discreteMatrixKernel p)]
    (m k : ℕ) :
    (((discreteMatrixKernel p ^ (m + k)) (0 : LatticePoint d)
      ({0} : Set (LatticePoint d))).toReal) =
      ∑' z : LatticePoint d,
        (((discreteMatrixKernel p ^ m) (0 : LatticePoint d) ({z} : Set (LatticePoint d))).toReal) *
          (((discreteMatrixKernel p ^ k) (0 : LatticePoint d) ({-z} : Set (LatticePoint d))).toReal) := by
  let κ : Kernel (LatticePoint d) (LatticePoint d) := discreteMatrixKernel p
  -- Proof comment: expand the split time `(m + k)` by Chapman-Kolmogorov, convert the resulting
  -- kernel integral into a countable singleton series, and then transport the `k`-step factor
  -- back to the origin row by translation invariance.
  rw [Kernel.pow_add_apply_eq_lintegral κ m k (0 : LatticePoint d) (measurableSet_singleton 0)]
  rw [lintegralKernelApplySingleton_eq_tsum (κ := κ ^ k) ((κ ^ m) (0 : LatticePoint d))
    (0 : LatticePoint d)]
  rw [ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun z ↦ ?_
    rw [ENNReal.toReal_mul]
    rw [translationInvariantDiscreteKernel_pow_apply_singleton_eq_originMass
      (p := p) htranslation k z (0 : LatticePoint d)]
    simp [κ, mul_comm]
  · intro z
    exact ENNReal.mul_ne_top
      (measure_ne_top ((κ ^ k) z) ({0} : Set (LatticePoint d)))
      (measure_ne_top ((κ ^ m) (0 : LatticePoint d)) ({z} : Set (LatticePoint d)))

/-- Helper for Exercise 18.2.3: even return masses of the base walk are bounded by the diagonal
return masses of the free difference walk. -/
private lemma baseEvenReturnMass_toReal_le_differenceReturnMass
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [IsMarkovKernel (discreteMatrixKernel p)]
    (n : ℕ) :
    (((discreteMatrixKernel p ^ (2 * n)) (0 : LatticePoint d)
      ({0} : Set (LatticePoint d))).toReal) ≤
      (((discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^ n)
        (0 : LatticePoint d) ({0} : Set (LatticePoint d))).toReal) := by
  let a : LatticePoint d → ℝ :=
    fun z ↦ (((discreteMatrixKernel p ^ n) (0 : LatticePoint d)
      ({z} : Set (LatticePoint d))).toReal)
  have ha_nonneg : ∀ z : LatticePoint d, 0 ≤ a z := by
    intro z
    exact ENNReal.toReal_nonneg
  have ha_le_one : ∀ z : LatticePoint d, a z ≤ 1 := by
    intro z
    let μ : Measure (LatticePoint d) := ((discreteMatrixKernel p ^ n) (0 : LatticePoint d))
    letI : IsProbabilityMeasure μ := inferInstance
    simpa [a, μ, MeasureTheory.measureReal_def] using
      (measureReal_le_one (μ := μ) (s := ({z} : Set (LatticePoint d))))
  have hsummableMass : Summable a := by
    let μ : Measure (LatticePoint d) := ((discreteMatrixKernel p ^ n) (0 : LatticePoint d))
    letI : IsProbabilityMeasure μ := inferInstance
    simpa [a, μ, MeasureTheory.Measure.toPMF_apply] using
      (ENNReal.summable_toReal
        (f := fun z : LatticePoint d ↦ μ.toPMF z)
        (by simp))
  have hsquare : Summable (fun z : LatticePoint d ↦ (a z) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hsummableMass
    · intro z
      exact sq_nonneg (a z)
    · intro z
      nlinarith [ha_nonneg z, ha_le_one z]
  have hsquareNeg : Summable (fun z : LatticePoint d ↦ (a (-z)) ^ 2) := by
    simpa using hsquare.comp_injective (Equiv.neg (LatticePoint d)).injective
  have hsquareAvg :
      Summable (fun z : LatticePoint d ↦ ((a z) ^ 2 + (a (-z)) ^ 2) / 2) := by
    simpa [div_eq_mul_inv, right_distrib] using
      (hsquare.add hsquareNeg).mul_right (1 / 2 : ℝ)
  have hcross : Summable (fun z : LatticePoint d ↦ a z * a (-z)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hsquareAvg
    · intro z
      exact mul_nonneg (ha_nonneg z) (ha_nonneg (-z))
    · intro z
      nlinarith [sq_nonneg (a z - a (-z))]
  have hsum_le :
      (∑' z : LatticePoint d, a z * a (-z)) ≤
        ∑' z : LatticePoint d, ((a z) ^ 2 + (a (-z)) ^ 2) / 2 := by
    exact hasSum_le
      (fun z ↦ by nlinarith [sq_nonneg (a z - a (-z))])
      hcross.hasSum hsquareAvg.hasSum
  have hsquareAvg_eq :
      (∑' z : LatticePoint d, ((a z) ^ 2 + (a (-z)) ^ 2) / 2) =
        ∑' z : LatticePoint d, (a z) ^ 2 := by
    have hsquareSum : Summable (fun z : LatticePoint d ↦ (a z) ^ 2 + (a (-z)) ^ 2) :=
      hsquare.add hsquareNeg
    have hsquareNeg_eq :
        (∑' z : LatticePoint d, (a (-z)) ^ 2) = ∑' z : LatticePoint d, (a z) ^ 2 := by
      simpa using (tsum_comp_neg (f := fun z : LatticePoint d ↦ (a z) ^ 2))
    calc
      (∑' z : LatticePoint d, ((a z) ^ 2 + (a (-z)) ^ 2) / 2)
          = ((∑' z : LatticePoint d, ((a z) ^ 2 + (a (-z)) ^ 2))) / 2 := by
              simpa [div_eq_mul_inv] using hsquareSum.tsum_mul_right (1 / 2 : ℝ)
      _ = ((∑' z : LatticePoint d, (a z) ^ 2) +
            (∑' z : LatticePoint d, (a (-z)) ^ 2)) / 2 := by
              rw [Summable.tsum_add hsquare hsquareNeg]
      _ = ((∑' z : LatticePoint d, (a z) ^ 2) +
            (∑' z : LatticePoint d, (a z) ^ 2)) / 2 := by
              rw [hsquareNeg_eq]
      _ = ∑' z : LatticePoint d, (a z) ^ 2 := by
              ring
  -- Proof comment: expand the even return mass as the cross-sum `a_z a_{-z}`, compare each
  -- term by AM-GM, and then identify the resulting square-sum with the difference return mass.
  calc
    (((discreteMatrixKernel p ^ (2 * n)) (0 : LatticePoint d)
      ({0} : Set (LatticePoint d))).toReal)
        = ∑' z : LatticePoint d, a z * a (-z) := by
            simpa [a, two_mul] using
              baseReturnMassSplit_toReal_eq_crossSum (p := p) htranslation n n
    _ ≤ ∑' z : LatticePoint d, ((a z) ^ 2 + (a (-z)) ^ 2) / 2 := hsum_le
    _ = ∑' z : LatticePoint d, (a z) ^ 2 := hsquareAvg_eq
    _ =
        (((discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^ n)
          (0 : LatticePoint d) ({0} : Set (LatticePoint d))).toReal) := by
            symm
            simpa [a] using
              differenceReturnMass_toReal_eq_squareSum (p := p) htranslation n

/-- Helper for Exercise 18.2.3: odd return masses of the base walk are bounded by the arithmetic
mean of two consecutive diagonal return masses of the free difference walk. -/
private lemma baseOddReturnMass_toReal_le_differenceReturnPairAverage
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [IsMarkovKernel (discreteMatrixKernel p)]
    (n : ℕ) :
    (((discreteMatrixKernel p ^ (2 * n + 1)) (0 : LatticePoint d)
      ({0} : Set (LatticePoint d))).toReal) ≤
      ((((discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^ n)
        (0 : LatticePoint d) ({0} : Set (LatticePoint d))).toReal) +
        (((discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^
          (n + 1)) (0 : LatticePoint d) ({0} : Set (LatticePoint d))).toReal)) / 2 := by
  let a : LatticePoint d → ℝ :=
    fun z ↦ (((discreteMatrixKernel p ^ n) (0 : LatticePoint d)
      ({z} : Set (LatticePoint d))).toReal)
  let b : LatticePoint d → ℝ :=
    fun z ↦ (((discreteMatrixKernel p ^ (n + 1)) (0 : LatticePoint d)
      ({z} : Set (LatticePoint d))).toReal)
  have ha_nonneg : ∀ z : LatticePoint d, 0 ≤ a z := by
    intro z
    exact ENNReal.toReal_nonneg
  have hb_nonneg : ∀ z : LatticePoint d, 0 ≤ b z := by
    intro z
    exact ENNReal.toReal_nonneg
  have ha_le_one : ∀ z : LatticePoint d, a z ≤ 1 := by
    intro z
    let μ : Measure (LatticePoint d) := ((discreteMatrixKernel p ^ n) (0 : LatticePoint d))
    letI : IsProbabilityMeasure μ := inferInstance
    simpa [a, μ, MeasureTheory.measureReal_def] using
      (measureReal_le_one (μ := μ) (s := ({z} : Set (LatticePoint d))))
  have hb_le_one : ∀ z : LatticePoint d, b z ≤ 1 := by
    intro z
    let μ : Measure (LatticePoint d) := ((discreteMatrixKernel p ^ (n + 1)) (0 : LatticePoint d))
    letI : IsProbabilityMeasure μ := inferInstance
    simpa [b, μ, MeasureTheory.measureReal_def] using
      (measureReal_le_one (μ := μ) (s := ({z} : Set (LatticePoint d))))
  have ha_summable : Summable a := by
    let μ : Measure (LatticePoint d) := ((discreteMatrixKernel p ^ n) (0 : LatticePoint d))
    letI : IsProbabilityMeasure μ := inferInstance
    simpa [a, μ, MeasureTheory.Measure.toPMF_apply] using
      (ENNReal.summable_toReal
        (f := fun z : LatticePoint d ↦ μ.toPMF z)
        (by simp))
  have hb_summable : Summable b := by
    let μ : Measure (LatticePoint d) := ((discreteMatrixKernel p ^ (n + 1)) (0 : LatticePoint d))
    letI : IsProbabilityMeasure μ := inferInstance
    simpa [b, μ, MeasureTheory.Measure.toPMF_apply] using
      (ENNReal.summable_toReal
        (f := fun z : LatticePoint d ↦ μ.toPMF z)
        (by simp))
  have ha_square : Summable (fun z : LatticePoint d ↦ (a z) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ ha_summable
    · intro z
      exact sq_nonneg (a z)
    · intro z
      nlinarith [ha_nonneg z, ha_le_one z]
  have hb_square : Summable (fun z : LatticePoint d ↦ (b z) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hb_summable
    · intro z
      exact sq_nonneg (b z)
    · intro z
      nlinarith [hb_nonneg z, hb_le_one z]
  have hb_square_neg : Summable (fun z : LatticePoint d ↦ (b (-z)) ^ 2) := by
    simpa using hb_square.comp_injective (Equiv.neg (LatticePoint d)).injective
  have hpairAvg :
      Summable (fun z : LatticePoint d ↦ ((a z) ^ 2 + (b (-z)) ^ 2) / 2) := by
    simpa [div_eq_mul_inv, right_distrib] using
      (ha_square.add hb_square_neg).mul_right (1 / 2 : ℝ)
  have hcross : Summable (fun z : LatticePoint d ↦ a z * b (-z)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hpairAvg
    · intro z
      exact mul_nonneg (ha_nonneg z) (hb_nonneg (-z))
    · intro z
      nlinarith [sq_nonneg (a z - b (-z))]
  have hsum_le :
      (∑' z : LatticePoint d, a z * b (-z)) ≤
        ∑' z : LatticePoint d, ((a z) ^ 2 + (b (-z)) ^ 2) / 2 := by
    exact hasSum_le
      (fun z ↦ by nlinarith [sq_nonneg (a z - b (-z))])
      hcross.hasSum hpairAvg.hasSum
  have hpairAvg_eq :
      (∑' z : LatticePoint d, ((a z) ^ 2 + (b (-z)) ^ 2) / 2) =
        (((∑' z : LatticePoint d, (a z) ^ 2) +
          (∑' z : LatticePoint d, (b z) ^ 2)) / 2) := by
    have hpairSum : Summable (fun z : LatticePoint d ↦ (a z) ^ 2 + (b (-z)) ^ 2) :=
      ha_square.add hb_square_neg
    have hb_square_neg_eq :
        (∑' z : LatticePoint d, (b (-z)) ^ 2) = ∑' z : LatticePoint d, (b z) ^ 2 := by
      simpa using (tsum_comp_neg (f := fun z : LatticePoint d ↦ (b z) ^ 2))
    calc
      (∑' z : LatticePoint d, ((a z) ^ 2 + (b (-z)) ^ 2) / 2)
          = ((∑' z : LatticePoint d, ((a z) ^ 2 + (b (-z)) ^ 2))) / 2 := by
              simpa [div_eq_mul_inv] using hpairSum.tsum_mul_right (1 / 2 : ℝ)
      _ = ((∑' z : LatticePoint d, (a z) ^ 2) +
            (∑' z : LatticePoint d, (b (-z)) ^ 2)) / 2 := by
              rw [Summable.tsum_add ha_square hb_square_neg]
      _ = ((∑' z : LatticePoint d, (a z) ^ 2) +
            (∑' z : LatticePoint d, (b z) ^ 2)) / 2 := by
              rw [hb_square_neg_eq]
  -- Proof comment: the odd return mass is the mixed cross-sum `a_z b_{-z}`. Pointwise AM-GM
  -- bounds this by the average of the two square-sums, which are exactly the consecutive
  -- difference return masses at times `n` and `n + 1`.
  calc
    (((discreteMatrixKernel p ^ (2 * n + 1)) (0 : LatticePoint d)
      ({0} : Set (LatticePoint d))).toReal)
        = ∑' z : LatticePoint d, a z * b (-z) := by
            simpa [a, b, two_mul, Nat.add_assoc, Nat.succ_eq_add_one] using
              baseReturnMassSplit_toReal_eq_crossSum (p := p) htranslation n (n + 1)
    _ ≤ ∑' z : LatticePoint d, ((a z) ^ 2 + (b (-z)) ^ 2) / 2 := hsum_le
    _ = (((∑' z : LatticePoint d, (a z) ^ 2) +
          (∑' z : LatticePoint d, (b z) ^ 2)) / 2) := hpairAvg_eq
    _ =
        ((((discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^ n)
          (0 : LatticePoint d) ({0} : Set (LatticePoint d))).toReal) +
          (((discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^
            (n + 1)) (0 : LatticePoint d) ({0} : Set (LatticePoint d))).toReal)) / 2 := by
            have ha_square_eq :
                (∑' z : LatticePoint d, (a z) ^ 2) =
                  (((discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^ n)
                    (0 : LatticePoint d) ({0} : Set (LatticePoint d))).toReal) := by
              symm
              simpa only [a] using
                differenceReturnMass_toReal_eq_squareSum (p := p) htranslation n
            have hb_square_eq :
                (∑' z : LatticePoint d, (b z) ^ 2) =
                  (((discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^
                    (n + 1)) (0 : LatticePoint d) ({0} : Set (LatticePoint d))).toReal) := by
              symm
              simpa only [b] using
                differenceReturnMass_toReal_eq_squareSum (p := p) htranslation (n + 1)
            rw [ha_square_eq, hb_square_eq]

/-- Helper for Exercise 18.2.3: every stochastic matrix on a countable discrete space admits the
canonical path-space realization coming from `Kernel.trajMeasure`. -/
private theorem existsCanonicalDiscreteMatrixRealization
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (q : S → S → ENNReal) (hq : IsStochasticMatrix q) :
    ∃ Pq : S → ProbabilityMeasure (ℕ → S),
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q ^ n) Pq Function.eval := by
  let κ : Kernel S S := discreteMatrixKernel q
  letI : IsMarkovKernel κ := discreteMatrixKernel_isMarkovKernel q hq
  let η : (n : ℕ) → Kernel (Π i : Finset.Iic n, S) S :=
    fun n ↦
      Kernel.comap κ
        (fun z : Π i : Finset.Iic n, S ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
        (by fun_prop)
  have hη : ∀ n : ℕ, IsMarkovKernel (η n) := by
    intro n
    dsimp [η]
    infer_instance
  let μ : S → Measure (ℕ → S) :=
    fun x ↦
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      Kernel.trajMeasure (X := fun _ : ℕ ↦ S) (Measure.dirac x) η
  have hμ : ∀ x : S, IsProbabilityMeasure (μ x) := by
    intro x
    dsimp [μ]
    infer_instance
  let Pq : S → ProbabilityMeasure (ℕ → S) := fun x ↦ ⟨μ x, hμ x⟩
  refine ⟨Pq, ?_⟩
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := κ)
    (P := Pq)
    (X := Function.eval)
    (hmeas := fun n ↦ measurable_pi_apply n)
    ?_ ?_
  · intro x
    have hprefix :
        (μ x).map (Preorder.frestrictLe 0) = Measure.dirac (fun _ : Finset.Iic 0 ↦ x) := by
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      simpa [μ, η, Kernel.partialTraj_self] using
        (Kernel.trajMeasure_map_frestrictLe
          (X := fun _ : ℕ ↦ S) (μ₀ := Measure.dirac x) (κ := η) 0)
    calc
      (Pq x : Measure (ℕ → S)).map (Function.eval 0)
          = ((μ x).map (Preorder.frestrictLe 0)).map
              (fun z : Finset.Iic 0 → S ↦ z ⟨0, Finset.mem_Iic.2 le_rfl⟩) := by
                rw [Measure.map_map (by fun_prop) (by fun_prop)]
                rfl
      _ = Measure.dirac x := by
            rw [hprefix]
            simp
  · intro x A hA n
    letI : Nonempty S := ⟨x⟩
    let H : (ℕ → S) → Finset.Iic n → S := Preorder.frestrictLe n
    have hH_meas : Measurable H := Preorder.measurable_frestrictLe n
    have hnext_meas : Measurable (Function.eval (n + 1) : (ℕ → S) → S) :=
      measurable_pi_apply (n + 1)
    have hcond :
        condDistrib (Function.eval (n + 1)) H (μ x) =ᵐ[(μ x).map H] η n := by
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      simpa [μ, H, η] using
        (Kernel.condDistrib_trajMeasure
          (X := fun _ : ℕ ↦ S) (μ₀ := Measure.dirac x) (κ := η) (a := n))
    have hcondexp :
        (μ x)⟦(Function.eval (n + 1)) ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ x]
          fun ξ ↦ (condDistrib (Function.eval (n + 1)) H (μ x) (H ξ)).real A := by
      simpa using
        (condDistrib_ae_eq_condExp (μ := μ x) (X := H) (Y := Function.eval (n + 1))
          hH_meas hnext_meas hA).symm
    have hcond_comp :
        (fun ξ ↦ (condDistrib (Function.eval (n + 1)) H (μ x) (H ξ)).real A) =ᵐ[μ x]
          fun ξ ↦ (η n (H ξ)).real A := by
      filter_upwards [ae_eq_comp hH_meas.aemeasurable hcond] with ξ hξ
      simpa [Function.comp] using congrArg (fun ν : Measure S ↦ ν.real A) hξ
    have hgen :
        generatedFiltrationSpace (Function.eval : ℕ → (ℕ → S) → S) n =
          MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance := by
      refine le_antisymm ?_ ?_
      · rw [generatedFiltrationSpace]
        refine iSup₂_le fun t ht ↦ ?_
        let i : Finset.Iic n := ⟨t, Finset.mem_Iic.2 ht⟩
        have hCoord :
            Measurable[
              MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance]
              (Function.eval t : (ℕ → S) → S) := by
          simpa [Function.eval, Preorder.frestrictLe_apply, i] using
            (measurable_pi_apply i).comp (comap_measurable (Preorder.frestrictLe n))
        exact hCoord.comap_le
      · have hPrefix :
          Measurable[
            generatedFiltrationSpace (Function.eval : ℕ → (ℕ → S) → S) n]
            (Preorder.frestrictLe n : (ℕ → S) → Finset.Iic n → S) := by
          rw [@measurable_pi_iff]
          intro i
          refine Measurable.of_comap_le ?_
          exact le_iSup_of_le i.1 <| le_iSup_of_le (Finset.mem_Iic.1 i.2) le_rfl
        exact hPrefix.comap_le
    rw [hgen]
    exact hcondexp.trans <|
      hcond_comp.trans <|
        Filter.Eventually.of_forall fun ξ ↦ by
          simpa [η, H, Preorder.frestrictLe_apply] using
            congrArg (fun ν : Measure S ↦ ν.real A) rfl

/-- Helper for Exercise 18.2.3: the strictly positive visit times of the path `ω` at the state
`x`. -/
private def positiveVisitSet
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) (ω : ΩS) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ Y n ω = x}

/-- Helper for Exercise 18.2.3: a bound on the infimum of a set of natural times in `ℕ∞` is
equivalent to a bounded witness in the underlying set. -/
private lemma sInf_natImage_le_iff_local {S : Set ℕ} {N : ℕ} :
    sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) ≤ N ↔ ∃ n ∈ S, n ≤ N := by
  by_cases hS : S.Nonempty
  · have hsInf :
        sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) = (((sInf S : ℕ) : ℕ∞)) := by
      simpa using (WithTop.coe_sInf' hS (OrderBot.bddBelow S)).symm
    constructor
    · intro h
      refine ⟨(sInf S : ℕ), Nat.sInf_mem hS, ?_⟩
      have hsInf_leN : ((((sInf S : ℕ) : ℕ) : ℕ∞)) ≤ N := by
        simpa [hsInf] using h
      exact_mod_cast hsInf_leN
    · rintro ⟨n, hnS, hnN⟩
      have hsInf_le_nat : (sInf S : ℕ) ≤ n := Nat.sInf_le hnS
      have hsInf_leN_nat : (sInf S : ℕ) ≤ N := hsInf_le_nat.trans hnN
      have hsInf_leN : ((((sInf S : ℕ) : ℕ) : ℕ∞)) ≤ N := by
        exact_mod_cast hsInf_leN_nat
      simpa [hsInf] using hsInf_leN
  · have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    subst hS_empty
    simp

/-- Helper for Exercise 18.2.3: the successor entrance time is bounded by `N` exactly when there
is a visit to `x` by time `N` occurring strictly after the previous entrance. -/
private lemma iteratedEntranceTime_succ_le_iff_existsHitAfter_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) (ω : ΩS) (k : ℕ+) (N : ℕ) :
    (τ_[Y, x]^(k + 1)) ω ≤ N ↔
      ∃ n : ℕ, (τ_[Y, x]^k) ω < n ∧ n ≤ N ∧ Y n ω = x := by
  rw [iteratedEntranceTime_succ]
  rw [sInf_natImage_le_iff_local]
  constructor
  · rintro ⟨n, hn, hnN⟩
    exact ⟨n, hn.1, hnN, hn.2⟩
  · rintro ⟨n, hτ, hnN, hx⟩
    exact ⟨n, ⟨hτ, hx⟩, hnN⟩

/-- Helper for Exercise 18.2.3: `prefixHasIteratedReturn x k m f` records `k` strictly positive
visits to `x` inside the finite prefix `f : Fin m → S`. -/
private def prefixHasIteratedReturn
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (x : S) : ℕ+ → ∀ m : ℕ, (Fin m → S) → Prop :=
  fun k =>
    PNat.recOn k
      (fun m f => ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x)
      (fun _ ih m f =>
        ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x ∧
          ih i (fun j : Fin i ↦ f ⟨j, Nat.lt_trans j.2 i.2⟩))

/-- Helper for Exercise 18.2.3: the first positive return in a prefix is one positive index
carrying the value `x`. -/
private lemma prefixHasIteratedReturn_one_iff_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (x : S) (m : ℕ) (f : Fin m → S) :
    prefixHasIteratedReturn x 1 m f ↔ ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x := by
  simp [prefixHasIteratedReturn]

/-- Helper for Exercise 18.2.3: the successor prefix-return predicate peels off the last
positive return and recurses on the earlier prefix. -/
private lemma prefixHasIteratedReturn_succ_iff_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (x : S) (k : ℕ+) (m : ℕ) (f : Fin m → S) :
    prefixHasIteratedReturn x (k + 1) m f ↔
      ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = x ∧
        prefixHasIteratedReturn x k i (fun j : Fin i ↦ f ⟨j, Nat.lt_trans j.2 i.2⟩) := by
  simp [prefixHasIteratedReturn]

/-- Helper for Exercise 18.2.3: the bounded event `τ_[Y, x]^k < m` is equivalent to the
recursive finite-prefix predicate on the first `m` coordinates of the path. -/
private lemma iteratedEntranceTime_lt_iff_prefixHasIteratedReturn_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) (ω : ΩS) :
    ∀ (k : ℕ+) (m : ℕ),
      (τ_[Y, x]^k) ω < m ↔
        prefixHasIteratedReturn x k m (fun i : Fin m ↦ Y i ω) := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m
      cases m with
      | zero =>
          constructor
          · intro h
            simpa using h
          · intro h
            rcases h with ⟨i, _, _⟩
            exact Fin.elim0 i
      | succ m =>
          constructor
          · intro h
            have hhit :
                hittingAfter Y ({x} : Set S) 1 ω < ↑(m + 1) := by
              simpa [iteratedEntranceTime_one] using h
            rcases (MeasureTheory.hittingAfter_lt_iff
              (u := Y) (s := ({x} : Set S)) (n := 1) (ω := ω) (i := m + 1)).1 hhit with
              ⟨n, hn_mem, hn_eq⟩
            exact
              (prefixHasIteratedReturn_one_iff_local x (m + 1) (fun i : Fin (m + 1) ↦ Y i ω)).2
                ⟨⟨n, hn_mem.2⟩, by simpa using hn_mem.1,
                  by simpa [Set.mem_singleton_iff] using hn_eq⟩
          · intro h
            rcases
                (prefixHasIteratedReturn_one_iff_local x (m + 1)
                  (fun i : Fin (m + 1) ↦ Y i ω)).1 h with
              ⟨i, hi_pos, hi_eq⟩
            have hhit :
                hittingAfter Y ({x} : Set S) 1 ω < ↑(m + 1) := by
              exact
                (MeasureTheory.hittingAfter_lt_iff
                  (u := Y) (s := ({x} : Set S)) (n := 1) (ω := ω) (i := m + 1)).2
                  ⟨i, ⟨by simpa using hi_pos, i.2⟩,
                    by simpa [Set.mem_singleton_iff] using hi_eq⟩
            simpa [iteratedEntranceTime_one] using hhit
  | succ k ih =>
      intro m
      cases m with
      | zero =>
          constructor
          · intro h
            simpa using h
          · intro h
            rcases
                (prefixHasIteratedReturn_succ_iff_local x k 0 (fun i : Fin 0 ↦ Y i ω)).1 h with
              ⟨i, _, _, _⟩
            exact Fin.elim0 i
      | succ m =>
          have hbound :
              (τ_[Y, x]^(k + 1)) ω < ↑(m + 1) ↔ (τ_[Y, x]^(k + 1)) ω ≤ m := by
            simpa using (ENat.lt_coe_add_one_iff (m := (τ_[Y, x]^(k + 1)) ω) (n := m))
          constructor
          · intro h
            have hle : (τ_[Y, x]^(k + 1)) ω ≤ m := hbound.mp h
            rcases
                (iteratedEntranceTime_succ_le_iff_existsHitAfter_local
                  (Y := Y) (x := x) (ω := ω) (k := k) (N := m)).1 hle with
              ⟨n, hτn, hn_le, hn_eq⟩
            have hn_pos : 0 < n := by
              by_contra hn_zero
              have hn_eq_zero : n = 0 := Nat.eq_zero_of_not_pos hn_zero
              have : ¬ (τ_[Y, x]^k) ω < (0 : ℕ) := by simp
              exact this (by simpa [hn_eq_zero] using hτn)
            exact
              (prefixHasIteratedReturn_succ_iff_local x k (m + 1)
                (fun i : Fin (m + 1) ↦ Y i ω)).2
                ⟨⟨n, Nat.lt_succ_iff.mpr hn_le⟩, by simpa using hn_pos,
                  by simpa using hn_eq, (ih n).1 hτn⟩
          · intro h
            rcases
                (prefixHasIteratedReturn_succ_iff_local x k (m + 1)
                  (fun i : Fin (m + 1) ↦ Y i ω)).1 h with
              ⟨i, hi_pos, hi_eq, hi_prefix⟩
            have hle : (τ_[Y, x]^(k + 1)) ω ≤ m := by
              exact
                (iteratedEntranceTime_succ_le_iff_existsHitAfter_local
                  (Y := Y) (x := x) (ω := ω) (k := k) (N := m)).2
                  ⟨i, (ih i).2 hi_prefix, Nat.le_of_lt_succ i.2, by simpa using hi_eq⟩
            exact hbound.mpr hle

/-- Helper for Exercise 18.2.3: the recursive finite-prefix witness forces at least the
corresponding number of positive visits in that prefix. -/
private lemma prefixHasIteratedReturn_le_card_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (x : S) :
    ∀ {k : ℕ+} {m : ℕ} {f : Fin m → S},
      prefixHasIteratedReturn x k m f →
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m f h
      rcases (prefixHasIteratedReturn_one_iff_local x m f).1 h with ⟨i, hi_pos, hi_eq⟩
      have hone : 1 ≤ (Finset.univ.filter fun j : Fin m ↦ 0 < (j : ℕ) ∧ f j = x).card := by
        rw [Finset.one_le_card]
        exact ⟨i, by simp [hi_pos, hi_eq]⟩
      simpa using hone
  | succ k ih =>
      intro m f h
      let s : Finset (Fin m) := Finset.univ.filter fun j : Fin m ↦ 0 < (j : ℕ) ∧ f j = x
      rcases (prefixHasIteratedReturn_succ_iff_local x k m f).1 h with ⟨i, hi_pos, hi_eq, hi_prefix⟩
      let t : Finset (Fin i) := Finset.univ.filter fun j : Fin i ↦
        0 < (j : ℕ) ∧ f ⟨j, Nat.lt_trans j.2 i.2⟩ = x
      have hi_mem : i ∈ s := by
        simp [s, hi_pos, hi_eq]
      have hk_le_t : (k : ℕ) ≤ t.card := ih hi_prefix
      have ht_le_erase : t.card ≤ (s.erase i).card := by
        refine Finset.card_le_card_of_injOn
          (fun j : Fin i ↦ (⟨(j : ℕ), Nat.lt_trans j.2 i.2⟩ : Fin m)) ?_ ?_
        · intro j hj
          have hj_props : 0 < (j : ℕ) ∧ f ⟨j, Nat.lt_trans j.2 i.2⟩ = x := by
            simpa [t] using hj
          refine Finset.mem_erase.2 ⟨?_, ?_⟩
          · intro hji
            exact (ne_of_lt j.2) (Fin.ext_iff.mp hji)
          · simp [s, hj_props]
        · intro a₁ ha₁ b hb hEq
          exact Fin.ext (congrArg (fun z : Fin m ↦ (z : ℕ)) hEq)
      have hk_le_erase : (k : ℕ) ≤ (s.erase i).card := le_trans hk_le_t ht_le_erase
      have hs_card : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi_mem
      have hs_succ : (k : ℕ) + 1 ≤ s.card := by
        rw [← hs_card]
        exact Nat.succ_le_succ hk_le_erase
      simpa [s] using hs_succ

/-- Helper for Exercise 18.2.3: a prefix with at least `k` positive visits already carries the
recursive witness for the `k`th iterated return. -/
private lemma prefixHasIteratedReturn_of_le_card_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (x : S) :
    ∀ {k : ℕ+} {m : ℕ} {f : Fin m → S},
      (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card →
        prefixHasIteratedReturn x k m f := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m f h
      have h' : 1 ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card := by
        simpa using h
      rw [Finset.one_le_card] at h'
      rcases h' with ⟨i, hi_mem⟩
      have hi_props : 0 < (i : ℕ) ∧ f i = x := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi_mem
      exact (prefixHasIteratedReturn_one_iff_local x m f).2 ⟨i, hi_props.1, hi_props.2⟩
  | succ k ih =>
      intro m f h
      let s : Finset (Fin m) := Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x
      have hs_card_pos : 0 < s.card := by
        have hk_pos : 0 < ((k + 1 : ℕ+) : ℕ) := PNat.pos (k + 1)
        exact lt_of_lt_of_le hk_pos (by simpa [s] using h)
      have hs_nonempty : s.Nonempty := Finset.card_pos.mp hs_card_pos
      let i : Fin m := s.max' hs_nonempty
      have hi_mem : i ∈ s := Finset.max'_mem s hs_nonempty
      have hi_props : 0 < (i : ℕ) ∧ f i = x := by
        simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi_mem
      let toInitialSegment : Fin m → Fin i :=
        fun j ↦ if hj : (j : ℕ) < i then ⟨(j : ℕ), hj⟩ else ⟨0, hi_props.1⟩
      let t : Finset (Fin i) := Finset.univ.filter fun j : Fin i ↦
        0 < (j : ℕ) ∧ f ⟨j, Nat.lt_trans j.2 i.2⟩ = x
      have hk_le_erase : (k : ℕ) ≤ (s.erase i).card := by
        have hk_succ : (k : ℕ) + 1 ≤ s.card := by
          simpa [s, Nat.succ_eq_add_one] using h
        have hs_card : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi_mem
        have hk_succ' : Nat.succ (k : ℕ) ≤ Nat.succ (s.erase i).card := by
          simpa [hs_card, Nat.succ_eq_add_one] using hk_succ
        exact Nat.succ_le_succ_iff.mp hk_succ'
      have herase_le_t : (s.erase i).card ≤ t.card := by
        refine Finset.card_le_card_of_injOn toInitialSegment ?_ ?_
        · intro j hj
          have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
          have hj_mem : j ∈ s := (Finset.mem_erase.mp hj).2
          have hj_props : 0 < (j : ℕ) ∧ f j = x := by
            simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hj_mem
          have hj_le : j ≤ i := Finset.le_max' s j hj_mem
          have hj_lt : (j : ℕ) < i := by
            exact show (j : ℕ) < (i : ℕ) from
              lt_of_le_of_ne hj_le (fun hji ↦ hj_ne (Fin.ext hji))
          have hsegment : toInitialSegment j = ⟨(j : ℕ), hj_lt⟩ := by
            have hji : (j : ℕ) < i := hj_lt
            change
              (if h : (j : ℕ) < i then (⟨(j : ℕ), h⟩ : Fin i) else ⟨0, hi_props.1⟩) =
                ⟨(j : ℕ), hj_lt⟩
            rw [dif_pos hji]
          simp [t, hsegment, hj_props]
        · intro a₁ ha₁ b hb hEq
          have ha_ne : a₁ ≠ i := (Finset.mem_erase.mp ha₁).1
          have hb_ne : b ≠ i := (Finset.mem_erase.mp hb).1
          have ha_mem : a₁ ∈ s := (Finset.mem_erase.mp ha₁).2
          have hb_mem : b ∈ s := (Finset.mem_erase.mp hb).2
          have ha_le : a₁ ≤ i := Finset.le_max' s a₁ ha_mem
          have hb_le : b ≤ i := Finset.le_max' s b hb_mem
          have ha_lt : (a₁ : ℕ) < i := by
            exact show (a₁ : ℕ) < (i : ℕ) from
              lt_of_le_of_ne ha_le (fun hai ↦ ha_ne (Fin.ext hai))
          have hb_lt : (b : ℕ) < i := by
            exact show (b : ℕ) < (i : ℕ) from
              lt_of_le_of_ne hb_le (fun hbi ↦ hb_ne (Fin.ext hbi))
          have ha_seg : toInitialSegment a₁ = ⟨(a₁ : ℕ), ha_lt⟩ := by
            have ha' : (a₁ : ℕ) < i := ha_lt
            change
              (if h : (a₁ : ℕ) < i then (⟨(a₁ : ℕ), h⟩ : Fin i) else ⟨0, hi_props.1⟩) =
                ⟨(a₁ : ℕ), ha_lt⟩
            rw [dif_pos ha']
          have hb_seg : toInitialSegment b = ⟨(b : ℕ), hb_lt⟩ := by
            have hb' : (b : ℕ) < i := hb_lt
            change
              (if h : (b : ℕ) < i then (⟨(b : ℕ), h⟩ : Fin i) else ⟨0, hi_props.1⟩) =
                ⟨(b : ℕ), hb_lt⟩
            rw [dif_pos hb']
          have himage_eq : (⟨(a₁ : ℕ), ha_lt⟩ : Fin i) = ⟨(b : ℕ), hb_lt⟩ := by
            calc
              (⟨(a₁ : ℕ), ha_lt⟩ : Fin i) = toInitialSegment a₁ := by
                simpa using ha_seg.symm
              _ = toInitialSegment b := hEq
              _ = (⟨(b : ℕ), hb_lt⟩ : Fin i) := by
                simpa using hb_seg
          exact Fin.ext (congrArg (fun z : Fin i ↦ (z : ℕ)) himage_eq)
      have hk_le_t : (k : ℕ) ≤ t.card := le_trans hk_le_erase herase_le_t
      exact (prefixHasIteratedReturn_succ_iff_local x k m f).2 ⟨i, hi_props.1, hi_props.2, ih hk_le_t⟩

/-- Helper for Exercise 18.2.3: the recursive finite-prefix predicate is equivalent to the
corresponding prefix visit-count lower bound. -/
private lemma prefixHasIteratedReturn_iff_prefixVisitCountAtLeast_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (x : S) {k : ℕ+} {m : ℕ} {f : Fin m → S} :
    prefixHasIteratedReturn x k m f ↔
      (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = x).card := by
  constructor
  · exact prefixHasIteratedReturn_le_card_local x
  · exact prefixHasIteratedReturn_of_le_card_local x

/-- Helper for Exercise 18.2.3: the event `τ_[Y, x]^k < m` is equivalent to having at least `k`
positive visits to `x` in the first `m` coordinates of the path. -/
private lemma iteratedEntranceTime_lt_iff_prefixVisitCountAtLeast_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) (ω : ΩS) :
    ∀ (k : ℕ+) (m : ℕ),
      (τ_[Y, x]^k) ω < m ↔
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ Y i ω = x).card
  | k, m => by
      rw [iteratedEntranceTime_lt_iff_prefixHasIteratedReturn_local,
        prefixHasIteratedReturn_iff_prefixVisitCountAtLeast_local]

/-- Helper for Exercise 18.2.3: the event `τ_[Y, x]^k ≤ N` is equivalent to having at least `k`
positive visits to `x` in the first `N + 1` coordinates of the path. -/
private lemma iteratedEntranceTime_le_iff_prefixVisitCountAtLeast_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) (ω : ΩS) :
    ∀ (k : ℕ+) (N : ℕ),
      (τ_[Y, x]^k) ω ≤ N ↔
        (k : ℕ) ≤
          (Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card
  | k, N => by
      have hbound :
          (τ_[Y, x]^k) ω ≤ N ↔ (τ_[Y, x]^k) ω < N + 1 := by
        simpa using (ENat.lt_coe_add_one_iff (m := (τ_[Y, x]^k) ω) (n := N)).symm
      constructor
      · intro h
        exact (iteratedEntranceTime_lt_iff_prefixVisitCountAtLeast_local Y x ω k (N + 1)).1
          (hbound.mp h)
      · intro h
        exact hbound.mpr
          ((iteratedEntranceTime_lt_iff_prefixVisitCountAtLeast_local Y x ω k (N + 1)).2 h)

/-- Helper for Exercise 18.2.3: every bounded prefix count of visits to `x` injects into the full
set of positive visit times, so its cardinality is bounded by the total positive-visit encard. -/
private lemma prefixHitCount_le_positiveVisitEncard_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) (ω : ΩS) (N : ℕ) :
    ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card : ℕ∞) ≤
      (positiveVisitSet Y x ω).encard := by
  let s : Set (Fin (N + 1)) := {i : Fin (N + 1) | 0 < (i : ℕ) ∧ Y i ω = x}
  have hs_subset : (fun i : Fin (N + 1) ↦ (i : ℕ)) '' s ⊆ positiveVisitSet Y x ω := by
    intro n hn
    rcases hn with ⟨i, hi, rfl⟩
    exact ⟨Nat.succ_le_of_lt hi.1, hi.2⟩
  calc
    ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card : ℕ∞) = s.encard := by
      calc
        ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card : ℕ∞)
            = s.toFinset.card := by
                simp [s]
        _ = s.encard := by
                symm
                exact Set.encard_eq_coe_toFinset_card s
    _ = ((fun i : Fin (N + 1) ↦ (i : ℕ)) '' s).encard := by
      symm
      exact Fin.val_injective.encard_image s
    _ ≤ (positiveVisitSet Y x ω).encard := Set.encard_mono hs_subset

/-- Helper for Exercise 18.2.3: among positive integers, exactly `m` indices satisfy `k ≤ m`. -/
private lemma count_pnat_le_eq_local (m : ℕ) :
    Measure.count {k : ℕ+ | (k : ℕ) ≤ m} = m := by
  let s : Set ℕ+ := {k : ℕ+ | (k : ℕ) ≤ m}
  have himage : Equiv.pnatEquivNat '' s = {n : ℕ | n < m} := by
    ext n
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k.natPred + 1 ≤ m := by
        simpa [s, PNat.natPred_add_one] using hk
      exact lt_of_lt_of_le (Nat.lt_succ_self k.natPred) hk'
    · intro hn
      refine ⟨n.succPNat, ?_, by simp [Equiv.pnatEquivNat]⟩
      simpa [s] using Nat.succ_le_of_lt hn
  calc
    Measure.count s = Measure.count (Equiv.pnatEquivNat '' s) := by
      symm
      exact Measure.count_injective_image Equiv.pnatEquivNat.injective s
    _ = Measure.count {n : ℕ | n < m} := by
      rw [himage]
    _ = ({n : ℕ | n < m}).encard := by
      rw [Measure.count_apply MeasurableSet.of_discrete]
    _ = (m : ℝ≥0∞) := by
      exact_mod_cast (Set.Nat.encard_range m)

/-- Helper for Exercise 18.2.3: counting positive integers bounded by an `ℕ∞` value recovers
that bound. -/
private lemma count_pnat_le_enat_eq_local (t : ℕ∞) :
    Measure.count {k : ℕ+ | (k : ℕ∞) ≤ t} = t := by
  by_cases ht : t = ⊤
  · subst ht
    simpa [ENat.card_eq_top_of_infinite] using
      (Measure.count_univ : Measure.count (Set.univ : Set ℕ+) = ENat.card ℕ+)
  · calc
      Measure.count {k : ℕ+ | (k : ℕ∞) ≤ t}
        = Measure.count {k : ℕ+ | (k : ℕ) ≤ ENat.toNat t} := by
            congr 1
            ext k
            constructor
            · intro hk
              simpa using ENat.toNat_le_toNat hk ht
            · intro hk
              have hk' : ((k : ℕ) : ℕ∞) ≤ (ENat.toNat t : ℕ∞) := by
                exact (ENat.coe_le_coe).2 hk
              simpa [ENat.coe_toNat ht] using hk'
      _ = ENat.toNat t := by
            simpa using count_pnat_le_eq_local (ENat.toNat t)
      _ = (t : ℝ≥0∞) := by
            exact_mod_cast ENat.coe_toNat ht

/-- Helper for Exercise 18.2.3: a finite iterated entrance time is equivalent to having at
least `k` positive visits to `x`, expressed through the full positive-visit encard. -/
private lemma iteratedEntranceTime_lt_top_iff_le_positiveVisitEncard_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) (ω : ΩS) (k : ℕ+) :
    (τ_[Y, x]^k) ω < ⊤ ↔ (k : ℕ∞) ≤ (positiveVisitSet Y x ω).encard := by
  constructor
  · intro hτ
    let N : ℕ := ENat.toNat ((τ_[Y, x]^k) ω)
    have hτ_ne_top : (τ_[Y, x]^k) ω ≠ ⊤ := ne_of_lt hτ
    have hτ_le : (τ_[Y, x]^k) ω ≤ N := by
      simp [N, ENat.coe_toNat hτ_ne_top]
    have hk_le_prefix :
        (k : ℕ∞) ≤
          ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card : ℕ∞) := by
      exact_mod_cast (iteratedEntranceTime_le_iff_prefixVisitCountAtLeast_local Y x ω k N).1 hτ_le
    exact hk_le_prefix.trans (prefixHitCount_le_positiveVisitEncard_local Y x ω N)
  · intro hk
    obtain ⟨t, ht_subset, ht_card⟩ := Set.exists_subset_encard_eq (s := positiveVisitSet Y x ω) hk
    have ht_finite : t.Finite := Set.finite_of_encard_eq_coe (by simpa using ht_card)
    let tfin : Finset ℕ := ht_finite.toFinset
    have htfin_card_enat : (tfin.card : ℕ∞) = (k : ℕ∞) := by
      rw [← ht_finite.encard_eq_coe_toFinset_card]
      simpa [tfin] using ht_card
    have htfin_card : tfin.card = (k : ℕ) := ENat.coe_inj.mp htfin_card_enat
    have htfin_nonempty : tfin.Nonempty := by
      apply Finset.card_pos.mp
      rw [htfin_card]
      exact k.2
    let N : ℕ := tfin.max' htfin_nonempty
    let toPrefix : ℕ → Fin (N + 1) :=
      fun n ↦
        if hn : n ∈ tfin then
          ⟨n, Nat.lt_succ_of_le (Finset.le_max' tfin n hn)⟩
        else 0
    have hk_le_prefix :
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card := by
      have hcard_le :
          tfin.card ≤ (Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = x).card := by
        refine Finset.card_le_card_of_injOn toPrefix ?_ ?_
        · intro n hn
          have hn_t : n ∈ t := by
            simpa [tfin] using hn
          have hn_props : 1 ≤ n ∧ Y n ω = x := ht_subset hn_t
          have htoPrefix : toPrefix n = ⟨n, Nat.lt_succ_of_le (Finset.le_max' tfin n hn)⟩ := by
            by_cases hmem : n ∈ tfin
            · simp [toPrefix, hmem]
            · exact (hmem hn).elim
          have hprefix_val : ((toPrefix n : Fin (N + 1)) : ℕ) = n := by
            rw [htoPrefix]
          have hpos : 0 < ((toPrefix n : Fin (N + 1)) : ℕ) := by
            simpa [hprefix_val] using Nat.succ_le_iff.mp hn_props.1
          have hstate : Y (toPrefix n) ω = x := by
            simpa [hprefix_val] using hn_props.2
          refine Finset.mem_filter.mpr ?_
          refine ⟨by simp, ?_⟩
          exact ⟨show (0 : Fin (N + 1)) < toPrefix n from hpos, hstate⟩
        · intro n₁ hn₁ n₂ hn₂ hEq
          have hvals :
              ((toPrefix n₁ : Fin (N + 1)) : ℕ) = ((toPrefix n₂ : Fin (N + 1)) : ℕ) := by
            exact congrArg (fun i : Fin (N + 1) ↦ (i : ℕ)) hEq
          have hn₁_val : ((toPrefix n₁ : Fin (N + 1)) : ℕ) = n₁ := by
            have htoPrefix :
                toPrefix n₁ = ⟨n₁, Nat.lt_succ_of_le (Finset.le_max' tfin n₁ hn₁)⟩ := by
              by_cases hmem : n₁ ∈ tfin
              · simp [toPrefix, hmem]
              · exact (hmem hn₁).elim
            rw [htoPrefix]
          have hn₂_val : ((toPrefix n₂ : Fin (N + 1)) : ℕ) = n₂ := by
            have htoPrefix :
                toPrefix n₂ = ⟨n₂, Nat.lt_succ_of_le (Finset.le_max' tfin n₂ hn₂)⟩ := by
              by_cases hmem : n₂ ∈ tfin
              · simp [toPrefix, hmem]
              · exact (hmem hn₂).elim
            rw [htoPrefix]
          calc
            n₁ = ((toPrefix n₁ : Fin (N + 1)) : ℕ) := hn₁_val.symm
            _ = ((toPrefix n₂ : Fin (N + 1)) : ℕ) := hvals
            _ = n₂ := hn₂_val
      rw [htfin_card] at hcard_le
      exact hcard_le
    have hτ_le : (τ_[Y, x]^k) ω ≤ N :=
      (iteratedEntranceTime_le_iff_prefixVisitCountAtLeast_local Y x ω k N).2 hk_le_prefix
    exact lt_of_le_of_lt hτ_le (by simp)

/-- Helper for Exercise 18.2.3: the exact entrance slice at time `n` for the `k`th entrance
into `x`. -/
private def entranceSlice
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) (k : ℕ+) (n : ℕ) : Set ΩS :=
  {ω | (τ_[Y, x]^k) ω = n}

/-- Helper for Exercise 18.2.3: the finite entrance event is the union of its exact-time
slices. -/
private lemma finiteEntranceEvent_eq_iUnion_entranceSlice_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) (k : ℕ+) :
    {ω | (τ_[Y, x]^k) ω < ⊤} = ⋃ n : ℕ, entranceSlice Y x k n := by
  ext ω
  constructor
  · intro hω
    refine Set.mem_iUnion.2 ⟨ENat.toNat ((τ_[Y, x]^k) ω), ?_⟩
    have hne : (τ_[Y, x]^k) ω ≠ ⊤ := ne_of_lt hω
    simp [entranceSlice, ENat.coe_toNat hne]
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
    simp [entranceSlice] at hn
    simpa [hn]

/-- Helper for Exercise 18.2.3: the generated history filtration is monotone in the time index. -/
private lemma generatedFiltrationSpace_mono_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) {m n : ℕ} (hmn : m ≤ n) :
    generatedFiltrationSpace Y m ≤ generatedFiltrationSpace Y n := by
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hmn) le_rfl

/-- Helper for Exercise 18.2.3: every coordinate `Y i` is measurable with respect to the
generated history filtration at any later time `n ≥ i`. -/
private lemma measurable_process_generated_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) {i n : ℕ} (hi : i ≤ n) :
    @Measurable ΩS S (generatedFiltrationSpace Y n) _ (Y i) := by
  exact Measurable.of_comap_le <|
    le_iSup_of_le i <| le_iSup_of_le hi le_rfl

/-- Helper for Exercise 18.2.3: the state event `{ω | Y i ω = x}` is measurable in every
generated history filtration that already contains time `i`. -/
private lemma measurableSet_stateEvent_generated_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) {i n : ℕ} (hi : i ≤ n) :
    MeasurableSet[generatedFiltrationSpace Y n] {ω | Y i ω = x} := by
  let hYi : @Measurable ΩS S (generatedFiltrationSpace Y n) _ (Y i) :=
    measurable_process_generated_local (Y := Y) hi
  change MeasurableSet[generatedFiltrationSpace Y n] ((Y i) ⁻¹' ({x} : Set S))
  exact hYi (MeasurableSet.singleton x)

/-- Helper for Exercise 18.2.3: the bounded entrance event `{τ_[Y, x]^k ≤ N}` is measurable
with respect to the history sigma-algebra at time `N`. -/
private lemma iteratedEntranceTime_le_measurable_generated_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) :
    ∀ (k : ℕ+) (N : ℕ),
      MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, x]^k) ω ≤ N} := by
  intro k N
  induction k using PNat.recOn generalizing N with
  | one =>
      have hEq :
          {ω | (τ_[Y, x]^1) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), {ω | Y j ω = x} := by
        ext ω
        simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
          (MeasureTheory.hittingAfter_le_iff
            (u := Y) (s := ({x} : Set S)) (n := 1) (ω := ω) (i := N))
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      exact measurableSet_stateEvent_generated_local
        (Y := Y) x (hi := (Finset.mem_Icc.mp hj).2)
  | succ k ih =>
      let slice : ℕ → Set ΩS := fun j =>
        {ω | (τ_[Y, x]^k) ω < j} ∩ {ω | Y j ω = x}
      have hEq :
          {ω | (τ_[Y, x]^(k + 1)) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), slice j := by
        ext ω
        constructor
        · intro hω
          rcases
              (iteratedEntranceTime_succ_le_iff_existsHitAfter_local Y x ω k N).1 hω with
            ⟨j, hτj, hjN, hjx⟩
          have hj_pos : 0 < j := by
            cases j with
            | zero => simpa using hτj
            | succ j => exact Nat.succ_pos j
          exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨Finset.mem_Icc.mpr ⟨hj_pos, hjN⟩,
            ⟨hτj, hjx⟩⟩⟩
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨j, hω⟩
          rcases Set.mem_iUnion.1 hω with ⟨hj, hslice⟩
          exact (iteratedEntranceTime_succ_le_iff_existsHitAfter_local Y x ω k N).2
            ⟨j, hslice.1, (Finset.mem_Icc.mp hj).2, hslice.2⟩
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      have hj_le : j ≤ N := (Finset.mem_Icc.mp hj).2
      have hlt_N :
          MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, x]^k) ω < j} := by
        cases j with
        | zero =>
            have hj_false : ¬ 0 ∈ (Finset.Icc 1 N : Finset ℕ) := by
              simpa using hj
            exact False.elim (hj_false hj)
        | succ j =>
            have hle_j :
                MeasurableSet[generatedFiltrationSpace Y j]
                  {ω | (τ_[Y, x]^k) ω ≤ j} :=
              ih j
            have hle_N :
                MeasurableSet[generatedFiltrationSpace Y N]
                  {ω | (τ_[Y, x]^k) ω ≤ j} := by
              have hmono := generatedFiltrationSpace_mono_local
                (Y := Y) (Nat.le_trans (Nat.le_succ j) hj_le)
              exact hmono (s := {ω | (τ_[Y, x]^k) ω ≤ j}) hle_j
            simpa [ENat.lt_coe_add_one_iff] using hle_N
      exact hlt_N.inter (measurableSet_stateEvent_generated_local (Y := Y) x (hi := hj_le))

/-- Helper for Exercise 18.2.3: the strict bounded entrance event `{τ_[Y, x]^k < N}` is
measurable with respect to the history sigma-algebra at time `N`. -/
private lemma iteratedEntranceTime_lt_measurable_generated_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Y : ℕ → ΩS → S) (x : S) (k : ℕ+) :
    ∀ N : ℕ,
      MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, x]^k) ω < N} := by
  intro N
  cases N with
  | zero =>
      simpa using (MeasurableSet.empty : MeasurableSet (∅ : Set ΩS))
  | succ N =>
      have hle_N :
          MeasurableSet[generatedFiltrationSpace Y (N + 1)] {ω | (τ_[Y, x]^k) ω ≤ N} := by
        have hle_N_base :
            MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, x]^k) ω ≤ N} :=
          iteratedEntranceTime_le_measurable_generated_local (Y := Y) x k N
        have hmono := generatedFiltrationSpace_mono_local (Y := Y) (Nat.le_succ N)
        exact hmono (s := {ω | (τ_[Y, x]^k) ω ≤ N}) hle_N_base
      simpa [ENat.lt_coe_add_one_iff] using hle_N

/-- Helper for Exercise 18.2.3: exact entrance slices are measurable in the ambient
sigma-algebra. -/
private lemma entranceSlice_measurable
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    {κ : ℕ → Kernel S S} {P : S → ProbabilityMeasure ΩS} {X : ℕ → ΩS → S}
    [IsMarkovProcessRealization κ P X] (x : S) (k : ℕ+) (n : ℕ) :
    MeasurableSet (entranceSlice X x k n) := by
  have hslice_meas_gen :
      MeasurableSet[generatedFiltrationSpace X n] (entranceSlice X x k n) := by
    have hEq :
        entranceSlice X x k n =
          {ω | (τ_[X, x]^k) ω ≤ n} \ {ω | (τ_[X, x]^k) ω < n} := by
      ext ω
      constructor
      · intro hω
        have hτ : (τ_[X, x]^k) ω = n := by
          simpa [entranceSlice] using hω
        constructor
        · simp [hτ]
        · simp [hτ]
      · intro hω
        have hτ : (τ_[X, x]^k) ω = n := by
          exact le_antisymm hω.1 (le_of_not_gt hω.2)
        simpa [entranceSlice] using hτ
    rw [hEq]
    exact
      (iteratedEntranceTime_le_measurable_generated_local (Y := X) x k n).diff
        (iteratedEntranceTime_lt_measurable_generated_local (Y := X) x k n)
  exact (generatedFiltrationSpace_le_ambient (X := X)
    (inferInstance : IsMarkovProcessRealization κ P X).measurable_process n) _ hslice_meas_gen

/-- Helper for Exercise 18.2.3: the positive visit count from time `1` equals the number of
finite iterated entrance times into the same state. -/
private lemma totalVisitsFromOne_eq_countFiniteIteratedEntrances_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Xq : ℕ → ΩS → S) (x : S) (ω : ΩS) :
    totalVisitsFrom Xq x 1 ω = Measure.count {k : ℕ+ | (τ_[Xq, x]^k) ω < ⊤} := by
  calc
    totalVisitsFrom Xq x 1 ω = Measure.count {n : ℕ | 1 ≤ n ∧ Xq n ω = x} := by
      rw [totalVisitsFrom_eq_count]
    _ = (positiveVisitSet Xq x ω).encard := by
      rw [Measure.count_apply MeasurableSet.of_discrete]
      simp [positiveVisitSet]
    _ = Measure.count {k : ℕ+ | (k : ℕ∞) ≤ (positiveVisitSet Xq x ω).encard} := by
      symm
      exact count_pnat_le_enat_eq_local ((positiveVisitSet Xq x ω).encard)
    _ = Measure.count {k : ℕ+ | (τ_[Xq, x]^k) ω < ⊤} := by
      congr 1
      ext k
      simpa using
        (iteratedEntranceTime_lt_top_iff_le_positiveVisitEncard_local Xq x ω k).symm

/-- Helper for Exercise 18.2.3: pathwise, the indicator series of finite iterated entrance
times is the counting measure of the finite-entrance index set. -/
private lemma tsum_iteratedEntranceIndicators_eq_countFiniteIteratedEntrances_local
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {ΩS : Type*} [MeasurableSpace ΩS]
    (Xq : ℕ → ΩS → S) (x : S) (ω : ΩS) :
    (∑' k : ℕ+,
      Set.indicator {ω' | (τ_[Xq, x]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω) =
        Measure.count {k : ℕ+ | (τ_[Xq, x]^k) ω < ⊤} := by
  rw [Measure.count_apply MeasurableSet.of_discrete]
  calc
    (∑' k : ℕ+,
        Set.indicator {ω' | (τ_[Xq, x]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω) =
          ∑' _ : {k : ℕ+ | (τ_[Xq, x]^k) ω < ⊤}, (1 : ℝ≥0∞) := by
            symm
            simpa [Set.indicator_apply] using
              (tsum_subtype
                (s := {k : ℕ+ | (τ_[Xq, x]^k) ω < ⊤})
                (f := fun _ : ℕ+ ↦ (1 : ℝ≥0∞)))
    _ = ENat.card {k : ℕ+ | (τ_[Xq, x]^k) ω < ⊤} := by
          simpa using
            (ENNReal.tsum_one :
              ∑' _ : {k : ℕ+ | (τ_[Xq, x]^k) ω < ⊤}, (1 : ℝ≥0∞) =
                ENat.card {k : ℕ+ | (τ_[Xq, x]^k) ω < ⊤})
    _ = ({k : ℕ+ | (τ_[Xq, x]^k) ω < ⊤}).encard := by
          rw [ENat.card_coe_set_eq]

/-- Helper for Exercise 18.2.3: rewrite the positive-time diagonal Green function as the series of
finite iterated-entrance probabilities. -/
private lemma greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities_local
    {d : ℕ}
    {ΩS : Type*} [MeasurableSpace ΩS]
    {κ : ℕ → Kernel (LatticePoint d) (LatticePoint d)}
    {Pq : LatticePoint d → ProbabilityMeasure ΩS}
    {Xq : ℕ → ΩS → LatticePoint d}
    [IsMarkovProcessRealization κ Pq Xq] (x : LatticePoint d) :
    (G[Pq, Xq; 1]) x x =
      ∑' k : ℕ+, ENNReal.ofReal ((Pq x : Measure ΩS).real {ω | (τ_[Xq, x]^k) ω < ⊤}) := by
  have hτ_meas : ∀ k : ℕ+, MeasurableSet {ω | (τ_[Xq, x]^k) ω < ⊤} := by
    intro k
    rw [finiteEntranceEvent_eq_iUnion_entranceSlice_local (Y := Xq) (x := x) k]
    exact MeasurableSet.iUnion fun n =>
      entranceSlice_measurable (κ := κ) (P := Pq) (X := Xq) x k n
  -- Proof comment: normalize the positive-time Green function to the expected count of finite
  -- iterated entrances, then expand that count into the indicator series over `ℕ+`.
  calc
    (G[Pq, Xq; 1]) x x = ∫⁻ ω, totalVisitsFrom Xq x 1 ω ∂(Pq x : Measure ΩS) := by
      rw [greenFunctionFrom_eq_lintegral_totalVisitsFrom]
    _ = ∫⁻ ω, Measure.count {k : ℕ+ | (τ_[Xq, x]^k) ω < ⊤} ∂(Pq x : Measure ΩS) := by
          refine lintegral_congr_ae ?_
          filter_upwards [] with ω
          rw [totalVisitsFromOne_eq_countFiniteIteratedEntrances_local Xq x ω]
    _ = ∫⁻ ω,
          ∑' k : ℕ+,
            Set.indicator {ω' | (τ_[Xq, x]^k) ω' < ⊤} (fun _ ↦ (1 : ENNReal)) ω
          ∂(Pq x : Measure ΩS) := by
            refine lintegral_congr_ae ?_
            filter_upwards [] with ω
            symm
            exact tsum_iteratedEntranceIndicators_eq_countFiniteIteratedEntrances_local Xq x ω
    _ = ∑' k : ℕ+,
          ∫⁻ ω,
            Set.indicator {ω' | (τ_[Xq, x]^k) ω' < ⊤} (fun _ ↦ (1 : ENNReal)) ω
          ∂(Pq x : Measure ΩS) := by
            rw [lintegral_tsum fun k ↦
              (measurable_const.indicator (hτ_meas k)).aemeasurable]
    _ = ∑' k : ℕ+, (Pq x : Measure ΩS) {ω | (τ_[Xq, x]^k) ω < ⊤} := by
          refine tsum_congr fun k ↦ ?_
          simpa using
            (lintegral_indicator_one (μ := (Pq x : Measure ΩS))
              (s := {ω | (τ_[Xq, x]^k) ω < ⊤}) (hτ_meas k))
    _ = ∑' k : ℕ+, ENNReal.ofReal ((Pq x : Measure ΩS).real {ω | (τ_[Xq, x]^k) ω < ⊤}) := by
          refine tsum_congr fun k ↦ ?_
          simp [MeasureTheory.measureReal_def]

/-- Helper for Exercise 18.2.3: the full diagonal Green function splits into the time-`0`
visit and the strictly positive-time tail. -/
private lemma greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf_general
    {d : ℕ}
    {ΩS : Type*} [MeasurableSpace ΩS]
    {κ : ℕ → Kernel (LatticePoint d) (LatticePoint d)}
    {Pq : LatticePoint d → ProbabilityMeasure ΩS}
    {Xq : ℕ → ΩS → LatticePoint d}
    [IsMarkovProcessRealization κ Pq Xq] (x : LatticePoint d) :
    (G[Pq, Xq]) x x = 1 + (G[Pq, Xq; 1]) x x := by
  let hreal : IsMarkovProcessRealization κ Pq Xq := inferInstance
  let hproc : IsStochasticProcess Xq := fun n ↦ hreal.measurable_process n
  have hzero :
      (Pq x : Measure ΩS) {ω | Xq 0 ω = x} = 1 := by
    have hpreimage :
        {ω | Xq 0 ω = x} = Xq 0 ⁻¹' ({x} : Set (LatticePoint d)) := by
      ext ω
      simp
    -- Proof comment: under the law started from `x`, the process sits at `x` at time `0`.
    calc
        (Pq x : Measure ΩS) {ω | Xq 0 ω = x}
          = ((Pq x : Measure ΩS).map (Xq 0)) ({x} : Set (LatticePoint d)) := by
              rw [hpreimage]
              rw [← Measure.map_apply (hreal.measurable_process 0) (MeasurableSet.singleton x)]
      _ = Measure.dirac x ({x} : Set (LatticePoint d)) := by
            rw [hreal.initial_eq x]
      _ = 1 := by
            simp
  -- Proof comment: separate the `n = 0` term from the full Green series and rewrite the
  -- remaining tail as the positive-time Green function.
  calc
    (G[Pq, Xq]) x x = ∑' n : ℕ, (Pq x : Measure ΩS) {ω | Xq n ω = x} := by
      rw [greenFunction_eq_tsum_stateProbabilities Pq Xq hproc x x]
    _ = (Pq x : Measure ΩS) {ω | Xq 0 ω = x} +
        ∑' n : ℕ, ite (n = 0) 0 ((Pq x : Measure ΩS) {ω | Xq n ω = x}) := by
          classical
          simpa [eq_comm] using
            (ENNReal.tsum_eq_add_tsum_ite
              (f := fun n : ℕ ↦ (Pq x : Measure ΩS) {ω | Xq n ω = x}) 0)
    _ = 1 + ∑' n : ℕ, ite (n = 0) 0 ((Pq x : Measure ΩS) {ω | Xq n ω = x}) := by
          simp [hzero]
    _ = 1 + ∑' n : ℕ, (Pq x : Measure ΩS) {ω | 0 < n ∧ Xq n ω = x} := by
          congr 1
          refine tsum_congr fun n ↦ ?_
          by_cases hn : n = 0
          · subst hn
            simp
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            simp [hn, hnpos]
    _ = 1 + (G[Pq, Xq; 1]) x x := by
          rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities Pq Xq hproc x x]

/-- Helper for Exercise 18.2.3: a shifted geometric series of `ENNReal.ofReal` terms stays
finite when the ratio lies in `[0, 1)`. -/
private lemma ennrealOfRealTsumGeometricSucc_lt_top_general {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) :
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1)) < ⊤ := by
  have hsum : Summable (fun n : ℕ ↦ q ^ (n + 1)) :=
    (_root_.summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq_nonneg hq_lt_one)
  -- Proof comment: nonnegative summable real terms remain finite after the termwise cast.
  calc
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1))
        = ENNReal.ofReal (∑' n : ℕ, q ^ (n + 1)) := by
            rw [ENNReal.ofReal_tsum_of_nonneg]
            · intro n
              exact pow_nonneg hq_nonneg _
            · exact hsum
    _ < ⊤ := by
          simp

/-- Helper for Exercise 18.2.3: reindexing the shifted power series along `ℕ+ ≃ ℕ` preserves its
value. -/
private lemma pnatShiftedPowerSeries_eq_natShiftedPowerSeries (r : ℝ) :
    (∑' k : ℕ+, ENNReal.ofReal (r * r ^ k.natPred)) =
      ∑' n : ℕ, ENNReal.ofReal (r * r ^ n) := by
  let g : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (r * r ^ n)
  simpa [g] using (Equiv.tsum_eq Equiv.pnatEquivNat g)

/-- Helper for Exercise 18.2.3: Theorem 17.29 rewrites the iterated-entrance probabilities at
`x` as the shifted power series of `F(x, x)`. -/
private lemma iteratedEntranceProbabilitySeries_eq_selfPowerSeries
    {d : ℕ}
    {ΩS : Type*} [MeasurableSpace ΩS]
    {κ : ℕ → Kernel (LatticePoint d) (LatticePoint d)}
    {Pq : LatticePoint d → ProbabilityMeasure ΩS}
    {Xq : ℕ → ΩS → LatticePoint d}
    [IsMarkovProcessRealization κ Pq Xq] (x : LatticePoint d) :
    (∑' k : ℕ+, ENNReal.ofReal ((Pq x : Measure ΩS).real {ω | (τ_[Xq, x]^k) ω < ⊤})) =
      ∑' n : ℕ, ENNReal.ofReal (((F[Pq, Xq]) x x) ^ (n + 1)) := by
  let r : ℝ := (F[Pq, Xq]) x x
  -- Proof comment: substitute the Chapter 17 entrance-time formula and reindex `ℕ+` by `ℕ`.
  calc
    (∑' k : ℕ+, ENNReal.ofReal ((Pq x : Measure ΩS).real {ω | (τ_[Xq, x]^k) ω < ⊤})) =
        ∑' k : ℕ+, ENNReal.ofReal (r * r ^ k.natPred) := by
          refine tsum_congr fun k ↦ ?_
          simpa [r] using congrArg ENNReal.ofReal
            (iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
              (κ := κ) (P := Pq) (X := Xq) x x k)
    _ = ∑' n : ℕ, ENNReal.ofReal (r * r ^ n) := by
          exact pnatShiftedPowerSeries_eq_natShiftedPowerSeries r
    _ = ∑' n : ℕ, ENNReal.ofReal (r ^ (n + 1)) := by
          refine tsum_congr fun n ↦ ?_
          rw [pow_succ, mul_comm]
    _ = ∑' n : ℕ, ENNReal.ofReal (((F[Pq, Xq]) x x) ^ (n + 1)) := by
          simp [r]

/-- Helper for Exercise 18.2.3: the positive-time diagonal Green tail is the shifted power
series of the return probability. -/
private lemma greenFunctionFromOneSelf_eq_tsum_selfPowers_general
    {d : ℕ}
    {ΩS : Type*} [MeasurableSpace ΩS]
    {κ : ℕ → Kernel (LatticePoint d) (LatticePoint d)}
    {Pq : LatticePoint d → ProbabilityMeasure ΩS}
    {Xq : ℕ → ΩS → LatticePoint d}
    [IsMarkovProcessRealization κ Pq Xq] (x : LatticePoint d) :
    (G[Pq, Xq; 1]) x x =
      ∑' n : ℕ, ENNReal.ofReal (((F[Pq, Xq]) x x) ^ (n + 1)) := by
  -- Proof comment: normalize the positive-time Green tail through the iterated entrance-time API.
  exact
    (greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities_local
      (κ := κ) (Pq := Pq) (Xq := Xq) x).trans
      (iteratedEntranceProbabilitySeries_eq_selfPowerSeries
        (κ := κ) (Pq := Pq) (Xq := Xq) x)

/-- Helper for Exercise 18.2.3: an infinite diagonal Green value forces recurrence. -/
private lemma isRecurrentState_of_greenFunctionSelf_eq_top_general
    {d : ℕ}
    {ΩS : Type*} [MeasurableSpace ΩS]
    {κ : ℕ → Kernel (LatticePoint d) (LatticePoint d)}
    {Pq : LatticePoint d → ProbabilityMeasure ΩS}
    {Xq : ℕ → ΩS → LatticePoint d}
    [IsMarkovProcessRealization κ Pq Xq] (x : LatticePoint d) (hx : (G[Pq, Xq]) x x = ⊤) :
    IsRecurrentState Pq Xq x := by
  have hq_nonneg : 0 ≤ (F[Pq, Xq]) x x := measureReal_nonneg
  have hq_le_one : (F[Pq, Xq]) x x ≤ 1 := by
    rw [everHitsProbability_def]
    exact measureReal_le_one
  -- Proof comment: a nonrecurrent state would force a finite geometric Green tail, contradicting
  -- the assumed infinite diagonal Green value.
  by_contra htrans
  have hq_lt_one : (F[Pq, Xq]) x x < 1 := by
    rw [IsRecurrentState] at htrans
    exact lt_of_le_of_ne hq_le_one (by simpa [eq_comm] using htrans)
  have htail_lt_top :
      ∑' n : ℕ, ENNReal.ofReal (((F[Pq, Xq]) x x) ^ (n + 1)) < ⊤ :=
    ennrealOfRealTsumGeometricSucc_lt_top_general hq_nonneg hq_lt_one
  have hgreen_lt_top : (G[Pq, Xq]) x x < ⊤ := by
    calc
      (G[Pq, Xq]) x x = 1 + (G[Pq, Xq; 1]) x x := by
        rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf_general
          (κ := κ) (Pq := Pq) (Xq := Xq)]
      _ = 1 + ∑' n : ℕ, ENNReal.ofReal (((F[Pq, Xq]) x x) ^ (n + 1)) := by
            rw [greenFunctionFromOneSelf_eq_tsum_selfPowers_general
              (κ := κ) (Pq := Pq) (Xq := Xq)]
      _ < ⊤ := by
            exact ENNReal.add_lt_top.2 ⟨by simp, htail_lt_top⟩
  exact (ne_of_lt hgreen_lt_top) hx

/-- Helper for Exercise 18.2.3: recurrence of a state forces the diagonal Green value to be
infinite. -/
private lemma greenFunctionSelf_eq_top_of_isRecurrentState_general
    {d : ℕ}
    {ΩS : Type*} [MeasurableSpace ΩS]
    {κ : ℕ → Kernel (LatticePoint d) (LatticePoint d)}
    {Pq : LatticePoint d → ProbabilityMeasure ΩS}
    {Xq : ℕ → ΩS → LatticePoint d}
    [IsMarkovProcessRealization κ Pq Xq] (x : LatticePoint d) (hx : IsRecurrentState Pq Xq x) :
    (G[Pq, Xq]) x x = ⊤ := by
  -- Proof comment: recurrence makes every power of `F(x, x)` equal to `1`, so the positive-time
  -- Green tail is already the divergent series of ones.
  calc
    (G[Pq, Xq]) x x = 1 + (G[Pq, Xq; 1]) x x := by
      rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf_general
        (κ := κ) (Pq := Pq) (Xq := Xq)]
    _ = 1 + ∑' n : ℕ, ENNReal.ofReal (1 ^ (n + 1 : ℕ)) := by
          rw [greenFunctionFromOneSelf_eq_tsum_selfPowers_general
            (κ := κ) (Pq := Pq) (Xq := Xq)]
          rw [IsRecurrentState] at hx
          simp [hx]
    _ = ⊤ := by
          simp

/-- Helper for Exercise 18.2.3: recurrence of the base walk forces recurrence of the origin for
the canonical free difference walk. -/
private theorem differenceOriginRecurrent_of_baseRecurrent
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    {P : LatticePoint d → ProbabilityMeasure Ω} {X : ℕ → Ω → LatticePoint d}
    {Ωq : Type*} [MeasurableSpace Ωq]
    {Pq : LatticePoint d → ProbabilityMeasure Ωq} {Xq : ℕ → Ωq → LatticePoint d}
    [IsMarkovKernel (discreteMatrixKernel p)]
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^ n)
      Pq Xq]
    (htranslation : IsTranslationInvariantStepMatrix p)
    (hrec : IsRecurrentMarkovChain P X) :
    IsRecurrentState Pq Xq (0 : LatticePoint d) := by
  let ν0 : PMF (LatticePoint d) := (discreteMatrixKernel p 0).toPMF
  let baseMass : ℕ → ENNReal :=
    fun n ↦ ((discreteMatrixKernel p ^ n) (0 : LatticePoint d)) ({0} : Set (LatticePoint d))
  let diffMass : ℕ → ENNReal :=
    fun n ↦
      ((discreteMatrixKernel (differenceStepMatrix ν0) ^ n) (0 : LatticePoint d))
        ({0} : Set (LatticePoint d))
  let hbaseReal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let hdiffReal :
      IsMarkovProcessRealization
        (fun n ↦ discreteMatrixKernel (differenceStepMatrix ν0) ^ n) Pq Xq := inferInstance
  let hbaseProc : IsStochasticProcess X := fun n ↦ hbaseReal.measurable_process n
  let hdiffProc : IsStochasticProcess Xq := fun n ↦ hdiffReal.measurable_process n
  have hbase_series_top : ∑' n : ℕ, baseMass n = ⊤ := by
    have htop :
        (G[P, X]) (0 : LatticePoint d) (0 : LatticePoint d) = ⊤ :=
      greenFunctionSelf_eq_top_of_isRecurrentState_general
        (κ := fun n ↦ discreteMatrixKernel p ^ n) (Pq := P) (Xq := X)
        (0 : LatticePoint d) (hrec 0)
    have hseries :
        ∑' n : ℕ, (P (0 : LatticePoint d) : Measure Ω) {ω | X n ω = (0 : LatticePoint d)} = ⊤ := by
      simpa [greenFunction_eq_tsum_stateProbabilities P X hbaseProc (0 : LatticePoint d)
        (0 : LatticePoint d)] using htop
    calc
      ∑' n : ℕ, baseMass n
          = ∑' n : ℕ,
              (P (0 : LatticePoint d) : Measure Ω) {ω | X n ω = (0 : LatticePoint d)} := by
                refine tsum_congr fun n ↦ ?_
                have hpreimage :
                    {ω | X n ω = (0 : LatticePoint d)} =
                      X n ⁻¹' ({(0 : LatticePoint d)} : Set (LatticePoint d)) := by
                  ext ω
                  simp
                calc
                  baseMass n = ((discreteMatrixKernel p ^ n) (0 : LatticePoint d))
                      ({(0 : LatticePoint d)} : Set (LatticePoint d)) := rfl
                  _ = ((P (0 : LatticePoint d) : Measure Ω).map (X n))
                        ({(0 : LatticePoint d)} : Set (LatticePoint d)) := by
                          rw [← hbaseReal.transition_eq (0 : LatticePoint d) n]
                  _ = (P (0 : LatticePoint d) : Measure Ω) {ω | X n ω = (0 : LatticePoint d)} := by
                          simpa [hpreimage] using
                            (Measure.map_apply
                              (μ := (P (0 : LatticePoint d) : Measure Ω))
                              (f := X n)
                              (s := ({(0 : LatticePoint d)} : Set (LatticePoint d)))
                              (hbaseReal.measurable_process n)
                              (MeasurableSet.singleton (0 : LatticePoint d)))
      _ = ⊤ := hseries
  by_contra hnotrec
  have hdiff_series_ne_top : ∑' n : ℕ, diffMass n ≠ ⊤ := by
    intro htop
    apply hnotrec
    apply isRecurrentState_of_greenFunctionSelf_eq_top_general
      (κ := fun n ↦ discreteMatrixKernel (differenceStepMatrix ν0) ^ n)
      (Pq := Pq) (Xq := Xq) (0 : LatticePoint d)
    have hseries :
        ∑' n : ℕ,
          (Pq (0 : LatticePoint d) : Measure Ωq) {ω | Xq n ω = (0 : LatticePoint d)} = ⊤ := by
      calc
        ∑' n : ℕ,
            (Pq (0 : LatticePoint d) : Measure Ωq) {ω | Xq n ω = (0 : LatticePoint d)}
            = ∑' n : ℕ, diffMass n := by
                refine tsum_congr fun n ↦ ?_
                have hpreimage :
                    {ω | Xq n ω = (0 : LatticePoint d)} =
                      Xq n ⁻¹' ({(0 : LatticePoint d)} : Set (LatticePoint d)) := by
                  ext ω
                  simp
                calc
                  (Pq (0 : LatticePoint d) : Measure Ωq) {ω | Xq n ω = (0 : LatticePoint d)}
                      = ((Pq (0 : LatticePoint d) : Measure Ωq).map (Xq n))
                          ({(0 : LatticePoint d)} : Set (LatticePoint d)) := by
                            simpa [hpreimage] using
                              (Measure.map_apply
                                (μ := (Pq (0 : LatticePoint d) : Measure Ωq))
                                (f := Xq n)
                                (s := ({(0 : LatticePoint d)} : Set (LatticePoint d)))
                                (hdiffReal.measurable_process n)
                                (MeasurableSet.singleton (0 : LatticePoint d))).symm
                  _ = ((discreteMatrixKernel (differenceStepMatrix ν0) ^ n) (0 : LatticePoint d))
                        ({(0 : LatticePoint d)} : Set (LatticePoint d)) := by
                          rw [hdiffReal.transition_eq (0 : LatticePoint d) n]
                  _ = diffMass n := rfl
        _ = ⊤ := htop
    simpa [greenFunction_eq_tsum_stateProbabilities Pq Xq hdiffProc (0 : LatticePoint d)
      (0 : LatticePoint d)] using hseries
  have hdiff_real_summable : Summable (fun n : ℕ ↦ (diffMass n).toReal) :=
    ENNReal.summable_toReal hdiff_series_ne_top
  have hdiff_real_shift_summable :
      Summable (fun n : ℕ ↦ (diffMass (n + 1)).toReal) := by
    simpa using ((_root_.summable_nat_add_iff 1).2 hdiff_real_summable)
  have hbase_even_summable :
      Summable (fun n : ℕ ↦ (baseMass (2 * n)).toReal) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hdiff_real_summable
    · intro n
      exact ENNReal.toReal_nonneg
    · intro n
      simpa [baseMass, diffMass] using
        baseEvenReturnMass_toReal_le_differenceReturnMass
          (p := p) htranslation n
  have hbase_odd_majorant_summable :
      Summable (fun n : ℕ ↦ (diffMass n).toReal + (diffMass (n + 1)).toReal) :=
    hdiff_real_summable.add hdiff_real_shift_summable
  have hbase_odd_summable :
      Summable (fun n : ℕ ↦ (baseMass (2 * n + 1)).toReal) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hbase_odd_majorant_summable
    · intro n
      exact ENNReal.toReal_nonneg
    · intro n
      have hcmp :
          (baseMass (2 * n + 1)).toReal ≤
            (((diffMass n).toReal + (diffMass (n + 1)).toReal) / 2) := by
        simpa only [baseMass, diffMass] using
          baseOddReturnMass_toReal_le_differenceReturnPairAverage
            (p := p) htranslation n
      have hnonneg₀ : 0 ≤ (diffMass n).toReal := ENNReal.toReal_nonneg
      have hnonneg₁ : 0 ≤ (diffMass (n + 1)).toReal := ENNReal.toReal_nonneg
      linarith
  have hbase_real_summable : Summable (fun n : ℕ ↦ (baseMass n).toReal) :=
    Summable.even_add_odd hbase_even_summable hbase_odd_summable
  have hbase_series_eq :
      ∑' n : ℕ, baseMass n = ENNReal.ofReal (∑' n : ℕ, (baseMass n).toReal) := by
    calc
      ∑' n : ℕ, baseMass n
          = ∑' n : ℕ, ENNReal.ofReal ((baseMass n).toReal) := by
              refine tsum_congr fun n ↦ ?_
              exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = ENNReal.ofReal (∑' n : ℕ, (baseMass n).toReal) := by
            rw [ENNReal.ofReal_tsum_of_nonneg]
            · intro n
              exact ENNReal.toReal_nonneg
            · exact hbase_real_summable
  have hbase_series_ne_top : ∑' n : ℕ, baseMass n ≠ ⊤ := by
    rw [hbase_series_eq]
    exact ENNReal.ofReal_ne_top
  exact hbase_series_ne_top hbase_series_top

/-- Helper for Exercise 18.2.3: once the origin is recurrent for the free difference walk,
irreducibility propagates that recurrence to every displacement. -/
private theorem differenceStepMatrix_recurrent_of_originRecurrent
    {d : ℕ} (ν : PMF (LatticePoint d))
    {Ωq : Type*}
    [MeasurableSpace Ωq]
    {Pq : LatticePoint d → ProbabilityMeasure Ωq} {Xq : ℕ → Ωq → LatticePoint d}
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (differenceStepMatrix ν) ^ n) Pq Xq]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d))
      (discreteMatrixKernel (differenceStepMatrix ν))]
    (horigin : IsRecurrentState Pq Xq (0 : LatticePoint d)) :
    IsRecurrentMarkovChain Pq Xq := by
  let hqreal :
      IsMarkovProcessRealization
        (fun n ↦ discreteMatrixKernel (differenceStepMatrix ν) ^ n) Pq Xq := inferInstance
  let hqproc : IsStochasticProcess Xq := fun n ↦ hqreal.measurable_process n
  have hirr : IsIrreducibleMarkovChain Pq Xq :=
    isIrreducibleMarkovChain_of_discreteMatrixKernel_isIrreducible
      (p := differenceStepMatrix ν) (P := Pq) (X := Xq)
  intro z
  by_cases hz : z = 0
  · subst hz
    simpa using horigin
  · have hgreen_pos : 0 < (G[Pq, Xq; 1]) (0 : LatticePoint d) z := by
      exact
        (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
          (κ := fun n ↦ discreteMatrixKernel (differenceStepMatrix ν) ^ n) Pq Xq).1
          hirr (by simpa [eq_comm] using hz)
    have hhit_pos : 0 < (F[Pq, Xq]) (0 : LatticePoint d) z := by
      exact (greenFunctionFrom_one_pos_iff_everHitsProbability_pos
        Pq Xq hqproc (0 : LatticePoint d) z).1 hgreen_pos
    -- Proof comment: irreducibility provides positive communication from `0` to `z`, and
    -- Theorem 17.35 transports recurrence along that positive-probability connection.
    exact
      isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
        (P := Pq) (X := Xq)
        (κ := fun n ↦ discreteMatrixKernel (differenceStepMatrix ν) ^ n)
        horigin hhit_pos

/-- Helper for Exercise 18.2.3: recurrence of the base walk should force recurrence of the free
difference walk. -/
theorem differenceStepMatrix_recurrent_of_baseRecurrent
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    {P : LatticePoint d → ProbabilityMeasure Ω} {X : ℕ → Ω → LatticePoint d}
    {Ωq : Type*} [MeasurableSpace Ωq]
    {Pq : LatticePoint d → ProbabilityMeasure Ωq} {Xq : ℕ → Ωq → LatticePoint d}
    [IsMarkovKernel (discreteMatrixKernel p)]
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    [IsMarkovProcessRealization
      (fun n ↦
        discreteMatrixKernel (differenceStepMatrix ((discreteMatrixKernel p 0).toPMF)) ^ n)
      Pq Xq]
    (htranslation : IsTranslationInvariantStepMatrix p)
    (hrec : IsRecurrentMarkovChain P X)
    (haperiodic : IsAperiodic (discreteMatrixKernel p)) :
    IsRecurrentMarkovChain Pq Xq := by
  let ν0 : PMF (LatticePoint d) := (discreteMatrixKernel p 0).toPMF
  have horigin : IsRecurrentState Pq Xq (0 : LatticePoint d) :=
    differenceOriginRecurrent_of_baseRecurrent
      (p := p) (P := P) (X := X) (Pq := Pq) (Xq := Xq)
      htranslation hrec
  letI :
      Kernel.IsIrreducible
        (Measure.count : Measure (LatticePoint d))
        (discreteMatrixKernel (differenceStepMatrix ν0)) :=
    differenceStepMatrix_isIrreducible_of_aperiodic
      (p := p) htranslation haperiodic
  -- Proof comment: once recurrence at the origin is established, irreducibility of the canonical
  -- difference walk propagates it to every displacement.
  exact differenceStepMatrix_recurrent_of_originRecurrent (ν := ν0) horigin

/-- Helper for Exercise 18.2.3: once the free difference walk is recurrent, every displacement
hits `0` almost surely. -/
lemma freeDifference_everHitsZero_eq_one
    {d : ℕ} (ν : PMF (LatticePoint d))
    {Pq : LatticePoint d → ProbabilityMeasure Ω'} {Xq : ℕ → Ω' → LatticePoint d}
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (differenceStepMatrix ν) ^ n) Pq Xq]
    (hqrec : IsRecurrentMarkovChain Pq Xq)
    (hqreachesZero :
      ∀ z : LatticePoint d,
        ∃ n : ℕ, 0 < n ∧
          0 < (discreteMatrixKernel (differenceStepMatrix ν) ^ n) z
            ({0} : Set (LatticePoint d))) :
    ∀ z : LatticePoint d, (F[Pq, Xq]) z 0 = 1 := by
  intro z
  rcases hqreachesZero z with ⟨n, hn, hmass⟩
  have hhit_pos : 0 < (F[Pq, Xq]) z 0 :=
    everHitsProbability_pos_of_positiveStepMass
      (κ := fun m ↦ discreteMatrixKernel (differenceStepMatrix ν) ^ m)
      (P := Pq) (X := Xq) hn hmass
  -- Proof comment: the chain is recurrent at the starting displacement `z`, and the positive
  -- finite-time step mass gives positive ever-hit probability to `0`; Theorem 17.35 upgrades that
  -- to almost-sure hitting.
  exact
    everHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos
      (P := Pq) (X := Xq)
      (κ := fun m ↦ discreteMatrixKernel (differenceStepMatrix ν) ^ m)
      (hqrec z) hhit_pos

/-- Helper for Exercise 18.2.3: absorbing a lattice step matrix at `0` freezes the state `0`
and leaves all other rows unchanged. -/
def absorbAtZeroStepMatrix {d : ℕ} (q : LatticePoint d → LatticePoint d → ENNReal) :
    LatticePoint d → LatticePoint d → ENNReal :=
  -- Proof comment: replace the row at `0` by the Dirac mass at `0` and leave every other row
  -- unchanged.
  fun z w ↦ if z = 0 then if w = 0 then 1 else 0 else q z w

/-- Helper for Exercise 18.2.3: the absorbed-at-zero matrix has the Dirac row at `0`. -/
lemma absorbAtZeroStepMatrix_apply_zero
    {d : ℕ} (q : LatticePoint d → LatticePoint d → ENNReal)
    (w : LatticePoint d) :
    absorbAtZeroStepMatrix q 0 w = if w = 0 then 1 else 0 := by
  -- Proof comment: evaluating the absorbed matrix at the absorbing state immediately exposes the
  -- inserted Dirac row.
  simp [absorbAtZeroStepMatrix]

/-- Helper for Exercise 18.2.3: away from `0`, the absorbed-at-zero matrix agrees with the
original step matrix. -/
lemma absorbAtZeroStepMatrix_apply_of_ne
    {d : ℕ} (q : LatticePoint d → LatticePoint d → ENNReal)
    {z w : LatticePoint d} (hz : z ≠ 0) :
    absorbAtZeroStepMatrix q z w = q z w := by
  -- Proof comment: only the `0`-row is modified by the absorption construction.
  simp [absorbAtZeroStepMatrix, hz]

/-- Helper for Exercise 18.2.3: if `q` is stochastic, then the absorbed-at-zero matrix is also
stochastic. -/
lemma absorbAtZeroStepMatrix_isStochastic
    {d : ℕ} (q : LatticePoint d → LatticePoint d → ENNReal)
    (hq : IsStochasticMatrix q) :
    IsStochasticMatrix (absorbAtZeroStepMatrix q) := by
  intro z
  by_cases hz : z = 0
  · subst hz
    -- Proof comment: the new row at `0` is exactly the Dirac mass, so its total mass is `1`.
    rw [tsum_eq_single (0 : LatticePoint d)]
    · simp [absorbAtZeroStepMatrix]
    · intro w hw
      simp [absorbAtZeroStepMatrix, hw]
  · -- Proof comment: away from `0`, stochasticity is inherited from the original matrix `q`.
    simp [absorbAtZeroStepMatrix, hz, hq z]

/-- Helper for Exercise 18.2.3: an off-diagonal coalescent row is the product of the two
independent one-step rows. -/
lemma coalescentRow_eq_prod_of_ne
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    {x y : LatticePoint d} (hxy : x ≠ y) :
    discreteMatrixKernel (independentCoalescentMatrix p) (x, y) =
      (discreteMatrixKernel p x).prod (discreteMatrixKernel p y) := by
  refine Measure.ext_of_singleton ?_
  intro b
  rcases b with ⟨z, w⟩
  have hsingleton :
      ({((z, w) : LatticePoint d × LatticePoint d)} :
          Set (LatticePoint d × LatticePoint d)) =
        ({z} : Set (LatticePoint d)) ×ˢ ({w} : Set (LatticePoint d)) := by
    ext s
    simp
  -- Proof comment: compare both rows on singleton rectangles and then unfold the off-diagonal
  -- branch of `independentCoalescentMatrix`.
  rw [discreteMatrixKernel_apply_singleton, hsingleton]
  rw [Measure.prod_prod]
  rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
  rw [independentCoalescentMatrix_apply_of_ne (p := p) hxy]

/-- Helper for Exercise 18.2.3: subtracting the coordinates of the product row yields the free
difference kernel at the current displacement. -/
lemma productPairDifferenceRow_eq_freeDifferenceKernel
    {d : ℕ} (ν : PMF (LatticePoint d))
    {p : LatticePoint d → LatticePoint d → ENNReal}
    (hkernel : discreteMatrixKernel p = dirac_convolution_kernel ν.toMeasure)
    (x y : LatticePoint d) :
    Measure.map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2)
      ((discreteMatrixKernel p x).prod (discreteMatrixKernel p y)) =
      discreteMatrixKernel (differenceStepMatrix ν) (x - y) := by
  let μ : Measure (LatticePoint d) := ν.toMeasure
  have hx :
      discreteMatrixKernel p x =
        Measure.map (fun z : LatticePoint d ↦ x + z) μ := by
    -- Proof comment: the row at `x` is the translate of the common increment law.
    rw [hkernel, dirac_convolution_kernel_apply, Measure.dirac_conv]
  have hy :
      discreteMatrixKernel p y =
        Measure.map (fun z : LatticePoint d ↦ y + z) μ := by
    -- Proof comment: the same translation formula applies to the row at `y`.
    rw [hkernel, dirac_convolution_kernel_apply, Measure.dirac_conv]
  have hcomp₁ :
      (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2) ∘
          Prod.map (fun z : LatticePoint d ↦ x + z) (fun z : LatticePoint d ↦ y + z) =
        fun s : LatticePoint d × LatticePoint d ↦ (x - y) + (s.1 - s.2) := by
    funext s
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hcomp₂ :
      (fun s : LatticePoint d × LatticePoint d ↦ (x - y) + (s.1 - s.2)) =
        (fun z : LatticePoint d ↦ (x - y) + z) ∘
          (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2) := by
    rfl
  rw [hx, hy]
  -- Proof comment: move the subtraction map through the translated product measure and recognize
  -- the resulting translated difference-step law.
  calc
    Measure.map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2)
        ((Measure.map (fun z : LatticePoint d ↦ x + z) μ).prod
          (Measure.map (fun z : LatticePoint d ↦ y + z) μ)) =
      Measure.map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2)
        ((μ.prod μ).map
          (Prod.map (fun z : LatticePoint d ↦ x + z) (fun z : LatticePoint d ↦ y + z))) := by
            rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    _ =
        Measure.map (fun s : LatticePoint d × LatticePoint d ↦ (x - y) + (s.1 - s.2))
          (μ.prod μ) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            simp [hcomp₁]
    _ =
        Measure.map (fun z : LatticePoint d ↦ (x - y) + z)
          (Measure.map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2) (μ.prod μ)) := by
            rw [hcomp₂]
            rw [← Measure.map_map (μ := μ.prod μ)
              (f := fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2)
              (g := fun z : LatticePoint d ↦ (x - y) + z) (by fun_prop) (by fun_prop)]
    _ =
        Measure.map (fun z : LatticePoint d ↦ (x - y) + z)
          (differenceStepPMF ν).toMeasure := by
            simp [differenceStepPMF, μ]
    _ = discreteMatrixKernel (differenceStepMatrix ν) (x - y) := by
          rw [differenceStepMatrix_kernel_eq_diracConvolutionKernel,
            dirac_convolution_kernel_apply, Measure.dirac_conv]

/-- Helper for Exercise 18.2.3: one coalescent step from a diagonal state has no off-diagonal
mass. -/
private theorem coalescentDiagonalOffDiagonalMass_eq_zero
    {d : ℕ} {p : LatticePoint d → LatticePoint d → ENNReal}
    (x : LatticePoint d) :
    discreteMatrixKernel (independentCoalescentMatrix p) (x, x)
      {s : LatticePoint d × LatticePoint d | s.1 ≠ s.2} = 0 := by
  let offDiag : Set (LatticePoint d × LatticePoint d) := {s | s.1 ≠ s.2}
  rw [discreteMatrixKernel_apply,
    Measure.sum_apply _ (show MeasurableSet offDiag from MeasurableSet.of_discrete)]
  refine ENNReal.tsum_eq_zero.mpr ?_
  intro s
  rcases s with ⟨z, w⟩
  by_cases hs : z ≠ w
  · -- Proof comment: every off-diagonal singleton already has zero diagonal-row mass.
    simpa [Measure.smul_apply, Measure.dirac_apply', offDiag, hs] using
      independentCoalescentMatrix_apply_diag_of_ne (p := p) (x := x) hs
  · -- Proof comment: diagonal singletons lie outside `offDiag`, so the restricted Dirac mass
    -- vanishes immediately.
    simp [Measure.smul_apply, Measure.dirac_apply', offDiag, hs]

/-- Helper for Exercise 18.2.3: subtracting a diagonal coalescent row collapses to the absorbing
Dirac row at `0`. -/
private lemma coalescentDiagonalDifferenceRow_eq_absorbZeroRow
    {d : ℕ} {p q : LatticePoint d → LatticePoint d → ENNReal}
    [IsMarkovKernel (discreteMatrixKernel p)]
    (x : LatticePoint d) :
    Measure.map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2)
      (discreteMatrixKernel (independentCoalescentMatrix p) (x, x)) =
      discreteMatrixKernel (absorbAtZeroStepMatrix q) 0 := by
  have hp : IsStochasticMatrix p := by
    intro z
    let hprob : IsProbabilityMeasure (discreteMatrixKernel p z) :=
      (inferInstance : IsMarkovKernel (discreteMatrixKernel p)).isProbabilityMeasure z
    simpa [discreteMatrixKernel_univ] using hprob.measure_univ
  have hstochastic : IsStochasticMatrix (independentCoalescentMatrix p) := by
    exact independentCoalescentMatrix_isStochasticMatrix (p := p) hp
  refine Measure.ext_of_singleton ?_
  intro w
  by_cases hw : w = 0
  · subst hw
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
    have hpreimage :
        (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2) ⁻¹'
            ({0} : Set (LatticePoint d)) =
          {s : LatticePoint d × LatticePoint d | s.1 = s.2} := by
      ext s
      simp [sub_eq_zero]
    rw [hpreimage]
    let offDiag : Set (LatticePoint d × LatticePoint d) := {s | s.1 ≠ s.2}
    have hOff :
        discreteMatrixKernel (independentCoalescentMatrix p) (x, x) offDiag = 0 := by
      simpa [offDiag] using coalescentDiagonalOffDiagonalMass_eq_zero (p := p) x
    have hDiag :
        discreteMatrixKernel (independentCoalescentMatrix p) (x, x)
          {s : LatticePoint d × LatticePoint d | s.1 = s.2} = 1 := by
      have hcompl_zero :
          discreteMatrixKernel (independentCoalescentMatrix p) (x, x)
            ({s : LatticePoint d × LatticePoint d | s.1 = s.2}ᶜ) = 0 := by
        simpa [offDiag, Set.compl_setOf, not_not] using hOff
      calc
        discreteMatrixKernel (independentCoalescentMatrix p) (x, x)
            {s : LatticePoint d × LatticePoint d | s.1 = s.2} =
          discreteMatrixKernel (independentCoalescentMatrix p) (x, x) Set.univ := by
              exact
                measure_of_measure_compl_eq_zero
                  (μ := discreteMatrixKernel (independentCoalescentMatrix p) (x, x))
                  hcompl_zero
        _ = 1 := by
              simpa [discreteMatrixKernel_univ] using hstochastic (x, x)
    calc
      discreteMatrixKernel (independentCoalescentMatrix p) (x, x)
          {s : LatticePoint d × LatticePoint d | s.1 = s.2} = 1 := hDiag
      _ = discreteMatrixKernel (absorbAtZeroStepMatrix q) 0
            ({0} : Set (LatticePoint d)) := by
              rw [discreteMatrixKernel_apply_singleton, absorbAtZeroStepMatrix_apply_zero]
              simp
  · have hsubset :
        (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2) ⁻¹' ({w} : Set (LatticePoint d)) ⊆
          {s : LatticePoint d × LatticePoint d | s.1 ≠ s.2} := by
      intro s hs
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hs
      have hne : s.1 - s.2 ≠ 0 := by
        rwa [hs]
      exact fun hEq ↦ hne (sub_eq_zero.mpr hEq)
    let offDiag : Set (LatticePoint d × LatticePoint d) := {s | s.1 ≠ s.2}
    have hOff :
        discreteMatrixKernel (independentCoalescentMatrix p) (x, x) offDiag = 0 := by
      simpa [offDiag] using coalescentDiagonalOffDiagonalMass_eq_zero (p := p) x
    have hright :
        discreteMatrixKernel (absorbAtZeroStepMatrix q) 0 ({w} : Set (LatticePoint d)) = 0 := by
      rw [discreteMatrixKernel_apply_singleton, absorbAtZeroStepMatrix_apply_zero]
      simp [hw]
    have hleft :
        Measure.map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2)
            (discreteMatrixKernel (independentCoalescentMatrix p) (x, x))
            ({w} : Set (LatticePoint d)) = 0 := by
      refine le_antisymm ?_ bot_le
      calc
        Measure.map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2)
            (discreteMatrixKernel (independentCoalescentMatrix p) (x, x))
            ({w} : Set (LatticePoint d)) =
          discreteMatrixKernel (independentCoalescentMatrix p) (x, x)
            ((fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2) ⁻¹'
              ({w} : Set (LatticePoint d))) := by
                rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w)]
        _ ≤ discreteMatrixKernel (independentCoalescentMatrix p) (x, x) offDiag := by
              exact measure_mono hsubset
        _ = 0 := hOff
    rw [hleft, hright]

/-- Helper for Exercise 18.2.3: subtracting the coordinates of one coalescent step gives the
absorbed difference kernel. -/
lemma coalescentDifferenceRow_eq_absorbedDifferenceKernel
    {d : ℕ} (ν : PMF (LatticePoint d))
    {p : LatticePoint d → LatticePoint d → ENNReal}
    [IsMarkovKernel (discreteMatrixKernel p)]
    (hkernel : discreteMatrixKernel p = dirac_convolution_kernel ν.toMeasure)
    (x y : LatticePoint d) :
    Measure.map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2)
      (discreteMatrixKernel (independentCoalescentMatrix p) (x, y)) =
      discreteMatrixKernel (absorbAtZeroStepMatrix (differenceStepMatrix ν)) (x - y) := by
  -- Route correction: split the coalescent row into the diagonal Dirac case and the off-diagonal
  -- product case, rather than pushing a single singleton-normalization proof through both
  -- branches at once.
  by_cases hxy : x = y
  · subst hxy
    simpa [sub_self] using
      coalescentDiagonalDifferenceRow_eq_absorbZeroRow
        (p := p) (q := differenceStepMatrix ν) x
  · -- Proof comment: off the diagonal, subtracting the coordinates of the coalescent row recovers
    -- the free difference row, and absorption leaves that row unchanged away from `0`.
    rw [coalescentRow_eq_prod_of_ne (p := p) hxy]
    rw [productPairDifferenceRow_eq_freeDifferenceKernel (ν := ν) hkernel x y]
    have hdiff : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hrow :
        discreteMatrixKernel (absorbAtZeroStepMatrix (differenceStepMatrix ν)) (x - y) =
          discreteMatrixKernel (differenceStepMatrix ν) (x - y) := by
      refine Measure.ext_of_singleton ?_
      intro w
      rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
      rw [absorbAtZeroStepMatrix_apply_of_ne (q := differenceStepMatrix ν) hdiff]
    exact hrow.symm

/-- Helper for Exercise 18.2.3: pushing the coalescent `n`-step law through subtraction yields
the absorbed difference `n`-step law. -/
lemma coalescentDifferencePow_map_eq_absorbedDifferencePow
    {d : ℕ} (ν : PMF (LatticePoint d))
    {p : LatticePoint d → LatticePoint d → ENNReal}
    [IsMarkovKernel (discreteMatrixKernel p)]
    [IsMarkovKernel (discreteMatrixKernel (absorbAtZeroStepMatrix (differenceStepMatrix ν)))]
    (hkernel : discreteMatrixKernel p = dirac_convolution_kernel ν.toMeasure) :
    ∀ n : ℕ, ∀ x y : LatticePoint d,
      Measure.map (fun s : LatticePoint d × LatticePoint d ↦ s.1 - s.2)
        ((discreteMatrixKernel (independentCoalescentMatrix p) ^ n) (x, y)) =
        (discreteMatrixKernel (absorbAtZeroStepMatrix (differenceStepMatrix ν)) ^ n) (x - y) := by
  let κPair : Kernel (LatticePoint d × LatticePoint d) (LatticePoint d × LatticePoint d) :=
    discreteMatrixKernel (independentCoalescentMatrix p)
  let κAbs : Kernel (LatticePoint d) (LatticePoint d) :=
    discreteMatrixKernel (absorbAtZeroStepMatrix (differenceStepMatrix ν))
  let diff : LatticePoint d × LatticePoint d → LatticePoint d := fun s ↦ s.1 - s.2
  -- Route correction: prove the power transport by singleton extensionality and a flat
  -- Chapman-Kolmogorov induction, instead of keeping the successor step in a transport-heavy
  -- raw `lintegral` form.
  have hdiff_meas : Measurable diff := Measurable.of_discrete
  intro n
  induction n with
  | zero =>
      intro x y
      -- Proof comment: at time `0`, both sides are the Dirac mass at the initial difference.
      refine Measure.ext_of_singleton ?_
      intro w
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w)]
      simp only [pow_zero]
      change Measure.dirac (x, y) (diff ⁻¹' ({w} : Set (LatticePoint d))) =
        Measure.dirac (x - y) ({w} : Set (LatticePoint d))
      by_cases h : x - y = w
      · simp [Measure.dirac_apply', diff, h]
      · simp [Measure.dirac_apply', diff, h]
  | succ n ih =>
      intro x y
      -- Proof comment: rewrite the successor step through the pushed-forward `n`-step law, then
      -- replace the one-step coalescent row by the absorbed difference row.
      refine Measure.ext_of_singleton ?_
      intro w
      have hpreimage_meas :
          MeasurableSet (diff ⁻¹' ({w} : Set (LatticePoint d))) :=
        hdiff_meas (measurableSet_singleton w)
      calc
        Measure.map diff ((κPair ^ (n + 1)) (x, y)) ({w} : Set (LatticePoint d)) =
            ((κPair ^ (n + 1)) (x, y)) (diff ⁻¹' ({w} : Set (LatticePoint d))) := by
              rw [Measure.map_apply hdiff_meas (measurableSet_singleton w)]
        _ =
            ∫⁻ s : LatticePoint d × LatticePoint d,
              (κPair s) (diff ⁻¹' ({w} : Set (LatticePoint d))) ∂((κPair ^ n) (x, y)) := by
                rw [Kernel.pow_succ_apply_eq_lintegral κPair n (x, y) hpreimage_meas]
        _ =
            ∫⁻ s : LatticePoint d × LatticePoint d,
              Measure.map diff (κPair s) ({w} : Set (LatticePoint d)) ∂((κPair ^ n) (x, y)) := by
                refine lintegral_congr_ae <| Filter.Eventually.of_forall ?_
                intro s
                symm
                exact Measure.map_apply hdiff_meas (measurableSet_singleton w)
        _ =
            ∫⁻ s : LatticePoint d × LatticePoint d,
              κAbs (diff s) ({w} : Set (LatticePoint d)) ∂((κPair ^ n) (x, y)) := by
                refine lintegral_congr_ae <| Filter.Eventually.of_forall ?_
                intro s
                rcases s with ⟨a, b⟩
                have hrow : Measure.map diff (κPair (a, b)) = κAbs (a - b) := by
                  simpa [κPair, κAbs, diff] using
                    (coalescentDifferenceRow_eq_absorbedDifferenceKernel
                      (ν := ν) (p := p) hkernel a b)
                exact congrArg
                  (fun μ : Measure (LatticePoint d) ↦ μ ({w} : Set (LatticePoint d))) hrow
        _ =
            ∫⁻ z : LatticePoint d,
              κAbs z ({w} : Set (LatticePoint d))
                ∂Measure.map diff ((κPair ^ n) (x, y)) := by
                symm
                exact
                  MeasureTheory.lintegral_map'
                    (μ := ((κPair ^ n) (x, y)))
                    (f := fun z : LatticePoint d ↦ κAbs z ({w} : Set (LatticePoint d)))
                    (g := diff)
                    (Kernel.measurable_coe κAbs (measurableSet_singleton w)).aemeasurable
                    hdiff_meas.aemeasurable
        _ =
            ∫⁻ z : LatticePoint d,
              κAbs z ({w} : Set (LatticePoint d)) ∂((κAbs ^ n) (x - y)) := by
                rw [ih x y]
        _ = (κAbs ^ (n + 1)) (x - y) ({w} : Set (LatticePoint d)) := by
              rw [Kernel.pow_succ_apply_eq_lintegral κAbs n (x - y)
                (measurableSet_singleton w)]

/-- Helper for Exercise 18.2.3: finite-horizon zero-avoidance probabilities for the free
difference walk tend to `0` once the walk hits `0` almost surely. -/
theorem freeAvoidZeroProb_tendsto_zero
    {d : ℕ} {Ωq : Type*} [MeasurableSpace Ωq]
    {q : LatticePoint d → LatticePoint d → ENNReal}
    {Pq : LatticePoint d → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq]
    (hfreeHit : ∀ z : LatticePoint d, (F[Pq, Xq]) z 0 = 1)
    (z : LatticePoint d) :
    Tendsto
      (fun n ↦ (Pq z : Measure Ωq) {ω | ∀ m ≤ n, Xq m ω ≠ 0})
      atTop (nhds 0) := by
  -- Route correction: close the generic avoid-zero limit directly by continuity from above,
  -- without waiting on the absorbed-endpoint transport lemmas.
  let μ : Measure Ωq := (Pq z : Measure Ωq)
  let avoidUpTo : ℕ → Set Ωq := fun n ↦ {ω | ∀ m ≤ n, Xq m ω ≠ 0}
  let noHit : Set Ωq := {ω | ∀ m : ℕ, Xq m ω ≠ 0}
  let noPositiveHit : Set Ωq := {ω | ∀ m : ℕ, 0 < m → Xq m ω ≠ 0}
  let hitZero : Set Ωq := {ω | ∃ m : ℕ, 0 < m ∧ Xq m ω = 0}
  let hReal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq := inferInstance
  have hAvoid_meas : ∀ n : ℕ, MeasurableSet (avoidUpTo n) := by
    intro n
    have hrepr :
        avoidUpTo n = ⋂ m : ℕ, if m ≤ n then {ω | Xq m ω ≠ 0} else Set.univ := by
      ext ω
      simp [avoidUpTo]
    rw [hrepr]
    refine MeasurableSet.iInter fun m ↦ ?_
    by_cases hm : m ≤ n
    · have hNonzero :
          MeasurableSet ({ω | Xq m ω ≠ (0 : LatticePoint d)} : Set Ωq) := by
        rw [show ({ω | Xq m ω ≠ (0 : LatticePoint d)} : Set Ωq) =
            Xq m ⁻¹' ({0} : Set (LatticePoint d))ᶜ by
          ext ω
          simp]
        exact (hReal.measurable_process m) (measurableSet_singleton (0 : LatticePoint d)).compl
      simpa [hm] using hNonzero
    · simp [hm]
  have hNoPositiveHit_meas : MeasurableSet noPositiveHit := by
    have hrepr :
        noPositiveHit = ⋂ m : ℕ, if 0 < m then {ω | Xq m ω ≠ 0} else Set.univ := by
      ext ω
      simp [noPositiveHit]
    rw [hrepr]
    refine MeasurableSet.iInter fun m ↦ ?_
    by_cases hm : 0 < m
    · have hNonzero :
          MeasurableSet ({ω | Xq m ω ≠ (0 : LatticePoint d)} : Set Ωq) := by
        rw [show ({ω | Xq m ω ≠ (0 : LatticePoint d)} : Set Ωq) =
            Xq m ⁻¹' ({0} : Set (LatticePoint d))ᶜ by
          ext ω
          simp]
        exact (hReal.measurable_process m) (measurableSet_singleton (0 : LatticePoint d)).compl
      simpa [hm] using hNonzero
    · simp [hm]
  have hAntitone : Antitone avoidUpTo := by
    intro n m hnm ω hω k hk
    exact hω k (le_trans hk hnm)
  have hInter : (⋂ n : ℕ, avoidUpTo n) = noHit := by
    ext ω
    constructor
    · intro hω m
      exact (Set.mem_iInter.1 hω) m m le_rfl
    · intro hω
      refine Set.mem_iInter.2 ?_
      intro n
      exact fun m _ ↦ hω m
  have hHit_compl : hitZero = noPositiveHitᶜ := by
    ext ω
    simp [hitZero, noPositiveHit]
  have hNoHit_subset : noHit ⊆ noPositiveHit := by
    intro ω hω m hm
    exact hω m
  have hAvoid_tendsto :
      Tendsto (fun n ↦ μ (avoidUpTo n)) atTop (nhds (μ (⋂ n : ℕ, avoidUpTo n))) := by
    exact
      tendsto_measure_iInter_atTop
        (μ := μ)
        (s := avoidUpTo)
        (fun n ↦ (hAvoid_meas n).nullMeasurableSet)
        hAntitone
        ⟨0, by finiteness⟩
  have hHit_real : μ.real hitZero = 1 := by
    simpa [μ, hitZero, everHitsProbability_def] using hfreeHit z
  have hNoPositiveHit_real : μ.real noPositiveHit = 0 := by
    have hsum :
        μ.real noPositiveHit + μ.real hitZero = μ.real Set.univ := by
      rw [hHit_compl]
      simpa using measureReal_add_measureReal_compl (μ := μ) hNoPositiveHit_meas
    have huniv : μ.real Set.univ = 1 := by
      simp [μ]
    linarith
  have hNoPositiveHit_zero : μ noPositiveHit = 0 := by
    exact (measureReal_eq_zero_iff (μ := μ) (s := noPositiveHit)).1 hNoPositiveHit_real
  have hInter_zero : μ (⋂ n : ℕ, avoidUpTo n) = 0 := by
    rw [hInter]
    exact le_antisymm
      (le_trans (measure_mono hNoHit_subset) hNoPositiveHit_zero.le)
      bot_le
  -- Proof comment: continuity from above reduces bounded avoidance to the infinite no-hit event,
  -- and the almost-sure hit hypothesis makes that limit event null.
  simpa [μ, hInter_zero] using hAvoid_tendsto

/-- Helper for Exercise 18.2.3: the endpoint-refined bounded zero-avoidance event for the free
difference walk. -/
def avoidZeroUntilWithEndpoint {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → LatticePoint d) (n : ℕ) (w : LatticePoint d) : Set Ω :=
  -- Proof comment: this records both the prescribed endpoint `X n = w` and zero-avoidance up to
  -- time `n`.
  {ω | X n ω = w ∧ ∀ m ≤ n, X m ω ≠ 0}

/-- Helper for Exercise 18.2.3: the endpoint-refined bounded zero-avoidance event is measurable
with respect to the time-`n` history filtration. -/
lemma avoidZeroUntilWithEndpoint_measurableSet
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → LatticePoint d}
    (hX : ∀ n : ℕ, Measurable (X n)) (n : ℕ) (w : LatticePoint d) :
    MeasurableSet[generatedFiltrationSpace X n] (avoidZeroUntilWithEndpoint X n w) := by
  have hState :
      MeasurableSet[generatedFiltrationSpace X n] {ω | X n ω = w} := by
    have hXn : Measurable[generatedFiltrationSpace X n] (X n) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := X) n
    rw [show ({ω | X n ω = w} : Set Ω) = X n ⁻¹' ({w} : Set (LatticePoint d)) by
      ext ω
      simp]
    exact hXn (measurableSet_singleton w)
  have hAvoid :
      MeasurableSet[generatedFiltrationSpace X n] {ω | ∀ m ≤ n, X m ω ≠ 0} := by
    have hrepr :
        {ω | ∀ m ≤ n, X m ω ≠ 0} =
          ⋂ m : ℕ, if m ≤ n then {ω | X m ω ≠ 0} else Set.univ := by
      ext ω
      simp
    rw [hrepr]
    refine MeasurableSet.iInter fun m ↦ ?_
    by_cases hm : m ≤ n
    · have hXm : Measurable[generatedFiltrationSpace X n] (X m) := by
        exact Measurable.of_comap_le <|
          le_iSup_of_le m <| le_iSup_of_le hm le_rfl
      have hZero :
          MeasurableSet[generatedFiltrationSpace X n] {ω : Ω | X m ω = (0 : LatticePoint d)} := by
        rw [show ({ω : Ω | X m ω = (0 : LatticePoint d)} : Set Ω) =
            X m ⁻¹' ({0} : Set (LatticePoint d)) by
          ext ω
          simp]
        exact hXm (measurableSet_singleton (0 : LatticePoint d))
      have hNonzero :
          MeasurableSet[generatedFiltrationSpace X n] {ω : Ω | X m ω ≠ (0 : LatticePoint d)} := by
        rw [show ({ω : Ω | X m ω ≠ (0 : LatticePoint d)} : Set Ω) =
            ({ω : Ω | X m ω = (0 : LatticePoint d)} : Set Ω)ᶜ by
          ext ω
          simp]
        exact hZero.compl
      simpa [hm] using hNonzero
    · simp [hm]
  -- Proof comment: both the endpoint condition and the bounded zero-avoidance condition are
  -- determined by the time-`n` history, so their intersection is history measurable.
  have hrepr :
      avoidZeroUntilWithEndpoint X n w =
        {ω | X n ω = w} ∩ {ω | ∀ m ≤ n, X m ω ≠ 0} := by
    ext ω
    simp [avoidZeroUntilWithEndpoint]
  rw [hrepr]
  exact hState.inter hAvoid

/-- Helper for Exercise 18.2.3: the endpoint-refined bounded zero-avoidance event is empty at the
zero endpoint. -/
lemma avoidZeroUntilWithEndpoint_eq_empty_of_zero
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → LatticePoint d}
    (n : ℕ) :
    avoidZeroUntilWithEndpoint X n 0 = (∅ : Set Ω) := by
  ext ω
  constructor
  · intro hω
    -- Proof comment: if the endpoint is `0`, bounded zero-avoidance fails at time `n` itself.
    exact False.elim <| (hω.2 n le_rfl) hω.1
  · simp [avoidZeroUntilWithEndpoint]

/-- Helper for Exercise 18.2.3: on a history event that fixes `X n = y`, the next-step singleton
mass factors through the one-step row from `y`. -/
lemma measureInter_eq_mul_stepMass_of_stateEvent
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {q : LatticePoint d → LatticePoint d → ENNReal}
    {P : LatticePoint d → ProbabilityMeasure Ω}
    {X : ℕ → Ω → LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    (x y w : LatticePoint d) (n : ℕ) (A : Set Ω)
    (hA_meas : MeasurableSet A)
    (hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_state : ∀ ⦃ω : Ω⦄, ω ∈ A → X n ω = y) :
    (P x : Measure Ω) (A ∩ {ω | X (n + 1) ω = w}) =
      (discreteMatrixKernel q y ({w} : Set (LatticePoint d))) * (P x : Measure Ω) A := by
  -- Route correction: prove the history-slice identity from the one-step Markov property
  -- directly, so later absorbed-kernel arguments can reuse it as a stable API fact.
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel q) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hstep :
      ∀ x' : LatticePoint d, ∀ ⦃B : Set (LatticePoint d)⦄, MeasurableSet B → ∀ s : ℕ,
        (P x')⟦X (s + 1) ⁻¹' B | generatedFiltrationSpace X s⟧ =ᵐ[(P x' : Measure Ω)]
          fun ω ↦ ((discreteMatrixKernel q) (X s ω)).real B := by
    intro x' B hB s
    -- Proof comment: specialize the Markov-property owner theorem to one step and simplify `^ 1`.
    simpa [Nat.add_comm] using hReal.markov_property x' (A := B) hB s 1
  have hnext_meas : MeasurableSet (X (n + 1) ⁻¹' ({w} : Set (LatticePoint d))) := by
    exact (hReal.measurable_process (n + 1)) (measurableSet_singleton w)
  have hslice_real :
      μ.real (A ∩ {ω | X (n + 1) ω = w}) =
        (discreteMatrixKernel q y ({w} : Set (LatticePoint d))).toReal * μ.real A := by
    calc
      μ.real (A ∩ {ω | X (n + 1) ω = w}) =
          ∫ ω in A,
            Set.indicator (X (n + 1) ⁻¹' ({w} : Set (LatticePoint d))) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
              rw [← MeasureTheory.integral_indicator hA_meas]
              -- Proof comment: rewrite the sliced intersection as the indicator of the next-step
              -- singleton event restricted to the history event.
              simpa [Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                Set.inter_comm, smul_eq_mul] using
                (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                  (hA_meas.inter hnext_meas)).symm
      _ =
          ∫ ω in A, ((discreteMatrixKernel q ^ 1) (X n ω)).real ({w} : Set (LatticePoint d)) ∂μ := by
            symm
            -- Proof comment: reduce the sliced event to the one-step kernel mass seen from the
            -- time-`n` state.
            simpa [Nat.add_comm] using
              kernelPow_setIntegral_eq_on_history
                (κ₁ := discreteMatrixKernel q) (P := P) (X := X)
                hReal.measurable_process hstep x (A := ({w} : Set (LatticePoint d)))
                (measurableSet_singleton w) n 1 (B := A) hA_measFiltration
      _ = ∫ ω in A, (discreteMatrixKernel q y).real ({w} : Set (LatticePoint d)) ∂μ := by
            -- Proof comment: on `A`, the time-`n` state is frozen at `y`, so the integrand is
            -- constant.
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem hA_meas] with ω hω
            rw [hA_state hω]
            simp [pow_one]
      _ = (discreteMatrixKernel q y ({w} : Set (LatticePoint d))).toReal * μ.real A := by
            rw [show ((discreteMatrixKernel q) y).real ({w} : Set (LatticePoint d)) =
                (((discreteMatrixKernel q) y) ({w} : Set (LatticePoint d))).toReal by rfl]
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hslice_enn :
      μ (A ∩ {ω | X (n + 1) ω = w}) =
        (discreteMatrixKernel q y ({w} : Set (LatticePoint d))) * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff'
        (measure_lt_top μ _).ne
        (ENNReal.mul_ne_top
          (by exact (measure_lt_top (discreteMatrixKernel q y) ({w} : Set (LatticePoint d))).ne)
          (by exact (measure_lt_top μ A).ne))).mp ?_
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, mul_comm] using hslice_real
  simpa [μ] using hslice_enn

/-- Helper for Exercise 18.2.3: bounded zero-avoidance with nonzero endpoint has the same
probability as the absorbed difference kernel power at that endpoint. -/
theorem freeAvoidZeroEndpointProb_eq_absorbedEndpointMass
    {d : ℕ} {Ωq : Type*} [MeasurableSpace Ωq]
    {q : LatticePoint d → LatticePoint d → ENNReal}
    {Pq : LatticePoint d → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq]
    [IsMarkovKernel (discreteMatrixKernel (absorbAtZeroStepMatrix q))] :
    ∀ n : ℕ, ∀ z : LatticePoint d, ∀ {w : LatticePoint d}, w ≠ 0 →
      (Pq z : Measure Ωq) (avoidZeroUntilWithEndpoint Xq n w) =
        ((discreteMatrixKernel (absorbAtZeroStepMatrix q) ^ n) z)
          ({w} : Set (LatticePoint d)) := by
  let κAbs : Kernel (LatticePoint d) (LatticePoint d) :=
    discreteMatrixKernel (absorbAtZeroStepMatrix q)
  let hqreal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq := inferInstance
  intro n
  induction n with
  | zero =>
      intro z w hw
      have hset : avoidZeroUntilWithEndpoint Xq 0 w = {ω | Xq 0 ω = w} := by
        -- Proof comment: at time `0`, the endpoint condition already forces zero avoidance.
        ext ω
        constructor
        · intro hω
          exact hω.1
        · intro hω
          refine ⟨hω, ?_⟩
          intro m hm
          have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
          subst hm0
          intro hzero
          exact hw (hω.symm.trans hzero)
      rw [hset]
      rw [show ({ω | Xq 0 ω = w} : Set Ωq) = Xq 0 ⁻¹' ({w} : Set (LatticePoint d)) by
        ext ω
        simp]
      rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton w)]
      rw [hqreal.transition_eq z 0]
      simp [κAbs, Kernel.id_apply, hw]
  | succ n ih =>
      intro z w hw
      let μ : Measure Ωq := (Pq z : Measure Ωq)
      have hUnion :
          avoidZeroUntilWithEndpoint Xq (n + 1) w =
            ⋃ c : LatticePoint d,
              avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w} := by
            ext ω
            constructor
            · intro hω
              refine Set.mem_iUnion.2 ⟨Xq n ω, ?_⟩
              refine ⟨?_, hω.1⟩
              refine ⟨rfl, ?_⟩
              intro m hm
              exact hω.2 m (Nat.le_trans hm (Nat.le_succ _))
            · intro hω
              rcases Set.mem_iUnion.1 hω with ⟨c, hcω⟩
              refine ⟨hcω.2, ?_⟩
              intro m hm
              rcases Nat.eq_or_lt_of_le hm with rfl | hm_lt
              · intro hzero
                exact hw (hcω.2.symm.trans hzero)
              · exact hcω.1.2 m (Nat.le_of_lt_succ hm_lt)
      have hPairwise :
          Pairwise fun c d : LatticePoint d ↦
            Disjoint
              (avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w})
              (avoidZeroUntilWithEndpoint Xq n d ∩ {ω | Xq (n + 1) ω = w}) := by
            intro c d hcd
            refine Set.disjoint_left.2 ?_
            intro ω hc hd
            apply hcd
            exact hc.1.1.symm.trans hd.1.1
      have hMeas :
          ∀ c : LatticePoint d,
            MeasurableSet
              (avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w}) := by
            intro c
            have hAvoid_hist :
                MeasurableSet[generatedFiltrationSpace Xq n]
                  (avoidZeroUntilWithEndpoint Xq n c) :=
              avoidZeroUntilWithEndpoint_measurableSet hqreal.measurable_process n c
            have hAvoid :
                MeasurableSet (avoidZeroUntilWithEndpoint Xq n c) := by
              exact (generatedHistory_le_ambient Xq hqreal.measurable_process n) _ hAvoid_hist
            have hState :
                MeasurableSet ({ω | Xq (n + 1) ω = w} : Set Ωq) := by
              rw [show ({ω | Xq (n + 1) ω = w} : Set Ωq) =
                  Xq (n + 1) ⁻¹' ({w} : Set (LatticePoint d)) by
                ext ω
                simp]
              exact (hqreal.measurable_process (n + 1)) (measurableSet_singleton w)
            exact hAvoid.inter hState
      -- Proof comment: decompose by the time-`n` endpoint, factor each history slice through the
      -- free one-step row, and replace that row by the absorbed row away from `0`.
      calc
        μ (avoidZeroUntilWithEndpoint Xq (n + 1) w) =
            ∑' c : LatticePoint d,
              μ (avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w}) := by
                rw [hUnion]
                exact MeasureTheory.measure_iUnion hPairwise hMeas
        _ =
            ∑' c : LatticePoint d,
              (discreteMatrixKernel (absorbAtZeroStepMatrix q) c
                  ({w} : Set (LatticePoint d))) *
                ((κAbs ^ n) z) ({c} : Set (LatticePoint d)) := by
                  refine tsum_congr fun c ↦ ?_
                  by_cases hc : c ≠ 0
                  · have hAvoid_meas :
                        MeasurableSet[generatedFiltrationSpace Xq n]
                          (avoidZeroUntilWithEndpoint Xq n c) :=
                      avoidZeroUntilWithEndpoint_measurableSet hqreal.measurable_process n c
                    have hAvoid_meas_ambient :
                        MeasurableSet (avoidZeroUntilWithEndpoint Xq n c) := by
                      exact
                        (generatedHistory_le_ambient Xq hqreal.measurable_process n) _ hAvoid_meas
                    have hAvoid_measFiltration :
                        MeasurableSet[generatedFiltrationSpace Xq n]
                          (avoidZeroUntilWithEndpoint Xq n c) := hAvoid_meas
                    have hAvoid_state :
                        ∀ ⦃ω : Ωq⦄, ω ∈ avoidZeroUntilWithEndpoint Xq n c → Xq n ω = c := by
                      intro ω hω
                      exact hω.1
                    rw [measureInter_eq_mul_stepMass_of_stateEvent
                      (q := q) (P := Pq) (X := Xq) z c w n
                      (avoidZeroUntilWithEndpoint Xq n c)
                      hAvoid_meas_ambient hAvoid_measFiltration hAvoid_state]
                    rw [ih z hc, discreteMatrixKernel_apply_singleton,
                      discreteMatrixKernel_apply_singleton]
                    simpa [κAbs, absorbAtZeroStepMatrix, hc]
                  · have hczero : c = 0 := by simpa using hc
                    subst hczero
                    have hrow_zero :
                        discreteMatrixKernel (absorbAtZeroStepMatrix q) 0
                          ({w} : Set (LatticePoint d)) = 0 := by
                      rw [discreteMatrixKernel_apply_singleton, absorbAtZeroStepMatrix_apply_zero]
                      simp [hw]
                    rw [avoidZeroUntilWithEndpoint_eq_empty_of_zero (X := Xq) n]
                    rw [hrow_zero]
                    simp
        _ = ((κAbs ^ (n + 1)) z) ({w} : Set (LatticePoint d)) := by
              -- Proof comment: normalize the successor-step absorbed kernel integral to the same
              -- singleton-mass series used on the previous line.
              rw [Kernel.pow_succ_apply_eq_lintegral κAbs n z (measurableSet_singleton w)]
              rw [lintegralKernelApplySingleton_eq_tsum κAbs ((κAbs ^ n) z) w]

/-- Helper for Exercise 18.2.3: the nonzero mass of the absorbed difference walk is exactly the
bounded zero-avoidance probability of the free difference walk. -/
theorem absorbedDifferenceNonzeroMass_eq_freeAvoidZeroProb
    {d : ℕ} {Ωq : Type*} [MeasurableSpace Ωq]
    {q : LatticePoint d → LatticePoint d → ENNReal}
    {Pq : LatticePoint d → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq]
    [IsMarkovKernel (discreteMatrixKernel (absorbAtZeroStepMatrix q))]
    (z : LatticePoint d) (n : ℕ) :
    ((discreteMatrixKernel (absorbAtZeroStepMatrix q) ^ n) z)
        {w : LatticePoint d | w ≠ 0} =
      (Pq z : Measure Ωq) {ω | ∀ m ≤ n, Xq m ω ≠ 0} := by
  let κAbs : Kernel (LatticePoint d) (LatticePoint d) :=
    discreteMatrixKernel (absorbAtZeroStepMatrix q)
  let offZero : Set (LatticePoint d) := {w : LatticePoint d | w ≠ 0}
  let μ : Measure Ωq := (Pq z : Measure Ωq)
  let hqreal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq := inferInstance
  have hMass :
      ((κAbs ^ n) z) offZero =
        ∑' w : {u : LatticePoint d // u ∈ offZero},
          ((κAbs ^ n) z) ({(w : LatticePoint d)} : Set (LatticePoint d)) := by
    calc
      ((κAbs ^ n) z) offZero =
          ∑' w : LatticePoint d,
            offZero.indicator
              (fun w ↦ ((κAbs ^ n) z) ({w} : Set (LatticePoint d))) w := by
                simpa using
                  (Measure.tsum_indicator_apply_singleton ((κAbs ^ n) z) offZero
                    (show MeasurableSet offZero from MeasurableSet.of_discrete)).symm
      _ =
          ∑' w : {u : LatticePoint d // u ∈ offZero},
            ((κAbs ^ n) z) ({(w : LatticePoint d)} : Set (LatticePoint d)) := by
              rw [← tsum_subtype offZero
                (fun w : LatticePoint d ↦ ((κAbs ^ n) z) ({w} : Set (LatticePoint d)))]
  have hUnion :
      {ω | ∀ m ≤ n, Xq m ω ≠ 0} =
        ⋃ w : {u : LatticePoint d // u ∈ offZero}, avoidZeroUntilWithEndpoint Xq n w := by
      ext ω
      constructor
      · intro hω
        refine Set.mem_iUnion.2 ⟨⟨Xq n ω, hω n le_rfl⟩, ?_⟩
        exact ⟨rfl, hω⟩
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨w, hw⟩
        exact hw.2
  have hAvoid :
      μ {ω | ∀ m ≤ n, Xq m ω ≠ 0} =
        ∑' w : {u : LatticePoint d // u ∈ offZero},
          μ (avoidZeroUntilWithEndpoint Xq n w) := by
    have hPairwise :
        Pairwise fun w₁ w₂ : {u : LatticePoint d // u ∈ offZero} ↦
          Disjoint
            (avoidZeroUntilWithEndpoint Xq n (w₁ : LatticePoint d))
            (avoidZeroUntilWithEndpoint Xq n (w₂ : LatticePoint d)) := by
          intro w₁ w₂ hw
          refine Set.disjoint_left.2 ?_
          intro ω h₁ h₂
          apply hw
          exact Subtype.ext <| h₁.1.symm.trans h₂.1
    have hMeas :
        ∀ w : {u : LatticePoint d // u ∈ offZero},
          MeasurableSet (avoidZeroUntilWithEndpoint Xq n (w : LatticePoint d)) := by
          intro w
          have hAvoid_hist :
              MeasurableSet[generatedFiltrationSpace Xq n]
                (avoidZeroUntilWithEndpoint Xq n (w : LatticePoint d)) :=
            avoidZeroUntilWithEndpoint_measurableSet hqreal.measurable_process n (w : LatticePoint d)
          exact (generatedHistory_le_ambient Xq hqreal.measurable_process n) _ hAvoid_hist
    rw [hUnion]
    exact MeasureTheory.measure_iUnion hPairwise hMeas
  -- Proof comment: decompose the absorbed nonzero mass into singleton endpoints and match each
  -- singleton mass with the corresponding bounded free zero-avoidance endpoint event.
  calc
    ((κAbs ^ n) z) offZero =
        ∑' w : {u : LatticePoint d // u ∈ offZero},
          ((κAbs ^ n) z) ({(w : LatticePoint d)} : Set (LatticePoint d)) := hMass
    _ =
        ∑' w : {u : LatticePoint d // u ∈ offZero},
          μ (avoidZeroUntilWithEndpoint Xq n w) := by
            refine tsum_congr fun w ↦ ?_
            symm
            simpa [μ, offZero] using
              freeAvoidZeroEndpointProb_eq_absorbedEndpointMass
                (Pq := Pq) (Xq := Xq) n z (w := (w : LatticePoint d)) w.2
    _ = μ {ω | ∀ m ≤ n, Xq m ω ≠ 0} := hAvoid.symm

/-- Helper for Exercise 18.2.3: the absorbed difference kernel loses all nonzero mass in the
limit because the free difference walk hits `0` almost surely. -/
theorem absorbedDifferenceNonzeroMass_tendsto_zero
    {d : ℕ} {Ωq : Type*} [MeasurableSpace Ωq]
    {q : LatticePoint d → LatticePoint d → ENNReal}
    {Pq : LatticePoint d → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq]
    [IsMarkovKernel (discreteMatrixKernel (absorbAtZeroStepMatrix q))]
    (hfreeHit : ∀ z : LatticePoint d, (F[Pq, Xq]) z 0 = 1)
    (z : LatticePoint d) :
    Tendsto
      (fun n ↦
        ((discreteMatrixKernel (absorbAtZeroStepMatrix q) ^ n) z)
          {w : LatticePoint d | w ≠ 0})
      atTop (nhds 0) := by
  have hAvoid :
      Tendsto
        (fun n ↦ (Pq z : Measure Ωq) {ω | ∀ m ≤ n, Xq m ω ≠ 0})
        atTop (nhds 0) :=
    freeAvoidZeroProb_tendsto_zero (q := q) (Pq := Pq) (Xq := Xq) hfreeHit z
  have hfun :
      (fun n ↦
        ((discreteMatrixKernel (absorbAtZeroStepMatrix q) ^ n) z)
          {w : LatticePoint d | w ≠ 0}) =
        (fun n ↦ (Pq z : Measure Ωq) {ω | ∀ m ≤ n, Xq m ω ≠ 0}) := by
    funext n
    exact absorbedDifferenceNonzeroMass_eq_freeAvoidZeroProb
      (q := q) (Pq := Pq) (Xq := Xq) z n
  -- Proof comment: the absorbed nonzero mass is exactly the bounded free avoid-zero probability,
  -- so the generic free limit theorem applies verbatim.
  simpa [hfun] using hAvoid

/-- Helper for Exercise 18.2.3: the time-`n` disagreement probability of the coalescent equals
the nonzero mass of the absorbed difference kernel at time `n`. -/
lemma coalescentCurrentDisagreement_eq_absorbedDifferenceNonzeroMass
    {d : ℕ} (ν : PMF (LatticePoint d))
    {p : LatticePoint d → LatticePoint d → ENNReal}
    [IsMarkovKernel (discreteMatrixKernel p)]
    [IsMarkovKernel (discreteMatrixKernel (absorbAtZeroStepMatrix (differenceStepMatrix ν)))]
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z]
    (hkernel : discreteMatrixKernel p = dirac_convolution_kernel ν.toMeasure)
    (n : ℕ) (x y : LatticePoint d) :
    (Pcouple (x, y) : Measure Ω') {ω | (Z n ω).1 ≠ (Z n ω).2} =
      ((discreteMatrixKernel (absorbAtZeroStepMatrix (differenceStepMatrix ν)) ^ n) (x - y))
        {w : LatticePoint d | w ≠ 0} := by
  let κPair : Kernel (LatticePoint d × LatticePoint d) (LatticePoint d × LatticePoint d) :=
    discreteMatrixKernel (independentCoalescentMatrix p)
  let diff : LatticePoint d × LatticePoint d → LatticePoint d := fun s ↦ s.1 - s.2
  let offZero : Set (LatticePoint d) := {w : LatticePoint d | w ≠ 0}
  have hdiff_meas : Measurable diff := Measurable.of_discrete
  let hReal :
      IsMarkovProcessRealization
        (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z :=
    inferInstance
  have hdiff_process_meas : Measurable (fun ω ↦ (Z n ω).1 - (Z n ω).2) :=
    hdiff_meas.comp (hReal.measurable_process n)
  -- Proof comment: rewrite disagreement as nonvanishing of the difference process and then push
  -- the time-`n` coalescent law through subtraction.
  rw [coalescentDisagreementEvent_eq_differenceEvent (Z := Z) n]
  have hpreimage :
      {ω | (Z n ω).1 - (Z n ω).2 ≠ 0} =
        (fun ω ↦ (Z n ω).1 - (Z n ω).2) ⁻¹' offZero := by
    ext ω
    simp [offZero]
  rw [hpreimage, ← Measure.map_apply hdiff_process_meas
    (show MeasurableSet offZero from MeasurableSet.of_discrete)]
  have hmap :
      Measure.map (fun ω ↦ (Z n ω).1 - (Z n ω).2) (Pcouple (x, y) : Measure Ω') =
        Measure.map diff ((κPair ^ n) (x, y)) := by
    calc
      Measure.map (fun ω ↦ (Z n ω).1 - (Z n ω).2) (Pcouple (x, y) : Measure Ω') =
          Measure.map diff (Measure.map (Z n) (Pcouple (x, y) : Measure Ω')) := by
            symm
            simpa [diff, Function.comp] using
              (Measure.map_map (μ := (Pcouple (x, y) : Measure Ω'))
                (f := Z n) (g := diff)
                (hf := hReal.measurable_process n) (hg := hdiff_meas))
      _ = Measure.map diff ((κPair ^ n) (x, y)) := by
            rw [hReal.transition_eq (x, y) n]
  rw [hmap]
  simpa [offZero] using
    congrArg
      (fun μ : Measure (LatticePoint d) ↦ μ offZero)
      (coalescentDifferencePow_map_eq_absorbedDifferencePow
        (ν := ν) (p := p) hkernel n x y)

/-- Helper for Exercise 18.2.3: from a diagonal state, the independent coalescent one-step kernel
assigns zero mass to the off-diagonal. -/
private theorem coalescentDiagonal_offDiagonalMass_eq_zero
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (x : LatticePoint d) :
    discreteMatrixKernel (independentCoalescentMatrix p) (x, x)
      {s : LatticePoint d × LatticePoint d | s.1 ≠ s.2} = 0 := by
  let κ : Kernel (LatticePoint d × LatticePoint d) (LatticePoint d × LatticePoint d) :=
    discreteMatrixKernel (independentCoalescentMatrix p)
  let offDiag : Set (LatticePoint d × LatticePoint d) := {s | s.1 ≠ s.2}
  calc
    κ (x, x) offDiag
        = ∑' s : LatticePoint d × LatticePoint d,
            offDiag.indicator (fun s ↦ κ (x, x) ({s} : Set (LatticePoint d × LatticePoint d))) s := by
              simpa using
                (Measure.tsum_indicator_apply_singleton (κ (x, x)) offDiag
                  (show MeasurableSet offDiag from MeasurableSet.of_discrete)).symm
    _ = 0 := by
          refine ENNReal.tsum_eq_zero.mpr ?_
          intro s
          by_cases hs : s.1 ≠ s.2
          · rcases s with ⟨z, w⟩
            have hsOff : (z, w) ∈ offDiag := by
              simpa [offDiag] using hs
            rw [Set.indicator_of_mem hsOff]
            rw [discreteMatrixKernel_apply_singleton]
            simpa using independentCoalescentMatrix_apply_diag_of_ne (p := p) (x := x) hs
          · have hsNotOff : s ∉ offDiag := by
              simpa [offDiag] using hs
            rw [Set.indicator_of_notMem hsNotOff]

/-- Helper for Exercise 18.2.3: once the independent coalescent starts on the diagonal, every
positive-time marginal remains supported on the diagonal. -/
private theorem coalescentDiagonal_offDiagonalMass_pow_eq_zero
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    [IsMarkovKernel (discreteMatrixKernel (independentCoalescentMatrix p))]
    (x : LatticePoint d) :
    ∀ n : ℕ, 0 < n →
      ((discreteMatrixKernel (independentCoalescentMatrix p) ^ n) (x, x))
        {s : LatticePoint d × LatticePoint d | s.1 ≠ s.2} = 0 := by
  let κ : Kernel (LatticePoint d × LatticePoint d) (LatticePoint d × LatticePoint d) :=
    discreteMatrixKernel (independentCoalescentMatrix p)
  let offDiag : Set (LatticePoint d × LatticePoint d) := {s | s.1 ≠ s.2}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  have hstep_le :
      ∀ z : LatticePoint d × LatticePoint d,
        κ z offDiag ≤ Set.indicator offDiag (fun _ ↦ (1 : ℝ≥0∞)) z := by
    intro z
    by_cases hz : z.1 ≠ z.2
    · have hzOff : z ∈ offDiag := by
        simpa [offDiag] using hz
      rw [Set.indicator_of_mem hzOff]
      calc
        κ z offDiag ≤ κ z Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by
            letI : IsProbabilityMeasure (κ z) := by infer_instance
            simp
    · have hzNotOff : z ∉ offDiag := by
        simpa [offDiag] using hz
      rw [Set.indicator_of_notMem hzNotOff]
      rcases z with ⟨a, b⟩
      have hab : a = b := by
        simpa using hz
      subst b
      simpa [κ, offDiag] using coalescentDiagonal_offDiagonalMass_eq_zero (p := p) a
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction m with
  | zero =>
      -- Proof comment: at one step, the diagonal row already has zero off-diagonal mass.
      simpa [κ, offDiag] using coalescentDiagonal_offDiagonalMass_eq_zero (p := p) x
  | succ m ih =>
      -- Proof comment: one more Chapman-Kolmogorov step integrates the same one-step
      -- off-diagonal bound against a measure already supported on the diagonal.
      rw [Kernel.pow_succ_apply_eq_lintegral κ (m + 1) (x, x) hoffDiag_meas]
      refine le_antisymm ?_ bot_le
      calc
        ∫⁻ z, κ z offDiag ∂((κ ^ (m + 1)) (x, x)) ≤
            ∫⁻ z, Set.indicator offDiag (fun _ ↦ (1 : ℝ≥0∞)) z
              ∂((κ ^ (m + 1)) (x, x)) := by
                refine lintegral_mono ?_
                intro z
                exact hstep_le z
        _ = ((κ ^ (m + 1)) (x, x)) offDiag := by
            simp [offDiag, hoffDiag_meas]
        _ = 0 := ih (Nat.succ_pos _)

/-- Helper for Exercise 18.2.3: starting from a diagonal state, every fixed-time disagreement
event has probability `0`. -/
private theorem coalescentDiagonal_disagreementProb_eq_zero
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z]
    (x : LatticePoint d) :
    ∀ n : ℕ,
      (Pcouple (x, x) : Measure Ω') {ω | (Z n ω).1 ≠ (Z n ω).2} = 0 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z :=
    inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel (independentCoalescentMatrix p)) := by
    simpa [pow_one] using hReal.semigroup.isMarkovKernel 1
  let offDiag : Set (LatticePoint d × LatticePoint d) := {s | s.1 ≠ s.2}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  intro n
  have hpreimage :
      {ω | (Z n ω).1 ≠ (Z n ω).2} = Z n ⁻¹' offDiag := by
    ext ω
    simp [offDiag]
  rw [hpreimage, ← Measure.map_apply (hReal.measurable_process n) hoffDiag_meas,
    hReal.transition_eq (x, x) n]
  cases n with
  | zero =>
      -- Proof comment: at time `0`, the realization starts from the deterministic diagonal state.
      have hzero :
          ((discreteMatrixKernel (independentCoalescentMatrix p) ^ 0) (x, x)) =
            Measure.dirac (x, x) := by
              simpa [pow_zero] using (Kernel.id_apply (x, x))
      rw [hzero]
      simp [offDiag]
  | succ k =>
      -- Proof comment: after any positive number of steps, the diagonal-support lemma already
      -- kills the off-diagonal mass.
      simpa [offDiag] using
        coalescentDiagonal_offDiagonalMass_pow_eq_zero (p := p) x (k + 1) (Nat.succ_pos _)

/-- Helper for Exercise 18.2.3: starting from a diagonal state, every tail disagreement event has
probability `0`. -/
private theorem coalescentDiagonal_tailDisagreementProb_eq_zero
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z]
    (x : LatticePoint d) (n : ℕ) :
    (Pcouple (x, x) : Measure Ω') (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}) = 0 := by
  let μ : Measure Ω' := Pcouple (x, x)
  let A : ℕ → Set Ω' := fun m ↦ {ω | (Z m ω).1 ≠ (Z m ω).2}
  have hUnion : (⋃ m ≥ n, A m) = ⋃ k : ℕ, A (n + k) := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨m, hm⟩
      rcases Set.mem_iUnion.1 hm with ⟨hmn, hA⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact Set.mem_iUnion.2 ⟨k, hA⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨k, hA⟩
      exact Set.mem_iUnion.2 ⟨n + k, Set.mem_iUnion.2 ⟨Nat.le_add_right n k, hA⟩⟩
  have hslice_zero : ∀ k : ℕ, μ (A (n + k)) = 0 := by
    intro k
    simpa [μ, A] using coalescentDiagonal_disagreementProb_eq_zero
      (p := p) (Pcouple := Pcouple) (Z := Z) x (n + k)
  -- Proof comment: rewrite the tail as a countable union of its fixed-time slices and use that
  -- each slice is already null.
  rw [hUnion, measure_iUnion_null hslice_zero]

/-- Helper for Exercise 18.2.3: on a history event fixing `X n = y`, the future singleton mass
after `t` additional steps factors through the `t`-step kernel row from `y`. -/
lemma measureInter_eq_mul_kernelPowMass_of_stateEvent
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {q : LatticePoint d → LatticePoint d → ENNReal}
    {P : LatticePoint d → ProbabilityMeasure Ω}
    {X : ℕ → Ω → LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    (x y w : LatticePoint d) (n t : ℕ) (A : Set Ω)
    (hA_meas : MeasurableSet A)
    (hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_state : ∀ ⦃ω : Ω⦄, ω ∈ A → X n ω = y) :
    (P x : Measure Ω) (A ∩ {ω | X (n + t) ω = w}) =
      ((discreteMatrixKernel q ^ t) y ({w} : Set (LatticePoint d))) * (P x : Measure Ω) A := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel q) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hstep :
      ∀ x' : LatticePoint d, ∀ ⦃B : Set (LatticePoint d)⦄, MeasurableSet B → ∀ s : ℕ,
        (P x')⟦X (s + 1) ⁻¹' B | generatedFiltrationSpace X s⟧ =ᵐ[(P x' : Measure Ω)]
          fun ω ↦ ((discreteMatrixKernel q) (X s ω)).real B := by
    intro x' B hB s
    -- Proof comment: specialize the owner Markov property to one step and simplify `^ 1`.
    simpa [Nat.add_comm] using hReal.markov_property x' (A := B) hB s 1
  have hfuture_meas : MeasurableSet (X (n + t) ⁻¹' ({w} : Set (LatticePoint d))) := by
    exact (hReal.measurable_process (n + t)) (measurableSet_singleton w)
  have hslice_real :
      μ.real (A ∩ {ω | X (n + t) ω = w}) =
        (((discreteMatrixKernel q ^ t) y) ({w} : Set (LatticePoint d))).toReal * μ.real A := by
    calc
      μ.real (A ∩ {ω | X (n + t) ω = w}) =
          ∫ ω in A,
            Set.indicator (X (n + t) ⁻¹' ({w} : Set (LatticePoint d))) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
              rw [← MeasureTheory.integral_indicator hA_meas]
              -- Proof comment: rewrite the sliced future event as the restricted indicator on the
              -- history event.
              simpa [Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                Set.inter_comm, smul_eq_mul] using
                (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                  (hA_meas.inter hfuture_meas)).symm
      _ =
          ∫ ω in A, ((discreteMatrixKernel q ^ t) (X n ω)).real ({w} : Set (LatticePoint d)) ∂μ := by
            symm
            -- Proof comment: the arbitrary-gap history bridge identifies the restricted future
            -- singleton event with the `t`-step kernel mass from the present state.
            simpa [Nat.add_comm] using
              kernelPow_setIntegral_eq_on_history
                (κ₁ := discreteMatrixKernel q) (P := P) (X := X)
                hReal.measurable_process hstep x (A := ({w} : Set (LatticePoint d)))
                (measurableSet_singleton w) n t (B := A) hA_measFiltration
      _ = ∫ ω in A, ((discreteMatrixKernel q ^ t) y).real ({w} : Set (LatticePoint d)) ∂μ := by
            -- Proof comment: on `A`, the time-`n` state is fixed, so the `t`-step row is constant.
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem hA_meas] with ω hω
            rw [hA_state hω]
      _ = (((discreteMatrixKernel q ^ t) y) ({w} : Set (LatticePoint d))).toReal * μ.real A := by
            rw [show ((discreteMatrixKernel q ^ t) y).real ({w} : Set (LatticePoint d)) =
                (((discreteMatrixKernel q ^ t) y) ({w} : Set (LatticePoint d))).toReal by rfl]
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hslice_enn :
      μ (A ∩ {ω | X (n + t) ω = w}) =
        ((discreteMatrixKernel q ^ t) y ({w} : Set (LatticePoint d))) * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff'
        (measure_lt_top μ _).ne
        (ENNReal.mul_ne_top
          (by exact (measure_lt_top ((discreteMatrixKernel q ^ t) y) ({w} : Set (LatticePoint d))).ne)
          (by exact (measure_lt_top μ A).ne))).mp ?_
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, mul_comm] using hslice_real
  simpa [μ] using hslice_enn

/-- Helper for Exercise 18.2.3: on a history event fixing `X n = y`, the future mass of any
measurable target set factors through the `t`-step kernel row from `y`. -/
lemma measureInter_eq_mul_kernelPowMass_of_stateEvent_set
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {Ω : Type*} [MeasurableSpace Ω]
    {q : E → E → ENNReal}
    {P : E → ProbabilityMeasure Ω}
    {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    (x y : E) (n t : ℕ) (A : Set Ω) (B : Set E)
    (hB_meas : MeasurableSet B)
    (hA_meas : MeasurableSet A)
    (hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_state : ∀ ⦃ω : Ω⦄, ω ∈ A → X n ω = y) :
    (P x : Measure Ω) (A ∩ {ω | X (n + t) ω ∈ B}) =
      ((discreteMatrixKernel q ^ t) y B) * (P x : Measure Ω) A := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel q) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hstep :
      ∀ x' : E, ∀ ⦃C : Set E⦄, MeasurableSet C → ∀ s : ℕ,
        (P x')⟦X (s + 1) ⁻¹' C | generatedFiltrationSpace X s⟧ =ᵐ[(P x' : Measure Ω)]
          fun ω ↦ ((discreteMatrixKernel q) (X s ω)).real C := by
    intro x' C hC s
    -- Proof comment: specialize the one-step Markov property to the future target set `C`.
    simpa [Nat.add_comm] using hReal.markov_property x' (A := C) hC s 1
  have hfuture_meas : MeasurableSet (X (n + t) ⁻¹' B) := by
    exact (hReal.measurable_process (n + t)) hB_meas
  have hslice_real :
      μ.real (A ∩ {ω | X (n + t) ω ∈ B}) =
        (((discreteMatrixKernel q ^ t) y) B).toReal * μ.real A := by
    calc
      μ.real (A ∩ {ω | X (n + t) ω ∈ B}) =
          ∫ ω in A, Set.indicator (X (n + t) ⁻¹' B) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
            rw [← MeasureTheory.integral_indicator hA_meas]
            -- Proof comment: rewrite the sliced future event as the indicator of the measurable
            -- target set restricted to the history slice `A`.
            simpa [Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
              Set.inter_comm, smul_eq_mul] using
              (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                (hA_meas.inter hfuture_meas)).symm
      _ =
          ∫ ω in A, ((discreteMatrixKernel q ^ t) (X n ω)).real B ∂μ := by
            symm
            -- Proof comment: the arbitrary-gap history bridge replaces the future event by the
            -- `t`-step kernel mass seen from the time-`n` state.
            simpa [Nat.add_comm] using
              kernelPow_setIntegral_eq_on_history
                (κ₁ := discreteMatrixKernel q) (P := P) (X := X)
                hReal.measurable_process hstep x (A := B) hB_meas n t (B := A)
                hA_measFiltration
      _ = ∫ ω in A, ((discreteMatrixKernel q ^ t) y).real B ∂μ := by
            -- Proof comment: the history slice `A` pins the present state to `y`, so the future
            -- `t`-step row is constant there.
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem hA_meas] with ω hω
            rw [hA_state hω]
      _ = (((discreteMatrixKernel q ^ t) y) B).toReal * μ.real A := by
            rw [show ((discreteMatrixKernel q ^ t) y).real B =
                (((discreteMatrixKernel q ^ t) y) B).toReal by rfl]
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hslice_enn :
      μ (A ∩ {ω | X (n + t) ω ∈ B}) =
        ((discreteMatrixKernel q ^ t) y B) * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff'
        (measure_lt_top μ _).ne
        (ENNReal.mul_ne_top
          (by exact (measure_lt_top ((discreteMatrixKernel q ^ t) y) B).ne)
          (by exact (measure_lt_top μ A).ne))).mp ?_
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, mul_comm] using hslice_real
  simpa [μ] using hslice_enn

/-- Helper for Exercise 18.2.3: the disagreement tail splits into the present slice and the
strictly later slices. -/
private lemma coalescentTailDisagreement_eq_currentUnionFuture
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℕ → Ω → LatticePoint d × LatticePoint d) (n : ℕ) :
    (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}) =
      {ω | (Z n ω).1 ≠ (Z n ω).2} ∪
        ⋃ k : ℕ, {ω | (Z (n + (k + 1)) ω).1 ≠ (Z (n + (k + 1)) ω).2} := by
  ext ω
  constructor
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨m, hm⟩
    rcases Set.mem_iUnion.1 hm with ⟨hmn, hdis⟩
    rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
    · exact Or.inl hdis
    · have hkExists : ∃ k : ℕ, n + (k + 1) = m := ⟨m - n - 1, by omega⟩
      rcases hkExists with ⟨k, hk⟩
      exact Or.inr <| Set.mem_iUnion.2 ⟨k, hk ▸ hdis⟩
  · intro hω
    rcases hω with hω | hω
    · exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨le_rfl, hω⟩⟩
    · rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
      exact Set.mem_iUnion.2 ⟨n + (k + 1), Set.mem_iUnion.2 ⟨by omega, hk⟩⟩

/-- Helper for Exercise 18.2.3: a strictly future disagreement either is already present at time
`n` or occurs together with being on the diagonal at time `n`. -/
private lemma futureDisagreement_subset_currentOrDiagonalFuture
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℕ → Ω → LatticePoint d × LatticePoint d) (n : ℕ) :
    (⋃ k : ℕ, {ω | (Z (n + (k + 1)) ω).1 ≠ (Z (n + (k + 1)) ω).2}) ⊆
      {ω | (Z n ω).1 ≠ (Z n ω).2} ∪
        ({ω | (Z n ω).1 = (Z n ω).2} ∩
          ⋃ k : ℕ, {ω | (Z (n + (k + 1)) ω).1 ≠ (Z (n + (k + 1)) ω).2}) := by
  intro ω hω
  by_cases hdis : (Z n ω).1 ≠ (Z n ω).2
  · exact Or.inl hdis
  · have hEq : (Z n ω).1 = (Z n ω).2 := by
      by_contra hneq
      exact hdis hneq
    exact Or.inr ⟨hEq, hω⟩

/-- Helper for Exercise 18.2.3: fixing a diagonal state at time `n`, the future off-diagonal
slice after `k + 1` more steps has probability `0`. -/
private theorem coalescentDiagonalFutureOffDiagonalSlice_eq_zero
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z]
    (x y z : LatticePoint d) (n k : ℕ) :
    (Pcouple (x, y) : Measure Ω')
      ({ω | Z n ω = (z, z)} ∩
        {ω | (Z (n + (k + 1)) ω).1 ≠ (Z (n + (k + 1)) ω).2}) = 0 := by
  let μ : Measure Ω' := Pcouple (x, y)
  let offDiag : Set (LatticePoint d × LatticePoint d) := {s | s.1 ≠ s.2}
  let hReal :
      IsMarkovProcessRealization
        (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z :=
    inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel (independentCoalescentMatrix p)) := by
    simpa [pow_one] using hReal.semigroup.isMarkovKernel 1
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  have hState_meas : MeasurableSet ({ω | Z n ω = (z, z)} : Set Ω') := by
    rw [show ({ω | Z n ω = (z, z)} : Set Ω') =
        Z n ⁻¹' ({(z, z)} : Set (LatticePoint d × LatticePoint d)) by
      ext ω
      simp]
    exact hReal.measurable_process n (measurableSet_singleton (z, z))
  have hState_hist :
      MeasurableSet[generatedFiltrationSpace Z n] ({ω | Z n ω = (z, z)} : Set Ω') := by
    have hZn : Measurable[generatedFiltrationSpace Z n] (Z n) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Z) n
    rw [show ({ω | Z n ω = (z, z)} : Set Ω') =
        Z n ⁻¹' ({(z, z)} : Set (LatticePoint d × LatticePoint d)) by
      ext ω
      simp]
    exact hZn (measurableSet_singleton (z, z))
  have hState_eq :
      ∀ ⦃ω : Ω'⦄, ω ∈ ({ω | Z n ω = (z, z)} : Set Ω') → Z n ω = (z, z) := by
    intro ω hω
    simpa using hω
  rw [show ({ω | (Z (n + (k + 1)) ω).1 ≠ (Z (n + (k + 1)) ω).2} : Set Ω') =
      {ω | Z (n + (k + 1)) ω ∈ offDiag} by
    ext ω
    simp [offDiag]]
  rw [measureInter_eq_mul_kernelPowMass_of_stateEvent_set
    (q := independentCoalescentMatrix p)
    (P := Pcouple) (X := Z) (x := (x, y)) (y := (z, z))
    n (k + 1) ({ω | Z n ω = (z, z)}) offDiag
    hoffDiag_meas hState_meas hState_hist hState_eq]
  -- Proof comment: once the chain is pinned to the diagonal at time `n`, the positive-time
  -- coalescent kernel never puts mass back on the off-diagonal.
  rw [coalescentDiagonal_offDiagonalMass_pow_eq_zero (p := p) z (k + 1) (Nat.succ_pos _)]
  simp [μ]

/-- Helper for Exercise 18.2.3: the event of being diagonal at time `n` and later leaving the
diagonal has probability `0`. -/
private theorem coalescentDiagonalFutureNull
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z]
    (x y : LatticePoint d) (n : ℕ) :
    (Pcouple (x, y) : Measure Ω')
      ({ω | (Z n ω).1 = (Z n ω).2} ∩
        ⋃ k : ℕ, {ω | (Z (n + (k + 1)) ω).1 ≠ (Z (n + (k + 1)) ω).2}) = 0 := by
  let μ : Measure Ω' := Pcouple (x, y)
  let disagree : ℕ → Set Ω' := fun m ↦ {ω | (Z m ω).1 ≠ (Z m ω).2}
  have hslice_zero :
      ∀ k : ℕ,
        μ ({ω | (Z n ω).1 = (Z n ω).2} ∩ disagree (n + (k + 1))) = 0 := by
    intro k
    have hcover :
        {ω | (Z n ω).1 = (Z n ω).2} ∩ disagree (n + (k + 1)) ⊆
          ⋃ z : LatticePoint d,
            ({ω | Z n ω = (z, z)} ∩ disagree (n + (k + 1))) := by
      intro ω hω
      rcases hω with ⟨hdiag, hdis⟩
      have hdiag' : (Z n ω).1 = (Z n ω).2 := by
        simpa using hdiag
      refine Set.mem_iUnion.2 ⟨(Z n ω).1, ?_⟩
      constructor
      · exact Prod.ext rfl hdiag'.symm
      · exact hdis
    refine measure_mono_null hcover ?_
    refine measure_iUnion_null fun z ↦ ?_
    simpa [μ, disagree] using
      coalescentDiagonalFutureOffDiagonalSlice_eq_zero
        (p := p) (Pcouple := Pcouple) (Z := Z) x y z n k
  have hinter :
      {ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1)) =
        ⋃ k : ℕ, ({ω | (Z n ω).1 = (Z n ω).2} ∩ disagree (n + (k + 1))) := by
    ext ω
    simp
  -- Proof comment: cover the diagonal-future branch by its fixed-time slices and use the nullity
  -- of each diagonal slice proved above.
  rw [hinter]
  exact measure_iUnion_null hslice_zero

/-- Helper for Exercise 18.2.3: after time `n`, any later disagreement was already present at time
`n`, because the coalescent cannot leave the diagonal once it has entered it. -/
lemma coalescentTailDisagreement_le_currentDisagreement
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z]
    (x y : LatticePoint d) :
    ∀ n : ℕ,
      (Pcouple (x, y) : Measure Ω') (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}) ≤
        (Pcouple (x, y) : Measure Ω') {ω | (Z n ω).1 ≠ (Z n ω).2} := by
  let μ : Measure Ω' := Pcouple (x, y)
  let disagree : ℕ → Set Ω' := fun m ↦ {ω | (Z m ω).1 ≠ (Z m ω).2}
  intro n
  have hfuture_null :
      μ ({ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1))) = 0 := by
    -- Proof comment: after the chain hits the diagonal at time `n`, the packaged diagonal-future
    -- null lemma shows that no later disagreement can occur with positive mass.
    simpa [μ, disagree] using
      coalescentDiagonalFutureNull (p := p) (Pcouple := Pcouple) (Z := Z) x y n
  -- Proof comment: split the tail into the present disagreement slice and the strictly future
  -- disagreements, then absorb the future term into the null diagonal-future branch.
  calc
    μ (⋃ m ≥ n, disagree m) = μ (disagree n ∪ ⋃ k : ℕ, disagree (n + (k + 1))) := by
      rw [coalescentTailDisagreement_eq_currentUnionFuture (Z := Z) n]
    _ ≤ μ (disagree n) +
        μ ({ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1))) := by
          refine le_trans (measure_mono ?_) (measure_union_le _ _)
          intro ω hω
          rcases hω with hω | hω
          · exact Or.inl hω
          · exact futureDisagreement_subset_currentOrDiagonalFuture (Z := Z) n hω
    _ = μ (disagree n) := by
      rw [hfuture_null, add_zero]

/-- Helper for Exercise 18.2.3: for a translation-invariant recurrent lattice walk, the
independent-coalescent tail disagreement probabilities tend to `0`. -/
theorem translationInvariant_independentCoalescentTailDisagreement_tendsto_zero_of_recurrent
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    {P : LatticePoint d → ProbabilityMeasure Ω} {X : ℕ → Ω → LatticePoint d}
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z]
    [Kernel.IsIrreducible (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    (htranslation : IsTranslationInvariantStepMatrix p)
    (hrec : IsRecurrentMarkovChain P X)
    (haperiodic : IsAperiodic (discreteMatrixKernel p)) :
    ∀ x y : LatticePoint d,
      Tendsto
        (fun n ↦
          (Pcouple (x, y) : Measure Ω') (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}))
        atTop (nhds 0) := by
  let hbaseReal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hbaseReal.semigroup.isMarkovKernel 1
  let ν0 : PMF (LatticePoint d) := (discreteMatrixKernel p 0).toPMF
  let q : LatticePoint d → LatticePoint d → ENNReal := differenceStepMatrix ν0
  have hkernel :
      discreteMatrixKernel p = dirac_convolution_kernel ν0.toMeasure :=
    (translationInvariantDiscreteKernel_eq_diracConvolutionKernel
      (p := p) htranslation).symm
  have hqstochastic : IsStochasticMatrix q :=
    differenceStepMatrix_isStochastic (ν := ν0)
  letI : IsMarkovKernel (discreteMatrixKernel q) :=
    discreteMatrixKernel_isMarkovKernel q hqstochastic
  letI :
      IsMarkovKernel (discreteMatrixKernel (absorbAtZeroStepMatrix q)) :=
    discreteMatrixKernel_isMarkovKernel
      (absorbAtZeroStepMatrix q)
      (absorbAtZeroStepMatrix_isStochastic (q := q) hqstochastic)
  obtain ⟨Pq, hqreal⟩ :=
    existsCanonicalDiscreteMatrixRealization (q := q) hqstochastic
  letI :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Function.eval := hqreal
  have hqrec : IsRecurrentMarkovChain Pq Function.eval :=
    differenceStepMatrix_recurrent_of_baseRecurrent
      (p := p) (P := P) (X := X) (Pq := Pq) (Xq := Function.eval)
      htranslation hrec haperiodic
  have hreachZero :
      ∀ z : LatticePoint d,
        ∃ n : ℕ, 0 < n ∧
          0 < (discreteMatrixKernel q ^ n) z ({0} : Set (LatticePoint d)) :=
    differenceStepMatrix_reachesZero
      (p := p) htranslation haperiodic
  have hhitZero : ∀ z : LatticePoint d, (F[Pq, Function.eval]) z 0 = 1 :=
    freeDifference_everHitsZero_eq_one
      (ν := ν0) (Pq := Pq) (Xq := Function.eval) hqrec hreachZero
  intro x y
  have hcurrentAbs :
      Tendsto
        (fun n ↦
          ((discreteMatrixKernel (absorbAtZeroStepMatrix q) ^ n) (x - y))
            {w : LatticePoint d | w ≠ 0})
        atTop (nhds 0) :=
    absorbedDifferenceNonzeroMass_tendsto_zero
      (q := q) (Pq := Pq) (Xq := Function.eval) hhitZero (x - y)
  have hcurrent :
      Tendsto
        (fun n ↦ (Pcouple (x, y) : Measure Ω') {ω | (Z n ω).1 ≠ (Z n ω).2})
        atTop (nhds 0) := by
    have hrewrite :
        (fun n ↦ (Pcouple (x, y) : Measure Ω') {ω | (Z n ω).1 ≠ (Z n ω).2}) =
          (fun n ↦
            ((discreteMatrixKernel (absorbAtZeroStepMatrix q) ^ n) (x - y))
              {w : LatticePoint d | w ≠ 0}) := by
          funext n
          simpa [q] using
            coalescentCurrentDisagreement_eq_absorbedDifferenceNonzeroMass
              (ν := ν0) (p := p) (Pcouple := Pcouple) (Z := Z)
              hkernel n x y
    simpa [hrewrite] using hcurrentAbs
  -- Proof comment: every tail disagreement probability is squeezed between `0` and the current
  -- disagreement probability, and the current term already tends to `0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcurrent ?_ ?_
  · intro n
    simp
  · intro n
    exact coalescentTailDisagreement_le_currentDisagreement
      (p := p) (Pcouple := Pcouple) (Z := Z) x y n

-- Exercise 18.2.3 at the owner layer: if `X` is an aperiodic irreducible recurrent random walk
-- on `ℤ^d` with increment law `ν`, then every realization of the associated independent
-- coalescent chain is a successful Markov coupling.
/-- Exercise 18.2.3 at the owner layer: if `X` is an aperiodic irreducible recurrent random walk
on `ℤ^d` with increment law `ν`, then every realization of the associated independent coalescent
chain is a successful Markov coupling. -/
theorem independentCoalescent_isSuccessfulMarkovCoupling_of_aperiodic_irreducible_recurrent_latticeRandomWalk
    {d : ℕ} (ν : PMF (LatticePoint d))
    {P : LatticePoint d → ProbabilityMeasure Ω} {X : ℕ → Ω → LatticePoint d}
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    [IsMarkovProcessRealization
      (fun n ↦
        discreteMatrixKernel
          (independentCoalescentMatrix
            (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})) ^ n)
      Pcouple Z]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)]
    (hrec : IsRecurrentMarkovChain P X)
    (haperiodic : IsAperiodic (dirac_convolution_kernel ν.toMeasure)) :
    IsSuccessfulMarkovCoupling
      (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) Pcouple Z := by
  have hbaseKernel :
      discreteMatrixKernel (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) =
        dirac_convolution_kernel ν.toMeasure := by
    ext x s hs
    have hrow :
        discreteMatrixKernel (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) x =
          dirac_convolution_kernel ν.toMeasure x := by
      refine Measure.ext_of_singleton ?_
      intro y
      rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
      rw [tsum_eq_single y]
      · simp
      · intro z hz
        simp [Measure.smul_apply, Measure.dirac_apply', hz]
    exact congrArg (fun μ ↦ μ s) hrow
  letI :
      IsMarkovProcessRealization
        (fun n ↦
          discreteMatrixKernel (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) ^ n)
        P X := by
          have hfamily :
              (fun n ↦
                discreteMatrixKernel (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) ^ n) =
                (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) := by
            funext n
            exact congrArg (fun κ : Kernel (LatticePoint d) (LatticePoint d) ↦ κ ^ n) hbaseKernel
          rw [hfamily]
          exact
            (inferInstance :
              IsMarkovProcessRealization
                (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X)
  letI :
      Kernel.IsIrreducible
        (Measure.count : Measure (LatticePoint d))
        (discreteMatrixKernel (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})) := by
          rw [hbaseKernel]
          exact
            (inferInstance :
              Kernel.IsIrreducible
                (Measure.count : Measure (LatticePoint d))
                (dirac_convolution_kernel ν.toMeasure))
  have haperiodic' :
      IsAperiodic
        (discreteMatrixKernel (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})) := by
    rw [hbaseKernel]
    exact haperiodic
  refine
    { toIsMarkovCoupling :=
        independentCoalescentChain_isMarkovCoupling
          (p := fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})
          (P := Pcouple) (Z := Z)
      tail_disagreement_tendsto_zero := ?_ }
  -- Proof comment: the owner-level structure is just the Markov-coupling package from Exercise
  -- 18.2.2 together with the translation-invariant tail-disagreement theorem above.
  exact
    translationInvariant_independentCoalescentTailDisagreement_tendsto_zero_of_recurrent
      (p := fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})
      (P := P) (X := X) (Pcouple := Pcouple) (Z := Z)
      (diracConvolutionKernel_isTranslationInvariantStepMatrix (ν := ν))
      hrec haperiodic'

end ProbabilityTheory
