/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Lemma_1_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.FiniteDimensionalKernel
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.MarkovPathMeasureBridge
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.Kernel

noncomputable section

open FiniteDimensionalKernelLocal

/-- Helper for Example 14.45: the public finite-dimensional coordinate projection on the canonical
path space `NNReal → E`. -/
private def finiteDimensionalProjection {E : Type*} {n : ℕ} (times : Fin (n + 1) → NNReal) :
    (NNReal → E) → Fin (n + 1) → E :=
  fun ω i ↦ ω (times i)

/-- Helper for Example 14.45: finite-dimensional coordinate projections are measurable. -/
private theorem measurable_finiteDimensionalProjection {E : Type*} [MeasurableSpace E] {n : ℕ}
    (times : Fin (n + 1) → NNReal) :
    Measurable
      (finiteDimensionalProjection (E := E) times : (NNReal → E) → Fin (n + 1) → E) := by
  -- Proof comment: each output coordinate is evaluation at one deterministic time.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply (times i)

/-- Helper for Example 14.45: the source-facing `Iic n` index set is canonically equivalent to
`Fin (n + 1)`. -/
private def iicEquivFinLocal (n : ℕ) : Finset.Iic n ≃ Fin (n + 1) where
  toFun i := ⟨i.1, Nat.lt_succ_of_le <| Finset.mem_Iic.mp i.2⟩
  invFun i := ⟨i.1, Finset.mem_Iic.mpr <| Nat.le_of_lt_succ i.2⟩
  left_inv i := by
    cases i
    rfl
  right_inv i := by
    cases i
    rfl

/-- Helper for Example 14.45: reindex a finite `Fin` time tuple as an ordered `Iic` chain. -/
private def orderedTimeChainLocal {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Π _ : Finset.Iic n, NNReal :=
  fun i ↦ times (iicEquivFinLocal n i)

/-- Helper for Example 14.45: strict monotonicity of the `Fin` time tuple transfers to the
ordered `Iic` chain. -/
private theorem orderedTimeChainLocal_strictMono {n : ℕ} {times : Fin (n + 1) → NNReal}
    (htimes : StrictMono times) :
    StrictMono (orderedTimeChainLocal times) := by
  intro i j hij
  exact htimes (by simpa [orderedTimeChainLocal, iicEquivFinLocal] using hij)

/-- Helper for Example 14.45: the ordered finite-dimensional kernel associated to a Markov
semigroup on `NNReal`, reindexed through the local `Iic`-history API. -/
private def markovSemigroupFiniteDimKernel {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] [PolishSpace E] (κ : NNReal → Kernel E E) {n : ℕ}
    (times : Fin (n + 1) → NNReal) (htimes : StrictMono times) :
    Kernel E (Fin (n + 1) → E) :=
  (consistentFamilyFiniteDimensionalKernel (fun {s t : NNReal} _ ↦ κ (t - s))
      (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes)).map
    (fun x i ↦ x ((iicEquivFinLocal n).symm i))

/-- Helper for Example 14.45: the translated centered Gaussian kernels
`x ↦ δ_x ∗ gaussianReal 0 t` form a Markov semigroup. -/
private theorem gaussianIncrementKernel_isMarkovSemigroup :
    IsMarkovSemigroup (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t)) := by
  let κ : NNReal → Kernel ℝ ℝ := fun t ↦ dirac_convolution_kernel (gaussianReal 0 t)
  refine
    { isMarkovKernel := ?_
      zero_eq := ?_
      comp_eq := ?_ }
  · intro t
    -- Proof comment: every row is the translated Gaussian law `δ_x ∗ 𝒩(0,t)`, hence a
    -- probability measure.
    refine ⟨?_⟩
    intro x
    simpa [κ, dirac_convolution_kernel_apply] using
      (inferInstance : IsProbabilityMeasure (Measure.dirac x ∗ gaussianReal 0 t))
  · -- Proof comment: at time `0`, the Gaussian law is `δ₀`, so convolution by it is the identity.
    ext x A hA
    simpa [Kernel.id_apply, hA, gaussianReal_zero_var] using
      congrArg (fun μ : Measure ℝ ↦ μ A) (Measure.conv_dirac_zero (Measure.dirac x))
  · intro s t
    -- Proof comment: composing translated kernels convolves the increment laws, and Gaussian
    -- convolution collapses the result to variance `s + t`.
    ext x A hA
    rw [Kernel.comp_apply' _ _ _ hA]
    rw [show κ s x = Measure.dirac x ∗ gaussianReal 0 s by
      simp [κ, dirac_convolution_kernel_apply]]
    rw [show κ (s + t) x = Measure.dirac x ∗ gaussianReal 0 (s + t) by
      simp [κ, dirac_convolution_kernel_apply]]
    have hcomp :
        ∫⁻ y, dirac_convolution_kernel (gaussianReal 0 t) y A
          ∂(Measure.dirac x ∗ gaussianReal 0 s) =
          ((Measure.dirac x ∗ gaussianReal 0 s) ∗ gaussianReal 0 t) A := by
      simpa only [Kernel.comp_apply', Kernel.const_apply, hA] using
        congrArg (fun η : Kernel ℝ ℝ ↦ η x A)
          (dirac_convolution_kernel_comp_const_eq_const_conv
            (μ := Measure.dirac x ∗ gaussianReal 0 s)
            (ν := gaussianReal 0 t))
    calc
      ∫⁻ y, (κ t y) A ∂(Measure.dirac x ∗ gaussianReal 0 s)
          = ((Measure.dirac x ∗ gaussianReal 0 s) ∗ gaussianReal 0 t) A := by
              simpa only [κ] using hcomp
      _ = (Measure.dirac x ∗ (gaussianReal 0 s ∗ gaussianReal 0 t)) A := by
            simpa using congrArg (fun μ : Measure ℝ ↦ μ A)
              (Measure.conv_assoc (Measure.dirac x) (gaussianReal 0 s) (gaussianReal 0 t))
      _ = (Measure.dirac x ∗ gaussianReal 0 (s + t)) A := by
            rw [gaussianReal_conv_gaussianReal, zero_add]

/-- Helper for Example 14.45: convolution with a Dirac mass preserves total mass `1`, so
`dirac_convolution_kernel μ` is a Markov kernel whenever `μ` is a probability measure. -/
private instance instIsMarkovKernelDiracConvolutionKernelPath
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsMarkovKernel (dirac_convolution_kernel μ) := by
  refine ⟨?_⟩
  intro x
  rw [dirac_convolution_kernel_apply]
  infer_instance

/-- Helper for Example 14.45: the canonical Gaussian Markov path measure starts from `0`. -/
private theorem canonicalGaussianPathMeasureStart_hasLaw
    {P : Measure (NNReal → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernel
              (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
              times htimes ∘ₘ Measure.dirac 0) :
    HasLaw (Function.eval 0) (Measure.dirac 0) P := by
  let times : Fin 1 → NNReal := fun _ ↦ 0
  let e0 : ℝ → Fin 1 → ℝ := fun y _ ↦ y
  have htimes : StrictMono times := by
    intro i j hij
    fin_cases i
    fin_cases j
    cases hij
  have he0_measurable : Measurable e0 := by
    refine measurable_pi_lambda _ fun _ ↦ ?_
    exact measurable_id
  have hproj : finiteDimensionalProjection times = e0 ∘ Function.eval 0 := by
    -- Proof comment: the one-point finite-dimensional projection only records the time-zero
    -- coordinate, packaged as a constant `Fin 1` tuple.
    funext ω
    funext i
    fin_cases i
    simp [finiteDimensionalProjection, times, e0]
  have htuple : P.map (e0 ∘ Function.eval 0) = (Measure.dirac 0).map e0 := by
    -- Proof comment: the `n = 0` marginal from Corollary 14.44 is exactly the initial Dirac law.
    calc
      P.map (e0 ∘ Function.eval 0) = P.map (finiteDimensionalProjection times) := by
        simp [hproj]
      _ =
          markovSemigroupFiniteDimKernel
            (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
            times htimes ∘ₘ Measure.dirac 0 := hP_fdim times rfl htimes
      _ = (Measure.dirac 0).map e0 := by
        rw [markovSemigroupFiniteDimKernel]
        rw [← Measure.map_comp _ _ (by
          refine measurable_pi_lambda _ fun _ ↦ ?_
          exact measurable_pi_apply _)]
        change
          Measure.map _ (consistentFamilyFiniteDimensionalMeasure (Measure.dirac 0)
            (fun {s t : NNReal} _ ↦
              dirac_convolution_kernel (gaussianReal 0 (t - s)))
            _ _) = _
        rw [consistentFamilyFiniteDimensionalMeasure_zero]
        rw [Measure.map_map (by
          refine measurable_pi_lambda _ fun _ ↦ ?_
          exact measurable_pi_apply _)
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ ℝ)).symm.measurable]
        rfl
  refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
  -- Proof comment: postcompose the singleton-tuple law with `Function.eval 0` to recover the
  -- scalar time-zero law.
  calc
    P.map (Function.eval 0) = P.map ((Function.eval 0) ∘ (e0 ∘ Function.eval 0)) := by
      rfl
    _ = (P.map (e0 ∘ Function.eval 0)).map (Function.eval 0) := by
      rw [Measure.map_map (measurable_pi_apply 0)
        (he0_measurable.comp (measurable_pi_apply 0))]
    _ = ((Measure.dirac 0).map e0).map (Function.eval 0) := by
      rw [htuple]
    _ = (Measure.dirac 0).map ((Function.eval 0) ∘ e0) := by
      rw [Measure.map_map (measurable_pi_apply 0) he0_measurable]
    _ = Measure.dirac 0 := by
      simp [e0]

/-- Helper for Example 14.45: the finite-grid increment tuple attached to a time grid
`times : Fin (n + 1) → NNReal`. -/
private def pathIncrementTuple {n : ℕ} (times : Fin (n + 1) → NNReal) :
    (NNReal → ℝ) → Fin n → ℝ :=
  fun ω i ↦ ω (times i.succ) - ω (times i.castSucc)

/-- Helper for Example 14.45: drop the final time from a finite time grid. -/
private def dropLastTimes {n : ℕ} (times : Fin (n + 2) → NNReal) : Fin (n + 1) → NNReal :=
  fun i ↦ times i.castSucc

/-- Helper for Example 14.45: dropping the final time preserves the anchored `0` entry. -/
private theorem dropLastTimes_zero {n : ℕ} {times : Fin (n + 2) → NNReal}
    (hzero : times 0 = 0) :
    dropLastTimes times 0 = 0 := by
  -- Proof comment: `Fin.castSucc` fixes the zeroth coordinate, so the dropped grid still starts
  -- at `0`.
  simpa [dropLastTimes] using hzero

/-- Helper for Example 14.45: dropping the final time preserves strict monotonicity. -/
private theorem dropLastTimes_strictMono {n : ℕ} {times : Fin (n + 2) → NNReal}
    (htimes : StrictMono times) :
    StrictMono (dropLastTimes times) := by
  -- Proof comment: `Fin.castSucc` is the order-preserving inclusion of the prefix coordinates.
  intro i j hij
  exact htimes (by simpa [dropLastTimes] using hij)

/-- Helper for Example 14.45: the finite-grid increment tuple is measurable. -/
private theorem measurable_pathIncrementTuple {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Measurable (pathIncrementTuple times) := by
  -- Proof comment: each increment coordinate is a measurable difference of two path evaluations.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- Helper for Example 14.45: recover a coordinate tuple from its zero-based increment vector by
finite partial sums. -/
private def prependZeroPartialSums {n : ℕ} : (Fin n → ℝ) → Fin (n + 1) → ℝ :=
  fun z i ↦ Fin.partialSum z i

/-- Helper for Example 14.45: each finite partial-sum coordinate is measurable. -/
private theorem measurable_finPartialSum {n : ℕ} (i : Fin (n + 1)) :
    Measurable (fun z : Fin n → ℝ ↦ Fin.partialSum z i) := by
  induction i using Fin.induction with
  | zero =>
      -- Proof comment: the zero-th partial sum is the constant `0`.
      simp
  | succ i hi =>
      -- Proof comment: each successor partial sum adds the next increment coordinate to the
      -- previous partial sum.
      simpa [Fin.partialSum_succ] using hi.add (measurable_pi_apply i)

/-- Helper for Example 14.45: the zero-prepended partial-sum reconstruction map is measurable. -/
private theorem measurable_prependZeroPartialSums {n : ℕ} :
    Measurable (prependZeroPartialSums (n := n)) := by
  -- Proof comment: measurability is checked coordinatewise through the partial-sum coordinates.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [prependZeroPartialSums] using measurable_finPartialSum (n := n) i

/-- Helper for Example 14.45: composing the finite-dimensional projection with the tuple
increment observable gives the path-space increment tuple. -/
private theorem incrementTuple_comp_finiteDimensionalProjection {n : ℕ}
    (times : Fin (n + 1) → NNReal) :
    (fun z : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ z i.succ - z i.castSucc) ∘
        finiteDimensionalProjection times =
      pathIncrementTuple times := by
  -- Proof comment: both sides read the same adjacent coordinate differences from the path.
  funext ω
  ext i
  simp [pathIncrementTuple, finiteDimensionalProjection]

/-- Helper for Example 14.45: the partial sums of a finite increment tuple telescope to the
corresponding coordinate difference. -/
private theorem partialSum_pathIncrementTuple_eq_sub {n : ℕ}
    (times : Fin (n + 1) → NNReal) (ω : NNReal → ℝ) (i : Fin (n + 1)) :
    Fin.partialSum (pathIncrementTuple times ω) i = ω (times i) - ω (times 0) := by
  induction i using Fin.induction with
  | zero =>
      -- Proof comment: the zero-th partial sum and the zero coordinate difference are both `0`.
      simp
  | succ i hi =>
      -- Proof comment: append the next adjacent increment and simplify the telescoping sum.
      rw [Fin.partialSum_succ, hi]
      rw [show pathIncrementTuple times ω i = ω (times i.succ) - ω (times i.castSucc) by rfl]
      ring

/-- Helper for Example 14.45: if the path starts from `0`, the zero-prepended partial sums of the
increment tuple recover the full finite-dimensional coordinate tuple. -/
private theorem prependZeroPartialSums_pathIncrementTuple_eq {n : ℕ}
    (times : Fin (n + 1) → NNReal) (hzero : times 0 = 0)
    {ω : NNReal → ℝ} (hω0 : ω 0 = 0) :
    prependZeroPartialSums (pathIncrementTuple times ω) = finiteDimensionalProjection times ω := by
  -- Proof comment: once the initial coordinate is fixed at `0`, the partial sums telescope to the
  -- successive coordinates of the path.
  funext i
  calc
    prependZeroPartialSums (pathIncrementTuple times ω) i
        = ω (times i) - ω (times 0) := by
            simp [prependZeroPartialSums, partialSum_pathIncrementTuple_eq_sub]
    _ = ω (times i) - ω 0 := by simp [hzero]
    _ = ω (times i) := by simp [hω0]
    _ = finiteDimensionalProjection times ω i := by rfl

/-- Helper for Example 14.45: adjacent differences recover the original increment vector after
applying `prependZeroPartialSums`. -/
private theorem incrementTuple_prependZeroPartialSums_eq_self {n : ℕ}
    (z : Fin n → ℝ) :
    (fun y : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ y i.succ - y i.castSucc)
      (prependZeroPartialSums z) = z := by
  -- Proof comment: consecutive partial sums differ by exactly the increment inserted at that
  -- successor step.
  ext i
  simp [prependZeroPartialSums, Fin.partialSum_succ]

/-- Helper for Example 14.45: a start-at-zero law rewrites the full coordinate tuple law as the
pushforward of the increment tuple law by zero-prepended partial sums. -/
private theorem finiteDimensionalProjection_map_eq_prependZeroPartialSums_of_start_zero
    {μ : Measure (NNReal → ℝ)} {n : ℕ} (times : Fin (n + 1) → NNReal)
    (hzero : times 0 = 0)
    (hstart : HasLaw (Function.eval 0) (Measure.dirac 0) μ) :
    μ.map (finiteDimensionalProjection times) =
      (μ.map (pathIncrementTuple times)).map (prependZeroPartialSums (n := n)) := by
  have hω0 : ∀ᵐ ω ∂μ, ω 0 = 0 := by
    exact (hstart.ae_iff (p := fun y : ℝ ↦ y = 0) (by fun_prop)).2 (by simp)
  calc
    μ.map (finiteDimensionalProjection times) =
        μ.map ((prependZeroPartialSums (n := n)) ∘ pathIncrementTuple times) := by
          refine Measure.map_congr ?_
          filter_upwards [hω0] with ω hω0ω
          funext i
          simpa [Function.comp] using
            (congrFun (prependZeroPartialSums_pathIncrementTuple_eq times hzero hω0ω) i).symm
    _ = (μ.map (pathIncrementTuple times)).map (prependZeroPartialSums (n := n)) := by
          rw [Measure.map_map
            (measurable_prependZeroPartialSums (n := n))
            (measurable_pathIncrementTuple times)]

/-- Helper for Example 14.45: independent increments plus the Gaussian gap laws identify the full
increment tuple law with the corresponding product Gaussian law. -/
private theorem incrementTuple_map_eq_gaussianPi_of_targetAssumptions
    {μ : Measure (NNReal → ℝ)} [IsProbabilityMeasure μ] {n : ℕ}
    (times : Fin (n + 1) → NNReal) (htimes : Monotone times)
    (hindep : HasIndepIncrements Function.eval μ)
    (hlaw :
      ∀ i : Fin n,
        HasLaw
          (fun ω : NNReal → ℝ ↦ ω (times i.succ) - ω (times i.castSucc))
          (gaussianReal 0 (times i.succ - times i.castSucc))
          μ) :
    μ.map (pathIncrementTuple times) =
      Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := by
  have htupleIndep :
      iIndepFun (fun i : Fin n ↦ fun ω : NNReal → ℝ ↦
        ω (times i.succ) - ω (times i.castSucc)) μ :=
    hindep n times htimes
  calc
    μ.map (pathIncrementTuple times)
        = Measure.pi
            (fun i : Fin n ↦
              μ.map (fun ω : NNReal → ℝ ↦ ω (times i.succ) - ω (times i.castSucc))) := by
            simpa [pathIncrementTuple] using
              (iIndepFun_iff_map_fun_eq_pi_map
                (fun i : Fin n ↦ (hlaw i).aemeasurable)).1 htupleIndep
    _ = Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := by
          congr 1
          funext i
          exact (hlaw i).map_eq

/-- Helper for Example 14.45: reindex an ordered history on `Iic n` as a `Fin (n + 1)` tuple. -/
private def reindexOrderedHistory {n : ℕ} :
    (Π _ : Finset.Iic n, ℝ) → Fin (n + 1) → ℝ :=
  fun z i ↦ z ((iicEquivFinLocal n).symm i)

/-- Helper for Example 14.45: the increment tuple of an ordered `Iic` history, viewed through the
canonical `Fin` reindexing. -/
private def orderedHistoryIncrementTuple {n : ℕ} :
    (Π _ : Finset.Iic n, ℝ) → Fin n → ℝ :=
  fun z i ↦ reindexOrderedHistory z i.succ - reindexOrderedHistory z i.castSucc

/-- Helper for Example 14.45: the ordered-history increment tuple is measurable. -/
private theorem measurable_orderedHistoryIncrementTuple {n : ℕ} :
    Measurable (orderedHistoryIncrementTuple (n := n)) := by
  -- Proof comment: after reindexing the ordered history to a `Fin` tuple, each increment
  -- coordinate is a measurable difference of two evaluations.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- Helper for Example 14.45: the last coordinate on an `Iic n`-indexed history is measurable. -/
private theorem measurable_lastIicCoordinate {n : ℕ} :
    Measurable (fun z : Π _ : Finset.Iic n, ℝ ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩) := by
  exact measurable_pi_apply _

/-- Helper for Example 14.45: the first coordinate on an `Iic n`-indexed history is measurable. -/
private theorem measurable_zeroIicCoordinate {n : ℕ} :
    Measurable
      (fun z : Π _ : Finset.Iic n, ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩) := by
  exact measurable_pi_apply _

/-- Helper for Example 14.45: in `Finset.Iic (n + 1)`, the last prefix index is strictly below
the terminal index. -/
private theorem lastIic_lt_succLast (n : ℕ) :
    (⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ : Finset.Iic (n + 1)) <
      ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := by
  -- Proof comment: this is the subtype version of `n < n + 1`.
  simp

/-- Helper for Example 14.45: split a successor history into its prefix history and final state. -/
private noncomputable def succHistoryEquivLocal (n : ℕ) :
    (Π _ : Finset.Iic (n + 1), ℝ) ≃ᵐ ((Π _ : Finset.Iic n, ℝ) × ℝ) :=
  (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ ↦ ℝ) (Nat.le_succ n)).symm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n).symm)

/-- Helper for Example 14.45: `succHistoryEquivLocal` records the prefix restriction and the final
state. -/
@[simp] private theorem succHistoryEquivLocal_apply (n : ℕ)
    (z : Π _ : Finset.Iic (n + 1), ℝ) :
    succHistoryEquivLocal n z =
      (Preorder.frestrictLe₂ (π := fun _ : ℕ ↦ ℝ) (Nat.le_succ n) z,
        z ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) := by
  -- Proof comment: unfold the measurable equivalence into the canonical `IicProdIoc` split and
  -- then collapse the singleton tail coordinate.
  rfl

/-- Helper for Example 14.45: splitting the canonical `IicProdIoc` glue map recovers the stored
prefix together with the terminal singleton coordinate. -/
@[simp] private theorem succHistoryEquivLocal_apply_IicProdIoc
    (n : ℕ) (z : (Π _ : Finset.Iic n, ℝ) × (Π _ : Finset.Ioc n (n + 1), ℝ)) :
    succHistoryEquivLocal n
        (_root_.IicProdIoc (X := fun _ : ℕ ↦ ℝ) n (n + 1) z) =
      Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n).symm z := by
  -- Proof comment: splitting the glued history recovers the prefix restriction and collapses the
  -- singleton tail coordinate back to the final state.
  rcases z with ⟨z₁, z₂⟩
  apply Prod.ext
  · ext i
    have hi : (i : ℕ) ≤ n := Finset.mem_Iic.mp i.2
    simpa [succHistoryEquivLocal_apply, _root_.IicProdIoc_def,
      MeasurableEquiv.piSingleton, hi] using
      congrFun
        (congrFun
          (frestrictLe₂_comp_IicProdIoc (X := fun _ : ℕ ↦ ℝ) (hab := Nat.le_succ n))
          (z₁, z₂))
        i
  · simp [succHistoryEquivLocal_apply, _root_.IicProdIoc_def, MeasurableEquiv.piSingleton]

/-- Helper for Example 14.45: the inverse of `succHistoryEquivLocal` glues a prefix history and
one terminal state back into a successor history. -/
@[simp] private theorem succHistoryEquivLocal_symm_apply (n : ℕ)
    (z : (Π _ : Finset.Iic n, ℝ) × ℝ) :
    (succHistoryEquivLocal n).symm z =
      _root_.IicProdIoc (X := fun _ : ℕ ↦ ℝ) n (n + 1)
        (z.1, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n z.2) := by
  -- Proof comment: the inverse first restores the singleton tail coordinate and then uses the
  -- canonical `IicProdIoc` gluing map.
  rfl

/-- Helper for Example 14.45: after reindexing an ordered successor history to `Fin`, splitting
off the last increment is exactly the same as recording the final gap and the prefix increment
tuple. -/
private theorem orderedHistoryIncrementTuple_piFinSuccAbove_last {n : ℕ} :
    (fun z : Π _ : Finset.Iic (n + 1), ℝ ↦
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
        (orderedHistoryIncrementTuple (n := n + 1) z)) =
      fun z ↦
        let p := succHistoryEquivLocal n z
        (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
          orderedHistoryIncrementTuple (n := n) p.1) := by
  funext z
  apply Prod.ext
  · simp [orderedHistoryIncrementTuple, reindexOrderedHistory,
      MeasurableEquiv.piFinSuccAbove_apply, succHistoryEquivLocal_apply, iicEquivFinLocal]
  · ext i
    simp [orderedHistoryIncrementTuple, reindexOrderedHistory,
      MeasurableEquiv.piFinSuccAbove_apply, succHistoryEquivLocal_apply, Fin.init_def,
      iicEquivFinLocal]

/-- Helper for Example 14.45: after splitting off the last coordinate from a finite tuple of
real-valued increments, the second component is the `Fin.castSucc` prefix. -/
private theorem piFinSuccAboveLast_snd_eq_castSucc {n : ℕ} :
    Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n) =
      fun z : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ z i.castSucc := by
  funext z i
  -- Proof comment: for `Fin.last`, `succAbove` is exactly `Fin.castSucc`, so the second
  -- component records the prefix coordinates unchanged.
  simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]

/-- Helper for Example 14.45: `piFinSuccAbove` splits the last increment off a finite-grid
increment tuple into the terminal gap and the prefix increment tuple. -/
private theorem pathIncrementTuple_piFinSuccAbove_last {n : ℕ}
    (times : Fin (n + 2) → NNReal) :
    (fun ω ↦
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
        (pathIncrementTuple times ω)) =
      fun ω ↦
        (ω (times (Fin.last n).succ) - ω (times (Fin.last n).castSucc),
          pathIncrementTuple (dropLastTimes times) ω) := by
  -- Proof comment: `piFinSuccAbove` isolates the terminal increment, and the remaining
  -- coordinates are exactly the increment tuple on the dropped-last prefix grid.
  funext ω
  have htail :
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n))
        (pathIncrementTuple times ω)).2 =
        fun i : Fin n ↦ pathIncrementTuple times ω i.castSucc := by
    ext i
    simpa [MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def, Fin.succAbove_last]
  apply Prod.ext
  · simp [pathIncrementTuple, MeasurableEquiv.piFinSuccAbove_apply]
  · ext i
    rw [htail]
    change
      ω (times (i.castSucc).succ) - ω (times (i.castSucc).castSucc) =
        ω ((dropLastTimes times) i.succ) - ω ((dropLastTimes times) i.castSucc)
    rw [show (dropLastTimes times) i.succ = times i.succ.castSucc by rfl]
    rw [show (dropLastTimes times) i.castSucc = times i.castSucc.castSucc by rfl]
    rw [Fin.succ_castSucc]

/-- Helper for Example 14.45: splitting the Gaussian increment product law at the final coordinate
gives the terminal gap marginal together with the prefix increment product law. -/
private theorem gaussianIncrementPi_map_piFinSuccAbove_last {n : ℕ}
    (times : Fin (n + 2) → NNReal) :
    (Measure.pi (fun i : Fin (n + 1) ↦ gaussianReal 0 (times i.succ - times i.castSucc))).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)) =
    (gaussianReal 0 (times (Fin.last n).succ - times (Fin.last n).castSucc)).prod
      (Measure.pi (fun i : Fin n ↦
        gaussianReal 0 ((dropLastTimes times) i.succ - (dropLastTimes times) i.castSucc))) := by
  let μ : Fin (n + 1) → Measure ℝ := fun i ↦ gaussianReal 0 (times i.succ - times i.castSucc)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
  have hMapEq :
      (Measure.pi μ).map e =
        (μ (Fin.last n)).prod (Measure.pi fun i : Fin n ↦ μ ((Fin.last n).succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ (Fin.last n)).map_eq
  have hprefixFamily :
      (fun i : Fin n ↦ μ ((Fin.last n).succAbove i)) =
        (fun i : Fin n ↦
          gaussianReal 0 ((dropLastTimes times) i.succ - (dropLastTimes times) i.castSucc)) := by
    funext i
    rw [Fin.succAbove_last]
    change
      gaussianReal 0 (times (i.castSucc).succ - times (i.castSucc).castSucc) =
        gaussianReal 0 ((dropLastTimes times) i.succ - (dropLastTimes times) i.castSucc)
    rw [show (dropLastTimes times) i.succ = times i.succ.castSucc by rfl]
    rw [show (dropLastTimes times) i.castSucc = times i.castSucc.castSucc by rfl]
    rw [Fin.succ_castSucc]
  -- Proof comment: `measurePreserving_piFinSuccAbove` already gives the product factorization;
  -- for `Fin.last`, the remaining coordinates are the `castSucc` prefix increments.
  rw [hMapEq, hprefixFamily]

/-- Helper for Example 14.45: the singleton-history initialization map in the local scalar
finite-dimensional-kernel model. -/
private def initialHistoryScalarLocal : ℝ → Π _ : Finset.Iic 0, ℝ :=
  fun x _ ↦ x

/-- Helper for Example 14.45: the local scalar singleton-history initializer is measurable. -/
private theorem measurable_initialHistoryScalarLocal :
    Measurable initialHistoryScalarLocal := by
  refine measurable_pi_lambda _ fun _ ↦ ?_
  simpa [initialHistoryScalarLocal] using measurable_id

/-- Helper for Example 14.45: the local scalar history-kernel family matching the owner
finite-dimensional-kernel construction. -/
private noncomputable def consistentFamilyHistoryKernelsScalarLocal
    (K : ∀ ⦃s t : NNReal⦄, s < t → Kernel ℝ ℝ) {n : ℕ}
    (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) :
    (m : ℕ) → Kernel (Π _ : Finset.Iic m, ℝ) ℝ :=
  fun m ↦
    if hm : m < n then
      Kernel.comap
        (K (hj (show (⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
          ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)))
        (fun z : Π _ : Finset.Iic m, ℝ ↦ z ⟨m, Finset.mem_Iic.2 le_rfl⟩)
        (measurable_lastIicCoordinate (n := m))
    else
      Kernel.deterministic
        (fun z : Π _ : Finset.Iic m, ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩)
        (measurable_zeroIicCoordinate (n := m))

/-- Helper for Example 14.45: the local scalar history trajectory is the owner `partialTraj`
started from time `0`. -/
private noncomputable def consistentFamilyHistoryTrajScalarLocal {n : ℕ}
    (κhist : (m : ℕ) → Kernel (Π _ : Finset.Iic m, ℝ) ℝ) :
    Kernel (Π _ : Finset.Iic 0, ℝ) (Π _ : Finset.Iic n, ℝ) :=
  ((@ProbabilityTheory.Kernel.partialTraj (fun _ : ℕ ↦ ℝ) _ κhist 0 n) :
    Kernel (Π _ : Finset.Iic 0, ℝ) (Π _ : Finset.Iic n, ℝ))

/-- Helper for Example 14.45: the public scalar finite-dimensional kernel is definitionally the
local scalar history trajectory followed by the singleton-history initializer. -/
private theorem consistentFamilyFiniteDimensionalKernel_eq_scalarHistoryTraj
    (K : ∀ ⦃s t : NNReal⦄, s < t → Kernel ℝ ℝ) {n : ℕ}
    (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) :
    consistentFamilyFiniteDimensionalKernel K j hj =
      consistentFamilyHistoryTrajScalarLocal
          (consistentFamilyHistoryKernelsScalarLocal K j hj) ∘ₖ
        Kernel.deterministic initialHistoryScalarLocal measurable_initialHistoryScalarLocal := by
  rfl

/-- Helper for Example 14.45: restricting the ordered time chain to `Iic n` does not change the
scalar history kernel at any earlier index `r < n`. -/
private theorem consistentFamilyHistoryKernelsScalarLocal_prefix_eq
    {n r : ℕ}
    (K : ∀ ⦃s t : NNReal⦄, s < t → Kernel ℝ ℝ)
    (j : Π _ : Finset.Iic (n + 1), NNReal) (hj : StrictMono j)
    (hr : r < n) :
    let jPrefix : Π _ : Finset.Iic n, NNReal := fun i ↦
      j ⟨i.1, Finset.mem_Iic.2
        (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
    let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
    consistentFamilyHistoryKernelsScalarLocal K j hj r =
      consistentFamilyHistoryKernelsScalarLocal K jPrefix hjPrefix r := by
  let jPrefix : Π _ : Finset.Iic n, NNReal := fun i ↦
    j ⟨i.1, Finset.mem_Iic.2
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
  let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
  have hrFull : r < n + 1 := Nat.lt_succ_of_lt hr
  -- Proof comment: before the terminal index, both local history families pick the same
  -- last-coordinate transition kernel from the same adjacent time pair.
  simp [consistentFamilyHistoryKernelsScalarLocal, jPrefix, hjPrefix, hr, hrFull]

/-- Helper for Example 14.45: up to any prefix length `m ≤ n`, the trajectory built from the full
ordered history family agrees with the one built from the restricted prefix family. -/
private theorem consistentFamilyHistoryTrajScalarLocal_prefix_eq
    {n m : ℕ}
    (K : ∀ ⦃s t : NNReal⦄, s < t → Kernel ℝ ℝ)
    (j : Π _ : Finset.Iic (n + 1), NNReal) (hj : StrictMono j)
    (hm : m ≤ n) :
    let jPrefix : Π _ : Finset.Iic n, NNReal := fun i ↦
      j ⟨i.1, Finset.mem_Iic.2
        (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
    let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
    ProbabilityTheory.Kernel.partialTraj
        (X := fun _ : ℕ ↦ ℝ) (κ := consistentFamilyHistoryKernelsScalarLocal K j hj) 0 m =
      ProbabilityTheory.Kernel.partialTraj
        (X := fun _ : ℕ ↦ ℝ) (κ := consistentFamilyHistoryKernelsScalarLocal K jPrefix hjPrefix) 0 m := by
  let jPrefix : Π _ : Finset.Iic n, NNReal := fun i ↦
    j ⟨i.1, Finset.mem_Iic.2
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
  let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
  let κfull :
      (r : ℕ) → Kernel (Π _ : Finset.Iic r, ℝ) ℝ :=
    consistentFamilyHistoryKernelsScalarLocal K j hj
  let κprefix :
      (r : ℕ) → Kernel (Π _ : Finset.Iic r, ℝ) ℝ :=
    consistentFamilyHistoryKernelsScalarLocal K jPrefix hjPrefix
  dsimp only
  induction m with
  | zero =>
      -- Proof comment: both trajectory kernels over the empty prefix are the identity kernel.
      rw [ProbabilityTheory.Kernel.partialTraj_self, ProbabilityTheory.Kernel.partialTraj_self]
  | succ m ih =>
      have hm' : m ≤ n := Nat.le_of_succ_le hm
      have hlt : m < n := Nat.lt_of_succ_le hm
      have hk : κfull m = κprefix m := by
        -- Proof comment: before the terminal index, the full and restricted history families use
        -- the same one-step kernel.
        simpa [κfull, κprefix] using
          consistentFamilyHistoryKernelsScalarLocal_prefix_eq
            (K := K) (j := j) (hj := hj) (r := m) hlt
      have hprefixTraj :
          ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ ℝ) (κ := κfull) 0 m =
            ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ ℝ) (κ := κprefix) 0 m := by
        simpa [κfull, κprefix] using ih hm'
      -- Proof comment: split both trajectories at the last step, use the induction hypothesis on
      -- the shorter prefix, and then rewrite the last-step kernels with `hk`.
      rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
        (X := fun _ : ℕ ↦ ℝ) (κ := κfull) (Nat.zero_le m)]
      rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
        (X := fun _ : ℕ ↦ ℝ) (κ := κprefix) (Nat.zero_le m)]
      rw [hprefixTraj]
      rw [ProbabilityTheory.Kernel.partialTraj_succ_self
        (X := fun _ : ℕ ↦ ℝ) (κ := κfull) m]
      rw [ProbabilityTheory.Kernel.partialTraj_succ_self
        (X := fun _ : ℕ ↦ ℝ) (κ := κprefix) m]
      simp [hk]

/-- Helper for Example 14.45: the one-step scalar `partialTraj` kernel splits through
`succHistoryEquivLocal` as the identity on the prefix history paired with the last-step row. -/
private theorem partialTrajSucc_map_succHistoryEquivLocal_eq_splitKernel
    {n : ℕ}
    (κhist : (m : ℕ) → Kernel (Π _ : Finset.Iic m, ℝ) ℝ)
    (stepKernel : Kernel (Π _ : Finset.Iic n, ℝ) ℝ)
    [IsSFiniteKernel stepKernel]
    (hstepKernel : κhist n = stepKernel) :
    ((ProbabilityTheory.Kernel.partialTraj
        (X := fun _ : ℕ ↦ ℝ) (κ := κhist) n (n + 1)).map
        (succHistoryEquivLocal n) :
          Kernel (Π _ : Finset.Iic n, ℝ) ((Π _ : Finset.Iic n, ℝ) × ℝ)) =
      (Kernel.id ×ₖ stepKernel) := by
  let _ : IsSFiniteKernel
      ((κhist n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n)) := by
    simpa [hstepKernel] using
      (inferInstance :
        IsSFiniteKernel (stepKernel.map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n)))
  have hcompose :
      succHistoryEquivLocal n ∘
          _root_.IicProdIoc (X := fun _ : ℕ ↦ ℝ) n (n + 1) =
        Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n).symm := by
    -- Proof comment: `succHistoryEquivLocal` is the standard `IicProdIoc` split followed by the
    -- singleton-tail collapse.
    funext z
    simpa [Function.comp] using succHistoryEquivLocal_apply_IicProdIoc n z
  have hmapCompose :
      (((Kernel.id ×ₖ
          (κhist n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n)).map
          (_root_.IicProdIoc (X := fun _ : ℕ ↦ ℝ) n (n + 1))).map
          (succHistoryEquivLocal n)) =
        ((Kernel.id ×ₖ
          (κhist n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n)).map
          (succHistoryEquivLocal n ∘
            _root_.IicProdIoc (X := fun _ : ℕ ↦ ℝ) n (n + 1))) := by
    -- Proof comment: first combine the two successive pushforwards into one composite map.
    symm
    exact
      Kernel.map_comp_right
        (Kernel.id ×ₖ (κhist n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n))
        measurable_IicProdIoc (succHistoryEquivLocal n).measurable
  -- Proof comment: after that composite-map normalization, only the inverse singleton map on the
  -- last coordinate remains to be canceled.
  rw [ProbabilityTheory.Kernel.partialTraj_succ_self, hmapCompose, hcompose]
  rw [← Kernel.map_prod_map
    (Kernel.id :
      Kernel (Π _ : Finset.Iic n, ℝ) (Π _ : Finset.Iic n, ℝ))
    ((κhist n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n))
    measurable_id
    (MeasurableEquiv.symm
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n)).measurable]
  rw [Kernel.map_id]
  rw [hstepKernel]
  rw [← Kernel.map_comp_right _
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n).measurable
    (MeasurableEquiv.symm
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ ℝ) n)).measurable]
  simpa using Kernel.map_id stepKernel

/-- Helper for Example 14.45: under `succHistoryEquivLocal`, the owner finite-dimensional kernel
on an `Iic (n + 1)` history splits into the prefix-history law together with the final translated
step kernel. -/
private theorem consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
    {n : ℕ}
    (K : ∀ ⦃s t : NNReal⦄, s < t → Kernel ℝ ℝ)
    (hK : ∀ {s t : NNReal} (hst : s < t), IsMarkovKernel (K hst))
    (j : Π _ : Finset.Iic (n + 1), NNReal) (hj : StrictMono j) (x : ℝ) :
    let jPrefix : Π _ : Finset.Iic n, NNReal := fun i ↦
      j ⟨i.1, Finset.mem_Iic.2
        (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
    let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
    let lastPrefix : (Π _ : Finset.Iic n, ℝ) → ℝ := fun z ↦
      z ⟨n, Finset.mem_Iic.2 le_rfl⟩
    let hLastIdx :
        (⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ : Finset.Iic (n + 1)) <
          ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := lastIic_lt_succLast n
    let hLast :
        j ⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ <
          j ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
    let hlastPrefixMeasurable : Measurable lastPrefix := by
      simpa [lastPrefix] using measurable_lastIicCoordinate (n := n)
    (consistentFamilyFiniteDimensionalKernel K j hj x).map (succHistoryEquivLocal n) =
      (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
        Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable := by
  -- Route correction: stop comparing two separately declared prefix/full trajectory families.
  -- Instead, reuse the exact one-`κhist` factorization pattern from `Theorem_14_42`, so the
  -- prefix law is read directly from the same history family before the final step.
  let jPrefix : Π _ : Finset.Iic n, NNReal := fun i ↦
    j ⟨i.1, Finset.mem_Iic.2
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
  let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
  let lastPrefix : (Π _ : Finset.Iic n, ℝ) → ℝ := fun z ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩
  let hLastIdx :
      (⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ : Finset.Iic (n + 1)) <
        ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := lastIic_lt_succLast n
  let hLast :
      j ⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ <
        j ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
  let hlastPrefixMeasurable : Measurable lastPrefix := by
    simpa [lastPrefix] using measurable_lastIicCoordinate (n := n)
  let κhist :
      (r : ℕ) → Kernel (Π _ : Finset.Iic r, ℝ) ℝ :=
    consistentFamilyHistoryKernelsScalarLocal K j hj
  let stepKernel : Kernel (Π _ : Finset.Iic n, ℝ) ℝ :=
    Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable
  let splitKernel :
      Kernel (Π _ : Finset.Iic n, ℝ) ((Π _ : Finset.Iic n, ℝ) × ℝ) :=
    Kernel.id ×ₖ stepKernel
  letI : IsMarkovKernel (K hLast) := hK hLast
  letI : IsMarkovKernel stepKernel := by
    dsimp [stepKernel]
    infer_instance
  letI : IsSFiniteKernel stepKernel := by
    infer_instance
  have hstepKernel :
      κhist n = stepKernel := by
    -- Proof comment: at the terminal prefix index, the scalar history family is exactly the
    -- final translated increment kernel read from the last prefix coordinate.
    simp [κhist, consistentFamilyHistoryKernelsScalarLocal, stepKernel, lastPrefix]
  have hsplitKernel :
      ((ProbabilityTheory.Kernel.partialTraj
          (X := fun _ : ℕ ↦ ℝ) (κ := κhist) n (n + 1)).map
          (succHistoryEquivLocal n) :
            Kernel (Π _ : Finset.Iic n, ℝ) ((Π _ : Finset.Iic n, ℝ) × ℝ)) =
        splitKernel := by
    -- Proof comment: the one-step trajectory already splits through `succHistoryEquivLocal` as
    -- the identity prefix kernel paired with the last-step row.
    simpa [splitKernel] using
      partialTrajSucc_map_succHistoryEquivLocal_eq_splitKernel
        (κhist := κhist) (stepKernel := stepKernel) hstepKernel
  have hsucc :
      consistentFamilyFiniteDimensionalKernel K j hj =
        ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ ℝ) (κ := κhist) n (n + 1) ∘ₖ
          consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix := by
    have hprefixTraj :
        ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ ℝ)
            (κ := consistentFamilyHistoryKernelsScalarLocal K j hj) 0 n =
          ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ ℝ)
            (κ := consistentFamilyHistoryKernelsScalarLocal K jPrefix hjPrefix) 0 n := by
      simpa [jPrefix, hjPrefix] using
        consistentFamilyHistoryTrajScalarLocal_prefix_eq
          (K := K) (j := j) (hj := hj) (m := n) le_rfl
    -- Proof comment: the full finite-dimensional kernel is the prefix law followed by one final
    -- transition step, and both sides are unfolded in the same `κhist` spelling.
    rw [consistentFamilyFiniteDimensionalKernel_eq_scalarHistoryTraj,
      consistentFamilyFiniteDimensionalKernel_eq_scalarHistoryTraj]
    rw [consistentFamilyHistoryTrajScalarLocal, consistentFamilyHistoryTrajScalarLocal]
    rw [show consistentFamilyHistoryKernelsScalarLocal K j hj = κhist by rfl]
    rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
      (X := fun _ : ℕ ↦ ℝ)
      (κ := consistentFamilyHistoryKernelsScalarLocal K j hj) (Nat.zero_le n)]
    rw [hprefixTraj]
    rw [show consistentFamilyHistoryKernelsScalarLocal K j hj = κhist by rfl]
    rw [Kernel.comp_assoc]
  letI : IsMarkovKernel (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) :=
    consistentFamilyFiniteDimensionalKernel_isMarkov K
      (fun {_ _} hst ↦ hK hst) jPrefix hjPrefix
  -- Proof comment: combine the public factorization with the one-step split and read the result
  -- as the canonical composition-product measure.
  calc
    (consistentFamilyFiniteDimensionalKernel K j hj x).map (succHistoryEquivLocal n) =
        (((ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ ℝ) (κ := κhist) n (n + 1)).map
            (succHistoryEquivLocal n)) ∘ₖ
              consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x := by
          rw [hsucc]
          rw [← Kernel.map_apply
            (ProbabilityTheory.Kernel.partialTraj
              (X := fun _ : ℕ ↦ ℝ) (κ := κhist) n (n + 1) ∘ₖ
                consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix)
            (succHistoryEquivLocal n).measurable x]
          simpa using congrArg
            (fun ξ :
              Kernel ℝ ((Π _ : Finset.Iic n, ℝ) × ℝ) ↦ ξ x)
            (Kernel.map_comp
              (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix)
              (ProbabilityTheory.Kernel.partialTraj
                (X := fun _ : ℕ ↦ ℝ) (κ := κhist) n (n + 1))
              (succHistoryEquivLocal n))
    _ = (splitKernel ∘ₖ consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x := by
          rw [hsplitKernel]
    _ = (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ stepKernel := by
          simpa [splitKernel] using
            (Measure.compProd_eq_comp_prod
              (μ := consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x)
              (κ := stepKernel)).symm

/-- Helper for Example 14.45: if the final state is sampled from the translated increment kernel
based on the last prefix value, then subtracting that prefix value recovers the centered gap
law. -/
private theorem compProd_map_sub_lastPrefix_eq
    {n : ℕ}
    (ν : ProbabilityMeasure ℝ)
    (μ : Measure (Π _ : Finset.Iic n, ℝ))
    [IsProbabilityMeasure μ]
    (lastPrefix : (Π _ : Finset.Iic n, ℝ) → ℝ)
    (hlastPrefixMeasurable : Measurable lastPrefix) :
    let stepKernel : Kernel (Π _ : Finset.Iic n, ℝ) ℝ :=
      Kernel.comap (dirac_convolution_kernel (ν : Measure ℝ)) lastPrefix
        hlastPrefixMeasurable
    (μ ⊗ₘ stepKernel).map
        (fun p : (Π _ : Finset.Iic n, ℝ) × ℝ ↦ p.2 - lastPrefix p.1) =
      (ν : Measure ℝ) := by
  let stepKernel : Kernel (Π _ : Finset.Iic n, ℝ) ℝ :=
    Kernel.comap (dirac_convolution_kernel (ν : Measure ℝ)) lastPrefix
      hlastPrefixMeasurable
  let gapMap : ((Π _ : Finset.Iic n, ℝ) × ℝ) → ℝ := fun p ↦ p.2 - lastPrefix p.1
  have hgapMapMeasurable : Measurable gapMap := by
    exact measurable_snd.sub (hlastPrefixMeasurable.comp measurable_fst)
  letI : IsSFiniteKernel stepKernel := by
    dsimp [stepKernel]
    infer_instance
  have hkernel :
      ((Kernel.id ×ₖ stepKernel).map gapMap) =
        Kernel.const (Π _ : Finset.Iic n, ℝ) (ν : Measure ℝ) := by
    ext z A hA
    -- Proof comment: rowwise, the last state is sampled as `lastPrefix z + ξ`; subtracting the
    -- prefix endpoint cancels this translation.
    rw [Kernel.map_apply _ hgapMapMeasurable, Kernel.prod_apply, Kernel.id_apply]
    rw [Measure.dirac_prod, Measure.map_map hgapMapMeasurable measurable_prodMk_left]
    rw [Kernel.comap_apply, dirac_convolution_kernel_apply]
    rw [Measure.dirac_conv]
    have hcancel :
        Measure.map (fun y : ℝ ↦ y - lastPrefix z)
            (Measure.map (fun y : ℝ ↦ lastPrefix z + y) (ν : Measure ℝ)) =
          (ν : Measure ℝ) := by
      simpa [Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Measure.map_map
          (μ := (ν : Measure ℝ))
          (f := fun y : ℝ ↦ lastPrefix z + y)
          (g := fun y : ℝ ↦ y - lastPrefix z)
          (measurable_id.sub measurable_const)
          (measurable_const.add measurable_id))
    exact congrArg (fun m : Measure ℝ ↦ m A) hcancel
  -- Proof comment: rewrite the `compProd` measure as the composition of the pair kernel with the
  -- prefix measure and use the rowwise cancellation once.
  calc
    (μ ⊗ₘ stepKernel).map gapMap = (((Kernel.id ×ₖ stepKernel).map gapMap) ∘ₘ μ) := by
      rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hgapMapMeasurable]
    _ = (Kernel.const (Π _ : Finset.Iic n, ℝ) (ν : Measure ℝ)) ∘ₘ μ := by
          rw [hkernel]
    _ = (ν : Measure ℝ) := by
          simpa using
            (Measure.const_comp
              (μ := μ) (ν := (ν : Measure ℝ)))

/-- Helper for Example 14.45: after separating the last translated step into `(gap, prefix)`,
the gap law factors from the pushed-forward prefix statistic as a product measure. -/
private theorem compProd_map_gapAndPrefix_eq_prod
    {n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (νGap : ProbabilityMeasure ℝ)
    (μ : Measure (Π _ : Finset.Iic n, ℝ))
    [IsProbabilityMeasure μ]
    (lastPrefix : (Π _ : Finset.Iic n, ℝ) → ℝ)
    (hlastPrefixMeasurable : Measurable lastPrefix)
    (prefixMap : (Π _ : Finset.Iic n, ℝ) → Y)
    (hprefixMap : Measurable prefixMap) :
    let stepKernel : Kernel (Π _ : Finset.Iic n, ℝ) ℝ :=
      Kernel.comap (dirac_convolution_kernel (νGap : Measure ℝ)) lastPrefix
        hlastPrefixMeasurable
    (μ ⊗ₘ stepKernel).map
        (fun p : (Π _ : Finset.Iic n, ℝ) × ℝ ↦
          (p.2 - lastPrefix p.1, prefixMap p.1)) =
      (νGap : Measure ℝ).prod (μ.map prefixMap) := by
  let stepKernel : Kernel (Π _ : Finset.Iic n, ℝ) ℝ :=
    Kernel.comap (dirac_convolution_kernel (νGap : Measure ℝ)) lastPrefix
      hlastPrefixMeasurable
  let historyGap : ((Π _ : Finset.Iic n, ℝ) × ℝ) → (Π _ : Finset.Iic n, ℝ) × ℝ :=
    fun p ↦ (p.1, p.2 - lastPrefix p.1)
  have hhistoryGapMeasurable : Measurable historyGap := by
    exact measurable_fst.prodMk (measurable_snd.sub (hlastPrefixMeasurable.comp measurable_fst))
  have hswapPrefixMeasurable :
      Measurable (fun q : (Π _ : Finset.Iic n, ℝ) × ℝ ↦ (q.2, prefixMap q.1)) := by
    exact measurable_snd.prodMk (hprefixMap.comp measurable_fst)
  letI : IsSFiniteKernel stepKernel := by
    dsimp [stepKernel]
    infer_instance
  have hhistoryGapKernel :
      ((Kernel.id ×ₖ stepKernel).map historyGap) =
        Kernel.id ×ₖ Kernel.const (Π _ : Finset.Iic n, ℝ) (νGap : Measure ℝ) := by
    ext z s hs
    let shift : ℝ → ℝ := fun y ↦ y - lastPrefix z
    have hshiftMeasurable : Measurable shift := by
      simpa [shift] using (measurable_id.sub measurable_const)
    have htranslateMeasurable : Measurable (fun y : ℝ ↦ lastPrefix z + y) := by
      simpa using (measurable_const.add measurable_id)
    have hshift :
        (stepKernel z).map shift = (νGap : Measure ℝ) := by
      -- Proof comment: the row law of `stepKernel` is the translate of `νGap` by
      -- `lastPrefix z`, so subtracting that prefix endpoint recovers the centered gap law.
      rw [Kernel.comap_apply, dirac_convolution_kernel_apply]
      rw [Measure.dirac_conv]
      simpa [shift, Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Measure.map_map
          (μ := (νGap : Measure ℝ))
          (f := fun y : ℝ ↦ lastPrefix z + y)
          (g := shift)
          hshiftMeasurable
          htranslateMeasurable)
    have hmap :
        (((Kernel.id ×ₖ stepKernel).map historyGap) z) s =
          (((stepKernel z).map shift).map (Prod.mk z)) s := by
      -- Proof comment: after fixing the history, the mapped pair row is obtained by inserting
      -- that history coordinate and centering the fresh increment.
      have hcomp : historyGap ∘ Prod.mk z = Prod.mk z ∘ shift := by
        funext y
        rfl
      have hmapEq :
          Measure.map historyGap (Measure.map (Prod.mk z) (stepKernel z)) =
            Measure.map (Prod.mk z) (Measure.map shift (stepKernel z)) := by
        calc
          Measure.map historyGap (Measure.map (Prod.mk z) (stepKernel z)) =
              Measure.map (historyGap ∘ Prod.mk z) (stepKernel z) := by
                simpa using
                  (Measure.map_map
                    (μ := stepKernel z)
                    (f := Prod.mk z)
                    (g := historyGap)
                    hhistoryGapMeasurable
                    ((measurable_const).prodMk measurable_id))
          _ = Measure.map (Prod.mk z ∘ shift) (stepKernel z) := by
                simp [hcomp]
          _ = Measure.map (Prod.mk z) (Measure.map shift (stepKernel z)) := by
                simpa using
                  (Measure.map_map
                    (μ := stepKernel z)
                    (f := shift)
                    (g := Prod.mk z)
                    ((measurable_const).prodMk measurable_id)
                    hshiftMeasurable).symm
      rw [Kernel.map_apply' _ hhistoryGapMeasurable _ hs]
      rw [Kernel.id_prod_apply' stepKernel z (hhistoryGapMeasurable hs)]
      have hleft :
          (stepKernel z) (Prod.mk z ⁻¹' (historyGap ⁻¹' s)) =
            (Measure.map historyGap (Measure.map (Prod.mk z) (stepKernel z))) s := by
        calc
          (stepKernel z) (Prod.mk z ⁻¹' (historyGap ⁻¹' s)) =
              (Measure.map (Prod.mk z) (stepKernel z)) (historyGap ⁻¹' s) := by
                simpa using
                  (Measure.map_apply ((measurable_const).prodMk measurable_id)
                    (hhistoryGapMeasurable hs) (μ := stepKernel z) (s := historyGap ⁻¹' s)).symm
          _ = (Measure.map historyGap (Measure.map (Prod.mk z) (stepKernel z))) s := by
                simpa using
                  (Measure.map_apply hhistoryGapMeasurable hs
                    (μ := Measure.map (Prod.mk z) (stepKernel z))).symm
      exact hleft.trans (congrArg (fun m : Measure ((Π _ : Finset.Iic n, ℝ) × ℝ) ↦ m s) hmapEq)
    calc
      (((Kernel.id ×ₖ stepKernel).map historyGap) z) s
          = (((stepKernel z).map shift).map (Prod.mk z)) s := hmap
      _ = (Measure.map (Prod.mk z) (νGap : Measure ℝ)) s := by
            rw [hshift]
      _ =
          ((Kernel.id ×ₖ Kernel.const (Π _ : Finset.Iic n, ℝ) (νGap : Measure ℝ)) z) s := by
            rw [Kernel.id_prod_apply' (Kernel.const _ (νGap : Measure ℝ)) z hs]
            rw [Kernel.const_apply, Measure.map_apply (by fun_prop) hs]
  have hhistoryGapMeasure :
      (μ ⊗ₘ stepKernel).map historyGap = μ.prod (νGap : Measure ℝ) := by
    -- Proof comment: the mapped pair law has the history as its first coordinate and the centered
    -- fresh increment as an independent second coordinate.
    calc
      (μ ⊗ₘ stepKernel).map historyGap =
          (((Kernel.id ×ₖ stepKernel).map historyGap) ∘ₘ μ) := by
            rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ (by fun_prop)]
      _ =
          ((Kernel.id ×ₖ Kernel.const (Π _ : Finset.Iic n, ℝ) (νGap : Measure ℝ)) ∘ₘ μ) := by
            rw [hhistoryGapKernel]
      _ = μ ⊗ₘ Kernel.const (Π _ : Finset.Iic n, ℝ) (νGap : Measure ℝ) := by
            rw [Measure.compProd_eq_comp_prod]
      _ = μ.prod (νGap : Measure ℝ) := by
            simpa using
              (Measure.compProd_const
                (μ := μ) (ν := (νGap : Measure ℝ)))
  -- Proof comment: once the centered pair law is `μ.prod νGap`, map the history through
  -- `prefixMap` and then swap the factors.
  calc
    (μ ⊗ₘ stepKernel).map
        (fun p : (Π _ : Finset.Iic n, ℝ) × ℝ ↦
          (p.2 - lastPrefix p.1, prefixMap p.1)) =
        ((μ ⊗ₘ stepKernel).map historyGap).map
          (fun q : (Π _ : Finset.Iic n, ℝ) × ℝ ↦ (q.2, prefixMap q.1)) := by
            simpa [historyGap, Function.comp] using
              (Measure.map_map
                (μ := μ ⊗ₘ stepKernel)
                (f := historyGap)
                (g := fun q : (Π _ : Finset.Iic n, ℝ) × ℝ ↦ (q.2, prefixMap q.1))
                hswapPrefixMeasurable
                hhistoryGapMeasurable).symm
    _ = (μ.prod (νGap : Measure ℝ)).map
          (fun q : (Π _ : Finset.Iic n, ℝ) × ℝ ↦ (q.2, prefixMap q.1)) := by
            rw [hhistoryGapMeasure]
    _ = (((μ.prod (νGap : Measure ℝ)).map (Prod.map prefixMap id)).map Prod.swap) := by
          simpa [Function.comp] using
            (Measure.map_map
              (μ := μ.prod (νGap : Measure ℝ))
              (f := Prod.map prefixMap id)
              (g := Prod.swap)
              measurable_swap
              (hprefixMap.prodMap measurable_id)).symm
    _ = (((μ.map prefixMap).prod (νGap : Measure ℝ)).map Prod.swap) := by
          rw [← Measure.map_prod_map
            (μa := μ) (μc := (νGap : Measure ℝ)) hprefixMap measurable_id]
          simp
    _ = (νGap : Measure ℝ).prod (μ.map prefixMap) := by
          simpa [Measure.map_id] using
            (Measure.prod_swap
              (μ := μ.map prefixMap) (ν := (νGap : Measure ℝ)))

/-- Helper for Example 14.45: under the owner ordered-history law, the initial coordinate is the
deterministic starting point. -/
private theorem consistentFamilyFiniteDimensionalKernel_map_zeroIicCoordinate_eq_dirac
    {n : ℕ}
    (K : ∀ ⦃s t : NNReal⦄, s < t → Kernel ℝ ℝ)
    (hK : ∀ ⦃s t : NNReal⦄ (hst : s < t), IsMarkovKernel (K hst))
    (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) (x : ℝ) :
    (consistentFamilyFiniteDimensionalKernel K j hj x).map
        (fun z : Π _ : Finset.Iic n, ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩) =
      Measure.dirac x := by
  induction n with
  | zero =>
      -- Proof comment: for a one-point history there is only the initial coordinate.
      rw [consistentFamilyFiniteDimensionalKernel_apply]
      rw [consistentFamilyFiniteDimensionalMeasure_zero]
      rw [Measure.map_map
        (measurable_zeroIicCoordinate (n := 0))
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ ℝ)).symm.measurable]
      simp
  | succ n ih =>
      let jPrefix : Π _ : Finset.Iic n, NNReal := fun i ↦
        j ⟨i.1, Finset.mem_Iic.2
          (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
      let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
      let lastPrefix : (Π _ : Finset.Iic n, ℝ) → ℝ := fun z ↦
        z ⟨n, Finset.mem_Iic.2 le_rfl⟩
      let hLastIdx :
          (⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ : Finset.Iic (n + 1)) <
            ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := lastIic_lt_succLast n
      let hLast :
          j ⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ <
            j ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
      let hlastPrefixMeasurable : Measurable lastPrefix := by
        simpa [lastPrefix] using measurable_lastIicCoordinate (n := n)
      letI : IsMarkovKernel (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) :=
        consistentFamilyFiniteDimensionalKernel_isMarkov K
          (fun {_ _} hst ↦ hK hst) jPrefix hjPrefix
      letI : IsProbabilityMeasure (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) :=
        inferInstance
      letI : IsMarkovKernel (Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable) := by
        infer_instance
      -- Proof comment: after splitting off the final state, the first coordinate is still the
      -- first coordinate of the prefix history.
      calc
        (consistentFamilyFiniteDimensionalKernel K j hj x).map
            (fun z : Π _ : Finset.Iic (n + 1), ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le (n + 1))⟩) =
            (((consistentFamilyFiniteDimensionalKernel K j hj x).map (succHistoryEquivLocal n)).map
              (fun p : (Π _ : Finset.Iic n, ℝ) × ℝ ↦
                p.1 ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩)) := by
                  symm
                  simpa [Function.comp, succHistoryEquivLocal_apply] using
                    (Measure.map_map
                      (μ := (consistentFamilyFiniteDimensionalKernel K j hj x))
                      (f := succHistoryEquivLocal n)
                      (g := fun p : (Π _ : Finset.Iic n, ℝ) × ℝ ↦
                        p.1 ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩)
                      ((measurable_zeroIicCoordinate (n := n)).comp measurable_fst)
                      (succHistoryEquivLocal n).measurable)
        _ =
            (((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
                Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable).map
              (fun p : (Π _ : Finset.Iic n, ℝ) × ℝ ↦
                p.1 ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩)) := by
                  rw [consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
                    (K := K) (hK := fun {_ _} hst ↦ hK hst) (j := j) (hj := hj) (x := x)]
        _ =
            (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x).map
              (fun z : Π _ : Finset.Iic n, ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩) := by
                calc
                  (((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
                      Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable).map
                    (fun p : (Π _ : Finset.Iic n, ℝ) × ℝ ↦
                      p.1 ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩)) =
                      ((((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
                          Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable).fst).map
                        (fun z : Π _ : Finset.Iic n, ℝ ↦
                          z ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩)) := by
                            rw [Measure.fst]
                            simpa [Function.comp] using
                              (Measure.map_map
                                (μ := (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
                                  Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable)
                                (f := Prod.fst)
                                (g := fun z : Π _ : Finset.Iic n, ℝ ↦
                                  z ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩)
                                (measurable_zeroIicCoordinate (n := n))
                                measurable_fst).symm
                  _ =
                      (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x).map
                        (fun z : Π _ : Finset.Iic n, ℝ ↦
                          z ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩) := by
                            rw [Measure.fst_compProd]
        _ = Measure.dirac x := by
              exact ih jPrefix hjPrefix

/-- Helper for Example 14.45: the ordered-history finite-dimensional Gaussian law sends adjacent
history differences to the product Gaussian gap law. -/
private theorem gaussianOrderedHistoryIncrementTuple_map_eq_pi
    {n : ℕ} (times : Fin (n + 1) → NNReal)
    (hzero : times 0 = 0) (htimes : StrictMono times) :
    (consistentFamilyFiniteDimensionalMeasure (Measure.dirac 0)
      (fun {s t : NNReal} _ ↦ dirac_convolution_kernel (gaussianReal 0 (t - s)))
      (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes)).map
        (orderedHistoryIncrementTuple (n := n)) =
      Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := by
  rw [← consistentFamilyFiniteDimensionalKernel_apply
    (fun {s t : NNReal} _ ↦ dirac_convolution_kernel (gaussianReal 0 (t - s)))
    (0 : ℝ) (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes)]
  induction n with
  | zero =>
      let K : ∀ ⦃s t : NNReal⦄, s < t → Kernel ℝ ℝ :=
        fun {s t} _ ↦ dirac_convolution_kernel (gaussianReal 0 (t - s))
      letI :
          IsMarkovKernel
            (consistentFamilyFiniteDimensionalKernel K
              (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes)) :=
        consistentFamilyFiniteDimensionalKernel_isMarkov K
          (fun {_ _} hst ↦ by
            dsimp [K]
            infer_instance)
          (orderedTimeChainLocal times)
          (orderedTimeChainLocal_strictMono htimes)
      letI : IsProbabilityMeasure
          ((consistentFamilyFiniteDimensionalKernel K
              (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes)) (0 : ℝ)) :=
        inferInstance
      have hconst :
          orderedHistoryIncrementTuple (n := 0) =
            fun _ : (Π _ : Finset.Iic 0, ℝ) ↦ (isEmptyElim : Fin 0 → ℝ) := by
        funext z i
        exact Fin.elim0 i
      -- Proof comment: a one-point ordered history has no increment coordinates, so both sides
      -- are the unique empty product law.
      rw [hconst, Measure.map_const]
      simpa using
        (Measure.pi_of_empty
          (fun i : Fin 0 ↦ gaussianReal 0 (times i.succ - times i.castSucc))
          (isEmptyElim : Fin 0 → ℝ)).symm
  | succ n ih =>
      let K : ∀ ⦃s t : NNReal⦄, s < t → Kernel ℝ ℝ :=
        fun {s t} _ ↦ dirac_convolution_kernel (gaussianReal 0 (t - s))
      let prefixTimes : Fin (n + 1) → NNReal := dropLastTimes times
      let hprefixStrict : StrictMono prefixTimes := dropLastTimes_strictMono htimes
      let νHist : Measure (Π _ : Finset.Iic (n + 1), ℝ) :=
        consistentFamilyFiniteDimensionalKernel K
          (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes) (0 : ℝ)
      let νPrefix : Measure (Π _ : Finset.Iic n, ℝ) :=
        consistentFamilyFiniteDimensionalKernel K
          (orderedTimeChainLocal prefixTimes)
          (orderedTimeChainLocal_strictMono hprefixStrict) (0 : ℝ)
      let e :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
      let νGap : ProbabilityMeasure ℝ :=
        ⟨gaussianReal 0 (times (Fin.last n).succ - times (Fin.last n).castSucc), inferInstance⟩
      letI :
          IsMarkovKernel
            (consistentFamilyFiniteDimensionalKernel K
              (orderedTimeChainLocal prefixTimes)
              (orderedTimeChainLocal_strictMono hprefixStrict)) :=
        consistentFamilyFiniteDimensionalKernel_isMarkov K
          (fun {_ _} hst ↦ by
            dsimp [K]
            infer_instance)
          (orderedTimeChainLocal prefixTimes)
          (orderedTimeChainLocal_strictMono hprefixStrict)
      letI : IsProbabilityMeasure νPrefix := by
        dsimp [νPrefix]
        infer_instance
      have hsplit :
          νHist.map (succHistoryEquivLocal n) =
            νPrefix ⊗ₘ
              Kernel.comap (dirac_convolution_kernel (νGap : Measure ℝ))
                (fun z : Π _ : Finset.Iic n, ℝ ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                (measurable_lastIicCoordinate (n := n)) := by
        -- Proof comment: split the ordered history into its prefix and the final translated step.
        simpa [νHist, νPrefix, K, νGap, prefixTimes, orderedTimeChainLocal, iicEquivFinLocal] using
          (consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
            (K := K) (hK := fun {_ _} _ ↦ inferInstance) (j := orderedTimeChainLocal times)
            (hj := orderedTimeChainLocal_strictMono htimes) (x := (0 : ℝ)))
      have hpair :
          ((νHist.map (orderedHistoryIncrementTuple (n := n + 1))).map e) =
            (νGap : Measure ℝ).prod
              (Measure.pi
                (fun i : Fin n ↦
                  gaussianReal 0 (prefixTimes i.succ - prefixTimes i.castSucc))) := by
        -- Proof comment: isolate the terminal increment with `piFinSuccAbove`; the split-history
        -- law then factors this last gap from the prefix increment tuple.
        calc
          ((νHist.map (orderedHistoryIncrementTuple (n := n + 1))).map e) =
              (νHist.map
                (fun z : Π _ : Finset.Iic (n + 1), ℝ ↦
                  e (orderedHistoryIncrementTuple (n := n + 1) z))) := by
                    simpa [Function.comp] using
                      (Measure.map_map
                        (μ := νHist)
                        (f := orderedHistoryIncrementTuple (n := n + 1))
                        (g := e)
                        e.measurable
                        (measurable_orderedHistoryIncrementTuple (n := n + 1)))
          _ =
              (νHist.map
                (fun z : Π _ : Finset.Iic (n + 1), ℝ ↦
                  let p := succHistoryEquivLocal n z
                  (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
                    orderedHistoryIncrementTuple (n := n) p.1))) := by
                      congr 1
                      exact orderedHistoryIncrementTuple_piFinSuccAbove_last (n := n)
          _ =
              ((νHist.map (succHistoryEquivLocal n)).map
                (fun p : (Π _ : Finset.Iic n, ℝ) × ℝ ↦
                  (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
                    orderedHistoryIncrementTuple (n := n) p.1))) := by
                      symm
                      exact
                        Measure.map_map
                          ((measurable_snd.sub
                            ((measurable_lastIicCoordinate (n := n)).comp measurable_fst)).prodMk
                            ((measurable_orderedHistoryIncrementTuple (n := n)).comp
                              measurable_fst))
                          (succHistoryEquivLocal n).measurable
          _ =
              ((νPrefix ⊗ₘ
                Kernel.comap (dirac_convolution_kernel (νGap : Measure ℝ))
                  (fun z : Π _ : Finset.Iic n, ℝ ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                  (measurable_lastIicCoordinate (n := n))).map
                (fun p : (Π _ : Finset.Iic n, ℝ) × ℝ ↦
                  (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
                    orderedHistoryIncrementTuple (n := n) p.1))) := by
                      rw [hsplit]
          _ =
              (νGap : Measure ℝ).prod
                (νPrefix.map (orderedHistoryIncrementTuple (n := n))) := by
                simpa [νGap, νPrefix] using
                  (compProd_map_gapAndPrefix_eq_prod
                    (n := n) (Y := Fin n → ℝ)
                    (νGap := νGap) (μ := νPrefix)
                    (lastPrefix := fun z : Π _ : Finset.Iic n, ℝ ↦
                      z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                    (hlastPrefixMeasurable := measurable_lastIicCoordinate (n := n))
                    (prefixMap := orderedHistoryIncrementTuple (n := n))
                    (hprefixMap := measurable_orderedHistoryIncrementTuple (n := n)))
          _ =
              (νGap : Measure ℝ).prod
                (Measure.pi
                  (fun i : Fin n ↦
                    gaussianReal 0 (prefixTimes i.succ - prefixTimes i.castSucc))) := by
                have hprefixZero : prefixTimes 0 = 0 := dropLastTimes_zero hzero
                have hprefixLaw :
                    νPrefix.map (orderedHistoryIncrementTuple (n := n)) =
                      Measure.pi
                        (fun i : Fin n ↦
                          gaussianReal 0 (prefixTimes i.succ - prefixTimes i.castSucc)) := by
                  exact ih prefixTimes hprefixZero hprefixStrict
                rw [hprefixLaw]
      have hpairPi :
          (Measure.pi (fun i : Fin (n + 1) ↦
            gaussianReal 0 (times i.succ - times i.castSucc))).map e =
              (νGap : Measure ℝ).prod
                (Measure.pi
                  (fun i : Fin n ↦
                    gaussianReal 0 (prefixTimes i.succ - prefixTimes i.castSucc))) := by
        simpa [e, νGap, prefixTimes] using
          gaussianIncrementPi_map_piFinSuccAbove_last times
      have hhist :
          νHist.map (orderedHistoryIncrementTuple (n := n + 1)) =
            Measure.pi (fun i : Fin (n + 1) ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := by
        -- Proof comment: `piFinSuccAbove` has the same image law on both sides, so mapping back
        -- by its inverse recovers the full product law.
        calc
          νHist.map (orderedHistoryIncrementTuple (n := n + 1)) =
              ((νHist.map (orderedHistoryIncrementTuple (n := n + 1))).map e).map e.symm := by
                simpa [e] using
                  (MeasurableEquiv.map_map_symm
                    (ν := νHist.map (orderedHistoryIncrementTuple (n := n + 1)))
                    e.symm).symm
          _ =
              ((Measure.pi (fun i : Fin (n + 1) ↦
                gaussianReal 0 (times i.succ - times i.castSucc))).map e).map e.symm := by
                  rw [hpair, hpairPi.symm]
          _ =
              Measure.pi (fun i : Fin (n + 1) ↦
                gaussianReal 0 (times i.succ - times i.castSucc)) := by
                  simpa [e] using
                    (MeasurableEquiv.map_map_symm
                      (ν := Measure.pi
                        (fun i : Fin (n + 1) ↦ gaussianReal 0 (times i.succ - times i.castSucc)))
                      e.symm)
      exact hhist

/-- Helper for Example 14.45: the public finite-dimensional Gaussian Markov law sends adjacent
coordinate differences to the product Gaussian gap law. -/
private theorem gaussianMarkovFiniteDimKernel_incrementTuple_map_eq_pi
    {n : ℕ} (times : Fin (n + 1) → NNReal)
    (hzero : times 0 = 0) (htimes : StrictMono times) :
    ((markovSemigroupFiniteDimKernel
      (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
      times htimes) ∘ₘ Measure.dirac 0).map
        (fun y : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ y i.succ - y i.castSucc) =
      Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := by
  let νHist : Measure (Π _ : Finset.Iic n, ℝ) :=
    consistentFamilyFiniteDimensionalKernel
      (fun {s t : NNReal} _ ↦ dirac_convolution_kernel (gaussianReal 0 (t - s)))
      (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes) (0 : ℝ)
  let publicKernel : Measure (Fin (n + 1) → ℝ) :=
    (markovSemigroupFiniteDimKernel
      (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
      times htimes) ∘ₘ Measure.dirac 0
  have hpublicKernelEq :
      publicKernel =
        Measure.map
          (fun z : Π _ : Finset.Iic n, ℝ ↦ fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i))
          νHist := by
    have hreindexMeasurable :
        Measurable
          (fun z : Π _ : Finset.Iic n, ℝ ↦
            fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i)) := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact measurable_pi_apply ((iicEquivFinLocal n).symm i)
    change
      ((markovSemigroupFiniteDimKernel
          (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
          times htimes) ∘ₘ Measure.dirac 0) =
        Measure.map
          (fun z : Π _ : Finset.Iic n, ℝ ↦ fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i))
          νHist
    rw [Measure.dirac_bind (Kernel.measurable _) (0 : ℝ)]
    simpa [νHist, markovSemigroupFiniteDimKernel] using
      (Kernel.map_apply
        (κ := consistentFamilyFiniteDimensionalKernel
          (fun {s t : NNReal} _ ↦ dirac_convolution_kernel (gaussianReal 0 (t - s)))
          (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes))
        (f := fun z : Π _ : Finset.Iic n, ℝ ↦
          fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i))
        hreindexMeasurable (0 : ℝ))
  have hpublic :
      (Measure.map
        (fun y : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ y i.succ - y i.castSucc)
        (Measure.map
          (fun z : Π _ : Finset.Iic n, ℝ ↦ fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i))
          νHist)) =
        νHist.map (orderedHistoryIncrementTuple (n := n)) := by
    -- Proof comment: the public adjacent-difference tuple is exactly the owner ordered-history
    -- increment tuple after the canonical reindexing to `Fin`.
    simpa [orderedHistoryIncrementTuple, Function.comp] using
      (Measure.map_map
        (μ := νHist)
        (f := fun z : Π _ : Finset.Iic n, ℝ ↦
          fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i))
        (g := fun y : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ y i.succ - y i.castSucc)
        (by
          refine measurable_pi_lambda _ fun i ↦ ?_
          exact (measurable_pi_apply _).sub (measurable_pi_apply _))
        (by
          refine measurable_pi_lambda _ fun i ↦ ?_
          exact measurable_pi_apply ((iicEquivFinLocal n).symm i)))
  -- Proof comment: evaluate the public finite-dimensional kernel at the initial point `0`,
  -- rewrite it through the owner ordered-history law, and then invoke the strict-grid product law.
  have hhist :
      νHist.map (orderedHistoryIncrementTuple (n := n)) =
        Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := by
    calc
      νHist.map (orderedHistoryIncrementTuple (n := n)) =
          (consistentFamilyFiniteDimensionalMeasure (Measure.dirac 0)
            (fun {s t : NNReal} _ ↦ dirac_convolution_kernel (gaussianReal 0 (t - s)))
            (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes)).map
              (orderedHistoryIncrementTuple (n := n)) := by
                rw [← consistentFamilyFiniteDimensionalKernel_apply
                  (fun {s t : NNReal} _ ↦ dirac_convolution_kernel (gaussianReal 0 (t - s)))
                  (0 : ℝ) (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes)]
      _ = Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := by
            exact gaussianOrderedHistoryIncrementTuple_map_eq_pi times hzero htimes
  calc
    publicKernel.map
        (fun y : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ y i.succ - y i.castSucc) =
        Measure.map
          (fun y : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ y i.succ - y i.castSucc)
          (Measure.map
            (fun z : Π _ : Finset.Iic n, ℝ ↦ fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i))
            νHist) := by
              rw [hpublicKernelEq]
    _ = νHist.map (orderedHistoryIncrementTuple (n := n)) := hpublic
    _ = Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := hhist

/-- Helper for Example 14.45: zero-prepended partial sums invert adjacent differences on finite
tuples whose initial coordinate is `0`. -/
private theorem prependZeroPartialSums_incrementTupleOnTuples_eq
    {n : ℕ} {y : Fin (n + 1) → ℝ} (hy0 : y 0 = 0) :
    prependZeroPartialSums (fun i : Fin n ↦ y i.succ - y i.castSucc) = y := by
  -- Proof comment: evaluate the reconstructed tuple coordinatewise; the base coordinate is fixed
  -- by `hy0`, and each successor coordinate is obtained by adding one more adjacent increment to
  -- the previous partial sum.
  funext i
  induction i using Fin.induction with
  | zero =>
      simpa [prependZeroPartialSums, hy0]
  | succ i hi =>
      rw [show
          prependZeroPartialSums (fun j : Fin n ↦ y j.succ - y j.castSucc) i.succ =
            Fin.partialSum (fun j : Fin n ↦ y j.succ - y j.castSucc) i.succ by
          rfl]
      rw [Fin.partialSum_succ]
      rw [show
          Fin.partialSum (fun j : Fin n ↦ y j.succ - y j.castSucc) i.castSucc =
            y i.castSucc by
          simpa [prependZeroPartialSums] using hi]
      ring

/-- Helper for Example 14.45: a finite tuple law with deterministic initial coordinate is the
pushforward of its increment-tuple law by zero-prepended partial sums. -/
private theorem tupleMeasure_eq_prependZeroPartialSums_of_zero_start
    {n : ℕ} {ν : Measure (Fin (n + 1) → ℝ)}
    (hzero : ν.map (Function.eval 0) = Measure.dirac 0) :
    ν =
      (ν.map (fun y : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ y i.succ - y i.castSucc)).map
        (prependZeroPartialSums (n := n)) := by
  let incrementTupleOnTuples : (Fin (n + 1) → ℝ) → Fin n → ℝ :=
    fun y i ↦ y i.succ - y i.castSucc
  have hmeasIncrementTupleOnTuples : Measurable incrementTupleOnTuples := by
    -- Proof comment: each tuple increment coordinate is a measurable difference of two
    -- coordinate projections.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact (measurable_pi_apply _).sub (measurable_pi_apply _)
  have hstart : HasLaw (Function.eval 0) (Measure.dirac 0) ν :=
    ⟨(measurable_pi_apply 0).aemeasurable, hzero⟩
  have hcomp :
      id =ᵐ[ν] (prependZeroPartialSums (n := n)) ∘ incrementTupleOnTuples := by
    have hy0 : ∀ᵐ y ∂ν, y 0 = 0 := by
      exact (hstart.ae_iff (p := fun x : ℝ ↦ x = 0) (by fun_prop)).2 (by simp)
    filter_upwards [hy0] with y hy0y
    funext i
    symm
    exact congrFun (prependZeroPartialSums_incrementTupleOnTuples_eq (n := n) hy0y) i
  -- Proof comment: the deterministic start-at-zero coordinate makes the identity map agree
  -- almost everywhere with the composition "take adjacent differences, then reconstruct by
  -- partial sums".
  calc
    ν = ν.map id := by
      symm
      rw [Measure.map_id]
    _ = ν.map ((prependZeroPartialSums (n := n)) ∘ incrementTupleOnTuples) := by
      rw [Measure.map_congr hcomp]
    _ = (ν.map incrementTupleOnTuples).map (prependZeroPartialSums (n := n)) := by
      rw [Measure.map_map (measurable_prependZeroPartialSums (n := n))
        hmeasIncrementTupleOnTuples]
    _ =
        (ν.map (fun y : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ y i.succ - y i.castSucc)).map
          (prependZeroPartialSums (n := n)) := by
      rfl

/-- Helper for Example 14.45: on an anchored strict grid, the Gaussian Markov finite-dimensional
law is the pushforward of the product Gaussian gap law by `prependZeroPartialSums`. -/
private theorem gaussianMarkovFiniteDimLaw_eq_prependZeroPartialSumsPushforward
    {n : ℕ} (times : Fin (n + 1) → NNReal)
    (hzero : times 0 = 0) (htimes : StrictMono times) :
    markovSemigroupFiniteDimKernel
        (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
        times htimes ∘ₘ Measure.dirac 0 =
      (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc))).map
        (prependZeroPartialSums (n := n)) := by
  let νHist : Measure (Π _ : Finset.Iic n, ℝ) :=
    consistentFamilyFiniteDimensionalKernel
      (fun {s t : NNReal} _ ↦ dirac_convolution_kernel (gaussianReal 0 (t - s)))
      (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes) (0 : ℝ)
  let reindex : (Π _ : Finset.Iic n, ℝ) → Fin (n + 1) → ℝ :=
    fun z i ↦ z ((iicEquivFinLocal n).symm i)
  have hreindexMeasurable : Measurable reindex := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_pi_apply ((iicEquivFinLocal n).symm i)
  have hpublicKernel :
      markovSemigroupFiniteDimKernel
          (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
          times htimes 0 =
        Measure.map reindex νHist := by
    simpa [νHist, reindex, markovSemigroupFiniteDimKernel] using
      (Kernel.map_apply
        (κ := consistentFamilyFiniteDimensionalKernel
          (fun {s t : NNReal} _ ↦ dirac_convolution_kernel (gaussianReal 0 (t - s)))
          (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes))
        (f := reindex) hreindexMeasurable (0 : ℝ))
  have hzeroCoord :
      (markovSemigroupFiniteDimKernel
          (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
          times htimes 0).map (Function.eval 0) =
        Measure.dirac 0 := by
    -- Proof comment: the public time-zero coordinate is the owner zero-history coordinate, which
    -- is fixed by the initial Dirac law at `0`.
    calc
      (markovSemigroupFiniteDimKernel
          (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
          times htimes 0).map (Function.eval 0) =
          (Measure.map reindex νHist).map (Function.eval 0) := by
            rw [hpublicKernel]
      _ = νHist.map (fun z : Π _ : Finset.Iic n, ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩) := by
            rw [Measure.map_map (measurable_pi_apply 0) hreindexMeasurable]
            rfl
      _ = Measure.dirac 0 := by
            exact
              consistentFamilyFiniteDimensionalKernel_map_zeroIicCoordinate_eq_dirac
                (K := fun {s t : NNReal} _ ↦ dirac_convolution_kernel (gaussianReal 0 (t - s)))
                (hK := fun {_ _} hst ↦ by
                  dsimp
                  infer_instance)
                (j := orderedTimeChainLocal times)
                (hj := orderedTimeChainLocal_strictMono htimes)
                (x := (0 : ℝ))
  -- Proof comment: reconstruct the finite tuple from its adjacent increments using the
  -- deterministic start-at-zero coordinate.
  rw [Measure.dirac_bind (Kernel.measurable _) (0 : ℝ)]
  calc
    markovSemigroupFiniteDimKernel
        (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
        times htimes 0 =
      ((markovSemigroupFiniteDimKernel
          (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
          times htimes 0).map
            (fun y : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ y i.succ - y i.castSucc)).map
          (prependZeroPartialSums (n := n)) := by
            exact tupleMeasure_eq_prependZeroPartialSums_of_zero_start hzeroCoord
    _ =
      (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc))).map
        (prependZeroPartialSums (n := n)) := by
          exact congrArg
            (fun m : Measure (Fin n → ℝ) ↦ m.map (prependZeroPartialSums (n := n)))
            (by
              simpa [Measure.dirac_bind (Kernel.measurable _) (0 : ℝ)] using
                gaussianMarkovFiniteDimKernel_incrementTuple_map_eq_pi times hzero htimes)

/-- Helper for Example 14.45: the canonical Gaussian Markov path measure sends the increment tuple
on an anchored strict grid to the product law of the Gaussian gaps. -/
private theorem canonicalGaussianIncrementTuple_map_eq_pi
    {P : Measure (NNReal → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernel
              (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
              times htimes ∘ₘ Measure.dirac 0)
    {n : ℕ} (times : Fin (n + 1) → NNReal)
    (hzero : times 0 = 0) (htimes : StrictMono times) :
    P.map (pathIncrementTuple times) =
      Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := by
  let incrementTupleOnTuples : (Fin (n + 1) → ℝ) → Fin n → ℝ :=
    fun y i ↦ y i.succ - y i.castSucc
  have hmeasIncrementTupleOnTuples : Measurable incrementTupleOnTuples := by
    -- Proof comment: each output coordinate is a measurable adjacent difference of tuple
    -- coordinates.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact (measurable_pi_apply _).sub (measurable_pi_apply _)
  have hcomp :
      incrementTupleOnTuples ∘ finiteDimensionalProjection times = pathIncrementTuple times := by
    -- Proof comment: the public increment tuple is exactly the adjacent-difference map applied to
    -- the finite-dimensional coordinate tuple.
    simpa [incrementTupleOnTuples] using
      incrementTuple_comp_finiteDimensionalProjection times
  have hid :
      incrementTupleOnTuples ∘ prependZeroPartialSums (n := n) = id := by
    -- Proof comment: taking adjacent differences after zero-prepended partial sums returns the
    -- original increment vector.
    funext z
    simpa [incrementTupleOnTuples] using
      incrementTuple_prependZeroPartialSums_eq_self (n := n) z
  -- Proof comment: rewrite the finite-dimensional marginal by `hP_fdim` and then apply the
  -- public strict-grid adjacent-difference product law directly.
  calc
    P.map (pathIncrementTuple times) =
        P.map (incrementTupleOnTuples ∘ finiteDimensionalProjection times) := by
          simpa [hcomp]
    _ = (P.map (finiteDimensionalProjection times)).map incrementTupleOnTuples := by
          symm
          rw [Measure.map_map hmeasIncrementTupleOnTuples
            (measurable_finiteDimensionalProjection times)]
    _ =
        ((markovSemigroupFiniteDimKernel
          (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
          times htimes ∘ₘ Measure.dirac 0)).map incrementTupleOnTuples := by
            rw [hP_fdim times hzero htimes]
    _ = Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := by
          simpa [incrementTupleOnTuples] using
            gaussianMarkovFiniteDimKernel_incrementTuple_map_eq_pi times hzero htimes

/-- Helper for Example 14.45: a zero-length increment of the canonical process is the constant
`0` random variable, so its law is `Measure.dirac 0`. -/
private theorem selfIncrement_hasLaw_diracZero
    {P : Measure (NNReal → ℝ)} [IsProbabilityMeasure P] (t : NNReal) :
    HasLaw
      (fun ω : NNReal → ℝ ↦ ω t - ω t)
      (Measure.dirac 0)
      P := by
  -- Proof comment: the increment map is pointwise equal to `0`, so its pushforward is the Dirac
  -- mass at `0`.
  refine ⟨((measurable_pi_apply t).sub (measurable_pi_apply t)).aemeasurable, ?_⟩
  ext A hA
  simp [hA]

/-- Helper for Example 14.45: the canonical two-point time tuple `(0, t)` on `Fin 2`. -/
private def twoPointTimes (t : NNReal) : Fin 2 → NNReal
  | 0 => 0
  | 1 => t

/-- Helper for Example 14.45: if `t > 0`, then `(0, t)` is strictly increasing. -/
private theorem twoPointTimes_strictMono {t : NNReal} (ht : 0 < t) :
    StrictMono (twoPointTimes t) := by
  -- Proof comment: the only nontrivial comparison in `Fin 2` is `0 < 1`, which maps to `0 < t`.
  intro i j hij
  have hijNat : (i : ℕ) < j := hij
  fin_cases i <;> fin_cases j
  · have : False := by simpa using hij
    exact this.elim
  · simpa [twoPointTimes] using ht
  · have : False := by simpa using hij
    exact this.elim
  · have : False := by simpa using hij
    exact this.elim

/-- Helper for Example 14.45: on `(0, t)`, the unique increment coordinate is `ω t - ω 0`. -/
private theorem twoPointTimesIncrementAdapter (t : NNReal) :
    (Function.eval 0) ∘ pathIncrementTuple (twoPointTimes t) =
      (fun ω : NNReal → ℝ ↦ ω t - ω 0) := by
  -- Proof comment: `pathIncrementTuple` on the two-point grid reads the difference between the
  -- terminal and initial coordinates.
  funext ω
  simp [pathIncrementTuple, twoPointTimes]

/-- Helper for Example 14.45: the canonical three-point time tuple `(0, s, t)` on `Fin 3`. -/
private def threePointTimes (s t : NNReal) : Fin 3 → NNReal
  | 0 => 0
  | 1 => s
  | 2 => t

/-- Helper for Example 14.45: if `0 < s < t`, then `(0, s, t)` is strictly increasing. -/
private theorem threePointTimes_strictMono {s t : NNReal} (hs : 0 < s) (hst : s < t) :
    StrictMono (threePointTimes s t) := by
  -- Proof comment: the only forward comparisons in `Fin 3` are `0 < 1`, `0 < 2`, and `1 < 2`.
  intro i j hij
  have hijNat : (i : ℕ) < j := hij
  fin_cases i <;> fin_cases j
  · have : False := by simpa using hij
    exact this.elim
  · simpa [threePointTimes] using hs
  · simpa [threePointTimes] using lt_trans hs hst
  · have : False := by simpa using hij
    exact this.elim
  · have : False := by simpa using hij
    exact this.elim
  · simpa [threePointTimes] using hst
  · have : False := by simpa using hij
    exact this.elim
  · have : False := by simpa using hij
    exact this.elim
  · have : False := by simpa using hij
    exact this.elim

/-- Helper for Example 14.45: on `(0, s, t)`, the second increment coordinate is `ω t - ω s`. -/
private theorem threePointTimesIncrementAdapter (s t : NNReal) :
    (Function.eval 1) ∘ pathIncrementTuple (threePointTimes s t) =
      (fun ω : NNReal → ℝ ↦ ω t - ω s) := by
  -- Proof comment: the second adjacent difference in the three-point grid is exactly the
  -- interval increment over `[s, t]`.
  funext ω
  simp [pathIncrementTuple, threePointTimes]

/-- Helper for Example 14.45: delete the later endpoint of one adjacent duplicate from a finite
time grid. -/
private def deleteAdjacentDuplicateTimes {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1)) : Fin (n + 1) → NNReal :=
  fun i ↦ times (k.succ.succAbove i)

/-- Helper for Example 14.45: deleting the later endpoint of an adjacent duplicate preserves the
anchored start at `0`. -/
private theorem deleteAdjacentDuplicateTimes_zero {n : ℕ}
    {times : Fin (n + 2) → NNReal} {k : Fin (n + 1)} (hzero : times 0 = 0) :
    deleteAdjacentDuplicateTimes times k 0 = 0 := by
  -- Proof comment: the deleted coordinate is always positive, so the initial time survives.
  simpa [deleteAdjacentDuplicateTimes] using hzero

/-- Helper for Example 14.45: deleting the later endpoint of an adjacent duplicate preserves
monotonicity. -/
private theorem deleteAdjacentDuplicateTimes_monotone {n : ℕ}
    {times : Fin (n + 2) → NNReal} {k : Fin (n + 1)} (htimes : Monotone times) :
    Monotone (deleteAdjacentDuplicateTimes times k) := by
  -- Proof comment: `Fin.succAbove` preserves the order of all surviving coordinates.
  intro i j hij
  exact htimes (by simpa [deleteAdjacentDuplicateTimes] using hij)

/-- Helper for Example 14.45: on the shortened grid, the successor coordinate is the successor of
the surviving long-grid increment index. -/
private theorem deleteAdjacentDuplicateTimes_succ {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1)) (i : Fin n) :
    deleteAdjacentDuplicateTimes times k i.succ = times (k.succAbove i).succ := by
  -- Proof comment: `succAbove` commutes with `succ` when deleting the right endpoint of the
  -- duplicated adjacent pair.
  simp [deleteAdjacentDuplicateTimes]

/-- Helper for Example 14.45: on the shortened grid, the surviving left endpoint matches the
corresponding long-grid increment index. -/
private theorem deleteAdjacentDuplicateTimes_castSucc {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1))
    (hdup : times k.castSucc = times k.succ) (i : Fin n) :
    deleteAdjacentDuplicateTimes times k i.castSucc = times (k.succAbove i).castSucc := by
  -- Proof comment: before the duplicated pair, both index constructions are literally the same;
  -- at or after the duplicate, either we use the duplicate equality `hdup` or both sides shift to
  -- the same successor index.
  change times (k.succ.succAbove i.castSucc) = times (k.succAbove i).castSucc
  by_cases hik : i.castSucc < k
  · rw [show k.succ.succAbove i.castSucc = i.castSucc.castSucc by
        exact Fin.succAbove_succ_of_le k i.castSucc (le_of_lt hik)]
    rw [Fin.succAbove_of_castSucc_lt k i hik]
  · have hk : k ≤ i.castSucc := le_of_not_gt hik
    rcases lt_or_eq_of_le hk with hki | hEq
    · rw [show k.succ.succAbove i.castSucc = i.castSucc.succ by
          exact Fin.succAbove_of_le_castSucc k.succ i.castSucc
            (Fin.succ_le_castSucc_iff.mpr hki)]
      rw [Fin.succAbove_of_le_castSucc k i hk, Fin.succ_castSucc]
    · subst hEq
      rw [Fin.succAbove_succ_self, Fin.succAbove_castSucc_self]
      exact hdup.trans (congrArg times (Fin.succ_castSucc i))

/-- Helper for Example 14.45: if two adjacent times coincide, then separating that increment
coordinate exposes a deterministic `0` together with the shortened increment tuple. -/
private theorem pathIncrementTuple_piFinSuccAbove_of_adjacentDuplicate {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1))
    (hdup : times k.castSucc = times k.succ) :
    (fun ω ↦
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) k
        (pathIncrementTuple times ω)) =
      fun ω ↦ (0, pathIncrementTuple (deleteAdjacentDuplicateTimes times k) ω) := by
  -- Proof comment: the separated increment is the duplicated zero gap, and every surviving
  -- coordinate matches the shortened-grid increment tuple.
  funext ω
  apply Prod.ext
  · simp [pathIncrementTuple, MeasurableEquiv.piFinSuccAbove_apply, hdup]
  · ext i
    change
      ω (times (k.succAbove i).succ) - ω (times (k.succAbove i).castSucc) =
        ω (deleteAdjacentDuplicateTimes times k i.succ) -
          ω (deleteAdjacentDuplicateTimes times k i.castSucc)
    rw [deleteAdjacentDuplicateTimes_succ, deleteAdjacentDuplicateTimes_castSucc _ _ hdup]

/-- Helper for Example 14.45: the Gaussian product law on a grid with one adjacent duplicate is
the zero-insertion of the shortened Gaussian product law. -/
private theorem gaussianIncrementPi_map_piFinSuccAbove_of_adjacentDuplicate {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1))
    (hdup : times k.castSucc = times k.succ) :
    (Measure.pi (fun i : Fin (n + 1) ↦ gaussianReal 0 (times i.succ - times i.castSucc))).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) k) =
        (Measure.dirac 0).prod
          (Measure.pi (fun i : Fin n ↦
            gaussianReal 0
              ((deleteAdjacentDuplicateTimes times k) i.succ -
                (deleteAdjacentDuplicateTimes times k) i.castSucc))) := by
  let μ : Fin (n + 1) → Measure ℝ := fun i ↦
    gaussianReal 0 (times i.succ - times i.castSucc)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) k
  have hMapEq :
      (Measure.pi μ).map e = (μ k).prod (Measure.pi fun i : Fin n ↦ μ (k.succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ k).map_eq
  have hk : μ k = Measure.dirac 0 := by
    -- Proof comment: the duplicated adjacent gap has variance `0`, so its Gaussian law is `δ₀`.
    simpa [μ, hdup] using (gaussianReal_zero_var (γ := (0 : ℝ)) (σ2 := (0 : ℝ≥0)))
  have htail :
      (fun i : Fin n ↦ μ (k.succAbove i)) =
        (fun i : Fin n ↦
          gaussianReal 0
            ((deleteAdjacentDuplicateTimes times k) i.succ -
              (deleteAdjacentDuplicateTimes times k) i.castSucc)) := by
    -- Proof comment: every surviving marginal is the Gaussian gap law on the shortened grid.
    funext i
    simp [μ, deleteAdjacentDuplicateTimes_succ, deleteAdjacentDuplicateTimes_castSucc, hdup]
  rw [hMapEq, hk, htail]

/-- Helper for Example 14.45: the strict-grid Gaussian increment product law extends to monotone
anchored grids by repeatedly deleting adjacent duplicate times. -/
private theorem canonicalGaussianIncrementTuple_map_eq_pi_of_monotone_start_zero
    {P : Measure (NNReal → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernel
              (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
              times htimes ∘ₘ Measure.dirac 0) :
    ∀ {n : ℕ} (times : Fin (n + 1) → NNReal), times 0 = 0 → Monotone times →
      P.map (pathIncrementTuple times) =
        Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc))
    := by
  intro n times hzero htimes
  letI : IsProbabilityMeasure P :=
    (canonicalGaussianPathMeasureStart_hasLaw hP_fdim).isProbabilityMeasure
  induction n with
  | zero =>
      -- Proof comment: an anchored grid with no increments has the trivial empty product law.
      have hconst :
          pathIncrementTuple times =
            fun _ : NNReal → ℝ ↦ (isEmptyElim : Fin 0 → ℝ) := by
        funext ω i
        exact Fin.elim0 i
      rw [hconst, Measure.map_const]
      simpa using
        (Measure.pi_of_empty
          (fun i : Fin 0 ↦ gaussianReal 0 (times i.succ - times i.castSucc))
          (isEmptyElim : Fin 0 → ℝ)).symm
  | succ n ih =>
      by_cases hstrict : StrictMono times
      · -- Proof comment: once the grid is strict, the strict-grid theorem applies directly.
        exact canonicalGaussianIncrementTuple_map_eq_pi hP_fdim times hzero hstrict
      · have hnotlt : ¬ ∀ i : Fin (n + 1), times i.castSucc < times i.succ := by
          simpa [Fin.strictMono_iff_lt_succ] using hstrict
        push Not at hnotlt
        obtain ⟨k, hk⟩ := hnotlt
        have hdup : times k.castSucc = times k.succ := by
          -- Proof comment: on a monotone grid, failure of strict increase means one adjacent pair
          -- coincides.
          exact le_antisymm (htimes Fin.castSucc_lt_succ.le) hk
        let times' : Fin (n + 1) → NNReal := deleteAdjacentDuplicateTimes times k
        have hzero' : times' 0 = 0 := deleteAdjacentDuplicateTimes_zero hzero
        have htimes' : Monotone times' := deleteAdjacentDuplicateTimes_monotone htimes
        have hshort :
            P.map (pathIncrementTuple times') =
              Measure.pi (fun i : Fin n ↦
                gaussianReal 0 (times' i.succ - times' i.castSucc)) :=
          ih times' hzero' htimes'
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) k
        have hpair :
            (P.map (pathIncrementTuple times)).map e =
              (P.map (pathIncrementTuple times')).map (Prod.mk (0 : ℝ)) := by
          -- Proof comment: splitting at the duplicated increment exposes a deterministic zero and
          -- the shortened-grid increment tuple.
          calc
            (P.map (pathIncrementTuple times)).map e =
                P.map (fun ω ↦ e (pathIncrementTuple times ω)) := by
                  simpa [Function.comp] using
                    (Measure.map_map e.measurable
                      (measurable_pathIncrementTuple times))
            _ = P.map (fun ω ↦ (0, pathIncrementTuple times' ω)) := by
                  congr 1
                  exact pathIncrementTuple_piFinSuccAbove_of_adjacentDuplicate times k hdup
            _ = (P.map (pathIncrementTuple times')).map (Prod.mk (0 : ℝ)) := by
                  simpa [Function.comp] using
                    (Measure.map_map
                      (μ := P)
                      (f := pathIncrementTuple times')
                      (g := Prod.mk (0 : ℝ))
                      ((measurable_const).prodMk measurable_id)
                      (measurable_pathIncrementTuple times')).symm
        have hpairPi :
            (Measure.pi (fun i : Fin (n + 1) ↦ gaussianReal 0 (times i.succ - times i.castSucc))).map e =
                (Measure.pi (fun i : Fin n ↦
                  gaussianReal 0 (times' i.succ - times' i.castSucc))).map
                    (Prod.mk (0 : ℝ)) := by
          -- Proof comment: the product gap law undergoes the same zero-insertion normalization.
          calc
            (Measure.pi (fun i : Fin (n + 1) ↦ gaussianReal 0 (times i.succ - times i.castSucc))).map e =
                (Measure.dirac (0 : ℝ)).prod
                  (Measure.pi (fun i : Fin n ↦
                    gaussianReal 0 (times' i.succ - times' i.castSucc))) := by
                      simpa [times'] using
                        gaussianIncrementPi_map_piFinSuccAbove_of_adjacentDuplicate times k hdup
            _ =
                (Measure.pi (fun i : Fin n ↦
                  gaussianReal 0 (times' i.succ - times' i.castSucc))).map
                    (Prod.mk (0 : ℝ)) := by
                      rw [Measure.dirac_prod]
        -- Proof comment: compare both image laws after deleting the duplicated coordinate, then
        -- map back through `e`.
        calc
          P.map (pathIncrementTuple times) =
              ((P.map (pathIncrementTuple times)).map e).map e.symm := by
                simpa [e] using
                  (MeasurableEquiv.map_map_symm
                    (ν := P.map (pathIncrementTuple times)) e.symm).symm
          _ = (((P.map (pathIncrementTuple times')).map (Prod.mk (0 : ℝ))).map e.symm) := by
                rw [hpair]
          _ =
              (((Measure.pi (fun i : Fin n ↦
                gaussianReal 0 (times' i.succ - times' i.castSucc))).map
                  (Prod.mk (0 : ℝ))).map e.symm) := by
                    rw [hshort]
          _ =
              (((Measure.pi (fun i : Fin (n + 1) ↦
                gaussianReal 0 (times i.succ - times i.castSucc))).map e)).map e.symm := by
                    rw [hpairPi.symm]
          _ =
              Measure.pi (fun i : Fin (n + 1) ↦
                gaussianReal 0 (times i.succ - times i.castSucc)) := by
                  simpa [e] using
                    (MeasurableEquiv.map_map_symm
                      (ν := Measure.pi
                        (fun i : Fin (n + 1) ↦ gaussianReal 0 (times i.succ - times i.castSucc)))
                      e.symm)

/-- Helper for Example 14.45: every canonical Gaussian increment over `[s, t]` has law
`gaussianReal 0 (t - s)`. -/
private theorem canonicalGaussianIncrement_hasLaw
    {P : Measure (NNReal → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernel
              (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
              times htimes ∘ₘ Measure.dirac 0)
    {s t : NNReal} (hst : s ≤ t) :
    HasLaw
      (fun ω : NNReal → ℝ ↦ ω t - ω s)
      (gaussianReal 0 (t - s))
      P := by
  letI : IsProbabilityMeasure P := (canonicalGaussianPathMeasureStart_hasLaw hP_fdim).isProbabilityMeasure
  rcases lt_or_eq_of_le hst with hst' | rfl
  · by_cases hs : s = 0
    · have htpos : 0 < t := by simpa [hs] using hst'
      subst hs
      let times : Fin 2 → NNReal := twoPointTimes t
      have htupleLaw :
          HasLaw
            (Function.eval 0)
            (gaussianReal 0 t)
            (P.map (pathIncrementTuple times)) := by
        refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
        calc
          (P.map (pathIncrementTuple times)).map (Function.eval 0) =
              (Measure.pi (fun i : Fin 1 ↦ gaussianReal 0 (times i.succ - times i.castSucc))).map
                (Function.eval 0) := by
                  rw [canonicalGaussianIncrementTuple_map_eq_pi hP_fdim times rfl
                    (twoPointTimes_strictMono htpos)]
          _ = gaussianReal 0 t := by
                simpa [times, twoPointTimes, Measure.pi_map_eval]
      -- Proof comment: on the two-point anchored grid, the unique increment coordinate is the
      -- interval increment over `[0, t]`.
      simpa [times, twoPointTimesIncrementAdapter] using
        (HasLaw.comp htupleLaw
          ⟨(measurable_pathIncrementTuple times).aemeasurable, rfl⟩)
    · have hspos : 0 < s := pos_iff_ne_zero.mpr hs
      let times : Fin 3 → NNReal := threePointTimes s t
      have htupleLaw :
          HasLaw
            (Function.eval 1)
            (gaussianReal 0 (t - s))
            (P.map (pathIncrementTuple times)) := by
        refine ⟨(measurable_pi_apply 1).aemeasurable, ?_⟩
        calc
          (P.map (pathIncrementTuple times)).map (Function.eval 1) =
              (Measure.pi (fun i : Fin 2 ↦ gaussianReal 0 (times i.succ - times i.castSucc))).map
                (Function.eval 1) := by
                  rw [canonicalGaussianIncrementTuple_map_eq_pi hP_fdim times rfl
                    (threePointTimes_strictMono hspos hst')]
          _ = gaussianReal 0 (t - s) := by
                simpa [times, threePointTimes, Measure.pi_map_eval]
      -- Proof comment: on the three-point grid `(0, s, t)`, the second increment coordinate is
      -- exactly the interval increment over `[s, t]`.
      simpa [times, threePointTimesIncrementAdapter] using
        (HasLaw.comp htupleLaw
          ⟨(measurable_pathIncrementTuple times).aemeasurable, rfl⟩)
  · -- Proof comment: a zero-length increment is identically `0`, and `gaussianReal 0 0 = δ₀`.
    simpa [gaussianReal_zero_var] using (selfIncrement_hasLaw_diracZero (P := P) s)

/-- Helper for Example 14.45: the canonical Gaussian path measure has stationary increment laws. -/
private theorem canonicalGaussianHasStationaryIncrementLaws
    {P : Measure (NNReal → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernel
              (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
              times htimes ∘ₘ Measure.dirac 0) :
    HasStationaryIncrementLaws Function.eval P := by
  intro r s t
  have hleft_le : t + r ≤ (s + t) + r := by
    have hbase : t ≤ t + s := le_add_of_nonneg_right (show 0 ≤ s from bot_le)
    simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hbase r
  have hright_le : r ≤ s + r := by
    have hbase : r ≤ r + s := le_add_of_nonneg_right (show 0 ≤ s from bot_le)
    simpa [add_assoc, add_left_comm, add_comm] using hbase
  have hleftRaw :
      HasLaw
        (fun ω : NNReal → ℝ ↦ ω ((s + t) + r) - ω (t + r))
        (gaussianReal 0 (((s + t) + r) - (t + r)))
        P := by
    -- Proof comment: the increment over `[(t + r), (s + t) + r]` only depends on its lag.
    simpa [add_assoc, add_left_comm, add_comm] using
      (canonicalGaussianIncrement_hasLaw hP_fdim (s := t + r) (t := (s + t) + r) hleft_le)
  have hrightRaw :
      HasLaw
        (fun ω : NNReal → ℝ ↦ ω (s + r) - ω r)
        (gaussianReal 0 ((s + r) - r))
        P := by
    -- Proof comment: the translated interval `[r, s + r]` has the same lag `s`.
    simpa [add_assoc, add_left_comm, add_comm] using
      (canonicalGaussianIncrement_hasLaw hP_fdim (s := r) (t := s + r) hright_le)
  have hleftGap : ((s + t) + r) - (t + r) = s := by
    rw [add_assoc, add_tsub_cancel_right]
  have hrightGap : (s + r) - r = s := by
    rw [add_tsub_cancel_right]
  have hleft :
      HasLaw
        (fun ω : NNReal → ℝ ↦ ω ((s + t) + r) - ω (t + r))
        (gaussianReal 0 s)
        P := by
    rwa [hleftGap] at hleftRaw
  have hright :
      HasLaw
        (fun ω : NNReal → ℝ ↦ ω (s + r) - ω r)
        (gaussianReal 0 s)
        P := by
    rwa [hrightGap] at hrightRaw
  exact hleft.identDistrib hright

/-- Helper for Example 14.45: the canonical Gaussian path measure has independent increments. -/
private theorem canonicalGaussianHasIndepIncrements
    {P : Measure (NNReal → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernel
              (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
              times htimes ∘ₘ Measure.dirac 0) :
    HasIndepIncrements Function.eval P := by
  classical
  letI : IsProbabilityMeasure P := (canonicalGaussianPathMeasureStart_hasLaw hP_fdim).isProbabilityMeasure
  rw [hasIndepIncrements_iff_nat]
  intro t ht
  -- Proof comment: package the monotone `ℕ`-grid through one finite anchored prefix, identify the
  -- full increment tuple law there, and then restrict back to the requested finite family.
  refine iIndepFun_iff_finset.2 ?_
  intro s
  by_cases hs : s.Nonempty
  · let N : ℕ := s.max' hs + 1
    let times : Fin (N + 2) → NNReal := Fin.cases 0 fun i ↦ t i
    have htimes : Monotone times := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              simp [times]
          | succ j =>
              simp [times]
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              cases hij
          | succ j =>
              simpa [times] using ht (show i ≤ j by simpa using hij)
    have hgrid :
        P.map (pathIncrementTuple times) =
          Measure.pi (fun i : Fin (N + 1) ↦ gaussianReal 0 (times i.succ - times i.castSucc)) :=
      canonicalGaussianIncrementTuple_map_eq_pi_of_monotone_start_zero hP_fdim times
        (by simp [times]) htimes
    have hcoord (i : Fin (N + 1)) :
        P.map (fun ω : NNReal → ℝ ↦ pathIncrementTuple times ω i) =
          gaussianReal 0 (times i.succ - times i.castSucc) := by
      calc
        P.map (fun ω : NNReal → ℝ ↦ pathIncrementTuple times ω i) =
            (P.map (pathIncrementTuple times)).map (Function.eval i) := by
              symm
              simpa [Function.comp] using
                (Measure.map_map
                  (μ := P)
                  (f := pathIncrementTuple times)
                  (g := Function.eval i)
                  (measurable_pi_apply i)
                  (measurable_pathIncrementTuple times))
        _ = gaussianReal 0 (times i.succ - times i.castSucc) := by
              simpa [Measure.pi_map_eval] using
                congrArg
                  (fun m : Measure (Fin (N + 1) → ℝ) ↦ m.map (Function.eval i))
                  hgrid
    have hfull :
        iIndepFun
          (fun i : Fin (N + 1) ↦ fun ω : NNReal → ℝ ↦ pathIncrementTuple times ω i)
          P := by
      -- Proof comment: the anchored finite-grid product-law equality is exactly the `iIndepFun`
      -- criterion for the full increment tuple.
      refine (iIndepFun_iff_map_fun_eq_pi_map ?_).2 ?_
      · intro i
        exact ((measurable_pi_apply i).comp (measurable_pathIncrementTuple times)).aemeasurable
      · calc
          P.map (fun ω ↦ fun i : Fin (N + 1) ↦ pathIncrementTuple times ω i) =
              P.map (pathIncrementTuple times) := by
                rfl
          _ =
              Measure.pi (fun i : Fin (N + 1) ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := hgrid
          _ =
              Measure.pi (fun i : Fin (N + 1) ↦
                P.map (fun ω : NNReal → ℝ ↦ pathIncrementTuple times ω i)) := by
                  congr 1
                  funext i
                  exact (hcoord i).symm
    have htail :
        iIndepFun
          (fun i : Fin N ↦ fun ω : NNReal → ℝ ↦ pathIncrementTuple times ω i.succ)
          P := by
      -- Proof comment: removing the leading anchored increment preserves independence.
      exact hfull.precomp (g := Fin.succ) fun a b h ↦ by simpa using h
    let g : s → Fin N := fun x ↦
      ⟨x.1, Nat.lt_of_le_of_lt (s.le_max' x.1 x.2) (Nat.lt_succ_self _)⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      exact Fin.ext_iff.mp hab
    -- Proof comment: every requested finite family of increments is a restriction of the
    -- anchored finite-grid tail family.
    simpa [times, g, Finset.restrict, pathIncrementTuple] using htail.precomp (g := g) hg
  · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    -- Proof comment: the empty family is independent for trivial reasons.
    simpa using
      (iIndepFun.of_subsingleton
        (μ := P)
        (f := (∅ : Finset ℕ).restrict
          (fun i ω ↦ Function.eval (t (i + 1)) ω - Function.eval (t i) ω)))


/-- Helper for Example 14.45: start-at-zero, stationary independent increments, and the Gaussian
interval laws determine the Gaussian Markov finite-dimensional marginals. -/
private theorem finiteDimensionalProjection_eq_gaussianMarkov_of_targetAssumptions
    {Q : Measure (NNReal → ℝ)} [IsProbabilityMeasure Q] {n : ℕ}
    (times : Fin (n + 1) → NNReal) (hzero : times 0 = 0) (htimes : StrictMono times)
    (hQstart : HasLaw (Function.eval 0) (Measure.dirac 0) Q)
    (hQstatIndep : HasStationaryIndependentIncrements Function.eval Q)
    (hQgauss :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s)) Q) :
    Q.map (finiteDimensionalProjection times) =
      markovSemigroupFiniteDimKernel
        (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
        times htimes ∘ₘ Measure.dirac 0 := by
  have hQincrement :
      Q.map (pathIncrementTuple times) =
        Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc)) := by
    -- Proof comment: the increment tuple is independent, and each coordinate has the prescribed
    -- Gaussian gap law.
    refine incrementTuple_map_eq_gaussianPi_of_targetAssumptions
      times htimes.monotone hQstatIndep.1 ?_
    intro i
    exact hQgauss (le_of_lt (htimes i.castSucc_lt_succ))
  -- Proof comment: reconstruct the coordinate tuple from its increments, then replace the
  -- resulting product increment law by the Gaussian Markov finite-dimensional law.
  calc
    Q.map (finiteDimensionalProjection times) =
        (Q.map (pathIncrementTuple times)).map (prependZeroPartialSums (n := n)) := by
          exact
            finiteDimensionalProjection_map_eq_prependZeroPartialSums_of_start_zero
              times hzero hQstart
    _ =
        (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (times i.succ - times i.castSucc))).map
          (prependZeroPartialSums (n := n)) := by
            rw [hQincrement]
    _ =
        markovSemigroupFiniteDimKernel
          (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
          times htimes ∘ₘ Measure.dirac 0 := by
            exact
              (gaussianMarkovFiniteDimLaw_eq_prependZeroPartialSumsPushforward
                times hzero htimes).symm

/-- Helper for Example 14.45: package the centered Gaussian law `gaussianReal 0 t` as a
probability measure. -/
private noncomputable def centeredGaussianLaw (t : NNReal) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 t, inferInstance⟩

/-- Helper for Example 14.45: the centered Gaussian family is a convolution semigroup with
zero-time Dirac mass. -/
private theorem centeredGaussianLaw_isConvolutionSemigroupWithZero :
    IsConvolutionSemigroupWithZero centeredGaussianLaw := by
  refine
    { toIsConvolutionSemigroup := ?_
      zero_eq := ?_ }
  · refine
      { convolution_eq := ?_ }
    intro s t
    apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
    intro A hA
    change (gaussianReal 0 (s + t)) A = ((gaussianReal 0 s ∗ gaussianReal 0 t) A)
    rw [gaussianReal_conv_gaussianReal, zero_add]
  · apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
    intro A hA
    change (gaussianReal 0 0) A = Measure.dirac (0 : ℝ) A
    rw [gaussianReal_zero_var]

/-- Helper for Example 14.45: the canonical equivalence between `Fin 1 → ℝ` and `ℝ`. -/
private noncomputable abbrev fin1RealEquiv : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ

/-- Helper for Example 14.45: the same `Fin 1 → ℝ ≃ ℝ` identification viewed as a measurable
equivalence. -/
private noncomputable abbrev fin1RealMeasEquiv : (Fin 1 → ℝ) ≃ᵐ ℝ :=
  fin1RealEquiv.toHomeomorph.toMeasurableEquiv

/-- Helper for Example 14.45: `fin1RealEquiv` reads off the unique coordinate. -/
@[simp] private theorem fin1RealEquiv_apply (x : Fin 1 → ℝ) :
    fin1RealEquiv x = x 0 := by
  -- Proof comment: `ContinuousLinearEquiv.funUnique` is evaluation at the unique index.
  simp [fin1RealEquiv]

/-- Helper for Example 14.45: transport the centered Gaussian family to the `Fin 1 → ℝ` model. -/
private noncomputable abbrev transportedFin1Law :
    NNReal → ProbabilityMeasure (Fin 1 → ℝ) :=
  fun t ↦ ProbabilityMeasure.map (centeredGaussianLaw t)
    fin1RealMeasEquiv.symm.measurable.aemeasurable

/-- Helper for Example 14.45: transporting a real law to `Fin 1 → ℝ` and back recovers the
original law. -/
@[simp] private theorem mapBackTransportedFin1Law (μ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure.map
      (ProbabilityMeasure.map μ fin1RealMeasEquiv.symm.measurable.aemeasurable)
      fin1RealMeasEquiv.measurable.aemeasurable = μ := by
  -- Proof comment: the measurable equivalence cancels after the two successive pushforwards.
  apply Subtype.ext
  simpa [ProbabilityMeasure.map] using
    (MeasurableEquiv.map_map_symm (ν := (μ : Measure ℝ)) fin1RealMeasEquiv)

/-- Helper for Example 14.45: mapping the Dirac mass at the zero vector of `Fin 1 → ℝ` back to
`ℝ` still gives the Dirac mass at `0`. -/
@[simp] private theorem mapDiracProbaFin1RealZero :
    ProbabilityMeasure.map
      (diracProba (0 : Fin 1 → ℝ))
      fin1RealMeasEquiv.measurable.aemeasurable =
      diracProba (0 : ℝ) := by
  -- Proof comment: the canonical equivalence sends the zero vector of `ℝ¹` to the real number
  -- `0`.
  apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro s hs
  rw [ProbabilityMeasure.toMeasure_map, MeasurableEquiv.map_apply]
  by_cases h : (0 : ℝ) ∈ s
  · simp [h, fin1RealMeasEquiv, fin1RealEquiv]
  · simp [h, fin1RealMeasEquiv, fin1RealEquiv]

/-- Helper for Example 14.45: transporting the centered Gaussian family to `Fin 1 → ℝ` preserves
the convolution-semigroup structure. -/
private theorem transportedFin1Law_isConvolutionSemigroupWithZero :
    IsConvolutionSemigroupWithZero transportedFin1Law := by
  letI : IsConvolutionSemigroupWithZero centeredGaussianLaw :=
    centeredGaussianLaw_isConvolutionSemigroupWithZero
  refine
    { toIsConvolutionSemigroup := ?_
      zero_eq := ?_ }
  · refine
      { convolution_eq := fun s t ↦ ?_ }
    apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
    intro A hA
    have hConvMap :
        Measure.map fin1RealEquiv.symm
            ((centeredGaussianLaw s : Measure ℝ) ∗ (centeredGaussianLaw t : Measure ℝ)) =
          Measure.map fin1RealEquiv.symm (centeredGaussianLaw s : Measure ℝ) ∗
            Measure.map fin1RealEquiv.symm (centeredGaussianLaw t : Measure ℝ) := by
      simpa using
        (Measure.map_conv_continuousLinearMap
          (μ := (centeredGaussianLaw s : Measure ℝ))
          (ν := (centeredGaussianLaw t : Measure ℝ))
          (fin1RealEquiv.symm : ℝ →L[ℝ] (Fin 1 → ℝ)))
    have hMap :
        ((centeredGaussianLaw (s + t) : Measure ℝ).map fin1RealEquiv.symm) A =
          ((((centeredGaussianLaw s : Measure ℝ).map fin1RealEquiv.symm) ∗
              ((centeredGaussianLaw t : Measure ℝ).map fin1RealEquiv.symm)) A) := by
      calc
        ((centeredGaussianLaw (s + t) : Measure ℝ).map fin1RealEquiv.symm) A =
            (Measure.map fin1RealEquiv.symm
              ((centeredGaussianLaw s : Measure ℝ) ∗
                (centeredGaussianLaw t : Measure ℝ))) A := by
                  rw [IsConvolutionSemigroup.convolution_eq_toMeasure
                    (ν := centeredGaussianLaw) s t]
        _ =
            ((((centeredGaussianLaw s : Measure ℝ).map fin1RealEquiv.symm) ∗
                ((centeredGaussianLaw t : Measure ℝ).map fin1RealEquiv.symm)) A) := by
              exact congrArg (fun ρ : Measure (Fin 1 → ℝ) ↦ ρ A) hConvMap
    simpa [transportedFin1Law, ProbabilityMeasure.map] using hMap
  · apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
    intro A hA
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.one_eq_diracProba]
    rw [MeasurableEquiv.map_apply]
    have hzero : fin1RealMeasEquiv.symm (0 : ℝ) = 0 := by
      simp [fin1RealMeasEquiv]
    rw [IsConvolutionSemigroupWithZero.zero_eq_diracProba (ν := centeredGaussianLaw)]
    by_cases h : (0 : Fin 1 → ℝ) ∈ A
    · simp [h, hzero]
    · simp [h, hzero]

/-- Helper for Example 14.45: identify `Fin 1 → ℝ`-valued paths with real-valued paths
pointwise via the unique coordinate. -/
private noncomputable abbrev realPathMeasEquiv :
    (NNReal → Fin 1 → ℝ) ≃ᵐ (NNReal → ℝ) :=
  MeasurableEquiv.piCongrRight fun _ ↦ fin1RealMeasEquiv

/-- Helper for Example 14.45: the path-space transport acts pointwise on every time coordinate. -/
@[simp] private theorem realPathMeasEquiv_apply
    (ω : NNReal → Fin 1 → ℝ) (t : NNReal) :
    realPathMeasEquiv ω t = ω t 0 := by
  -- Proof comment: `MeasurableEquiv.piCongrRight` acts coordinatewise at each time.
  change fin1RealMeasEquiv (ω t) = ω t 0
  simp [fin1RealMeasEquiv]

/-- Helper for Example 14.45: read the scalar coordinate of a `Fin 1 → ℝ`-valued path. -/
private noncomputable def realCoordinateProcess :
    NNReal → (NNReal → Fin 1 → ℝ) → ℝ :=
  fun t ω ↦ fin1RealEquiv (ω t)

/-- Helper for Example 14.45: the scalar coordinate process is measurable at every time. -/
private theorem realCoordinateProcess_measurable (t : NNReal) :
    Measurable (realCoordinateProcess t) := by
  -- Proof comment: evaluate the path at time `t`, then apply the measurable equivalence
  -- `Fin 1 → ℝ ≃ ℝ`.
  exact fin1RealEquiv.continuous.measurable.comp (measurable_pi_apply t)

/-- Helper for Example 14.45: applying the scalar coordinate to a vector increment gives the
corresponding real increment. -/
@[simp] private theorem realCoordinateProcess_sub_eq
    (s t : NNReal) (ω : NNReal → Fin 1 → ℝ) :
    fin1RealEquiv (ω t - ω s) =
      realCoordinateProcess t ω - realCoordinateProcess s ω := by
  -- Proof comment: the coordinate identification is linear, so it commutes with subtraction.
  simpa [realCoordinateProcess] using fin1RealEquiv.toLinearMap.map_sub (ω t) (ω s)

/-- Helper for Example 14.45: transporting a vector-valued path law to real-valued paths and
then taking a finite increment tuple agrees with taking the scalar-coordinate increment tuple on
the original vector-valued path space. -/
private theorem realPathMap_incrementTuple
    (Pvec : ProbabilityMeasure (NNReal → Fin 1 → ℝ))
    {n : ℕ} (times : Fin (n + 1) → NNReal) :
    (ProbabilityMeasure.map Pvec realPathMeasEquiv.measurable.aemeasurable :
        Measure (NNReal → ℝ)).map
      (fun ω : NNReal → ℝ ↦ fun i : Fin n ↦ ω (times i.succ) - ω (times i.castSucc)) =
      (Pvec : Measure (NNReal → Fin 1 → ℝ)).map
        (fun ω : NNReal → Fin 1 → ℝ ↦
          fun i : Fin n ↦
            realCoordinateProcess (times i.succ) ω - realCoordinateProcess (times i.castSucc) ω) :=
    by
  let f : (NNReal → ℝ) → Fin n → ℝ :=
    fun ω i ↦ ω (times i.succ) - ω (times i.castSucc)
  let g : (NNReal → Fin 1 → ℝ) → Fin n → ℝ :=
    fun ω i ↦ realCoordinateProcess (times i.succ) ω - realCoordinateProcess (times i.castSucc) ω
  have hf : Measurable f := by
    -- Proof comment: each coordinate is a measurable difference of two path evaluations.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact (measurable_pi_apply _).sub (measurable_pi_apply _)
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_map hf realPathMeasEquiv.measurable]
  exact Measure.map_congr <| Filter.EventuallyEq.of_eq <| by
    funext ω
    ext i
    simp [f, g, realCoordinateProcess]

/-- Helper for Example 14.45: transporting a vector-valued path law to real-valued paths and
then taking one increment agrees with taking the scalar-coordinate increment on the original
vector-valued path space. -/
private theorem realPathMap_increment
    (Pvec : ProbabilityMeasure (NNReal → Fin 1 → ℝ))
    (s t : NNReal) :
    (ProbabilityMeasure.map Pvec realPathMeasEquiv.measurable.aemeasurable :
        Measure (NNReal → ℝ)).map
      (fun ω : NNReal → ℝ ↦ ω t - ω s) =
      (Pvec : Measure (NNReal → Fin 1 → ℝ)).map
        (fun ω : NNReal → Fin 1 → ℝ ↦
          realCoordinateProcess t ω - realCoordinateProcess s ω) := by
  let f : (NNReal → ℝ) → ℝ := fun ω ↦ ω t - ω s
  let g : (NNReal → Fin 1 → ℝ) → ℝ :=
    fun ω ↦ realCoordinateProcess t ω - realCoordinateProcess s ω
  have hf : Measurable f := by
    -- Proof comment: the one-step increment is a measurable difference of evaluations.
    exact (measurable_pi_apply _).sub (measurable_pi_apply _)
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_map hf realPathMeasEquiv.measurable]
  exact Measure.map_congr <| Filter.EventuallyEq.of_eq <| by
    funext ω
    simp [f, g, realCoordinateProcess]

/-- Helper for Example 14.45: transporting the `Fin 1 → ℝ` path-space realization to real-valued
paths preserves stationary independent increments and the interval increment laws. -/
private theorem realPathTransport_of_fin1PathLaw
    {Pvec : ProbabilityMeasure (NNReal → Fin 1 → ℝ)}
    (hVecStatIndep :
      HasStationaryIndependentIncrements Function.eval
        (Pvec : Measure (NNReal → Fin 1 → ℝ)))
    (hIncVec : ∀ ⦃s t : NNReal⦄, s ≤ t →
      HasLaw (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s)
        (transportedFin1Law (t - s) : Measure (Fin 1 → ℝ))
        (Pvec : Measure (NNReal → Fin 1 → ℝ))) :
    let P : ProbabilityMeasure (NNReal → ℝ) :=
      ProbabilityMeasure.map Pvec realPathMeasEquiv.measurable.aemeasurable
    HasStationaryIndependentIncrements Function.eval (P : Measure (NNReal → ℝ)) ∧
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s)
          (centeredGaussianLaw (t - s) : Measure ℝ)
          (P : Measure (NNReal → ℝ)) := by
  let P : ProbabilityMeasure (NNReal → ℝ) :=
    ProbabilityMeasure.map Pvec realPathMeasEquiv.measurable.aemeasurable
  have hVecIndep :
      HasIndepIncrements Function.eval (Pvec : Measure (NNReal → Fin 1 → ℝ)) :=
    hVecStatIndep.1
  have hVecStat :
      HasStationaryIncrementLaws Function.eval (Pvec : Measure (NNReal → Fin 1 → ℝ)) :=
    hVecStatIndep.2
  have hRealIndep :
      HasIndepIncrements realCoordinateProcess
        (Pvec : Measure (NNReal → Fin 1 → ℝ)) := by
    -- Proof comment: map the vector increments through the unique scalar coordinate.
    simpa [realCoordinateProcess] using hVecIndep.map fin1RealEquiv.toContinuousLinearMap
  have hPathIndep :
      HasIndepIncrements Function.eval (P : Measure (NNReal → ℝ)) := by
    intro n times htimes
    let f : Fin n → (NNReal → ℝ) → ℝ :=
      fun i ω ↦ ω (times i.succ) - ω (times i.castSucc)
    let g : Fin n → (NNReal → Fin 1 → ℝ) → ℝ :=
      fun i ω ↦ realCoordinateProcess (times i.succ) ω - realCoordinateProcess (times i.castSucc) ω
    have hg :
        iIndepFun g (Pvec : Measure (NNReal → Fin 1 → ℝ)) := by
      -- Proof comment: the scalar-coordinate images of the vector increments remain independent.
      simpa [g] using hRealIndep n times htimes
    have hmap :
        (P : Measure (NNReal → ℝ)).map (fun ω ↦ fun i ↦ f i ω) =
          (Pvec : Measure (NNReal → Fin 1 → ℝ)).map (fun ω ↦ fun i ↦ g i ω) := by
      simpa [P, f, g] using realPathMap_incrementTuple Pvec times
    have hmarg :
        ∀ i, (P : Measure (NNReal → ℝ)).map (f i) =
          (Pvec : Measure (NNReal → Fin 1 → ℝ)).map (g i) := by
      intro i
      simpa [P, f, g] using
        realPathMap_increment Pvec (times i.castSucc) (times i.succ)
    refine
      (iIndepFun_iff_map_fun_eq_pi_map fun i : Fin n ↦
        ((measurable_pi_apply (times i.succ)).sub
          (measurable_pi_apply (times i.castSucc))).aemeasurable).2 ?_
    calc
      (P : Measure (NNReal → ℝ)).map (fun ω ↦ fun i ↦ f i ω) =
          (Pvec : Measure (NNReal → Fin 1 → ℝ)).map (fun ω ↦ fun i ↦ g i ω) := hmap
      _ = Measure.pi (fun i ↦ (Pvec : Measure (NNReal → Fin 1 → ℝ)).map (g i)) := by
            exact
              (iIndepFun_iff_map_fun_eq_pi_map fun i : Fin n ↦
                ((realCoordinateProcess_measurable (times i.succ)).sub
                  (realCoordinateProcess_measurable (times i.castSucc))).aemeasurable).1 hg
      _ = Measure.pi (fun i ↦ (P : Measure (NNReal → ℝ)).map (f i)) := by
            congr 1
            funext i
            exact (hmarg i).symm
  have hRealStat :
      HasStationaryIncrementLaws realCoordinateProcess
        (Pvec : Measure (NNReal → Fin 1 → ℝ)) := by
    intro r s t
    let leftVec : (NNReal → Fin 1 → ℝ) → ℝ :=
      fun ω ↦ fin1RealEquiv (ω ((s + t) + r) - ω (t + r))
    let rightVec : (NNReal → Fin 1 → ℝ) → ℝ :=
      fun ω ↦ fin1RealEquiv (ω (s + r) - ω r)
    have hComp :
        IdentDistrib leftVec rightVec
          (Pvec : Measure (NNReal → Fin 1 → ℝ))
          (Pvec : Measure (NNReal → Fin 1 → ℝ)) := by
      simpa [leftVec, rightVec, Function.comp] using
        (hVecStat r s t).comp fin1RealEquiv.continuous.measurable
    have hLeft :
        (fun ω : NNReal → Fin 1 → ℝ ↦
          realCoordinateProcess ((s + t) + r) ω - realCoordinateProcess (t + r) ω)
          =ᵐ[(Pvec : Measure (NNReal → Fin 1 → ℝ))]
        leftVec := by
      exact Filter.EventuallyEq.of_eq <| by
        funext ω
        simpa [leftVec] using
          (realCoordinateProcess_sub_eq (s := t + r) (t := (s + t) + r) ω).symm
    have hRight :
        (fun ω : NNReal → Fin 1 → ℝ ↦
          realCoordinateProcess (s + r) ω - realCoordinateProcess r ω)
          =ᵐ[(Pvec : Measure (NNReal → Fin 1 → ℝ))]
        rightVec := by
      exact Filter.EventuallyEq.of_eq <| by
        funext ω
        simpa [rightVec] using
          (realCoordinateProcess_sub_eq (s := r) (t := s + r) ω).symm
    exact
      (IdentDistrib.of_ae_eq
        (((realCoordinateProcess_measurable ((s + t) + r)).sub
          (realCoordinateProcess_measurable (t + r))).aemeasurable)
        hLeft).trans <|
        hComp.trans <|
          (IdentDistrib.of_ae_eq
            (((realCoordinateProcess_measurable (s + r)).sub
              (realCoordinateProcess_measurable r)).aemeasurable)
            hRight).symm
  have hPathStat :
      HasStationaryIncrementLaws Function.eval (P : Measure (NNReal → ℝ)) := by
    intro r s t
    have hVec :
        IdentDistrib
          (fun ω : NNReal → Fin 1 → ℝ ↦
            realCoordinateProcess ((s + t) + r) ω - realCoordinateProcess (t + r) ω)
          (fun ω : NNReal → Fin 1 → ℝ ↦
            realCoordinateProcess (s + r) ω - realCoordinateProcess r ω)
          (Pvec : Measure (NNReal → Fin 1 → ℝ))
          (Pvec : Measure (NNReal → Fin 1 → ℝ)) :=
      hRealStat r s t
    refine
      { aemeasurable_fst :=
          ((measurable_pi_apply ((s + t) + r)).sub
            (measurable_pi_apply (t + r))).aemeasurable
        aemeasurable_snd :=
          ((measurable_pi_apply (s + r)).sub
            (measurable_pi_apply r)).aemeasurable
        map_eq := ?_ }
    calc
      Measure.map (fun ω : NNReal → ℝ ↦ ω ((s + t) + r) - ω (t + r))
          (P : Measure (NNReal → ℝ)) =
            Measure.map
              (fun ω : NNReal → Fin 1 → ℝ ↦
                realCoordinateProcess ((s + t) + r) ω - realCoordinateProcess (t + r) ω)
              (Pvec : Measure (NNReal → Fin 1 → ℝ)) := by
                simpa [P] using realPathMap_increment Pvec (t + r) ((s + t) + r)
      _ =
          Measure.map
            (fun ω : NNReal → Fin 1 → ℝ ↦
              realCoordinateProcess (s + r) ω - realCoordinateProcess r ω)
            (Pvec : Measure (NNReal → Fin 1 → ℝ)) := hVec.map_eq
      _ = Measure.map (fun ω : NNReal → ℝ ↦ ω (s + r) - ω r) (P : Measure (NNReal → ℝ)) := by
            simpa [P] using (realPathMap_increment Pvec r (s + r)).symm
  have hIncReal :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s)
          (centeredGaussianLaw (t - s) : Measure ℝ)
          (P : Measure (NNReal → ℝ)) := by
    intro s t hst
    have hCoordLaw :
        HasLaw fin1RealMeasEquiv (centeredGaussianLaw (t - s) : Measure ℝ)
          (transportedFin1Law (t - s) : Measure (Fin 1 → ℝ)) := by
      -- Proof comment: the inverse transport in `transportedFin1Law` is canceled by mapping back
      -- through `fin1RealMeasEquiv`.
      refine ⟨fin1RealMeasEquiv.measurable.aemeasurable, ?_⟩
      simpa [transportedFin1Law, ProbabilityMeasure.map] using
        congrArg (fun ρ : ProbabilityMeasure ℝ ↦ (ρ : Measure ℝ))
          (mapBackTransportedFin1Law (μ := centeredGaussianLaw (t - s)))
    have hVecLaw :
        HasLaw
          (fun ω : NNReal → Fin 1 → ℝ ↦
            realCoordinateProcess t ω - realCoordinateProcess s ω)
          (centeredGaussianLaw (t - s) : Measure ℝ)
          (Pvec : Measure (NNReal → Fin 1 → ℝ)) := by
      have hCompLaw :
          HasLaw
            (fun ω : NNReal → Fin 1 → ℝ ↦ fin1RealMeasEquiv (ω t - ω s))
            (centeredGaussianLaw (t - s) : Measure ℝ)
            (Pvec : Measure (NNReal → Fin 1 → ℝ)) := by
        simpa [Function.comp] using HasLaw.comp hCoordLaw (hIncVec hst)
      have hEq :
          (fun ω : NNReal → Fin 1 → ℝ ↦
            realCoordinateProcess t ω - realCoordinateProcess s ω)
            =ᵐ[(Pvec : Measure (NNReal → Fin 1 → ℝ))]
          (fun ω : NNReal → Fin 1 → ℝ ↦ fin1RealMeasEquiv (ω t - ω s)) := by
        exact Filter.EventuallyEq.of_eq <| by
          funext ω
          simpa [fin1RealMeasEquiv] using (realCoordinateProcess_sub_eq s t ω).symm
      exact hCompLaw.congr hEq
    refine
      { aemeasurable :=
          ((measurable_pi_apply t).sub
            (measurable_pi_apply s)).aemeasurable
        map_eq := ?_ }
    calc
      Measure.map (fun ω : NNReal → ℝ ↦ ω t - ω s) (P : Measure (NNReal → ℝ)) =
          Measure.map
            (fun ω : NNReal → Fin 1 → ℝ ↦
              realCoordinateProcess t ω - realCoordinateProcess s ω)
            (Pvec : Measure (NNReal → Fin 1 → ℝ)) := by
              simpa [P] using realPathMap_increment Pvec s t
      _ = (centeredGaussianLaw (t - s) : Measure ℝ) := hVecLaw.map_eq
  exact ⟨⟨hPathIndep, hPathStat⟩, hIncReal⟩

/-- Helper for Example 14.45: transporting the time-zero law from `NNReal → Fin 1 → ℝ` to
`NNReal → ℝ` preserves the Dirac law at `0`. -/
private theorem realPathMeasure_start_hasLaw
    {Pvec : ProbabilityMeasure (NNReal → Fin 1 → ℝ)}
    (hVecStart : HasLaw (Function.eval 0) (Measure.dirac (0 : Fin 1 → ℝ))
      (Pvec : Measure (NNReal → Fin 1 → ℝ))) :
    HasLaw (Function.eval 0) (Measure.dirac (0 : ℝ))
      (ProbabilityMeasure.map Pvec realPathMeasEquiv.measurable.aemeasurable :
        Measure (NNReal → ℝ)) := by
  have hCoordLaw :
      HasLaw fin1RealMeasEquiv (Measure.dirac (0 : ℝ))
        (Measure.dirac (0 : Fin 1 → ℝ)) := by
    refine ⟨fin1RealMeasEquiv.measurable.aemeasurable, ?_⟩
    simpa using congrArg (fun ρ : ProbabilityMeasure ℝ ↦ (ρ : Measure ℝ))
      mapDiracProbaFin1RealZero
  have hCompLaw :
      HasLaw
        (fun ω : NNReal → Fin 1 → ℝ ↦ fin1RealMeasEquiv (ω 0))
        (Measure.dirac (0 : ℝ))
        (Pvec : Measure (NNReal → Fin 1 → ℝ)) := by
    simpa [Function.comp] using HasLaw.comp hCoordLaw hVecStart
  refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
  calc
    (ProbabilityMeasure.map Pvec realPathMeasEquiv.measurable.aemeasurable :
        Measure (NNReal → ℝ)).map (Function.eval 0) =
        (Pvec : Measure (NNReal → Fin 1 → ℝ)).map
          (fun ω : NNReal → Fin 1 → ℝ ↦ fin1RealMeasEquiv (ω 0)) := by
            rw [ProbabilityMeasure.toMeasure_map, Measure.map_map
              (measurable_pi_apply 0) realPathMeasEquiv.measurable]
            exact Measure.map_congr <| Filter.EventuallyEq.of_eq <| by
              funext ω
              simp [realPathMeasEquiv]
    _ = Measure.dirac (0 : ℝ) := hCompLaw.map_eq

/-- Helper for Example 14.45: restricting a path to finitely many coordinates is measurable. -/
private theorem measurable_finsetRestrictPath (I : Finset NNReal) :
    Measurable (fun ω : NNReal → ℝ ↦ I.restrict ω) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply (i : NNReal)

/-- Helper for Example 14.45: `Finset.Iic n` is canonically order-isomorphic to `Fin (n + 1)`. -/
private def iicOrderIsoFinLocal (n : ℕ) : Finset.Iic n ≃o Fin (n + 1) where
  toFun := iicEquivFinLocal n
  invFun := (iicEquivFinLocal n).symm
  left_inv := (iicEquivFinLocal n).left_inv
  right_inv := (iicEquivFinLocal n).right_inv
  map_rel_iff' := by
    intro i j
    rfl

/-- Helper for Example 14.45: a finite set containing `0` is nonempty. -/
private theorem finiteSetNonemptyOfZeroMem (J : Finset NNReal) (hJ0 : 0 ∈ J) :
    J.Nonempty :=
  ⟨0, hJ0⟩

/-- Helper for Example 14.45: a finite subset of `NNReal` containing `0` admits an increasing
enumeration indexed by `Finset.Iic (J.card - 1)`. -/
private noncomputable def orderedFiniteSetOrderIso (J : Finset NNReal) (hJ0 : 0 ∈ J) :
    Finset.Iic (J.card - 1) ≃o J :=
  ((iicOrderIsoFinLocal (J.card - 1)).trans
      (Fin.castOrderIso
        (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (finiteSetNonemptyOfZeroMem J hJ0))))).trans
    (J.orderIsoOfFin rfl)

/-- Helper for Example 14.45: the increasing chain enumerating a finite subset containing `0`. -/
private noncomputable def orderedFiniteSetChain (J : Finset NNReal) (hJ0 : 0 ∈ J) :
    Π _ : Finset.Iic (J.card - 1), NNReal :=
  fun i ↦ (orderedFiniteSetOrderIso J hJ0 i : NNReal)

/-- Helper for Example 14.45: the ordered finite-set chain is strict. -/
private theorem orderedFiniteSetChain_strictMono (J : Finset NNReal) (hJ0 : 0 ∈ J) :
    StrictMono (orderedFiniteSetChain J hJ0) := by
  simpa [orderedFiniteSetChain] using (orderedFiniteSetOrderIso J hJ0).strictMono

/-- Helper for Example 14.45: the first element in the increasing enumeration of a finite set
containing `0` is `0`. -/
private theorem orderedFiniteSetChain_zero (J : Finset NNReal) (hJ0 : 0 ∈ J) :
    orderedFiniteSetChain J hJ0 ⟨0, Finset.mem_Iic.2 (Nat.zero_le (J.card - 1))⟩ = 0 := by
  have hJne : J.Nonempty := finiteSetNonemptyOfZeroMem J hJ0
  have hmin : J.min' hJne = 0 := by
    rw [Finset.min'_eq_iff]
    exact ⟨hJ0, fun b hb ↦ bot_le⟩
  let i0 : Finset.Iic (J.card - 1) :=
    ⟨0, Finset.mem_Iic.2 (Nat.zero_le (J.card - 1))⟩
  have hi0_mem : orderedFiniteSetChain J hJ0 i0 ∈ J := by
    exact (orderedFiniteSetOrderIso J hJ0 i0).2
  have hi0_least : ∀ b : NNReal, b ∈ J → orderedFiniteSetChain J hJ0 i0 ≤ b := by
    intro b hb
    simpa [orderedFiniteSetChain] using
      (orderedFiniteSetOrderIso J hJ0).monotone
        (show i0 ≤ (orderedFiniteSetOrderIso J hJ0).symm ⟨b, hb⟩ from Nat.zero_le _)
  have hi0_eq_min : orderedFiniteSetChain J hJ0 i0 = J.min' hJne := by
    exact ((Finset.min'_eq_iff (s := J) (H := hJne) (a := orderedFiniteSetChain J hJ0 i0)).2
      ⟨hi0_mem, hi0_least⟩).symm
  -- Proof comment: the initial index in the monotone enumeration is the minimum of the set.
  exact hi0_eq_min.trans hmin

/-- Helper for Example 14.45: the increasing enumeration of a finite subset containing `0`,
reindexed directly by `Fin`. -/
private noncomputable def orderedFiniteSetFinOrderIso (J : Finset NNReal) (hJ0 : 0 ∈ J) :
    Fin ((J.card - 1) + 1) ≃o J :=
  (iicOrderIsoFinLocal (J.card - 1)).symm.trans (orderedFiniteSetOrderIso J hJ0)

/-- Helper for Example 14.45: the `Fin`-indexed increasing enumeration of a finite subset
containing `0`. -/
private noncomputable def orderedFiniteSetFinTimes (J : Finset NNReal) (hJ0 : 0 ∈ J) :
    Fin ((J.card - 1) + 1) → NNReal :=
  fun i ↦ (orderedFiniteSetFinOrderIso J hJ0 i : NNReal)

/-- Helper for Example 14.45: the `Fin`-indexed ordered enumeration starts at `0`. -/
private theorem orderedFiniteSetFinTimes_zero (J : Finset NNReal) (hJ0 : 0 ∈ J) :
    orderedFiniteSetFinTimes J hJ0 0 = 0 := by
  simpa [orderedFiniteSetFinTimes, orderedFiniteSetFinOrderIso, orderedFiniteSetChain] using
    orderedFiniteSetChain_zero J hJ0

/-- Helper for Example 14.45: the `Fin`-indexed ordered enumeration is strictly increasing. -/
private theorem orderedFiniteSetFinTimes_strictMono (J : Finset NNReal) (hJ0 : 0 ∈ J) :
    StrictMono (orderedFiniteSetFinTimes J hJ0) := by
  simpa [orderedFiniteSetFinTimes] using (orderedFiniteSetFinOrderIso J hJ0).strictMono

/-- Helper for Example 14.45: forget the extra `0`-coordinate after adjoining it to a finite
support set. -/
private def restrictInsertZero (I : Finset NNReal) :
    ((↑(insert (0 : NNReal) I)) → ℝ) → I → ℝ :=
  fun z i ↦ z ⟨i.1, Finset.mem_insert.mpr (Or.inr i.2)⟩

/-- Helper for Example 14.45: forgetting the adjoined `0`-coordinate is measurable. -/
private theorem measurable_restrictInsertZero (I : Finset NNReal) :
    Measurable (restrictInsertZero I) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply
    ((⟨i.1, Finset.mem_insert.mpr (Or.inr i.2)⟩ : ↑(insert (0 : NNReal) I)))

/-- Helper for Example 14.45: restricting to `I ∪ {0}` and then forgetting the adjoined
`0`-coordinate recovers the original finite restriction. -/
private theorem restrictInsertZero_comp_restrict (I : Finset NNReal) :
    restrictInsertZero I ∘ (fun ω : NNReal → ℝ ↦ (insert (0 : NNReal) I).restrict ω) =
      fun ω ↦ I.restrict ω := by
  funext ω
  ext i
  rfl

/-- Helper for Example 14.45: pushing a Brownian motion forward to its canonical path law makes
the path map measurable. -/
private theorem measurable_processPath_of_brownian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion P B) :
    Measurable (processPath B) := by
  refine measurable_pi_lambda _ fun t ↦ ?_
  exact (hB.stronglyMeasurable t).measurable

/-- Helper for Example 14.45: the canonical path law of a Brownian motion starts from `0`. -/
private theorem brownianPathLaw_start_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion (P : Measure Ω) B) :
    HasLaw (Function.eval 0) (Measure.dirac 0)
      (ProbabilityMeasure.map P (measurable_processPath_of_brownian hB).aemeasurable :
        Measure (NNReal → ℝ)) := by
  refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
  have hzero : (fun ω ↦ B 0 ω) = fun _ : Ω ↦ (0 : ℝ) := by
    funext ω
    simp [hB.zero]
  calc
    (ProbabilityMeasure.map P (measurable_processPath_of_brownian hB).aemeasurable :
        Measure (NNReal → ℝ)).map (Function.eval 0) =
        (P : Measure Ω).map (fun ω ↦ B 0 ω) := by
          rw [ProbabilityMeasure.toMeasure_map, Measure.map_map
            (measurable_pi_apply 0) (measurable_processPath_of_brownian hB)]
          rfl
    _ = Measure.dirac (0 : ℝ) := by
          rw [hzero]
          simp

/-- Helper for Example 14.45: the canonical path law of a Brownian motion preserves independent
increments. -/
private theorem brownianPathLaw_hasIndepIncrements
    {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion (P : Measure Ω) B) :
    HasIndepIncrements Function.eval
      (ProbabilityMeasure.map P (measurable_processPath_of_brownian hB).aemeasurable :
        Measure (NNReal → ℝ)) := by
  let pathLaw : ProbabilityMeasure (NNReal → ℝ) :=
    ProbabilityMeasure.map P (measurable_processPath_of_brownian hB).aemeasurable
  intro n times htimes
  let f : Fin n → (NNReal → ℝ) → ℝ :=
    fun i ω ↦ ω (times i.succ) - ω (times i.castSucc)
  let g : Fin n → Ω → ℝ :=
    fun i ω ↦ B (times i.succ) ω - B (times i.castSucc) ω
  have hg : iIndepFun g (P : Measure Ω) := hB.indepIncrements n times htimes
  have hk :
      Measurable (fun ω : NNReal → ℝ ↦ fun i ↦ f i ω) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact (measurable_pi_apply (times i.succ)).sub (measurable_pi_apply (times i.castSucc))
  have hmap :
      (pathLaw : Measure (NNReal → ℝ)).map (fun ω ↦ fun i ↦ f i ω) =
        (P : Measure Ω).map (fun ω ↦ fun i ↦ g i ω) := by
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_map hk
      (measurable_processPath_of_brownian hB)]
    rfl
  have hmarg :
      ∀ i, (pathLaw : Measure (NNReal → ℝ)).map (f i) =
        (P : Measure Ω).map (g i) := by
    intro i
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_map
      ((measurable_pi_apply (times i.succ)).sub
        (measurable_pi_apply (times i.castSucc)))
      (measurable_processPath_of_brownian hB)]
    rfl
  refine
    (iIndepFun_iff_map_fun_eq_pi_map fun i : Fin n ↦
      ((measurable_pi_apply (times i.succ)).sub
        (measurable_pi_apply (times i.castSucc))).aemeasurable).2 ?_
  calc
    (pathLaw : Measure (NNReal → ℝ)).map (fun ω ↦ fun i ↦ f i ω) =
        (P : Measure Ω).map (fun ω ↦ fun i ↦ g i ω) := hmap
    _ = Measure.pi (fun i ↦ (P : Measure Ω).map (g i)) := by
          exact
            (iIndepFun_iff_map_fun_eq_pi_map fun i : Fin n ↦
              ((hB.stronglyMeasurable (times i.succ)).measurable.sub
                (hB.stronglyMeasurable (times i.castSucc)).measurable).aemeasurable).1 hg
    _ = Measure.pi (fun i ↦ (pathLaw : Measure (NNReal → ℝ)).map (f i)) := by
          congr 1
          funext i
          exact (hmarg i).symm

/-- Helper for Example 14.45: the canonical path law of a Brownian motion preserves stationary
increment laws. -/
private theorem brownianPathLaw_hasStationaryIncrementLaws
    {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion (P : Measure Ω) B) :
    HasStationaryIncrementLaws Function.eval
      (ProbabilityMeasure.map P (measurable_processPath_of_brownian hB).aemeasurable :
        Measure (NNReal → ℝ)) := by
  let pathLaw : ProbabilityMeasure (NNReal → ℝ) :=
    ProbabilityMeasure.map P (measurable_processPath_of_brownian hB).aemeasurable
  intro r s t
  refine
    { aemeasurable_fst :=
        ((measurable_pi_apply ((s + t) + r)).sub
          (measurable_pi_apply (t + r))).aemeasurable
      aemeasurable_snd :=
        ((measurable_pi_apply (s + r)).sub
          (measurable_pi_apply r)).aemeasurable
      map_eq := ?_ }
  calc
    Measure.map (fun ω : NNReal → ℝ ↦ ω ((s + t) + r) - ω (t + r))
        (pathLaw : Measure (NNReal → ℝ)) =
          Measure.map (fun ω ↦ B ((s + t) + r) ω - B (t + r) ω) (P : Measure Ω) := by
            rw [ProbabilityMeasure.toMeasure_map, Measure.map_map
              ((measurable_pi_apply ((s + t) + r)).sub
                (measurable_pi_apply (t + r)))
              (measurable_processPath_of_brownian hB)]
            rfl
    _ = Measure.map (fun ω ↦ B (s + r) ω - B r ω) (P : Measure Ω) := by
          exact (hB.stationaryIncrements r s t).map_eq
    _ = Measure.map (fun ω : NNReal → ℝ ↦ ω (s + r) - ω r)
          (pathLaw : Measure (NNReal → ℝ)) := by
            rw [ProbabilityMeasure.toMeasure_map, Measure.map_map
              ((measurable_pi_apply (s + r)).sub
                (measurable_pi_apply r))
              (measurable_processPath_of_brownian hB)]
            rfl

/-- Helper for Example 14.45: every Brownian path increment has the prescribed centered Gaussian
law after pushing forward to the canonical path space. -/
private theorem brownianPathLaw_increment_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion (P : Measure Ω) B) {s t : NNReal} (hst : s ≤ t) :
    HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s))
      (ProbabilityMeasure.map P (measurable_processPath_of_brownian hB).aemeasurable :
        Measure (NNReal → ℝ)) := by
  refine
    { aemeasurable :=
        ((measurable_pi_apply t).sub (measurable_pi_apply s)).aemeasurable
      map_eq := ?_ }
  calc
    Measure.map (fun ω : NNReal → ℝ ↦ ω t - ω s)
        (ProbabilityMeasure.map P (measurable_processPath_of_brownian hB).aemeasurable :
          Measure (NNReal → ℝ)) =
          Measure.map (fun ω ↦ B t ω - B s ω) (P : Measure Ω) := by
            rw [ProbabilityMeasure.toMeasure_map, Measure.map_map
              ((measurable_pi_apply t).sub
                (measurable_pi_apply s))
              (measurable_processPath_of_brownian hB)]
            rfl
    _ = gaussianReal 0 (t - s) := by
          exact ProbabilityTheory.brownianIncrement_hasLaw hB hst |>.map_eq

/-- Helper for Example 14.45: the canonical path law of a Brownian motion satisfies the target
start-at-zero, stationary independent increments, and Gaussian increment laws. -/
private theorem brownianPathLawHasTargetAssumptions
    {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion (P : Measure Ω) B) :
    let pathLaw : Measure (NNReal → ℝ) :=
      (ProbabilityMeasure.map P (measurable_processPath_of_brownian hB).aemeasurable :
        Measure (NNReal → ℝ))
    HasLaw (Function.eval 0) (Measure.dirac 0) pathLaw ∧
      HasStationaryIndependentIncrements Function.eval pathLaw ∧
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s)) pathLaw := by
  -- Proof comment: package the three previously established Brownian path-law interfaces into the
  -- exact target-assumption shape consumed by uniqueness.
  refine ⟨brownianPathLaw_start_hasLaw hB, ?_, ?_⟩
  · exact
      ⟨brownianPathLaw_hasIndepIncrements hB,
        brownianPathLaw_hasStationaryIncrementLaws hB⟩
  · intro s t hst
    exact brownianPathLaw_increment_hasLaw hB hst

/-- Helper for Example 14.45: any Brownian motion yields one canonical-path witness satisfying the
target assumptions. -/
private theorem exists_pathMeasure_of_brownian
    {Ω : Type*} [MeasurableSpace Ω]
    (PΩ : ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : IsBrownianMotion (PΩ : Measure Ω) B) :
    ∃ μ : Measure (NNReal → ℝ),
      IsProbabilityMeasure μ ∧
        HasLaw (Function.eval 0) (Measure.dirac 0) μ ∧
        HasStationaryIndependentIncrements Function.eval μ ∧
        ∀ ⦃s t : NNReal⦄, s ≤ t →
          HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s)) μ := by
  let P : Measure (NNReal → ℝ) :=
    (ProbabilityMeasure.map PΩ (measurable_processPath_of_brownian hB).aemeasurable :
      Measure (NNReal → ℝ))
  have hPspec :
      HasLaw (Function.eval 0) (Measure.dirac 0) P ∧
        HasStationaryIndependentIncrements Function.eval P ∧
        ∀ ⦃s t : NNReal⦄, s ≤ t →
          HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s)) P := by
    -- Proof comment: specialize the packaged Brownian path-law interface to the chosen
    -- pushforward measure.
    simpa [P] using brownianPathLawHasTargetAssumptions hB
  rcases hPspec with ⟨hPstart, hPstatIndep, hPgauss⟩
  refine ⟨P, ?_, hPstart, hPstatIndep, ?_⟩
  · infer_instance
  · intro s t hst
    exact hPgauss hst

/-- Helper for Example 14.45: the target assumptions determine every finite restriction law on the
canonical path space. -/
private theorem map_restrict_eq_of_targetAssumptions
    {P Q : Measure (NNReal → ℝ)} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPstart : HasLaw (Function.eval 0) (Measure.dirac 0) P)
    (hPstatIndep : HasStationaryIndependentIncrements Function.eval P)
    (hPgauss :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s)) P)
    (hQstart : HasLaw (Function.eval 0) (Measure.dirac 0) Q)
    (hQstatIndep : HasStationaryIndependentIncrements Function.eval Q)
    (hQgauss :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s)) Q)
    (I : Finset NNReal) :
    P.map (fun ω ↦ I.restrict ω) = Q.map (fun ω ↦ I.restrict ω) := by
  let J : Finset NNReal := insert 0 I
  have hJ0 : 0 ∈ J := by
    simp [J]
  let times : Fin ((J.card - 1) + 1) → NNReal := orderedFiniteSetFinTimes J hJ0
  have hzero : times 0 = 0 := orderedFiniteSetFinTimes_zero J hJ0
  have htimes : StrictMono times := orderedFiniteSetFinTimes_strictMono J hJ0
  have hPfdim :
      P.map (finiteDimensionalProjection times) =
        markovSemigroupFiniteDimKernel
          (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
          times htimes ∘ₘ Measure.dirac 0 :=
    finiteDimensionalProjection_eq_gaussianMarkov_of_targetAssumptions
      times hzero htimes hPstart hPstatIndep hPgauss
  have hQfdim :
      Q.map (finiteDimensionalProjection times) =
        markovSemigroupFiniteDimKernel
          (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
          times htimes ∘ₘ Measure.dirac 0 :=
    finiteDimensionalProjection_eq_gaussianMarkov_of_targetAssumptions
      times hzero htimes hQstart hQstatIndep hQgauss
  let eπ : (Fin ((J.card - 1) + 1) → ℝ) ≃ᵐ (J → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : J ↦ ℝ) (orderedFiniteSetFinOrderIso J hJ0).toEquiv
  have hrestrictInsert :
      P.map (fun ω : NNReal → ℝ ↦ J.restrict ω) =
        Q.map (fun ω : NNReal → ℝ ↦ J.restrict ω) := by
    have hcomp :
        eπ ∘ finiteDimensionalProjection times = fun ω : NNReal → ℝ ↦ J.restrict ω := by
      funext ω
      ext j
      simpa [eπ, times, orderedFiniteSetFinTimes, finiteDimensionalProjection] using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : J ↦ ℝ)
          (orderedFiniteSetFinOrderIso J hJ0).toEquiv
          (finiteDimensionalProjection times ω)
          ((orderedFiniteSetFinOrderIso J hJ0).symm j))
    calc
      P.map (fun ω : NNReal → ℝ ↦ J.restrict ω) =
          (P.map (finiteDimensionalProjection times)).map eπ := by
            rw [Measure.map_map eπ.measurable (measurable_finiteDimensionalProjection times)]
            simp [hcomp]
      _ = (Q.map (finiteDimensionalProjection times)).map eπ := by
            exact congrArg (fun m : Measure (Fin ((J.card - 1) + 1) → ℝ) ↦ m.map eπ)
              (hPfdim.trans hQfdim.symm)
      _ = Q.map (fun ω : NNReal → ℝ ↦ J.restrict ω) := by
            rw [Measure.map_map eπ.measurable (measurable_finiteDimensionalProjection times)]
            simp [hcomp]
  have hforget :
      restrictInsertZero I ∘ (fun ω : NNReal → ℝ ↦ J.restrict ω) =
        fun ω ↦ I.restrict ω := by
    simpa [J] using restrictInsertZero_comp_restrict I
  calc
    P.map (fun ω ↦ I.restrict ω) =
        P.map (restrictInsertZero I ∘ fun ω : NNReal → ℝ ↦ J.restrict ω) := by
          rw [hforget.symm]
    _ = (P.map (fun ω : NNReal → ℝ ↦ J.restrict ω)).map (restrictInsertZero I) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map
              (μ := P)
              (f := fun ω : NNReal → ℝ ↦ J.restrict ω)
              (g := restrictInsertZero I)
              (measurable_restrictInsertZero I)
              (measurable_finsetRestrictPath J))
    _ = (Q.map (fun ω : NNReal → ℝ ↦ J.restrict ω)).map (restrictInsertZero I) := by
          rw [hrestrictInsert]
    _ = Q.map (restrictInsertZero I ∘ fun ω : NNReal → ℝ ↦ J.restrict ω) := by
          simpa [Function.comp] using
            (Measure.map_map
              (μ := Q)
              (f := fun ω : NNReal → ℝ ↦ J.restrict ω)
              (g := restrictInsertZero I)
              (measurable_restrictInsertZero I)
              (measurable_finsetRestrictPath J))
    _ = Q.map (fun ω ↦ I.restrict ω) := by
          rw [hforget]

/-- Helper for Example 14.45: the target assumptions determine the full canonical path-space law.
-/
private theorem pathMeasure_eq_of_targetAssumptions
    {P Q : Measure (NNReal → ℝ)} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPstart : HasLaw (Function.eval 0) (Measure.dirac 0) P)
    (hPstatIndep : HasStationaryIndependentIncrements Function.eval P)
    (hPgauss :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s)) P)
    (hQstart : HasLaw (Function.eval 0) (Measure.dirac 0) Q)
    (hQstatIndep : HasStationaryIndependentIncrements Function.eval Q)
    (hQgauss :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s)) Q) :
    P = Q := by
  refine measure_ext_of_generateFrom_of_isProbabilityMeasure
    (generateFrom_measurableCylinders :
      MeasurableSpace.generateFrom (measurableCylinders (fun _ : NNReal ↦ ℝ)) =
        MeasurableSpace.pi).symm
    (isPiSystem_measurableCylinders :
      IsPiSystem (measurableCylinders (fun _ : NNReal ↦ ℝ))) ?_
  intro t ht
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
  have hmap :=
    map_restrict_eq_of_targetAssumptions
      hPstart hPstatIndep hPgauss hQstart hQstatIndep hQgauss I
  have hmap_apply_P :
      P.map (fun ω : NNReal → ℝ ↦ I.restrict ω) S =
        P ((fun ω : NNReal → ℝ ↦ I.restrict ω) ⁻¹' S) :=
    Measure.map_apply (measurable_finsetRestrictPath I) hS
  have hmap_apply_Q :
      Q.map (fun ω : NNReal → ℝ ↦ I.restrict ω) S =
        Q ((fun ω : NNReal → ℝ ↦ I.restrict ω) ⁻¹' S) :=
    Measure.map_apply (measurable_finsetRestrictPath I) hS
  rw [show cylinder I S = (fun ω : NNReal → ℝ ↦ I.restrict ω) ⁻¹' S by rfl,
    ← hmap_apply_P, hmap, hmap_apply_Q]

/-- Helper for Example 14.45: the Gaussian translated Markov semigroup already yields one
canonical path-space law with the required start law and Gaussian stationary independent
increments. -/
private theorem exists_canonicalGaussianPathMeasure :
    ∃ μ : Measure (NNReal → ℝ),
      IsProbabilityMeasure μ ∧
        HasLaw (Function.eval 0) (Measure.dirac 0) μ ∧
        HasStationaryIndependentIncrements Function.eval μ ∧
        ∀ ⦃s t : NNReal⦄, s ≤ t →
          HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s)) μ := by
  let κ : NNReal → Kernel ℝ ℝ := fun t ↦ dirac_convolution_kernel (gaussianReal 0 t)
  letI : IsMarkovSemigroup κ := gaussianIncrementKernel_isMarkovSemigroup
  obtain ⟨P, hPspec, -⟩ := existsUnique_markovPathMeasure κ (Measure.dirac (0 : ℝ))
  rcases hPspec with ⟨hPprob, hPfdimSupport⟩
  have hPfdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernel
              (fun t : NNReal ↦ dirac_convolution_kernel (gaussianReal 0 t))
              times htimes ∘ₘ Measure.dirac 0 := by
    intro n times hzero htimes
    simpa [κ, finiteDimensionalProjection, markovSemigroupFiniteDimKernel,
      supportFiniteDimensionalProjection, supportMarkovSemigroupFiniteDimKernel] using
      hPfdimSupport times hzero htimes
  refine ⟨P, hPprob, canonicalGaussianPathMeasureStart_hasLaw hPfdim, ?_, ?_⟩
  · exact
      ⟨canonicalGaussianHasIndepIncrements hPfdim,
        canonicalGaussianHasStationaryIncrementLaws hPfdim⟩
  · intro s t hst
    exact canonicalGaussianIncrement_hasLaw hPfdim hst

/-- Example 14.45: on the canonical path space `ℝ^[0,∞)`, there is a unique probability measure
under which the coordinate process starts at `0` and has independent, stationary, normally
distributed increments. -/
theorem existsUnique_pathMeasure_independent_stationary_gaussian_increments :
    ∃! μ : Measure (NNReal → ℝ),
      IsProbabilityMeasure μ ∧
        HasLaw (Function.eval 0) (Measure.dirac 0) μ ∧
        HasStationaryIndependentIncrements Function.eval μ ∧
        ∀ ⦃s t : NNReal⦄, s ≤ t →
          HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s)) μ := by
  obtain ⟨μ, hμprob, hμstart, hμstatIndep, hμgauss⟩ := exists_canonicalGaussianPathMeasure
  refine ⟨μ, ⟨hμprob, hμstart, hμstatIndep, ?_⟩, ?_⟩
  · intro s t hst
    exact hμgauss hst
  · intro ν hν
    rcases hν with ⟨hνprob, hνstart, hνstatIndep, hνgauss⟩
    letI : IsProbabilityMeasure μ := hμprob
    letI : IsProbabilityMeasure ν := hνprob
    -- Proof comment: uniqueness is exactly the previously proved cylinder-determination theorem.
    exact pathMeasure_eq_of_targetAssumptions
      hνstart hνstatIndep hνgauss hμstart hμstatIndep hμgauss

/-- The canonical path-space law with independent stationary centered Gaussian increments starting
at `0`. -/
noncomputable def gaussianIncrementPathMeasure : Measure (NNReal → ℝ) :=
  Classical.choose existsUnique_pathMeasure_independent_stationary_gaussian_increments

-- Proof sketch: apply `Classical.choose_spec` to the unique-existence theorem defining
-- `gaussianIncrementPathMeasure`.
/-- The chosen Gaussian increment path measure satisfies the defining start-at-zero and
independent-stationary-Gaussian-increment properties. -/
theorem gaussianIncrementPathMeasure_spec :
    IsProbabilityMeasure gaussianIncrementPathMeasure ∧
      HasLaw (Function.eval 0) (Measure.dirac 0) gaussianIncrementPathMeasure ∧
      HasStationaryIndependentIncrements Function.eval gaussianIncrementPathMeasure ∧
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw
          (fun ω : NNReal → ℝ ↦ ω t - ω s)
          (gaussianReal 0 (t - s))
          gaussianIncrementPathMeasure := by
  rcases Classical.choose_spec
      existsUnique_pathMeasure_independent_stationary_gaussian_increments with
    ⟨hμ, _⟩
  exact hμ

/-- The chosen Gaussian increment path measure is a probability measure. -/
instance : IsProbabilityMeasure gaussianIncrementPathMeasure := by
  rcases gaussianIncrementPathMeasure_spec with ⟨hprob, _, _, _⟩
  exact hprob

/-- The chosen Gaussian increment path measure starts from `0`. -/
theorem gaussianIncrementPathMeasure_start_hasLaw :
    HasLaw (Function.eval 0) (Measure.dirac 0) gaussianIncrementPathMeasure := by
  rcases gaussianIncrementPathMeasure_spec with ⟨_, hstart, _, _⟩
  exact hstart

/-- The chosen Gaussian increment path measure has stationary independent increments for the
canonical coordinate process. -/
theorem gaussianIncrementPathMeasure_hasStationaryIndependentIncrements :
    HasStationaryIndependentIncrements Function.eval gaussianIncrementPathMeasure := by
  rcases gaussianIncrementPathMeasure_spec with ⟨_, _, hinc, _⟩
  exact hinc

/-- Under the chosen Gaussian increment path measure, every increment over `[s,t]` has the
centered Gaussian law with variance `t - s`. -/
theorem gaussianIncrementPathMeasure_increment_hasLaw {s t : NNReal} (hst : s ≤ t) :
    HasLaw
      (fun ω : NNReal → ℝ ↦ ω t - ω s)
      (gaussianReal 0 (t - s))
      gaussianIncrementPathMeasure := by
  rcases gaussianIncrementPathMeasure_spec with ⟨_, _, _, hgauss⟩
  exact hgauss hst
