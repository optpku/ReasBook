/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.MarkovPathMeasureBridge
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

/-- Helper for Theorem 14.47: the public finite-dimensional coordinate projection on
`NNReal → Fin d → ℝ` paths. -/
private def finiteDimensionalProjection {d n : ℕ} (times : Fin (n + 1) → NNReal) :
    (NNReal → Fin d → ℝ) → Fin (n + 1) → Fin d → ℝ :=
  fun ω i ↦ ω (times i)

/-- Helper for Theorem 14.47: finite-dimensional coordinate projections are measurable. -/
private theorem measurable_finiteDimensionalProjection {d n : ℕ}
    (times : Fin (n + 1) → NNReal) :
    Measurable
      (finiteDimensionalProjection (d := d) times :
        (NNReal → Fin d → ℝ) → Fin (n + 1) → Fin d → ℝ) := by
  -- Proof comment: each component of the tuple-valued projection is evaluation at a fixed time.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply (times i)

/-- Helper for Theorem 14.47: the translated convolution kernels coming from a convolution
semigroup with zero form a Markov semigroup. -/
private theorem translatedConvolutionKernel_isMarkovSemigroup
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (hν : IsConvolutionSemigroupWithZero ν) :
    IsMarkovSemigroup
      (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ))) := by
  let κ : NNReal → Kernel (Fin d → ℝ) (Fin d → ℝ) :=
    fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ))
  refine
    { isMarkovKernel := ?_
      zero_eq := ?_
      comp_eq := ?_ }
  · intro t
    -- Proof comment: each translated convolution row is `δ_x ∗ ν_t`, hence a probability
    -- measure.
    refine ⟨?_⟩
    intro x
    simpa [κ, dirac_convolution_kernel_apply] using
      (inferInstance :
        IsProbabilityMeasure
          (Measure.dirac x ∗ (ν t : Measure (Fin d → ℝ))))
  · -- Proof comment: at time `0`, the increment law is `δ₀`, so translating by it is the
    -- identity kernel.
    ext x A hA
    simpa [Kernel.id_apply, hA, ProbabilityMeasure.one_eq_diracProba] using
      congrArg (fun μ : Measure (Fin d → ℝ) ↦ μ A) <|
        show Measure.dirac x ∗ (ν 0 : Measure (Fin d → ℝ)) = Measure.dirac x by
          rw [hν.zero_eq, ProbabilityMeasure.one_eq_diracProba]
          exact Measure.conv_dirac_zero (Measure.dirac x)
  · intro s t
    -- Proof comment: composing translated kernels convolves the increment laws, and the
    -- convolution-semigroup identity collapses the result to time `s + t`.
    ext x A hA
    rw [Kernel.comp_apply' _ _ _ hA]
    rw [show κ s x = Measure.dirac x ∗ (ν s : Measure (Fin d → ℝ)) by
      simp [κ, dirac_convolution_kernel_apply]]
    rw [show κ (s + t) x = Measure.dirac x ∗ (ν (s + t) : Measure (Fin d → ℝ)) by
      simp [κ, dirac_convolution_kernel_apply]]
    have hcomp :
        ∫⁻ y, (dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)) y) A
          ∂(Measure.dirac x ∗ (ν s : Measure (Fin d → ℝ))) =
          ((Measure.dirac x ∗ (ν s : Measure (Fin d → ℝ))) ∗
            (ν t : Measure (Fin d → ℝ))) A := by
      simpa only [Kernel.comp_apply', Kernel.const_apply, hA] using
        congrArg (fun η : Kernel (Fin d → ℝ) (Fin d → ℝ) ↦ η x A)
          (dirac_convolution_kernel_comp_const_eq_const_conv
            (μ := (Measure.dirac x ∗ (ν s : Measure (Fin d → ℝ))))
            (ν := (ν t : Measure (Fin d → ℝ))))
    calc
      ∫⁻ y, (κ t y) A ∂(Measure.dirac x ∗ (ν s : Measure (Fin d → ℝ)))
          = ((Measure.dirac x ∗ (ν s : Measure (Fin d → ℝ))) ∗ (ν t : Measure (Fin d → ℝ))) A := by
              simpa only [κ] using hcomp
      _ = (Measure.dirac x ∗ ((ν s : Measure (Fin d → ℝ)) ∗ (ν t : Measure (Fin d → ℝ)))) A := by
            simpa using congrArg (fun μ : Measure (Fin d → ℝ) ↦ μ A)
              (Measure.conv_assoc (Measure.dirac x) (ν s : Measure (Fin d → ℝ))
                (ν t : Measure (Fin d → ℝ)))
      _ = (Measure.dirac x ∗ (ν (s + t) : Measure (Fin d → ℝ))) A := by
            rw [IsConvolutionSemigroup.convolution_eq_toMeasure (ν := ν) s t]

/-- Helper for Theorem 14.47: convolution with a Dirac mass preserves total mass `1`, so
`dirac_convolution_kernel μ` is a Markov kernel whenever `μ` is a probability measure. -/
private instance instIsMarkovKernelDiracConvolutionKernelPath {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] :
    IsMarkovKernel (dirac_convolution_kernel μ) := by
  refine ⟨?_⟩
  intro x
  rw [dirac_convolution_kernel_apply]
  infer_instance

/-- Helper for Theorem 14.47: the source-facing `Iic n` index set is canonically equivalent to
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

/-- Helper for Theorem 14.47: reindex a finite `Fin` time tuple as an ordered `Iic` chain. -/
private def orderedTimeChainLocal {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Π _ : Finset.Iic n, NNReal :=
  fun i ↦ times (iicEquivFinLocal n i)

/-- Helper for Theorem 14.47: strict monotonicity of the `Fin` time tuple transfers to the
ordered `Iic` chain. -/
private theorem orderedTimeChainLocal_strictMono {n : ℕ} {times : Fin (n + 1) → NNReal}
    (htimes : StrictMono times) :
    StrictMono (orderedTimeChainLocal times) := by
  intro i j hij
  exact htimes (by simpa [orderedTimeChainLocal, iicEquivFinLocal] using hij)

/-- Helper for Theorem 14.47: the singleton initial history determined by the starting state. -/
private def initialHistory {d : ℕ} : (Fin d → ℝ) → Π _ : Finset.Iic 0, Fin d → ℝ :=
  fun x _ ↦ x

/-- Helper for Theorem 14.47: the initial-history map is measurable. -/
private theorem measurable_initialHistory {d : ℕ} :
    Measurable (initialHistory : (Fin d → ℝ) → Π _ : Finset.Iic 0, Fin d → ℝ) := by
  -- Proof comment: on the singleton index type, the initial history is coordinatewise `id`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [initialHistory] using measurable_id

/-- Helper for Theorem 14.47: the last coordinate on an `Iic n`-indexed history is measurable. -/
private theorem measurable_lastIicCoordinate {d n : ℕ} :
    Measurable (fun z : Π _ : Finset.Iic n, Fin d → ℝ ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩) := by
  exact measurable_pi_apply _

/-- Helper for Theorem 14.47: the first coordinate on an `Iic n`-indexed history is measurable. -/
private theorem measurable_zeroIicCoordinate {d n : ℕ} :
    Measurable
      (fun z : Π _ : Finset.Iic n, Fin d → ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩) := by
  exact measurable_pi_apply _

/-- Helper for Theorem 14.47: the step kernels used by the owner finite-dimensional construction
along an ordered finite time chain. -/
private noncomputable def consistentFamilyHistoryKernels
    {d : ℕ} (κ : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin d → ℝ) (Fin d → ℝ)) {n : ℕ}
    (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) :
    (m : ℕ) → Kernel (Π _ : Finset.Iic m, Fin d → ℝ) (Fin d → ℝ) :=
  fun m ↦
    if hm : m < n then
      Kernel.comap
        (κ (hj (show (⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
            ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)))
        (fun z : Π _ : Finset.Iic m, Fin d → ℝ ↦ z ⟨m, Finset.mem_Iic.2 le_rfl⟩)
        (by
          simpa using
            (measurable_pi_apply ((⟨m, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic m))))
    else
      Kernel.deterministic
        (fun z : Π _ : Finset.Iic m, Fin d → ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩)
        (by
          simpa using
            (measurable_pi_apply
              ((⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩ : Finset.Iic m))))

/-- Helper for Theorem 14.47: the history-valued trajectory kernel built from the ordered step
kernels above. -/
private noncomputable def consistentFamilyHistoryTraj {d n : ℕ}
    (κhist : (m : ℕ) → Kernel (Π _ : Finset.Iic m, Fin d → ℝ) (Fin d → ℝ)) :
    Kernel (Π _ : Finset.Iic 0, Fin d → ℝ) (Π _ : Finset.Iic n, Fin d → ℝ) :=
  ((@ProbabilityTheory.Kernel.partialTraj (fun _ : ℕ ↦ Fin d → ℝ) _ κhist 0 n) :
    Kernel (Π _ : Finset.Iic 0, Fin d → ℝ) (Π _ : Finset.Iic n, Fin d → ℝ))

/-- Helper for Theorem 14.47: the ordered-chain finite-dimensional kernel built from the local
history-step construction. -/
private noncomputable def consistentFamilyFiniteDimensionalKernel
    {d : ℕ} (κ : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin d → ℝ) (Fin d → ℝ)) {n : ℕ}
    (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) :
    Kernel (Fin d → ℝ) (Π _ : Finset.Iic n, Fin d → ℝ) :=
  consistentFamilyHistoryTraj (consistentFamilyHistoryKernels κ j hj) ∘ₖ
    Kernel.deterministic initialHistory measurable_initialHistory

/-- Helper for Theorem 14.47: the finite-dimensional law obtained by composing the local
finite-dimensional kernel with an initial measure. -/
private noncomputable def consistentFamilyFiniteDimensionalMeasure
    {d : ℕ} (μ : Measure (Fin d → ℝ))
    (κ : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin d → ℝ) (Fin d → ℝ)) {n : ℕ}
    (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) :
    Measure (Π _ : Finset.Iic n, Fin d → ℝ) :=
  consistentFamilyFiniteDimensionalKernel κ j hj ∘ₘ μ

/-- Helper for Theorem 14.47: at level `n = 0`, the finite-dimensional law is just the initial
law viewed on the singleton history space. -/
private theorem consistentFamilyFiniteDimensionalMeasure_zero
    {d : ℕ} (μ : Measure (Fin d → ℝ))
    (κ : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin d → ℝ) (Fin d → ℝ))
    (j : Π _ : Finset.Iic 0, NNReal) (hj : StrictMono j) :
    consistentFamilyFiniteDimensionalMeasure μ κ j hj =
      μ.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ Fin d → ℝ)).symm := by
  have hinitial :
      initialHistory =
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ Fin d → ℝ)).symm := by
    funext x i
    simp [initialHistory]
  -- Proof comment: `partialTraj ... 0 0` is the identity kernel, so only the initial-history
  -- pushforward remains.
  rw [consistentFamilyFiniteDimensionalMeasure, consistentFamilyFiniteDimensionalKernel,
    ← Measure.comp_assoc]
  rw [consistentFamilyHistoryTraj, ProbabilityTheory.Kernel.partialTraj_self, Measure.id_comp]
  rw [Measure.deterministic_comp_eq_map]
  rw [hinitial]

/-- Helper for Theorem 14.47: ordered finite-dimensional kernels built from Markov transition
kernels are themselves Markov. -/
private theorem consistentFamilyFiniteDimensionalKernel_isMarkov
    {d : ℕ} (κ : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin d → ℝ) (Fin d → ℝ))
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (κ hst)) {n : ℕ}
    (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) :
    IsMarkovKernel (consistentFamilyFiniteDimensionalKernel κ j hj) := by
  let κhist := consistentFamilyHistoryKernels κ j hj
  have hκhist : ∀ m, IsMarkovKernel (κhist m) := by
    intro m
    dsimp [κhist, consistentFamilyHistoryKernels]
    split_ifs with hm
    · let hstep :
          j (⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
            j ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ := by
          exact hj (show
            (⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
              ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)
      letI : IsMarkovKernel (κ hstep) := hMarkov hstep
      simpa [hstep] using
        (inferInstance :
          IsMarkovKernel
            (Kernel.comap
              (κ hstep)
              (fun z : Π _ : Finset.Iic m, Fin d → ℝ ↦ z ⟨m, Finset.mem_Iic.2 le_rfl⟩)
              (measurable_lastIicCoordinate (d := d) (n := m))))
    · simpa using
        (inferInstance :
          IsMarkovKernel
            (Kernel.deterministic
              (fun z : Π _ : Finset.Iic m, Fin d → ℝ ↦
                z ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩)
              (measurable_zeroIicCoordinate (d := d) (n := m))))
  letI : ∀ m, IsMarkovKernel (κhist m) := hκhist
  let κtraj :
      Kernel (Π _ : Finset.Iic 0, Fin d → ℝ) (Π _ : Finset.Iic n, Fin d → ℝ) :=
    ((@ProbabilityTheory.Kernel.partialTraj (fun _ : ℕ ↦ Fin d → ℝ) _ κhist 0 n) :
      Kernel (Π _ : Finset.Iic 0, Fin d → ℝ) (Π _ : Finset.Iic n, Fin d → ℝ))
  letI : IsMarkovKernel κtraj := by
    dsimp [κtraj]
    infer_instance
  -- Proof comment: `partialTraj` preserves the Markov property, and composing with the
  -- deterministic initial-history kernel keeps the full finite-dimensional law Markov.
  simpa [consistentFamilyFiniteDimensionalKernel, consistentFamilyHistoryTraj, κhist, κtraj] using
    (inferInstance :
      IsMarkovKernel
        (κtraj ∘ₖ
          Kernel.deterministic initialHistory measurable_initialHistory))

/-- Helper for Theorem 14.47: the owner finite-dimensional Markov kernel attached to the
time-difference family `κ (t - s)`, written using the local `Iic`-to-`Fin` reindexing API used
throughout this file. -/
private def markovSemigroupFiniteDimKernelLocal
    {d : ℕ} (κ : NNReal → Kernel (Fin d → ℝ) (Fin d → ℝ))
    {n : ℕ} (times : Fin (n + 1) → NNReal) (htimes : StrictMono times) :
    Kernel (Fin d → ℝ) (Fin (n + 1) → Fin d → ℝ) :=
  (consistentFamilyFiniteDimensionalKernel (fun {s t : NNReal} _ ↦ κ (t - s))
      (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes)).map
    (fun z i ↦ z ((iicEquivFinLocal n).symm i))

-- Proof sketch: apply the Kolmogorov extension theorem to the finite-dimensional distributions
-- determined by the convolution semigroup, then identify the coordinate process on the product
-- space as the resulting process with the prescribed increment laws.
/-- Helper for Theorem 14.47: the canonical path measure built from the translated kernels starts
from the deterministic point `x`. -/
private theorem canonicalPathMeasureStart_hasLaw
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ)) (x : Fin d → ℝ)
    {P : Measure (NNReal → Fin d → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
              times htimes ∘ₘ Measure.dirac x) :
    HasLaw (Function.eval 0) (Measure.dirac x) P := by
  let times : Fin 1 → NNReal := fun _ ↦ 0
  let e0 : (Fin d → ℝ) → Fin 1 → Fin d → ℝ := fun y _ ↦ y
  have htimes : StrictMono times := by
    intro i j hij
    fin_cases i
    fin_cases j
    cases hij
  have he0_measurable : Measurable e0 := by
    refine measurable_pi_lambda _ fun _ ↦ ?_
    exact measurable_id
  have hproj :
      finiteDimensionalProjection times = e0 ∘ Function.eval 0 := by
    -- Proof comment: the one-point finite-dimensional projection only records the value at time
    -- `0`, packaged as a constant `Fin 1` tuple.
    funext ω
    funext i
    fin_cases i
    simp [finiteDimensionalProjection, times, e0]
  have htuple :
      P.map (e0 ∘ Function.eval 0) = (Measure.dirac x).map e0 := by
    -- Proof comment: identify the one-point marginal with the `n = 0` consistent-family law and
    -- then collapse the unique-history coordinate back to `Fin 1`.
    calc
      P.map (e0 ∘ Function.eval 0) = P.map (finiteDimensionalProjection times) := by
        simp [hproj]
      _ =
          markovSemigroupFiniteDimKernelLocal
            (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
            times htimes ∘ₘ Measure.dirac x :=
        hP_fdim times rfl htimes
      _ = (Measure.dirac x).map e0 := by
        rw [markovSemigroupFiniteDimKernelLocal]
        rw [← Measure.map_comp _ _ (by
          refine measurable_pi_lambda _ fun _ ↦ ?_
          exact measurable_pi_apply _)]
        change
          Measure.map _ (consistentFamilyFiniteDimensionalMeasure (Measure.dirac x)
            (fun {s t : NNReal} _ ↦
              dirac_convolution_kernel (ν (t - s) : Measure (Fin d → ℝ)))
            _ _) = _
        rw [consistentFamilyFiniteDimensionalMeasure_zero]
        rw [Measure.map_map (by
          refine measurable_pi_lambda _ fun _ ↦ ?_
          exact measurable_pi_apply _)
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ Fin d → ℝ)).symm.measurable]
        rfl
  refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
  -- Proof comment: postcompose the singleton-tuple law with `Function.eval 0`, which is a left
  -- inverse to the embedding `e0`.
  calc
    P.map (Function.eval 0)
        = P.map ((Function.eval 0) ∘ (e0 ∘ Function.eval 0)) := by
            rfl
    _ = (P.map (e0 ∘ Function.eval 0)).map (Function.eval 0) := by
          rw [Measure.map_map (measurable_pi_apply 0)
            (he0_measurable.comp (measurable_pi_apply 0))]
    _ = ((Measure.dirac x).map e0).map (Function.eval 0) := by
          rw [htuple]
    _ = (Measure.dirac x).map ((Function.eval 0) ∘ e0) := by
          rw [Measure.map_map (measurable_pi_apply 0) he0_measurable]
    _ = Measure.dirac x := by
          simp [e0]

/-- Helper for Theorem 14.47: a zero-length increment of the canonical process is the constant
zero random variable, so its law is `Measure.dirac 0`. -/
private theorem selfIncrement_hasLaw_diracZero
    {d : ℕ} {P : Measure (NNReal → Fin d → ℝ)} [IsProbabilityMeasure P] (t : NNReal) :
    HasLaw
      (fun ω : NNReal → Fin d → ℝ ↦ ω t - ω t)
      (Measure.dirac (0 : Fin d → ℝ))
      P := by
  -- Proof comment: the increment map is pointwise equal to `0`, and a probability measure maps a
  -- constant random variable to the corresponding Dirac mass.
  refine ⟨((measurable_pi_apply t).sub (measurable_pi_apply t)).aemeasurable, ?_⟩
  ext A hA
  simp [hA]

/-- Helper for Theorem 14.47: the deterministic finite-grid increment vector attached to a time
tuple `times`. -/
private def incrementVector {d n : ℕ} (times : Fin (n + 1) → NNReal) :
    (NNReal → Fin d → ℝ) → Fin n → Fin d → ℝ :=
  fun ω i ↦ ω (times i.succ) - ω (times i.castSucc)

/-- Helper for Theorem 14.47: the finite-grid increment vector is measurable. -/
private theorem incrementVector_measurable {d n : ℕ}
    (times : Fin (n + 1) → NNReal) :
    Measurable (incrementVector (d := d) times) := by
  -- Proof comment: measurability is checked coordinatewise, since each increment coordinate is a
  -- difference of two measurable evaluations on the canonical path space.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- Helper for Theorem 14.47: the adjacent-difference map on a finite coordinate tuple. -/
private def tupleIncrementVector {d n : ℕ} :
    (Fin (n + 1) → Fin d → ℝ) → Fin n → Fin d → ℝ :=
  fun z i ↦ z i.succ - z i.castSucc

/-- Helper for Theorem 14.47: the adjacent-difference map on finite coordinate tuples is
measurable. -/
private theorem measurable_tupleIncrementVector {d n : ℕ} :
    Measurable (tupleIncrementVector (d := d) (n := n)) := by
  -- Proof comment: each output coordinate is the difference of two measurable tuple
  -- coordinates.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [tupleIncrementVector] using
    (measurable_pi_apply i.succ).sub (measurable_pi_apply i.castSucc)

/-- Helper for Theorem 14.47: applying adjacent differences after the finite-dimensional
projection recovers the canonical path-space increment vector. -/
private theorem tupleIncrementVector_comp_finiteDimensionalProjection {d n : ℕ}
    (times : Fin (n + 1) → NNReal) :
    tupleIncrementVector (d := d) (n := n) ∘ finiteDimensionalProjection times =
      incrementVector (d := d) times := by
  -- Proof comment: both sides read the same adjacent coordinate differences from the projected
  -- path tuple.
  funext ω
  ext i
  simp [tupleIncrementVector, incrementVector, finiteDimensionalProjection]

/-- Helper for Theorem 14.47: reindex an ordered history by `Fin` and record its adjacent
increments. -/
private def orderedHistoryIncrementVector {d n : ℕ} :
    (Π _ : Finset.Iic n, Fin d → ℝ) → Fin n → Fin d → ℝ :=
  fun z i ↦ z ((iicEquivFinLocal n).symm i.succ) - z ((iicEquivFinLocal n).symm i.castSucc)

/-- Helper for Theorem 14.47: the ordered-history increment vector is measurable. -/
private theorem measurable_orderedHistoryIncrementVector {d n : ℕ} :
    Measurable (orderedHistoryIncrementVector (d := d) (n := n)) := by
  -- Proof comment: after reindexing the ordered history to `Fin`, each increment coordinate is a
  -- measurable difference of two coordinate projections.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [orderedHistoryIncrementVector] using
    (measurable_pi_apply ((iicEquivFinLocal n).symm i.succ)).sub
      (measurable_pi_apply ((iicEquivFinLocal n).symm i.castSucc))

/-- Helper for Theorem 14.47: in `Finset.Iic (n + 1)`, the prefix endpoint is strictly below the
final index. -/
private theorem lastIic_lt_succLast (n : ℕ) :
    (⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ : Finset.Iic (n + 1)) <
      ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := by
  -- Proof comment: this is just the strict inequality `n < n + 1` viewed in the subtype.
  simpa using (Nat.lt_succ_self n)

/-- Helper for Theorem 14.47: after splitting off the last coordinate from a finite tuple of
`Fin d → ℝ`-valued entries, the second component is the `Fin.castSucc` prefix. -/
private theorem piFinSuccAboveLast_snd_eq_castSucc {d n : ℕ} :
    Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin d → ℝ) (Fin.last n) =
      fun z : Fin (n + 1) → Fin d → ℝ ↦ fun i : Fin n ↦ z i.castSucc := by
  funext z i
  -- Proof comment: for `Fin.last`, `succAbove` is exactly `Fin.castSucc`.
  simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]

/-- Helper for Theorem 14.47: `piFinSuccAbove` splits the last coordinate off a finite-grid
increment vector into the terminal increment and the prefix increment vector. -/
private theorem incrementVector_piFinSuccAbove_last {d n : ℕ}
    (times : Fin (n + 2) → NNReal) :
    (fun ω ↦
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin d → ℝ) (Fin.last n)
        (incrementVector (d := d) times ω)) =
      fun ω ↦
        (ω (times (Fin.last n).succ) - ω (times (Fin.last n).castSucc),
          incrementVector (d := d) (fun i : Fin (n + 1) ↦ times i.castSucc) ω) := by
  -- Proof comment: `piFinSuccAbove` isolates the terminal increment and reindexes the remaining
  -- coordinates by `Fin.castSucc`, which matches the prefix increment vector exactly.
  funext ω
  have htail :
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin d → ℝ) (Fin.last n))
        (incrementVector (d := d) times ω)).2 =
        fun i : Fin n ↦ incrementVector (d := d) times ω i.castSucc := by
    ext i x
    simpa [MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def, Fin.succAbove_last]
  apply Prod.ext
  · ext x
    simp [incrementVector, MeasurableEquiv.piFinSuccAbove_apply]
  · ext i x
    rw [htail]
    change ω (times (i.castSucc).succ) x - ω (times (i.castSucc).castSucc) x =
      ω (times i.succ.castSucc) x - ω (times i.castSucc.castSucc) x
    rw [Fin.succ_castSucc]

/-- Helper for Theorem 14.47: splitting the gap product law at the final coordinate gives the
terminal gap marginal together with the prefix gap product law. -/
private theorem incrementLawPi_map_piFinSuccAbove_last {d n : ℕ}
    (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (times : Fin (n + 2) → NNReal) :
    (Measure.pi (fun i : Fin (n + 1) ↦
      (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ)))).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin d → ℝ) (Fin.last n)) =
    (ν (times (Fin.last n).succ - times (Fin.last n).castSucc) : Measure (Fin d → ℝ)).prod
      (Measure.pi (fun i : Fin n ↦
        (ν ((fun j : Fin (n + 1) ↦ times j.castSucc) i.succ -
            (fun j : Fin (n + 1) ↦ times j.castSucc) i.castSucc) : Measure (Fin d → ℝ)))) := by
  let μ : Fin (n + 1) → Measure (Fin d → ℝ) := fun i ↦
    (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin d → ℝ) (Fin.last n)
  have hMapEq :
      (Measure.pi μ).map e =
        (μ (Fin.last n)).prod (Measure.pi fun i : Fin n ↦ μ ((Fin.last n).succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ (Fin.last n)).map_eq
  have hprefixFamily :
      (fun i : Fin n ↦ μ ((Fin.last n).succAbove i)) =
        (fun i : Fin n ↦
          (ν ((fun j : Fin (n + 1) ↦ times j.castSucc) i.succ -
              (fun j : Fin (n + 1) ↦ times j.castSucc) i.castSucc) :
            Measure (Fin d → ℝ))) := by
    funext i
    rw [Fin.succAbove_last]
    change
      (ν (times (i.castSucc).succ - times (i.castSucc).castSucc) :
        Measure (Fin d → ℝ)) =
      (ν ((fun j : Fin (n + 1) ↦ times j.castSucc) i.succ -
          (fun j : Fin (n + 1) ↦ times j.castSucc) i.castSucc) :
        Measure (Fin d → ℝ))
    rw [show (fun j : Fin (n + 1) ↦ times j.castSucc) i.succ = times i.succ.castSucc by rfl]
    rw [show (fun j : Fin (n + 1) ↦ times j.castSucc) i.castSucc = times i.castSucc.castSucc by rfl]
    rw [Fin.succ_castSucc]
  -- Proof comment: `measurePreserving_piFinSuccAbove` already gives the product factorization;
  -- for `Fin.last`, the remaining coordinates are exactly the `castSucc` prefix gaps.
  rw [hMapEq, hprefixFamily]

/-- Helper for Theorem 14.47: the canonical two-point time tuple `(0, t)` on `Fin 2`. -/
private def twoPointTimes (t : NNReal) : Fin 2 → NNReal
  | 0 => 0
  | 1 => t

/-- Helper for Theorem 14.47: if `t > 0`, then the two-point tuple `(0, t)` is strictly
increasing. -/
private theorem twoPointTimes_strictMono {t : NNReal} (ht : 0 < t) :
    StrictMono (twoPointTimes t) := by
  -- Proof comment: the only nontrivial comparison in `Fin 2` is `0 < 1`, which maps to
  -- `0 < t`.
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

/-- Helper for Theorem 14.47: the last coordinate extracted after reindexing `Iic 1` back to
`Fin 2` is the actual last history entry. -/
private theorem reindexTwoPoint_last {d : ℕ} :
    (Function.eval 1 : (Fin 2 → Fin d → ℝ) → Fin d → ℝ) ∘
        (fun z : (Π _ : Finset.Iic 1, Fin d → ℝ) ↦
          fun i ↦ z ((iicEquivFinLocal 1).symm i)) =
      (fun z : (Π _ : Finset.Iic 1, Fin d → ℝ) ↦ z ⟨1, Finset.mem_Iic.2 le_rfl⟩) := by
  -- Proof comment: reindexing the ordered two-point history back to `Fin 2` preserves the last
  -- coordinate.
  funext z
  simp [iicEquivFinLocal]

/-- Helper for Theorem 14.47: the last coordinate of the two-point finite-dimensional projection
is exactly evaluation at time `t`. -/
private theorem finiteDimensionalProjection_twoPoint_last {d : ℕ} (t : NNReal) :
    (fun ω : NNReal → Fin d → ℝ ↦ (finiteDimensionalProjection (twoPointTimes t) ω) 1) =
      Function.eval t := by
  funext ω
  simp [finiteDimensionalProjection, twoPointTimes]

/-- Helper for Theorem 14.47: the canonical three-point time tuple `(0, s, t)` on `Fin 3`. -/
private def threePointTimes (s t : NNReal) : Fin 3 → NNReal
  | 0 => 0
  | 1 => s
  | 2 => t

/-- Helper for Theorem 14.47: if `0 < s < t`, then the three-point tuple `(0, s, t)` is strictly
increasing. -/
private theorem threePointTimes_strictMono {s t : NNReal} (hs : 0 < s) (hst : s < t) :
    StrictMono (threePointTimes s t) := by
  -- Proof comment: the only nontrivial forward comparisons in `Fin 3` are `0 < 1`, `0 < 2`,
  -- and `1 < 2`, yielding `0 < s`, `0 < t`, and `s < t`.
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

/-- Helper for Theorem 14.47: after reindexing `Iic 2` back to `Fin 3`, the difference of the
last two coordinates is the actual increment between the last two history entries. -/
private theorem reindexThreePoint_increment {d : ℕ} :
    (fun z : (Π _ : Finset.Iic 2, Fin d → ℝ) ↦
      ((fun i : Fin 3 ↦ z ((iicEquivFinLocal 2).symm i)) 2) -
        ((fun i : Fin 3 ↦ z ((iicEquivFinLocal 2).symm i)) 1)) =
      (fun z : (Π _ : Finset.Iic 2, Fin d → ℝ) ↦
        z ⟨2, Finset.mem_Iic.2 le_rfl⟩ - z ⟨1, Finset.mem_Iic.2 (by decide : 1 ≤ 2)⟩) := by
  funext z
  simp [iicEquivFinLocal]

/-- Helper for Theorem 14.47: the increment extracted from the three-point finite-dimensional
projection `(0, s, t)` is exactly `ω t - ω s`. -/
private theorem finiteDimensionalProjection_threePoint_increment {d : ℕ} (s t : NNReal) :
    (fun ω : NNReal → Fin d → ℝ ↦
      (finiteDimensionalProjection (threePointTimes s t) ω) 2 -
        (finiteDimensionalProjection (threePointTimes s t) ω) 1) =
      (fun ω : NNReal → Fin d → ℝ ↦ ω t - ω s) := by
  funext ω
  simp [finiteDimensionalProjection, threePointTimes]

/-- Helper for Theorem 14.47: split a successor history into its prefix history and final state. -/
private noncomputable def succHistoryEquivLocal {d : ℕ} (n : ℕ) :
    (Π _ : Finset.Iic (n + 1), Fin d → ℝ) ≃ᵐ
      ((Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ)) :=
  (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ ↦ Fin d → ℝ) (Nat.le_succ n)).symm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n).symm)

/-- Helper for Theorem 14.47: `succHistoryEquivLocal` records the prefix restriction and the final
state. -/
@[simp] private theorem succHistoryEquivLocal_apply {d : ℕ} (n : ℕ)
    (z : Π _ : Finset.Iic (n + 1), Fin d → ℝ) :
    succHistoryEquivLocal (d := d) n z =
      (Preorder.frestrictLe₂ (π := fun _ : ℕ ↦ Fin d → ℝ) (Nat.le_succ n) z,
        z ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) := by
  -- Proof comment: unfold the measurable equivalence into the canonical `IicProdIoc` split and
  -- then collapse the singleton tail coordinate.
  rfl

/-- Helper for Theorem 14.47: the inverse of `succHistoryEquivLocal` glues a prefix history and
one terminal state back into a successor history. -/
@[simp] private theorem succHistoryEquivLocal_symm_apply {d : ℕ} (n : ℕ)
    (z : (Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ)) :
    (succHistoryEquivLocal (d := d) n).symm z =
      _root_.IicProdIoc (X := fun _ : ℕ ↦ Fin d → ℝ) n (n + 1)
        (z.1, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n z.2) := by
  -- Proof comment: the inverse first restores the singleton tail coordinate and then uses the
  -- canonical `IicProdIoc` gluing map.
  rfl

/-- Helper for Theorem 14.47: applying `succHistoryEquivLocal` after the canonical
`IicProdIoc` gluing map recovers the stored prefix together with the unique terminal state. -/
@[simp] private theorem succHistoryEquivLocal_apply_IicProdIoc {d : ℕ} (n : ℕ)
    (z : (Π _ : Finset.Iic n, Fin d → ℝ) × (Π _ : Finset.Ioc n (n + 1), Fin d → ℝ)) :
    succHistoryEquivLocal (d := d) n
        (_root_.IicProdIoc (X := fun _ : ℕ ↦ Fin d → ℝ) n (n + 1) z) =
      Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n).symm z := by
  -- Proof comment: splitting the glued successor history recovers its prefix restriction and
  -- collapses the singleton terminal fiber back to the last state.
  rcases z with ⟨z₁, z₂⟩
  apply Prod.ext
  · ext i x
    have hi : (i : ℕ) ≤ n := Finset.mem_Iic.mp i.2
    simp [succHistoryEquivLocal_apply, _root_.IicProdIoc_def, MeasurableEquiv.piSingleton, hi]
  · ext x
    simp [succHistoryEquivLocal_apply, _root_.IicProdIoc_def, MeasurableEquiv.piSingleton]

/-- Helper for Theorem 14.47: package the pointwise `succHistoryEquivLocal` normalization as the
function equality consumed by `Kernel.map_comp_right`. -/
private theorem succHistoryEquivLocal_comp_IicProdIoc {d : ℕ} (n : ℕ) :
    succHistoryEquivLocal (d := d) n ∘
        _root_.IicProdIoc (X := fun _ : ℕ ↦ Fin d → ℝ) n (n + 1) =
      Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n).symm := by
  -- Proof comment: `succHistoryEquivLocal` first splits the successor history into prefix plus
  -- singleton tail, and then collapses that singleton tail back to the last state.
  funext z
  simpa [Function.comp] using succHistoryEquivLocal_apply_IicProdIoc (d := d) n z

/-- Helper for Theorem 14.47: after reindexing an ordered successor history to `Fin`, splitting
off the last increment is the same as recording the final gap together with the prefix increment
vector. -/
private theorem orderedHistoryIncrementVector_piFinSuccAbove_last {d n : ℕ} :
    (fun z : Π _ : Finset.Iic (n + 1), Fin d → ℝ ↦
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin d → ℝ) (Fin.last n)
        (orderedHistoryIncrementVector (d := d) (n := n + 1) z)) =
      fun z ↦
        let p := succHistoryEquivLocal (d := d) n z
        (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
          orderedHistoryIncrementVector (d := d) (n := n) p.1) := by
  funext z
  apply Prod.ext
  · ext x
    simp [orderedHistoryIncrementVector, MeasurableEquiv.piFinSuccAbove_apply,
      succHistoryEquivLocal_apply, iicEquivFinLocal]
  · ext i x
    simp [orderedHistoryIncrementVector, MeasurableEquiv.piFinSuccAbove_apply,
      succHistoryEquivLocal_apply, Fin.init_def, iicEquivFinLocal]

/-- Helper for Theorem 14.47: on ordered three-point histories, the last gap factors through the
canonical split into `(prefix,last)`. -/
private theorem threePointOrderedGap_eq_gapAfterSplit {d : ℕ} :
    (fun z : (Π _ : Finset.Iic 2, Fin d → ℝ) ↦
      z ⟨2, Finset.mem_Iic.2 le_rfl⟩ - z ⟨1, Finset.mem_Iic.2 (by decide : 1 ≤ 2)⟩) =
      (fun p : (Π _ : Finset.Iic 1, Fin d → ℝ) × (Fin d → ℝ) ↦
        p.2 - p.1 ⟨1, Finset.mem_Iic.2 le_rfl⟩) ∘
        succHistoryEquivLocal (d := d) 1 := by
  -- Proof comment: after splitting a length-two history into its prefix and terminal state, the
  -- increment `z₂ - z₁` is just `last - prefix(1)`.
  funext z x
  simp [Function.comp, succHistoryEquivLocal_apply, Preorder.frestrictLe₂_apply]

/-- Helper for Theorem 14.47: once the mapped singleton-tail kernel is known to be s-finite,
the one-step partial trajectory normalizes under `succHistoryEquivLocal` to the product of the
stored prefix and the final-step kernel. -/
private theorem partialTraj_succ_self_map_succHistoryEquivLocal
    {d n : ℕ}
    (κhist : (m : ℕ) → Kernel (Π _ : Finset.Iic m, Fin d → ℝ) (Fin d → ℝ))
    [IsSFiniteKernel
      ((κhist n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n))] :
    ((ProbabilityTheory.Kernel.partialTraj
        (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist) n (n + 1)).map
        (succHistoryEquivLocal (d := d) n) :
          Kernel (Π _ : Finset.Iic n, Fin d → ℝ)
            ((Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ))) =
      Kernel.id ×ₖ κhist n := by
  -- Proof comment: rewrite the one-step partial trajectory by `partialTraj_succ_self`, then
  -- collapse the singleton tail coordinate through `succHistoryEquivLocal`.
  rw [ProbabilityTheory.Kernel.partialTraj_succ_self]
  rw [← Kernel.map_comp_right
    (κ := Kernel.id ×ₖ
      ((κhist n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n)))
    (f := _root_.IicProdIoc (X := fun _ : ℕ ↦ Fin d → ℝ) n (n + 1))
    (g := succHistoryEquivLocal (d := d) n)
    measurable_IicProdIoc
    (by fun_prop)]
  rw [succHistoryEquivLocal_comp_IicProdIoc (d := d) n]
  rw [← Kernel.map_prod_map _ _ measurable_id
    (MeasurableEquiv.symm
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n)).measurable]
  rw [Kernel.map_id]
  rw [← Kernel.map_comp_right
    (κ := κhist n)
    (f := MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n)
    (g := (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n).symm)
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n).measurable
    (MeasurableEquiv.symm
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n)).measurable]
  simpa using Kernel.map_id (κhist n)

/-- Helper for Theorem 14.47: mapping an ordered successor-history law through the canonical split
equivalence yields the composition-product of the prefix law with the final-step kernel. -/
private theorem consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
    {d n : ℕ}
    (K : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin d → ℝ) (Fin d → ℝ))
    (hSFinite : ∀ ⦃s t : NNReal⦄ (hst : s < t), IsSFiniteKernel (K hst))
    (j : Π _ : Finset.Iic (n + 1), NNReal) (hj : StrictMono j) (x : Fin d → ℝ) :
    let jPrefix : Π _ : Finset.Iic n, NNReal := fun i ↦
      j ⟨i.1, Finset.mem_Iic.2
        (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
    let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
    let lastPrefix : (Π _ : Finset.Iic n, Fin d → ℝ) → Fin d → ℝ := fun z ↦
      z ⟨n, Finset.mem_Iic.2 le_rfl⟩
    let hLastIdx :
        (⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ : Finset.Iic (n + 1)) <
          ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := lastIic_lt_succLast n
    let hLast :
        j ⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ <
          j ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
    let hlastPrefixMeasurable : Measurable lastPrefix := by
      simpa [lastPrefix] using measurable_lastIicCoordinate (d := d) (n := n)
    (consistentFamilyFiniteDimensionalKernel K j hj x).map (succHistoryEquivLocal (d := d) n) =
      (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
        Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable := by
  -- Route correction: avoid the old mapped-singleton helper boundary and normalize the terminal
  -- step directly in the owner spelling used by the finite-dimensional kernel.
  let jPrefix : Π _ : Finset.Iic n, NNReal := fun i ↦
    j ⟨i.1, Finset.mem_Iic.2
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
  let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
  let lastPrefix : (Π _ : Finset.Iic n, Fin d → ℝ) → Fin d → ℝ := fun z ↦
    z ⟨n, Finset.mem_Iic.2 le_rfl⟩
  let hLastIdx :
      (⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ : Finset.Iic (n + 1)) <
        ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := lastIic_lt_succLast n
  let hLast :
      j ⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ <
        j ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
  let hlastPrefixMeasurable : Measurable lastPrefix := by
    simpa [lastPrefix] using measurable_lastIicCoordinate (d := d) (n := n)
  let κhist :
      (m : ℕ) → Kernel (Π _ : Finset.Iic m, Fin d → ℝ) (Fin d → ℝ) :=
    fun m ↦
      if hm : m < n + 1 then
        Kernel.comap
          (K (hj (show (⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic (n + 1)) <
            ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)))
          (fun z : Π _ : Finset.Iic m, Fin d → ℝ ↦ z ⟨m, Finset.mem_Iic.2 le_rfl⟩)
          (measurable_lastIicCoordinate (d := d) (n := m))
      else
        Kernel.deterministic
          (fun z : Π _ : Finset.Iic m, Fin d → ℝ ↦
            z ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩)
          (measurable_zeroIicCoordinate (d := d) (n := m))
  let stepKernel : Kernel (Π _ : Finset.Iic n, Fin d → ℝ) (Fin d → ℝ) :=
    Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable
  let splitKernel :
      Kernel (Π _ : Finset.Iic n, Fin d → ℝ)
        ((Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ)) :=
    Kernel.id ×ₖ stepKernel
  have hstepKernel :
      κhist n = stepKernel := by
    -- Proof comment: at the final prefix index, the history kernel is exactly the last-step
    -- kernel read from the terminal prefix coordinate.
    simp [κhist, stepKernel, lastPrefix]
  have hcompose :
      succHistoryEquivLocal (d := d) n ∘
          _root_.IicProdIoc (X := fun _ : ℕ ↦ Fin d → ℝ) n (n + 1) =
        Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n).symm := by
    -- Proof comment: the successor-history split is the `IicProdIoc` gluing map followed by
    -- collapsing the singleton terminal coordinate.
    funext z
    simpa [Function.comp] using succHistoryEquivLocal_apply_IicProdIoc (d := d) n z
  have hsplitKernel :
      ((ProbabilityTheory.Kernel.partialTraj
          (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist) n (n + 1)).map
          (succHistoryEquivLocal (d := d) n) :
            Kernel (Π _ : Finset.Iic n, Fin d → ℝ)
              ((Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ))) =
        splitKernel := by
    -- Proof comment: the one-step trajectory becomes the product of the stored prefix and the
    -- terminal transition kernel once we split the successor history into `(prefix,last)`.
    letI : IsSFiniteKernel (K hLast) := hSFinite hLast
    letI : IsSFiniteKernel stepKernel := by
      dsimp [stepKernel]
      infer_instance
    letI :
        IsSFiniteKernel
          ((κhist n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n)) := by
      simpa [hstepKernel] using
        (inferInstance :
          IsSFiniteKernel
            (stepKernel.map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n)))
    rw [ProbabilityTheory.Kernel.partialTraj_succ_self]
    rw [← Kernel.map_comp_right
      (κ := Kernel.id ×ₖ
        ((κhist n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n)))
      (f := _root_.IicProdIoc (X := fun _ : ℕ ↦ Fin d → ℝ) n (n + 1))
      (g := succHistoryEquivLocal (d := d) n)
      measurable_IicProdIoc
      (succHistoryEquivLocal (d := d) n).measurable,
      hcompose]
    rw [← Kernel.map_prod_map _ _ measurable_id
      (MeasurableEquiv.symm
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n)).measurable]
    rw [Kernel.map_id]
    rw [hstepKernel]
    rw [← Kernel.map_comp_right _
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n).measurable
      (MeasurableEquiv.symm
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin d → ℝ) n)).measurable]
    simpa [splitKernel] using Kernel.map_id stepKernel
  have hκhistPrefix :
      ∀ m, m < n →
        κhist m = (consistentFamilyHistoryKernels K jPrefix hjPrefix) m := by
    intro m hm
    have hmLe : m ≤ n := Nat.le_of_lt hm
    simp [κhist, consistentFamilyHistoryKernels, jPrefix, hm, hmLe]
  have hpartialPrefix :
      ∀ m, m ≤ n →
        ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist) 0 m =
          ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ Fin d → ℝ)
            (κ := consistentFamilyHistoryKernels K jPrefix hjPrefix) 0 m := by
    intro m
    induction m with
    | zero =>
        intro _
        simp
    | succ k ih =>
        intro hm
        have hk : k < n := Nat.lt_of_succ_le hm
        rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
          (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist) (Nat.zero_le k)]
        rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
          (X := fun _ : ℕ ↦ Fin d → ℝ)
          (κ := consistentFamilyHistoryKernels K jPrefix hjPrefix) (Nat.zero_le k)]
        rw [ProbabilityTheory.Kernel.partialTraj_succ_self
          (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist)]
        rw [ProbabilityTheory.Kernel.partialTraj_succ_self
          (X := fun _ : ℕ ↦ Fin d → ℝ)
          (κ := consistentFamilyHistoryKernels K jPrefix hjPrefix)]
        rw [hκhistPrefix k hk, ih (Nat.le_of_lt hk)]
  have hsucc :
      consistentFamilyFiniteDimensionalKernel K j hj =
        ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist) n (n + 1) ∘ₖ
          consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix := by
    -- Proof comment: the successor finite-dimensional kernel factors as the prefix kernel
    -- followed by one additional history extension step.
    rw [consistentFamilyFiniteDimensionalKernel, consistentFamilyFiniteDimensionalKernel,
      consistentFamilyHistoryTraj, consistentFamilyHistoryTraj]
    change
      ProbabilityTheory.Kernel.partialTraj
          (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist) 0 (n + 1) ∘ₖ
        Kernel.deterministic initialHistory measurable_initialHistory =
      ProbabilityTheory.Kernel.partialTraj
          (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist) n (n + 1) ∘ₖ
        (ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ Fin d → ℝ)
            (κ := consistentFamilyHistoryKernels K jPrefix hjPrefix) 0 n ∘ₖ
          Kernel.deterministic initialHistory measurable_initialHistory)
    rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
      (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist) (Nat.zero_le n)]
    rw [Kernel.comp_assoc]
    rw [hpartialPrefix n le_rfl]
  have hκhistPrefix :
      ∀ m, IsSFiniteKernel ((consistentFamilyHistoryKernels K jPrefix hjPrefix) m) := by
    intro m
    dsimp [consistentFamilyHistoryKernels]
    split_ifs with hm
    · let hstep :
          jPrefix ⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ <
            jPrefix ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ := by
          exact hjPrefix (show
            (⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
              ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)
      letI : IsSFiniteKernel (K hstep) := hSFinite hstep
      simpa [hstep] using
        (inferInstance :
          IsSFiniteKernel
            (Kernel.comap
              (K hstep)
              (fun z : Π _ : Finset.Iic m, Fin d → ℝ ↦ z ⟨m, Finset.mem_Iic.2 le_rfl⟩)
              (measurable_lastIicCoordinate (d := d) (n := m))))
    · simpa using
        (inferInstance :
          IsSFiniteKernel
            (Kernel.deterministic
              (fun z : Π _ : Finset.Iic m, Fin d → ℝ ↦
                z ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩)
              (measurable_zeroIicCoordinate (d := d) (n := m))))
  letI : ∀ m, IsSFiniteKernel ((consistentFamilyHistoryKernels K jPrefix hjPrefix) m) :=
    hκhistPrefix
  letI : IsSFiniteKernel (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) := by
    dsimp [consistentFamilyFiniteDimensionalKernel, consistentFamilyHistoryTraj]
    infer_instance
  -- Proof comment: rewrite the successor law as prefix law followed by the one-step split and
  -- read the resulting pair kernel as a composition-product measure.
  calc
    (consistentFamilyFiniteDimensionalKernel K j hj x).map (succHistoryEquivLocal (d := d) n) =
        (((ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist) n (n + 1)).map
            (succHistoryEquivLocal (d := d) n)) ∘ₖ
              consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x := by
          rw [hsucc]
          rw [← Kernel.map_apply
            (ProbabilityTheory.Kernel.partialTraj
              (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist) n (n + 1) ∘ₖ
                consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix)
            (succHistoryEquivLocal (d := d) n).measurable x]
          simpa using congrArg
            (fun ξ :
              Kernel (Fin d → ℝ)
                ((Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ)) ↦ ξ x)
            (Kernel.map_comp
              (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix)
              (ProbabilityTheory.Kernel.partialTraj
                (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := κhist) n (n + 1))
              (succHistoryEquivLocal (d := d) n))
    _ = (splitKernel ∘ₖ consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x := by
          rw [hsplitKernel]
    _ = (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ stepKernel := by
          simpa [splitKernel] using
            (Measure.compProd_eq_comp_prod
              (μ := consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x)
              (κ := stepKernel)).symm

/-- Helper for Theorem 14.47: if the final state is sampled from the translated increment kernel
based on the last prefix value, then subtracting that prefix value recovers the increment law. -/
private theorem compProd_map_sub_lastPrefix_eq
    {d n : ℕ}
    (ν : ProbabilityMeasure (Fin d → ℝ))
    (μ : Measure (Π _ : Finset.Iic n, Fin d → ℝ))
    [IsProbabilityMeasure μ]
    (lastPrefix : (Π _ : Finset.Iic n, Fin d → ℝ) → Fin d → ℝ)
    (hlastPrefixMeasurable : Measurable lastPrefix) :
    let stepKernel : Kernel (Π _ : Finset.Iic n, Fin d → ℝ) (Fin d → ℝ) :=
      Kernel.comap (dirac_convolution_kernel (ν : Measure (Fin d → ℝ))) lastPrefix
        hlastPrefixMeasurable
    (μ ⊗ₘ stepKernel).map
        (fun p : (Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ) ↦ p.2 - lastPrefix p.1) =
      (ν : Measure (Fin d → ℝ)) := by
  let stepKernel : Kernel (Π _ : Finset.Iic n, Fin d → ℝ) (Fin d → ℝ) :=
    Kernel.comap (dirac_convolution_kernel (ν : Measure (Fin d → ℝ))) lastPrefix
      hlastPrefixMeasurable
  let gapMap :
      ((Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ)) → Fin d → ℝ :=
    fun p ↦ p.2 - lastPrefix p.1
  have hgapMapMeasurable : Measurable gapMap := by
    exact measurable_snd.sub (hlastPrefixMeasurable.comp measurable_fst)
  letI : IsSFiniteKernel stepKernel := by
    dsimp [stepKernel]
    infer_instance
  have hkernel :
      ((Kernel.id ×ₖ stepKernel).map gapMap) =
        Kernel.const (Π _ : Finset.Iic n, Fin d → ℝ) (ν : Measure (Fin d → ℝ)) := by
    ext z A hA
    -- Proof comment: after fixing the prefix history `z`, the pair kernel is just the translated
    -- row law `δ_{lastPrefix z} * ν`, and subtracting the prefix endpoint cancels the translation.
    rw [Kernel.map_apply _ hgapMapMeasurable, Kernel.prod_apply, Kernel.id_apply]
    rw [Measure.dirac_prod, Measure.map_map hgapMapMeasurable measurable_prodMk_left]
    rw [Kernel.comap_apply, dirac_convolution_kernel_apply]
    rw [Measure.dirac_conv]
    have hcancel :
        Measure.map (fun y : Fin d → ℝ ↦ y - lastPrefix z)
            (Measure.map (fun y : Fin d → ℝ ↦ lastPrefix z + y) (ν : Measure (Fin d → ℝ))) =
          (ν : Measure (Fin d → ℝ)) := by
      simpa [Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Measure.map_map
          (μ := (ν : Measure (Fin d → ℝ)))
          (f := fun y : Fin d → ℝ ↦ lastPrefix z + y)
          (g := fun y : Fin d → ℝ ↦ y - lastPrefix z)
          (measurable_id.sub measurable_const)
          (measurable_const.add measurable_id))
    exact congrArg (fun m : Measure (Fin d → ℝ) ↦ m A) hcancel
  -- Proof comment: rewrite the `compProd` measure as the composition of the pair kernel with the
  -- prefix measure and use the rowwise cancellation proved above.
  calc
    (μ ⊗ₘ stepKernel).map gapMap = (((Kernel.id ×ₖ stepKernel).map gapMap) ∘ₘ μ) := by
      rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hgapMapMeasurable]
    _ = (Kernel.const (Π _ : Finset.Iic n, Fin d → ℝ) (ν : Measure (Fin d → ℝ))) ∘ₘ μ := by
          rw [hkernel]
    _ = (ν : Measure (Fin d → ℝ)) := by
          simpa using
            (Measure.const_comp
              (μ := μ) (ν := (ν : Measure (Fin d → ℝ))))

/-- Helper for Theorem 14.47: after separating the final translated step into `(history, gap)`,
pushing the history through any measurable prefix statistic yields the product of the gap law and
the pushed-forward prefix law. -/
private theorem compProd_map_gapAndPrefix_eq_prod
    {d n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (νGap : ProbabilityMeasure (Fin d → ℝ))
    (μ : Measure (Π _ : Finset.Iic n, Fin d → ℝ))
    [IsProbabilityMeasure μ]
    (lastPrefix : (Π _ : Finset.Iic n, Fin d → ℝ) → Fin d → ℝ)
    (hlastPrefixMeasurable : Measurable lastPrefix)
    (prefixMap : (Π _ : Finset.Iic n, Fin d → ℝ) → Y)
    (hprefixMap : Measurable prefixMap) :
    let stepKernel : Kernel (Π _ : Finset.Iic n, Fin d → ℝ) (Fin d → ℝ) :=
      Kernel.comap (dirac_convolution_kernel (νGap : Measure (Fin d → ℝ))) lastPrefix
        hlastPrefixMeasurable
    (μ ⊗ₘ stepKernel).map
        (fun p : (Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ) ↦
          (p.2 - lastPrefix p.1, prefixMap p.1)) =
      (νGap : Measure (Fin d → ℝ)).prod (μ.map prefixMap) := by
  let stepKernel : Kernel (Π _ : Finset.Iic n, Fin d → ℝ) (Fin d → ℝ) :=
    Kernel.comap (dirac_convolution_kernel (νGap : Measure (Fin d → ℝ))) lastPrefix
      hlastPrefixMeasurable
  let historyGap :
      ((Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ)) →
        (Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ) :=
    fun p ↦ (p.1, p.2 - lastPrefix p.1)
  have hhistoryGapMeasurable : Measurable historyGap := by
    exact measurable_fst.prodMk (measurable_snd.sub (hlastPrefixMeasurable.comp measurable_fst))
  have hswapPrefixMeasurable :
      Measurable
        (fun q : (Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ) ↦
          (q.2, prefixMap q.1)) := by
    exact measurable_snd.prodMk (hprefixMap.comp measurable_fst)
  letI : IsSFiniteKernel stepKernel := by
    dsimp [stepKernel]
    infer_instance
  have hhistoryGapKernel :
      ((Kernel.id ×ₖ stepKernel).map historyGap) =
        Kernel.id ×ₖ
          Kernel.const (Π _ : Finset.Iic n, Fin d → ℝ) (νGap : Measure (Fin d → ℝ)) := by
    ext z s hs
    let shift : (Fin d → ℝ) → Fin d → ℝ := fun y ↦ y - lastPrefix z
    have hshiftMeasurable : Measurable shift := by
      simpa [shift] using (measurable_id.sub measurable_const)
    have htranslateMeasurable :
        Measurable (fun y : Fin d → ℝ ↦ lastPrefix z + y) := by
      simpa using (measurable_const.add measurable_id)
    have hshift :
        (stepKernel z).map shift = (νGap : Measure (Fin d → ℝ)) := by
      -- Proof comment: the row law of `stepKernel` is the translate of `νGap` by
      -- `lastPrefix z`, so subtracting that prefix endpoint recovers the centered gap law.
      rw [Kernel.comap_apply, dirac_convolution_kernel_apply]
      rw [Measure.dirac_conv]
      simpa [shift, Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Measure.map_map
          (μ := (νGap : Measure (Fin d → ℝ)))
          (f := fun y ↦ lastPrefix z + y) (g := shift)
          hshiftMeasurable htranslateMeasurable)
    have hmap :
        ((Kernel.id ×ₖ stepKernel).map historyGap) z s =
          (((stepKernel z).map shift).map (Prod.mk z)) s := by
      -- Proof comment: after fixing the history, the mapped pair row is obtained by inserting
      -- that history coordinate and centering the fresh increment.
      rw [Kernel.map_apply' _ hhistoryGapMeasurable _ hs]
      rw [Kernel.id_prod_apply' stepKernel z (hhistoryGapMeasurable hs)]
      rw [Measure.map_apply measurable_prodMk_left hs]
      rw [Measure.map_apply hshiftMeasurable (measurable_prodMk_left hs)]
      congr 1
    calc
      (((Kernel.id ×ₖ stepKernel).map historyGap) z) s
          = (((stepKernel z).map shift).map (Prod.mk z)) s := hmap
      _ = (Measure.map (Prod.mk z) (νGap : Measure (Fin d → ℝ))) s := by
            rw [hshift]
      _ =
          ((Kernel.id ×ₖ
              Kernel.const (Π _ : Finset.Iic n, Fin d → ℝ) (νGap : Measure (Fin d → ℝ))) z) s := by
            rw [Kernel.id_prod_apply' (Kernel.const _ (νGap : Measure (Fin d → ℝ))) z hs]
            rw [Kernel.const_apply, Measure.map_apply (by fun_prop) hs]
  have hhistoryGapMeasure :
      (μ ⊗ₘ stepKernel).map historyGap = μ.prod (νGap : Measure (Fin d → ℝ)) := by
    -- Proof comment: the mapped pair law has the history as its first coordinate and the centered
    -- fresh increment as an independent second coordinate.
    calc
      (μ ⊗ₘ stepKernel).map historyGap =
          (((Kernel.id ×ₖ stepKernel).map historyGap) ∘ₘ μ) := by
            rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ (by fun_prop)]
      _ =
          ((Kernel.id ×ₖ
              Kernel.const (Π _ : Finset.Iic n, Fin d → ℝ) (νGap : Measure (Fin d → ℝ))) ∘ₘ μ) := by
            rw [hhistoryGapKernel]
      _ =
          μ ⊗ₘ Kernel.const (Π _ : Finset.Iic n, Fin d → ℝ) (νGap : Measure (Fin d → ℝ)) := by
            rw [Measure.compProd_eq_comp_prod]
      _ = μ.prod (νGap : Measure (Fin d → ℝ)) := by
            simpa using
              (Measure.compProd_const
                (μ := μ) (ν := (νGap : Measure (Fin d → ℝ))))
  -- Proof comment: once the centered pair law is `μ.prod νGap`, mapping the history coordinate
  -- by `prefixMap` and swapping the factors gives the desired product measure on
  -- `(gap, prefix statistic)`.
  calc
    (μ ⊗ₘ stepKernel).map
        (fun p : (Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ) ↦
          (p.2 - lastPrefix p.1, prefixMap p.1))
        = ((μ ⊗ₘ stepKernel).map historyGap).map
            (fun q : (Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ) ↦
              (q.2, prefixMap q.1)) := by
              simpa [historyGap, Function.comp] using
                (Measure.map_map
                  (μ := μ ⊗ₘ stepKernel)
                  (f := historyGap)
                  (g := fun q : (Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ) ↦
                    (q.2, prefixMap q.1))
                  hswapPrefixMeasurable
                  hhistoryGapMeasurable).symm
    _ = (μ.prod (νGap : Measure (Fin d → ℝ))).map
          (fun q : (Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ) ↦
            (q.2, prefixMap q.1)) := by
              rw [hhistoryGapMeasure]
    _ = (((μ.prod (νGap : Measure (Fin d → ℝ))).map (Prod.map prefixMap id)).map Prod.swap) := by
          simpa [Function.comp] using
            (Measure.map_map
              (μ := μ.prod (νGap : Measure (Fin d → ℝ)))
              (f := Prod.map prefixMap id)
              (g := Prod.swap)
              measurable_swap
              (hprefixMap.prodMap measurable_id)).symm
    _ = (((μ.map prefixMap).prod (νGap : Measure (Fin d → ℝ))).map Prod.swap) := by
          rw [← Measure.map_prod_map
            (μa := μ) (μc := (νGap : Measure (Fin d → ℝ))) hprefixMap measurable_id]
          simp
    _ = (νGap : Measure (Fin d → ℝ)).prod (μ.map prefixMap) := by
          simpa [Measure.map_id] using
            (Measure.prod_swap
              (μ := μ.map prefixMap) (ν := (νGap : Measure (Fin d → ℝ))))

/-- Helper for Theorem 14.47: on a strict time grid, the ordered-history increment vector under
the owner finite-dimensional kernel has the product law of the successive gap measures. -/
private theorem orderedHistoryIncrementVector_map_eq_pi_of_strict
    {d n : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (times : Fin (n + 1) → NNReal) (htimes : StrictMono times) (x : Fin d → ℝ) :
    let K : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin d → ℝ) (Fin d → ℝ) :=
      fun {s t} _ ↦ dirac_convolution_kernel (ν (t - s) : Measure (Fin d → ℝ))
    let j : Π _ : Finset.Iic n, NNReal := orderedTimeChainLocal times
    let hj : StrictMono j := orderedTimeChainLocal_strictMono htimes
    (consistentFamilyFiniteDimensionalKernel K j hj x).map
        (orderedHistoryIncrementVector (d := d) (n := n)) =
      Measure.pi (fun i : Fin n ↦
        (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))) := by
  induction n with
  | zero =>
      -- Proof comment: a one-point history has no nontrivial increment coordinates.
      have hconst :
          orderedHistoryIncrementVector (d := d) (n := 0) =
            fun _ : (Π _ : Finset.Iic 0, Fin d → ℝ) ↦ (isEmptyElim : Fin 0 → Fin d → ℝ) := by
        funext z i
        exact Fin.elim0 i
      let κ0 : Kernel (Fin d → ℝ) (Π _ : Finset.Iic 0, Fin d → ℝ) :=
        consistentFamilyFiniteDimensionalKernel
          (fun {s t} _ ↦ dirac_convolution_kernel (ν (t - s) : Measure (Fin d → ℝ)))
          (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes)
      have hKernelMarkov :
          IsMarkovKernel
            κ0 := by
        refine
          consistentFamilyFiniteDimensionalKernel_isMarkov
            (κ := fun {s t} _ ↦ dirac_convolution_kernel (ν (t - s) : Measure (Fin d → ℝ)))
            ?_
            (j := orderedTimeChainLocal times)
            (hj := orderedTimeChainLocal_strictMono htimes)
        intro s t hst
        infer_instance
      have hmass : (κ0 x) Set.univ = 1 := by
        letI : IsMarkovKernel κ0 := hKernelMarkov
        letI : IsProbabilityMeasure (κ0 x) := inferInstance
        simpa using (show (κ0 x) Set.univ = 1 from measure_univ)
      simpa [hconst] using
        (show
          Measure.map
              (fun _ : (Π _ : Finset.Iic 0, Fin d → ℝ) ↦ (isEmptyElim : Fin 0 → Fin d → ℝ))
              (κ0 x) =
            Measure.pi (fun i : Fin 0 ↦
              (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))) from by
            rw [Measure.map_const]
            rw [hmass]
            simpa using
              (Measure.pi_of_empty
                (fun i : Fin 0 ↦
                  (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ)))
                (isEmptyElim : Fin 0 → Fin d → ℝ)).symm)
  | succ n ih =>
      let K : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin d → ℝ) (Fin d → ℝ) :=
        fun {s t} _ ↦ dirac_convolution_kernel (ν (t - s) : Measure (Fin d → ℝ))
      let prefixTimes : Fin (n + 1) → NNReal := fun i ↦ times i.castSucc
      let hprefixStrict : StrictMono prefixTimes := by
        intro i k hik
        exact htimes (by simpa [prefixTimes] using hik)
      let νHist : Measure (Π _ : Finset.Iic (n + 1), Fin d → ℝ) :=
        consistentFamilyFiniteDimensionalKernel K
          (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes) x
      let νPrefix : Measure (Π _ : Finset.Iic n, Fin d → ℝ) :=
        consistentFamilyFiniteDimensionalKernel K
          (orderedTimeChainLocal prefixTimes)
          (orderedTimeChainLocal_strictMono hprefixStrict) x
      let e :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin d → ℝ) (Fin.last n)
      let νGap : ProbabilityMeasure (Fin d → ℝ) :=
        ν (times (Fin.last n).succ - times (Fin.last n).castSucc)
      have hκMarkov : ∀ {s t : NNReal} (hst : s < t), IsMarkovKernel (K hst) := by
        intro s t hst
        dsimp [K]
        infer_instance
      letI :
          IsMarkovKernel
            (consistentFamilyFiniteDimensionalKernel K
              (orderedTimeChainLocal prefixTimes)
              (orderedTimeChainLocal_strictMono hprefixStrict)) :=
        consistentFamilyFiniteDimensionalKernel_isMarkov K
          (fun {_ _} hst ↦ hκMarkov hst)
          (orderedTimeChainLocal prefixTimes)
          (orderedTimeChainLocal_strictMono hprefixStrict)
      letI : IsProbabilityMeasure νPrefix := by
        dsimp [νPrefix]
        infer_instance
      have hsplit :
          νHist.map (succHistoryEquivLocal (d := d) n) =
            νPrefix ⊗ₘ
              Kernel.comap (dirac_convolution_kernel (νGap : Measure (Fin d → ℝ)))
                (fun z : Π _ : Finset.Iic n, Fin d → ℝ ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                (measurable_lastIicCoordinate (d := d) (n := n)) := by
        -- Proof comment: split the ordered history into its prefix and the final translated
        -- step.
        simpa [νHist, νPrefix, K, νGap, prefixTimes, orderedTimeChainLocal, iicEquivFinLocal]
          using
            (consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
              (d := d) (K := K)
              (hSFinite := fun {_ _} _ ↦ by infer_instance)
              (j := orderedTimeChainLocal times)
              (hj := orderedTimeChainLocal_strictMono htimes) (x := x))
      have hpair :
          ((νHist.map (orderedHistoryIncrementVector (d := d) (n := n + 1))).map e) =
            (νGap : Measure (Fin d → ℝ)).prod
              (Measure.pi
                (fun i : Fin n ↦
                  (ν (prefixTimes i.succ - prefixTimes i.castSucc) :
                    Measure (Fin d → ℝ)))) := by
        -- Proof comment: isolate the terminal increment with `piFinSuccAbove`; the split-history
        -- law then factors this last gap from the prefix increment vector.
        calc
          ((νHist.map (orderedHistoryIncrementVector (d := d) (n := n + 1))).map e) =
              (νHist.map
                (fun z : Π _ : Finset.Iic (n + 1), Fin d → ℝ ↦
                  e (orderedHistoryIncrementVector (d := d) (n := n + 1) z))) := by
                    simpa [Function.comp] using
                      (Measure.map_map
                        (μ := νHist)
                        (f := orderedHistoryIncrementVector (d := d) (n := n + 1))
                        (g := e)
                        e.measurable
                        (measurable_orderedHistoryIncrementVector (d := d) (n := n + 1)))
          _ =
              (νHist.map
                (fun z : Π _ : Finset.Iic (n + 1), Fin d → ℝ ↦
                  let p := succHistoryEquivLocal (d := d) n z
                  (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
                    orderedHistoryIncrementVector (d := d) (n := n) p.1))) := by
                      congr 1
                      exact orderedHistoryIncrementVector_piFinSuccAbove_last (d := d) (n := n)
          _ =
              ((νHist.map (succHistoryEquivLocal (d := d) n)).map
                (fun p : (Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ) ↦
                  (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
                    orderedHistoryIncrementVector (d := d) (n := n) p.1))) := by
                      symm
                      exact
                        Measure.map_map
                          ((measurable_snd.sub
                            ((measurable_lastIicCoordinate (d := d) (n := n)).comp measurable_fst)).prodMk
                            ((measurable_orderedHistoryIncrementVector (d := d) (n := n)).comp
                              measurable_fst))
                          (succHistoryEquivLocal (d := d) n).measurable
          _ =
              ((νPrefix ⊗ₘ
                Kernel.comap (dirac_convolution_kernel (νGap : Measure (Fin d → ℝ)))
                  (fun z : Π _ : Finset.Iic n, Fin d → ℝ ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                  (measurable_lastIicCoordinate (d := d) (n := n))).map
                (fun p : (Π _ : Finset.Iic n, Fin d → ℝ) × (Fin d → ℝ) ↦
                  (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
                    orderedHistoryIncrementVector (d := d) (n := n) p.1))) := by
                      rw [hsplit]
          _ =
              (νGap : Measure (Fin d → ℝ)).prod
                (νPrefix.map (orderedHistoryIncrementVector (d := d) (n := n))) := by
                simpa [νGap, νPrefix] using
                  (compProd_map_gapAndPrefix_eq_prod
                    (d := d) (n := n) (Y := Fin n → Fin d → ℝ)
                    (νGap := νGap) (μ := νPrefix)
                    (lastPrefix := fun z : Π _ : Finset.Iic n, Fin d → ℝ ↦
                      z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                    (hlastPrefixMeasurable := measurable_lastIicCoordinate (d := d) (n := n))
                    (prefixMap := orderedHistoryIncrementVector (d := d) (n := n))
                    (hprefixMap := measurable_orderedHistoryIncrementVector (d := d) (n := n)))
          _ =
              (νGap : Measure (Fin d → ℝ)).prod
                (Measure.pi
                  (fun i : Fin n ↦
                    (ν (prefixTimes i.succ - prefixTimes i.castSucc) :
                      Measure (Fin d → ℝ)))) := by
                rw [ih prefixTimes hprefixStrict]
      have hpairPi :
          (Measure.pi (fun i : Fin (n + 1) ↦
            (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ)))).map e =
              (νGap : Measure (Fin d → ℝ)).prod
                (Measure.pi
                  (fun i : Fin n ↦
                    (ν (prefixTimes i.succ - prefixTimes i.castSucc) :
                      Measure (Fin d → ℝ)))) := by
        simpa [e, νGap, prefixTimes] using
          incrementLawPi_map_piFinSuccAbove_last (d := d) ν times
      -- Proof comment: `piFinSuccAbove` has the same image law on both sides, so mapping back by
      -- its inverse cancels the split and recovers the full product law.
      calc
        νHist.map (orderedHistoryIncrementVector (d := d) (n := n + 1)) =
            ((νHist.map (orderedHistoryIncrementVector (d := d) (n := n + 1))).map e).map
              e.symm := by
                simpa [e] using
                  (MeasurableEquiv.map_map_symm
                    (ν := νHist.map (orderedHistoryIncrementVector (d := d) (n := n + 1)))
                    e.symm).symm
        _ =
            ((Measure.pi (fun i : Fin (n + 1) ↦
              (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ)))).map e).map
                e.symm := by
                  rw [hpair, hpairPi.symm]
        _ =
            Measure.pi (fun i : Fin (n + 1) ↦
              (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))) := by
                simpa [e] using
                  (MeasurableEquiv.map_map_symm
                    (ν := Measure.pi (fun i : Fin (n + 1) ↦
                      (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))))
                    e.symm)

/-- Helper for Theorem 14.47: on an anchored strict time grid, the canonical path measure sends
the finite increment vector to the product law of the successive gap measures. -/
private theorem canonicalIncrementVector_map_eq_pi_of_strict_start_zero
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ)) (x : Fin d → ℝ)
    {P : Measure (NNReal → Fin d → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
              times htimes ∘ₘ Measure.dirac x)
    {n : ℕ} (times : Fin (n + 1) → NNReal)
    (hzero : times 0 = 0) (htimes : StrictMono times) :
    P.map (incrementVector (d := d) times) =
      Measure.pi (fun i : Fin n ↦
        (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))) := by
  letI : IsProbabilityMeasure P :=
    (canonicalPathMeasureStart_hasLaw ν x hP_fdim).isProbabilityMeasure
  have hcomp :
      tupleIncrementVector (d := d) (n := n) ∘ finiteDimensionalProjection times =
        incrementVector (d := d) times := by
    -- Proof comment: the public increment vector is the adjacent-difference map applied to the
    -- finite-dimensional coordinate tuple.
    exact tupleIncrementVector_comp_finiteDimensionalProjection (d := d) times
  let νHist : Measure (Π _ : Finset.Iic n, Fin d → ℝ) :=
    consistentFamilyFiniteDimensionalKernel
      (fun {s t : NNReal} _ ↦ dirac_convolution_kernel (ν (t - s) : Measure (Fin d → ℝ)))
      (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes) x
  have hpublic :
      ((markovSemigroupFiniteDimKernelLocal
        (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
        times htimes) ∘ₘ Measure.dirac x).map
          (tupleIncrementVector (d := d) (n := n)) =
        νHist.map (orderedHistoryIncrementVector (d := d) (n := n)) := by
    -- Proof comment: `markovSemigroupFiniteDimKernelLocal` is exactly the ordered-history law
    -- reindexed to `Fin`, and `orderedHistoryIncrementVector` records the corresponding adjacent
    -- differences.
    rw [markovSemigroupFiniteDimKernelLocal]
    rw [Measure.dirac_bind (Kernel.measurable _) x]
    rw [Kernel.map_apply _ (by
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact measurable_pi_apply ((iicEquivFinLocal n).symm i)) x]
    calc
      Measure.map (tupleIncrementVector (d := d) (n := n))
          (Measure.map
            (fun z : Π _ : Finset.Iic n, Fin d → ℝ ↦
              fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i))
            νHist)
          =
            Measure.map
              ((tupleIncrementVector (d := d) (n := n)) ∘
                (fun z : Π _ : Finset.Iic n, Fin d → ℝ ↦
                  fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i)))
              νHist := by
                have hreindexMeasurable :
                    Measurable
                      (fun z : Π _ : Finset.Iic n, Fin d → ℝ ↦
                        fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i)) := by
                  refine measurable_pi_lambda _ fun i ↦ ?_
                  exact measurable_pi_apply ((iicEquivFinLocal n).symm i)
                exact
                  Measure.map_map
                    (μ := νHist)
                    (f := fun z : Π _ : Finset.Iic n, Fin d → ℝ ↦
                      fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i))
                    (g := tupleIncrementVector (d := d) (n := n))
                    (measurable_tupleIncrementVector (d := d) (n := n))
                    hreindexMeasurable
      _ = Measure.map (orderedHistoryIncrementVector (d := d) (n := n)) νHist := by
            rfl
  -- Proof comment: rewrite the public increment vector as adjacent differences of the
  -- finite-dimensional tuple, replace that tuple law by `hP_fdim`, and then transport the strict
  -- owner-side product law back to the public path space.
  calc
    P.map (incrementVector (d := d) times) =
        P.map (tupleIncrementVector (d := d) (n := n) ∘ finiteDimensionalProjection times) := by
          simpa [Function.comp] using
            congrArg
              (fun f : (NNReal → Fin d → ℝ) → Fin n → Fin d → ℝ ↦ P.map f)
              hcomp.symm
    _ =
        (P.map (finiteDimensionalProjection times)).map
          (tupleIncrementVector (d := d) (n := n)) := by
            symm
            exact
              Measure.map_map
                (measurable_tupleIncrementVector (d := d) (n := n))
                (measurable_finiteDimensionalProjection times)
    _ =
        (((markovSemigroupFiniteDimKernelLocal
          (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
          times htimes) ∘ₘ Measure.dirac x)).map
            (tupleIncrementVector (d := d) (n := n)) := by
              rw [hP_fdim times hzero htimes]
    _ = νHist.map (orderedHistoryIncrementVector (d := d) (n := n)) := hpublic
    _ =
        Measure.pi (fun i : Fin n ↦
          (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))) := by
            exact orderedHistoryIncrementVector_map_eq_pi_of_strict ν times htimes x

/-- Helper for Theorem 14.47: delete the later endpoint of one adjacent duplicate from a finite
time grid. -/
private def deleteAdjacentDuplicateTimes {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1)) : Fin (n + 1) → NNReal :=
  fun i ↦ times (k.succ.succAbove i)

/-- Helper for Theorem 14.47: deleting the later endpoint of an adjacent duplicate preserves the
anchored zero start. -/
private theorem deleteAdjacentDuplicateTimes_zero {n : ℕ}
    {times : Fin (n + 2) → NNReal} {k : Fin (n + 1)} (hzero : times 0 = 0) :
    deleteAdjacentDuplicateTimes times k 0 = 0 := by
  -- Proof comment: deleting a strictly positive index leaves the initial time unchanged.
  simpa [deleteAdjacentDuplicateTimes] using hzero

/-- Helper for Theorem 14.47: deleting the later endpoint of an adjacent duplicate preserves
monotonicity. -/
private theorem deleteAdjacentDuplicateTimes_monotone {n : ℕ}
    {times : Fin (n + 2) → NNReal} {k : Fin (n + 1)} (htimes : Monotone times) :
    Monotone (deleteAdjacentDuplicateTimes times k) := by
  intro i j hij
  -- Proof comment: `Fin.succAbove` preserves the order of the surviving coordinates.
  exact htimes (by simpa [deleteAdjacentDuplicateTimes] using hij)

/-- Helper for Theorem 14.47: on the shortened grid, the `i.succ` coordinate is the successor of
the surviving long-grid increment index. -/
private theorem deleteAdjacentDuplicateTimes_succ {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1)) (i : Fin n) :
    deleteAdjacentDuplicateTimes times k i.succ = times (k.succAbove i).succ := by
  -- Proof comment: `succAbove` commutes with `succ` when the deleted coordinate is `k.succ`.
  simp [deleteAdjacentDuplicateTimes]

/-- Helper for Theorem 14.47: on the shortened grid, the `i.castSucc` coordinate is the surviving
left endpoint of the corresponding long-grid increment. -/
private theorem deleteAdjacentDuplicateTimes_castSucc {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1))
    (hdup : times k.castSucc = times k.succ) (i : Fin n) :
    deleteAdjacentDuplicateTimes times k i.castSucc = times (k.succAbove i).castSucc := by
  -- Proof comment: the surviving left endpoint depends on whether the deleted duplicate lies
  -- after `i.castSucc` or at/before it.
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

/-- Helper for Theorem 14.47: if two adjacent times coincide, then splitting the increment vector
at that increment coordinate exposes a deterministic `0` together with the shortened increment
vector. -/
private theorem incrementVector_piFinSuccAbove_of_adjacentDuplicate {d n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1))
    (hdup : times k.castSucc = times k.succ) :
    (fun ω ↦
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin d → ℝ) k
        (incrementVector (d := d) times ω)) =
      fun ω ↦ (0, incrementVector (d := d) (deleteAdjacentDuplicateTimes times k) ω) := by
  funext ω
  apply Prod.ext
  · -- Proof comment: the separated increment is the duplicated gap, hence it vanishes.
    ext x
    simp [incrementVector, MeasurableEquiv.piFinSuccAbove_apply, hdup]
  · -- Proof comment: every surviving increment on the shortened grid matches the corresponding
    -- surviving increment on the long grid.
    ext i x
    change
      ω (times (k.succAbove i).succ) x - ω (times (k.succAbove i).castSucc) x =
        ω (deleteAdjacentDuplicateTimes times k i.succ) x -
          ω (deleteAdjacentDuplicateTimes times k i.castSucc) x
    rw [deleteAdjacentDuplicateTimes_succ, deleteAdjacentDuplicateTimes_castSucc _ _ hdup]

/-- Helper for Theorem 14.47: the increment product law on a grid with one adjacent duplicate is
the zero-insertion of the shortened increment product law. -/
private theorem incrementLawPi_map_piFinSuccAbove_of_adjacentDuplicate {d n : ℕ}
    (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (hν : IsConvolutionSemigroupWithZero ν)
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1))
    (hdup : times k.castSucc = times k.succ) :
    (Measure.pi (fun i : Fin (n + 1) ↦
      (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ)))).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin d → ℝ) k) =
        (Measure.dirac (0 : Fin d → ℝ)).prod
          (Measure.pi (fun i : Fin n ↦
            (ν ((deleteAdjacentDuplicateTimes times k) i.succ -
                (deleteAdjacentDuplicateTimes times k) i.castSucc) :
              Measure (Fin d → ℝ)))) := by
  let μ : Fin (n + 1) → Measure (Fin d → ℝ) := fun i ↦
    (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin d → ℝ) k
  have hMapEq :
      (Measure.pi μ).map e = (μ k).prod (Measure.pi fun i : Fin n ↦ μ (k.succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ k).map_eq
  have hk : μ k = Measure.dirac (0 : Fin d → ℝ) := by
    -- Proof comment: the duplicated adjacent gap has law `ν 0`, which is the Dirac mass at `0`.
    have hzeroProb : ν 0 = diracProba (0 : Fin d → ℝ) := by
      simpa [ProbabilityMeasure.one_eq_diracProba] using hν.zero_eq
    have hzero :
        (ν 0 : Measure (Fin d → ℝ)) = Measure.dirac (0 : Fin d → ℝ) := by
      exact congrArg (fun ρ : ProbabilityMeasure (Fin d → ℝ) ↦ (ρ : Measure (Fin d → ℝ))) hzeroProb
    simpa [μ, hdup] using hzero
  have htail :
      (fun i : Fin n ↦ μ (k.succAbove i)) =
        (fun i : Fin n ↦
          (ν ((deleteAdjacentDuplicateTimes times k) i.succ -
              (deleteAdjacentDuplicateTimes times k) i.castSucc) :
            Measure (Fin d → ℝ))) := by
    -- Proof comment: all surviving increment laws are read from the shortened grid.
    funext i
    simp [μ, deleteAdjacentDuplicateTimes_succ, deleteAdjacentDuplicateTimes_castSucc _ _ hdup]
  rw [hMapEq, hk, htail]

/-- Helper for Theorem 14.47: the strict-grid increment product law extends to monotone anchored
grids by repeatedly deleting adjacent duplicate times. -/
private theorem canonicalIncrementVector_map_eq_pi_of_monotone_start_zero
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (hν : IsConvolutionSemigroupWithZero ν) (x : Fin d → ℝ)
    {P : Measure (NNReal → Fin d → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
              times htimes ∘ₘ Measure.dirac x) :
    ∀ {n : ℕ} (times : Fin (n + 1) → NNReal), times 0 = 0 → Monotone times →
      P.map (incrementVector (d := d) times) =
        Measure.pi (fun i : Fin n ↦
          (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))) := by
  letI : IsProbabilityMeasure P :=
    (canonicalPathMeasureStart_hasLaw ν x hP_fdim).isProbabilityMeasure
  intro n times hzero htimes
  induction n with
  | zero =>
      -- Proof comment: an anchored grid with no increments has the trivial empty product law.
      have hconst :
          incrementVector (d := d) times =
            fun _ : NNReal → Fin d → ℝ ↦ (isEmptyElim : Fin 0 → Fin d → ℝ) := by
        funext ω i
        exact Fin.elim0 i
      rw [hconst, Measure.map_const]
      simpa using
        (Measure.pi_of_empty
          (fun i : Fin 0 ↦
            (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ)))
          (isEmptyElim : Fin 0 → Fin d → ℝ)).symm
  | succ n ih =>
      by_cases hstrict : StrictMono times
      · -- Proof comment: once the grid is strict, the previously proved strict-grid theorem
        -- closes the argument.
        exact canonicalIncrementVector_map_eq_pi_of_strict_start_zero ν x hP_fdim times hzero hstrict
      · have hnotlt : ¬ ∀ i : Fin (n + 1), times i.castSucc < times i.succ := by
          simpa [Fin.strictMono_iff_lt_succ] using hstrict
        push Not at hnotlt
        obtain ⟨k, hk⟩ := hnotlt
        have hdup : times k.castSucc = times k.succ := by
          -- Proof comment: on a monotone grid, the first failure of strict increase is an
          -- adjacent equality.
          exact le_antisymm (htimes Fin.castSucc_lt_succ.le) hk
        let times' : Fin (n + 1) → NNReal := deleteAdjacentDuplicateTimes times k
        have hzero' : times' 0 = 0 := deleteAdjacentDuplicateTimes_zero hzero
        have htimes' : Monotone times' := deleteAdjacentDuplicateTimes_monotone htimes
        have hshort :
            P.map (incrementVector (d := d) times') =
              Measure.pi (fun i : Fin n ↦
                (ν (times' i.succ - times' i.castSucc) : Measure (Fin d → ℝ))) :=
          ih times' hzero' htimes'
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin d → ℝ) k
        have hpair :
            (P.map (incrementVector (d := d) times)).map e =
              (P.map (incrementVector (d := d) times')).map (Prod.mk (0 : Fin d → ℝ)) := by
          -- Proof comment: separating the duplicated increment coordinate exposes a deterministic
          -- zero and the shortened increment vector.
          calc
            (P.map (incrementVector (d := d) times)).map e =
                P.map (fun ω ↦ e (incrementVector (d := d) times ω)) := by
                  simpa [Function.comp] using
                    (Measure.map_map e.measurable
                      (incrementVector_measurable (d := d) times))
            _ = P.map (fun ω ↦ (0, incrementVector (d := d) times' ω)) := by
                  congr 1
                  exact incrementVector_piFinSuccAbove_of_adjacentDuplicate (d := d) times k hdup
            _ = (P.map (incrementVector (d := d) times')).map (Prod.mk (0 : Fin d → ℝ)) := by
                  simpa [Function.comp] using
                    (Measure.map_map
                      (μ := P)
                      (f := incrementVector (d := d) times')
                      (g := Prod.mk (0 : Fin d → ℝ))
                      ((measurable_const).prodMk measurable_id)
                      (incrementVector_measurable (d := d) times')).symm
        have hpairPi :
            (Measure.pi (fun i : Fin (n + 1) ↦
              (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ)))).map e =
                (Measure.pi (fun i : Fin n ↦
                  (ν (times' i.succ - times' i.castSucc) : Measure (Fin d → ℝ)))).map
                    (Prod.mk (0 : Fin d → ℝ)) := by
          -- Proof comment: the increment product law undergoes the same zero-insertion
          -- normalization.
          calc
            (Measure.pi (fun i : Fin (n + 1) ↦
              (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ)))).map e =
                (Measure.dirac (0 : Fin d → ℝ)).prod
                  (Measure.pi (fun i : Fin n ↦
                    (ν (times' i.succ - times' i.castSucc) : Measure (Fin d → ℝ)))) := by
                      simpa [times'] using
                        incrementLawPi_map_piFinSuccAbove_of_adjacentDuplicate
                          (d := d) ν hν times k hdup
            _ =
                (Measure.pi (fun i : Fin n ↦
                  (ν (times' i.succ - times' i.castSucc) : Measure (Fin d → ℝ)))).map
                    (Prod.mk (0 : Fin d → ℝ)) := by
                      rw [Measure.dirac_prod]
        -- Proof comment: compare both image laws after deleting the duplicated coordinate and then
        -- map back through the measurable equivalence `e`.
        calc
          P.map (incrementVector (d := d) times) =
              ((P.map (incrementVector (d := d) times)).map e).map e.symm := by
                simpa [e] using
                  (MeasurableEquiv.map_map_symm
                    (ν := P.map (incrementVector (d := d) times)) e.symm).symm
          _ = (((P.map (incrementVector (d := d) times')).map (Prod.mk (0 : Fin d → ℝ))).map
                e.symm) := by
                  rw [hpair]
          _ =
              (((Measure.pi (fun i : Fin n ↦
                (ν (times' i.succ - times' i.castSucc) : Measure (Fin d → ℝ)))).map
                  (Prod.mk (0 : Fin d → ℝ))).map e.symm) := by
                    rw [hshort]
          _ =
              (((Measure.pi (fun i : Fin (n + 1) ↦
                (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ)))).map e)).map
                  e.symm := by
                    rw [hpairPi.symm]
          _ =
              Measure.pi (fun i : Fin (n + 1) ↦
                (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))) := by
                  simpa [e] using
                    (MeasurableEquiv.map_map_symm
                      (ν := Measure.pi (fun i : Fin (n + 1) ↦
                        (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))))
                      e.symm)

/-- Helper for Theorem 14.47: collapsing the singleton-history `comap` against the deterministic
initial history recovers the original kernel. -/
private theorem comap_zeroHistory_comp_initialHistory_eq
    {d : ℕ} (κ : Kernel (Fin d → ℝ) (Fin d → ℝ)) :
    Kernel.comap κ
        (fun z : Π _ : Finset.Iic 0, Fin d → ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le 0)⟩)
        (measurable_zeroIicCoordinate (d := d) (n := 0)) ∘ₖ
      Kernel.deterministic initialHistory measurable_initialHistory =
        κ := by
  -- Proof comment: evaluating the singleton-history projection after `initialHistory` gives the
  -- original starting state, so the composed kernel acts exactly like `κ`.
  ext x s hs
  rw [Kernel.comp_deterministic_eq_comap]
  rw [Kernel.comap_apply' _ measurable_initialHistory x s]
  rw [Kernel.comap_apply' _ (measurable_zeroIicCoordinate (d := d) (n := 0)) (initialHistory x) s]
  simp [initialHistory]

/-- Helper for Theorem 14.47: on a two-point ordered chain, the unique history step kernel is the
translated row kernel read from the singleton-history coordinate. -/
private theorem consistentFamilyHistoryKernels_twoPoint_zero_eq
    {d : ℕ}
    (K : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin d → ℝ) (Fin d → ℝ))
    (j : Π _ : Finset.Iic 1, NNReal) (hj : StrictMono j)
    (h01 : j ⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ < j ⟨1, Finset.mem_Iic.2 le_rfl⟩) :
    consistentFamilyHistoryKernels K j hj 0 =
      Kernel.comap (K h01)
        (fun z : Π _ : Finset.Iic 0, Fin d → ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le 0)⟩)
        (measurable_zeroIicCoordinate (d := d) (n := 0)) := by
  have hproof :
      hj (show (⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ : Finset.Iic 1) <
          ⟨1, Finset.mem_Iic.2 le_rfl⟩ from Nat.lt_succ_self 0) = h01 := by
    apply Subsingleton.elim
  -- Proof comment: at history length `0`, the branch `m < 1` is active and the final-prefix
  -- coordinate is also the unique history coordinate.
  simp [consistentFamilyHistoryKernels, hproof]

/-- Helper for Theorem 14.47: on the ordered two-point chain, every history kernel row is
Markov once the underlying transition kernels are Markov. -/
private theorem consistentFamilyHistoryKernels_twoPoint_isMarkov
    {d : ℕ}
    (K : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin d → ℝ) (Fin d → ℝ))
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (j : Π _ : Finset.Iic 1, NNReal) (hj : StrictMono j) :
    ∀ m, IsMarkovKernel (consistentFamilyHistoryKernels K j hj m) := by
  intro m
  cases m with
  | zero =>
      have h01idx :
          (⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ : Finset.Iic 1) <
            ⟨1, Finset.mem_Iic.2 le_rfl⟩ := by
        decide
      let h01 :
          j ⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ <
            j ⟨1, Finset.mem_Iic.2 le_rfl⟩ := hj h01idx
      letI : IsMarkovKernel (K h01) := hMarkov h01
      -- Proof comment: at the unique active step, the two-point history kernel is exactly the
      -- terminal transition read from the singleton history coordinate.
      rw [consistentFamilyHistoryKernels_twoPoint_zero_eq K j hj h01]
      infer_instance
  | succ m =>
      have hnot : ¬ Nat.succ m < 1 := by
        exact Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.zero_le m))
      -- Proof comment: beyond the unique positive step, the history kernels are deterministic
      -- projections back to the initial state.
      simpa [consistentFamilyHistoryKernels, hnot] using
        (inferInstance :
          IsMarkovKernel
            (Kernel.deterministic
              (fun z : Π _ : Finset.Iic (Nat.succ m), Fin d → ℝ ↦
                z ⟨0, Finset.mem_Iic.2 (Nat.zero_le (Nat.succ m))⟩)
              (measurable_zeroIicCoordinate (d := d) (n := Nat.succ m))))

/-- Helper for Theorem 14.47: under the two-point finite-dimensional kernel `(0, t)`, the last
coordinate has the translated increment law `x ↦ δ_x ∗ ν_t`. -/
private theorem markovSemigroupFiniteDimKernel_twoPoint_last
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ)) {t : NNReal} (ht : 0 < t) :
    (markovSemigroupFiniteDimKernelLocal
        (fun s ↦ dirac_convolution_kernel (ν s : Measure (Fin d → ℝ)))
        (twoPointTimes t) (twoPointTimes_strictMono ht)).map (Function.eval 1) =
      dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)) := by
  let K : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin d → ℝ) (Fin d → ℝ) :=
    fun {s t} _ ↦ dirac_convolution_kernel (ν (t - s) : Measure (Fin d → ℝ))
  let j : Π _ : Finset.Iic 1, NNReal := orderedTimeChainLocal (twoPointTimes t)
  let hj : StrictMono j := orderedTimeChainLocal_strictMono (twoPointTimes_strictMono ht)
  let last : (Π _ : Finset.Iic 1, Fin d → ℝ) → Fin d → ℝ :=
    fun z ↦ z ⟨1, Finset.mem_Iic.2 le_rfl⟩
  have h01idx :
      (⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ : Finset.Iic 1) <
        ⟨1, Finset.mem_Iic.2 le_rfl⟩ := by
    decide
  have h01 :
      j ⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ <
        j ⟨1, Finset.mem_Iic.2 le_rfl⟩ := hj h01idx
  have hkernel :
      (consistentFamilyFiniteDimensionalKernel K j hj).map last =
        dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)) := by
    -- Proof comment: on a two-point ordered history there is exactly one translated step, so the
    -- last coordinate is sampled from the one-step translated kernel.
    letI : ∀ m, IsMarkovKernel (consistentFamilyHistoryKernels K j hj m) :=
      consistentFamilyHistoryKernels_twoPoint_isMarkov K
        (fun {_ _} _ ↦ inferInstance) j hj
    rw [consistentFamilyFiniteDimensionalKernel, Kernel.map_comp]
    rw [consistentFamilyHistoryTraj]
    have htraj :
        (((ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ Fin d → ℝ)
            (κ := consistentFamilyHistoryKernels K j hj)
            0 1) :
            Kernel (Π _ : Finset.Iic 0, Fin d → ℝ) (Π _ : Finset.Iic 1, Fin d → ℝ)).map last) =
          Kernel.comap (K h01)
            (fun z : Π _ : Finset.Iic 0, Fin d → ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le 0)⟩)
            (measurable_zeroIicCoordinate (d := d) (n := 0)) := by
      simpa [last] using
        (ProbabilityTheory.Kernel.map_partialTraj_succ_self
          (X := fun _ : ℕ ↦ Fin d → ℝ) (κ := consistentFamilyHistoryKernels K j hj) 0)
    rw [htraj]
    -- Proof comment: on a singleton history, the last coordinate is the unique history value, so
    -- the comap collapses to the identity on the one-step kernel.
    rw [comap_zeroHistory_comp_initialHistory_eq (d := d) (κ := K h01)]
    simpa [K, j, orderedTimeChainLocal, twoPointTimes, iicEquivFinLocal, tsub_zero] using
      rfl
  -- Proof comment: after reindexing the ordered two-point history back to `Fin 2`, the last
  -- coordinate is still the last state.
  rw [markovSemigroupFiniteDimKernelLocal]
  rw [← Kernel.map_comp_right
    (κ := consistentFamilyFiniteDimensionalKernel K j hj)
    (f := fun z : Π _ : Finset.Iic 1, Fin d → ℝ ↦
      fun i : Fin 2 ↦ z ((iicEquivFinLocal 1).symm i))
    (g := Function.eval 1)
    (hf := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact measurable_pi_apply ((iicEquivFinLocal 1).symm i))
    (hg := measurable_pi_apply 1)]
  rw [reindexTwoPoint_last]
  exact hkernel

/-- Helper for Theorem 14.47: every one-time canonical marginal has the translated convolution
law `δ_x ∗ ν_t`. -/
private theorem canonicalPathMeasure_coordinate_hasLaw
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (hν : IsConvolutionSemigroupWithZero ν) (x : Fin d → ℝ)
    {P : Measure (NNReal → Fin d → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
              times htimes ∘ₘ Measure.dirac x)
    (t : NNReal) :
    HasLaw (Function.eval t) (Measure.dirac x ∗ (ν t : Measure (Fin d → ℝ))) P := by
  by_cases ht : t = 0
  · have hzero :
        Measure.dirac x ∗ (ν 0 : Measure (Fin d → ℝ)) = Measure.dirac x := by
      rw [hν.zero_eq, ProbabilityMeasure.one_eq_diracProba]
      exact Measure.conv_dirac_zero (Measure.dirac x)
    -- Proof comment: at time `0`, the coordinate law is the deterministic start law.
    rw [ht]
    rw [hzero]
    exact canonicalPathMeasureStart_hasLaw ν x hP_fdim
  · have htpos : 0 < t := by
      exact pos_iff_ne_zero.mpr ht
    have hfdim :=
      hP_fdim (twoPointTimes t) rfl (twoPointTimes_strictMono htpos)
    have hlastLaw :
        HasLaw
          (Function.eval 1)
          (((markovSemigroupFiniteDimKernelLocal
              (fun s ↦ dirac_convolution_kernel (ν s : Measure (Fin d → ℝ)))
              (twoPointTimes t) (twoPointTimes_strictMono htpos)).map (Function.eval 1)) ∘ₘ
            Measure.dirac x)
          (P.map (finiteDimensionalProjection (twoPointTimes t))) := by
      refine ⟨(measurable_pi_apply 1).aemeasurable, ?_⟩
      -- Proof comment: push the two-point marginal identity forward to its last coordinate.
      calc
        (P.map (finiteDimensionalProjection (twoPointTimes t))).map (Function.eval 1)
            = ((markovSemigroupFiniteDimKernelLocal
                (fun s ↦ dirac_convolution_kernel (ν s : Measure (Fin d → ℝ)))
                (twoPointTimes t) (twoPointTimes_strictMono htpos) ∘ₘ
                  Measure.dirac x)).map (Function.eval 1) := by
                rw [hfdim]
        _ =
            ((markovSemigroupFiniteDimKernelLocal
                (fun s ↦ dirac_convolution_kernel (ν s : Measure (Fin d → ℝ)))
                (twoPointTimes t) (twoPointTimes_strictMono htpos)).map
              (Function.eval 1)) ∘ₘ Measure.dirac x := by
                rw [Measure.map_comp _ _ (measurable_pi_apply 1)]
    have hlastMeasure :
        (((markovSemigroupFiniteDimKernelLocal
            (fun s ↦ dirac_convolution_kernel (ν s : Measure (Fin d → ℝ)))
            (twoPointTimes t) (twoPointTimes_strictMono htpos)).map (Function.eval 1)) ∘ₘ
          Measure.dirac x) =
          Measure.dirac x ∗ (ν t : Measure (Fin d → ℝ)) := by
      -- Proof comment: evaluating the two-point last-coordinate kernel at the Dirac initial law
      -- gives the translated increment law `δ_x ∗ ν_t`.
      rw [Measure.dirac_bind (Kernel.measurable _) x]
      rw [markovSemigroupFiniteDimKernel_twoPoint_last ν htpos]
      simp [dirac_convolution_kernel_apply]
    have htupleLaw :
        HasLaw
          (Function.eval 1)
          (Measure.dirac x ∗ (ν t : Measure (Fin d → ℝ)))
          (P.map (finiteDimensionalProjection (twoPointTimes t))) := by
      rw [hlastMeasure] at hlastLaw
      exact hlastLaw
    -- Proof comment: compose the last-coordinate law with the two-point projection and identify
    -- the resulting observable with `ω ↦ ω t`.
    have hprojLaw :
        HasLaw
          ((Function.eval 1) ∘ finiteDimensionalProjection (twoPointTimes t))
          (Measure.dirac x ∗ (ν t : Measure (Fin d → ℝ)))
          P :=
      HasLaw.comp htupleLaw
        ⟨(measurable_finiteDimensionalProjection (twoPointTimes t)).aemeasurable, rfl⟩
    simpa [finiteDimensionalProjection_twoPoint_last] using hprojLaw

/-- Helper for Theorem 14.47: the anchored increment `[0, t]` under the canonical path law has
law `ν t`. -/
private theorem canonicalPathMeasure_anchoredIncrement_hasLaw
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (hν : IsConvolutionSemigroupWithZero ν) (x : Fin d → ℝ)
    {P : Measure (NNReal → Fin d → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
              times htimes ∘ₘ Measure.dirac x)
    (t : NNReal) :
    HasLaw
      (fun ω : NNReal → Fin d → ℝ ↦ ω t - ω 0)
      (ν t : Measure (Fin d → ℝ))
      P := by
  letI : IsProbabilityMeasure P := (canonicalPathMeasureStart_hasLaw ν x hP_fdim).isProbabilityMeasure
  by_cases ht : t = 0
  · -- Proof comment: the anchored increment over `[0, 0]` is identically zero.
    simpa [ht, hν.zero_eq, ProbabilityMeasure.one_eq_diracProba] using
      (selfIncrement_hasLaw_diracZero (d := d) (P := P) 0)
  · have hcoord := canonicalPathMeasure_coordinate_hasLaw ν hν x hP_fdim t
    have hstart := canonicalPathMeasureStart_hasLaw ν x hP_fdim
    have hzero_ae : ∀ᵐ ω ∂P, ω 0 = x := by
      exact (hstart.ae_iff (p := fun y : Fin d → ℝ ↦ y = x)
        (measurable_id.eq measurable_const)).2 (by simp)
    have htranslate :
        HasLaw
          (fun y : Fin d → ℝ ↦ y - x)
          (ν t : Measure (Fin d → ℝ))
          (Measure.dirac x ∗ (ν t : Measure (Fin d → ℝ))) := by
      refine ⟨(measurable_id.sub measurable_const).aemeasurable, ?_⟩
      -- Proof comment: `δ_x ∗ ν_t` is the translate of `ν_t` by `x`, so subtracting `x`
      -- recovers the original increment law.
      rw [Measure.dirac_conv]
      have hcancel :
          Measure.map (fun y : Fin d → ℝ ↦ y - x)
              (Measure.map (fun y : Fin d → ℝ ↦ x + y) (ν t : Measure (Fin d → ℝ))) =
            (ν t : Measure (Fin d → ℝ)) := by
        have hcomp :
            (fun y : Fin d → ℝ ↦ y - x) ∘ (fun y : Fin d → ℝ ↦ x + y) = id := by
          funext y
          ext i
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        rw [Measure.map_map
          (μ := (ν t : Measure (Fin d → ℝ)))
          (f := fun y : Fin d → ℝ ↦ x + y)
          (g := fun y : Fin d → ℝ ↦ y - x)
          (measurable_id.sub measurable_const)
          (measurable_const.add measurable_id)]
        simpa [hcomp] using (Measure.map_id (μ := (ν t : Measure (Fin d → ℝ))))
      simpa using hcancel
    have hshifted :
        HasLaw
          (fun ω : NNReal → Fin d → ℝ ↦ ω t - x)
          (ν t : Measure (Fin d → ℝ))
          P :=
      HasLaw.comp htranslate hcoord
    have hcongr :
        (fun ω : NNReal → Fin d → ℝ ↦ ω t - ω 0) =ᵐ[P]
          (fun ω : NNReal → Fin d → ℝ ↦ ω t - x) := by
      -- Proof comment: the time-zero coordinate is almost surely equal to the deterministic start
      -- value `x`.
      filter_upwards [hzero_ae] with ω hω
      simp [hω]
    exact hshifted.congr hcongr

/-- Helper for Theorem 14.47: for `0 < s < t`, the canonical increment over `[s, t]` has law
`ν (t - s)`. -/
private theorem intervalIncrement_hasLaw_of_lt
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ)) (x : Fin d → ℝ)
    {P : Measure (NNReal → Fin d → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
              times htimes ∘ₘ Measure.dirac x)
    {s t : NNReal} (hs : 0 < s) (hst : s < t) :
    HasLaw
      (fun ω : NNReal → Fin d → ℝ ↦ ω t - ω s)
      (ν (t - s) : Measure (Fin d → ℝ))
      P := by
  let times : Fin 3 → NNReal := threePointTimes s t
  let htimes : StrictMono times := threePointTimes_strictMono hs hst
  let K : ∀ ⦃u v : NNReal⦄, u < v → Kernel (Fin d → ℝ) (Fin d → ℝ) :=
    fun {u v} _ ↦ dirac_convolution_kernel (ν (v - u) : Measure (Fin d → ℝ))
  let j : Π _ : Finset.Iic 2, NNReal := orderedTimeChainLocal times
  let hj : StrictMono j := orderedTimeChainLocal_strictMono htimes
  let jPrefix : Π _ : Finset.Iic 1, NNReal := fun i ↦
    j ⟨i.1, Finset.mem_Iic.2
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ 1))⟩
  let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
  let lastPrefix : (Π _ : Finset.Iic 1, Fin d → ℝ) → Fin d → ℝ := fun z ↦
    z ⟨1, Finset.mem_Iic.2 le_rfl⟩
  let hLastIdx :
      (⟨1, Finset.mem_Iic.2 (Nat.le_succ 1)⟩ : Finset.Iic 2) <
        ⟨2, Finset.mem_Iic.2 le_rfl⟩ := by
          decide
  let hLast :
      j ⟨1, Finset.mem_Iic.2 (Nat.le_succ 1)⟩ <
        j ⟨2, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
  let gap : (Fin 3 → Fin d → ℝ) → Fin d → ℝ := fun z ↦ z 2 - z 1
  let orderedGap : (Π _ : Finset.Iic 2, Fin d → ℝ) → Fin d → ℝ := fun z ↦
    z ⟨2, Finset.mem_Iic.2 le_rfl⟩ - z ⟨1, Finset.mem_Iic.2 (by decide : 1 ≤ 2)⟩
  let splitGap :
      ((Π _ : Finset.Iic 1, Fin d → ℝ) × (Fin d → ℝ)) → Fin d → ℝ := fun p ↦
    p.2 - p.1 ⟨1, Finset.mem_Iic.2 le_rfl⟩
  have hfdim := hP_fdim times rfl htimes
  have hsplitGapMeasurable : Measurable splitGap := by
    exact measurable_snd.sub
      ((measurable_lastIicCoordinate (d := d) (n := 1)).comp measurable_fst)
  have hgapMeasure :
      ((markovSemigroupFiniteDimKernelLocal
          (fun u ↦ dirac_convolution_kernel (ν u : Measure (Fin d → ℝ)))
          times htimes).map gap) ∘ₘ Measure.dirac x =
        (ν (t - s) : Measure (Fin d → ℝ)) := by
    rw [Measure.dirac_bind (Kernel.measurable _) x]
    rw [markovSemigroupFiniteDimKernelLocal]
    rw [← Kernel.map_comp_right
      (κ := consistentFamilyFiniteDimensionalKernel K j hj)
      (f := fun z : Π _ : Finset.Iic 2, Fin d → ℝ ↦
        fun i : Fin 3 ↦ z ((iicEquivFinLocal 2).symm i))
      (g := gap)
      (hf := by
        refine measurable_pi_lambda _ fun i ↦ ?_
        exact measurable_pi_apply ((iicEquivFinLocal 2).symm i))
      (hg := (measurable_pi_apply 2).sub (measurable_pi_apply 1))]
    have hreindex :
        gap ∘ (fun z : Π _ : Finset.Iic 2, Fin d → ℝ ↦
          fun i : Fin 3 ↦ z ((iicEquivFinLocal 2).symm i)) = orderedGap := by
      funext z
      simpa [gap, orderedGap] using congrFun reindexThreePoint_increment z
    rw [hreindex]
    calc
      ((consistentFamilyFiniteDimensionalKernel K j hj).map orderedGap) x
          = Measure.map orderedGap ((consistentFamilyFiniteDimensionalKernel K j hj) x) := by
              exact
                Kernel.map_apply
                  (consistentFamilyFiniteDimensionalKernel K j hj)
                  ((measurable_pi_apply _).sub (measurable_pi_apply _))
                  x
      _ =
          Measure.map
              (splitGap ∘ succHistoryEquivLocal (d := d) 1)
              ((consistentFamilyFiniteDimensionalKernel K j hj) x) := by
                exact congrArg
                  (fun f : (Π _ : Finset.Iic 2, Fin d → ℝ) → Fin d → ℝ ↦
                    Measure.map f ((consistentFamilyFiniteDimensionalKernel K j hj) x))
                  (threePointOrderedGap_eq_gapAfterSplit (d := d).symm)
      _ = Measure.map splitGap
            (Measure.map (succHistoryEquivLocal (d := d) 1)
              ((consistentFamilyFiniteDimensionalKernel K j hj) x)) := by
              rw [← Measure.map_map hsplitGapMeasurable
                (succHistoryEquivLocal (d := d) 1).measurable]
      _ =
          Measure.map splitGap
            ((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
              Kernel.comap (K hLast) lastPrefix
                (measurable_lastIicCoordinate (d := d) (n := 1))) := by
              exact congrArg
                (fun m : Measure ((Π _ : Finset.Iic 1, Fin d → ℝ) × (Fin d → ℝ)) ↦
                  Measure.map splitGap m)
                (consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
                  (d := d) (n := 1) (K := K)
                  (hSFinite := fun {_ _} _ ↦ by infer_instance)
                  (j := j) (hj := hj) x)
      _ = (ν (t - s) : Measure (Fin d → ℝ)) := by
            have hKernelMarkov :
                IsMarkovKernel (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) := by
              refine consistentFamilyFiniteDimensionalKernel_isMarkov K ?_ _ _
              intro u v huv
              infer_instance
            letI : IsMarkovKernel (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) :=
              hKernelMarkov
            letI :
                IsProbabilityMeasure
                  ((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x) :=
              inferInstance
            simpa [K, j, orderedTimeChainLocal, times, threePointTimes, iicEquivFinLocal,
              lastPrefix] using
              (compProd_map_sub_lastPrefix_eq
                (d := d) (n := 1) (ν := ν (t - s))
                (μ := consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x)
                (lastPrefix := lastPrefix)
                (hlastPrefixMeasurable := by
                  simpa [lastPrefix] using measurable_lastIicCoordinate (d := d) (n := 1)))
  have htupleLaw :
      HasLaw
        gap
        (ν (t - s) : Measure (Fin d → ℝ))
        (P.map (finiteDimensionalProjection times)) := by
    refine ⟨((measurable_pi_apply 2).sub (measurable_pi_apply 1)).aemeasurable, ?_⟩
    calc
      (P.map (finiteDimensionalProjection times)).map gap
          = (((markovSemigroupFiniteDimKernelLocal
                (fun u ↦ dirac_convolution_kernel (ν u : Measure (Fin d → ℝ)))
                times htimes).map gap) ∘ₘ Measure.dirac x) := by
                rw [hfdim, Measure.map_comp _ _ ((measurable_pi_apply 2).sub (measurable_pi_apply 1))]
      _ = (ν (t - s) : Measure (Fin d → ℝ)) := hgapMeasure
  have hprojLaw :
      HasLaw
        (gap ∘ finiteDimensionalProjection times)
        (ν (t - s) : Measure (Fin d → ℝ))
        P :=
    HasLaw.comp htupleLaw
      ⟨(measurable_finiteDimensionalProjection times).aemeasurable, rfl⟩
  simpa [gap, times, finiteDimensionalProjection_threePoint_increment] using hprojLaw

/-- Helper for Theorem 14.47: every canonical increment over `[s,t]` has the prescribed law
`ν (t - s)`. -/
private theorem canonicalPathMeasure_increment_hasLaw
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (hν : IsConvolutionSemigroupWithZero ν) (x : Fin d → ℝ)
    {P : Measure (NNReal → Fin d → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
              times htimes ∘ₘ Measure.dirac x)
    {s t : NNReal} (hst : s ≤ t) :
    HasLaw
      (fun ω : NNReal → Fin d → ℝ ↦ ω t - ω s)
      (ν (t - s) : Measure (Fin d → ℝ))
      P := by
  letI : IsProbabilityMeasure P := (canonicalPathMeasureStart_hasLaw ν x hP_fdim).isProbabilityMeasure
  rcases lt_or_eq_of_le hst with hst' | rfl
  · by_cases hs : s = 0
    · -- Proof comment: when the interval starts at `0`, this is exactly the anchored increment
      -- law already proved above.
      subst hs
      simpa using canonicalPathMeasure_anchoredIncrement_hasLaw ν hν x hP_fdim t
    · -- Proof comment: for a genuine interior interval `0 < s < t`, specialize the strict
      -- three-point computation from `intervalIncrement_hasLaw_of_lt`.
      exact intervalIncrement_hasLaw_of_lt ν x hP_fdim (pos_iff_ne_zero.mpr hs) hst'
  · -- Proof comment: a zero-length increment is identically `0`, and the semigroup starts at the
    -- Dirac mass at `0`.
    simpa [hν.zero_eq, ProbabilityMeasure.one_eq_diracProba] using
      (selfIncrement_hasLaw_diracZero (d := d) (P := P) s)

/-- Helper for Theorem 14.47: the canonical path measure has stationary increment laws. -/
private theorem canonicalPathMeasure_hasStationaryIncrementLaws
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (hν : IsConvolutionSemigroupWithZero ν) (x : Fin d → ℝ)
    {P : Measure (NNReal → Fin d → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
              times htimes ∘ₘ Measure.dirac x) :
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
        (fun ω : NNReal → Fin d → ℝ ↦ ω ((s + t) + r) - ω (t + r))
        (ν (((s + t) + r) - (t + r)) : Measure (Fin d → ℝ))
        P := by
    -- Proof comment: the shifted increment over `[(t + r), (s + t) + r]` has lag `s`.
    simpa [add_assoc, add_left_comm, add_comm] using
      (canonicalPathMeasure_increment_hasLaw (ν := ν) hν x hP_fdim (s := t + r)
        (t := (s + t) + r) hleft_le)
  have hrightRaw :
      HasLaw
        (fun ω : NNReal → Fin d → ℝ ↦ ω (s + r) - ω r)
        (ν ((s + r) - r) : Measure (Fin d → ℝ))
        P := by
    -- Proof comment: the anchored translated increment over `[r, s + r]` has the same lag `s`.
    simpa [add_assoc, add_left_comm, add_comm] using
      (canonicalPathMeasure_increment_hasLaw (ν := ν) hν x hP_fdim (s := r)
        (t := s + r) hright_le)
  have hleftGap : ((s + t) + r) - (t + r) = s := by
    rw [add_assoc, add_tsub_cancel_right]
  have hrightGap : (s + r) - r = s := by
    rw [add_tsub_cancel_right]
  have hleft :
      HasLaw
        (fun ω : NNReal → Fin d → ℝ ↦ ω ((s + t) + r) - ω (t + r))
        (ν s : Measure (Fin d → ℝ))
        P := by
    rwa [hleftGap] at hleftRaw
  have hright :
      HasLaw
        (fun ω : NNReal → Fin d → ℝ ↦ ω (s + r) - ω r)
        (ν s : Measure (Fin d → ℝ))
        P := by
    rwa [hrightGap] at hrightRaw
  exact hleft.identDistrib hright

/-- Helper for Theorem 14.47: the canonical path measure has independent increments. -/
private theorem canonicalPathMeasure_hasIndepIncrements
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (hν : IsConvolutionSemigroupWithZero ν) (x : Fin d → ℝ)
    {P : Measure (NNReal → Fin d → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
              times htimes ∘ₘ Measure.dirac x) :
    HasIndepIncrements Function.eval P := by
  classical
  letI : IsProbabilityMeasure P := (canonicalPathMeasureStart_hasLaw ν x hP_fdim).isProbabilityMeasure
  rw [hasIndepIncrements_iff_nat]
  intro t ht
  -- Route correction: package each monotone `ℕ`-grid through a finite anchored prefix, then use
  -- the monotone zero-start finite-grid law and restrict back to the requested finite family of
  -- increment indices.
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
        P.map (incrementVector (d := d) times) =
          Measure.pi (fun i : Fin (N + 1) ↦
            (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))) :=
      canonicalIncrementVector_map_eq_pi_of_monotone_start_zero ν hν x hP_fdim times
        (by simp [times]) htimes
    have hcoord (i : Fin (N + 1)) :
        P.map (fun ω : NNReal → Fin d → ℝ ↦ incrementVector (d := d) times ω i) =
            (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ)) := by
      calc
        P.map (fun ω : NNReal → Fin d → ℝ ↦ incrementVector (d := d) times ω i) =
            (P.map (incrementVector (d := d) times)).map (Function.eval i) := by
              symm
              simpa [Function.comp] using
                (Measure.map_map
                  (μ := P)
                  (f := incrementVector (d := d) times)
                  (g := Function.eval i)
                  (measurable_pi_apply i)
                  (incrementVector_measurable (d := d) times))
        _ = (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ)) := by
              simpa [Measure.pi_map_eval] using
                congrArg
                  (fun m : Measure (Fin (N + 1) → Fin d → ℝ) ↦ m.map (Function.eval i))
                  hgrid
    have hfull :
        iIndepFun
          (fun i : Fin (N + 1) ↦ fun ω : NNReal → Fin d → ℝ ↦
            incrementVector (d := d) times ω i)
          P := by
      -- Proof comment: the finite-grid product-law equality is exactly the `iIndepFun` criterion
      -- on the anchored increment vector.
      refine (iIndepFun_iff_map_fun_eq_pi_map ?_).2 ?_
      · intro i
        exact ((measurable_pi_apply i).comp (incrementVector_measurable (d := d) times)).aemeasurable
      · calc
          P.map (incrementVector (d := d) times) =
              Measure.pi (fun i : Fin (N + 1) ↦
                (ν (times i.succ - times i.castSucc) : Measure (Fin d → ℝ))) := hgrid
          _ = Measure.pi (fun i : Fin (N + 1) ↦
                P.map (fun ω : NNReal → Fin d → ℝ ↦ incrementVector (d := d) times ω i)) := by
                congr 1
                funext i
                exact (hcoord i).symm
    have htail :
        iIndepFun
          (fun i : Fin N ↦ fun ω : NNReal → Fin d → ℝ ↦
            incrementVector (d := d) times ω i.succ)
          P := by
      -- Proof comment: removing the leading anchored increment preserves independence.
      exact hfull.precomp (g := Fin.succ) fun a b h ↦ by simpa using h
    let g : s → Fin N := fun x ↦
      ⟨x.1, Nat.lt_of_le_of_lt (s.le_max' x.1 x.2) (Nat.lt_succ_self _)⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      exact Fin.ext_iff.mp hab
    -- Proof comment: each requested finite family of increments is a restriction of the anchored
    -- finite-grid tail family, so it inherits independence by precomposition.
    simpa [times, g, Finset.restrict, incrementVector] using htail.precomp (g := g) hg
  · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    -- Proof comment: the empty family of increments is independent for trivial reasons.
    simpa using
      (iIndepFun.of_subsingleton
        (μ := P)
        (f := (∅ : Finset ℕ).restrict
          (fun i ω ↦ Function.eval (t (i + 1)) ω - Function.eval (t i) ω)))

/-- Theorem 14.47 (1): every convolution semigroup on `ℝ^d` is realized by the canonical process
on the path space `(ℝ^d)^{ℝ≥0}`, started from the deterministic point `x`, with stationary
independent increments and increment law `ν (t - s)` over every interval `[s,t]`. -/
theorem exists_pathMeasure_of_isConvolutionSemigroup
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (hν : IsConvolutionSemigroupWithZero ν) (x : Fin d → ℝ) :
    ∃ P : ProbabilityMeasure (NNReal → Fin d → ℝ),
      HasLaw (Function.eval 0) (Measure.dirac x) (P : Measure (NNReal → Fin d → ℝ)) ∧
        HasStationaryIndependentIncrements Function.eval (P : Measure (NNReal → Fin d → ℝ)) ∧
        ∀ ⦃s t : NNReal⦄, s ≤ t →
          HasLaw
            (fun ω : NNReal → Fin d → ℝ ↦ ω t - ω s)
            (ν (t - s) : Measure (Fin d → ℝ))
            (P : Measure (NNReal → Fin d → ℝ)) := by
  let κ : NNReal → Kernel (Fin d → ℝ) (Fin d → ℝ) :=
    fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ))
  letI : IsMarkovSemigroup κ := translatedConvolutionKernel_isMarkovSemigroup ν hν
  obtain ⟨P, hPspec, -⟩ := existsUnique_markovPathMeasure κ (Measure.dirac x)
  rcases hPspec with ⟨hP_prob, hP_fdim⟩
  let Pprob : ProbabilityMeasure (NNReal → Fin d → ℝ) := ⟨P, hP_prob⟩
  have hP_fdim' :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
              times htimes ∘ₘ Measure.dirac x := by
    intro n times hzero htimes
    simpa [κ] using hP_fdim times hzero htimes
  refine ⟨Pprob, canonicalPathMeasureStart_hasLaw ν x hP_fdim', ?_, ?_⟩
  · refine ⟨?_, canonicalPathMeasure_hasStationaryIncrementLaws ν hν x hP_fdim'⟩
    exact canonicalPathMeasure_hasIndepIncrements ν hν x hP_fdim'
  · intro s t hst
    exact canonicalPathMeasure_increment_hasLaw ν hν x hP_fdim' hst

/-- Helper for Theorem 14.47: the anchored increment `X t - X 0` has the defining law obtained
by mapping `P` through that increment observable. -/
private theorem anchoredIncrement_hasLaw
    {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (X : NNReal → Ω → Fin d → ℝ) (hX : IsStochasticProcess X) (t : NNReal) :
    HasLaw
      (fun ω ↦ X t ω - X 0 ω)
      (((ProbabilityMeasure.map P
          ((hX.measurable t).sub (hX.measurable 0)).aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ)))
      (P : Measure Ω) := by
  -- Proof comment: this is the direct `HasLaw` packaging of the measurable anchored increment.
  exact ⟨((hX.measurable t).sub (hX.measurable 0)).aemeasurable, rfl⟩

/-- Helper for Theorem 14.47: stationary increment laws transport the anchored increment law
`X t - X 0` to the shifted increment law over `[s, s + t]`. -/
private theorem shiftedIncrement_hasLaw_of_stationaryIncrementLaws
    {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (X : NNReal → Ω → Fin d → ℝ) (hX : IsStochasticProcess X)
    (hX_stat : HasStationaryIncrementLaws X (P : Measure Ω)) (s t : NNReal) :
    HasLaw
      (fun ω ↦ X (s + t) ω - X s ω)
      (((ProbabilityMeasure.map P
          ((hX.measurable t).sub (hX.measurable 0)).aemeasurable :
            ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ)))
      (P : Measure Ω) := by
  have hAnchored :
      HasLaw
        (fun ω ↦ X (t + 0) ω - X 0 ω)
        (((ProbabilityMeasure.map P
            ((hX.measurable t).sub (hX.measurable 0)).aemeasurable :
              ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ)))
        (P : Measure Ω) := by
    -- Proof comment: reuse the anchored increment law before transporting it by stationarity.
    simpa using anchoredIncrement_hasLaw P X hX t
  let hIdent :=
    hX_stat.identDistrib_increment (X := X) (μ := (P : Measure Ω)) 0 t s
  have hShifted :
      HasLaw
        (fun ω ↦ X ((t + s) + 0) ω - X (s + 0) ω)
        (((ProbabilityMeasure.map P
            ((hX.measurable t).sub (hX.measurable 0)).aemeasurable :
              ProbabilityMeasure (Fin d → ℝ)) : Measure (Fin d → ℝ)))
        (P : Measure Ω) :=
    hIdent.symm.hasLaw hAnchored
  -- Proof comment: after simplifying the translated endpoints, this is exactly the increment
  -- over `[s, s + t]`.
  simpa [add_assoc, add_left_comm, add_comm] using hShifted

/-- Helper for Theorem 14.47: the sum of the adjacent increments over `[0, s]` and `[s, s+t]`
telescopes to the anchored increment over `[0, s+t]`. -/
private theorem add_adjacentIncrements_eq_anchoredIncrement
    {d : ℕ} {Ω : Type u} (X : NNReal → Ω → Fin d → ℝ) (s t : NNReal) (ω : Ω) :
    (X s ω - X 0 ω) + (X (s + t) ω - X s ω) = X (s + t) ω - X 0 ω := by
  -- Proof comment: the middle values `X s ω` cancel after expanding the two adjacent gaps.
  abel_nf

-- Proof sketch: unpack the canonical owner `HasStationaryIndependentIncrements` into independent
-- increments and stationary increment laws, identify the law of `X_{s+t} - X_s` with
-- `X_t - X_0`, use independent increments plus `IndepFun.hasLaw_add` to obtain the convolution
-- identity, and read off the time-zero law from the zero increment.
/-- Theorem 14.47 (2): on an arbitrary probability space, the family of laws
`ν_t = law(X_t - X_0)` of a process with stationary independent increments is a convolution
semigroup on `ℝ^d`. -/
theorem incrementLaw_isConvolutionSemigroup
    {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (X : NNReal → Ω → Fin d → ℝ) (hX : IsStochasticProcess X)
    (hX_statIndep : HasStationaryIndependentIncrements X (P : Measure Ω)) :
    IsConvolutionSemigroupWithZero
      (fun t ↦
        ProbabilityMeasure.map P
          ((hX.measurable t).sub (hX.measurable 0)).aemeasurable) := by
  let ν : NNReal → ProbabilityMeasure (Fin d → ℝ) :=
    fun t ↦
      ProbabilityMeasure.map P
        ((hX.measurable t).sub (hX.measurable 0)).aemeasurable
  rcases hX_statIndep with ⟨hX_indep, hX_stat⟩
  refine
    { convolution_eq := ?_
      zero_eq := ?_ }
  · intro s t
    -- Route correction: keep the converse proof in the anchored/shifted increment-law API,
    -- rather than reopening any stale finite-grid transport route.
    -- Proof comment: split the anchored increment over `[0, s + t]` into the independent
    -- adjacent increments over `[0, s]` and `[s, s + t]`.
    have hνs :
        HasLaw
          (fun ω ↦ X s ω - X 0 ω)
          (ν s : Measure (Fin d → ℝ))
          (P : Measure Ω) := by
      simpa [ν] using anchoredIncrement_hasLaw P X hX s
    have hstep :
        HasLaw
          (fun ω ↦ X (s + t) ω - X s ω)
          (ν t : Measure (Fin d → ℝ))
          (P : Measure Ω) := by
      -- Proof comment: stationarity rewrites the translated increment `[s, s + t]` to the
      -- anchored increment `[0, t]`.
      simpa [ν, add_assoc, add_left_comm, add_comm] using
        shiftedIncrement_hasLaw_of_stationaryIncrementLaws P X hX hX_stat s t
    have hIndep :
        (fun ω ↦ X s ω - X 0 ω) ⟂ᵢ[P] (fun ω ↦ X (s + t) ω - X s ω) :=
      hX_indep.indepFun_sub_sub (r := 0) (s := s) (t := s + t) (by simp) (by simp)
    have hsum :
        HasLaw
          (fun ω ↦ (X s ω - X 0 ω) + (X (s + t) ω - X s ω))
          (((ν s : Measure (Fin d → ℝ)) ∗ (ν t : Measure (Fin d → ℝ))))
          (P : Measure Ω) :=
      ProbabilityTheory.IndepFun.hasLaw_add hνs hstep hIndep
    have hanchored :
        HasLaw
          (fun ω ↦ X (s + t) ω - X 0 ω)
          (((ν s : Measure (Fin d → ℝ)) ∗ (ν t : Measure (Fin d → ℝ))))
          (P : Measure Ω) := by
      -- Proof comment: the algebraic telescoping identity collapses the sum of adjacent
      -- increments to the anchored increment over `[0, s + t]`.
      exact hsum.congr <|
        Filter.Eventually.of_forall fun ω ↦
          (add_adjacentIncrements_eq_anchoredIncrement X s t ω).symm
    apply ProbabilityMeasure.toMeasure_injective
    simpa [ν] using hanchored.map_eq
  · -- Proof comment: the zero-time anchored increment is the constant zero random variable, so
    -- its law is the convolution unit `δ₀`.
    ext A hA
    -- Proof comment: mapping a probability measure by the constant zero function gives `δ₀`.
    simp [ProbabilityMeasure.one_eq_diracProba, hA]
