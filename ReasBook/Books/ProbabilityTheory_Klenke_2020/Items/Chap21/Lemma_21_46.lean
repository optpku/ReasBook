/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {κ : NNReal → Kernel NNReal NNReal}

/-- Helper for Lemma 21.46: restrict a continuous-time kernel family on `NNReal` to the top
additive submonoid so the Chapter 17 realization theorem applies directly. -/
def topRestrictedKernel (κ : NNReal → Kernel NNReal NNReal) :
    (⊤ : AddSubmonoid NNReal) → Kernel NNReal NNReal :=
  fun t ↦ κ t.1

/-- The kernel family `κ` has the branching-diffusion Laplace transform
`E_x[e^{-λ Y_t}] = exp (- λ x / (1 + λ t))` for all nonnegative times and Laplace parameters. -/
def HasBranchingDiffusionLaplaceTransform (κ : NNReal → Kernel NNReal NNReal) : Prop :=
  ∀ x t lam : NNReal,
    ∫ y, Real.exp (-((lam : ℝ) * (y : ℝ))) ∂ κ t x =
      Real.exp (-((lam : ℝ) * (x : ℝ)) / (((lam : ℝ) * (t : ℝ)) + 1))

/-- Helper for Lemma 21.46: evaluating the Laplace identity at `λ = 0` shows that each kernel
row has total mass `1`, hence is a probability measure. -/
lemma branchingDiffusionKernel_row_isProbabilityMeasure
    (hκ : HasBranchingDiffusionLaplaceTransform κ) (x t : NNReal) :
    IsProbabilityMeasure (κ t x) := by
  -- Proof comment: at `λ = 0`, the Laplace test function is the constant `1`, so the integral
  -- is exactly the total mass of the row measure.
  refine (MeasureTheory.isProbabilityMeasure_iff_real).2 ?_
  simpa [HasBranchingDiffusionLaplaceTransform] using hκ x t 0

/-- Helper for Lemma 21.46: every nonnegative time belongs to the top additive submonoid of
`NNReal`. -/
lemma memTopAddSubmonoid (t : NNReal) : t ∈ (⊤ : AddSubmonoid NNReal) := by
  simp

/-- Helper for Lemma 21.46: the time-zero row agrees with the Dirac law at the starting point,
so the zero-time kernel is `Kernel.id`. -/
lemma branchingDiffusionKernel_zero_eq_id
    (hκ : HasBranchingDiffusionLaplaceTransform κ) :
    κ 0 = Kernel.id := by
  -- Proof comment: compare `κ 0 x` with `δ_x` via the Chapter 15 uniqueness theorem for
  -- Laplace transforms of finite measures on `NNReal`.
  apply Kernel.ext
  intro x
  let μ : ProbabilityMeasure NNReal :=
    ⟨κ 0 x, branchingDiffusionKernel_row_isProbabilityMeasure hκ x 0⟩
  have hfinite :
      μ.toFiniteMeasure = (diracProba x : ProbabilityMeasure NNReal).toFiniteMeasure := by
    refine (MeasureTheory.FiniteMeasure.ext_iff_laplaceTransform_eq _ _).2 ?_
    intro lam
    rw [MeasureTheory.FiniteMeasure.laplaceTransform_def,
      MeasureTheory.FiniteMeasure.laplaceTransform_def]
    -- Proof comment: the prescribed Laplace transform at time `0` is exactly the Laplace
    -- transform of the Dirac mass at `x`.
    calc
      ∫ y, Real.exp (-((lam : ℝ) * (y : ℝ))) ∂(μ : Measure NNReal) =
          Real.exp (-((lam : ℝ) * (x : ℝ)) / (((lam : ℝ) * (0 : ℝ)) + 1)) := by
            simpa [μ] using hκ x 0 lam
      _ = Real.exp (-((lam : ℝ) * (x : ℝ))) := by
            simp
      _ = ∫ y, Real.exp (-((lam : ℝ) * (y : ℝ)))
            ∂((diracProba x : ProbabilityMeasure NNReal) : Measure NNReal) := by
            simpa [MeasureTheory.diracProba] using
              (integral_dirac
                (f := fun y : NNReal ↦ Real.exp (-((lam : ℝ) * (y : ℝ)))) (a := x)).symm
  have hmeasure : κ 0 x = Measure.dirac x := by
    exact congrArg (fun ρ : FiniteMeasure NNReal ↦ (ρ : Measure NNReal)) hfinite
  simpa [Kernel.id_apply] using hmeasure

/-- Helper for Lemma 21.46: the Laplace transform of the composed row
`((κ t ∘ₖ κ s) x)` has the expected `s + t` denominator. -/
lemma branchingDiffusionKernel_comp_laplace
    (hκ : HasBranchingDiffusionLaplaceTransform κ) (x s t lam : NNReal) :
    ∫ z, Real.exp (-((lam : ℝ) * (z : ℝ))) ∂((κ t ∘ₖ κ s) x) =
      Real.exp (-((lam : ℝ) * (x : ℝ)) / (((lam : ℝ) * ((s + t : NNReal) : ℝ)) + 1)) := by
  let _ : IsMarkovKernel (κ s) :=
    ⟨fun y ↦ branchingDiffusionKernel_row_isProbabilityMeasure hκ y s⟩
  let _ : IsMarkovKernel (κ t) :=
    ⟨fun y ↦ branchingDiffusionKernel_row_isProbabilityMeasure hκ y t⟩
  let lam' : NNReal := Real.toNNReal ((lam : ℝ) / (((lam : ℝ) * (t : ℝ)) + 1))
  have hlam' : (lam' : ℝ) = (lam : ℝ) / (((lam : ℝ) * (t : ℝ)) + 1) := by
    have hlam'_nonneg : 0 ≤ (lam : ℝ) / (((lam : ℝ) * (t : ℝ)) + 1) := by
      positivity
    dsimp [lam']
    exact max_eq_left hlam'_nonneg
  have hIntegrable :
      Integrable (fun z : NNReal ↦ Real.exp (-((lam : ℝ) * (z : ℝ)))) ((κ t ∘ₖ κ s) x) := by
    -- Proof comment: the Laplace test function is measurable and bounded by `1`, while the
    -- composed row is a probability measure.
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · have hmeas : Measurable (fun z : NNReal ↦ Real.exp (-((lam : ℝ) * (z : ℝ)))) := by
        fun_prop
      exact hmeas.aestronglyMeasurable
    · filter_upwards with z
      have hnonpos : -((lam : ℝ) * (z : ℝ)) ≤ 0 := by
        have hmul_nonneg : 0 ≤ (lam : ℝ) * (z : ℝ) := by
          positivity
        linarith
      have hle : Real.exp (-((lam : ℝ) * (z : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr hnonpos
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hle
  -- Proof comment: expand the kernel composition, apply the Laplace formula to the inner time
  -- `t`, then apply it again to the outer time `s` with the transformed parameter.
  calc
    ∫ z, Real.exp (-((lam : ℝ) * (z : ℝ))) ∂((κ t ∘ₖ κ s) x) =
        ∫ y, ∫ z, Real.exp (-((lam : ℝ) * (z : ℝ))) ∂κ t y ∂κ s x := by
          simpa using
            (ProbabilityTheory.Kernel.integral_comp
              (a := x) (κ := κ s) (η := κ t) hIntegrable)
    _ = ∫ y, Real.exp (-((lam : ℝ) * (y : ℝ)) / (((lam : ℝ) * (t : ℝ)) + 1)) ∂κ s x := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun y ↦ hκ y t lam
    _ = ∫ y, Real.exp (-((lam' : ℝ) * (y : ℝ))) ∂κ s x := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun y ↦ by
            rw [hlam']
            have hdenom : (((lam : ℝ) * (t : ℝ)) + 1) ≠ 0 := by
              positivity
            field_simp [hdenom]
    _ = Real.exp (-((lam' : ℝ) * (x : ℝ)) / (((lam' : ℝ) * (s : ℝ)) + 1)) := by
          simpa [lam'] using hκ x s lam'
    _ = Real.exp (-((lam : ℝ) * (x : ℝ)) / (((lam : ℝ) * ((s + t : NNReal) : ℝ)) + 1)) := by
          rw [hlam']
          congr 1
          have hdenom : (((lam : ℝ) * (t : ℝ)) + 1) ≠ 0 := by
            positivity
          have hstdenom :
              ((((lam : ℝ) / (((lam : ℝ) * (t : ℝ)) + 1)) * (s : ℝ)) + 1) ≠ 0 := by
            positivity
          rw [NNReal.coe_add]
          field_simp [hdenom, hstdenom]
          ring_nf

/-- Helper for Lemma 21.46: the Laplace transform identity for the composed row uniquely
identifies it with the row of `κ (s + t)`. -/
lemma branchingDiffusionKernel_comp_eq
    (hκ : HasBranchingDiffusionLaplaceTransform κ) (s t : NNReal) :
    κ t ∘ₖ κ s = κ (s + t) := by
  let _ : IsMarkovKernel (κ s) :=
    ⟨fun y ↦ branchingDiffusionKernel_row_isProbabilityMeasure hκ y s⟩
  let _ : IsMarkovKernel (κ t) :=
    ⟨fun y ↦ branchingDiffusionKernel_row_isProbabilityMeasure hκ y t⟩
  apply Kernel.ext
  intro x
  let μ : ProbabilityMeasure NNReal := ⟨(κ t ∘ₖ κ s) x, inferInstance⟩
  let ν : ProbabilityMeasure NNReal :=
    ⟨κ (s + t) x, branchingDiffusionKernel_row_isProbabilityMeasure hκ x (s + t)⟩
  have hfinite : μ.toFiniteMeasure = ν.toFiniteMeasure := by
    refine (MeasureTheory.FiniteMeasure.ext_iff_laplaceTransform_eq _ _).2 ?_
    intro lam
    rw [MeasureTheory.FiniteMeasure.laplaceTransform_def,
      MeasureTheory.FiniteMeasure.laplaceTransform_def]
    -- Proof comment: both finite measures have the same explicit Laplace transform, so the
    -- Chapter 15 uniqueness theorem identifies them.
    calc
      ∫ y, Real.exp (-((lam : ℝ) * (y : ℝ))) ∂(μ : Measure NNReal) =
          Real.exp (-((lam : ℝ) * (x : ℝ)) / (((lam : ℝ) * ((s + t : NNReal) : ℝ)) + 1)) := by
            simpa [μ] using branchingDiffusionKernel_comp_laplace hκ x s t lam
      _ = ∫ y, Real.exp (-((lam : ℝ) * (y : ℝ))) ∂(ν : Measure NNReal) := by
            simpa [ν] using (hκ x (s + t) lam).symm
  exact congrArg (fun ρ : FiniteMeasure NNReal ↦ (ρ : Measure NNReal)) hfinite

/-- Helper for Lemma 21.46: reindexing a process from the top additive submonoid of `NNReal`
back to `NNReal` preserves the generated history σ-algebras. -/
lemma topRestricted_generatedFiltrationSpace
    {Ω : Type u} [MeasurableSpace Ω]
    (X : (⊤ : AddSubmonoid NNReal) → Ω → NNReal) (s : NNReal) :
    generatedFiltrationSpace (fun t ω ↦ X ⟨t, memTopAddSubmonoid t⟩ ω) s =
      generatedFiltrationSpace X ⟨s, memTopAddSubmonoid s⟩ := by
  apply le_antisymm
  · refine iSup₂_le fun r hr ↦ ?_
    refine le_iSup_of_le ⟨r, memTopAddSubmonoid r⟩ ?_
    refine le_iSup_of_le hr ?_
    rfl
  · refine iSup₂_le fun q hq ↦ ?_
    have hqeq : (⟨q.1, memTopAddSubmonoid q.1⟩ : (⊤ : AddSubmonoid NNReal)) = q := by
      ext
      rfl
    refine le_iSup_of_le q.1 ?_
    refine le_iSup_of_le hq ?_
    simp [hqeq]

/-- Helper for Lemma 21.46: a realization indexed by the top additive submonoid of `NNReal`
reindexes to a realization indexed directly by `NNReal`. -/
lemma topRestrictedRealization_toFullTime
    {Ω : Type u} [MeasurableSpace Ω] {P : NNReal → ProbabilityMeasure Ω}
    {X : (⊤ : AddSubmonoid NNReal) → Ω → NNReal}
    (hX : IsMarkovProcessRealization (topRestrictedKernel κ) P X) :
    IsMarkovProcessRealization κ P (fun t ω ↦ X ⟨t, memTopAddSubmonoid t⟩ ω) := by
  -- Proof comment: every field is the corresponding top-restricted field with the time index
  -- rewritten by the canonical equivalence `t ↔ ⟨t, trivial⟩`.
  refine
    { semigroup := ?_
      measurable_process := ?_
      initial_eq := ?_
      transition_eq := ?_
      markov_property := ?_ }
  · refine
      { isMarkovKernel := ?_
        zero_eq := ?_
        comp_eq := ?_ }
    · intro t
      simpa [topRestrictedKernel] using
        hX.semigroup.isMarkovKernel ⟨t, memTopAddSubmonoid t⟩
    · simpa [topRestrictedKernel] using hX.semigroup.zero_eq
    · intro s t
      simpa [topRestrictedKernel] using
        hX.semigroup.comp_eq ⟨s, memTopAddSubmonoid s⟩ ⟨t, memTopAddSubmonoid t⟩
  · intro t
    simpa using hX.measurable_process ⟨t, memTopAddSubmonoid t⟩
  · intro x
    simpa [topRestrictedKernel] using hX.initial_eq x
  · intro x t
    simpa [topRestrictedKernel] using hX.transition_eq x ⟨t, memTopAddSubmonoid t⟩
  · intro x A hA s t
    simpa [topRestrictedKernel, topRestricted_generatedFiltrationSpace] using
      hX.markov_property x hA ⟨s, memTopAddSubmonoid s⟩ ⟨t, memTopAddSubmonoid t⟩

-- Proof sketch: first evaluate the Laplace identity at `λ = 0` to identify each `κ t x` as a
-- probability measure, then use uniqueness of Laplace transforms on `ℝ≥0` together with the
-- explicit formula to deduce the Chapman--Kolmogorov composition law `κ t ∘ₖ κ s = κ (s + t)`.
/-- Lemma 21.46 (1): a kernel family on `ℝ≥0` with Laplace transform
`E_x[e^{-λ Y_t}] = exp (- λ x / (1 + λ t))` is a Markov semigroup. -/
theorem branchingDiffusionKernel_isMarkovSemigroup
    (hκ : HasBranchingDiffusionLaplaceTransform κ) : IsMarkovSemigroup κ := by
  let hMarkovKernel : ∀ t : NNReal, IsMarkovKernel (κ t) :=
    fun t ↦ ⟨fun x ↦ branchingDiffusionKernel_row_isProbabilityMeasure hκ x t⟩
  -- Proof comment: once the rows are known to be probability measures, the semigroup structure
  -- reduces to the time-zero identity and Chapman--Kolmogorov equality proved above.
  refine
    { isMarkovKernel := hMarkovKernel
      zero_eq := branchingDiffusionKernel_zero_eq_id hκ
      comp_eq := branchingDiffusionKernel_comp_eq hκ }

-- Proof sketch: apply the standard realization theorem for Markov semigroups on the standard
-- Borel state space `ℝ≥0` to the semigroup supplied by
-- `branchingDiffusionKernel_isMarkovSemigroup`.
/-- Lemma 21.46 (2): the branching-diffusion kernel family admits a time-homogeneous Markov
process realization whose one-time marginals are exactly the kernel rows `κ t x`. -/
theorem exists_markovProcessRealization_of_branchingDiffusionKernel
    (hκ : HasBranchingDiffusionLaplaceTransform κ) :
    ∃ (Ω : Type u), ∃ _ : MeasurableSpace Ω, ∃ Y : NNReal → Ω → NNReal,
      ∃ P : NNReal → ProbabilityMeasure Ω, IsMarkovProcessRealization κ P Y := by
  let _ : IsMarkovSemigroup κ := branchingDiffusionKernel_isMarkovSemigroup hκ
  obtain ⟨Ω, mΩ, X, P, hX⟩ :=
    exists_markovProcessRealization_of_markovSemigroup (κ := topRestrictedKernel κ)
  -- Proof comment: reindex the top-submonoid realization back to `NNReal` using the canonical
  -- inclusion `t ↦ ⟨t, trivial⟩`.
  refine ⟨Ω, mΩ, (fun t ω ↦ X ⟨t, memTopAddSubmonoid t⟩ ω), P, ?_⟩
  exact topRestrictedRealization_toFullTime (κ := κ) hX

end ProbabilityTheory
