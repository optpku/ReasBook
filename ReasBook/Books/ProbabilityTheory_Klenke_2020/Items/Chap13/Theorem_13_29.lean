/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal

universe u

namespace MeasureTheory
namespace FiniteMeasure

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]

local instance : MeasurableSpace (E ⊕ Unit) := borel (E ⊕ Unit)
local instance : BorelSpace (E ⊕ Unit) := ⟨rfl⟩

/-- Helper for Theorem 13.29: restrict a bounded continuous test on `E ⊕ Unit` to the
`Sum.inl` copy of `E`. -/
private def inlRestrictedTest (g : BoundedContinuousFunction (E ⊕ Unit) ℝ) :
    BoundedContinuousFunction E ℝ :=
  { toContinuousMap := g.toContinuousMap.comp ⟨Sum.inl, continuous_inl⟩
    map_bounded' := by
      rcases g.map_bounded' with ⟨C, hC⟩
      exact ⟨C, fun x y ↦ hC (Sum.inl x) (Sum.inl y)⟩ }

/-- Helper for Theorem 13.29: extend a bounded continuous test on `E` to `E ⊕ Unit` by sending
the cemetery point to `0`. -/
private noncomputable def cemeteryExtendedTest (f : BoundedContinuousFunction E ℝ) :
    BoundedContinuousFunction (E ⊕ Unit) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨Sum.elim f (fun _ : Unit ↦ 0), Continuous.sumElim f.continuous continuous_const⟩
    (2 * ‖f‖)
    (by
      intro x y
      rcases x with x | x <;> rcases y with y | y
      · simpa using f.dist_le_two_norm x y
      · have hxy : dist (f x) 0 ≤ 2 * ‖f‖ := by
          calc
            dist (f x) 0 = ‖f x‖ := by simp
            _ ≤ ‖f‖ := f.norm_coe_le_norm x
            _ ≤ 2 * ‖f‖ := by nlinarith [norm_nonneg f]
        simpa using hxy
      · have hyx : dist 0 (f y) ≤ 2 * ‖f‖ := by
          calc
            dist 0 (f y) = ‖f y‖ := by simp
            _ ≤ ‖f‖ := f.norm_coe_le_norm y
            _ ≤ 2 * ‖f‖ := by nlinarith [norm_nonneg f]
        simpa using hyx
      · simp [norm_nonneg f])

/-- Helper for Theorem 13.29: the cemetery extension agrees with the original test on the
`Sum.inl` copy. -/
@[simp] private theorem cemeteryExtendedTest_inl (f : BoundedContinuousFunction E ℝ) (x : E) :
    cemeteryExtendedTest f (Sum.inl x) = f x := by
  simp [cemeteryExtendedTest]

/-- Helper for Theorem 13.29: the cemetery extension vanishes at the cemetery point. -/
@[simp] private theorem cemeteryExtendedTest_inr (f : BoundedContinuousFunction E ℝ) (u : Unit) :
    cemeteryExtendedTest f (Sum.inr u) = 0 := by
  simp [cemeteryExtendedTest]

/-- Helper for Theorem 13.29: restricting the cemetery extension back to `E` recovers the
original test. -/
@[simp] private theorem inlRestrictedTest_cemeteryExtendedTest
    (f : BoundedContinuousFunction E ℝ) :
    inlRestrictedTest (cemeteryExtendedTest f) = f := by
  ext x
  change cemeteryExtendedTest f (Sum.inl x) = f x
  simp

/-- Helper for Theorem 13.29: `Sum.inl` is a measurable embedding for the local Borel
sum-space structure. -/
private theorem measurableEmbedding_sumInl : MeasurableEmbedding (Sum.inl : E → E ⊕ Unit) :=
  Topology.IsOpenEmbedding.inl.measurableEmbedding

/-- Helper for Theorem 13.29: the `Sum.inl` pushforward of a bounded continuous test integrates
as restriction to the `E` coordinate. -/
private theorem integral_map_sumInl_boundedContinuous
    (g : BoundedContinuousFunction (E ⊕ Unit) ℝ)
    (μ : FiniteMeasure E) :
    ∫ z, g z ∂(Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E)) =
      ∫ x, g (Sum.inl x) ∂((μ : Measure E)) := by
  -- Proof comment: this is the standard `integral_map` rewrite for the measurable inclusion.
  simpa using
    (MeasureTheory.integral_map measurableEmbedding_sumInl.measurable.aemeasurable
      (show AEStronglyMeasurable (fun z : E ⊕ Unit ↦ g z)
          (Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E)) from
        g.continuous.aestronglyMeasurable))

/-- Helper for Theorem 13.29: encode a subprobability finite measure as a probability measure on
`E ⊕ Unit` by adding the missing mass at the cemetery point. -/
private noncomputable def subprobabilityCemeteryMeasure (μ : FiniteMeasure E) :
    Measure (E ⊕ Unit) :=
  Measure.map Sum.inl (μ : Measure E) + (1 - μ.mass) • Measure.dirac (Sum.inr ())

/-- Helper for Theorem 13.29: the cemetery encoding has total mass one whenever the original mass
is at most one. -/
private theorem subprobabilityCemeteryMeasure_univ (μ : FiniteMeasure E) (hμ : μ.mass ≤ 1) :
    subprobabilityCemeteryMeasure μ Set.univ = 1 := by
  -- Proof comment: the missing mass is exactly `1 - μ.mass`, so the total mass becomes `1`.
  rw [subprobabilityCemeteryMeasure, Measure.add_apply]
  · rw [Measure.smul_apply,
      Measure.map_apply measurableEmbedding_sumInl.measurable
        (by simp : MeasurableSet (Set.univ : Set (E ⊕ Unit))),
      Measure.dirac_apply_of_mem]
    · change (μ : Measure E) Set.univ + (((1 - μ.mass : NNReal) : ℝ≥0∞) * 1) = 1
      rw [mul_one]
      simpa [FiniteMeasure.ennreal_mass] using
        congrArg (fun t : NNReal => (t : ℝ≥0∞)) (add_tsub_cancel_of_le hμ)
    · simp

/-- Helper for Theorem 13.29: bundle the cemetery measure as a probability measure. -/
private noncomputable def encodeSubprobability (μ : FiniteMeasure E) (hμ : μ.mass ≤ 1) :
    ProbabilityMeasure (E ⊕ Unit) :=
  ⟨subprobabilityCemeteryMeasure μ,
    MeasureTheory.isProbabilityMeasure_iff.2 <| subprobabilityCemeteryMeasure_univ μ hμ⟩

/-- Helper for Theorem 13.29: integrating a bounded continuous test against the encoded
probability measure splits into the `E` part plus the cemetery atom. -/
private theorem integral_encodeSubprobability
    (g : BoundedContinuousFunction (E ⊕ Unit) ℝ)
    (μ : FiniteMeasure E) (hμ : μ.mass ≤ 1) :
    ∫ z, g z ∂(encodeSubprobability μ hμ : Measure (E ⊕ Unit)) =
      ∫ x, inlRestrictedTest g x ∂((μ : Measure E)) + (1 - (μ.mass : ℝ)) * g (Sum.inr ()) := by
  -- Proof comment: expand the encoded measure into the pushed-forward `E` part and the cemetery
  -- atom, then rewrite each contribution explicitly.
  have h_map0 :
      Integrable g (Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E)) := by
    simpa using g.integrable (Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E))
  have h_dirac0 : Integrable g (Measure.dirac (Sum.inr ())) := by
    simpa using g.integrable (Measure.dirac (Sum.inr ()))
  have h_map :
      Integrable g (Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E)) := h_map0
  have h_dirac :
      Integrable g ((1 - μ.mass) • Measure.dirac (Sum.inr ())) := by
    simpa using g.integrable ((1 - μ.mass) • Measure.dirac (Sum.inr ()))
  change
    ∫ z, g z ∂subprobabilityCemeteryMeasure μ =
      ∫ x, inlRestrictedTest g x ∂((μ : Measure E)) + (1 - (μ.mass : ℝ)) * g (Sum.inr ())
  calc
    ∫ z, g z ∂subprobabilityCemeteryMeasure μ
        = ∫ z, g z ∂(Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E)) +
            ∫ z, g z ∂((1 - μ.mass) • Measure.dirac (Sum.inr ())) := by
              rw [subprobabilityCemeteryMeasure, integral_add_measure h_map h_dirac]
    _ = ∫ x, g (Sum.inl x) ∂((μ : Measure E)) +
          (((1 - μ.mass : NNReal) : ℝ)) * g (Sum.inr ()) := by
            have hsmul :
                ∫ z, g z ∂((1 - μ.mass) • Measure.dirac (Sum.inr ())) =
                  (((1 - μ.mass : NNReal) : ℝ)) * g (Sum.inr ()) := by
              change
                (∫ z, g z ∂((((1 - μ.mass : NNReal) : ℝ≥0∞) • Measure.dirac (Sum.inr ())))) =
                  (((1 - μ.mass : NNReal) : ℝ)) * g (Sum.inr ())
              rw [integral_smul_measure, integral_dirac]
              rfl
            rw [integral_map_sumInl_boundedContinuous, hsmul]
    _ = ∫ x, inlRestrictedTest g x ∂((μ : Measure E)) +
          (((1 - μ.mass : NNReal) : ℝ)) * g (Sum.inr ()) := by
            have hinl : (fun x : E ↦ g (Sum.inl x)) = fun x : E ↦ inlRestrictedTest g x := by
              funext x
              rfl
            rw [hinl]
  have htsub :
      (((1 - μ.mass : NNReal) : ℝ)) = 1 - (μ.mass : ℝ) := by
    simpa using (NNReal.coe_sub hμ)
  simp [htsub]

/-- Helper for Theorem 13.29: for zero-at-cemetery tests, the cemetery encoding preserves the
original bounded-continuous integral exactly. -/
private theorem integral_encodeSubprobability_cemeteryExtendedTest
    (f : BoundedContinuousFunction E ℝ)
    (μ : FiniteMeasure E) (hμ : μ.mass ≤ 1) :
    ∫ z, cemeteryExtendedTest f z ∂(encodeSubprobability μ hμ : Measure (E ⊕ Unit)) =
      ∫ x, f x ∂((μ : Measure E)) := by
  -- Proof comment: the cemetery contribution disappears because the extension is zero there.
  simpa using integral_encodeSubprobability (cemeteryExtendedTest f) μ hμ

/-- Helper for Theorem 13.29: decoding a probability measure on `E ⊕ Unit` by restricting to the
`Sum.inl` coordinate recovers bounded-continuous integrals through the cemetery extension. -/
private theorem integral_decodeSubprobability
    (f : BoundedContinuousFunction E ℝ)
    (π : ProbabilityMeasure (E ⊕ Unit)) :
    ∫ x, f x ∂((π.toFiniteMeasure.comap Sum.inl : FiniteMeasure E) : Measure E) =
      ∫ z, cemeteryExtendedTest f z ∂((π : Measure (E ⊕ Unit))) := by
  let ν : FiniteMeasure E := π.toFiniteMeasure.comap Sum.inl
  have hMap :
      Measure.map (Sum.inl : E → E ⊕ Unit) (ν : Measure E) =
        Measure.restrict (π : Measure (E ⊕ Unit)) (Set.range (Sum.inl : E → E ⊕ Unit)) := by
    -- Proof comment: pushing the `Sum.inl` comap forward identifies it with restriction to the
    -- `Sum.inl` copy of `E`.
    simpa [ν] using
      (MeasurableEmbedding.map_comap measurableEmbedding_sumInl (π : Measure (E ⊕ Unit)))
  have hRestrict :
      ∫ z, cemeteryExtendedTest f z
          ∂(Measure.restrict (π : Measure (E ⊕ Unit)) (Set.range (Sum.inl : E → E ⊕ Unit))) =
        ∫ z, cemeteryExtendedTest f z ∂((π : Measure (E ⊕ Unit))) := by
    -- Proof comment: the cemetery extension is already zero away from the `Sum.inl` range.
    rw [← integral_indicator measurableEmbedding_sumInl.measurableSet_range]
    refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
    rcases z with z | u
    · simp
    · simp [cemeteryExtendedTest]
  calc
    ∫ x, f x ∂((ν : Measure E))
        = ∫ x, cemeteryExtendedTest f (Sum.inl x) ∂((ν : Measure E)) := by simp
    _ = ∫ z, cemeteryExtendedTest f z ∂(Measure.map (Sum.inl : E → E ⊕ Unit) (ν : Measure E)) := by
      symm
      exact integral_map_sumInl_boundedContinuous (cemeteryExtendedTest f) ν
    _ = ∫ z, cemeteryExtendedTest f z
          ∂(Measure.restrict (π : Measure (E ⊕ Unit)) (Set.range (Sum.inl : E → E ⊕ Unit))) := by
      rw [hMap]
    _ = ∫ z, cemeteryExtendedTest f z ∂((π : Measure (E ⊕ Unit))) := hRestrict

/-- Helper for Theorem 13.29: the cemetery encoding records the complement of a measurable set in
`E` exactly as the complement of its lifted compact together with the cemetery point. -/
private theorem encodeSubprobability_apply_liftedCompl
    (μ : FiniteMeasure E) (hμ : μ.mass ≤ 1) {A : Set E} (hA : MeasurableSet A) :
    (encodeSubprobability μ hμ : Measure (E ⊕ Unit)) (((Sum.inl '' A) ∪ {Sum.inr ()})ᶜ) =
      (μ : Measure E) Aᶜ := by
  -- Proof comment: the lifted complement contains no cemetery mass, and the `Sum.inl`
  -- pushforward sees exactly the original complement of `A`.
  change subprobabilityCemeteryMeasure μ (((Sum.inl '' A) ∪ {Sum.inr ()})ᶜ) =
    (μ : Measure E) Aᶜ
  have hpre :
      (Sum.inl : E → E ⊕ Unit) ⁻¹' (((Sum.inl '' A) ∪ {Sum.inr ()})ᶜ) = Aᶜ := by
    ext x
    simp
  have hLiftedMeas : MeasurableSet (((Sum.inl '' A) ∪ {Sum.inr ()})ᶜ) :=
    ((measurableEmbedding_sumInl.measurableSet_image' hA).union
      (measurableSet_singleton (Sum.inr ()))).compl
  have hdirac :
      Measure.dirac (Sum.inr ()) (((Sum.inl '' A) ∪ {Sum.inr ()})ᶜ) = 0 := by
    simp
  rw [subprobabilityCemeteryMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.map_apply measurableEmbedding_sumInl.measurable hLiftedMeas, hpre, hdirac]
  simp

/-- Helper for Theorem 13.29: weak convergence of subprobability finite measures implies weak
convergence of their cemetery encodings. -/
private theorem tendsto_encodeSubprobability_of_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hμs : ∀ i, (μs i).mass ≤ 1) (hμ : μ.mass ≤ 1)
    (h : Tendsto μs F (𝓝 μ)) :
    Tendsto (fun i ↦ encodeSubprobability (μs i) (hμs i)) F (𝓝 (encodeSubprobability μ hμ)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have hIntegral :
      Tendsto (fun i ↦ ∫ x, inlRestrictedTest g x ∂((μs i : FiniteMeasure E) : Measure E)) F
        (𝓝 (∫ x, inlRestrictedTest g x ∂((μ : Measure E)))) :=
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp h) (inlRestrictedTest g)
  have hMass :
      Tendsto (fun i ↦ 1 - ((μs i).mass : ℝ)) F (𝓝 (1 - (μ.mass : ℝ))) :=
    (((continuous_const : Continuous fun _ : FiniteMeasure E => (1 : ℝ)).sub
      (NNReal.continuous_coe.comp FiniteMeasure.continuous_mass)).continuousAt.tendsto).comp h
  simpa [integral_encodeSubprobability, hμ, hIntegral, hMass] using hIntegral.add
    (hMass.mul tendsto_const_nhds)

/-- Helper for Theorem 13.29: the cemetery encoding of a family of subprobability finite measures
as probability measures on `E ⊕ Unit`. -/
private noncomputable def encodedFamily (ℱ : Set (FiniteMeasure E))
    (hℱ : ∀ μ ∈ ℱ, μ.mass ≤ 1) : Set (ProbabilityMeasure (E ⊕ Unit)) :=
  Set.range (fun μ : ℱ ↦ encodeSubprobability μ.1 (hℱ μ.1 μ.2))

/-- Helper for Theorem 13.29: in a metric space, a set whose every sequence admits a convergent
subsequence has compact closure. -/
private theorem isCompact_closure_of_subsequence_property {α : Type*} [PseudoMetricSpace α]
    (s : Set α)
    (hs : ∀ x : ℕ → α, (∀ n, x n ∈ s) →
      ∃ a : α, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)) :
    IsCompact (closure s) := by
  have hseq : IsSeqCompact (closure s) := by
    intro y hy
    have hchoose :
        ∀ n : ℕ, ∃ x : α, x ∈ s ∧ dist (y n) x < ((n : ℝ) + 1)⁻¹ := by
      intro n
      exact (Metric.mem_closure_iff.mp (hy n)) (((n : ℝ) + 1)⁻¹) (by positivity)
    choose x hx_mem hx_dist using hchoose
    obtain ⟨a, φ, hφ, hxtendsto⟩ := hs x hx_mem
    have hdist_zero :
        Tendsto (fun n ↦ dist ((x ∘ φ) n) ((y ∘ φ) n)) atTop (𝓝 0) := by
      have hbound :
          ∀ n : ℕ, dist ((x ∘ φ) n) ((y ∘ φ) n) ≤ (((φ n + 1 : ℕ) : ℝ)⁻¹) := by
        intro n
        calc
          dist ((x ∘ φ) n) ((y ∘ φ) n) = dist (y (φ n)) (x (φ n)) := by
            simp [Function.comp, dist_comm]
          _ ≤ (((φ n + 1 : ℕ) : ℝ)⁻¹) := by
            simpa [Nat.cast_add, Nat.cast_one] using (hx_dist (φ n)).le
      have hzero :
          Tendsto (fun n : ℕ ↦ (((φ n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
        have hbase :
            Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
          have hadd : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
            change Tendsto (Nat.cast ∘ fun n : ℕ ↦ n + 1) atTop atTop
            exact
              (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).comp
                (tendsto_add_atTop_nat 1)
          exact tendsto_inv_atTop_zero.comp hadd
        simpa [Function.comp] using hbase.comp hφ.tendsto_atTop
      exact squeeze_zero (fun n ↦ dist_nonneg) hbound hzero
    have hytendsto : Tendsto (y ∘ φ) atTop (𝓝 a) :=
      tendsto_of_tendsto_of_dist hxtendsto hdist_zero
    have ha_closure : a ∈ closure s := by
      apply isClosed_closure.mem_of_tendsto hxtendsto
      exact Filter.Eventually.of_forall fun n ↦ subset_closure (hx_mem (φ n))
    exact ⟨a, ha_closure, φ, hφ, hytendsto⟩
  simpa [isCompact_iff_isSeqCompact] using hseq

/-- Helper for Theorem 13.29: a tight family admits compact control sets with geometric complement
bounds. -/
private theorem exists_geometricCompactControl
    (ℱ : Set (FiniteMeasure E))
    (h_tight : IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' ℱ)) :
    ∃ K : ℕ → Set E, (∀ n, IsCompact (K n)) ∧ Monotone K ∧
      ∀ n, ∀ μ ∈ ℱ, (μ : Measure E) (K n)ᶜ ≤ ((1 / 2 : ENNReal) ^ n) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at h_tight
  have hpos : ∀ n, 0 < ((1 / 2 : ENNReal) ^ n) := by
    intro n
    simp [pos_iff_ne_zero]
  choose K0 hKcompact0 hKbound0 using fun n ↦ h_tight (((1 / 2 : ENNReal) ^ n)) (hpos n)
  let K : ℕ → Set E := fun n ↦ ⋃ i ∈ Iic n, K0 i
  refine ⟨K, ?_, ?_, ?_⟩
  · intro n
    exact (finite_Iic n).isCompact_biUnion fun i _ ↦ hKcompact0 i
  · intro n m hnm
    simp only [K, mem_Iic, le_eq_subset, iUnion_subset_iff]
    intro i hi
    exact subset_biUnion_of_mem (show i ≤ m from hi.trans hnm)
  · intro n μ hμ
    calc
      (μ : Measure E) (K n)ᶜ ≤ (μ : Measure E) (K0 n)ᶜ := by
        gcongr
        simp only [K, mem_Iic]
        exact subset_biUnion_of_mem (show n ≤ n by simp)
      _ ≤ ((1 / 2 : ENNReal) ^ n) := hKbound0 n _ ⟨μ, hμ, rfl⟩

/-- Helper for Theorem 13.29: pulling a finite measure back to a closed subtype and then pushing it
forward along the subtype inclusion recovers the original measure when the complement has zero
mass. -/
private theorem map_comap_subtypeVal_of_null_compl
    {S : Set E} (hS : IsClosed S) (μ : FiniteMeasure E) (hμ : (μ : Measure E) Sᶜ = 0) :
    (μ.comap (Subtype.val : S → E)).map (Subtype.val : S → E) = μ := by
  -- Proof comment: `map_comap_subtype_coe` rewrites the round-trip as a restriction to `S`, and
  -- the support assumption says that this restriction is already the original measure.
  apply FiniteMeasure.toMeasure_injective
  rw [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_comap,
    map_comap_subtype_coe hS.measurableSet, Measure.restrict_eq_self_of_ae_mem hμ]

/-- Helper for Theorem 13.29: the closure of a countable union of compact control sets is
separable. -/
private theorem isSeparable_closure_iUnion_of_isCompact
    (K : ℕ → Set E) (hK : ∀ n, IsCompact (K n)) :
    TopologicalSpace.IsSeparable (closure (⋃ n, K n)) := by
  -- Proof comment: countable unions of separable compact sets stay separable, and closure preserves
  -- separability.
  exact (TopologicalSpace.IsSeparable.iUnion fun n ↦ (hK n).isSeparable).closure

/-- Helper for Theorem 13.29: geometric escape bounds force zero mass outside the closed support
generated by the compact controls. -/
private theorem measure_compl_closure_iUnion_eq_zero
    (ℱ : Set (FiniteMeasure E)) (K : ℕ → Set E)
    (hKbound : ∀ n, ∀ μ ∈ ℱ, (μ : Measure E) (K n)ᶜ ≤ ((1 / 2 : ENNReal) ^ n))
    (μ : FiniteMeasure E) (hμ : μ ∈ ℱ) :
    (μ : Measure E) (closure (⋃ n, K n))ᶜ = 0 := by
  have hle : ∀ n, (μ : Measure E) (closure (⋃ n, K n))ᶜ ≤ ((1 / 2 : ENNReal) ^ n) := by
    intro n
    refine le_trans (measure_mono ?_) (hKbound n μ hμ)
    intro x hx
    have hx' : x ∉ closure (⋃ n, K n) := hx
    have hx'' : x ∉ K n := by
      intro hxK
      exact hx' <| subset_closure <| mem_iUnion.mpr ⟨n, hxK⟩
    simpa using hx''
  refine le_antisymm ?_ bot_le
  have hpow : Tendsto (fun n ↦ ((1 / 2 : ENNReal) ^ n)) atTop (𝓝 0) := by
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hpow hle

/-- Helper for Theorem 13.29: every sequence in the encoded family admits a convergent
subsequence. -/
private theorem encodedFamilySubsequenceProperty [PolishSpace E]
    (ℱ : Set (FiniteMeasure E)) (hℱ : ∀ μ ∈ ℱ, μ.mass ≤ 1)
    (h_seq : ∀ μs : ℕ → FiniteMeasure E, (∀ n, μs n ∈ ℱ) →
      ∃ μ : FiniteMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ)) :
    ∀ πs : ℕ → ProbabilityMeasure (E ⊕ Unit), (∀ n, πs n ∈ encodedFamily ℱ hℱ) →
      ∃ π : ProbabilityMeasure (E ⊕ Unit), ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Tendsto (πs ∘ φ) atTop (𝓝 π) := by
  intro πs hπs
  have hrepr :
      ∀ n, ∃ μ : ℱ, πs n = encodeSubprobability μ.1 (hℱ μ.1 μ.2) := by
    intro n
    rcases hπs n with ⟨μ, hμ⟩
    exact ⟨μ, hμ.symm⟩
  choose μs hμs using hrepr
  obtain ⟨μ, φ, hφ, hμ_tendsto⟩ := h_seq (fun n ↦ (μs n).1) (fun n ↦ (μs n).2)
  have hμ_mass : μ.mass ≤ 1 := by
    let S : Set (FiniteMeasure E) := {ν : FiniteMeasure E | ν.mass ≤ 1}
    have hS_closed : IsClosed S := isClosed_le FiniteMeasure.continuous_mass continuous_const
    have hS_eventually : ∀ᶠ n in atTop, (μs (φ n)).1 ∈ S := by
      exact Filter.Eventually.of_forall fun n ↦ hℱ (μs (φ n)).1 (μs (φ n)).2
    exact hS_closed.mem_of_tendsto hμ_tendsto hS_eventually
  refine ⟨encodeSubprobability μ hμ_mass, φ, hφ, ?_⟩
  -- Proof comment: once the underlying finite measures converge, the cemetery encoding preserves
  -- the convergence and identifies the encoded subsequence with `πs ∘ φ`.
  have hencode :
      Tendsto (fun n ↦ encodeSubprobability ((μs (φ n)).1) (hℱ (μs (φ n)).1 (μs (φ n)).2))
        atTop (𝓝 (encodeSubprobability μ hμ_mass)) := by
    exact tendsto_encodeSubprobability_of_tendsto
      (μs := fun n ↦ (μs (φ n)).1)
      (hμs := fun n ↦ hℱ (μs (φ n)).1 (μs (φ n)).2) hμ_mass hμ_tendsto
  have hcomp :
      (fun n ↦ encodeSubprobability ((μs (φ n)).1) (hℱ (μs (φ n)).1 (μs (φ n)).2)) = πs ∘ φ := by
    funext n
    exact (hμs (φ n)).symm
  rw [hcomp] at hencode
  exact hencode

/-- Helper for Theorem 13.29: the closure of the encoded family is compact. -/
private theorem encodedCompactClosure_ofSequentialCompactFamily [PolishSpace E]
    (ℱ : Set (FiniteMeasure E)) (hℱ : ∀ μ ∈ ℱ, μ.mass ≤ 1)
    (h_seq : ∀ μs : ℕ → FiniteMeasure E, (∀ n, μs n ∈ ℱ) →
      ∃ μ : FiniteMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ)) :
    IsCompact (closure (encodedFamily ℱ hℱ)) := by
  letI : TopologicalSpace.MetrizableSpace (ProbabilityMeasure (E ⊕ Unit)) := by infer_instance
  letI : MetricSpace (ProbabilityMeasure (E ⊕ Unit)) := TopologicalSpace.metrizableSpaceMetric _
  -- Proof comment: the encoded family is sequentially precompact by hypothesis, and metric spaces
  -- turn this into compactness of the closure.
  refine isCompact_closure_of_subsequence_property (s := encodedFamily ℱ hℱ) ?_
  exact encodedFamilySubsequenceProperty ℱ hℱ h_seq

/-- Helper for Theorem 13.29: a compact-closure family of probability measures is tight after
forgetting to ambient measures. -/
private theorem tightMeasureView_of_isCompactClosure [PolishSpace E]
    {T : Set (ProbabilityMeasure (E ⊕ Unit))} (hcompactT : IsCompact (closure T)) :
    IsTightMeasureSet
      {((π : ProbabilityMeasure (E ⊕ Unit)) : Measure (E ⊕ Unit)) | π ∈ T} := by
  -- Proof comment: this is exactly the owner compact-closure-to-tightness theorem on
  -- `ProbabilityMeasure (E ⊕ Unit)`.
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable (E ⊕ Unit)
  letI : OpensMeasurableSpace (E ⊕ Unit) := by infer_instance
  letI : SecondCountableTopology (E ⊕ Unit) := by infer_instance
  exact MeasureTheory.isTightMeasureSet_of_isCompact_closure (S := T) hcompactT

/-- Helper for Theorem 13.29: compact control on the cemetery-encoded family pulls back along
`Sum.inl` to compact control on the original family. -/
private theorem compactPullbackEscapeBound
    (ℱ : Set (FiniteMeasure E)) (hℱ : ∀ μ ∈ ℱ, μ.mass ≤ 1)
    {K' : Set (E ⊕ Unit)} (hK' : IsCompact K')
    {r : ℝ≥0∞}
    (hbound : ∀ μ (hμ : μ ∈ ℱ),
      (encodeSubprobability μ (hℱ μ hμ) : Measure (E ⊕ Unit)) K'ᶜ ≤ r) :
    ∃ K : Set E, IsCompact K ∧ ∀ μ ∈ ℱ, (μ : Measure E) Kᶜ ≤ r := by
  refine ⟨(Sum.inl : E → E ⊕ Unit) ⁻¹' K', ?_, ?_⟩
  · -- Proof comment: preimages of compact sets along the closed embedding `Sum.inl` stay compact.
    exact Topology.IsClosedEmbedding.inl.isCompact_preimage hK'
  · intro μ hμ
    have hKmeas : MeasurableSet ((Sum.inl : E → E ⊕ Unit) ⁻¹' K') :=
      continuous_inl.measurable hK'.measurableSet
    have hsubset :
        (((Sum.inl '' ((Sum.inl : E → E ⊕ Unit) ⁻¹' K')) ∪ {Sum.inr ()})ᶜ) ⊆ K'ᶜ := by
      intro z hz hKz
      rcases z with x | u
      · exact hz (Or.inl ⟨x, hKz, rfl⟩)
      · exact hz (Or.inr (by simp))
    -- Proof comment: the lifted complement computes the original escape mass exactly, and the
    -- lifted compact contains `K'` after adjoining the cemetery point.
    calc
      (μ : Measure E) (((Sum.inl : E → E ⊕ Unit) ⁻¹' K')ᶜ)
          = (encodeSubprobability μ (hℱ μ hμ) : Measure (E ⊕ Unit))
              (((Sum.inl '' ((Sum.inl : E → E ⊕ Unit) ⁻¹' K')) ∪ {Sum.inr ()})ᶜ) := by
                symm
                simpa using
                  encodeSubprobability_apply_liftedCompl
                    μ (hℱ μ hμ) (A := ((Sum.inl : E → E ⊕ Unit) ⁻¹' K')) hKmeas
      _ ≤ (encodeSubprobability μ (hℱ μ hμ) : Measure (E ⊕ Unit)) K'ᶜ := measure_mono hsubset
      _ ≤ r := hbound μ hμ

-- Proof sketch: apply tightness to the range of an arbitrary sequence in `ℱ` to obtain compact
-- sets with uniformly small complement mass, then use the Prokhorov compactness argument for
-- subprobability finite measures to extract a weakly convergent subsequence.
/-- Forward implication of Theorem 13.29: a tight family of subprobability finite measures on a
metric space is weakly
relatively sequentially compact for the weak topology on `FiniteMeasure E`. -/
theorem isWeaklyRelativelySequentiallyCompactFamily_of_isTightMeasureSet
    (ℱ : Set (FiniteMeasure E)) (hℱ : ∀ μ ∈ ℱ, μ.mass ≤ 1)
    (h_tight : IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' ℱ)) :
    ∀ μs : ℕ → FiniteMeasure E, (∀ n, μs n ∈ ℱ) →
      ∃ μ : FiniteMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  intro μs hμs
  -- Route correction: instead of rebuilding a general finite-measure metrization theorem here,
  -- reduce to the separable support subtype and apply the finite-measure Prokhorov compactness
  -- theorem directly there.
  obtain ⟨K, hKcompact, hKmono, hKbound⟩ := exists_geometricCompactControl ℱ h_tight
  let S : Set E := closure (⋃ n, K n)
  have hS_closed : IsClosed S := isClosed_closure
  have hS_sep : TopologicalSpace.IsSeparable S :=
    isSeparable_closure_iUnion_of_isCompact K hKcompact
  letI : TopologicalSpace.SeparableSpace S := hS_sep.separableSpace
  have hS_zero : ∀ μ ∈ ℱ, (μ : Measure E) Sᶜ = 0 := by
    intro μ hμ
    exact measure_compl_closure_iUnion_eq_zero ℱ K hKbound μ hμ
  let f : S → E := Subtype.val
  have hf : Topology.IsClosedEmbedding f := Topology.IsClosedEmbedding.subtypeVal hS_closed
  have hf_meas : MeasurableEmbedding f := MeasurableEmbedding.subtype_coe hS_closed.measurableSet
  let L : ℕ → Set S := fun n ↦ f ⁻¹' K n
  have hLcompact : ∀ n, IsCompact (L n) := by
    intro n
    exact hf.isCompact_preimage (hKcompact n)
  have hLmono : Monotone L := by
    intro n m hnm
    exact preimage_mono (hKmono hnm)
  let νs : ℕ → FiniteMeasure S := fun n ↦ (μs n).comap f
  have hνs_mass : ∀ n, (νs n).mass ≤ 1 := by
    intro n
    exact (FiniteMeasure.mass_comap_le f (μs n)).trans (hℱ _ (hμs n))
  have hνs_support : ∀ n, (νs n).map f = μs n := by
    intro n
    exact map_comap_subtypeVal_of_null_compl hS_closed (μs n) (hS_zero _ (hμs n))
  have hLbound :
      ∀ n m, ((νs m : FiniteMeasure S) : Measure S) ((L n)ᶜ) ≤ ((1 / 2 : ENNReal) ^ n) := by
    intro n m
    -- Proof comment: pushing `νs m` forward along the subtype inclusion rewrites the subtype
    -- complement exactly as the original compact-control complement on `K n`.
    calc
      ((νs m : FiniteMeasure S) : Measure S) ((L n)ᶜ)
          = (((νs m).map f : FiniteMeasure E) : Measure E) (K n)ᶜ := by
              simpa [L, f, FiniteMeasure.toMeasure_map] using
                (hf_meas.map_apply (((νs m : FiniteMeasure S) : Measure S)) ((K n)ᶜ)).symm
      _ = (μs m : Measure E) (K n)ᶜ := by rw [hνs_support m]
      _ ≤ ((1 / 2 : ENNReal) ^ n) := hKbound n (μs m) (hμs m)
  let A : ℕ → Set (S ⊕ Unit) := fun n ↦ (Sum.inl '' L n) ∪ {Sum.inr ()}
  have hAcompact : ∀ n, IsCompact (A n) := by
    intro n
    exact (hLcompact n).image continuous_inl |>.union isCompact_singleton
  have hAmono : Monotone A := by
    intro n m hnm
    refine union_subset_union ?_ Subset.rfl
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hLmono hnm hx, rfl⟩
  let πs : ℕ → ProbabilityMeasure (S ⊕ Unit) :=
    fun n ↦ encodeSubprobability (νs n) (hνs_mass n)
  have hπs_mem :
      ∀ n, πs n ∈ {π : ProbabilityMeasure (S ⊕ Unit) | ∀ m, π (A m)ᶜ ≤ ((1 / 2 : NNReal) ^ m)} := by
    intro n m
    -- Proof comment: the cemetery encoding turns the subtype compact-control estimate into the
    -- exact lifted-compact estimate needed by probability-measure Prokhorov compactness.
    refine (show ((πs n) (A m)ᶜ : NNReal) ≤ ((1 / 2 : NNReal) ^ m) from ?_)
    have hbound :
        ((((πs n) (A m)ᶜ : NNReal) : ℝ≥0∞)) ≤
          ((((1 / 2 : NNReal) ^ m : NNReal) : ℝ≥0∞)) := by
      calc
        ((((πs n) (A m)ᶜ : NNReal) : ℝ≥0∞))
            = ((πs n : Measure (S ⊕ Unit)) ((A m)ᶜ) : ℝ≥0∞) := by
                simp [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
        _
            = ((νs n : FiniteMeasure S) : Measure S) ((L m)ᶜ) := by
                simpa [πs, A] using
                  encodeSubprobability_apply_liftedCompl
                    (νs n) (hνs_mass n) (hLcompact m).measurableSet
        _ ≤ ((1 / 2 : ENNReal) ^ m) := hLbound m n
        _ = ((((1 / 2 : NNReal) ^ m : NNReal) : ℝ≥0∞)) := by norm_num
    exact ENNReal.coe_le_coe.mp hbound
  let u : ℕ → ℝ≥0 := fun n ↦ ((1 / 2 : ℝ≥0) ^ n)
  have hu : Tendsto u atTop (𝓝 (0 : ℝ≥0)) := by
    simpa [u] using NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ≥0)) (by norm_num)
  letI : TopologicalSpace.MetrizableSpace (ProbabilityMeasure (S ⊕ Unit)) := by infer_instance
  letI : MetricSpace (ProbabilityMeasure (S ⊕ Unit)) := TopologicalSpace.metrizableSpaceMetric _
  have hcompact :
      IsCompact {π : ProbabilityMeasure (S ⊕ Unit) | ∀ n, π (A n)ᶜ ≤ u n} := by
    -- Proof comment: the encoded sequence lies in the standard compact Prokhorov class on the
    -- separable support-plus-cemetery space.
    exact isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
      (u := u) hu hAcompact (Or.inr hAmono)
  obtain ⟨π, hπ_mem, φ, hφ, hπ_tendsto⟩ := hcompact.tendsto_subseq hπs_mem
  let ν : FiniteMeasure S := π.toFiniteMeasure.comap Sum.inl
  have hν_tendsto : Tendsto (νs ∘ φ) atTop (𝓝 ν) := by
    -- Proof comment: convergence of the encoded probabilities transfers back to convergence of the
    -- original finite measures by testing against cemetery-extended bounded continuous functions.
    rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
    intro g
    have htest :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hπ_tendsto)
        (cemeteryExtendedTest g)
    rw [show ∫ x, g x ∂((ν : FiniteMeasure S) : Measure S) =
        ∫ z, cemeteryExtendedTest g z ∂((π : Measure (S ⊕ Unit))) by
          simpa [ν] using integral_decodeSubprobability g π]
    simpa [πs, Function.comp, integral_encodeSubprobability_cemeteryExtendedTest] using htest
  refine ⟨ν.map f, φ, hφ, ?_⟩
  have hmap_tendsto :
      Tendsto (fun n ↦ (νs (φ n)).map f) atTop (𝓝 (ν.map f)) := by
    -- Proof comment: continuity of pushforward along the subtype inclusion transports the compact
    -- subsequence convergence back to `FiniteMeasure E`.
    exact ((FiniteMeasure.continuous_map (f := f) continuous_subtype_val).tendsto ν).comp
      hν_tendsto
  simpa [Function.comp, hνs_support] using hmap_tendsto

-- Proof sketch: assuming `E` is Polish, use the sequential compactness hypothesis to obtain a
-- weak limit from any carefully chosen sequence in `ℱ`, apply the Polish-space tightness of single
-- finite measures together with Portmanteau control on closed complements, and derive uniform
-- compact containment for the whole family.
/-- Theorem 13.29 (2): on a Polish space, a weakly relatively sequentially compact family of
subprobability finite measures is tight. -/
theorem isTightMeasureSet_of_isWeaklyRelativelySequentiallyCompactFamily [PolishSpace E]
    (ℱ : Set (FiniteMeasure E)) (hℱ : ∀ μ ∈ ℱ, μ.mass ≤ 1)
    (h_seq : ∀ μs : ℕ → FiniteMeasure E, (∀ n, μs n ∈ ℱ) →
      ∃ μ : FiniteMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ)) :
    IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' ℱ) := by
  -- Route correction: freeze the encoded-family compact-closure step in local helpers, then pull
  -- one compact witness on `E ⊕ Unit` back along `Sum.inl`.
  rw [FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt]
  intro ε hε
  let T : Set (ProbabilityMeasure (E ⊕ Unit)) := encodedFamily ℱ hℱ
  let Tview : Set (Measure (E ⊕ Unit)) :=
    {((π : ProbabilityMeasure (E ⊕ Unit)) : Measure (E ⊕ Unit)) | π ∈ T}
  have hcompactT : IsCompact (closure T) := by
    simpa [T] using encodedCompactClosure_ofSequentialCompactFamily ℱ hℱ h_seq
  have htightEncoded : IsTightMeasureSet Tview := by
    have htightT : IsTightMeasureSet
        {((π : ProbabilityMeasure (E ⊕ Unit)) : Measure (E ⊕ Unit)) | π ∈ T} :=
      tightMeasureView_of_isCompactClosure (T := T) hcompactT
    -- Proof comment: `Tview` is the owner-level measure view of the encoded probability family.
    simpa [Tview] using htightT
  have hεhalf : 0 < ENNReal.ofReal (ε / 2) := by
    positivity
  obtain ⟨K', hK'compact, hK'bound⟩ :=
    (MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htightEncoded)
      (ENNReal.ofReal (ε / 2)) hεhalf
  have hencodedBound :
      ∀ μ (hμ : μ ∈ ℱ),
        (encodeSubprobability μ (hℱ μ hμ) : Measure (E ⊕ Unit)) K'ᶜ ≤
          ENNReal.ofReal (ε / 2) := by
    intro μ hμ
    have hmemTview :
        (encodeSubprobability μ (hℱ μ hμ) : Measure (E ⊕ Unit)) ∈ Tview := by
      refine ⟨encodeSubprobability μ (hℱ μ hμ), ?_, rfl⟩
      exact ⟨⟨μ, hμ⟩, rfl⟩
    exact hK'bound _ hmemTview
  obtain ⟨K, hKcompact, hKbound⟩ :=
    compactPullbackEscapeBound ℱ hℱ hK'compact hencodedBound
  refine ⟨K, hKcompact, ?_⟩
  intro μ hμ
  -- Proof comment: the encoded witness is requested at scale `ε / 2`, so the pulled-back
  -- estimate is automatically strict at scale `ε`.
  exact (hKbound μ hμ).trans_lt <| by
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by nlinarith)

end FiniteMeasure
end MeasureTheory
