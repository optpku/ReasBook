/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Lemma_13_15

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction CompactlySupported Topology

noncomputable section

universe u

namespace MeasureTheory
namespace FiniteMeasure

section Portmanteau

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]

/-- Helper for Theorem 13.16: a bounded Lipschitz real-valued function is a bounded continuous
test function in the weak topology on `FiniteMeasure E`. -/
def boundedContinuousOfBoundedLipschitz (f : E → ℝ)
    (hf_bdd : Bornology.IsBounded (range f)) (hf_lip : ∃ L, LipschitzWith L f) :
    E →ᵇ ℝ :=
  -- Proof comment: package the source-facing bounded Lipschitz data into mathlib's bundled
  -- bounded continuous-function type.
  ⟨⟨f, hf_lip.choose_spec.continuous⟩, Metric.isBounded_range_iff.1 hf_bdd⟩

/-- Helper for Theorem 13.16: weak convergence of finite measures implies convergence of the
integrals of every bounded Lipschitz test function. -/
lemma tendstoIntegralOfBoundedLipschitzOfTendsto
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (h : Tendsto μs atTop (𝓝 μ)) :
    ∀ f : E → ℝ, Bornology.IsBounded (range f) → (∃ L, LipschitzWith L f) →
      Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
  intro f hf_bdd hf_lip
  -- Proof comment: once the test function is bundled as a bounded continuous function, this is
  -- exactly the owner characterization of weak convergence for finite measures.
  simpa [boundedContinuousOfBoundedLipschitz] using
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp h)
      (boundedContinuousOfBoundedLipschitz f hf_bdd hf_lip)

/-- Helper for Theorem 13.16: for `NNReal`-valued sequences, matching liminf and limsup bounds force
convergence. -/
lemma massTendstoOfLiminfLimsup {a : ℕ → NNReal} {m : NNReal}
    (hBound : atTop.IsBoundedUnder (· ≤ ·) a)
    (hInf : m ≤ liminf a atTop) (hSup : limsup a atTop ≤ m) :
    Tendsto a atTop (𝓝 m) := by
  -- Proof comment: once an eventual upper bound is supplied explicitly, nonnegativity gives the
  -- lower bound and the standard liminf/limsup squeeze theorem finishes.
  exact tendsto_of_le_liminf_of_limsup_le hInf hSup hBound ⟨0, by simp⟩

/-- Helper for Theorem 13.16: integrating against the normalized probability measure rewrites as
dividing the original integral by the total mass. -/
lemma integralNormalize_eq_invMass_mul_integral
    [Nonempty E] {f : E → ℝ} {ν : FiniteMeasure E} (hν : ν ≠ 0) :
    ∫ x, f x ∂((ν.normalize : ProbabilityMeasure E) : Measure E) =
      (ν.mass : ℝ)⁻¹ * ∫ x, f x ∂(ν : Measure E) := by
  -- Proof comment: rewrite the normalized integral through `average`, which is exactly mass
  -- inversion times the original integral in the real-valued case.
  rw [← ν.average_eq_integral_normalize hν]
  rw [MeasureTheory.average_eq]
  simp [smul_eq_mul]

/-- Helper for Theorem 13.16: convergence of the integrals of every bounded Lipschitz test
function already implies weak convergence of finite measures. -/
lemma tendstoOfBoundedLipschitzIntegralCondition
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (h :
      ∀ f : E → ℝ, Bornology.IsBounded (range f) → (∃ L, LipschitzWith L f) →
        Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
          (𝓝 (∫ x, f x ∂(μ : Measure E)))) :
    Tendsto μs atTop (𝓝 μ) := by
  by_cases hE : Nonempty E
  · letI := hE
    have hone_bdd : Bornology.IsBounded (range fun _ : E ↦ (1 : ℝ)) := by
      simpa [Set.range_const] using (Bornology.isBounded_singleton (1 : ℝ))
    have hmassReal :
        Tendsto (fun n ↦ ∫ x, (1 : ℝ) ∂(μs n : Measure E)) atTop
          (𝓝 (∫ x, (1 : ℝ) ∂(μ : Measure E))) :=
      h (fun _ ↦ (1 : ℝ)) hone_bdd ⟨0, LipschitzWith.const 1⟩
    have hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := by
      apply (NNReal.tendsto_coe).1
      simpa [FiniteMeasure.measureReal_eq_coe_coeFn] using hmassReal
    by_cases hμ : μ = 0
    · simpa [hμ] using
        (FiniteMeasure.tendsto_zero_of_tendsto_zero_mass (by simpa [hμ] using hmass))
    · have hne :
          ∀ᶠ n in atTop, μs n ≠ 0 := by
        have hmass_ne : ∀ᶠ n in atTop, (μs n).mass ≠ 0 :=
          hmass (isOpen_compl_singleton.mem_nhds (μ.mass_nonzero_iff.mpr hμ))
        exact hmass_ne.mono fun n hn ↦ (μs n).mass_nonzero_iff.mp hn
      have hmassInv :
          Tendsto (fun n ↦ ((μs n).mass : ℝ)⁻¹) atTop (𝓝 ((μ.mass : ℝ)⁻¹)) := by
        exact (NNReal.tendsto_coe).2 <| Tendsto.inv₀ hmass (μ.mass_nonzero_iff.mpr hμ)
      have hnorm : Tendsto (fun n ↦ (μs n).normalize) atTop (𝓝 μ.normalize) := by
        rw [tendsto_iff_forall_lipschitz_integral_tendsto]
        intro f hf_bdd hf_lip
        have hf_bdd_range : Bornology.IsBounded (range f) := Metric.isBounded_range_iff.2 hf_bdd
        have hf_tendsto := h f hf_bdd_range hf_lip
        have hscaled :
            Tendsto (fun n ↦ ((μs n).mass : ℝ)⁻¹ * ∫ x, f x ∂(μs n : Measure E)) atTop
              (𝓝 ((μ.mass : ℝ)⁻¹ * ∫ x, f x ∂(μ : Measure E))) := by
          exact hmassInv.mul hf_tendsto
        have hEventually :
            ∀ᶠ n in atTop,
              ∫ x, f x ∂((μs n).normalize : Measure E) =
                ((μs n).mass : ℝ)⁻¹ * ∫ x, f x ∂(μs n : Measure E) := by
          filter_upwards [hne] with n hn
          simpa using
            integralNormalize_eq_invMass_mul_integral (f := f) (ν := μs n) hn
        have hμIntegral :
            ∫ x, f x ∂((μ.normalize : ProbabilityMeasure E) : Measure E) =
              ((μ.mass : ℝ)⁻¹ * ∫ x, f x ∂(μ : Measure E)) :=
          integralNormalize_eq_invMass_mul_integral (f := f) (ν := μ) hμ
        refine (tendsto_congr' hEventually).2 ?_
        simpa [hμIntegral] using hscaled
      exact (FiniteMeasure.tendsto_normalize_iff_tendsto hμ).mp ⟨hnorm, hmass⟩
  · haveI : IsEmpty E := not_nonempty_iff.mp hE
    have hzero (ν : FiniteMeasure E) : ν = 0 := by
      ext s hs
      have hs_empty : s = ∅ := Subsingleton.elim _ _
      simp [hs_empty]
    have hconst : μs = fun _ : ℕ ↦ μ := by
      funext n
      rw [hzero (μs n), hzero μ]
    simpa [hconst] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ μ) atTop (𝓝 μ))

/-- Helper for Theorem 13.16: if the total masses converge to a nonzero limit mass, then the
finite measures are eventually nonzero. -/
lemma eventually_ne_zero_of_tendsto_mass_nonzero
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass)) (hμ : μ ≠ 0) :
    ∀ᶠ n in atTop, μs n ≠ 0 := by
  have hmass_ne : ∀ᶠ n in atTop, (μs n).mass ≠ 0 :=
    hmass (isOpen_compl_singleton.mem_nhds (μ.mass_nonzero_iff.mpr hμ))
  exact hmass_ne.mono fun n hn ↦ (μs n).mass_nonzero_iff.mp hn

/-- Helper for Theorem 13.16: total-mass convergence uniformly bounds the mass of every fixed set
along the sequence. -/
lemma isBoundedUnderApplyOfMassTendsto
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass)) (s : Set E) :
    atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ μs n s) := by
  refine Filter.isBoundedUnder_of_eventually_le (a := μ.mass + 1) ?_
  filter_upwards [hmass (Iio_mem_nhds (by simp : μ.mass < μ.mass + 1))] with n hn
  exact le_trans ((μs n).apply_le_mass s) hn.le

/-- Helper for Theorem 13.16: an `ENNReal` liminf lower bound on a fixed set converts to the
corresponding `NNReal` inequality for finite measures. -/
lemma finiteMeasureApply_le_liminf_of_measureApply_le_liminf
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass)) {s : Set E}
    (h : (μ : Measure E) s ≤ liminf (fun n ↦ (μs n : Measure E) s) atTop) :
    μ s ≤ liminf (fun n ↦ μs n s) atTop := by
  have hBound := isBoundedUnderApplyOfMassTendsto (μs := μs) (μ := μ) hmass s
  have hAux :
      ENNReal.ofNNReal (liminf (fun n ↦ μs n s) atTop) =
        liminf (ENNReal.ofNNReal ∘ fun n ↦ μs n s) atTop := by
    simpa [Function.comp_apply] using
      Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono (fun n ↦ μs n s)
        ENNReal.continuous_coe.continuousAt hBound.isCoboundedUnder_ge ⟨0, by simp⟩
  have hFun :
      (fun n ↦ (μs n : Measure E) s) = ENNReal.ofNNReal ∘ fun n ↦ μs n s := by
    funext n
    simp [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Function.comp_apply]
  have h' : ENNReal.ofNNReal (μ s) ≤ ENNReal.ofNNReal (liminf (fun n ↦ μs n s) atTop) := by
    have h'' : ENNReal.ofNNReal (μ s) ≤
        liminf (ENNReal.ofNNReal ∘ fun n ↦ μs n s) atTop := by
      simpa [hFun, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Function.comp_apply] using h
    simpa [hAux] using h''
  exact ENNReal.coe_le_coe.mp h'

/-- Helper for Theorem 13.16: an `ENNReal` limsup upper bound on a fixed set converts to the
corresponding `NNReal` inequality for finite measures. -/
lemma finiteMeasureLimsup_le_of_measureLimsup_le
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass)) {s : Set E}
    (h : limsup (fun n ↦ (μs n : Measure E) s) atTop ≤ (μ : Measure E) s) :
    limsup (fun n ↦ μs n s) atTop ≤ μ s := by
  have hBound := isBoundedUnderApplyOfMassTendsto (μs := μs) (μ := μ) hmass s
  have hAux :
      ENNReal.ofNNReal (limsup (fun n ↦ μs n s) atTop) =
        limsup (ENNReal.ofNNReal ∘ fun n ↦ μs n s) atTop := by
    simpa [Function.comp_apply] using
      Monotone.map_limsup_of_continuousAt (F := atTop) ENNReal.coe_mono (fun n ↦ μs n s)
        ENNReal.continuous_coe.continuousAt hBound ⟨0, by simp⟩
  have hFun :
      (fun n ↦ (μs n : Measure E) s) = ENNReal.ofNNReal ∘ fun n ↦ μs n s := by
    funext n
    simp [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Function.comp_apply]
  have h' : ENNReal.ofNNReal (limsup (fun n ↦ μs n s) atTop) ≤ ENNReal.ofNNReal (μ s) := by
    have h'' :
        limsup (ENNReal.ofNNReal ∘ fun n ↦ μs n s) atTop ≤ ENNReal.ofNNReal (μ s) := by
      simpa [hFun, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Function.comp_apply] using h
    simpa [hAux] using h''
  exact ENNReal.coe_le_coe.mp h'

/-- Helper for Theorem 13.16: bounded `NNReal` sequences satisfy the expected limsup product upper
bound after transport to `ENNReal`. -/
lemma nnrealLimsupMulLe {u v : ℕ → NNReal}
    (hu : atTop.IsBoundedUnder (· ≤ ·) u) (hv : atTop.IsBoundedUnder (· ≤ ·) v) :
    limsup (fun n ↦ u n * v n) atTop ≤ limsup u atTop * limsup v atTop := by
  have huv : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ u n * v n) := by
    exact isBoundedUnder_le_mul_of_nonneg
      (Filter.Frequently.of_forall fun n ↦ show (0 : NNReal) ≤ u n from bot_le) hu
      (Filter.Eventually.of_forall fun n ↦ show (0 : NNReal) ≤ v n from bot_le) hv
  have hu_ne_top : limsup (fun n ↦ (u n : ENNReal)) atTop ≠ (⊤ : ENNReal) := by
    rw [← ENNReal.ofNNReal_limsup hu]
    simp
  have hv_ne_top : limsup (fun n ↦ (v n : ENNReal)) atTop ≠ (⊤ : ENNReal) := by
    rw [← ENNReal.ofNNReal_limsup hv]
    simp
  have hENN :
      limsup (fun n ↦ (u n : ENNReal) * (v n : ENNReal)) atTop ≤
        limsup (fun n ↦ (u n : ENNReal)) atTop * limsup (fun n ↦ (v n : ENNReal)) atTop := by
    exact ENNReal.limsup_mul_le' (u := fun n ↦ (u n : ENNReal)) (v := fun n ↦ (v n : ENNReal))
      (f := atTop) (Or.inr hv_ne_top) (Or.inl hu_ne_top)
  exact ENNReal.coe_le_coe.mp <| by
    simpa [ENNReal.ofNNReal_limsup hu, ENNReal.ofNNReal_limsup hv,
      ENNReal.ofNNReal_limsup huv, ENNReal.coe_mul] using hENN

/-- Helper for Theorem 13.16: for nonnegative `NNReal` sequences, an upper bound on the first
sequence and an eventual upper bound on the second give the corresponding liminf product lower
bound after transport to `ENNReal`. -/
lemma nnrealLeLiminfMul {u v : ℕ → NNReal}
    (hu : atTop.IsBoundedUnder (· ≤ ·) u) (hv : atTop.IsCoboundedUnder (· ≥ ·) v) :
    liminf u atTop * liminf v atTop ≤ liminf (fun n ↦ u n * v n) atTop := by
  have huv : atTop.IsCoboundedUnder (· ≥ ·) (fun n ↦ u n * v n) := by
    exact isCoboundedUnder_ge_mul_of_nonneg
      (Filter.Eventually.of_forall fun n ↦ show (0 : NNReal) ≤ u n from bot_le) hu
      (Filter.Eventually.of_forall fun n ↦ show (0 : NNReal) ≤ v n from bot_le) hv
  have hENN :
      liminf (fun n ↦ (u n : ENNReal)) atTop * liminf (fun n ↦ (v n : ENNReal)) atTop ≤
        liminf (fun n ↦ (u n : ENNReal) * (v n : ENNReal)) atTop := by
    exact ENNReal.le_liminf_mul (u := fun n ↦ (u n : ENNReal)) (v := fun n ↦ (v n : ENNReal))
      (f := atTop)
  exact ENNReal.coe_le_coe.mp <| by
    simpa [ENNReal.ofNNReal_liminf hu.isCoboundedUnder_ge, ENNReal.ofNNReal_liminf hv,
      ENNReal.ofNNReal_liminf huv, ENNReal.coe_mul] using hENN

/-- Helper for Theorem 13.16: mass convergence together with the closed-set Portmanteau bounds
forces weak convergence of the normalized probability measures. -/
lemma tendstoNormalizeOfClosedCondition
    [Nonempty E] {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass)) (hμ : μ ≠ 0)
    (hClosed : ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F) :
    Tendsto (fun n ↦ (μs n).normalize) atTop (𝓝 μ.normalize) := by
  have hne := eventually_ne_zero_of_tendsto_mass_nonzero (μs := μs) (μ := μ) hmass hμ
  have hmassInv :
      Tendsto (fun n ↦ ((μs n).mass)⁻¹) atTop (𝓝 (μ.mass⁻¹)) :=
    Tendsto.inv₀ hmass (μ.mass_nonzero_iff.mpr hμ)
  have hmassInvBound : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ((μs n).mass)⁻¹) := by
    refine Filter.isBoundedUnder_of_eventually_le (a := μ.mass⁻¹ + 1) ?_
    filter_upwards [hmassInv (Iio_mem_nhds (by simp : μ.mass⁻¹ < μ.mass⁻¹ + 1))] with n hn
    exact hn.le
  refine tendsto_of_forall_isClosed_limsup_le_nat ?_
  intro F hF
  have hApply :
      ∀ᶠ n in atTop, (μs n).normalize F = ((μs n).mass)⁻¹ * μs n F := by
    filter_upwards [hne] with n hn
    exact (μs n).normalize_eq_of_nonzero hn F
  calc
    limsup (fun n ↦ (μs n).normalize F) atTop
        = limsup (fun n ↦ ((μs n).mass)⁻¹ * μs n F) atTop := by
          exact limsup_congr hApply
    _ ≤ limsup (fun n ↦ ((μs n).mass)⁻¹) atTop * limsup (fun n ↦ μs n F) atTop := by
          exact nnrealLimsupMulLe hmassInvBound
            (isBoundedUnderApplyOfMassTendsto (μs := μs) (μ := μ) hmass F)
    _ ≤ μ.mass⁻¹ * μ F := by
          rw [hmassInv.limsup_eq]
          exact mul_le_mul' le_rfl (hClosed F hF)
    _ = μ.normalize F := by
          symm
          exact μ.normalize_eq_of_nonzero hμ F

/-- Helper for Theorem 13.16: mass convergence together with the open-set Portmanteau bounds
forces weak convergence of the normalized probability measures. -/
lemma tendstoNormalizeOfOpenCondition
    [Nonempty E] {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass)) (hμ : μ ≠ 0)
    (hOpen : ∀ G : Set E, IsOpen G → μ G ≤ liminf (fun n ↦ μs n G) atTop) :
    Tendsto (fun n ↦ (μs n).normalize) atTop (𝓝 μ.normalize) := by
  have hne := eventually_ne_zero_of_tendsto_mass_nonzero (μs := μs) (μ := μ) hmass hμ
  have hmassInv :
      Tendsto (fun n ↦ ((μs n).mass)⁻¹) atTop (𝓝 (μ.mass⁻¹)) :=
    Tendsto.inv₀ hmass (μ.mass_nonzero_iff.mpr hμ)
  have hmassInvBound : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ((μs n).mass)⁻¹) := by
    refine Filter.isBoundedUnder_of_eventually_le (a := μ.mass⁻¹ + 1) ?_
    filter_upwards [hmassInv (Iio_mem_nhds (by simp : μ.mass⁻¹ < μ.mass⁻¹ + 1))] with n hn
    exact hn.le
  refine tendsto_of_forall_isOpen_le_liminf_nat ?_
  intro G hG
  have hApply :
      ∀ᶠ n in atTop, (μs n).normalize G = ((μs n).mass)⁻¹ * μs n G := by
    filter_upwards [hne] with n hn
    exact (μs n).normalize_eq_of_nonzero hn G
  calc
    μ.normalize G = μ.mass⁻¹ * μ G := by
        exact μ.normalize_eq_of_nonzero hμ G
    _ ≤ liminf (fun n ↦ ((μs n).mass)⁻¹) atTop * liminf (fun n ↦ μs n G) atTop := by
        rw [hmassInv.liminf_eq]
        exact mul_le_mul' le_rfl (hOpen G hG)
    _ ≤ liminf (fun n ↦ ((μs n).mass)⁻¹ * μs n G) atTop := by
        exact nnrealLeLiminfMul hmassInvBound
          (isBoundedUnderApplyOfMassTendsto (μs := μs) (μ := μ) hmass G).isCoboundedUnder_ge
    _ = liminf (fun n ↦ (μs n).normalize G) atTop := by
        symm
        exact liminf_congr hApply

/-- Helper for Theorem 13.16: after transporting the closed-set complement bound to real masses,
mass convergence upgrades it to the corresponding open-set lower bound. -/
lemma openConditionOfMassTendstoAndClosedCondition
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass))
    (hClosed : ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F) :
    ∀ G : Set E, IsOpen G → μ G ≤ liminf (fun n ↦ μs n G) atTop := by
  by_cases hμ : μ = 0
  · intro G hG
    simpa [hμ] using (show (0 : NNReal) ≤ liminf (fun n ↦ μs n G) atTop from bot_le)
  · have hE : Nonempty E := by
      by_contra hE
      haveI : IsEmpty E := not_nonempty_iff.mp hE
      have hzero : μ = 0 := by
        ext s hs
        have hs_empty : s = ∅ := Subsingleton.elim _ _
        simp [hs_empty]
      exact hμ hzero
    letI := hE
    have hnorm :=
      tendstoNormalizeOfClosedCondition (μs := μs) (μ := μ) hmass hμ hClosed
    intro G hG
    have hOpenNormMeasure :
        (μ.normalize : Measure E) G ≤
          liminf (fun n ↦ ((μs n).normalize : Measure E) G) atTop :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hnorm hG
    have hNormalizeMass :
        Tendsto (fun n ↦ ((μs n).normalize.toFiniteMeasure).mass) atTop
          (𝓝 ((μ.normalize.toFiniteMeasure).mass)) := by
      simpa [ProbabilityMeasure.mass_toFiniteMeasure] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : NNReal)) atTop (𝓝 1))
    have hOpenNorm :
        μ.normalize G ≤ liminf (fun n ↦ (μs n).normalize G) atTop := by
      exact finiteMeasureApply_le_liminf_of_measureApply_le_liminf
        (μs := fun n ↦ (μs n).normalize.toFiniteMeasure)
        (μ := μ.normalize.toFiniteMeasure)
        hNormalizeMass
        (by simpa using hOpenNormMeasure)
    have hMassBound : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ (μs n).mass) := by
      refine Filter.isBoundedUnder_of_eventually_le (a := μ.mass + 1) ?_
      filter_upwards [hmass (Iio_mem_nhds (by simp : μ.mass < μ.mass + 1))] with n hn
      exact hn.le
    have hNormalizeBound : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ (μs n).normalize G) := by
      refine Filter.isBoundedUnder_of_eventually_le (a := 1) ?_
      exact Filter.Eventually.of_forall fun n ↦ (μs n).normalize.apply_le_one G
    calc
      μ G = μ.mass * μ.normalize G := μ.self_eq_mass_mul_normalize G
      _ ≤ liminf (fun n ↦ (μs n).mass) atTop * liminf (fun n ↦ (μs n).normalize G) atTop := by
          rw [hmass.liminf_eq]
          exact mul_le_mul' le_rfl hOpenNorm
      _ ≤ liminf (fun n ↦ (μs n).mass * (μs n).normalize G) atTop := by
          exact nnrealLeLiminfMul hMassBound hNormalizeBound.isCoboundedUnder_ge
      _ = liminf (fun n ↦ μs n G) atTop := by
          refine liminf_congr <| Filter.Eventually.of_forall fun n ↦ ?_
          exact ((μs n).self_eq_mass_mul_normalize G).symm

/-- Helper for Theorem 13.16: after transporting the open-set lower bound to real masses,
mass convergence upgrades it to the corresponding closed-set limsup bound. -/
lemma closedConditionOfMassTendstoAndOpenCondition
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass))
    (hOpen : ∀ G : Set E, IsOpen G → μ G ≤ liminf (fun n ↦ μs n G) atTop) :
    ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F := by
  by_cases hμ : μ = 0
  · intro F hF
    have hENN : limsup (fun n ↦ (μs n : Measure E) F) atTop ≤ (0 : ENNReal) := by
      calc
        limsup (fun n ↦ (μs n : Measure E) F) atTop
            ≤ limsup (fun n ↦ (μs n : Measure E) Set.univ) atTop := by
              exact limsup_le_limsup (Filter.Eventually.of_forall fun n ↦ measure_mono (Set.subset_univ F))
        _ = 0 := by
              simpa [hμ, FiniteMeasure.ennreal_mass] using ((ENNReal.tendsto_coe).2 hmass).limsup_eq
    have hμzero : μ = 0 := hμ
    have hNN :
        limsup (fun n ↦ μs n F) atTop ≤ μ F := by
      simpa [hμzero] using
        finiteMeasureLimsup_le_of_measureLimsup_le (μs := μs) (μ := μ) hmass
          (by simpa [hμzero] using hENN)
    simpa [hμzero] using hNN
  · have hE : Nonempty E := by
      by_contra hE
      haveI : IsEmpty E := not_nonempty_iff.mp hE
      have hzero : μ = 0 := by
        ext s hs
        have hs_empty : s = ∅ := Subsingleton.elim _ _
        simp [hs_empty]
      exact hμ hzero
    letI := hE
    have hnorm :=
      tendstoNormalizeOfOpenCondition (μs := μs) (μ := μ) hmass hμ hOpen
    intro F hF
    have hClosedNormMeasure :
        limsup (fun n ↦ ((μs n).normalize : Measure E) F) atTop ≤
          (μ.normalize : Measure E) F :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hnorm hF
    have hNormalizeMass :
        Tendsto (fun n ↦ ((μs n).normalize.toFiniteMeasure).mass) atTop
          (𝓝 ((μ.normalize.toFiniteMeasure).mass)) := by
      simpa [ProbabilityMeasure.mass_toFiniteMeasure] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : NNReal)) atTop (𝓝 1))
    have hClosedNorm :
        limsup (fun n ↦ (μs n).normalize F) atTop ≤ μ.normalize F := by
      exact finiteMeasureLimsup_le_of_measureLimsup_le
        (μs := fun n ↦ (μs n).normalize.toFiniteMeasure)
        (μ := μ.normalize.toFiniteMeasure)
        hNormalizeMass
        (by simpa using hClosedNormMeasure)
    have hMassBound : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ (μs n).mass) := by
      refine Filter.isBoundedUnder_of_eventually_le (a := μ.mass + 1) ?_
      filter_upwards [hmass (Iio_mem_nhds (by simp : μ.mass < μ.mass + 1))] with n hn
      exact hn.le
    have hNormalizeBound : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ (μs n).normalize F) := by
      refine Filter.isBoundedUnder_of_eventually_le (a := 1) ?_
      exact Filter.Eventually.of_forall fun n ↦ (μs n).normalize.apply_le_one F
    calc
      limsup (fun n ↦ μs n F) atTop
          = limsup (fun n ↦ (μs n).mass * (μs n).normalize F) atTop := by
              exact limsup_congr <| Filter.Eventually.of_forall fun n ↦
                (μs n).self_eq_mass_mul_normalize F
      _ ≤ limsup (fun n ↦ (μs n).mass) atTop * limsup (fun n ↦ (μs n).normalize F) atTop := by
              exact nnrealLimsupMulLe hMassBound hNormalizeBound
      _ ≤ μ.mass * μ.normalize F := by
              rw [hmass.limsup_eq]
              exact mul_le_mul' le_rfl hClosedNorm
      _ = μ F := by
              exact (μ.self_eq_mass_mul_normalize F).symm

/-- Helper for Theorem 13.16: the bounded-measurable null-discontinuity criterion already implies
weak convergence, because bounded continuous functions have empty discontinuity set. -/
lemma tendstoOfNullDiscontinuityIntegralCondition
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (h :
      ∀ f : E → ℝ, Bornology.IsBounded (range f) → Measurable f →
        μ {x : E | ¬ ContinuousAt f x} = 0 →
          Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
            (𝓝 (∫ x, f x ∂(μ : Measure E)))) :
    Tendsto μs atTop (𝓝 μ) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hdisc : μ {x : E | ¬ ContinuousAt f x} = 0 := by
    -- Proof comment: a bounded continuous test function is continuous at every point, so its
    -- discontinuity set is empty.
    have hempty : {x : E | ¬ ContinuousAt f x} = ∅ := by
      ext x
      simp [f.continuous.continuousAt]
    simp [hempty]
  -- Proof comment: specialize the assumed integral criterion to the bounded continuous test
  -- function `f`.
  simpa using h f f.isBounded_range f.continuous.measurable hdisc

/-- Helper for Theorem 13.16: weak convergence implies the closed-set Portmanteau inequalities and
the lower bound on the total masses. -/
lemma closedConditionOfTendsto {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (h : Tendsto μs atTop (𝓝 μ)) :
    μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop ∧
      ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F := by
  constructor
  · -- Proof comment: total mass is continuous for the weak topology on finite measures.
    have hmass := h.mass
    rw [hmass.liminf_eq]
  · intro F hF
    -- Proof comment: this is mathlib's finite-measure closed-set Portmanteau implication.
    have hF' :
        limsup (fun n ↦ (μs n : Measure E) F) atTop ≤ (μ : Measure E) F :=
      FiniteMeasure.limsup_measure_closed_le_of_tendsto h hF
    have hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := h.mass
    have hbounded : atTop.IsBoundedUnder (· ≤ ·) (μs · F) := by
      refine Filter.isBoundedUnder_of_eventually_le (a := μ.mass + 1) ?_
      filter_upwards [hmass (Iio_mem_nhds (by simp : μ.mass < μ.mass + 1))] with n hn
      exact le_trans ((μs n).apply_le_mass F) hn.le
    have aux : ENNReal.ofNNReal (limsup (fun n ↦ μs n F) atTop) =
        limsup (ENNReal.ofNNReal ∘ fun n ↦ μs n F) atTop :=
      ENNReal.coe_mono.map_limsup_of_continuousAt (μs · F) ENNReal.continuous_coe.continuousAt
        hbounded ⟨0, by simp⟩
    have hfun : (fun n ↦ ((μs n : Measure E) F)) = ENNReal.ofNNReal ∘ fun n ↦ μs n F := by
      funext n
      simp [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Function.comp_apply]
    have hF'' : limsup (ENNReal.ofNNReal ∘ fun n ↦ μs n F) atTop ≤ ENNReal.ofNNReal (μ F) := by
      simpa [hfun, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hF'
    have hObs : ENNReal.ofNNReal (limsup (fun n ↦ μs n F) atTop) ≤ ENNReal.ofNNReal (μ F) := by
      rw [aux]
      exact hF''
    exact_mod_cast hObs

/-- Helper for Theorem 13.16: the closed-set Portmanteau condition already forces convergence of
the total masses. -/
lemma massTendstoOfClosedCondition {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hμs : ∀ n, (μs n).mass ≤ 1)
    (h :
      μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop ∧
        ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F) :
    Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := by
  -- Proof comment: `Set.univ` is closed, so the closed-set inequality supplies the missing
  -- limsup bound on the masses.
  have hmassUpper : limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass := by
    simpa using h.2 Set.univ isClosed_univ
  have hBound : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ (μs n).mass) := by
    refine Filter.isBoundedUnder_of_eventually_le (a := 1) ?_
    exact Filter.Eventually.of_forall fun n ↦ hμs n
  exact massTendstoOfLiminfLimsup hBound h.1 hmassUpper

-- TODO: derive the open-set lower bound from the closed-set limsup bound by combining the closed
-- complement estimate with the already established convergence of the total masses.
/-- Helper for Theorem 13.16: the closed-set Portmanteau inequalities imply the corresponding
open-set lower bounds together with the limsup mass bound. -/
lemma openConditionOfClosedCondition {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hμs : ∀ n, (μs n).mass ≤ 1)
    (h :
      μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop ∧
        ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F) :
    limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass ∧
      ∀ G : Set E, IsOpen G → μ G ≤ liminf (fun n ↦ μs n G) atTop := by
  have hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) :=
    massTendstoOfClosedCondition (μs := μs) (μ := μ) hμs h
  have hmassUpper : limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass := by
    simpa using h.2 Set.univ isClosed_univ
  refine ⟨hmassUpper, ?_⟩
  -- Proof comment: once mass convergence is available, the open-set lower bound is just the real
  -- complement transport of the closed-set hypothesis.
  exact openConditionOfMassTendstoAndClosedCondition (μs := μs) (μ := μ) hmass h.2

-- TODO: apply `MeasureTheory.tendsto_measure_of_le_liminf_measure_of_limsup_measure_le` to
-- `interior A ⊆ A ⊆ closure A`, using the open-set lower bound for `interior A` and the closed-set
-- upper bound recovered from the same open condition on `closure Aᶜ`.
/-- Helper for Theorem 13.16: the open-set Portmanteau inequalities imply convergence on all
measurable sets whose frontier is `μ`-null. -/
lemma nullBoundaryConditionOfOpenCondition
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hμs : ∀ n, (μs n).mass ≤ 1)
    (h :
      limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass ∧
        ∀ G : Set E, IsOpen G → μ G ≤ liminf (fun n ↦ μs n G) atTop) :
    ∀ A : Set E, MeasurableSet A → μ (frontier A) = 0 →
      Tendsto (fun n ↦ μs n A) atTop (𝓝 (μ A)) := by
  intro A hA hFrontier
  have hFrontierMeasure : (μ : Measure E) (frontier A) = 0 := by
    simpa [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hFrontier
  have hmassLower : μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop := by
    simpa using h.2 Set.univ isOpen_univ
  have hmassBound : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ (μs n).mass) := by
    refine Filter.isBoundedUnder_of_eventually_le (a := 1) ?_
    exact Filter.Eventually.of_forall hμs
  have hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) :=
    massTendstoOfLiminfLimsup hmassBound hmassLower h.1
  have hClosed :
      ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F :=
    closedConditionOfMassTendstoAndOpenCondition (μs := μs) (μ := μ) hmass h.2
  have hInteriorEq : μ A = μ (interior A) := by
    exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top (μ : Measure E) A)
      (measure_ne_top (μ : Measure E) (interior A))).mpr <|
      (measure_interior_of_null_frontier (μ := (μ : Measure E)) hFrontierMeasure).symm
  have hClosureEq : μ (closure A) = μ A := by
    exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top (μ : Measure E) (closure A))
      (measure_ne_top (μ : Measure E) A)).mpr <|
      (measure_closure_of_null_frontier (μ := (μ : Measure E)) hFrontierMeasure)
  have hApplyBound (s : Set E) : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ μs n s) := by
    refine Filter.isBoundedUnder_of_eventually_le (a := 1) ?_
    exact Filter.Eventually.of_forall fun n ↦ le_trans ((μs n).apply_le_mass s) (hμs n)
  have hLower : μ A ≤ liminf (fun n ↦ μs n A) atTop := by
    calc
      μ A = μ (interior A) := hInteriorEq
      _ ≤ liminf (fun n ↦ μs n (interior A)) atTop := h.2 (interior A) isOpen_interior
      _ ≤ liminf (fun n ↦ μs n A) atTop := by
          exact Filter.liminf_le_liminf
            (Filter.Eventually.of_forall fun n ↦ (μs n).apply_mono interior_subset)
            (isBoundedUnder_of_eventually_ge <|
              Filter.Eventually.of_forall fun n : ℕ ↦
                show (0 : NNReal) ≤ (μs n) (interior A) from bot_le)
            (isCoboundedUnder_ge_of_le atTop (x := (1 : NNReal))
              fun n : ℕ ↦ le_trans ((μs n).apply_le_mass A) (hμs n))
  have hUpper : limsup (fun n ↦ μs n A) atTop ≤ μ A := by
    calc
      limsup (fun n ↦ μs n A) atTop ≤ limsup (fun n ↦ μs n (closure A)) atTop := by
          exact limsup_le_limsup
            (Filter.Eventually.of_forall fun n ↦ (μs n).apply_mono subset_closure)
            (isCoboundedUnder_le_of_le atTop (x := (0 : NNReal)) fun n ↦ show (0 : NNReal) ≤ μs n A from bot_le)
            (hApplyBound (closure A))
      _ ≤ μ (closure A) := hClosed (closure A) isClosed_closure
      _ = μ A := hClosureEq
  have hBound : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ μs n A) := hApplyBound A
  exact massTendstoOfLiminfLimsup hBound hLower hUpper

/-- Helper for Theorem 13.16: a frontier point of a closed-ray superlevel set is either a level
point or a discontinuity point of the function. -/
lemma frontier_preimageIci_subset_preimage_level_union_discontinuity
    {g : E → ℝ} {t : ℝ} :
    frontier {x : E | t ≤ g x} ⊆ g ⁻¹' {t} ∪ {x : E | ¬ ContinuousAt g x} := by
  intro x hx
  by_cases hcont : ContinuousAt g x
  · by_cases hxt : g x = t
    · exact Or.inl hxt
    · by_cases hlt : g x < t
      · have hxMem : x ∈ {y : E | t ≤ g y}ᶜ := by
          simp [not_le.mpr hlt]
        -- Proof comment: if `g x < t` at a continuity point, then the strict sublevel set is a
        -- neighborhood of `x`, so `x` lies in the interior of the complement.
        have hnhds : {y : E | g y < t} ∈ 𝓝 x := by
          simpa [Set.preimage, Set.mem_setOf_eq] using
            hcont.preimage_mem_nhds (Iio_mem_nhds hlt)
        have hxInterior : x ∈ interior ({y : E | t ≤ g y}ᶜ) := by
          rw [mem_interior_iff_mem_nhds]
          exact mem_of_superset hnhds (by
            intro y hy
            simp at hy
            simp [not_le.mpr hy])
        have hxCompl : x ∈ frontier ({y : E | t ≤ g y}ᶜ) := by
          simpa [frontier_compl] using hx
        exact False.elim <| (mem_frontier_iff_notMem_interior hxMem).1 hxCompl hxInterior
      · have hgt : t < g x := (lt_or_gt_of_ne hxt).resolve_left hlt
        have hxMem : x ∈ {y : E | t ≤ g y} := by
          simp [hgt.le]
        -- Proof comment: if `g x > t` at a continuity point, then the strict superlevel set is a
        -- neighborhood of `x`, so `x` lies in the interior of the superlevel set itself.
        have hnhds : {y : E | t < g y} ∈ 𝓝 x := by
          simpa [Set.preimage, Set.mem_setOf_eq] using
            hcont.preimage_mem_nhds (Ioi_mem_nhds hgt)
        have hxInterior : x ∈ interior {y : E | t ≤ g y} := by
          rw [mem_interior_iff_mem_nhds]
          exact mem_of_superset hnhds (by
            intro y hy
            simp at hy
            exact hy.le)
        exact False.elim <| (mem_frontier_iff_notMem_interior hxMem).1 hx hxInterior
  · exact Or.inr hcont

/-- Helper for Theorem 13.16: if both the relevant level set and the discontinuity set are
`μ`-null, then the corresponding closed-ray superlevel set is a `μ`-continuity set. -/
lemma nullBoundary_superlevel_of_atomFree
    {μ : FiniteMeasure E} {g : E → ℝ} {t : ℝ}
    (hdisc : μ {x : E | ¬ ContinuousAt g x} = 0)
    (hlevel : μ (g ⁻¹' {t}) = 0) :
    μ (frontier {x : E | t ≤ g x}) = 0 := by
  -- Proof comment: the frontier is contained in the union of one level set and the discontinuity
  -- set, both of which are null by assumption.
  have hnull :
      (μ : Measure E) (g ⁻¹' {t} ∪ {x : E | ¬ ContinuousAt g x}) = 0 := by
    exact measure_union_null
      (by simpa [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hlevel)
      (by simpa [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hdisc)
  simpa [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    measure_mono_null
      (frontier_preimageIci_subset_preimage_level_union_discontinuity (g := g) (t := t)) hnull

/-- Helper for Theorem 13.16: the null-boundary convergence hypothesis applies to superlevel sets
at atom-free levels, and after coercion this gives convergence of their real masses. -/
lemma tendstoMeasureReal_superlevel_of_nullBoundaryCondition
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (h :
      ∀ A : Set E, MeasurableSet A → μ (frontier A) = 0 →
        Tendsto (fun n ↦ μs n A) atTop (𝓝 (μ A)))
    {g : E → ℝ} (hg : Measurable g)
    (hdisc : μ {x : E | ¬ ContinuousAt g x} = 0)
    {t : ℝ} (hlevel : μ (g ⁻¹' {t}) = 0) :
    Tendsto (fun n ↦ (μs n : Measure E).real {x | t ≤ g x}) atTop
      (𝓝 ((μ : Measure E).real {x | t ≤ g x})) := by
  have htail :
      Tendsto (fun n ↦ μs n {x : E | t ≤ g x}) atTop
        (𝓝 (μ {x : E | t ≤ g x})) := by
    -- Proof comment: the superlevel set is measurable, and the previous helper turns the atom-free
    -- level hypothesis into the required null-frontier condition.
    refine h _ (hg measurableSet_Ici) ?_
    exact nullBoundary_superlevel_of_atomFree (μ := μ) hdisc hlevel
  exact (NNReal.tendsto_coe).2 <| by
    simpa [FiniteMeasure.measureReal_eq_coe_coeFn] using htail

/-- Helper for Theorem 13.16: the real-valued superlevel-mass function
`t ↦ ν.real {x | t ≤ g x}` is measurable on every bounded interval. -/
lemma aestronglyMeasurable_measureReal_superlevel
    {ν : FiniteMeasure E} {g : E → ℝ} {M : ℝ} (hg_meas : Measurable g) :
    AEStronglyMeasurable (fun t : ℝ ↦ (ν : Measure E).real {x : E | t ≤ g x})
      (volume.restrict (Set.Ioc 0 M)) := by
  have hmeas : Measurable fun t : ℝ ↦ (ν : Measure E) {x : E | t ≤ g x} := by
    -- Proof comment: superlevel sets are antitone in the threshold parameter, so their masses are
    -- measurable before coercing from `ℝ≥0∞` to `ℝ`.
    exact Antitone.measurable (fun s t hst ↦ measure_mono (fun x hx ↦ hst.trans hx))
  simpa [measureReal_def] using
    (Measurable.ennreal_toReal hmeas).aestronglyMeasurable

/-- Helper for Theorem 13.16: a uniform bound on the total mass bounds every real-valued
superlevel mass on the same interval. -/
lemma ae_norm_measureReal_superlevel_le_of_mass_le
    {ν : FiniteMeasure E} {g : E → ℝ} {M C : ℝ}
    (hC_nonneg : 0 ≤ C) (hmass : (ν : Measure E).real Set.univ ≤ C) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 M)),
      ‖(ν : Measure E).real {x : E | t ≤ g x}‖ ≤ C := by
  refine Filter.Eventually.of_forall fun t ↦ ?_
  have htail : (ν : Measure E).real {x : E | t ≤ g x} ≤ (ν : Measure E).real Set.univ := by
    -- Proof comment: each superlevel set is contained in `Set.univ`, so its real mass is at most
    -- the total mass.
    exact measureReal_mono (Set.subset_univ _)
  simpa [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, abs_of_nonneg hC_nonneg] using
    htail.trans hmass

/-- Helper for Theorem 13.16: layer-cake rewrites the integral of a bounded nonnegative measurable
function as the integral of its real-valued superlevel masses over `Set.Ioc 0 M`. -/
lemma integral_eq_integral_Ioc_measureReal_superlevel
    {ν : FiniteMeasure E} {g : E → ℝ} {M : ℝ}
    (hg_meas : Measurable g) (hg_nonneg : ∀ x : E, 0 ≤ g x) (hg_upper : ∀ x : E, g x ≤ M) :
    ∫ x, g x ∂(ν : Measure E) =
      ∫ t, (ν : Measure E).real {x : E | t ≤ g x} ∂(volume.restrict (Set.Ioc 0 M)) := by
  have hnorm_le : ∀ x : E, ‖g x‖ ≤ M := by
    intro x
    simpa [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg x)] using hg_upper x
  have hg_int : Integrable g (ν : Measure E) := by
    -- Proof comment: boundedness by the constant `M` upgrades measurability to integrability for
    -- the finite measure `ν`.
    refine Integrable.of_bound hg_meas.aestronglyMeasurable M ?_
    exact Filter.Eventually.of_forall hnorm_le
  -- Proof comment: apply the owner layer-cake identity for bounded nonnegative functions.
  simpa using
    hg_int.integral_eq_integral_Ioc_meas_le
      (Eventually.of_forall hg_nonneg) (Eventually.of_forall hg_upper)

/-- Helper for Theorem 13.16: a bounded nonnegative measurable function is determined by its
superlevel measures on `Set.Ioc 0 M`, so almost-everywhere convergence of those real-valued
superlevel masses plus a uniform mass bound yields convergence of the integrals. -/
lemma tendstoIntegralOfNonnegativeBoundedOfSuperlevelTendsto
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    {g : E → ℝ} {M C : ℝ}
    (hg_meas : Measurable g) (hM_nonneg : 0 ≤ M)
    (hg_nonneg : ∀ x : E, 0 ≤ g x) (hg_upper : ∀ x : E, g x ≤ M)
    (hC_nonneg : 0 ≤ C)
    (hmass_bound : ∀ n, (μs n : Measure E).real Set.univ ≤ C)
    (hpointwise :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 M)),
        Tendsto (fun n ↦ (μs n : Measure E).real {x : E | t ≤ g x}) atTop
          (𝓝 ((μ : Measure E).real {x : E | t ≤ g x}))) :
    Tendsto (fun n ↦ ∫ x, g x ∂(μs n : Measure E)) atTop
      (𝓝 (∫ x, g x ∂(μ : Measure E))) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc 0 M)) := ⟨by
    simpa using (measure_Ioc_lt_top (a := (0 : ℝ)) (b := M)).ne⟩
  have hC_int : Integrable (fun _ : ℝ ↦ C) (volume.restrict (Set.Ioc 0 M)) := integrable_const C
  have hOuter :
      Tendsto
        (fun n ↦ ∫ t, (μs n : Measure E).real {x : E | t ≤ g x} ∂(volume.restrict (Set.Ioc 0 M)))
        atTop
        (𝓝 (∫ t, (μ : Measure E).real {x : E | t ≤ g x} ∂(volume.restrict (Set.Ioc 0 M)))) := by
    -- Proof comment: dominated convergence applies on the outer interval because the superlevel
    -- masses are pointwise convergent almost everywhere and uniformly dominated by `C`.
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ ↦ C)
      (fun n ↦ aestronglyMeasurable_measureReal_superlevel (ν := μs n) (g := g) (M := M) hg_meas)
      hC_int
      (fun n ↦ ae_norm_measureReal_superlevel_le_of_mass_le
        (ν := μs n) (g := g) (M := M) hC_nonneg (hmass_bound n))
      hpointwise
  have hOuter' :
      Tendsto (fun n ↦ ∫ x, g x ∂(μs n : Measure E)) atTop
        (𝓝 (∫ t, (μ : Measure E).real {x : E | t ≤ g x} ∂(volume.restrict (Set.Ioc 0 M)))) := by
    refine (tendsto_congr' <| Filter.Eventually.of_forall fun n ↦ ?_).2 hOuter
    simpa using
      integral_eq_integral_Ioc_measureReal_superlevel
        (ν := μs n) (g := g) (M := M) hg_meas hg_nonneg hg_upper
  -- Proof comment: rewrite the limit integral by the same layer-cake identity.
  simpa [integral_eq_integral_Ioc_measureReal_superlevel
    (ν := μ) (g := g) (M := M) hg_meas hg_nonneg hg_upper] using hOuter'

/-- Helper for Theorem 13.16: convergence on all `μ`-continuity sets implies convergence of the
integrals of every bounded measurable function whose discontinuity set is `μ`-null. -/
lemma tendstoIntegralOfNullDiscontinuityOfNullBoundaryCondition
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (h :
      ∀ A : Set E, MeasurableSet A → μ (frontier A) = 0 →
        Tendsto (fun n ↦ μs n A) atTop (𝓝 (μ A))) :
    ∀ f : E → ℝ, Bornology.IsBounded (range f) → Measurable f →
      μ {x : E | ¬ ContinuousAt f x} = 0 →
        Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
          (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
  intro f hf_bdd hf_meas hdisc
  -- Route correction: the earlier finite partition route kept getting stuck on `Ioc`-cell
  -- frontier bookkeeping, so this proof shifts `f` to a nonnegative bounded function and applies
  -- layer-cake plus dominated convergence on the superlevel measures.
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hf_bdd
  let R : ℝ := max B 0
  have hR_nonneg : 0 ≤ R := le_max_right _ _
  have hnorm_le : ∀ x : E, ‖f x‖ ≤ R := by
    intro x
    exact (hB _ ⟨x, rfl⟩).trans (le_max_left _ _)
  have hlower : ∀ x : E, -R ≤ f x := by
    intro x
    exact (abs_le.mp <| by simpa [Real.norm_eq_abs] using hnorm_le x).1
  have hupper : ∀ x : E, f x ≤ R := by
    intro x
    exact (abs_le.mp <| by simpa [Real.norm_eq_abs] using hnorm_le x).2
  let g : E → ℝ := fun x ↦ f x + R
  let I : Set ℝ := Set.Ioc 0 (2 * R)
  let F : ℕ → ℝ → ℝ := fun n t ↦ (μs n : Measure E).real {x : E | t ≤ g x}
  let Fμ : ℝ → ℝ := fun t ↦ (μ : Measure E).real {x : E | t ≤ g x}
  have hg_meas : Measurable g := hf_meas.add measurable_const
  have hg_nonneg : ∀ x : E, 0 ≤ g x := by
    intro x
    dsimp [g]
    linarith [hlower x]
  have hg_upper : ∀ x : E, g x ≤ 2 * R := by
    intro x
    dsimp [g]
    linarith [hupper x, hR_nonneg]
  have hdisc_g : μ {x : E | ¬ ContinuousAt g x} = 0 := by
    have hcont_iff : ∀ x : E, ContinuousAt g x ↔ ContinuousAt f x := by
      intro x
      constructor
      · intro hx
        have hx' : ContinuousAt (fun y : E ↦ g y + (-R)) x := hx.add continuousAt_const
        simpa [g, add_assoc] using hx'
      · intro hx
        simpa [g] using hx.add continuousAt_const
    have hset :
        {x : E | ¬ ContinuousAt g x} = {x : E | ¬ ContinuousAt f x} := by
      ext x
      simp [hcont_iff x]
    simpa [hset] using hdisc
  have hmass :
      Tendsto (fun n ↦ (μs n : Measure E).real Set.univ) atTop
        (𝓝 ((μ : Measure E).real Set.univ)) := by
    -- Proof comment: `Set.univ` is a continuity set, so the hypothesis already gives convergence
    -- of the total masses.
    exact (NNReal.tendsto_coe).2 <| by
      simpa [frontier_univ, FiniteMeasure.measureReal_eq_coe_coeFn] using
        h Set.univ MeasurableSet.univ (by simp)
  have hmassRange :
      Bornology.IsBounded (range fun n ↦ (μs n : Measure E).real Set.univ) :=
    Metric.isBounded_range_of_tendsto _ hmass
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hmassRange
  let C0 : ℝ := max C 0
  have hmass_bound : ∀ n, (μs n : Measure E).real Set.univ ≤ C0 := by
    intro n
    have hCn : ‖(μs n : Measure E).real Set.univ‖ ≤ C := hC _ ⟨n, rfl⟩
    have hCn' : (μs n : Measure E).real Set.univ ≤ C := by
      simpa [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using hCn
    exact hCn'.trans (le_max_left _ _)
  have hf_int_μs : ∀ n, Integrable f (μs n : Measure E) := by
    intro n
    refine Integrable.of_bound hf_meas.aestronglyMeasurable R ?_
    exact Filter.Eventually.of_forall hnorm_le
  have hf_int_μ : Integrable f (μ : Measure E) := by
    refine Integrable.of_bound hf_meas.aestronglyMeasurable R ?_
    exact Filter.Eventually.of_forall hnorm_le
  have hg_int_μs : ∀ n, Integrable g (μs n : Measure E) := by
    intro n
    dsimp [g]
    exact (hf_int_μs n).add (integrable_const R)
  have hg_int_μ : Integrable g (μ : Measure E) := by
    dsimp [g]
    exact hf_int_μ.add (integrable_const R)
  let atoms : Set ℝ := {t : ℝ | 0 < (μ : Measure E) (g ⁻¹' {t})}
  have hatoms_countable : atoms.Countable :=
    MeasureTheory.Measure.countable_meas_level_set_pos (μ := (μ : Measure E)) hg_meas
  have hpointwise :
      ∀ᵐ t ∂(volume.restrict I), Tendsto (fun n ↦ F n t) atTop (𝓝 (Fμ t)) := by
    have hatoms_ae : atomsᶜ ∈ ae (volume.restrict I) := by
      exact compl_mem_ae_iff.2 (hatoms_countable.measure_zero (μ := volume.restrict I))
    filter_upwards [hatoms_ae] with t ht
    have hlevel : μ (g ⁻¹' {t}) = 0 := by
      by_contra hlevel
      have hlevel_pos : 0 < (μ : Measure E) (g ⁻¹' {t}) := by
        exact pos_iff_ne_zero.mpr <| by
          simpa [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hlevel
      exact ht (by
        change t ∈ atoms
        simpa [atoms] using hlevel_pos)
    -- Proof comment: outside the countable exceptional set of atom levels, each superlevel set is
    -- a `μ`-continuity set, so the hypothesis gives convergence of its real mass.
    simpa [F, Fμ] using
      tendstoMeasureReal_superlevel_of_nullBoundaryCondition
        (μs := μs) (μ := μ) h hg_meas hdisc_g hlevel
  have hg_tendsto :
      Tendsto (fun n ↦ ∫ x, g x ∂(μs n : Measure E)) atTop
        (𝓝 (∫ x, g x ∂(μ : Measure E))) := by
    -- Proof comment: the previous helper packages the layer-cake rewrite and dominated
    -- convergence, so only the pointwise superlevel convergence and the mass bound remain here.
    simpa [I, F, Fμ] using
      tendstoIntegralOfNonnegativeBoundedOfSuperlevelTendsto
        (μs := μs) (μ := μ) (g := g) (M := 2 * R) (C := C0)
        hg_meas (by positivity) hg_nonneg hg_upper (le_max_right _ _) hmass_bound hpointwise
  have hShift_μs :
      ∀ n, ∫ x, g x ∂(μs n : Measure E) =
        ∫ x, f x ∂(μs n : Measure E) + R * (μs n : Measure E).real Set.univ := by
    intro n
    -- Proof comment: shifting by the constant `R` isolates the mass term of `μs n`.
    dsimp [g]
    rw [integral_add (hf_int_μs n) (integrable_const R), integral_const]
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have hShift_μ :
      ∫ x, g x ∂(μ : Measure E) =
        ∫ x, f x ∂(μ : Measure E) + R * (μ : Measure E).real Set.univ := by
    dsimp [g]
    rw [integral_add hf_int_μ (integrable_const R), integral_const]
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have hmassScaled :
      Tendsto (fun n ↦ R * (μs n : Measure E).real Set.univ) atTop
        (𝓝 (R * (μ : Measure E).real Set.univ)) := by
    exact tendsto_const_nhds.mul hmass
  have hf_tendsto' :
      Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
        (𝓝 (∫ x, g x ∂(μ : Measure E) - R * (μ : Measure E).real Set.univ)) := by
    have hsub := hg_tendsto.sub hmassScaled
    refine (tendsto_congr' <| Filter.Eventually.of_forall fun n ↦ ?_).2 hsub
    rw [hShift_μs n]
    ring
  have hShift_μ_sub :
      ∫ x, g x ∂(μ : Measure E) - R * (μ : Measure E).real Set.univ =
        ∫ x, f x ∂(μ : Measure E) := by
    rw [hShift_μ]
    ring
  exact hShift_μ_sub ▸ hf_tendsto'

section LocallyCompact

variable [LocallyCompactSpace E] [PolishSpace E]

/-- Helper for Theorem 13.16: weak convergence on a locally compact Polish space implies vague
convergence of the underlying Radon measures together with convergence of the total masses. -/
lemma weakImpliesVagueAndMass {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (h : Tendsto μs atTop (𝓝 μ)) :
    radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
      Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := by
  constructor
  · -- Proof comment: compactly supported continuous functions are bounded continuous, so weak
    -- convergence immediately gives the vague test-function convergence.
    refine ⟨IsRadonMeasure.of_owner (μ : Measure E), ?_, ?_⟩
    · intro n
      exact IsRadonMeasure.of_owner (μs n : Measure E)
    · intro f
      simpa using
        (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp h)
          f.toBoundedContinuousFunction
  · -- Proof comment: mass is continuous for weak convergence of finite measures.
    exact h.mass

/-- Helper for Theorem 13.16: in the vague-convergence branch, the one-sided mass upper bound
upgrades to full mass convergence using Lemma 13.15. -/
lemma vagueAndLimsupMassImpliesMassTendsto {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hμs : ∀ n, (μs n).mass ≤ 1)
    (h :
      radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
        limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass) :
    radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
      Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := by
  refine ⟨h.1, ?_⟩
  have hLowerENNReal :
      (μ : Measure E) Set.univ ≤ liminf (fun n ↦ (μs n : Measure E) Set.univ) atTop :=
    measure_univ_le_liminf_of_vaguely_converges h.1
  have hLower :
      μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop := by
    have hAux :
        ENNReal.ofNNReal (liminf (fun n ↦ (μs n).mass) atTop) =
          liminf (ENNReal.ofNNReal ∘ fun n ↦ (μs n).mass) atTop := by
      -- Proof comment: the total masses stay in `[0,1]`, so `ENNReal.ofNNReal` transports the
      -- liminf of the `NNReal` mass sequence without introducing extra coercion churn.
      refine Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono
        (fun n ↦ (μs n).mass) ?_ ?_ ?_
      · exact ENNReal.continuous_coe.continuousAt
      · exact isCoboundedUnder_ge_of_le atTop hμs
      · exact ⟨0, by simp⟩
    have hMassFun :
        (fun n ↦ (μs n : Measure E) Set.univ) =
          ENNReal.ofNNReal ∘ fun n ↦ (μs n).mass := by
      funext n
      simp [FiniteMeasure.ennreal_mass, Function.comp_apply]
    have hLower' :
        ENNReal.ofNNReal μ.mass ≤
          liminf (ENNReal.ofNNReal ∘ fun n ↦ (μs n).mass) atTop := by
      -- Proof comment: rewrite the vague lower-mass bound through the finite-measure total-mass
      -- API before collapsing the `ENNReal.ofNNReal` liminf transport back to `NNReal`.
      simpa [hMassFun, Function.comp_apply] using hLowerENNReal
    have hLower'' :
        ENNReal.ofNNReal μ.mass ≤ ENNReal.ofNNReal (liminf (fun n ↦ (μs n).mass) atTop) := by
      simpa [hAux] using hLower'
    exact ENNReal.coe_le_coe.mp hLower''
  have hBound : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ (μs n).mass) := by
    -- Proof comment: the subprobability hypothesis keeps every mass below `1`, providing the
    -- boundedness input needed by the abstract squeeze lemma.
    refine Filter.isBoundedUnder_of_eventually_le (a := 1) ?_
    exact Filter.Eventually.of_forall hμs
  exact massTendstoOfLiminfLimsup hBound hLower h.2

/-- Helper for Theorem 13.16: if a thickening of `K` stays inside an open set with compact
closure, then the real-valued thickened indicator defines an element of `C_c(E, ℝ)`. -/
lemma compactlySupportedThickenedIndicator
    {K V : Set E} {ε : ℝ} (hε : 0 < ε)
    (hthick : Metric.thickening ε K ⊆ V) (hVc : IsCompact (closure V)) :
    ∃ g : C_c(E, ℝ), (g : E → ℝ) = fun x : E ↦ (thickenedIndicator hε K x : ℝ) := by
  have hContinuous :
      Continuous (fun x : E ↦ (thickenedIndicator hε K x : ℝ)) := by
    -- Proof comment: the thickened indicator is already a bundled continuous `NNReal`-valued map,
    -- so coercing to `ℝ` preserves continuity.
    exact NNReal.continuous_coe.comp (thickenedIndicator hε K).continuous
  let f : C(E, ℝ) := ⟨fun x : E ↦ (thickenedIndicator hε K x : ℝ), hContinuous⟩
  have hsupport :
      Function.support (fun x : E ↦ (thickenedIndicator hε K x : ℝ)) ⊆ closure V := by
    -- Proof comment: outside `closure V` the point is not in `V`, hence not in the whole
    -- thickening of `K`, so the cutoff vanishes there.
    refine Function.support_subset_iff'.2 ?_
    intro x hxV
    have hx_not_mem_V : x ∉ V := fun hx => hxV (subset_closure hx)
    have hx_not_thick : x ∉ Metric.thickening ε K := by
      intro hx_thick
      exact hx_not_mem_V (hthick hx_thick)
    simp [thickenedIndicator_zero hε K hx_not_thick]
  -- Proof comment: the support lies in the compact set `closure V`, so the continuous cutoff is
  -- compactly supported.
  refine ⟨⟨f, HasCompactSupport.of_support_subset_isCompact hVc hsupport⟩, rfl⟩

/-- Helper for Theorem 13.16: on a locally compact Polish space, vague convergence together with
mass convergence implies the open-set Portmanteau lower bounds. -/
lemma openConditionOfVagueAndMass {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (h :
      radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
        Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass)) :
    limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass ∧
      ∀ G : Set E, IsOpen G → μ G ≤ liminf (fun n ↦ μs n G) atTop := by
  rcases h.1 with ⟨hμ, hμs, htest⟩
  refine ⟨by simpa using h.2.limsup_eq.le, ?_⟩
  intro G hG
  letI : IsRadonMeasure (μ : Measure E) := hμ
  letI : Measure.Regular (μ : Measure E) := inferInstance
  have hBoundG : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ μs n G) :=
    isBoundedUnderApplyOfMassTendsto (μs := μs) (μ := μ) h.2 G
  refine (le_liminf_iff hBoundG.isCoboundedUnder_ge
    (isBoundedUnder_of_eventually_ge <|
      Filter.Eventually.of_forall fun n : ℕ ↦ show (0 : NNReal) ≤ μs n G from bot_le)).2 ?_
  intro r hr
  have hrENN : (r : ENNReal) < (μ : Measure E) G := by
    simpa [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      (show (r : ENNReal) < (μ G : ENNReal) from ENNReal.coe_lt_coe.mpr hr)
  obtain ⟨K, hKG, hKCompact, hrK⟩ := hG.exists_lt_isCompact (μ := (μ : Measure E)) hrENN
  obtain ⟨V, hVOpen, hKV, hVClosureSubset, hVClosureCompact⟩ :=
    exists_open_between_and_isCompact_closure hKCompact hG hKG
  obtain ⟨ε, hε, hThick⟩ := hKCompact.exists_thickening_subset_open hVOpen hKV
  obtain ⟨g, hg_eq⟩ :=
    compactlySupportedThickenedIndicator (K := K) (V := V) hε hThick hVClosureCompact
  have hgIntμ : Integrable g (μ : Measure E) :=
    g.1.continuous.integrable_of_hasCompactSupport g.2
  have hμK_le_integral : (μ : Measure E).real K ≤ ∫ x, g x ∂(μ : Measure E) := by
    rw [← integral_indicator_one hKCompact.measurableSet]
    refine integral_mono ?_ hgIntμ ?_
    · exact (integrable_indicator_iff hKCompact.measurableSet).mpr (integrable_const (1 : ℝ)).integrableOn
    · intro x
      by_cases hx : x ∈ K
      · simp [hx, hg_eq, thickenedIndicator_one hε K hx]
      · have hnonneg : 0 ≤ (g x : ℝ) := by
          rw [hg_eq]
          exact_mod_cast (show (0 : NNReal) ≤ thickenedIndicator hε K x from bot_le)
        simpa [hx] using hnonneg
  have hrIntegral : (r : ℝ) < ∫ x, g x ∂(μ : Measure E) := by
    have hrKNN : r < μ K := by
      exact ENNReal.coe_lt_coe.mp <| by
        simpa [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hrK
    have hrKReal : (r : ℝ) < (μ : Measure E).real K := by
      simpa [FiniteMeasure.measureReal_eq_coe_coeFn] using hrKNN
    exact lt_of_lt_of_le hrKReal hμK_le_integral
  have hEventuallyIntegral :
      ∀ᶠ n in atTop, (r : ℝ) < ∫ x, g x ∂(μs n : Measure E) :=
    (htest g).eventually_const_lt hrIntegral
  filter_upwards [hEventuallyIntegral] with n hn
  have hgIntμs : Integrable g (μs n : Measure E) :=
    g.1.continuous.integrable_of_hasCompactSupport g.2
  have hIntegral_le_measure : ∫ x, g x ∂(μs n : Measure E) ≤ (μs n : Measure E).real G := by
    rw [← integral_indicator_one hG.measurableSet]
    refine integral_mono hgIntμs ?_ ?_
    · exact (integrable_indicator_iff hG.measurableSet).mpr (integrable_const (1 : ℝ)).integrableOn
    · intro x
      by_cases hxG : x ∈ G
      · have hg_le_one : (g x : ℝ) ≤ 1 := by
          rw [hg_eq]
          exact_mod_cast (thickenedIndicator_le_one hε K x)
        simpa [hxG] using hg_le_one
      · have hx_not_thick : x ∉ Metric.thickening ε K := by
          intro hx_thick
          have hxV : x ∈ V := hThick hx_thick
          exact hxG (hVClosureSubset (subset_closure hxV))
        have hg_zero : (g x : ℝ) = 0 := by
          rw [hg_eq]
          exact congrArg (fun t : NNReal ↦ (t : ℝ)) (thickenedIndicator_zero hε K hx_not_thick)
        simp [hxG, hg_zero]
  simpa [FiniteMeasure.measureReal_eq_coe_coeFn] using lt_of_lt_of_le hn hIntegral_le_measure

end LocallyCompact

-- Proof sketch: for the first six clauses, pass between finite subprobability measures and their
-- normalized probability measures, then combine mathlib's weak-convergence characterization for
-- `FiniteMeasure`, the probability-measure Portmanteau implications, and the null-boundary
-- criterion. Under local compactness and Polish assumptions, identify vague convergence plus mass
-- control with weak convergence via the source-facing predicate
-- `radonMeasureVaguelyConvergesTo`.
/-- Theorem 13.16: For subprobability finite measures on a metric space, weak convergence, the
bounded-Lipschitz and bounded-measurable test-function criteria, the closed/open Portmanteau
inequalities, and convergence on `μ`-continuity sets are equivalent; if the space is locally
compact and Polish, the two vague-convergence formulations are equivalent to the same conditions. -/
theorem portmanteau_subprobability_tfae (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1) :
    List.TFAE
      [ Tendsto μs atTop (𝓝 μ)
      , ∀ f : E → ℝ, Bornology.IsBounded (range f) → (∃ L, LipschitzWith L f) →
          Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
            (𝓝 (∫ x, f x ∂(μ : Measure E)))
      , ∀ f : E → ℝ, Bornology.IsBounded (range f) → Measurable f →
          μ {x : E | ¬ ContinuousAt f x} = 0 →
            Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
              (𝓝 (∫ x, f x ∂(μ : Measure E)))
      , μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop ∧
          ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F
      , limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass ∧
          ∀ G : Set E, IsOpen G → μ G ≤ liminf (fun n ↦ μs n G) atTop
      , ∀ A : Set E, MeasurableSet A → μ (frontier A) = 0 →
          Tendsto (fun n ↦ μs n A) atTop (𝓝 (μ A))
      ] ∧
      (∀ [LocallyCompactSpace E] [PolishSpace E],
        List.TFAE
          [ Tendsto μs atTop (𝓝 μ)
          , ∀ f : E → ℝ, Bornology.IsBounded (range f) → (∃ L, LipschitzWith L f) →
              Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
                (𝓝 (∫ x, f x ∂(μ : Measure E)))
          , ∀ f : E → ℝ, Bornology.IsBounded (range f) → Measurable f →
              μ {x : E | ¬ ContinuousAt f x} = 0 →
                Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
                  (𝓝 (∫ x, f x ∂(μ : Measure E)))
          , μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop ∧
              ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F
          , limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass ∧
              ∀ G : Set E, IsOpen G → μ G ≤ liminf (fun n ↦ μs n G) atTop
          , ∀ A : Set E, MeasurableSet A → μ (frontier A) = 0 →
              Tendsto (fun n ↦ μs n A) atTop (𝓝 (μ A))
          , radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
              Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass)
          , radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
              limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass
          ]) := by
  -- Proof comment: the first six clauses form the standard Portmanteau cycle for finite
  -- subprobability measures.
  constructor
  · tfae_have 1 → 2 := by
      exact tendstoIntegralOfBoundedLipschitzOfTendsto (μs := μs) (μ := μ)
    tfae_have 2 → 1 := by
      exact tendstoOfBoundedLipschitzIntegralCondition (μs := μs) (μ := μ)
    tfae_have 1 → 4 := by
      exact closedConditionOfTendsto (μs := μs) (μ := μ)
    tfae_have 4 → 5 := by
      exact openConditionOfClosedCondition (μs := μs) (μ := μ) hμs
    tfae_have 5 → 6 := by
      exact nullBoundaryConditionOfOpenCondition (μs := μs) (μ := μ) hμs
    tfae_have 6 → 3 := by
      exact tendstoIntegralOfNullDiscontinuityOfNullBoundaryCondition (μs := μs) (μ := μ)
    tfae_have 3 → 1 := by
      exact tendstoOfNullDiscontinuityIntegralCondition (μs := μs) (μ := μ)
    tfae_finish
  · intro _ _
    -- Proof comment: in the locally compact Polish case, add the vague-plus-mass formulations to
    -- the same six-clause cycle.
    tfae_have 1 → 2 := by
      exact tendstoIntegralOfBoundedLipschitzOfTendsto (μs := μs) (μ := μ)
    tfae_have 2 → 1 := by
      exact tendstoOfBoundedLipschitzIntegralCondition (μs := μs) (μ := μ)
    tfae_have 1 → 4 := by
      exact closedConditionOfTendsto (μs := μs) (μ := μ)
    tfae_have 4 → 5 := by
      exact openConditionOfClosedCondition (μs := μs) (μ := μ) hμs
    tfae_have 5 → 6 := by
      exact nullBoundaryConditionOfOpenCondition (μs := μs) (μ := μ) hμs
    tfae_have 6 → 3 := by
      exact tendstoIntegralOfNullDiscontinuityOfNullBoundaryCondition (μs := μs) (μ := μ)
    tfae_have 3 → 1 := by
      exact tendstoOfNullDiscontinuityIntegralCondition (μs := μs) (μ := μ)
    tfae_have 1 → 7 := by
      exact weakImpliesVagueAndMass (μs := μs) (μ := μ)
    tfae_have 7 → 8 := by
      intro h
      exact ⟨h.1, by rw [h.2.limsup_eq]⟩
    tfae_have 8 → 7 := by
      exact vagueAndLimsupMassImpliesMassTendsto (μs := μs) (μ := μ) hμs
    tfae_have 7 → 5 := by
      exact openConditionOfVagueAndMass (μs := μs) (μ := μ)
    tfae_finish

end Portmanteau

end FiniteMeasure
end MeasureTheory
