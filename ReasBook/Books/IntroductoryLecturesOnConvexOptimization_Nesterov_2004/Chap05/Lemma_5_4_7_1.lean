/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

open scoped PowerConePlus
open Filter

/- Lemma 5.4.7.1 lies in the Chapter 5 power-cone / self-concordant-barrier domain.

Sampled owner declarations:
* `power_cone_plus` from `Definition_5_4_7_4`, the source-facing owner for the one-sided power
  cone `K_α^+`;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  from `Theorem_5_4_1_2`, the canonical barrier-parameter lower-bound owner theorem;
* `Chap05RealProdL2.instInnerProductSpaceRealProdProd` from `RealProdL2`, the chapter owner
  bridge equipping the raw triple model `((ℝ × ℝ) × ℝ)` with the canonical Euclidean `L²`
  ambient structure needed by the barrier owner theorem.

Source/core/bridge triage:
* source-facing: the lower bound `ν ≥ 3` for barriers on `K_[α]⁺`;
* core/canonical: the barrier owner
  `IsSelfConcordantBarrierOnWith (interior (K_[α]⁺)) ν F`;
* bridge/view: the shared `RealProdL2` ambient-instance activation together with the proof-level
  recession directions `((1, 0), 0)`, `((0, 1), 0)`, and `((0, 0), -1)` and the auxiliary point
  family `((1, 1), -τ)`.

Primitive data:
* the source-facing cone owner `K_[α]⁺`;
* the barrier owner `hF : IsSelfConcordantBarrierOnWith (interior (K_[α]⁺)) ν F`.

Derived API:
* the source-facing lower bound `(3 : ℝ) ≤ (ν : ℝ)`.

The source-facing cone owner `K_[α]⁺` remains the public surface. This file now reuses the
chapter-wide `RealProdL2` ambient bridge instead of repeating local `WithLp` instance blocks, and
the explicit recession directions remain proof-only data rather than public API. -/

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` directly to the cone
-- `K_[α]⁺` with recession directions `((1, 0), 0)`, `((0, 1), 0)`, and
-- `((0, 0), -1)`, base point `((1, 1), -τ)`, and coefficients
-- `α₁ = α₂ = β₁ = β₂ = 1`, `α₃ = τ`, `β₃ = 1 + τ`. This gives
-- `ν ≥ 2 + τ / (1 + τ)`. Under the contradiction hypothesis `ν < 3`, choosing
-- `τ = ν / (3 - ν)` turns this into `2 + ν / 3 ≤ ν`, which is impossible.
/-- Helper for Lemma 5.4.7.1: strict positivity of the first two coordinates together with strict
slack places a point in `interior (K_[α]⁺)`. -/
private theorem strict_mem_interior_powerConePlus
    {α x₁ x₂ z : ℝ} (hα_nonneg : 0 ≤ α) (hOne_sub_nonneg : 0 ≤ 1 - α)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hz : z < powerConeGeometricMean α (x₁, x₂)) :
    ((x₁, x₂), z) ∈ interior (K_[α]⁺) := by
  let q : ((ℝ × ℝ) × ℝ) := ((x₁, x₂), z)
  let slack : ((ℝ × ℝ) × ℝ) → ℝ := fun y ↦ powerConeGeometricMean α y.1 - y.2
  have hslack_pos : 0 < slack q := by
    simpa [q, slack] using sub_pos.mpr hz
  have hslack_cont : ContinuousAt slack q := by
    -- The slack map is continuous because both fixed-exponent `rpow` factors are continuous.
    have hfst :
        ContinuousAt (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.rpow y.1.1 α) q := by
      simpa using continuousAt_fst.fst.rpow_const (Or.inr hα_nonneg)
    have hsnd :
        ContinuousAt (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.rpow y.1.2 (1 - α)) q := by
      simpa using continuousAt_fst.snd.rpow_const (Or.inr hOne_sub_nonneg)
    have hmul :
        ContinuousAt
          (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.rpow y.1.1 α * Real.rpow y.1.2 (1 - α))
          q :=
      hfst.mul hsnd
    simpa [slack, powerConeGeometricMean_apply] using hmul.sub continuousAt_snd
  have hfirst :
      (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.1) ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
    continuousAt_fst.fst.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx₁)
  have hsecond :
      (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.2) ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
    continuousAt_fst.snd.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx₂)
  have hslack :
      slack ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
    hslack_cont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hslack_pos)
  -- Intersect the three strict neighborhoods and rewrite them back to cone membership.
  rw [mem_interior_iff_mem_nhds]
  refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem hfirst hsecond) hslack) ?_
  rintro y ⟨⟨hy₁, hy₂⟩, hy₃⟩
  rw [mem_power_cone_plus_iff]
  refine ⟨le_of_lt hy₁, le_of_lt hy₂, ?_⟩
  have hy₃' : 0 < powerConeGeometricMean α y.1 - y.2 := by
    simpa [slack] using hy₃
  linarith

/-- Helper for Lemma 5.4.7.1: interior points of `K_[α]⁺` have strictly positive coordinates and
strict slack. -/
private theorem strict_of_mem_interior_powerConePlus
    {α x₁ x₂ z : ℝ} (hx : ((x₁, x₂), z) ∈ interior (K_[α]⁺)) :
    0 < x₁ ∧ 0 < x₂ ∧ z < powerConeGeometricMean α (x₁, x₂) := by
  have hcone : ((x₁, x₂), z) ∈ K_[α]⁺ := interior_subset hx
  have hmem := (mem_power_cone_plus_iff α x₁ x₂ z).1 hcone
  have hx₁_nonneg : 0 ≤ x₁ := hmem.1
  have hx₂_nonneg : 0 ≤ x₂ := hmem.2.1
  have hx₁_pos : 0 < x₁ := by
    by_contra hx₁_not
    have hx₁_zero : x₁ = 0 := le_antisymm (le_of_not_gt hx₁_not) hx₁_nonneg
    let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun s ↦ ((s, x₂), z)
    have hpre :
        γ ⁻¹' interior (K_[α]⁺) ∈ nhds x₁ := by
      exact (show Continuous γ by fun_prop).continuousAt.preimage_mem_nhds <|
        IsOpen.mem_nhds isOpen_interior (by simpa [γ] using hx)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
    have hneg : -ε / 2 ∈ Metric.ball x₁ ε := by
      have hhalf_neg : -ε / 2 < 0 := by linarith
      have habs : |(-ε / 2 : ℝ) - 0| = ε / 2 := by
        rw [sub_zero, abs_of_neg hhalf_neg]
        ring
      rw [hx₁_zero, Metric.mem_ball, Real.dist_eq, habs]
      linarith
    have hbad : γ (-ε / 2) ∈ K_[α]⁺ := interior_subset (hεsub hneg)
    have hbad_mem := (mem_power_cone_plus_iff α (-ε / 2) x₂ z).1 hbad
    linarith
  have hx₂_pos : 0 < x₂ := by
    by_contra hx₂_not
    have hx₂_zero : x₂ = 0 := le_antisymm (le_of_not_gt hx₂_not) hx₂_nonneg
    let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun s ↦ ((x₁, s), z)
    have hpre :
        γ ⁻¹' interior (K_[α]⁺) ∈ nhds x₂ := by
      exact (show Continuous γ by fun_prop).continuousAt.preimage_mem_nhds <|
        IsOpen.mem_nhds isOpen_interior (by simpa [γ] using hx)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
    have hneg : -ε / 2 ∈ Metric.ball x₂ ε := by
      have hhalf_neg : -ε / 2 < 0 := by linarith
      have habs : |(-ε / 2 : ℝ) - 0| = ε / 2 := by
        rw [sub_zero, abs_of_neg hhalf_neg]
        ring
      rw [hx₂_zero, Metric.mem_ball, Real.dist_eq, habs]
      linarith
    have hbad : γ (-ε / 2) ∈ K_[α]⁺ := interior_subset (hεsub hneg)
    have hbad_mem := (mem_power_cone_plus_iff α x₁ (-ε / 2) z).1 hbad
    linarith
  have hz_strict : z < powerConeGeometricMean α (x₁, x₂) := by
    by_contra hz_not
    have hz_eq : z = powerConeGeometricMean α (x₁, x₂) := le_antisymm hmem.2.2 (not_lt.mp hz_not)
    let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun s ↦ ((x₁, x₂), s)
    have hpre :
        γ ⁻¹' interior (K_[α]⁺) ∈ nhds z := by
      exact (show Continuous γ by fun_prop).continuousAt.preimage_mem_nhds <|
        IsOpen.mem_nhds isOpen_interior (by simpa [γ] using hx)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
    have hup : z + ε / 2 ∈ Metric.ball z ε := by
      have hhalf_nonneg : 0 ≤ z + ε / 2 - z := by linarith
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hhalf_nonneg]
      linarith
    have hbad : γ (z + ε / 2) ∈ K_[α]⁺ := interior_subset (hεsub hup)
    have hbad_mem := (mem_power_cone_plus_iff α x₁ x₂ (z + ε / 2)).1 hbad
    rw [hz_eq] at hbad_mem
    linarith
  exact ⟨hx₁_pos, hx₂_pos, hz_strict⟩

/-- Helper for Lemma 5.4.7.1: the one-sided power cone `K_[α]⁺` is closed when the exponents are
nonnegative. -/
private theorem powerConePlus_closed
    {α : ℝ} (hα_nonneg : 0 ≤ α) (hOne_sub_nonneg : 0 ≤ 1 - α) :
    IsClosed (K_[α]⁺ : Set ((ℝ × ℝ) × ℝ)) := by
  have hgm_cont : Continuous (powerConeGeometricMean α) := by
    -- Both fixed-exponent `rpow` factors are continuous on all of `ℝ` for nonnegative exponents.
    have hfst : Continuous (fun y : ℝ × ℝ ↦ Real.rpow y.1 α) :=
      continuous_fst.rpow_const fun _ ↦ Or.inr hα_nonneg
    have hsnd : Continuous (fun y : ℝ × ℝ ↦ Real.rpow y.2 (1 - α)) :=
      continuous_snd.rpow_const fun _ ↦ Or.inr hOne_sub_nonneg
    simpa [powerConeGeometricMean_apply] using hfst.mul hsnd
  have hrepr :
      (K_[α]⁺ : Set ((ℝ × ℝ) × ℝ)) =
        {q | 0 ≤ q.1.1} ∩ {q | 0 ≤ q.1.2} ∩ {q | q.2 ≤ powerConeGeometricMean α q.1} := by
    ext q
    rcases q with ⟨⟨u, v⟩, w⟩
    constructor
    · intro hq
      have hmem := (mem_power_cone_plus_iff α u v w).1 hq
      exact ⟨⟨hmem.1, hmem.2.1⟩, hmem.2.2⟩
    · intro hq
      exact (mem_power_cone_plus_iff α u v w).2 ⟨hq.1.1, hq.1.2, hq.2⟩
  -- Rewrite the cone as the intersection of two coordinate half-spaces and one closed hypograph.
  rw [hrepr]
  simpa [Set.inter_assoc] using
    (isClosed_le continuous_const continuous_fst.fst).inter <|
      (isClosed_le continuous_const continuous_fst.snd).inter <|
        isClosed_le continuous_snd (hgm_cont.comp continuous_fst)

/-- Helper for Lemma 5.4.7.1: every point of `K_[α]⁺` lies in the closure of its interior when
the exponents are nonnegative. -/
private theorem powerConePlus_mem_closure_interior
    {α : ℝ} (hα_nonneg : 0 ≤ α) (hOne_sub_nonneg : 0 ≤ 1 - α)
    {q : ((ℝ × ℝ) × ℝ)} (hq : q ∈ K_[α]⁺) :
    q ∈ closure (interior (K_[α]⁺)) := by
  rcases q with ⟨⟨x₁, x₂⟩, z⟩
  have hmem := (mem_power_cone_plus_iff α x₁ x₂ z).1 hq
  let δ : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹
  let qSeq : ℕ → ((ℝ × ℝ) × ℝ) := fun n ↦ ((x₁ + δ n, x₂ + δ n), z - δ n)
  refine mem_closure_iff_seq_limit.mpr ⟨qSeq, ?_, ?_⟩
  · intro n
    have hδ_pos : 0 < δ n := by
      dsimp [δ]
      positivity
    have hpow₁ :
        Real.rpow x₁ α ≤ Real.rpow (x₁ + δ n) α := by
      exact Real.rpow_le_rpow hmem.1 (by linarith) hα_nonneg
    have hpow₂ :
        Real.rpow x₂ (1 - α) ≤ Real.rpow (x₂ + δ n) (1 - α) := by
      exact Real.rpow_le_rpow hmem.2.1 (by linarith) hOne_sub_nonneg
    have hgeom :
        powerConeGeometricMean α (x₁, x₂) ≤
          powerConeGeometricMean α (x₁ + δ n, x₂ + δ n) := by
      rw [powerConeGeometricMean_apply, powerConeGeometricMean_apply]
      exact mul_le_mul hpow₁ hpow₂
        (Real.rpow_nonneg hmem.2.1 (1 - α))
        (Real.rpow_nonneg (by linarith : 0 ≤ x₁ + δ n) α)
    have hslack :
        z - δ n < powerConeGeometricMean α (x₁ + δ n, x₂ + δ n) := by
      linarith [hmem.2.2, hgeom]
    -- Push both coordinates slightly forward and the third coordinate slightly downward.
    simpa [qSeq] using
      strict_mem_interior_powerConePlus hα_nonneg hOne_sub_nonneg
        (by linarith) (by linarith) hslack
  · have hδ_tendsto : Tendsto δ atTop (nhds 0) := by
      simpa [δ, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0))
    let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun t ↦ ((x₁ + t, x₂ + t), z - t)
    have hγ_tendsto : Tendsto γ (nhds 0) (nhds ((x₁, x₂), z)) := by
      have hγ_cont : Continuous γ := by
        continuity
      simpa [γ] using (show ContinuousAt γ 0 from hγ_cont.continuousAt).tendsto
    -- The explicit perturbation sequence converges back to the boundary point.
    have hcomp : Tendsto (fun n ↦ γ (δ n)) atTop (nhds ((x₁, x₂), z)) :=
      hγ_tendsto.comp hδ_tendsto
    simpa [δ, qSeq, γ] using hcomp

/-- Lemma 5.4.7.1: for `0 < α < 1`, every `ν`-self-concordant barrier for the one-sided power
cone `K_α^+` has barrier parameter at least `3`. -/
theorem power_cone_plus_barrierParameter_ge_three
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    {ν : NNReal} {F : ((ℝ × ℝ) × ℝ) → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (interior (K_[α]⁺)) ν F) :
    (3 : ℝ) ≤ (ν : ℝ) := by
  have hα_nonneg : 0 ≤ α := by linarith
  have hOne_sub_nonneg : 0 ≤ 1 - α := by linarith
  by_contra hν
  have hν_lt : (ν : ℝ) < 3 := by
    exact not_le.mp hν
  let τ : ℝ := (ν : ℝ) / (3 - (ν : ℝ))
  have hden_pos : 0 < 3 - (ν : ℝ) := sub_pos.mpr hν_lt
  have hτ_nonneg : 0 ≤ τ := by
    -- The contradiction parameter `τ` is nonnegative because both numerator and denominator are.
    have hν_nonneg : 0 ≤ (ν : ℝ) := by exact_mod_cast ν.2
    rw [show τ = (ν : ℝ) / (3 - (ν : ℝ)) by rfl]
    exact div_nonneg hν_nonneg hden_pos.le
  have hK_eq :
      (K_[α]⁺ : Set ((ℝ × ℝ) × ℝ)) =
        closure (interior (K_[α]⁺)) := by
    ext q
    constructor
    · intro hq
      exact powerConePlus_mem_closure_interior hα_nonneg hOne_sub_nonneg hq
    · intro hq
      exact closure_minimal interior_subset (powerConePlus_closed hα_nonneg hOne_sub_nonneg) hq
  have hQ_convex : Convex ℝ (K_[α]⁺ : Set ((ℝ × ℝ) × ℝ)) := by
    -- Convexity comes from the open barrier domain after identifying the cone with its closure.
    rw [hK_eq]
    exact hF.toIsStandardSelfConcordantOn.convex_domain.closure
  let xBar : ((ℝ × ℝ) × ℝ) := ((1, 1), -τ)
  let p : Fin 3 → ((ℝ × ℝ) × ℝ) := ![ ((1, 0), 0), ((0, 1), 0), ((0, 0), -1) ]
  let β : Fin 3 → ℝ := ![1, 1, 1 + τ]
  let a : Fin 3 → ℝ := ![1, 1, τ]
  have hxBar :
      xBar ∈ interior (K_[α]⁺) := by
    -- The base point has positive coordinates and strict negative slack.
    refine strict_mem_interior_powerConePlus hα_nonneg hOne_sub_nonneg zero_lt_one zero_lt_one ?_
    have : -τ < (1 : ℝ) := by linarith
    simpa [xBar, powerConeGeometricMean_apply] using this
  have hrecession :
      ∀ i, ∀ ⦃x : ((ℝ × ℝ) × ℝ)⦄, x ∈ K_[α]⁺ → ∀ t : ℝ, 0 ≤ t → x + t • p i ∈ K_[α]⁺ := by
    intro i x hx t ht
    rcases x with ⟨⟨x₁, x₂⟩, z⟩
    have hmem := (mem_power_cone_plus_iff α x₁ x₂ z).1 hx
    fin_cases i
    · -- Increasing the first coordinate preserves the cone by monotonicity of `rpow`.
      have hx' : ((x₁ + t, x₂), z) ∈ K_[α]⁺ := by
        rw [mem_power_cone_plus_iff]
        have hpow :
            Real.rpow x₁ α ≤ Real.rpow (x₁ + t) α := by
          exact Real.rpow_le_rpow hmem.1 (by linarith) hα_nonneg
        have hgeom :
            powerConeGeometricMean α (x₁, x₂) ≤ powerConeGeometricMean α (x₁ + t, x₂) := by
          rw [powerConeGeometricMean_apply, powerConeGeometricMean_apply]
          exact mul_le_mul hpow le_rfl
            (Real.rpow_nonneg hmem.2.1 (1 - α))
            (Real.rpow_nonneg (by linarith : 0 ≤ x₁ + t) α)
        refine ⟨by linarith, hmem.2.1, le_trans hmem.2.2 hgeom⟩
      simpa [p] using hx'
    · -- Increasing the second coordinate is symmetric.
      have hx' : ((x₁, x₂ + t), z) ∈ K_[α]⁺ := by
        rw [mem_power_cone_plus_iff]
        have hpow :
            Real.rpow x₂ (1 - α) ≤ Real.rpow (x₂ + t) (1 - α) := by
          exact Real.rpow_le_rpow hmem.2.1 (by linarith) hOne_sub_nonneg
        have hgeom :
            powerConeGeometricMean α (x₁, x₂) ≤ powerConeGeometricMean α (x₁, x₂ + t) := by
          rw [powerConeGeometricMean_apply, powerConeGeometricMean_apply]
          exact mul_le_mul le_rfl hpow
            (Real.rpow_nonneg hmem.2.1 (1 - α))
            (Real.rpow_nonneg hmem.1 α)
        refine ⟨hmem.1, by linarith, le_trans hmem.2.2 hgeom⟩
      simpa [p] using hx'
    · -- Decreasing the third coordinate keeps the point below the same graph.
      have hx' : ((x₁, x₂), z - t) ∈ K_[α]⁺ := by
        rw [mem_power_cone_plus_iff]
        refine ⟨hmem.1, hmem.2.1, ?_⟩
        linarith
      simpa [p] using hx'
  have hβ_pos : ∀ i, 0 < β i := by
    intro i
    fin_cases i
    · simp [β]
    · simp [β]
    · have hpos : 0 < 1 + τ := by linarith
      simpa [β] using hpos
  have hβ_exit : ∀ i, xBar - β i • p i ∉ interior (K_[α]⁺) := by
    intro i hx
    have hstrict := strict_of_mem_interior_powerConePlus hx
    fin_cases i
    · simpa [xBar, p, β, τ] using hstrict.1
    · simpa [xBar, p, β, τ] using hstrict.2.1
    · have hnot : ¬ (1 : ℝ) < 1 := by linarith
      apply hnot
      simpa [xBar, p, β, τ, powerConeGeometricMean_apply] using hstrict.2.2
  have hα_nonneg_fin : ∀ i, 0 ≤ a i := by
    intro i
    fin_cases i
    · simp [a]
    · simp [a]
    · simpa [a] using hτ_nonneg
  have hy :
      xBar - ∑ i, a i • p i ∈ K_[α]⁺ := by
    -- The chosen forward step lands at the cone origin.
    have hzero : xBar - ∑ i, a i • p i = (((0 : ℝ), 0), 0) := by
      ext <;> simp [xBar, p, a, Fin.sum_univ_three]
    rw [hzero, mem_power_cone_plus_iff]
    refine ⟨le_rfl, le_rfl, ?_⟩
    have hα_pos' : 0 < α := hα₀
    have hOne_sub_pos : 0 < 1 - α := sub_pos.mpr hα₁
    simp [powerConeGeometricMean_apply, hα_pos'.ne', hOne_sub_pos.ne']
  have hbound :
      ∑ i : Fin 3, a i / β i ≤ (ν : ℝ) :=
    hF.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions
      hQ_convex hxBar p hrecession β a hβ_pos hβ_exit hα_nonneg_fin hy
  have hsum :
      ∑ i : Fin 3, a i / β i = 1 + 1 + τ / (1 + τ) := by
    simp [a, β, Fin.sum_univ_three, add_assoc]
  have hτ_ratio : τ / (1 + τ) = (ν : ℝ) / 3 := by
    -- The specific choice `τ = ν / (3 - ν)` normalizes the third summand to `ν / 3`.
    rw [show τ = (ν : ℝ) / (3 - (ν : ℝ)) by rfl]
    field_simp [hden_pos.ne']
    ring
  have hscalar : 2 + (ν : ℝ) / 3 ≤ (ν : ℝ) := by
    rw [hsum] at hbound
    linarith [hbound, hτ_ratio]
  linarith
