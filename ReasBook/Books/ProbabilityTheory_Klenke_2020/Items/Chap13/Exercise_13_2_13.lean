/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace StieltjesFunction

/-- The left-continuous inverse, or quantile function, of a real distribution function. It is
defined by the infimum of the superlevel set `{x | u ≤ F x}`. -/
def leftInverse (F : StieltjesFunction ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | u ≤ F x}

/-- Helper for Exercise 13.2.13: for every interior level `u ∈ (0,1)`, the superlevel set
`{x : ℝ | u ≤ F x}` is nonempty. -/
lemma leftInverseSuperlevel_nonempty
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    Set.Nonempty {x : ℝ | u ≤ F x} := by
  -- Proof comment: because `F x → 1` at `+∞`, some point reaches level `u`.
  have hmem : Set.Ioi u ∈ 𝓝 (1 : ℝ) := Ioi_mem_nhds hu.2
  have hEventual : ∀ᶠ x in atTop, u < F x := IsDistributionFunction.tendsto_atTop_one hmem
  obtain ⟨x, hx⟩ := hEventual.exists
  exact ⟨x, le_of_lt hx⟩

/-- Helper for Exercise 13.2.13: for every interior level `u ∈ (0,1)`, the superlevel set
`{x : ℝ | u ≤ F x}` is bounded below. -/
lemma leftInverseSuperlevel_bddBelow
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    BddBelow {x : ℝ | u ≤ F x} := by
  -- Proof comment: a point where `F` is still below `u` becomes a lower bound by monotonicity.
  have hmem : Set.Iio u ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hu.1
  have hEventual : ∀ᶠ x in atBot, F x < u :=
    IsDefectiveDistributionFunction.tendsto_atBot_zero hmem
  obtain ⟨x, hx⟩ := hEventual.exists
  refine ⟨x, ?_⟩
  intro y hy
  by_contra hxy
  have hyx : y < x := lt_of_not_ge hxy
  have hFx : F x < u := hx
  have hFy : u ≤ F y := hy
  have hle : F y ≤ F x := F.mono (le_of_lt hyx)
  exact not_lt_of_ge (hFy.trans hle) hFx

/-- Helper for Exercise 13.2.13: the defining infimum of the quantile still belongs to the
corresponding superlevel set. -/
lemma leftInverse_level_le
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    u ≤ F (F.leftInverse u) := by
  let S : Set ℝ := {x : ℝ | u ≤ F x}
  have hS_nonempty : S.Nonempty := by
    simpa [S] using leftInverseSuperlevel_nonempty F hu
  have hS_bddBelow : BddBelow S := by
    simpa [S] using leftInverseSuperlevel_bddBelow F hu
  -- Proof comment: right continuity transports the infimum of the superlevel set through `F`.
  have hcont : ContinuousWithinAt F S (sInf S) := by
    refine (F.right_continuous (sInf S)).mono ?_
    intro x hx
    exact csInf_le hS_bddBelow hx
  have hmap :
      F (sInf S) = sInf (F '' S) :=
    MonotoneOn.map_csInf_of_continuousWithinAt hcont (F.mono.monotoneOn S) hS_nonempty hS_bddBelow
  have hu_le : u ≤ sInf (F '' S) := by
    refine le_csInf ?_ ?_
    · rcases hS_nonempty with ⟨x, hx⟩
      exact ⟨F x, ⟨x, hx, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
  simpa [leftInverse, S, hmap] using hu_le

/-- Helper for Exercise 13.2.13: every point whose cdf value already reaches level `u` lies to the
right of the quantile `F.leftInverse u`. -/
lemma leftInverse_le_of_le
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] {u x : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hx : u ≤ F x) :
    F.leftInverse u ≤ x := by
  let S : Set ℝ := {y : ℝ | u ≤ F y}
  have hS_bddBelow : BddBelow S := by
    simpa [S] using leftInverseSuperlevel_bddBelow F hu
  -- Proof comment: `x` is itself in the defining superlevel set, so the infimum lies below it.
  change sInf S ≤ x
  exact csInf_le hS_bddBelow (by simpa [S] using hx)

/-- Helper for Exercise 13.2.13: every point strictly to the right of the quantile belongs to the
superlevel set for the same level. -/
lemma level_le_of_leftInverse_lt
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] {u x : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hx : F.leftInverse u < x) :
    u ≤ F x := by
  -- Proof comment: the quantile itself already reaches level `u`, and monotonicity propagates the
  -- level bound to points on its right.
  exact (leftInverse_level_le F hu).trans (F.mono (le_of_lt hx))

/-- Helper for Exercise 13.2.13: if `F x` is still below level `u`, then `x` lies strictly to the
left of the quantile `F.leftInverse u`. -/
lemma lt_leftInverse_of_lt
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] {u x : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hx : F x < u) :
    x < F.leftInverse u := by
  -- Proof comment: if `x` were at or to the right of the quantile, monotonicity would force
  -- `F x` to already be at least `u`.
  by_contra hqx
  have hq_le_x : F.leftInverse u ≤ x := le_of_not_gt hqx
  have hu_le_x : u ≤ F x := (leftInverse_level_le F hu).trans (F.mono hq_le_x)
  exact not_le_of_gt hx hu_le_x

-- Proof sketch: if `u ≤ v`, then the superlevel set `{x | v ≤ F x}` is contained in
-- `{x | u ≤ F x}`. Taking infima of these nested superlevel sets yields monotonicity on `(0,1)`.
/-- The left-continuous inverse of a distribution function is monotone on the open unit interval.
-/
theorem monotoneOn_leftInverse
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] :
    MonotoneOn F.leftInverse (Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv
  -- Proof comment: the quantile at level `v` already reaches `v`, hence also the smaller level
  -- `u`, so it bounds the quantile at level `u` from above.
  exact leftInverse_le_of_le F hu (huv.trans (leftInverse_level_le F hv))

-- Proof sketch: apply the standard theorem that a monotone real function has at most countably
-- many discontinuities, restricted to the interval `(0,1)`, to the monotone quantile function.
/-- The left-continuous inverse of a distribution function is continuous for Lebesgue-almost every
parameter `u ∈ (0,1)`. -/
theorem ae_continuousWithinAt_leftInverse
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] :
    ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ContinuousWithinAt F.leftInverse (Ioo (0 : ℝ) 1) u := by
  let bad :
      Set ℝ := {u ∈ Ioo (0 : ℝ) 1 | ¬ ContinuousWithinAt F.leftInverse (Ioo (0 : ℝ) 1) u}
  have hbadCount : bad.Countable :=
    (monotoneOn_leftInverse F).countable_not_continuousWithinAt
  -- Proof comment: the monotone quantile has only countably many bad points, hence a null
  -- exceptional set under Lebesgue measure.
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hbadCount.ae_notMem volume] with u huBad huMem
  by_contra hnot
  exact huBad ⟨huMem, hnot⟩

end StieltjesFunction

section

open StieltjesFunction

variable {Fs : ℕ → StieltjesFunction ℝ} {F : StieltjesFunction ℝ}

-- Proof sketch: combine the continuity-point convergence encoded in
-- `distribution_function_weakly_converges_to` with the defining infimum formula for the
-- left-continuous inverses. Continuity of the limit inverse at `u` lets the two-sided squeezing
-- argument for quantiles pass to the limit.
/-- Exercise 13.2.13 (1): if distribution functions `Fₙ` converge weakly to `F`, then their
left-continuous inverses converge at every continuity point of the limit inverse on `(0,1)`. -/
theorem tendsto_leftInverse_of_weak_convergence :
    Π hF : IsDistributionFunction F,
      Π hFs : ∀ n, IsDistributionFunction (Fs n),
        distribution_function_weakly_converges_to Fs F →
        {u : ℝ} →
          (hu : u ∈ Ioo (0 : ℝ) 1) →
          (hcont : ContinuousWithinAt F.leftInverse (Ioo (0 : ℝ) 1) u) →
          Tendsto (fun n ↦ (Fs n).leftInverse u) atTop (𝓝 (F.leftInverse u)) := by
  intro hF hFs hconv u hu hcont
  letI : IsDistributionFunction F := hF
  rcases hconv with ⟨_, _, hpointwise, _⟩
  let q : ℝ := F.leftInverse u
  let D : Set ℝ := {x : ℝ | ¬ ContinuousAt F x}
  have hcontAt : ContinuousAt F.leftInverse u :=
    (continuousWithinAt_iff_continuousAt (isOpen_Ioo.mem_nhds hu)).1 hcont
  have hDcount : D.Countable := F.mono.countable_not_continuousAt
  have hDdense : Dense Dᶜ := hDcount.dense_compl ℝ
  -- Proof comment: prove convergence by trapping the approximating quantiles between continuity
  -- points of `F` chosen near the target quantile.
  rw [tendsto_order]
  constructor
  · intro a ha
    have hcontLeft : ContinuousWithinAt F.leftInverse (Iio u) u := hcontAt.continuousWithinAt
    have hleftValue : {t : ℝ | a < F.leftInverse t} ∈ 𝓝[<] u := by
      simpa using hcontLeft (Ioi_mem_nhds ha)
    have hleftDomain : Ioo (0 : ℝ) u ∈ 𝓝[<] u := Ioo_mem_nhdsLT hu.1
    have hleftEventually : ∀ᶠ t in 𝓝[<] u, t ∈ Ioo (0 : ℝ) u ∧ a < F.leftInverse t := by
      filter_upwards [hleftDomain, hleftValue] with t ht hval
      exact ⟨ht, hval⟩
    obtain ⟨u₁, hu₁Ioo, hau₁⟩ := hleftEventually.exists
    have hu₁_right : u₁ < 1 := lt_trans hu₁Ioo.2 hu.2
    have hu₁ : u₁ ∈ Ioo (0 : ℝ) 1 := ⟨hu₁Ioo.1, hu₁_right⟩
    obtain ⟨x, hxD, hax, hxq⟩ := hDdense.exists_between hau₁
    have hxcont : ContinuousAt F x := by
      simpa [D] using hxD
    have hFx_lt_u₁ : F x < u₁ := by
      by_contra hnot
      have hu₁_le : u₁ ≤ F x := not_lt.mp hnot
      have hq_le : F.leftInverse u₁ ≤ x := leftInverse_le_of_le F hu₁ hu₁_le
      exact not_le_of_gt hxq hq_le
    have hFx_lt_u : F x < u := lt_trans hFx_lt_u₁ hu₁Ioo.2
    have hxConv : Tendsto (fun n ↦ Fs n x) atTop (𝓝 (F x)) := hpointwise hxcont
    have hxEventually : ∀ᶠ n in atTop, Fs n x < u := hxConv.eventually_lt_const hFx_lt_u
    filter_upwards [hxEventually] with n hn
    letI : IsDistributionFunction (Fs n) := hFs n
    have hxLeft : x < (Fs n).leftInverse u := lt_leftInverse_of_lt (Fs n) hu hn
    exact lt_trans hax hxLeft
  · intro b hb
    have hcontRight : ContinuousWithinAt F.leftInverse (Ioi u) u := hcontAt.continuousWithinAt
    have hrightValue : {t : ℝ | F.leftInverse t < b} ∈ 𝓝[>] u := by
      simpa using hcontRight (Iio_mem_nhds hb)
    have hrightDomain : Ioo u (1 : ℝ) ∈ 𝓝[>] u := Ioo_mem_nhdsGT hu.2
    have hrightEventually : ∀ᶠ t in 𝓝[>] u, t ∈ Ioo u (1 : ℝ) ∧ F.leftInverse t < b := by
      filter_upwards [hrightDomain, hrightValue] with t ht hval
      exact ⟨ht, hval⟩
    obtain ⟨u₂, hu₂Ioo, hu₂b⟩ := hrightEventually.exists
    have hu₂_left : 0 < u₂ := lt_trans hu.1 hu₂Ioo.1
    have hu₂ : u₂ ∈ Ioo (0 : ℝ) 1 := ⟨hu₂_left, hu₂Ioo.2⟩
    obtain ⟨y, hyD, hq₂y, hyb⟩ := hDdense.exists_between hu₂b
    have hycont : ContinuousAt F y := by
      simpa [D] using hyD
    have hu₂_le_Fy : u₂ ≤ F y := level_le_of_leftInverse_lt F hu₂ hq₂y
    have hu_lt_Fy : u < F y := lt_of_lt_of_le hu₂Ioo.1 hu₂_le_Fy
    have hyConv : Tendsto (fun n ↦ Fs n y) atTop (𝓝 (F y)) := hpointwise hycont
    have hyEventually : ∀ᶠ n in atTop, u ≤ Fs n y := hyConv.eventually_const_le hu_lt_Fy
    filter_upwards [hyEventually] with n hn
    letI : IsDistributionFunction (Fs n) := hFs n
    have hyRight : (Fs n).leftInverse u ≤ y := leftInverse_le_of_le (Fs n) hu hn
    exact lt_of_le_of_lt hyRight hyb

-- Proof sketch: by the previous theorem, convergence of the inverses fails only at points where
-- the limit inverse is discontinuous. The exceptional set is Lebesgue-null because the quantile
-- function is monotone on `(0,1)`.
/-- Exercise 13.2.13 (2): consequently, the left-continuous inverses converge for
Lebesgue-almost every `u ∈ (0,1)`. -/
theorem ae_tendsto_leftInverse_of_weak_convergence :
    Π hF : IsDistributionFunction F,
      Π hFs : ∀ n, IsDistributionFunction (Fs n),
        distribution_function_weakly_converges_to Fs F →
    ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Tendsto (fun n ↦ (Fs n).leftInverse u) atTop (𝓝 (F.leftInverse u)) := by
  intro hF hFs hconv
  letI : IsDistributionFunction F := hF
  have hcontAE :
      ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 →
        ContinuousWithinAt F.leftInverse (Ioo (0 : ℝ) 1) u :=
    (ae_restrict_iff' measurableSet_Ioo).1 (ae_continuousWithinAt_leftInverse F)
  -- Proof comment: outside the null discontinuity set of the limit quantile, the pointwise
  -- convergence theorem applies directly.
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hcontAE] with u huCont hu
  exact tendsto_leftInverse_of_weak_convergence hF hFs hconv hu (huCont hu)

end
