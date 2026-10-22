/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology BigOperators ENNReal

namespace ENNReal

/-- The upper small-noise exponential growth of `u`, namely `limsup_{ε→0+} ε log u(ε)`. This is
the `ε ↓ 0` analogue of `ExpGrowth.expGrowthSup`. -/
noncomputable def smallNoiseExpGrowthSup (u : ℝ → ℝ≥0∞) : EReal :=
  limsup (fun ε : ℝ ↦ (ε : EReal) * log (u ε)) (𝓝[>] (0 : ℝ))

/-- Unfolding `smallNoiseExpGrowthSup` gives the scaled logarithmic `limsup`. -/
theorem smallNoiseExpGrowthSup_def (u : ℝ → ℝ≥0∞) :
    smallNoiseExpGrowthSup u =
      limsup (fun ε : ℝ ↦ (ε : EReal) * log (u ε)) (𝓝[>] (0 : ℝ)) := rfl

/-- Helper for Lemma 23.9: the zero family has trivial upper small-noise exponential growth. -/
lemma smallNoiseExpGrowthSup_zero : smallNoiseExpGrowthSup 0 = ⊥ := by
  -- Unfold the definition and note that `ε * log 0 = ⊥` for every `ε > 0`.
  rw [smallNoiseExpGrowthSup_def]
  refine (limsup_congr ?_).trans Filter.limsup_const_bot
  filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
  rw [Pi.zero_apply, ENNReal.log_zero,
    EReal.mul_bot_of_pos (show 0 < (ε : EReal) by exact_mod_cast hε)]

/-- Helper for Lemma 23.9: eventual pointwise domination gives the corresponding bound on
`smallNoiseExpGrowthSup`. -/
lemma smallNoiseExpGrowthSup_eventually_monotone {u v : ℝ → ℝ≥0∞}
    (h : u ≤ᶠ[𝓝[>] (0 : ℝ)] v) : smallNoiseExpGrowthSup u ≤ smallNoiseExpGrowthSup v := by
  -- Compare the logarithms pointwise and preserve the inequality by multiplying with `ε > 0`.
  rw [smallNoiseExpGrowthSup_def, smallNoiseExpGrowthSup_def]
  have hscaled :
      (fun ε : ℝ ↦ (ε : EReal) * log (u ε)) ≤ᶠ[𝓝[>] (0 : ℝ)]
        fun ε : ℝ ↦ (ε : EReal) * log (v ε) := by
    filter_upwards [h, eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε huv hε
    have hmul : Monotone fun x : EReal ↦ (ε : EReal) * x :=
      monotone_mul_left_of_nonneg <| by
        exact_mod_cast le_of_lt hε
    exact hmul (ENNReal.log_le_log huv)
  refine Filter.limsup_le_limsup hscaled ?_ ?_
  · exact
      (Filter.isBoundedUnder_of
        (u := fun ε : ℝ ↦ (ε : EReal) * log (u ε))
        (r := fun x y : EReal ↦ x ≥ y) ⟨⊥, fun ε ↦ bot_le⟩).isCoboundedUnder_le
  · exact Filter.isBoundedUnder_of
      (u := fun ε : ℝ ↦ (ε : EReal) * log (v ε))
      (r := fun x y : EReal ↦ x ≤ y) ⟨⊤, fun ε ↦ le_top⟩

/-- Helper for Lemma 23.9: the deterministic error term `ε ↦ ε log b` vanishes as `ε → 0+` for
every positive finite constant `b`. -/
lemma tendsto_smallNoiseLogConst {b : ℝ≥0∞} (hb0 : b ≠ 0) (hbTop : b ≠ ⊤) :
    Tendsto (fun ε : ℝ ↦ (ε : EReal) * log b) (𝓝[>] (0 : ℝ)) (nhds (0 : EReal)) := by
  have hεReal : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)) :=
    continuousWithinAt_id.tendsto
  have hε : Tendsto (fun ε : ℝ ↦ (ε : EReal)) (𝓝[>] (0 : ℝ)) (nhds (0 : EReal)) := by
    -- The right-sided small-noise filter still converges to `0` in the ambient space.
    exact EReal.tendsto_coe.2 hεReal
  have hlog_bot : log b ≠ ⊥ := by
    intro hlog
    exact hb0 (log_eq_bot_iff.mp hlog)
  have hlog_top : log b ≠ ⊤ := by
    intro hlog
    exact hbTop (log_eq_top_iff.mp hlog)
  -- Multiply the convergent `ε`-term by the finite constant `log b`.
  simpa [zero_mul] using
    (EReal.Tendsto.mul_const (b := log b) hε (Or.inr hlog_bot) (Or.inr hlog_top))

/-- Helper for Lemma 23.9: adding an `EReal` error term that tends to `0` does not change the
`limsup`. -/
lemma limsup_add_tendsto_zero_right {α : Type*} {F : Filter α} [F.NeBot] (f g : α → EReal)
    (hg : Tendsto g F (nhds (0 : EReal))) :
    limsup (fun x ↦ f x + g x) F = limsup f F := by
  have hlimsup_g : limsup g F = 0 := hg.limsup_eq
  have hliminf_g : liminf g F = 0 := hg.liminf_eq
  apply le_antisymm
  · -- The upper bound comes from the standard `limsup` subadditivity inequality.
    have hupper : limsup (fun x ↦ f x + g x) F ≤ limsup f F + limsup g F :=
      EReal.limsup_add_le
        (Or.inr <| by rw [hlimsup_g]; simp)
        (Or.inr <| by rw [hlimsup_g]; simp)
    rw [hlimsup_g, add_zero] at hupper
    exact hupper
  · -- The lower bound uses the companion `liminf` inequality and the vanishing of `g`.
    have hlower : limsup f F + liminf g F ≤ limsup (fun x ↦ f x + g x) F :=
      EReal.le_limsup_add
    rw [hliminf_g, add_zero] at hlower
    exact hlower

/-- Helper for Lemma 23.9: multiplying by a fixed positive finite constant does not change
`smallNoiseExpGrowthSup`. -/
lemma smallNoiseExpGrowthSup_mul_const (u : ℝ → ℝ≥0∞) {b : ℝ≥0∞}
    (hb0 : b ≠ 0) (hbTop : b ≠ ⊤) :
    smallNoiseExpGrowthSup (fun ε ↦ b * u ε) = smallNoiseExpGrowthSup u := by
  have herr :
      Tendsto (fun ε : ℝ ↦ (ε : EReal) * log b) (𝓝[>] (0 : ℝ)) (nhds (0 : EReal)) :=
    tendsto_smallNoiseLogConst hb0 hbTop
  rw [smallNoiseExpGrowthSup_def, smallNoiseExpGrowthSup_def]
  trans limsup (fun ε : ℝ ↦ (ε : EReal) * log (u ε) + (ε : EReal) * log b) (𝓝[>] (0 : ℝ))
  · -- Rewrite the logarithm of a constant multiple as the sum of the base term and a vanishing
    -- error term.
    refine limsup_congr ?_
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
    rw [ENNReal.log_mul_add,
      EReal.left_distrib_of_nonneg_of_ne_top
        (show 0 ≤ (ε : EReal) by exact_mod_cast le_of_lt hε) (by simp),
      add_comm]
  · -- The error term tends to `0`, so it does not affect the `limsup`.
    simpa using
      (limsup_add_tendsto_zero_right
        (f := fun ε : ℝ ↦ (ε : EReal) * log (u ε))
        (g := fun ε : ℝ ↦ (ε : EReal) * log b) herr)

/-- Helper for Lemma 23.9: the small-noise exponential growth of a pointwise supremum is the
supremum of the two small-noise exponential growths. -/
lemma smallNoiseExpGrowthSup_sup {u v : ℝ → ℝ≥0∞} :
    smallNoiseExpGrowthSup (u ⊔ v) = smallNoiseExpGrowthSup u ⊔ smallNoiseExpGrowthSup v := by
  -- Reduce the pointwise supremum to `max` and then move multiplication by `ε ≥ 0` across `max`.
  rw [smallNoiseExpGrowthSup_def, smallNoiseExpGrowthSup_def, smallNoiseExpGrowthSup_def]
  rw [← limsup_max]
  refine limsup_congr ?_
  filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
  have hmul : Monotone fun x : EReal ↦ (ε : EReal) * x :=
    monotone_mul_left_of_nonneg <| by
      exact_mod_cast le_of_lt hε
  rw [Pi.sup_apply, show u ε ⊔ v ε = max (u ε) (v ε) by rfl, ENNReal.log_monotone.map_max,
    hmul.map_max]

/-- Helper for Lemma 23.9: the small-noise exponential growth of a pointwise sum is the supremum
of the small-noise exponential growths of the summands. -/
lemma smallNoiseExpGrowthSup_add {u v : ℝ → ℝ≥0∞} :
    smallNoiseExpGrowthSup (u + v) = smallNoiseExpGrowthSup u ⊔ smallNoiseExpGrowthSup v := by
  -- Compare `u + v` with `u ⊔ v` from below and with `2 * (u ⊔ v)` from above.
  rw [← smallNoiseExpGrowthSup_sup]
  apply le_antisymm
  · calc
      smallNoiseExpGrowthSup (u + v)
          ≤ smallNoiseExpGrowthSup (fun ε ↦ (2 : ℝ≥0∞) * (u ⊔ v) ε) := by
            apply smallNoiseExpGrowthSup_eventually_monotone
            exact Eventually.of_forall fun ε ↦ by
              change u ε + v ε ≤ 2 * (u ε ⊔ v ε)
              rw [two_mul]
              exact add_le_add (le_sup_left : u ε ≤ u ε ⊔ v ε)
                (le_sup_right : v ε ≤ u ε ⊔ v ε)
      _ = smallNoiseExpGrowthSup (u ⊔ v) :=
        smallNoiseExpGrowthSup_mul_const (u := u ⊔ v) (b := 2) two_ne_zero (by simp)
  · exact smallNoiseExpGrowthSup_eventually_monotone <|
      Eventually.of_forall fun ε ↦ by
        exact sup_le (self_le_add_right (u ε) (v ε)) (self_le_add_left (v ε) (u ε))

/-- For a finite family of nonnegative functions of `ε`, the upper small-noise exponential growth
of the pointwise sum over a `Finset` is the supremum of the corresponding upper small-noise
exponential growths. This is the owner-facing finite-aggregation API for
`smallNoiseExpGrowthSup`, mirroring `ExpGrowth.expGrowthSup_sum`. -/
theorem smallNoiseExpGrowthSup_sum {α : Type*} (u : α → ℝ → ℝ≥0∞) (s : Finset α) :
    smallNoiseExpGrowthSup (∑ x ∈ s, u x) = ⨆ x ∈ s, smallNoiseExpGrowthSup (u x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is the zero function, so the finite supremum is also bottom.
      rw [Finset.sum_empty, ← Finset.iSup_coe, Finset.coe_empty, iSup_emptyset,
        smallNoiseExpGrowthSup_zero]
  | insert a t ha ht =>
      -- The induction step is the binary-addition identity followed by the usual `iSup_insert`
      -- normalization.
      rw [Finset.sum_insert ha, smallNoiseExpGrowthSup_add, ← Finset.iSup_coe,
        Finset.coe_insert a t, iSup_insert, Finset.iSup_coe, ht]

end ENNReal

-- Proof sketch: in the nonempty case compare the pointwise finite sum with the finite supremum:
-- `Finset.univ.sup (fun i ↦ a i ε) ≤ ∑ i, a i ε`
-- and `∑ i, a i ε ≤ Fintype.card ι * Finset.univ.sup (fun i ↦ a i ε)`.
-- Applying `log`, multiplying by `ε`, and taking the `limsup` along `𝓝[>] 0` yields the claim
-- because the additive error `ε * log (Fintype.card ι)` tends to `0`; the empty-index case is
-- immediate.
/-- Lemma 23.9: for a finite family of nonnegative functions of `ε`, the upper small-noise
exponential growth of the pointwise sum equals the supremum of the upper small-noise exponential
growths of the summands. The public API is stated for an arbitrary finite index type, treating the
textbook's `N + 1`-tuple as a concrete model of a finite family rather than as primitive data. -/
theorem limsup_zero_right_mul_log_sum_eq_iSup {ι : Type*} [Fintype ι] (a : ι → ℝ → ℝ≥0∞) :
    ENNReal.smallNoiseExpGrowthSup (∑ i, a i) =
      ⨆ i : ι, ENNReal.smallNoiseExpGrowthSup (a i) := by
  simpa using ENNReal.smallNoiseExpGrowthSup_sum a Finset.univ
