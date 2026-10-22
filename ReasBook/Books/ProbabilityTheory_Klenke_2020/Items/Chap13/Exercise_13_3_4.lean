/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Theorem_13_29
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Sequences

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open MeasureTheory.FiniteMeasure
open scoped Topology

noncomputable section

/-- A real-valued function on `ℝ^d`, modeled as `(Fin d → ℝ) → ℝ`, belongs to the multivariate
Helly class `V_d` when it is coordinatewise monotone, right continuous from the upper orthant
`Set.Ici x` at every `x`, and bounded. -/
class IsCoordinatewiseRightContinuousMonotoneBoundedFunction {d : ℕ}
    (F : (Fin d → ℝ) → ℝ) : Prop where
  right_continuous : ∀ x : Fin d → ℝ, ContinuousWithinAt F (Set.Ici x) x
  monotone : Monotone F
  bounded : ∃ C : ℝ, ∀ x : Fin d → ℝ, ‖F x‖ ≤ C

/-- Constant functions on `ℝ^d` belong to the multivariate Helly class `V_d`. -/
instance instIsCoordinatewiseRightContinuousMonotoneBoundedFunctionConst {d : ℕ} (c : ℝ) :
    IsCoordinatewiseRightContinuousMonotoneBoundedFunction (fun _ : Fin d → ℝ ↦ c) := by
  refine
    { right_continuous := ?_
      monotone := ?_
      bounded := ?_ }
  · intro x
    -- Proof comment: constant maps are continuous on every upper orthant.
    simpa using continuousWithinAt_const
  · intro x y hxy
    -- Proof comment: coordinatewise order does not change the value of a constant function.
    simp
  · refine ⟨‖c‖, ?_⟩
    intro x
    -- Proof comment: every value of the constant function has the same norm.
    simp

/-- Helper for Exercise 13.3.4: every point of `ℝ^d` admits a rational vector strictly above it
in every coordinate. -/
private theorem existsRatVecGt {d : ℕ} (x : Fin d → ℝ) :
    ∃ q : Fin d → ℚ, ∀ i, x i < (q i : ℝ) := by
  classical
  choose q hq using fun i : Fin d => exists_rat_gt (x i)
  exact ⟨q, hq⟩

/-- Helper for Exercise 13.3.4: between two real vectors with strict coordinatewise inequality
there is a rational vector. -/
private theorem existsRatVecBtwn {d : ℕ} {x y : Fin d → ℝ}
    (hxy : ∀ i, x i < y i) :
    ∃ q : Fin d → ℚ, ∀ i, x i < (q i : ℝ) ∧ (q i : ℝ) < y i := by
  classical
  choose q hq using fun i : Fin d => exists_rat_btwn (hxy i)
  exact ⟨q, hq⟩

/-- Helper for Exercise 13.3.4: a uniformly bounded sequence on `ℝ^d` admits a strictly
increasing subsequence whose values converge on the rational grid `(Fin d → ℚ)`. -/
private theorem existsStrictMonoSubseqTendstoRatVec
    (d : ℕ) (u : ℕ → (Fin d → ℝ) → ℝ) {C : ℝ}
    (hC : ∀ n x, ‖u n x‖ ≤ C) (hmono : ∀ n, Monotone (u n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : (Fin d → ℚ) → ℝ,
      (∀ q, Tendsto (fun k ↦ u (φ k) (fun i ↦ (q i : ℝ))) atTop (𝓝 (g q))) ∧
      Monotone g ∧ ∀ q, -C ≤ g q ∧ g q ≤ C := by
  let K : Set ((Fin d → ℚ) → ℝ) := Set.pi Set.univ (fun _ : Fin d → ℚ ↦ Set.Icc (-C) C)
  have hKCompact : IsCompact K := by
    simpa [K] using isCompact_univ_pi (fun _ : Fin d → ℚ ↦ isCompact_Icc)
  have hu_mem : ∀ n, (fun q : Fin d → ℚ ↦ u n (fun i ↦ (q i : ℝ))) ∈ K := by
    intro n q _
    -- Proof comment: every rational evaluation stays inside the common compact interval.
    exact abs_le.mp (by simpa [Real.norm_eq_abs] using hC n (fun i ↦ (q i : ℝ)))
  obtain ⟨g, hgK, φ, hφ, hφtendsto⟩ := hKCompact.tendsto_subseq hu_mem
  have hgTendsto : ∀ q, Tendsto (fun k ↦ u (φ k) (fun i ↦ (q i : ℝ))) atTop (𝓝 (g q)) := by
    intro q
    -- Proof comment: convergence in the product space is exactly coordinatewise convergence.
    simpa [Function.comp] using (tendsto_pi_nhds.1 hφtendsto q)
  have hgMonotone : Monotone g := by
    intro p q hpq
    have hpqReal : (fun i ↦ (p i : ℝ)) ≤ fun i ↦ (q i : ℝ) := by
      intro i
      change (p i : ℝ) ≤ (q i : ℝ)
      exact_mod_cast (hpq i)
    -- Proof comment: the order relation survives passage to the pointwise limit on the grid.
    exact le_of_tendsto_of_tendsto (hgTendsto p) (hgTendsto q)
      (Eventually.of_forall fun k ↦ (hmono (φ k)) hpqReal)
  have hgBound : ∀ q, -C ≤ g q ∧ g q ≤ C := by
    intro q
    simpa [K] using hgK q (by simp)
  exact ⟨φ, hφ, g, hgTendsto, hgMonotone, hgBound⟩

/-- Helper for Exercise 13.3.4: the multivariate rational upper envelope is the infimum of `g q`
over rational vectors strictly above `x` in every coordinate. -/
private noncomputable def ratUpperEnvelopeVec {d : ℕ} (g : (Fin d → ℚ) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ⨅ q : {q : Fin d → ℚ // ∀ i, x i < (q i : ℝ)}, g q

/-- Helper for Exercise 13.3.4: the indexing subtype of `ratUpperEnvelopeVec g x` is nonempty. -/
private theorem ratUpperEnvelopeVec_nonempty {d : ℕ} (x : Fin d → ℝ) :
    Nonempty {q : Fin d → ℚ // ∀ i, x i < (q i : ℝ)} := by
  obtain ⟨q, hq⟩ := existsRatVecGt x
  exact ⟨⟨q, hq⟩⟩

/-- Helper for Exercise 13.3.4: a coordinatewise lower bound on `g` gives a lower bound on the
range used to define the rational upper envelope. -/
private theorem ratUpperEnvelopeVec_rangeBddBelow {d : ℕ} {g : (Fin d → ℚ) → ℝ} {B : ℝ}
    (hB : ∀ q, B ≤ g q) (x : Fin d → ℝ) :
    BddBelow (Set.range fun q : {q : Fin d → ℚ // ∀ i, x i < (q i : ℝ)} ↦ g q) := by
  refine ⟨B, ?_⟩
  rintro y ⟨q, rfl⟩
  exact hB q

/-- Helper for Exercise 13.3.4: the rational upper envelope is coordinatewise monotone. -/
private theorem ratUpperEnvelopeVec_monotone {d : ℕ} {g : (Fin d → ℚ) → ℝ} {B : ℝ}
    (hB : ∀ q, B ≤ g q) (_hg : Monotone g) :
    Monotone (ratUpperEnvelopeVec g) := by
  intro x y hxy
  letI : Nonempty {q : Fin d → ℚ // ∀ i, y i < (q i : ℝ)} := ratUpperEnvelopeVec_nonempty y
  -- Proof comment: the right-ray above `y` is contained in the right-ray above `x`.
  unfold ratUpperEnvelopeVec
  refine le_ciInf fun q ↦ ?_
  exact (ciInf_le (ratUpperEnvelopeVec_rangeBddBelow hB x)
    ⟨q.1, fun i ↦ (hxy i).trans_lt (q.2 i)⟩).trans_eq rfl

/-- Helper for Exercise 13.3.4: if `ratUpperEnvelopeVec g x < b`, then one rational vector above
`x` already has `g q < b`. -/
private theorem existsRatVecGtOfRatUpperEnvelopeVecLt {d : ℕ}
    {g : (Fin d → ℚ) → ℝ} {x : Fin d → ℝ} {b : ℝ}
    (hb : ratUpperEnvelopeVec g x < b) :
    ∃ q : Fin d → ℚ, (∀ i, x i < (q i : ℝ)) ∧ g q < b := by
  by_contra hExists
  letI : Nonempty {q : Fin d → ℚ // ∀ i, x i < (q i : ℝ)} := ratUpperEnvelopeVec_nonempty x
  have hLowerBound :
      ∀ q : {q : Fin d → ℚ // ∀ i, x i < (q i : ℝ)}, b ≤ g q := by
    intro q
    exact le_of_not_gt fun hlt => hExists ⟨q.1, q.2, hlt⟩
  -- Proof comment: if every rational value above `x` were at least `b`, then the infimum would
  -- also be at least `b`, contradicting `hb`.
  have hImpossible : b ≤ ratUpperEnvelopeVec g x := by
    exact le_ciInf hLowerBound
  exact (not_le_of_gt hb) hImpossible

/-- Helper for Exercise 13.3.4: the rational upper envelope again belongs to the multivariate
Helly class `V_d`. -/
private theorem ratUpperEnvelopeVec_memVd {d : ℕ} {g : (Fin d → ℚ) → ℝ} {C : ℝ}
    (hLower : ∀ q, -C ≤ g q) (hUpper : ∀ q, g q ≤ C) (hg : Monotone g) :
    IsCoordinatewiseRightContinuousMonotoneBoundedFunction (ratUpperEnvelopeVec g) := by
  refine
    { right_continuous := ?_
      monotone := ratUpperEnvelopeVec_monotone hLower hg
      bounded := ?_ }
  · intro x
    have hEnvelopeMono : Monotone (ratUpperEnvelopeVec g) := ratUpperEnvelopeVec_monotone hLower hg
    rw [Metric.continuousWithinAt_iff']
    intro ε hε
    obtain ⟨q, hxq, hqε⟩ :=
      existsRatVecGtOfRatUpperEnvelopeVecLt
        (x := x) (b := ratUpperEnvelopeVec g x + ε) (by linarith)
    have hUpperNhds :
        (⋂ i : Fin d, {y : Fin d → ℝ | y i < (q i : ℝ)}) ∈ 𝓝 x := by
      refine Filter.iInter_mem.2 ?_
      intro i
      exact IsOpen.mem_nhds
        (isOpen_lt (continuous_apply i) continuous_const) (hxq i)
    have hUpperNhdsWithin :
        (⋂ i : Fin d, {y : Fin d → ℝ | y i < (q i : ℝ)}) ∈ 𝓝[Set.Ici x] x :=
      nhdsWithin_le_nhds hUpperNhds
    have hEventually :
        ∀ᶠ y in 𝓝[Set.Ici x] x,
          y ∈ Set.Ici x ∧ y ∈ ⋂ i : Fin d, {y : Fin d → ℝ | y i < (q i : ℝ)} := by
      exact inter_mem self_mem_nhdsWithin hUpperNhdsWithin
    filter_upwards [hEventually] with y hy
    have hxy : x ≤ y := hy.1
    have hyq : ∀ i, y i < (q i : ℝ) := fun i ↦ mem_iInter.mp hy.2 i
    have hFy_le_gq : ratUpperEnvelopeVec g y ≤ g q := by
      exact ciInf_le (ratUpperEnvelopeVec_rangeBddBelow hLower y) ⟨q, hyq⟩
    have hFx_le_Fy : ratUpperEnvelopeVec g x ≤ ratUpperEnvelopeVec g y := hEnvelopeMono hxy
    -- Proof comment: on this neighborhood, the envelope is trapped between `F x` and `g q`.
    have hDist : dist (ratUpperEnvelopeVec g y) (ratUpperEnvelopeVec g x) < ε := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hFx_le_Fy)]
      linarith
    exact hDist
  · refine ⟨C, ?_⟩
    intro x
    have hLowerFx : -C ≤ ratUpperEnvelopeVec g x := by
      letI : Nonempty {q : Fin d → ℚ // ∀ i, x i < (q i : ℝ)} := ratUpperEnvelopeVec_nonempty x
      -- Proof comment: every term in the defining infimum is bounded below by `-C`.
      exact le_ciInf fun q ↦ hLower q
    have hUpperFx : ratUpperEnvelopeVec g x ≤ C := by
      obtain ⟨q, hq⟩ := existsRatVecGt x
      -- Proof comment: one rational vector above `x` bounds the infimum from above.
      exact (ciInf_le (ratUpperEnvelopeVec_rangeBddBelow hLower x) ⟨q, hq⟩).trans (hUpper q)
    simpa [Real.norm_eq_abs] using abs_le.mpr ⟨hLowerFx, hUpperFx⟩

/-- Helper for Exercise 13.3.4: if `a` lies strictly below the rational upper envelope at a
continuity point `x`, then the extracted subsequence is eventually above `a` at `x`. -/
private theorem eventuallyGtSubseqOfLtRatUpperEnvelopeVec {d : ℕ}
    {u : ℕ → (Fin d → ℝ) → ℝ} {φ : ℕ → ℕ} {g : (Fin d → ℚ) → ℝ}
    {C : ℝ} {x : Fin d → ℝ} {a : ℝ}
    (hφt : ∀ q, Tendsto (fun k ↦ u (φ k) (fun i ↦ (q i : ℝ))) atTop (𝓝 (g q)))
    (hLower : ∀ q, -C ≤ g q) (hmono : ∀ n, Monotone (u n))
    (hxcont : ContinuousAt (ratUpperEnvelopeVec g) x) (ha : a < ratUpperEnvelopeVec g x) :
    ∀ᶠ k in atTop, a < u (φ k) x := by
  let ε : ℝ := (ratUpperEnvelopeVec g x - a) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.1 hxcont ε hε
  let y : Fin d → ℝ := fun i ↦ x i - δ / 2
  have hdist : dist y x < δ := by
    rw [dist_pi_lt_iff hδpos]
    intro i
    dsimp [y]
    rw [Real.dist_eq]
    have hneg : x i - δ / 2 - x i ≤ 0 := by
      linarith
    rw [abs_of_nonpos hneg]
    linarith
  have hyClose : dist (ratUpperEnvelopeVec g y) (ratUpperEnvelopeVec g x) < ε := hδ hdist
  have hFxε_lt_Fy : ratUpperEnvelopeVec g x - ε < ratUpperEnvelopeVec g y := by
    have hyClose' : |ratUpperEnvelopeVec g y - ratUpperEnvelopeVec g x| < ε := by
      simpa [Real.dist_eq] using hyClose
    have hAbs := abs_lt.mp hyClose'
    linarith
  have hyx : ∀ i, y i < x i := by
    intro i
    dsimp [y]
    linarith
  obtain ⟨q, hq⟩ := existsRatVecBtwn hyx
  have hyq : ∀ i, y i < (q i : ℝ) := fun i ↦ (hq i).1
  have hqx : ∀ i, (q i : ℝ) < x i := fun i ↦ (hq i).2
  have hFy_le_gq : ratUpperEnvelopeVec g y ≤ g q := by
    -- Proof comment: any rational point above `y` bounds the defining infimum from above.
    exact ciInf_le (ratUpperEnvelopeVec_rangeBddBelow hLower y) ⟨q, hyq⟩
  have ha_lt_gq : a < g q := by
    have : ratUpperEnvelopeVec g x - ε < g q := lt_of_lt_of_le hFxε_lt_Fy hFy_le_gq
    dsimp [ε] at this
    linarith
  have hEventually : ∀ᶠ k in atTop, a < u (φ k) (fun i ↦ (q i : ℝ)) := by
    exact (tendsto_order.1 (hφt q)).1 a ha_lt_gq
  filter_upwards [hEventually] with k hk
  have hqxLe : (fun i ↦ (q i : ℝ)) ≤ x := fun i ↦ (hqx i).le
  exact lt_of_lt_of_le hk ((hmono (φ k)) hqxLe)

/-- Helper for Exercise 13.3.4: if `b` lies strictly above the rational upper envelope at `x`,
then the extracted subsequence is eventually below `b` at `x`. -/
private theorem eventuallyLtSubseqOfRatUpperEnvelopeVecLt {d : ℕ}
    {u : ℕ → (Fin d → ℝ) → ℝ} {φ : ℕ → ℕ} {g : (Fin d → ℚ) → ℝ}
    {x : Fin d → ℝ} {b : ℝ}
    (hφt : ∀ q, Tendsto (fun k ↦ u (φ k) (fun i ↦ (q i : ℝ))) atTop (𝓝 (g q)))
    (hmono : ∀ n, Monotone (u n)) (hb : ratUpperEnvelopeVec g x < b) :
    ∀ᶠ k in atTop, u (φ k) x < b := by
  obtain ⟨q, hxq, hqb⟩ := existsRatVecGtOfRatUpperEnvelopeVecLt hb
  have hEventually : ∀ᶠ k in atTop, u (φ k) (fun i ↦ (q i : ℝ)) < b := by
    exact (tendsto_order.1 (hφt q)).2 b hqb
  filter_upwards [hEventually] with k hk
  have hxqLe : x ≤ fun i ↦ (q i : ℝ) := fun i ↦ (hxq i).le
  exact lt_of_le_of_lt ((hmono (φ k)) hxqLe) hk

/-- A subsequence `u ∘ φ` converges to `F` in the multivariate Helly sense if `φ` is strictly
increasing, the limit function `F` again belongs to `V_d`, and the subsequence converges pointwise
at every continuity point of `F`. -/
class IsHellySubsequenceLimitInRd {d : ℕ}
    (u : ℕ → (Fin d → ℝ) → ℝ) (φ : ℕ → ℕ) (F : (Fin d → ℝ) → ℝ) : Prop where
  strictMono : StrictMono φ
  limit_mem : IsCoordinatewiseRightContinuousMonotoneBoundedFunction F
  tendsto_at_continuity_points :
    ∀ ⦃x : Fin d → ℝ⦄, ContinuousAt F x →
      Tendsto (fun k ↦ u (φ k) x) atTop (𝓝 (F x))

-- Proof sketch: use the multidimensional Helly diagonal extraction on a countable dense subset of
-- `ℝ^d`, define the limit by the upper-orthant envelope of the pointwise subsequential limits, and
-- then use coordinatewise monotonicity together with right continuity to upgrade convergence to
-- every continuity point of the limit function.
/-- Exercise 13.3.4 (1): Item (i). Helly's theorem remains valid for the multivariate class `V_d`
of coordinatewise monotone, bounded, right-continuous functions on `ℝ^d`. -/
theorem exists_helly_subsequence_tendsto_at_continuity_points_in_Rd
    (d : ℕ) (u : ℕ → (Fin d → ℝ) → ℝ)
    (hV : ∀ n : ℕ, IsCoordinatewiseRightContinuousMonotoneBoundedFunction (u n))
    (h_uniform : ∃ C : ℝ, ∀ n (x : Fin d → ℝ), ‖u n x‖ ≤ C) :
    ∃ φ : ℕ → ℕ, ∃ F : (Fin d → ℝ) → ℝ, IsHellySubsequenceLimitInRd u φ F := by
  obtain ⟨C, hC⟩ := h_uniform
  have hmono : ∀ n, Monotone (u n) := fun n ↦ (hV n).monotone
  obtain ⟨φ, hφ, g, hgTendsto, hgMonotone, hgBound⟩ :=
    existsStrictMonoSubseqTendstoRatVec d u hC hmono
  have hLower : ∀ q, -C ≤ g q := fun q ↦ (hgBound q).1
  have hUpper : ∀ q, g q ≤ C := fun q ↦ (hgBound q).2
  let F : (Fin d → ℝ) → ℝ := ratUpperEnvelopeVec g
  have hFmem : IsCoordinatewiseRightContinuousMonotoneBoundedFunction F :=
    ratUpperEnvelopeVec_memVd hLower hUpper hgMonotone
  refine ⟨φ, F, ?_⟩
  refine
    { strictMono := hφ
      limit_mem := hFmem
      tendsto_at_continuity_points := ?_ }
  intro x hxcont
  have hxcont' : ContinuousAt (ratUpperEnvelopeVec g) x := by
    simpa [F] using hxcont
  -- Proof comment: the rational-grid convergence gives one-sided order bounds, and continuity of
  -- `F` upgrades them to full convergence at continuity points.
  rw [tendsto_order]
  constructor
  · intro a ha
    have ha' : a < ratUpperEnvelopeVec g x := by
      simpa [F] using ha
    simpa [F] using
      eventuallyGtSubseqOfLtRatUpperEnvelopeVec hgTendsto hLower hmono hxcont' ha'
  · intro b hb
    have hb' : ratUpperEnvelopeVec g x < b := by
      simpa [F] using hb
    simpa [F] using
      eventuallyLtSubseqOfRatUpperEnvelopeVecLt hgTendsto hmono hb'

-- Proof sketch: identify each subprobability finite measure on `ℝ^d` with its lower-orthant
-- distribution function, apply the multidimensional Helly theorem from part (1) to obtain
-- subsequential weak limits, and use the standard Polish-space converse on `ℝ^d` to recover
-- tightness from weak relative sequential compactness.
/-- Exercise 13.3.4 (2): Item (ii). Prohorov's theorem holds on `ℝ^d`, modeled as `Fin d → ℝ`, so
for subprobability finite measures tightness is equivalent to weak relative sequential
compactness. -/
theorem prohorov_theorem_iff_tight_in_Rd
    (d : ℕ) (ℱ : Set (FiniteMeasure (Fin d → ℝ)))
    (hℱ : ∀ μ ∈ ℱ, μ.mass ≤ 1) :
    IsTightMeasureSet (((↑) : FiniteMeasure (Fin d → ℝ) → Measure (Fin d → ℝ)) '' ℱ) ↔
      (∀ μs : ℕ → FiniteMeasure (Fin d → ℝ), (∀ n, μs n ∈ ℱ) →
        ∃ μ : FiniteMeasure (Fin d → ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (μs ∘ φ) atTop (𝓝 μ)) := by
  constructor
  · exact isWeaklyRelativelySequentiallyCompactFamily_of_isTightMeasureSet ℱ hℱ
  · exact isTightMeasureSet_of_isWeaklyRelativelySequentiallyCompactFamily ℱ hℱ

end
