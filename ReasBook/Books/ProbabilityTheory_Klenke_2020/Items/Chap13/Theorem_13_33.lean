/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sequences

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set
open scoped Topology

noncomputable section

section

/-- Helper for Theorem 13.33: a uniformly bounded sequence of Stieltjes functions admits a
strictly increasing subsequence whose values converge at every rational point, and the rational
limit profile remains monotone and uniformly bounded. -/
private theorem existsStrictMonoSubseqTendstoRat
    (u : ℕ → StieltjesFunction ℝ) {C : ℝ} (hC : ∀ n x, |u n x| ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℚ → ℝ,
      (∀ q : ℚ, Tendsto (fun k ↦ u (φ k) q) atTop (𝓝 (g q))) ∧
      Monotone g ∧ ∀ q : ℚ, -C ≤ g q ∧ g q ≤ C := by
  let K : Set (ℚ → ℝ) := Set.pi Set.univ (fun _ : ℚ ↦ Set.Icc (-C) C)
  have hKCompact : IsCompact K := by
    simpa [K] using isCompact_univ_pi (fun _ : ℚ ↦ isCompact_Icc)
  have hu_mem : ∀ n, (fun q : ℚ ↦ u n q) ∈ K := by
    -- Every rational section stays inside the common compact interval.
    intro n q _
    exact abs_le.mp (hC n q)
  obtain ⟨g, hgK, φ, hφ, hφtendsto⟩ := hKCompact.tendsto_subseq hu_mem
  have hgTendsto : ∀ q : ℚ, Tendsto (fun k ↦ u (φ k) q) atTop (𝓝 (g q)) := by
    intro q
    -- Product convergence is exactly coordinatewise convergence on `ℚ`.
    simpa [Function.comp] using (tendsto_pi_nhds.1 hφtendsto q)
  have hgMonotone : Monotone g := by
    intro p q hpq
    -- The pointwise order on the subsequence survives passage to the limit.
    have hpq' : (p : ℝ) ≤ q := by
      exact_mod_cast hpq
    exact le_of_tendsto_of_tendsto (hgTendsto p) (hgTendsto q)
      (Eventually.of_forall fun k ↦ (u (φ k)).mono hpq')
  have hgBound : ∀ q : ℚ, -C ≤ g q ∧ g q ≤ C := by
    intro q
    simpa [K] using hgK q (by simp)
  exact ⟨φ, hφ, g, hgTendsto, hgMonotone, hgBound⟩

/-- Helper for Theorem 13.33: the rational upper-envelope attached to `g` is the infimum of the
values `g q` over rational points strictly to the right of `x`. -/
private noncomputable def ratUpperEnvelope (g : ℚ → ℝ) (x : ℝ) : ℝ :=
  ⨅ r : {q : ℚ // x < q}, g r

/-- Helper for Theorem 13.33: there is always a rational point strictly to the right of a real
number, so the indexing type of `ratUpperEnvelope g x` is nonempty. -/
private theorem ratUpperEnvelope_nonempty (x : ℝ) : Nonempty {q : ℚ // x < q} := by
  obtain ⟨q, hq⟩ := exists_rat_gt x
  exact ⟨⟨q, hq⟩⟩

/-- Helper for Theorem 13.33: a uniform lower bound for `g` gives a lower bound for every
rational upper-envelope indexing family. -/
private theorem ratUpperEnvelope_rangeBddBelow {g : ℚ → ℝ} {B : ℝ}
    (hB : ∀ q, B ≤ g q) (x : ℝ) :
    BddBelow (Set.range fun r : {q : ℚ // x < q} ↦ g r) := by
  refine ⟨B, ?_⟩
  rintro y ⟨r, rfl⟩
  exact hB r

/-- Helper for Theorem 13.33: the rational upper-envelope of a monotone rational profile is
monotone on `ℝ`. -/
private theorem ratUpperEnvelope_monotone {g : ℚ → ℝ} {B : ℝ}
    (hB : ∀ q, B ≤ g q) (_hg : Monotone g) :
    Monotone (ratUpperEnvelope g) := by
  intro x y hxy
  letI : Nonempty {q : ℚ // y < q} := ratUpperEnvelope_nonempty y
  -- The infimum over the larger right-ray `{q | x < q}` is below every term from the smaller
  -- right-ray `{q | y < q}`.
  unfold ratUpperEnvelope
  refine le_ciInf fun r ↦ ?_
  exact (ciInf_le (ratUpperEnvelope_rangeBddBelow hB x) ⟨r.1, hxy.trans_lt r.2⟩).trans_eq rfl

/-- Helper for Theorem 13.33: taking the infimum of the envelope over rational points strictly to
the right of `x` returns the envelope value at `x`. This is the stable right-ray normalization
used in the right-continuity proof. -/
private theorem ratUpperEnvelope_iInf_rat_gt_eq {g : ℚ → ℝ} {B : ℝ}
    (hB : ∀ q, B ≤ g q) (hg : Monotone g) (x : ℝ) :
    (⨅ r : {q : ℚ // x < q}, ratUpperEnvelope g r) = ratUpperEnvelope g x := by
  letI : Nonempty {q : ℚ // x < q} := ratUpperEnvelope_nonempty x
  have hEnvMono := ratUpperEnvelope_monotone hB hg
  have hEnvRangeBddBelow :
      BddBelow (Set.range fun r : {q : ℚ // x < q} ↦ ratUpperEnvelope g r) := by
    refine ⟨ratUpperEnvelope g x, ?_⟩
    rintro z ⟨r, rfl⟩
    exact hEnvMono (le_of_lt r.2)
  apply le_antisymm
  · -- A rational point `r ∈ (x, q)` witnesses that the right-ray infimum is below `g q`.
    refine le_ciInf fun q ↦ ?_
    obtain ⟨r, hxr, hrq⟩ := exists_rat_btwn q.2
    calc
      (⨅ s : {q : ℚ // x < q}, ratUpperEnvelope g s) ≤ ratUpperEnvelope g r := by
        exact ciInf_le hEnvRangeBddBelow ⟨r, hxr⟩
      _ ≤ g q := by
        exact ciInf_le_of_le (ratUpperEnvelope_rangeBddBelow hB r) ⟨q, by exact_mod_cast hrq⟩ le_rfl
  · -- Monotonicity makes `ratUpperEnvelope g x` a lower bound for all later envelope values.
    refine le_ciInf fun r ↦ ?_
    exact hEnvMono (le_of_lt r.2)

/-- Helper for Theorem 13.33: the rational upper-envelope is right-continuous, so it defines a
Stieltjes function once monotonicity is known. -/
private theorem ratUpperEnvelope_rightContinuous {g : ℚ → ℝ} {B : ℝ}
    (hB : ∀ q, B ≤ g q) (hg : Monotone g) (x : ℝ) :
    ContinuousWithinAt (ratUpperEnvelope g) (Ici x) x := by
  have hEnvMono := ratUpperEnvelope_monotone hB hg
  have hImageBdd : BddBelow (ratUpperEnvelope g '' Ioi x) := by
    refine ⟨ratUpperEnvelope g x, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact hEnvMono (le_of_lt hy)
  -- Route correction: normalize the right limit through rational right-rays instead of proving a
  -- separate `sInf`-image identity with repeated set/image coercions.
  rw [← continuousWithinAt_Ioi_iff_Ici]
  rw [hEnvMono.continuousWithinAt_Ioi_iff_rightLim_eq]
  rw [hEnvMono.rightLim_eq_sInf, sInf_image']
  · rw [Real.iInf_Ioi_eq_iInf_rat_gt x hImageBdd hEnvMono]
    exact ratUpperEnvelope_iInf_rat_gt_eq hB hg x
  · rw [← neBot_iff]
    infer_instance

/-- Helper for Theorem 13.33: if `a` lies strictly below the limit envelope at a continuity
point `x`, then the extracted subsequence is eventually above `a` at `x`. -/
private theorem eventually_gt_subseq_of_lt_ratUpperEnvelope
    {u : ℕ → StieltjesFunction ℝ} {φ : ℕ → ℕ} {g : ℚ → ℝ} {C x a : ℝ}
    (hgTendsto : ∀ q : ℚ, Tendsto (fun k ↦ u (φ k) q) atTop (𝓝 (g q)))
    (hgLower : ∀ q, -C ≤ g q)
    (hxcont : ContinuousAt (ratUpperEnvelope g) x) (ha : a < ratUpperEnvelope g x) :
    ∀ᶠ k in atTop, a < u (φ k) x := by
  let ε : ℝ := (ratUpperEnvelope g x - a) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨δ, _hδpos, hδ⟩ := Metric.continuousAt_iff.1 hxcont ε hε
  let y : ℝ := x - δ / 2
  have hyx : y < x := by
    dsimp [y]
    linarith
  have hdist : dist y x < δ := by
    dsimp [y]
    rw [Real.dist_eq]
    ring_nf
    rw [abs_of_nonpos]
    · linarith
    · linarith
  have hyClose : dist (ratUpperEnvelope g y) (ratUpperEnvelope g x) < ε := hδ hdist
  have hFxε_lt_Fy : ratUpperEnvelope g x - ε < ratUpperEnvelope g y := by
    have hyClose' : |ratUpperEnvelope g y - ratUpperEnvelope g x| < ε := by
      simpa [Real.dist_eq] using hyClose
    have hAbs := abs_lt.mp hyClose'
    linarith
  obtain ⟨qMinus, hyq, hqx⟩ := exists_rat_btwn hyx
  have hFy_le_gq : ratUpperEnvelope g y ≤ g qMinus := by
    -- Any rational point above `y` bounds the infimum defining `ratUpperEnvelope g y` from above.
    exact ciInf_le (ratUpperEnvelope_rangeBddBelow hgLower y) ⟨qMinus, hyq⟩
  have ha_lt_gq : a < g qMinus := by
    have : ratUpperEnvelope g x - ε < g qMinus := lt_of_lt_of_le hFxε_lt_Fy hFy_le_gq
    dsimp [ε] at this
    linarith
  have hEventually : ∀ᶠ k in atTop, a < u (φ k) qMinus := by
    exact (tendsto_order.1 (hgTendsto qMinus)).1 a ha_lt_gq
  filter_upwards [hEventually] with k hk
  exact lt_of_lt_of_le hk ((u (φ k)).mono hqx.le)

/-- Helper for Theorem 13.33: if `b` lies strictly above the limit envelope at `x`, then the
extracted subsequence is eventually below `b` at `x`. -/
private theorem eventually_lt_subseq_of_ratUpperEnvelope_lt
    {u : ℕ → StieltjesFunction ℝ} {φ : ℕ → ℕ} {g : ℚ → ℝ} {x b : ℝ}
    (hgTendsto : ∀ q : ℚ, Tendsto (fun k ↦ u (φ k) q) atTop (𝓝 (g q)))
    (hb : ratUpperEnvelope g x < b) :
    ∀ᶠ k in atTop, u (φ k) x < b := by
  let ε : ℝ := (b - ratUpperEnvelope g x) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hExists : ∃ q : ℚ, x < q ∧ g q < ratUpperEnvelope g x + ε := by
    by_contra hExists
    letI : Nonempty {q : ℚ // x < q} := ratUpperEnvelope_nonempty x
    have hLowerBound : ∀ q : {q : ℚ // x < q}, ratUpperEnvelope g x + ε ≤ g q := by
      intro q
      exact le_of_not_gt fun hlt => hExists ⟨q.1, q.2, hlt⟩
    have hImpossible : ratUpperEnvelope g x + ε ≤ ratUpperEnvelope g x := by
      exact le_ciInf hLowerBound
    linarith
  rcases hExists with ⟨qPlus, hxq, hqPlus⟩
  have hgq_lt_b : g qPlus < b := by
    dsimp [ε] at hqPlus
    linarith
  have hEventually : ∀ᶠ k in atTop, u (φ k) qPlus < b := by
    exact (tendsto_order.1 (hgTendsto qPlus)).2 b hgq_lt_b
  filter_upwards [hEventually] with k hk
  exact lt_of_le_of_lt ((u (φ k)).mono hxq.le) hk

-- Proof sketch: use a diagonal extraction on the rational numbers to obtain pointwise convergence
-- along a subsequence on `ℚ`, define the candidate limit by the right-envelope of those rational
-- limits, and use monotonicity plus right continuity to upgrade convergence to every continuity
-- point of the limit function.
/-- Theorem 13.33: every uniformly bounded sequence in Helly's class `V` admits a subsequence
that converges pointwise at every continuity point of a limit function in the same class. -/
theorem exists_helly_subsequence_tendsto_at_continuity_points
    (u : ℕ → StieltjesFunction ℝ)
    (h_uniform : Bornology.IsBounded (⋃ n, range (u n))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ F : StieltjesFunction ℝ, Bornology.IsBounded (range F) ∧
        ∀ ⦃x : ℝ⦄, ContinuousAt F x →
          Tendsto (fun k ↦ u (φ k) x) atTop (𝓝 (F x)) := by
  let S : Set ℝ := ⋃ n, range (u n)
  have hS : Bornology.IsBounded S := by
    simpa [S] using h_uniform
  obtain ⟨C, hCnorm⟩ := (Bornology.IsBounded.exists_norm_le (E := ℝ) (s := S) hS)
  have hC : ∀ n x, |u n x| ≤ C := by
    intro n x
    -- The bounded union hypothesis gives one common real interval containing every function value.
    have hxmem : u n x ∈ S := by
      exact mem_iUnion.2 ⟨n, mem_range_self x⟩
    simpa [Real.norm_eq_abs] using hCnorm (u n x) hxmem
  obtain ⟨φ, hφ, g, hgTendsto, hgMonotone, hgBound⟩ :=
    existsStrictMonoSubseqTendstoRat u (C := C) hC
  have hgLower : ∀ q, -C ≤ g q := fun q ↦ (hgBound q).1
  let F : StieltjesFunction ℝ :=
    { toFun := ratUpperEnvelope g
      mono' := ratUpperEnvelope_monotone hgLower hgMonotone
      right_continuous' := ratUpperEnvelope_rightContinuous hgLower hgMonotone }
  have hFBounded : Bornology.IsBounded (range F) := by
    have hRangeSubset : range F ⊆ Set.Icc (-C) C := by
      rintro y ⟨x, rfl⟩
      constructor
      · letI : Nonempty {q : ℚ // x < q} := ratUpperEnvelope_nonempty x
        -- The lower envelope stays above the common lower bound for the rational profile.
        change -C ≤ ratUpperEnvelope g x
        exact le_ciInf fun q ↦ (hgBound q).1
      · -- The upper envelope lies below every rational value to its right, hence below `C`.
        obtain ⟨q, hq⟩ := exists_rat_gt x
        change ratUpperEnvelope g x ≤ C
        exact (ciInf_le (ratUpperEnvelope_rangeBddBelow hgLower x) ⟨q, hq⟩).trans (hgBound q).2
    exact (Metric.isBounded_Icc (-C) C).subset hRangeSubset
  refine ⟨φ, hφ, F, hFBounded, ?_⟩
  intro x hxcont
  -- The continuity-point convergence follows from a two-sided monotone squeeze between rational
  -- points where the extracted subsequence already converges.
  rw [tendsto_order]
  constructor
  · intro a ha
    have hxcont' : ContinuousAt (ratUpperEnvelope g) x := by
      simpa [F] using hxcont
    have ha' : a < ratUpperEnvelope g x := by
      simpa [F] using ha
    simpa [F] using
      eventually_gt_subseq_of_lt_ratUpperEnvelope hgTendsto hgLower hxcont' ha'
  · intro b hb
    have hb' : ratUpperEnvelope g x < b := by
      simpa [F] using hb
    simpa [F] using
      eventually_lt_subseq_of_ratUpperEnvelope_lt hgTendsto hb'

end
