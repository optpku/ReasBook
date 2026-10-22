/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_26
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Example_2_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_35

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

private noncomputable def blockMarkToUnitInterval {n : ℕ} :
    Set.Ioc (n : ℝ) (n + 1) → I
  | x =>
      ⟨(x : ℝ) - n, by
        constructor
        · linarith [x.2.1]
        · linarith [x.2.2]⟩

private noncomputable def unitIntervalBlockMarks
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1)) (n : ℕ) :
    ℕ → Ω → I :=
  fun k ω ↦ blockMarkToUnitInterval (X n (k - 1) ω)

/-- Helper for Exercise 5.5.1: globally shift the real block `(n,n+1]` back to the unit interval
and clamp the result to `[0,1]`. On the block itself this agrees with the exact subtype map
`blockMarkToUnitInterval`. -/
private noncomputable def blockRealToUnitInterval (n : ℕ) : ℝ → I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one ∘ fun x : ℝ ↦ x - n

private noncomputable def lastBlockTime (t : NNReal) (n : ℕ)
    (hn : n = Nat.floor (t : ℝ)) : I :=
  ⟨(t : ℝ) - n, by
    constructor
    · have hn_le : (n : ℝ) ≤ t := by
        rw [hn]
        exact_mod_cast Nat.floor_le t.2
      linarith
    · have ht_lt : (t : ℝ) < Nat.floor (t : ℝ) + 1 := by
        simpa using Nat.lt_floor_add_one (t : ℝ)
      rw [← hn] at ht_lt
      linarith⟩

section

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: translating a point of `(n, n + 1]` to the unit interval keeps it
strictly above `0`. -/
private theorem zero_lt_blockMarkToUnitInterval {n : ℕ} (x : Set.Ioc (n : ℝ) (n + 1)) :
    (0 : I) < blockMarkToUnitInterval x := by
  -- Proof comment: points in `Set.Ioc (n : ℝ) (n + 1)` satisfy `n < x`, so subtracting `n`
  -- lands strictly inside the positive part of the unit interval.
  change (0 : ℝ) < (x : ℝ) - n
  linarith [x.2.1]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: translating a point of `(n, n + 1]` to the unit interval keeps it
below `1`. -/
private theorem blockMarkToUnitInterval_le_one {n : ℕ} (x : Set.Ioc (n : ℝ) (n + 1)) :
    blockMarkToUnitInterval x ≤ (1 : I) := by
  -- Proof comment: points in the block satisfy `x ≤ n + 1`, so subtracting `n` puts them at
  -- most at the right endpoint `1`.
  change (x : ℝ) - n ≤ 1
  linarith [x.2.2]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: inside the last active block, the translated local-time comparison
is equivalent to the original global-time comparison. -/
private theorem blockMarkToUnitInterval_le_iff
    {n : ℕ} (x : Set.Ioc (n : ℝ) (n + 1)) (t : I) :
    blockMarkToUnitInterval x ≤ t ↔ (x : ℝ) ≤ n + (t : ℝ) := by
  -- Proof comment: both sides compare the same point after translating the block `(n, n + 1]`
  -- back by `n`, so the inequality is preserved exactly.
  change ((x : ℝ) - n ≤ (t : ℝ) ↔ (x : ℝ) ≤ n + (t : ℝ))
  constructor <;> intro h <;> linarith

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: inside the last active block, the translated local-time comparison
is equivalent to the original global-time comparison. -/
private theorem blockMarkToUnitInterval_le_lastBlockTime_iff
    {n : ℕ} (t : NNReal) (hn : n = Nat.floor (t : ℝ))
    (x : Set.Ioc (n : ℝ) (n + 1)) :
    blockMarkToUnitInterval x ≤ lastBlockTime t n hn ↔ (x : ℝ) ≤ (t : ℝ) := by
  -- Proof comment: both quantities are obtained from the original coordinates by subtracting the
  -- same block index `n`, so the comparison is preserved exactly.
  change ((x : ℝ) - n ≤ (t : ℝ) - n ↔ (x : ℝ) ≤ (t : ℝ))
  constructor <;> intro h <;> linarith

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: the global shift-and-clamp transport is literally subtraction by
`n` on the active block `(n,n+1]`. -/
private theorem coe_blockRealToUnitInterval_of_mem {n : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ioc (n : ℝ) (n + 1)) :
    ((blockRealToUnitInterval n x : I) : ℝ) = x - n := by
  -- Proof comment: for points already lying in the block, the clamping map `Set.projIcc`
  -- acts trivially because the shifted coordinate is already in `[0,1]`.
  have hmem : x - n ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hx.1]
    · linarith [hx.2]
  simpa [blockRealToUnitInterval, Function.comp, hmem] using
    congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hmem)

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: on subtype-valued block marks, the global real transport agrees
with the exact block translation. -/
private theorem blockRealToUnitInterval_eq_blockMarkToUnitInterval {n : ℕ}
    (x : Set.Ioc (n : ℝ) (n + 1)) :
    blockRealToUnitInterval n (x : ℝ) = blockMarkToUnitInterval x := by
  -- Proof comment: both maps have the same real coordinate on the active block, so the subtype
  -- points in `I` coincide.
  ext
  simpa using coe_blockRealToUnitInterval_of_mem (n := n) x.2

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: the exact subtype translation map is measurable. -/
private theorem measurable_blockMarkToUnitInterval {n : ℕ} :
    Measurable (blockMarkToUnitInterval (n := n)) := by
  -- Proof comment: the map is just subtraction by `n`, with codomain restricted to the unit
  -- interval by the block inequalities.
  have hsub :
      Measurable (fun x : Set.Ioc (n : ℝ) (n + 1) ↦ (x : ℝ) - (n : ℝ)) :=
    measurable_subtype_coe.sub (measurable_const : Measurable fun _ : Set.Ioc (n : ℝ) (n + 1) ↦ (n : ℝ))
  have hmem : ∀ x : Set.Ioc (n : ℝ) (n + 1), ((x : ℝ) - (n : ℝ)) ∈ I := fun x ↦ by
    constructor
    · linarith [x.2.1]
    · linarith [x.2.2]
  change Measurable (fun x : Set.Ioc (n : ℝ) (n + 1) ↦
    (⟨(x : ℝ) - (n : ℝ), hmem x⟩ : I))
  exact hsub.subtype_mk (h := hmem)

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: the global real transport is measurable. -/
private theorem measurable_blockRealToUnitInterval (n : ℕ) :
    Measurable (blockRealToUnitInterval n) := by
  -- Proof comment: compose the continuous projection onto `[0,1]` with the measurable shift
  -- `x ↦ x - n`.
  simpa [blockRealToUnitInterval, Function.comp] using
    (continuous_projIcc.measurable.comp (measurable_id.sub measurable_const))

end

/-- The counting process from Exercise 5.5.1, written in the canonical `0`-based Lean indexing of
the textbook families `L₁, L₂, …` and `X₁¹, X₂¹, …`. Thus `L n` represents `L_(n+1)` and
`X n k` represents `X_(k+1)^(n+1)`. The implementation reuses the chapter's canonical
unit-interval counting process blockwise after translating the block `(n, n + 1]` to `(0,1]`,
and evaluates the last block at the local time `t - ⌊t⌋`. -/
noncomputable def poissonizedUniformBlockCountingProcess
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1)) :
    NNReal → Ω → ℕ :=
  fun t ω ↦
    Finset.sum (Finset.range (Nat.floor (t : ℝ) + 1)) fun n ↦
      poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
        (if hn : n = Nat.floor (t : ℝ) then lastBlockTime t n hn else 1) ω

section

omit [MeasurableSpace Ω] in
/-- The blockwise Poissonized counting process is the cardinality of the set of `0`-based
block/mark pairs `(n, k)` with `n ≤ ⌊t⌋`, `k < L n`, and `X n k ≤ t`, written as a finite
blockwise sum. -/
theorem poissonizedUniformBlockCountingProcess_apply
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (t : NNReal) (ω : Ω) :
    poissonizedUniformBlockCountingProcess L X t ω =
      Finset.sum (Finset.range (Nat.floor (t : ℝ) + 1)) fun n ↦
        Finset.sum (Finset.range (L n ω)) fun k ↦
          if (X n k ω : ℝ) ≤ (t : ℝ) then 1 else 0 := by
  rw [poissonizedUniformBlockCountingProcess]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [poissonizedUniformCountingProcess_apply]
  rw [← Finset.Ico_succ_right_eq_Icc]
  change
    (∑ i ∈ Finset.Ico 1 (Nat.succ (L n ω)),
        if
            0 < unitIntervalBlockMarks X n i ω ∧
              unitIntervalBlockMarks X n i ω ≤
                if hn : n = Nat.floor (t : ℝ) then lastBlockTime t n hn else 1 then
          1
        else 0) =
      ∑ k ∈ Finset.range (L n ω), if (X n k ω : ℝ) ≤ (t : ℝ) then 1 else 0
  rw [Nat.succ_eq_add_one, Nat.add_comm]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  by_cases hlast : n = Nat.floor (t : ℝ)
  · -- Proof comment: on the final active block, the local cutoff `t - n` is equivalent to the
    -- original condition `X n k ≤ t`.
    subst hlast
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hpos : (0 : I) < blockMarkToUnitInterval (X (Nat.floor (t : ℝ)) k ω) :=
      zero_lt_blockMarkToUnitInterval (X (Nat.floor (t : ℝ)) k ω)
    have hcut :
        blockMarkToUnitInterval (X (Nat.floor (t : ℝ)) k ω) ≤
            lastBlockTime t (Nat.floor (t : ℝ)) rfl ↔
          (X (Nat.floor (t : ℝ)) k ω : ℝ) ≤ (t : ℝ) :=
      blockMarkToUnitInterval_le_lastBlockTime_iff t rfl
        (X (Nat.floor (t : ℝ)) k ω)
    rw [unitIntervalBlockMarks]
    simp [hpos]
    by_cases hx : (X (Nat.floor (t : ℝ)) k ω : ℝ) ≤ (t : ℝ)
    · have hlocal :
          blockMarkToUnitInterval (X (Nat.floor (t : ℝ)) k ω) ≤
            lastBlockTime t (Nat.floor (t : ℝ)) rfl := hcut.2 hx
      simp [hx, hlocal]
    · have hlocal :
          ¬blockMarkToUnitInterval (X (Nat.floor (t : ℝ)) k ω) ≤
            lastBlockTime t (Nat.floor (t : ℝ)) rfl := by
        intro hlocal
        exact hx (hcut.1 hlocal)
      have hlocal_lt :
          lastBlockTime t (Nat.floor (t : ℝ)) rfl <
            blockMarkToUnitInterval (X (Nat.floor (t : ℝ)) k ω) :=
        lt_of_not_ge hlocal
      simp [hx, hlocal_lt]
  · -- Proof comment: on every earlier block, all block points lie before time `t`, so both the
    -- local and global indicators are identically `1`.
    have hn_le : n ≤ Nat.floor (t : ℝ) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hn_lt : n < Nat.floor (t : ℝ) := lt_of_le_of_ne hn_le hlast
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hpos : (0 : I) < blockMarkToUnitInterval (X n k ω) :=
      zero_lt_blockMarkToUnitInterval (X n k ω)
    have hle_one : blockMarkToUnitInterval (X n k ω) ≤ (1 : I) :=
      blockMarkToUnitInterval_le_one (X n k ω)
    have hx_le_t : (X n k ω : ℝ) ≤ (t : ℝ) := by
      have hx_le_block_end : (X n k ω : ℝ) ≤ n + 1 := (X n k ω).2.2
      have hblock_end_le_floor : (n + 1 : ℝ) ≤ Nat.floor (t : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hn_lt
      have hfloor_le_t : (Nat.floor (t : ℝ) : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast Nat.floor_le t.2
      linarith
    simp [unitIntervalBlockMarks, hlast, hpos, hle_one, hx_le_t]

end

section

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: the blockwise counting process starts at `0`. -/
private theorem poissonizedUniformBlockCountingProcess_zero_eq
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1)) :
    poissonizedUniformBlockCountingProcess L X 0 = 0 := by
  ext ω
  -- Proof comment: at time `0`, every block indicator vanishes because each block point has
  -- strictly positive real coordinate.
  rw [poissonizedUniformBlockCountingProcess_apply]
  simp only [NNReal.coe_zero, Nat.floor_zero]
  change (∑ k ∈ Finset.range (L 0 ω), if (X 0 k ω : ℝ) ≤ 0 then (1 : ℕ) else 0) = (0 : ℕ)
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hx_pos : (0 : ℝ) < (X 0 k ω : ℝ) := by
    simpa using (X 0 k ω).2.1
  have hx_not_le : ¬((X 0 k ω : ℝ) ≤ 0) := by
    linarith
  simp [hx_not_le]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: the blockwise counting process is nondecreasing in time. -/
private theorem poissonizedUniformBlockCountingProcess_mono
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1)) :
    Monotone (poissonizedUniformBlockCountingProcess L X) := by
  intro s t hst ω
  -- Proof comment: compare the pathwise counting formulas at `s` and `t`; each indicator counted
  -- at time `s` is also counted at time `t`, and the extra blocks present at time `t` contribute
  -- only nonnegative terms.
  rw [poissonizedUniformBlockCountingProcess_apply, poissonizedUniformBlockCountingProcess_apply]
  let Cs : ℕ → ℕ := fun n ↦
    ∑ k ∈ Finset.range (L n ω), if (X n k ω : ℝ) ≤ (s : ℝ) then 1 else 0
  let Ct : ℕ → ℕ := fun n ↦
    ∑ k ∈ Finset.range (L n ω), if (X n k ω : ℝ) ≤ (t : ℝ) then 1 else 0
  have hfloor : Nat.floor (s : ℝ) ≤ Nat.floor (t : ℝ) := Nat.floor_mono hst
  have hpointwise :
      ∀ n ∈ Finset.range (Nat.floor (s : ℝ) + 1), Cs n ≤ Ct n := by
    intro n hn
    refine Finset.sum_le_sum ?_
    intro k hk
    by_cases hsx : (X n k ω : ℝ) ≤ (s : ℝ)
    · have htx : (X n k ω : ℝ) ≤ (t : ℝ) := le_trans hsx hst
      simp [hsx, htx]
    · by_cases htx : (X n k ω : ℝ) ≤ (t : ℝ)
      · simp [hsx, htx]
      · simp [hsx, htx]
  have hprefix :
      ∑ n ∈ Finset.range (Nat.floor (s : ℝ) + 1), Cs n ≤
        ∑ n ∈ Finset.range (Nat.floor (s : ℝ) + 1), Ct n := by
    exact Finset.sum_le_sum hpointwise
  have hsuffix :
      ∑ n ∈ Finset.range (Nat.floor (s : ℝ) + 1), Ct n ≤
        ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), Ct n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.succ_le_succ hfloor)) ?_
    intro n hn ht_not_mem
    exact Nat.zero_le _
  exact le_trans hprefix hsuffix

end

section

/-- Helper for Exercise 5.5.1: each half-open unit block has Lebesgue mass `1`, so its restricted
volume measure is a probability measure. -/
private instance blockVolumeIsProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) where
  measure_univ := by
    -- Proof comment: the block `(n,n+1]` has length exactly `1`.
    simp [Measure.restrict_apply, Real.volume_Ioc]

/-- Helper for Exercise 5.5.1: the real-valued mark matrix, viewed row-by-row, has the curried
product law obtained from the pair-indexed product law by `Measure.infinitePi_map_curry`. -/
private theorem blockRowRealFamily_hasLaw
    (P : Measure Ω)
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (hX_indep : iIndepFun (fun p : ℕ × ℕ ↦ fun ω ↦ (X p.1 p.2 ω : ℝ)) P)
    (hX_law : ∀ n k,
      HasLaw (fun ω ↦ (X n k ω : ℝ))
        (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) P) :
    HasLaw
      (fun ω n k ↦ (X n k ω : ℝ))
      (Measure.infinitePi
        (fun n : ℕ ↦ Measure.infinitePi fun _ : ℕ ↦
          volume.restrict (Set.Ioc (n : ℝ) (n + 1))))
      P := by
  letI : IsProbabilityMeasure P := (hX_law 0 0).isProbabilityMeasure
  have hpair :
      HasLaw
        (fun ω : Ω ↦ fun p : ℕ × ℕ ↦ (X p.1 p.2 ω : ℝ))
        (Measure.infinitePi
          (fun p : ℕ × ℕ ↦ volume.restrict (Set.Ioc (p.1 : ℝ) (p.1 + 1))))
        P := by
    refine ⟨aemeasurable_pi_iff.2 (fun p ↦ (hX_law p.1 p.2).aemeasurable), ?_⟩
    -- Proof comment: first identify the joint matrix law with the product of its coordinate
    -- marginals using the given pair-indexed independence.
    calc
      P.map (fun ω : Ω ↦ fun p : ℕ × ℕ ↦ (X p.1 p.2 ω : ℝ))
          = Measure.infinitePi
              (fun p : ℕ × ℕ ↦ P.map (fun ω ↦ (X p.1 p.2 ω : ℝ))) := by
            exact
              (iIndepFun_iff_map_fun_eq_infinitePi_map₀'
                (P := P)
                (X := fun p : ℕ × ℕ ↦ fun ω ↦ (X p.1 p.2 ω : ℝ))
                (fun p ↦ (hX_law p.1 p.2).aemeasurable)).1 hX_indep
      _ = Measure.infinitePi
            (fun p : ℕ × ℕ ↦ volume.restrict (Set.Ioc (p.1 : ℝ) (p.1 + 1))) := by
            congr 1
            funext p
            exact (hX_law p.1 p.2).map_eq
  have hcurry :
      HasLaw
        (MeasurableEquiv.curry ℕ ℕ ℝ)
        (Measure.infinitePi
          (fun n : ℕ ↦ Measure.infinitePi fun _ : ℕ ↦
            volume.restrict (Set.Ioc (n : ℝ) (n + 1))))
        (Measure.infinitePi
          (fun p : ℕ × ℕ ↦ volume.restrict (Set.Ioc (p.1 : ℝ) (p.1 + 1)))) := by
    refine ⟨(MeasurableEquiv.curry ℕ ℕ ℝ).measurable.aemeasurable, ?_⟩
    -- Proof comment: then curry the pair-indexed product law into the row-family product law.
    simpa using
      (Measure.infinitePi_map_curry
        (μ := fun n _ : ℕ ↦ volume.restrict (Set.Ioc (n : ℝ) (n + 1))))
  -- Proof comment: composing the pair law with the measurable curry equivalence gives the row law.
  simpa [Function.comp] using hcurry.comp hpair

/-- Helper for Exercise 5.5.1: the row process of real-valued block marks is independent across
blocks. -/
private theorem blockRowRealFamily_iIndep
    (P : Measure Ω)
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (hX_indep : iIndepFun (fun p : ℕ × ℕ ↦ fun ω ↦ (X p.1 p.2 ω : ℝ)) P)
    (hX_law : ∀ n k,
      HasLaw (fun ω ↦ (X n k ω : ℝ))
        (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) P) :
    iIndepFun (fun n : ℕ ↦ fun ω ↦ fun k : ℕ ↦ (X n k ω : ℝ)) P := by
  letI : IsProbabilityMeasure P := (hX_law 0 0).isProbabilityMeasure
  have hfamily := blockRowRealFamily_hasLaw P X hX_indep hX_law
  have hrow :
      ∀ n,
        HasLaw
          (fun ω ↦ fun k : ℕ ↦ (X n k ω : ℝ))
          (Measure.infinitePi fun _ : ℕ ↦ volume.restrict (Set.Ioc (n : ℝ) (n + 1)))
          P := by
    intro n
    have heval :
        HasLaw
          (Function.eval n)
          (Measure.infinitePi fun _ : ℕ ↦ volume.restrict (Set.Ioc (n : ℝ) (n + 1)))
          (Measure.infinitePi
            (fun m : ℕ ↦ Measure.infinitePi fun _ : ℕ ↦
              volume.restrict (Set.Ioc (m : ℝ) (m + 1)))) := by
      exact
        (measurePreserving_eval_infinitePi
          (fun m : ℕ ↦ Measure.infinitePi fun _ : ℕ ↦
            volume.restrict (Set.Ioc (m : ℝ) (m + 1))) n).hasLaw
    -- Proof comment: evaluate the joint row-family law at a fixed block index.
    simpa [Function.comp] using heval.comp hfamily
  -- Proof comment: compare the joint row-family law with the infinite product of its row
  -- marginals to recover independence of the rows.
  refine
    (iIndepFun_iff_map_fun_eq_infinitePi_map₀'
      (P := P)
      (X := fun n : ℕ ↦ fun ω ↦ fun k : ℕ ↦ (X n k ω : ℝ))
      (fun n ↦ (hrow n).aemeasurable)).2 ?_
  calc
    P.map (fun ω ↦ fun n k ↦ (X n k ω : ℝ))
        = Measure.infinitePi
            (fun n : ℕ ↦ Measure.infinitePi fun _ : ℕ ↦
              volume.restrict (Set.Ioc (n : ℝ) (n + 1))) := hfamily.map_eq
    _ = Measure.infinitePi
          (fun n : ℕ ↦ P.map (fun ω ↦ fun k : ℕ ↦ (X n k ω : ℝ))) := by
          congr 1
          funext n
          symm
          exact (hrow n).map_eq

/-- Helper for Exercise 5.5.1: the whole length sequence is independent of the real-valued
row-process family obtained by currying the mark matrix. -/
private theorem lengthSequence_indep_blockRowRealFamily
    (P : Measure Ω)
    (L : ℕ → Ω → ℕ)
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (hLX_indep :
      IndepFun (fun ω ↦ fun n : ℕ ↦ L n ω)
        (fun ω ↦ fun p : ℕ × ℕ ↦ (X p.1 p.2 ω : ℝ)) P) :
    IndepFun
      (fun ω ↦ fun n : ℕ ↦ L n ω)
      (fun ω ↦ fun n : ℕ ↦ fun k : ℕ ↦ (X n k ω : ℝ))
      P := by
  -- Proof comment: only the second coordinate changes here, by postcomposing the pair-indexed
  -- matrix with the measurable curry equivalence.
  simpa [Function.comp] using
    hLX_indep.comp measurable_id (MeasurableEquiv.curry ℕ ℕ ℝ).measurable

end

section

/-- Helper for Exercise 5.5.1: pushing the restricted block volume through the global
shift-and-clamp map gives the canonical unit-interval volume. -/
private theorem blockRealToUnitInterval_map_blockVolume (n : ℕ) :
    Measure.map (blockRealToUnitInterval n)
    (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) =
      (volume : Measure I) := by
  have hcoemap :
      Measure.map ((↑) : I → ℝ)
          (Measure.map (blockRealToUnitInterval n)
            (volume.restrict (Set.Ioc (n : ℝ) (n + 1)))) =
        Measure.map ((↑) : I → ℝ) (volume : Measure I) := by
    have hproj_eq :
        (fun x : ℝ ↦ ((blockRealToUnitInterval n x : I) : ℝ)) =ᵐ[volume.restrict (Set.Ioc (n : ℝ) (n + 1))]
        (fun x : ℝ ↦ x - n) := by
      -- Proof comment: on the restricted block, `Set.projIcc` is the identity after shifting.
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact coe_blockRealToUnitInterval_of_mem (n := n) hx
    calc
      Measure.map ((↑) : I → ℝ)
          (Measure.map (blockRealToUnitInterval n)
            (volume.restrict (Set.Ioc (n : ℝ) (n + 1)))) =
        Measure.map (fun x : ℝ ↦ x - n)
          (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) := by
            rw [Measure.map_map measurable_subtype_coe (measurable_blockRealToUnitInterval n)]
            exact Measure.map_congr hproj_eq
      _ = Measure.map (fun x : ℝ ↦ x - n)
          (volume.restrict (Set.Icc (n : ℝ) (n + 1))) := by
            rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
      _ = (Measure.map (fun x : ℝ ↦ x - n) (volume : Measure ℝ)).restrict I := by
            have hpre :
                (fun x : ℝ ↦ x - n) ⁻¹' I = Set.Icc (n : ℝ) (n + 1) := by
              ext x
              constructor <;> intro hx
              · constructor <;> linarith [hx.1, hx.2]
              · constructor
                · linarith [hx.1, hx.2]
                · linarith [hx.1, hx.2]
            simpa [hpre] using
              (Measure.restrict_map (μ := (volume : Measure ℝ))
                (f := fun x : ℝ ↦ x - n)
                (s := I)
                (hf := measurable_id.sub measurable_const)
                (hs := measurableSet_Icc)).symm
      _ = volume.restrict I := by
            rw [show Measure.map (fun x : ℝ ↦ x - n) (volume : Measure ℝ) = volume by
              simpa [sub_eq_add_neg] using
                (map_add_right_eq_self (μ := (volume : Measure ℝ)) (g := (-(n : ℝ))))]
      _ = Measure.map ((↑) : I → ℝ) (volume : Measure I) := by
            simpa using (unitInterval.measurePreserving_coe.map_eq :
              Measure.map ((↑) : I → ℝ) (volume : Measure I) = volume.restrict I).symm
  -- Proof comment: compare both measures after applying the subtype coercion `I → ℝ`, then use
  -- the measurable embedding property of the coercion to pull the equality back to `I`.
  calc
    Measure.map (blockRealToUnitInterval n)
        (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) =
      Measure.comap ((↑) : I → ℝ)
        (Measure.map ((↑) : I → ℝ)
          (Measure.map (blockRealToUnitInterval n)
            (volume.restrict (Set.Ioc (n : ℝ) (n + 1))))) := by
              symm
              exact unitInterval.measurableEmbedding_coe.comap_map _
    _ = Measure.comap ((↑) : I → ℝ) (Measure.map ((↑) : I → ℝ) (volume : Measure I)) := by
          exact congrArg (Measure.comap ((↑) : I → ℝ)) hcoemap
    _ = (volume : Measure I) := unitInterval.measurableEmbedding_coe.comap_map _

/-- Helper for Exercise 5.5.1: every fixed unit block yields a unit-interval Poisson counting
process after translation. -/
private theorem blockCountingProcess_isPoissonOnUnitInterval
    (P : Measure Ω) (α : NNReal) (L : ℕ → Ω → ℕ)
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (hLX_indep :
      IndepFun (fun ω ↦ fun n : ℕ ↦ L n ω)
        (fun ω ↦ fun p : ℕ × ℕ ↦ (X p.1 p.2 ω : ℝ)) P)
    (hX_indep : iIndepFun (fun p : ℕ × ℕ ↦ fun ω ↦ (X p.1 p.2 ω : ℝ)) P)
    (hL_law : ∀ n, HasLaw (L n) (poissonMeasure α) P)
    (hX_law : ∀ n k,
      HasLaw (fun ω ↦ (X n k ω : ℝ))
        (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) P)
    (n : ℕ) :
    let B := poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
    B 0 = 0 ∧
      Monotone B ∧
      HasIndepIncrements B P ∧
      ∀ ⦃s t : I⦄, s ≤ t →
        HasLaw
          (fun ω ↦ B t ω - B s ω)
          (poissonMeasure (α * Real.toNNReal ((t : ℝ) - (s : ℝ)))) P := by
  let F : ℝ → I := blockRealToUnitInterval n
  have hF_meas : Measurable F := measurable_blockRealToUnitInterval n
  have hF_law :
      HasLaw F (volume : Measure I) (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) := by
    -- Proof comment: the translated block measure is exactly the unit-interval volume.
    exact ⟨hF_meas.aemeasurable, blockRealToUnitInterval_map_blockVolume n⟩
  have hrowRealIndep :
      iIndepFun (fun k : ℕ ↦ fun ω ↦ (X n k ω : ℝ)) P := by
    -- Proof comment: fix the block index `n` inside the pairwise independent mark matrix.
    simpa using
      (hX_indep.precomp (g := fun k : ℕ => (n, k)) (by
        intro i j hij
        simpa using congrArg Prod.snd hij))
  have hrowTransportIndep :
      iIndepFun (fun k : ℕ ↦ fun ω ↦ F ((X n k ω : ℝ))) P := by
    -- Proof comment: coordinatewise measurable postcomposition preserves independence.
    simpa [F] using hrowRealIndep.comp (fun _ ↦ F) (fun _ ↦ hF_meas)
  have hrowTransportLaw :
      ∀ k, HasLaw (fun ω ↦ F ((X n k ω : ℝ))) (volume : Measure I) P := by
    intro k
    -- Proof comment: each translated block mark has the unit-interval law by the pushforward
    -- statement proved above.
    simpa [Function.comp, F] using (HasLaw.comp hF_law (hX_law n k))
  have hshiftEq :
      ∀ k, (fun ω ↦ F ((X n k ω : ℝ))) = unitIntervalBlockMarks X n (k + 1) := by
    intro k
    funext ω
    -- Proof comment: the shifted tail of `unitIntervalBlockMarks` is exactly the translated real
    -- block row.
    simpa [F, unitIntervalBlockMarks, Nat.add_comm] using
      blockRealToUnitInterval_eq_blockMarkToUnitInterval (n := n) (X n k ω)
  have hmarks_iid : IsIID (fun k ↦ unitIntervalBlockMarks X n (k + 1)) P := by
    refine ⟨?_, ?_⟩
    · -- Proof comment: rewrite the shifted tail to the transported real row and reuse the
      -- coordinatewise independence already established.
      refine hrowTransportIndep.congr ?_
      intro k
      exact Filter.EventuallyEq.of_eq (hshiftEq k)
    · intro i j
      exact ((hrowTransportLaw i).congr (Filter.EventuallyEq.of_eq (hshiftEq i).symm)).identDistrib
        ((hrowTransportLaw j).congr (Filter.EventuallyEq.of_eq (hshiftEq j).symm))
  have hfirstLaw :
      HasLaw (unitIntervalBlockMarks X n 1) (volume : Measure I) P := by
    -- Proof comment: the theorem on the unit interval asks for the first shifted mark `X 1`;
    -- here it is the translated `k = 0` block mark.
    simpa using ((hrowTransportLaw 0).congr (Filter.EventuallyEq.of_eq (hshiftEq 0).symm))
  have hLX_row :
      IndepFun (L n) (fun ω ↦ fun k : ℕ ↦ (X n k ω : ℝ)) P := by
    have hrows := lengthSequence_indep_blockRowRealFamily P L X hLX_indep
    -- Proof comment: evaluate the independent length/row family at the chosen block index.
    simpa [Function.comp] using hrows.comp (measurable_pi_apply n) (measurable_pi_apply n)
  have hrowTransportMeas :
      Measurable (fun f : ℕ → ℝ ↦ fun k : ℕ ↦ F (f k)) := by
    -- Proof comment: measurability on function space is checked coordinatewise.
    refine measurable_pi_lambda _ fun k ↦ ?_
    exact hF_meas.comp (measurable_pi_apply k)
  have hLX_transport :
      IndepFun (L n) (fun ω ↦ fun k : ℕ ↦ F ((X n k ω : ℝ))) P := by
    -- Proof comment: transport the row variable through the same measurable coordinate map.
    exact hLX_row.comp measurable_id hrowTransportMeas
  have hLX_marks :
      IndepFun (L n) (fun ω ↦ fun k : ℕ ↦ unitIntervalBlockMarks X n (k + 1) ω) P := by
    -- Proof comment: finally rewrite the transported row back to the shifted tail used by
    -- `Theorem_5_35`.
    have hrowEq :
        (fun ω ↦ fun k : ℕ ↦ F ((X n k ω : ℝ))) =
          fun ω ↦ fun k : ℕ ↦ unitIntervalBlockMarks X n (k + 1) ω := by
      funext ω k
      exact congrFun (hshiftEq k) ω
    refine hLX_transport.congr (Filter.EventuallyEq.of_eq rfl) ?_
    exact Filter.EventuallyEq.of_eq hrowEq
  -- Proof comment: all inputs for the unit-interval theorem are now available blockwise.
  dsimp
  simpa using
    (poissonized_uniform_counting_process_is_poisson_process_on_unit_interval
      (P := P) (α := α) (L := L n) (X := unitIntervalBlockMarks X n)
      (hL := hL_law n) (hLX_indep := hLX_marks) (hX_iid := hmarks_iid) (hX1_law := hfirstLaw))

end

section

-- Route correction: normalize the global time parameter blockwise before attempting the
-- independence and Poisson-law assembly.

/-- Helper for Exercise 5.5.1: `blockLocalTime t n` is the local time seen by block `n` at the
global time `t`. Earlier blocks are already at `1`, the current block is clipped to
`lastBlockTime`, and later blocks are still at `0`. -/
private noncomputable def blockLocalTime (t : NNReal) (n : ℕ) : I :=
  if hlt : n < Nat.floor (t : ℝ) then
    1
  else if heq : n = Nat.floor (t : ℝ) then
    lastBlockTime t n heq
  else
    0

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: blocks strictly before `⌊t⌋` are fully activated. -/
private theorem blockLocalTime_of_lt {t : NNReal} {n : ℕ}
    (hn : n < Nat.floor (t : ℝ)) :
    blockLocalTime t n = 1 := by
  -- Proof comment: the first branch of the block-local normal form applies on earlier blocks.
  simp [blockLocalTime, hn]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: the last active block is evaluated at its clipped local time. -/
private theorem blockLocalTime_of_eq {t : NNReal} {n : ℕ}
    (hn : n = Nat.floor (t : ℝ)) :
    blockLocalTime t n = lastBlockTime t n hn := by
  -- Proof comment: at the floor index, the first branch is impossible and the second branch is
  -- exactly the clipped final-block time.
  subst hn
  simp [blockLocalTime]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: blocks strictly after `⌊t⌋` have not started yet. -/
private theorem blockLocalTime_of_gt {t : NNReal} {n : ℕ}
    (hn : Nat.floor (t : ℝ) < n) :
    blockLocalTime t n = 0 := by
  -- Proof comment: both the “earlier block” and “current block” branches are impossible once the
  -- block index lies strictly above the floor.
  have hnotlt : ¬n < Nat.floor (t : ℝ) := Nat.not_lt.mpr (Nat.le_of_lt hn)
  have hnoteq : ¬n = Nat.floor (t : ℝ) := by
    intro heq
    exact (ne_of_gt hn) heq
  simp [blockLocalTime, hnotlt, hnoteq]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: within a fixed block index, the clipped last-block time is
monotone in the global time as long as the floor index stays the same. -/
private theorem lastBlockTime_mono {s t : NNReal} {n : ℕ}
    (hs : n = Nat.floor (s : ℝ)) (ht : n = Nat.floor (t : ℝ)) (hst : s ≤ t) :
    lastBlockTime s n hs ≤ lastBlockTime t n ht := by
  -- Proof comment: once the block index is fixed, both local times are just the translated real
  -- coordinates `s - n` and `t - n`.
  change (s : ℝ) - n ≤ (t : ℝ) - n
  linarith

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: each block-local time is monotone in the global time. -/
private theorem blockLocalTime_mono {s t : NNReal} (hst : s ≤ t) (n : ℕ) :
    blockLocalTime s n ≤ blockLocalTime t n := by
  have hfloor : Nat.floor (s : ℝ) ≤ Nat.floor (t : ℝ) := Nat.floor_mono hst
  by_cases hs_lt : n < Nat.floor (s : ℝ)
  · -- Proof comment: blocks already completed by time `s` stay completed at time `t`.
    have ht_lt : n < Nat.floor (t : ℝ) := lt_of_lt_of_le hs_lt hfloor
    simpa [blockLocalTime_of_lt hs_lt, blockLocalTime_of_lt ht_lt]
  · by_cases hs_eq : n = Nat.floor (s : ℝ)
    · -- Proof comment: the `s`-block is either still the last block at time `t`, or it has
      -- become a fully completed earlier block.
      by_cases ht_lt : n < Nat.floor (t : ℝ)
      · rw [blockLocalTime_of_eq hs_eq, blockLocalTime_of_lt ht_lt]
        exact le_top
      · have ht_eq : n = Nat.floor (t : ℝ) := by
          exact le_antisymm (hs_eq ▸ hfloor) (Nat.le_of_not_gt ht_lt)
        simpa [blockLocalTime_of_eq hs_eq, blockLocalTime_of_eq ht_eq] using
          lastBlockTime_mono hs_eq ht_eq hst
    · have hs_gt : Nat.floor (s : ℝ) < n := by
        have hs_ge : Nat.floor (s : ℝ) ≤ n := Nat.le_of_not_gt hs_lt
        have hs_ne : Nat.floor (s : ℝ) ≠ n := by
          intro h
          exact hs_eq h.symm
        exact lt_of_le_of_ne hs_ge hs_ne
      by_cases ht_lt : n < Nat.floor (t : ℝ)
      · -- Proof comment: a block inactive at time `s` may become fully active by time `t`.
        simpa [blockLocalTime_of_gt hs_gt, blockLocalTime_of_lt ht_lt] using (bot_le : (0 : I) ≤ 1)
      · by_cases ht_eq : n = Nat.floor (t : ℝ)
        · -- Proof comment: or it may become the final active block of time `t`.
          simpa [blockLocalTime_of_gt hs_gt, blockLocalTime_of_eq ht_eq] using
            (bot_le : (0 : I) ≤ lastBlockTime t n ht_eq)
        · -- Proof comment: if the block is still beyond `⌊t⌋`, both local times are `0`.
          have ht_ge : Nat.floor (t : ℝ) ≤ n := Nat.le_of_not_gt ht_lt
          have ht_ne : Nat.floor (t : ℝ) ≠ n := by
            intro h
            exact ht_eq h.symm
          have ht_gt : Nat.floor (t : ℝ) < n := lt_of_le_of_ne ht_ge ht_ne
          simpa [blockLocalTime_of_gt hs_gt, blockLocalTime_of_gt ht_gt]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: the global counting process is the finite sum of the blockwise
unit-interval processes evaluated at the canonical block-local times. -/
private theorem poissonizedUniformBlockCountingProcess_eq_sum_blockLocalTime
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (t : NNReal) (ω : Ω) :
    poissonizedUniformBlockCountingProcess L X t ω =
      ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
          (blockLocalTime t n) ω := by
  rw [poissonizedUniformBlockCountingProcess]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn_le : n ≤ Nat.floor (t : ℝ) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  by_cases hlt : n < Nat.floor (t : ℝ)
  · -- Proof comment: earlier blocks contribute at local time `1`.
    rw [blockLocalTime_of_lt hlt]
    simp [hlt.ne]
  · -- Proof comment: within the active range, a non-earlier block must be the last active one.
    have heq : n = Nat.floor (t : ℝ) := le_antisymm hn_le (le_of_not_gt hlt)
    rw [blockLocalTime_of_eq heq]
    simp [heq]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: each global increment is the finite sum of the corresponding
block-local increments. -/
private theorem globalIncrement_eq_sumBlockContrib
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    {s t : NNReal} (hst : s ≤ t) (ω : Ω) :
    poissonizedUniformBlockCountingProcess L X t ω -
        poissonizedUniformBlockCountingProcess L X s ω =
      ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
            (blockLocalTime t n) ω -
          poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
            (blockLocalTime s n) ω) := by
  let B : ℕ → I → Ω → ℕ := fun n ↦
    poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
  have hfloor : Nat.floor (s : ℝ) ≤ Nat.floor (t : ℝ) := Nat.floor_mono hst
  have hs_extend :
      ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), B n (blockLocalTime s n) ω =
        ∑ n ∈ Finset.range (Nat.floor (s : ℝ) + 1), B n (blockLocalTime s n) ω := by
    -- Proof comment: beyond the active range of time `s`, the block-local time is `0`, so the
    -- extra terms vanish.
    symm
    refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hfloor)) ?_
    intro n hn hnot
    have hs_ge : Nat.floor (s : ℝ) + 1 ≤ n := Nat.not_lt.mp (by simpa using hnot)
    have hs_gt : Nat.floor (s : ℝ) < n := Nat.lt_of_succ_le hs_ge
    rw [blockLocalTime_of_gt hs_gt]
    simpa [B] using
      congrFun (poissonizedUniformCountingProcess_zero_eq (L := L n)
        (X := unitIntervalBlockMarks X n)) ω
  calc
    poissonizedUniformBlockCountingProcess L X t ω -
        poissonizedUniformBlockCountingProcess L X s ω =
      (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), B n (blockLocalTime t n) ω) -
        ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), B n (blockLocalTime s n) ω := by
          rw [poissonizedUniformBlockCountingProcess_eq_sum_blockLocalTime L X t ω,
            poissonizedUniformBlockCountingProcess_eq_sum_blockLocalTime L X s ω, hs_extend]
    _ =
        ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
          (B n (blockLocalTime t n) ω - B n (blockLocalTime s n) ω) := by
            -- Proof comment: after putting both sums on the same finite range, monotonicity of
            -- each block process allows termwise subtraction.
            symm
            refine Finset.sum_tsub_distrib (Finset.range (Nat.floor (t : ℝ) + 1)) ?_
            intro n hn
            exact
              (poissonizedUniformCountingProcess_mono (L := L n)
                (X := unitIntervalBlockMarks X n))
                (blockLocalTime_mono hst n) ω
    _ =
        ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
          (poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
              (blockLocalTime t n) ω -
            poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
              (blockLocalTime s n) ω) := by
            simp [B]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: if `t ≤ T`, then the global increment over `(s,t]` may be summed
over the fixed block range up to `⌊T⌋`, because every later block contributes zero. -/
private theorem globalIncrement_eq_sumBlockContrib_extend
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    {s t T : NNReal} (hst : s ≤ t) (htT : t ≤ T) (ω : Ω) :
    poissonizedUniformBlockCountingProcess L X t ω -
        poissonizedUniformBlockCountingProcess L X s ω =
      ∑ n ∈ Finset.range (Nat.floor (T : ℝ) + 1),
        (poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
            (blockLocalTime t n) ω -
          poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
            (blockLocalTime s n) ω) := by
  let B : ℕ → I → Ω → ℕ := fun n ↦
    poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
  have hfloor_tT : Nat.floor (t : ℝ) ≤ Nat.floor (T : ℝ) := Nat.floor_mono htT
  have hfloor_st : Nat.floor (s : ℝ) ≤ Nat.floor (t : ℝ) := Nat.floor_mono hst
  calc
    poissonizedUniformBlockCountingProcess L X t ω -
        poissonizedUniformBlockCountingProcess L X s ω =
      ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (B n (blockLocalTime t n) ω - B n (blockLocalTime s n) ω) := by
          simpa [B] using globalIncrement_eq_sumBlockContrib L X hst ω
    _ =
      ∑ n ∈ Finset.range (Nat.floor (T : ℝ) + 1),
        (B n (blockLocalTime t n) ω - B n (blockLocalTime s n) ω) := by
          refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hfloor_tT)) ?_
          intro n hn hnot
          have ht_ge : Nat.floor (t : ℝ) + 1 ≤ n := Nat.not_lt.mp (by simpa using hnot)
          have ht_gt : Nat.floor (t : ℝ) < n := Nat.lt_of_succ_le ht_ge
          have hs_gt : Nat.floor (s : ℝ) < n := lt_of_le_of_lt hfloor_st ht_gt
          rw [blockLocalTime_of_gt ht_gt, blockLocalTime_of_gt hs_gt]
          have hzero :
              B n 0 ω = 0 := by
            simpa [B] using
              congrFun
                (poissonizedUniformCountingProcess_zero_eq (L := L n)
                  (X := unitIntervalBlockMarks X n))
                ω
          simp [hzero]
    _ =
      ∑ n ∈ Finset.range (Nat.floor (T : ℝ) + 1),
        (poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
            (blockLocalTime t n) ω -
          poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
            (blockLocalTime s n) ω) := by
          simp [B]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.5.1: if a monotone time grid `u` stays below `T`, then every global
increment of the blockwise process rewrites to one fixed finite block sum over `⌊T⌋`. -/
private theorem globalIncrementFamily_eq_fixedBlockSums_of_boundedGrid
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (u : ℕ → NNReal) (hu : Monotone u) {T : NNReal} (hbound : ∀ i, u i ≤ T)
    (i : ℕ) (ω : Ω) :
    poissonizedUniformBlockCountingProcess L X (u (i + 1)) ω -
        poissonizedUniformBlockCountingProcess L X (u i) ω =
      ∑ n ∈ Finset.range (Nat.floor (T : ℝ) + 1),
        (poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
            (blockLocalTime (u (i + 1)) n) ω -
          poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
            (blockLocalTime (u i) n) ω) := by
  -- Proof comment: monotonicity gives the local increment interval `(u i, u (i + 1)]`, and the
  -- uniform bound on `u` lets us rewrite that increment over one common terminal block range.
  simpa using
    globalIncrement_eq_sumBlockContrib_extend
      L X (s := u i) (t := u (i + 1)) (T := T) (hu (Nat.le_succ i)) (hbound (i + 1)) ω

/-- Helper for Exercise 5.5.1: each fixed block increment at the canonical local times has the
expected Poisson law. -/
private theorem blockLocalIncrement_hasLawPoisson
    (P : Measure Ω) (α : NNReal) (L : ℕ → Ω → ℕ)
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (hLX_indep :
      IndepFun (fun ω ↦ fun n : ℕ ↦ L n ω)
        (fun ω ↦ fun p : ℕ × ℕ ↦ (X p.1 p.2 ω : ℝ)) P)
    (hX_indep : iIndepFun (fun p : ℕ × ℕ ↦ fun ω ↦ (X p.1 p.2 ω : ℝ)) P)
    (hL_law : ∀ n, HasLaw (L n) (poissonMeasure α) P)
    (hX_law : ∀ n k,
      HasLaw (fun ω ↦ (X n k ω : ℝ))
        (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) P)
    (n : ℕ) {s t : NNReal} (hst : s ≤ t) :
    let B := poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
    HasLaw
      (fun ω ↦ B (blockLocalTime t n) ω - B (blockLocalTime s n) ω)
      (poissonMeasure
        (α * Real.toNNReal (((blockLocalTime t n : I) : ℝ) - ((blockLocalTime s n : I) : ℝ))))
      P := by
  rcases blockCountingProcess_isPoissonOnUnitInterval P α L X hLX_indep hX_indep hL_law hX_law n with
    ⟨-, -, -, hB_law⟩
  -- Proof comment: this is exactly the fixed-block Poisson increment law, evaluated at the
  -- monotone pair of canonical local times.
  simpa using hB_law (blockLocalTime_mono hst n)

/-- Helper for Exercise 5.5.1: pairing two independent coordinate families coordinatewise keeps
the resulting family independent. -/
private theorem iIndepFun_pair_of_iIndepFun_of_indepFun
    (P : Measure Ω) [IsProbabilityMeasure P]
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (Y : ℕ → Ω → E) (Z : ℕ → Ω → F)
    (hY_iIndep : iIndepFun Y P) (hY_ae : ∀ n, AEMeasurable (Y n) P)
    (hZ_iIndep : iIndepFun Z P) (hZ_ae : ∀ n, AEMeasurable (Z n) P)
    (hYZ_indep : IndepFun (fun ω n ↦ Y n ω) (fun ω n ↦ Z n ω) P) :
    iIndepFun (fun n ω ↦ (Y n ω, Z n ω)) P := by
  -- Proof comment: reduce to finite restrictions, use the sequence-level independence to get a
  -- product law for the two restricted vectors, then identify vectorized pairs with paired
  -- vectors through `MeasurableEquiv.arrowProdEquivProdArrow`.
  rw [iIndepFun_iff_finset]
  intro s
  have hY_restrict' : iIndepFun (fun i : s ↦ Y i) P :=
    hY_iIndep.precomp Subtype.val_injective
  have hY_restrict : iIndepFun (s.restrict Y) P := by
    simpa [Finset.restrict] using hY_restrict'
  have hZ_restrict' : iIndepFun (fun i : s ↦ Z i) P :=
    hZ_iIndep.precomp Subtype.val_injective
  have hZ_restrict : iIndepFun (s.restrict Z) P := by
    simpa [Finset.restrict] using hZ_restrict'
  rw [iIndepFun_iff_map_fun_eq_pi_map]
  · change P.map (fun ω (i : s) ↦ (Y i ω, Z i ω)) =
      Measure.pi (fun i : s ↦ P.map (fun ω ↦ (Y i ω, Z i ω)))
    let φ : (ℕ → E) → (s → E) := fun f i ↦ f i
    let ψ : (ℕ → F) → (s → F) := fun f i ↦ f i
    have h_indep_restrict :
        IndepFun (fun ω (i : s) ↦ Y i ω) (fun ω (i : s) ↦ Z i ω) P := by
      have hφ : Measurable φ := by
        fun_prop
      have hψ : Measurable ψ := by
        fun_prop
      simpa [φ, ψ] using hYZ_indep.comp hφ hψ
    have h_map_eq :
        P.map (fun ω ↦ (fun i : s ↦ Y i ω, fun i : s ↦ Z i ω)) =
          (Measure.pi fun i : s ↦ P.map (Y i)).prod
            (Measure.pi fun i : s ↦ P.map (Z i)) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map
        (aemeasurable_pi_lambda _ fun i : s ↦ hY_ae i)
        (aemeasurable_pi_lambda _ fun i : s ↦ hZ_ae i)).mp h_indep_restrict,
        (iIndepFun_iff_map_fun_eq_pi_map fun i : s ↦ hY_ae i).mp hY_restrict,
        (iIndepFun_iff_map_fun_eq_pi_map fun i : s ↦ hZ_ae i).mp hZ_restrict]
    have h_pair_map_eq (i : s) :
        P.map (fun ω ↦ (Y i ω, Z i ω)) = (P.map (Y i)).prod (P.map (Z i)) := by
      have h_indep_i : Y i ⟂ᵢ[P] Z i := by
        simpa using hYZ_indep.comp (measurable_pi_apply (i : ℕ)) (measurable_pi_apply (i : ℕ))
      rw [(indepFun_iff_map_prod_eq_prod_map_map (hY_ae i) (hZ_ae i)).mp h_indep_i]
    let e := MeasurableEquiv.arrowProdEquivProdArrow E F s
    have h_pair_vec_aemeasurable :
        AEMeasurable (fun ω (i : s) ↦ (Y i ω, Z i ω)) P :=
      aemeasurable_pi_lambda _ fun i : s ↦ (hY_ae i).prodMk (hZ_ae i)
    rw [← e.map_measurableEquiv_injective.eq_iff]
    rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable h_pair_vec_aemeasurable]
    change P.map (fun ω ↦ (fun i : s ↦ Y i ω, fun i : s ↦ Z i ω)) =
      Measure.map e (Measure.pi fun i : s ↦ P.map (fun ω ↦ (Y i ω, Z i ω)))
    refine h_map_eq.trans ?_
    symm
    calc
      Measure.map e (Measure.pi fun i : s ↦ P.map (fun ω ↦ (Y i ω, Z i ω)))
          = Measure.map e (Measure.pi fun i : s ↦ (P.map (Y i)).prod (P.map (Z i))) := by
              simp [h_pair_map_eq]
      _ = (Measure.pi fun i : s ↦ P.map (Y i)).prod (Measure.pi fun i : s ↦ P.map (Z i)) :=
            (measurePreserving_arrowProdEquivProdArrow E F s
              (fun i : s ↦ P.map (Y i)) (fun i : s ↦ P.map (Z i))).map_eq
  · intro i
    simpa [Finset.restrict] using ((hY_ae i).prodMk (hZ_ae i) :
      AEMeasurable (fun ω ↦ (Y i ω, Z i ω)) P)

/-- Helper for Exercise 5.5.1: the full row data `(L n, X n ·)` are independent across block
indices. -/
private theorem lengthRowPair_iIndep
    (P : Measure Ω) [IsProbabilityMeasure P] (α : NNReal) (L : ℕ → Ω → ℕ)
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (hL_indep : iIndepFun L P)
    (hLX_indep :
      IndepFun (fun ω ↦ fun n : ℕ ↦ L n ω)
        (fun ω ↦ fun p : ℕ × ℕ ↦ (X p.1 p.2 ω : ℝ)) P)
    (hX_indep : iIndepFun (fun p : ℕ × ℕ ↦ fun ω ↦ (X p.1 p.2 ω : ℝ)) P)
    (hL_law : ∀ n, HasLaw (L n) (poissonMeasure α) P)
    (hX_law : ∀ n k,
      HasLaw (fun ω ↦ (X n k ω : ℝ))
        (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) P) :
    iIndepFun (fun n : ℕ ↦ fun ω ↦ (L n ω, fun k : ℕ ↦ (X n k ω : ℝ))) P := by
  have hrow_iIndep :
      iIndepFun (fun n : ℕ ↦ fun ω ↦ fun k : ℕ ↦ (X n k ω : ℝ)) P :=
    blockRowRealFamily_iIndep P X hX_indep hX_law
  have hrow_ae :
      ∀ n, AEMeasurable (fun ω ↦ fun k : ℕ ↦ (X n k ω : ℝ)) P := by
    intro n
    -- Proof comment: row measurability is checked coordinatewise from the given single-mark laws.
    exact aemeasurable_pi_lambda _ fun k ↦ (hX_law n k).aemeasurable
  have hL_ae : ∀ n, AEMeasurable (L n) P := fun n ↦ (hL_law n).aemeasurable
  have hseq_indep :
      IndepFun
        (fun ω ↦ fun n : ℕ ↦ L n ω)
        (fun ω ↦ fun n : ℕ ↦ fun k : ℕ ↦ (X n k ω : ℝ))
        P :=
    lengthSequence_indep_blockRowRealFamily P L X hLX_indep
  -- Proof comment: the generic pairing lemma now packages the independent lengths with the
  -- independent row families coordinatewise across the block index.
  exact iIndepFun_pair_of_iIndepFun_of_indepFun P L
    (fun n : ℕ ↦ fun ω ↦ fun k : ℕ ↦ (X n k ω : ℝ))
    hL_indep hL_ae hrow_iIndep hrow_ae hseq_indep

/-- Helper for Exercise 5.5.1: for fixed block index `n` and local time `t`, counting the first
`z.1` real marks below the translated threshold `n + t` is a measurable function of the row data
`z`. -/
private noncomputable def blockRowCountUpTo (n : ℕ) (t : I) :
    (ℕ × (ℕ → ℝ)) → ℕ :=
  fun z ↦
    Finset.sum (Finset.range z.1) fun k ↦ if z.2 k ≤ (n : ℝ) + (t : ℝ) then 1 else 0

/-- Helper for Exercise 5.5.1: the deterministic count of row marks below a fixed threshold is
measurable. -/
private theorem measurable_blockRowCountUpTo (n : ℕ) (t : I) :
    Measurable (blockRowCountUpTo n t) := by
  -- Proof comment: freeze the row length `z.1 = j`, prove measurability of the corresponding
  -- finite prefix count, and then take the countable union over all possible `j`.
  refine measurable_to_countable' ?_
  intro m
  have hprefix_meas :
      ∀ j : ℕ,
        Measurable
          (fun z : ℕ × (ℕ → ℝ) ↦
            Finset.sum (Finset.range j) fun k ↦
              if z.2 k ≤ (n : ℝ) + (t : ℝ) then 1 else 0) := by
    intro j
    refine Finset.measurable_sum (Finset.range j) ?_
    intro k hk
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_le ((measurable_pi_apply k).comp measurable_snd) measurable_const
  have hfiber :
      {z | blockRowCountUpTo n t z = m} =
        ⋃ j : ℕ,
          ({z | z.1 = j} ∩
            {z |
              (Finset.sum (Finset.range j) fun k ↦
                if z.2 k ≤ (n : ℝ) + (t : ℝ) then 1 else 0) = m}) := by
    ext z
    constructor
    · intro hz
      refine Set.mem_iUnion.2 ⟨z.1, ?_⟩
      constructor
      · simp
      · simpa [blockRowCountUpTo] using hz
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨j, hj⟩
      have hj' :
          z.1 = j ∧
            (Finset.sum (Finset.range j) fun k ↦
              if z.2 k ≤ (n : ℝ) + (t : ℝ) then 1 else 0) = m := by
        simpa using hj
      rcases hj' with ⟨hj₁, hj₂⟩
      simpa [blockRowCountUpTo, hj₁] using hj₂
  change MeasurableSet {z | blockRowCountUpTo n t z = m}
  rw [hfiber]
  refine MeasurableSet.iUnion ?_
  intro j
  refine (measurable_fst (measurableSet_singleton j)).inter ?_
  exact hprefix_meas j (measurableSet_singleton m)

/-- Helper for Exercise 5.5.1: from one row of deterministic data, extract the full sequence of
increments along the global time grid `u`, clipped to block `n`. -/
private noncomputable def blockIncrementRowMap (u : ℕ → NNReal) (n : ℕ) :
    (ℕ × (ℕ → ℝ)) → (ℕ → ℕ) :=
  fun z i ↦
    blockRowCountUpTo n (blockLocalTime (u (i + 1)) n) z -
      blockRowCountUpTo n (blockLocalTime (u i) n) z

/-- Helper for Exercise 5.5.1: the row-to-increment-sequence transport is measurable. -/
private theorem measurable_blockIncrementRowMap (u : ℕ → NNReal) (n : ℕ) :
    Measurable (blockIncrementRowMap u n) := by
  -- Proof comment: each coordinate is the difference of two measurable deterministic row counts,
  -- and the full sequence map is then measurable coordinatewise.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact (measurable_blockRowCountUpTo n (blockLocalTime (u (i + 1)) n)).sub
    (measurable_blockRowCountUpTo n (blockLocalTime (u i) n))

/-- Helper for Exercise 5.5.1: the deterministic row-count model agrees with the actual block
Poissonized counting process after translating row marks back to the unit interval. -/
private theorem blockRowCountUpTo_eq_process
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (n : ℕ) (t : I) (ω : Ω) :
    blockRowCountUpTo n t (L n ω, fun k : ℕ ↦ (X n k ω : ℝ)) =
      poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n) t ω := by
  -- Proof comment: rewrite the unit-interval process into the canonical `range` sum, then
  -- identify the translated unit-interval threshold with the original real threshold `n + t`.
  rw [poissonizedUniformCountingProcess_apply]
  rw [← Finset.Ico_succ_right_eq_Icc]
  change
    Finset.sum (Finset.range (L n ω)) (fun k ↦ if (X n k ω : ℝ) ≤ (n : ℝ) + (t : ℝ) then 1 else 0) =
      ∑ i ∈ Finset.Ico 1 (Nat.succ (L n ω)),
        if 0 < unitIntervalBlockMarks X n i ω ∧ unitIntervalBlockMarks X n i ω ≤ t then 1 else 0
  rw [Nat.succ_eq_add_one, Nat.add_comm]
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) ?_
  intro k hk
  have hpos : (0 : I) < blockMarkToUnitInterval (X n k ω) :=
    zero_lt_blockMarkToUnitInterval (X n k ω)
  have hcut :
      blockMarkToUnitInterval (X n k ω) ≤ t ↔ (X n k ω : ℝ) ≤ (n : ℝ) + (t : ℝ) :=
    blockMarkToUnitInterval_le_iff (X n k ω) t
  simp [unitIntervalBlockMarks, hpos, hcut]

/-- Helper for Exercise 5.5.1: the measurable row transport reproduces the actual block increment
sequence. -/
private theorem blockIncrementRowMap_comp_eq_actual
    (u : ℕ → NNReal) (L : ℕ → Ω → ℕ)
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (n : ℕ) :
    (fun ω ↦ blockIncrementRowMap u n (L n ω, fun k : ℕ ↦ (X n k ω : ℝ))) =
      fun ω i ↦
        poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
            (blockLocalTime (u (i + 1)) n) ω -
          poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
            (blockLocalTime (u i) n) ω := by
  -- Proof comment: both coordinates of the deterministic row increment map are the corresponding
  -- block counts, so rewrite them one by one using `blockRowCountUpTo_eq_process`.
  funext ω i
  simp [blockIncrementRowMap, blockRowCountUpTo_eq_process]

/-- Helper for Exercise 5.5.1: for a monotone global time grid, the full increment sequence in
each block row is a measurable image of the row data, hence the rows are independent. -/
private theorem blockIncrementRows_iIndep
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (hrowPair : iIndepFun (fun n : ℕ ↦ fun ω ↦ (L n ω, fun k : ℕ ↦ (X n k ω : ℝ))) P)
    (u : ℕ → NNReal) :
    iIndepFun
      (fun n : ℕ ↦
        fun ω ↦
          fun i : ℕ ↦
            poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
                (blockLocalTime (u (i + 1)) n) ω -
              poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
                (blockLocalTime (u i) n) ω)
      P := by
  have himage :
      iIndepFun
        (fun n : ℕ ↦ fun ω ↦ blockIncrementRowMap u n (L n ω, fun k : ℕ ↦ (X n k ω : ℝ)))
        P := by
    -- Proof comment: independence is preserved when each row datum is pushed through its own
    -- measurable increment-sequence extractor.
    simpa [Function.comp] using
      hrowPair.comp (fun n ↦ blockIncrementRowMap u n) (fun n ↦ measurable_blockIncrementRowMap u n)
  -- Proof comment: the measurable image agrees pointwise with the concrete block increment
  -- sequence appearing in the theorem statement.
  refine himage.congr ?_
  intro n
  exact Filter.EventuallyEq.of_eq (blockIncrementRowMap_comp_eq_actual u L X n)

/-- Helper for Exercise 5.5.1: summing the block-local times over the active range recovers the
global time `t`. -/
private theorem sum_blockLocalTimes (t : NNReal) :
    ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), ((blockLocalTime t n : I) : ℝ) = t := by
  -- Proof comment: split the active range into the fully active prefix `n < ⌊t⌋` and the final
  -- clipped block at `n = ⌊t⌋`.
  set m : ℕ := Nat.floor (t : ℝ)
  change (∑ n ∈ Finset.range (m + 1), ((blockLocalTime t n : I) : ℝ)) = t
  rw [Finset.sum_range_succ]
  calc
    Finset.sum (Finset.range m) (fun n ↦ ((blockLocalTime t n : I) : ℝ)) + ((blockLocalTime t m : I) : ℝ)
        = Finset.sum (Finset.range m) (fun _ ↦ (1 : ℝ)) + ((lastBlockTime t m (by simp [m]) : I) : ℝ) := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro n hn
              rw [blockLocalTime_of_lt (by simpa [m] using Finset.mem_range.mp hn)]
              simp
            · rw [blockLocalTime_of_eq (by simp [m])]
    _ = (m : ℝ) + ((lastBlockTime t m (by simp [m]) : I) : ℝ) := by
          simp
    _ = (m : ℝ) + ((t : ℝ) - m) := by
          simp [lastBlockTime]
    _ = t := by
          linarith

/-- Helper for Exercise 5.5.1: extending the block-local time sum from `⌊s⌋` to `⌊t⌋` adds only
zero terms when `s ≤ t`. -/
private theorem sum_blockLocalTimes_extend {s t : NNReal} (hst : s ≤ t) :
    ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), ((blockLocalTime s n : I) : ℝ) =
      ∑ n ∈ Finset.range (Nat.floor (s : ℝ) + 1), ((blockLocalTime s n : I) : ℝ) := by
  -- Proof comment: enlarging the range only adds blocks strictly beyond `⌊s⌋`, and those have
  -- local time `0`.
  have hfloor : Nat.floor (s : ℝ) ≤ Nat.floor (t : ℝ) := Nat.floor_mono hst
  symm
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hfloor)) ?_
  intro n hn hnot
  have hs_ge : Nat.floor (s : ℝ) + 1 ≤ n := Nat.not_lt.mp (by simpa using hnot)
  have hs_gt : Nat.floor (s : ℝ) < n := Nat.lt_of_succ_le hs_ge
  rw [blockLocalTime_of_gt hs_gt]
  simp

/-- Helper for Exercise 5.5.1: the total blockwise increment length is exactly the global interval
length `t - s`. -/
private theorem sum_blockLocalLengths {s t : NNReal} (hst : s ≤ t) :
    ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
      Real.toNNReal (((blockLocalTime t n : I) : ℝ) - ((blockLocalTime s n : I) : ℝ)) = t - s := by
  -- Proof comment: each clipped block increment is nonnegative, so the `toNNReal` coercions drop
  -- out after passing to real coefficients; the remaining real sum telescopes to `t - s`.
  have hnonneg :
      ∀ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        0 ≤ ((blockLocalTime t n : I) : ℝ) - ((blockLocalTime s n : I) : ℝ) := by
    intro n hn
    exact sub_nonneg.mpr (blockLocalTime_mono hst n)
  apply NNReal.coe_injective
  rw [NNReal.coe_sum]
  calc
    ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        ↑(Real.toNNReal (((blockLocalTime t n : I) : ℝ) - ((blockLocalTime s n : I) : ℝ)))
        =
      ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (((blockLocalTime t n : I) : ℝ) - ((blockLocalTime s n : I) : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          exact Real.coe_toNNReal _ (hnonneg n hn)
    _ =
      (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), ((blockLocalTime t n : I) : ℝ)) -
        ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), ((blockLocalTime s n : I) : ℝ) := by
          rw [Finset.sum_sub_distrib]
    _ = (t : ℝ) - s := by
          rw [sum_blockLocalTimes t, sum_blockLocalTimes_extend hst, sum_blockLocalTimes s]
    _ = ((t - s : NNReal) : ℝ) := by
          simp [NNReal.coe_sub hst]

/-- Helper for Exercise 5.5.1: after currying the independent row increment sequences back to the
pair index set `(n, i)`, the full block-increment family is independent. -/
private theorem blockIncrementPair_iIndep
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α : NNReal) (L : ℕ → Ω → ℕ)
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (hLX_indep :
      IndepFun (fun ω ↦ fun n : ℕ ↦ L n ω)
        (fun ω ↦ fun p : ℕ × ℕ ↦ (X p.1 p.2 ω : ℝ)) P)
    (hX_indep : iIndepFun (fun p : ℕ × ℕ ↦ fun ω ↦ (X p.1 p.2 ω : ℝ)) P)
    (hL_indep : iIndepFun L P)
    (hL_meas : ∀ n, Measurable (L n))
    (hX_meas : ∀ n k, Measurable (fun ω ↦ (X n k ω : ℝ)))
    (hL_law : ∀ n, HasLaw (L n) (poissonMeasure α) P)
    (hX_law : ∀ n k,
      HasLaw (fun ω ↦ (X n k ω : ℝ))
        (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) P)
    (u : ℕ → NNReal) (hu : Monotone u) :
    iIndepFun
      (fun p : ℕ × ℕ ↦
        fun ω ↦
          poissonizedUniformCountingProcess (L p.1) (unitIntervalBlockMarks X p.1)
              (blockLocalTime (u (p.2 + 1)) p.1) ω -
            poissonizedUniformCountingProcess (L p.1) (unitIntervalBlockMarks X p.1)
              (blockLocalTime (u p.2) p.1) ω)
      P := by
  -- Route correction: instead of hand-transporting the row-product law through
  -- `Measure.infinitePi_map_curry_symm`, use the existing deterministic row map together with
  -- mathlib's `iIndepFun_uncurry'`.
  let rowData : ℕ → Ω → ℕ × (ℕ → ℝ) :=
    fun n ω ↦ (L n ω, fun k : ℕ ↦ (X n k ω : ℝ))
  let rowIncrement : ℕ → ℕ → Ω → ℕ :=
    fun n i ω ↦ blockIncrementRowMap u n (rowData n ω) i
  have hrowPair :
      iIndepFun rowData P :=
    lengthRowPair_iIndep P α L X hL_indep hLX_indep hX_indep hL_law hX_law
  have hrowData_meas : ∀ n, Measurable (rowData n) := by
    intro n
    -- Proof comment: each row datum is the measurable pair of the row length and the full real
    -- row of marks.
    refine (hL_meas n).prodMk ?_
    exact measurable_pi_lambda _ fun k ↦ hX_meas n k
  have hrowImage :
      iIndepFun (fun n : ℕ ↦ fun ω ↦ fun i : ℕ ↦ rowIncrement n i ω) P := by
    -- Proof comment: apply the measurable row-to-increment extractor to each independent row.
    simpa [rowIncrement, rowData, Function.comp] using
      hrowPair.comp (fun n ↦ blockIncrementRowMap u n) (fun n ↦ measurable_blockIncrementRowMap u n)
  have hrowCoord_meas : ∀ n i, Measurable (rowIncrement n i) := by
    intro n i
    -- Proof comment: each coordinate is obtained by evaluating the measurable increment-sequence
    -- map after the measurable row-data embedding.
    exact (measurable_pi_apply i).comp ((measurable_blockIncrementRowMap u n).comp (hrowData_meas n))
  have hrowWithin : ∀ n, iIndepFun (rowIncrement n) P := by
    intro n
    let B := poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
    rcases blockCountingProcess_isPoissonOnUnitInterval
        P α L X hLX_indep hX_indep hL_law hX_law n with
      ⟨-, -, hB_indep, -⟩
    have hactual :
        iIndepFun
          (fun i : ℕ ↦
            fun ω ↦
              B (blockLocalTime (u (i + 1)) n) ω - B (blockLocalTime (u i) n) ω)
          P := by
      -- Proof comment: within one block, the unit-interval process has independent increments
      -- along the clipped local-time grid.
      simpa [B] using
        (hB_indep.nat
          (t := fun i : ℕ ↦ blockLocalTime (u i) n)
          (fun i j hij ↦ blockLocalTime_mono (hu hij) n))
    -- Proof comment: the deterministic row map was designed to reproduce exactly these actual
    -- block increments.
    have hEq := blockIncrementRowMap_comp_eq_actual u L X n
    refine hactual.congr ?_
    intro i
    exact Filter.EventuallyEq.of_eq <| by
      simpa [rowIncrement, rowData, B] using
        (congrArg (fun f : Ω → ℕ → ℕ ↦ fun ω ↦ f ω i) hEq).symm
  have huncurried :
      iIndepFun (fun p : ℕ × ℕ ↦ fun ω ↦ rowIncrement p.1 p.2 ω) P := by
    -- Proof comment: the row families are independent across `n`, each row is independent across
    -- `i`, and the coordinate maps are measurable, so uncurry to the pair index.
    exact iIndepFun_uncurry' (P := P) (X := rowIncrement) hrowCoord_meas hrowImage hrowWithin
  -- Proof comment: finally rewrite the measurable surrogate coordinates back to the concrete block
  -- increment formula from the statement.
  refine huncurried.congr ?_
  intro p
  have hEq := blockIncrementRowMap_comp_eq_actual u L X p.1
  exact Filter.EventuallyEq.of_eq <| by
    simpa [rowIncrement, rowData] using
      congrArg (fun f : Ω → ℕ → ℕ ↦ fun ω ↦ f ω p.2) hEq

/-- Helper for Exercise 5.5.1: each concrete pair-indexed block increment is measurable. -/
private theorem blockIncrementPair_measurable
    (L : ℕ → Ω → ℕ)
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (hL_meas : ∀ n, Measurable (L n))
    (hX_meas : ∀ n k, Measurable (fun ω ↦ (X n k ω : ℝ)))
    (u : ℕ → NNReal) :
    ∀ p : ℕ × ℕ,
      Measurable
        (fun ω ↦
          poissonizedUniformCountingProcess (L p.1) (unitIntervalBlockMarks X p.1)
              (blockLocalTime (u (p.2 + 1)) p.1) ω -
            poissonizedUniformCountingProcess (L p.1) (unitIntervalBlockMarks X p.1)
              (blockLocalTime (u p.2) p.1) ω) := by
  intro p
  have hrowData_meas :
      Measurable (fun ω ↦ (L p.1 ω, fun k : ℕ ↦ (X p.1 k ω : ℝ))) := by
    -- Proof comment: package one block row as the measurable pair of its Poisson length and its
    -- real-valued mark sequence.
    refine (hL_meas p.1).prodMk ?_
    exact measurable_pi_lambda _ fun k ↦ hX_meas p.1 k
  have hcoord_meas :
      Measurable
        (fun ω ↦ blockIncrementRowMap u p.1
          (L p.1 ω, fun k : ℕ ↦ (X p.1 k ω : ℝ)) p.2) := by
    -- Proof comment: the `p.2`-coordinate of the measurable row increment map is measurable.
    exact
      (measurable_pi_apply p.2).comp
        ((measurable_blockIncrementRowMap u p.1).comp hrowData_meas)
  have hcoord_eq :
      (fun ω ↦ blockIncrementRowMap u p.1
        (L p.1 ω, fun k : ℕ ↦ (X p.1 k ω : ℝ)) p.2) =
        (fun ω ↦
          poissonizedUniformCountingProcess (L p.1) (unitIntervalBlockMarks X p.1)
              (blockLocalTime (u (p.2 + 1)) p.1) ω -
            poissonizedUniformCountingProcess (L p.1) (unitIntervalBlockMarks X p.1)
              (blockLocalTime (u p.2) p.1) ω) := by
    -- Proof comment: `blockIncrementRowMap_comp_eq_actual` identifies the measurable surrogate
    -- coordinate with the concrete block increment at `(p.1, p.2)`.
    simpa using
      congrArg
        (fun f : Ω → ℕ → ℕ ↦ fun ω ↦ f ω p.2)
        (blockIncrementRowMap_comp_eq_actual u L X p.1)
  rw [← hcoord_eq]
  exact hcoord_meas

/-- Helper for Exercise 5.5.1: summing an independent pair-indexed family over a fixed finite
block range preserves independence in the increment index. -/
private theorem blockIncrementSums_iIndep_of_pairFamily
    (P : Measure Ω) (F : ℕ × ℕ → Ω → ℕ)
    (hF_indep : iIndepFun F P) (hF_meas : ∀ p, Measurable (F p))
    (N : ℕ) :
    iIndepFun (fun i ω ↦ ∑ n ∈ Finset.range N, F (n, i) ω) P := by
  let J : ℕ → Set (ℕ × ℕ) := fun i ↦ {p | p.1 < N ∧ p.2 = i}
  have h_disjoint : Pairwise fun i j ↦ Disjoint (J i) (J j) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    intro p hpI hpJ
    have hpi : p.1 < N ∧ p.2 = i := by
      simpa [J] using hpI
    have hpj : p.1 < N ∧ p.2 = j := by
      simpa [J] using hpJ
    exact hij (hpi.2.symm.trans hpj.2)
  have h_blocks :
      iIndepFun (fun i ω (j : J i) ↦ F j.1 ω) P :=
    iIndepFun_block_of_pairwise_disjoint_blocks P F J h_disjoint hF_indep hF_meas
  let blockSum := fun i (f : (j : J i) → ℕ) =>
    Finset.sum (Finset.attach (Finset.range N)) fun n ↦
      f ⟨(n.1, i), by simp [J, Finset.mem_range.mp n.2]⟩
  have h_blockSum_meas : ∀ i, Measurable (blockSum i) := by
    intro i
    -- Proof comment: the finite block sum is a sum of measurable coordinate evaluations.
    refine Finset.measurable_sum _ ?_
    intro n hn
    exact
      measurable_pi_apply
        ((⟨(n.1, i), by simp [J, Finset.mem_range.mp n.2]⟩ : J i))
  have h_sum_indep :
      iIndepFun (fun i ω ↦ blockSum i (fun j : J i ↦ F j.1 ω)) P :=
    h_blocks.comp blockSum h_blockSum_meas
  -- Proof comment: identify the subtype-indexed block sum with the ordinary `Finset.range N`
  -- sum appearing in the global increment formula.
  refine h_sum_indep.congr ?_
  intro i
  exact Filter.Eventually.of_forall fun ω ↦ by
    simpa [blockSum, J] using
      (Finset.sum_attach (s := Finset.range N) (f := fun n ↦ F (n, i) ω))

/-- Helper for Exercise 5.5.1: a finite sum of independent Poisson variables is Poisson with the
sum of the rates. -/
private theorem hasLaw_finset_sum_poisson_of_iIndepFun
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rates : ℕ → NNReal) (Y : ℕ → Ω → ℕ)
    (hY_indep : iIndepFun Y P)
    (hY_law : ∀ n, HasLaw (Y n) (poissonMeasure (rates n)) P) :
    ∀ N : ℕ,
      HasLaw (∑ n ∈ Finset.range N, Y n)
        (poissonMeasure (∑ n ∈ Finset.range N, rates n)) P
  | 0 => by
      -- Proof comment: the empty sum is identically zero, whose law is `poissonMeasure 0`.
      simpa using (hasLawZeroPoissonMeasureZero (μ := P) (Ω := Ω))
  | N + 1 => by
      have hsum :
          HasLaw (∑ n ∈ Finset.range N, Y n)
            (poissonMeasure (∑ n ∈ Finset.range N, rates n)) P :=
        hasLaw_finset_sum_poisson_of_iIndepFun P rates Y hY_indep hY_law N
      have hindep :
          IndepFun (∑ n ∈ Finset.range N, Y n) (Y N) P :=
        hY_indep.indepFun_sum_range_succ₀ (fun n ↦ (hY_law n).aemeasurable) N
      have hstep :
          HasLaw ((∑ n ∈ Finset.range N, Y n) + Y N)
            (poissonMeasure ((∑ n ∈ Finset.range N, rates n) + rates N))
            P := by
        -- Proof comment: append the last independent Poisson variable and convolve the rates.
        simpa [poissonMeasure_conv_poissonMeasure] using
          hindep.hasLaw_add hsum (hY_law N)
      -- Proof comment: rewrite the successor-range sum on both the random-variable side and the
      -- rate side.
      simpa [Finset.sum_range_succ] using hstep

end

-- Proof sketch: for each `n`, apply the unit-interval result to the counting process built from
-- the Poisson number `L n` of i.i.d. marks in `(n, n + 1]`, after translating that block to
-- `(0,1]`. The processes coming from different blocks are independent and their time-shifted
-- superposition has Poisson increments with parameter `α (t - s)`, hence defines a Poisson
-- process of intensity `α`.
/-- Exercise 5.5.1: if `L₁, L₂, …` are independent Poisson random variables with parameter `α`,
the families `X₁¹, X₂¹, …`, `X₁², X₂², …`, … are independent and each `X_k^(n+1)` is uniformly
distributed on `(n, n + 1]`, then the counting process is a Poisson process with intensity `α`.
In the faithful Lean version, exact block membership is encoded by taking
`X n k : Ω → Set.Ioc (n : ℝ) (n + 1)`, while the uniform law is stated for the coerced real-valued
random variables `ω ↦ (X n k ω : ℝ)`. This is the canonical 0-based reindexing of the textbook
statement, where `L n` encodes `L_(n+1)` and `X n k` encodes `X_(k+1)^(n+1)`. -/
theorem poissonizedUniformBlockCountingProcess_isPoissonProcess
    (P : Measure Ω) (α : NNReal) (L : ℕ → Ω → ℕ)
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (hL_indep : iIndepFun L P)
    (hLX_indep :
      IndepFun (fun ω ↦ fun n : ℕ ↦ L n ω)
        (fun ω ↦ fun p : ℕ × ℕ ↦ (X p.1 p.2 ω : ℝ)) P)
    (hX_indep : iIndepFun (fun p : ℕ × ℕ ↦ fun ω ↦ (X p.1 p.2 ω : ℝ)) P)
    (hL_meas : ∀ n, Measurable (L n))
    (hX_meas : ∀ n k, Measurable (fun ω ↦ (X n k ω : ℝ)))
    (hL_law : ∀ n, HasLaw (L n) (poissonMeasure α) P)
    (hX_law : ∀ n k,
      HasLaw (fun ω ↦ (X n k ω : ℝ))
        (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) P) :
    IsPoissonProcess α P (poissonizedUniformBlockCountingProcess L X) := by
  letI : IsProbabilityMeasure P := (hL_law 0).isProbabilityMeasure
  -- Proof comment: the pathwise counting formula, zero-time value, and monotonicity are now
  -- reduced to finite block sums. The remaining step is the distributional assembly of blockwise
  -- increments into global independent Poisson increments.
  refine isPoissonProcess_of_textbook
    (hstochastic := ?_)
    (hzero := poissonizedUniformBlockCountingProcess_zero_eq L X)
    (hmono := poissonizedUniformBlockCountingProcess_mono L X)
    (hindep := ?_)
    (hpoisson := ?_)
  · intro t
    -- Proof comment: the outer block sum is finite for fixed `t`. For each block, rewrite the
    -- random finite sum by conditioning on the value of `L n`; the resulting singleton fibers are
    -- countable unions of measurable intersections.
    change Measurable (fun ω ↦ poissonizedUniformBlockCountingProcess L X t ω)
    have hEq :
        (fun ω ↦ poissonizedUniformBlockCountingProcess L X t ω) =
          fun ω ↦
            ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
              ∑ k ∈ Finset.range (L n ω), if (X n k ω : ℝ) ≤ (t : ℝ) then 1 else 0 := by
      funext ω
      exact poissonizedUniformBlockCountingProcess_apply L X t ω
    rw [hEq]
    refine Finset.measurable_sum (Finset.range (Nat.floor (t : ℝ) + 1)) ?_
    intro n hn
    have hprefix_meas :
        ∀ j : ℕ,
          Measurable
            (fun ω ↦
              ∑ k ∈ Finset.range j, if (X n k ω : ℝ) ≤ (t : ℝ) then 1 else 0) := by
      intro j
      refine Finset.measurable_sum (Finset.range j) ?_
      intro k hk
      have hset : MeasurableSet {ω | (X n k ω : ℝ) ≤ (t : ℝ)} := by
        simpa [Set.preimage] using (hX_meas n k) measurableSet_Iic
      exact Measurable.ite hset measurable_const measurable_const
    refine measurable_to_countable' ?_
    intro m
    change MeasurableSet
      {ω |
        (∑ k ∈ Finset.range (L n ω),
          if (X n k ω : ℝ) ≤ (t : ℝ) then 1 else 0) = m}
    have hfiber :
        {ω |
            (∑ k ∈ Finset.range (L n ω),
              if (X n k ω : ℝ) ≤ (t : ℝ) then 1 else 0) = m} =
          ⋃ j : ℕ,
            ({ω | L n ω = j} ∩
              {ω |
                (∑ k ∈ Finset.range j,
                  if (X n k ω : ℝ) ≤ (t : ℝ) then 1 else 0) = m}) := by
      ext ω
      constructor
      · intro hω
        refine Set.mem_iUnion.2 ⟨L n ω, ?_⟩
        exact (Set.mem_inter_iff ω _ _).2 ⟨by simp, by simpa using hω⟩
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨j, hj⟩
        rcases (Set.mem_inter_iff ω _ _).1 hj with ⟨hLj, hjm⟩
        simpa [hLj.symm] using hjm
    rw [hfiber]
    refine MeasurableSet.iUnion ?_
    intro j
    refine ((hL_meas n) (measurableSet_singleton j)).inter ?_
    exact (hprefix_meas j) (measurableSet_singleton m)
  · refine HasIndepIncrements.of_nat ?_
    intro u hu huconst
    obtain ⟨T, huT⟩ := huconst.eventuallyEq_const
    rcases Filter.mem_atTop_sets.mp huT with ⟨N0, hN0⟩
    let F : ℕ × ℕ → Ω → ℕ := fun p ω ↦
      poissonizedUniformCountingProcess (L p.1) (unitIntervalBlockMarks X p.1)
          (blockLocalTime (u (p.2 + 1)) p.1) ω -
        poissonizedUniformCountingProcess (L p.1) (unitIntervalBlockMarks X p.1)
          (blockLocalTime (u p.2) p.1) ω
    have hbound : ∀ i, u i ≤ T := by
      intro i
      -- Proof comment: compare `u i` with the stabilized tail value `u (max i N0) = T`.
      have hi_le : u i ≤ u (max i N0) := hu (le_max_left i N0)
      have htail : u (max i N0) = T := hN0 (max i N0) (le_max_right i N0)
      simpa [htail] using hi_le
    have hpair : iIndepFun F P := by
      -- Proof comment: the pair-indexed block increment family is already independent blockwise.
      simpa [F] using
        blockIncrementPair_iIndep
          P α L X hLX_indep hX_indep hL_indep hL_meas hX_meas hL_law hX_law u hu
    have hF_meas : ∀ p, Measurable (F p) := by
      intro p
      -- Proof comment: coordinate measurability comes from the deterministic row transport.
      simpa [F] using blockIncrementPair_measurable L X hL_meas hX_meas u p
    have hsum_indep :
        iIndepFun
          (fun i ω ↦ ∑ n ∈ Finset.range (Nat.floor (T : ℝ) + 1), F (n, i) ω)
          P :=
      blockIncrementSums_iIndep_of_pairFamily
        P F hpair hF_meas (Nat.floor (T : ℝ) + 1)
    -- Proof comment: every global increment now has the fixed finite-range normal form required
    -- by the finite-sum independence wrapper.
    refine hsum_indep.congr ?_
    intro i
    refine Filter.EventuallyEq.of_eq ?_
    funext ω
    symm
    simpa [F] using
      globalIncrementFamily_eq_fixedBlockSums_of_boundedGrid
        L X u hu hbound i ω
  · intro s t hst
    let u : ℕ → NNReal
      | 0 => s
      | _ + 1 => t
    have hu : Monotone u := by
      intro i j hij
      cases i with
      | zero =>
          cases j with
          | zero => simp [u]
          | succ j =>
              simpa [u] using hst.le
      | succ i =>
          cases j with
          | zero =>
              cases (Nat.not_succ_le_zero _ hij)
          | succ j =>
              simp [u]
    let F : ℕ → Ω → ℕ := fun n ω ↦
      poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
          (blockLocalTime t n) ω -
        poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
          (blockLocalTime s n) ω
    let rates : ℕ → NNReal := fun n ↦
      α * Real.toNNReal (((blockLocalTime t n : I) : ℝ) - ((blockLocalTime s n : I) : ℝ))
    have hpair :
        iIndepFun
          (fun p : ℕ × ℕ ↦
            fun ω ↦
              poissonizedUniformCountingProcess (L p.1) (unitIntervalBlockMarks X p.1)
                  (blockLocalTime (u (p.2 + 1)) p.1) ω -
                poissonizedUniformCountingProcess (L p.1) (unitIntervalBlockMarks X p.1)
                  (blockLocalTime (u p.2) p.1) ω)
          P :=
      blockIncrementPair_iIndep
        P α L X hLX_indep hX_indep hL_indep hL_meas hX_meas hL_law hX_law u hu
    have hblock_indep : iIndepFun F P := by
      -- Proof comment: specialize the pair-indexed block-increment family to the single
      -- increment coordinate `i = 0`, which corresponds to the interval `(s, t]`.
      let g : ℕ → ℕ × ℕ := fun n ↦ (n, 0)
      have hg_inj : Function.Injective g := by
        intro a b hab
        exact (Prod.mk.inj hab).1
      simpa [F, rates, u, g] using hpair.precomp hg_inj
    have hblock_law : ∀ n, HasLaw (F n) (poissonMeasure (rates n)) P := by
      intro n
      -- Proof comment: each block contributes a Poisson increment with parameter equal to its
      -- clipped local-time length.
      simpa [F, rates] using
        blockLocalIncrement_hasLawPoisson
          P α L X hLX_indep hX_indep hL_law hX_law n hst.le
    have hsum_law :
        HasLaw (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), F n)
          (poissonMeasure
            (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), rates n))
          P :=
      hasLaw_finset_sum_poisson_of_iIndepFun
        P rates F hblock_indep hblock_law (Nat.floor (t : ℝ) + 1)
    have hsum_eq :
        (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), F n) =
          fun ω ↦
            poissonizedUniformBlockCountingProcess L X t ω -
              poissonizedUniformBlockCountingProcess L X s ω := by
      funext ω
      symm
      simpa [F] using globalIncrement_eq_sumBlockContrib L X hst.le ω
    have hrate :
        (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), rates n) = α * (t - s) := by
      calc
        ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1), rates n
            =
          ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
            Real.toNNReal (((blockLocalTime t n : I) : ℝ) - ((blockLocalTime s n : I) : ℝ)) * α := by
              simp_rw [rates, mul_comm α]
        _ =
          (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
            Real.toNNReal (((blockLocalTime t n : I) : ℝ) - ((blockLocalTime s n : I) : ℝ))) * α := by
              rw [Finset.sum_mul]
        _ = α * (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
            Real.toNNReal (((blockLocalTime t n : I) : ℝ) - ((blockLocalTime s n : I) : ℝ))) := by
              rw [mul_comm]
        _ = α * (t - s) := by
              rw [sum_blockLocalLengths hst.le]
    -- Proof comment: rewrite the finite block sum back to the global increment and compress the
    -- total rate with the clipped-length identity.
    simpa [hrate] using hsum_law.congr (Filter.EventuallyEq.of_eq hsum_eq.symm)
