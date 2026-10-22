/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_31
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

-- Proof sketch: since `α ∈ [0, 1)` and `θ > -α`, the quantity `θ + (n + 1) * α` is bounded below
-- by `θ + α`, which is positive; this is the positivity needed for the second Beta parameter.
/-- The second Beta shape parameter in the GEM construction is positive in every coordinate. -/
private theorem gemBetaSecondShape_pos (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hθα : -α < θ) (n : ℕ) :
    0 < θ + ((n : ℝ) + 1) * α := by
  have hn : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  linarith [mul_nonneg hn hα_nonneg]

/-- The `n`th independent Beta coordinate used in the GEM stick-breaking construction. -/
private noncomputable def gemBetaCoordinateLaw (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1)
    (hθα : -α < θ) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨betaMeasure (1 - α) (θ + ((n : ℝ) + 1) * α),
    isProbabilityMeasureBeta (sub_pos.mpr hα_lt_one)
      (gemBetaSecondShape_pos α θ hα_nonneg hθα n)⟩

/-- The stick-breaking map associated with the infinite Beta coordinate sequence in the GEM
construction. -/
private def gemStickBreaking (v : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦ (Finset.range k).prod (fun i ↦ 1 - v i) * v k

/-- The infinite product law of the independent Beta coordinates appearing in the GEM
stick-breaking construction. -/
private noncomputable def gemBetaProductLaw (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1)
    (hθα : -α < θ) : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨Measure.infinitePi fun n ↦ (gemBetaCoordinateLaw α θ hα_nonneg hα_lt_one hθα n : Measure ℝ),
    inferInstance⟩

-- Proof sketch: measurability into the product space reduces to measurability of each coordinate;
-- each coordinate is a finite product of measurable coordinate projections and measurable algebraic
-- operations.
/-- Helper for Definition 24.34: the local GEM stick-breaking map is measurable. -/
private theorem measurable_gemStickBreakingDistribution :
    Measurable (gemStickBreaking : (ℕ → ℝ) → ℕ → ℝ) := by
  refine measurable_pi_lambda _ fun k ↦ ?_
  simp [gemStickBreaking]
  measurability

/-- The mass partition with a single block of mass `1`. -/
def singletonMassPartition : MassPartition :=
  ⟨fun n ↦ if n = 0 then 1 else 0, by
    constructor
    · intro i j hij
      by_cases hi : i = 0
      · subst hi
        by_cases hj : j = 0
        · simp [hj]
        · simp [hj]
      · have hj : j ≠ 0 := by
          intro hj
          apply hi
          exact Nat.eq_zero_of_le_zero (hj ▸ hij)
        simp [hi, hj]
    constructor
    · exact (hasSum_ite_eq 0 (1 : NNReal)).summable
    · exact (hasSum_ite_eq 0 (1 : NNReal)).tsum_eq⟩

/-- A mass partition `x` is a ranked rearrangement of `z` when its coordinates are obtained from
`z` by a permutation of `ℕ`. -/
def IsRankedRearrangement (x : MassPartition) (z : ℕ → ℝ) : Prop :=
  ∃ e : Equiv.Perm ℕ, (fun n ↦ (x n : ℝ)) = z ∘ e

/-- Helper for Definition 24.34: two decreasing mass partitions that are both permutations of the
same sequence satisfy the coordinatewise order forced by the decreasing arrangement. -/
private theorem coordLe_of_permWitness {x y : MassPartition} {z : ℕ → ℝ}
    (ex ey : Equiv.Perm ℕ) (hex : (fun n ↦ (x n : ℝ)) = z ∘ ex)
    (hey : (fun n ↦ (y n : ℝ)) = z ∘ ey) (n : ℕ) :
    x n ≤ y n := by
  -- Proof comment: if `x n` were larger than `y n`, then the first `n + 1` coordinates of `x`
  -- would all exceed `y n`; transporting them through the permutation witness would produce an
  -- injection `Fin (n + 1) ↪ Fin n`, which is impossible.
  by_contra hxy
  have hxy' : y n < x n := lt_of_not_ge hxy
  let f : Fin (n + 1) → Fin n := fun i ↦
    ⟨ey.symm (ex i), by
      have hi_le : i.1 ≤ n := Nat.le_of_lt_succ i.2
      have hxn_le_xi : x n ≤ x i := x.2.1 hi_le
      have hy_lt_xi : y n < x i := lt_of_lt_of_le hxy' hxn_le_xi
      have hperm : x i = y (ey.symm (ex i)) := by
        apply NNReal.coe_injective
        calc
          ((x i : NNReal) : ℝ) = z (ex i) := by
            simpa [Function.comp] using congrFun hex i
          _ = ((y (ey.symm (ex i)) : NNReal) : ℝ) := by
            symm
            simpa [Function.comp] using congrFun hey (ey.symm (ex i))
      have hy_lt_perm : y n < y (ey.symm (ex i)) := by
        simpa [hperm] using hy_lt_xi
      by_contra hnot
      have h_ge : n ≤ ey.symm (ex i) := Nat.not_lt.mp hnot
      have hperm_le : y (ey.symm (ex i)) ≤ y n := y.2.1 h_ge
      exact (not_le_of_gt hy_lt_perm) hperm_le⟩
  have hf_injective : Function.Injective f := by
    intro i j hij
    have hval : ey.symm (ex i) = ey.symm (ex j) := by
      simpa [f] using congrArg Fin.val hij
    have hex_eq : ex i = ex j := ey.symm.injective hval
    apply Fin.ext
    exact ex.injective hex_eq
  have hcard : n + 1 ≤ n := by
    simpa using Fintype.card_le_of_injective f hf_injective
  exact Nat.not_succ_le_self n hcard

/-- Helper for Definition 24.34: two decreasing mass partitions that are both permutations of the
same sequence satisfy the coordinatewise order forced by the decreasing arrangement. -/
private theorem coord_le_of_isRankedRearrangement {x y : MassPartition} {z : ℕ → ℝ}
    (hx : IsRankedRearrangement x z) (hy : IsRankedRearrangement y z) (n : ℕ) :
    x n ≤ y n := by
  rcases hx with ⟨ex, hex⟩
  rcases hy with ⟨ey, hey⟩
  -- Proof comment: repackage the Prop-level witnesses into the computational witness lemma.
  exact coordLe_of_permWitness ex ey hex hey n

/-- Helper for Definition 24.34: two decreasing mass partitions that are both permutations of the
same sequence must coincide coordinatewise. -/
private theorem eq_of_isRankedRearrangement {x y : MassPartition} {z : ℕ → ℝ}
    (hx : IsRankedRearrangement x z) (hy : IsRankedRearrangement y z) :
    x = y := by
  -- Proof comment: apply the one-sided coordinate inequality twice and use antisymmetry.
  apply Subtype.ext
  funext n
  exact le_antisymm
    (coord_le_of_isRankedRearrangement hx hy n)
    (coord_le_of_isRankedRearrangement hy hx n)

/-- Any sequence that admits a ranked rearrangement has a unique such rearrangement. -/
private theorem existsUnique_rankedRearrangement (z : ℕ → ℝ)
    (hz : ∃ x : MassPartition, IsRankedRearrangement x z) :
    ∃! x : MassPartition, IsRankedRearrangement x z := by
  rcases hz with ⟨x, hx⟩
  -- Proof comment: existence is part of the hypothesis, and uniqueness follows from the rigidity
  -- of decreasing permutations proved above.
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact (eq_of_isRankedRearrangement hx hy).symm

/-- The canonical ranked rearrangement of a sequence, as a mass partition when one exists;
otherwise the singleton mass partition. -/
noncomputable def rankedRearrangement (z : ℕ → ℝ) : MassPartition :=
  if hz : ∃ x : MassPartition, IsRankedRearrangement x z then
    (existsUnique_rankedRearrangement z hz).choose
  else
    singletonMassPartition

/-- If a sequence admits a ranked rearrangement, then `rankedRearrangement` returns it. -/
theorem isRankedRearrangement_rankedRearrangement {z : ℕ → ℝ}
    (hz : ∃ x : MassPartition, IsRankedRearrangement x z) :
    IsRankedRearrangement (rankedRearrangement z) z := by
  rw [rankedRearrangement, dif_pos hz]
  exact (existsUnique_rankedRearrangement z hz).choose_spec.1

/-- A ranked rearrangement is uniquely determined by the source sequence. -/
theorem rankedRearrangement_eq_of_isRankedRearrangement {x : MassPartition} {z : ℕ → ℝ}
    (hx : IsRankedRearrangement x z) :
    rankedRearrangement z = x := by
  let hz : ∃ y : MassPartition, IsRankedRearrangement y z := ⟨x, hx⟩
  rw [rankedRearrangement, dif_pos hz]
  exact (ExistsUnique.choose_eq_iff (existsUnique_rankedRearrangement z hz)).2 hx

/-- Helper for Definition 24.34: a finite subset of cardinality `n + 1` is nonempty. -/
private theorem finiteSubset_nonempty_of_card_succ {s : Finset ℕ} {n : ℕ}
    (hs : s.card = n + 1) : s.Nonempty := by
  refine Finset.card_ne_zero.mp ?_
  rw [hs]
  exact Nat.succ_ne_zero n

/-- The finite-subset minimum of the nonnegative coordinates of `z`, viewed in `ℝ≥0∞`. -/
private def finiteSubsetInfMass (s : Finset ℕ) (hs : s.Nonempty) (z : ℕ → ℝ) : ℝ≥0∞ :=
  s.inf' hs (fun i ↦ ENNReal.ofReal (z i))

/-- Helper for Definition 24.34: the finite-subset minimum model is measurable for each fixed
finite subset. -/
private theorem measurable_finiteSubsetInfMass (s : Finset ℕ) (hs : s.Nonempty) :
    Measurable (finiteSubsetInfMass s hs) := by
  classical
  -- Proof comment: the finite infimum is built by repeatedly taking the infimum of measurable
  -- coordinate projections.
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      simpa [finiteSubsetInfMass] using (measurable_pi_apply a).ennreal_ofReal
  | cons a s ha hs ih =>
      have hcons :
          finiteSubsetInfMass (Finset.cons a s ha) (Finset.cons_nonempty ha) =
            fun z : ℕ → ℝ ↦ ENNReal.ofReal (z a) ⊓ finiteSubsetInfMass s hs z := by
        funext z
        simpa [finiteSubsetInfMass] using
          (Finset.inf'_cons (s := s) (H := hs) (f := fun i ↦ ENNReal.ofReal (z i))
            (b := a) (hb := ha))
      rw [hcons]
      exact ((measurable_pi_apply a).ennreal_ofReal).inf' ih

/-- Helper for Definition 24.34: the `n`th global order statistic of `z`, computed as the supremum
of the minima over all finite subsets of size `n + 1`. -/
private def nthLargestMass (z : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ s : {s : Finset ℕ // s.card = n + 1},
    finiteSubsetInfMass s.1 (finiteSubset_nonempty_of_card_succ s.2) z

/-- Helper for Definition 24.34: each global order-statistic coordinate is measurable. -/
private theorem measurable_nthLargestMass (n : ℕ) :
    Measurable fun z : ℕ → ℝ ↦ nthLargestMass z n := by
  classical
  -- Proof comment: this is a countable supremum of measurable finite-subset minima.
  unfold nthLargestMass
  refine Measurable.iSup fun s ↦ ?_
  exact measurable_finiteSubsetInfMass s.1 (finiteSubset_nonempty_of_card_succ s.2)

/-- Helper for Definition 24.34: the global order-statistic formula recovers the coordinates of any
ranked rearrangement. -/
private theorem nthLargestMass_eq_of_permWitness {x : MassPartition} {z : ℕ → ℝ}
    (e : Equiv.Perm ℕ) (he : (fun n ↦ (x n : ℝ)) = z ∘ e) (n : ℕ) :
    nthLargestMass z n = x n := by
  classical
  apply le_antisymm
  · -- Proof comment: every subset of size `n + 1` contains an index whose rank is at least `n`,
    -- so its minimum cannot exceed the `n`th ranked coordinate.
    refine iSup_le fun s ↦ ?_
    have hsne : s.1.Nonempty := finiteSubset_nonempty_of_card_succ s.2
    have hlarge :
        ∃ j ∈ s.1, n ≤ e.symm j := by
      by_contra hlarge
      have hlt : ∀ j ∈ s.1, e.symm j < n := by
        intro j hj
        exact lt_of_not_ge fun hge ↦ hlarge ⟨j, hj, hge⟩
      have himage : s.1.image e.symm ⊆ Finset.range n := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
        exact Finset.mem_range.mpr (hlt j hj)
      have hcard_le : s.1.card ≤ n := by
        calc
          s.1.card = (s.1.image e.symm).card := by
            symm
            exact Finset.card_image_of_injective s.1 e.symm.injective
          _ ≤ (Finset.range n).card := Finset.card_le_card himage
          _ = n := by simp
      have : n + 1 ≤ n := by
        have hcard_le' := hcard_le
        simp [s.2] at hcard_le'
      exact Nat.not_succ_le_self n this
    rcases hlarge with ⟨j, hj, hnj⟩
    have hzj : ENNReal.ofReal (z j) = x (e.symm j) := by
      simpa using (congrArg ENNReal.ofReal (congrFun he (e.symm j))).symm
    calc
      finiteSubsetInfMass s.1 hsne z ≤ ENNReal.ofReal (z j) := by
        unfold finiteSubsetInfMass
        exact Finset.inf'_le _ hj
      _ = x (e.symm j) := hzj
      _ ≤ x n := by
        exact_mod_cast x.2.1 hnj
  · -- Proof comment: the first `n + 1` coordinates of the ranked partition give one admissible
    -- subset whose minimum is exactly the `n`th coordinate.
    let s : Finset ℕ := (Finset.range (n + 1)).image e
    have hsne : s.Nonempty := by
      refine Finset.card_ne_zero.mp ?_
      rw [Finset.card_image_of_injective _ e.injective, Finset.card_range]
      exact Nat.succ_ne_zero n
    have hcard : s.card = n + 1 := by
      rw [Finset.card_image_of_injective _ e.injective, Finset.card_range]
    have hle : (x n : ℝ≥0∞) ≤ finiteSubsetInfMass s hsne z := by
      unfold finiteSubsetInfMass
      refine Finset.le_inf' (s := s) (H := hsne) (f := fun i ↦ ENNReal.ofReal (z i)) ?_
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
      have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      calc
        (x n : ℝ≥0∞) ≤ x k := by
          exact_mod_cast x.2.1 hk_le
        _ = ENNReal.ofReal (z (e k)) := by
          simpa using congrArg ENNReal.ofReal (congrFun he k)
    exact le_iSup_of_le ⟨s, hcard⟩ hle

/-- Helper for Definition 24.34: the global order-statistic formula recovers the coordinates of any
ranked rearrangement. -/
private theorem nthLargestMass_eq_of_isRankedRearrangement {x : MassPartition} {z : ℕ → ℝ}
    (hx : IsRankedRearrangement x z) (n : ℕ) :
    nthLargestMass z n = x n := by
  rcases hx with ⟨e, he⟩
  -- Proof comment: switch from the existential witness to the explicit permutation lemma.
  exact nthLargestMass_eq_of_permWitness e he n

/-- Helper for Definition 24.34: whenever a ranked rearrangement exists, the canonical one has
coordinates given by the global order-statistic model. -/
private theorem rankedRearrangement_eq_nthLargestMass {z : ℕ → ℝ}
    (hz : ∃ x : MassPartition, IsRankedRearrangement x z) (n : ℕ) :
    ((rankedRearrangement z n : NNReal) : ℝ≥0∞) = nthLargestMass z n := by
  -- Proof comment: apply the order-statistic characterization to the canonical ranked witness.
  symm
  exact nthLargestMass_eq_of_isRankedRearrangement
    (isRankedRearrangement_rankedRearrangement hz) n

/-- Helper for Definition 24.34: a real sequence is a probability mass sequence when all
coordinates are nonnegative and its partial sums converge to `1`. -/
private def isProbabilityMassSequence (z : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ z n) ∧ Tendsto (fun N : ℕ ↦ (Finset.range N).sum z) atTop (𝓝 1)

/-- Helper for Definition 24.34: the probability-mass-sequence condition is measurable on the
product space `ℝ^ℕ`. -/
private theorem measurableSet_isProbabilityMassSequence :
    MeasurableSet {z : ℕ → ℝ | isProbabilityMassSequence z} := by
  -- Proof comment: coordinatewise nonnegativity is a countable intersection of measurable
  -- half-spaces, and convergence of the measurable partial sums is measurable by the Polish-space
  -- convergence-set theorem.
  have hnonneg : MeasurableSet {z : ℕ → ℝ | ∀ n, 0 ≤ z n} := by
    simp_rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun n ↦ ?_
    exact measurableSet_le measurable_const (measurable_pi_apply n)
  have hpartial : ∀ N : ℕ, Measurable fun z : ℕ → ℝ ↦ (Finset.range N).sum z := by
    intro N
    simpa using (Finset.range N).measurable_fun_sum fun i _ ↦ measurable_pi_apply i
  have hlimit :
      MeasurableSet {z : ℕ → ℝ | Tendsto (fun N : ℕ ↦ (Finset.range N).sum z) atTop (𝓝 1)} := by
    simpa using
      (MeasureTheory.measurableSet_tendsto_fun hpartial
        (measurable_const : Measurable fun _ : ℕ → ℝ ↦ (1 : ℝ)))
  simpa [isProbabilityMassSequence, Set.setOf_and] using hnonneg.inter hlimit

/-- Helper for Definition 24.34: a probability mass sequence is summable because its nonnegative
partial sums converge. -/
private theorem summable_of_isProbabilityMassSequence {z : ℕ → ℝ}
    (hz : isProbabilityMassSequence z) : Summable z := by
  -- Proof comment: for nonnegative real series, convergence of the partial sums is exactly the
  -- `HasSum` criterion.
  exact ((hasSum_iff_tendsto_nat_of_nonneg hz.1 1).2 hz.2).summable

/-- Helper for Definition 24.34: a probability mass sequence has total mass `1`. -/
private theorem tsum_eq_one_of_isProbabilityMassSequence {z : ℕ → ℝ}
    (hz : isProbabilityMassSequence z) : ∑' n, z n = 1 := by
  -- Proof comment: once the nonnegative series is identified as a `HasSum`, the total sum is its
  -- limit.
  exact ((hasSum_iff_tendsto_nat_of_nonneg hz.1 1).2 hz.2).tsum_eq

/-- Helper for Definition 24.34: every ranked rearrangement comes from a nonnegative summable
sequence of total mass `1`. -/
private theorem isProbabilityMassSequence_of_isRankedRearrangement {x : MassPartition}
    {z : ℕ → ℝ} (hx : IsRankedRearrangement x z) : isProbabilityMassSequence z := by
  rcases hx with ⟨e, he⟩
  let w : ℕ → NNReal := fun n ↦ x (e.symm n)
  have hz_eq : z = fun n ↦ (w n : ℝ) := by
    -- Proof comment: rewrite the source sequence by pulling the permutation witness back through
    -- `e.symm`.
    funext n
    have h := congrFun he (e.symm n)
    simpa [w, Function.comp] using h.symm
  have hz_nonneg : ∀ n, 0 ≤ z n := by
    -- Proof comment: each source coordinate is a reordered coordinate of the mass partition.
    intro n
    rw [hz_eq]
    exact NNReal.coe_nonneg (w n)
  have hw_summable : Summable w := by
    -- Proof comment: summability is invariant under reindexing by the permutation.
    exact NNReal.summable_comp_injective x.2.2.1 e.symm.injective
  have hw_tsum : ∑' n, w n = 1 := by
    -- Proof comment: compare both reindexings of the same `NNReal` series using the injection
    -- inequality in the two permutation directions.
    have hle₁ : ∑' n, w n ≤ ∑' n, x n := by
      exact NNReal.tsum_comp_le_tsum_of_inj x.2.2.1 e.symm.injective
    have hle₂ : ∑' n, x n ≤ ∑' n, w n := by
      simpa [w, Function.comp] using
        (NNReal.tsum_comp_le_tsum_of_inj hw_summable e.injective :
          ∑' n, w (e n) ≤ ∑' n, w n)
    calc
      ∑' n, w n = ∑' n, x n := le_antisymm hle₁ hle₂
      _ = 1 := x.2.2.2
  constructor
  · exact hz_nonneg
  · have hw_hasSum : HasSum (fun n ↦ (w n : ℝ)) 1 := by
      -- Proof comment: after identifying the total `NNReal` mass, pass to the real-valued series.
      exact NNReal.hasSum_coe.2 (by simpa [hw_tsum] using hw_summable.hasSum)
    have hz_hasSum : HasSum z 1 := by
      simpa [hz_eq] using hw_hasSum
    exact (hasSum_iff_tendsto_nat_of_nonneg hz_nonneg 1).1 hz_hasSum

/-- Helper for Definition 24.34: the existence of a ranked rearrangement forces the measurable
probability-mass-sequence criterion. -/
private theorem isProbabilityMassSequence_of_existsRankedRearrangement {z : ℕ → ℝ}
    (hz : ∃ x : MassPartition, IsRankedRearrangement x z) : isProbabilityMassSequence z := by
  -- Proof comment: unpack the witness and apply the permutation-invariance argument.
  rcases hz with ⟨x, hx⟩
  exact isProbabilityMassSequence_of_isRankedRearrangement hx

/-- Helper for Definition 24.34: a probability mass sequence is rearrangeable precisely when it is
either everywhere positive or eventually zero. -/
private def isRearrangeableMassSequence (z : ℕ → ℝ) : Prop :=
  isProbabilityMassSequence z ∧ ((∀ n, 0 < z n) ∨ ∃ N, ∀ n ≥ N, z n = 0)

/-- Helper for Definition 24.34: the existence of a ranked rearrangement forces the exact support
criterion needed for the measurable branch split. -/
private theorem isRearrangeableMassSequence_of_isRankedRearrangement {x : MassPartition}
    {z : ℕ → ℝ} (hx : IsRankedRearrangement x z) : isRearrangeableMassSequence z := by
  rcases hx with ⟨e, he⟩
  refine ⟨isProbabilityMassSequence_of_isRankedRearrangement ⟨e, he⟩, ?_⟩
  by_cases hpos : ∀ n, 0 < z n
  · exact Or.inl hpos
  · -- Proof comment: once one source coordinate vanishes, the decreasing witness has only finitely
    -- many positive coordinates, so the source sequence is eventually zero.
    have hnonpos : ∃ m, z m ≤ 0 := by
      by_contra hnonpos
      apply hpos
      intro m
      exact lt_of_not_ge fun hm ↦ hnonpos ⟨m, hm⟩
    rcases hnonpos with ⟨m, hm⟩
    have hz_mass : isProbabilityMassSequence z :=
      isProbabilityMassSequence_of_isRankedRearrangement ⟨e, he⟩
    have hzm : z m = 0 := le_antisymm hm (hz_mass.1 m)
    let k := e.symm m
    have hxk_zero : x k = 0 := by
      have hk : ((x k : NNReal) : ℝ) = 0 := by
        simpa [k, Function.comp, hzm] using congrFun he k
      exact NNReal.coe_eq_zero.mp hk
    let s : Finset ℕ := (Finset.range k).image e
    have hz_zero_of_not_mem : ∀ n, n ∉ s → z n = 0 := by
      intro n hn
      have hk_le : k ≤ e.symm n := by
        by_contra hlt
        have hmem : n ∈ s := by
          apply Finset.mem_image.mpr
          refine ⟨e.symm n, Finset.mem_range.mpr (Nat.lt_of_not_ge hlt), ?_⟩
          simp
        exact hn hmem
      have hx_zero : x (e.symm n) = 0 := by
        exact le_antisymm (by simpa [hxk_zero] using x.2.1 hk_le) bot_le
      have hcoord := congrFun he (e.symm n)
      simpa [Function.comp, hx_zero] using hcoord.symm
    refine Or.inr ?_
    refine ⟨s.sup id + 1, ?_⟩
    intro n hn
    apply hz_zero_of_not_mem n
    intro hmem
    have hle : n ≤ s.sup id := Finset.le_sup (f := id) hmem
    exact Nat.not_succ_le_self (s.sup id) (le_trans hn hle)

/-- Helper for Definition 24.34: the rearrangeable-mass-sequence branch criterion is measurable on
`ℝ^ℕ`. -/
private theorem measurableSet_isRearrangeableMassSequence :
    MeasurableSet {z : ℕ → ℝ | isRearrangeableMassSequence z} := by
  have hAllPositive : MeasurableSet {z : ℕ → ℝ | ∀ n, 0 < z n} := by
    -- Proof comment: strict positivity is a countable intersection of coordinate half-spaces.
    simp_rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun n ↦ ?_
    exact measurableSet_lt measurable_const (measurable_pi_apply n)
  have hEventuallyZeroShift :
      ∀ N : ℕ, MeasurableSet {z : ℕ → ℝ | ∀ m, z (N + m) = 0} := by
    intro N
    -- Proof comment: each shifted tail condition is a countable intersection of coordinate
    -- equality sets.
    simp_rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun m ↦ ?_
    exact measurableSet_eq_fun (measurable_pi_apply (N + m)) measurable_const
  have hEventuallyZeroEq :
      {z : ℕ → ℝ | ∃ N, ∀ n ≥ N, z n = 0} =
        ⋃ N : ℕ, {z : ℕ → ℝ | ∀ m, z (N + m) = 0} := by
    ext z
    constructor
    · rintro ⟨N, hN⟩
      refine Set.mem_iUnion.mpr ?_
      refine ⟨N, ?_⟩
      exact Set.mem_setOf.mpr fun m ↦ hN (N + m) (Nat.le_add_right N m)
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn
      rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
      exact Set.mem_setOf.mp hN m
  have hEventuallyZero : MeasurableSet {z : ℕ → ℝ | ∃ N, ∀ n ≥ N, z n = 0} := by
    rw [hEventuallyZeroEq]
    exact MeasurableSet.iUnion hEventuallyZeroShift
  -- Proof comment: combine the measurable mass-sequence condition with the measurable support
  -- alternative.
  simpa [isRearrangeableMassSequence, Set.setOf_and, Set.setOf_or] using
    measurableSet_isProbabilityMassSequence.inter (hAllPositive.union hEventuallyZero)

/-- Helper for Definition 24.34: every positive superlevel set of a probability mass sequence is
finite. -/
private theorem finiteSuperlevelSet_of_isProbabilityMassSequence {z : ℕ → ℝ}
    (hz : isProbabilityMassSequence z) {eps : ℝ} (heps : 0 < eps) :
    Set.Finite {n : ℕ | eps ≤ z n} := by
  have hz_tendsto : Tendsto z atTop (𝓝 0) := by
    exact (summable_of_isProbabilityMassSequence hz).tendsto_atTop_zero
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hz_tendsto.eventually_lt_const heps)
  refine Set.Finite.subset (Set.toFinite {n : ℕ | n < N}) ?_
  intro n hn
  by_contra hnot
  have hge : N ≤ n := Nat.le_of_not_lt hnot
  have hzlt : z n < eps := hN n hge
  exact (not_lt_of_ge hn) hzlt

/-- Helper for Definition 24.34: the finite nonzero support cut out by an eventual-zero witness. -/
private def eventualZeroSupport (z : ℕ → ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n ↦ z n ≠ 0

/-- Helper for Definition 24.34: attach the descending-value lexicographic key used to sort a
finite support set without losing the original index. -/
private def descendingIndexEmbedding (z : ℕ → ℝ) : ℕ ↪ OrderDual ℝ ×ₗ ℕ where
  toFun n := ((z n : OrderDual ℝ), n)
  inj' := by
    intro i j hij
    exact congrArg Prod.snd hij

/-- Helper for Definition 24.34: a permutation whose reordered coordinates are decreasing packages
the source mass sequence into a ranked mass partition. -/
private theorem existsRankedRearrangement_of_permAntitone {z : ℕ → ℝ}
    (hz : isProbabilityMassSequence z) (e : Equiv.Perm ℕ)
    (hemono : ∀ i j, i ≤ j → z (e j) ≤ z (e i)) :
    ∃ x : MassPartition, IsRankedRearrangement x z := by
  let w : ℕ → NNReal := fun n ↦ Real.toNNReal (z (e n))
  have hw_antitone : Antitone w := by
    -- Proof comment: the reordered real coordinates are decreasing, and each of them is
    -- nonnegative because `z` is a probability mass sequence.
    intro i j hij
    change ((w j : NNReal) : ℝ) ≤ ((w i : NNReal) : ℝ)
    simpa [w, Real.toNNReal_of_nonneg (hz.1 (e i)), Real.toNNReal_of_nonneg (hz.1 (e j))] using
      hemono i j hij
  have hz_hasSum : HasSum z 1 := (hasSum_iff_tendsto_nat_of_nonneg hz.1 1).2 hz.2
  have hw_hasSum_coe : HasSum (fun n ↦ ((w n : NNReal) : ℝ)) 1 := by
    -- Proof comment: reindex the convergent real series by the permutation witness.
    simpa [w, Function.comp, hz.1] using (Equiv.hasSum_iff e).2 hz_hasSum
  have hw_hasSum : HasSum w 1 := by
    -- Proof comment: once the reordered coordinates are nonnegative, the `NNReal` and real
    -- summation statements are equivalent.
    simpa using (NNReal.hasSum_coe.1 hw_hasSum_coe)
  refine ⟨⟨w, hw_antitone, hw_hasSum.summable, hw_hasSum.tsum_eq⟩, ?_⟩
  refine ⟨e, ?_⟩
  -- Proof comment: the constructed mass partition is exactly the permuted source sequence.
  funext n
  simp [w, Function.comp, Real.toNNReal_of_nonneg (hz.1 (e n))]

/-- Helper for Definition 24.34: sorting a finite support by the descending lexicographic key
gives a prefix equivalence whose coordinates are decreasing. -/
private theorem sortedFiniteSupportPrefixEquiv {z : ℕ → ℝ} {s : Finset ℕ} :
    ∃ u : Fin s.card ↪ ℕ, Finset.image u Finset.univ = s ∧
      (∀ i j, i ≤ j → z (u j) ≤ z (u i)) := by
  classical
  let t : Finset (OrderDual ℝ ×ₗ ℕ) := Finset.map (descendingIndexEmbedding z) s
  have htcard : t.card = s.card := by simp [t]
  let g : Fin s.card ↪o OrderDual ℝ ×ₗ ℕ := t.orderEmbOfFin htcard
  let u : Fin s.card ↪ ℕ := ⟨fun i ↦ (g i).2, by
    intro i j hij
    have hi_mem : g i ∈ t := Finset.orderEmbOfFin_mem t htcard i
    have hj_mem : g j ∈ t := Finset.orderEmbOfFin_mem t htcard j
    rcases Finset.mem_map.mp hi_mem with ⟨m, hm, hm_eq⟩
    rcases Finset.mem_map.mp hj_mem with ⟨n, hn, hn_eq⟩
    have hmn : m = n := by
      calc
        m = (g i).2 := by simpa [descendingIndexEmbedding] using congrArg Prod.snd hm_eq
        _ = (g j).2 := hij
        _ = n := by simpa [descendingIndexEmbedding] using congrArg Prod.snd hn_eq.symm
    apply g.injective
    calc
      g i = descendingIndexEmbedding z m := hm_eq.symm
      _ = descendingIndexEmbedding z n := by simp [descendingIndexEmbedding, hmn]
      _ = g j := hn_eq⟩
  have hg_range : Set.range g = t := by
    exact Finset.range_orderEmbOfFin t htcard
  have hu_range : Set.range u = s := by
    ext n
    constructor
    · rintro ⟨i, rfl⟩
      have hi_mem : g i ∈ t := Finset.orderEmbOfFin_mem t htcard i
      rcases Finset.mem_map.mp hi_mem with ⟨m, hm, hm_eq⟩
      have hmu : m = u i := by
        simpa [descendingIndexEmbedding, u, g] using congrArg Prod.snd hm_eq
      exact hmu.symm ▸ hm
    · intro hn
      have hn_mem : descendingIndexEmbedding z n ∈ t := Finset.mem_map.mpr ⟨n, hn, rfl⟩
      have hn_range : descendingIndexEmbedding z n ∈ Set.range g := by
        rw [hg_range]
        exact hn_mem
      rcases hn_range with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simpa [u, g, descendingIndexEmbedding] using congrArg Prod.snd hi
  refine ⟨u, ?_, ?_⟩
  · -- Proof comment: the projected sorted keys hit exactly the original finite support.
    apply Finset.coe_injective
    simp [hu_range]
  · intro i j hij
    -- Proof comment: monotonicity of the sorted lexicographic keys gives the decreasing
    -- coordinate order after projecting back to the original indices.
    have hkey :
        ∀ k : Fin s.card, (g k).1 = (z (u k) : OrderDual ℝ) := by
      intro k
      have hk_mem : g k ∈ t := Finset.orderEmbOfFin_mem t htcard k
      rcases Finset.mem_map.mp hk_mem with ⟨m, hm, hm_eq⟩
      have hmfst : (g k).1 = (z m : OrderDual ℝ) := by
        simpa [descendingIndexEmbedding] using congrArg Prod.fst hm_eq.symm
      have hmsnd : m = u k := by
        simpa [descendingIndexEmbedding, u, g] using congrArg Prod.snd hm_eq
      simpa [hmsnd] using hmfst
    have hlex : g i ≤ g j := g.monotone hij
    have hfst : (g i).1 ≤ (g j).1 := (Prod.Lex.le_iff'.mp hlex).1
    simpa [hkey i, hkey j] using hfst

/-- Helper for Definition 24.34: every finite used set has an unused index with maximal mass
among the unused coordinates. -/
private theorem chooseUnusedMax {z : ℕ → ℝ} (hz : isProbabilityMassSequence z)
    (hpos : ∀ n, 0 < z n) (S : Finset ℕ) :
    ∃ m, m ∉ S ∧ ∀ n, n ∉ S → z n ≤ z m := by
  classical
  obtain ⟨a, haS⟩ := Infinite.exists_notMem_finset S
  let superlevel : Finset ℕ :=
    (finiteSuperlevelSet_of_isProbabilityMassSequence hz (heps := hpos a)).toFinset
  let candidates : Finset ℕ := superlevel.filter fun n ↦ n ∉ S
  have haCand : a ∈ candidates := by
    simp [candidates, superlevel, haS]
  obtain ⟨m, hmCand, hmMax⟩ := Finset.exists_max_image candidates z ⟨a, haCand⟩
  refine ⟨m, ?_, ?_⟩
  · simpa [candidates] using (Finset.mem_filter.mp hmCand).2
  · intro n hnS
    have hm_ge_seed : z a ≤ z m := hmMax a haCand
    by_cases hna : z a ≤ z n
    · exact hmMax n (by simp [candidates, superlevel, hna, hnS])
    · exact le_trans (le_of_lt (lt_of_not_ge hna)) hm_ge_seed

/-- Helper for Definition 24.34: the greedy prefixes obtained by repeatedly adjoining an unused
maximizer. -/
private noncomputable def greedyUnusedMaxPrefix {z : ℕ → ℝ}
    (hz : isProbabilityMassSequence z) (hpos : ∀ n, 0 < z n) : ∀ n, Fin n → ℕ
  | 0 => Fin.elim0
  | n + 1 =>
      let f := greedyUnusedMaxPrefix hz hpos n
      let m := Classical.choose (chooseUnusedMax hz hpos (Finset.image f Finset.univ))
      Fin.snoc f m

/-- Helper for Definition 24.34: recursively choosing an unused maximizer produces an injective
sequence whose `n`th term dominates every coordinate not used before stage `n`. -/
private theorem existsInjectiveUnusedMaxSequence {z : ℕ → ℝ}
    (hz : isProbabilityMassSequence z) (hpos : ∀ n, 0 < z n) :
    ∃ e : ℕ → ℕ, Function.Injective e ∧
      (∀ n m, m ∉ Finset.image e (Finset.range n) → z m ≤ z (e n)) := by
  classical
  let e : ℕ → ℕ := fun n ↦ greedyUnusedMaxPrefix hz hpos (n + 1) (Fin.last n)
  have himage :
      ∀ n, Finset.image e (Finset.range n) =
        Finset.image (greedyUnusedMaxPrefix hz hpos n) Finset.univ := by
    intro n
    induction n with
    | zero =>
        simp [e]
    | succ n ih =>
        let f : Fin n → ℕ := greedyUnusedMaxPrefix hz hpos n
        let s : Finset ℕ := Finset.image f Finset.univ
        let m : ℕ := Classical.choose (chooseUnusedMax hz hpos s)
        have hm_not_mem : m ∉ s := (Classical.choose_spec (chooseUnusedMax hz hpos s)).1
        have hstep :
            greedyUnusedMaxPrefix hz hpos (n + 1) = Fin.snoc f m := by
          simp [greedyUnusedMaxPrefix, f, s, m]
        have he_n : e n = m := by
          simp [e, hstep, f, s, m]
        have hsnocImage :
            Finset.image (greedyUnusedMaxPrefix hz hpos (n + 1)) Finset.univ =
              insert m (Finset.image f Finset.univ) := by
          rw [hstep]
          ext x
          constructor
          · intro hx
            rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
            cases i using Fin.lastCases with
            | last =>
                simp
            | cast i =>
                simp [Fin.snoc_castSucc]
          · intro hx
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, by simp⟩
            · rcases Finset.mem_image.mp hx' with ⟨i, -, hi⟩
              exact Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, by
                simpa [Fin.snoc_castSucc] using hi⟩
        rw [Finset.range_add_one, Finset.image_insert]
        have hnot_prev : e n ∉ Finset.image e (Finset.range n) := by
          rw [ih, he_n]
          exact hm_not_mem
        simp [ih, hsnocImage, he_n, f]
  have hstage_not_mem :
      ∀ n, e n ∉ Finset.image (greedyUnusedMaxPrefix hz hpos n) Finset.univ := by
    intro n
    let f : Fin n → ℕ := greedyUnusedMaxPrefix hz hpos n
    let s : Finset ℕ := Finset.image f Finset.univ
    let m : ℕ := Classical.choose (chooseUnusedMax hz hpos s)
    have hm_not_mem : m ∉ s := (Classical.choose_spec (chooseUnusedMax hz hpos s)).1
    have hstep :
        greedyUnusedMaxPrefix hz hpos (n + 1) = Fin.snoc f m := by
      simp [greedyUnusedMaxPrefix, f, s, m]
    rw [show e n = m by simp [e, hstep, f, s, m]]
    exact hm_not_mem
  have hdom :
      ∀ n m, m ∉ Finset.image e (Finset.range n) → z m ≤ z (e n) := by
    intro n m hm
    let f : Fin n → ℕ := greedyUnusedMaxPrefix hz hpos n
    let s : Finset ℕ := Finset.image f Finset.univ
    let chosen : ℕ := Classical.choose (chooseUnusedMax hz hpos s)
    have hchosen :
        chosen ∉ s ∧ ∀ k, k ∉ s → z k ≤ z chosen :=
      Classical.choose_spec (chooseUnusedMax hz hpos s)
    have hm' : m ∉ s := by
      intro hm_mem
      exact hm (by simpa [s, f, himage n] using hm_mem)
    have hstep :
        greedyUnusedMaxPrefix hz hpos (n + 1) = Fin.snoc f chosen := by
      simp [greedyUnusedMaxPrefix, f, s, chosen]
    simpa [e, hstep, f, s, chosen] using hchosen.2 m hm'
  have he_injective : Function.Injective e := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij_lt | hji_lt
    · have hmem : e i ∈ Finset.image e (Finset.range j) := by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hij_lt, rfl⟩
      have hmem_e : e j ∈ Finset.image e (Finset.range j) := by
        simpa [hij] using hmem
      have hmem' : e j ∈ Finset.image (greedyUnusedMaxPrefix hz hpos j) Finset.univ := by
        simpa [himage j] using hmem_e
      exact hstage_not_mem j hmem'
    · have hmem : e j ∈ Finset.image e (Finset.range i) := by
        exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hji_lt, rfl⟩
      have hmem_e : e i ∈ Finset.image e (Finset.range i) := by
        simpa [hij] using hmem
      have hmem' : e i ∈ Finset.image (greedyUnusedMaxPrefix hz hpos i) Finset.univ := by
        simpa [himage i] using hmem_e
      exact hstage_not_mem i hmem'
  exact ⟨e, he_injective, hdom⟩

/-- Helper for Definition 24.34: an eventually-zero probability mass sequence admits a ranked
rearrangement by sorting its finite positive support and then appending the zero tail. -/
private theorem existsRankedRearrangement_of_eventuallyZeroMassSequence {z : ℕ → ℝ}
    (hz : isProbabilityMassSequence z) (hzero : ∃ N, ∀ n ≥ N, z n = 0) :
    ∃ x : MassPartition, IsRankedRearrangement x z := by
  classical
  rcases hzero with ⟨N, hN⟩
  let s : Finset ℕ := eventualZeroSupport z N
  have hs_zero : ∀ n, n ∉ s → z n = 0 := by
    intro n hn
    by_cases hlt : n < N
    · by_cases hzn : z n = 0
      · exact hzn
      · exfalso
        exact hn (by simp [s, eventualZeroSupport, hlt, hzn])
    · exact hN n (Nat.le_of_not_gt hlt)
  rcases sortedFiniteSupportPrefixEquiv (z := z) (s := s) with ⟨u, hu_image, hu_mono⟩
  have hcompl_infinite : Set.Infinite {n : ℕ | n ∉ s} := by
    simpa [Finset.mem_coe] using (Finset.finite_toSet s).infinite_compl
  let tail : ℕ → ℕ := Nat.nth (fun n ↦ n ∉ s)
  have htail_injective : Function.Injective tail := Nat.nth_injective hcompl_infinite
  have htail_range : Set.range tail = {n : ℕ | n ∉ s} := Nat.range_nth_of_infinite hcompl_infinite
  let e : ℕ → ℕ := fun n ↦
    if hn : n < s.card then u ⟨n, hn⟩ else tail (n - s.card)
  have he_bijective : Function.Bijective e := by
    constructor
    · intro i j hij
      by_cases hi : i < s.card <;> by_cases hj : j < s.card
      · have hu_eq : u ⟨i, hi⟩ = u ⟨j, hj⟩ := by
          simpa [e, hi, hj] using hij
        exact congrArg Fin.val (u.injective hu_eq)
      · have hprefix_mem : e i ∈ s := by
          rw [← hu_image]
          exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, by simp [e, hi]⟩
        have htail_not_mem : e j ∉ s := by
          have : e j ∈ Set.range tail := ⟨j - s.card, by simp [e, hj]⟩
          rw [htail_range] at this
          simpa using this
        exact False.elim (htail_not_mem (hij.symm ▸ hprefix_mem))
      · have htail_not_mem : e i ∉ s := by
          have : e i ∈ Set.range tail := ⟨i - s.card, by simp [e, hi]⟩
          rw [htail_range] at this
          simpa using this
        have hprefix_mem : e j ∈ s := by
          rw [← hu_image]
          exact Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, by simp [e, hj]⟩
        exact False.elim (htail_not_mem (hij ▸ hprefix_mem))
      · have hsub : i - s.card = j - s.card := by
          exact htail_injective (by simpa [e, hi, hj] using hij)
        have hsi : s.card ≤ i := Nat.le_of_not_gt hi
        have hsj : s.card ≤ j := Nat.le_of_not_gt hj
        calc
          i = (i - s.card) + s.card := by rw [Nat.sub_add_cancel hsi]
          _ = (j - s.card) + s.card := by rw [hsub]
          _ = j := by rw [Nat.sub_add_cancel hsj]
    · intro n
      by_cases hn : n ∈ s
      · rw [← hu_image] at hn
        rcases Finset.mem_image.mp hn with ⟨i, -, rfl⟩
        exact ⟨i, by simp [e, i.2]⟩
      · have hn_range : n ∈ Set.range tail := by
          rw [htail_range]
          simpa using hn
        rcases hn_range with ⟨k, rfl⟩
        refine ⟨s.card + k, ?_⟩
        have hk : ¬ s.card + k < s.card := by
          exact Nat.not_lt.mpr (Nat.le_add_right s.card k)
        simp [e, hk]
  let perm : Equiv.Perm ℕ := Equiv.ofBijective e he_bijective
  have hmono_perm : ∀ i j, i ≤ j → z (perm j) ≤ z (perm i) := by
    intro i j hij
    by_cases hi : i < s.card
    · by_cases hj : j < s.card
      · simpa [perm, e, hi, hj] using hu_mono ⟨i, hi⟩ ⟨j, hj⟩ hij
      · have hzj_zero : z (perm j) = 0 := by
          apply hs_zero
          have : perm j ∈ Set.range tail := ⟨j - s.card, by simp [perm, e, hj]⟩
          rw [htail_range] at this
          simpa using this
        simpa [hzj_zero] using hz.1 (perm i)
    · have hsgi : s.card ≤ i := Nat.le_of_not_gt hi
      have hsj : s.card ≤ j := le_trans hsgi hij
      have hzi_zero : z (perm i) = 0 := by
        apply hs_zero
        have : perm i ∈ Set.range tail := ⟨i - s.card, by simp [perm, e, hi]⟩
        rw [htail_range] at this
        simpa using this
      have hzj_zero : z (perm j) = 0 := by
        apply hs_zero
        have hj : ¬ j < s.card := Nat.not_lt.mpr hsj
        have : perm j ∈ Set.range tail := ⟨j - s.card, by simp [perm, e, hj]⟩
        rw [htail_range] at this
        simpa using this
      rw [hzj_zero, hzi_zero]
  -- Proof comment: the finite sorted prefix controls the positive support, and the canonical
  -- complement enumeration appends only zero coordinates.
  exact existsRankedRearrangement_of_permAntitone hz perm hmono_perm

/-- Helper for Definition 24.34: the remaining infinite-support branch is the construction of a
decreasing permutation of an everywhere-positive summable mass sequence. -/
private theorem existsRankedRearrangement_of_allPositiveMassSequence {z : ℕ → ℝ}
    (hz : isProbabilityMassSequence z) (hpos : ∀ n, 0 < z n) :
    ∃ x : MassPartition, IsRankedRearrangement x z := by
  classical
  rcases existsInjectiveUnusedMaxSequence hz hpos with ⟨e, he_injective, hdom⟩
  have he_surjective : Function.Surjective e := by
    intro n
    by_contra hn
    have hsubset : Set.range e ⊆ {m : ℕ | z n ≤ z m} := by
      rintro m ⟨k, rfl⟩
      have hn_not_mem : n ∉ Finset.image e (Finset.range k) := by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨i, -, hi⟩
        exact hn ⟨i, hi⟩
      exact hdom k n hn_not_mem
    have hinfinite : Set.Infinite {m : ℕ | z n ≤ z m} :=
      (Set.infinite_range_of_injective he_injective).mono hsubset
    exact (Set.not_infinite.2
      (finiteSuperlevelSet_of_isProbabilityMassSequence hz (eps := z n) (hpos n))) hinfinite
  let perm : Equiv.Perm ℕ := Equiv.ofBijective e ⟨he_injective, he_surjective⟩
  have hmono_perm : ∀ i j, i ≤ j → z (perm j) ≤ z (perm i) := by
    intro i j hij
    by_cases hEq : i = j
    · simp [hEq]
    · have hij_lt : i < j := lt_of_le_of_ne hij hEq
      have hnot_mem : e j ∉ Finset.image e (Finset.range i) := by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨k, hk, hk_eq⟩
        have hk_lt : k < i := Finset.mem_range.mp hk
        have hk_lt' : k < j := lt_of_lt_of_le hk_lt hij
        exact (Nat.ne_of_lt hk_lt') (he_injective hk_eq)
      simpa [perm] using hdom i (e j) hnot_mem
  -- Proof comment: finite superlevel sets force the greedy injective sequence to hit every index,
  -- so it upgrades to a permutation whose reordered coordinates are decreasing.
  exact existsRankedRearrangement_of_permAntitone hz perm hmono_perm

/-- Helper for Definition 24.34: the exact branch predicate is equivalent to the existence of a
ranked rearrangement. -/
private theorem existsRankedRearrangement_iff_isRearrangeableMassSequence {z : ℕ → ℝ} :
    (∃ x : MassPartition, IsRankedRearrangement x z) ↔ isRearrangeableMassSequence z := by
  constructor
  · rintro ⟨x, hx⟩
    exact isRearrangeableMassSequence_of_isRankedRearrangement hx
  · intro hz
    rcases hz.2 with hpos | hzero
    · exact existsRankedRearrangement_of_allPositiveMassSequence hz.1 hpos
    · exact existsRankedRearrangement_of_eventuallyZeroMassSequence hz.1 hzero

-- Proof sketch: the ranked rearrangement is characterized pointwise by the unique decreasing mass
-- partition equidistributed with the input sequence, and this mass-partition-valued selection is
-- measurable on the product space.
/-- Definition 24.34: the canonical ranked-rearrangement map on real sequences, valued in
`MassPartition`, is measurable. -/
theorem measurable_rankedRearrangement :
    Measurable rankedRearrangement :=
  -- Route correction: the earlier finite-prefix sorting idea was false because the `n`th ranked
  -- value can come from arbitrarily far out in the sequence. The verified frontier is now the
  -- global order-statistic coordinate `nthLargestMass`.
  by
  have hcoord :
      ∀ n : ℕ, Measurable fun z : ℕ → ℝ ↦ rankedRearrangement z n := by
    intro n
    let s : Set (ℕ → ℝ) := {z | isRearrangeableMassSequence z}
    have hs : MeasurableSet s := measurableSet_isRearrangeableMassSequence
    have hpiece :
        (fun z : ℕ → ℝ ↦ rankedRearrangement z n) =
          s.piecewise
            (fun z ↦ (nthLargestMass z n).toNNReal)
            (fun _ ↦ singletonMassPartition n) := by
      funext z
      by_cases hz : isRearrangeableMassSequence z
      · have hExists : ∃ x : MassPartition, IsRankedRearrangement x z :=
          (existsRankedRearrangement_iff_isRearrangeableMassSequence).2 hz
        have hNth :
            rankedRearrangement z n = (nthLargestMass z n).toNNReal := by
          have hENN := rankedRearrangement_eq_nthLargestMass hExists n
          simpa using congrArg ENNReal.toNNReal hENN
        simp [s, hz, hNth]
      · have hNoExists : ¬ ∃ x : MassPartition, IsRankedRearrangement x z := by
          intro hExists
          exact hz ((existsRankedRearrangement_iff_isRearrangeableMassSequence).1 hExists)
        simp [s, hz, rankedRearrangement, hNoExists]
    rw [hpiece]
    exact Measurable.piecewise hs ((measurable_nthLargestMass n).ennreal_toNNReal)
      measurable_const
  -- Proof comment: first prove measurability of the underlying `ℕ → NNReal` coordinate map and
  -- then package it into the subtype `MassPartition`.
  have hbase : Measurable fun z : ℕ → ℝ ↦ (fun n ↦ rankedRearrangement z n : ℕ → NNReal) := by
    refine measurable_pi_lambda _ hcoord
  simpa using Measurable.subtype_mk hbase

/-- Helper for Definition 24.34: for `α ∈ [0,1)` and `θ > -α`, the GEM distribution with
parameters `(α, θ)` is the law of the stick-breaking sequence built from independent Beta
variables with shapes `(1 - α, θ + (n + 1) * α)`. -/
noncomputable def gemDistribution (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1)
    (hθα : -α < θ) : ProbabilityMeasure (ℕ → ℝ) :=
  (gemBetaProductLaw α θ hα_nonneg hα_lt_one hθα).map
    measurable_gemStickBreakingDistribution.aemeasurable

-- Proof sketch: unfold `gemDistribution` as the pushforward of `gemBetaProductLaw` by
-- `gemStickBreaking`, then apply `ProbabilityMeasure.map_apply`.
/-- The GEM law evaluates measurable sets by pulling them back along the stick-breaking map. -/
theorem gemDistribution_apply (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1)
    (hθα : -α < θ) {A : Set (ℕ → ℝ)} (hA : MeasurableSet A) :
    gemDistribution α θ hα_nonneg hα_lt_one hθα A =
      gemBetaProductLaw α θ hα_nonneg hα_lt_one hθα (gemStickBreaking ⁻¹' A) := by
  simpa [gemDistribution] using
    (gemBetaProductLaw α θ hα_nonneg hα_lt_one hθα).map_apply
      measurable_gemStickBreakingDistribution.aemeasurable hA

/-- Helper for Definition 24.34: the Poisson--Dirichlet distribution `PD_{α,θ}` is the law of the
ranked rearrangement of a `GEM_{α,θ}` stick-breaking sequence. -/
noncomputable def poissonDirichletDistribution (α θ : ℝ) (hα_nonneg : 0 ≤ α)
    (hα_lt_one : α < 1) (hθα : -α < θ) : ProbabilityMeasure MassPartition :=
  (gemDistribution α θ hα_nonneg hα_lt_one hθα).map measurable_rankedRearrangement.aemeasurable

-- Proof sketch: unfold `poissonDirichletDistribution` as the pushforward of `gemDistribution` by
-- `rankedRearrangement`, then apply `ProbabilityMeasure.map_apply`.
/-- The Poisson--Dirichlet law evaluates measurable sets by pulling them back along the canonical
ranked-rearrangement map. -/
theorem poissonDirichletDistribution_apply (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1)
    (hθα : -α < θ) {A : Set MassPartition} (hA : MeasurableSet A) :
    poissonDirichletDistribution α θ hα_nonneg hα_lt_one hθα A =
      gemDistribution α θ hα_nonneg hα_lt_one hθα (rankedRearrangement ⁻¹' A) := by
  simpa [poissonDirichletDistribution] using
    (gemDistribution α θ hα_nonneg hα_lt_one hθα).map_apply
      measurable_rankedRearrangement.aemeasurable hA

-- Proof sketch: use the uniqueness of ranked rearrangements to identify `X` almost everywhere with
-- `rankedRearrangement ∘ Z`, then push forward the `GEM_{α,θ}` law along
-- `rankedRearrangement`.
/-- Any random ranked rearrangement of a `GEM_{α,θ}` sequence has the canonical
`PD_{α,θ}` law. -/
theorem hasLaw_poissonDirichletDistribution_of_hasLaw_gemDistribution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → MassPartition} {Z : Ω → ℕ → ℝ}
    (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1) (hθα : -α < θ)
    (hZ : HasLaw Z (gemDistribution α θ hα_nonneg hα_lt_one hθα : Measure (ℕ → ℝ)) P)
    (hX_ranked : ∀ᵐ ω ∂P, IsRankedRearrangement (X ω) (Z ω)) :
    HasLaw X (poissonDirichletDistribution α θ hα_nonneg hα_lt_one hθα : Measure MassPartition) P :=
  by
  -- Proof comment: first transport the `GEM` law along the canonical ranked map.
  have hRankedLaw :
      HasLaw rankedRearrangement
        (poissonDirichletDistribution α θ hα_nonneg hα_lt_one hθα : Measure MassPartition)
        (gemDistribution α θ hα_nonneg hα_lt_one hθα : Measure (ℕ → ℝ)) := by
    refine ⟨measurable_rankedRearrangement.aemeasurable, ?_⟩
    rfl
  have hComp :
      HasLaw (fun ω ↦ rankedRearrangement (Z ω))
        (poissonDirichletDistribution α θ hα_nonneg hα_lt_one hθα : Measure MassPartition) P :=
    HasLaw.comp hRankedLaw hZ
  -- Proof comment: the almost sure ranked-rearrangement hypothesis identifies `X` with that
  -- canonical image, so `HasLaw.congr` finishes the transport.
  have hX_eq :
      X =ᵐ[P] fun ω ↦ rankedRearrangement (Z ω) := by
    filter_upwards [hX_ranked] with ω hω
    symm
    exact rankedRearrangement_eq_of_isRankedRearrangement hω
  exact hComp.congr hX_eq

end ProbabilityTheory
