/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_4
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.UrysohnsBounded

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BoundedContinuousFunction CompactlySupported
open Set Metric

noncomputable section

/-- Part (1) of Exercise 13.1.1: the supremum-norm space `C([0,1], ℝ)` is separable. -/
-- This is the canonical owner instance for continuous maps on a locally compact second-countable
-- domain.
theorem continuousMap_Icc_zero_one_separable :
    TopologicalSpace.SeparableSpace (C(Set.Icc (0 : ℝ) 1, ℝ)) := by
  infer_instance

-- Proof sketch for Exercise 13.1.1 (2): produce an uncountable family of bounded continuous
-- functions that are pairwise
-- separated by a fixed positive distance in the supremum norm.
/-- Helper for Exercise 13.1.1: the sampled point `n` lies in `Set.Ici (0 : ℝ)`. -/
lemma samplePoint_mem (n : ℕ) : (0 : ℝ) ≤ n := by
  exact_mod_cast Nat.zero_le n

/-- Helper for Exercise 13.1.1: sample the half-line at the natural numbers. -/
abbrev samplePoint : ℕ → Set.Ici (0 : ℝ) := fun n ↦ ⟨n, samplePoint_mem n⟩

/-- Helper for Exercise 13.1.1: the sampled natural numbers form a closed discrete subset of
`Set.Ici (0 : ℝ)`. -/
lemma samplePoint_isClosedEmbedding : Topology.IsClosedEmbedding samplePoint := by
  -- The sample points stay uniformly separated by distance at least `1`.
  refine Metric.isClosedEmbedding_of_pairwise_le_dist zero_lt_one ?_
  intro m n hmn
  simpa [samplePoint] using Nat.pairwise_one_le_dist hmn

/-- Helper for Exercise 13.1.1: every sampled subset of `ℕ` is closed in `Set.Ici (0 : ℝ)`. -/
lemma samplePoint_image_isClosed (s : Set ℕ) : IsClosed (samplePoint '' s) := by
  -- Closed embeddings send closed sets to closed sets, and subsets of `ℕ` are closed.
  exact samplePoint_isClosedEmbedding.isClosedMap _ (isClosed_discrete s)

/-- Helper for Exercise 13.1.1: the images of a subset of `ℕ` and of its complement are disjoint. -/
lemma samplePoint_image_compl_disjoint (s : Set ℕ) :
    Disjoint (samplePoint '' s) (samplePoint '' sᶜ) := by
  -- Injectivity of the sampling map reduces the claim to `Disjoint s sᶜ`.
  rw [Set.disjoint_left]
  intro x hx hx'
  rcases hx with ⟨n, hn, rfl⟩
  rcases hx' with ⟨m, hm, hEq⟩
  have hnm : n = m := by
    simpa using (congrArg Subtype.val hEq).symm
  subst hnm
  exact hm hn

/-- Helper for Exercise 13.1.1: Urysohn's lemma codes a subset of `ℕ` by a bounded continuous
function that is `0` on the sampled set and `1` on the sampled complement. -/
def subsetCodeFunction (s : Set ℕ) : (Set.Ici (0 : ℝ)) →ᵇ ℝ :=
  Classical.choose <|
    exists_bounded_zero_one_of_closed
      (samplePoint_image_isClosed s)
      (samplePoint_image_isClosed sᶜ)
      (samplePoint_image_compl_disjoint s)

/-- Helper for Exercise 13.1.1: `subsetCodeFunction s` has the expected zero/one values on the
sampled subset and its complement. -/
lemma subsetCodeFunction_spec (s : Set ℕ) :
    EqOn (subsetCodeFunction s) 0 (samplePoint '' s) ∧
      EqOn (subsetCodeFunction s) 1 (samplePoint '' sᶜ) := by
  -- This unwraps the chosen Urysohn witness once and stores only the rewrite-ready API.
  have hspec :=
    Classical.choose_spec
      (exists_bounded_zero_one_of_closed
        (samplePoint_image_isClosed s)
        (samplePoint_image_isClosed sᶜ)
        (samplePoint_image_compl_disjoint s))
  exact ⟨by simpa [subsetCodeFunction] using hspec.1, by simpa [subsetCodeFunction] using hspec.2.1⟩

/-- Helper for Exercise 13.1.1: different subsets of `ℕ` produce bounded continuous functions at
distance at least `1`. -/
lemma subsetCodeFunction_one_le_dist {s t : Set ℕ} (hst : s ≠ t) :
    1 ≤ dist (subsetCodeFunction s) (subsetCodeFunction t) := by
  classical
  -- Pick a natural number where the two subsets disagree.
  have hdiff : ∃ n, (n ∈ s ∧ n ∉ t) ∨ (n ∈ t ∧ n ∉ s) := by
    by_contra hNoDiff
    apply hst
    ext n
    by_cases hs : n ∈ s
    · by_cases ht : n ∈ t
      · simp [hs, ht]
      · exfalso
        exact hNoDiff ⟨n, Or.inl ⟨hs, ht⟩⟩
    · by_cases ht : n ∈ t
      · exfalso
        exact hNoDiff ⟨n, Or.inr ⟨ht, hs⟩⟩
      · simp [hs, ht]
  rcases hdiff with ⟨n, hst' | hts'⟩
  · rcases hst' with ⟨hs, hnt⟩
    have hsSpec := (subsetCodeFunction_spec s).1 ⟨n, hs, rfl⟩
    have htSpec := (subsetCodeFunction_spec t).2 ⟨n, hnt, rfl⟩
    -- Evaluating at the witness point transfers a pointwise distance lower bound to the sup norm.
    calc
      1 =
          dist ((subsetCodeFunction s) (samplePoint n))
            ((subsetCodeFunction t) (samplePoint n)) := by
        rw [hsSpec, htSpec]
        norm_num
      _ ≤ dist (subsetCodeFunction s) (subsetCodeFunction t) := by
        simpa using
          (BoundedContinuousFunction.dist_coe_le_dist
            (f := subsetCodeFunction s) (g := subsetCodeFunction t) (x := samplePoint n))
  · rcases hts' with ⟨ht, hns⟩
    have hsSpec := (subsetCodeFunction_spec s).2 ⟨n, hns, rfl⟩
    have htSpec := (subsetCodeFunction_spec t).1 ⟨n, ht, rfl⟩
    -- The symmetric-difference witness gives the same estimate with the roles reversed.
    calc
      1 =
          dist ((subsetCodeFunction s) (samplePoint n))
            ((subsetCodeFunction t) (samplePoint n)) := by
        rw [hsSpec, htSpec]
        norm_num
      _ ≤ dist (subsetCodeFunction s) (subsetCodeFunction t) := by
        simpa using
          (BoundedContinuousFunction.dist_coe_le_dist
            (f := subsetCodeFunction s) (g := subsetCodeFunction t) (x := samplePoint n))

/-- Helper for Exercise 13.1.1: the powerset of `ℕ` is not countable. -/
lemma not_countable_setNat : ¬ Countable (Set ℕ) := by
  -- Countability would give an injection into `ℕ`, contradicting Cantor's theorem.
  intro hCountable
  letI : Countable (Set ℕ) := hCountable
  rcases Countable.exists_injective_nat (Set ℕ) with ⟨f, hf⟩
  exact Function.cantor_injective f hf

/-- Helper for Exercise 13.1.1: the inclusion into bounded continuous functions remembers a
compactly supported continuous function completely. -/
lemma toBoundedContinuousFunction_injective :
    Function.Injective
      (CompactlySupportedContinuousMap.toBoundedContinuousFunction :
        C_c(Set.Ici (0 : ℝ), ℝ) → (Set.Ici (0 : ℝ)) →ᵇ ℝ) := by
  intro f g hfg
  ext x
  exact DFunLike.congr_fun hfg x

/-- Helper for Exercise 13.1.1: `C_c(Set.Ici (0 : ℝ), ℝ)` carries the sup metric induced from its
inclusion into bounded continuous functions. -/
noncomputable instance : MetricSpace (C_c(Set.Ici (0 : ℝ), ℝ)) := fast_instance%
  MetricSpace.induced
    CompactlySupportedContinuousMap.toBoundedContinuousFunction
    toBoundedContinuousFunction_injective
    inferInstance

/-- Part (2) of Exercise 13.1.1: the supremum-norm space of bounded continuous real-valued
functions on `[0, ∞)` is not separable. -/
theorem boundedContinuousFunction_Ici_not_separable :
    ¬ TopologicalSpace.SeparableSpace ((Set.Ici (0 : ℝ)) →ᵇ ℝ) := by
  intro hSeparable
  letI : TopologicalSpace.SeparableSpace ((Set.Ici (0 : ℝ)) →ᵇ ℝ) := hSeparable
  -- Route correction: instead of constructing ad hoc bump functions, code subsets of `ℕ` by
  -- Urysohn separation on a closed discrete subset of `Set.Ici (0 : ℝ)`.
  have hCountable : Countable (Set ℕ) := by
    -- The `1/2`-balls around the code functions are pairwise disjoint, open, and nonempty.
    refine Pairwise.countable_of_isOpen_disjoint
      (s := fun s : Set ℕ ↦ ball (subsetCodeFunction s) (1 / 2))
      ?_ ?_ ?_
    · intro s t hst
      have hdist : 1 ≤ dist (subsetCodeFunction s) (subsetCodeFunction t) :=
        subsetCodeFunction_one_le_dist hst
      have hhalf : (1 / 2 : ℝ) + 1 / 2 ≤ dist (subsetCodeFunction s) (subsetCodeFunction t) := by
        linarith
      simpa using Metric.ball_disjoint_ball hhalf
    · intro s
      simp
    · intro s
      refine ⟨subsetCodeFunction s, ?_⟩
      simp
  exact not_countable_setNat hCountable

/-- Helper for Exercise 13.1.1: the half-line `[0, ∞)` as a subtype. -/
abbrev halfLine : Type := Set.Ici (0 : ℝ)

/-- Helper for Exercise 13.1.1: the zero point of `halfLine`. -/
abbrev halfLineZero : halfLine := ⟨0, by simp⟩

/-- Helper for Exercise 13.1.1: the sampled compact interval `[0, n]` inside `halfLine`. -/
def sampledInterval (n : ℕ) : Set halfLine := Set.Icc halfLineZero (samplePoint n)

/-- Helper for Exercise 13.1.1: the sampled point lies above `0` in the half-line order. -/
lemma zero_le_samplePoint (n : ℕ) : halfLineZero ≤ samplePoint n := by
  change (0 : ℝ) ≤ (samplePoint n : ℝ)
  exact samplePoint_mem n

/-- Helper for Exercise 13.1.1: the right endpoint of `sampledInterval n`. -/
def sampledIntervalTop (n : ℕ) : sampledInterval n :=
  ⟨samplePoint n, Set.right_mem_Icc.2 (zero_le_samplePoint n)⟩

/-- Helper for Exercise 13.1.1: `sampledInterval n` is compact as a subset of `halfLine`. -/
lemma sampledInterval_isCompact (n : ℕ) : IsCompact (sampledInterval n) := by
  have hEmbedding : Topology.IsClosedEmbedding (Subtype.val : halfLine → ℝ) :=
    isClosed_Ici.isClosedEmbedding_subtypeVal
  have hEq :
      sampledInterval n = (Subtype.val : halfLine → ℝ) ⁻¹' Set.Icc (0 : ℝ) n := by
    ext x
    constructor
    · intro hx
      simpa [sampledInterval, halfLineZero, samplePoint] using hx.2
    · intro hx
      refine ⟨?_, ?_⟩
      · change (0 : ℝ) ≤ (x : ℝ)
        exact x.2
      · simpa [sampledInterval, halfLineZero, samplePoint] using hx
  rw [hEq]
  exact hEmbedding.isCompact_preimage (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) n))

/-- Helper for Exercise 13.1.1: the interval carrier `sampledInterval n` is compact. -/
instance sampledInterval_compactSpace (n : ℕ) : CompactSpace (sampledInterval n) :=
  isCompact_iff_compactSpace.mp (sampledInterval_isCompact n)

/-- Helper for Exercise 13.1.1: the `n`-tail-zero subspace of `C_c([0, ∞), ℝ)`. -/
def zeroTailSubspace (n : ℕ) : Set (C_c(halfLine, ℝ)) :=
  {f | ∀ x, samplePoint n ≤ x → f x = 0}

/-- Helper for Exercise 13.1.1: the endpoint-zero subspace of `C([0, n], ℝ)`. -/
def topZeroSubspace (n : ℕ) : Set (C(sampledInterval n, ℝ)) :=
  {g | g (sampledIntervalTop n) = 0}

/-- Helper for Exercise 13.1.1: every compactly supported continuous map on `halfLine` vanishes on
some tail `[{samplePoint n}, ∞)`. -/
lemma exists_zero_tail (f : C_c(halfLine, ℝ)) :
    ∃ n : ℕ, ∀ x, samplePoint n ≤ x → f x = 0 := by
  let K : Set halfLine := tsupport f
  have hK : IsCompact K := f.hasCompactSupport.isCompact
  have hBounded : BddAbove (Subtype.val '' K) := (hK.image continuous_subtype_val).bddAbove
  rcases bddAbove_def.mp hBounded with ⟨b, hb⟩
  refine ⟨Nat.ceil b + 1, ?_⟩
  intro x hx
  by_cases hxSupport : x ∈ tsupport f
  · -- A support point would lie below the compact-support bound, contradicting `x ≥ samplePoint n`.
    have hxLe : (x : ℝ) ≤ b := hb _ ⟨x, hxSupport, rfl⟩
    have hbLt : b < ((Nat.ceil b + 1 : ℕ) : ℝ) := by
      refine lt_of_le_of_lt (Nat.le_ceil b) ?_
      exact_mod_cast Nat.lt_succ_self (Nat.ceil b)
    have hxLt : (x : ℝ) < ((Nat.ceil b + 1 : ℕ) : ℝ) := lt_of_le_of_lt hxLe hbLt
    exact False.elim <| (not_lt_of_ge (show (((Nat.ceil b + 1 : ℕ) : ℝ) ≤ x) from hx)) hxLt
  · -- Outside the topological support the function is forced to be zero.
    simpa using image_eq_zero_of_notMem_tsupport hxSupport

/-- Helper for Exercise 13.1.1: tail-zero functions restrict to interval maps vanishing at the top
endpoint. -/
lemma restrict_mem_topZeroSubspace {n : ℕ} {f : C_c(halfLine, ℝ)}
    (hf : f ∈ zeroTailSubspace n) :
    ContinuousMap.restrict (sampledInterval n) (f : C(halfLine, ℝ)) ∈ topZeroSubspace n := by
  -- The tail-zero condition evaluated at the right endpoint gives the endpoint-zero constraint.
  simpa [zeroTailSubspace, topZeroSubspace, sampledIntervalTop] using hf (samplePoint n) le_rfl

/-- Helper for Exercise 13.1.1: the interval extension of an endpoint-zero map to `halfLine`. -/
def topZeroExtensionToContinuousMap (n : ℕ) (g : topZeroSubspace n) : C(halfLine, ℝ) :=
  ContinuousMap.IccExtend (zero_le_samplePoint n) g.1

/-- Helper for Exercise 13.1.1: the interval extension is supported inside `sampledInterval n`. -/
lemma topZeroExtension_support_subset (n : ℕ) (g : topZeroSubspace n) :
    Function.support (topZeroExtensionToContinuousMap n g) ⊆ sampledInterval n := by
  intro x hx
  refine ⟨?_, ?_⟩
  · change (0 : ℝ) ≤ (x : ℝ)
    exact x.2
  by_contra hxNotLe
  have hxGe : samplePoint n ≤ x := le_of_not_ge hxNotLe
  have hxZero : topZeroExtensionToContinuousMap n g x = 0 := by
    calc
      topZeroExtensionToContinuousMap n g x = g.1 (sampledIntervalTop n) := by
        simpa [topZeroExtensionToContinuousMap, sampledIntervalTop] using
          (Set.IccExtend_of_right_le (zero_le_samplePoint n) g.1 hxGe)
      _ = 0 := g.2
  exact hx hxZero

/-- Helper for Exercise 13.1.1: the interval extension defines a compactly supported map on
`halfLine`. -/
lemma topZeroExtension_hasCompactSupport (n : ℕ) (g : topZeroSubspace n) :
    HasCompactSupport (topZeroExtensionToContinuousMap n g) := by
  -- The extension is zero to the right of `samplePoint n`, so its support stays in a compact
  -- interval.
  exact HasCompactSupport.of_support_subset_isCompact (sampledInterval_isCompact n)
    (topZeroExtension_support_subset n g)

/-- Helper for Exercise 13.1.1: extend an endpoint-zero interval map by zero on the tail. -/
def topZeroExtension (n : ℕ) (g : topZeroSubspace n) : C_c(halfLine, ℝ) :=
  ⟨topZeroExtensionToContinuousMap n g, topZeroExtension_hasCompactSupport n g⟩

/-- Helper for Exercise 13.1.1: on the interval, `topZeroExtension` agrees with the original
interval map. -/
lemma topZeroExtension_apply_of_mem {n : ℕ} (g : topZeroSubspace n) {x : halfLine}
    (hx : x ∈ sampledInterval n) :
    topZeroExtension n g x = g.1 ⟨x, hx⟩ := by
  -- Inside the interval, `IccExtend` is just evaluation of the original map.
  simpa [topZeroExtension, topZeroExtensionToContinuousMap] using
    (Set.IccExtend_of_mem (zero_le_samplePoint n) g.1 hx)

/-- Helper for Exercise 13.1.1: on the tail, `topZeroExtension` is identically zero. -/
lemma topZeroExtension_apply_of_right_le {n : ℕ} (g : topZeroSubspace n) {x : halfLine}
    (hx : samplePoint n ≤ x) :
    topZeroExtension n g x = 0 := by
  -- To the right of the interval, `IccExtend` stays equal to the top endpoint value, which is `0`.
  calc
    topZeroExtension n g x = g.1 (sampledIntervalTop n) := by
      simpa [topZeroExtension, topZeroExtensionToContinuousMap, sampledIntervalTop] using
        (Set.IccExtend_of_right_le (zero_le_samplePoint n) g.1 hx)
    _ = 0 := g.2

/-- Helper for Exercise 13.1.1: every endpoint-zero interval extension belongs to the corresponding
tail-zero piece. -/
lemma topZeroExtension_mem_zeroTailSubspace (n : ℕ) (g : topZeroSubspace n) :
    topZeroExtension n g ∈ zeroTailSubspace n := by
  -- The extension is explicitly zero on the whole tail.
  intro x hx
  exact topZeroExtension_apply_of_right_le g hx

/-- Helper for Exercise 13.1.1: restrict a tail-zero function to the corresponding endpoint-zero
interval subspace. -/
def restrictToTopZeroSubspace (n : ℕ) (f : {f : C_c(halfLine, ℝ) // f ∈ zeroTailSubspace n}) :
    topZeroSubspace n :=
  ⟨ContinuousMap.restrict (sampledInterval n) (f.1 : C(halfLine, ℝ)),
    restrict_mem_topZeroSubspace f.2⟩

/-- Helper for Exercise 13.1.1: restricting the extension recovers the original interval map. -/
lemma restrict_topZeroExtension (n : ℕ) (g : topZeroSubspace n) :
    restrictToTopZeroSubspace n
      ⟨topZeroExtension n g, topZeroExtension_mem_zeroTailSubspace n g⟩ = g := by
  apply Subtype.ext
  ext x
  -- Restriction followed by interval extension is identity on the interval.
  simp [restrictToTopZeroSubspace, topZeroExtension_apply_of_mem, x.2]

/-- Helper for Exercise 13.1.1: extending the restriction recovers a tail-zero function. -/
lemma topZeroExtension_restrict (n : ℕ) (f : {f : C_c(halfLine, ℝ) // f ∈ zeroTailSubspace n}) :
    topZeroExtension n (restrictToTopZeroSubspace n f) = f.1 := by
  ext x
  by_cases hx : x ∈ sampledInterval n
  · -- On the interval, the extension equals the original restricted function.
    rw [topZeroExtension_apply_of_mem (restrictToTopZeroSubspace n f) hx]
    simp [restrictToTopZeroSubspace, ContinuousMap.restrict_apply]
  · -- Off the interval, the extension and the original function are both zero.
    have hxNotLe : ¬ x ≤ samplePoint n := by
      intro hxLe
      exact hx ⟨x.2, hxLe⟩
    have hxGe : samplePoint n ≤ x := le_of_not_ge hxNotLe
    rw [topZeroExtension_apply_of_right_le (restrictToTopZeroSubspace n f) hxGe, f.2 x hxGe]

/-- Helper for Exercise 13.1.1: the bounded-function avatar of `topZeroExtension` is an isometry.
-/
lemma topZeroExtension_toBoundedContinuousFunction_isometry (n : ℕ) :
    Isometry fun g : topZeroSubspace n =>
      CompactlySupportedContinuousMap.toBoundedContinuousFunction (topZeroExtension n g) := by
  refine Isometry.of_dist_eq ?_
  intro g h
  letI : Nonempty (sampledInterval n) := ⟨sampledIntervalTop n⟩
  apply le_antisymm
  · -- The extension cannot increase the sup distance because outside the interval both functions
    -- are zero.
    refine (BoundedContinuousFunction.dist_le dist_nonneg).2 ?_
    intro x
    by_cases hx : x ∈ sampledInterval n
    · rw [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
        CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
        topZeroExtension_apply_of_mem g hx, topZeroExtension_apply_of_mem h hx]
      simpa using ContinuousMap.dist_apply_le_dist (f := g.1) (g := h.1) ⟨x, hx⟩
    · have hxGe : samplePoint n ≤ x := by
        have hxNotLe : ¬ x ≤ samplePoint n := by
          intro hxLe
          exact hx ⟨by
            change (0 : ℝ) ≤ (x : ℝ)
            exact x.2, hxLe⟩
        exact le_of_not_ge hxNotLe
      rw [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
        CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
        topZeroExtension_apply_of_right_le g hxGe, topZeroExtension_apply_of_right_le h hxGe]
      simp
  · -- Evaluating the extensions on the interval recovers the original pointwise distances.
    change dist g.1 h.1 ≤
      dist
        (CompactlySupportedContinuousMap.toBoundedContinuousFunction (topZeroExtension n g))
        (CompactlySupportedContinuousMap.toBoundedContinuousFunction (topZeroExtension n h))
    refine (ContinuousMap.dist_le_iff_of_nonempty (f := g.1) (g := h.1)).2 ?_
    intro x
    have hx :=
      BoundedContinuousFunction.dist_coe_le_dist
        (f := CompactlySupportedContinuousMap.toBoundedContinuousFunction (topZeroExtension n g))
        (g := CompactlySupportedContinuousMap.toBoundedContinuousFunction (topZeroExtension n h))
        (x := (x : halfLine))
    rw [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
      topZeroExtension_apply_of_mem g x.2, topZeroExtension_apply_of_mem h x.2] at hx
    simpa using hx

/-- Helper for Exercise 13.1.1: `topZeroExtension` is continuous for the induced sup topology on
compactly supported maps. -/
lemma topZeroExtension_continuous (n : ℕ) : Continuous (topZeroExtension n) := by
  have hEmbedding :
      Topology.IsEmbedding
        (CompactlySupportedContinuousMap.toBoundedContinuousFunction :
          C_c(halfLine, ℝ) → halfLine →ᵇ ℝ) :=
    Function.Injective.isEmbedding_induced toBoundedContinuousFunction_injective
  have hCompContinuous :
      Continuous fun g : topZeroSubspace n =>
        CompactlySupportedContinuousMap.toBoundedContinuousFunction (topZeroExtension n g) :=
    (topZeroExtension_toBoundedContinuousFunction_isometry n).continuous
  -- The compactly supported topology is induced from bounded continuous functions, so continuity
  -- can be checked after applying the embedding.
  exact (hEmbedding.isInducing.continuous_iff).2 hCompContinuous

/-- Helper for Exercise 13.1.1: the `n`-tail-zero piece is exactly the range of
`topZeroExtension n`. -/
lemma mem_range_topZeroExtension_iff {n : ℕ} {f : C_c(halfLine, ℝ)} :
    f ∈ Set.range (topZeroExtension n) ↔ f ∈ zeroTailSubspace n := by
  constructor
  · rintro ⟨g, rfl⟩
    exact topZeroExtension_mem_zeroTailSubspace n g
  · intro hf
    refine ⟨restrictToTopZeroSubspace n ⟨f, hf⟩, ?_⟩
    simpa using topZeroExtension_restrict n ⟨f, hf⟩

/-- Helper for Exercise 13.1.1: each tail-zero piece is separable because it is the range of an
isometric extension from a separable compact-interval function space. -/
lemma zeroTail_isSeparable (n : ℕ) :
    TopologicalSpace.IsSeparable (zeroTailSubspace n) := by
  letI : TopologicalSpace.SeparableSpace (topZeroSubspace n) := by infer_instance
  have hRange : TopologicalSpace.IsSeparable (Set.range (topZeroExtension n)) :=
    TopologicalSpace.isSeparable_range (topZeroExtension_continuous n)
  have hEq : Set.range (topZeroExtension n) = zeroTailSubspace n := by
    ext f
    exact mem_range_topZeroExtension_iff
  simpa [hEq] using hRange

/-- Exercise 13.1.1 (3): the supremum-norm space `C_c([0, ∞), ℝ)` is separable. -/
-- This is the canonical owner instance for compactly supported continuous maps on a locally
-- compact second-countable domain.
theorem compactlySupportedContinuousMap_Ici_separable :
    TopologicalSpace.SeparableSpace (C_c(Set.Ici (0 : ℝ), ℝ)) := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  have hCover : (⋃ n : ℕ, zeroTailSubspace n) = (Set.univ : Set (C_c(halfLine, ℝ))) := by
    ext f
    constructor
    · intro _
      simp
    · intro _
      rcases exists_zero_tail f with ⟨n, hn⟩
      exact Set.mem_iUnion.2 ⟨n, hn⟩
  -- A compactly supported function belongs to some tail-zero piece, and each piece is separable.
  rw [← hCover]
  exact TopologicalSpace.IsSeparable.iUnion zeroTail_isSeparable
