/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_36

-- Declarations for this item will be appended below by the statement pipeline.

open Filter TopologicalSpace
open scoped InnerProductSpace Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Fact 2.37: compact weak subsets of a separable real Hilbert space are first
countable. -/
private theorem compact_weak_subset_firstCountable_of_separable
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [SeparableSpace K] {s : Set (WeakSpace ℝ K)} (hs : IsCompact s) :
    FirstCountableTopology s := by
  -- Transport the compact set to the weak dual, where compact subsets are metrizable in the
  -- separable case.
  let e : WeakSpace ℝ K ≃ₜ WeakDual ℝ K := weakSpaceHomeomorphWeakDual
  have hsImage : IsCompact (e '' s) := hs.image e.continuous
  haveI : MetrizableSpace (e '' s) := WeakDual.metrizable_of_isCompact ℝ K (e '' s) hsImage
  exact (e.image s).isEmbedding.firstCountableTopology

/-- Helper for Fact 2.37: in a separable real Hilbert space, every sequence in a weakly compact
set has a weakly convergent subsequence. -/
private theorem compact_weak_subset_tendsto_subseq_of_separable
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [SeparableSpace K] {s : Set (WeakSpace ℝ K)} (hs : IsCompact s)
    {x : ℕ → WeakSpace ℝ K} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  letI := compact_weak_subset_firstCountable_of_separable hs
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  -- On the compact subtype we may use the metric-space compact implies sequential compact theorem.
  let xs : ℕ → s := fun n ↦ ⟨x n, hx n⟩
  rcases CompactSpace.tendsto_subseq xs with ⟨a, φ, hφ, hφ_tendsto⟩
  have hφ_tendsto' :
      Tendsto (fun n ↦ ((xs (φ n)) : WeakSpace ℝ K)) atTop (𝓝 (a : WeakSpace ℝ K)) := by
    exact (continuous_subtype_val.tendsto a).comp hφ_tendsto
  refine ⟨a, a.2, φ, hφ, ?_⟩
  simpa [xs, Function.comp] using hφ_tendsto'

/-- Helper for Fact 2.37: a weakly convergent sequence in a real Hilbert space has norm-bounded
range. -/
private theorem isBounded_range_of_tendsto_weakSpace
    {x : ℕ → H} {y : WeakSpace ℝ H}
    (hy : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 y)) :
    Bornology.IsBounded (Set.range x) := by
  let T : ℕ → H →L[ℝ] ℝ := fun n ↦ InnerProductSpace.toDual ℝ H (x n)
  have hpointwise : ∀ u : H, ∃ C : ℝ, ∀ n : ℕ, ‖T n u‖ ≤ C := by
    intro u
    -- Weak convergence controls every scalar inner-product coordinate.
    have hu_tendsto :
        Tendsto (fun n ↦ inner ℝ (x n) u) atTop
          (𝓝 (inner ℝ ((toWeakSpace ℝ H).symm y) u)) := by
      simpa using
        (weakSpace_continuous_inner_right (H := H) u).tendsto y |>.comp hy
    have hu_bounded :
        Bornology.IsBounded (Set.range fun n ↦ inner ℝ (x n) u) :=
      Metric.isBounded_range_of_tendsto _ hu_tendsto
    rcases isBounded_iff_forall_norm_le.mp hu_bounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    have hCn : ‖inner ℝ (x n) u‖ ≤ C := hC _ (Set.mem_range_self n)
    simpa [T, InnerProductSpace.toDual_apply_apply] using hCn
  -- Banach-Steinhaus upgrades pointwise bounds to a uniform norm bound.
  obtain ⟨C, hC⟩ := uniform_boundedness_principle hpointwise
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C, ?_⟩
  rintro z ⟨n, rfl⟩
  have hTn : ‖T n‖ ≤ C := hC n
  change ‖InnerProductSpace.toDual ℝ H (x n)‖ ≤ C at hTn
  rw [(InnerProductSpace.toDual ℝ H).norm_map] at hTn
  exact hTn

/-- Helper for Fact 2.37: weak sequential compactness forces norm boundedness of the underlying
set in the ambient Hilbert space. -/
private theorem isBounded_preimage_of_isSeqCompact_weakSpace
    {s : Set (WeakSpace ℝ H)} (hs : IsSeqCompact s) :
    Bornology.IsBounded ((toWeakSpace ℝ H).symm '' s) := by
  by_contra hbounded
  rw [isBounded_iff_forall_norm_le] at hbounded
  push Not at hbounded
  have hlargeTerms :
      ∀ n : ℕ, ∃ y ∈ ((toWeakSpace ℝ H).symm '' s), ((n : ℝ) < ‖y‖) := by
    intro n
    exact hbounded n
  choose y hyMem hyNorm using hlargeTerms
  choose x hx_mem hx_eq using fun n ↦ hyMem n
  have hx_mem : ∀ n, x n ∈ s := by
    intro n
    exact hx_mem n
  rcases hs hx_mem with ⟨z, hz, φ, hφ, hφ_tendsto⟩
  have hboundedSubseq :
      Bornology.IsBounded (Set.range fun n ↦ (toWeakSpace ℝ H).symm (x (φ n))) := by
    -- A weakly convergent subsequence is norm-bounded.
    have hweakSubseq :
        Tendsto (fun n ↦ x (φ n)) atTop (𝓝 z) := by
      simpa [Function.comp] using hφ_tendsto
    have hweakSubseq' :
        Tendsto (fun n ↦ toWeakSpace ℝ H ((toWeakSpace ℝ H).symm (x (φ n)))) atTop (𝓝 z) := by
      simpa using hweakSubseq
    simpa using isBounded_range_of_tendsto_weakSpace hweakSubseq'
  rcases isBounded_iff_forall_norm_le.mp hboundedSubseq with ⟨C, hC⟩
  have hC_le : C ≤ (φ ⌈C⌉₊ : ℝ) := by
    have hmono : ⌈C⌉₊ ≤ φ ⌈C⌉₊ := StrictMono.id_le hφ ⌈C⌉₊
    exact le_trans (by exact_mod_cast Nat.le_ceil C) (by exact_mod_cast hmono)
  have hlarge : C < ‖y (φ ⌈C⌉₊)‖ := lt_of_le_of_lt hC_le (hyNorm (φ ⌈C⌉₊))
  have hsmall :
      ‖(toWeakSpace ℝ H).symm (x (φ ⌈C⌉₊))‖ ≤ C := hC _ (Set.mem_range_self ⌈C⌉₊)
  have hxy : (toWeakSpace ℝ H).symm (x (φ ⌈C⌉₊)) = y (φ ⌈C⌉₊) := hx_eq (φ ⌈C⌉₊)
  have hsmall' : ‖y (φ ⌈C⌉₊)‖ ≤ C := by simpa [hxy] using hsmall
  exact (not_lt_of_ge hsmall') hlarge

omit [CompleteSpace H] in
/-- Helper for Fact 2.37: the closed linear span of a sequence range in a real Hilbert space is
separable. -/
private theorem separableSpace_topologicalClosure_span_range (x : ℕ → H) :
    SeparableSpace (Submodule.topologicalClosure (Submodule.span ℝ (Set.range x))) := by
  -- A countable set has separable span, and taking closure preserves separability.
  exact ((Set.countable_range x).isSeparable.span.closure).separableSpace

omit [CompleteSpace H] in
/-- Helper for Fact 2.37: on a closed subspace, inclusion after orthogonal projection is the
identity. -/
private theorem weak_subtype_projection_eq_self_of_mem
    (K : Submodule ℝ H) [CompleteSpace ↥K] {z : WeakSpace ℝ H}
    (hz : (toWeakSpace ℝ H).symm z ∈ K) :
    WeakSpace.map K.subtypeL (WeakSpace.map K.orthogonalProjection z) = z := by
  -- The star projection acts as the identity on vectors already lying in the subspace.
  change toWeakSpace ℝ H ((K.subtypeL (K.orthogonalProjection ((toWeakSpace ℝ H).symm z))) : H) = z
  rw [show K.subtypeL (K.orthogonalProjection ((toWeakSpace ℝ H).symm z)) =
      K.starProjection ((toWeakSpace ℝ H).symm z) by rfl]
  rw [Submodule.starProjection_eq_self_iff.mpr hz]
  exact LinearEquiv.symm_apply_apply (toWeakSpace ℝ H) z

/-- Helper for Fact 2.37: finite weak-coordinate tubes centered at a point form neighborhoods in
`WeakSpace ℝ H`. -/
private theorem weak_coordinate_tube_mem_nhds
    (x : WeakSpace ℝ H) (F : Finset H) {ε : ℝ} (hε : 0 < ε) :
    {w : WeakSpace ℝ H |
      ∀ v ∈ F, |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) v| < ε} ∈ 𝓝 x := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha hs =>
      have hsingle :
          {w : WeakSpace ℝ H |
              |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) a| < ε} ∈ 𝓝 x := by
        let f : WeakSpace ℝ H → ℝ :=
          fun w ↦ inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) a
        have hf : Continuous f := by
          -- Weak coordinate maps remain continuous after subtracting the fixed center.
          have hcoord : Continuous fun w : WeakSpace ℝ H ↦
              inner ℝ ((toWeakSpace ℝ H).symm w) a :=
            weakSpace_continuous_inner_right (H := H) a
          simpa [f, inner_sub_left] using hcoord.sub continuous_const
        have hball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) :=
          Metric.ball_mem_nhds _ hε
        have hpre : f ⁻¹' Metric.ball (0 : ℝ) ε ∈ 𝓝 x :=
          hf.continuousAt.preimage_mem_nhds (by simpa [f] using hball)
        have hset :
            f ⁻¹' Metric.ball (0 : ℝ) ε =
              {w : WeakSpace ℝ H |
                |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) a| < ε} := by
          ext w
          simp [f, Metric.mem_ball]
        simpa [hset] using hpre
      have hinter :
          {w : WeakSpace ℝ H |
              ∀ v ∈ insert a s,
                |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) v| < ε} =
            {w : WeakSpace ℝ H |
                |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) a| < ε} ∩
              {w : WeakSpace ℝ H |
                ∀ v ∈ s, |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) v| < ε} := by
        ext w
        simp
      rw [hinter]
      exact inter_mem hsingle hs

omit [CompleteSpace H] in
/-- Helper for Fact 2.37: if orthogonal projection followed by inclusion fixes a weak point, then
the underlying vector already lies in the subspace. -/
private theorem mem_of_weak_subtype_projection_eq_self
    (K : Submodule ℝ H) [CompleteSpace ↥K] {z : WeakSpace ℝ H}
    (hz : WeakSpace.map K.subtypeL (WeakSpace.map K.orthogonalProjection z) = z) :
    (toWeakSpace ℝ H).symm z ∈ K := by
  -- Unfold the weak-space map and use the characterization of the star projection.
  change toWeakSpace ℝ H (K.starProjection ((toWeakSpace ℝ H).symm z)) = z at hz
  exact Submodule.starProjection_eq_self_iff.mp ((toWeakSpace ℝ H).injective hz)

/-- Helper for Fact 2.37: every weak closure point of `s` is the unique sequential cluster point of
some sequence in `s`. -/
private theorem exists_sequence_with_unique_cluster_of_mem_closure
    {s : Set (WeakSpace ℝ H)} {x : WeakSpace ℝ H} (hx : x ∈ closure s) :
    ∃ u : ℕ → WeakSpace ℝ H,
      (∀ n, u n ∈ s) ∧
      ∀ y : WeakSpace ℝ H,
        (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 y)) → y = x := by
  classical
  let x0 : H := (toWeakSpace ℝ H).symm x
  let P : ℕ × WeakSpace ℝ H → Prop := fun p ↦ p.2 ∈ s
  let r : (ℕ × WeakSpace ℝ H) → (ℕ × WeakSpace ℝ H) → Prop := fun p q ↦
    p.1 < q.1 ∧
      |inner ℝ ((toWeakSpace ℝ H).symm q.2 - x0) x0| < 1 / ((q.1 : ℝ) + 1) ∧
      |inner ℝ ((toWeakSpace ℝ H).symm q.2 - x0) ((toWeakSpace ℝ H).symm p.2)| <
        1 / ((q.1 : ℝ) + 1)
  have hstep : ∀ F : Finset (ℕ × WeakSpace ℝ H), (∀ p ∈ F, P p) → ∃ q, P q ∧ ∀ p ∈ F, r p q := by
    intro F hF
    let N : ℕ := F.sup Prod.fst + 1
    let G : Finset H := insert x0 (F.image fun p ↦ (toWeakSpace ℝ H).symm p.2)
    have htube :
        {w : WeakSpace ℝ H |
            ∀ v ∈ G, |inner ℝ ((toWeakSpace ℝ H).symm w - x0) v| < 1 / ((N : ℝ) + 1)} ∈ 𝓝 x := by
      have hpos : 0 < 1 / ((N : ℝ) + 1) := by positivity
      simpa [x0, G] using weak_coordinate_tube_mem_nhds (H := H) x G hpos
    obtain ⟨z, hz_tube⟩ := (mem_closure_iff_nhds').1 hx _ htube
    refine ⟨(N, z), z.2, ?_⟩
    intro p hp
    have hp_lt : p.1 < N := by
      exact lt_of_le_of_lt (Finset.le_sup hp) (Nat.lt_succ_self _)
    have hx_mem_G : x0 ∈ G := by
      simp [G]
    have hp_mem_G : (toWeakSpace ℝ H).symm p.2 ∈ G := by
      rw [show G = insert x0 (F.image fun q ↦ (toWeakSpace ℝ H).symm q.2) by rfl]
      rw [Finset.mem_insert]
      right
      exact Finset.mem_image.2 ⟨p, hp, rfl⟩
    exact ⟨hp_lt, hz_tube _ hx_mem_G, hz_tube _ hp_mem_G⟩
  obtain ⟨f, hf_mem, hf_rel⟩ := exists_seq_of_forall_finset_exists P r hstep
  let u : ℕ → WeakSpace ℝ H := fun n ↦ (f n).2
  have hu_mem : ∀ n, u n ∈ s := by
    intro n
    exact hf_mem n
  have hindex_mono : StrictMono fun n ↦ (f n).1 := by
    intro m n hmn
    exact (hf_rel m n hmn).1
  refine ⟨u, hu_mem, ?_⟩
  intro y hy
  rcases hy with ⟨φ, hφ, hφ_tendsto⟩
  let K : Submodule ℝ H :=
    Submodule.topologicalClosure
      (Submodule.span ℝ (Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n))))
  letI : CompleteSpace ↥K := by
    change CompleteSpace ↥((Submodule.span ℝ
      (Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n)))).topologicalClosure)
    infer_instance
  have hx_mem_K : x0 ∈ K := by
    have hx_mem :
        x0 ∈ Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n)) := by
      exact Set.mem_insert _ _
    exact Submodule.closure_subset_topologicalClosure_span (R := ℝ)
      (s := Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n)))
      (subset_closure hx_mem)
  have hu_mem_K : ∀ n, (toWeakSpace ℝ H).symm (u n) ∈ K := by
    intro n
    have hu_mem_range :
        (toWeakSpace ℝ H).symm (u n) ∈
          Set.insert x0 (Set.range fun m ↦ (toWeakSpace ℝ H).symm (u m)) := by
      exact Set.mem_insert_of_mem _ (Set.mem_range_self n)
    exact Submodule.closure_subset_topologicalClosure_span (R := ℝ)
      (s := Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n)))
      (subset_closure hu_mem_range)
  let F : WeakSpace ℝ H → WeakSpace ℝ H :=
    fun z ↦ WeakSpace.map K.subtypeL (WeakSpace.map K.orthogonalProjection z)
  have hF_cont : Continuous F :=
    (WeakSpace.map K.subtypeL).continuous.comp (WeakSpace.map K.orthogonalProjection).continuous
  have hF_subseq_eq : F ∘ (u ∘ φ) = u ∘ φ := by
    funext n
    dsimp [F, u, Function.comp]
    exact weak_subtype_projection_eq_self_of_mem (K := K) (hz := hu_mem_K (φ n))
  have hFy_eq_y : F y = y := by
    -- Sequential cluster points of the constructed sequence stay in the closed span generated by
    -- `x` and the sequence itself.
    have hFy_tendsto : Tendsto (F ∘ (u ∘ φ)) atTop (𝓝 (F y)) := by
      exact (hF_cont.tendsto y).comp hφ_tendsto
    rw [hF_subseq_eq] at hFy_tendsto
    exact tendsto_nhds_unique hFy_tendsto hφ_tendsto
  have hy_mem_K : (toWeakSpace ℝ H).symm y ∈ K :=
    mem_of_weak_subtype_projection_eq_self (K := K) (hz := hFy_eq_y)
  have hindex_tendsto : Tendsto (fun n ↦ (f (φ n)).1) atTop atTop :=
    (hindex_mono.comp hφ).tendsto_atTop
  have hbound_tendsto :
      Tendsto (fun n ↦ 1 / (((f (φ n)).1 : ℝ) + 1)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Function.comp] using hbase.comp hindex_tendsto
  have hx_coord :
      inner ℝ ((toWeakSpace ℝ H).symm y - x0) x0 = 0 := by
    -- The stagewise `x`-coordinate control forces the subsequential limit to match `x` on `x`.
    have hcoord_tendsto :
        Tendsto (fun n ↦ inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) x0) atTop
          (𝓝 (inner ℝ ((toWeakSpace ℝ H).symm y - x0) x0)) := by
      let g : WeakSpace ℝ H → ℝ := fun z ↦ inner ℝ ((toWeakSpace ℝ H).symm z - x0) x0
      have hg : Continuous g := by
        have hcoord : Continuous fun z : WeakSpace ℝ H ↦ inner ℝ ((toWeakSpace ℝ H).symm z) x0 :=
          weakSpace_continuous_inner_right (H := H) x0
        simpa [g, inner_sub_left] using hcoord.sub continuous_const
      simpa [g] using (hg.tendsto y).comp hφ_tendsto
    have hbound :
        ∀ᶠ n in atTop,
          |inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) x0| ≤
            1 / (((f (φ n)).1 : ℝ) + 1) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hlt : 0 < φ n := lt_of_lt_of_le Nat.zero_lt_one <|
        le_trans hn (StrictMono.id_le hφ n)
      exact le_of_lt (hf_rel 0 (φ n) hlt).2.1
    have hzero_tendsto :
        Tendsto (fun n ↦ inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) x0) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      exact squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hbound hbound_tendsto
    exact tendsto_nhds_unique hcoord_tendsto hzero_tendsto
  have hu_coord :
      ∀ m : ℕ, inner ℝ ((toWeakSpace ℝ H).symm y - x0) ((toWeakSpace ℝ H).symm (u m)) = 0 := by
    intro m
    -- The same control works for each previously chosen term `u m`.
    have hcoord_tendsto :
        Tendsto (fun n ↦
            inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) ((toWeakSpace ℝ H).symm (u m))) atTop
          (𝓝 (inner ℝ ((toWeakSpace ℝ H).symm y - x0) ((toWeakSpace ℝ H).symm (u m)))) := by
      let g : WeakSpace ℝ H → ℝ :=
        fun z ↦ inner ℝ ((toWeakSpace ℝ H).symm z - x0) ((toWeakSpace ℝ H).symm (u m))
      have hg : Continuous g := by
        have hcoord : Continuous fun z : WeakSpace ℝ H ↦
            inner ℝ ((toWeakSpace ℝ H).symm z) ((toWeakSpace ℝ H).symm (u m)) :=
          weakSpace_continuous_inner_right (H := H) ((toWeakSpace ℝ H).symm (u m))
        simpa [g, inner_sub_left] using hcoord.sub continuous_const
      simpa [g] using (hg.tendsto y).comp hφ_tendsto
    have hbound :
        ∀ᶠ n in atTop,
          |inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) ((toWeakSpace ℝ H).symm (u m))| ≤
            1 / (((f (φ n)).1 : ℝ) + 1) := by
      filter_upwards [eventually_ge_atTop (m + 1)] with n hn
      have hlt : m < φ n := lt_of_lt_of_le (Nat.lt_succ_self m) <|
        le_trans hn (StrictMono.id_le hφ n)
      exact le_of_lt (hf_rel m (φ n) hlt).2.2
    have hzero_tendsto :
        Tendsto (fun n ↦
            inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) ((toWeakSpace ℝ H).symm (u m))) atTop
          (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      exact squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hbound hbound_tendsto
    exact tendsto_nhds_unique hcoord_tendsto hzero_tendsto
  let L : H →L[ℝ] ℝ := InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm y - x0)
  have hspan_le_ker :
      Submodule.span ℝ (Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n))) ≤ L.ker := by
    refine Submodule.span_le.2 ?_
    intro z hz
    change inner ℝ ((toWeakSpace ℝ H).symm y - x0) z = 0
    rcases hz with rfl | hz
    · exact hx_coord
    · rcases hz with ⟨n, rfl⟩
      exact hu_coord n
  have hK_le_ker : K ≤ L.ker :=
    Submodule.topologicalClosure_minimal
      (s := Submodule.span ℝ (Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n))))
      hspan_le_ker (ContinuousLinearMap.isClosed_ker L)
  have hdiff_mem : (toWeakSpace ℝ H).symm y - x0 ∈ K := K.sub_mem hy_mem_K hx_mem_K
  have hdiff_zero :
      inner ℝ ((toWeakSpace ℝ H).symm y - x0) ((toWeakSpace ℝ H).symm y - x0) = 0 :=
    hK_le_ker hdiff_mem
  have hnorm_zero : ‖(toWeakSpace ℝ H).symm y - x0‖ = 0 := by
    have hsq :
        ‖(toWeakSpace ℝ H).symm y - x0‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hdiff_zero
    nlinarith [sq_nonneg ‖(toWeakSpace ℝ H).symm y - x0‖, hsq]
  have hy_eq_x0 : (toWeakSpace ℝ H).symm y = x0 := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
  exact (toWeakSpace ℝ H).injective (by simpa [x0, hy_eq_x0])

/-- Helper for Fact 2.37: a sequence in a weakly compact subset of `WeakSpace ℝ H` has a weakly
convergent subsequence after reducing to the separable closed span of its range. -/
private theorem compact_weak_subset_subseq_of_sequence_range_in_separable_span
    {s : Set (WeakSpace ℝ H)} (hs : IsCompact s)
    {x : ℕ → WeakSpace ℝ H} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  let U : Submodule ℝ H :=
    Submodule.span ℝ (Set.range fun n ↦ (toWeakSpace ℝ H).symm (x n))
  let K : Submodule ℝ H := U.topologicalClosure
  have hK_complete : CompleteSpace ↥K := by
    change CompleteSpace ↥(U.topologicalClosure)
    infer_instance
  have hK_sep : SeparableSpace ↥K :=
    separableSpace_topologicalClosure_span_range (fun n ↦ (toWeakSpace ℝ H).symm (x n))
  let y : ℕ → WeakSpace ℝ K := fun n ↦ WeakSpace.map K.orthogonalProjection (x n)
  have hy_mem : ∀ n, y n ∈ WeakSpace.map K.orthogonalProjection '' s := by
    -- The projected sequence still lies in the projected compact set.
    intro n
    exact ⟨x n, hx n, rfl⟩
  have hs_proj : IsCompact (WeakSpace.map K.orthogonalProjection '' s) := by
    -- Orthogonal projection is weak-to-weak continuous, so it preserves compactness.
    exact hs.image (WeakSpace.map K.orthogonalProjection).continuous
  rcases
      (@compact_weak_subset_tendsto_subseq_of_separable (↥K) _ _ hK_complete hK_sep
        (WeakSpace.map K.orthogonalProjection '' s) hs_proj y hy_mem) with
      ⟨aK, haK, φ, hφ, hyφ_tendsto⟩
  let a : WeakSpace ℝ H := WeakSpace.map K.subtypeL aK
  have hx_mem_K : ∀ n, (toWeakSpace ℝ H).symm (x n) ∈ K := by
    -- Each term belongs to the closed span generated by the whole sequence range.
    intro n
    exact Submodule.closure_subset_topologicalClosure_span (R := ℝ)
      (s := Set.range fun n ↦ (toWeakSpace ℝ H).symm (x n))
      (subset_closure (Set.mem_range_self n))
  have hxφ_tendsto : Tendsto (x ∘ φ) atTop (𝓝 a) := by
    -- Re-embed the projected subsequence; on the closed span this recovers the original terms.
    have ha_tendsto :
        Tendsto (fun n ↦ WeakSpace.map K.subtypeL (y (φ n))) atTop (𝓝 a) := by
      simpa [a, y, Function.comp] using
        ((WeakSpace.map K.subtypeL).continuous.tendsto aK).comp hyφ_tendsto
    have hsubseq_eq :
        (fun n ↦ WeakSpace.map K.subtypeL (y (φ n))) = x ∘ φ := by
      funext n
      dsimp [y]
      exact weak_subtype_projection_eq_self_of_mem (K := K) (hz := hx_mem_K (φ n))
    rw [hsubseq_eq] at ha_tendsto
    exact ha_tendsto
  have ha_mem : a ∈ s := by
    -- Compact subsets of the Hausdorff weak space are closed, so the subsequence limit stays in `s`.
    exact hs.isClosed.mem_of_tendsto hxφ_tendsto (Eventually.of_forall fun n ↦ hx (φ n))
  exact ⟨a, ha_mem, φ, hφ, hxφ_tendsto⟩

-- Proof sketch: this is the Eberlein-Smulian theorem specialized to the canonical weak-topology
-- space `WeakSpace ℝ H`.
private theorem isCompact_iff_isSeqCompact_weakSpace (s : Set (WeakSpace ℝ H)) :
    IsCompact s ↔ IsSeqCompact s := by
  constructor
  · intro hs
    -- Route correction: instead of working with an arbitrary subnet, project the compact weak set
    -- to the separable closed span of the given sequence and extract a subsequence there.
    intro x hx
    exact compact_weak_subset_subseq_of_sequence_range_in_separable_span hs hx
  · intro hs
    have hb : Bornology.IsBounded ((toWeakSpace ℝ H).symm '' s) :=
      isBounded_preimage_of_isSeqCompact_weakSpace hs
    have hs_closed : IsClosed s := by
      -- Route correction: instead of proving a direct Fréchet-Urysohn statement for arbitrary
      -- weakly compact sets, build a sequence in `s` whose only weak sequential cluster point is
      -- the given closure point.
      rw [← closure_subset_iff_isClosed]
      intro x hx
      rcases exists_sequence_with_unique_cluster_of_mem_closure (H := H) hx with
        ⟨u, hu_mem, hunique⟩
      rcases hs hu_mem with ⟨y, hy, φ, hφ, hφ_tendsto⟩
      have hy_eq_x : y = x := hunique y ⟨φ, hφ, hφ_tendsto⟩
      simpa [hy_eq_x] using hy
    have himage :
        (toWeakSpace ℝ H) '' ((toWeakSpace ℝ H).symm '' s) = s := by
      ext z
      constructor
      · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
        exact hw
      · intro hz
        exact ⟨(toWeakSpace ℝ H).symm z, ⟨z, hz, rfl⟩, by simp⟩
    have hclosed_preimage :
        IsClosed ((toWeakSpace ℝ H) '' ((toWeakSpace ℝ H).symm '' s)) := by
      simpa [himage] using hs_closed
    have hcompact_preimage :
        IsCompact ((toWeakSpace ℝ H) '' ((toWeakSpace ℝ H).symm '' s)) :=
      (weaklyCompact_iff_weaklyClosed_and_bounded
        (C := (toWeakSpace ℝ H).symm '' s)).2 ⟨hclosed_preimage, hb⟩
    simpa [himage] using hcompact_preimage

-- Proof sketch: apply the canonical weak-space theorem to the image of `C` under `toWeakSpace`.
/-- Fact 2.37: a subset `C` of a real Hilbert space is weakly compact if and only if it is weakly
sequentially compact. -/
theorem weaklyCompact_iff_weaklySeqCompact (C : Set H) :
    IsCompact (toWeakSpace ℝ H '' C) ↔ IsSeqCompact (toWeakSpace ℝ H '' C) := by
  simpa using isCompact_iff_isSeqCompact_weakSpace ((toWeakSpace ℝ H) '' C)
