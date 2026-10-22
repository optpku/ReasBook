/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Corollary_13_30
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Metrizable.Urysohn

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory MeasureTheory.FiniteMeasure Set
open scoped CompactlySupported Topology ENNReal

universe u

section

variable {E : Type u} [MetricSpace E] [TopologicalSpace.SeparableSpace E] [MeasurableSpace E]
  [BorelSpace E]
  [LocallyCompactSpace E]

local instance instMeasurableSpaceOnePoint : MeasurableSpace (OnePoint E) := borel (OnePoint E)
local instance instBorelSpaceOnePoint : BorelSpace (OnePoint E) := ⟨rfl⟩

instance instIsRadonMeasureSubtype (μ : { μ : Measure E // IsRadonMeasure μ }) :
    IsRadonMeasure (μ : Measure E) :=
  μ.2

/-- Helper for Corollary 13.31: integrate a compactly supported continuous test against a Radon
measure. -/
noncomputable def radonVagueIntegral (f : C_c(E, ℝ)) : { μ : Measure E // IsRadonMeasure μ } → ℝ :=
  fun μ ↦ ∫ x, f x ∂(μ : Measure E)

omit [BorelSpace E] in
@[simp] theorem radonVagueIntegral_apply (f : C_c(E, ℝ))
    (μ : { μ : Measure E // IsRadonMeasure μ }) :
    radonVagueIntegral f μ = ∫ x, f x ∂(μ : Measure E) :=
  rfl

/-- Helper for Corollary 13.31: the vague topology is induced by all compactly supported test
integrals. -/
@[reducible] noncomputable def vagueTopology
    (E : Type u) [MetricSpace E] [MeasurableSpace E] [BorelSpace E] :
    TopologicalSpace { μ : Measure E // IsRadonMeasure μ } :=
  ⨅ f : C_c(E, ℝ),
    TopologicalSpace.induced (radonVagueIntegral f) inferInstance

noncomputable instance instTopologicalSpaceRadonMeasureSubtype :
    TopologicalSpace { μ : Measure E // IsRadonMeasure μ } :=
  vagueTopology E

/-- Helper for Corollary 13.31: a finite measure on `E` is Radon in the chapter's locally compact
metric setting. -/
lemma isRadonMeasure_coeFiniteMeasure (μ : FiniteMeasure E) :
    IsRadonMeasure (μ : Measure E) := by
  -- Proof comment: the ambient finite measure already carries the owner instances required by the
  -- Radon predicate.
  exact IsRadonMeasure.of_owner (μ : Measure E)

/-- Helper for Corollary 13.31: bundle a finite measure as a Radon measure. -/
noncomputable def toRadonMeasure (μ : FiniteMeasure E) :
    { ν : Measure E // IsRadonMeasure ν } :=
  ⟨μ, isRadonMeasure_coeFiniteMeasure μ⟩

/-- Helper for Corollary 13.31: the pullback of a finite measure to a compact exhaustion piece is
again finite. -/
lemma isFiniteMeasure_compactPieceComap
    (K : CompactExhaustion E) (μ : FiniteMeasure E) (n : ℕ) :
    IsFiniteMeasure (Measure.comap Subtype.val (μ : Measure E) : Measure ↥(K n)) := by
  -- Proof comment: the compact-piece pullback measures exactly the ambient compact piece, and the
  -- ambient finite measure is finite on every set.
  refine ⟨?_⟩
  rw [show (Measure.comap Subtype.val (μ : Measure E)) Set.univ = (μ : Measure E) (K n) by
    simpa using
      comap_subtype_coe_apply ((K.isCompact n).measurableSet) (μ : Measure E)
        (Set.univ : Set ↥(K n))]
  exact measure_lt_top (μ : Measure E) _

/-- Helper for Corollary 13.31: restrict a finite measure on `E` to the compact exhaustion piece
`K n`. -/
noncomputable def compactPieceFiniteMeasure
    (K : CompactExhaustion E) (μ : FiniteMeasure E) (n : ℕ) :
    FiniteMeasure ↥(K n) :=
  ⟨Measure.comap Subtype.val (μ : Measure E), isFiniteMeasure_compactPieceComap K μ n⟩

/-- Helper for Corollary 13.31: the mass of a compact-piece restriction is bounded by the ambient
mass. -/
lemma compactPieceFiniteMeasure_mass_le
    (K : CompactExhaustion E) (μ : FiniteMeasure E) (n : ℕ) :
    (compactPieceFiniteMeasure K μ n).mass ≤ μ.mass := by
  -- Proof comment: the compact-piece restriction only sees the subset `K n ⊆ univ`.
  apply ENNReal.coe_le_coe.mp
  rw [FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass]
  have hpiece :
      (compactPieceFiniteMeasure K μ n : Measure ↥(K n)) Set.univ = (μ : Measure E) (K n) := by
    simpa [compactPieceFiniteMeasure] using
      comap_subtype_coe_apply ((K.isCompact n).measurableSet) (μ : Measure E)
        (Set.univ : Set ↥(K n))
  rw [hpiece]
  exact measure_mono (subset_univ _)

/-- Helper for Corollary 13.31: a subprobability stays a subprobability after restriction to a
compact exhaustion piece. -/
lemma compactPieceFiniteMeasure_mass_le_one
    (K : CompactExhaustion E) {μ : FiniteMeasure E} (hμ : μ.mass ≤ 1) (n : ℕ) :
    (compactPieceFiniteMeasure K μ n).mass ≤ 1 := by
  -- Proof comment: combine the monotonicity of mass under restriction with the original
  -- subprobability bound.
  exact (compactPieceFiniteMeasure_mass_le K μ n).trans hμ

/-- Helper for Corollary 13.31: if the support of `f` is contained in `K n`, then integrating `f`
over the compact-piece restriction agrees with the ambient integral. -/
lemma integral_compactPieceFiniteMeasure_eq
    (K : CompactExhaustion E) (μ : FiniteMeasure E) {n : ℕ}
    (f : C_c(E, ℝ)) (hf : tsupport f ⊆ K n) :
    ∫ x : ↥(K n), f x ∂(compactPieceFiniteMeasure K μ n : Measure ↥(K n)) =
      ∫ x, f x ∂(μ : Measure E) := by
  have hsubtype :
      ∫ x : ↥(K n), f x ∂(compactPieceFiniteMeasure K μ n : Measure ↥(K n)) =
        ∫ x in K n, f x ∂(μ : Measure E) := by
    -- Proof comment: the compact-piece owner is exactly the subtype pullback of the ambient
    -- measure.
    simpa [compactPieceFiniteMeasure] using
      (integral_subtype_comap ((K.isCompact n).measurableSet) f : _)
  have hrestrict :
      ∫ x in K n, f x ∂(μ : Measure E) = ∫ x, f x ∂(μ : Measure E) := by
    -- Proof comment: outside `K n` the test vanishes, because its topological support is already
    -- contained in `K n`.
    calc
      ∫ x in K n, f x ∂(μ : Measure E) = ∫ x, Set.indicator (K n) f x ∂(μ : Measure E) := by
        rw [integral_indicator ((K.isCompact n).measurableSet)]
      _ = ∫ x, f x ∂(μ : Measure E) := by
        refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
        by_cases hx : x ∈ K n
        · simp [hx]
        · have hfx : f x = 0 := by
            by_contra hne
            exact hx (hf (subset_tsupport f hne))
          simp [hx, hfx]
  exact hsubtype.trans hrestrict

/-- Helper for Corollary 13.31: the `n`th compact layer is the part of `K n` not already covered
by the previous compact exhaustion piece. -/
def compactLayer (K : CompactExhaustion E) : ℕ → Set E
  | 0 => K 0
  | n + 1 => K (n + 1) \ K n

/-- Helper for Corollary 13.31: compact layers are measurable. -/
lemma compactLayer_measurableSet (K : CompactExhaustion E) (n : ℕ) :
    MeasurableSet (compactLayer K n) := by
  -- Proof comment: each layer is either a compact exhaustion piece or a measurable difference of
  -- two such pieces.
  cases n with
  | zero =>
      simpa [compactLayer] using (K.isCompact 0).measurableSet
  | succ n =>
      simpa [compactLayer] using
        (K.isCompact (n + 1)).measurableSet.diff (K.isCompact n).measurableSet

/-- Helper for Corollary 13.31: every compact layer is contained in the corresponding compact
piece. -/
lemma compactLayer_subset_piece (K : CompactExhaustion E) (n : ℕ) :
    compactLayer K n ⊆ K n := by
  -- Proof comment: this is immediate from the layer definition.
  cases n with
  | zero =>
      simpa [compactLayer]
  | succ n =>
      simpa [compactLayer] using inter_subset_left

/-- Helper for Corollary 13.31: later compact layers are disjoint from earlier compact pieces. -/
lemma compactLayer_disjoint_piece (K : CompactExhaustion E) {m n : ℕ} (hmn : m < n) :
    Disjoint (K m) (compactLayer K n) := by
  -- Proof comment: once a point lies in an earlier compact piece, monotonicity of the exhaustion
  -- keeps it out of every strictly later layer.
  rcases n with _ | n
  · cases hmn
  · refine Set.disjoint_left.2 ?_
    intro x hx hm
    exact hm.2 (K.subset (Nat.lt_succ_iff.mp hmn) hx)

/-- Helper for Corollary 13.31: distinct compact layers are disjoint. -/
lemma compactLayer_pairwiseDisjoint (K : CompactExhaustion E) :
    Pairwise fun m n ↦ Disjoint (compactLayer K m) (compactLayer K n) := by
  -- Proof comment: the earlier layer lies in the earlier compact piece, which is already disjoint
  -- from every later layer.
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (compactLayer_disjoint_piece K hlt).mono_left (compactLayer_subset_piece K m)
  · exact (compactLayer_disjoint_piece K hgt).symm.mono_right (compactLayer_subset_piece K n)

/-- Helper for Corollary 13.31: the compact layers cover the whole space. -/
lemma iUnion_compactLayer_eq_univ (K : CompactExhaustion E) :
    ⋃ n, compactLayer K n = Set.univ := by
  -- Proof comment: place `x` in the first exhaustion piece that contains it; it then belongs to
  -- the corresponding new layer.
  ext x
  constructor
  · intro _
    trivial
  · intro _
    cases hfind : K.find x with
    | zero =>
        refine Set.mem_iUnion.2 ⟨0, ?_⟩
        simpa [compactLayer, hfind] using K.mem_find x
    | succ n =>
        refine Set.mem_iUnion.2 ⟨n + 1, ?_⟩
        refine ⟨by simpa [compactLayer, hfind] using K.mem_find x, ?_⟩
        intro hxPrev
        have hle : K.find x ≤ n := (K.mem_iff_find_le).mp hxPrev
        simpa [hfind] using hle

/-- Helper for Corollary 13.31: the subtype of subprobability finite measures on a compact
exhaustion piece is sequentially compact. -/
lemma compactPieceSubprobabilitySubtype_isSeqCompact
    (K : CompactExhaustion E) (n : ℕ) :
    IsSeqCompact (Set.univ : Set {ν : FiniteMeasure ↥(K n) | ν.mass ≤ 1}) := by
  letI : CompactSpace ↥(K n) := isCompact_iff_compactSpace.mp (K.isCompact n)
  intro u _
  have hu :
      ∀ k, ((u k).1 : FiniteMeasure ↥(K n)) ∈
        ({ν : FiniteMeasure ↥(K n) | ν.mass ≤ 1} : Set (FiniteMeasure ↥(K n))) := by
    -- Proof comment: forgetting the subtype proof lands back in the ambient subprobability set.
    intro k
    exact (u k).2
  have hseq :
      IsSeqCompact ({ν : FiniteMeasure ↥(K n) | ν.mass ≤ 1} :
        Set (FiniteMeasure ↥(K n))) :=
    subprobabilityMeasures_isSeqCompact (E := ↥(K n))
  obtain ⟨v, hv, φ, hφ, hconv⟩ :=
    hseq (x := fun k ↦ ((u k).1 : FiniteMeasure ↥(K n))) hu
  refine ⟨⟨v, hv⟩, by trivial, φ, hφ, ?_⟩
  -- Proof comment: convergence in the subtype is equivalent to convergence of the underlying
  -- finite measures on the compact piece.
  simpa [Function.comp] using (tendsto_subtype_rng.2 hconv)

/-- Helper for Corollary 13.31: a single diagonal subsequence makes every compact-piece coordinate
converge. -/
lemma diagonalCompactPieceSubsequence
    (K : CompactExhaustion E)
    (u : ℕ → ∀ n, {ν : FiniteMeasure ↥(K n) | ν.mass ≤ 1}) :
    ∃ v : ∀ n, {ν : FiniteMeasure ↥(K n) | ν.mass ≤ 1},
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ n, Tendsto (fun k ↦ ((u (φ k) n).1 : FiniteMeasure ↥(K n))) atTop (𝓝 ((v n).1)) := by
  -- Route correction: the earlier countable-product stub hid the actual textbook move.
  -- Proof comment: at stage `n`, extract a convergent subsequence for the `n`th compact-piece
  -- coordinate from the subsequence chosen at stage `n - 1`.
  have hstep :
      ∀ n (σ : ℕ → ℕ), StrictMono σ →
        ∃ ν : {ν : FiniteMeasure ↥(K n) | ν.mass ≤ 1},
          ∃ τ : ℕ → ℕ, StrictMono τ ∧
            Tendsto (fun k ↦ ((u (σ (τ k)) n).1 : FiniteMeasure ↥(K n))) atTop (𝓝 ((ν).1)) := by
    intro n σ hσ
    obtain ⟨ν, -, τ, hτ, hconv⟩ :=
      compactPieceSubprobabilitySubtype_isSeqCompact (K := K) (n := n)
        (x := fun k ↦ u (σ k) n) (by intro k; trivial)
    refine ⟨ν, τ, hτ, ?_⟩
    simpa [Function.comp] using (tendsto_subtype_rng.1 hconv)
  let stage : ℕ → Σ' σ : ℕ → ℕ, StrictMono σ :=
    Nat.rec ⟨id, strictMono_id⟩ fun n prev ↦
      let h := hstep n prev.1 prev.2
      let τ : ℕ → ℕ := Classical.choose (Classical.choose_spec h)
      have hτ : StrictMono τ := (Classical.choose_spec (Classical.choose_spec h)).1
      ⟨prev.1 ∘ τ, prev.2.comp hτ⟩
  let τ : ℕ → ℕ → ℕ :=
    fun n ↦ Classical.choose (Classical.choose_spec (hstep n (stage n).1 (stage n).2))
  let v : ∀ n, {ν : FiniteMeasure ↥(K n) | ν.mass ≤ 1} :=
    fun n ↦ Classical.choose (hstep n (stage n).1 (stage n).2)
  have hτ : ∀ n, StrictMono (τ n) := by
    intro n
    exact (Classical.choose_spec
      (Classical.choose_spec (hstep n (stage n).1 (stage n).2))).1
  have hstage_succ : ∀ n, (stage (n + 1)).1 = (stage n).1 ∘ τ n := by
    intro n
    rfl
  have hstage_le :
      ∀ {m n : ℕ}, m ≤ n → ∀ k, (stage m).1 k ≤ (stage n).1 k := by
    intro m n hmn
    induction hmn with
    | refl =>
        intro k
        rfl
    | @step n hmn ih =>
        intro k
        calc
          (stage m).1 k ≤ (stage n).1 k := ih k
          _ ≤ ((stage n).1 ∘ τ n) k := by
            exact (stage n).2.monotone ((hτ n).id_le k)
          _ = (stage (n + 1)).1 k := by rw [hstage_succ n]
  have hstage_factor :
      ∀ {m n : ℕ}, m ≤ n → ∀ k, ∃ r, (stage n).1 k = (stage m).1 r := by
    intro m n hmn
    induction hmn with
    | refl =>
        intro k
        exact ⟨k, rfl⟩
    | @step n hmn ih =>
        intro k
        rcases ih ((τ n) k) with ⟨r, hr⟩
        refine ⟨r, ?_⟩
        rw [hstage_succ n]
        exact hr
  have hstage_conv :
      ∀ n,
        Tendsto (fun k ↦ ((u ((stage (n + 1)).1 k) n).1 : FiniteMeasure ↥(K n))) atTop
          (𝓝 ((v n).1)) := by
    intro n
    -- Proof comment: the chosen stage-`n` extraction converges exactly along the next nested
    -- subsequence.
    simpa [v, hstage_succ n, τ, Function.comp] using
      (Classical.choose_spec
        (Classical.choose_spec (hstep n (stage n).1 (stage n).2))).2
  let φ : ℕ → ℕ := fun k ↦ (stage (k + 1)).1 k
  have hφ : StrictMono φ := by
    intro a b hab
    -- Proof comment: later diagonal entries are computed in a later stage, which dominates every
    -- earlier stage pointwise and is itself strictly increasing in the sequence index.
    calc
      φ a = (stage (a + 1)).1 a := rfl
      _ ≤ (stage (b + 1)).1 a := by
        exact hstage_le (m := a + 1) (n := b + 1) (Nat.succ_le_succ (Nat.le_of_lt hab)) a
      _ < (stage (b + 1)).1 b := (stage (b + 1)).2 hab
      _ = φ b := rfl
  have htail_factor :
      ∀ n k, ∃ r, φ (n + k) = (stage (n + 1)).1 r := by
    intro n k
    rcases hstage_factor (Nat.succ_le_succ (Nat.le_add_right n k)) (n + k) with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    simpa [φ, Nat.add_assoc] using hr
  let ψ : ℕ → ℕ → ℕ := fun n k ↦ Classical.choose (htail_factor n k)
  have hψ_eq : ∀ n k, φ (n + k) = (stage (n + 1)).1 (ψ n k) := by
    intro n k
    exact Classical.choose_spec (htail_factor n k)
  have hψ : ∀ n, StrictMono (ψ n) := by
    intro n
    intro a b hab
    have hlt : φ (n + a) < φ (n + b) := hφ (Nat.add_lt_add_left hab n)
    have himage :
        (stage (n + 1)).1 (ψ n a) < (stage (n + 1)).1 (ψ n b) := by
      simpa [hψ_eq n a, hψ_eq n b] using hlt
    exact ((stage (n + 1)).2.lt_iff_lt).mp himage
  refine ⟨v, φ, hφ, ?_⟩
  intro n
  have htail :
      Tendsto (fun k ↦ ((u (φ (n + k)) n).1 : FiniteMeasure ↥(K n))) atTop
        (𝓝 ((v n).1)) := by
    -- Proof comment: every tail of the diagonal factors through the stage where coordinate `n`
    -- was frozen, so the stagewise convergence transfers by composition.
    simpa [hψ_eq n] using (hstage_conv n).comp ((hψ n).tendsto_atTop)
  have htail' :
      Tendsto (fun k ↦ ((u (φ (k + n)) n).1 : FiniteMeasure ↥(K n))) atTop
        (𝓝 ((v n).1)) := by
    simpa [add_comm, add_left_comm, add_assoc] using htail
  exact (tendsto_add_atTop_iff_nat n).1 htail'

/-- Helper for Corollary 13.31: include the `n`th compact exhaustion piece into the next one. -/
def compactPieceSuccInclusion (K : CompactExhaustion E) (n : ℕ) :
    ↥(K n) → ↥(K (n + 1)) :=
  fun x ↦ ⟨x, K.subset (Nat.le_succ n) x.2⟩

/-- Helper for Corollary 13.31: the image of a measurable subset of `K n` stays measurable in
`K (n + 1)` under the canonical inclusion. -/
lemma measurableSet_compactPieceSuccInclusion_image
    (K : CompactExhaustion E) (n : ℕ) {s : Set ↥(K n)} (hs : MeasurableSet s) :
    MeasurableSet (compactPieceSuccInclusion K n '' s : Set ↥(K (n + 1))) := by
  -- Proof comment: the inclusion image is just the pullback of the measurable ambient image along
  -- the subtype coercion into `E`.
  have hs' : MeasurableSet (Subtype.val '' s : Set E) := by
    exact MeasurableSet.subtype_image ((K.isCompact n).measurableSet) hs
  have himage :
      (compactPieceSuccInclusion K n '' s : Set ↥(K (n + 1))) =
        Subtype.val ⁻¹' (Subtype.val '' s : Set E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, Subtype.ext hxy⟩
  rw [himage]
  exact measurable_subtype_coe hs'

/-- Helper for Corollary 13.31: restricting the `(n + 1)`st compact-piece finite measure back to
`K n` recovers the `n`th compact-piece finite measure. -/
lemma compactPieceFiniteMeasure_restrict_succ
    (K : CompactExhaustion E) (μ : FiniteMeasure E) (n : ℕ) :
    (compactPieceFiniteMeasure K μ (n + 1)).comap (compactPieceSuccInclusion K n) =
      compactPieceFiniteMeasure K μ n := by
  apply FiniteMeasure.toMeasure_injective
  -- Proof comment: after coercing to measures, both sides are pullbacks of `(μ : Measure E)`, and
  -- the nested pullback collapses along the canonical subtype inclusion.
  simpa [compactPieceFiniteMeasure, compactPieceSuccInclusion, Function.comp] using
    (Measure.comap_comap
      (f := compactPieceSuccInclusion K n)
      (g := (Subtype.val : ↥(K (n + 1)) → E))
      (hf' := fun s hs ↦ measurableSet_compactPieceSuccInclusion_image K n hs)
      (hg := Subtype.val_injective)
      (hg' := fun s hs ↦
        MeasurableSet.subtype_image ((K.isCompact (n + 1)).measurableSet) hs)
      (μ := (μ : Measure E)))

/-- Helper for Corollary 13.31: restrict a finite measure on `E` to one compact layer. -/
noncomputable def compactLayerFiniteMeasure
    (K : CompactExhaustion E) (μ : FiniteMeasure E) (n : ℕ) :
    FiniteMeasure ↥(compactLayer K n) :=
  ⟨Measure.comap Subtype.val (μ : Measure E), by
    -- Proof comment: the layer sits inside the compact piece `K n`, so its pullback mass is
    -- bounded by the finite mass of that compact exhaustion piece.
    refine ⟨?_⟩
    rw [show (Measure.comap Subtype.val (μ : Measure E)) Set.univ =
        (μ : Measure E) (compactLayer K n) by
          simpa using comap_subtype_coe_apply
            (compactLayer_measurableSet K n) (μ : Measure E)
            (Set.univ : Set ↥(compactLayer K n))]
    exact (measure_mono (compactLayer_subset_piece K n)).trans_lt
      (measure_lt_top (μ : Measure E) _)⟩

/-- Helper for Corollary 13.31: recover an ambient measure by summing pushforwards of compact-layer
coordinates. -/
noncomputable def compactLayerRecoveryMeasure
    (K : CompactExhaustion E)
    (u : (n : ℕ) → FiniteMeasure ↥(compactLayer K n)) :
    Measure E :=
  Measure.sum fun n ↦
    (u n : Measure ↥(compactLayer K n)).map Subtype.val

/-- Helper for Corollary 13.31: the compact-layer recovery measure is locally finite because every
compact exhaustion piece meets only finitely many layers. -/
lemma isLocallyFiniteMeasure_compactLayerRecoveryMeasure
    (K : CompactExhaustion E)
    (u : (n : ℕ) → FiniteMeasure ↥(compactLayer K n)) :
    IsLocallyFiniteMeasure (compactLayerRecoveryMeasure K u) := by
  -- Proof comment: around `x`, choose one compact exhaustion piece `K N` already in the
  -- neighborhood filter. All later layers are disjoint from `K N`, so only finitely many finite
  -- layer measures contribute there.
  constructor
  intro x
  rcases K.exists_mem_nhds x with ⟨N, hKN⟩
  refine ⟨K N, hKN, ?_⟩
  rw [compactLayerRecoveryMeasure, Measure.sum_apply _ (K.isCompact N).measurableSet]
  have hzero :
      ∀ n ∉ Finset.range (N + 1),
        ((u n : Measure ↥(compactLayer K n)).map Subtype.val) (K N) = 0 := by
    intro n hn
    have hNn : N < n := by
      exact Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hn)
    have hdisj :
        Disjoint (K N) (compactLayer K n) :=
      compactLayer_disjoint_piece K hNn
    have hpre :
        Subtype.val ⁻¹' K N = (∅ : Set ↥(compactLayer K n)) := by
      ext y
      constructor
      · intro hy
        exact False.elim (hdisj.le_bot ⟨hy, y.2⟩)
      · intro hy
        simp at hy
    rw [Measure.map_apply measurable_subtype_coe (K.isCompact N).measurableSet, hpre, measure_empty]
  rw [tsum_eq_sum hzero]
  simp [measure_lt_top]

/-- Helper for Corollary 13.31: the one-point compactification of a locally compact separable
metric space is second countable. -/
private theorem onePoint_secondCountable :
    SecondCountableTopology (OnePoint E) := by
  let K : CompactExhaustion E := CompactExhaustion.choice E
  obtain ⟨bE, hbE_count, -, hbE_basis⟩ := TopologicalSpace.exists_countable_basis E
  let Binf : Set (Set (OnePoint E)) :=
    {s | ∃ n : ℕ, s = (((↑) : E → OnePoint E) '' (K n : Set E))ᶜ}
  let B : Set (Set (OnePoint E)) :=
    ((fun s : Set E ↦ ((↑) : E → OnePoint E) '' s) '' bE) ∪ Binf
  have hBopen : ∀ s ∈ B, IsOpen s := by
    intro s hs
    rcases hs with hs | hs
    · rcases hs with ⟨u, hu, rfl⟩
      -- Proof comment: the open embedding `E ↪ OnePoint E` transports basis opens from `E`.
      exact OnePoint.isOpen_image_coe.2 (hbE_basis.isOpen hu)
    · rcases hs with ⟨n, rfl⟩
      -- Proof comment: neighborhoods of `∞` are complements of compact exhaustion pieces.
      exact (OnePoint.isClosed_image_coe.mpr ⟨(K.isCompact n).isClosed, K.isCompact n⟩).isOpen_compl
  have hBnhds : ∀ x u, x ∈ u → IsOpen u → ∃ v ∈ B, x ∈ v ∧ v ⊆ u := by
    intro x u hx hu
    cases x using OnePoint.rec with
    | infty =>
        have hu_nhds : u ∈ 𝓝 (OnePoint.infty : OnePoint E) := hu.mem_nhds hx
        obtain ⟨t, htc, htu⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hu_nhds
        rcases htc with ⟨_, htcompact⟩
        rcases K.exists_superset_of_isCompact htcompact with ⟨n, htn⟩
        refine ⟨(((↑) : E → OnePoint E) '' (K n : Set E))ᶜ, Or.inr ⟨n, rfl⟩, ?_, ?_⟩
        · simp [OnePoint.coe_ne_infty]
        · have himage : ((↑) : E → OnePoint E) '' t ⊆ ((↑) : E → OnePoint E) '' (K n : Set E) := by
            intro y hy
            rcases hy with ⟨z, hz, rfl⟩
            exact ⟨z, htn hz, rfl⟩
          have hsubset :
              (((↑) : E → OnePoint E) '' (K n : Set E))ᶜ ⊆
                ((↑) '' tᶜ : Set (OnePoint E)) ∪ {OnePoint.infty} := by
            simpa [OnePoint.compl_image_coe] using Set.compl_subset_compl.2 himage
          exact hsubset.trans htu
    | coe x =>
        have hu_pre : IsOpen (((↑) : E → OnePoint E) ⁻¹' u) :=
          OnePoint.continuous_coe.isOpen_preimage _ hu
        have hx_pre : x ∈ ((↑) : E → OnePoint E) ⁻¹' u := by
          simpa using hx
        rcases hbE_basis.exists_subset_of_mem_open hx_pre hu_pre with ⟨v, hv, hxv, hvu⟩
        refine ⟨((↑) : E → OnePoint E) '' v, Or.inl ⟨v, hv, rfl⟩, by simpa using hxv, ?_⟩
        -- Proof comment: inside the open copy of `E`, the ambient basis is the transported basis
        -- of `E`.
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        exact hvu hz
  have hBbasis : TopologicalSpace.IsTopologicalBasis B :=
    TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds hBopen hBnhds
  have hBinf_eq :
      Binf = Set.range (fun n : ℕ => (((↑) : E → OnePoint E) '' (K n : Set E))ᶜ) := by
    ext s
    simp [Binf, eq_comm]
  have hBinf_count : Binf.Countable := by
    rw [hBinf_eq]
    exact Set.countable_range _
  exact hBbasis.secondCountableTopology ((hbE_count.image _).union hBinf_count)

/-- Helper for Corollary 13.31: extend a compactly supported continuous test by zero to the
one-point compactification. -/
private noncomputable def onePointTestExtension (f : C_c(E, ℝ)) : C(OnePoint E, ℝ) :=
  OnePoint.continuousMapMk f.toContinuousMap 0 <| by
    -- Proof comment: compact support means the test tends to `0` along the cocompact filter.
    rw [Filter.coclosedCompact_eq_cocompact]
    simpa using f.hasCompactSupport.is_zero_at_infty

/-- Helper for Corollary 13.31: the zero extension agrees with the original test on `E`. -/
@[simp] private theorem onePointTestExtension_coe (f : C_c(E, ℝ)) (x : E) :
    onePointTestExtension f x = f x :=
  rfl

/-- Helper for Corollary 13.31: the zero extension vanishes at the point at infinity. -/
@[simp] private theorem onePointTestExtension_infty (f : C_c(E, ℝ)) :
    onePointTestExtension f OnePoint.infty = 0 :=
  rfl

/-- Helper for Corollary 13.31: the zero extension vanishes off the embedded copy of `E`. -/
private theorem onePointTestExtension_eq_zero_offRange
    (f : C_c(E, ℝ)) {z : OnePoint E}
    (hz : z ∉ Set.range ((↑) : E → OnePoint E)) :
    onePointTestExtension f z = 0 := by
  -- Proof comment: outside the range of the canonical embedding, the only point left is `∞`.
  rw [OnePoint.notMem_range_coe_iff] at hz
  rw [hz, onePointTestExtension_infty]

/-- Helper for Corollary 13.31: encode a finite subprobability on `E` as a probability measure on
the one-point compactification by putting the missing mass at `∞`. -/
private noncomputable def subProbabilityToOnePointMeasure (μ : FiniteMeasure E) :
    Measure (OnePoint E) :=
  Measure.map ((↑) : E → OnePoint E) (μ : Measure E) +
    ((1 : ℝ≥0∞) - (μ.mass : ℝ≥0∞)) • Measure.dirac (OnePoint.infty : OnePoint E)

/-- Helper for Corollary 13.31: the one-point encoding has total mass `1` once the source mass is
at most `1`. -/
private theorem subProbabilityToOnePointMeasure_univ
    (μ : FiniteMeasure E) (hμ : μ.mass ≤ 1) :
    subProbabilityToOnePointMeasure μ Set.univ = 1 := by
  -- Proof comment: evaluate the map and cemetery parts on `univ` and close the resulting
  -- ENNReal identity with the subprobability bound.
  have hμ' : (μ.mass : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast hμ
  rw [subProbabilityToOnePointMeasure, Measure.add_apply,
    Measure.map_apply OnePoint.continuous_coe.measurable MeasurableSet.univ]
  rw [Set.preimage_univ, ← FiniteMeasure.ennreal_mass, Measure.smul_apply,
    Measure.dirac_apply_of_mem (by simp)]
  simpa using add_tsub_cancel_of_le hμ'

/-- Helper for Corollary 13.31: bundle the one-point encoding as a probability measure. -/
private noncomputable def subProbabilityToOnePointProbability
    (μ : FiniteMeasure E) (hμ : μ.mass ≤ 1) :
    ProbabilityMeasure (OnePoint E) :=
  ⟨subProbabilityToOnePointMeasure μ, MeasureTheory.isProbabilityMeasure_iff.2
    (subProbabilityToOnePointMeasure_univ μ hμ)⟩

/-- Helper for Corollary 13.31: recover the ambient finite measure by restricting a probability
measure on the one-point compactification back to `E`. -/
private noncomputable def onePointProbabilityToFiniteMeasure
    (Q : ProbabilityMeasure (OnePoint E)) :
    FiniteMeasure E :=
  Q.toFiniteMeasure.comap ((↑) : E → OnePoint E)

/-- Helper for Corollary 13.31: the recovered finite measure is again a subprobability. -/
private theorem onePointProbabilityToFiniteMeasure_mass_le_one
    (Q : ProbabilityMeasure (OnePoint E)) :
    (onePointProbabilityToFiniteMeasure Q).mass ≤ 1 := by
  -- Proof comment: the recovered finite measure is a comap of the probability measure, so its
  -- mass is bounded by the source mass `1`.
  calc
    (onePointProbabilityToFiniteMeasure Q).mass ≤ Q.toFiniteMeasure.mass := by
      simpa [onePointProbabilityToFiniteMeasure] using
        (FiniteMeasure.mass_comap_le ((↑) : E → OnePoint E) Q.toFiniteMeasure)
    _ = 1 := by simp

/-- Helper for Corollary 13.31: recovering from the encoded one-point probability measure returns
the original finite measure. -/
private theorem onePointProbabilityToFiniteMeasure_encode
    (μ : FiniteMeasure E) (hμ : μ.mass ≤ 1) :
    onePointProbabilityToFiniteMeasure (subProbabilityToOnePointProbability μ hμ) = μ := by
  let hf : MeasurableEmbedding ((↑) : E → OnePoint E) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  apply FiniteMeasure.toMeasure_injective
  ext s hs
  -- Proof comment: comapping the encoded measure along `E ↪ OnePoint E` keeps the pushforward
  -- piece and deletes the cemetery atom because `∞` is not in the image of `E`.
  change Measure.comap ((↑) : E → OnePoint E) (subProbabilityToOnePointMeasure μ) s =
    (μ : Measure E) s
  rw [hf.comap_apply (subProbabilityToOnePointMeasure μ) s, subProbabilityToOnePointMeasure,
    Measure.add_apply,
    Measure.map_apply OnePoint.continuous_coe.measurable (hf.measurableSet_image' hs)]
  rw [OnePoint.coe_injective.preimage_image]
  simp

/-- Helper for Corollary 13.31: bundle the recovered finite measure together with its
subprobability bound. -/
private noncomputable def onePointProbabilityToSubProbability
    (Q : ProbabilityMeasure (OnePoint E)) :
    { μ : FiniteMeasure E | μ.mass ≤ 1 } :=
  ⟨onePointProbabilityToFiniteMeasure Q, onePointProbabilityToFiniteMeasure_mass_le_one Q⟩

/-- Helper for Corollary 13.31: integrating a zero-extended compactly supported test against the
encoded one-point measure recovers the original integral on `E`. -/
private theorem integral_onePointTestExtension_encode
    (f : C_c(E, ℝ)) (μ : FiniteMeasure E) :
    ∫ z, onePointTestExtension f z ∂(subProbabilityToOnePointMeasure μ) =
      ∫ x, f x ∂(μ : Measure E) := by
  -- Proof comment: split the encoded measure into its pushforward part and its cemetery atom;
  -- the pushforward integral is `integral_map`, while the atom contributes `0` at `∞`.
  let g : BoundedContinuousFunction (OnePoint E) ℝ :=
    BoundedContinuousFunction.mkOfCompact (onePointTestExtension f)
  let hf : MeasurableEmbedding ((↑) : E → OnePoint E) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  have hIntMap :
      Integrable (onePointTestExtension f) (Measure.map ((↑) : E → OnePoint E) (μ : Measure E)) := by
    simpa [g] using
      g.integrable (μ := Measure.map ((↑) : E → OnePoint E) (μ : Measure E))
  have hIntDirac :
      Integrable (onePointTestExtension f)
        (((1 : ℝ≥0∞) - (μ.mass : ℝ≥0∞)) • Measure.dirac (OnePoint.infty : OnePoint E)) := by
    have hfiniteDirac :
        IsFiniteMeasure
          (((1 : ℝ≥0∞) - (μ.mass : ℝ≥0∞)) • Measure.dirac (OnePoint.infty : OnePoint E)) := by
      refine ⟨?_⟩
      rw [Measure.smul_apply, Measure.dirac_apply_of_mem (by simp)]
      simpa using
        ((tsub_le_self : (1 : ℝ≥0∞) - (μ.mass : ℝ≥0∞) ≤ 1).trans_lt ENNReal.one_lt_top)
    letI := hfiniteDirac
    simpa [g] using
      g.integrable
        (μ := ((1 : ℝ≥0∞) - (μ.mass : ℝ≥0∞)) •
          Measure.dirac (OnePoint.infty : OnePoint E))
  rw [subProbabilityToOnePointMeasure, integral_add_measure hIntMap hIntDirac,
    hf.integral_map, integral_smul_measure, integral_dirac]
  simp

/-- Helper for Corollary 13.31: integrating a zero-extended compactly supported test against a
probability measure on the one-point compactification only depends on the pulled-back finite
measure on `E`. -/
private theorem integral_onePointTestExtension_recover
    (f : C_c(E, ℝ)) (Q : ProbabilityMeasure (OnePoint E)) :
    ∫ z, onePointTestExtension f z ∂(Q : Measure (OnePoint E)) =
      ∫ x, f x ∂(onePointProbabilityToFiniteMeasure Q : Measure E) := by
  -- Proof comment: first discard the null contribution from the complement of `range coe`,
  -- then identify the restricted measure with the map of the recovered finite measure.
  let hf : MeasurableEmbedding ((↑) : E → OnePoint E) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  have hrestrict :
      ∫ z, onePointTestExtension f z
          ∂((Q : Measure (OnePoint E)).restrict (Set.range ((↑) : E → OnePoint E))) =
        ∫ z, onePointTestExtension f z ∂(Q : Measure (OnePoint E)) := by
    rw [show ∫ z, onePointTestExtension f z
        ∂((Q : Measure (OnePoint E)).restrict (Set.range ((↑) : E → OnePoint E))) =
          ∫ z in Set.range ((↑) : E → OnePoint E), onePointTestExtension f z
            ∂(Q : Measure (OnePoint E)) by
          rfl]
    rw [← integral_indicator hf.measurableSet_range]
    refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
    by_cases hz : z ∈ Set.range ((↑) : E → OnePoint E)
    · simp [hz]
    · simp [hz, onePointTestExtension_eq_zero_offRange (f := f) hz]
  have hmapMeasure :
      Measure.map ((↑) : E → OnePoint E) (onePointProbabilityToFiniteMeasure Q : Measure E) =
        (Q : Measure (OnePoint E)).restrict (Set.range ((↑) : E → OnePoint E)) := by
    -- Proof comment: `map_comap` is exact for the canonical measurable embedding `E ↪ OnePoint E`.
    simpa [onePointProbabilityToFiniteMeasure] using
      (hf.map_comap (Q : Measure (OnePoint E)))
  calc
    ∫ z, onePointTestExtension f z ∂(Q : Measure (OnePoint E)) =
        ∫ z, onePointTestExtension f z
          ∂((Q : Measure (OnePoint E)).restrict (Set.range ((↑) : E → OnePoint E))) := by
          exact hrestrict.symm
    _ =
        ∫ z, onePointTestExtension f z
          ∂Measure.map ((↑) : E → OnePoint E) (onePointProbabilityToFiniteMeasure Q : Measure E) := by
          rw [hmapMeasure.symm]
    _ = ∫ x, onePointTestExtension f (((↑) : E → OnePoint E) x)
          ∂(onePointProbabilityToFiniteMeasure Q : Measure E) := by
          rw [hf.integral_map]
    _ = ∫ x, f x ∂(onePointProbabilityToFiniteMeasure Q : Measure E) := by
          simp

-- Proof sketch: exhaust `E` by relatively compact open sets, apply the preceding Prohorov-type
-- compactness result to the restricted owner family of subprobability finite measures on the
-- compact closures, and diagonalize the resulting subsequences. The compatibility of the
-- restricted limits reconstructs a vague limit in the image of the canonical bridge
-- `toRadonMeasure : FiniteMeasure E → RadonMeasure E`.
/-- Corollary 13.31: if `E` is a locally compact separable metric space, then the textbook space
`𝓜_{≤ 1}(E)` of sub-probability measures is sequentially compact for the vague topology, viewed as
the image under `toRadonMeasure` of the canonical owner set
`{μ : FiniteMeasure E | μ.mass ≤ 1}`. -/
theorem subProbabilityMeasureSpace_isSeqCompact_vagueTopology :
    IsSeqCompact (toRadonMeasure '' {μ : FiniteMeasure E | μ.mass ≤ 1}) := by
  intro ρs hρs
  have hrepr :
      ∀ n, ∃ μ : FiniteMeasure E, μ.mass ≤ 1 ∧ toRadonMeasure μ = ρs n := by
    -- Proof comment: unwrap each point of the image set into its finite-measure representative.
    intro n
    rcases hρs n with ⟨μ, hμ, hρn⟩
    exact ⟨μ, hμ, hρn⟩
  choose μs hμs_subprob hμs_eq using hrepr
  -- Route correction: the remaining obstruction is no longer the old compact-piece restriction
  -- equality. The active route is the one-point compactification model: encode each subprobability
  -- as a probability on `OnePoint E`, extract a weakly convergent subsequence there, recover the
  -- limit finite measure by comap, and compare vague coordinates through zero-extended tests.
  let Qs : ℕ → ProbabilityMeasure (OnePoint E) :=
    fun n ↦ subProbabilityToOnePointProbability (μs n) (hμs_subprob n)
  letI : SecondCountableTopology (OnePoint E) := onePoint_secondCountable
  letI : TopologicalSpace.MetrizableSpace (OnePoint E) := by
    infer_instance
  letI : MetricSpace (OnePoint E) := TopologicalSpace.metrizableSpaceMetric (OnePoint E)
  letI : TopologicalSpace.MetrizableSpace (ProbabilityMeasure (OnePoint E)) := by
    infer_instance
  letI : SeqCompactSpace (ProbabilityMeasure (OnePoint E)) := by
    infer_instance
  obtain ⟨Q, φ, hφ, hQφ⟩ := SeqCompactSpace.tendsto_subseq Qs
  let μ : FiniteMeasure E := onePointProbabilityToFiniteMeasure Q
  have hcoord :
      ∀ f : C_c(E, ℝ),
        Tendsto
          (fun n ↦ radonVagueIntegral f (toRadonMeasure (μs (φ n))))
          atTop
          (𝓝 (radonVagueIntegral f (toRadonMeasure μ))) := by
    intro f
    let g : BoundedContinuousFunction (OnePoint E) ℝ :=
      BoundedContinuousFunction.mkOfCompact (onePointTestExtension f)
    -- Proof comment: weak convergence on the one-point compactification transfers to vague
    -- convergence on `E` by the encode/recover integral identities for the zero extension.
    have hg :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hQφ) g
    simpa [Qs, g, μ, Function.comp, radonVagueIntegral_apply,
      onePointProbabilityToFiniteMeasure_encode,
      integral_onePointTestExtension_encode, integral_onePointTestExtension_recover] using hg
  have hconv :
      Tendsto (fun n ↦ toRadonMeasure (μs (φ n))) atTop (𝓝 (toRadonMeasure μ)) := by
    -- Proof comment: `vagueTopology` is the infimum of the induced test-integral topologies, so
    -- the coordinatewise integral convergence above is exactly convergence in the vague topology.
    simpa [vagueTopology, nhds_iInf, nhds_induced, Filter.tendsto_iInf,
      Filter.tendsto_comap_iff, Function.comp_def] using hcoord
  refine ⟨toRadonMeasure μ, ?_, φ, hφ, ?_⟩
  · exact ⟨μ, onePointProbabilityToFiniteMeasure_mass_le_one Q, rfl⟩
  · simpa [Function.comp, hμs_eq] using hconv

end
