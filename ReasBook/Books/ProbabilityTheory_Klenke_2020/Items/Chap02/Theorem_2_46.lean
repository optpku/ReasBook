/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.BondPercolationAPI
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.BondPercolationBoxErasure
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.BondPercolationFiniteCylinder
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_45

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped unitInterval
open unitInterval

local notation "half" => oneHalfUnitInterval

/-- The canonical percolation function `θ` for bond percolation on `ℤ²`: it sends `p ∈ [0,1]` to
the probability that the origin belongs to an infinite open cluster under the canonical Bernoulli
bond-percolation law with parameter `p`. -/
noncomputable def canonicalBondPercolationTheta : unitInterval → NNReal :=
  fun p ↦
    originPercolationProbability
      ⟨ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p, inferInstance⟩
      (openCluster
        (bondConnectionEvent (fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg)))

/-- Helper for Theorem 2.46: under the canonical Bernoulli law on edge configurations, the
identity random edge set already has the prescribed Bernoulli distribution. -/
lemma canonicalBernoulli_id_isSetBernoulli
    (p : unitInterval) :
    IsSetBernoulli
      (fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg)
      (latticeGraph 2).edgeSet p
      (ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p) := by
  -- Proof comment: the identity map has the canonical Bernoulli law by construction.
  simpa using
    (ProbabilityTheory.HasLaw.id :
      HasLaw
        (fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg)
        (ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p)
        (ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p))

/-- Helper for Theorem 2.46: enlarging the set of open bonds preserves the event that the origin
lies in an infinite open cluster. -/
lemma originInInfiniteClusterEvent_increasing
    {cfg cfg' : Set (Sym2 (LatticePoint 2))}
    (hcfg : cfg ⊆ cfg')
    (horigin :
      cfg ∈ originInInfiniteClusterEvent
        (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s)))) :
    cfg' ∈ originInInfiniteClusterEvent
      (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) := by
  have horiginInfinite :
      Set.Infinite
        (openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
          0 cfg) := by
    simpa [originInInfiniteClusterEvent] using horigin
  have hedgeSubset :
      (cfg ∩ (latticeGraph 2).edgeSet) ⊆
        (cfg' ∩ (latticeGraph 2).edgeSet) := by
    intro e he
    exact ⟨hcfg he.1, he.2⟩
  have hmono :
      openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg ≤
        openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg' :=
    SimpleGraph.fromEdgeSet_mono hedgeSubset
  have hclusterSubset :
      openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
          0 cfg ⊆
        openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
          0 cfg' := by
    intro y hy
    -- Proof comment: any open path in the smaller configuration is still an open path after more
    -- edges are declared open.
    simpa [openCluster_mem_iff, bondConnectionEvent] using
      (SimpleGraph.Reachable.mono hmono <|
        by simpa [openCluster_mem_iff, bondConnectionEvent] using hy)
  -- Proof comment: the origin cluster itself grows under `cfg ⊆ cfg'`, so infinitude persists.
  have horiginInfinite' :
      Set.Infinite
        (openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
          0 cfg') :=
    horiginInfinite.mono hclusterSubset
  simpa [originInInfiniteClusterEvent] using horiginInfinite'

/-- Helper for Theorem 2.46: if a `unitInterval` point lies strictly above `1/2`, then there is
another `unitInterval` point strictly between `1/2` and it. -/
lemma exists_unitInterval_between_half_and
    (x : unitInterval) (hx : half < x) :
    ∃ q : unitInterval, half < q ∧ q < x := by
  let q : unitInterval := Set.Icc.convexCombo half x oneHalfUnitInterval
  have hx_real : (1 : ℝ) / 2 < (x : ℝ) := by
    simpa [oneHalfUnitInterval] using hx
  have hq_formula : (q : ℝ) = (((1 : ℝ) / 2) + x) / 2 := by
    rw [Set.Icc.coe_convexCombo]
    norm_num [q, oneHalfUnitInterval]
    ring
  refine ⟨q, ?_, ?_⟩
  · change
      (1 : ℝ) / 2 <
        ((Set.Icc.convexCombo half x oneHalfUnitInterval : unitInterval) : ℝ)
    simpa [q] using show (1 : ℝ) / 2 < (q : ℝ) by
      nlinarith [hx_real, hq_formula]
  · change
      (((Set.Icc.convexCombo half x oneHalfUnitInterval : unitInterval) : ℝ) <
        x)
    simpa [q] using show (q : ℝ) < (x : ℝ) by
      nlinarith [hx_real, hq_formula]

/-- Helper for Theorem 2.46: the midpoint parameter `1 / 2` is not the left endpoint of
`[0,1]`. -/
lemma half_ne_zero : (half : unitInterval) ≠ 0 := by
  intro hhalf
  have hhalfReal : ((half : unitInterval) : ℝ) = 0 := by
    exact congrArg (fun p : unitInterval ↦ (p : ℝ)) hhalf
  -- Proof comment: coercing to `ℝ` turns the midpoint claim into the false identity `1 / 2 = 0`.
  norm_num [oneHalfUnitInterval] at hhalfReal

/-- Helper for Theorem 2.46: the midpoint parameter `1 / 2` is not the right endpoint of
`[0,1]`. -/
lemma half_ne_one : (half : unitInterval) ≠ 1 := by
  intro hhalf
  have hhalfReal : ((half : unitInterval) : ℝ) = 1 := by
    exact congrArg (fun p : unitInterval ↦ (p : ℝ)) hhalf
  -- Proof comment: coercing to `ℝ` turns the midpoint claim into the false identity `1 / 2 = 1`.
  norm_num [oneHalfUnitInterval] at hhalfReal

/-- Helper for Theorem 2.46: the complementary Bernoulli parameter fixes the midpoint. -/
lemma sigma_half_eq_half : σ half = half := by
  apply Subtype.ext
  -- Proof comment: on the midpoint, the complement map `p ↦ 1 - p` is the identity.
  norm_num [oneHalfUnitInterval]

/-- Helper for Theorem 2.46: parameters below `1 / 2` are sent above `1 / 2` by the complement
map `σ p = 1 - p`. -/
lemma half_lt_sigma_of_lt_half
    (p : unitInterval) (hp : p < half) :
    half < σ p := by
  change (1 : ℝ) / 2 < ((σ p : unitInterval) : ℝ)
  have hpReal : (p : ℝ) < (1 : ℝ) / 2 := by
    simpa [oneHalfUnitInterval] using hp
  -- Proof comment: rewriting `σ p` as `1 - p` reduces the claim to elementary real arithmetic.
  have hsigmaReal : (((σ p : unitInterval) : ℝ)) = 1 - p := by
    rfl
  nlinarith [hpReal, hsigmaReal]

/-- Helper for Theorem 2.46: parameters above `1 / 2` are sent below `1 / 2` by the complement
map `σ p = 1 - p`. -/
lemma sigma_lt_half_of_half_lt
    (p : unitInterval) (hp : half < p) :
    σ p < half := by
  change (((σ p : unitInterval) : ℝ) < (1 : ℝ) / 2)
  have hpReal : (1 : ℝ) / 2 < (p : ℝ) := by
    simpa [oneHalfUnitInterval] using hp
  -- Proof comment: this is the symmetric real-arithmetic companion to
  -- `half_lt_sigma_of_lt_half`.
  have hsigmaReal : (((σ p : unitInterval) : ℝ)) = 1 - p := by
    rfl
  nlinarith [hpReal, hsigmaReal]

/-- Helper for Theorem 2.46: the number of distinct infinite open clusters in a configuration,
obtained by counting the infinite cluster sets that occur among all lattice roots. -/
noncomputable def infiniteOpenClusterCount
    {Ω : Type*} {d : ℕ}
    (cluster : LatticePoint d → Ω → Set (LatticePoint d)) : Ω → ℕ∞ :=
  fun ω ↦
    {C : Set (LatticePoint d) | ∃ x : LatticePoint d, C = cluster x ω ∧ Set.Infinite C}.encard

/-- Helper for Theorem 2.46: two roots determine the same open cluster exactly when they are
bond-connected in the underlying configuration. -/
lemma openCluster_eq_iff_bondConnected
    {Ω : Type*} {d : ℕ}
    (openEdges : Ω → Set (Sym2 (LatticePoint d))) (x y : LatticePoint d) (ω : Ω) :
    openCluster (bondConnectionEvent openEdges) x ω =
      openCluster (bondConnectionEvent openEdges) y ω ↔
        ω ∈ bondConnectionEvent openEdges x y := by
  constructor
  · intro hxyClusters
    -- Proof comment: if the cluster sets agree, then the root `y` lies in the cluster of `x`
    -- because every root is connected to itself.
    have hyMem : y ∈ openCluster (bondConnectionEvent openEdges) y ω := by
      simp [openCluster, bondConnectionEvent]
    rw [← hxyClusters] at hyMem
    simpa [openCluster, bondConnectionEvent] using hyMem
  · intro hxy
    -- Proof comment: once the roots are connected, transitivity of reachability transports
    -- membership between the two cluster descriptions.
    ext z
    constructor
    · intro hz
      change (openBondGraph openEdges ω).Reachable y z
      change (openBondGraph openEdges ω).Reachable x z at hz
      exact (SimpleGraph.Reachable.symm hxy).trans hz
    · intro hz
      change (openBondGraph openEdges ω).Reachable x z
      change (openBondGraph openEdges ω).Reachable y z at hz
      exact hxy.trans hz

/-- Helper for Theorem 2.46: the exact-two cluster count is equivalent to the existence of two
distinct infinite root clusters that exhaust all infinite clusters. -/
lemma infiniteOpenClusterCount_eq_two_iff
    {Ω : Type*} {d : ℕ}
    (openEdges : Ω → Set (Sym2 (LatticePoint d))) (ω : Ω) :
    infiniteOpenClusterCount (openCluster (bondConnectionEvent openEdges)) ω = 2 ↔
      ∃ x y : LatticePoint d,
        Set.Infinite (openCluster (bondConnectionEvent openEdges) x ω) ∧
        Set.Infinite (openCluster (bondConnectionEvent openEdges) y ω) ∧
        ω ∉ bondConnectionEvent openEdges x y ∧
        ∀ z : LatticePoint d,
          Set.Infinite (openCluster (bondConnectionEvent openEdges) z ω) →
            ω ∈ bondConnectionEvent openEdges z x ∨
              ω ∈ bondConnectionEvent openEdges z y := by
  set cluster : LatticePoint d → Set (LatticePoint d) :=
    fun x ↦ openCluster (bondConnectionEvent openEdges) x ω
  set S : Set (Set (LatticePoint d)) :=
    {C | ∃ x : LatticePoint d, C = cluster x ∧ Set.Infinite C}
  -- Proof comment: count infinite cluster sets first, then recover representative roots.
  change S.encard = 2 ↔ _
  constructor
  · intro hS
    rcases (Set.encard_eq_two).1 hS with ⟨Cx, Cy, hCxCy, hS_eq⟩
    have hCx_mem : Cx ∈ S := by
      rw [hS_eq]
      simp
    have hCy_mem : Cy ∈ S := by
      rw [hS_eq]
      simp
    rcases hCx_mem with ⟨x, rfl, hxinf⟩
    rcases hCy_mem with ⟨y, rfl, hyinf⟩
    refine ⟨x, y, hxinf, hyinf, ?_, ?_⟩
    · intro hxy
      exact hCxCy ((openCluster_eq_iff_bondConnected openEdges x y ω).2 hxy)
    · intro z hzinf
      have hzmem : cluster z ∈ S := ⟨z, rfl, hzinf⟩
      rw [hS_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hzmem
      rcases hzmem with hzx | hzy
      · exact Or.inl ((openCluster_eq_iff_bondConnected openEdges z x ω).1 hzx)
      · exact Or.inr ((openCluster_eq_iff_bondConnected openEdges z y ω).1 hzy)
  · rintro ⟨x, y, hxinf, hyinf, hxy, hclass⟩
    have hcluster_ne : cluster x ≠ cluster y := by
      intro hxyClusters
      exact hxy ((openCluster_eq_iff_bondConnected openEdges x y ω).1 hxyClusters)
    have hS_eq : S = {cluster x, cluster y} := by
      ext C
      constructor
      · intro hC
        rcases hC with ⟨z, rfl, hzinf⟩
        rcases hclass z hzinf with hzx | hzy
        · left
          exact (openCluster_eq_iff_bondConnected openEdges z x ω).2 hzx
        · right
          exact (openCluster_eq_iff_bondConnected openEdges z y ω).2 hzy
      · intro hC
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
        rcases hC with hC | hC
        · subst hC
          exact ⟨x, rfl, hxinf⟩
        · subst hC
          exact ⟨y, rfl, hyinf⟩
    exact (Set.encard_eq_two).2 ⟨cluster x, cluster y, hcluster_ne, hS_eq⟩

/-- Helper for Theorem 2.46: the erased outside-box two-arm event asks for two distinct shell
vertices whose erased clusters are both infinite and remain disconnected after the box edges are
deleted. -/
def outsideBoxTwoArmEvent_config
    (d : ℕ) (L : ℕ) : Set (Set (Sym2 (LatticePoint d))) :=
  {cfg |
    ∃ x ∈ boundaryShell d L, ∃ y ∈ boundaryShell d L,
      x ≠ y ∧
        Set.Infinite
          (openCluster
            (bondConnectionEvent
              (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L)) x cfg) ∧
        Set.Infinite
          (openCluster
            (bondConnectionEvent
              (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L)) y cfg) ∧
        cfg ∉
          bondConnectionEvent
            (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) x y}

/-- Helper for Theorem 2.46: fixing the shell witnesses gives the stable witness form of the
erased outside-box two-arm event. -/
def outsideBoxTwoArmWitnessEvent_config
    (d : ℕ) (L : ℕ) (x y : LatticePoint d) :
    Set (Set (Sym2 (LatticePoint d))) :=
  {cfg |
    x ∈ boundaryShell d L ∧
      y ∈ boundaryShell d L ∧
      x ≠ y ∧
      Set.Infinite
        (openCluster
          (bondConnectionEvent
            (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L)) x cfg) ∧
      Set.Infinite
        (openCluster
          (bondConnectionEvent
            (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L)) y cfg) ∧
      cfg ∉
        bondConnectionEvent
          (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) x y}

/-- Helper for Theorem 2.46: the coarse erased outside-box two-arm event is the countable union of
its fixed witness versions. -/
lemma outsideBoxTwoArmEvent_config_eq_iUnion_witness
    (d : ℕ) (L : ℕ) :
    outsideBoxTwoArmEvent_config d L =
      ⋃ x : LatticePoint d, ⋃ y : LatticePoint d,
        outsideBoxTwoArmWitnessEvent_config d L x y := by
  ext cfg
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hxinf, hyinf, hnotconn⟩
    -- Proof comment: package the coarse witnesses as one point in the iterated union.
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨y, ?_⟩⟩
    exact ⟨hx, hy, hxy, hxinf, hyinf, hnotconn⟩
  · intro hcfg
    -- Proof comment: unpack a point of the iterated union back into the coarse event data.
    rcases Set.mem_iUnion.1 hcfg with ⟨x, hxcfg⟩
    rcases Set.mem_iUnion.1 hxcfg with ⟨y, hycfg⟩
    rcases hycfg with ⟨hx, hy, hxy, hxinf, hyinf, hnotconn⟩
    exact ⟨x, hx, y, hy, hxy, hxinf, hyinf, hnotconn⟩

/-- Helper for Theorem 2.46: positive mass of the coarse erased outside-box two-arm event refines
to positive mass of one concrete shell witness pair. -/
lemma exists_pos_measure_fixedOutsideTwoArmWitness_of_outsideBoxTwoArmEvent_pos
    (d : ℕ) (p : unitInterval) {L : ℕ}
    (hPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p
          (outsideBoxTwoArmEvent_config d L)) :
    ∃ x y : LatticePoint d,
      x ∈ boundaryShell d L ∧
      y ∈ boundaryShell d L ∧
      x ≠ y ∧
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p
          (outsideBoxTwoArmWitnessEvent_config d L x y) := by
  let μ : Measure (Set (Sym2 (LatticePoint d))) :=
    ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p
  have hUnionPos :
      0 <
        μ (⋃ x : LatticePoint d, ⋃ y : LatticePoint d,
          outsideBoxTwoArmWitnessEvent_config d L x y) := by
    -- Proof comment: rewrite the coarse event as the witness union before selecting a positive
    -- coordinate slice.
    simpa [μ, outsideBoxTwoArmEvent_config_eq_iUnion_witness (d := d) L] using hPos
  obtain ⟨x, hxPos⟩ :
      ∃ x : LatticePoint d,
        0 < μ (⋃ y : LatticePoint d,
          outsideBoxTwoArmWitnessEvent_config d L x y) :=
    exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hUnionPos)
  obtain ⟨y, hyPos⟩ :
      ∃ y : LatticePoint d,
        0 < μ (outsideBoxTwoArmWitnessEvent_config d L x y) :=
    exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hxPos)
  have hxShell : x ∈ boundaryShell d L := by
    by_contra hxNotShell
    have hEmpty : outsideBoxTwoArmWitnessEvent_config d L x y = ∅ := by
      ext cfg
      simp [outsideBoxTwoArmWitnessEvent_config, hxNotShell]
    have : (0 : ENNReal) < 0 := by
      simpa [μ, hEmpty] using hyPos
    exact (lt_irrefl (0 : ENNReal)) this
  have hyShell : y ∈ boundaryShell d L := by
    by_contra hyNotShell
    have hEmpty : outsideBoxTwoArmWitnessEvent_config d L x y = ∅ := by
      ext cfg
      simp [outsideBoxTwoArmWitnessEvent_config, hyNotShell]
    have : (0 : ENNReal) < 0 := by
      simpa [μ, hEmpty] using hyPos
    exact (lt_irrefl (0 : ENNReal)) this
  have hxy : x ≠ y := by
    by_contra hxyEq
    have hEmpty : outsideBoxTwoArmWitnessEvent_config d L x y = ∅ := by
      ext cfg
      simp [outsideBoxTwoArmWitnessEvent_config, hxyEq]
    have : (0 : ENNReal) < 0 := by
      simpa [μ, hEmpty] using hyPos
    exact (lt_irrefl (0 : ENNReal)) this
  -- Proof comment: positivity of the chosen witness event forces the shell and inequality side
  -- conditions, because each violated side condition would collapse the event to `∅`.
  exact ⟨x, y, hxShell, hyShell, hxy, by simpa [μ] using hyPos⟩

/-- Helper for Theorem 2.46: bond-connection events are symmetric because reachability in an
undirected graph is symmetric. -/
lemma mem_bondConnectionEvent_symm
    {d : ℕ}
    (openEdges : Set (Sym2 (LatticePoint d)) → Set (Sym2 (LatticePoint d)))
    {cfg : Set (Sym2 (LatticePoint d))} {x y : LatticePoint d}
    (hxy : cfg ∈ bondConnectionEvent openEdges x y) :
    cfg ∈ bondConnectionEvent openEdges y x := by
  -- Proof comment: the open bond graph is undirected, so every connection can be traversed in
  -- the reverse direction.
  simpa [bondConnectionEvent] using SimpleGraph.Reachable.symm hxy

/-- Helper for Theorem 2.46: deleting `boxEdges d L` can only remove open edges, so every
erased-box connection is still a connection in the original configuration. -/
lemma bondConnectionEvent_eraseBox_subset_id
    {d : ℕ} (L : ℕ) {cfg : Set (Sym2 (LatticePoint d))} {x y : LatticePoint d}
    (hxy :
      cfg ∈ bondConnectionEvent
        (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) x y) :
    cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x y := by
  have hsubset :
      ((cfg \ boxEdges d L) ∩ (latticeGraph d).edgeSet) ⊆
        (cfg ∩ (latticeGraph d).edgeSet) := by
    intro e he
    simp only [Set.mem_inter_iff, Set.mem_diff, and_assoc] at he
    simp only [Set.mem_inter_iff]
    exact ⟨he.1, he.2.2⟩
  have hmono :
      openBondGraph (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) cfg ≤
        openBondGraph (fun s : Set (Sym2 (LatticePoint d)) ↦ s) cfg :=
    SimpleGraph.fromEdgeSet_mono hsubset
  -- Proof comment: every erased-box open path is also an open path before erasing edges, because
  -- the erased edge set is a subset of the original one.
  simpa [bondConnectionEvent, openBondGraph] using SimpleGraph.Reachable.mono hmono hxy

/-- Helper for Theorem 2.46: if two roots are disconnected in the original configuration, then
their erased shell witnesses are still distinct and disconnected after deleting the box edges. -/
lemma shellWitnesses_not_connected_of_roots_not_connected
    {d : ℕ} {L : ℕ} {cfg : Set (Sym2 (LatticePoint d))}
    {x y u v : LatticePoint d}
    (hxu : cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x u)
    (hyv : cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) y v)
    (hxy :
      cfg ∉ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x y) :
    u ≠ v ∧
      cfg ∉
        bondConnectionEvent
          (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) u v := by
  constructor
  · intro huv
    subst huv
    -- Proof comment: if the shell witnesses coincide, concatenating the two root-to-witness paths
    -- already reconnects the original roots.
    exact hxy <|
      hxu.trans <|
        mem_bondConnectionEvent_symm
          (openEdges := fun s : Set (Sym2 (LatticePoint d)) ↦ s) hyv
  · intro huv
    -- Proof comment: an erased-box connection remains an original connection, so joining it with
    -- the root-to-witness paths again contradicts the assumed separation of `x` and `y`.
    exact hxy <|
      hxu.trans <|
        (bondConnectionEvent_eraseBox_subset_id (L := L) huv).trans <|
          mem_bondConnectionEvent_symm
            (openEdges := fun s : Set (Sym2 (LatticePoint d)) ↦ s) hyv

/-- Helper for Theorem 2.46: a canonical exact-two configuration already yields a coarse erased
outside-box two-arm event at some finite scale. -/
lemma clusterCountEqTwo_subset_iUnion_outsideBoxTwoArmEvent :
    {cfg : Set (Sym2 (LatticePoint 2)) |
      infiniteOpenClusterCount
          (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg = 2} ⊆
      ⋃ L : ℕ, outsideBoxTwoArmEvent_config 2 L := by
  intro cfg hcfg
  rcases (infiniteOpenClusterCount_eq_two_iff
      (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).1 hcfg with
    ⟨x, y, hxinf, hyinf, hxy, _hcover⟩
  rcases exists_boxVertices_pred_contains_pair (d := 2) x y with ⟨L, hL, hxBox, hyBox⟩
  rcases existsBoundaryShellInfiniteErasedClusterOfInfiniteCluster
      (d := 2) (L := L) (cfg := cfg) (x := x) hL hxBox hxinf with
    ⟨ux, huxShell, hxux, huxInf⟩
  rcases existsBoundaryShellInfiniteErasedClusterOfInfiniteCluster
      (d := 2) (L := L) (cfg := cfg) (x := y) hL hyBox hyinf with
    ⟨uy, huyShell, hyuy, huyInf⟩
  have hShell :
      ux ≠ uy ∧
        cfg ∉
          bondConnectionEvent
            (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) ux uy :=
    shellWitnesses_not_connected_of_roots_not_connected
      (d := 2) (L := L) hxux hyuy hxy
  rcases hShell with ⟨huxuy, hnotUxUy⟩
  -- Proof comment: choosing a box that contains the two original infinite roots inside `B_{L-1}`
  -- turns the erased shell witnesses into a concrete outside-two-arm witness.
  refine Set.mem_iUnion.2 ⟨L, ?_⟩
  exact ⟨ux, huxShell, uy, huyShell, huxuy, huxInf, huyInf, hnotUxUy⟩

/-- Helper for Theorem 2.46: if the canonical exact-two event has full Bernoulli mass, then one
outside-box two-arm event already has positive mass. -/
lemma exists_pos_measure_outsideBoxTwoArmEvent_of_clusterCountEqTwo_full
    (p : unitInterval)
    (hAfull :
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p
        {cfg : Set (Sym2 (LatticePoint 2)) |
          infiniteOpenClusterCount
              (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg =
            2} = 1) :
    ∃ L : ℕ,
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p
          (outsideBoxTwoArmEvent_config 2 L) := by
  have hcover :
      {cfg : Set (Sym2 (LatticePoint 2)) |
        infiniteOpenClusterCount
            (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg =
          2} ⊆
        ⋃ L : ℕ, outsideBoxTwoArmEvent_config 2 L :=
    clusterCountEqTwo_subset_iUnion_outsideBoxTwoArmEvent
  have hUnionPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p
          (⋃ L : ℕ, outsideBoxTwoArmEvent_config 2 L) := by
    have hmono :
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p
            {cfg : Set (Sym2 (LatticePoint 2)) |
              infiniteOpenClusterCount
                  (openCluster
                    (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg =
                2} ≤
          ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p
            (⋃ L : ℕ, outsideBoxTwoArmEvent_config 2 L) :=
      measure_mono hcover
    rw [hAfull] at hmono
    exact lt_of_lt_of_le zero_lt_one hmono
  -- Proof comment: a positive countable union under a probability measure contains at least one
  -- positive coordinate event.
  exact exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hUnionPos)

/-- Helper for Theorem 2.46: full Bernoulli mass of the canonical exact-two event refines to one
fixed shell witness pair with positive Bernoulli mass. -/
lemma exists_pos_measure_fixedOutsideTwoArmWitness_of_clusterCountEqTwo_full
    (p : unitInterval)
    (hAfull :
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p
        {cfg : Set (Sym2 (LatticePoint 2)) |
          infiniteOpenClusterCount
              (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg =
            2} = 1) :
    ∃ L : ℕ, ∃ x y : LatticePoint 2,
      x ∈ boundaryShell 2 L ∧
      y ∈ boundaryShell 2 L ∧
      x ≠ y ∧
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p
          (outsideBoxTwoArmWitnessEvent_config 2 L x y) := by
  rcases exists_pos_measure_outsideBoxTwoArmEvent_of_clusterCountEqTwo_full p hAfull with
    ⟨L, hPos⟩
  rcases exists_pos_measure_fixedOutsideTwoArmWitness_of_outsideBoxTwoArmEvent_pos
      (d := 2) (p := p) (L := L) hPos with
    ⟨x, y, hxShell, hyShell, hxy, hxyPos⟩
  -- Proof comment: once one outside-two-arm scale has positive mass, the earlier witness
  -- selection lemma already extracts a concrete shell pair.
  exact ⟨L, x, y, hxShell, hyShell, hxy, hxyPos⟩

/-- Helper for Theorem 2.46: once pairwise connection events are measurable, the event that the
open cluster at a fixed site is infinite is measurable as well. -/
lemma measurableSet_infiniteOpenClusterEvent
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (connectionEvent : LatticePoint d → LatticePoint d → Set Ω)
    (hmeas : ∀ x y : LatticePoint d, MeasurableSet (connectionEvent x y))
    (x : LatticePoint d) :
    MeasurableSet {ω | Set.Infinite (openCluster connectionEvent x ω)} := by
  -- Proof comment: rewrite infinitude as the event that the cluster-size random variable hits
  -- `⊤`, then pull back the measurable singleton `{⊤}`.
  have hsize : Measurable (openClusterSize connectionEvent x) :=
    measurable_openClusterSize connectionEvent hmeas x
  have hEq :
      {ω | Set.Infinite (openCluster connectionEvent x ω)} =
        {ω | openClusterSize connectionEvent x ω = ⊤} := by
    ext ω
    -- Proof comment: unfold the cluster-size random variable once and simplify the resulting
    -- `encard = ⊤` statement back to infinitude.
    simpa [openClusterSize_def, Set.encard_eq_top_iff]
  rw [hEq]
  simpa [Set.preimage, eq_comm] using hsize (measurableSet_singleton (⊤ : ℕ∞))

/-- Helper for Theorem 2.46: a finite vertex sequence witnesses a connection in the canonical
configuration space when each consecutive bond is present in the configuration. -/
def pathWitnessEvent_config
    {d : ℕ} (x y : LatticePoint d)
    (w : Σ n : ℕ, Fin (n + 1) → LatticePoint d) :
    Set (Set (Sym2 (LatticePoint d))) :=
  {cfg |
    w.2 0 = x ∧
      w.2 ⟨w.1, Nat.lt_succ_self w.1⟩ = y ∧
      ∀ i : Fin w.1,
        s(w.2 i.castSucc, w.2 i.succ) ∈ cfg ∩ (latticeGraph d).edgeSet}

/-- Helper for Theorem 2.46: the cylinder event attached to a fixed finite witness path is
measurable in the canonical configuration space. -/
lemma measurableSet_pathWitnessEvent_config
    {d : ℕ} (x y : LatticePoint d)
    (w : Σ n : ℕ, Fin (n + 1) → LatticePoint d) :
    MeasurableSet (pathWitnessEvent_config x y w) := by
  classical
  by_cases hx : w.2 0 = x
  · by_cases hy : w.2 ⟨w.1, Nat.lt_succ_self w.1⟩ = y
    · have hsteps :
          MeasurableSet
            {cfg : Set (Sym2 (LatticePoint d)) |
              ∀ i : Fin w.1,
                s(w.2 i.castSucc, w.2 i.succ) ∈ cfg ∩ (latticeGraph d).edgeSet} := by
        -- Proof comment: the fixed witness condition is a finite intersection of one-edge
        -- cylinder events.
        rw [show
          {cfg : Set (Sym2 (LatticePoint d)) |
            ∀ i : Fin w.1,
              s(w.2 i.castSucc, w.2 i.succ) ∈ cfg ∩ (latticeGraph d).edgeSet} =
            ⋂ i : Fin w.1,
              {cfg : Set (Sym2 (LatticePoint d)) |
                s(w.2 i.castSucc, w.2 i.succ) ∈ cfg ∩ (latticeGraph d).edgeSet} by
          ext cfg
          simp]
        exact MeasurableSet.iInter fun i ↦ by
          let e : Sym2 (LatticePoint d) := s(w.2 i.castSucc, w.2 i.succ)
          by_cases he : e ∈ (latticeGraph d).edgeSet
          · simpa [e, he, Set.mem_inter_iff] using
              (measurableSet_mem e : MeasurableSet {cfg : Set (Sym2 (LatticePoint d)) | e ∈ cfg})
          · simp [e, he]
      -- Proof comment: once the endpoints are fixed, only the finite family of edge-membership
      -- constraints remains.
      simpa [pathWitnessEvent_config, hx, hy] using hsteps
    · simp [pathWitnessEvent_config, hx, hy]
  · simp [pathWitnessEvent_config, hx]

/-- Helper for Theorem 2.46: a finite witness path in the canonical configuration space induces
reachability in the corresponding open bond graph. -/
lemma reachableOfPathWitnessEvent_config
    {d : ℕ} (cfg : Set (Sym2 (LatticePoint d))) :
    ∀ {n : ℕ} (v : Fin (n + 1) → LatticePoint d),
      (∀ i : Fin n, s(v i.castSucc, v i.succ) ∈ cfg ∩ (latticeGraph d).edgeSet) →
      (openBondGraph (fun s : Set (Sym2 (LatticePoint d)) ↦ s) cfg).Reachable
        (v 0) (v ⟨n, Nat.lt_succ_self n⟩) := by
  intro n
  induction n with
  | zero =>
      intro v hv
      -- Proof comment: a length-zero witness path starts and ends at the same lattice site.
      change
        (openBondGraph (fun s : Set (Sym2 (LatticePoint d)) ↦ s) cfg).Reachable
          (v 0) (v 0)
      exact SimpleGraph.Reachable.refl (v 0)
  | succ n ihn =>
      intro v hv
      let Gcfg : SimpleGraph (LatticePoint d) :=
        openBondGraph (fun s : Set (Sym2 (LatticePoint d)) ↦ s) cfg
      have hfirst : s(v 0, v 1) ∈ cfg ∩ (latticeGraph d).edgeSet := hv 0
      have hfirstAdjLattice : (latticeGraph d).Adj (v 0) (v 1) := by
        simpa [SimpleGraph.mem_edgeSet] using hfirst.2
      have hfirstAdj : Gcfg.Adj (v 0) (v 1) := by
        -- Proof comment: the first witness step is open because it belongs to
        -- `cfg ∩ (latticeGraph d).edgeSet`.
        change
          (SimpleGraph.fromEdgeSet (cfg ∩ (latticeGraph d).edgeSet)).Adj (v 0) (v 1)
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨hfirst, hfirstAdjLattice.ne⟩
      let tail : Fin (n + 1) → LatticePoint d := fun i ↦ v i.succ
      have htail :
          ∀ i : Fin n, s(tail i.castSucc, tail i.succ) ∈ cfg ∩ (latticeGraph d).edgeSet := by
        intro i
        simpa [tail] using hv i.succ
      have htailReach :
          Gcfg.Reachable (v 1) (v ⟨n + 1, Nat.succ_lt_succ (Nat.lt_succ_self n)⟩) := by
        -- Proof comment: after discarding the first edge, the remaining witness is a shorter
        -- path of the same form.
        simpa [Gcfg, tail] using ihn tail htail
      exact (SimpleGraph.Adj.reachable hfirstAdj).trans htailReach

/-- Helper for Theorem 2.46: the bond-connection event is measurable on the canonical
configuration space. -/
lemma measurableSet_bondConnectionEvent_config
    {d : ℕ} (x y : LatticePoint d) :
    MeasurableSet
      (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x y) := by
  classical
  have hwitness :
      bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x y =
        ⋃ w : Σ n : ℕ, Fin (n + 1) → LatticePoint d, pathWitnessEvent_config x y w := by
    ext cfg
    constructor
    · intro hcfg
      change
        (openBondGraph (fun s : Set (Sym2 (LatticePoint d)) ↦ s) cfg).Reachable x y at hcfg
      rcases hcfg with ⟨p⟩
      refine Set.mem_iUnion.mpr ?_
      refine ⟨⟨p.length, fun i ↦ p.getVert i⟩, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · exact p.getVert_zero
      · exact p.getVert_length
      · intro i
        -- Proof comment: each consecutive edge of the witness walk is an open lattice bond.
        have hadj := p.adj_getVert_succ (show (i : ℕ) < p.length by exact i.2)
        change
          (SimpleGraph.fromEdgeSet (cfg ∩ (latticeGraph d).edgeSet)).Adj
            (p.getVert i) (p.getVert (i + 1)) at hadj
        rw [SimpleGraph.fromEdgeSet_adj] at hadj
        exact hadj.1
    · intro hcfg
      rcases Set.mem_iUnion.mp hcfg with ⟨w, hw⟩
      rcases w with ⟨n, v⟩
      rcases hw with ⟨hx, hy, hv⟩
      have hreach := reachableOfPathWitnessEvent_config cfg v hv
      change
        (openBondGraph (fun s : Set (Sym2 (LatticePoint d)) ↦ s) cfg).Reachable x y
      exact hx ▸ hy ▸ hreach
  rw [hwitness]
  exact MeasurableSet.iUnion fun w ↦ measurableSet_pathWitnessEvent_config x y w

/-- Helper for Theorem 2.46: after deleting a fixed finite box of edges, the corresponding
connection event is still measurable on canonical configurations. -/
lemma measurableSet_bondConnectionEvent_config_eraseBox
    {d : ℕ} (L : ℕ) (x y : LatticePoint d) :
    MeasurableSet
      (bondConnectionEvent
        (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) x y) := by
  let eraseBox : Set (Sym2 (LatticePoint d)) → Set (Sym2 (LatticePoint d)) :=
    fun cfg ↦ cfg \ boxEdges d L
  have hrewrite :
      bondConnectionEvent
          (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) x y =
        eraseBox ⁻¹' bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x y := by
    rfl
  -- Proof comment: box erasure is measurable, so the erased connection event is a measurable
  -- preimage of the canonical connection event.
  rw [hrewrite]
  exact measurableSet_preimage
    (measurable_eraseEdges_config (d := d) (boxEdges d L))
    (measurableSet_bondConnectionEvent_config x y)

/-- Helper for Theorem 2.46: applying the erased-box connection event to an already erased
configuration changes nothing. -/
lemma bondConnectionEvent_eraseBox_idem_iff
    {d : ℕ} (L : ℕ) (x y : LatticePoint d) (cfg : Set (Sym2 (LatticePoint d))) :
    cfg \ boxEdges d L ∈
        bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) x y ↔
      cfg ∈
        bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) x y := by
  -- Proof comment: erasing the same finite box twice does not change the resulting open bond
  -- graph, so the connection predicate is unchanged.
  simp [bondConnectionEvent, openBondGraph]

/-- Helper for Theorem 2.46: evaluating erased-box open clusters on an already erased
configuration gives the same cluster. -/
lemma openCluster_eraseBox_idem_eq
    {d : ℕ} (L : ℕ) (x : LatticePoint d) (cfg : Set (Sym2 (LatticePoint d))) :
    openCluster
        (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L))
        x (cfg \ boxEdges d L) =
      openCluster
        (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L))
        x cfg := by
  -- Proof comment: cluster membership is exactly the erased-box connection event, so the
  -- idempotence statement is pointwise the previous connectivity lemma.
  ext y
  simpa [openCluster] using bondConnectionEvent_eraseBox_idem_iff (d := d) L x y cfg

/-- Helper for Theorem 2.46: fixing the two shell witnesses gives a measurable event, because only
the erased infinite-cluster tests and one erased non-connection test vary with the configuration. -/
lemma measurableSet_outsideBoxTwoArmWitnessEvent_config
    (d : ℕ) (L : ℕ) (x y : LatticePoint d) :
    MeasurableSet (outsideBoxTwoArmWitnessEvent_config d L x y) := by
  let conn : LatticePoint d → LatticePoint d → Set (Set (Sym2 (LatticePoint d))) :=
    bondConnectionEvent
      (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L)
  let infOutside : LatticePoint d → Set (Set (Sym2 (LatticePoint d))) :=
    fun z ↦ {cfg | Set.Infinite (openCluster conn z cfg)}
  have hconn : ∀ z w : LatticePoint d, MeasurableSet (conn z w) := by
    intro z w
    exact measurableSet_bondConnectionEvent_config_eraseBox (d := d) L z w
  have hinf : ∀ z : LatticePoint d, MeasurableSet (infOutside z) := by
    intro z
    exact measurableSet_infiniteOpenClusterEvent conn hconn z
  have hrewrite :
      outsideBoxTwoArmWitnessEvent_config d L x y =
        {cfg | x ∈ boundaryShell d L ∧ y ∈ boundaryShell d L ∧ x ≠ y} ∩
          (infOutside x ∩ (infOutside y ∩ (conn x y)ᶜ)) := by
    ext cfg
    constructor
    · rintro ⟨hx, hy, hxy, hxinf, hyinf, hnotconn⟩
      exact ⟨⟨hx, hy, hxy⟩, ⟨hxinf, ⟨hyinf, hnotconn⟩⟩⟩
    · rintro ⟨hxy, hxrest⟩
      rcases hxrest with ⟨hxinf, hyrest⟩
      rcases hyrest with ⟨hyinf, hnotconn⟩
      exact ⟨hxy.1, hxy.2.1, hxy.2.2, hxinf, hyinf, hnotconn⟩
  rw [hrewrite]
  have hconst :
      MeasurableSet
        ({cfg : Set (Sym2 (LatticePoint d)) |
          x ∈ boundaryShell d L ∧ y ∈ boundaryShell d L ∧ x ≠ y}) := by
    by_cases hxy : x ∈ boundaryShell d L ∧ y ∈ boundaryShell d L ∧ x ≠ y
    · simp [hxy]
    · simp [hxy]
  -- Proof comment: with fixed shell witnesses, the event is a finite intersection of measurable
  -- erased-cluster and erased-connection constraints.
  exact hconst.inter ((hinf x).inter ((hinf y).inter (hconn x y).compl))

/-- Helper for Theorem 2.46: erasing `boxEdges d L` again does not change a fixed two-arm witness
event, because that witness event already depends only on the erased outside configuration. -/
lemma eraseEdges_preimage_outsideBoxTwoArmWitnessEvent_config
    (d : ℕ) (L : ℕ) (x y : LatticePoint d) :
    (fun cfg : Set (Sym2 (LatticePoint d)) ↦ cfg \ boxEdges d L) ⁻¹'
        outsideBoxTwoArmWitnessEvent_config d L x y =
      outsideBoxTwoArmWitnessEvent_config d L x y := by
  -- Proof comment: the shell conditions are constant and the erased-cluster / erased-connection
  -- predicates are idempotent under a second deletion of `boxEdges d L`.
  ext cfg
  simp only [outsideBoxTwoArmWitnessEvent_config, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hy, hxy, hxinf, hyinf, hnotconn⟩
    refine ⟨hx, hy, hxy, ?_, ?_, ?_⟩
    · simpa [openCluster_eraseBox_idem_eq (d := d) L x cfg] using hxinf
    · simpa [openCluster_eraseBox_idem_eq (d := d) L y cfg] using hyinf
    · intro hconn
      exact hnotconn ((bondConnectionEvent_eraseBox_idem_iff (d := d) L x y cfg).2 hconn)
  · rintro ⟨hx, hy, hxy, hxinf, hyinf, hnotconn⟩
    refine ⟨hx, hy, hxy, ?_, ?_, ?_⟩
    · simpa [openCluster_eraseBox_idem_eq (d := d) L x cfg] using hxinf
    · simpa [openCluster_eraseBox_idem_eq (d := d) L y cfg] using hyinf
    · intro hconn
      exact hnotconn ((bondConnectionEvent_eraseBox_idem_iff (d := d) L x y cfg).1 hconn)

/-- Helper for Theorem 2.46: the outside-box two-arm event is measurable because it is a countable
union of measurable fixed-witness events. -/
lemma measurableSet_outsideBoxTwoArmEvent_config
    (d : ℕ) (L : ℕ) :
    MeasurableSet (outsideBoxTwoArmEvent_config d L) := by
  classical
  -- Proof comment: normalize the coarse event to the fixed-witness union before doing any
  -- measurability work.
  rw [outsideBoxTwoArmEvent_config_eq_iUnion_witness]
  exact MeasurableSet.iUnion fun x ↦
    MeasurableSet.iUnion fun y ↦
      measurableSet_outsideBoxTwoArmWitnessEvent_config d L x y

/-- Helper for Theorem 2.46: erasing `boxEdges d L` twice does not change the coarse outside-box
two-arm event, because every fixed witness event is already erase-stable. -/
lemma eraseEdges_preimage_outsideBoxTwoArmEvent_config
    (d : ℕ) (L : ℕ) :
    (fun cfg : Set (Sym2 (LatticePoint d)) ↦ cfg \ boxEdges d L) ⁻¹'
        outsideBoxTwoArmEvent_config d L =
      outsideBoxTwoArmEvent_config d L := by
  -- Proof comment: after normalizing to fixed witnesses, the coarse event is stable because each
  -- witness event is already stable under a second box erasure.
  ext cfg
  simp only [outsideBoxTwoArmEvent_config_eq_iUnion_witness, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hxcfg⟩
    rcases hxcfg with ⟨y, hycfg⟩
    refine ⟨x, ?_⟩
    refine ⟨y, ?_⟩
    have hw :
        cfg \ boxEdges d L ∈ outsideBoxTwoArmWitnessEvent_config d L x y ↔
          cfg ∈ outsideBoxTwoArmWitnessEvent_config d L x y := by
      change cfg ∈
          (fun cfg : Set (Sym2 (LatticePoint d)) ↦ cfg \ boxEdges d L) ⁻¹'
            outsideBoxTwoArmWitnessEvent_config d L x y ↔
        cfg ∈ outsideBoxTwoArmWitnessEvent_config d L x y
      rw [eraseEdges_preimage_outsideBoxTwoArmWitnessEvent_config (d := d) L x y]
    exact hw.mp hycfg
  · rintro ⟨x, hxcfg⟩
    rcases hxcfg with ⟨y, hycfg⟩
    refine ⟨x, ?_⟩
    refine ⟨y, ?_⟩
    have hw :
        cfg \ boxEdges d L ∈ outsideBoxTwoArmWitnessEvent_config d L x y ↔
          cfg ∈ outsideBoxTwoArmWitnessEvent_config d L x y := by
      change cfg ∈
          (fun cfg : Set (Sym2 (LatticePoint d)) ↦ cfg \ boxEdges d L) ⁻¹'
            outsideBoxTwoArmWitnessEvent_config d L x y ↔
        cfg ∈ outsideBoxTwoArmWitnessEvent_config d L x y
      rw [eraseEdges_preimage_outsideBoxTwoArmWitnessEvent_config (d := d) L x y]
    exact hw.mpr hycfg

/-- Helper for Theorem 2.46: the canonical exact-two event is measurable after normalizing it to
countably many root witnesses. -/
lemma measurableSet_clusterCountEqTwo_config :
    MeasurableSet
      {cfg : Set (Sym2 (LatticePoint 2)) |
        infiniteOpenClusterCount
            (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg = 2} := by
  classical
  let E :=
    fun x y : LatticePoint 2 ↦
      {cfg : Set (Sym2 (LatticePoint 2)) |
        Set.Infinite
            (openCluster
              (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
              x cfg) ∧
          Set.Infinite
              (openCluster
                (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
                y cfg) ∧
          cfg ∉ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) x y ∧
          ∀ z : LatticePoint 2,
            Set.Infinite
                (openCluster
                  (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
                  z cfg) →
              cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z x ∨
                cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z y}
  have hInfinite :
      ∀ x : LatticePoint 2,
        MeasurableSet
          {cfg : Set (Sym2 (LatticePoint 2)) |
            Set.Infinite
              (openCluster
                (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
                x cfg)} := by
    intro x
    exact measurableSet_infiniteOpenClusterEvent
      (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
      measurableSet_bondConnectionEvent_config
      x
  have hWitness :
      ∀ x y : LatticePoint 2, MeasurableSet (E x y) := by
    intro x y
    have hCover :
        MeasurableSet
          {cfg : Set (Sym2 (LatticePoint 2)) |
            ∀ z : LatticePoint 2,
              Set.Infinite
                  (openCluster
                    (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
                    z cfg) →
                cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z x ∨
                  cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z y} := by
      have hEqCover :
          {cfg : Set (Sym2 (LatticePoint 2)) |
            ∀ z : LatticePoint 2,
              Set.Infinite
                  (openCluster
                    (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
                    z cfg) →
                cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z x ∨
                  cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z y} =
            ⋂ z : LatticePoint 2,
              {cfg : Set (Sym2 (LatticePoint 2)) |
                Set.Infinite
                    (openCluster
                      (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
                      z cfg) →
                  cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z x ∨
                    cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z y} := by
        ext cfg
        simp
      rw [hEqCover]
      refine MeasurableSet.iInter fun z ↦ ?_
      -- Proof comment: each cover clause is one implication between measurable events, so rewrite
      -- it as a union of measurable pieces.
      have hImp :
          {cfg : Set (Sym2 (LatticePoint 2)) |
            Set.Infinite
                (openCluster
                  (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
                  z cfg) →
              cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z x ∨
                cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z y} =
            {cfg : Set (Sym2 (LatticePoint 2)) |
              ¬ Set.Infinite
                    (openCluster
                      (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
                      z cfg) ∨
                cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z x ∨
                  cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z y} := by
        ext cfg
        simp [imp_iff_not_or, or_assoc]
      rw [hImp]
      exact
        (hInfinite z).compl.union <|
          (measurableSet_bondConnectionEvent_config z x).union
            (measurableSet_bondConnectionEvent_config z y)
    -- Proof comment: a fixed exact-two witness is a finite conjunction of measurable infinitude
    -- tests, one non-connection test, and the measurable cover condition.
    exact (hInfinite x).inter <|
      (hInfinite y).inter <|
        (measurableSet_bondConnectionEvent_config x y).compl.inter hCover
  have hEq :
      {cfg : Set (Sym2 (LatticePoint 2)) |
        infiniteOpenClusterCount
            (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg = 2} =
        ⋃ x : LatticePoint 2, ⋃ y : LatticePoint 2, E x y := by
    ext cfg
    simp [E, infiniteOpenClusterCount_eq_two_iff]
  rw [hEq]
  exact MeasurableSet.iUnion fun x ↦ MeasurableSet.iUnion fun y ↦ hWitness x y

/-- Helper for Theorem 2.46: updating one coordinate of a box vertex by another value still
inside `[-L, L]` keeps the updated vertex inside the same box. -/
lemma boxVertices_update_mem
    {d : ℕ} {x : LatticePoint d} {L : ℕ} (hx : x ∈ boxVertices d L)
    (i : Fin d) {z : ℤ} (hz : z ∈ Set.Icc (-(L : ℤ)) (L : ℤ)) :
    Function.update x i z ∈ boxVertices d L := by
  -- Proof comment: only the `i`-th coordinate changes, and the new coordinate still lies in the
  -- defining interval of `B_L`.
  intro j
  by_cases hji : j = i
  · subst hji
    simpa using hz
  · simpa [Function.update, hji] using hx j

/-- Helper for Theorem 2.46: two box vertices that differ by one positive unit step in one
coordinate are adjacent in the box graph. -/
lemma boxGraph_adj_update_succ
    {d : ℕ} {x : LatticePoint d} {L : ℕ} (hx : x ∈ boxVertices d L)
    (i : Fin d) {z : ℤ}
    (hz : z ∈ Set.Icc (-(L : ℤ)) (L : ℤ))
    (hz' : z + 1 ∈ Set.Icc (-(L : ℤ)) (L : ℤ)) :
    (SimpleGraph.fromEdgeSet (boxEdges d L)).Adj
      (Function.update x i z) (Function.update x i (z + 1)) := by
  let xz : LatticePoint d := Function.update x i z
  let xz' : LatticePoint d := Function.update x i (z + 1)
  have hxz : xz ∈ boxVertices d L := boxVertices_update_mem (d := d) hx i hz
  have hxz' : xz' ∈ boxVertices d L := boxVertices_update_mem (d := d) hx i hz'
  have hadj : (latticeGraph d).Adj xz xz' := by
    -- Proof comment: the two updated vertices differ only in the `i`-th coordinate by exactly
    -- one unit.
    rw [latticeGraph_adj_iff]
    refine ⟨i, ?_, ?_⟩
    · simp [xz, xz']
    · intro j hj
      simp [xz, xz', hj]
  change (SimpleGraph.fromEdgeSet (boxEdges d L)).Adj xz xz'
  rw [SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, hadj.ne⟩
  exact ⟨xz, hxz, xz', hxz', rfl, hadj⟩

/-- Helper for Theorem 2.46: two box vertices that differ by one negative unit step in one
coordinate are adjacent in the box graph. -/
lemma boxGraph_adj_update_pred
    {d : ℕ} {x : LatticePoint d} {L : ℕ} (hx : x ∈ boxVertices d L)
    (i : Fin d) {z : ℤ}
    (hz : z ∈ Set.Icc (-(L : ℤ)) (L : ℤ))
    (hz' : z - 1 ∈ Set.Icc (-(L : ℤ)) (L : ℤ)) :
    (SimpleGraph.fromEdgeSet (boxEdges d L)).Adj
      (Function.update x i z) (Function.update x i (z - 1)) := by
  let xz : LatticePoint d := Function.update x i z
  let xz' : LatticePoint d := Function.update x i (z - 1)
  have hxz : xz ∈ boxVertices d L := boxVertices_update_mem (d := d) hx i hz
  have hxz' : xz' ∈ boxVertices d L := boxVertices_update_mem (d := d) hx i hz'
  have hadj : (latticeGraph d).Adj xz xz' := by
    -- Proof comment: the two updated vertices differ only in the `i`-th coordinate by exactly
    -- one unit in the negative direction.
    rw [latticeGraph_adj_iff]
    refine ⟨i, ?_, ?_⟩
    · simp [xz, xz']
    · intro j hj
      simp [xz, xz', hj]
  change (SimpleGraph.fromEdgeSet (boxEdges d L)).Adj xz xz'
  rw [SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, hadj.ne⟩
  exact ⟨xz, hxz, xz', hxz', rfl, hadj⟩

/-- Helper for Theorem 2.46: moving one coordinate of a box vertex while staying inside the box
produces a path in the box graph. -/
lemma boxVertices_reachable_updateWithinBox
    {d : ℕ} {x : LatticePoint d} {L : ℕ} (hx : x ∈ boxVertices d L)
    (i : Fin d) {z : ℤ} (hz : z ∈ Set.Icc (-(L : ℤ)) (L : ℤ)) :
    (SimpleGraph.fromEdgeSet (boxEdges d L)).Reachable x (Function.update x i z) := by
  let Gbox : SimpleGraph (LatticePoint d) := SimpleGraph.fromEdgeSet (boxEdges d L)
  have hxi : x i ∈ Set.Icc (-(L : ℤ)) (L : ℤ) := hx i
  by_cases hxiz : x i ≤ z
  · let n : ℕ := Int.toNat (z - x i)
    have hforward :
        ∀ m : ℕ,
          x i + m ∈ Set.Icc (-(L : ℤ)) (L : ℤ) →
            Gbox.Reachable x (Function.update x i (x i + m)) := by
      intro m
      induction m with
      | zero =>
          intro _hm
          -- Proof comment: the zero-step walk leaves the vertex unchanged.
          simp [Gbox]
      | succ m ihm =>
          intro hm
          have hm_prev : x i + m ∈ Set.Icc (-(L : ℤ)) (L : ℤ) := by
            refine ⟨?_, ?_⟩
            · exact le_trans hxi.1 (by omega)
            · exact le_trans (by omega) hm.2
          have hreach : Gbox.Reachable x (Function.update x i (x i + m)) := ihm hm_prev
          have hadj :
              Gbox.Adj (Function.update x i (x i + m))
                (Function.update x i (x i + (m + 1))) := by
            have hm_succ : x i + m + 1 ∈ Set.Icc (-(L : ℤ)) (L : ℤ) := by
              simpa [Nat.cast_add, add_assoc] using hm
            simpa [Gbox, Nat.cast_add, add_assoc] using
              boxGraph_adj_update_succ (d := d) hx i hm_prev hm_succ
          exact hreach.trans (SimpleGraph.Adj.reachable hadj)
    have hn_eq : (n : ℤ) = z - x i := by
      simp [n, Int.toNat_of_nonneg (sub_nonneg.mpr hxiz)]
    have hz_eq : x i + n = z := by
      rw [hn_eq]
      omega
    -- Proof comment: march the `i`-th coordinate forward one unit at a time until it reaches
    -- `z`.
    simpa [hz_eq, Gbox] using hforward n (by simpa [hz_eq] using hz)
  · have hzx : z ≤ x i := le_of_not_ge hxiz
    let n : ℕ := Int.toNat (x i - z)
    have hbackward :
        ∀ m : ℕ,
          x i - m ∈ Set.Icc (-(L : ℤ)) (L : ℤ) →
            Gbox.Reachable x (Function.update x i (x i - m)) := by
      intro m
      induction m with
      | zero =>
          intro _hm
          -- Proof comment: the zero-step walk again leaves the vertex unchanged.
          simp [Gbox]
      | succ m ihm =>
          intro hm
          have hm_prev : x i - m ∈ Set.Icc (-(L : ℤ)) (L : ℤ) := by
            refine ⟨?_, ?_⟩
            · exact le_trans hm.1 (by omega)
            · exact le_trans (by omega) hxi.2
          have hreach : Gbox.Reachable x (Function.update x i (x i - m)) := ihm hm_prev
          have hadj :
              Gbox.Adj (Function.update x i (x i - m))
                (Function.update x i (x i - (m + 1))) := by
            have hm_succ : x i - m - 1 ∈ Set.Icc (-(L : ℤ)) (L : ℤ) := by
              simpa [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hm
            simpa [Gbox, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              boxGraph_adj_update_pred (d := d) hx i hm_prev hm_succ
          exact hreach.trans (SimpleGraph.Adj.reachable hadj)
    have hn_eq : (n : ℤ) = x i - z := by
      simp [n, Int.toNat_of_nonneg (sub_nonneg.mpr hzx)]
    have hz_eq : x i - n = z := by
      rw [hn_eq]
      omega
    -- Proof comment: the same coordinate walk works backward when `z ≤ x i`.
    simpa [hz_eq, Gbox] using hbackward n (by simpa [hz_eq] using hz)

/-- Helper for Theorem 2.46: any two vertices of `B_L` are connected by box edges alone. -/
lemma boxVertices_reachableWithinBox
    {d : ℕ} {x y : LatticePoint d} {L : ℕ}
    (hx : x ∈ boxVertices d L) (hy : y ∈ boxVertices d L) :
    (SimpleGraph.fromEdgeSet (boxEdges d L)).Reachable x y := by
  let Gbox : SimpleGraph (LatticePoint d) := SimpleGraph.fromEdgeSet (boxEdges d L)
  have hstep :
      ∀ s : Finset (Fin d),
        Gbox.Reachable x (fun j ↦ if j ∈ s then y j else x j) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · -- Proof comment: with no coordinates updated, the intermediate vertex is just `x`.
      simp [Gbox]
    · intro i s hi hs
      let zs : LatticePoint d := fun j ↦ if j ∈ s then y j else x j
      have hzs : zs ∈ boxVertices d L := by
        intro j
        by_cases hjs : j ∈ s
        · simpa [zs, hjs] using hy j
        · simpa [zs, hjs] using hx j
      have hreach : Gbox.Reachable x zs := hs
      have hupdate :
          (fun j ↦ if j ∈ insert i s then y j else x j) = Function.update zs i (y i) := by
        -- Proof comment: inserting `i` updates exactly one coordinate of the current
        -- intermediate vertex.
        ext j
        by_cases hji : j = i
        · subst hji
          simp [zs, hi]
        · by_cases hjs : j ∈ s
          · simp [zs, hji, hjs]
          · simp [zs, hji, hjs]
      rw [hupdate]
      have hyi : y i ∈ Set.Icc (-(L : ℤ)) (L : ℤ) := hy i
      exact hreach.trans (boxVertices_reachable_updateWithinBox (d := d) hzs i hyi)
  -- Proof comment: after updating every coordinate, the intermediate vertex becomes `y`.
  simpa [Gbox] using hstep Finset.univ

/-- Helper for Theorem 2.46: every shell vertex of `B_L` already lies in the enclosing box
`B_L`. -/
lemma mem_boxVertices_of_mem_boundaryShell
    {d : ℕ} {x : LatticePoint d} {L : ℕ} (hx : x ∈ boundaryShell d L) :
    x ∈ boxVertices d L :=
  hx.1

/-- Helper for Theorem 2.46: if every edge of `boxEdges d L` is open, then any two vertices of
`B_L` are connected in the full configuration. -/
lemma bondConnectionEvent_of_boxVertices_allOpenBox
    {d : ℕ} {L : ℕ} {cfg : Set (Sym2 (LatticePoint d))} {x y : LatticePoint d}
    (hx : x ∈ boxVertices d L) (hy : y ∈ boxVertices d L)
    (hall : boxEdges d L ⊆ cfg) :
    cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x y := by
  have hle :
      SimpleGraph.fromEdgeSet (boxEdges d L) ≤
        openBondGraph (fun s : Set (Sym2 (LatticePoint d)) ↦ s) cfg := by
    intro u v huv
    change (SimpleGraph.fromEdgeSet (cfg ∩ (latticeGraph d).edgeSet)).Adj u v
    rw [SimpleGraph.fromEdgeSet_adj] at huv ⊢
    exact ⟨⟨hall huv.1, boxEdges_subset_edgeSet d L huv.1⟩, huv.2⟩
  -- Proof comment: the deterministic path inside the box remains open because all box edges are
  -- present in `cfg`.
  exact SimpleGraph.Reachable.mono hle (boxVertices_reachableWithinBox (d := d) hx hy)

/-- Helper for Theorem 2.46: if every box edge is open, then any two shell vertices are connected
in the full configuration as well. -/
lemma bondConnectionEvent_of_boundaryShell_allOpenBox
    {d : ℕ} {L : ℕ} {cfg : Set (Sym2 (LatticePoint d))} {x y : LatticePoint d}
    (hx : x ∈ boundaryShell d L) (hy : y ∈ boundaryShell d L)
    (hall : boxEdges d L ⊆ cfg) :
    cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x y := by
  -- Proof comment: shell vertices are box vertices, so the stronger box-connectivity lemma
  -- applies directly.
  exact
    bondConnectionEvent_of_boxVertices_allOpenBox
      (d := d)
      (mem_boxVertices_of_mem_boundaryShell hx)
      (mem_boxVertices_of_mem_boundaryShell hy)
      hall

/-- Helper for Theorem 2.46: if no edge of `boxEdges d L` is open, then deleting those edges does
nothing to the configuration. -/
lemma eraseBox_eq_self_of_inter_boxEdges_eq_empty
    {d : ℕ} (L : ℕ) {cfg : Set (Sym2 (LatticePoint d))}
    (hcfg : cfg ∩ boxEdges d L = ∅) :
    cfg \ boxEdges d L = cfg := by
  -- Proof comment: deleting a family of edges that is absent from `cfg` leaves `cfg`
  -- unchanged.
  ext e
  by_cases he : e ∈ boxEdges d L
  · have hnot : e ∉ cfg := by
      intro heCfg
      have : e ∈ (∅ : Set (Sym2 (LatticePoint d))) := by
        rw [← hcfg]
        exact ⟨heCfg, he⟩
      simp at this
    simp [he, hnot]
  · simp [he]

/-- Helper for Theorem 2.46: if the open cluster of `z` never reaches `B_L`, then deleting the box
edges does not change connections from `z`. -/
lemma bondConnectionEvent_eraseBox_iff_of_no_connection_to_box
    {L : ℕ} {cfg : Set (Sym2 (LatticePoint 2))} {z y : LatticePoint 2}
    (hno :
      ∀ w : LatticePoint 2, w ∈ boxVertices 2 L →
        cfg ∉ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z w) :
    cfg ∈ bondConnectionEvent
        (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) z y ↔
      cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z y := by
  constructor
  · intro hzy
    exact bondConnectionEvent_eraseBox_subset_id (d := 2) (L := L) hzy
  · intro hzy
    let Gcfg : SimpleGraph (LatticePoint 2) :=
      openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg
    rcases hzy with ⟨p⟩
    have hNoBoxEdges : ∀ e, e ∈ p.edges → e ∉ boxEdges 2 L := by
      intro e he hed
      rcases hed with ⟨u, huBox, _v, _hvBox, rfl, _huvAdj⟩
      have huSupport : u ∈ p.support := p.fst_mem_support_of_mem_edges he
      have hzuReach : Gcfg.Reachable z u := (p.takeUntil u huSupport).reachable
      have hzu :
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z u := by
        change Gcfg.Reachable z u
        simpa [Gcfg] using hzuReach
      exact hno u huBox hzu
    have hdeleteReach : (Gcfg.deleteEdges (boxEdges 2 L)).Reachable z y := by
      exact (p.toDeleteEdges (boxEdges 2 L) hNoBoxEdges).reachable
    have hdeleteEq :
        Gcfg.deleteEdges (boxEdges 2 L) =
          openBondGraph
            (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) cfg := by
      change
        (SimpleGraph.fromEdgeSet (cfg ∩ (latticeGraph 2).edgeSet)).deleteEdges (boxEdges 2 L) =
          SimpleGraph.fromEdgeSet ((cfg \ boxEdges 2 L) ∩ (latticeGraph 2).edgeSet)
      rw [SimpleGraph.deleteEdges_fromEdgeSet]
      have hsetEq :
          (cfg ∩ (latticeGraph 2).edgeSet) \ boxEdges 2 L =
            (cfg \ boxEdges 2 L) ∩ (latticeGraph 2).edgeSet := by
        ext e
        by_cases hcfg : e ∈ cfg <;> by_cases hedge : e ∈ (latticeGraph 2).edgeSet <;>
            by_cases hbox : e ∈ boxEdges 2 L <;>
            simp [Set.mem_diff, hcfg, hedge, hbox, and_assoc]
      rw [hsetEq]
    -- Proof comment: once the witness path avoids all deleted edges, it survives unchanged in the
    -- erased open graph.
    change
      (openBondGraph
        (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) cfg).Reachable z y
    rwa [hdeleteEq] at hdeleteReach

/-- Helper for Theorem 2.46: every infinite original cluster contains a root whose erased-box
cluster is still infinite. -/
lemma existsErasedInfiniteRootOfInfiniteCluster
    {L : ℕ} {cfg : Set (Sym2 (LatticePoint 2))} {z : LatticePoint 2}
    (_hL : 0 < L)
    (hzinf :
      Set.Infinite
        (openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s)) z cfg)) :
    ∃ t : LatticePoint 2,
      cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z t ∧
      Set.Infinite
        (openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L)) t cfg) := by
  by_cases hmeet :
      ∃ w : LatticePoint 2, w ∈ boxVertices 2 L ∧
        cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z w
  · rcases hmeet with ⟨w, hwBox, hzw⟩
    have hwinf :
        Set.Infinite
          (openCluster
            (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
            w cfg) := by
      have hEq :=
        (openCluster_eq_iff_bondConnected
          (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z w cfg).2 hzw
      simpa [hEq] using hzinf
    rcases existsBoundaryShellInfiniteErasedClusterOfInfiniteCluster
        (d := 2) (L := L + 1) (cfg := cfg) (x := w) (Nat.succ_pos L)
        (by simpa using hwBox)
        hwinf with
      ⟨t, _htShell, hwt, htinfSucc⟩
    refine ⟨t, ?_, ?_⟩
    · change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable z t
      change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable z w at hzw
      change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable w t at hwt
      exact hzw.trans hwt
    · have hBoxMono : boxEdges 2 L ⊆ boxEdges 2 (L + 1) := by
        intro e he
        rcases he with ⟨u, hu, v, hv, rfl, huv⟩
        exact ⟨u,
          boxVertices_mono (d := 2) (L := L) (M := L + 1) (Nat.le_succ L) hu,
          v,
          boxVertices_mono (d := 2) (L := L) (M := L + 1) (Nat.le_succ L) hv,
          rfl, huv⟩
      have hsubset :
          ((cfg \ boxEdges 2 (L + 1)) ∩ (latticeGraph 2).edgeSet) ⊆
            ((cfg \ boxEdges 2 L) ∩ (latticeGraph 2).edgeSet) := by
        intro e he
        simp [Set.mem_diff, and_assoc] at he ⊢
        refine ⟨he.1, ?_, he.2.2⟩
        intro heL
        exact he.2.1 (hBoxMono heL)
      have hmono :
          openBondGraph
              (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 (L + 1))
              cfg ≤
            openBondGraph
              (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L)
              cfg :=
        SimpleGraph.fromEdgeSet_mono hsubset
      have hclusterSubset :
          openCluster
              (bondConnectionEvent
                (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 (L + 1)))
              t cfg ⊆
            openCluster
              (bondConnectionEvent
                (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L))
              t cfg := by
        intro y hy
        exact SimpleGraph.Reachable.mono hmono hy
      -- Proof comment: deleting fewer box edges only enlarges the erased cluster, so the
      -- infinite witness from radius `L + 1` remains infinite at radius `L`.
      exact htinfSucc.mono hclusterSubset
  · refine ⟨z, ?_, ?_⟩
    · change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable z z
      exact SimpleGraph.Reachable.refl z
    · have hno :
          ∀ w : LatticePoint 2, w ∈ boxVertices 2 L →
            cfg ∉ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z w := by
        intro w hwBox hzw
        exact hmeet ⟨w, hwBox, hzw⟩
      have hclusterEq :
          openCluster
              (bondConnectionEvent
                (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L))
              z cfg =
            openCluster
              (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
              z cfg := by
        ext y
        rw [openCluster_mem_iff, openCluster_mem_iff]
        exact bondConnectionEvent_eraseBox_iff_of_no_connection_to_box hno
      -- Proof comment: if the cluster never meets the box, then erasing box edges changes
      -- nothing about that cluster.
      simpa [hclusterEq] using hzinf

/-- Helper for Theorem 2.46: if the canonical exact-two event has full Bernoulli measure, then the
same remains true after erasing a fixed finite box of edges. -/
lemma eraseBoxClusterCountEqTwo_full_of_clusterCountEqTwo_full
    (p : unitInterval) (hp0 : p ≠ 0) (hp1 : p ≠ 1) (L : ℕ)
    (hAfull :
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p
        {cfg : Set (Sym2 (LatticePoint 2)) |
          infiniteOpenClusterCount
              (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg =
            2} = 1) :
    ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p
      ((fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg \ boxEdges 2 L) ⁻¹'
        {cfg : Set (Sym2 (LatticePoint 2)) |
          infiniteOpenClusterCount
              (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg =
            2}) = 1 := by
  classical
  let μ : Measure (Set (Sym2 (LatticePoint 2))) :=
    ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p
  let μprob : ProbabilityMeasure (Set (Sym2 (LatticePoint 2))) := ⟨μ, inferInstance⟩
  let Aexact : Set (Set (Sym2 (LatticePoint 2))) :=
    {cfg : Set (Sym2 (LatticePoint 2)) |
      infiniteOpenClusterCount
          (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg = 2}
  let C0 : Set (Set (Sym2 (LatticePoint 2))) := {cfg | cfg ∩ boxEdges 2 L = ∅}
  let erase : Set (Sym2 (LatticePoint 2)) → Set (Sym2 (LatticePoint 2)) :=
    fun cfg ↦ cfg \ boxEdges 2 L
  have hAmeas : MeasurableSet Aexact := by
    simpa [Aexact] using measurableSet_clusterCountEqTwo_config
  have hExactCompl : μ Aexactᶜ = 0 := by
    -- Proof comment: full mass of the exact-two event makes its complement null.
    have hCompl : μ Aexactᶜ = μ Set.univ - μ Aexact :=
      measure_compl hAmeas (by
        have : μ Aexact = 1 := by
          simpa [μ, Aexact] using hAfull
        rw [this]
        exact ENNReal.one_ne_top)
    have hAfull' : μ Aexact = 1 := by
      simpa [μ, Aexact] using hAfull
    rw [hAfull'] at hCompl
    simpa [μ] using hCompl
  have hC0pos : 0 < μ C0 := by
    -- Proof comment: the all-closed box cylinder is a positive finite pattern in the strict
    -- interior Bernoulli regime.
    simpa [μ, C0] using
      finiteCylinderAllClosedPos
        (μ := μprob)
        (openEdges := fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg)
        (p := p) hp0 hp1
        (canonicalBernoulli_id_isSetBernoulli p)
        (boxEdges_finite 2 L) (boxEdges_subset_edgeSet 2 L)
  have hEraseOnC0 :
      (erase ⁻¹' Aexact) ∩ C0 = Aexact ∩ C0 := by
    -- Proof comment: on the all-closed box cylinder, erasing `boxEdges 2 L` is the identity.
    ext cfg
    constructor
    · rintro ⟨hcfg, hclosed⟩
      refine ⟨?_, hclosed⟩
      have herase : erase cfg = cfg := by
        simpa [erase] using eraseBox_eq_self_of_inter_boxEdges_eq_empty (d := 2) L hclosed
      simpa [herase] using hcfg
    · rintro ⟨hcfg, hclosed⟩
      refine ⟨?_, hclosed⟩
      have herase : erase cfg = cfg := by
        simpa [erase] using eraseBox_eq_self_of_inter_boxEdges_eq_empty (d := 2) L hclosed
      simpa [herase] using hcfg
  have hExactOnC0 : μ (Aexact ∩ C0) = μ C0 := by
    -- Proof comment: intersecting a conull event with `C0` leaves the measure of `C0` unchanged.
    have hInter : μ (C0 ∩ Aexact) = μ C0 :=
      measure_inter_conull hExactCompl
    simpa [Set.inter_comm] using hInter
  have hFactor :
      μ ((erase ⁻¹' Aexact) ∩ C0) =
        μ (erase ⁻¹' Aexact) * μ C0 := by
    -- Proof comment: the erased exact-two event only depends on the outside configuration, so it
    -- factors independently from the finite in-box cylinder.
    simpa [μ, erase, C0] using
      (eraseEdgesPreimage_inter_finitePattern_eq_mul
        (d := 2) (p := p)
        (F := boxEdges 2 L) (A := ∅) (E0 := Aexact) hAmeas)
  have hMul :
      μ (erase ⁻¹' Aexact) * μ C0 = 1 * μ C0 := by
    calc
      μ (erase ⁻¹' Aexact) * μ C0 = μ ((erase ⁻¹' Aexact) ∩ C0) := hFactor.symm
      _ = μ (Aexact ∩ C0) := by rw [hEraseOnC0]
      _ = μ C0 := hExactOnC0
      _ = 1 * μ C0 := by simp
  have hC0toReal_ne : (μ C0).toReal ≠ 0 := by
    exact (ENNReal.toReal_pos (ne_of_gt hC0pos) (measure_ne_top μ C0)).ne'
  have hMulToReal :
      (μ (erase ⁻¹' Aexact)).toReal * (μ C0).toReal =
        1 * (μ C0).toReal := by
    simpa [ENNReal.toReal_mul] using congrArg ENNReal.toReal hMul
  have hEraseFullToReal : (μ (erase ⁻¹' Aexact)).toReal = 1 :=
    mul_right_cancel₀ hC0toReal_ne hMulToReal
  exact (ENNReal.toReal_eq_one_iff _).mp hEraseFullToReal

/-- Helper for Theorem 2.46: if the erased configuration already has exactly two infinite
clusters, then forcing the finite box open contradicts the original exact-two event whenever a
coarse outside two-arm witness is present. -/
lemma allOpenBox_not_clusterCountEqTwo_of_outsideTwoArm_and_erasedExactTwo
    {L : ℕ} {cfg : Set (Sym2 (LatticePoint 2))}
    (hOutside : cfg ∈ outsideBoxTwoArmEvent_config 2 L)
    (hEraseExactTwo :
      infiniteOpenClusterCount
          (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s)))
          (cfg \ boxEdges 2 L) = 2)
    (hall : boxEdges 2 L ⊆ cfg) :
    cfg ∉
      {cfg : Set (Sym2 (LatticePoint 2)) |
        infiniteOpenClusterCount
          (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg = 2} := by
  -- Route correction: `outside two-arm + all-open box` alone is too weak; the erased exact-two
  -- hypothesis is what prevents extra infinite clusters from surviving outside the box.
  intro hCfgExactTwo
  rcases hOutside with ⟨u, huShell, v, hvShell, _huvNe, huInf, hvInf, huvNotConn⟩
  have hLpos : 0 < L := by
    cases L with
    | zero =>
        exact False.elim (huShell.2 huShell.1)
    | succ L =>
        exact Nat.succ_pos _
  rcases (infiniteOpenClusterCount_eq_two_iff
      (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s) (cfg \ boxEdges 2 L)).1
      hEraseExactTwo with
    ⟨a, b, haInf, hbInf, habNotConn, hcover⟩
  have huInf' :
      Set.Infinite
        (openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
          u (cfg \ boxEdges 2 L)) := by
    simpa [openCluster_mem_iff] using huInf
  have hvInf' :
      Set.Infinite
        (openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
          v (cfg \ boxEdges 2 L)) := by
    simpa [openCluster_mem_iff] using hvInf
  have huvOrig :
      cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) u v :=
    bondConnectionEvent_of_boundaryShell_allOpenBox (d := 2) huShell hvShell hall
  have huCover := hcover u huInf'
  have hvCover := hcover v hvInf'
  have habOrig :
      cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) a b := by
    rcases huCover with huA | huB <;> rcases hvCover with hvA | hvB
    · exact False.elim <|
        huvNotConn <| by
          change
            (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) cfg).Reachable u v
          have huA' :
              cfg ∈ bondConnectionEvent
                (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) u a := by
            simpa using huA
          have hvA' :
              cfg ∈ bondConnectionEvent
                (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) v a := by
            simpa using hvA
          change
            (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) cfg).Reachable u a
            at huA'
          have haV :
              cfg ∈ bondConnectionEvent
                (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) a v :=
            mem_bondConnectionEvent_symm
              (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) hvA'
          change
            (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) cfg).Reachable a v
            at haV
          exact huA'.trans haV
    · have huA' :
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) u a :=
        bondConnectionEvent_eraseBox_subset_id (d := 2) L <| by simpa using huA
      have hvB' :
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) v b :=
        bondConnectionEvent_eraseBox_subset_id (d := 2) L <| by simpa using hvB
      change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable a b
      have haU :
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) a u :=
        mem_bondConnectionEvent_symm
          (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s) huA'
      change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable a u at haU
      change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable u v at huvOrig
      change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable v b at hvB'
      exact haU.trans (huvOrig.trans hvB')
    · have huB' :
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) u b :=
        bondConnectionEvent_eraseBox_subset_id (d := 2) L <| by simpa using huB
      have hvA' :
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) v a :=
        bondConnectionEvent_eraseBox_subset_id (d := 2) L <| by simpa using hvA
      have haB :
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) a b := by
        change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable a b
        have haV :
            cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) a v :=
          mem_bondConnectionEvent_symm
            (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s) hvA'
        change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable a v at haV
        change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable u v at huvOrig
        change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable u b at huB'
        have vu :
            cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) v u :=
          mem_bondConnectionEvent_symm
            (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s) huvOrig
        change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable v u at vu
        exact haV.trans (vu.trans huB')
      exact haB
    · exact False.elim <|
        huvNotConn <| by
          change
            (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) cfg).Reachable u v
          have huB' :
              cfg ∈ bondConnectionEvent
                (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) u b := by
            simpa using huB
          have hvB' :
              cfg ∈ bondConnectionEvent
                (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) v b := by
            simpa using hvB
          change
            (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) cfg).Reachable u b
            at huB'
          have hbV :
              cfg ∈ bondConnectionEvent
                (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) b v :=
            mem_bondConnectionEvent_symm
              (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) hvB'
          change
            (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) cfg).Reachable b v
            at hbV
          exact huB'.trans hbV
  have hconnectToA :
      ∀ z : LatticePoint 2,
        Set.Infinite
          (openCluster
            (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
            z cfg) →
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) z a := by
    intro z hzInf
    rcases existsErasedInfiniteRootOfInfiniteCluster (L := L) (cfg := cfg) (z := z)
        hLpos hzInf with
      ⟨t, hzt, htInf⟩
    have htInf' :
        Set.Infinite
          (openCluster
            (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
            t (cfg \ boxEdges 2 L)) := by
      simpa [openCluster_mem_iff] using htInf
    rcases hcover t htInf' with htA | htB
    · change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable z a
      change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable z t at hzt
      have htA' :
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) t a :=
        bondConnectionEvent_eraseBox_subset_id (d := 2) L <| by simpa using htA
      change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable t a at htA'
      exact hzt.trans htA'
    · change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable z a
      change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable z t at hzt
      have htB' :
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) t b :=
        bondConnectionEvent_eraseBox_subset_id (d := 2) L <| by simpa using htB
      change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable t b at htB'
      have hbA :
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) b a :=
        mem_bondConnectionEvent_symm
          (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s) habOrig
      change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable b a at hbA
      exact hzt.trans (htB'.trans hbA)
  rcases (infiniteOpenClusterCount_eq_two_iff
      (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).1 hCfgExactTwo with
    ⟨x, y, hxInf, hyInf, hxy, _hcoverFull⟩
  have hxA := hconnectToA x hxInf
  have hyA := hconnectToA y hyInf
  have hxyConn :
      cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) x y := by
    change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable x y
    change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable x a at hxA
    have haY :
        cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) a y :=
      mem_bondConnectionEvent_symm
        (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s) hyA
    change (openBondGraph (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).Reachable a y at haY
    exact hxA.trans haY
  exact hxy hxyConn

/-- Helper for Theorem 2.46: in the strict interior Bernoulli regime, full mass of the canonical
exact-two event is impossible because opening a finite box merges the two erased infinite
clusters. -/
lemma canonicalClusterCountEqTwoFull_contradiction
    (p : unitInterval) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hfull :
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p
        {cfg : Set (Sym2 (LatticePoint 2)) |
          infiniteOpenClusterCount
              (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg =
            2} = 1) :
    False := by
  classical
  let νprob : ProbabilityMeasure (Set (Sym2 (LatticePoint 2))) :=
    ⟨ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet p, inferInstance⟩
  let ν : Measure (Set (Sym2 (LatticePoint 2))) := νprob
  let Aexact : Set (Set (Sym2 (LatticePoint 2))) :=
    {cfg : Set (Sym2 (LatticePoint 2)) |
      infiniteOpenClusterCount
          (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg = 2}
  have hAmeas : MeasurableSet Aexact := by
    simpa [Aexact] using measurableSet_clusterCountEqTwo_config
  obtain ⟨L, hTwoArmPos⟩ :=
    exists_pos_measure_outsideBoxTwoArmEvent_of_clusterCountEqTwo_full p hfull
  let erase : Set (Sym2 (LatticePoint 2)) → Set (Sym2 (LatticePoint 2)) :=
    fun cfg ↦ cfg \ boxEdges 2 L
  let allOpenEq : Set (Set (Sym2 (LatticePoint 2))) :=
    {cfg | cfg ∩ boxEdges 2 L = boxEdges 2 L}
  let allOpen : Set (Set (Sym2 (LatticePoint 2))) := {cfg | boxEdges 2 L ⊆ cfg}
  let outsideTwo : Set (Set (Sym2 (LatticePoint 2))) := outsideBoxTwoArmEvent_config 2 L
  let erasedExactTwo : Set (Set (Sym2 (LatticePoint 2))) := erase ⁻¹' Aexact
  let erasedOutsideExactTwo : Set (Set (Sym2 (LatticePoint 2))) := outsideTwo ∩ erasedExactTwo
  let erasedOutsideExactTwoCore : Set (Set (Sym2 (LatticePoint 2))) := outsideTwo ∩ Aexact
  have hOutsideMeas : MeasurableSet outsideTwo := by
    simpa [outsideTwo] using measurableSet_outsideBoxTwoArmEvent_config 2 L
  have hCanonicalFull : ν Aexact = 1 := by
    simpa [ν, Aexact] using hfull
  have hErasedExactTwoFull : ν erasedExactTwo = 1 := by
    -- Proof comment: exact-two full mass survives erasing a finite box by the previous helper.
    simpa [ν, erasedExactTwo, erase, Aexact] using
      eraseBoxClusterCountEqTwo_full_of_clusterCountEqTwo_full p hp0 hp1 L hfull
  have hErasedExactTwoCompl : ν erasedExactTwoᶜ = 0 := by
    -- Proof comment: the erased exact-two event is therefore conull.
    have hCompl : ν erasedExactTwoᶜ = ν Set.univ - ν erasedExactTwo :=
      measure_compl
        (measurableSet_preimage (measurable_eraseEdges_config (d := 2) (boxEdges 2 L)) hAmeas)
        (by rw [hErasedExactTwoFull]; exact ENNReal.one_ne_top)
    rw [hErasedExactTwoFull] at hCompl
    simpa [ν] using hCompl
  have hOutsideErasePos : 0 < ν erasedOutsideExactTwo := by
    -- Proof comment: intersecting the positive outside-two-arm event with a conull erased
    -- exact-two event keeps the event positive.
    have hInter : ν (outsideTwo ∩ erasedExactTwo) = ν outsideTwo :=
      measure_inter_conull hErasedExactTwoCompl
    have hEq : ν erasedOutsideExactTwo = ν outsideTwo := by
      simpa [erasedOutsideExactTwo, outsideTwo, Set.inter_comm] using hInter
    rw [hEq]
    exact hTwoArmPos
  have hAllOpenEq : allOpenEq = allOpen := by
    -- Proof comment: package the all-open box cylinder either as an equality on the finite box
    -- pattern or as the direct subset condition.
    ext cfg
    constructor
    · intro hcfg e he
      have hmem := congrArg (fun s : Set (Sym2 (LatticePoint 2)) ↦ e ∈ s) hcfg
      simpa [allOpenEq, allOpen, he] using hmem
    · intro hcfg
      ext e
      constructor
      · intro he
        exact he.2
      · intro he
        exact ⟨hcfg he, he⟩
  have hAllOpenPos : 0 < ν allOpenEq := by
    -- Proof comment: the all-open finite box cylinder is positive for every interior parameter.
    rw [hAllOpenEq]
    simpa [ν, allOpen] using
      finiteCylinderAllOpenPos
        (μ := νprob)
        (openEdges := fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg)
        (p := p) hp0 hp1
        (canonicalBernoulli_id_isSetBernoulli p)
        (boxEdges_finite 2 L) (boxEdges_subset_edgeSet 2 L)
  have hCoreMeas : MeasurableSet erasedOutsideExactTwoCore := by
    exact hOutsideMeas.inter hAmeas
  have hOutsidePreimage : erase ⁻¹' outsideTwo = outsideTwo := by
    simpa [erase, outsideTwo] using eraseEdges_preimage_outsideBoxTwoArmEvent_config 2 L
  have hCorePreimage :
      erase ⁻¹' erasedOutsideExactTwoCore = erasedOutsideExactTwo := by
    -- Proof comment: the outside-two-arm factor already depends only on the erased
    -- configuration, so erasing again only affects the exact-two factor.
    ext cfg
    constructor
    · intro hcfg
      simp only [Set.mem_preimage, erasedOutsideExactTwoCore, erasedOutsideExactTwo,
        erasedExactTwo] at hcfg ⊢
      refine ⟨?_, hcfg.2⟩
      have : cfg ∈ erase ⁻¹' outsideTwo := hcfg.1
      rwa [hOutsidePreimage] at this
    · intro hcfg
      simp only [Set.mem_preimage, erasedOutsideExactTwoCore, erasedOutsideExactTwo,
        erasedExactTwo] at hcfg ⊢
      refine ⟨?_, hcfg.2⟩
      have : cfg ∈ outsideTwo := hcfg.1
      rwa [← hOutsidePreimage] at this
  have hOutsideEraseOpenPos : 0 < ν (erasedOutsideExactTwo ∩ allOpenEq) := by
    -- Proof comment: after fixing the erased outside-two-arm event, prescribing the all-open
    -- box is an independent positive finite cylinder.
    have hFactor :
        ν ((erase ⁻¹' erasedOutsideExactTwoCore) ∩ allOpenEq) =
          ν (erase ⁻¹' erasedOutsideExactTwoCore) * ν allOpenEq := by
      have hFactor' :
          ν ((erase ⁻¹' erasedOutsideExactTwoCore) ∩
              {cfg | cfg ∩ boxEdges 2 L = boxEdges 2 L}) =
            ν (erase ⁻¹' erasedOutsideExactTwoCore) *
              ν {cfg | cfg ∩ boxEdges 2 L = boxEdges 2 L} := by
        simpa [ν, erase, erasedOutsideExactTwoCore] using
          (eraseEdgesPreimage_inter_finitePattern_eq_mul
            (d := 2) (p := p)
            (F := boxEdges 2 L) (A := boxEdges 2 L)
            (E0 := erasedOutsideExactTwoCore) hCoreMeas)
      simpa [allOpenEq] using hFactor'
    have hMulPos :
        0 < ν (erase ⁻¹' erasedOutsideExactTwoCore) * ν allOpenEq :=
      pos_iff_ne_zero.mpr <|
        mul_ne_zero
          (by simpa [hCorePreimage] using ne_of_gt hOutsideErasePos)
          (ne_of_gt hAllOpenPos)
    have hEq :
        ν (erasedOutsideExactTwo ∩ allOpenEq) =
          ν (erase ⁻¹' erasedOutsideExactTwoCore) * ν allOpenEq := by
      rw [← hCorePreimage, hFactor]
    rw [hEq]
    exact hMulPos
  have hExactCompl : ν Aexactᶜ = 0 := by
    -- Proof comment: the original exact-two event is conull under the full-mass assumption too.
    have hCompl : ν Aexactᶜ = ν Set.univ - ν Aexact :=
      measure_compl hAmeas (by rw [hCanonicalFull]; exact ENNReal.one_ne_top)
    rw [hCanonicalFull] at hCompl
    simpa [ν] using hCompl
  have hContradictionEventPos :
      0 < ν ((erasedOutsideExactTwo ∩ allOpenEq) ∩ Aexact) := by
    -- Proof comment: intersecting the already positive event with the conull original exact-two
    -- event preserves positivity.
    have hInter :
        ν ((erasedOutsideExactTwo ∩ allOpenEq) ∩ Aexact) =
          ν (erasedOutsideExactTwo ∩ allOpenEq) :=
      measure_inter_conull hExactCompl
    have hEq :
        ν ((erasedOutsideExactTwo ∩ allOpenEq) ∩ Aexact) =
          ν (erasedOutsideExactTwo ∩ allOpenEq) := by
      simpa [Set.inter_assoc] using hInter
    rw [hEq]
    exact hOutsideEraseOpenPos
  have hWitnessNonempty :
      (((erasedOutsideExactTwo ∩ allOpenEq) ∩ Aexact) :
        Set (Set (Sym2 (LatticePoint 2)))).Nonempty := by
    by_contra hEmpty
    have hEmptySet :
        ((erasedOutsideExactTwo ∩ allOpenEq) ∩ Aexact :
          Set (Set (Sym2 (LatticePoint 2)))) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hEmpty
    have hZero :
        ν ((erasedOutsideExactTwo ∩ allOpenEq) ∩ Aexact) = 0 := by
      simp [hEmptySet]
    exact (ne_of_gt hContradictionEventPos) hZero
  rcases hWitnessNonempty with ⟨cfg, hcfg⟩
  have hOutside : cfg ∈ outsideTwo := hcfg.1.1.1
  have hEraseExactTwoSet : cfg ∈ erasedExactTwo := hcfg.1.1.2
  have hallEq : cfg ∈ allOpenEq := hcfg.1.2
  have hCfgExactTwo : cfg ∈ Aexact := hcfg.2
  have hall : boxEdges 2 L ⊆ cfg := by
    have : cfg ∈ allOpen := by
      simpa [hAllOpenEq] using hallEq
    simpa [allOpen] using this
  have hEraseExactTwo :
      infiniteOpenClusterCount
          (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s)))
          (cfg \ boxEdges 2 L) = 2 := by
    simpa [erasedExactTwo, erase, Aexact] using hEraseExactTwoSet
  have hNotExactTwo :
      cfg ∉ Aexact := by
    simpa [outsideTwo, Aexact] using
      allOpenBox_not_clusterCountEqTwo_of_outsideTwoArm_and_erasedExactTwo
        hOutside hEraseExactTwo hall
  exact hNotExactTwo hCfgExactTwo

/-- Helper for Theorem 2.46: the fixed radius-one erased outside-arm event rooted at `x`. -/
def radiusOneOutsideArmEvent_config
    (x : LatticePoint 2) :
    Set (Set (Sym2 (LatticePoint 2))) :=
  {cfg |
    Set.Infinite
      (openCluster
        (bondConnectionEvent
          (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 1)) x cfg)}

/-- Helper for Theorem 2.46: the fixed radius-one erased outside-arm event is measurable. -/
lemma measurableSet_radiusOneOutsideArmEvent_config
    (x : LatticePoint 2) :
    MeasurableSet (radiusOneOutsideArmEvent_config x) := by
  -- Proof comment: this is just the standard erased-cluster infinitude event at radius `1`.
  simpa [radiusOneOutsideArmEvent_config] using
    measurableSet_infiniteOpenClusterEvent
      (bondConnectionEvent
        (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 1))
      (fun z w ↦ measurableSet_bondConnectionEvent_config_eraseBox (d := 2) 1 z w)
      x

/-- Helper for Theorem 2.46: positive half-critical origin percolation already yields positive
mass for one fixed radius-one erased outside-arm event rooted on the shell `∂B₁`. -/
lemma exists_pos_measure_fixedRadiusOneOutsideArm_of_halfPositive
    (hhalfPos : 0 < canonicalBondPercolationTheta half) :
    ∃ x : LatticePoint 2,
      x ∈ boundaryShell 2 1 ∧
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (radiusOneOutsideArmEvent_config x) := by
  classical
  let μprob : ProbabilityMeasure (Set (Sym2 (LatticePoint 2))) :=
    ⟨ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half, inferInstance⟩
  let μ : Measure (Set (Sym2 (LatticePoint 2))) := μprob
  let originInf : Set (Set (Sym2 (LatticePoint 2))) :=
    originInInfiniteClusterEvent
      (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s)))
  let shellArm : LatticePoint 2 → Set (Set (Sym2 (LatticePoint 2))) :=
    fun x ↦
      {cfg : Set (Sym2 (LatticePoint 2)) |
        x ∈ boundaryShell 2 1 ∧
          cfg ∈ radiusOneOutsideArmEvent_config x}
  let pureArm : LatticePoint 2 → Set (Set (Sym2 (LatticePoint 2))) :=
    fun x ↦ radiusOneOutsideArmEvent_config x
  have hOriginPosNN : 0 < μprob originInf := by
    -- Proof comment: `canonicalBondPercolationTheta half` is exactly the Bernoulli mass of the
    -- origin infinite-cluster event at the midpoint parameter.
    simpa [μprob, originInf, canonicalBondPercolationTheta, originPercolationProbability] using
      hhalfPos
  have hOriginPos : 0 < μ originInf := by
    simpa [μ, μprob] using
      (show (0 : ENNReal) < (μprob originInf : ENNReal) from ENNReal.coe_pos.2 hOriginPosNN)
  have hCover : originInf ⊆ ⋃ x : LatticePoint 2, shellArm x := by
    intro cfg hcfg
    have hOriginInf :
        Set.Infinite
          (openCluster
            (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))
            0 cfg) := by
      simpa [originInf, originInInfiniteClusterEvent] using hcfg
    have hzeroBox : (0 : LatticePoint 2) ∈ boxVertices 2 0 := by
      -- Proof comment: the origin lies in the degenerate box `B₀`.
      simp [boxVertices]
    rcases existsBoundaryShellInfiniteErasedClusterOfInfiniteCluster
        (d := 2) (L := 1) (cfg := cfg) (x := (0 : LatticePoint 2))
        (by norm_num) hzeroBox hOriginInf with
      ⟨x, hxShell, _hxConn, hxInf⟩
    -- Proof comment: every infinite origin cluster exits `B₀` through some shell vertex whose
    -- erased radius-one cluster remains infinite.
    exact Set.mem_iUnion.2 ⟨x, ⟨hxShell, hxInf⟩⟩
  have hUnionPos : 0 < μ (⋃ x : LatticePoint 2, shellArm x) := by
    -- Proof comment: the origin event is contained in the shell-union event, so its positivity
    -- transfers by monotonicity of measure.
    exact lt_of_lt_of_le hOriginPos (measure_mono hCover)
  obtain ⟨x, hxPos⟩ :
      ∃ x : LatticePoint 2, 0 < μ (shellArm x) :=
    exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hUnionPos)
  have hxShell : x ∈ boundaryShell 2 1 := by
    by_contra hxNotShell
    have hEmpty : shellArm x = ∅ := by
      ext cfg
      simp [shellArm, hxNotShell]
    have : (0 : ENNReal) < 0 := by
      simpa [μ, hEmpty] using hxPos
    exact (lt_irrefl (0 : ENNReal)) this
  have hShellArmEq : shellArm x = pureArm x := by
    -- Proof comment: after fixing the shell witness, the shell side condition becomes redundant.
    ext cfg
    simp [shellArm, pureArm, hxShell]
  exact ⟨x, hxShell, by simpa [μ, hShellArmEq] using hxPos⟩

/-- Helper for Theorem 2.46: any parameter strictly below `criticalPercolationValue θ` already
lies in the zero set of `θ`. -/
lemma theta_eq_zero_of_lt_criticalPercolationValue
    (θ : unitInterval → NNReal) {p : unitInterval}
    (hp : p < criticalPercolationValue θ) :
    θ p = 0 := by
  -- Proof comment: a positive value at `p` would place `p` in the defining threshold set, so the
  -- infimum could not stay strictly above `p`.
  by_contra hθp
  have hθpPos : 0 < θ p := pos_iff_ne_zero.mpr hθp
  have hcrit_le : criticalPercolationValue θ ≤ p :=
    criticalPercolationValue_le_of_positive θ hθpPos
  exact hp.not_ge hcrit_le

/-- Helper for Theorem 2.46: for a monotone percolation function, every parameter strictly above
`criticalPercolationValue θ` is already supercritical. -/
lemma theta_pos_of_criticalPercolationValue_lt_of_monotone
    (θ : unitInterval → NNReal) (hmono : Monotone θ) {p : unitInterval}
    (hp : criticalPercolationValue θ < p) :
    0 < θ p := by
  -- Proof comment: if `θ p = 0`, then `p` belongs to the zero set whose supremum is the critical
  -- value for monotone `θ`, contradicting `criticalPercolationValue θ < p`.
  by_contra hθp
  have hθpZero : θ p = 0 := le_antisymm (le_of_not_gt hθp) (zero_le _)
  have hp_le_crit : p ≤ criticalPercolationValue θ := by
    rw [criticalPercolationValue_eq_sSup_theta_zero θ hmono]
    exact le_csSup
      (OrderTop.bddAbove {q : unitInterval | θ q = 0})
      (by simpa using hθpZero)
  exact hp.not_ge hp_le_crit

/-- Helper for Theorem 2.46: the canonical exact-two event on edge configurations. -/
abbrev canonicalExactTwoEvent : Set (Set (Sym2 (LatticePoint 2))) :=
  {cfg : Set (Sym2 (LatticePoint 2)) |
    infiniteOpenClusterCount
        (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg =
      2}

/-- Helper for Theorem 2.46: the strengthened radius-one seed keeps the fixed erased outside
two-arm witness together with exact-two after erasing `boxEdges 2 1`. -/
def erasedExactTwoSeedEvent
    (x y : LatticePoint 2) :
    Set (Set (Sym2 (LatticePoint 2))) :=
  outsideBoxTwoArmWitnessEvent_config 2 1 x y ∩
    ((fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg \ boxEdges 2 1) ⁻¹' canonicalExactTwoEvent)

/-- Helper for Theorem 2.46: the radius-`L` stage used to build the coexistence tail event. -/
abbrev coexistenceTailStageEvent
    (L : ℕ) :
    Set (Set (Sym2 (LatticePoint 2))) :=
  outsideBoxTwoArmEvent_config 2 L ∩
    ((fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg \ boxEdges 2 L) ⁻¹' canonicalExactTwoEvent)

/-- Helper for Theorem 2.46: the tail coexistence event asks that for every finite cutoff there is
some larger box radius with an erased outside-two-arm witness and erased exact-two data. -/
def coexistenceTailEvent : Set (Set (Sym2 (LatticePoint 2))) :=
  ⋂ N : ℕ, ⋃ L ∈ Set.Ici N,
    coexistenceTailStageEvent L

/-- Helper for Theorem 2.46: the canonical exact-two event is measurable. -/
lemma measurableSet_canonicalExactTwoEvent :
    MeasurableSet canonicalExactTwoEvent := by
  -- Proof comment: this is exactly the previously established measurability statement.
  simpa [canonicalExactTwoEvent] using measurableSet_clusterCountEqTwo_config

/-- Helper for Theorem 2.46: the strengthened erased exact-two seed event is measurable. -/
lemma measurableSet_erasedExactTwoSeedEvent
    (x y : LatticePoint 2) :
    MeasurableSet (erasedExactTwoSeedEvent x y) := by
  -- Proof comment: the strengthened seed is the intersection of the measurable fixed witness event
  -- with the measurable erased exact-two pullback.
  refine (measurableSet_outsideBoxTwoArmWitnessEvent_config 2 1 x y).inter ?_
  exact measurableSet_preimage
    (measurable_eraseEdges_config (d := 2) (boxEdges 2 1))
    measurableSet_canonicalExactTwoEvent

/-- Helper for Theorem 2.46: each radius stage in the coexistence tail event is measurable. -/
lemma measurableSet_coexistenceTailStageEvent
    (L : ℕ) :
    MeasurableSet (coexistenceTailStageEvent L) := by
  -- Proof comment: each stage is the measurable outside-two-arm event intersected with the
  -- measurable erased exact-two pullback at the same radius.
  refine (measurableSet_outsideBoxTwoArmEvent_config 2 L).inter ?_
  exact measurableSet_preimage
    (measurable_eraseEdges_config (d := 2) (boxEdges 2 L))
    measurableSet_canonicalExactTwoEvent

/-- Helper for Theorem 2.46: each coexistence-tail stage is exactly the preimage, under radius-`L`
box erasure, of the corresponding outside-two-arm event intersected with the canonical exact-two
event. -/
lemma coexistenceTailStageEvent_eq_preimage_eraseBox
    (L : ℕ) :
    coexistenceTailStageEvent L =
      (fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg \ boxEdges 2 L) ⁻¹'
        (outsideBoxTwoArmEvent_config 2 L ∩ canonicalExactTwoEvent) := by
  -- Proof comment: the outside-two-arm factor already depends only on the erased configuration,
  -- so both stage constraints can be packaged into one erased preimage.
  ext cfg
  constructor
  · intro hcfg
    have hOutside :
        cfg \ boxEdges 2 L ∈ outsideBoxTwoArmEvent_config 2 L := by
      have hEq :
          cfg ∈
              (fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg \ boxEdges 2 L) ⁻¹'
                outsideBoxTwoArmEvent_config 2 L ↔
            cfg ∈ outsideBoxTwoArmEvent_config 2 L := by
        rw [eraseEdges_preimage_outsideBoxTwoArmEvent_config (d := 2) L]
      exact hEq.mpr hcfg.1
    refine ⟨?_, hcfg.2⟩
    exact hOutside
  · intro hcfg
    have hOutside :
        cfg ∈ outsideBoxTwoArmEvent_config 2 L := by
      have hEq :
          cfg ∈
              (fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg \ boxEdges 2 L) ⁻¹'
                outsideBoxTwoArmEvent_config 2 L ↔
            cfg ∈ outsideBoxTwoArmEvent_config 2 L := by
        rw [eraseEdges_preimage_outsideBoxTwoArmEvent_config (d := 2) L]
      exact hEq.mp hcfg.1
    refine ⟨?_, hcfg.2⟩
    exact hOutside

/-- Helper for Theorem 2.46: each fixed coexistence-tail stage is independent of every prescribed
inside-box pattern at the same radius. -/
lemma coexistenceTailStageEvent_inter_boxPattern_eq_mul
    (L : ℕ) (A : Set (Sym2 (LatticePoint 2))) :
    ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
      (coexistenceTailStageEvent L ∩ {cfg | cfg ∩ boxEdges 2 L = A}) =
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
            (coexistenceTailStageEvent L) *
          ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
            {cfg | cfg ∩ boxEdges 2 L = A} := by
  -- Proof comment: rewrite the stage as a radius-`L` erasure preimage, then apply the finite-box
  -- Bernoulli factorization theorem.
  rw [coexistenceTailStageEvent_eq_preimage_eraseBox (L := L)]
  simpa using
    (eraseEdgesPreimage_inter_finitePattern_eq_mul
      (d := 2) (p := half)
      (F := boxEdges 2 L) (A := A)
      (E0 := outsideBoxTwoArmEvent_config 2 L ∩ canonicalExactTwoEvent)
      ((measurableSet_outsideBoxTwoArmEvent_config 2 L).inter
        measurableSet_canonicalExactTwoEvent))

/-- Helper for Theorem 2.46: the coexistence tail event is measurable in the canonical
configuration space. -/
lemma measurableSet_coexistenceTailEvent :
    MeasurableSet coexistenceTailEvent := by
  -- Proof comment: the tail event is a countable intersection of countable unions of measurable
  -- stage events.
  refine MeasurableSet.iInter fun N ↦ ?_
  let EN : Set (Set (Sym2 (LatticePoint 2))) :=
    ⋃ L ∈ Set.Ici N, coexistenceTailStageEvent L
  have hEN :
      EN = ⋃ L : {L // L ∈ Set.Ici N}, coexistenceTailStageEvent L.1 := by
    ext cfg
    simp [EN]
  rw [show (⋃ L ∈ Set.Ici N, coexistenceTailStageEvent L) = EN by rfl, hEN]
  exact MeasurableSet.iUnion fun L ↦ measurableSet_coexistenceTailStageEvent L.1

/-- Helper for Theorem 2.46: forgetting the erased exact-two factor leaves the fixed outside-two-arm
witness event. -/
lemma erasedExactTwoSeedEvent_subset_witness
    (x y : LatticePoint 2) :
    erasedExactTwoSeedEvent x y ⊆ outsideBoxTwoArmWitnessEvent_config 2 1 x y := by
  -- Proof comment: the strengthened seed is just the witness event intersected with one more
  -- erased exact-two condition.
  intro cfg hcfg
  exact hcfg.1

/-- Helper for Theorem 2.46: a fixed radius-one outside-two-arm witness already forces the rooted
erased outside-arm event at its left shell root. -/
lemma outsideBoxTwoArmWitnessEvent_subset_radiusOneOutsideArmEvent_left
    (x y : LatticePoint 2) :
    outsideBoxTwoArmWitnessEvent_config 2 1 x y ⊆ radiusOneOutsideArmEvent_config x := by
  intro cfg hcfg
  -- Proof comment: the left component of the fixed witness data is exactly the infinitude
  -- predicate defining the rooted radius-one erased outside-arm event.
  simpa [radiusOneOutsideArmEvent_config] using hcfg.2.2.2.1

/-- Helper for Theorem 2.46: a fixed radius-one outside-two-arm witness already forces the rooted
erased outside-arm event at its right shell root. -/
lemma outsideBoxTwoArmWitnessEvent_subset_radiusOneOutsideArmEvent_right
    (x y : LatticePoint 2) :
    outsideBoxTwoArmWitnessEvent_config 2 1 x y ⊆ radiusOneOutsideArmEvent_config y := by
  intro cfg hcfg
  -- Proof comment: the right component of the fixed witness data gives the symmetric rooted
  -- erased outside-arm event.
  simpa [radiusOneOutsideArmEvent_config] using hcfg.2.2.2.2.1

/-- Helper for Theorem 2.46: the strengthened radius-one seed still forces the rooted erased
outside-arm event at its first shell witness. -/
lemma erasedExactTwoSeedEvent_subset_radiusOneOutsideArmEvent
    (x y : LatticePoint 2) :
    erasedExactTwoSeedEvent x y ⊆ radiusOneOutsideArmEvent_config x := by
  intro cfg hcfg
  -- Proof comment: first forget the erased exact-two factor, then read off the left witness arm.
  exact outsideBoxTwoArmWitnessEvent_subset_radiusOneOutsideArmEvent_left x y hcfg.1

/-- Helper for Theorem 2.46: every fixed radius-one outside-two-arm witness is, in particular, a
point of the coarse radius-one outside-two-arm event. -/
lemma outsideBoxTwoArmWitnessEvent_subset_outsideBoxTwoArmEvent
    (x y : LatticePoint 2) :
    outsideBoxTwoArmWitnessEvent_config 2 1 x y ⊆ outsideBoxTwoArmEvent_config 2 1 := by
  intro cfg hcfg
  rcases hcfg with ⟨hxShell, hyShell, hxy, hxInf, hyInf, hnotConn⟩
  -- Proof comment: the coarse event simply forgets that the two shell witnesses were fixed in
  -- advance.
  exact ⟨x, hxShell, y, hyShell, hxy, hxInf, hyInf, hnotConn⟩

/-- Helper for Theorem 2.46: the strengthened radius-one seed already lands in the first
coexistence-tail stage. -/
lemma erasedExactTwoSeedEvent_subset_coexistenceTailStageEventOne
    (x y : LatticePoint 2) :
    erasedExactTwoSeedEvent x y ⊆ coexistenceTailStageEvent 1 := by
  intro cfg hcfg
  refine ⟨?_, hcfg.2⟩
  -- Proof comment: the seed contains the fixed witness data at radius `1`, so only the coarse
  -- outside-two-arm packaging changes when passing to the stage event.
  exact outsideBoxTwoArmWitnessEvent_subset_outsideBoxTwoArmEvent x y hcfg.1

/-- Helper for Theorem 2.46: erasing `boxEdges 2 1` again does not change the strengthened
radius-one seed, because both the fixed witness event and the exact-two factor already live on the
once-erased configuration. -/
lemma eraseEdges_preimage_erasedExactTwoSeedEvent
    (x y : LatticePoint 2) :
    (fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg \ boxEdges 2 1) ⁻¹'
        erasedExactTwoSeedEvent x y =
      erasedExactTwoSeedEvent x y := by
  ext cfg
  simp only [erasedExactTwoSeedEvent, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hWitness, hExact⟩
    refine ⟨?_, ?_⟩
    · have hWitnessEq :
          cfg \ boxEdges 2 1 ∈ outsideBoxTwoArmWitnessEvent_config 2 1 x y ↔
            cfg ∈ outsideBoxTwoArmWitnessEvent_config 2 1 x y := by
        change cfg ∈ (fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg \ boxEdges 2 1) ⁻¹'
            outsideBoxTwoArmWitnessEvent_config 2 1 x y ↔
          cfg ∈ outsideBoxTwoArmWitnessEvent_config 2 1 x y
        exact Set.ext_iff.mp
          (eraseEdges_preimage_outsideBoxTwoArmWitnessEvent_config (d := 2) 1 x y) cfg
      exact hWitnessEq.mp hWitness
    · simpa [Set.diff_diff] using hExact
  · rintro ⟨hWitness, hExact⟩
    refine ⟨?_, ?_⟩
    · have hWitnessEq :
          cfg \ boxEdges 2 1 ∈ outsideBoxTwoArmWitnessEvent_config 2 1 x y ↔
            cfg ∈ outsideBoxTwoArmWitnessEvent_config 2 1 x y := by
        change cfg ∈ (fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg \ boxEdges 2 1) ⁻¹'
            outsideBoxTwoArmWitnessEvent_config 2 1 x y ↔
          cfg ∈ outsideBoxTwoArmWitnessEvent_config 2 1 x y
        exact Set.ext_iff.mp
          (eraseEdges_preimage_outsideBoxTwoArmWitnessEvent_config (d := 2) 1 x y) cfg
      exact hWitnessEq.mpr hWitness
    · simpa [Set.diff_diff] using hExact

/-- Helper for Theorem 2.46: the strengthened radius-one seed is independent of every prescribed
radius-one box pattern, because it already depends only on the once-erased outside configuration. -/
lemma erasedExactTwoSeedEvent_inter_boxPattern_eq_mul
    (x y : LatticePoint 2) (A : Set (Sym2 (LatticePoint 2))) :
    ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
      (erasedExactTwoSeedEvent x y ∩ {cfg | cfg ∩ boxEdges 2 1 = A}) =
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
            (erasedExactTwoSeedEvent x y) *
          ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
            {cfg | cfg ∩ boxEdges 2 1 = A} := by
  -- Proof comment: rewrite the seed as a radius-one erasure preimage and factor it from the
  -- finite inside-box cylinder.
  rw [← eraseEdges_preimage_erasedExactTwoSeedEvent x y]
  simpa using
    (eraseEdgesPreimage_inter_finitePattern_eq_mul
      (d := 2) (p := half)
      (F := boxEdges 2 1) (A := A)
      (E0 := erasedExactTwoSeedEvent x y)
      (measurableSet_erasedExactTwoSeedEvent x y))

/-- Helper for Theorem 2.46: intersecting a positive strengthened radius-one seed with the
all-closed radius-one box cylinder preserves positive half-critical mass. -/
lemma erasedExactTwoSeedEvent_inter_closedBox_pos_of_pos
    {x y : LatticePoint 2}
    (hseedPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (erasedExactTwoSeedEvent x y)) :
    0 <
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
        (erasedExactTwoSeedEvent x y ∩ {cfg | cfg ∩ boxEdges 2 1 = ∅}) := by
  have hClosedPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          {cfg | cfg ∩ boxEdges 2 1 = ∅} := by
    -- Proof comment: the midpoint Bernoulli law assigns positive mass to the all-closed radius-one
    -- box pattern.
    simpa using
      finiteCylinderAllClosedPos
        (μ := ⟨ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half, inferInstance⟩)
        (openEdges := fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg)
        (p := half) half_ne_zero half_ne_one
        (canonicalBernoulli_id_isSetBernoulli half)
        (boxEdges_finite 2 1) (boxEdges_subset_edgeSet 2 1)
  -- Proof comment: apply the seed-specific finite-box factorization and multiply the two positive
  -- factors.
  rw [erasedExactTwoSeedEvent_inter_boxPattern_eq_mul x y ∅]
  exact ENNReal.mul_pos (ne_of_gt hseedPos) (ne_of_gt hClosedPos)

/-- Helper for Theorem 2.46: on the all-closed radius-one box cylinder, the strengthened seed's
exact-two factor becomes the original canonical exact-two event. -/
lemma erasedExactTwoSeedEvent_inter_closedBox_subset_canonicalExactTwoEvent
    (x y : LatticePoint 2) :
    erasedExactTwoSeedEvent x y ∩ {cfg | cfg ∩ boxEdges 2 1 = ∅} ⊆ canonicalExactTwoEvent := by
  intro cfg hcfg
  have hSeed : cfg ∈ erasedExactTwoSeedEvent x y := hcfg.1
  have hClosed : cfg ∩ boxEdges 2 1 = ∅ := hcfg.2
  have hErase :
      cfg \ boxEdges 2 1 = cfg := by
    simpa using eraseBox_eq_self_of_inter_boxEdges_eq_empty (d := 2) 1 hClosed
  -- Proof comment: once the radius-one box is already closed, the erased exact-two constraint in
  -- the seed is literally the original exact-two event.
  simpa [erasedExactTwoSeedEvent, hErase] using hSeed.2

/-- Helper for Theorem 2.46: enlarging the box radius enlarges the box-edge set. -/
lemma boxEdges_mono
    {d : ℕ} {L M : ℕ} (hLM : L ≤ M) :
    boxEdges d L ⊆ boxEdges d M := by
  intro e he
  rcases he with ⟨x, hx, y, hy, rfl, hxy⟩
  -- Proof comment: every endpoint of a radius-`L` box edge still lies in the larger radius-`M`
  -- box, so the same lattice bond is also an `M`-box edge.
  exact ⟨x, boxVertices_mono (d := d) (L := L) (M := M) hLM hx,
    y, boxVertices_mono (d := d) (L := L) (M := M) hLM hy, rfl, hxy⟩

/-- Helper for Theorem 2.46: erasing a smaller box before asking for an `M`-erased connection is
irrelevant once `L ≤ M`. -/
lemma bondConnectionEvent_eraseBox_smaller_iff
    {d : ℕ} {L M : ℕ} (hLM : L ≤ M)
    (x y : LatticePoint d) (cfg : Set (Sym2 (LatticePoint d))) :
    cfg \ boxEdges d L ∈
        bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d M) x y ↔
      cfg ∈
        bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d M) x y := by
  have hbox : boxEdges d L ⊆ boxEdges d M := boxEdges_mono (d := d) hLM
  have hGraph :
      openBondGraph
          (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d M)
          (cfg \ boxEdges d L) =
        openBondGraph
          (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d M)
          cfg := by
    ext u v
    -- Proof comment: at adjacency level, deleting `boxEdges d L` first and then deleting the
    -- larger set `boxEdges d M` gives exactly the same open edge set as deleting `boxEdges d M`
    -- once.
    simp [openBondGraph, Set.diff_diff, Set.union_eq_right.mpr hbox]
  -- Proof comment: after the larger deletion by `boxEdges d M`, the earlier smaller deletion has
  -- already been absorbed into the same erased configuration.
  simpa [bondConnectionEvent, hGraph]

/-- Helper for Theorem 2.46: the erased `M`-cluster is unchanged if one first erases a smaller box
of radius `L ≤ M`. -/
lemma openCluster_eraseBox_smaller_eq
    {d : ℕ} {L M : ℕ} (hLM : L ≤ M)
    (x : LatticePoint d) (cfg : Set (Sym2 (LatticePoint d))) :
    openCluster
        (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d M))
        x (cfg \ boxEdges d L) =
      openCluster
        (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d M))
        x cfg := by
  ext y
  -- Proof comment: cluster membership is exactly the corresponding erased-box connection event, so
  -- the previous connection lemma applies pointwise.
  simpa [openCluster] using bondConnectionEvent_eraseBox_smaller_iff hLM x y cfg

/-- Helper for Theorem 2.46: an `M`-scale outside-two-arm event only depends on the configuration
outside `B_M`, so erasing a smaller box first does not change it. -/
lemma outsideBoxTwoArmEvent_eraseBox_smaller_iff
    {d : ℕ} {L M : ℕ} (hLM : L ≤ M)
    (cfg : Set (Sym2 (LatticePoint d))) :
    cfg \ boxEdges d L ∈ outsideBoxTwoArmEvent_config d M ↔
      cfg ∈ outsideBoxTwoArmEvent_config d M := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hxInf, hyInf, hnotConn⟩
    refine ⟨x, hx, y, hy, hxy, ?_, ?_, ?_⟩
    · simpa [openCluster_eraseBox_smaller_eq hLM x cfg] using hxInf
    · simpa [openCluster_eraseBox_smaller_eq hLM y cfg] using hyInf
    · intro hconn
      exact hnotConn ((bondConnectionEvent_eraseBox_smaller_iff hLM x y cfg).2 hconn)
  · rintro ⟨x, hx, y, hy, hxy, hxInf, hyInf, hnotConn⟩
    refine ⟨x, hx, y, hy, hxy, ?_, ?_, ?_⟩
    · simpa [openCluster_eraseBox_smaller_eq hLM x cfg] using hxInf
    · simpa [openCluster_eraseBox_smaller_eq hLM y cfg] using hyInf
    · intro hconn
      exact hnotConn ((bondConnectionEvent_eraseBox_smaller_iff hLM x y cfg).1 hconn)

/-- Helper for Theorem 2.46: once `L ≤ M`, the radius-`M` coexistence-tail stage is unchanged if
one first erases the smaller box `boxEdges 2 L`. -/
lemma coexistenceTailStageEvent_eraseBox_smaller_iff
    {L M : ℕ} (hLM : L ≤ M)
    (cfg : Set (Sym2 (LatticePoint 2))) :
    cfg \ boxEdges 2 L ∈ coexistenceTailStageEvent M ↔
      cfg ∈ coexistenceTailStageEvent M := by
  have hbox : boxEdges 2 L ⊆ boxEdges 2 M := boxEdges_mono (d := 2) hLM
  have hdiff :
      (cfg \ boxEdges 2 L) \ boxEdges 2 M = cfg \ boxEdges 2 M := by
    -- Proof comment: deleting the smaller box before deleting the larger one has no extra effect
    -- because the smaller box edges are already contained in the larger box.
    ext e
    constructor
    · rintro ⟨⟨heCfg, _heNotL⟩, heNotM⟩
      exact ⟨heCfg, heNotM⟩
    · rintro ⟨heCfg, heNotM⟩
      exact ⟨⟨heCfg, fun heL ↦ heNotM (hbox heL)⟩, heNotM⟩
  constructor
  · intro hcfg
    refine ⟨?_, ?_⟩
    · exact
        (outsideBoxTwoArmEvent_eraseBox_smaller_iff
          (d := 2) (L := L) (M := M) hLM cfg).1 hcfg.1
    · simpa [coexistenceTailStageEvent, hdiff] using hcfg.2
  · intro hcfg
    refine ⟨?_, ?_⟩
    · exact
        (outsideBoxTwoArmEvent_eraseBox_smaller_iff
          (d := 2) (L := L) (M := M) hLM cfg).2 hcfg.1
    · simpa [coexistenceTailStageEvent, hdiff] using hcfg.2

/-- Helper for Theorem 2.46: erasing any fixed finite box does not change the full coexistence
tail event. -/
lemma coexistenceTailEvent_eraseBox_iff
    (L : ℕ) (cfg : Set (Sym2 (LatticePoint 2))) :
    cfg \ boxEdges 2 L ∈ coexistenceTailEvent ↔
      cfg ∈ coexistenceTailEvent := by
  constructor
  · intro hcfg
    refine Set.mem_iInter.2 ?_
    intro N
    -- Proof comment: ask the erased configuration for a witness stage beyond both `N` and the
    -- erased radius `L`, then transport that stage back to the original configuration.
    have hTailAtMax : cfg \ boxEdges 2 L ∈ ⋃ M ∈ Set.Ici (max N L), coexistenceTailStageEvent M :=
      Set.mem_iInter.1 hcfg (max N L)
    rcases Set.mem_iUnion.1 hTailAtMax with ⟨M, hTailAtM⟩
    rcases Set.mem_iUnion.1 hTailAtM with ⟨hMlarge, hStage⟩
    have hLM : L ≤ M := le_trans (le_max_right N L) hMlarge
    have hStage' : cfg ∈ coexistenceTailStageEvent M :=
      (coexistenceTailStageEvent_eraseBox_smaller_iff (L := L) (M := M) hLM cfg).1 hStage
    exact
      Set.mem_iUnion.2 ⟨M, Set.mem_iUnion.2 ⟨le_trans (le_max_left N L) hMlarge, hStage'⟩⟩
  · intro hcfg
    refine Set.mem_iInter.2 ?_
    intro N
    -- Proof comment: the converse direction uses the same large witness stage and then erases the
    -- smaller box on that stage.
    have hTailAtMax : cfg ∈ ⋃ M ∈ Set.Ici (max N L), coexistenceTailStageEvent M :=
      Set.mem_iInter.1 hcfg (max N L)
    rcases Set.mem_iUnion.1 hTailAtMax with ⟨M, hTailAtM⟩
    rcases Set.mem_iUnion.1 hTailAtM with ⟨hMlarge, hStage⟩
    have hLM : L ≤ M := le_trans (le_max_right N L) hMlarge
    have hStage' : cfg \ boxEdges 2 L ∈ coexistenceTailStageEvent M :=
      (coexistenceTailStageEvent_eraseBox_smaller_iff (L := L) (M := M) hLM cfg).2 hStage
    exact
      Set.mem_iUnion.2 ⟨M, Set.mem_iUnion.2 ⟨le_trans (le_max_left N L) hMlarge, hStage'⟩⟩

/-- Helper for Theorem 2.46: the coexistence tail event is the preimage of itself under finite
box erasure. -/
lemma coexistenceTailEvent_eq_preimage_eraseBox
    (L : ℕ) :
    coexistenceTailEvent =
      (fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg \ boxEdges 2 L) ⁻¹' coexistenceTailEvent := by
  ext cfg
  -- Proof comment: membership in the preimage is exactly the erased-box version of the previous
  -- invariance statement.
  simpa using (coexistenceTailEvent_eraseBox_iff L cfg).symm

/-- Helper for Theorem 2.46: the coexistence tail event is independent of every prescribed finite
box pattern. -/
lemma coexistenceTailEvent_inter_boxPattern_eq_mul
    (L : ℕ) (A : Set (Sym2 (LatticePoint 2))) :
    ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
      (coexistenceTailEvent ∩ {cfg | cfg ∩ boxEdges 2 L = A}) =
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half coexistenceTailEvent *
          ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
            {cfg | cfg ∩ boxEdges 2 L = A} := by
  -- Proof comment: rewrite the tail event as an erased-box preimage and then apply the existing
  -- Bernoulli factorization across the finite inside-box coordinates.
  rw [coexistenceTailEvent_eq_preimage_eraseBox (L := L)]
  simpa using
    (eraseEdgesPreimage_inter_finitePattern_eq_mul
      (d := 2) (p := half)
      (F := boxEdges 2 L) (A := A) (E0 := coexistenceTailEvent)
      measurableSet_coexistenceTailEvent)

/-- Helper for Theorem 2.46: if one radius stage of the coexistence package has positive
half-critical mass, then intersecting that stage with the all-closed box cylinder at the same
radius keeps positive mass. -/
lemma coexistenceTailStageEvent_inter_closedBox_pos_of_pos
    (L : ℕ)
    (hStagePos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (coexistenceTailStageEvent L)) :
    0 <
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
        (coexistenceTailStageEvent L ∩ {cfg | cfg ∩ boxEdges 2 L = ∅}) := by
  have hClosedPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          {cfg | cfg ∩ boxEdges 2 L = ∅} := by
    -- Proof comment: the midpoint Bernoulli law assigns positive mass to the all-closed finite
    -- box pattern.
    simpa using
      finiteCylinderAllClosedPos
        (μ := ⟨ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half, inferInstance⟩)
        (openEdges := fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg)
        (p := half) half_ne_zero half_ne_one
        (canonicalBernoulli_id_isSetBernoulli half)
        (boxEdges_finite 2 L) (boxEdges_subset_edgeSet 2 L)
  -- Proof comment: combine the stage-wise factorization with positivity of the closed cylinder.
  rw [coexistenceTailStageEvent_inter_boxPattern_eq_mul (L := L) (A := ∅)]
  exact ENNReal.mul_pos (ne_of_gt hStagePos) (ne_of_gt hClosedPos)

/-- Helper for Theorem 2.46: on the all-closed radius-`L` box cylinder, the erased exact-two
factor inside a coexistence stage becomes the original canonical exact-two event. -/
lemma coexistenceTailStageEvent_inter_closedBox_subset_canonicalExactTwoEvent
    (L : ℕ) :
    coexistenceTailStageEvent L ∩ {cfg | cfg ∩ boxEdges 2 L = ∅} ⊆
      canonicalExactTwoEvent := by
  intro cfg hcfg
  have hStage : cfg ∈ coexistenceTailStageEvent L := hcfg.1
  have hClosed : cfg ∩ boxEdges 2 L = ∅ := hcfg.2
  have hErase :
      cfg \ boxEdges 2 L = cfg := by
    -- Proof comment: on the all-closed cylinder, erasing the radius-`L` box does nothing.
    simpa using eraseBox_eq_self_of_inter_boxEdges_eq_empty (d := 2) L hClosed
  -- Proof comment: after the erasure collapses to the identity, the stage's exact-two factor is
  -- exactly the original exact-two event.
  simpa [coexistenceTailStageEvent, hErase] using hStage.2

/-- Helper for Theorem 2.46: positive mass of one coexistence stage already forces positive mass
of the canonical exact-two event. -/
lemma canonicalExactTwoEvent_pos_of_coexistenceTailStageEventPos
    {L : ℕ}
    (hStagePos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (coexistenceTailStageEvent L)) :
    0 <
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
        canonicalExactTwoEvent := by
  have hClosedStagePos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (coexistenceTailStageEvent L ∩ {cfg | cfg ∩ boxEdges 2 L = ∅}) :=
    coexistenceTailStageEvent_inter_closedBox_pos_of_pos L hStagePos
  -- Proof comment: the positive closed-box slice sits inside the original exact-two event.
  refine lt_of_lt_of_le hClosedStagePos ?_
  exact
    measure_mono
      (coexistenceTailStageEvent_inter_closedBox_subset_canonicalExactTwoEvent L)

/-- Helper for Theorem 2.46: if the coexistence tail event has positive half-critical mass, then
its intersection with the all-closed radius-`L` box cylinder still has positive mass. -/
lemma coexistenceTailEvent_inter_closedBox_pos_of_pos
    (L : ℕ)
    (hTailPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          coexistenceTailEvent) :
    0 <
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
        (coexistenceTailEvent ∩ {cfg | cfg ∩ boxEdges 2 L = ∅}) := by
  have hClosedPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          {cfg | cfg ∩ boxEdges 2 L = ∅} := by
    -- Proof comment: the midpoint Bernoulli law gives positive mass to every all-closed finite
    -- box pattern.
    simpa using
      finiteCylinderAllClosedPos
        (μ := ⟨ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half, inferInstance⟩)
        (openEdges := fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg)
        (p := half) half_ne_zero half_ne_one
        (canonicalBernoulli_id_isSetBernoulli half)
        (boxEdges_finite 2 L) (boxEdges_subset_edgeSet 2 L)
  -- Proof comment: combine finite-box independence with positivity of the closed-cylinder factor.
  rw [coexistenceTailEvent_inter_boxPattern_eq_mul (L := L) (A := ∅)]
  exact ENNReal.mul_pos (ne_of_gt hTailPos) (ne_of_gt hClosedPos)

/-- Helper for Theorem 2.46: if the coexistence tail event has positive half-critical mass, then
its intersection with the all-open radius-`L` box cylinder still has positive mass. -/
lemma coexistenceTailEvent_inter_openBox_pos_of_pos
    (L : ℕ)
    (hTailPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          coexistenceTailEvent) :
    0 <
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
        (coexistenceTailEvent ∩ {cfg | cfg ∩ boxEdges 2 L = boxEdges 2 L}) := by
  have hOpenPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          {cfg | cfg ∩ boxEdges 2 L = boxEdges 2 L} := by
    -- Proof comment: the midpoint Bernoulli law also gives positive mass to the all-open finite
    -- box pattern.
    simpa using
      finiteCylinderPatternPos
        (μ := ⟨ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half, inferInstance⟩)
        (openEdges := fun cfg : Set (Sym2 (LatticePoint 2)) ↦ cfg)
        (p := half) half_ne_zero half_ne_one
        (canonicalBernoulli_id_isSetBernoulli half)
        (F := boxEdges 2 L) (A := boxEdges 2 L)
        (boxEdges_finite 2 L) (by intro e he; exact he) (boxEdges_subset_edgeSet 2 L)
  -- Proof comment: combine the same independence identity with positivity of the open-cylinder
  -- factor.
  rw [coexistenceTailEvent_inter_boxPattern_eq_mul (L := L) (A := boxEdges 2 L)]
  exact ENNReal.mul_pos (ne_of_gt hTailPos) (ne_of_gt hOpenPos)

/-- Helper for Theorem 2.46: intersecting a configuration with the actual lattice-edge set does
not change the canonical open bond graph. -/
lemma openBondGraph_inter_edgeSet_eq
    (cfg : Set (Sym2 (LatticePoint 2))) :
    openBondGraph
        (fun s : Set (Sym2 (LatticePoint 2)) ↦ s)
        (cfg ∩ (latticeGraph 2).edgeSet) =
      openBondGraph
        (fun s : Set (Sym2 (LatticePoint 2)) ↦ s)
        cfg := by
  ext x y
  rw [openBondGraph, openBondGraph, SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
  constructor <;> rintro ⟨hmem, hne⟩
  · refine ⟨?_, hne⟩
    simpa [Set.mem_inter_iff, and_assoc, and_left_comm, and_comm] using hmem
  · refine ⟨?_, hne⟩
    simpa [Set.mem_inter_iff, and_assoc, and_left_comm, and_comm] using hmem

/-- Helper for Theorem 2.46: erasing a fixed box after intersecting with the lattice-edge set gives
the same canonical open bond graph as erasing the box in the original configuration. -/
lemma openBondGraph_eraseBox_inter_edgeSet_eq
    (L : ℕ) (cfg : Set (Sym2 (LatticePoint 2))) :
    openBondGraph
        (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L)
        (cfg ∩ (latticeGraph 2).edgeSet) =
      openBondGraph
        (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L)
        cfg := by
  ext x y
  rw [openBondGraph, openBondGraph, SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
  constructor <;> rintro ⟨hmem, hne⟩
  · refine ⟨?_, hne⟩
    simpa [Set.mem_inter_iff, Set.mem_diff, and_assoc, and_left_comm, and_comm] using hmem
  · refine ⟨?_, hne⟩
    simpa [Set.mem_inter_iff, Set.mem_diff, and_assoc, and_left_comm, and_comm] using hmem

/-- Helper for Theorem 2.46: the canonical bond-connection event depends only on edges of
`latticeGraph 2`. -/
lemma bondConnectionEvent_inter_edgeSet_iff
    (x y : LatticePoint 2) (cfg : Set (Sym2 (LatticePoint 2))) :
    cfg ∩ (latticeGraph 2).edgeSet ∈
        bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) x y ↔
      cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s) x y := by
  -- Proof comment: `openBondGraph` already intersects with the lattice-edge set, so extra
  -- off-graph bonds are invisible to reachability.
  simpa [bondConnectionEvent, openBondGraph_inter_edgeSet_eq (cfg := cfg)]

/-- Helper for Theorem 2.46: the erased bond-connection event still depends only on actual lattice
edges. -/
lemma bondConnectionEvent_eraseBox_inter_edgeSet_iff
    (L : ℕ) (x y : LatticePoint 2) (cfg : Set (Sym2 (LatticePoint 2))) :
    cfg ∩ (latticeGraph 2).edgeSet ∈
        bondConnectionEvent
          (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) x y ↔
      cfg ∈
        bondConnectionEvent
          (fun s : Set (Sym2 (LatticePoint 2)) ↦ s \ boxEdges 2 L) x y := by
  -- Proof comment: erasing a finite box commutes with discarding non-lattice bonds because
  -- `boxEdges 2 L` itself lies inside the lattice-edge set.
  simpa [bondConnectionEvent, openBondGraph_eraseBox_inter_edgeSet_eq (L := L) (cfg := cfg)]

/-- Helper for Theorem 2.46: the canonical exact-two event only depends on the lattice bonds of
the configuration. -/
lemma canonicalExactTwoEvent_inter_edgeSet_iff
    (cfg : Set (Sym2 (LatticePoint 2))) :
    cfg ∩ (latticeGraph 2).edgeSet ∈ canonicalExactTwoEvent ↔
      cfg ∈ canonicalExactTwoEvent := by
  change
    infiniteOpenClusterCount
        (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s)))
        (cfg ∩ (latticeGraph 2).edgeSet) = 2 ↔
      infiniteOpenClusterCount
        (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s)))
        cfg = 2
  -- Proof comment: every cluster in the canonical graph already forgets off-graph bonds.
  simp_rw [infiniteOpenClusterCount, openCluster, bondConnectionEvent_inter_edgeSet_iff]

/-- Helper for Theorem 2.46: the radius-`L` coexistence stage depends only on the actual lattice
edges of the configuration. -/
lemma coexistenceTailStageEvent_inter_edgeSet_iff
    (L : ℕ) (cfg : Set (Sym2 (LatticePoint 2))) :
    cfg ∩ (latticeGraph 2).edgeSet ∈ coexistenceTailStageEvent L ↔
      cfg ∈ coexistenceTailStageEvent L := by
  constructor
  · rintro ⟨hOutside, hExact⟩
    refine ⟨?_, ?_⟩
    · rcases hOutside with ⟨x, hx, y, hy, hxy, hxInf, hyInf, hnotConn⟩
      refine ⟨x, hx, y, hy, hxy, ?_, ?_, ?_⟩
      · simpa [openCluster, bondConnectionEvent_eraseBox_inter_edgeSet_iff (L := L)] using hxInf
      · simpa [openCluster, bondConnectionEvent_eraseBox_inter_edgeSet_iff (L := L)] using hyInf
      · intro hconn
        exact hnotConn ((bondConnectionEvent_eraseBox_inter_edgeSet_iff (L := L) x y cfg).2 hconn)
    · have hEq :
          ((cfg ∩ (latticeGraph 2).edgeSet) \ boxEdges 2 L) ∩
              (latticeGraph 2).edgeSet =
            (cfg \ boxEdges 2 L) ∩ (latticeGraph 2).edgeSet := by
        ext e
        simp [Set.mem_inter_iff, Set.mem_diff, and_assoc, and_left_comm, and_comm]
      have hExact' :
          (cfg \ boxEdges 2 L) ∩ (latticeGraph 2).edgeSet ∈ canonicalExactTwoEvent := by
        have hEdgeExact :
            (((cfg ∩ (latticeGraph 2).edgeSet) \ boxEdges 2 L) ∩
                (latticeGraph 2).edgeSet) ∈ canonicalExactTwoEvent :=
          (canonicalExactTwoEvent_inter_edgeSet_iff
            (((cfg ∩ (latticeGraph 2).edgeSet) \ boxEdges 2 L))).2 hExact
        simpa [hEq] using hEdgeExact
      exact (canonicalExactTwoEvent_inter_edgeSet_iff ((cfg \ boxEdges 2 L))).1 hExact'
  · rintro ⟨hOutside, hExact⟩
    refine ⟨?_, ?_⟩
    · rcases hOutside with ⟨x, hx, y, hy, hxy, hxInf, hyInf, hnotConn⟩
      refine ⟨x, hx, y, hy, hxy, ?_, ?_, ?_⟩
      · simpa [openCluster, bondConnectionEvent_eraseBox_inter_edgeSet_iff (L := L)] using hxInf
      · simpa [openCluster, bondConnectionEvent_eraseBox_inter_edgeSet_iff (L := L)] using hyInf
      · intro hconn
        exact hnotConn ((bondConnectionEvent_eraseBox_inter_edgeSet_iff (L := L) x y cfg).1 hconn)
    · have hEq :
          ((cfg ∩ (latticeGraph 2).edgeSet) \ boxEdges 2 L) ∩
              (latticeGraph 2).edgeSet =
            (cfg \ boxEdges 2 L) ∩ (latticeGraph 2).edgeSet := by
        ext e
        simp [Set.mem_inter_iff, Set.mem_diff, and_assoc, and_left_comm, and_comm]
      have hExact' :
          (((cfg ∩ (latticeGraph 2).edgeSet) \ boxEdges 2 L) ∩
              (latticeGraph 2).edgeSet) ∈ canonicalExactTwoEvent := by
        have hEdgeExact :
            (cfg \ boxEdges 2 L) ∩ (latticeGraph 2).edgeSet ∈ canonicalExactTwoEvent :=
          (canonicalExactTwoEvent_inter_edgeSet_iff (cfg \ boxEdges 2 L)).2 hExact
        simpa [hEq] using hEdgeExact
      exact
        (canonicalExactTwoEvent_inter_edgeSet_iff
          ((cfg ∩ (latticeGraph 2).edgeSet) \ boxEdges 2 L)).1 hExact'

/-- Helper for Theorem 2.46: the full coexistence tail event depends only on the lattice bonds of
the configuration. -/
lemma coexistenceTailEvent_inter_edgeSet_iff
    (cfg : Set (Sym2 (LatticePoint 2))) :
    cfg ∩ (latticeGraph 2).edgeSet ∈ coexistenceTailEvent ↔
      cfg ∈ coexistenceTailEvent := by
  constructor
  · intro hcfg
    refine Set.mem_iInter.2 ?_
    intro N
    rcases Set.mem_iInter.1 hcfg N with hTail
    rcases Set.mem_iUnion.1 hTail with ⟨L, hTailL⟩
    rcases Set.mem_iUnion.1 hTailL with ⟨hL, hStage⟩
    exact
      Set.mem_iUnion.2 ⟨L, Set.mem_iUnion.2 ⟨hL,
        (coexistenceTailStageEvent_inter_edgeSet_iff L cfg).1 hStage⟩⟩
  · intro hcfg
    refine Set.mem_iInter.2 ?_
    intro N
    rcases Set.mem_iInter.1 hcfg N with hTail
    rcases Set.mem_iUnion.1 hTail with ⟨L, hTailL⟩
    rcases Set.mem_iUnion.1 hTailL with ⟨hL, hStage⟩
    exact
      Set.mem_iUnion.2 ⟨L, Set.mem_iUnion.2 ⟨hL,
        (coexistenceTailStageEvent_inter_edgeSet_iff L cfg).2 hStage⟩⟩

/-- Helper for Theorem 2.46: an exact-two configuration yields coarse outside-two-arm witnesses at
arbitrarily large radii. -/
lemma exists_large_outsideBoxTwoArmEvent_of_canonicalExactTwoEvent
    {cfg : Set (Sym2 (LatticePoint 2))}
    (hcfg : cfg ∈ canonicalExactTwoEvent) (N : ℕ) :
    ∃ L ∈ Set.Ici N, cfg ∈ outsideBoxTwoArmEvent_config 2 L := by
  rcases (infiniteOpenClusterCount_eq_two_iff
      (openEdges := fun s : Set (Sym2 (LatticePoint 2)) ↦ s) cfg).1 hcfg with
    ⟨x, y, hxInf, hyInf, hxy, _hcover⟩
  rcases exists_boxVertices_pred_contains_pair (d := 2) x y with
    ⟨L0, hL0pos, hxBox0, hyBox0⟩
  let L : ℕ := max N L0
  have hLN : N ≤ L := le_max_left N L0
  have hL0L : L0 ≤ L := le_max_right N L0
  have hLpos : 0 < L := lt_of_lt_of_le hL0pos hL0L
  have hxBox : x ∈ boxVertices 2 (L - 1) := by
    exact
      boxVertices_mono
        (d := 2)
        (L := L0 - 1)
        (M := L - 1)
        (Nat.sub_le_sub_right hL0L 1)
        hxBox0
  have hyBox : y ∈ boxVertices 2 (L - 1) := by
    exact
      boxVertices_mono
        (d := 2)
        (L := L0 - 1)
        (M := L - 1)
        (Nat.sub_le_sub_right hL0L 1)
        hyBox0
  rcases existsBoundaryShellInfiniteErasedClusterOfInfiniteCluster
      (d := 2) (L := L) (cfg := cfg) (x := x) hLpos hxBox hxInf with
    ⟨u, huShell, hxu, huInf⟩
  rcases existsBoundaryShellInfiniteErasedClusterOfInfiniteCluster
      (d := 2) (L := L) (cfg := cfg) (x := y) hLpos hyBox hyInf with
    ⟨v, hvShell, hyv, hvInf⟩
  rcases shellWitnesses_not_connected_of_roots_not_connected
      (d := 2) (L := L) hxu hyv hxy with
    ⟨huv, hnotConn⟩
  -- Proof comment: once the two infinite root clusters are pushed out to the boundary shell of a
  -- large box, they form the desired coarse outside-two-arm witness at that radius.
  exact ⟨L, hLN, ⟨u, huShell, v, hvShell, huv, huInf, hvInf, hnotConn⟩⟩

/-- Helper for Theorem 2.46: the strengthened radius-one seed already forces coarse outside-two-arm
occurrence at arbitrarily large radii. -/
lemma erasedExactTwoSeedEvent_subset_outsideBoxTwoArmTail
    (x y : LatticePoint 2) :
    erasedExactTwoSeedEvent x y ⊆
      ⋂ N : ℕ, ⋃ L ∈ Set.Ici N, outsideBoxTwoArmEvent_config 2 L := by
  intro cfg hcfg
  have hEraseExact : cfg \ boxEdges 2 1 ∈ canonicalExactTwoEvent := hcfg.2
  refine Set.mem_iInter.2 ?_
  intro N
  obtain ⟨L, hLlarge, hEraseOutside⟩ :=
    exists_large_outsideBoxTwoArmEvent_of_canonicalExactTwoEvent hEraseExact (max N 1)
  have hOneLe : 1 ≤ L := le_trans (le_max_right N 1) hLlarge
  have hOutside :
      cfg ∈ outsideBoxTwoArmEvent_config 2 L := by
    exact
      (outsideBoxTwoArmEvent_eraseBox_smaller_iff (d := 2) (L := 1) (M := L) hOneLe cfg).1
        hEraseOutside
  -- Proof comment: the exact-two factor lives on the radius-one erased configuration, and for
  -- larger radii that erased configuration yields the same coarse outside-two-arm witness data as
  -- the original configuration.
  exact Set.mem_iUnion.2 ⟨L, Set.mem_iUnion.2 ⟨le_trans (le_max_left N 1) hLlarge, hOutside⟩⟩

/-- Helper for Theorem 2.46: a positive strengthened radius-one seed already gives positive mass
to the first coexistence-tail stage. -/
lemma coexistenceTailStageEventOne_pos_of_erasedExactTwoSeedPos
    {x y : LatticePoint 2}
    (hseedPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (erasedExactTwoSeedEvent x y)) :
    0 <
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
        (coexistenceTailStageEvent 1) := by
  -- Proof comment: the strengthened seed is already a point of the first stage of the coexistence
  -- package, so positivity transfers by monotonicity.
  exact
    lt_of_lt_of_le hseedPos <|
      measure_mono (erasedExactTwoSeedEvent_subset_coexistenceTailStageEventOne x y)

/-- Helper for Theorem 2.46: a positive strengthened radius-one seed already forces positive mass
of the canonical exact-two event. -/
lemma canonicalExactTwoEvent_pos_of_erasedExactTwoSeedPos
    {x y : LatticePoint 2}
    (hseedPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (erasedExactTwoSeedEvent x y)) :
    0 <
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
        canonicalExactTwoEvent := by
  have hClosedSeedPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (erasedExactTwoSeedEvent x y ∩ {cfg | cfg ∩ boxEdges 2 1 = ∅}) :=
    erasedExactTwoSeedEvent_inter_closedBox_pos_of_pos hseedPos
  -- Proof comment: on the all-closed radius-one cylinder, the seed's erased exact-two factor is
  -- exactly the original exact-two event, so positivity transfers by monotonicity.
  refine lt_of_lt_of_le hClosedSeedPos ?_
  exact measure_mono (erasedExactTwoSeedEvent_inter_closedBox_subset_canonicalExactTwoEvent x y)

/-- Helper for Theorem 2.46: once a positive radius-one arm event is covered by shell-partner
slices, one concrete shell partner already carries positive Bernoulli mass. -/
lemma exists_pos_measure_shellPartnerSlice_of_subset_iUnion
    {x : LatticePoint 2}
    {E : LatticePoint 2 → Set (Set (Sym2 (LatticePoint 2)))}
    (hxPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (radiusOneOutsideArmEvent_config x))
    (hCover :
      radiusOneOutsideArmEvent_config x ⊆
        ⋃ y : {y // y ∈ boundaryShell 2 1 ∧ y ≠ x}, E y.1) :
    ∃ y : LatticePoint 2,
      y ∈ boundaryShell 2 1 ∧
      x ≠ y ∧
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (E y) := by
  let μ : Measure (Set (Sym2 (LatticePoint 2))) :=
    ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
  have hUnionPos :
      0 < μ (⋃ y : {y // y ∈ boundaryShell 2 1 ∧ y ≠ x}, E y.1) := by
    -- Proof comment: once the positive radius-one arm event sits inside the shell-partner union,
    -- monotonicity of measure transfers positivity to the whole union.
    exact lt_of_lt_of_le (by simpa [μ] using hxPos) (measure_mono hCover)
  obtain ⟨y, hyPos⟩ :
      ∃ y : {y // y ∈ boundaryShell 2 1 ∧ y ≠ x}, 0 < μ (E y.1) :=
    exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hUnionPos)
  -- Proof comment: unpack the positive subtype index back into a concrete shell partner.
  exact ⟨y.1, y.2.1, y.2.2.symm, by simpa [μ] using hyPos⟩

/-- Helper for Theorem 2.46: the off-critical threshold branches should come from one shared
complement-parameter duality package, rather than two separate public proof frontiers. -/
lemma canonicalBondPercolationOffCriticalViaDuality :
    (∀ p : unitInterval, p < half → canonicalBondPercolationTheta p = 0) ∧
      ∀ p : unitInterval, half < p → 0 < canonicalBondPercolationTheta p := by
  -- Route correction: the remaining off-critical work is one shared planar-duality argument in
  -- the complement parameter `σ p = 1 - p`; splitting it into two separate public sorries only
  -- duplicated the same missing dependency-closed bridge.
  -- TODO: prove the below-half vanishing and the above-half positivity simultaneously from one
  -- complement-parameter duality/crossing theorem, then project the two branches here.
  sorry

/-- Helper for Theorem 2.46: the below-half branch of the threshold package. -/
lemma canonicalBondPercolation_subcritical_below_half :
    ∀ p : unitInterval, p < half → canonicalBondPercolationTheta p = 0 := by
  -- Proof comment: this branch is the first projection of the shared off-critical duality
  -- package.
  exact canonicalBondPercolationOffCriticalViaDuality.1

/-- Helper for Theorem 2.46: the above-half branch of the threshold package. -/
lemma canonicalBondPercolation_supercritical_above_half :
    ∀ p : unitInterval, half < p → 0 < canonicalBondPercolationTheta p := by
  -- Proof comment: this branch is the second projection of the shared off-critical duality
  -- package.
  exact canonicalBondPercolationOffCriticalViaDuality.2

/-- Helper for Theorem 2.46: a positive half-critical radius-one outside arm refines to the
strengthened erased exact-two seed at some shell partner. -/
lemma radiusOneOutsideArm_half_to_erasedExactTwoSeed_pos
    {x : LatticePoint 2}
    (hxShell : x ∈ boundaryShell 2 1)
    (hxPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (radiusOneOutsideArmEvent_config x)) :
    ∃ y : LatticePoint 2,
      y ∈ boundaryShell 2 1 ∧
      x ≠ y ∧
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (erasedExactTwoSeedEvent x y) := by
  -- Route correction: the real missing radius-one bridge must already land in the erased
  -- exact-two world; the raw fixed witness event is too weak for the later tail promotion.
  -- TODO: first prove a shell-indexed cover of `radiusOneOutsideArmEvent_config x` by radius-one
  -- slices, then apply `exists_pos_measure_shellPartnerSlice_of_subset_iUnion` and transport the
  -- resulting positive slice through the missing deterministic slice-to-seed bridge.
  sorry

/-- Helper for Theorem 2.46: a positive strengthened radius-one seed forces full mass of the
canonical exact-two event. -/
lemma clusterCountEqTwo_full_of_erasedExactTwoSeed_pos
    {x y : LatticePoint 2}
    (hxShell : x ∈ boundaryShell 2 1)
    (hyShell : y ∈ boundaryShell 2 1)
    (hxy : x ≠ y)
    (hseedPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (erasedExactTwoSeedEvent x y)) :
    ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
      canonicalExactTwoEvent = 1 := by
  have hStageOnePos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (coexistenceTailStageEvent 1) :=
    coexistenceTailStageEventOne_pos_of_erasedExactTwoSeedPos hseedPos
  have hExactTwoPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          canonicalExactTwoEvent :=
    canonicalExactTwoEvent_pos_of_coexistenceTailStageEventPos hStageOnePos
  -- Route correction: the verified prefix is now stronger than the old coarse outside-arm tail.
  -- The seed gives a positive true coexistence stage and already forces positive exact-two mass.
  -- TODO: turn that positive stage into a positive genuine tail event, apply Kolmogorov `0-1` to
  -- the tail event, and then upgrade the resulting positive exact-two mass to full exact-two mass.
  have _ : 0 <
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
        (coexistenceTailStageEvent 1) := hStageOnePos
  have _ : 0 <
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
        canonicalExactTwoEvent := hExactTwoPos
  sorry

/-- Helper for Theorem 2.46: the strict threshold-side data needed by Kesten's theorem consists of
subcritical vanishing below `1/2` together with strict positivity above `1/2`. -/
lemma canonicalBondPercolationOffCriticalData :
    (∀ p : unitInterval, p < half → canonicalBondPercolationTheta p = 0) ∧
      ∀ p : unitInterval, half < p → 0 < canonicalBondPercolationTheta p := by
  -- Route correction: the previous monotonicity packaging was the wrong normal form for this
  -- theorem. The main result only consumes the threshold-side vanishing/positivity dichotomy.
  exact
    ⟨canonicalBondPercolation_subcritical_below_half,
      canonicalBondPercolation_supercritical_above_half⟩

/-- Helper for Theorem 2.46: a positive half-critical radius-one erased outside arm at a fixed
shell root should already produce a positive half-critical fixed outside-two-arm witness at the
same radius. -/
lemma radiusOnePlanarDualityPackage
    {x : LatticePoint 2}
    (hxShell : x ∈ boundaryShell 2 1)
    (hxPos :
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (radiusOneOutsideArmEvent_config x)) :
    ∃ y : LatticePoint 2,
      y ∈ boundaryShell 2 1 ∧
      x ≠ y ∧
      0 <
        ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
          (outsideBoxTwoArmWitnessEvent_config 2 1 x y) := by
  rcases radiusOneOutsideArm_half_to_erasedExactTwoSeed_pos hxShell hxPos with
    ⟨y, hyShell, hxy, hseedPos⟩
  refine ⟨y, hyShell, hxy, ?_⟩
  -- Proof comment: the strengthened seed event is contained in the fixed witness event, so its
  -- positive mass survives after forgetting the erased exact-two factor.
  exact lt_of_lt_of_le hseedPos <|
    measure_mono (erasedExactTwoSeedEvent_subset_witness x y)

/-- Helper for Theorem 2.46: positive half-critical origin percolation should force full mass of
the canonical exact-two event. -/
lemma canonicalClusterCountEqTwoFull_of_halfPositive
    (hhalfPos : 0 < canonicalBondPercolationTheta half) :
    ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
      canonicalExactTwoEvent = 1 := by
  -- Route correction: the remaining half-critical gap is not in the finite-box contradiction
  -- anymore. The missing input is exactly the half-critical bridge from `θ(1/2) > 0` to full
  -- mass of the canonical exact-two event.
  rcases exists_pos_measure_fixedRadiusOneOutsideArm_of_halfPositive hhalfPos with
    ⟨x, hxShell, hxPos⟩
  -- Proof comment: first strengthen the positive radius-one outside arm to a seed that already
  -- carries erased exact-two data.
  rcases radiusOneOutsideArm_half_to_erasedExactTwoSeed_pos hxShell hxPos with
    ⟨y, hyShell, hxy, hseedPos⟩
  -- Proof comment: the remaining blocker is now the tail/coexistence promotion from this single
  -- strengthened seed to full mass of the canonical exact-two event.
  exact clusterCountEqTwo_full_of_erasedExactTwoSeed_pos hxShell hyShell hxy hseedPos

/-- Helper for Theorem 2.46: the canonical origin-percolation probability vanishes at the critical
point `p = 1/2`. -/
lemma canonicalBondPercolationHalfNull :
    canonicalBondPercolationTheta half = 0 := by
  by_contra hhalfNeZero
  have hhalfPos : 0 < canonicalBondPercolationTheta half :=
    pos_iff_ne_zero.mpr hhalfNeZero
  have hExactTwoFull :
      ProbabilityTheory.setBernoulli (latticeGraph 2).edgeSet half
        {cfg : Set (Sym2 (LatticePoint 2)) |
          infiniteOpenClusterCount
              (openCluster (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint 2)) ↦ s))) cfg =
            2} = 1 :=
    canonicalClusterCountEqTwoFull_of_halfPositive hhalfPos
  -- Proof comment: once the missing half-critical bridge supplies full mass of the exact-two
  -- event, the in-file contradiction engine rules this out at the interior point `p = 1 / 2`.
  exact
    canonicalClusterCountEqTwoFull_contradiction
      half half_ne_zero half_ne_one hExactTwoFull

/-- Helper for Theorem 2.46: the half-threshold package needed for Kesten's theorem. -/
lemma canonicalBondPercolationThresholdDataAtHalf :
    (∀ p : unitInterval, p < half → canonicalBondPercolationTheta p = 0) ∧
      ∀ p : unitInterval, half < p → 0 < canonicalBondPercolationTheta p := by
  -- Proof comment: after repairing the helper surface, this threshold package is exactly the
  -- direct off-critical data.
  exact canonicalBondPercolationOffCriticalData

/-- Helper for Theorem 2.46: once the strict threshold-side behavior is known at `1 / 2`, the
critical value itself must equal `1 / 2`. -/
lemma criticalPercolationValue_eq_half_of_thresholdDataAtHalf
    (hthreshold :
      (∀ p : unitInterval, p < half → canonicalBondPercolationTheta p = 0) ∧
        ∀ p : unitInterval, half < p → 0 < canonicalBondPercolationTheta p) :
    criticalPercolationValue canonicalBondPercolationTheta = half := by
  -- Proof comment: the subcritical branch gives the lower bound `1 / 2 ≤ p_c`.
  have hhalf_le :
      half ≤ criticalPercolationValue canonicalBondPercolationTheta :=
    subcriticalPoint_le_criticalPercolationValue
      canonicalBondPercolationTheta half hthreshold.1
  have hcrit_le_half :
      criticalPercolationValue canonicalBondPercolationTheta ≤ half := by
    -- Proof comment: if `p_c` were strictly above `1 / 2`, an intermediate parameter would
    -- already be supercritical, contradicting the defining infimum property of `p_c`.
    by_contra hnot
    have hhalf_lt :
        half < criticalPercolationValue canonicalBondPercolationTheta :=
      lt_of_not_ge hnot
    obtain ⟨q, hq_lower, hq_upper⟩ :=
      exists_unitInterval_between_half_and
        (criticalPercolationValue canonicalBondPercolationTheta) hhalf_lt
    have hq_pos : 0 < canonicalBondPercolationTheta q :=
      hthreshold.2 q hq_lower
    have hcrit_le_q :
        criticalPercolationValue canonicalBondPercolationTheta ≤ q :=
      criticalPercolationValue_le_of_positive canonicalBondPercolationTheta hq_pos
    exact hq_upper.not_ge hcrit_le_q
  exact le_antisymm hcrit_le_half hhalf_le

/-- Theorem 2.46 (Kesten 1980): for bond percolation on `ℤ²`, the critical value is `1/2` and the
origin percolation probability vanishes at the critical point. -/
theorem canonicalBondPercolationKesten :
    criticalPercolationValue canonicalBondPercolationTheta = half ∧
      canonicalBondPercolationTheta half = 0 := by
  -- Route correction: the previous failure here was structural file loss, not a defect in the
  -- theorem statement. The theorem now reduces to the compact half-threshold interface.
  have hthreshold := canonicalBondPercolationThresholdDataAtHalf
  refine ⟨criticalPercolationValue_eq_half_of_thresholdDataAtHalf hthreshold, ?_⟩
  -- Proof comment: the boundary-value conclusion is the separate half-critical nullity helper.
  exact canonicalBondPercolationHalfNull
