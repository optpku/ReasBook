/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.BondPercolationAPI
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_26

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped unitInterval
open unitInterval

universe u

variable {Ω : Type u} {d : ℕ}

/-- The canonical box of radius `L` in `Z^d`. -/
def boxVertices (d : ℕ) (L : ℕ) : Set (LatticePoint d) :=
  {x | ∀ i : Fin d, x i ∈ Set.Icc (-(L : ℤ)) (L : ℤ)}

/-- The boundary shell `B_L \ B_{L-1}` of the canonical radius-`L` box. -/
def boundaryShell (d : ℕ) (L : ℕ) : Set (LatticePoint d) :=
  boxVertices d L \ boxVertices d (L - 1)

/-- The lattice bonds with both endpoints inside the canonical radius-`L` box. -/
def boxEdges (d : ℕ) (L : ℕ) : Set (Sym2 (LatticePoint d)) :=
  {e | ∃ x ∈ boxVertices d L, ∃ y ∈ boxVertices d L, e = s(x, y) ∧ (latticeGraph d).Adj x y}

/-- The canonical box `B_L` is finite. -/
lemma boxVertices_finite (d : ℕ) (L : ℕ) :
    (boxVertices d L).Finite := by
  -- Proof comment: each coordinate ranges over the finite interval `[-L, L]`, so the whole box
  -- is a finite product of finite sets.
  simpa [boxVertices, Set.pi, Set.setOf_forall] using
    (Set.Finite.pi' fun _ : Fin d => Set.finite_Icc (-(L : ℤ)) (L : ℤ))

/-- The boundary shell of a canonical box is finite. -/
lemma boundaryShell_finite (d : ℕ) (L : ℕ) :
    (boundaryShell d L).Finite := by
  -- Proof comment: the shell is a subset of the finite box `B_L`.
  exact (boxVertices_finite d L).subset (by intro x hx; exact hx.1)

/-- The canonical box-edge set is finite. -/
lemma boxEdges_finite (d : ℕ) (L : ℕ) :
    (boxEdges d L).Finite := by
  let vertexPairs : Set (LatticePoint d × LatticePoint d) :=
    boxVertices d L ×ˢ boxVertices d L
  have hPairs : vertexPairs.Finite :=
    (boxVertices_finite d L).prod (boxVertices_finite d L)
  let edgeOfPair : LatticePoint d × LatticePoint d → Sym2 (LatticePoint d) :=
    fun p ↦ s(p.1, p.2)
  have hImage : (edgeOfPair '' vertexPairs).Finite :=
    hPairs.image edgeOfPair
  -- Proof comment: every box edge comes from a pair of box vertices, so it lies in the image of
  -- the finite product `B_L × B_L`.
  refine hImage.subset ?_
  intro e he
  rcases he with ⟨x, hx, y, hy, rfl, _⟩
  exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩

/-- Every canonical box edge is an edge of `latticeGraph d`. -/
lemma boxEdges_subset_edgeSet (d : ℕ) (L : ℕ) :
    boxEdges d L ⊆ (latticeGraph d).edgeSet := by
  -- Proof comment: `boxEdges` explicitly requires lattice adjacency of its endpoints.
  intro e he
  rcases he with ⟨x, _, y, _, rfl, hxy⟩
  simpa [SimpleGraph.mem_edgeSet] using hxy

/-- The canonical boxes are monotone in the radius. -/
lemma boxVertices_mono
    {L M : ℕ} (hLM : L ≤ M) :
    boxVertices d L ⊆ boxVertices d M := by
  intro x hx i
  rcases hx i with ⟨hlo, hhi⟩
  have hneg : -((M : ℕ) : ℤ) ≤ -((L : ℕ) : ℤ) := by
    omega
  have hpos : ((L : ℕ) : ℤ) ≤ ((M : ℕ) : ℤ) := by
    exact_mod_cast hLM
  -- Proof comment: enlarging the radius only widens the coordinate interval `[-L, L]`.
  exact ⟨le_trans hneg hlo, le_trans hhi hpos⟩

/-- One nearest-neighbor step from `B_{L-1}` still lands inside `B_L`. -/
lemma boxVertices_succ_of_adj_mem_pred
    {x y : LatticePoint d} {L : ℕ}
    (hL : 0 < L)
    (hx : x ∈ boxVertices d (L - 1))
    (hxy : (latticeGraph d).Adj x y) :
    y ∈ boxVertices d L := by
  rcases (latticeGraph_adj_iff x y).mp hxy with ⟨i, hi, hsame⟩
  intro j
  by_cases hj : j = i
  · subst j
    rcases hx i with ⟨hxlo, hxhi⟩
    have habs : |x i - y i| = (1 : ℤ) := by
      simpa [Int.natCast_natAbs] using congrArg (fun n : ℕ ↦ (n : ℤ)) hi
    have hstep : -1 ≤ x i - y i ∧ x i - y i ≤ 1 := by
      exact abs_le.mp (by simpa [habs] using le_rfl : |x i - y i| ≤ (1 : ℤ))
    -- Proof comment: the unique changed coordinate moves by at most one, so `[-(L-1), L-1]`
    -- widens to `[-L, L]`.
    have hxylow : x i - 1 ≤ y i := by linarith [hstep.2]
    have hxlow' : -((L : ℕ) : ℤ) ≤ x i - 1 := by
      have hshift : -(((L - 1 : ℕ) : ℤ)) - 1 = -((L : ℕ) : ℤ) := by
        omega
      simpa [hshift] using sub_le_sub_right hxlo 1
    have hylo : -((L : ℕ) : ℤ) ≤ y i := le_trans hxlow' hxylow
    have hxyhigh : y i ≤ x i + 1 := by linarith [hstep.1]
    have hxhigh' : x i + 1 ≤ ((L : ℕ) : ℤ) := by
      have hshift : (((L - 1 : ℕ) : ℤ)) + 1 = ((L : ℕ) : ℤ) := by
        omega
      have hxhi' : x i + 1 ≤ (((L - 1 : ℕ) : ℤ)) + 1 := by
        linarith
      simpa [hshift] using hxhi'
    exact ⟨hylo, le_trans hxyhigh hxhigh'⟩
  · have hsame' : y j = x j := (hsame j hj).symm
    have hxInL : x ∈ boxVertices d L :=
      boxVertices_mono (d := d) (L := L - 1) (M := L) (Nat.sub_le _ _) hx
    simpa [hsame'] using hxInL j

/-- If an edge exits `B_L` from a vertex still inside `B_L`, then that inside endpoint lies on
the shell `B_L \ B_{L-1}`. -/
lemma mem_boundaryShell_of_adj_outside_box
    {x y : LatticePoint d} {L : ℕ}
    (hL : 0 < L)
    (hx : x ∈ boxVertices d L)
    (hy : y ∉ boxVertices d L)
    (hxy : (latticeGraph d).Adj x y) :
    x ∈ boundaryShell d L := by
  refine ⟨hx, ?_⟩
  intro hxPred
  have hyIn : y ∈ boxVertices d L :=
    boxVertices_succ_of_adj_mem_pred (d := d) hL hxPred hxy
  exact hy hyIn

/-- An infinite open cluster rooted inside `B_L` must reach some vertex outside `B_L`. -/
lemma exists_connected_outside_box_of_infinite_cluster
    (openEdges : Ω → Set (Sym2 (LatticePoint d))) (ω : Ω) {x : LatticePoint d} {L : ℕ}
    (hinf : Set.Infinite (openCluster (bondConnectionEvent openEdges) x ω)) :
    ∃ y : LatticePoint d, y ∉ boxVertices d L ∧ ω ∈ bondConnectionEvent openEdges x y := by
  have hnot_subset :
      ¬ openCluster (bondConnectionEvent openEdges) x ω ⊆ boxVertices d L := by
    intro hsubset
    exact ((boxVertices_finite d L).subset hsubset).not_infinite hinf
  rcases Set.not_subset.mp hnot_subset with ⟨y, hyCluster, hyOut⟩
  -- Proof comment: any witness outside the finite box already gives the required connection.
  refine ⟨y, hyOut, ?_⟩
  simpa [openCluster_mem_iff] using hyCluster

/-- Any two lattice sites are contained in a common predecessor box `B_{L-1}`. -/
lemma exists_boxVertices_pred_contains_pair
    (x y : LatticePoint d) :
    ∃ L : ℕ, 0 < L ∧ x ∈ boxVertices d (L - 1) ∧ y ∈ boxVertices d (L - 1) := by
  let R : ℕ :=
    Finset.univ.sup fun i : Fin d ↦ max (Int.natAbs (x i)) (Int.natAbs (y i))
  refine ⟨R + 1, Nat.succ_pos _, ?_, ?_⟩
  · intro i
    have hsup : max (Int.natAbs (x i)) (Int.natAbs (y i)) ≤ R := by
      exact Finset.le_sup (s := Finset.univ) (f := fun j : Fin d ↦
        max (Int.natAbs (x j)) (Int.natAbs (y j))) (Finset.mem_univ i)
    have hxR : Int.natAbs (x i) ≤ R := by
      exact le_trans (le_max_left _ _) hsup
    have hxi : -((R : ℕ) : ℤ) ≤ x i ∧ x i ≤ ((R : ℕ) : ℤ) := by
      omega
    -- Proof comment: the sup over coordinate absolute values bounds the `i`-th coordinate.
    simpa [R] using hxi
  · intro i
    have hsup : max (Int.natAbs (x i)) (Int.natAbs (y i)) ≤ R := by
      exact Finset.le_sup (s := Finset.univ) (f := fun j : Fin d ↦
        max (Int.natAbs (x j)) (Int.natAbs (y j))) (Finset.mem_univ i)
    have hyR : Int.natAbs (y i) ≤ R := by
      exact le_trans (le_max_right _ _) hsup
    have hyi : -((R : ℕ) : ℤ) ≤ y i ∧ y i ≤ ((R : ℕ) : ℤ) := by
      omega
    -- Proof comment: the same radius works for the second root.
    simpa [R] using hyi

/-- A path from a point inside `B_L` to a point outside `B_L` meets the shell at a last in-box
vertex, and the remaining tail survives deleting `boxEdges d L`. -/
lemma existsBoundaryShellBridgeOfConnectedOutsideBox
    {L : ℕ} {cfg : Set (Sym2 (LatticePoint d))} {x y : LatticePoint d}
    (hL : 0 < L)
    (hx : x ∈ boxVertices d L)
    (hy : y ∉ boxVertices d L)
    (hxy : cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x y) :
    ∃ z ∈ boundaryShell d L,
      cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x z ∧
      cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) z y := by
  classical
  let Gcfg : SimpleGraph (LatticePoint d) :=
    openBondGraph (fun s : Set (Sym2 (LatticePoint d)) ↦ s) cfg
  rcases hxy with ⟨p⟩
  let q : Gcfg.Path x y := p.toPath
  let r : Gcfg.Walk y x := ((q : Gcfg.Walk x y)).reverse
  let sBox : Finset (LatticePoint d) := (boxVertices_finite d L).toFinset
  have hboxNonempty : {u ∈ sBox | u ∈ r.support}.Nonempty := by
    refine ⟨x, Finset.mem_filter.mpr ?_⟩
    exact ⟨(boxVertices_finite d L).mem_toFinset.mpr hx, r.end_mem_support⟩
  obtain ⟨z, hzBoxFin, hzSupport, hzfirst⟩ :=
    r.exists_mem_support_forall_mem_support_imp_eq sBox hboxNonempty
  have hzBox : z ∈ boxVertices d L :=
    (boxVertices_finite d L).mem_toFinset.mp hzBoxFin
  let rTake : Gcfg.Walk y z := r.takeUntil z hzSupport
  let tail : Gcfg.Walk z y := rTake.reverse
  have hy_ne_z : y ≠ z := by
    intro hyz
    exact hy (hyz ▸ hzBox)
  have hrTake_not_nil : ¬ rTake.Nil := by
    simpa [rTake, SimpleGraph.Walk.nil_takeUntil] using hy_ne_z
  have htail_not_nil : ¬ tail.Nil := by
    simpa [tail] using hrTake_not_nil
  have htailAdj : Gcfg.Adj z tail.snd := by
    exact SimpleGraph.Walk.adj_snd htail_not_nil
  have htailSnd_ne : tail.snd ≠ z := htailAdj.ne.symm
  have htailSnd_out : tail.snd ∉ boxVertices d L := by
    intro hIn
    have hInFin : tail.snd ∈ sBox := (boxVertices_finite d L).mem_toFinset.mpr hIn
    have hInTake : tail.snd ∈ rTake.support := by
      simpa [tail, SimpleGraph.Walk.support_reverse] using tail.getVert_mem_support 1
    exact htailSnd_ne (hzfirst (tail.snd) hInFin hInTake)
  have htailAdjLattice : (latticeGraph d).Adj z tail.snd := by
    change (SimpleGraph.fromEdgeSet (cfg ∩ (latticeGraph d).edgeSet)).Adj z tail.snd at htailAdj
    rw [SimpleGraph.fromEdgeSet_adj] at htailAdj
    simpa [SimpleGraph.mem_edgeSet] using htailAdj.1.2
  have hzShell : z ∈ boundaryShell d L :=
    mem_boundaryShell_of_adj_outside_box (d := d) hL hzBox htailSnd_out htailAdjLattice
  have hzSupport_q : z ∈ (q : Gcfg.Walk x y).support := by
    simpa [r, SimpleGraph.Walk.support_reverse] using hzSupport
  have hxzReach : Gcfg.Reachable x z := by
    -- Proof comment: the prefix of the witness path up to the shell vertex still connects `x`
    -- to `z`.
    exact ((q : Gcfg.Walk x y).takeUntil z hzSupport_q).reachable
  have htailNoBoxEdges : ∀ e, e ∈ tail.edges → e ∉ boxEdges d L := by
    intro e he hed
    rcases hed with ⟨u, huBox, v, hvBox, rfl, huvAdj⟩
    have huInTake : u ∈ rTake.support := by
      simpa [tail, SimpleGraph.Walk.support_reverse] using tail.fst_mem_support_of_mem_edges he
    have hvInTake : v ∈ rTake.support := by
      simpa [tail, SimpleGraph.Walk.support_reverse] using tail.snd_mem_support_of_mem_edges he
    have huEq : u = z := hzfirst u ((boxVertices_finite d L).mem_toFinset.mpr huBox) huInTake
    have hvEq : v = z := hzfirst v ((boxVertices_finite d L).mem_toFinset.mpr hvBox) hvInTake
    subst u
    subst v
    exact (latticeGraph d).loopless.irrefl z huvAdj
  have hdeleteEq :
      Gcfg.deleteEdges (boxEdges d L) =
        openBondGraph (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) cfg := by
    change
      (SimpleGraph.fromEdgeSet (cfg ∩ (latticeGraph d).edgeSet)).deleteEdges (boxEdges d L) =
        SimpleGraph.fromEdgeSet ((cfg \ boxEdges d L) ∩ (latticeGraph d).edgeSet)
    rw [SimpleGraph.deleteEdges_fromEdgeSet]
    have hsetEq :
        (cfg ∩ (latticeGraph d).edgeSet) \ boxEdges d L =
          (cfg \ boxEdges d L) ∩ (latticeGraph d).edgeSet := by
      ext e
      by_cases hcfg : e ∈ cfg <;> by_cases hedge : e ∈ (latticeGraph d).edgeSet <;>
          by_cases hbox : e ∈ boxEdges d L <;>
          simp [Set.mem_diff, hcfg, hedge, hbox, and_assoc]
    rw [hsetEq]
  have hzyReach :
      (openBondGraph (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L) cfg).Reachable z y := by
    have hReachDelete : (Gcfg.deleteEdges (boxEdges d L)).Reachable z y :=
      (tail.toDeleteEdges (boxEdges d L) htailNoBoxEdges).reachable
    rwa [hdeleteEq] at hReachDelete
  refine ⟨z, hzShell, ?_, ?_⟩
  · exact hxzReach
  · exact hzyReach

/-- An infinite cluster meeting `B_{L-1}` yields a shell vertex whose erased-box cluster is still
infinite. -/
lemma existsBoundaryShellInfiniteErasedClusterOfInfiniteCluster
    {L : ℕ} {cfg : Set (Sym2 (LatticePoint d))} {x : LatticePoint d}
    (hL : 0 < L)
    (hx : x ∈ boxVertices d (L - 1))
    (hinf :
      Set.Infinite
        (openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s)) x cfg)) :
    ∃ z ∈ boundaryShell d L,
      cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x z ∧
      Set.Infinite
        (openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s \ boxEdges d L)) z cfg) := by
  classical
  let eraseOpen : Set (Sym2 (LatticePoint d)) → Set (Sym2 (LatticePoint d)) :=
    fun s ↦ s \ boxEdges d L
  let shellRoots : Set (LatticePoint d) :=
    {z | z ∈ boundaryShell d L ∧
      cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x z}
  have hxL : x ∈ boxVertices d L :=
    boxVertices_mono (d := d) (L := L - 1) (M := L) (Nat.sub_le _ _) hx
  by_contra hno
  have hfiniteShellRoots : shellRoots.Finite :=
    (boundaryShell_finite d L).subset fun _ hz ↦ by simpa [shellRoots] using hz.1
  have hfiniteShellUnion :
      (⋃ z ∈ shellRoots,
        openCluster (bondConnectionEvent eraseOpen) z cfg).Finite := by
    refine hfiniteShellRoots.biUnion ?_
    intro z hz
    have hz' : z ∈ boundaryShell d L ∧
        cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x z := by
      simpa [shellRoots] using hz
    have hzfinite :
        (openCluster (bondConnectionEvent eraseOpen) z cfg).Finite := by
      apply Set.not_infinite.mp
      intro hzinf
      exact hno ⟨z, hz'.1, hz'.2, hzinf⟩
    exact hzfinite
  have hcover :
      openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s)) x cfg ⊆
        boxVertices d L ∪
          ⋃ z ∈ shellRoots, openCluster (bondConnectionEvent eraseOpen) z cfg := by
    intro y hyCluster
    by_cases hyIn : y ∈ boxVertices d L
    · exact Or.inl hyIn
    · have hxy :
          cfg ∈ bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s) x y := by
        simpa [openCluster_mem_iff] using hyCluster
      rcases existsBoundaryShellBridgeOfConnectedOutsideBox
          (d := d) (L := L) (cfg := cfg) (x := x) (y := y) hL hxL hyIn hxy with
        ⟨z, hzShell, hxz, hzy⟩
      refine Or.inr <| Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ?_⟩
      refine ⟨by simpa [shellRoots] using And.intro hzShell hxz, ?_⟩
      simpa [openCluster_mem_iff] using hzy
  have hfiniteCluster :
      (openCluster
          (bondConnectionEvent (fun s : Set (Sym2 (LatticePoint d)) ↦ s)) x cfg).Finite :=
    ((boxVertices_finite d L).union hfiniteShellUnion).subset hcover
  -- Proof comment: if every shell-rooted erased cluster were finite, then the original cluster
  -- would sit inside a finite union of finite sets.
  exact hfiniteCluster.not_infinite hinf

/-- Deleting a fixed family of edges from a configuration is measurable on the canonical
configuration space. -/
lemma measurable_eraseEdges_config
    (F : Set (Sym2 (LatticePoint d))) :
    Measurable (fun cfg : Set (Sym2 (LatticePoint d)) ↦ cfg \ F) := by
  let e : ((Sym2 (LatticePoint d)) → Prop) ≃ᵐ Set (Sym2 (LatticePoint d)) :=
    MeasurableEquiv.setOf
  have hpred :
      Measurable
        (fun q : (Sym2 (LatticePoint d)) → Prop ↦
          fun a : Sym2 (LatticePoint d) ↦ q a ∧ a ∉ F) := by
    -- Proof comment: under `Set α ≃ᵐ (α → Prop)`, deletion is coordinatewise conjunction with
    -- the deterministic predicate `a ∉ F`.
    fun_prop
  simpa using e.measurable.comp (hpred.comp e.symm.measurable)

/-- Intersecting a configuration with a fixed edge set is measurable on the canonical
configuration space. -/
lemma measurable_interEdges_config
    (F : Set (Sym2 (LatticePoint d))) :
    Measurable (fun cfg : Set (Sym2 (LatticePoint d)) ↦ cfg ∩ F) := by
  let e : ((Sym2 (LatticePoint d)) → Prop) ≃ᵐ Set (Sym2 (LatticePoint d)) :=
    MeasurableEquiv.setOf
  have hpred :
      Measurable
        (fun q : (Sym2 (LatticePoint d)) → Prop ↦
          fun a : Sym2 (LatticePoint d) ↦ q a ∧ a ∈ F) := by
    -- Proof comment: intersection is the analogous coordinatewise deterministic conjunction.
    fun_prop
  simpa using e.measurable.comp (hpred.comp e.symm.measurable)

/-- A predicate on a subtype determines the corresponding ambient set supported on that subtype. -/
def supportedSetOf {α : Type*} (S : Set α) (q : S → Prop) : Set α :=
  {a | ∃ ha : a ∈ S, q ⟨a, ha⟩}

/-- The ambient set supported on a subtype varies measurably with the predicate on that subtype. -/
lemma measurable_supportedSetOf {α : Type*} [Countable α] (S : Set α) :
    Measurable (supportedSetOf S) := by
  let e : (α → Prop) ≃ᵐ Set α := MeasurableEquiv.setOf
  have hcore : Measurable (fun q : S → Prop => fun a : α ↦ ∃ ha : a ∈ S, q ⟨a, ha⟩) := by
    -- Proof comment: each ambient coordinate depends on at most one subtype coordinate.
    fun_prop
  simpa [supportedSetOf] using e.measurable.comp hcore

/-- Restricting an ambient predicate to a subtype and rebuilding the ambient set simply
intersects with the support set. -/
lemma supportedSetOf_restrict_eq_inter {α : Type*} (S : Set α) (q : α → Prop) :
    supportedSetOf S (fun a : S ↦ q a) = {a | q a} ∩ S := by
  -- Proof comment: rebuilding from the subtype keeps exactly the coordinates in `S` that satisfy
  -- the original predicate.
  ext a
  constructor
  · rintro ⟨haS, ha⟩
    exact ⟨ha, haS⟩
  · rintro ⟨ha, haS⟩
    exact ⟨haS, ha⟩

/-- Rebuilding from the complementary block gives exactly the ambient configuration with the
supporting set deleted. -/
lemma supportedSetOf_restrict_compl_eq_diff {α : Type*} (S : Set α) (q : α → Prop) :
    supportedSetOf {a | a ∉ S} (fun a : {b // b ∉ S} ↦ q a) = {a | q a} \ S := by
  -- Proof comment: the complement-supported reconstruction keeps precisely the coordinates that
  -- survive deleting `S`.
  simpa [Set.diff_eq, Set.ext_iff, and_left_comm, and_assoc, and_comm] using
    supportedSetOf_restrict_eq_inter {a | a ∉ S} q

/-- Under the Bernoulli product law on predicate-valued configurations, the coordinates indexed by
`F` are independent of the complementary coordinates indexed by `Fᶜ`. -/
lemma indepFun_memBlock_memBlockCompl
    {α : Type*} [Countable α] (u F : Set α) (p : unitInterval) :
    let ν : α → Measure Prop := fun i : α ↦
      toNNReal p • Measure.dirac (i ∈ u) + toNNReal (σ p) • Measure.dirac False
    IndepFun
      (fun q : α → Prop ↦ fun e : {x // x ∈ F} ↦ q e)
      (fun q : α → Prop ↦ fun e : {x // x ∉ F} ↦ q e)
      (Measure.infinitePi ν) := by
  classical
  let ν : α → Measure Prop := fun i : α ↦
    toNNReal p • Measure.dirac (i ∈ u) + toNNReal (σ p) • Measure.dirac False
  let blocks : Fin 2 → Set α := fun b ↦ if b = 0 then F else {x | x ∉ F}
  have hdisjoint : Pairwise fun k l ↦ Disjoint (blocks k) (blocks l) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · cases (hkl rfl)
    · rw [Set.disjoint_left]
      intro x hxF hxCompl
      exact hxCompl hxF
    · rw [Set.disjoint_left]
      intro x hxCompl hxF
      exact hxCompl hxF
    · cases (hkl rfl)
  have hind :
      iIndepFun (fun i (q : α → Prop) ↦ q i) (Measure.infinitePi ν) := by
    -- Proof comment: the Bernoulli product law is an independent product of one-coordinate laws.
    exact iIndepFun_infinitePi (P := ν) (fun _ ↦ measurable_id)
  have hblock :
      iIndepFun (fun b (q : α → Prop) (j : blocks b) ↦ q j) (Measure.infinitePi ν) := by
    -- Proof comment: Theorem 2.26 groups the product coordinates into the inside block `F` and
    -- the outside block `Fᶜ`.
    refine iIndepFun_block_of_pairwise_disjoint_blocks (μ := Measure.infinitePi ν)
      (X := fun i (q : α → Prop) ↦ q i) blocks hdisjoint ?_ ?_
    · simpa [ν] using hind
    · intro i
      fun_prop
  have hpair := hblock.indepFun (i := 0) (j := 1) (by decide)
  simpa [ν, blocks] using hpair

/-- Under the canonical Bernoulli law, prescribing the finite inside-box pattern on `F` is
independent of any event seen only after erasing `F`. -/
lemma eraseEdgesPreimage_inter_finitePattern_eq_mul
    (p : unitInterval)
    {F A : Set (Sym2 (LatticePoint d))}
    {E0 : Set (Set (Sym2 (LatticePoint d)))}
    (hE0 : MeasurableSet E0) :
    ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p
      (((fun cfg : Set (Sym2 (LatticePoint d)) ↦ cfg \ F) ⁻¹' E0) ∩
        {cfg | cfg ∩ F = A}) =
      ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p
        ((fun cfg : Set (Sym2 (LatticePoint d)) ↦ cfg \ F) ⁻¹' E0) *
      ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p {cfg | cfg ∩ F = A} := by
  classical
  let α := Sym2 (LatticePoint d)
  let e : (α → Prop) ≃ᵐ Set α := MeasurableEquiv.setOf
  let ν : α → Measure Prop := fun a : α ↦
    toNNReal p • Measure.dirac (a ∈ (latticeGraph d).edgeSet) + toNNReal (σ p) • Measure.dirac False
  let insideRestr : (α → Prop) → ({a // a ∈ F} → Prop) := fun q a ↦ q a
  let outsideRestr : (α → Prop) → ({a // a ∉ F} → Prop) := fun q a ↦ q a
  let insideEvent : Set ({a // a ∈ F} → Prop) := {q | supportedSetOf F q = A}
  let outsideEvent : Set ({a // a ∉ F} → Prop) :=
    {q | supportedSetOf {a : α | a ∉ F} q ∈ E0}
  have hmap_set :
      Measure.map e (Measure.infinitePi ν) =
        ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p := by
    symm
    simpa [e, ν] using
      (ProbabilityTheory.setBernoulli_eq_map (u := (latticeGraph d).edgeSet) (p := p))
  have hfieldLaw :
      Measure.map e.symm (ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p) =
        Measure.infinitePi ν := by
    exact
      (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq
        (μ := Measure.infinitePi ν)
        (ν := ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p)
        (e := e)).mp hmap_set |>.symm
  have hinsideMeas : MeasurableSet insideEvent := by
    -- Proof comment: the inside pattern event is a singleton preimage under the measurable
    -- support-reconstruction map on the finite block `F`.
    exact measurableSet_preimage (measurable_supportedSetOf F) (MeasurableSet.singleton A)
  have houtsideMeas : MeasurableSet outsideEvent := by
    -- Proof comment: the erased outside event is the corresponding preimage on the complementary
    -- block.
    exact measurableSet_preimage (measurable_supportedSetOf {a : α | a ∉ F}) hE0
  have hinsidePreMeas : MeasurableSet (insideRestr ⁻¹' insideEvent) := by
    exact measurableSet_preimage (by fun_prop) hinsideMeas
  have houtsidePreMeas : MeasurableSet (outsideRestr ⁻¹' outsideEvent) := by
    exact measurableSet_preimage (by fun_prop) houtsideMeas
  have hleft_preimage :
      e.symm ⁻¹' (insideRestr ⁻¹' insideEvent ∩ outsideRestr ⁻¹' outsideEvent) =
        (((fun cfg : Set α ↦ cfg \ F) ⁻¹' E0) ∩ {cfg | cfg ∩ F = A}) := by
    ext cfg
    constructor
    · intro hcfg
      rcases hcfg with ⟨hinside, houtside⟩
      refine ⟨?_, ?_⟩
      · change supportedSetOf {a : α | a ∉ F} (fun a : {a // a ∉ F} ↦ e.symm cfg a) ∈ E0 at houtside
        have hOutsideEq :
            supportedSetOf {a : α | a ∉ F} (fun a : {a // a ∉ F} ↦ e.symm cfg a) = cfg \ F := by
          calc
            supportedSetOf {a : α | a ∉ F} (fun a : {a // a ∉ F} ↦ e.symm cfg a)
              = {a : α | e.symm cfg a} \ F := supportedSetOf_restrict_compl_eq_diff F (e.symm cfg)
            _ = cfg \ F := by rfl
        rwa [hOutsideEq] at houtside
      · change supportedSetOf F (fun a : {a // a ∈ F} ↦ e.symm cfg a) = A at hinside
        simpa [insideEvent, insideRestr, e, supportedSetOf_restrict_eq_inter] using hinside
    · rintro ⟨houtside, hinside⟩
      refine ⟨?_, ?_⟩
      · change supportedSetOf F (fun a : {a // a ∈ F} ↦ e.symm cfg a) = A
        simpa [insideEvent, insideRestr, e, supportedSetOf_restrict_eq_inter] using hinside
      · change supportedSetOf {a : α | a ∉ F} (fun a : {a // a ∉ F} ↦ e.symm cfg a) ∈ E0
        have hOutsideEq :
            supportedSetOf {a : α | a ∉ F} (fun a : {a // a ∉ F} ↦ e.symm cfg a) = cfg \ F := by
          calc
            supportedSetOf {a : α | a ∉ F} (fun a : {a // a ∉ F} ↦ e.symm cfg a)
              = {a : α | e.symm cfg a} \ F := supportedSetOf_restrict_compl_eq_diff F (e.symm cfg)
            _ = cfg \ F := by rfl
        rwa [hOutsideEq]
  have hinside_pull :
      e.symm ⁻¹' (insideRestr ⁻¹' insideEvent) = {cfg | cfg ∩ F = A} := by
    ext cfg
    change supportedSetOf F (fun a : {a // a ∈ F} ↦ e.symm cfg a) = A ↔ cfg ∩ F = A
    simpa [insideEvent, insideRestr, e, supportedSetOf_restrict_eq_inter]
  have houtside_pull :
      e.symm ⁻¹' (outsideRestr ⁻¹' outsideEvent) =
        ((fun cfg : Set α ↦ cfg \ F) ⁻¹' E0) := by
    ext cfg
    change supportedSetOf {a : α | a ∉ F} (fun a : {a // a ∉ F} ↦ e.symm cfg a) ∈ E0 ↔ cfg \ F ∈ E0
    have hOutsideEq :
        supportedSetOf {a : α | a ∉ F} (fun a : {a // a ∉ F} ↦ e.symm cfg a) = cfg \ F := by
      calc
        supportedSetOf {a : α | a ∉ F} (fun a : {a // a ∉ F} ↦ e.symm cfg a)
          = {a : α | e.symm cfg a} \ F := supportedSetOf_restrict_compl_eq_diff F (e.symm cfg)
        _ = cfg \ F := by rfl
    rw [hOutsideEq]
  have hind :
      IndepFun insideRestr outsideRestr (Measure.infinitePi ν) :=
    indepFun_memBlock_memBlockCompl (u := (latticeGraph d).edgeSet) F p
  -- Proof comment: move to the predicate-valued product space, use block independence there, and
  -- then transport the two factors back to configuration space.
  calc
    ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p
        (((fun cfg : Set α ↦ cfg \ F) ⁻¹' E0) ∩ {cfg | cfg ∩ F = A})
      =
        ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p
          (e.symm ⁻¹' (insideRestr ⁻¹' insideEvent ∩ outsideRestr ⁻¹' outsideEvent)) := by
            rw [hleft_preimage]
    _ =
        Measure.map e.symm (ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p)
          (insideRestr ⁻¹' insideEvent ∩ outsideRestr ⁻¹' outsideEvent) := by
            rw [Measure.map_apply_of_aemeasurable e.symm.measurable.aemeasurable
              (hinsidePreMeas.inter houtsidePreMeas)]
    _ =
        Measure.infinitePi ν (insideRestr ⁻¹' insideEvent ∩ outsideRestr ⁻¹' outsideEvent) := by
            rw [hfieldLaw]
    _ =
        Measure.infinitePi ν (insideRestr ⁻¹' insideEvent) *
          Measure.infinitePi ν (outsideRestr ⁻¹' outsideEvent) := by
            exact hind.measure_inter_preimage_eq_mul insideEvent outsideEvent hinsideMeas houtsideMeas
    _ =
        Measure.map e.symm (ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p)
          (insideRestr ⁻¹' insideEvent) *
          Measure.map e.symm (ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p)
            (outsideRestr ⁻¹' outsideEvent) := by
              rw [hfieldLaw]
    _ =
        ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p
            (e.symm ⁻¹' (insideRestr ⁻¹' insideEvent)) *
          ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p
            (e.symm ⁻¹' (outsideRestr ⁻¹' outsideEvent)) := by
              rw [Measure.map_apply_of_aemeasurable e.symm.measurable.aemeasurable hinsidePreMeas,
                Measure.map_apply_of_aemeasurable e.symm.measurable.aemeasurable houtsidePreMeas]
    _ =
        ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p {cfg | cfg ∩ F = A} *
          ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p
            (((fun cfg : Set α ↦ cfg \ F) ⁻¹' E0)) := by
              rw [hinside_pull, houtside_pull]
    _ =
        ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p
            (((fun cfg : Set α ↦ cfg \ F) ⁻¹' E0)) *
          ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p {cfg | cfg ∩ F = A} := by
              rw [mul_comm]
