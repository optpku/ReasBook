/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_theorem_3_40
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_1.ch4_sec4_3_1_definition_4_3_1_extra_1

open scoped BigOperators

universe u w

section Lemma_4_10

variable {V : Type u} {A : Type w} [Fintype A]

/-- Helper for Lemma 4.10: the pointed-cone hull of the zero singleton is exactly `{0}` in the
function space `A → ℝ`. -/
private theorem mem_singleton_pointedCone_hull_iff {r x : A → ℝ} :
    x ∈ (PointedCone.hull ℝ ({r} : Set (A → ℝ)) : Set (A → ℝ)) ↔
      ∃ μ : ℝ, 0 ≤ μ ∧ x = μ • r := by
  constructor
  · intro hx
    -- Collapse the finite conic-combination presentation because every source vector equals `r`.
    rcases (mem_hull_iff).1 hx with ⟨q, s, hs, coeff, hcoeff_nonneg, hx_eq⟩
    refine ⟨∑ j, coeff j, Finset.sum_nonneg fun j _ ↦ hcoeff_nonneg j, ?_⟩
    calc
      x = ∑ j, coeff j • s j := hx_eq
      _ = ∑ j, coeff j • r := by
        refine Finset.sum_congr rfl ?_
        intro j _
        simpa using congrArg (fun y : A → ℝ ↦ coeff j • y) (Set.mem_singleton_iff.mp (hs j))
      _ = (∑ j, coeff j) • r := by
        simpa using (Finset.sum_smul (s := Finset.univ) (f := coeff) (x := r)).symm
  · rintro ⟨μ, hμ, rfl⟩
    -- A singleton ray is already a one-term conic combination in the hull presentation.
    refine (mem_hull_iff).2 ?_
    refine ⟨1, fun _ ↦ r, fun _ ↦ by simp, fun _ ↦ μ, fun _ ↦ hμ, ?_⟩
    simpa using (show (μ • r) = ∑ j : Fin 1, μ • r by simp)

/-- Helper for Lemma 4.10: the pointed-cone hull of the zero singleton is exactly `{0}` in the
function space `A → ℝ`. -/
private theorem singleton_pointedCone_hull_zero :
    (PointedCone.hull ℝ ({(0 : A → ℝ)} : Set (A → ℝ)) : Set (A → ℝ)) =
      ({0} : Set (A → ℝ)) := by
  ext x
  constructor
  · intro hx
    rcases (mem_singleton_pointedCone_hull_iff).1 hx with ⟨μ, _, rfl⟩
    simp
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    -- The zero scalar witnesses `0 ∈ hull {0}`.
    exact (mem_singleton_pointedCone_hull_iff).2 ⟨0, le_rfl, by simp⟩

/-- Helper for Lemma 4.10: an extreme-ray generator belongs to the ambient circulation cone. -/
private theorem extreme_ray_mem_of_isExtremeRayOfCone {C : Set (A → ℝ)} {x : A → ℝ}
    (hx : IsExtremeRayOfCone C x) :
    x ∈ C := by
  -- Unfold the extreme-ray alias and evaluate the extreme-subset condition at the generator.
  have hx_edge : IsEdgeOf C (PointedCone.hull ℝ ({x} : Set (A → ℝ)) : Set (A → ℝ)) :=
    (isExtremeRayOfCone_iff).1 hx
  exact hx_edge.isExtreme.1 (PointedCone.subset_hull (by simp))

/-- Helper for Lemma 4.10: an extreme-ray generator in `A → ℝ` is necessarily nonzero. -/
private theorem extreme_ray_ne_zero {C : Set (A → ℝ)} {x : A → ℝ}
    (hx : IsExtremeRayOfCone C x) :
    x ≠ 0 := by
  -- Rewriting the generator as `0` would force the supporting edge to have direction rank `0`.
  have hx_edge : IsEdgeOf C (PointedCone.hull ℝ ({x} : Set (A → ℝ)) : Set (A → ℝ)) :=
    (isExtremeRayOfCone_iff).1 hx
  intro hx_zero
  have hzero_edge : IsEdgeOf C ({0} : Set (A → ℝ)) := by
    simpa [hx_zero, singleton_pointedCone_hull_zero] using hx_edge
  have hdim_zero : Module.finrank ℝ (affineSpan ℝ ({0} : Set (A → ℝ))).direction = 0 := by
    rw [direction_affineSpan, vectorSpan_singleton]
    simp
  have hdim_one : Module.finrank ℝ (affineSpan ℝ ({0} : Set (A → ℝ))).direction = 1 :=
    hzero_edge.finrank_direction_eq_one
  have : (0 : ℕ) = 1 := by
    rwa [hdim_zero] at hdim_one
  exact Nat.zero_ne_one this

/-- Helper for Lemma 4.10: if a circulation vanishes off `C`, then its outgoing flow at `v`
reduces to the sum over the arcs of `C` leaving `v`. -/
private theorem outgoing_flow_eq_sum_filter_of_eq_zero_off_support
    [DecidableEq V] {tail : A → V} {C : Finset A} {x : A → ℝ}
    (hsupp : ∀ a, a ∉ C → x a = 0) (v : V) :
    outgoing_flow tail x v = Finset.sum (C.filter fun a ↦ tail a = v) x := by
  classical
  -- Restrict the outgoing sum from all arcs to the support set `C`, where all other terms vanish.
  unfold outgoing_flow
  symm
  refine Finset.sum_subset ?_ ?_
  · intro a ha
    have hav : tail a = v := (Finset.mem_filter.mp ha).2
    have haC : a ∈ C := (Finset.mem_filter.mp ha).1
    simpa [haC, hav]
  · intro a ha_out ha_not_mem
    have ha_not_C : a ∉ C := by
      intro haC
      exact ha_not_mem (by simpa [haC] using ha_out)
    exact hsupp a ha_not_C

/-- Helper for Lemma 4.10: if a circulation vanishes off `C`, then its incoming flow at `v`
reduces to the sum over the arcs of `C` entering `v`. -/
private theorem incoming_flow_eq_sum_filter_of_eq_zero_off_support
    [DecidableEq V] {head : A → V} {C : Finset A} {x : A → ℝ}
    (hsupp : ∀ a, a ∉ C → x a = 0) (v : V) :
    incoming_flow head x v = Finset.sum (C.filter fun a ↦ head a = v) x := by
  classical
  -- The same support restriction works for incoming arcs.
  unfold incoming_flow
  symm
  refine Finset.sum_subset ?_ ?_
  · intro a ha
    have hav : head a = v := (Finset.mem_filter.mp ha).2
    have haC : a ∈ C := (Finset.mem_filter.mp ha).1
    simpa [haC, hav]
  · intro a ha_in ha_not_mem
    have ha_not_C : a ∉ C := by
      intro haC
      exact ha_not_mem (by simpa [haC] using ha_in)
    exact hsupp a ha_not_C

/-- Helper for Lemma 4.10: at each incident vertex of a simple circuit there is a unique outgoing
arc in the circuit. -/
private theorem existsUnique_outgoing_arc_of_isSimpleCircuit
    {tail head : A → V} {C : Finset A}
    (hC : IsSimpleCircuit tail head C) (v : V) (hv : v ∈ circuit_vertex_set tail head C) :
    ∃! a : A, a ∈ C ∧ tail a = v := by
  classical
  -- Convert the cardinality-one outgoing fiber into an explicit unique arc.
  have hout : outgoing_arc_count tail C v = 1 := (hC.one_in_one_out v hv).2
  rw [outgoing_arc_count] at hout
  rcases Finset.card_eq_one.mp hout with ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · have ha_mem : a ∈ C.filter (fun b ↦ tail b = v) := by
      rw [ha]
      simp
    simpa using ha_mem
  · intro b hb
    have hb' : b ∈ C.filter (fun a ↦ tail a = v) := by
      simpa using hb
    rw [ha] at hb'
    simpa using hb'

/-- Helper for Lemma 4.10: at each incident vertex of a simple circuit there is a unique incoming
arc in the circuit. -/
private theorem existsUnique_incoming_arc_of_isSimpleCircuit
    {tail head : A → V} {C : Finset A}
    (hC : IsSimpleCircuit tail head C) (v : V) (hv : v ∈ circuit_vertex_set tail head C) :
    ∃! a : A, a ∈ C ∧ head a = v := by
  classical
  -- The incoming fiber is handled identically.
  have hin : incoming_arc_count head C v = 1 := (hC.one_in_one_out v hv).1
  rw [incoming_arc_count] at hin
  rcases Finset.card_eq_one.mp hin with ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · have ha_mem : a ∈ C.filter (fun b ↦ head b = v) := by
      rw [ha]
      simp
    simpa using ha_mem
  · intro b hb
    have hb' : b ∈ C.filter (fun a ↦ head a = v) := by
      simpa using hb
    rw [ha] at hb'
    simpa using hb'

/-- Helper for Lemma 4.10: the characteristic vector of a simple circuit is nonzero. -/
private theorem circuit_characteristic_vector_ne_zero
    {tail head : A → V} {C : Finset A} (hC : IsSimpleCircuit tail head C) :
    circuit_characteristic_vector C ≠ 0 := by
  classical
  -- Evaluate the characteristic vector on any arc of the nonempty circuit.
  rcases hC.nonempty with ⟨a, ha⟩
  intro hzero
  have ha_eval := congrArg (fun f : A → ℝ ↦ f a) hzero
  simpa [circuit_characteristic_vector_apply, ha] using ha_eval

/-- Helper for Lemma 4.10: the characteristic vector of a simple circuit is a circulation. -/
private theorem circuit_characteristic_vector_mem_circulation_cone
    {tail head : A → V} {C : Finset A} (hC : IsSimpleCircuit tail head C) :
    circuit_characteristic_vector C ∈ circulation_cone tail head := by
  classical
  -- Prove circulation directly from support restriction and the circuit degree equalities.
  rw [mem_circulation_cone_iff, isCirculation_iff]
  refine ⟨?_, ?_⟩
  · intro v
    -- On the circuit support, both flows count the incident circuit arcs; off support, both vanish.
    let _ : DecidableEq V := Classical.decEq V
    have hsupp : ∀ a, a ∉ C → circuit_characteristic_vector C a = 0 := by
      intro a ha
      simp [circuit_characteristic_vector_apply, ha]
    rw [incoming_flow_eq_sum_filter_of_eq_zero_off_support hsupp,
      outgoing_flow_eq_sum_filter_of_eq_zero_off_support hsupp]
    have hsubset_in : C.filter (fun a ↦ head a = v) ⊆ C := by
      intro a ha
      exact (Finset.mem_filter.mp ha).1
    have hsubset_out : C.filter (fun a ↦ tail a = v) ⊆ C := by
      intro a ha
      exact (Finset.mem_filter.mp ha).1
    have hsum_in :
        Finset.sum (C.filter (fun a ↦ head a = v)) (circuit_characteristic_vector C) =
          ((C.filter (fun a ↦ head a = v)).card : ℝ) := by
      simpa [Finset.inter_eq_left.mpr hsubset_in, circuit_characteristic_vector_apply]
    have hsum_out :
        Finset.sum (C.filter (fun a ↦ tail a = v)) (circuit_characteristic_vector C) =
          ((C.filter (fun a ↦ tail a = v)).card : ℝ) := by
      simpa [Finset.inter_eq_left.mpr hsubset_out, circuit_characteristic_vector_apply]
    rw [hsum_in, hsum_out]
    exact_mod_cast hC.balanced v
  · intro a
    by_cases ha : a ∈ C
    · simp [circuit_characteristic_vector_apply, ha]
    · simp [circuit_characteristic_vector_apply, ha]

/-- Helper for Lemma 4.10: nonnegative scalar multiples of circulations remain in the circulation
cone. -/
private theorem smul_mem_circulation_cone
    {tail head : A → V} {x : A → ℝ} {μ : ℝ}
    (hx : x ∈ circulation_cone tail head) (hμ : 0 ≤ μ) :
    μ • x ∈ circulation_cone tail head := by
  -- Scale both flow equalities and coordinatewise inequalities by the same nonnegative scalar.
  rw [mem_circulation_cone_iff, isCirculation_iff] at hx ⊢
  rcases hx with ⟨hflow, hnonneg⟩
  refine ⟨?_, ?_⟩
  · intro v
    calc
      incoming_flow head (μ • x) v = μ * incoming_flow head x v := by
        simp [incoming_flow, Pi.smul_apply, Finset.mul_sum]
      _ = μ * outgoing_flow tail x v := by
        rw [hflow v]
      _ = outgoing_flow tail (μ • x) v := by
        simp [outgoing_flow, Pi.smul_apply, Finset.mul_sum]
  · intro a
    simpa [Pi.smul_apply] using mul_nonneg hμ (hnonneg a)

/-- Helper for Lemma 4.10: a circulation supported on a simple circuit is a nonnegative scalar
multiple of that circuit characteristic vector. -/
private theorem supported_circulation_is_scalar_multiple_of_circuit_characteristic_vector
    {tail head : A → V} {C : Finset A} (hC : IsSimpleCircuit tail head C) {x : A → ℝ}
    (hx : x ∈ circulation_cone tail head) (hsupp : ∀ a, a ∉ C → x a = 0) :
    ∃ μ : ℝ, 0 ≤ μ ∧ x = μ • circuit_characteristic_vector C := by
  classical
  -- Unpack the circulation constraints once so every later step can use conservation directly.
  rw [mem_circulation_cone_iff, isCirculation_iff] at hx
  rcases hx with ⟨hflow, hnonneg⟩
  let outArc : circuit_vertex_set tail head C → A :=
    fun v ↦ Classical.choose (existsUnique_outgoing_arc_of_isSimpleCircuit hC v.1 v.2)
  let inArc : circuit_vertex_set tail head C → A :=
    fun v ↦ Classical.choose (existsUnique_incoming_arc_of_isSimpleCircuit hC v.1 v.2)
  let φ : circuit_vertex_set tail head C → ℝ := fun v ↦ x (outArc v)
  have houtArc_spec :
      ∀ v : circuit_vertex_set tail head C, outArc v ∈ C ∧ tail (outArc v) = v.1 := by
    intro v
    exact (Classical.choose_spec (existsUnique_outgoing_arc_of_isSimpleCircuit hC v.1 v.2)).1
  have houtArc_unique :
      ∀ v : circuit_vertex_set tail head C, ∀ a : A, a ∈ C ∧ tail a = v.1 → a = outArc v := by
    intro v a ha
    exact (Classical.choose_spec (existsUnique_outgoing_arc_of_isSimpleCircuit hC v.1 v.2)).2 a ha
  have hinArc_spec :
      ∀ v : circuit_vertex_set tail head C, inArc v ∈ C ∧ head (inArc v) = v.1 := by
    intro v
    exact (Classical.choose_spec (existsUnique_incoming_arc_of_isSimpleCircuit hC v.1 v.2)).1
  have hinArc_unique :
      ∀ v : circuit_vertex_set tail head C, ∀ a : A, a ∈ C ∧ head a = v.1 → a = inArc v := by
    intro v a ha
    exact (Classical.choose_spec (existsUnique_incoming_arc_of_isSimpleCircuit hC v.1 v.2)).2 a ha
  have h_outgoing_value :
      ∀ v : circuit_vertex_set tail head C, outgoing_flow tail x v.1 = x (outArc v) := by
    intro v
    -- The support restriction collapses the outgoing sum to the unique outgoing arc at `v`.
    have hfilter :
        C.filter (fun a ↦ tail a = v.1) = {outArc v} := by
      ext a
      constructor
      · intro ha
        have ha' : a ∈ C ∧ tail a = v.1 := by
          simpa using ha
        have hEq : a = outArc v := houtArc_unique v a ha'
        simp [hEq, (houtArc_spec v).1]
      · intro ha
        have hEq : a = outArc v := by
          simpa using ha
        subst hEq
        simpa [(houtArc_spec v).1, (houtArc_spec v).2]
    calc
      outgoing_flow tail x v.1 = Finset.sum (C.filter (fun a ↦ tail a = v.1)) x := by
        rw [outgoing_flow_eq_sum_filter_of_eq_zero_off_support hsupp]
      _ = x (outArc v) := by
        rw [hfilter]
        simp
  have h_incoming_value :
      ∀ v : circuit_vertex_set tail head C, incoming_flow head x v.1 = x (inArc v) := by
    intro v
    -- The incoming sum collapses to the unique incoming arc at `v`.
    have hfilter :
        C.filter (fun a ↦ head a = v.1) = {inArc v} := by
      ext a
      constructor
      · intro ha
        have ha' : a ∈ C ∧ head a = v.1 := by
          simpa using ha
        have hEq : a = inArc v := hinArc_unique v a ha'
        simp [hEq, (hinArc_spec v).1]
      · intro ha
        have hEq : a = inArc v := by
          simpa using ha
        subst hEq
        simpa [(hinArc_spec v).1, (hinArc_spec v).2]
    calc
      incoming_flow head x v.1 = Finset.sum (C.filter (fun a ↦ head a = v.1)) x := by
        rw [incoming_flow_eq_sum_filter_of_eq_zero_off_support hsupp]
      _ = x (inArc v) := by
        rw [hfilter]
        simp
  have hstep :
      ∀ {u v : circuit_vertex_set tail head C} {a : A},
        a ∈ C → tail a = u.1 → head a = v.1 → φ u = φ v := by
    intro u v a haC htail hhead
    -- Conservation at the head vertex identifies the common circuit value across one arc.
    have houtEq : outArc u = a := by
      symm
      exact houtArc_unique u a ⟨haC, htail⟩
    have hinEq : inArc v = a := by
      symm
      exact hinArc_unique v a ⟨haC, hhead⟩
    calc
      φ u = x a := by
        dsimp [φ]
        rw [houtEq]
      _ = x (inArc v) := by
        rw [hinEq]
      _ = incoming_flow head x v.1 := (h_incoming_value v).symm
      _ = outgoing_flow tail x v.1 := hflow v.1
      _ = x (outArc v) := h_outgoing_value v
      _ = φ v := rfl
  have hφ_adj :
      ∀ {u v : circuit_vertex_set tail head C},
        ((arc_induced_digraph tail head C).toSimpleGraphInclusive.induce
          (circuit_vertex_set tail head C)).Adj u v → φ u = φ v := by
    intro u v huv
    rw [SimpleGraph.induce_adj, Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at huv
    rcases huv with ⟨_, huv | huv⟩
    · rcases (arc_induced_digraph_adj_iff tail head C u.1 v.1).1 huv with ⟨a, haC, htail, hhead⟩
      exact hstep haC htail hhead
    · rcases (arc_induced_digraph_adj_iff tail head C v.1 u.1).1 huv with ⟨a, haC, htail, hhead⟩
      exact (hstep haC htail hhead).symm
  have hφ_reachable :
      ∀ {u v : circuit_vertex_set tail head C},
        ((arc_induced_digraph tail head C).toSimpleGraphInclusive.induce
          (circuit_vertex_set tail head C)).Reachable u v → φ u = φ v := by
    intro u v huv
    rcases huv with ⟨p⟩
    -- Walk induction propagates equality through the connected circuit support.
    induction p with
    | nil =>
        rfl
    | @cons a b c hab p ih =>
        exact (hφ_adj hab).trans ih
  rcases hC.nonempty with ⟨a₀, ha₀⟩
  let v₀ : circuit_vertex_set tail head C := ⟨tail a₀, ⟨a₀, ha₀, Or.inl rfl⟩⟩
  have hbase_out : outArc v₀ = a₀ := by
    symm
    exact houtArc_unique v₀ a₀ ⟨ha₀, rfl⟩
  refine ⟨x a₀, hnonneg a₀, ?_⟩
  ext a
  by_cases ha : a ∈ C
  · -- Connectivity forces every supported arc to share the base value `x a₀`.
    let v : circuit_vertex_set tail head C := ⟨tail a, ⟨a, ha, Or.inl rfl⟩⟩
    have hreach :
        ((arc_induced_digraph tail head C).toSimpleGraphInclusive.induce
          (circuit_vertex_set tail head C)).Reachable v₀ v := hC.connected v₀ v
    have houtEq : outArc v = a := by
      symm
      exact houtArc_unique v a ⟨ha, rfl⟩
    have hconst : x a = x a₀ := by
      calc
        x a = φ v := by
          dsimp [φ]
          rw [houtEq]
        _ = φ v₀ := by
          symm
          exact hφ_reachable hreach
        _ = x a₀ := by
          dsimp [φ]
          rw [hbase_out]
    simpa [Pi.smul_apply, circuit_characteristic_vector_apply, ha] using hconst
  · -- Off the circuit support, both the circulation and the characteristic vector vanish.
    simpa [Pi.smul_apply, circuit_characteristic_vector_apply, ha, hsupp a ha]

noncomputable local instance : DecidableEq A := Classical.decEq A
noncomputable local instance : DecidableEq V := Classical.decEq V

/-- Helper for Lemma 4.10: a list of arcs is a directed walk from `u` to `v` when consecutive arc
endpoints match, starting at `u` and ending at `v`. -/
private def IsDirectedWalkFromTo (tail head : A → V) : V → V → List A → Prop
  | u, v, [] => u = v
  | u, v, a :: p => tail a = u ∧ IsDirectedWalkFromTo tail head (head a) v p

/-- Helper for Lemma 4.10: the ordered vertex list visited by a directed walk. -/
private def walkVerticesFrom (head : A → V) (u : V) : List A → List V
  | [] => [u]
  | a :: p => u :: walkVerticesFrom head (head a) p

/-- Helper for Lemma 4.10: the visited vertices of a walk are the start vertex followed by the
heads of the traversed arcs. -/
private theorem walkVerticesFrom_eq_start_cons_map_head
    {head : A → V} (u : V) (p : List A) :
    walkVerticesFrom head u p = u :: p.map head := by
  induction p generalizing u with
  | nil =>
      simp [walkVerticesFrom]
  | cons a p ih =>
      simp [walkVerticesFrom, ih]

/-- Helper for Lemma 4.10: the tail of the visited-vertex list is exactly the head list of the
walk arcs. -/
private theorem walkVerticesFrom_tail_eq_map_head
    {head : A → V} (u : V) (p : List A) :
    (walkVerticesFrom head u p).tail = p.map head := by
  simp [walkVerticesFrom_eq_start_cons_map_head]

/-- Helper for Lemma 4.10: every arc of a walk contributes its tail vertex to the visited-vertex
list. -/
private theorem tail_mem_walkVerticesFrom_of_mem
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      ∀ {a : A}, a ∈ p → tail a ∈ walkVerticesFrom head u p
  | _, _, [], hwalk, _, hmem => by
      cases hmem
  | u, v, b :: p, hwalk, a, hmem => by
      rcases hwalk with ⟨hbu, hp⟩
      -- Split according to whether `a` is the first arc or lies in the tail walk.
      rw [walkVerticesFrom]
      rcases List.mem_cons.mp hmem with rfl | hmemTail
      · simp [hbu]
      · exact List.mem_cons_of_mem _ (tail_mem_walkVerticesFrom_of_mem hp hmemTail)

/-- Helper for Lemma 4.10: every arc of a walk contributes its head vertex to the tail of the
visited-vertex list. -/
private theorem head_mem_walkVerticesTail_of_mem
    {head : A → V} (u : V) {p : List A} {a : A} (ha : a ∈ p) :
    head a ∈ (walkVerticesFrom head u p).tail := by
  rw [walkVerticesFrom_tail_eq_map_head]
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

/-- Helper for Lemma 4.10: concatenating directed walks with a matching intermediate endpoint
produces the evident longer walk. -/
private theorem directedWalk_append
    {tail head : A → V} :
    ∀ {u w v : V} {p q : List A},
      IsDirectedWalkFromTo tail head u w p →
        IsDirectedWalkFromTo tail head w v q →
          IsDirectedWalkFromTo tail head u v (p ++ q)
  | _, _, _, [], q, hp, hq => by
      -- The empty prefix contributes no arcs.
      subst hp
      simpa using hq
  | u, w, v, a :: p, q, hp, hq => by
      rcases hp with ⟨hau, hpTail⟩
      -- Keep the first arc and append recursively to the tail walk.
      exact ⟨hau, directedWalk_append hpTail hq⟩

/-- Helper for Lemma 4.10: splitting a walk at a visited vertex yields compatible prefix and
suffix walks. -/
private theorem directedWalk_split_at_visited_vertex
    {tail head : A → V} :
    ∀ {u v w : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      w ∈ walkVerticesFrom head u p →
        ∃ p₁ p₂, p = p₁ ++ p₂ ∧
          IsDirectedWalkFromTo tail head u w p₁ ∧
            IsDirectedWalkFromTo tail head w v p₂
  | u, v, w, [], hp, hw => by
      subst hp
      have hwu : w = u := by
        simpa [walkVerticesFrom] using hw
      subst hwu
      -- The empty walk visits only its start/end vertex.
      refine ⟨[], [], rfl, rfl, rfl⟩
  | u, v, w, a :: p, hp, hw => by
      rcases hp with ⟨hau, hpTail⟩
      rw [walkVerticesFrom] at hw
      rcases List.mem_cons.mp hw with rfl | hwTail
      · -- Splitting at the initial vertex leaves the whole walk in the suffix.
        refine ⟨[], a :: p, by simp, rfl, ?_⟩
        exact ⟨hau, hpTail⟩
      · rcases directedWalk_split_at_visited_vertex hpTail hwTail with
          ⟨p₁, p₂, hpSplit, hp₁, hp₂⟩
        -- Otherwise split the tail walk recursively and restore the first arc.
        refine ⟨a :: p₁, p₂, ?_, ?_, hp₂⟩
        · simp [hpSplit]
        · exact ⟨hau, by simpa [hpSplit] using hp₁⟩

/-- Helper for Lemma 4.10: visited vertices of appended walks concatenate as expected. -/
private theorem walkVerticesFrom_append
    {tail head : A → V} :
    ∀ {u w v : V} {p q : List A},
      IsDirectedWalkFromTo tail head u w p →
        IsDirectedWalkFromTo tail head w v q →
          walkVerticesFrom head u (p ++ q) =
            walkVerticesFrom head u p ++ (walkVerticesFrom head w q).tail
  | _, _, _, [], q, hp, hq => by
      subst hp
      cases q with
      | nil =>
          simp [walkVerticesFrom]
      | cons a q =>
          simp [walkVerticesFrom]
  | u, w, v, a :: p, q, hp, hq => by
      rcases hp with ⟨hau, hpTail⟩
      -- Peel off the leading arc and apply the append formula recursively to the tail walk.
      simp [walkVerticesFrom, walkVerticesFrom_append hpTail hq]

/-- Helper for Lemma 4.10: the endpoint of a directed walk appears in its visited-vertex list. -/
private theorem terminalVertex_mem_walkVerticesFrom
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      v ∈ walkVerticesFrom head u p
  | _, _, [], hp => by
      subst hp
      simp [walkVerticesFrom]
  | u, v, a :: p, hp => by
      rcases hp with ⟨hau, hpTail⟩
      -- The endpoint of the tail walk is still the endpoint of the whole walk.
      simp [walkVerticesFrom, terminalVertex_mem_walkVerticesFrom hpTail]

/-- Helper for Lemma 4.10: if the visited vertices of a walk are nodup, then so are the walk
arcs. -/
private theorem directedWalk_nodup_of_verticesNodup
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      (walkVerticesFrom head u p).Nodup → p.Nodup
  | _, _, [], _, _ => by
      simp
  | u, v, a :: p, hp, hverts => by
      rcases hp with ⟨hau, hpTail⟩
      rw [walkVerticesFrom] at hverts
      rcases List.nodup_cons.mp hverts with ⟨hu_not_mem, htailVerts⟩
      have hpNodup := directedWalk_nodup_of_verticesNodup hpTail htailVerts
      have ha_not_mem : a ∉ p := by
        intro hmem
        -- Reusing `a` would revisit the tail vertex `u` later in the walk.
        have htailMem : tail a ∈ walkVerticesFrom head (head a) p :=
          tail_mem_walkVerticesFrom_of_mem hpTail hmem
        have huMem : u ∈ walkVerticesFrom head (head a) p := by
          simpa [hau] using htailMem
        exact hu_not_mem huMem
      exact List.nodup_cons.mpr ⟨ha_not_mem, hpNodup⟩

/-- Helper for Lemma 4.10: the final arc of a nonempty directed walk is a positive incoming arc
at the endpoint whenever every traversed arc is positive. -/
private theorem exists_positive_incoming_arc_at_walkEndpoint
    {tail head : A → V} {y : A → ℝ} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      p ≠ [] →
        (∀ b ∈ p.toFinset, 0 < y b) →
          ∃ a, a ∈ p.toFinset ∧ head a = v ∧ 0 < y a
  | _, _, [], _, hne, _ => by
      exact False.elim (hne rfl)
  | u, v, a :: p, hp, _, hpos => by
      rcases hp with ⟨hau, hpTail⟩
      by_cases hpnil : p = []
      · subst hpnil
        refine ⟨a, by simp, ?_, hpos a (by simp)⟩
        simpa using hpTail
      · have hposTail : ∀ b ∈ p.toFinset, 0 < y b := by
          intro b hb
          exact hpos b (by simpa using List.mem_cons_of_mem a (List.mem_toFinset.mp hb))
        rcases exists_positive_incoming_arc_at_walkEndpoint
            (tail := tail) (head := head) (y := y) (u := head a) (v := v) (p := p)
            hpTail hpnil hposTail with ⟨b, hb, hbhead, hbpos⟩
        refine ⟨b, ?_, hbhead, hbpos⟩
        exact List.mem_toFinset.mpr (List.mem_cons_of_mem a (List.mem_toFinset.mp hb))

/-- Helper for Lemma 4.10: if a positive walk revisits an earlier vertex after one more positive
arc, the repeated-vertex suffix is already a positive closed walk with nodup internal vertices. -/
private theorem positiveWalkRepeatedVertex_yieldsCircuitSuffix
    {tail head : A → V} {y : A → ℝ}
    {s u : V} {p : List A} {a : A}
    (hp : IsDirectedWalkFromTo tail head s u p)
    (hnodup : (walkVerticesFrom head s p).Nodup)
    (hposp : ∀ b ∈ p.toFinset, 0 < y b)
    (htail : tail a = u)
    (hposa : 0 < y a)
    (hhead : head a ∈ walkVerticesFrom head s p) :
    ∃ c : List A, c ≠ [] ∧ IsDirectedWalkFromTo tail head (head a) (head a) c ∧
      (walkVerticesFrom head (head a) c).tail.Nodup ∧ ∀ b ∈ c.toFinset, 0 < y b := by
  classical
  rcases directedWalk_split_at_visited_vertex hp hhead with
    ⟨p₁, p₂, rfl, hp₁, hp₂⟩
  let w := head a
  let c : List A := p₂ ++ [a]
  have hsingle : IsDirectedWalkFromTo tail head u w [a] := by
    -- The closing arc is a one-step walk back to the repeated vertex.
    exact ⟨htail, rfl⟩
  have hwalkc : IsDirectedWalkFromTo tail head w w c := by
    -- Appending the closing arc turns the suffix into a closed walk.
    simpa [c, w] using directedWalk_append hp₂ hsingle
  have hsplitVertices :
      walkVerticesFrom head s (p₁ ++ p₂) =
        walkVerticesFrom head s p₁ ++ (walkVerticesFrom head w p₂).tail := by
    simpa [w] using walkVerticesFrom_append hp₁ hp₂
  have htailNodup : (walkVerticesFrom head w p₂).tail.Nodup := by
    -- The suffix tail inherits nodup from the original walk after splitting at the repeated
    -- vertex.
    have happendNodup :
        (walkVerticesFrom head s p₁ ++ (walkVerticesFrom head w p₂).tail).Nodup := by
      simpa [hsplitVertices] using hnodup
    exact List.Nodup.of_append_right happendNodup
  have hw_mem_prefix : w ∈ walkVerticesFrom head s p₁ :=
    terminalVertex_mem_walkVerticesFrom hp₁
  have hw_not_mem_suffixTail : w ∉ (walkVerticesFrom head w p₂).tail := by
    have happendNodup :
        (walkVerticesFrom head s p₁ ++ (walkVerticesFrom head w p₂).tail).Nodup := by
      simpa [hsplitVertices] using hnodup
    have hdisj :
        List.Disjoint (walkVerticesFrom head s p₁) ((walkVerticesFrom head w p₂).tail) :=
      List.disjoint_of_nodup_append happendNodup
    exact fun hwTail ↦ (List.disjoint_left.1 hdisj hw_mem_prefix hwTail)
  have hcTailNodup : (walkVerticesFrom head w c).tail.Nodup := by
    have hvertices_c :
        walkVerticesFrom head w c = walkVerticesFrom head w p₂ ++ [w] := by
      -- The closing one-arc walk contributes the repeated basepoint as the final visited vertex.
      have happ := walkVerticesFrom_append hp₂ hsingle
      simpa [c, w, walkVerticesFrom, htail] using happ
    have htail_append :
        (walkVerticesFrom head w c).tail = (walkVerticesFrom head w p₂).tail ++ [w] := by
      cases p₂ with
      | nil =>
          simp [hvertices_c, walkVerticesFrom, c, w]
      | cons b p₂ =>
          simp [hvertices_c, walkVerticesFrom]
    have hdisjTail : List.Disjoint (walkVerticesFrom head w p₂).tail [w] := by
      refine List.disjoint_left.2 ?_
      intro x hx hxw
      simp at hxw
      subst hxw
      exact hw_not_mem_suffixTail hx
    have hnodupTailAppend :
        ((walkVerticesFrom head w p₂).tail ++ [w]).Nodup :=
      List.Nodup.append htailNodup (by simp) hdisjTail
    simpa [htail_append] using hnodupTailAppend
  refine ⟨c, by simp [c], hwalkc, hcTailNodup, ?_⟩
  intro b hb
  have hbList : b ∈ c := List.mem_toFinset.mp hb
  change b ∈ p₂ ++ [a] at hbList
  rcases List.mem_append.mp hbList with hb₂ | hbA
  · exact hposp b (by simpa using List.mem_append.mpr (Or.inr hb₂))
  · have hbEq : b = a := by simpa using hbA
    subst hbEq
    exact hposa

/-- Helper for Lemma 4.10: enlarging the supporting arc set only enlarges the induced undirected
support graph. -/
private theorem supportGraph_mono
    {tail head : A → V} {C D : Finset A} (hCD : C ⊆ D) :
    (arc_induced_digraph tail head C).toSimpleGraphInclusive ≤
      (arc_induced_digraph tail head D).toSimpleGraphInclusive := by
  intro u v huv
  rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at huv ⊢
  rcases huv with ⟨hne, huv | huv⟩
  · refine ⟨hne, Or.inl ?_⟩
    rcases (arc_induced_digraph_adj_iff tail head C u v).1 huv with ⟨a, haC, htail, hhead⟩
    exact (arc_induced_digraph_adj_iff tail head D u v).2 ⟨a, hCD haC, htail, hhead⟩
  · refine ⟨hne, Or.inr ?_⟩
    rcases (arc_induced_digraph_adj_iff tail head C v u).1 huv with ⟨a, haC, htail, hhead⟩
    exact (arc_induced_digraph_adj_iff tail head D v u).2 ⟨a, hCD haC, htail, hhead⟩

/-- Helper for Lemma 4.10: the terminal vertex of a directed walk is the last visited vertex. -/
private theorem getLast_walkVerticesFrom
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      let hne : walkVerticesFrom head u p ≠ [] := by
        cases p <;> simp [walkVerticesFrom]
      (walkVerticesFrom head u p).getLast hne = v
  | u, v, [], hwalk => by
      simpa [walkVerticesFrom] using hwalk
  | u, v, a :: p, hwalk => by
      rcases hwalk with ⟨_, hp⟩
      cases p with
      | nil =>
          simpa [walkVerticesFrom] using getLast_walkVerticesFrom hp
      | cons b p =>
          simpa [walkVerticesFrom] using getLast_walkVerticesFrom hp

/-- Helper for Lemma 4.10: the tail sequence of a directed walk is the visited-vertex list with
the terminal vertex removed. -/
private theorem directedWalk_map_tail_eq_dropLast_walkVertices
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      p.map tail = (walkVerticesFrom head u p).dropLast
  | _, _, [], _ => by
      simp [walkVerticesFrom]
  | u, v, a :: p, hwalk => by
      rcases hwalk with ⟨hau, hp⟩
      cases p with
      | nil =>
          simp [walkVerticesFrom, hau]
      | cons b p =>
          simp [walkVerticesFrom, hau, directedWalk_map_tail_eq_dropLast_walkVertices hp]

/-- Helper for Lemma 4.10: every closed directed walk yields an undirected support walk in the
induced support graph with the same visited-vertex set. -/
private theorem exists_supportWalk_of_directedWalk
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      ∃ q : ((arc_induced_digraph tail head p.toFinset).toSimpleGraphInclusive).Walk u v,
        ∀ x, x ∈ q.support ↔ x ∈ walkVerticesFrom head u p
  | u, v, [], hwalk => by
      have huv : u = v := by
        simpa [IsDirectedWalkFromTo] using hwalk
      subst v
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro x
      simp [walkVerticesFrom]
  | u, v, a :: p, hwalk => by
      rcases hwalk with ⟨hau, hp⟩
      rcases exists_supportWalk_of_directedWalk hp with ⟨q, hq⟩
      have hsubset : p.toFinset ⊆ (a :: p).toFinset := by
        intro b hb
        exact List.mem_toFinset.mpr (List.mem_cons_of_mem a (List.mem_toFinset.mp hb))
      let q' :
          ((arc_induced_digraph tail head (a :: p).toFinset).toSimpleGraphInclusive).Walk
            (head a) v :=
        q.mapLe (supportGraph_mono (tail := tail) (head := head) hsubset)
      have hq' : ∀ x, x ∈ q'.support ↔ x ∈ walkVerticesFrom head (head a) p := by
        intro x
        have hsupport : q'.support = q.support := by
          simpa [q'] using
            (SimpleGraph.Walk.support_mapLe_eq_support
              (p := q)
              (h := supportGraph_mono (tail := tail) (head := head) hsubset))
        rw [hsupport]
        exact hq x
      by_cases hloop : u = head a
      · subst hloop
        refine ⟨q', ?_⟩
        intro x
        have hstart_mem : head a ∈ walkVerticesFrom head (head a) p := by
          cases p with
          | nil =>
              simp [walkVerticesFrom]
          | cons b p =>
              simp [walkVerticesFrom]
        constructor
        · intro hx
          have hx' := (hq' x).1 hx
          exact List.mem_cons_of_mem _ hx'
        · intro hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact (hq' _).2 hstart_mem
          · exact (hq' _).2 hx'
      · have hadj :
          ((arc_induced_digraph tail head (a :: p).toFinset).toSimpleGraphInclusive).Adj u
            (head a) := by
          rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
          refine ⟨hloop, Or.inl ?_⟩
          exact (arc_induced_digraph_adj_iff tail head (a :: p).toFinset u (head a)).2
            ⟨a, by simp, hau, rfl⟩
        refine ⟨SimpleGraph.Walk.cons hadj q', ?_⟩
        intro x
        constructor
        · intro hx
          rw [SimpleGraph.Walk.support_cons] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · simp [walkVerticesFrom]
          · exact List.mem_cons_of_mem _ ((hq' x).1 hx)
        · intro hx
          rw [SimpleGraph.Walk.support_cons]
          rcases List.mem_cons.mp hx with rfl | hx
          · simp
          · exact List.mem_cons_of_mem _ ((hq' x).2 hx)

/-- Helper for Lemma 4.10: every visited vertex of a nonempty closed walk is incident to its
support arc set. -/
private theorem mem_circuit_vertex_set_of_mem_walkVertices_closedWalk
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c) {v : V}
    (hv : v ∈ walkVerticesFrom head w c) :
    v ∈ circuit_vertex_set tail head c.toFinset := by
  cases c with
  | nil =>
      exact False.elim (hc_ne rfl)
  | cons a c =>
      rcases hc_walk with ⟨hau, _⟩
      rw [walkVerticesFrom_eq_start_cons_map_head] at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨a, by simp, Or.inl hau⟩
      · rcases List.mem_map.mp hv with ⟨b, hb, rfl⟩
        exact ⟨b, List.mem_toFinset.mpr hb, Or.inr rfl⟩

/-- Helper for Lemma 4.10: every incident vertex of the support arc set appears on the closed
walk. -/
private theorem mem_walkVertices_of_mem_circuit_vertex_set
    {tail head : A → V} {w : V} {c : List A}
    (hc_walk : IsDirectedWalkFromTo tail head w w c) {v : V}
    (hv : v ∈ circuit_vertex_set tail head c.toFinset) :
    v ∈ walkVerticesFrom head w c := by
  rcases hv with ⟨a, haC, htail | hhead⟩
  · simpa [htail] using
      tail_mem_walkVerticesFrom_of_mem hc_walk (List.mem_toFinset.mp haC)
  · exact List.mem_of_mem_tail <|
      by simpa [hhead] using
        head_mem_walkVerticesTail_of_mem (head := head) (u := w) (p := c)
          (List.mem_toFinset.mp haC)

/-- Helper for Lemma 4.10: the support graph of a nonempty closed directed walk is connected on
its incident vertices. -/
private theorem connectedSupport_of_closedWalk
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c) :
    ((arc_induced_digraph tail head c.toFinset).toSimpleGraphInclusive.induce
      (circuit_vertex_set tail head c.toFinset)).Connected := by
  let G := (arc_induced_digraph tail head c.toFinset).toSimpleGraphInclusive
  rcases exists_supportWalk_of_directedWalk hc_walk with ⟨q, hq⟩
  have hconn : (G.induce {v | v ∈ q.support}).Connected := q.connected_induce_support
  have hverts : {v | v ∈ q.support} = circuit_vertex_set tail head c.toFinset := by
    ext v
    constructor
    · intro hv
      exact mem_circuit_vertex_set_of_mem_walkVertices_closedWalk hc_ne hc_walk ((hq v).1 hv)
    · intro hv
      exact (hq v).2 (mem_walkVertices_of_mem_circuit_vertex_set hc_walk hv)
  rw [hverts] at hconn
  simpa [G] using hconn

/-- Helper for Lemma 4.10: in a nonempty closed walk, the tail-vertex list and head-vertex list
have the same underlying membership. -/
private theorem mem_map_tail_iff_mem_map_head_of_closedWalk
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c) {v : V} :
    v ∈ c.map tail ↔ v ∈ c.map head := by
  let L := walkVerticesFrom head w c
  have hL_ne : L ≠ [] := by
    cases c with
    | nil =>
        exact False.elim (hc_ne rfl)
    | cons a c =>
        simp [L, walkVerticesFrom]
  have hL_head : L.head hL_ne = L.getLast hL_ne := by
    have hhead : L.head hL_ne = w := by
      cases c with
      | nil =>
          exact False.elim (hc_ne rfl)
      | cons a c =>
          simp [L, walkVerticesFrom, hL_ne]
    have hlast : L.getLast hL_ne = w := by
      simpa [L] using getLast_walkVerticesFrom hc_walk
    exact hhead.trans hlast.symm
  have hrot : L.dropLast ~r L.tail := List.IsRotated.dropLast_tail hL_ne hL_head
  simpa [L, directedWalk_map_tail_eq_dropLast_walkVertices hc_walk, walkVerticesFrom_tail_eq_map_head]
    using (hrot.mem_iff (a := v))

/-- Helper for Lemma 4.10: the tail-vertex list of a nonempty closed walk is nodup whenever the
head-vertex list is nodup. -/
private theorem map_tail_nodup_of_closedWalk_tailNodup
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c)
    (hc_nodup : (walkVerticesFrom head w c).tail.Nodup) :
    (c.map tail).Nodup := by
  let L := walkVerticesFrom head w c
  have hL_ne : L ≠ [] := by
    cases c with
    | nil =>
        exact False.elim (hc_ne rfl)
    | cons a c =>
        simp [L, walkVerticesFrom]
  have hL_head : L.head hL_ne = L.getLast hL_ne := by
    have hhead : L.head hL_ne = w := by
      cases c with
      | nil =>
          exact False.elim (hc_ne rfl)
      | cons a c =>
          simp [L, walkVerticesFrom, hL_ne]
    have hlast : L.getLast hL_ne = w := by
      simpa [L] using getLast_walkVerticesFrom hc_walk
    exact hhead.trans hlast.symm
  have hrot : L.dropLast ~r L.tail := List.IsRotated.dropLast_tail hL_ne hL_head
  have hdrop : L.dropLast.Nodup := (hrot.nodup_iff).2 hc_nodup
  simpa [L, directedWalk_map_tail_eq_dropLast_walkVertices hc_walk, walkVerticesFrom_tail_eq_map_head]
    using hdrop

/-- Helper for Lemma 4.10: each incident vertex of a nonempty closed walk is the head of exactly
one support arc when the internal visited vertices are pairwise distinct. -/
private theorem incomingArcCount_one_of_closedWalk_tailNodup
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c)
    (hc_nodup : (walkVerticesFrom head w c).tail.Nodup) :
    ∀ v ∈ circuit_vertex_set tail head c.toFinset, incoming_arc_count head c.toFinset v = 1 := by
  intro v hv
  have hheadNodup : (c.map head).Nodup := by
    simpa [walkVerticesFrom_tail_eq_map_head] using hc_nodup
  have hheadInj := List.inj_on_of_nodup_map hheadNodup
  have hexists : ∃ a, a ∈ c.toFinset ∧ head a = v := by
    rcases hv with ⟨a, haC, htail | hhead⟩
    · have htail_mem : v ∈ c.map tail := by
        rw [← htail]
        exact List.mem_map.mpr ⟨a, List.mem_toFinset.mp haC, rfl⟩
      have hhead_mem : v ∈ c.map head :=
        (mem_map_tail_iff_mem_map_head_of_closedWalk hc_ne hc_walk).1 htail_mem
      rcases List.mem_map.mp hhead_mem with ⟨b, hb, rfl⟩
      exact ⟨b, List.mem_toFinset.mpr hb, rfl⟩
    · exact ⟨a, haC, hhead⟩
  rcases hexists with ⟨a, haC, hheada⟩
  rw [incoming_arc_count, Finset.card_eq_one]
  refine ⟨a, ?_⟩
  ext b
  constructor
  · intro hb
    have hbC : b ∈ c.toFinset := (Finset.mem_filter.mp hb).1
    have hbhead : head b = v := (Finset.mem_filter.mp hb).2
    have hEq : b = a :=
      hheadInj (List.mem_toFinset.mp hbC) (List.mem_toFinset.mp haC) (hbhead.trans hheada.symm)
    simp [hEq]
  · intro hb
    have hEq : b = a := by simpa using hb
    subst hEq
    simp [haC, hheada]

/-- Helper for Lemma 4.10: each incident vertex of a nonempty closed walk is the tail of exactly
one support arc when the internal visited vertices are pairwise distinct. -/
private theorem outgoingArcCount_one_of_closedWalk_tailNodup
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c)
    (hc_nodup : (walkVerticesFrom head w c).tail.Nodup) :
    ∀ v ∈ circuit_vertex_set tail head c.toFinset, outgoing_arc_count tail c.toFinset v = 1 := by
  intro v hv
  have htailNodup : (c.map tail).Nodup :=
    map_tail_nodup_of_closedWalk_tailNodup hc_ne hc_walk hc_nodup
  have htailInj := List.inj_on_of_nodup_map htailNodup
  have hexists : ∃ a, a ∈ c.toFinset ∧ tail a = v := by
    rcases hv with ⟨a, haC, htail | hhead⟩
    · exact ⟨a, haC, htail⟩
    · have hhead_mem : v ∈ c.map head := by
        rw [← hhead]
        exact List.mem_map.mpr ⟨a, List.mem_toFinset.mp haC, rfl⟩
      have htail_mem : v ∈ c.map tail :=
        (mem_map_tail_iff_mem_map_head_of_closedWalk hc_ne hc_walk).2 hhead_mem
      rcases List.mem_map.mp htail_mem with ⟨b, hb, rfl⟩
      exact ⟨b, List.mem_toFinset.mpr hb, rfl⟩
  rcases hexists with ⟨a, haC, htaila⟩
  rw [outgoing_arc_count, Finset.card_eq_one]
  refine ⟨a, ?_⟩
  ext b
  constructor
  · intro hb
    have hbC : b ∈ c.toFinset := (Finset.mem_filter.mp hb).1
    have hbtail : tail b = v := (Finset.mem_filter.mp hb).2
    have hEq : b = a :=
      htailInj (List.mem_toFinset.mp hbC) (List.mem_toFinset.mp haC) (hbtail.trans htaila.symm)
    simp [hEq]
  · intro hb
    have hEq : b = a := by simpa using hb
    subst hEq
    simp [haC, htaila]

private theorem isSimpleCircuit_of_closedWalk_tailNodup
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c)
    (hc_nodup : (walkVerticesFrom head w c).tail.Nodup) :
    IsSimpleCircuit tail head c.toFinset := by
  -- Route correction: the remaining blocker is exactly the owner bridge from the extracted walk
  -- support to `IsSimpleCircuit`, split into connectivity and one-in-one-out support counts.
  refine ⟨?_, ?_, ?_⟩
  · cases c with
    | nil =>
        exact False.elim (hc_ne rfl)
    | cons a c =>
        exact ⟨a, by simp⟩
  · -- The undirected support graph is connected because one closed walk already traverses all of
    -- its incident vertices.
    exact connectedSupport_of_closedWalk hc_ne hc_walk
  · intro v hv
    -- The nodup visited-vertex condition upgrades the closed walk support to one-in-one-out.
    exact ⟨incomingArcCount_one_of_closedWalk_tailNodup hc_ne hc_walk hc_nodup v hv,
      outgoingArcCount_one_of_closedWalk_tailNodup hc_ne hc_walk hc_nodup v hv⟩

/-- Helper for Lemma 4.10: a positive sum of nonnegative terms has a positive summand. -/
private theorem exists_pos_of_sum_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ)
    (hnonneg : ∀ i ∈ s, 0 ≤ f i)
    (hsum : 0 < s.sum f) :
    ∃ i ∈ s, 0 < f i := by
  by_contra h
  have hnonpos : ∀ i ∈ s, f i ≤ 0 := by
    intro i hi
    by_contra hpos
    exact h ⟨i, hi, lt_of_not_ge hpos⟩
  have hzero : ∀ i ∈ s, f i = 0 := by
    intro i hi
    linarith [hnonneg i hi, hnonpos i hi]
  have hsum_zero : s.sum f = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    exact hzero i hi
  linarith

/-- Helper for Lemma 4.10: in a circulation, any vertex with a positive incoming arc also has a
positive outgoing arc. -/
private theorem exists_positive_outgoing_arc_of_positive_incoming_circulation
    {tail head : A → V} {z : A → ℝ}
    (hz : IsCirculation tail head z) {v : V}
    (hin : ∃ a, head a = v ∧ 0 < z a) :
    ∃ a, tail a = v ∧ 0 < z a := by
  classical
  have hin_pos : 0 < incoming_flow head z v := by
    rcases hin with ⟨a, ha, hza⟩
    unfold incoming_flow
    have ha_mem : a ∈ Finset.univ.filter (fun e ↦ head e = v) := by
      simp [ha]
    have hle :
        z a ≤ Finset.sum (Finset.univ.filter (fun e ↦ head e = v)) z := by
      exact Finset.single_le_sum (fun b hb ↦ hz.nonneg b) ha_mem
    exact lt_of_lt_of_le hza hle
  have hout_pos : 0 < outgoing_flow tail z v := by
    -- A circulation has equal incoming and outgoing flow at every vertex.
    rw [← hz.flow_conservation v]
    exact hin_pos
  unfold outgoing_flow at hout_pos
  rcases exists_pos_of_sum_pos (Finset.univ.filter fun e ↦ tail e = v) z
      (fun a _ ↦ hz.nonneg a) hout_pos with ⟨a, ha, hza⟩
  exact ⟨a, (Finset.mem_filter.mp ha).2, hza⟩

/-- Helper for Lemma 4.10: every nonzero circulation contains a positive closed walk whose
internal visited vertices are pairwise distinct. -/
private theorem positiveSupportClosedWalk_of_circulation
    {tail head : A → V} {z : A → ℝ}
    (hz : IsCirculation tail head z)
    (hpos : ∃ a, 0 < z a) :
    ∃ w : V, ∃ c : List A, c ≠ [] ∧ IsDirectedWalkFromTo tail head w w c ∧
      (walkVerticesFrom head w c).tail.Nodup ∧ ∀ a ∈ c.toFinset, 0 < z a := by
  classical
  rcases hpos with ⟨a₀, hza₀⟩
  let s := tail a₀
  by_cases hloop : head a₀ = s
  · refine ⟨s, [a₀], by simp, ?_, ?_, ?_⟩
    · simpa [IsDirectedWalkFromTo, s, hloop]
    · simp [walkVerticesFrom, hloop]
    · intro a ha
      have ha' : a = a₀ := by simpa using ha
      simpa [ha'] using hza₀
  · let S : Set (List A) :=
      {p | ∃ u, IsDirectedWalkFromTo tail head s u p ∧
          (walkVerticesFrom head s p).Nodup ∧
          ∀ b ∈ p.toFinset, 0 < z b}
    have hSfinite : S.Finite := by
      refine (List.finite_length_le A (Fintype.card A)).subset ?_
      intro p hpS
      rcases hpS with ⟨u, hwalk, hnodup, _⟩
      have hpNodup : p.Nodup := directedWalk_nodup_of_verticesNodup hwalk hnodup
      exact List.Nodup.length_le_card hpNodup
    have ha₀_in_S : [a₀] ∈ S := by
      refine ⟨head a₀, ?_, ?_, ?_⟩
      · simpa [IsDirectedWalkFromTo, s]
      · simpa [walkVerticesFrom, List.mem_singleton, eq_comm, s] using
          (List.nodup_cons.2
            ⟨by simpa [s, List.mem_singleton, eq_comm] using hloop, List.nodup_singleton _⟩)
      · intro b hb
        have hb' : b = a₀ := by simpa using hb
        simpa [hb'] using hza₀
    have hSnonempty : S.Nonempty := ⟨[a₀], ha₀_in_S⟩
    rcases Set.exists_max_image S List.length hSfinite hSnonempty with ⟨p, hpS, hpmax⟩
    rcases hpS with ⟨u, hwalk, hnodup, hposp⟩
    have hp_nonempty : p ≠ [] := by
      have hmax₀ := hpmax [a₀] ha₀_in_S
      intro hpnil
      simpa [hpnil] using hmax₀
    have hin :
        ∃ a, a ∈ p.toFinset ∧ head a = u ∧ 0 < z a :=
      exists_positive_incoming_arc_at_walkEndpoint hwalk hp_nonempty hposp
    rcases exists_positive_outgoing_arc_of_positive_incoming_circulation hz
        (by
          rcases hin with ⟨a, _, ha, hza⟩
          exact ⟨a, ha, hza⟩) with ⟨a, htail, hza⟩
    by_cases hvisited : head a ∈ walkVerticesFrom head s p
    · rcases positiveWalkRepeatedVertex_yieldsCircuitSuffix hwalk hnodup hposp htail hza hvisited
          with ⟨c, hc_ne, hwalkc, hnodupc, hcpos⟩
      exact ⟨head a, c, hc_ne, hwalkc, hnodupc, hcpos⟩
    · have hsingle : IsDirectedWalkFromTo tail head u (head a) [a] := by
        exact ⟨htail, rfl⟩
      have hwalk' : IsDirectedWalkFromTo tail head s (head a) (p ++ [a]) := by
        exact directedWalk_append hwalk hsingle
      have hvertices' :
          walkVerticesFrom head s (p ++ [a]) = walkVerticesFrom head s p ++ [head a] := by
        have happ := walkVerticesFrom_append hwalk hsingle
        simpa [walkVerticesFrom] using happ
      have hnodup' : (walkVerticesFrom head s (p ++ [a])).Nodup := by
        rw [hvertices']
        refine List.Nodup.append hnodup (by simp) ?_
        refine List.disjoint_left.2 ?_
        intro x hx hxlast
        have hxhead : x = head a := by simpa using hxlast
        subst hxhead
        exact hvisited hx
      have hpos' : ∀ b ∈ (p ++ [a]).toFinset, 0 < z b := by
        intro b hb
        have hb' : b ∈ p ++ [a] := List.mem_toFinset.mp hb
        rcases List.mem_append.mp hb' with hb | hb
        · exact hposp b (by simpa using hb)
        · have hbEq : b = a := by simpa using hb
          subst hbEq
          exact hza
      have hpS' : p ++ [a] ∈ S := by
        exact ⟨head a, hwalk', hnodup', hpos'⟩
      have hle := hpmax (p ++ [a]) hpS'
      exact False.elim (Nat.not_succ_le_self p.length (by simpa using hle))

/-- Helper for Lemma 4.10: every nonzero circulation contains a simple circuit inside its positive
support. -/
private theorem exists_simpleCircuit_subset_positiveSupport
    {tail head : A → V} {x : A → ℝ}
    (hx : x ∈ circulation_cone tail head) (hx_ne : x ≠ 0) :
    ∃ C : Finset A, IsSimpleCircuit tail head C ∧ ∀ a ∈ C, 0 < x a := by
  -- Route correction: first extract a positive closed walk with no repeated internal vertices.
  rw [mem_circulation_cone_iff, isCirculation_iff] at hx
  rcases hx with ⟨hflow, hnonneg⟩
  have hpos : ∃ a, 0 < x a := by
    by_contra hno
    apply hx_ne
    ext a
    have hxa_nonneg : 0 ≤ x a := hnonneg a
    have hxa_nonpos : x a ≤ 0 := by
      by_contra hxa_pos
      exact hno ⟨a, lt_of_not_ge hxa_pos⟩
    exact le_antisymm hxa_nonpos hxa_nonneg
  rcases positiveSupportClosedWalk_of_circulation ⟨hflow, hnonneg⟩ hpos with
    ⟨w, c, hc_ne, hc_walk, hc_nodup, hc_pos⟩
  let C : Finset A := c.toFinset
  -- The extracted closed walk already has the exact combinatorics of a simple circuit support.
  have hC_simple : IsSimpleCircuit tail head C := by
    simpa [C] using isSimpleCircuit_of_closedWalk_tailNodup hc_ne hc_walk hc_nodup
  refine ⟨C, hC_simple, ?_⟩
  intro a haC
  exact hc_pos a haC

/-- Lemma 4.10. For a finite digraph encoded by its tail and head maps, every extreme ray of the
circulation cone is the same ray as the characteristic vector of a simple circuit. -/
theorem extreme_ray_of_circulation_cone_sameRay_circuit_characteristic_vector
    (tail head : A → V)
    {x : A → ℝ}
    (hx : IsExtremeRayOfCone (circulation_cone tail head) x) :
    ∃ C : Finset A, IsSimpleCircuit tail head C ∧
      SameRay ℝ x (circuit_characteristic_vector C) := by
  classical
  -- Route correction: instead of the missing TU/polytope bridge, finish from an extracted positive
  -- simple circuit and rule out any support gap by the cone-level decomposition criterion.
  have hx_mem : x ∈ circulation_cone tail head := extreme_ray_mem_of_isExtremeRayOfCone hx
  have hx_ne : x ≠ 0 := extreme_ray_ne_zero hx
  have hx_circ : IsCirculation tail head x := (mem_circulation_cone_iff tail head x).1 hx_mem
  rcases exists_simpleCircuit_subset_positiveSupport hx_mem hx_ne with ⟨C, hC, hpos⟩
  by_cases hsupp : ∀ a, a ∉ C → x a = 0
  · -- If the whole support is already this circuit, support rigidity gives the same-ray witness.
    rcases supported_circulation_is_scalar_multiple_of_circuit_characteristic_vector hC hx_mem hsupp
      with ⟨μ, hμ_nonneg, hx_eq⟩
    have hμ_ne_zero : μ ≠ 0 := by
      intro hμ_zero
      apply hx_ne
      ext a
      simp [hx_eq, hμ_zero]
    have hμ_pos : 0 < μ := lt_of_le_of_ne hμ_nonneg (Ne.symm hμ_ne_zero)
    refine ⟨C, hC, ?_⟩
    rw [hx_eq]
    exact SameRay.sameRay_pos_smul_left (circuit_characteristic_vector C) hμ_pos
  · -- Otherwise, subtract the minimum circuit value to obtain a forbidden proper conic sum.
    rcases not_forall.mp hsupp with ⟨a_gap, hsupp_gap⟩
    rcases Classical.not_imp.mp hsupp_gap with ⟨ha_gap, hx_gap_ne_zero⟩
    have hx_gap_pos : 0 < x a_gap := lt_of_le_of_ne (hx_circ.nonneg a_gap) (Ne.symm hx_gap_ne_zero)
    let values : Finset ℝ := C.image x
    have hvalues_nonempty : values.Nonempty := by
      rcases hC.nonempty with ⟨a, ha⟩
      exact ⟨x a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
    let μ : ℝ := values.min' hvalues_nonempty
    have hμ_pos : 0 < μ := by
      rcases Finset.mem_image.mp (Finset.min'_mem values hvalues_nonempty) with ⟨a, haC, hμ_eq⟩
      have hμ_eq' : μ = x a := by
        simpa [μ] using hμ_eq.symm
      rw [hμ_eq']
      exact hpos a haC
    have hμ_le : ∀ a, a ∈ C → μ ≤ x a := by
      intro a haC
      exact Finset.min'_le values (x a) (Finset.mem_image.mpr ⟨a, haC, rfl⟩)
    let z : A → ℝ := μ • circuit_characteristic_vector C
    let y : A → ℝ := x - z
    have hz_mem : z ∈ circulation_cone tail head := by
      -- The circuit characteristic vector stays in the cone under nonnegative scaling.
      exact smul_mem_circulation_cone (circuit_characteristic_vector_mem_circulation_cone hC)
        (le_of_lt hμ_pos)
    have hz_circ : IsCirculation tail head z := (mem_circulation_cone_iff tail head z).1 hz_mem
    have hy_mem : y ∈ circulation_cone tail head := by
      -- The minimum choice keeps the remainder nonnegative while preserving flow conservation.
      rw [mem_circulation_cone_iff, isCirculation_iff]
      refine ⟨?_, ?_⟩
      · intro v
        calc
          incoming_flow head y v = incoming_flow head x v - incoming_flow head z v := by
            simp [y, incoming_flow, Finset.sum_sub_distrib]
          _ = outgoing_flow tail x v - outgoing_flow tail z v := by
            rw [hx_circ.flow_conservation v, hz_circ.flow_conservation v]
          _ = outgoing_flow tail y v := by
            simp [y, outgoing_flow, Finset.sum_sub_distrib]
      · intro a
        by_cases ha : a ∈ C
        · have hsub_nonneg : 0 ≤ x a - μ := sub_nonneg.mpr (hμ_le a ha)
          simpa [y, z, circuit_characteristic_vector_apply, ha, Pi.smul_apply] using hsub_nonneg
        · simpa [y, z, circuit_characteristic_vector_apply, ha, Pi.smul_apply]
            using hx_circ.nonneg a
    have hy_ne : y ≠ 0 := by
      intro hy_zero
      have hy_eval := congrArg (fun f : A → ℝ ↦ f a_gap) hy_zero
      have : x a_gap = 0 := by
        simpa [y, z, circuit_characteristic_vector_apply, ha_gap, Pi.smul_apply] using hy_eval
      exact hx_gap_ne_zero this
    have hz_ne : z ≠ 0 := by
      rcases hC.nonempty with ⟨aC, haC⟩
      intro hz_zero
      have hz_eval := congrArg (fun f : A → ℝ ↦ f aC) hz_zero
      have : μ = 0 := by
        simpa [z, circuit_characteristic_vector_apply, haC, Pi.smul_apply] using hz_eval
      exact (ne_of_gt hμ_pos) this
    have hyz_not_same : ¬ SameRay ℝ y z := by
      intro hyz_same
      rcases hyz_same.exists_nonneg_right hz_ne with ⟨t, ht, hy_eq⟩
      have hy_gap_zero : y a_gap = 0 := by
        have hy_eval := congrArg (fun f : A → ℝ ↦ f a_gap) hy_eq
        simpa [z, circuit_characteristic_vector_apply, ha_gap, Pi.smul_apply] using hy_eval
      have hy_gap_pos : 0 < y a_gap := by
        simpa [y, z, circuit_characteristic_vector_apply, ha_gap, Pi.smul_apply] using hx_gap_pos
      linarith
    have hx_not_combo :
        ¬ ProperConicCombinationOfDistinctConeRays (circulation_cone tail head) x :=
      (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays hx_mem hx_ne).1 hx
    exfalso
    apply hx_not_combo
    refine ⟨y, z, hy_mem, hz_mem, hy_ne, hz_ne, hyz_not_same, 1, 1, by norm_num, by norm_num, ?_⟩
    ext a
    simp [y, z, sub_eq_add_neg, add_assoc]

end Lemma_4_10
