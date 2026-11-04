/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_1.ch4_sec4_3_1_definition_4_3_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_definition_3_15_extra_1

noncomputable section

open scoped BigOperators

/-- Reusable simple-circuit API: each incident vertex of a simple circuit has a unique incoming
arc in that circuit. -/
theorem existsUnique_incomingArc_of_isSimpleCircuit
    {V A : Type*} {tail head : A → V} {C : Finset A}
    (hC : IsSimpleCircuit tail head C) (v : V) (hv : v ∈ circuit_vertex_set tail head C) :
    ∃! a : A, a ∈ C ∧ head a = v := by
  classical
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

/-- Reusable simple-circuit API: each incident vertex of a simple circuit has a unique outgoing
arc in that circuit. -/
theorem existsUnique_outgoingArc_of_isSimpleCircuit
    {V A : Type*} {tail head : A → V} {C : Finset A}
    (hC : IsSimpleCircuit tail head C) (v : V) (hv : v ∈ circuit_vertex_set tail head C) :
    ∃! a : A, a ∈ C ∧ tail a = v := by
  classical
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

/-- If a flow vanishes off `C`, its outgoing flow at `v` is the sum over the arcs of `C` leaving
`v`. -/
theorem outgoingFlow_eq_sum_filter_of_eq_zero_offSupport
    {V A : Type*} [Fintype A] [DecidableEq V] {tail : A → V} {C : Finset A} {x : A → ℝ}
    (hsupp : ∀ a, a ∉ C → x a = 0) (v : V) :
    outgoing_flow tail x v = Finset.sum (C.filter fun a ↦ tail a = v) x := by
  classical
  unfold outgoing_flow
  symm
  refine Finset.sum_subset ?_ ?_
  · intro a ha
    have hav : tail a = v := (Finset.mem_filter.mp ha).2
    have haC : a ∈ C := (Finset.mem_filter.mp ha).1
    simp [hav] at ha ⊢
  · intro a ha_out ha_not_mem
    have ha_not_C : a ∉ C := by
      intro haC
      exact ha_not_mem (by simpa [haC] using ha_out)
    exact hsupp a ha_not_C

/-- If a flow vanishes off `C`, its incoming flow at `v` is the sum over the arcs of `C` entering
`v`. -/
theorem incomingFlow_eq_sum_filter_of_eq_zero_offSupport
    {V A : Type*} [Fintype A] [DecidableEq V] {head : A → V} {C : Finset A} {x : A → ℝ}
    (hsupp : ∀ a, a ∉ C → x a = 0) (v : V) :
    incoming_flow head x v = Finset.sum (C.filter fun a ↦ head a = v) x := by
  classical
  unfold incoming_flow
  symm
  refine Finset.sum_subset ?_ ?_
  · intro a ha
    have hav : head a = v := (Finset.mem_filter.mp ha).2
    have haC : a ∈ C := (Finset.mem_filter.mp ha).1
    simp [hav] at ha ⊢
  · intro a ha_in ha_not_mem
    have ha_not_C : a ∉ C := by
      intro haC
      exact ha_not_mem (by simpa [haC] using ha_in)
    exact hsupp a ha_not_C

/-- The characteristic vector of a simple circuit lies in the circulation cone. -/
theorem circuitCharacteristicVector_mem_circulationCone
    {V A : Type*} [Fintype A] {tail head : A → V} {C : Finset A}
    (hC : IsSimpleCircuit tail head C) :
    circuit_characteristic_vector C ∈ circulation_cone tail head := by
  classical
  rw [mem_circulation_cone_iff, isCirculation_iff]
  refine ⟨?_, ?_⟩
  · intro v
    have hsupp : ∀ a, a ∉ C → circuit_characteristic_vector C a = 0 := by
      intro a ha
      simp [circuit_characteristic_vector_apply, ha]
    rw [incomingFlow_eq_sum_filter_of_eq_zero_offSupport hsupp,
      outgoingFlow_eq_sum_filter_of_eq_zero_offSupport hsupp]
    have hsubset_in : C.filter (fun a ↦ head a = v) ⊆ C := by
      intro a ha
      exact (Finset.mem_filter.mp ha).1
    have hsubset_out : C.filter (fun a ↦ tail a = v) ⊆ C := by
      intro a ha
      exact (Finset.mem_filter.mp ha).1
    have hsum_in :
        Finset.sum (C.filter (fun a ↦ head a = v)) (circuit_characteristic_vector C) =
          ((C.filter (fun a ↦ head a = v)).card : ℝ) := by
      simp [Finset.inter_eq_left.mpr hsubset_in, circuit_characteristic_vector_apply]
    have hsum_out :
        Finset.sum (C.filter (fun a ↦ tail a = v)) (circuit_characteristic_vector C) =
          ((C.filter (fun a ↦ tail a = v)).card : ℝ) := by
      simp [Finset.inter_eq_left.mpr hsubset_out, circuit_characteristic_vector_apply]
    rw [hsum_in, hsum_out]
    exact_mod_cast hC.balanced v
  · intro a
    by_cases ha : a ∈ C
    · simp [circuit_characteristic_vector_apply, ha]
    · simp [circuit_characteristic_vector_apply, ha]

/-- Nonnegative scalar multiples preserve circulation-cone membership. -/
theorem smul_mem_circulationCone
    {V A : Type*} [Fintype A] {tail head : A → V} {x : A → ℝ} {μ : ℝ}
    (hx : x ∈ circulation_cone tail head) (hμ : 0 ≤ μ) :
    μ • x ∈ circulation_cone tail head := by
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

section

variable {V A : Type*}

-- Local instance justification (defeq pin): fixes the `List.toFinset`/`Finset.filter` path.
noncomputable local instance : DecidableEq A := Classical.decEq A
-- Local instance justification (defeq pin): fixes the head/tail filter predicate path.
noncomputable local instance : DecidableEq V := Classical.decEq V

/-- A list of arcs is a directed walk from `u` to `v` when consecutive arc endpoints match,
starting at `u` and ending at `v`. -/
private def IsDirectedWalkFromTo (tail head : A → V) : V → V → List A → Prop
  | u, v, [] => u = v
  | u, v, a :: p => tail a = u ∧ IsDirectedWalkFromTo tail head (head a) v p

/-- The ordered vertex list visited by a directed walk. -/
private def walkVerticesFrom (head : A → V) (u : V) : List A → List V
  | [] => [u]
  | a :: p => u :: walkVerticesFrom head (head a) p

/-- The visited vertices of a walk are the start vertex followed by the heads of the traversed
arcs. -/
private theorem walkVerticesFrom_eq_start_cons_map_head
    {head : A → V} (u : V) (p : List A) :
    walkVerticesFrom head u p = u :: p.map head := by
  induction p generalizing u with
  | nil =>
      simp [walkVerticesFrom]
  | cons a p ih =>
      simp [walkVerticesFrom, ih]

/-- The tail of the visited-vertex list is exactly the head list of the walk arcs. -/
private theorem walkVerticesFrom_tail_eq_map_head
    {head : A → V} (u : V) (p : List A) :
    (walkVerticesFrom head u p).tail = p.map head := by
  simp [walkVerticesFrom_eq_start_cons_map_head]

/-- Every arc of a walk contributes its tail vertex to the visited-vertex list. -/
private theorem tail_mem_walkVerticesFrom_of_mem
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      ∀ {a : A}, a ∈ p → tail a ∈ walkVerticesFrom head u p
  | _, _, [], hwalk, _, hmem => by
      cases hmem
  | u, v, b :: p, hwalk, a, hmem => by
      rcases hwalk with ⟨hbu, hp⟩
      rw [walkVerticesFrom]
      rcases List.mem_cons.mp hmem with rfl | hmemTail
      · simp [hbu]
      · exact List.mem_cons_of_mem _ (tail_mem_walkVerticesFrom_of_mem hp hmemTail)

/-- Every arc of a walk contributes its head vertex to the tail of the visited-vertex list. -/
private theorem head_mem_walkVerticesTail_of_mem
    {head : A → V} (u : V) {p : List A} {a : A} (ha : a ∈ p) :
    head a ∈ (walkVerticesFrom head u p).tail := by
  rw [walkVerticesFrom_tail_eq_map_head]
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

/-- Concatenating directed walks with a matching intermediate endpoint produces the evident longer
walk. -/
private theorem directedWalk_append
    {tail head : A → V} :
    ∀ {u w v : V} {p q : List A},
      IsDirectedWalkFromTo tail head u w p →
        IsDirectedWalkFromTo tail head w v q →
          IsDirectedWalkFromTo tail head u v (p ++ q)
  | _, _, _, [], q, hp, hq => by
      subst hp
      simpa using hq
  | u, w, v, a :: p, q, hp, hq => by
      rcases hp with ⟨hau, hpTail⟩
      exact ⟨hau, directedWalk_append hpTail hq⟩

/-- Splitting a walk at a visited vertex yields compatible prefix and suffix walks. -/
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
      refine ⟨[], [], rfl, rfl, rfl⟩
  | u, v, w, a :: p, hp, hw => by
      rcases hp with ⟨hau, hpTail⟩
      rw [walkVerticesFrom] at hw
      rcases List.mem_cons.mp hw with rfl | hwTail
      · refine ⟨[], a :: p, by simp, rfl, ?_⟩
        exact ⟨hau, hpTail⟩
      · rcases directedWalk_split_at_visited_vertex hpTail hwTail with
          ⟨p₁, p₂, hpSplit, hp₁, hp₂⟩
        refine ⟨a :: p₁, p₂, ?_, ?_, hp₂⟩
        · simp [hpSplit]
        · exact ⟨hau, by simpa [hpSplit] using hp₁⟩

/-- Visited vertices of appended walks concatenate as expected. -/
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
      simp [walkVerticesFrom, walkVerticesFrom_append hpTail hq]

/-- The endpoint of a directed walk appears in its visited-vertex list. -/
private theorem terminalVertex_mem_walkVerticesFrom
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      v ∈ walkVerticesFrom head u p
  | _, _, [], hp => by
      subst hp
      simp [walkVerticesFrom]
  | u, v, a :: p, hp => by
      rcases hp with ⟨hau, hpTail⟩
      simp [walkVerticesFrom, terminalVertex_mem_walkVerticesFrom hpTail]

/-- If the visited vertices of a walk are nodup, then so are the walk arcs. -/
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
        have htailMem : tail a ∈ walkVerticesFrom head (head a) p :=
          tail_mem_walkVerticesFrom_of_mem hpTail hmem
        have huMem : u ∈ walkVerticesFrom head (head a) p := by
          simpa [hau] using htailMem
        exact hu_not_mem huMem
      exact List.nodup_cons.mpr ⟨ha_not_mem, hpNodup⟩

/-- The final arc of a nonempty directed walk is a positive incoming arc at the endpoint whenever
every traversed arc is positive. -/
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

/-- If a positive walk revisits an earlier vertex after one more positive arc, the repeated-vertex
suffix is already a positive closed walk with nodup internal vertices. -/
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
  rcases directedWalk_split_at_visited_vertex hp hhead with
    ⟨p₁, p₂, rfl, hp₁, hp₂⟩
  let w := head a
  let c : List A := p₂ ++ [a]
  have hsingle : IsDirectedWalkFromTo tail head u w [a] := by
    exact ⟨htail, rfl⟩
  have hwalkc : IsDirectedWalkFromTo tail head w w c := by
    simpa [c, w] using directedWalk_append hp₂ hsingle
  have hsplitVertices :
      walkVerticesFrom head s (p₁ ++ p₂) =
        walkVerticesFrom head s p₁ ++ (walkVerticesFrom head w p₂).tail := by
    simpa [w] using walkVerticesFrom_append hp₁ hp₂
  have htailNodup : (walkVerticesFrom head w p₂).tail.Nodup := by
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
      have happ := walkVerticesFrom_append hp₂ hsingle
      simpa [c, w, walkVerticesFrom, htail] using happ
    have htail_append :
        (walkVerticesFrom head w c).tail = (walkVerticesFrom head w p₂).tail ++ [w] := by
      cases p₂ with
      | nil =>
          simp [walkVerticesFrom, c, w]
      | cons b p₂ =>
          simp [hvertices_c, walkVerticesFrom]
    have hdisjTail : List.Disjoint (walkVerticesFrom head w p₂).tail [w] := by
      refine List.disjoint_left.2 ?_
      intro x hx hxw
      have hxw' : x = w := by simpa using hxw
      subst hxw'
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

/-- Enlarging the supporting arc set only enlarges the induced undirected support graph. -/
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

/-- The terminal vertex of a directed walk is the last visited vertex. -/
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

/-- The tail sequence of a directed walk is the visited-vertex list with the terminal vertex
removed. -/
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

/-- Every closed directed walk yields an undirected support walk in the induced support graph with
the same visited-vertex set. -/
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

/-- Every visited vertex of a nonempty closed walk is incident to its support arc set. -/
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

/-- Every incident vertex of the support arc set appears on the closed walk. -/
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

/-- The support graph of a nonempty closed directed walk is connected on its incident vertices. -/
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

/-- In a nonempty closed walk, the tail-vertex list and head-vertex list have the same underlying
membership. -/
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
          simp [L, walkVerticesFrom]
    have hlast : L.getLast hL_ne = w := by
      simpa [L] using getLast_walkVerticesFrom hc_walk
    exact hhead.trans hlast.symm
  have hrot : L.dropLast ~r L.tail := List.IsRotated.dropLast_tail hL_ne hL_head
  simpa
    [L, directedWalk_map_tail_eq_dropLast_walkVertices hc_walk, walkVerticesFrom_tail_eq_map_head]
    using (hrot.mem_iff (a := v))

/-- The tail-vertex list of a nonempty closed walk is nodup whenever the head-vertex list is
nodup. -/
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
          simp [L, walkVerticesFrom]
    have hlast : L.getLast hL_ne = w := by
      simpa [L] using getLast_walkVerticesFrom hc_walk
    exact hhead.trans hlast.symm
  have hrot : L.dropLast ~r L.tail := List.IsRotated.dropLast_tail hL_ne hL_head
  have hdrop : L.dropLast.Nodup := (hrot.nodup_iff).2 hc_nodup
  simpa
    [L, directedWalk_map_tail_eq_dropLast_walkVertices hc_walk, walkVerticesFrom_tail_eq_map_head]
    using hdrop

/-- Each incident vertex of a nonempty closed walk is the head of exactly one support arc when the
internal visited vertices are pairwise distinct. -/
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

/-- Each incident vertex of a nonempty closed walk is the tail of exactly one support arc when the
internal visited vertices are pairwise distinct. -/
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

/-- A nonempty closed walk with nodup internal visited vertices already has simple-circuit
support. -/
private theorem isSimpleCircuit_of_closedWalk_tailNodup
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c)
    (hc_nodup : (walkVerticesFrom head w c).tail.Nodup) :
    IsSimpleCircuit tail head c.toFinset := by
  refine ⟨?_, ?_, ?_⟩
  · cases c with
    | nil =>
        exact False.elim (hc_ne rfl)
    | cons a c =>
        exact ⟨a, by simp⟩
  · exact connectedSupport_of_closedWalk hc_ne hc_walk
  · intro v hv
    exact ⟨incomingArcCount_one_of_closedWalk_tailNodup hc_ne hc_walk hc_nodup v hv,
      outgoingArcCount_one_of_closedWalk_tailNodup hc_ne hc_walk hc_nodup v hv⟩

/-- A positive sum of nonnegative terms has a positive summand. -/
private theorem exists_pos_of_sum_pos
    {ι : Type*} (s : Finset ι) (f : ι → ℝ)
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

/-- In a circulation, any vertex with a positive incoming arc also has a positive outgoing arc. -/
private theorem exists_positive_outgoing_arc_of_positive_incoming_circulation
    [Fintype A] {tail head : A → V} {z : A → ℝ}
    (hz : IsCirculation tail head z) {v : V}
    (hin : ∃ a, head a = v ∧ 0 < z a) :
    ∃ a, tail a = v ∧ 0 < z a := by
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
    rw [← hz.flow_conservation v]
    exact hin_pos
  unfold outgoing_flow at hout_pos
  rcases exists_pos_of_sum_pos (Finset.univ.filter fun e ↦ tail e = v) z
      (fun a _ ↦ hz.nonneg a) hout_pos with ⟨a, ha, hza⟩
  exact ⟨a, (Finset.mem_filter.mp ha).2, hza⟩

/-- Every nonzero circulation contains a positive closed walk whose internal visited vertices are
pairwise distinct. -/
private theorem positiveSupportClosedWalk_of_circulation
    [Fintype A] {tail head : A → V} {z : A → ℝ}
    (hz : IsCirculation tail head z)
    (hpos : ∃ a, 0 < z a) :
    ∃ w : V, ∃ c : List A, c ≠ [] ∧ IsDirectedWalkFromTo tail head w w c ∧
      (walkVerticesFrom head w c).tail.Nodup ∧ ∀ a ∈ c.toFinset, 0 < z a := by
  rcases hpos with ⟨a₀, hza₀⟩
  let s := tail a₀
  by_cases hloop : head a₀ = s
  · refine ⟨s, [a₀], by simp, ?_, ?_, ?_⟩
    · simp [IsDirectedWalkFromTo, s, hloop]
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
      · simp [IsDirectedWalkFromTo, s]
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
      simp [hpnil] at hmax₀
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
      have : False := by
        simp at hle
      exact False.elim this

/-- Every nonzero circulation contains a simple circuit inside its positive support. -/
private theorem exists_simpleCircuit_subset_positiveSupport
    [Fintype A] {tail head : A → V} {x : A → ℝ}
    (hx : x ∈ circulation_cone tail head) (hx_ne : x ≠ 0) :
    ∃ C : Finset A, IsSimpleCircuit tail head C ∧ ∀ a ∈ C, 0 < x a := by
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
  have hC_simple : IsSimpleCircuit tail head C := by
    simpa [C] using isSimpleCircuit_of_closedWalk_tailNodup hc_ne hc_walk hc_nodup
  refine ⟨C, hC_simple, ?_⟩
  intro a haC
  exact hc_pos a haC

end

/-- Every nonzero circulation contains a simple circuit inside its positive support. -/
theorem existsSimpleCircuitSubsetPositiveSupport
    {V A : Type*} [Fintype A] {tail head : A → V} {x : A → ℝ}
    (hx : x ∈ circulation_cone tail head) (hx_ne : x ≠ 0) :
    ∃ C : Finset A, IsSimpleCircuit tail head C ∧ ∀ a ∈ C, 0 < x a := by
  classical
  exact exists_simpleCircuit_subset_positiveSupport hx hx_ne
