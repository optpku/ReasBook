/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_theorem_3_40
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3.ch4_sec4_3_definition_4_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_1.ch4_sec4_3_1_definition_4_3_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_definition_4_3_3_extra_1
import Mathlib

open scoped BigOperators Matrix

-- This source-facing exercise is organized around the Chapter 4 owners `IsSimpleCircuit` and
-- `circuit_characteristic_vector`, while reusing the Chapter 3 owner `IsExtremeRayOfCone`.
-- The incidence-matrix formulation is kept only as a bridge.

section Exercise_4_13

variable {V A : Type}

/-- Membership in the pointed-cone hull of a singleton is exactly being a nonnegative scalar
multiple of its generator. -/
theorem mem_singleton_pointedCone_hull_iff {E : Type*} [AddCommGroup E] [Module ℝ E] {r x : E} :
    x ∈ (PointedCone.hull ℝ ({r} : Set E) : Set E) ↔
      ∃ μ : ℝ, 0 ≤ μ ∧ x = μ • r := by
  constructor
  · intro hx
    -- Collapse the finite conic-combination presentation to a single scalar because every
    -- generator lies in the singleton `{r}`.
    rcases (mem_hull_iff).1 hx with ⟨q, s, hs, coeff, hcoeff_nonneg, hx_eq⟩
    refine ⟨∑ j, coeff j, Finset.sum_nonneg fun j _ ↦ hcoeff_nonneg j, ?_⟩
    calc
      x = ∑ j, coeff j • s j := hx_eq
      _ = ∑ j, coeff j • r := by
        refine Finset.sum_congr rfl ?_
        intro j _
        simpa using congrArg (fun y : E ↦ coeff j • y) (Set.mem_singleton_iff.mp (hs j))
      _ = (∑ j, coeff j) • r := by
        simpa using (Finset.sum_smul (s := Finset.univ) (f := coeff) (x := r)).symm
  · rintro ⟨μ, hμ, rfl⟩
    -- A singleton ray is already a one-term conic combination in the hull presentation.
    refine (mem_hull_iff).2 ?_
    refine ⟨1, fun _ ↦ r, fun _ ↦ by simp, fun _ ↦ μ, fun _ ↦ hμ, ?_⟩
    simpa using (show (μ • r) = ∑ j : Fin 1, μ • r by simp)

section FiniteDigraph

variable [Fintype A]

/-- Evaluating the chapter incidence matrix on an arc vector gives incoming minus outgoing flow at
each vertex. -/
theorem digraph_incidence_matrix_mulVec_apply
    (tail head : A → V) (x : A → ℝ) (v : V) :
    (digraph_incidence_matrix ℝ tail head *ᵥ x) v =
      incoming_flow head x v - outgoing_flow tail x v := by
  classical
  have hhead_sum :
      ∑ e, (if v = head e then x e else 0) = incoming_flow head x v := by
    -- The head-indicator part keeps exactly the arcs entering `v`.
    rw [incoming_flow_eq_sum_incoming_arcs]
    rw [incoming_arcs, Finset.sum_filter]
    simp [eq_comm]
  have htail_sum :
      ∑ e, (if v = tail e then x e else 0) = outgoing_flow tail x v := by
    -- The tail-indicator part keeps exactly the arcs leaving `v`.
    rw [outgoing_flow_eq_sum_outgoing_arcs]
    rw [outgoing_arcs, Finset.sum_filter]
    simp [eq_comm]
  -- Split the matrix entry into its head and tail contributions and rewrite each sum separately.
  calc
    (digraph_incidence_matrix ℝ tail head *ᵥ x) v
        = ∑ e, (((if v = head e then (1 : ℝ) else 0) -
            (if v = tail e then 1 else 0)) * x e) := by
            simp [Matrix.mulVec, dotProduct, digraph_incidence_matrix]
    _ = ∑ e, ((if v = head e then x e else 0) -
          (if v = tail e then x e else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro e _
            by_cases hhead : v = head e
            · by_cases htail : v = tail e
              · have hend : head e = tail e := hhead.symm.trans htail
                simp [hhead, htail, hend]
              · have hend : head e ≠ tail e := fun hend ↦ htail (hhead.trans hend)
                simp [hhead, htail, hend]
            · by_cases htail : v = tail e
              · have hend : tail e ≠ head e := fun hend ↦ hhead (htail.trans hend)
                simp [hhead, htail, hend]
              · simp [hhead, htail]
    _ = (∑ e, (if v = head e then x e else 0)) -
          ∑ e, (if v = tail e then x e else 0) := by
            rw [Finset.sum_sub_distrib]
    _ = incoming_flow head x v - outgoing_flow tail x v := by
          rw [hhead_sum, htail_sum]

/-- In this finite setting, the chapter circulation cone is exactly the nonnegative kernel of the
chapter digraph incidence matrix. -/
theorem mem_circulation_cone_iff_digraph_incidence_matrix_mulVec_eq_zero
    (tail head : A → V) (x : A → ℝ) :
    x ∈ circulation_cone tail head ↔
      digraph_incidence_matrix ℝ tail head *ᵥ x = 0 ∧ 0 ≤ x := by
  rw [mem_circulation_cone_iff, isCirculation_iff]
  constructor
  · rintro ⟨hflow, hnonneg⟩
    refine ⟨?_, hnonneg⟩
    ext v
    rw [digraph_incidence_matrix_mulVec_apply]
    exact sub_eq_zero.mpr (hflow v)
  · rintro ⟨hker, hnonneg⟩
    refine ⟨?_, hnonneg⟩
    intro v
    have hv := congrArg (fun y : V → ℝ ↦ y v) hker
    exact sub_eq_zero.mp (by simpa [digraph_incidence_matrix_mulVec_apply] using hv)

/-- Scaling a circulation by a nonnegative scalar stays inside the circulation cone. -/
theorem smul_mem_circulation_cone {tail head : A → V} {x : A → ℝ} {μ : ℝ}
    (hx : x ∈ circulation_cone tail head) (hμ : 0 ≤ μ) :
    μ • x ∈ circulation_cone tail head := by
  -- Rewrite cone membership as kernel plus nonnegativity so scaling is coordinatewise.
  rw [mem_circulation_cone_iff_digraph_incidence_matrix_mulVec_eq_zero] at hx ⊢
  refine ⟨?_, ?_⟩
  · calc
      digraph_incidence_matrix ℝ tail head *ᵥ (μ • x)
          = μ • (digraph_incidence_matrix ℝ tail head *ᵥ x) := by
              rw [Matrix.mulVec_smul]
      _ = μ • 0 := by rw [hx.1]
      _ = 0 := by simp
  · intro a
    simpa [Pi.smul_apply] using mul_nonneg hμ (hx.2 a)

section DecidableVertex

variable [DecidableEq V]

/-- If an arc vector vanishes off `C`, then the outgoing flow at `v` is the sum over the outgoing
arcs of `C`. -/
theorem outgoing_flow_eq_sum_filter_of_eq_zero_off_support {tail : A → V} {C : Finset A}
    {x : A → ℝ} (hsupp : ∀ a, a ∉ C → x a = 0) (v : V) :
    outgoing_flow tail x v = Finset.sum (C.filter (fun a ↦ tail a = v)) x := by
  classical
  -- Restrict the outgoing sum from all arcs to the support set `C`, where all other terms vanish.
  rw [outgoing_flow_eq_sum_outgoing_arcs]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro a ha
    have hav : tail a = v := (Finset.mem_filter.mp ha).2
    simpa [outgoing_arcs, hav]
  · intro a ha_out ha_not_mem
    have ha_not_C : a ∉ C := by
      intro haC
      exact ha_not_mem (by simpa [haC, outgoing_arcs] using ha_out)
    exact hsupp a ha_not_C

/-- If an arc vector vanishes off `C`, then the incoming flow at `v` is the sum over the incoming
arcs of `C`. -/
theorem incoming_flow_eq_sum_filter_of_eq_zero_off_support {head : A → V} {C : Finset A}
    {x : A → ℝ} (hsupp : ∀ a, a ∉ C → x a = 0) (v : V) :
    incoming_flow head x v = Finset.sum (C.filter (fun a ↦ head a = v)) x := by
  classical
  -- The same support restriction works for incoming arcs.
  rw [incoming_flow_eq_sum_incoming_arcs]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro a ha
    have hav : head a = v := (Finset.mem_filter.mp ha).2
    simpa [incoming_arcs, hav]
  · intro a ha_in ha_not_mem
    have ha_not_C : a ∉ C := by
      intro haC
      exact ha_not_mem (by simpa [haC, incoming_arcs] using ha_in)
    exact hsupp a ha_not_C

end DecidableVertex

end FiniteDigraph

/-- At each incident vertex of a simple circuit there is a unique outgoing arc in the chosen arc
set. -/
theorem existsUnique_outgoing_arc_of_isSimpleCircuit {tail head : A → V} {C : Finset A}
    (hC : IsSimpleCircuit tail head C) (v : V) (hv : v ∈ circuit_vertex_set tail head C) :
    ∃! a : A, a ∈ C ∧ tail a = v := by
  classical
  -- Convert the cardinality-one outgoing fiber into an explicit unique witness.
  have hout : outgoing_arc_count tail C v = 1 := (hC.one_in_one_out v hv).2
  rw [outgoing_arc_count] at hout
  rcases Finset.card_eq_one.mp hout with ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · have ha_mem : a ∈ C.filter (fun a ↦ tail a = v) := by rw [ha]; simp
    simpa using ha_mem
  · intro b hb
    have hb' : b ∈ C.filter (fun a ↦ tail a = v) := by
      simpa using hb
    rw [ha] at hb'
    simpa using hb'

/-- At each incident vertex of a simple circuit there is a unique incoming arc in the chosen arc
set. -/
theorem existsUnique_incoming_arc_of_isSimpleCircuit {tail head : A → V} {C : Finset A}
    (hC : IsSimpleCircuit tail head C) (v : V) (hv : v ∈ circuit_vertex_set tail head C) :
    ∃! a : A, a ∈ C ∧ head a = v := by
  classical
  -- The incoming fiber is handled identically.
  have hin : incoming_arc_count head C v = 1 := (hC.one_in_one_out v hv).1
  rw [incoming_arc_count] at hin
  rcases Finset.card_eq_one.mp hin with ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · have ha_mem : a ∈ C.filter (fun a ↦ head a = v) := by rw [ha]; simp
    simpa using ha_mem
  · intro b hb
    have hb' : b ∈ C.filter (fun a ↦ head a = v) := by
      simpa using hb
    rw [ha] at hb'
    simpa using hb'

/-- The characteristic vector of a nonempty simple circuit is nonzero. -/
theorem circuit_characteristic_vector_ne_zero {tail head : A → V} {C : Finset A}
    (hC : IsSimpleCircuit tail head C) :
    circuit_characteristic_vector C ≠ 0 := by
  classical
  -- A nonempty circuit has an arc where the characteristic vector takes the value `1`.
  rcases hC.nonempty with ⟨a, ha⟩
  intro hzero
  have ha_eval := congrArg (fun f : A → ℝ ↦ f a) hzero
  simpa [circuit_characteristic_vector_apply, ha] using ha_eval

section FiniteDigraph

variable [Fintype A]

/-- The characteristic vector of a simple circuit is a nonnegative circulation. -/
theorem circuit_characteristic_vector_mem_circulation_cone {tail head : A → V} {C : Finset A}
    (hC : IsSimpleCircuit tail head C) :
    circuit_characteristic_vector C ∈ circulation_cone tail head := by
  classical
  -- Route correction: prove circulation directly from support restriction and the circuit degree
  -- equalities instead of unfolding the full digraph connectivity package.
  rw [mem_circulation_cone_iff, isCirculation_iff]
  refine ⟨?_, ?_⟩
  · intro v
    -- On the circuit support, both flows count the unique incident arc; off support, both vanish.
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

/-- A circulation supported on a simple circuit is a nonnegative scalar multiple of that circuit's
characteristic vector. -/
theorem supported_circulation_is_scalar_multiple_of_circuit_characteristic_vector
    {tail head : A → V} {C : Finset A} (hC : IsSimpleCircuit tail head C) {x : A → ℝ}
    (hx : x ∈ circulation_cone tail head) (hsupp : ∀ a, a ∉ C → x a = 0) :
    ∃ μ : ℝ, 0 ≤ μ ∧ x = μ • circuit_characteristic_vector C := by
  classical
  -- Unpack the circulation constraints once so every later step can refer to conservation and
  -- nonnegativity directly.
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
        have ha' : a ∈ C ∧ tail a = v.1 := by simpa using ha
        have hEq : a = outArc v := houtArc_unique v a ha'
        simp [hEq, (houtArc_spec v).1]
      · intro ha
        have hEq : a = outArc v := by simpa using ha
        subst hEq
        simpa [(houtArc_spec v).1, (houtArc_spec v).2]
    calc
      outgoing_flow tail x v.1 = Finset.sum (C.filter (fun a ↦ tail a = v.1)) x := by
        rw [outgoing_flow_eq_sum_filter_of_eq_zero_off_support hsupp]
      _ = x (outArc v) := by rw [hfilter]; simp
  have h_incoming_value :
      ∀ v : circuit_vertex_set tail head C, incoming_flow head x v.1 = x (inArc v) := by
    intro v
    -- The incoming sum collapses to the unique incoming arc at `v`.
    have hfilter :
        C.filter (fun a ↦ head a = v.1) = {inArc v} := by
      ext a
      constructor
      · intro ha
        have ha' : a ∈ C ∧ head a = v.1 := by simpa using ha
        have hEq : a = inArc v := hinArc_unique v a ha'
        simp [hEq, (hinArc_spec v).1]
      · intro ha
        have hEq : a = inArc v := by simpa using ha
        subst hEq
        simpa [(hinArc_spec v).1, (hinArc_spec v).2]
    calc
      incoming_flow head x v.1 = Finset.sum (C.filter (fun a ↦ head a = v.1)) x := by
        rw [incoming_flow_eq_sum_filter_of_eq_zero_off_support hsupp]
      _ = x (inArc v) := by rw [hfilter]; simp
  have hstep :
      ∀ {u v : circuit_vertex_set tail head C} {a : A},
        a ∈ C → tail a = u.1 → head a = v.1 → φ u = φ v := by
    intro u v a haC htail hhead
    -- Along one oriented circuit arc, conservation at the head vertex identifies the two values.
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
      _ = x (inArc v) := by rw [hinEq]
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
    -- Walk induction propagates equality through the entire connected circuit support.
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

end FiniteDigraph

/-- The affine-span direction of a nonzero singleton ray hull is one-dimensional. -/
theorem singleton_ray_hull_direction_finrank_eq_one_of_ne_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] {r : E} (hr : r ≠ 0) :
    Module.finrank ℝ (affineSpan ℝ ((PointedCone.hull ℝ ({r} : Set E) : Set E))).direction = 1 := by
  have hzero :
      (0 : E) ∈ (PointedCone.hull ℝ ({r} : Set E) : Set E) := by
    exact (mem_singleton_pointedCone_hull_iff).2 ⟨0, le_rfl, by simp⟩
  have hspan :
      Submodule.span ℝ ((PointedCone.hull ℝ ({r} : Set E) : Set E)) = ℝ ∙ r := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      intro x hx
      rcases (mem_singleton_pointedCone_hull_iff).1 hx with ⟨μ, _, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r)
    · refine (Submodule.span_singleton_le_iff_mem r _).2 ?_
      exact Submodule.subset_span ((mem_singleton_pointedCone_hull_iff).2
        ⟨1, by positivity, by simp⟩)
  -- Because the ray hull contains `0`, its affine direction is the linear span of the hull.
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hzero]
  have himage :
      ((fun x : E ↦ x -ᵥ (0 : E)) '' ((PointedCone.hull ℝ ({r} : Set E) : Set E))) =
        ((PointedCone.hull ℝ ({r} : Set E) : Set E)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      simp
  rw [himage, hspan]
  simpa using finrank_span_singleton (K := ℝ) hr

/-- Exercise 4.13. The characteristic vector of a simple circuit is an extreme ray of the
circulation cone. -/
theorem circuit_characteristic_vector_is_extreme_ray_of_circulation_cone
    [Fintype A]
    (tail head : A → V) {C : Finset A} (hC : IsSimpleCircuit tail head C) :
    IsExtremeRayOfCone (circulation_cone tail head) (circuit_characteristic_vector C) := by
  -- Route correction: build the extreme ray as the singleton pointed-cone hull and prove
  -- extremality from support rigidity on the simple-circuit support.
  rw [isExtremeRayOfCone_iff]
  refine ⟨(PointedCone.hull ℝ ({circuit_characteristic_vector C} : Set (A → ℝ))).convex, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro z hz
      -- Every point on the ray is a nonnegative multiple of a circulation.
      rcases (mem_singleton_pointedCone_hull_iff).1 hz with ⟨μ, hμ, rfl⟩
      exact smul_mem_circulation_cone (circuit_characteristic_vector_mem_circulation_cone hC) hμ
    · intro x hx y hy z hz hzxy
      have hx_cone := hx
      have hy_cone := hy
      rw [mem_openSegment_iff_div] at hzxy
      rcases hzxy with ⟨a, b, ha, hb, hzxy⟩
      rcases (mem_singleton_pointedCone_hull_iff).1 hz with ⟨μ, _, hz_eq⟩
      rw [mem_circulation_cone_iff, isCirculation_iff] at hx hy
      rcases hx with ⟨_, hx_nonneg⟩
      rcases hy with ⟨_, hy_nonneg⟩
      have hsuppx : ∀ e, e ∉ C → x e = 0 := by
        intro e heC
        have hz_zero : z e = 0 := by
          calc
            z e = (μ • circuit_characteristic_vector C) e := by rw [hz_eq]
            _ = 0 := by simp [Pi.smul_apply, circuit_characteristic_vector_apply, heC]
        have hcoord := congrArg (fun f : A → ℝ ↦ f e) hzxy
        have hcoord_zero :
            (a / (a + b)) * x e + (b / (a + b)) * y e = 0 := by
          simpa [Pi.smul_apply, hz_zero] using hcoord
        have hx_term_nonneg : 0 ≤ (a / (a + b)) * x e := by
          exact mul_nonneg (by positivity) (hx_nonneg e)
        have hy_term_nonneg : 0 ≤ (b / (a + b)) * y e := by
          exact mul_nonneg (by positivity) (hy_nonneg e)
        have hterms :
            (a / (a + b)) * x e = 0 ∧ (b / (a + b)) * y e = 0 := by
          exact (add_eq_zero_iff_of_nonneg hx_term_nonneg hy_term_nonneg).mp
            hcoord_zero
        exact (mul_eq_zero.mp hterms.1).resolve_left (by positivity)
      rcases supported_circulation_is_scalar_multiple_of_circuit_characteristic_vector
        hC hx_cone hsuppx with ⟨μx, hμx, rfl⟩
      exact (mem_singleton_pointedCone_hull_iff).2 ⟨μx, hμx, rfl⟩
  · exact singleton_ray_hull_direction_finrank_eq_one_of_ne_zero
      (circuit_characteristic_vector_ne_zero hC)

end Exercise_4_13
