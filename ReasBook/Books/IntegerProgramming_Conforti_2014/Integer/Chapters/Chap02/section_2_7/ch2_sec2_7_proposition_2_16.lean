/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_definition_2_36.MTZ
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_proposition_2_16.Circulation
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_proposition_2_16.Root

namespace AsymmetricTravelingSalesmanProblem

universe w

section Proposition_2_16

variable {A : Type w} [Fintype A]
variable {n : ℕ} (hpos : 0 < n)
variable (P : AsymmetricTravelingSalesmanProblem (Fin n) A) (x : A → ℝ)

/-- Helper for Proposition 2.16: an MTZ-feasible arc vector is a nonnegative circulation. -/
lemma mtzFeasible_memCirculationCone
    {u : Fin n → ℝ} (h_feasible : P.mtzFeasible (textbook_root hpos) x u) :
    x ∈ circulation_cone P.tail P.head := by
  -- The degree equations give flow conservation, and binaryity gives coordinatewise nonnegativity.
  rw [mem_circulation_cone_iff, isCirculation_iff]
  refine ⟨?_, ?_⟩
  · intro v
    rw [mtzFeasible_incoming h_feasible v, mtzFeasible_outgoing h_feasible v]
  · intro a
    rcases mtzFeasible_binary h_feasible a with hxa | hxa <;> linarith

omit [Fintype A] in
/-- Helper for Proposition 2.16: summing a vertex function over the tails of a simple circuit
equals summing it over the heads. -/
lemma sumTail_eq_sumHead_of_isSimpleCircuit
    {C : Finset A} (hC : IsSimpleCircuit P.tail P.head C) (f : Fin n → ℝ) :
    Finset.sum C (fun a ↦ f (P.tail a)) = Finset.sum C (fun a ↦ f (P.head a)) := by
  classical
  -- Unique outgoing and incoming arcs make the tail and head maps biject onto the circuit vertices.
  have htail_inj : Set.InjOn P.tail (↑C : Set A) := by
    intro a ha b hb hab
    have hva : P.tail a ∈ circuit_vertex_set P.tail P.head C := ⟨a, ha, Or.inl rfl⟩
    rcases existsUnique_outgoingArc_of_isSimpleCircuit hC (P.tail a) hva with ⟨c, hc, huniq⟩
    have ha' : a ∈ C ∧ P.tail a = P.tail a := ⟨ha, rfl⟩
    have hb' : b ∈ C ∧ P.tail b = P.tail a := ⟨hb, hab.symm⟩
    calc
      a = c := huniq a ha'
      _ = b := (huniq b hb').symm
  have hhead_inj : Set.InjOn P.head (↑C : Set A) := by
    intro a ha b hb hab
    have hva : P.head a ∈ circuit_vertex_set P.tail P.head C := ⟨a, ha, Or.inr rfl⟩
    rcases existsUnique_incomingArc_of_isSimpleCircuit hC (P.head a) hva with ⟨c, hc, huniq⟩
    have ha' : a ∈ C ∧ P.head a = P.head a := ⟨ha, rfl⟩
    have hb' : b ∈ C ∧ P.head b = P.head a := ⟨hb, hab.symm⟩
    calc
      a = c := huniq a ha'
      _ = b := (huniq b hb').symm
  have htail_image : C.image P.tail = circuit_vertices P.tail P.head C := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨a, ha, rfl⟩
      exact (mem_circuit_vertices_iff P.tail P.head C (P.tail a)).2 ⟨a, ha, Or.inl rfl⟩
    · intro hv
      have hv' : v ∈ circuit_vertex_set P.tail P.head C :=
        (mem_circuit_vertices_iff P.tail P.head C v).1 hv
      rcases existsUnique_outgoingArc_of_isSimpleCircuit hC v hv' with ⟨a, ha, _⟩
      exact Finset.mem_image.mpr ⟨a, ha.1, ha.2⟩
  have hhead_image : C.image P.head = circuit_vertices P.tail P.head C := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨a, ha, rfl⟩
      exact (mem_circuit_vertices_iff P.tail P.head C (P.head a)).2 ⟨a, ha, Or.inr rfl⟩
    · intro hv
      have hv' : v ∈ circuit_vertex_set P.tail P.head C :=
        (mem_circuit_vertices_iff P.tail P.head C v).1 hv
      rcases existsUnique_incomingArc_of_isSimpleCircuit hC v hv' with ⟨a, ha, _⟩
      exact Finset.mem_image.mpr ⟨a, ha.1, ha.2⟩
  calc
    Finset.sum C (fun a ↦ f (P.tail a)) = Finset.sum (C.image P.tail) f := by
      symm
      exact Finset.sum_image htail_inj
    _ = Finset.sum (circuit_vertices P.tail P.head C) f := by
      rw [htail_image]
    _ = Finset.sum (C.image P.head) f := by
      rw [← hhead_image]
    _ = Finset.sum C (fun a ↦ f (P.head a)) := by
      exact Finset.sum_image hhead_inj

/-- Helper for Proposition 2.16: an MTZ-supported simple circuit cannot avoid the distinguished
root vertex `textbook_root hpos`. -/
lemma not_rootFree_of_mtzSupportedSimpleCircuit
    {u : Fin n → ℝ} {C : Finset A}
    (h_feasible : P.mtzFeasible (textbook_root hpos) x u)
    (hC : IsSimpleCircuit P.tail P.head C)
    (hroot : textbook_root hpos ∉ circuit_vertex_set P.tail P.head C)
    (hx_one : ∀ a ∈ C, x a = 1) : False := by
  classical
  -- Sum the MTZ inequalities around the circuit and cancel the potential terms.
  have hsum_le :
      Finset.sum C (fun a ↦ u (P.tail a) - u (P.head a) + 1) ≤
        Finset.sum C (fun a ↦ (n : ℝ) * (1 - x a)) := by
    refine Finset.sum_le_sum ?_
    intro a ha
    have htail_ne : P.tail a ≠ textbook_root hpos := by
      intro htail
      exact hroot ⟨a, ha, Or.inl htail⟩
    have hhead_ne : P.head a ≠ textbook_root hpos := by
      intro hhead
      exact hroot ⟨a, ha, Or.inr hhead⟩
    simpa [Fintype.card_fin] using mtzFeasible_order h_feasible a htail_ne hhead_ne
  have hsum_rhs :
      Finset.sum C (fun a ↦ (n : ℝ) * (1 - x a)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro a ha
    rw [hx_one a ha]
    ring
  have hsum_lhs :
      Finset.sum C (fun a ↦ u (P.tail a) - u (P.head a) + 1) = (C.card : ℝ) := by
    calc
      Finset.sum C (fun a ↦ u (P.tail a) - u (P.head a) + 1)
          = Finset.sum C (fun a ↦ u (P.tail a) - u (P.head a)) +
              Finset.sum C (fun _ ↦ (1 : ℝ)) := by
              rw [Finset.sum_add_distrib]
      _ = (Finset.sum C (fun a ↦ u (P.tail a)) - Finset.sum C (fun a ↦ u (P.head a))) +
            C.card := by
              rw [Finset.sum_sub_distrib]
              simp
      _ = (C.card : ℝ) := by
              rw [sumTail_eq_sumHead_of_isSimpleCircuit P hC u]
              ring
  have hcard_pos : 0 < (C.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hC.nonempty
  have hcard_nonpos : (C.card : ℝ) ≤ 0 := by
    rw [← hsum_lhs]
    calc
      Finset.sum C (fun a ↦ u (P.tail a) - u (P.head a) + 1)
          ≤ Finset.sum C (fun a ↦ (n : ℝ) * (1 - x a)) := hsum_le
      _ = 0 := hsum_rhs
  linarith

/-- Helper for Proposition 2.16: after subtracting a root-containing circuit characteristic
vector, the residual flow has zero incoming and outgoing root flow. -/
lemma residualRootFlows_eq_zero
    {u : Fin n → ℝ} {C : Finset A}
    (h_feasible : P.mtzFeasible (textbook_root hpos) x u)
    (hC : IsSimpleCircuit P.tail P.head C)
    (hroot : textbook_root hpos ∈ circuit_vertex_set P.tail P.head C) :
    outgoing_flow P.tail (x - circuit_characteristic_vector C) (textbook_root hpos) = 0 ∧
      incoming_flow P.head (x - circuit_characteristic_vector C) (textbook_root hpos) = 0 := by
  classical
  -- Compute the circuit contribution at the root, then subtract it from the unit degree equations.
  have hsupp : ∀ a, a ∉ C → circuit_characteristic_vector C a = 0 := by
    intro a ha
    simp [circuit_characteristic_vector_apply, ha]
  have hsubset_out :
      C.filter (fun a ↦ P.tail a = textbook_root hpos) ⊆ C := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hsubset_in :
      C.filter (fun a ↦ P.head a = textbook_root hpos) ⊆ C := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hout_sum :
      Finset.sum (C.filter (fun a ↦ P.tail a = textbook_root hpos))
          (circuit_characteristic_vector C) =
        ((C.filter (fun a ↦ P.tail a = textbook_root hpos)).card : ℝ) := by
    simp [Finset.inter_eq_left.mpr hsubset_out, circuit_characteristic_vector_apply]
  have hin_sum :
      Finset.sum (C.filter (fun a ↦ P.head a = textbook_root hpos))
          (circuit_characteristic_vector C) =
        ((C.filter (fun a ↦ P.head a = textbook_root hpos)).card : ℝ) := by
    simp [Finset.inter_eq_left.mpr hsubset_in, circuit_characteristic_vector_apply]
  have hout_char :
      outgoing_flow P.tail (circuit_characteristic_vector C) (textbook_root hpos) = 1 := by
    rcases existsUnique_outgoingArc_of_isSimpleCircuit hC (textbook_root hpos) hroot with
      ⟨a, ha, huniq⟩
    have hfilter :
        C.filter (fun b ↦ P.tail b = textbook_root hpos) = {a} := by
      ext b
      constructor
      · intro hb
        have hb' : b ∈ C ∧ P.tail b = textbook_root hpos := by
          simpa using hb
        have : b = a := huniq b hb'
        simp [this]
      · intro hb
        have : b = a := by simpa using hb
        subst this
        simpa [ha.2] using ha.1
    rw [outgoingFlow_eq_sum_filter_of_eq_zero_offSupport hsupp, hfilter]
    simp [circuit_characteristic_vector_apply, ha.1]
  have hin_char :
      incoming_flow P.head (circuit_characteristic_vector C) (textbook_root hpos) = 1 := by
    rcases existsUnique_incomingArc_of_isSimpleCircuit hC (textbook_root hpos) hroot with
      ⟨a, ha, huniq⟩
    have hfilter :
        C.filter (fun b ↦ P.head b = textbook_root hpos) = {a} := by
      ext b
      constructor
      · intro hb
        have hb' : b ∈ C ∧ P.head b = textbook_root hpos := by
          simpa using hb
        have : b = a := huniq b hb'
        simp [this]
      · intro hb
        have : b = a := by simpa using hb
        subst this
        simpa [ha.2] using ha.1
    rw [incomingFlow_eq_sum_filter_of_eq_zero_offSupport hsupp, hfilter]
    simp [circuit_characteristic_vector_apply, ha.1]
  constructor
  · calc
      outgoing_flow P.tail (x - circuit_characteristic_vector C) (textbook_root hpos)
          = outgoing_flow P.tail x (textbook_root hpos) -
              outgoing_flow P.tail (circuit_characteristic_vector C) (textbook_root hpos) := by
                simp [outgoing_flow, Finset.sum_sub_distrib]
      _ = 1 - 1 := by
            rw [mtzFeasible_outgoing h_feasible (textbook_root hpos), hout_char]
      _ = 0 := by ring
  · calc
      incoming_flow P.head (x - circuit_characteristic_vector C) (textbook_root hpos)
          = incoming_flow P.head x (textbook_root hpos) -
              incoming_flow P.head (circuit_characteristic_vector C) (textbook_root hpos) := by
                simp [incoming_flow, Finset.sum_sub_distrib]
      _ = 1 - 1 := by
            rw [mtzFeasible_incoming h_feasible (textbook_root hpos), hin_char]
      _ = 0 := by ring

/-- Helper for Proposition 2.16: if `x` equals a circuit characteristic vector and has unit
outgoing flow at `v`, then the circuit must visit `v`. -/
lemma memCircuitVertexSet_of_characteristicVector_outgoingEqOne
    {C : Finset A} {v : Fin n}
    (hx : x = circuit_characteristic_vector C)
    (hout : outgoing_flow P.tail x v = 1) :
    v ∈ circuit_vertex_set P.tail P.head C := by
  classical
  -- If `v` were absent from the circuit, the characteristic vector would contribute no outgoing
  -- root flow there, contradicting the unit degree equation.
  subst hx
  by_contra hv
  have hsupp : ∀ a, a ∉ C → circuit_characteristic_vector C a = 0 := by
    intro a ha
    simp [circuit_characteristic_vector_apply, ha]
  have hfilter_empty : C.filter (fun a ↦ P.tail a = v) = ∅ := by
    ext a
    constructor
    · intro ha
      exact False.elim <| hv ⟨a, (Finset.mem_filter.mp ha).1, Or.inl (Finset.mem_filter.mp ha).2⟩
    · intro ha
      cases ha
  have hout_zero : outgoing_flow P.tail (circuit_characteristic_vector C) v = 0 := by
    rw [outgoingFlow_eq_sum_filter_of_eq_zero_offSupport hsupp, hfilter_empty]
    simp
  linarith

/-- Companion API for Proposition 2.16: a direct
`P.mtzFeasible (textbook_root hpos) x u` witness forces `x` to be the characteristic vector of a
Hamiltonian tour in `P`. -/
theorem existsIsHamiltonianTour_ofMtzFeasible
    {u : Fin n → ℝ} (h_feasible : P.mtzFeasible (textbook_root hpos) x u) :
    ∃ C : Finset A, P.IsHamiltonianTour C ∧ x = circuit_characteristic_vector C := by
  classical
  -- First convert the MTZ witness into the generic circulation data needed for circuit extraction.
  have hx_mem : x ∈ circulation_cone P.tail P.head :=
    mtzFeasible_memCirculationCone hpos P x h_feasible
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    have hout_root : outgoing_flow P.tail x (textbook_root hpos) = 1 :=
      mtzFeasible_outgoing h_feasible (textbook_root hpos)
    have hout_zero : outgoing_flow P.tail x (textbook_root hpos) = 0 := by
      simp [hx_zero, outgoing_flow]
    linarith
  rcases existsSimpleCircuitSubsetPositiveSupport hx_mem hx_ne with ⟨C, hC, hposC⟩
  have hx_one_on_C : ∀ a ∈ C, x a = 1 := by
    intro a ha
    rcases mtzFeasible_binary h_feasible a with hxa | hxa
    · exfalso
      have hpos : 0 < x a := hposC a ha
      rw [hxa] at hpos
      linarith
    · exact hxa
  have hrootC : textbook_root hpos ∈ circuit_vertex_set P.tail P.head C := by
    by_contra hrootC
    exact not_rootFree_of_mtzSupportedSimpleCircuit hpos P x h_feasible hC hrootC hx_one_on_C
  have hx_minus_mem :
      x - circuit_characteristic_vector C ∈ circulation_cone P.tail P.head := by
    have hx_circ : IsCirculation P.tail P.head x :=
      (mem_circulation_cone_iff P.tail P.head x).1 hx_mem
    have hC_circ : IsCirculation P.tail P.head (circuit_characteristic_vector C) :=
      (mem_circulation_cone_iff P.tail P.head (circuit_characteristic_vector C)).1
        (circuitCharacteristicVector_mem_circulationCone hC)
    -- Removing the extracted circuit preserves both conservation and nonnegativity.
    rw [mem_circulation_cone_iff, isCirculation_iff]
    refine ⟨?_, ?_⟩
    · intro v
      calc
        incoming_flow P.head (x - circuit_characteristic_vector C) v
            = incoming_flow P.head x v -
                incoming_flow P.head (circuit_characteristic_vector C) v := by
                  simp [incoming_flow, Finset.sum_sub_distrib]
        _ = outgoing_flow P.tail x v -
              outgoing_flow P.tail (circuit_characteristic_vector C) v := by
                rw [hx_circ.flow_conservation v, hC_circ.flow_conservation v]
        _ = outgoing_flow P.tail (x - circuit_characteristic_vector C) v := by
              simp [outgoing_flow, Finset.sum_sub_distrib]
    · intro a
      by_cases ha : a ∈ C
      · have hxa : x a = 1 := hx_one_on_C a ha
        simp [circuit_characteristic_vector_apply, ha, hxa]
      · simpa [circuit_characteristic_vector_apply, ha] using hx_circ.nonneg a
  have hx_minus_zero : x - circuit_characteristic_vector C = 0 := by
    by_contra hx_minus_ne
    have hx_minus_circ : IsCirculation P.tail P.head (x - circuit_characteristic_vector C) :=
      (mem_circulation_cone_iff P.tail P.head (x - circuit_characteristic_vector C)).1 hx_minus_mem
    rcases existsSimpleCircuitSubsetPositiveSupport hx_minus_mem hx_minus_ne with ⟨D, hD, hposD⟩
    have hrootD :
        textbook_root hpos ∉ circuit_vertex_set P.tail P.head D := by
      intro hrootD
      rcases existsUnique_outgoingArc_of_isSimpleCircuit hD (textbook_root hpos) hrootD with
        ⟨a, ha, _⟩
      have hsum_ge :
          (x - circuit_characteristic_vector C) a ≤
            outgoing_flow P.tail (x - circuit_characteristic_vector C) (textbook_root hpos) := by
        unfold outgoing_flow
        exact Finset.single_le_sum
          (fun b _ ↦ hx_minus_circ.nonneg b)
          (by simp [ha.2])
      have hroot_zero :
          outgoing_flow P.tail (x - circuit_characteristic_vector C) (textbook_root hpos) = 0 :=
        (residualRootFlows_eq_zero hpos P x h_feasible hC hrootC).1
      have hroot_pos :
          0 < outgoing_flow P.tail (x - circuit_characteristic_vector C) (textbook_root hpos) :=
        lt_of_lt_of_le (hposD a ha.1) hsum_ge
      linarith
    have hx_one_on_D : ∀ a ∈ D, x a = 1 := by
      intro a ha
      have ha_not_C : a ∉ C := by
        intro haC
        have hxa : x a = 1 := hx_one_on_C a haC
        have : (x - circuit_characteristic_vector C) a = 0 := by
          simp [circuit_characteristic_vector_apply, haC, hxa]
        linarith [hposD a ha, this]
      have hy_eq : (x - circuit_characteristic_vector C) a = x a := by
        simp [circuit_characteristic_vector_apply, ha_not_C]
      rcases mtzFeasible_binary h_feasible a with hxa | hxa
      · rw [hxa] at hy_eq
        linarith [hposD a ha, hy_eq]
      · exact hxa
    exact not_rootFree_of_mtzSupportedSimpleCircuit hpos P x h_feasible hD hrootD hx_one_on_D
  have hx_eq_C : x = circuit_characteristic_vector C := sub_eq_zero.mp hx_minus_zero
  refine ⟨C, P.ofIsSimpleCircuit hC ?_, hx_eq_C⟩
  intro v
  -- The original unit outgoing equations force every vertex to lie on the extracted circuit.
  exact memCircuitVertexSet_of_characteristicVector_outgoingEqOne
    P x
    hx_eq_C
    (mtzFeasible_outgoing h_feasible v)

/-- Proposition 2.16 (Correctness of the MTZ subtour-elimination constraints): if `x` admits a
textbook MTZ witness for the distinguished root `textbook_root hpos`, then `x` is the
characteristic vector of a Hamiltonian tour in `P`. -/
theorem existsIsHamiltonianTour_ofTextbookMtzFeasible
    (h_feasible : ∃ u : Fin n → ℝ, P.mtzFeasible (textbook_root hpos) x u) :
    ∃ C : Finset A, P.IsHamiltonianTour C ∧ x = circuit_characteristic_vector C := by
  rcases h_feasible with ⟨u, hu⟩
  exact existsIsHamiltonianTour_ofMtzFeasible hpos P x hu

/-- The unpacked MTZ hypotheses of Proposition 2.16 imply the canonical
`P.mtzFeasible (textbook_root hpos) x u` condition. -/
theorem textbookMtzFeasible_ofBinaryMtz
    {u : Fin n → ℝ}
    (h_binary : ∀ a : A, x a = 0 ∨ x a = 1)
    (h_outgoing : ∀ v : Fin n, outgoing_flow P.tail x v = 1)
    (h_incoming : ∀ v : Fin n, incoming_flow P.head x v = 1)
    (h_mtz :
      ∀ a : A, P.tail a ≠ textbook_root hpos → P.head a ≠ textbook_root hpos →
        u (P.tail a) - u (P.head a) + 1 ≤ (n : ℝ) * (1 - x a)) :
    P.mtzFeasible (textbook_root hpos) x u := by
  rw [mtzFeasible_iff]
  refine ⟨h_outgoing, h_incoming, ?_, h_binary⟩
  simpa [Fintype.card_fin] using h_mtz

/-- The unpacked MTZ hypotheses of Proposition 2.16 force `x` to be the characteristic vector of
a Hamiltonian tour in `P`. -/
theorem existsIsHamiltonianTour_ofBinaryMtz
    (h_binary : ∀ a : A, x a = 0 ∨ x a = 1)
    (h_outgoing : ∀ v : Fin n, outgoing_flow P.tail x v = 1)
    (h_incoming : ∀ v : Fin n, incoming_flow P.head x v = 1)
    (h_mtz :
      ∃ u : Fin n → ℝ,
        ∀ a : A, P.tail a ≠ textbook_root hpos → P.head a ≠ textbook_root hpos →
          u (P.tail a) - u (P.head a) + 1 ≤ (n : ℝ) * (1 - x a)) :
    ∃ C : Finset A, P.IsHamiltonianTour C ∧ x = circuit_characteristic_vector C := by
  rcases h_mtz with ⟨u, hu⟩
  have h_feasible : P.mtzFeasible (textbook_root hpos) x u :=
    textbookMtzFeasible_ofBinaryMtz hpos P x h_binary h_outgoing h_incoming hu
  exact existsIsHamiltonianTour_ofMtzFeasible hpos P x h_feasible

/-- A feasible-set reformulation of Proposition 2.16 through the canonical owner
`P.mtzFeasible (textbook_root hpos) x u`. -/
theorem existsMemFeasibleSet_ofMtzFeasible
    {u : Fin n → ℝ} (h_feasible : P.mtzFeasible (textbook_root hpos) x u) :
    ∃ C : Finset A, C ∈ P.feasibleSet ∧ x = circuit_characteristic_vector C := by
  rcases existsIsHamiltonianTour_ofMtzFeasible hpos P x h_feasible with ⟨C, hC, rfl⟩
  exact ⟨C, (P.mem_feasibleSet_iff).2 hC, rfl⟩

/-- A feasible-set reformulation of Proposition 2.16 for an existential MTZ witness. -/
theorem existsMemFeasibleSet_ofTextbookMtzFeasible
    (h_feasible : ∃ u : Fin n → ℝ, P.mtzFeasible (textbook_root hpos) x u) :
    ∃ C : Finset A, C ∈ P.feasibleSet ∧ x = circuit_characteristic_vector C := by
  rcases h_feasible with ⟨u, hu⟩
  exact existsMemFeasibleSet_ofMtzFeasible hpos P x hu

/-- A feasible-set reformulation of `existsIsHamiltonianTour_ofBinaryMtz`. -/
theorem existsMemFeasibleSet_ofBinaryMtz
    (h_binary : ∀ a : A, x a = 0 ∨ x a = 1)
    (h_outgoing : ∀ v : Fin n, outgoing_flow P.tail x v = 1)
    (h_incoming : ∀ v : Fin n, incoming_flow P.head x v = 1)
    (h_mtz :
      ∃ u : Fin n → ℝ,
        ∀ a : A, P.tail a ≠ textbook_root hpos → P.head a ≠ textbook_root hpos →
          u (P.tail a) - u (P.head a) + 1 ≤ (n : ℝ) * (1 - x a)) :
    ∃ C : Finset A, C ∈ P.feasibleSet ∧ x = circuit_characteristic_vector C := by
  rcases h_mtz with ⟨u, hu⟩
  have h_feasible : P.mtzFeasible (textbook_root hpos) x u :=
    textbookMtzFeasible_ofBinaryMtz hpos P x h_binary h_outgoing h_incoming hu
  exact existsMemFeasibleSet_ofMtzFeasible hpos P x h_feasible

end Proposition_2_16

end AsymmetricTravelingSalesmanProblem
