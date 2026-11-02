import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Circulant
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_2_proposition_2_6.StableSetPolytope
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1

open scoped BigOperators
open SimpleGraph

-- Domain sampling note: this exercise reuses the shared Chapter 3 facet owner `IsFacetOf`
-- together with the extracted stable-set-polytope owner API for finite graphs.

section Exercise_7_2

variable {V : Type}
variable (G : SimpleGraph V)

private noncomputable instance : DecidableEq V := Classical.decEq V

/-- The adjacency relation underlying the wheel graph `W₅`. -/
private def fiveWheelAdj : Option (Fin 5) → Option (Fin 5) → Prop
  | some i, some j => (cycleGraph 5).Adj i j
  | none, some _ => True
  | some _, none => True
  | none, none => False

/-- The wheel adjacency relation is symmetric. -/
private lemma fiveWheelAdj_symm : Symmetric fiveWheelAdj := by
  rintro (_ | i) (_ | j)
  · intro h
    cases h
  · intro _
    trivial
  · intro _
    trivial
  · intro h
    exact h.symm

/-- The wheel adjacency relation has no loops. -/
private lemma fiveWheelAdj_loopless : Std.Irrefl fiveWheelAdj := by
  refine ⟨fun v ↦ ?_⟩
  cases v <;> simp [fiveWheelAdj]

/-- The wheel graph `W₅`, obtained from `C₅` by adjoining the hub `none` adjacent to every cycle
vertex `some j`. -/
def fiveWheelGraph : SimpleGraph (Option (Fin 5)) where
  Adj := fiveWheelAdj
  symm := fiveWheelAdj_symm
  loopless := fiveWheelAdj_loopless

/-- On the cycle vertices, `fiveWheelGraph` agrees with `cycleGraph 5`. -/
theorem fiveWheelGraph_adj_some_some {i j : Fin 5} :
    fiveWheelGraph.Adj (some i) (some j) ↔ (cycleGraph 5).Adj i j :=
  Iff.rfl

/-- The hub vertex `none` is adjacent to every cycle vertex in `fiveWheelGraph`. -/
theorem fiveWheelGraph_adj_hub (j : Fin 5) :
    fiveWheelGraph.Adj none (some j) := by
  change True
  trivial

/-- Adjacency in `fiveWheelGraph` is decidable. -/
instance instDecidableRelFiveWheelGraphAdj : DecidableRel fiveWheelGraph.Adj :=
  fun u v ↦
    match u, v with
    | some i, some j => inferInstanceAs (Decidable ((cycleGraph 5).Adj i j))
    | none, some _ => inferInstanceAs (Decidable True)
    | some _, none => inferInstanceAs (Decidable True)
    | none, none => inferInstanceAs (Decidable False)

/-- Helper for Exercise 7.2: the empty stable set has zero indicator vector. -/
private lemma stableSetIndicatorEmpty :
    stableSetIndicator (∅ : Finset V) = 0 := by
  classical
  -- The empty stable set contributes no active coordinates.
  ext v
  simp [stableSetIndicator]

/-- Helper for Exercise 7.2: singleton stable sets give coordinate unit vectors. -/
private lemma stableSetIndicatorSingleton [DecidableEq V] (v : V) :
    stableSetIndicator ({v} : Finset V) = Pi.single v 1 := by
  classical
  -- A singleton indicator is exactly the standard basis vector at that vertex.
  ext u
  by_cases huv : u = v
  · subst huv
    simp [stableSetIndicator]
  · simp [stableSetIndicator, huv]

/-- Helper for Exercise 7.2: two-point indicators split as a sum of coordinate unit vectors. -/
private lemma stableSetIndicatorPairOfNe [DecidableEq V] {v w : V} (hvw : v ≠ w) :
    stableSetIndicator ({v, w} : Finset V) = Pi.single v 1 + Pi.single w 1 := by
  classical
  -- The two support coordinates contribute `1`, and every other coordinate contributes `0`.
  ext u
  by_cases huv : u = v
  · subst huv
    simp [stableSetIndicator, hvw]
  · by_cases huw : u = w
    · subst huw
      simp [stableSetIndicator, huv]
    · simp [stableSetIndicator, huv, huw]

/-- Helper for Exercise 7.2: singleton coordinate points belong to the stable-set polytope. -/
private lemma singlePoint_memStableSetPolytope (v : V) :
    (Pi.single v (1 : ℝ) : V → ℝ) ∈ STAB(G) := by
  -- Rewrite the singleton indicator into the corresponding sparse coordinate vector.
  simpa [stableSetIndicatorSingleton] using
    (stableSetIndicator_mem_stableSetPolytope G
      (by simp : G.IsIndepSet ({v} : Finset V)))

/-- Helper for Exercise 7.2: stable pairs give sparse two-coordinate points of the stable-set
polytope. -/
private lemma pairPoint_memStableSetPolytope {u v : V} (huv : u ≠ v)
    (huv_indep : G.IsIndepSet ({u, v} : Finset V)) :
    ((Pi.single u (1 : ℝ) + Pi.single v 1 : V → ℝ)) ∈ STAB(G) := by
  -- Rewrite the pair indicator into the exact `Pi.single` normal form used in the facet proofs.
  simpa [stableSetIndicatorPairOfNe huv] using
    (stableSetIndicator_mem_stableSetPolytope G huv_indep)

/-- Helper for Exercise 7.2: `0` together with the coordinate unit vectors is affinely
independent in `ℝ^V`. -/
private lemma affineIndependentNoneOrSingle :
    AffineIndependent ℝ
      (fun o : Option V ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v (1 : ℝ))) := by
  classical
  let p : Option V → V → ℝ :=
    fun o ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v (1 : ℝ))
  let e : {o : Option V // o ≠ none} → V := fun o ↦
    match o with
    | ⟨none, hnone⟩ => False.elim (hnone rfl)
    | ⟨some v, _⟩ => v
  have he_injective : Function.Injective e := by
    intro a b hab
    rcases a with ⟨oa, hoa⟩
    rcases b with ⟨ob, hob⟩
    cases oa with
    | none => exact False.elim (hoa rfl)
    | some va =>
        cases ob with
        | none => exact False.elim (hob rfl)
        | some vb =>
            simp only [ne_eq] at hab
            subst hab
            rfl
  -- Affine independence reduces to linear independence of the standard basis.
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p none]
  have hvsub :
      (fun i : {o : Option V // o ≠ none} ↦ (p i -ᵥ p none : V → ℝ)) =
        fun i : {o : Option V // o ≠ none} ↦ Pi.single (e i) (1 : ℝ) := by
    funext i
    rcases i with ⟨o, ho⟩
    cases o with
    | none => exact False.elim (ho rfl)
    | some v =>
        simp [p, e, vsub_eq_sub]
  rw [hvsub]
  exact (Pi.linearIndependent_single_one V ℝ).comp e he_injective

/-- Helper for Exercise 7.2: the stable-set polytope spans the whole ambient function space. -/
private theorem stableSetPolytopeAffineSpanEqTop [Finite V] :
    affineSpan ℝ STAB(G) = ⊤ := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  let p : Option V → V → ℝ :=
    fun o ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v (1 : ℝ))
  have hp : Set.range p ⊆ STAB(G) := by
    intro x hx
    rcases hx with ⟨o, rfl⟩
    cases o with
    | none =>
        -- The origin comes from the empty stable set.
        have h0 : stableSetIndicator (∅ : Finset V) ∈ STAB(G) :=
          stableSetIndicator_mem_stableSetPolytope G
            (by simp : G.IsIndepSet (∅ : Finset V))
        simpa [p, stableSetIndicatorEmpty] using h0
    | some v =>
        -- Each singleton indicator is also a stable-set vertex.
        have hv : stableSetIndicator ({v} : Finset V) ∈ STAB(G) :=
          stableSetIndicator_mem_stableSetPolytope G
            (by simp : G.IsIndepSet ({v} : Finset V))
        simpa [p, stableSetIndicatorSingleton] using hv
  have hp_affine : AffineIndependent ℝ p := by
    -- The chosen family is exactly the origin plus the coordinate unit vectors.
    simpa [p] using (affineIndependentNoneOrSingle (V := V))
  have htop : affineSpan ℝ (Set.range p) = ⊤ := by
    -- The family has `|V| + 1` points in an ambient space of dimension `|V|`.
    have hcard : Fintype.card (Option V) = Fintype.card V + 1 := by
      simp
    exact hp_affine.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      rw [Module.finrank_fintype_fun_eq_card]
      exact hcard)
  have hmono : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ STAB(G) :=
    affineSpan_mono ℝ hp
  -- A superset of a spanning affine family has full affine span.
  exact top_unique (by simpa [htop] using hmono)

/-- Helper for Exercise 7.2: a nonzero linear functional on `ℝ^V` has a codimension-one kernel. -/
private lemma finrankKerEqCardSubOne [Fintype V] {L : (V → ℝ) →ₗ[ℝ] ℝ}
    (hL : L ≠ 0) :
    Module.finrank ℝ (LinearMap.ker L) = Fintype.card V - 1 := by
  let f : Module.Dual ℝ (V → ℝ) := L
  have hf : f ≠ 0 := by
    simpa [f] using hL
  have hker_add_one :
      Module.finrank ℝ (LinearMap.ker L) + 1 = Fintype.card V := by
    simpa [f, Module.finrank_fintype_fun_eq_card] using f.finrank_ker_add_one_of_ne_zero hf
  exact Nat.eq_sub_of_add_eq hker_add_one

/-- Helper for Exercise 7.2: a tight valid equality set is the exposed set of its defining linear
functional. -/
private lemma eqSetEqToExposedOfMem [Finite V]
    {P : Set (V → ℝ)} {L : (V → ℝ) →ₗ[ℝ] ℝ} {δ : ℝ} {x₀ : V → ℝ}
    (hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ P → L x ≤ δ)
    (hx₀ : x₀ ∈ P) (hx₀_eq : L x₀ = δ) :
    {x : V → ℝ | x ∈ P ∧ L x = δ} =
      (⟨L, L.continuous_of_finiteDimensional⟩ : (V → ℝ) →L[ℝ] ℝ).toExposed P := by
  let _ : Fintype V := Fintype.ofFinite V
  ext x
  constructor
  · rintro ⟨hxP, hxEq⟩
    refine ⟨hxP, fun y hyP ↦ ?_⟩
    calc
      L y ≤ δ := hvalid hyP
      _ = L x := hxEq.symm
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hx₀_le : L x₀ ≤ L x := hx.2 x₀ hx₀
    have hx_le : L x ≤ L x₀ := by
      simpa [hx₀_eq] using hvalid hx.1
    exact (le_antisymm hx_le hx₀_le).trans hx₀_eq

/-- Helper for Exercise 7.2: the dot-product coefficient vector defines the corresponding linear
functional. -/
private def dotProductLinearMap [Fintype V] (c : V → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ v, c v • LinearMap.proj v

/-- Helper for Exercise 7.2: `dotProductLinearMap c` evaluates as `c ⬝ᵥ x`. -/
private lemma dotProductLinearMap_apply [Fintype V] (c x : V → ℝ) :
    dotProductLinearMap c x = c ⬝ᵥ x := by
  -- The linear map was defined coordinatewise as the dot product with `c`.
  simp [dotProductLinearMap, dotProduct]

/-- Helper for Exercise 7.2: every nonempty tight equality set of a valid inequality is exposed. -/
private lemma equalitySetIsExposed [Fintype V]
    {P : Set (V → ℝ)} {c x₀ : V → ℝ} {δ : ℝ}
    (hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ δ)
    (hx₀ : x₀ ∈ P) (hx₀_eq : c ⬝ᵥ x₀ = δ) :
    IsExposed ℝ P {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ} := by
  have hvalid' : ∀ ⦃x : V → ℝ⦄, x ∈ P → dotProductLinearMap c x ≤ δ := by
    intro x hx
    simpa [dotProductLinearMap_apply] using hvalid hx
  have hEq :
      {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ} =
        {x : V → ℝ | x ∈ P ∧ dotProductLinearMap c x = δ} := by
    -- Rewrite the equality face into the spelling used by the generic exposed-set helper.
    ext x
    simp [dotProductLinearMap_apply]
  -- The equality slice is the exposed set of the dot-product functional.
  rw [hEq, eqSetEqToExposedOfMem (L := dotProductLinearMap c) hvalid' hx₀]
  · exact ContinuousLinearMap.toExposed.isExposed
  · simpa [dotProductLinearMap_apply] using hx₀_eq

/-- Helper for Exercise 7.2: the direction of an equality face lies in the kernel of its defining
linear functional. -/
private lemma equalitySetDirectionLeKer [Fintype V]
    {P : Set (V → ℝ)} {c x₀ : V → ℝ} {δ : ℝ}
    (hx₀_eq : c ⬝ᵥ x₀ = δ) :
    (affineSpan ℝ {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ}).direction ≤
      LinearMap.ker (dotProductLinearMap c) := by
  let F : Set (V → ℝ) := {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ}
  let H : AffineSubspace ℝ (V → ℝ) :=
    AffineSubspace.mk' x₀ (LinearMap.ker (dotProductLinearMap c))
  have hF_le_H : F ⊆ H := by
    intro x hx
    -- Points in the equality set differ by a kernel vector because the defining functional is
    -- constant on the face.
    change x ∈ H
    rw [AffineSubspace.mem_mk']
    refine LinearMap.mem_ker.2 ?_
    rcases hx with ⟨-, hx_eq⟩
    simp [dotProductLinearMap_apply, vsub_eq_sub, hx_eq, hx₀_eq]
  have h_aff_le : affineSpan ℝ F ≤ H := (affineSpan_le).2 hF_le_H
  -- Passing to directions identifies the ambient affine subspace with the kernel.
  simpa [H] using (AffineSubspace.direction_le h_aff_le :
    (affineSpan ℝ F).direction ≤ H.direction)

/-- Helper for Exercise 7.2: a dot-product inequality that holds on every stable-set vertex holds
on the whole stable-set polytope. -/
private lemma dotProductLeOfMemStableSetPolytope [Fintype V]
    {c : V → ℝ} {δ : ℝ}
    (hvertex : ∀ s : Finset V, G.IsIndepSet s → c ⬝ᵥ stableSetIndicator s ≤ δ)
    {x : V → ℝ} (hx : x ∈ STAB(G)) :
    c ⬝ᵥ x ≤ δ := by
  classical
  let H : Set (V → ℝ) := {y : V → ℝ | c ⬝ᵥ y ≤ δ}
  have hconvex : Convex ℝ H := by
    -- A dot-product inequality cuts out a linear halfspace.
    simpa [H, dotProductLinearMap_apply] using
      convex_halfSpace_le (dotProductLinearMap c).isLinear δ
  have hsubset : convexHull ℝ (stableSetVertices G) ⊆ H := by
    refine convexHull_min ?_ hconvex
    intro y hy
    rw [mem_stableSetVertices_iff] at hy
    rcases hy with ⟨s, hs, rfl⟩
    exact hvertex s hs
  rw [stableSetPolytope_eq_convexHull] at hx
  exact hsubset hx

/-- Helper for Exercise 7.2: summing the coordinates of a stable-set indicator counts its support.
-/
private lemma sum_stableSetIndicator_eq_card [Fintype V] (s : Finset V) :
    (∑ v, stableSetIndicator s v) = s.card := by
  classical
  -- Each active coordinate contributes `1`, and each inactive coordinate contributes `0`.
  simp [stableSetIndicator]

/-- Helper for Exercise 7.2: an edge of `C₅` is exactly a cyclic successor or predecessor pair. -/
private lemma cycleGraph_adj_iff_finRotate_five (i j : Fin 5) :
    (cycleGraph 5).Adj i j ↔ j = finRotate 5 i ∨ i = finRotate 5 j := by
  revert i j
  decide

/-- Helper for Exercise 7.2: `j` and `j+1` are distinct in `Fin 5`. -/
private lemma finRotate_ne_self_five (j : Fin 5) :
    j ≠ finRotate 5 j := by
  revert j
  decide

/-- Helper for Exercise 7.2: `j` and `j+2` are distinct in `Fin 5`. -/
private lemma finRotate_two_ne_self_five (j : Fin 5) :
    j ≠ finRotate 5 (finRotate 5 j) := by
  revert j
  decide

/-- Helper for Exercise 7.2: `j` and `j+3` are distinct in `Fin 5`. -/
private lemma finRotate_three_ne_self_five (j : Fin 5) :
    j ≠ finRotate 5 (finRotate 5 (finRotate 5 j)) := by
  revert j
  decide

/-- Helper for Exercise 7.2: `j+1` and `j+4` are distinct in `Fin 5`. -/
private lemma finRotate_succ_ne_pred_five (j : Fin 5) :
    finRotate 5 j ≠ finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j))) := by
  revert j
  decide

/-- Helper for Exercise 7.2: `j+1` and `j+2` are distinct in `Fin 5`. -/
private lemma finRotate_succ_ne_two_steps_five (j : Fin 5) :
    finRotate 5 j ≠ finRotate 5 (finRotate 5 j) := by
  revert j
  decide

/-- Helper for Exercise 7.2: `j+1` and `j+3` are distinct in `Fin 5`. -/
private lemma finRotate_succ_ne_three_steps_five (j : Fin 5) :
    finRotate 5 j ≠ finRotate 5 (finRotate 5 (finRotate 5 j)) := by
  revert j
  decide

/-- Helper for Exercise 7.2: `j` and `j+4` are distinct in `Fin 5`. -/
private lemma finRotate_four_ne_self_five (j : Fin 5) :
    j ≠ finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j))) := by
  revert j
  decide

/-- Helper for Exercise 7.2: vertices at cyclic distance two in `C₅` form a stable set. -/
private lemma cycleGraph_pair_two_steps_indep (j : Fin 5) :
    (cycleGraph 5).IsIndepSet
      ({j, finRotate 5 (finRotate 5 j)} : Finset (Fin 5)) := by
  revert j
  decide

/-- Helper for Exercise 7.2: vertices at cyclic distance three in `C₅` form a stable set. -/
private lemma cycleGraph_pair_three_steps_indep (j : Fin 5) :
    (cycleGraph 5).IsIndepSet
      ({j, finRotate 5 (finRotate 5 (finRotate 5 j))} : Finset (Fin 5)) := by
  revert j
  decide

/-- Helper for Exercise 7.2: every stable set of `C₅` has cardinality at most `2`. -/
private lemma cycleGraph_indep_card_le_two
    (s : Finset (Fin 5)) (hs : (cycleGraph 5).IsIndepSet s) :
    s.card ≤ 2 := by
  revert hs s
  decide

/-- Helper for Exercise 7.2: the same two-step cycle pairs stay stable in `W₅`. -/
private lemma fiveWheel_pair_two_steps_indep (j : Fin 5) :
    fiveWheelGraph.IsIndepSet
      ({some j, some (finRotate 5 (finRotate 5 j))} : Finset (Option (Fin 5))) := by
  revert j
  decide

/-- Helper for Exercise 7.2: the same three-step cycle pairs stay stable in `W₅`. -/
private lemma fiveWheel_pair_three_steps_indep (j : Fin 5) :
    fiveWheelGraph.IsIndepSet
      ({some j, some (finRotate 5 (finRotate 5 (finRotate 5 j)))} :
        Finset (Option (Fin 5))) := by
  revert j
  decide

/-- Helper for Exercise 7.2: if an independent set of `W₅` avoids the hub, it has at most two
cycle vertices. -/
private lemma fiveWheel_indep_card_without_hub_le_two
    (s : Finset (Option (Fin 5))) (hs : fiveWheelGraph.IsIndepSet s) (hnone : none ∉ s) :
    s.card ≤ 2 := by
  revert hs hnone s
  decide

/-- Helper for Exercise 7.2: the lifted odd-cycle weight vector evaluates to the weighted
coordinate sum `∑ x_(v_j) + 2 x_w`. -/
private lemma dotProductWheelWeights_apply (x : Option (Fin 5) → ℝ) :
    (fun v : Option (Fin 5) ↦ match v with | none => (2 : ℝ) | some _ => 1) ⬝ᵥ x =
      (∑ j : Fin 5, x (some j)) + 2 * x none := by
  -- Split the dot product into the hub coordinate and the five cycle coordinates.
  rw [dotProduct, Fintype.sum_option]
  ring_nf

/-- Helper for Exercise 7.2: the oriented `C₅` edge coefficient vector evaluates to the expected
two-coordinate sum. -/
private lemma dotProductCycleEdge_apply (j : Fin 5) (x : Fin 5 → ℝ) :
    (Pi.single j (1 : ℝ) + Pi.single (finRotate 5 j) 1) ⬝ᵥ x =
      x j + x (finRotate 5 j) := by
  -- Split the sparse dot product into its two singleton contributions.
  rw [add_dotProduct]
  simp

/-- Helper for Exercise 7.2: the lifted edge coefficient vector evaluates to the expected
three-coordinate sum. -/
private lemma dotProductWheelEdge_apply (j : Fin 5) (x : Option (Fin 5) → ℝ) :
    (Pi.single (some j) (1 : ℝ) + Pi.single (some (finRotate 5 j)) 1 + Pi.single none 1) ⬝ᵥ x =
      x (some j) + x (some (finRotate 5 j)) + x none := by
  -- Split the sparse dot product into the two cycle coordinates and the hub coordinate.
  rw [add_dotProduct, add_dotProduct]
  simp [add_assoc]

/-- Helper for Exercise 7.2: subtracting a singleton witness from a pair witness leaves the other
coordinate vector. -/
private lemma pairMinusSingleton_eq_single [DecidableEq V] (a b : V) :
    (((Pi.single a (1 : ℝ) : V → ℝ) + Pi.single b 1) - Pi.single a 1 : V → ℝ) = Pi.single b 1 := by
  -- Compare the two sparse vectors coordinatewise.
  ext u
  by_cases hua : u = a
  · subst hua
    simp [Pi.single_apply]
  · simp [Pi.single_apply, hua]

/-- Helper for Exercise 7.2: subtracting two pair witnesses with one shared coordinate leaves the
difference of the remaining singleton coordinates. -/
private lemma pairMinusPair_eq_single_sub_single [DecidableEq V] (a b c : V) :
    (((Pi.single a (1 : ℝ) : V → ℝ) + Pi.single b 1) - (Pi.single a 1 + Pi.single c 1) : V → ℝ) =
      Pi.single b 1 - Pi.single c 1 := by
  -- Compare the two sparse vectors coordinatewise.
  ext u
  by_cases hua : u = a
  · subst hua
    simp [Pi.single_apply]
  · simp [Pi.single_apply, hua]

/-- Helper for Exercise 7.2: subtracting a pair witness from a singleton witness separates into
the two expected singleton subtractions. -/
private lemma singleMinusPair_eq_single_sub_single_sub_single [DecidableEq V] (a b c : V) :
    ((Pi.single a (1 : ℝ) : V → ℝ) - (Pi.single b 1 + Pi.single c 1) : V → ℝ) =
      Pi.single a 1 - Pi.single b 1 - Pi.single c 1 := by
  -- Compare the two sparse vectors coordinatewise and reassociate the subtraction.
  ext u
  by_cases hua : u = a <;> by_cases hub : u = b <;> by_cases huc : u = c
  all_goals
    simp [Pi.single_apply, hua, hub, huc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 7.2: the hub singleton gives the exact sparse witness used in the lifted
facet proofs. -/
private lemma wheelHubSinglePoint_memStableSetPolytope :
    ((Pi.single none (1 : ℝ) : Option (Fin 5) → ℝ)) ∈ STAB(fiveWheelGraph) := by
  -- Rewrite the hub singleton indicator directly into the required sparse vector.
  have hmem :
      stableSetIndicator ({none} : Finset (Option (Fin 5))) ∈ STAB(fiveWheelGraph) :=
    stableSetIndicator_mem_stableSetPolytope fiveWheelGraph
      (by simp : fiveWheelGraph.IsIndepSet ({none} : Finset (Option (Fin 5))))
  have hrepr :
      stableSetIndicator ({none} : Finset (Option (Fin 5))) =
        (Pi.single none (1 : ℝ) : Option (Fin 5) → ℝ) := by
    ext u
    cases u <;> simp [stableSetIndicator]
  exact hrepr ▸ hmem

/-- Helper for Exercise 7.2: each cycle-vertex singleton of `C₅` gives the exact sparse witness
used in the facet proofs. -/
private lemma cycleSinglePoint_memStableSetPolytope (j : Fin 5) :
    ((Pi.single j (1 : ℝ) : Fin 5 → ℝ)) ∈ STAB(cycleGraph 5) := by
  -- Rewrite the singleton indicator directly into the required sparse vector.
  have hmem :
      stableSetIndicator ({j} : Finset (Fin 5)) ∈ STAB(cycleGraph 5) :=
    stableSetIndicator_mem_stableSetPolytope (cycleGraph 5)
      (by simp : (cycleGraph 5).IsIndepSet ({j} : Finset (Fin 5)))
  have hrepr :
      stableSetIndicator ({j} : Finset (Fin 5)) = (Pi.single j (1 : ℝ) : Fin 5 → ℝ) := by
    ext i
    by_cases hi : i = j
    · subst hi
      simp [stableSetIndicator]
    · simp [stableSetIndicator, hi]
  exact hrepr ▸ hmem

/-- Helper for Exercise 7.2: the two-step stable pairs of `C₅` give the exact sparse witnesses
used in the facet proofs. -/
private lemma cycleTwoStepPairPoint_memStableSetPolytope (j : Fin 5) :
    ((Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 j)) 1 : Fin 5 → ℝ)) ∈
      STAB(cycleGraph 5) := by
  -- Rewrite the stable pair indicator directly into the required sparse-vector normal form.
  have hmem :
      stableSetIndicator ({j, finRotate 5 (finRotate 5 j)} : Finset (Fin 5)) ∈ STAB(cycleGraph 5) :=
    stableSetIndicator_mem_stableSetPolytope (cycleGraph 5) (cycleGraph_pair_two_steps_indep j)
  have hrepr :
      stableSetIndicator ({j, finRotate 5 (finRotate 5 j)} : Finset (Fin 5)) =
        ((Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 j)) 1 : Fin 5 → ℝ)) := by
    ext i
    fin_cases i <;> fin_cases j <;> simp [stableSetIndicator]
  exact hrepr ▸ hmem

/-- Helper for Exercise 7.2: the three-step stable pairs of `C₅` give the exact sparse witnesses
used in the facet proofs. -/
private lemma cycleThreeStepPairPoint_memStableSetPolytope (j : Fin 5) :
    ((Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 (finRotate 5 j))) 1 :
        Fin 5 → ℝ)) ∈
      STAB(cycleGraph 5) := by
  -- Rewrite the stable pair indicator directly into the required sparse-vector normal form.
  have hmem :
      stableSetIndicator ({j, finRotate 5 (finRotate 5 (finRotate 5 j))} : Finset (Fin 5)) ∈
        STAB(cycleGraph 5) :=
    stableSetIndicator_mem_stableSetPolytope (cycleGraph 5) (cycleGraph_pair_three_steps_indep j)
  have hrepr :
      stableSetIndicator ({j, finRotate 5 (finRotate 5 (finRotate 5 j))} : Finset (Fin 5)) =
        ((Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 (finRotate 5 j))) 1 :
            Fin 5 → ℝ)) := by
    ext i
    fin_cases i <;> fin_cases j <;> simp [stableSetIndicator]
  exact hrepr ▸ hmem

/-- Helper for Exercise 7.2: each cycle-vertex singleton of `W₅` gives the exact sparse witness
used in the lifted facet proofs. -/
private lemma wheelSomeSinglePoint_memStableSetPolytope (j : Fin 5) :
    ((Pi.single (some j) (1 : ℝ) : Option (Fin 5) → ℝ)) ∈ STAB(fiveWheelGraph) := by
  -- Rewrite the singleton indicator directly into the required sparse vector.
  have hmem :
      stableSetIndicator ({some j} : Finset (Option (Fin 5))) ∈ STAB(fiveWheelGraph) :=
    stableSetIndicator_mem_stableSetPolytope fiveWheelGraph
      (by simp : fiveWheelGraph.IsIndepSet ({some j} : Finset (Option (Fin 5))))
  have hrepr :
      stableSetIndicator ({some j} : Finset (Option (Fin 5))) =
        (Pi.single (some j) (1 : ℝ) : Option (Fin 5) → ℝ) := by
    ext u
    cases u with
    | none =>
        simp [stableSetIndicator]
    | some i =>
        by_cases hi : i = j
        · subst hi
          simp [stableSetIndicator]
        · simp [stableSetIndicator, hi]
  exact hrepr ▸ hmem

/-- Helper for Exercise 7.2: the two-step cycle pairs of `W₅` give exact sparse witnesses. -/
private lemma wheelTwoStepPairPoint_memStableSetPolytope (j : Fin 5) :
    ((Pi.single (some j) (1 : ℝ) +
        Pi.single (some (finRotate 5 (finRotate 5 j))) 1 : Option (Fin 5) → ℝ)) ∈
      STAB(fiveWheelGraph) := by
  -- Rewrite the stable pair indicator directly into the required sparse-vector normal form.
  have hmem :
      stableSetIndicator
          ({some j, some (finRotate 5 (finRotate 5 j))} : Finset (Option (Fin 5))) ∈
        STAB(fiveWheelGraph) :=
    stableSetIndicator_mem_stableSetPolytope fiveWheelGraph (fiveWheel_pair_two_steps_indep j)
  have hrepr :
      stableSetIndicator
          ({some j, some (finRotate 5 (finRotate 5 j))} : Finset (Option (Fin 5))) =
        ((Pi.single (some j) (1 : ℝ) +
            Pi.single (some (finRotate 5 (finRotate 5 j))) 1 : Option (Fin 5) → ℝ)) := by
    ext u
    cases u with
    | none =>
        simp [stableSetIndicator]
    | some i =>
        fin_cases i <;> fin_cases j <;> simp [stableSetIndicator]
  exact hrepr ▸ hmem

/-- Helper for Exercise 7.2: the three-step cycle pairs of `W₅` give exact sparse witnesses. -/
private lemma wheelThreeStepPairPoint_memStableSetPolytope (j : Fin 5) :
    ((Pi.single (some j) (1 : ℝ) +
        Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1 :
          Option (Fin 5) → ℝ)) ∈
      STAB(fiveWheelGraph) := by
  -- Rewrite the stable pair indicator directly into the required sparse-vector normal form.
  have hmem :
      stableSetIndicator
          ({some j, some (finRotate 5 (finRotate 5 (finRotate 5 j)))} :
            Finset (Option (Fin 5))) ∈
        STAB(fiveWheelGraph) :=
    stableSetIndicator_mem_stableSetPolytope fiveWheelGraph (fiveWheel_pair_three_steps_indep j)
  have hrepr :
      stableSetIndicator
          ({some j, some (finRotate 5 (finRotate 5 (finRotate 5 j)))} :
            Finset (Option (Fin 5))) =
        ((Pi.single (some j) (1 : ℝ) +
            Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1 :
              Option (Fin 5) → ℝ)) := by
    ext u
    cases u with
    | none =>
        simp [stableSetIndicator]
    | some i =>
        fin_cases i <;> fin_cases j <;> simp [stableSetIndicator]
  exact hrepr ▸ hmem

/-- Helper for Exercise 7.2: every vector in the zero-sum hyperplane of `ℝ^5` is an explicit
combination of the four odd-cycle witness differences. -/
private lemma cycleSumZero_decomposition (x : Fin 5 → ℝ)
    (hx : (∑ i : Fin 5, x i) = 0) :
    x =
      x 4 • (Pi.single 4 (1 : ℝ) - Pi.single 0 1) +
        x 3 • (Pi.single 3 (1 : ℝ) - Pi.single 2 1) +
          (-x 2 - x 3) • (Pi.single 1 (1 : ℝ) - Pi.single 2 1) +
            (x 1 + x 2 + x 3) • (Pi.single 1 (1 : ℝ) - Pi.single 0 1) := by
  -- The zero-sum condition determines the remaining coordinate after choosing four generators.
  have hx' : x 0 + (x 1 + (x 2 + (x 3 + x 4))) = 0 := by
    simpa [Fin.sum_univ_succ, Fin.sum_univ_four, add_assoc] using hx
  have hx0 : x 0 = -x 1 - x 2 - x 3 - x 4 := by
    linarith [hx']
  ext i
  fin_cases i <;> simp [hx0] <;> ring

/-- Helper for Exercise 7.2: every vector in the lifted weighted-sum hyperplane of `ℝ^(W₅)` is an
explicit combination of the five lifted odd-cycle witness differences. -/
private lemma wheelWeightedSumZero_decomposition (x : Option (Fin 5) → ℝ)
    (hx : (∑ i : Fin 5, x (some i)) + 2 * x none = 0) :
    x =
      x (some 4) • (Pi.single (some 4) (1 : ℝ) - Pi.single (some 0) 1) +
        x (some 3) • (Pi.single (some 3) (1 : ℝ) - Pi.single (some 2) 1) +
          (-x (some 2) - x (some 3) - x none) •
            (Pi.single (some 1) (1 : ℝ) - Pi.single (some 2) 1) +
            (x (some 1) + x (some 2) + x (some 3) + x none) •
              (Pi.single (some 1) (1 : ℝ) - Pi.single (some 0) 1) +
                x none •
                  (Pi.single none (1 : ℝ) - Pi.single (some 0) 1 - Pi.single (some 2) 1) := by
  -- The weighted-sum relation determines the last cycle coordinate after choosing five generators.
  have hx' :
      x (some 0) + (x (some 1) + (x (some 2) + (x (some 3) + (x (some 4) + 2 * x none)))) = 0 := by
    simpa [Fin.sum_univ_succ, Fin.sum_univ_four, add_assoc] using hx
  have hx0 :
      x (some 0) =
        -x (some 1) - x (some 2) - x (some 3) - x (some 4) - 2 * x none := by
    linarith [hx']
  ext i
  cases i with
  | none =>
      simp
  | some i =>
      fin_cases i <;> simp [hx0] <;> ring

/-- Helper for Exercise 7.2: every vector in the edge-kernel hyperplane of `ℝ^5` is an explicit
combination of the oriented edge witness directions. -/
private lemma cycleEdgeKernelDecomposition (j : Fin 5) (x : Fin 5 → ℝ)
    (hx : x j + x (finRotate 5 j) = 0) :
    x =
      x (finRotate 5 j) • (Pi.single (finRotate 5 j) (1 : ℝ) - Pi.single j 1) +
        x (finRotate 5 (finRotate 5 j)) •
          Pi.single (finRotate 5 (finRotate 5 j)) 1 +
          x (finRotate 5 (finRotate 5 (finRotate 5 j))) •
            Pi.single (finRotate 5 (finRotate 5 (finRotate 5 j))) 1 +
            x (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j)))) •
              Pi.single (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1 := by
  -- The edge equation determines the missing `j`-coordinate from the other four coordinates.
  have hxj : x j = -x (finRotate 5 j) := by
    linarith
  ext i
  fin_cases i <;> fin_cases j
  · simpa using hxj
  · simp
  · simp
  · simp
  · simp
  · simp
  · simpa using hxj
  · simp
  · simp
  · simp
  · simp
  · simp
  · simpa using hxj
  · simp
  · simp
  · simp
  · simp
  · simp
  · simpa using hxj
  · simp
  · simp
  · simp
  · simp
  · simp
  · simpa using hxj

/-- Helper for Exercise 7.2: every vector in the lifted edge-kernel hyperplane of `ℝ^(W₅)` is an
explicit combination of the oriented lifted-edge witness directions. -/
private lemma wheelEdgeKernelDecomposition (j : Fin 5) (x : Option (Fin 5) → ℝ)
    (hx : x (some j) + x (some (finRotate 5 j)) + x none = 0) :
    x =
      x (some (finRotate 5 j)) •
        (Pi.single (some (finRotate 5 j)) (1 : ℝ) - Pi.single (some j) 1) +
        x none • (Pi.single none (1 : ℝ) - Pi.single (some j) 1) +
          x (some (finRotate 5 (finRotate 5 j))) •
            Pi.single (some (finRotate 5 (finRotate 5 j))) 1 +
            x (some (finRotate 5 (finRotate 5 (finRotate 5 j)))) •
              Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1 +
              x (some (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j))))) •
                Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j))))) 1 := by
  -- The lifted edge equation determines the missing `j`-coordinate from the remaining five
  -- coordinates.
  have hxj : x (some j) = -x (some (finRotate 5 j)) - x none := by
    linarith
  ext i
  cases i with
  | none =>
      simp
  | some i =>
      fin_cases i <;> fin_cases j
      · simpa using hxj
      · simp
      · simp
      · simp
      · simp
      · simp
      · simpa using hxj
      · simp
      · simp
      · simp
      · simp
      · simp
      · simpa using hxj
      · simp
      · simp
      · simp
      · simp
      · simp
      · simpa using hxj
      · simp
      · simp
      · simp
      · simp
      · simp
      · simpa using hxj

/-- Part (1) of the current exercise. For each cycle vertex `v_j` of `C₅`, the nonnegativity inequality
`x_j ≥ 0` cuts out the facet of `STAB(C₅)` where `x_j = 0`. -/
theorem exercise_7_2_nonnegativity_facet
    (j : Fin 5) :
    IsFacetOf
      STAB(cycleGraph 5)
      {x : Fin 5 → ℝ | x ∈ STAB(cycleGraph 5) ∧ x j = 0} := by
  let P : Set (Fin 5 → ℝ) := STAB(cycleGraph 5)
  let F : Set (Fin 5 → ℝ) := {x : Fin 5 → ℝ | x ∈ P ∧ x j = 0}
  let c : Fin 5 → ℝ := -Pi.single j 1
  have hzero_mem_P : (0 : Fin 5 → ℝ) ∈ P := by
    -- The origin is the indicator of the empty stable set.
    simpa [P, stableSetIndicatorEmpty] using
      (stableSetIndicator_mem_stableSetPolytope (cycleGraph 5)
        (by simp : (cycleGraph 5).IsIndepSet (∅ : Finset (Fin 5))))
  have hzero_mem_F : (0 : Fin 5 → ℝ) ∈ F := by
    -- The origin also satisfies the defining equality `x_j = 0`.
    exact ⟨hzero_mem_P, by simp [F]⟩
  have hvalid : ∀ ⦃x : Fin 5 → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ 0 := by
    intro x hx
    -- The inequality is checked on stable-set vertices and then extended to the convex hull.
    refine dotProductLeOfMemStableSetPolytope (G := cycleGraph 5) ?_ hx
    intro s hs
    by_cases hjs : j ∈ s
    · simp [c, dotProduct, stableSetIndicator, hjs]
    · simp [c, dotProduct, stableSetIndicator, hjs]
  have hzero_eq : c ⬝ᵥ (0 : Fin 5 → ℝ) = 0 := by
    simp [c, dotProduct]
  have hF_exposed : IsExposed ℝ P F := by
    -- The nonempty tight equality set is exposed by the coordinate functional `-x_j`.
    simpa [F, c, dotProduct, Pi.single_apply] using
      (equalitySetIsExposed (P := P) (c := c) (x₀ := (0 : Fin 5 → ℝ)) (δ := 0)
        hvalid hzero_mem_P hzero_eq)
  have hdir_le :
      (affineSpan ℝ F).direction ≤ LinearMap.ker (dotProductLinearMap c) := by
    -- Every face direction preserves the defining equality.
    simpa [F, c, dotProduct, Pi.single_apply] using
      (equalitySetDirectionLeKer (P := P) (c := c) (x₀ := (0 : Fin 5 → ℝ)) (δ := 0)
        hzero_eq)
  have hsingle_mem : ∀ i : Fin 5, i ≠ j → Pi.single i (1 : ℝ) ∈ F := by
    intro i hij
    have hi_indicator_mem_P : stableSetIndicator ({i} : Finset (Fin 5)) ∈ P := by
      -- Singleton stable sets give the coordinate unit vectors of `C₅`.
      simpa [P] using
        (stableSetIndicator_mem_stableSetPolytope (cycleGraph 5)
          (by simp : (cycleGraph 5).IsIndepSet ({i} : Finset (Fin 5))))
    have hi_indicator_eq : stableSetIndicator ({i} : Finset (Fin 5)) = Pi.single i (1 : ℝ) := by
      -- Rewrite the singleton indicator into the standard basis vector.
      ext u
      by_cases hu : u = i
      · subst hu
        simp [stableSetIndicator]
      · simp [stableSetIndicator, hu]
    have hi_mem_P : Pi.single i (1 : ℝ) ∈ P := hi_indicator_eq ▸ hi_indicator_mem_P
    exact ⟨hi_mem_P, by simp [hij]⟩
  have hsingle_dir :
      ∀ i : Fin 5, i ≠ j → Pi.single i (1 : ℝ) ∈ (affineSpan ℝ F).direction := by
    intro i hij
    have hi_aff : Pi.single i (1 : ℝ) ∈ affineSpan ℝ F := mem_affineSpan ℝ (hsingle_mem i hij)
    have hzero_aff : (0 : Fin 5 → ℝ) ∈ affineSpan ℝ F := mem_affineSpan ℝ hzero_mem_F
    -- Subtracting the basepoint `0` turns the face points into direction vectors.
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hi_aff hzero_aff
  have hker_le :
      LinearMap.ker (dotProductLinearMap c) ≤ (affineSpan ℝ F).direction := by
    intro x hx
    have hxj : x j = 0 := by
      have hx0 : c ⬝ᵥ x = 0 := by
        simpa [dotProductLinearMap_apply] using (LinearMap.mem_ker.mp hx)
      have hx1 : -(Pi.single j (1 : ℝ) ⬝ᵥ x) = 0 := by
        simpa [c, dotProduct] using hx0
      have hx2 : Pi.single j (1 : ℝ) ⬝ᵥ x = 0 := by
        linarith
      simpa [dotProduct, Pi.single_apply] using hx2
    have hsum_repr :
        x = Finset.sum (Finset.univ.erase j) (fun i ↦ x i • Pi.single i (1 : ℝ)) := by
      -- On the hyperplane `x_j = 0`, the remaining coordinate directions span every vector.
      calc
        x = ∑ i : Fin 5, x i • Pi.single i (1 : ℝ) := by
              ext i
              simp [Pi.single_apply]
        _ = x j • Pi.single j (1 : ℝ) +
              Finset.sum (Finset.univ.erase j) (fun i ↦ x i • Pi.single i (1 : ℝ)) := by
              simpa using (Finset.sum_erase_add (f := fun i : Fin 5 ↦ x i • Pi.single i (1 : ℝ))
                (Finset.mem_univ j)).symm
        _ = Finset.sum (Finset.univ.erase j) (fun i ↦ x i • Pi.single i (1 : ℝ)) := by
              simp [hxj]
    rw [hsum_repr]
    refine Submodule.sum_mem _ ?_
    intro i hi
    exact Submodule.smul_mem _ _ (hsingle_dir i (Finset.mem_erase.mp hi).1)
  have hdir_eq :
      (affineSpan ℝ F).direction = LinearMap.ker (dotProductLinearMap c) :=
    le_antisymm hdir_le hker_le
  have hL_ne : dotProductLinearMap c ≠ 0 := by
    intro hL0
    have hvalue : dotProductLinearMap c (Pi.single j (1 : ℝ)) = -1 := by
      simp [c, dotProductLinearMap_apply, dotProduct, Pi.single_apply]
    have hzero : dotProductLinearMap c (Pi.single j (1 : ℝ)) = 0 := by
      simpa [hL0]
    linarith
  have hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction = 4 := by
    calc
      Module.finrank ℝ (affineSpan ℝ F).direction
          = Module.finrank ℝ (LinearMap.ker (dotProductLinearMap c)) := by
              rw [hdir_eq]
      _ = 4 := by
        simpa using finrankKerEqCardSubOne (V := Fin 5) (L := dotProductLinearMap c) hL_ne
  have hP_dim :
      Module.finrank ℝ (affineSpan ℝ P).direction = 5 := by
    -- `STAB(C₅)` is full-dimensional in `ℝ⁵`.
    change Module.finrank ℝ (affineSpan ℝ STAB(cycleGraph 5)).direction = 5
    rw [stableSetPolytopeAffineSpanEqTop (G := cycleGraph 5),
      AffineSubspace.direction_top, finrank_top, Module.finrank_fintype_fun_eq_card]
    norm_num
  -- The equality face is nonempty, exposed, and has codimension one.
  rw [isFacetOf_iff]
  refine ⟨⟨0, hzero_mem_F⟩, hF_exposed, ?_⟩
  rw [hF_dim, hP_dim]

/-- Helper for Exercise 7.2: the oriented edge face `x j + x (j+1) = 1` of `STAB(C₅)` is a
facet. -/
private theorem cycleEdgeFacetOriented (j : Fin 5) :
    IsFacetOf
      STAB(cycleGraph 5)
      {x : Fin 5 → ℝ |
        x ∈ STAB(cycleGraph 5) ∧ x j + x (finRotate 5 j) = 1} := by
  -- Route correction: use the existing exposed-face and kernel-decomposition shell directly, with
  -- all witnesses frozen in the same sparse `Pi.single` normal form.
  let P : Set (Fin 5 → ℝ) := STAB(cycleGraph 5)
  let F : Set (Fin 5 → ℝ) :=
    {x : Fin 5 → ℝ | x ∈ P ∧ x j + x (finRotate 5 j) = 1}
  let c : Fin 5 → ℝ := Pi.single j (1 : ℝ) + Pi.single (finRotate 5 j) 1
  let pj : Fin 5 → ℝ := Pi.single j (1 : ℝ)
  let psucc : Fin 5 → ℝ := Pi.single (finRotate 5 j) (1 : ℝ)
  let p2 : Fin 5 → ℝ := Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 j)) 1
  let p3 : Fin 5 → ℝ :=
    Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 (finRotate 5 j))) 1
  let p4 : Fin 5 → ℝ :=
    Pi.single (finRotate 5 j) (1 : ℝ) +
      Pi.single (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1
  have hadj : (cycleGraph 5).Adj j (finRotate 5 j) := by
    -- The oriented edge is one of the five cycle edges.
    exact (cycleGraph_adj_iff_finRotate_five j (finRotate 5 j)).2 (Or.inl rfl)
  have hvalid : ∀ ⦃x : Fin 5 → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ 1 := by
    intro x hx
    -- A stable set cannot contain both endpoints of the oriented edge.
    refine dotProductLeOfMemStableSetPolytope (G := cycleGraph 5) ?_ hx
    intro s hs
    by_cases hj : j ∈ s
    · by_cases hsucc : finRotate 5 j ∈ s
      · have hnot : ¬ (cycleGraph 5).Adj j (finRotate 5 j) := hs hj hsucc (finRotate_ne_self_five j)
        exact False.elim (hnot hadj)
      · have hsucc' : j + 1 ∉ s := by
          simpa using hsucc
        rw [dotProductCycleEdge_apply]
        simp [stableSetIndicator, hj, hsucc']
    · by_cases hsucc : finRotate 5 j ∈ s
      · have hsucc' : j + 1 ∈ s := by
          simpa using hsucc
        rw [dotProductCycleEdge_apply]
        simp [stableSetIndicator, hj, hsucc']
      · rw [dotProductCycleEdge_apply]
        -- Local instance justification (defeq pin): unfolding the imported
        -- `stableSetIndicator` fixes the `Finset.mem` decider to `Classical.decEq`.
        let _ : DecidableEq (Fin 5) := Classical.decEq _
        have hbound : (if j + 1 ∈ s then (1 : ℝ) else 0) ≤ 1 := by
          split_ifs <;> norm_num
        simpa [stableSetIndicator, hj] using hbound
  have hpj_mem_P : pj ∈ P := by
    -- The singleton `{j}` is a stable set, so its indicator is a face point.
    simpa [P, pj] using
      (cycleSinglePoint_memStableSetPolytope j)
  have hpj_mem_F : pj ∈ F := by
    -- The singleton `{j}` is tight for the edge equation.
    have hpj_tight : c ⬝ᵥ pj = 1 := by
      rw [dotProductCycleEdge_apply]
      simp [pj]
    exact ⟨hpj_mem_P, by simpa [F, c, dotProductCycleEdge_apply] using hpj_tight⟩
  have hpj_eq : c ⬝ᵥ pj = 1 := by
    -- The defining functional takes value `1` on the singleton witness `{j}`.
    rw [dotProductCycleEdge_apply]
    simp [pj]
  have hF_exposed : IsExposed ℝ P F := by
    -- The nonempty equality face is exposed by the oriented edge functional.
    simpa [F, c, dotProductCycleEdge_apply] using
      (equalitySetIsExposed (P := P) (c := c) (x₀ := pj) (δ := 1)
        hvalid hpj_mem_P hpj_eq)
  have hdir_le :
      (affineSpan ℝ F).direction ≤ LinearMap.ker (dotProductLinearMap c) := by
    -- Every direction inside the face preserves the tight edge equation.
    simpa [F, c, dotProductCycleEdge_apply] using
      (equalitySetDirectionLeKer (P := P) (c := c) (x₀ := pj) (δ := 1)
        hpj_eq)
  have hpsucc_mem_F : psucc ∈ F := by
    have hpsucc_mem_P : psucc ∈ P := by
      -- The other endpoint singleton is a second tight face point.
      simpa [P, psucc] using
        (cycleSinglePoint_memStableSetPolytope (finRotate 5 j))
    have hpsucc_tight : c ⬝ᵥ psucc = 1 := by
      rw [dotProductCycleEdge_apply]
      simp [psucc]
    exact ⟨hpsucc_mem_P, by simpa [F, c, dotProductCycleEdge_apply] using hpsucc_tight⟩
  have hp2_mem_F : p2 ∈ F := by
    have hp2_mem_P : p2 ∈ P := by
      -- The pair `{j, j+2}` is stable and lies on the edge face.
      simpa [P, p2] using (cycleTwoStepPairPoint_memStableSetPolytope j)
    have hp2_tight : c ⬝ᵥ p2 = 1 := by
      rw [dotProductCycleEdge_apply]
      fin_cases j <;> simp [p2]
    exact ⟨hp2_mem_P, by simpa [F, c, dotProductCycleEdge_apply] using hp2_tight⟩
  have hp3_mem_F : p3 ∈ F := by
    have hp3_mem_P : p3 ∈ P := by
      -- The pair `{j, j+3}` is another stable tight witness.
      simpa [P, p3] using (cycleThreeStepPairPoint_memStableSetPolytope j)
    have hp3_tight : c ⬝ᵥ p3 = 1 := by
      rw [dotProductCycleEdge_apply]
      fin_cases j <;> simp [p3]
    exact ⟨hp3_mem_P, by simpa [F, c, dotProductCycleEdge_apply] using hp3_tight⟩
  have hp4_mem_F : p4 ∈ F := by
    have hp4_mem_P : p4 ∈ P := by
      -- The pair `{j+1, j+4}` isolates the last kernel generator.
      simpa [P, p4] using (cycleThreeStepPairPoint_memStableSetPolytope (finRotate 5 j))
    have hp4_tight : c ⬝ᵥ p4 = 1 := by
      rw [dotProductCycleEdge_apply]
      fin_cases j <;> simp [p4]
    exact ⟨hp4_mem_P, by simpa [F, c, dotProductCycleEdge_apply] using hp4_tight⟩
  have hsub_mem :
      ∀ {x y : Fin 5 → ℝ}, x ∈ F → y ∈ F → x - y ∈ (affineSpan ℝ F).direction := by
    intro x y hx hy
    have hx_aff : x ∈ affineSpan ℝ F := mem_affineSpan ℝ hx
    have hy_aff : y ∈ affineSpan ℝ F := mem_affineSpan ℝ hy
    -- Differences of tight witnesses lie in the direction of the face.
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hx_aff hy_aff
  have hgenSucc :
      (Pi.single (finRotate 5 j) (1 : ℝ) - Pi.single j 1 : Fin 5 → ℝ) ∈
        (affineSpan ℝ F).direction := by
    -- Subtract the two singleton witnesses to isolate `e_(j+1) - e_j`.
    simpa [pj, psucc] using hsub_mem hpsucc_mem_F hpj_mem_F
  have hgen2 :
      (Pi.single (finRotate 5 (finRotate 5 j)) (1 : ℝ) : Fin 5 → ℝ) ∈
        (affineSpan ℝ F).direction := by
    have hpair2 :
        ((Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 j)) 1) -
            Pi.single j 1 : Fin 5 → ℝ) =
          Pi.single (finRotate 5 (finRotate 5 j)) 1 := by
      simpa using
        (pairMinusSingleton_eq_single (V := Fin 5)
          (a := j) (b := finRotate 5 (finRotate 5 j)))
    have hraw :
        ((Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 j)) 1) -
            Pi.single j 1 : Fin 5 → ℝ) ∈
          (affineSpan ℝ F).direction := by
      simpa [p2, pj, add_comm, add_left_comm, add_assoc] using hsub_mem hp2_mem_F hpj_mem_F
    simpa [hpair2] using hraw
  have hgen3 :
      (Pi.single (finRotate 5 (finRotate 5 (finRotate 5 j))) (1 : ℝ) : Fin 5 → ℝ) ∈
        (affineSpan ℝ F).direction := by
    have hpair3 :
        ((Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 (finRotate 5 j))) 1) -
            Pi.single j 1 : Fin 5 → ℝ) =
          Pi.single (finRotate 5 (finRotate 5 (finRotate 5 j))) 1 := by
      simpa using
        (pairMinusSingleton_eq_single (V := Fin 5)
          (a := j) (b := finRotate 5 (finRotate 5 (finRotate 5 j))))
    have hraw :
        ((Pi.single j (1 : ℝ) + Pi.single (finRotate 5 (finRotate 5 (finRotate 5 j))) 1) -
            Pi.single j 1 : Fin 5 → ℝ) ∈
          (affineSpan ℝ F).direction := by
      simpa [p3, pj, add_comm, add_left_comm, add_assoc] using hsub_mem hp3_mem_F hpj_mem_F
    simpa [hpair3] using hraw
  have hgen4 :
      (Pi.single (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j)))) (1 : ℝ) :
          Fin 5 → ℝ) ∈
        (affineSpan ℝ F).direction := by
    have hpair4 :
        ((Pi.single (finRotate 5 j) (1 : ℝ) +
              Pi.single (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1) -
            Pi.single (finRotate 5 j) 1 : Fin 5 → ℝ) =
          Pi.single (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1 := by
      simpa using
        (pairMinusSingleton_eq_single (V := Fin 5)
          (a := finRotate 5 j)
          (b := finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j)))))
    have hraw :
        ((Pi.single (finRotate 5 j) (1 : ℝ) +
              Pi.single (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1) -
            Pi.single (finRotate 5 j) 1 : Fin 5 → ℝ) ∈
          (affineSpan ℝ F).direction := by
      simpa [p4, psucc, add_comm, add_left_comm, add_assoc] using
        hsub_mem hp4_mem_F hpsucc_mem_F
    simpa [hpair4] using hraw
  have hker_le :
      LinearMap.ker (dotProductLinearMap c) ≤ (affineSpan ℝ F).direction := by
    intro x hx
    have hxsum : x j + x (finRotate 5 j) = 0 := by
      simpa [c, dotProductCycleEdge_apply, dotProductLinearMap_apply] using
        (LinearMap.mem_ker.mp hx)
    -- The explicit edge-kernel decomposition rewrites every kernel vector into the four witness
    -- directions.
    rw [cycleEdgeKernelDecomposition j x hxsum]
    have hsumSucc2 :
        x (finRotate 5 j) • (Pi.single (finRotate 5 j) (1 : ℝ) - Pi.single j 1) +
            x (finRotate 5 (finRotate 5 j)) • Pi.single (finRotate 5 (finRotate 5 j)) 1 ∈
          (affineSpan ℝ F).direction :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hgenSucc) (Submodule.smul_mem _ _ hgen2)
    have hsumSucc23 :
        x (finRotate 5 j) • (Pi.single (finRotate 5 j) (1 : ℝ) - Pi.single j 1) +
            x (finRotate 5 (finRotate 5 j)) • Pi.single (finRotate 5 (finRotate 5 j)) 1 +
              x (finRotate 5 (finRotate 5 (finRotate 5 j))) •
                Pi.single (finRotate 5 (finRotate 5 (finRotate 5 j))) 1 ∈
          (affineSpan ℝ F).direction := by
      simpa [add_assoc] using
        Submodule.add_mem _ hsumSucc2 (Submodule.smul_mem _ _ hgen3)
    simpa [add_assoc] using
      Submodule.add_mem _ hsumSucc23 (Submodule.smul_mem _ _ hgen4)
  have hdir_eq :
      (affineSpan ℝ F).direction = LinearMap.ker (dotProductLinearMap c) :=
    le_antisymm hdir_le hker_le
  have hL_ne : dotProductLinearMap c ≠ 0 := by
    intro hL0
    have hvalue : dotProductLinearMap c pj = 1 := by
      simpa [dotProductLinearMap_apply] using hpj_eq
    have hzero : dotProductLinearMap c pj = 0 := by
      simpa [hL0]
    linarith
  have hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction = 4 := by
    calc
      Module.finrank ℝ (affineSpan ℝ F).direction
          = Module.finrank ℝ (LinearMap.ker (dotProductLinearMap c)) := by
              rw [hdir_eq]
      _ = 4 := by
        simpa using finrankKerEqCardSubOne (V := Fin 5) (L := dotProductLinearMap c) hL_ne
  have hP_dim :
      Module.finrank ℝ (affineSpan ℝ P).direction = 5 := by
    -- `STAB(C₅)` is full-dimensional in the ambient `ℝ⁵`.
    change Module.finrank ℝ (affineSpan ℝ STAB(cycleGraph 5)).direction = 5
    rw [stableSetPolytopeAffineSpanEqTop (G := cycleGraph 5),
      AffineSubspace.direction_top, finrank_top, Module.finrank_fintype_fun_eq_card]
    norm_num
  -- The oriented edge equality face is nonempty, exposed, and has codimension one.
  rw [isFacetOf_iff]
  refine ⟨⟨pj, hpj_mem_F⟩, hF_exposed, ?_⟩
  rw [hF_dim, hP_dim]

/-- Part (2) of the current exercise. For every edge `v_jv_k` of `C₅`, the edge inequality
`x_j + x_k ≤ 1` cuts out the facet of `STAB(C₅)` where `x_j + x_k = 1`. -/
theorem exercise_7_2_edge_facet
    {j k : Fin 5} (hjk : (cycleGraph 5).Adj j k) :
    IsFacetOf
      STAB(cycleGraph 5)
      {x : Fin 5 → ℝ | x ∈ STAB(cycleGraph 5) ∧ x j + x k = 1} := by
  -- Route correction: normalize the edge orientation first, then reuse the oriented facet proof.
  rcases (cycleGraph_adj_iff_finRotate_five j k).1 hjk with hsucc | hpred
  · subst hsucc
    simpa using cycleEdgeFacetOriented j
  · subst hpred
    simpa [add_comm] using cycleEdgeFacetOriented k

/-- Part (3) of the current exercise. The odd-cycle inequality `∑_{j=1}^5 x_j ≤ 2` cuts out the facet of
`STAB(C₅)` where the coordinate sum is `2`. -/
theorem exercise_7_2_odd_cycle_facet :
    IsFacetOf
      STAB(cycleGraph 5)
      {x : Fin 5 → ℝ | x ∈ STAB(cycleGraph 5) ∧ (∑ j : Fin 5, x j) = 2} := by
  let P : Set (Fin 5 → ℝ) := STAB(cycleGraph 5)
  let F : Set (Fin 5 → ℝ) := {x : Fin 5 → ℝ | x ∈ P ∧ (∑ j : Fin 5, x j) = 2}
  let c : Fin 5 → ℝ := fun _ ↦ 1
  let p02 : Fin 5 → ℝ := Pi.single 0 (1 : ℝ) + Pi.single 2 1
  let p13 : Fin 5 → ℝ := Pi.single 1 (1 : ℝ) + Pi.single 3 1
  let p24 : Fin 5 → ℝ := Pi.single 2 (1 : ℝ) + Pi.single 4 1
  let p30 : Fin 5 → ℝ := Pi.single 3 (1 : ℝ) + Pi.single 0 1
  let p41 : Fin 5 → ℝ := Pi.single 4 (1 : ℝ) + Pi.single 1 1
  have hvalid : ∀ ⦃x : Fin 5 → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ 2 := by
    intro x hx
    -- The odd-cycle inequality is valid because every stable set of `C₅` has size at most `2`.
    refine dotProductLeOfMemStableSetPolytope (G := cycleGraph 5) ?_ hx
    intro s hs
    have hs_card : (s.card : ℝ) ≤ 2 := by
      exact_mod_cast cycleGraph_indep_card_le_two s hs
    simpa [c, dotProduct, sum_stableSetIndicator_eq_card] using hs_card
  have hp02_mem_P : p02 ∈ P := by
    -- The stable pair `{0,2}` gives one tight vertex of the odd-cycle face.
    simpa [P, p02] using cycleTwoStepPairPoint_memStableSetPolytope 0
  have hp13_mem_P : p13 ∈ P := by
    -- The stable pair `{1,3}` gives a second tight vertex.
    simpa [P, p13] using cycleTwoStepPairPoint_memStableSetPolytope 1
  have hp24_mem_P : p24 ∈ P := by
    -- The stable pair `{2,4}` gives a third tight vertex.
    simpa [P, p24] using cycleTwoStepPairPoint_memStableSetPolytope 2
  have hp30_mem_P : p30 ∈ P := by
    -- The stable pair `{3,0}` gives a fourth tight vertex.
    simpa [P, p30] using cycleTwoStepPairPoint_memStableSetPolytope 3
  have hp41_mem_P : p41 ∈ P := by
    -- The stable pair `{4,1}` gives the fifth tight vertex.
    simpa [P, p41] using cycleTwoStepPairPoint_memStableSetPolytope 4
  have hp02_mem_F : p02 ∈ F := by
    -- Every stable pair has coordinate sum `2`, so it lies in the equality face.
    refine ⟨hp02_mem_P, by
      simp [p02, Fin.sum_univ_five, Pi.single_apply]
      norm_num⟩
  have hp13_mem_F : p13 ∈ F := by
    -- This second pair witness is tight for the same equality.
    refine ⟨hp13_mem_P, by
      simp [p13, Fin.sum_univ_five, Pi.single_apply]
      norm_num⟩
  have hp24_mem_F : p24 ∈ F := by
    -- This third pair witness is again tight.
    refine ⟨hp24_mem_P, by
      simp [p24, Fin.sum_univ_five, Pi.single_apply]
      norm_num⟩
  have hp30_mem_F : p30 ∈ F := by
    -- The fourth pair witness also has total weight `2`.
    refine ⟨hp30_mem_P, by
      simp [p30, Fin.sum_univ_five, Pi.single_apply]
      norm_num⟩
  have hp41_mem_F : p41 ∈ F := by
    -- The fifth pair witness closes the odd-cycle orbit of tight vertices.
    refine ⟨hp41_mem_P, by
      simp [p41, Fin.sum_univ_five, Pi.single_apply]
      norm_num⟩
  have hp02_eq : c ⬝ᵥ p02 = 2 := by
    -- The face is nonempty because the pair witness `{0,2}` is tight.
    simp [c, p02, dotProduct, Fin.sum_univ_five, Pi.single_apply]
    norm_num
  have hF_exposed : IsExposed ℝ P F := by
    -- The tight equality set is exposed by the all-ones functional.
    simpa [F, c, dotProduct] using
      (equalitySetIsExposed (P := P) (c := c) (x₀ := p02) (δ := 2)
        hvalid hp02_mem_P hp02_eq)
  have hdir_le :
      (affineSpan ℝ F).direction ≤ LinearMap.ker (dotProductLinearMap c) := by
    -- Any direction inside the equality face preserves the coordinate sum.
    simpa [F, c, dotProduct] using
      (equalitySetDirectionLeKer (P := P) (c := c) (x₀ := p02) (δ := 2)
        hp02_eq)
  have hsub_mem :
      ∀ {x y : Fin 5 → ℝ}, x ∈ F → y ∈ F → x - y ∈ (affineSpan ℝ F).direction := by
    intro x y hx hy
    have hx_aff : x ∈ affineSpan ℝ F := mem_affineSpan ℝ hx
    have hy_aff : y ∈ affineSpan ℝ F := mem_affineSpan ℝ hy
    -- Subtracting two tight witnesses lands in the direction of the face.
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hx_aff hy_aff
  have hgen40 :
      (Pi.single 4 (1 : ℝ) - Pi.single 0 1 : Fin 5 → ℝ) ∈ (affineSpan ℝ F).direction := by
    -- Comparing the tight witnesses `{2,4}` and `{0,2}` isolates `e₄ - e₀`.
    have hpair40 :
        (((Pi.single (2 : Fin 5) (1 : ℝ) : Fin 5 → ℝ) + Pi.single 4 1) -
            (Pi.single 2 1 + Pi.single 0 1) : Fin 5 → ℝ) =
          Pi.single 4 (1 : ℝ) - Pi.single 0 1 := by
      simpa using
        (pairMinusPair_eq_single_sub_single (V := Fin 5)
          (a := (2 : Fin 5)) (b := (4 : Fin 5)) (c := (0 : Fin 5)))
    have hraw :
        (((Pi.single (2 : Fin 5) (1 : ℝ) : Fin 5 → ℝ) + Pi.single 4 1) -
            (Pi.single 2 1 + Pi.single 0 1) : Fin 5 → ℝ) ∈
          (affineSpan ℝ F).direction := by
      simpa [p24, p02, add_comm, add_left_comm, add_assoc] using hsub_mem hp24_mem_F hp02_mem_F
    simpa [hpair40] using hraw
  have hgen32 :
      (Pi.single 3 (1 : ℝ) - Pi.single 2 1 : Fin 5 → ℝ) ∈ (affineSpan ℝ F).direction := by
    -- Comparing `{0,3}` with `{0,2}` isolates `e₃ - e₂`.
    have hpair32 :
        (((Pi.single (0 : Fin 5) (1 : ℝ) : Fin 5 → ℝ) + Pi.single 3 1) -
            (Pi.single 0 1 + Pi.single 2 1) : Fin 5 → ℝ) =
          Pi.single 3 (1 : ℝ) - Pi.single 2 1 := by
      simpa using
        (pairMinusPair_eq_single_sub_single (V := Fin 5)
          (a := (0 : Fin 5)) (b := (3 : Fin 5)) (c := (2 : Fin 5)))
    simpa [p30, p02, add_comm, add_left_comm, add_assoc, hpair32] using
      hsub_mem hp30_mem_F hp02_mem_F
  have hgen12 :
      (Pi.single 1 (1 : ℝ) - Pi.single 2 1 : Fin 5 → ℝ) ∈ (affineSpan ℝ F).direction := by
    -- Comparing `{1,4}` with `{2,4}` isolates `e₁ - e₂`.
    have hpair12 :
        (((Pi.single (4 : Fin 5) (1 : ℝ) : Fin 5 → ℝ) + Pi.single 1 1) -
            (Pi.single 4 1 + Pi.single 2 1) : Fin 5 → ℝ) =
          Pi.single 1 (1 : ℝ) - Pi.single 2 1 := by
      simpa using
        (pairMinusPair_eq_single_sub_single (V := Fin 5)
          (a := (4 : Fin 5)) (b := (1 : Fin 5)) (c := (2 : Fin 5)))
    simpa [p41, p24, add_comm, add_left_comm, add_assoc, hpair12] using
      hsub_mem hp41_mem_F hp24_mem_F
  have hgen10 :
      (Pi.single 1 (1 : ℝ) - Pi.single 0 1 : Fin 5 → ℝ) ∈ (affineSpan ℝ F).direction := by
    -- Comparing `{1,3}` with `{0,3}` isolates `e₁ - e₀`.
    have hpair10 :
        (((Pi.single (3 : Fin 5) (1 : ℝ) : Fin 5 → ℝ) + Pi.single 1 1) -
            (Pi.single 3 1 + Pi.single 0 1) : Fin 5 → ℝ) =
          Pi.single 1 (1 : ℝ) - Pi.single 0 1 := by
      simpa using
        (pairMinusPair_eq_single_sub_single (V := Fin 5)
          (a := (3 : Fin 5)) (b := (1 : Fin 5)) (c := (0 : Fin 5)))
    simpa [p13, p30, add_comm, add_left_comm, add_assoc, hpair10] using
      hsub_mem hp13_mem_F hp30_mem_F
  have hker_le :
      LinearMap.ker (dotProductLinearMap c) ≤ (affineSpan ℝ F).direction := by
    intro x hx
    have hxsum : (∑ i : Fin 5, x i) = 0 := by
      simpa [c, dotProduct, dotProductLinearMap_apply] using (LinearMap.mem_ker.mp hx)
    -- The zero-sum decomposition rewrites every kernel vector into the four witness directions.
    rw [cycleSumZero_decomposition x hxsum]
    have hsum43 :
        x 4 • (Pi.single 4 (1 : ℝ) - Pi.single 0 1) +
            x 3 • (Pi.single 3 (1 : ℝ) - Pi.single 2 1) ∈
          (affineSpan ℝ F).direction :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hgen40) (Submodule.smul_mem _ _ hgen32)
    have hsum432 :
        x 4 • (Pi.single 4 (1 : ℝ) - Pi.single 0 1) +
            x 3 • (Pi.single 3 (1 : ℝ) - Pi.single 2 1) +
              (-x 2 - x 3) • (Pi.single 1 (1 : ℝ) - Pi.single 2 1) ∈
          (affineSpan ℝ F).direction := by
      simpa [add_assoc] using
        Submodule.add_mem _ hsum43 (Submodule.smul_mem _ _ hgen12)
    simpa [add_assoc] using
      Submodule.add_mem _ hsum432 (Submodule.smul_mem _ _ hgen10)
  have hdir_eq :
      (affineSpan ℝ F).direction = LinearMap.ker (dotProductLinearMap c) :=
    le_antisymm hdir_le hker_le
  have hL_ne : dotProductLinearMap c ≠ 0 := by
    intro hL0
    have hvalue : dotProductLinearMap c (Pi.single 0 (1 : ℝ)) = 1 := by
      simp [c, dotProductLinearMap_apply, dotProduct]
    have hzero : dotProductLinearMap c (Pi.single 0 (1 : ℝ)) = 0 := by
      simpa [hL0]
    linarith
  have hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction = 4 := by
    calc
      Module.finrank ℝ (affineSpan ℝ F).direction
          = Module.finrank ℝ (LinearMap.ker (dotProductLinearMap c)) := by
              rw [hdir_eq]
      _ = 4 := by
        simpa using finrankKerEqCardSubOne (V := Fin 5) (L := dotProductLinearMap c) hL_ne
  have hP_dim :
      Module.finrank ℝ (affineSpan ℝ P).direction = 5 := by
    -- `STAB(C₅)` is full-dimensional in the ambient `ℝ⁵`.
    change Module.finrank ℝ (affineSpan ℝ STAB(cycleGraph 5)).direction = 5
    rw [stableSetPolytopeAffineSpanEqTop (G := cycleGraph 5),
      AffineSubspace.direction_top, finrank_top, Module.finrank_fintype_fun_eq_card]
    norm_num
  -- The odd-cycle equality face is nonempty, exposed, and has codimension one.
  rw [isFacetOf_iff]
  refine ⟨⟨p02, hp02_mem_F⟩, hF_exposed, ?_⟩
  rw [hF_dim, hP_dim]

/-- Part (4) of the current exercise. The nonnegativity facet `x_j ≥ 0` of `STAB(C₅)` lifts to the facet
`x_(v_j) ≥ 0` of `STAB(W₅)`, with equality face `x_(v_j) = 0`. -/
theorem exercise_7_2_lifted_nonnegativity_facet
    (j : Fin 5) :
    IsFacetOf
      STAB(fiveWheelGraph)
      {x : Option (Fin 5) → ℝ | x ∈ STAB(fiveWheelGraph) ∧ x (some j) = 0} := by
  let P : Set (Option (Fin 5) → ℝ) := STAB(fiveWheelGraph)
  let F : Set (Option (Fin 5) → ℝ) := {x : Option (Fin 5) → ℝ | x ∈ P ∧ x (some j) = 0}
  let c : Option (Fin 5) → ℝ := -Pi.single (some j) 1
  have hzero_mem_P : (0 : Option (Fin 5) → ℝ) ∈ P := by
    -- The origin is again the indicator of the empty stable set.
    simpa [P, stableSetIndicatorEmpty] using
      (stableSetIndicator_mem_stableSetPolytope fiveWheelGraph
        (by simp : fiveWheelGraph.IsIndepSet (∅ : Finset (Option (Fin 5)))))
  have hzero_mem_F : (0 : Option (Fin 5) → ℝ) ∈ F := by
    -- The origin satisfies the lifted equality `x_(v_j) = 0`.
    exact ⟨hzero_mem_P, by simp⟩
  have hvalid : ∀ ⦃x : Option (Fin 5) → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ 0 := by
    intro x hx
    -- The lifted lower bound is checked vertexwise on stable-set indicators.
    refine dotProductLeOfMemStableSetPolytope (G := fiveWheelGraph) ?_ hx
    intro s hs
    by_cases hjs : some j ∈ s
    · simp [c, dotProduct, stableSetIndicator, hjs]
    · simp [c, dotProduct, stableSetIndicator, hjs]
  have hzero_eq : c ⬝ᵥ (0 : Option (Fin 5) → ℝ) = 0 := by
    simp [c, dotProduct]
  have hF_exposed : IsExposed ℝ P F := by
    -- The tight equality set is exposed by the lifted coordinate functional.
    simpa [F, c, dotProduct, Pi.single_apply] using
      (equalitySetIsExposed (P := P) (c := c) (x₀ := (0 : Option (Fin 5) → ℝ)) (δ := 0)
        hvalid hzero_mem_P hzero_eq)
  have hdir_le :
      (affineSpan ℝ F).direction ≤ LinearMap.ker (dotProductLinearMap c) := by
    -- Directions inside the face preserve the equality `x_(v_j) = 0`.
    simpa [F, c, dotProduct, Pi.single_apply] using
      (equalitySetDirectionLeKer (P := P) (c := c) (x₀ := (0 : Option (Fin 5) → ℝ)) (δ := 0)
        hzero_eq)
  have hsingle_mem :
      ∀ i : Option (Fin 5), i ≠ some j → Pi.single i (1 : ℝ) ∈ F := by
    intro i hij
    have hi_indicator_mem_P : stableSetIndicator ({i} : Finset (Option (Fin 5))) ∈ P := by
      -- Every singleton of `W₅` is a stable set.
      simpa [P] using
        (stableSetIndicator_mem_stableSetPolytope fiveWheelGraph
          (by simp : fiveWheelGraph.IsIndepSet ({i} : Finset (Option (Fin 5)))))
    have hi_indicator_eq :
        stableSetIndicator ({i} : Finset (Option (Fin 5))) = Pi.single i (1 : ℝ) := by
      -- Rewrite the singleton indicator into the corresponding basis vector.
      ext u
      by_cases hu : u = i
      · subst hu
        simp [stableSetIndicator]
      · simp [stableSetIndicator, hu]
    have hi_mem_P : Pi.single i (1 : ℝ) ∈ P := hi_indicator_eq ▸ hi_indicator_mem_P
    exact ⟨hi_mem_P, by simp [hij]⟩
  have hsingle_dir :
      ∀ i : Option (Fin 5), i ≠ some j → Pi.single i (1 : ℝ) ∈ (affineSpan ℝ F).direction := by
    intro i hij
    have hi_aff : Pi.single i (1 : ℝ) ∈ affineSpan ℝ F := mem_affineSpan ℝ (hsingle_mem i hij)
    have hzero_aff : (0 : Option (Fin 5) → ℝ) ∈ affineSpan ℝ F := mem_affineSpan ℝ hzero_mem_F
    -- Subtracting the basepoint `0` again records the coordinate directions.
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hi_aff hzero_aff
  have hker_le :
      LinearMap.ker (dotProductLinearMap c) ≤ (affineSpan ℝ F).direction := by
    intro x hx
    have hxj : x (some j) = 0 := by
      have hx0 : c ⬝ᵥ x = 0 := by
        simpa [dotProductLinearMap_apply] using (LinearMap.mem_ker.mp hx)
      have hx1 : -(Pi.single (some j) (1 : ℝ) ⬝ᵥ x) = 0 := by
        simpa [c, dotProduct] using hx0
      have hx2 : Pi.single (some j) (1 : ℝ) ⬝ᵥ x = 0 := by
        linarith
      simpa [dotProduct, Pi.single_apply] using hx2
    have hsum_repr :
        x = Finset.sum (Finset.univ.erase (some j))
          (fun i ↦ x i • Pi.single i (1 : ℝ)) := by
      -- The lifted hyperplane is spanned by all basis vectors except `e_(some j)`.
      calc
        x = ∑ i : Option (Fin 5), x i • Pi.single i (1 : ℝ) := by
              ext i
              simp [Pi.single_apply]
        _ = x (some j) • Pi.single (some j) (1 : ℝ) +
              Finset.sum (Finset.univ.erase (some j))
                (fun i ↦ x i • Pi.single i (1 : ℝ)) := by
              simpa using
                (Finset.sum_erase_add
                  (f := fun i : Option (Fin 5) ↦ x i • Pi.single i (1 : ℝ))
                  (by simp : some j ∈ (Finset.univ : Finset (Option (Fin 5))))).symm
        _ = Finset.sum (Finset.univ.erase (some j))
              (fun i ↦ x i • Pi.single i (1 : ℝ)) := by
              simp [hxj]
    rw [hsum_repr]
    refine Submodule.sum_mem _ ?_
    intro i hi
    exact Submodule.smul_mem _ _ (hsingle_dir i (Finset.mem_erase.mp hi).1)
  have hdir_eq :
      (affineSpan ℝ F).direction = LinearMap.ker (dotProductLinearMap c) :=
    le_antisymm hdir_le hker_le
  have hL_ne : dotProductLinearMap c ≠ 0 := by
    intro hL0
    have hvalue : dotProductLinearMap c (Pi.single (some j) (1 : ℝ)) = -1 := by
      simp [c, dotProductLinearMap_apply, dotProduct, Pi.single_apply]
    have hzero : dotProductLinearMap c (Pi.single (some j) (1 : ℝ)) = 0 := by
      simpa [hL0]
    linarith
  have hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction = 5 := by
    calc
      Module.finrank ℝ (affineSpan ℝ F).direction
          = Module.finrank ℝ (LinearMap.ker (dotProductLinearMap c)) := by
              rw [hdir_eq]
      _ = 5 := by
        simpa using finrankKerEqCardSubOne
          (V := Option (Fin 5)) (L := dotProductLinearMap c) hL_ne
  have hP_dim :
      Module.finrank ℝ (affineSpan ℝ P).direction = 6 := by
    -- `STAB(W₅)` is full-dimensional in `ℝ⁶`.
    change Module.finrank ℝ (affineSpan ℝ STAB(fiveWheelGraph)).direction = 6
    rw [stableSetPolytopeAffineSpanEqTop (G := fiveWheelGraph),
      AffineSubspace.direction_top, finrank_top, Module.finrank_fintype_fun_eq_card]
    norm_num
  -- The lifted face is nonempty, exposed, and has codimension one.
  rw [isFacetOf_iff]
  refine ⟨⟨0, hzero_mem_F⟩, hF_exposed, ?_⟩
  rw [hF_dim, hP_dim]

/-- Helper for Exercise 7.2: the oriented lifted edge face
`x (some j) + x (some (j+1)) + x none = 1` of `STAB(W₅)` is a facet. -/
private theorem wheelEdgeFacetOriented (j : Fin 5) :
    IsFacetOf
      STAB(fiveWheelGraph)
      {x : Option (Fin 5) → ℝ |
        x ∈ STAB(fiveWheelGraph) ∧
          x (some j) + x (some (finRotate 5 j)) + x none = 1} := by
  -- Route correction: keep the lifted edge proof on the same exposed-face and kernel route, but
  -- freeze all witnesses in the exact `Option (Fin 5)` sparse spelling.
  let P : Set (Option (Fin 5) → ℝ) := STAB(fiveWheelGraph)
  let F : Set (Option (Fin 5) → ℝ) :=
    {x : Option (Fin 5) → ℝ |
      x ∈ P ∧ x (some j) + x (some (finRotate 5 j)) + x none = 1}
  let c : Option (Fin 5) → ℝ :=
    Pi.single (some j) (1 : ℝ) + Pi.single (some (finRotate 5 j)) 1 + Pi.single none 1
  let pj : Option (Fin 5) → ℝ := Pi.single (some j) (1 : ℝ)
  let psucc : Option (Fin 5) → ℝ := Pi.single (some (finRotate 5 j)) (1 : ℝ)
  let phub : Option (Fin 5) → ℝ := Pi.single none (1 : ℝ)
  let p2 : Option (Fin 5) → ℝ :=
    Pi.single (some j) (1 : ℝ) + Pi.single (some (finRotate 5 (finRotate 5 j))) 1
  let p3 : Option (Fin 5) → ℝ :=
    Pi.single (some j) (1 : ℝ) +
      Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1
  let p4 : Option (Fin 5) → ℝ :=
    Pi.single (some (finRotate 5 j)) (1 : ℝ) +
      Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j))))) 1
  have hadj : (cycleGraph 5).Adj j (finRotate 5 j) := by
    -- The oriented edge is one of the five cycle edges.
    exact (cycleGraph_adj_iff_finRotate_five j (finRotate 5 j)).2 (Or.inl rfl)
  have hvalid : ∀ ⦃x : Option (Fin 5) → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ 1 := by
    intro x hx
    -- No stable set of `W₅` can contain more than one vertex from `{v_j, v_(j+1), w}`.
    refine dotProductLeOfMemStableSetPolytope (G := fiveWheelGraph) ?_ hx
    intro s hs
    by_cases hnone : none ∈ s
    · have hj_not : some j ∉ s := by
        intro hj
        have hnot : ¬ fiveWheelGraph.Adj none (some j) := hs hnone hj (by simp)
        exact hnot (fiveWheelGraph_adj_hub j)
      have hsucc_not : some (finRotate 5 j) ∉ s := by
        intro hsucc
        have hnot : ¬ fiveWheelGraph.Adj none (some (finRotate 5 j)) := hs hnone hsucc (by simp)
        exact hnot (fiveWheelGraph_adj_hub (finRotate 5 j))
      have hsucc_not' : some (j + 1) ∉ s := by
        simpa using hsucc_not
      rw [dotProductWheelEdge_apply]
      simp [stableSetIndicator, hnone, hj_not, hsucc_not']
    · by_cases hj : some j ∈ s
      · have hsucc_not : some (finRotate 5 j) ∉ s := by
          intro hsucc
          have hnot : ¬ fiveWheelGraph.Adj (some j) (some (finRotate 5 j)) := by
            simpa [fiveWheelGraph_adj_some_some] using hs hj hsucc (by simp [finRotate_ne_self_five j])
          exact hnot hadj
        have hsucc_not' : some (j + 1) ∉ s := by
          simpa using hsucc_not
        rw [dotProductWheelEdge_apply]
        simp [stableSetIndicator, hnone, hj, hsucc_not']
      · by_cases hsucc : some (finRotate 5 j) ∈ s
        · have hsucc' : some (j + 1) ∈ s := by
            simpa using hsucc
          rw [dotProductWheelEdge_apply]
          simp [stableSetIndicator, hnone, hj, hsucc']
        · rw [dotProductWheelEdge_apply]
          -- Local instance justification (defeq pin): unfolding the imported
          -- `stableSetIndicator` fixes the `Finset.mem` decider to `Classical.decEq`.
          let _ : DecidableEq (Option (Fin 5)) := Classical.decEq _
          have hbound : (if some (j + 1) ∈ s then (1 : ℝ) else 0) ≤ 1 := by
            split_ifs <;> norm_num
          simpa [stableSetIndicator, hnone, hj] using hbound
  have hpj_mem_P : pj ∈ P := by
    -- The singleton `{v_j}` is a lifted tight witness.
    simpa [P, pj] using
      (wheelSomeSinglePoint_memStableSetPolytope j)
  have hpj_mem_F : pj ∈ F := by
    -- The singleton `{v_j}` satisfies the lifted edge equality.
    have hpj_tight : c ⬝ᵥ pj = 1 := by
      rw [dotProductWheelEdge_apply]
      simp [pj]
    exact ⟨hpj_mem_P, by simpa [F, c, dotProductWheelEdge_apply] using hpj_tight⟩
  have hpj_eq : c ⬝ᵥ pj = 1 := by
    -- The defining functional takes value `1` on the singleton witness `{v_j}`.
    rw [dotProductWheelEdge_apply]
    simp [pj]
  have hF_exposed : IsExposed ℝ P F := by
    -- The lifted edge equality set is exposed by its sparse defining functional.
    simpa [F, c, dotProductWheelEdge_apply] using
      (equalitySetIsExposed (P := P) (c := c) (x₀ := pj) (δ := 1)
        hvalid hpj_mem_P hpj_eq)
  have hdir_le :
      (affineSpan ℝ F).direction ≤ LinearMap.ker (dotProductLinearMap c) := by
    -- Every direction inside the lifted face preserves the edge equality.
    simpa [F, c, dotProductWheelEdge_apply] using
      (equalitySetDirectionLeKer (P := P) (c := c) (x₀ := pj) (δ := 1)
        hpj_eq)
  have hpsucc_mem_F : psucc ∈ F := by
    have hpsucc_mem_P : psucc ∈ P := by
      -- The second endpoint singleton is also tight.
      simpa [P, psucc] using
        (wheelSomeSinglePoint_memStableSetPolytope (finRotate 5 j))
    have hpsucc_tight : c ⬝ᵥ psucc = 1 := by
      rw [dotProductWheelEdge_apply]
      simp [psucc]
    exact ⟨hpsucc_mem_P, by simpa [F, c, dotProductWheelEdge_apply] using hpsucc_tight⟩
  have hphub_mem_F : phub ∈ F := by
    -- The hub singleton is the third tight witness on the lifted edge face.
    have hphub_mem_P : phub ∈ P := by
      simpa [P, phub] using wheelHubSinglePoint_memStableSetPolytope
    have hphub_tight : c ⬝ᵥ phub = 1 := by
      rw [dotProductWheelEdge_apply]
      simp [phub]
    exact ⟨hphub_mem_P, by simpa [F, c, dotProductWheelEdge_apply] using hphub_tight⟩
  have hp2_mem_F : p2 ∈ F := by
    have hp2_mem_P : p2 ∈ P := by
      -- The lifted pair `{v_j, v_(j+2)}` lies on the lifted edge face.
      simpa [P, p2, add_comm, add_left_comm, add_assoc] using
        (wheelTwoStepPairPoint_memStableSetPolytope j)
    have hp2_tight : c ⬝ᵥ p2 = 1 := by
      rw [dotProductWheelEdge_apply]
      fin_cases j <;> simp [p2]
    exact ⟨hp2_mem_P, by simpa [F, c, dotProductWheelEdge_apply] using hp2_tight⟩
  have hp3_mem_F : p3 ∈ F := by
    have hp3_mem_P : p3 ∈ P := by
      -- The lifted pair `{v_j, v_(j+3)}` gives the next tight witness.
      simpa [P, p3, add_comm, add_left_comm, add_assoc] using
        (wheelThreeStepPairPoint_memStableSetPolytope j)
    have hp3_tight : c ⬝ᵥ p3 = 1 := by
      rw [dotProductWheelEdge_apply]
      fin_cases j <;> simp [p3]
    exact ⟨hp3_mem_P, by simpa [F, c, dotProductWheelEdge_apply] using hp3_tight⟩
  have hp4_mem_F : p4 ∈ F := by
    have hp4_mem_P : p4 ∈ P := by
      -- The lifted pair `{v_(j+1), v_(j+4)}` isolates the last kernel generator.
      simpa [P, p4, add_comm, add_left_comm, add_assoc] using
        (wheelThreeStepPairPoint_memStableSetPolytope (finRotate 5 j))
    have hp4_tight : c ⬝ᵥ p4 = 1 := by
      rw [dotProductWheelEdge_apply]
      fin_cases j <;> simp [p4]
    exact ⟨hp4_mem_P, by simpa [F, c, dotProductWheelEdge_apply] using hp4_tight⟩
  have hsub_mem :
      ∀ {x y : Option (Fin 5) → ℝ},
        x ∈ F → y ∈ F → x - y ∈ (affineSpan ℝ F).direction := by
    intro x y hx hy
    have hx_aff : x ∈ affineSpan ℝ F := mem_affineSpan ℝ hx
    have hy_aff : y ∈ affineSpan ℝ F := mem_affineSpan ℝ hy
    -- Differences of tight witnesses span the direction of the face.
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hx_aff hy_aff
  have hgenSucc :
      (Pi.single (some (finRotate 5 j)) (1 : ℝ) - Pi.single (some j) 1 :
          Option (Fin 5) → ℝ) ∈
        (affineSpan ℝ F).direction := by
    -- Subtract the two endpoint singletons to isolate `e_(j+1) - e_j`.
    simpa [pj, psucc] using hsub_mem hpsucc_mem_F hpj_mem_F
  have hgenHub :
      (Pi.single none (1 : ℝ) - Pi.single (some j) 1 : Option (Fin 5) → ℝ) ∈
        (affineSpan ℝ F).direction := by
    -- Subtract the endpoint singleton from the hub singleton to isolate `e_w - e_j`.
    simpa [pj, phub] using hsub_mem hphub_mem_F hpj_mem_F
  have hgen2 :
      (Pi.single (some (finRotate 5 (finRotate 5 j))) (1 : ℝ) :
          Option (Fin 5) → ℝ) ∈
        (affineSpan ℝ F).direction := by
    have hpair2 :
        ((Pi.single (some j) (1 : ℝ) + Pi.single (some (finRotate 5 (finRotate 5 j))) 1) -
            Pi.single (some j) 1 : Option (Fin 5) → ℝ) =
          Pi.single (some (finRotate 5 (finRotate 5 j))) 1 := by
      simpa using
        (pairMinusSingleton_eq_single (V := Option (Fin 5))
          (a := some j) (b := some (finRotate 5 (finRotate 5 j))))
    have hraw :
        ((Pi.single (some j) (1 : ℝ) + Pi.single (some (finRotate 5 (finRotate 5 j))) 1) -
            Pi.single (some j) 1 : Option (Fin 5) → ℝ) ∈
          (affineSpan ℝ F).direction := by
      simpa [p2, pj, add_comm, add_left_comm, add_assoc] using hsub_mem hp2_mem_F hpj_mem_F
    simpa [hpair2] using hraw
  have hgen3 :
      (Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 j)))) (1 : ℝ) :
          Option (Fin 5) → ℝ) ∈
        (affineSpan ℝ F).direction := by
    have hpair3 :
        ((Pi.single (some j) (1 : ℝ) +
              Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1) -
            Pi.single (some j) 1 : Option (Fin 5) → ℝ) =
          Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1 := by
      simpa using
        (pairMinusSingleton_eq_single (V := Option (Fin 5))
          (a := some j) (b := some (finRotate 5 (finRotate 5 (finRotate 5 j)))))
    have hraw :
        ((Pi.single (some j) (1 : ℝ) +
              Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1) -
            Pi.single (some j) 1 : Option (Fin 5) → ℝ) ∈
          (affineSpan ℝ F).direction := by
      simpa [p3, pj, add_comm, add_left_comm, add_assoc] using hsub_mem hp3_mem_F hpj_mem_F
    simpa [hpair3] using hraw
  have hgen4 :
      (Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j))))) (1 : ℝ) :
          Option (Fin 5) → ℝ) ∈
        (affineSpan ℝ F).direction := by
    have hpair4 :
        ((Pi.single (some (finRotate 5 j)) (1 : ℝ) +
              Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j))))) 1) -
            Pi.single (some (finRotate 5 j)) 1 : Option (Fin 5) → ℝ) =
          Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j))))) 1 := by
      simpa using
        (pairMinusSingleton_eq_single (V := Option (Fin 5))
          (a := some (finRotate 5 j))
          (b := some (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j))))))
    have hraw :
        ((Pi.single (some (finRotate 5 j)) (1 : ℝ) +
              Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 j))))) 1) -
            Pi.single (some (finRotate 5 j)) 1 : Option (Fin 5) → ℝ) ∈
          (affineSpan ℝ F).direction := by
      simpa [p4, psucc, add_comm, add_left_comm, add_assoc] using
        hsub_mem hp4_mem_F hpsucc_mem_F
    simpa [hpair4] using hraw
  have hker_le :
      LinearMap.ker (dotProductLinearMap c) ≤ (affineSpan ℝ F).direction := by
    intro x hx
    have hxsum : x (some j) + x (some (finRotate 5 j)) + x none = 0 := by
      simpa [c, dotProductWheelEdge_apply, dotProductLinearMap_apply] using
        (LinearMap.mem_ker.mp hx)
    -- The lifted edge-kernel decomposition rewrites every kernel vector into the five witness
    -- directions.
    rw [wheelEdgeKernelDecomposition j x hxsum]
    have hsumSuccHub :
        x (some (finRotate 5 j)) •
              (Pi.single (some (finRotate 5 j)) (1 : ℝ) - Pi.single (some j) 1) +
            x none • (Pi.single none (1 : ℝ) - Pi.single (some j) 1) ∈
          (affineSpan ℝ F).direction :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hgenSucc) (Submodule.smul_mem _ _ hgenHub)
    have hsumSuccHub2 :
        x (some (finRotate 5 j)) •
              (Pi.single (some (finRotate 5 j)) (1 : ℝ) - Pi.single (some j) 1) +
            x none • (Pi.single none (1 : ℝ) - Pi.single (some j) 1) +
              x (some (finRotate 5 (finRotate 5 j))) •
                Pi.single (some (finRotate 5 (finRotate 5 j))) 1 ∈
          (affineSpan ℝ F).direction := by
      simpa [add_assoc] using
        Submodule.add_mem _ hsumSuccHub (Submodule.smul_mem _ _ hgen2)
    have hsumSuccHub23 :
        x (some (finRotate 5 j)) •
              (Pi.single (some (finRotate 5 j)) (1 : ℝ) - Pi.single (some j) 1) +
            x none • (Pi.single none (1 : ℝ) - Pi.single (some j) 1) +
              x (some (finRotate 5 (finRotate 5 j))) •
                Pi.single (some (finRotate 5 (finRotate 5 j))) 1 +
              x (some (finRotate 5 (finRotate 5 (finRotate 5 j)))) •
                Pi.single (some (finRotate 5 (finRotate 5 (finRotate 5 j)))) 1 ∈
          (affineSpan ℝ F).direction := by
      simpa [add_assoc] using
        Submodule.add_mem _ hsumSuccHub2 (Submodule.smul_mem _ _ hgen3)
    simpa [add_assoc] using
      Submodule.add_mem _ hsumSuccHub23 (Submodule.smul_mem _ _ hgen4)
  have hdir_eq :
      (affineSpan ℝ F).direction = LinearMap.ker (dotProductLinearMap c) :=
    le_antisymm hdir_le hker_le
  have hL_ne : dotProductLinearMap c ≠ 0 := by
    intro hL0
    have hvalue : dotProductLinearMap c pj = 1 := by
      simpa [dotProductLinearMap_apply] using hpj_eq
    have hzero : dotProductLinearMap c pj = 0 := by
      simpa [hL0]
    linarith
  have hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction = 5 := by
    calc
      Module.finrank ℝ (affineSpan ℝ F).direction
          = Module.finrank ℝ (LinearMap.ker (dotProductLinearMap c)) := by
              rw [hdir_eq]
      _ = 5 := by
        simpa using finrankKerEqCardSubOne
          (V := Option (Fin 5)) (L := dotProductLinearMap c) hL_ne
  have hP_dim :
      Module.finrank ℝ (affineSpan ℝ P).direction = 6 := by
    -- `STAB(W₅)` is full-dimensional in the ambient `ℝ⁶`.
    change Module.finrank ℝ (affineSpan ℝ STAB(fiveWheelGraph)).direction = 6
    rw [stableSetPolytopeAffineSpanEqTop (G := fiveWheelGraph),
      AffineSubspace.direction_top, finrank_top, Module.finrank_fintype_fun_eq_card]
    norm_num
  -- The oriented lifted edge face is nonempty, exposed, and has codimension one.
  rw [isFacetOf_iff]
  refine ⟨⟨pj, hpj_mem_F⟩, hF_exposed, ?_⟩
  rw [hF_dim, hP_dim]

/-- Part (5) of the current exercise. For every edge `v_jv_k` of `C₅`, the edge facet `x_j + x_k ≤ 1` lifts to
the facet `x_(v_j) + x_(v_k) + x_w ≤ 1` of `STAB(W₅)`. -/
theorem exercise_7_2_lifted_edge_facet
    {j k : Fin 5} (hjk : (cycleGraph 5).Adj j k) :
    IsFacetOf
      STAB(fiveWheelGraph)
      {x : Option (Fin 5) → ℝ |
        x ∈ STAB(fiveWheelGraph) ∧
          x (some j) + x (some k) + x none = 1} := by
  -- Route correction: first orient the cycle edge, then reuse the oriented lifted proof.
  rcases (cycleGraph_adj_iff_finRotate_five j k).1 hjk with hsucc | hpred
  · subst hsucc
    simpa using wheelEdgeFacetOriented j
  · subst hpred
    simpa [add_comm, add_left_comm, add_assoc] using wheelEdgeFacetOriented k

/-- Exercise 7.2 (6). The odd-cycle facet `∑_{j=1}^5 x_j ≤ 2` of `STAB(C₅)` lifts to the facet
`∑_{j=1}^5 x_(v_j) + 2 x_w ≤ 2` of `STAB(W₅)`. -/
theorem exercise_7_2_lifted_odd_cycle_facet :
    IsFacetOf
      STAB(fiveWheelGraph)
      {x : Option (Fin 5) → ℝ |
        x ∈ STAB(fiveWheelGraph) ∧
          (∑ j : Fin 5, x (some j)) + 2 * x none = 2} := by
  -- Route correction: mirror the completed `C₅` odd-cycle proof, but use the exact `W₅` sparse
  -- witnesses so the weighted decomposition applies without further transport.
  let P : Set (Option (Fin 5) → ℝ) := STAB(fiveWheelGraph)
  let F : Set (Option (Fin 5) → ℝ) :=
    {x : Option (Fin 5) → ℝ |
      x ∈ P ∧ (∑ j : Fin 5, x (some j)) + 2 * x none = 2}
  let c : Option (Fin 5) → ℝ := fun v ↦ match v with | none => (2 : ℝ) | some _ => 1
  let p02 : Option (Fin 5) → ℝ := Pi.single (some 0) (1 : ℝ) + Pi.single (some 2) 1
  let p13 : Option (Fin 5) → ℝ := Pi.single (some 1) (1 : ℝ) + Pi.single (some 3) 1
  let p24 : Option (Fin 5) → ℝ := Pi.single (some 2) (1 : ℝ) + Pi.single (some 4) 1
  let p30 : Option (Fin 5) → ℝ := Pi.single (some 3) (1 : ℝ) + Pi.single (some 0) 1
  let p41 : Option (Fin 5) → ℝ := Pi.single (some 4) (1 : ℝ) + Pi.single (some 1) 1
  let phub : Option (Fin 5) → ℝ := Pi.single none (1 : ℝ)
  have hvalid : ∀ ⦃x : Option (Fin 5) → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ 2 := by
    intro x hx
    -- The lifted odd-cycle inequality is valid because a stable set of `W₅` either contains the
    -- hub and nothing else, or avoids the hub and then has at most two cycle vertices.
    refine dotProductLeOfMemStableSetPolytope (G := fiveWheelGraph) ?_ hx
    intro s hs
    by_cases hnone : none ∈ s
    · have hcycle_not_mem : ∀ i : Fin 5, some i ∉ s := by
        intro i hi
        have hnot : ¬ fiveWheelGraph.Adj none (some i) := hs hnone hi (by simp)
        exact hnot (fiveWheelGraph_adj_hub i)
      have hvalue : c ⬝ᵥ stableSetIndicator s = 2 := by
        rw [dotProductWheelWeights_apply]
        simp [stableSetIndicator, hnone, hcycle_not_mem]
      linarith [hvalue]
    · have hs_card : (s.card : ℝ) ≤ 2 := by
        exact_mod_cast fiveWheel_indep_card_without_hub_le_two s hs hnone
      have hnone0 : stableSetIndicator s none = 0 :=
        stableSetIndicator_of_notMem hnone
      have hsum :
          (∑ i : Fin 5, stableSetIndicator s (some i)) = s.card := by
        simpa [Fintype.sum_option, hnone0, add_comm, add_left_comm, add_assoc] using
          (sum_stableSetIndicator_eq_card (V := Option (Fin 5)) s)
      have hvalue : c ⬝ᵥ stableSetIndicator s = s.card := by
        rw [dotProductWheelWeights_apply]
        simp [hsum, hnone0]
      linarith [hvalue, hs_card]
  have hp02_mem_P : p02 ∈ P := by
    -- The stable pair `{v₀, v₂}` is a tight lifted odd-cycle witness.
    simpa [P, p02] using wheelTwoStepPairPoint_memStableSetPolytope 0
  have hp13_mem_P : p13 ∈ P := by
    -- The stable pair `{v₁, v₃}` is the next tight witness.
    simpa [P, p13] using wheelTwoStepPairPoint_memStableSetPolytope 1
  have hp24_mem_P : p24 ∈ P := by
    -- The stable pair `{v₂, v₄}` is another tight witness.
    simpa [P, p24] using wheelTwoStepPairPoint_memStableSetPolytope 2
  have hp30_mem_P : p30 ∈ P := by
    -- The stable pair `{v₃, v₀}` continues the five-cycle of tight vertices.
    simpa [P, p30] using wheelTwoStepPairPoint_memStableSetPolytope 3
  have hp41_mem_P : p41 ∈ P := by
    -- The stable pair `{v₄, v₁}` closes the five-cycle of tight vertices.
    simpa [P, p41] using wheelTwoStepPairPoint_memStableSetPolytope 4
  have hphub_mem_P : phub ∈ P := by
    -- The hub singleton is the extra tight witness unique to `W₅`.
    simpa [P, phub] using wheelHubSinglePoint_memStableSetPolytope
  have hp02_mem_F : p02 ∈ F := by
    -- Every two-step stable pair has weighted sum `2`.
    exact ⟨hp02_mem_P, by
      simp [F, p02, Fin.sum_univ_five, Pi.single_apply]
      norm_num⟩
  have hp13_mem_F : p13 ∈ F := by
    -- The same weighted equality holds for `{v₁, v₃}`.
    exact ⟨hp13_mem_P, by
      simp [F, p13, Fin.sum_univ_five, Pi.single_apply]
      norm_num⟩
  have hp24_mem_F : p24 ∈ F := by
    -- The same weighted equality holds for `{v₂, v₄}`.
    exact ⟨hp24_mem_P, by
      simp [F, p24, Fin.sum_univ_five, Pi.single_apply]
      norm_num⟩
  have hp30_mem_F : p30 ∈ F := by
    -- The same weighted equality holds for `{v₃, v₀}`.
    exact ⟨hp30_mem_P, by
      simp [F, p30, Fin.sum_univ_five, Pi.single_apply]
      norm_num⟩
  have hp41_mem_F : p41 ∈ F := by
    -- The same weighted equality holds for `{v₄, v₁}`.
    exact ⟨hp41_mem_P, by
      simp [F, p41, Fin.sum_univ_five, Pi.single_apply]
      norm_num⟩
  have hphub_mem_F : phub ∈ F := by
    -- The hub singleton is also tight because it contributes weight `2`.
    exact ⟨hphub_mem_P, by simp [F, phub, Fin.sum_univ_five, Pi.single_apply]⟩
  have hp02_eq : c ⬝ᵥ p02 = 2 := by
    -- The lifted odd-cycle functional is tight on the witness `{v₀, v₂}`.
    rw [dotProductWheelWeights_apply]
    simp [p02, Fin.sum_univ_five, Pi.single_apply]
    norm_num
  have hF_exposed : IsExposed ℝ P F := by
    -- The weighted equality set is exposed by the lifted odd-cycle functional.
    simpa [F, c, dotProductWheelWeights_apply] using
      (equalitySetIsExposed (P := P) (c := c) (x₀ := p02) (δ := 2)
        hvalid hp02_mem_P hp02_eq)
  have hdir_le :
      (affineSpan ℝ F).direction ≤ LinearMap.ker (dotProductLinearMap c) := by
    -- Every direction inside the lifted face preserves the weighted equality.
    simpa [F, c, dotProductWheelWeights_apply] using
      (equalitySetDirectionLeKer (P := P) (c := c) (x₀ := p02) (δ := 2)
        hp02_eq)
  have hsub_mem :
      ∀ {x y : Option (Fin 5) → ℝ},
        x ∈ F → y ∈ F → x - y ∈ (affineSpan ℝ F).direction := by
    intro x y hx hy
    have hx_aff : x ∈ affineSpan ℝ F := mem_affineSpan ℝ hx
    have hy_aff : y ∈ affineSpan ℝ F := mem_affineSpan ℝ hy
    -- Subtracting tight witnesses records directions in the affine span of the face.
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hx_aff hy_aff
  have hgen40 :
      (Pi.single (some 4) (1 : ℝ) - Pi.single (some 0) 1 : Option (Fin 5) → ℝ) ∈
        (affineSpan ℝ F).direction := by
    -- Comparing `{v₂, v₄}` with `{v₀, v₂}` isolates `e₄ - e₀`.
    have hpair40 :
        (((Pi.single (some 2) (1 : ℝ) : Option (Fin 5) → ℝ) + Pi.single (some 4) 1) -
            (Pi.single (some 2) 1 + Pi.single (some 0) 1) : Option (Fin 5) → ℝ) =
          Pi.single (some 4) (1 : ℝ) - Pi.single (some 0) 1 := by
      simpa using
        (pairMinusPair_eq_single_sub_single (V := Option (Fin 5))
          (a := some 2) (b := some 4) (c := some 0))
    have hraw :
        (((Pi.single (some 2) (1 : ℝ) : Option (Fin 5) → ℝ) + Pi.single (some 4) 1) -
            (Pi.single (some 2) 1 + Pi.single (some 0) 1) : Option (Fin 5) → ℝ) ∈
          (affineSpan ℝ F).direction := by
      simpa [p24, p02, add_comm, add_left_comm, add_assoc] using hsub_mem hp24_mem_F hp02_mem_F
    simpa [hpair40] using hraw
  have hgen32 :
      (Pi.single (some 3) (1 : ℝ) - Pi.single (some 2) 1 : Option (Fin 5) → ℝ) ∈
        (affineSpan ℝ F).direction := by
    -- Comparing `{v₃, v₀}` with `{v₀, v₂}` isolates `e₃ - e₂`.
    have hpair32 :
        (((Pi.single (some 0) (1 : ℝ) : Option (Fin 5) → ℝ) + Pi.single (some 3) 1) -
            (Pi.single (some 0) 1 + Pi.single (some 2) 1) : Option (Fin 5) → ℝ) =
          Pi.single (some 3) (1 : ℝ) - Pi.single (some 2) 1 := by
      simpa using
        (pairMinusPair_eq_single_sub_single (V := Option (Fin 5))
          (a := some 0) (b := some 3) (c := some 2))
    simpa [p30, p02, add_comm, add_left_comm, add_assoc, hpair32] using
      hsub_mem hp30_mem_F hp02_mem_F
  have hgen12 :
      (Pi.single (some 1) (1 : ℝ) - Pi.single (some 2) 1 : Option (Fin 5) → ℝ) ∈
        (affineSpan ℝ F).direction := by
    -- Comparing `{v₄, v₁}` with `{v₂, v₄}` isolates `e₁ - e₂`.
    have hpair12 :
        (((Pi.single (some 4) (1 : ℝ) : Option (Fin 5) → ℝ) + Pi.single (some 1) 1) -
            (Pi.single (some 4) 1 + Pi.single (some 2) 1) : Option (Fin 5) → ℝ) =
          Pi.single (some 1) (1 : ℝ) - Pi.single (some 2) 1 := by
      simpa using
        (pairMinusPair_eq_single_sub_single (V := Option (Fin 5))
          (a := some 4) (b := some 1) (c := some 2))
    simpa [p41, p24, add_comm, add_left_comm, add_assoc, hpair12] using
      hsub_mem hp41_mem_F hp24_mem_F
  have hgen10 :
      (Pi.single (some 1) (1 : ℝ) - Pi.single (some 0) 1 : Option (Fin 5) → ℝ) ∈
        (affineSpan ℝ F).direction := by
    -- Comparing `{v₁, v₃}` with `{v₃, v₀}` isolates `e₁ - e₀`.
    have hpair10 :
        (((Pi.single (some 3) (1 : ℝ) : Option (Fin 5) → ℝ) + Pi.single (some 1) 1) -
            (Pi.single (some 3) 1 + Pi.single (some 0) 1) : Option (Fin 5) → ℝ) =
          Pi.single (some 1) (1 : ℝ) - Pi.single (some 0) 1 := by
      simpa using
        (pairMinusPair_eq_single_sub_single (V := Option (Fin 5))
          (a := some 3) (b := some 1) (c := some 0))
    simpa [p13, p30, add_comm, add_left_comm, add_assoc, hpair10] using
      hsub_mem hp13_mem_F hp30_mem_F
  have hgenHub :
      (Pi.single none (1 : ℝ) - Pi.single (some 0) 1 - Pi.single (some 2) 1 :
          Option (Fin 5) → ℝ) ∈
        (affineSpan ℝ F).direction := by
    -- Subtracting `{v₀, v₂}` from the hub singleton isolates the final lifted generator.
    have hpairHub :
        ((Pi.single none (1 : ℝ) - (Pi.single (some 0) 1 + Pi.single (some 2) 1) :
            Option (Fin 5) → ℝ)) =
          Pi.single none (1 : ℝ) - Pi.single (some 0) 1 - Pi.single (some 2) 1 := by
      simpa using
        (singleMinusPair_eq_single_sub_single_sub_single (V := Option (Fin 5))
          (a := none) (b := some 0) (c := some 2))
    have hraw :
        ((Pi.single none (1 : ℝ) - (Pi.single (some 0) 1 + Pi.single (some 2) 1) :
            Option (Fin 5) → ℝ)) ∈
          (affineSpan ℝ F).direction := by
      simpa [phub, p02, add_comm, add_left_comm, add_assoc] using
        hsub_mem hphub_mem_F hp02_mem_F
    simpa [hpairHub] using hraw
  have hker_le :
      LinearMap.ker (dotProductLinearMap c) ≤ (affineSpan ℝ F).direction := by
    intro x hx
    have hxsum : (∑ i : Fin 5, x (some i)) + 2 * x none = 0 := by
      simpa [c, dotProductWheelWeights_apply, dotProductLinearMap_apply] using
        (LinearMap.mem_ker.mp hx)
    -- The lifted weighted-sum decomposition rewrites every kernel vector into the five witness
    -- directions.
    rw [wheelWeightedSumZero_decomposition x hxsum]
    have hsum43 :
        x (some 4) • (Pi.single (some 4) (1 : ℝ) - Pi.single (some 0) 1) +
            x (some 3) • (Pi.single (some 3) (1 : ℝ) - Pi.single (some 2) 1) ∈
          (affineSpan ℝ F).direction :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hgen40) (Submodule.smul_mem _ _ hgen32)
    have hsum432 :
        x (some 4) • (Pi.single (some 4) (1 : ℝ) - Pi.single (some 0) 1) +
            x (some 3) • (Pi.single (some 3) (1 : ℝ) - Pi.single (some 2) 1) +
              (-x (some 2) - x (some 3) - x none) •
                (Pi.single (some 1) (1 : ℝ) - Pi.single (some 2) 1) ∈
          (affineSpan ℝ F).direction := by
      simpa [add_assoc] using
        Submodule.add_mem _ hsum43 (Submodule.smul_mem _ _ hgen12)
    have hsum4321 :
        x (some 4) • (Pi.single (some 4) (1 : ℝ) - Pi.single (some 0) 1) +
            x (some 3) • (Pi.single (some 3) (1 : ℝ) - Pi.single (some 2) 1) +
              (-x (some 2) - x (some 3) - x none) •
                (Pi.single (some 1) (1 : ℝ) - Pi.single (some 2) 1) +
              (x (some 1) + x (some 2) + x (some 3) + x none) •
                (Pi.single (some 1) (1 : ℝ) - Pi.single (some 0) 1) ∈
          (affineSpan ℝ F).direction := by
      simpa [add_assoc] using
        Submodule.add_mem _ hsum432 (Submodule.smul_mem _ _ hgen10)
    simpa [add_assoc] using
      Submodule.add_mem _ hsum4321 (Submodule.smul_mem _ _ hgenHub)
  have hdir_eq :
      (affineSpan ℝ F).direction = LinearMap.ker (dotProductLinearMap c) :=
    le_antisymm hdir_le hker_le
  have hL_ne : dotProductLinearMap c ≠ 0 := by
    intro hL0
    have hvalue : dotProductLinearMap c phub = 2 := by
      rw [dotProductLinearMap_apply, dotProductWheelWeights_apply]
      simp [phub]
    have hzero : dotProductLinearMap c phub = 0 := by
      simpa [hL0]
    linarith
  have hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction = 5 := by
    calc
      Module.finrank ℝ (affineSpan ℝ F).direction
          = Module.finrank ℝ (LinearMap.ker (dotProductLinearMap c)) := by
              rw [hdir_eq]
      _ = 5 := by
        simpa using finrankKerEqCardSubOne
          (V := Option (Fin 5)) (L := dotProductLinearMap c) hL_ne
  have hP_dim :
      Module.finrank ℝ (affineSpan ℝ P).direction = 6 := by
    -- `STAB(W₅)` is full-dimensional in the ambient `ℝ⁶`.
    change Module.finrank ℝ (affineSpan ℝ STAB(fiveWheelGraph)).direction = 6
    rw [stableSetPolytopeAffineSpanEqTop (G := fiveWheelGraph),
      AffineSubspace.direction_top, finrank_top, Module.finrank_fintype_fun_eq_card]
    norm_num
  -- The lifted odd-cycle equality face is nonempty, exposed, and has codimension one.
  rw [isFacetOf_iff]
  refine ⟨⟨p02, hp02_mem_F⟩, hF_exposed, ?_⟩
  rw [hF_dim, hP_dim]

end Exercise_7_2
