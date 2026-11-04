/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Domain sampling note: the stable-set-polytope owner API is reused from
-- `Chap07.section_7_7.ch7_sec7_7_exercise_7_19`; this file only adds the downstream
-- full-dimensionality and clique-facet theorems for Example 3.28.

section Example_3_28

variable {V : Type} [Fintype V]

noncomputable local instance : DecidableEq V := Classical.decEq V

private lemma stableSetIndicator_empty :
    stableSetIndicator (∅ : Finset V) = 0 := by
  ext v
  simp [stableSetIndicator]

private lemma stableSetIndicator_singleton (v : V) :
    stableSetIndicator ({v} : Finset V) = Pi.single v 1 := by
  ext u
  by_cases huv : u = v
  · subst huv
    simp [stableSetIndicator]
  · simp [stableSetIndicator, huv]

private lemma stableSetIndicator_pair_of_ne {v w : V} (hvw : v ≠ w) :
    stableSetIndicator ({v, w} : Finset V) = Pi.single v 1 + Pi.single w 1 := by
  ext u
  by_cases huv : u = v
  · subst huv
    simp [stableSetIndicator, hvw]
  · by_cases huw : u = w
    · subst huw
      simp [stableSetIndicator, huv]
    · simp [stableSetIndicator, huv, huw]

variable (G : SimpleGraph V)

noncomputable local instance : DecidableRel G.Adj := Classical.decRel G.Adj

private lemma stableSetIndicator_mem_stableSetPolytope {s : Finset V} (hs : G.IsIndepSet s) :
    stableSetIndicator s ∈ stableSetPolytope G := by
  rw [stableSetPolytope_eq_convexHull]
  apply subset_convexHull
  rw [mem_stableSetVertices_iff]
  exact ⟨s, hs, rfl⟩

section FullDimensional

/-- Helper for Example 3.28: `0` together with the coordinate unit vectors is affinely independent
in `ℝ^V`. -/
private lemma affineIndependent_none_or_single :
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
  -- Affine independence reduces to linear independence of the vectors based at `none`.
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
  -- Reindex the standard basis by the obvious equivalence.
  rw [hvsub]
  exact (Pi.linearIndependent_single_one V ℝ).comp e he_injective

omit [Fintype V] in
/-- Example 3.28 (1): the stable set polytope is full-dimensional in `ℝ^V`. -/
theorem stableSetPolytope_affineSpan_eq_top [Finite V] :
    affineSpan ℝ (stableSetPolytope G) = ⊤ := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let p : Option V → V → ℝ :=
    fun o ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v (1 : ℝ))
  have hp : Set.range p ⊆ stableSetPolytope G := by
    intro x hx
    rcases hx with ⟨o, rfl⟩
    cases o with
    | none =>
        -- The origin is one of the stable-set vertices.
        have h0 : stableSetIndicator (∅ : Finset V) ∈ stableSetPolytope G :=
          stableSetIndicator_mem_stableSetPolytope G (by simp)
        simpa [stableSetIndicator_empty] using h0
    | some v =>
        -- Each singleton characteristic vector is also a stable-set vertex.
        have hv : stableSetIndicator ({v} : Finset V) ∈ stableSetPolytope G :=
          stableSetIndicator_mem_stableSetPolytope G (by simp)
        simpa [p, stableSetIndicator_singleton] using hv
  have hp_affine : AffineIndependent ℝ p := by
    -- The `Option V`-indexed family is exactly the origin plus the unit vectors.
    simpa [p] using
      (affineIndependent_none_or_single :
        AffineIndependent ℝ
          (fun o : Option V ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v (1 : ℝ))))
  have htop : affineSpan ℝ (Set.range p) = ⊤ := by
    -- The cardinality matches `finrank (V → ℝ) + 1`.
    have hcard : Fintype.card (Option V) = Fintype.card V + 1 := by
      simpa using (Fintype.card_option : Fintype.card (Option V) = Fintype.card V + 1)
    exact hp_affine.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simpa [Module.finrank_fintype_fun_eq_card] using hcard)
  have hmono : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ (stableSetPolytope G) :=
    affineSpan_mono ℝ hp
  -- A superset of a spanning affine-independent family also has full affine span.
  exact top_unique (by simpa [htop] using hmono)

end FullDimensional

section CliqueInequalities

private def cliqueLinearMap (K : Finset V) : (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ v ∈ K, LinearMap.proj v

private lemma cliqueLinearMap_apply (K : Finset V) (x : V → ℝ) :
    cliqueLinearMap K x = K.sum x := by
  simp [cliqueLinearMap]

private lemma sum_stableSetIndicator_mul (K : Finset V) (x : V → ℝ) :
    (∑ v, stableSetIndicator K v * x v) = K.sum x := by
  classical
  simp [stableSetIndicator, Finset.sum_ite_mem]

/-- Helper for Example 3.28: a stable set meets a clique in at most one vertex, so the clique
inequality is valid on each stable-set vertex. -/
private lemma clique_sum_stableSetIndicator_le_one
    {K s : Finset V} (hK : G.IsClique K) (hs : G.IsIndepSet s) :
    K.sum (fun v ↦ stableSetIndicator s v) ≤ 1 := by
  classical
  have hsum :
      K.sum (fun v ↦ stableSetIndicator s v) = ((K.filter fun v ↦ v ∈ s).card : ℝ) := by
    -- Summing the `0/1` coordinates counts the clique vertices that lie in `s`.
    have hfilter : K.filter (fun v ↦ v ∈ s) = K ∩ s := by
      ext v
      simp
    rw [hfilter]
    simp [stableSetIndicator]
  have hcard : (K.filter fun v ↦ v ∈ s).card ≤ 1 := by
    -- Two distinct vertices in the intersection would be both adjacent and nonadjacent.
    refine Finset.card_le_one_iff.2 ?_
    intro a b ha hb
    by_contra hab
    have haK : a ∈ K := (Finset.mem_filter.mp ha).1
    have hbK : b ∈ K := (Finset.mem_filter.mp hb).1
    have has : a ∈ s := (Finset.mem_filter.mp ha).2
    have hbs : b ∈ s := (Finset.mem_filter.mp hb).2
    exact (hs has hbs hab) (hK haK hbK hab)
  rw [hsum]
  exact_mod_cast hcard

private lemma clique_sum_le_one_of_mem_stableSetPolytope
    (K : Finset V) (hK : G.IsClique K) (x : V → ℝ)
    (hx : x ∈ stableSetPolytope G) :
    K.sum x ≤ 1 := by
  let H : Set (V → ℝ) := {y : V → ℝ | K.sum (fun v ↦ y v) ≤ 1}
  have hconvex : Convex ℝ H := by
    -- The target set is a linear half-space.
    simpa [H, cliqueLinearMap, LinearMap.proj_apply] using
      convex_halfSpace_le (cliqueLinearMap K).isLinear (1 : ℝ)
  -- It is enough to check the inequality on the stable-set vertices.
  have hsubset : convexHull ℝ (stableSetVertices G) ⊆ H := by
    refine convexHull_min ?_ hconvex
    intro y hy
    rw [mem_stableSetVertices_iff] at hy
    rcases hy with ⟨s, hs, rfl⟩
    exact clique_sum_stableSetIndicator_le_one G hK hs
  rw [stableSetPolytope_eq_convexHull] at hx
  exact hsubset hx

omit [Fintype V] in
attribute [local instance] Fintype.ofFinite in
/-- Example 3.28 (2): every clique inequality is valid on the stable set polytope. -/
theorem clique_inequality_valid_on_stableSetPolytope [Finite V]
    (K : Finset V) (hK : G.IsClique K) (x : V → ℝ)
    (hx : x ∈ stableSetPolytope G) :
    K.sum x ≤ 1 := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  exact clique_sum_le_one_of_mem_stableSetPolytope G K hK x hx

/-- Helper for Example 3.28: every vertex outside a maximal clique has a nonneighbor inside that
clique. -/
private lemma maximal_clique_exists_nonadjacent_mem
    {K : Finset V} {v : V} (hK : Maximal G.IsClique K) (hv : v ∉ K) :
    ∃ w ∈ K, ¬ G.Adj v w := by
  by_contra h
  have hclique : G.IsClique K := hK.prop
  have hv_adj : ∀ w ∈ K, G.Adj v w := by
    intro w hw
    by_contra hvw
    exact h ⟨w, hw, hvw⟩
  have hinsert : G.IsClique (insert v (↑K : Set V)) := by
    rw [SimpleGraph.isClique_insert_of_notMem]
    · exact ⟨hclique, fun w hw ↦ hv_adj w hw⟩
    · simpa using hv
  exact hv (hK.mem_of_prop_insert hinsert)

/-- Helper for Example 3.28: the characteristic vectors attached to a facet witness are linearly
independent. -/
private lemma clique_witness_linearIndependent
    {K : Finset V} {W : V → Finset V}
    (h_singleton : ∀ v, v ∈ K → W v = {v})
    (h_mem : ∀ v, v ∉ K → v ∈ W v)
    (h_pair : ∀ v, v ∉ K → ∃ w ∈ K, W v = {v, w}) :
    LinearIndependent ℝ (fun v ↦ stableSetIndicator (W v)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum v hv
  have hOutside : ∀ u ∈ s, u ∉ K → g u = 0 := by
    intro u hu huK
    have hcoord : ∑ t ∈ s, (g t • stableSetIndicator (W t) u) = 0 := by
      -- Evaluate the dependence relation at the outside coordinate `u`.
      simpa [Finset.sum_apply, Pi.smul_apply] using congrFun hsum u
    have hrest : ∀ t ∈ s, t ≠ u → g t • stableSetIndicator (W t) u = 0 := by
      intro t ht htu
      by_cases htK : t ∈ K
      · -- Clique vertices contribute only on their own coordinate.
        rw [h_singleton t htK]
        have hut : u ≠ t := htu.symm
        simp [stableSetIndicator, hut]
      · -- A different outside witness contains only its own outside coordinate
        -- and one clique vertex.
        obtain ⟨w, hwK, hpair⟩ := h_pair t htK
        have htw : t ≠ w := by
          intro htw_eq
          exact htK (htw_eq ▸ hwK)
        have huw : u ≠ w := by
          intro huw_eq
          exact huK (huw_eq ▸ hwK)
        rw [hpair, stableSetIndicator_pair_of_ne htw]
        simp [htu, huw]
    rw [Finset.sum_eq_single_of_mem u hu hrest] at hcoord
    have hself : stableSetIndicator (W u) u = 1 := by
      -- The witness for an outside vertex always contains that vertex.
      rw [stableSetIndicator]
      exact if_pos (h_mem u huK)
    simpa [hself] using hcoord
  by_cases hKv : v ∈ K
  · have hcoord : ∑ t ∈ s, (g t • stableSetIndicator (W t) v) = 0 := by
      -- Now evaluate at the clique coordinate `v`.
      simpa [Finset.sum_apply, Pi.smul_apply] using congrFun hsum v
    have hrest : ∀ t ∈ s, t ≠ v → g t • stableSetIndicator (W t) v = 0 := by
      intro t ht htv
      by_cases htK : t ∈ K
      · -- Distinct clique witnesses are different singleton coordinates.
        rw [h_singleton t htK]
        have hvt : v ≠ t := htv.symm
        simp [stableSetIndicator, hvt]
      · -- Outside witnesses were already eliminated from their own outside coordinates.
        rw [hOutside t ht htK, zero_smul]
    rw [Finset.sum_eq_single_of_mem v hv hrest] at hcoord
    have hself : stableSetIndicator (W v) v = 1 := by
      -- The clique witness at `v` is exactly `{v}`.
      rw [h_singleton v hKv]
      simp [stableSetIndicator]
    simpa [hself] using hcoord
  · exact hOutside v hv hKv

/-- Example 3.28 (3): if `K` is a maximal clique, then the clique inequality has `|V|`
affinely independent tight stable-set vertices. -/
private theorem maximal_clique_clique_inequality_witness
    {K : Finset V} (hK : Maximal G.IsClique K) :
    ∃ W : V → Finset V,
      (∀ v, G.IsIndepSet (W v)) ∧
      (∀ v, K.sum (fun u ↦ stableSetIndicator (W v) u) = 1) ∧
      AffineIndependent ℝ (fun v ↦ stableSetIndicator (W v)) := by
  classical
  have hpartner :
      ∀ v, v ∉ K → ∃ w ∈ K, ¬ G.Adj v w := fun v hv ↦
        maximal_clique_exists_nonadjacent_mem G hK hv
  choose partner partner_mem partner_nonadj using hpartner
  let witnessSets : V → Finset V := fun v ↦
    if hv : v ∈ K then {v} else {v, partner v hv}
  have hsingle : ∀ v, v ∈ K → witnessSets v = {v} := by
    intro v hv
    simp [witnessSets, hv]
  have hmem : ∀ v, v ∉ K → v ∈ witnessSets v := by
    intro v hv
    simp [witnessSets, hv]
  have hpair : ∀ v, v ∉ K → ∃ w ∈ K, witnessSets v = {v, w} := by
    intro v hv
    refine ⟨partner v hv, partner_mem v hv, ?_⟩
    simp [witnessSets, hv]
  have hindep : ∀ v, G.IsIndepSet (witnessSets v) := by
    intro v
    by_cases hv : v ∈ K
    · -- Clique vertices contribute singleton stable sets.
      rw [hsingle v hv]
      simp
    · -- Outside vertices are paired with a nonneighbor in the clique.
      have hneq : v ≠ partner v hv := by
        intro hEq
        exact hv (hEq ▸ partner_mem v hv)
      have hpairClique : Gᶜ.IsClique ({v, partner v hv} : Set V) := by
        rw [SimpleGraph.isClique_pair]
        intro hne
        simpa [SimpleGraph.compl_adj, hne] using partner_nonadj v hv
      have hset : witnessSets v = {v, partner v hv} := by
        simp [witnessSets, hv]
      rw [hset]
      simpa using hpairClique
  have htight : ∀ v, K.sum (fun u ↦ stableSetIndicator (witnessSets v) u) = 1 := by
    intro v
    by_cases hv : v ∈ K
    · -- A clique singleton hits the clique sum exactly once.
      rw [hsingle v hv, stableSetIndicator_singleton]
      simp [hv]
    · -- An outside witness contributes only through its chosen clique partner.
      have hneq : v ≠ partner v hv := by
        intro hEq
        exact hv (hEq ▸ partner_mem v hv)
      have hset : witnessSets v = {v, partner v hv} := by
        simp [witnessSets, hv]
      rw [hset, stableSetIndicator_pair_of_ne hneq]
      simp [Finset.sum_add_distrib, hv, partner_mem v hv]
  refine ⟨witnessSets, hindep, htight, ?_⟩
  -- Linear independence of the witness vectors implies affine independence.
  exact (clique_witness_linearIndependent hsingle hmem hpair).affineIndependent

section Facet

variable [Nonempty V]

/-- A maximal clique in a nonempty graph is nonempty. -/
private lemma maximal_clique_nonempty {K : Finset V}
    (hK : Maximal G.IsClique K) :
    K.Nonempty := by
  classical
  by_contra hK_empty
  obtain ⟨v⟩ := ‹Nonempty V›
  have hsingleton : G.IsClique ({v} : Set V) := by
    simp
  have hsubset : (↑K : Set V) ⊆ ({v} : Set V) := by
    simp [Finset.not_nonempty_iff_eq_empty.mp hK_empty]
  have hv : v ∈ (↑K : Set V) := by
    have hEq := hK.eq_of_subset hsingleton hsubset
    simpa [Finset.not_nonempty_iff_eq_empty.mp hK_empty] using
      congrArg (fun S : Set V ↦ v ∈ S) hEq
  simp [Finset.not_nonempty_iff_eq_empty.mp hK_empty] at hv

/-- If a valid inequality is tight at `x₀`, then its equality set is the exposed set cut out by
the corresponding continuous linear functional. -/
private lemma eq_set_eq_toExposed_of_mem
    {P : Set (V → ℝ)} {L : (V → ℝ) →ₗ[ℝ] ℝ} {δ : ℝ} {x₀ : V → ℝ}
    (hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ P → L x ≤ δ)
    (hx₀ : x₀ ∈ P) (hx₀_eq : L x₀ = δ) :
    {x : V → ℝ | x ∈ P ∧ L x = δ} =
      (⟨L, L.continuous_of_finiteDimensional⟩ : (V → ℝ) →L[ℝ] ℝ).toExposed P := by
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

/-- The coefficient vector `c` defines the linear functional `x ↦ c ⬝ᵥ x`. -/
private def dotProductLinearMap (c : V → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ v, c v • LinearMap.proj v

/-- `dotProductLinearMap c` evaluates as the dot product with `c`. -/
private lemma dotProductLinearMap_apply (c x : V → ℝ) :
    dotProductLinearMap c x = c ⬝ᵥ x := by
  simp [dotProductLinearMap, dotProduct]

/-- A nonempty valid equality face is exposed. -/
private lemma face_set_eq_toExposed_of_mem
    {P : Set (V → ℝ)} {c x₀ : V → ℝ} {δ : ℝ}
    (hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ δ)
    (hx₀ : x₀ ∈ face_set P c δ) :
    face_set P c δ =
      (⟨dotProductLinearMap c, (dotProductLinearMap c).continuous_of_finiteDimensional⟩ :
        (V → ℝ) →L[ℝ] ℝ).toExposed P := by
  have hx₀P : x₀ ∈ P := (mem_face_set_iff P c δ x₀).1 hx₀ |>.1
  have hx₀_eq : dotProductLinearMap c x₀ = δ := by
    simpa [dotProductLinearMap_apply] using (mem_face_set_iff P c δ x₀).1 hx₀ |>.2
  have hvalid' : ∀ ⦃x : V → ℝ⦄, x ∈ P → dotProductLinearMap c x ≤ δ := by
    intro x hx
    simpa [dotProductLinearMap_apply] using hvalid hx
  calc
    face_set P c δ = {x : V → ℝ | x ∈ P ∧ dotProductLinearMap c x = δ} := by
      ext x
      rw [mem_face_set_iff]
      simp [dotProductLinearMap_apply]
    _ = (⟨dotProductLinearMap c, (dotProductLinearMap c).continuous_of_finiteDimensional⟩ :
          (V → ℝ) →L[ℝ] ℝ).toExposed P := by
      exact eq_set_eq_toExposed_of_mem hvalid' hx₀P hx₀_eq

/-- Example 3.28 (3) private codimension calculation: for a maximal clique, the clique equality
face has affine-span direction of dimension `|V| - 1`. -/
private lemma maximal_clique_clique_face_finrank
    (K : Finset V) (hK : Maximal G.IsClique K) :
    Module.finrank ℝ
        (affineSpan ℝ (face_set (stableSetPolytope G) (stableSetIndicator K) 1)).direction =
      Fintype.card V - 1 := by
  let F : Set (V → ℝ) := face_set (stableSetPolytope G) (stableSetIndicator K) 1
  obtain ⟨W, hW_indep, hW_tight, hW_affine⟩ := maximal_clique_clique_inequality_witness G hK
  let p : V → V → ℝ := fun v ↦ stableSetIndicator (W v)
  have hp_mem : Set.range p ⊆ F := by
    intro x hx
    rcases hx with ⟨v, rfl⟩
    rw [mem_face_set_iff]
    refine ⟨stableSetIndicator_mem_stableSetPolytope G (hW_indep v), ?_⟩
    simpa [dotProduct, p, sum_stableSetIndicator_mul] using hW_tight v
  have hspan_le : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ F :=
    affineSpan_mono ℝ hp_mem
  have hp_dim :
      Module.finrank ℝ (affineSpan ℝ (Set.range p)).direction = Fintype.card V - 1 := by
    rw [direction_affineSpan]
    exact hW_affine.finrank_vectorSpan <|
      (Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)).symm
  have hface_dim_lower :
      Fintype.card V - 1 ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by
    simpa [hp_dim] using
      Submodule.finrank_mono (AffineSubspace.direction_le hspan_le)
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hK_nonempty : K.Nonempty := maximal_clique_nonempty G hK
  have hLinear_nonzero : cliqueLinearMap K ≠ 0 := by
    rcases hK_nonempty with ⟨v, hv⟩
    intro hzero
    have hvalue := congrArg (fun L : (V → ℝ) →ₗ[ℝ] ℝ ↦ L (Pi.single v (1 : ℝ))) hzero
    simp [cliqueLinearMap, hv] at hvalue
  have hker_dim :
      Module.finrank ℝ (LinearMap.ker (cliqueLinearMap K)) = Fintype.card V - 1 := by
    have hker_add_one :
        Module.finrank ℝ (LinearMap.ker (cliqueLinearMap K)) + 1 = Fintype.card V := by
      let f : Module.Dual ℝ (V → ℝ) := cliqueLinearMap K
      have hf : f ≠ 0 := by
        simpa [f] using hLinear_nonzero
      simpa [f, Module.finrank_fintype_fun_eq_card] using f.finrank_ker_add_one_of_ne_zero hf
    exact Nat.eq_sub_of_add_eq hker_add_one
  have hdir_le_ker :
      (affineSpan ℝ F).direction ≤ LinearMap.ker (cliqueLinearMap K) := by
    let H : AffineSubspace ℝ (V → ℝ) :=
      AffineSubspace.mk' (p v₀) (LinearMap.ker (cliqueLinearMap K))
    have hF_le_H : F ⊆ H := by
      intro x hx
      change x ∈ H
      rw [AffineSubspace.mem_mk']
      refine LinearMap.mem_ker.2 ?_
      have hx_eq : cliqueLinearMap K x = 1 := by
        rw [mem_face_set_iff] at hx
        simpa [dotProduct, cliqueLinearMap_apply, sum_stableSetIndicator_mul] using hx.2
      have hv₀_eq : cliqueLinearMap K (p v₀) = 1 := by
        simpa [dotProduct, p, cliqueLinearMap_apply, sum_stableSetIndicator_mul] using hW_tight v₀
      simp [vsub_eq_sub, hx_eq, hv₀_eq]
    have h_aff_le : affineSpan ℝ F ≤ H := (affineSpan_le).2 hF_le_H
    simpa [H] using AffineSubspace.direction_le h_aff_le
  have hface_dim_upper :
      Module.finrank ℝ (affineSpan ℝ F).direction ≤ Fintype.card V - 1 := by
    simpa [hker_dim] using Submodule.finrank_mono hdir_le_ker
  exact le_antisymm hface_dim_upper hface_dim_lower

end Facet
end CliqueInequalities

end Example_3_28

section Example_3_28

variable {V : Type} (G : SimpleGraph V) [Nonempty V]

noncomputable local instance : DecidableEq V := Classical.decEq V

attribute [local instance] Fintype.ofFinite in
/-- Example 3.28 (3): if `K` is a maximal clique, then the clique equality face is a facet of the
stable set polytope. -/
theorem maximal_clique_clique_face_isFacetOf [Finite V]
    (K : Finset V) (hK : Maximal G.IsClique K) :
    IsFacetOf (stableSetPolytope G)
      (face_set (stableSetPolytope G) (stableSetIndicator K) 1) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let F : Set (V → ℝ) := face_set (stableSetPolytope G) (stableSetIndicator K) 1
  have hfacetDef :
      facet_defining_inequality (stableSetPolytope G) (stableSetIndicator K) 1 :=
    (exercise_7_19_clique_inequality_facet_defining_iff_maximal_clique G K hK.prop).2 hK
  have hF_nonempty : F.Nonempty := by
    simpa [F] using hfacetDef.facet.nonempty
  have hF_exposed : IsExposed ℝ (stableSetPolytope G) F := by
    rcases hfacetDef.facet.eq_face with ⟨c, δ, hvalid, hface_eq⟩
    rcases hfacetDef.facet.nonempty with ⟨x₀, hx₀⟩
    have hx₀_face : x₀ ∈ face_set (stableSetPolytope G) c δ := by
      simpa [F, hface_eq] using hx₀
    have hface_exposed :
        IsExposed ℝ (stableSetPolytope G) (face_set (stableSetPolytope G) c δ) := by
      rw [face_set_eq_toExposed_of_mem hvalid hx₀_face]
      exact ContinuousLinearMap.toExposed.isExposed
    simpa [F, hface_eq] using hface_exposed
  have hface_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction = Fintype.card V - 1 := by
    simpa [F] using maximal_clique_clique_face_finrank G K hK
  have hpoly_dim :
      Module.finrank ℝ (affineSpan ℝ (stableSetPolytope G)).direction = Fintype.card V := by
    rw [stableSetPolytope_affineSpan_eq_top G, AffineSubspace.direction_top,
      finrank_top, Module.finrank_fintype_fun_eq_card]
  refine ⟨hF_nonempty, hF_exposed, ?_⟩
  rw [hface_dim, hpoly_dim]
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)

end Example_3_28
