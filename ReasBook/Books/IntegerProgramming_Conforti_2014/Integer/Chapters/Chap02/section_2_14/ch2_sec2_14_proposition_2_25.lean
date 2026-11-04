/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Order.Bounds.Defs
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_55.NodeColoring
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_definition_2_55.StableSetCovering

public section

universe u

namespace SimpleGraph

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_25.lean:
a binary family of independent sets that covers every vertex bounds the chromatic number. -/
lemma chromaticNumber_le_indicatorSum_of_independentCover
    {V : Type u} {I : Type*} [Fintype I]
    (G : SimpleGraph V) (z : I → ℤ) (A : I → Set V)
    (hz : ∀ i, z i = 0 ∨ z i = 1)
    (hA : ∀ i, G.IsIndepSet (A i))
    (hcover : ∀ v, ∃ i, z i = 1 ∧ v ∈ A i) :
    (ENat.toNat G.chromaticNumber : ℤ) ≤ Finset.sum Finset.univ z := by
  classical
  -- Choose one selected independent set through each vertex.
  choose c hc_selected hc_mem using hcover
  have hproper :
      ∀ {v w : V}, G.Adj v w →
        (⟨c v, hc_selected v⟩ : {i : I // z i = 1}) ≠ ⟨c w, hc_selected w⟩ := by
    intro v w hvw heq
    have hc_eq : c v = c w := congrArg Subtype.val heq
    have hw_mem : w ∈ A (c v) := hc_eq ▸ hc_mem w
    exact (hA (c v)) (hc_mem v) hw_mem hvw.ne hvw
  let κ : G.Coloring {i : I // z i = 1} :=
    Coloring.mk (fun v ↦ ⟨c v, hc_selected v⟩) hproper
  have hchromatic :
      ENat.toNat G.chromaticNumber ≤ Fintype.card {i : I // z i = 1} :=
    ENat.toNat_le_of_le_coe κ.colorable.chromaticNumber_le
  have hsum :
      Finset.sum Finset.univ z = (Fintype.card {i : I // z i = 1} : ℤ) := by
    -- Binaryness identifies the objective sum with the selected-index cardinality.
    calc
      Finset.sum Finset.univ z =
          Finset.sum Finset.univ (fun i ↦ if z i = 1 then (1 : ℤ) else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            rcases hz i with hzero | hone
            · simp [hzero]
            · simp [hone]
      _ = (Fintype.card {i : I // z i = 1} : ℤ) := by
        rw [Finset.sum_boole]
        norm_cast
        exact (Fintype.card_subtype fun i : I ↦ z i = 1).symm
  -- Cast the chromatic lower bound only after the finite cardinality is fixed.
  rw [hsum]
  exact_mod_cast hchromatic

namespace StableSetColoring

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_25.lean:
every stable set of a finite graph is contained in a maximal stable set. -/
lemma exists_maximalStableSet_superset
    {V : Type u} [Fintype V] {G : SimpleGraph V} {s : Set V}
    (hs : G.IsIndepSet s) :
    ∃ S : maximalStableSets G, s ⊆ (S : Finset V) := by
  classical
  -- Maximize the independent set in the finite inclusion poset of vertex sets.
  obtain ⟨t, hst, ht⟩ := Finite.exists_le_maximal hs
  let T : Finset V := t.toFinite.toFinset
  have hT_coe : (T : Set V) = t := by
    simp only [T, Set.Finite.coe_toFinset]
  have hT_maximal : Maximal G.IsIndepSet (T : Set V) := by
    simpa only [hT_coe] using ht
  have hT_mem : T ∈ maximalStableSets G :=
    (mem_maximalStableSets_iff G T).2 hT_maximal
  have hsT : s ⊆ (T : Set V) := by
    simpa only [hT_coe] using hst
  exact ⟨⟨T, hT_mem⟩, hsT⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_25.lean:
a finite graph coloring yields a feasible maximal-stable-set cover with no larger objective. -/
lemma exists_feasible_objective_le_ofColoring
    {V : Type u} {C : Type*} [Fintype V] [Fintype C]
    {G : SimpleGraph V} (κ : G.Coloring C) :
    ∃ x : maximalStableSets G → ℤ,
      feasible G x ∧ objective x ≤ (Fintype.card C : ℤ) := by
  classical
  -- Extend every color class to a maximal stable set and select their finite image.
  have hextension :
      ∀ c : C, ∃ S : maximalStableSets G, κ.colorClass c ⊆ (S : Finset V) := by
    intro c
    exact exists_maximalStableSet_superset (κ.isIndepSet_colorClass c)
  choose S hS using hextension
  let selected : Finset (maximalStableSets G) := Finset.univ.image S
  let x : maximalStableSets G → ℤ := fun T ↦ if T ∈ selected then 1 else 0
  have hfeasible : feasible G x := by
    rw [feasible_iff]
    constructor
    · intro T
      by_cases hT : T ∈ selected
      · right
        simp only [x, if_pos hT]
      · left
        simp only [x, if_neg hT]
    · intro v
      have hvS : v ∈ (S (κ v) : Finset V) := hS (κ v) (κ.mem_colorClass v)
      have hcontaining : S (κ v) ∈ maximalStableSetsContaining G v :=
        mem_maximalStableSetsContaining_iff.2 hvS
      have hselected : S (κ v) ∈ selected := by
        simp only [selected, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨κ v, rfl⟩
      have hfilter :
          S (κ v) ∈ (maximalStableSetsContaining G v).filter (fun T ↦ T ∈ selected) :=
        Finset.mem_filter.2 ⟨hcontaining, hselected⟩
      have hcard_pos :
          0 < ((maximalStableSetsContaining G v).filter fun T ↦ T ∈ selected).card :=
        Finset.card_pos.mpr ⟨S (κ v), hfilter⟩
      have hsum :
          Finset.sum (maximalStableSetsContaining G v) x =
            (((maximalStableSetsContaining G v).filter fun T ↦ T ∈ selected).card : ℤ) := by
        simp only [x, Finset.sum_boole]
      rw [hsum]
      exact_mod_cast hcard_pos
  have hobjective : objective x = (selected.card : ℤ) := by
    -- The objective counts precisely the selected maximal stable sets.
    rw [objective_def]
    simp only [x, Finset.sum_boole, Finset.filter_univ_mem]
  have hselected_card : selected.card ≤ Fintype.card C := by
    simpa only [selected, Finset.card_univ] using (Finset.card_image_le :
      (Finset.univ.image S).card ≤ Finset.univ.card)
  refine ⟨x, hfeasible, ?_⟩
  rw [hobjective]
  exact_mod_cast hselected_card

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_25.lean:
every feasible maximal-stable-set cover has objective at least the chromatic number. -/
lemma chromaticNumber_le_objective_of_feasible
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    {x : maximalStableSets G → ℤ} (hx : feasible G x) :
    (ENat.toNat G.chromaticNumber : ℤ) ≤ objective x := by
  rw [feasible_iff] at hx
  have hcover :
      ∀ v : V, ∃ S : maximalStableSets G, x S = 1 ∧ v ∈ (S : Finset V) := by
    intro v
    have hsum_ne : Finset.sum (maximalStableSetsContaining G v) x ≠ 0 := by
      intro hsum_zero
      have hpositive := hx.2 v
      rw [hsum_zero] at hpositive
      exact (Int.not_lt_of_ge hpositive) Int.zero_lt_one
    obtain ⟨S, hS_mem, hS_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
    have hS_one : x S = 1 := by
      rcases hx.1 S with hS_zero | hS_one
      · exact (hS_ne hS_zero).elim
      · exact hS_one
    exact ⟨S, hS_one, mem_maximalStableSetsContaining_iff.1 hS_mem⟩
  have hindependent :
      ∀ S : maximalStableSets G, G.IsIndepSet ((S : Finset V) : Set V) := by
    intro S
    exact (mem_maximalStableSets_iff G S).1 S.property |>.1
  -- Apply the common independent-cover certificate, then expose the objective sum.
  rw [objective_def]
  exact chromaticNumber_le_indicatorSum_of_independentCover G x
    (fun S ↦ ((S : Finset V) : Set V)) hx.1 hindependent hcover

end StableSetColoring

namespace NodeColoring

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_25.lean:
recoloring along an embedding yields feasible node-color variables using at most the source
colors. -/
lemma exists_feasible_objective_le_ofRecoloring
    {V : Type u} {A C : Type*} [Finite V] [Fintype A] [Fintype C]
    {G : SimpleGraph V} (κ : G.Coloring A) (e : A ↪ C) :
    ∃ x : V → C → ℤ, ∃ y : C → ℤ,
      feasible G x y ∧ objective y ≤ (Fintype.card A : ℤ) := by
  classical
  -- Local instance justification (finite conversion): `feasible_iff` requires an enumeration.
  letI : Fintype V := Fintype.ofFinite V
  let selected : Finset C := Finset.univ.image e
  let x : V → C → ℤ := fun v c ↦ if e (κ v) = c then 1 else 0
  let y : C → ℤ := fun c ↦ if c ∈ selected then 1 else 0
  have hfeasible : feasible G x y := by
    -- Verify the five node-color constraints for the embedded coloring indicators.
    rw [feasible_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u v huv c
      by_cases huc : e (κ u) = c
      · have hvc : e (κ v) ≠ c := by
          intro hvc
          have hκ_eq : κ u = κ v := e.injective (huc.trans hvc.symm)
          exact κ.valid huv hκ_eq
        simp only [x, if_pos huc, if_neg hvc]
        omega
      · by_cases hvc : e (κ v) = c
        · simp only [x, if_neg huc, if_pos hvc]
          omega
        · simp only [x, if_neg huc, if_neg hvc]
          omega
    · intro v c
      by_cases hvc : e (κ v) = c
      · have hc_selected : c ∈ selected := by
          rw [← hvc]
          simp only [selected, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨κ v, rfl⟩
        simp only [x, y, if_pos hvc, if_pos hc_selected]
        exact le_rfl
      · by_cases hc_selected : c ∈ selected
        · simp only [x, y, if_neg hvc, if_pos hc_selected]
          omega
        · simp only [x, y, if_neg hvc, if_neg hc_selected]
          exact le_rfl
    · intro v
      rw [Finset.sum_eq_single (e (κ v))]
      · simp only [x, if_pos]
      · intro c hc hne
        simp only [x, if_neg hne.symm]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    · intro v c
      by_cases hvc : e (κ v) = c
      · right
        simp only [x, if_pos hvc]
      · left
        simp only [x, if_neg hvc]
    · intro c
      by_cases hc : c ∈ selected
      · right
        simp only [y, if_pos hc]
      · left
        simp only [y, if_neg hc]
  have hobjective : objective y = (selected.card : ℤ) := by
    -- The objective counts the image of the source palette embedding.
    rw [objective_def]
    simp only [y, Finset.sum_boole, Finset.filter_univ_mem]
  have hselected_card : selected.card = Fintype.card A := by
    simp only [selected, Finset.card_image_of_injective Finset.univ e.injective,
      Finset.card_univ]
  refine ⟨x, y, hfeasible, ?_⟩
  rw [hobjective, hselected_card]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_25.lean:
every feasible node-color solution has objective at least the chromatic number. -/
lemma chromaticNumber_le_objective_of_feasible
    {V : Type u} {C : Type*} [Finite V] [Fintype C]
    {G : SimpleGraph V} {x : V → C → ℤ} {y : C → ℤ}
    (hxy : feasible G x y) :
    (ENat.toNat G.chromaticNumber : ℤ) ≤ objective y := by
  -- Local instance justification (finite conversion): `feasible_iff` requires an enumeration.
  letI : Fintype V := Fintype.ofFinite V
  rw [feasible_iff] at hxy
  have hindependent : ∀ c : C, G.IsIndepSet {v : V | x v c = 1} := by
    intro c u hu v hv huv hadj
    simp only [Set.mem_setOf_eq] at hu hv
    have hadjacent := hxy.1 u v hadj c
    rw [hu, hv] at hadjacent
    omega
  have hcover : ∀ v : V, ∃ c : C, y c = 1 ∧ v ∈ {w : V | x w c = 1} := by
    intro v
    have hsum_ne : Finset.sum Finset.univ (x v) ≠ 0 := by
      rw [hxy.2.2.1 v]
      exact one_ne_zero
    obtain ⟨c, hc_mem, hc_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
    have hxc : x v c = 1 := by
      rcases hxy.2.2.2.1 v c with hxc_zero | hxc_one
      · exact (hc_ne hxc_zero).elim
      · exact hxc_one
    have hyc : y c = 1 := by
      have hlink := hxy.2.1 v c
      rcases hxy.2.2.2.2 c with hyc_zero | hyc_one
      · omega
      · exact hyc_one
    exact ⟨c, hyc, hxc⟩
  -- The selected used-color fibers form the common independent cover.
  rw [objective_def]
  exact chromaticNumber_le_indicatorSum_of_independentCover G y
    (fun c ↦ {v : V | x v c = 1}) hxy.2.2.2.2 hindependent hcover

end NodeColoring

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_25.lean.
Proposition 2.25 (1) [Equivalence to the chromatic number]. For a finite graph `G`, the
least objective value attained by the stable-set covering formulation from Definition 2.55 is the
chromatic number `ENat.toNat G.chromaticNumber`. -/
theorem stableSetColoring_optimalValue_eq_chromaticNumber
    {V : Type u} [Fintype V] (G : SimpleGraph V) :
    IsLeast (StableSetColoring.objectiveValues G) (ENat.toNat G.chromaticNumber : ℤ) := by
  classical
  -- Start with an optimal finite coloring and turn it into a stable-set cover.
  let κ : G.Coloring (Fin (ENat.toNat G.chromaticNumber)) :=
    (colorable_chromaticNumber_of_fintype G).some
  obtain ⟨x, hx_feasible, hx_upper⟩ :=
    StableSetColoring.exists_feasible_objective_le_ofColoring κ
  have hx_lower :
      (ENat.toNat G.chromaticNumber : ℤ) ≤ StableSetColoring.objective x :=
    StableSetColoring.chromaticNumber_le_objective_of_feasible hx_feasible
  have hx_eq :
      StableSetColoring.objective x = (ENat.toNat G.chromaticNumber : ℤ) := by
    apply le_antisymm
    · simpa only [Fintype.card_fin] using hx_upper
    · exact hx_lower
  constructor
  · -- The two bounds show that the constructed feasible cover attains the chromatic number.
    rw [StableSetColoring.mem_objectiveValues_iff]
    exact ⟨x, hx_feasible, hx_eq⟩
  · intro r hr
    rw [StableSetColoring.mem_objectiveValues_iff] at hr
    obtain ⟨y, hy_feasible, hy_eq⟩ := hr
    rw [← hy_eq]
    exact StableSetColoring.chromaticNumber_le_objective_of_feasible hy_feasible

/-- Companion theorem for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_25.lean.
Proposition 2.25 (2) [Equivalence to the chromatic number]. For a finite graph `G`, the
least objective value attained by the node-color formulation from Definition 2.55 with color index
type `Fin (Fintype.card V)` is the chromatic number `ENat.toNat G.chromaticNumber`. -/
theorem nodeColoring_optimalValue_eq_chromaticNumber
    {V : Type u} [Fintype V] (G : SimpleGraph V) :
    IsLeast
      (@NodeColoring.objectiveValues V (Fin (Fintype.card V)) _ G)
      (ENat.toNat G.chromaticNumber : ℤ) := by
  classical
  -- Embed an optimal palette into the vertex-sized palette used by the formulation.
  have hcard : ENat.toNat G.chromaticNumber ≤ Fintype.card V :=
    ENat.toNat_le_of_le_coe G.chromaticNumber_le_card
  have hfin_card :
      Fintype.card (Fin (ENat.toNat G.chromaticNumber)) ≤
        Fintype.card (Fin (Fintype.card V)) := by
    simpa only [Fintype.card_fin] using hcard
  let κ : G.Coloring (Fin (ENat.toNat G.chromaticNumber)) :=
    (colorable_chromaticNumber_of_fintype G).some
  let e : Fin (ENat.toNat G.chromaticNumber) ↪ Fin (Fintype.card V) :=
    (Function.Embedding.nonempty_of_card_le hfin_card).some
  obtain ⟨x, y, hxy_feasible, hy_upper⟩ :=
    NodeColoring.exists_feasible_objective_le_ofRecoloring κ e
  have hy_lower :
      (ENat.toNat G.chromaticNumber : ℤ) ≤ NodeColoring.objective y :=
    NodeColoring.chromaticNumber_le_objective_of_feasible hxy_feasible
  have hy_eq : NodeColoring.objective y = (ENat.toNat G.chromaticNumber : ℤ) := by
    apply le_antisymm
    · simpa only [Fintype.card_fin] using hy_upper
    · exact hy_lower
  constructor
  · -- The recolored indicators attain the lower bound exactly.
    rw [NodeColoring.mem_objectiveValues_iff]
    exact ⟨x, y, hxy_feasible, hy_eq⟩
  · intro r hr
    rw [NodeColoring.mem_objectiveValues_iff] at hr
    obtain ⟨x', y', hxy'_feasible, hy'_eq⟩ := hr
    rw [← hy'_eq]
    exact NodeColoring.chromaticNumber_le_objective_of_feasible hxy'_feasible

end SimpleGraph

end

#print axioms SimpleGraph.stableSetColoring_optimalValue_eq_chromaticNumber
#print axioms SimpleGraph.nodeColoring_optimalValue_eq_chromaticNumber
