import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_15
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant

open SimpleGraph
open scoped Matrix

noncomputable section

section Exercise10_7

local notation "C₅" => (cycleGraph 5 : SimpleGraph (Fin 5))

/-- The unit edge-weight function for the five-cycle in Exercise 10.7. -/
def exercise_10_7_unit_edge_weight : Sym2 (Fin 5) → ℝ :=
  fun _ ↦ 1

/-- The unit edge-weight function on the five-cycle is constantly `1`. -/
@[simp] theorem exercise_10_7_unit_edge_weight_apply (e : Sym2 (Fin 5)) :
    exercise_10_7_unit_edge_weight e = 1 :=
  rfl

/-- The explicit Gram matrix coming from five unit vectors with consecutive angle `4π/5`. Its
edge entries realize the pentagon lower bound for the Goemans-Williamson relaxation. -/
def exercise_10_7_witness : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, -(1 + Real.sqrt 5) / 4, (Real.sqrt 5 - 1) / 4, (Real.sqrt 5 - 1) / 4,
      -(1 + Real.sqrt 5) / 4;
    -(1 + Real.sqrt 5) / 4, 1, -(1 + Real.sqrt 5) / 4, (Real.sqrt 5 - 1) / 4,
      (Real.sqrt 5 - 1) / 4;
    (Real.sqrt 5 - 1) / 4, -(1 + Real.sqrt 5) / 4, 1, -(1 + Real.sqrt 5) / 4,
      (Real.sqrt 5 - 1) / 4;
    (Real.sqrt 5 - 1) / 4, (Real.sqrt 5 - 1) / 4, -(1 + Real.sqrt 5) / 4, 1,
      -(1 + Real.sqrt 5) / 4;
    -(1 + Real.sqrt 5) / 4, (Real.sqrt 5 - 1) / 4, (Real.sqrt 5 - 1) / 4,
      -(1 + Real.sqrt 5) / 4, 1]

/-- Helper for Exercise 10.7: the unit vectors at angles `0, 4π/5, 8π/5, 12π/5, 16π/5`. -/
def exercise_10_7_pentagonVectors : Fin 5 → EuclideanSpace ℝ (Fin 2) :=
  fun i ↦
    WithLp.toLp 2
      (![Real.cos (4 * Real.pi * (i : ℝ) / 5), Real.sin (4 * Real.pi * (i : ℝ) / 5)] :
        Fin 2 → ℝ)

/-- Helper for Exercise 10.7: each Gram entry is the cosine of the angle difference between the
corresponding pentagon vectors. -/
lemma exercise_10_7_gram_entry (i j : Fin 5) :
    Matrix.gram ℝ exercise_10_7_pentagonVectors i j =
      Real.cos ((4 * Real.pi / 5) * ((j : ℝ) - i)) := by
  -- Expand the inner product in `ℝ²` and collapse it with the cosine-difference identity.
  rw [Matrix.gram_apply]
  simp [exercise_10_7_pentagonVectors, PiLp.inner_apply]
  rw [← Real.cos_sub]
  ring_nf

/-- Helper for Exercise 10.7: `cos (2π / 5)` gives the distance-two pentagon entry. -/
lemma exercise_10_7_cosTwoPiDivFive :
    Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  -- Reduce to the double-angle formula at `π / 5`.
  have hangle : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by
    ring
  rw [hangle, Real.cos_two_mul, Real.cos_pi_div_five]
  ring_nf
  norm_num
  ring_nf

/-- Helper for Exercise 10.7: `cos (4π / 5)` gives the adjacent pentagon entry. -/
lemma exercise_10_7_cosFourPiDivFive :
    Real.cos (4 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  -- Rewrite `4π/5` as `π - π/5` and use the exact value of `cos (π/5)`.
  have hangle : 4 * Real.pi / 5 = Real.pi - Real.pi / 5 := by
    ring
  rw [hangle, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

/-- Helper for Exercise 10.7: `cos (8π / 5)` is the same distance-two pentagon entry. -/
lemma exercise_10_7_cosEightPiDivFive :
    Real.cos (8 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  -- Move `8π/5` back to `2π/5` with the `2π - x` cosine identity.
  have hangle : 8 * Real.pi / 5 = 2 * Real.pi - 2 * Real.pi / 5 := by
    ring
  rw [hangle, Real.cos_two_pi_sub, exercise_10_7_cosTwoPiDivFive]

/-- Helper for Exercise 10.7: `cos (12π / 5)` repeats the distance-two pentagon entry. -/
lemma exercise_10_7_cosTwelvePiDivFive :
    Real.cos (12 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  -- Peel off one full turn and reuse the `2π/5` value.
  have hangle : 12 * Real.pi / 5 = 2 * Real.pi + 2 * Real.pi / 5 := by
    ring
  rw [hangle, add_comm, Real.cos_add_two_pi, exercise_10_7_cosTwoPiDivFive]

/-- Helper for Exercise 10.7: `cos (16π / 5)` repeats the adjacent pentagon entry. -/
lemma exercise_10_7_cosSixteenPiDivFive :
    Real.cos (16 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  -- Reduce `16π/5` to `6π/5 = π + π/5`, then use `cos (x + π) = -cos x`.
  have hangle : 16 * Real.pi / 5 = (Real.pi + Real.pi / 5) + 2 * Real.pi := by
    ring
  rw [hangle, Real.cos_add_two_pi]
  have hangle' : Real.pi + Real.pi / 5 = Real.pi / 5 + Real.pi := by
    ring
  rw [hangle', Real.cos_add_pi, Real.cos_pi_div_five]
  ring

/-- Helper for Exercise 10.7: the normalized cosine value used by `norm_num` for adjacent pairs. -/
lemma exercise_10_7_cosMulOne :
    Real.cos (4 * Real.pi / 5) = (-Real.sqrt 5 + -1) / 4 := by
  simpa [neg_add_rev] using exercise_10_7_cosFourPiDivFive

/-- Helper for Exercise 10.7: the normalized cosine value used by `norm_num` for distance-two
pairs. -/
lemma exercise_10_7_cosMulTwo :
    Real.cos (4 * Real.pi / 5 * 2) = (Real.sqrt 5 - 1) / 4 := by
  have hangle : 4 * Real.pi / 5 * 2 = 8 * Real.pi / 5 := by
    ring
  rw [hangle, exercise_10_7_cosEightPiDivFive]

/-- Helper for Exercise 10.7: the normalized cosine value used by `norm_num` for distance-three
pairs. -/
lemma exercise_10_7_cosMulThree :
    Real.cos (4 * Real.pi / 5 * 3) = (Real.sqrt 5 - 1) / 4 := by
  have hangle : 4 * Real.pi / 5 * 3 = 12 * Real.pi / 5 := by
    ring
  rw [hangle, exercise_10_7_cosTwelvePiDivFive]

/-- Helper for Exercise 10.7: the normalized cosine value used by `norm_num` for distance-four
pairs. -/
lemma exercise_10_7_cosMulFour :
    Real.cos (4 * Real.pi / 5 * 4) = (-Real.sqrt 5 + -1) / 4 := by
  have hangle : 4 * Real.pi / 5 * 4 = 16 * Real.pi / 5 := by
    ring
  rw [hangle]
  simpa [neg_add_rev] using exercise_10_7_cosSixteenPiDivFive

/-- Helper for Exercise 10.7: the explicit matrix literal is exactly the Gram matrix of the
regular pentagon vectors. -/
lemma exercise_10_7_witness_eq_gram :
    exercise_10_7_witness = Matrix.gram ℝ exercise_10_7_pentagonVectors := by
  -- Compare the explicit matrix entries against the exact cosine values on the 25 index pairs.
  ext i j
  fin_cases i <;> fin_cases j
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulOne
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulTwo
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulThree
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulFour
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulOne
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulOne
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulTwo
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulThree
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulTwo
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulOne
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulOne
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulTwo
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulThree
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulTwo
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulOne
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulOne
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulFour
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulThree
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulTwo
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]
    symm
    exact exercise_10_7_cosMulOne
  · rw [exercise_10_7_gram_entry]
    norm_num [exercise_10_7_witness]

/-- Helper for Exercise 10.7: adjacency in `C₅` forces the witness entry to be the pentagon edge
value `-(1 + Real.sqrt 5) / 4`. -/
lemma exercise_10_7_witness_entry_of_adj {i j : Fin 5} (h : (C₅).Adj i j) :
    exercise_10_7_witness i j = -(1 + Real.sqrt 5) / 4 := by
  -- Check the ten actual cycle edges directly; every non-edge case contradicts adjacency.
  fin_cases i <;> fin_cases j
  · exfalso
    simpa [SimpleGraph.cycleGraph_adj'] using h
  · simpa [exercise_10_7_witness]
  · exfalso
    rw [SimpleGraph.cycleGraph_adj'] at h
    change (3 : Nat) = 1 ∨ (2 : Nat) = 1 at h
    norm_num at h
  · exfalso
    rw [SimpleGraph.cycleGraph_adj'] at h
    change (2 : Nat) = 1 ∨ (3 : Nat) = 1 at h
    norm_num at h
  · simpa [exercise_10_7_witness]
  · simpa [exercise_10_7_witness]
  · exfalso
    simpa [SimpleGraph.cycleGraph_adj'] using h
  · simpa [exercise_10_7_witness]
  · exfalso
    rw [SimpleGraph.cycleGraph_adj'] at h
    change (3 : Nat) = 1 ∨ (2 : Nat) = 1 at h
    norm_num at h
  · exfalso
    rw [SimpleGraph.cycleGraph_adj'] at h
    change (2 : Nat) = 1 ∨ (3 : Nat) = 1 at h
    norm_num at h
  · exfalso
    rw [SimpleGraph.cycleGraph_adj'] at h
    change (2 : Nat) = 1 ∨ (3 : Nat) = 1 at h
    norm_num at h
  · simpa [exercise_10_7_witness]
  · exfalso
    simpa [SimpleGraph.cycleGraph_adj'] using h
  · simpa [exercise_10_7_witness]
  · exfalso
    rw [SimpleGraph.cycleGraph_adj'] at h
    change (3 : Nat) = 1 ∨ (2 : Nat) = 1 at h
    norm_num at h
  · exfalso
    rw [SimpleGraph.cycleGraph_adj'] at h
    change (3 : Nat) = 1 ∨ (2 : Nat) = 1 at h
    norm_num at h
  · exfalso
    rw [SimpleGraph.cycleGraph_adj'] at h
    change (2 : Nat) = 1 ∨ (3 : Nat) = 1 at h
    norm_num at h
  · simpa [exercise_10_7_witness]
  · exfalso
    simpa [SimpleGraph.cycleGraph_adj'] using h
  · simpa [exercise_10_7_witness]
  · simpa [exercise_10_7_witness]
  · exfalso
    rw [SimpleGraph.cycleGraph_adj'] at h
    change (3 : Nat) = 1 ∨ (2 : Nat) = 1 at h
    norm_num at h
  · exfalso
    rw [SimpleGraph.cycleGraph_adj'] at h
    change (2 : Nat) = 1 ∨ (3 : Nat) = 1 at h
    norm_num at h
  · simpa [exercise_10_7_witness]
  · exfalso
    simpa [SimpleGraph.cycleGraph_adj'] using h

/-- Helper for Exercise 10.7: every adjacent edge of `C₅` contributes the same Goemans-Williamson
edge term for the explicit witness. -/
lemma exercise_10_7_edgeTerm_of_adj {i j : Fin 5} (h : (cycleGraph 5).Adj i j) :
    ((2 : ℝ) - exercise_10_7_witness i j - exercise_10_7_witness j i) / 4 =
      (5 + Real.sqrt 5) / 8 := by
  -- Normalize both oriented witness entries along the edge, then simplify the scalar expression.
  rw [exercise_10_7_witness_entry_of_adj h, exercise_10_7_witness_entry_of_adj h.symm]
  ring

/-- Helper for Exercise 10.7: the five-cycle has exactly five edges. -/
lemma exercise_10_7_cycleEdgeFinsetCard :
    ((cycleGraph 5 : SimpleGraph (Fin 5)).edgeFinset).card = 5 := by
  -- Reuse the general cycle-edge count established earlier in Chapter 4.
  simpa [Fintype.card_fin] using
    (Exercise_4_15.cycleGraph_card_edgeSet (n := 5) (by norm_num))

/-- The explicit witness satisfies the canonical Goemans-Williamson feasibility conditions for the
unit-weight five-cycle. -/
theorem exercise_10_7_witness_feasible :
    goemans_williamson_feasible exercise_10_7_witness := by
  -- Route correction: certify positive semidefiniteness through the Gram-matrix factorization.
  refine goemans_williamson_feasible.mk ?_ ?_
  · rw [exercise_10_7_witness_eq_gram]
    exact Matrix.posSemidef_gram ℝ exercise_10_7_pentagonVectors
  · intro v
    -- The diagonal entries are visibly `1` in the explicit matrix literal.
    fin_cases v <;> rfl

/-- Evaluating the canonical Goemans-Williamson objective on the explicit witness gives the
pentagon value `5 (5 + √5) / 8`. -/
theorem exercise_10_7_witness_objective :
    goemans_williamson_objective C₅ exercise_10_7_unit_edge_weight exercise_10_7_witness =
      5 * (5 + Real.sqrt 5) / 8 := by
  classical
  have hedgeFinset :
      (letI : DecidableRel (C₅).Adj := Classical.decRel (C₅).Adj
       (C₅).edgeFinset) =
        (C₅).edgeFinset := by
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  -- Route correction: rewrite the objective once as an edge sum, then normalize each edge
  -- summand through adjacency before collapsing the constant sum.
  rw [goemans_williamson_objective_eq_sum, hedgeFinset]
  calc
    Finset.sum (C₅).edgeFinset
        (fun e ↦
          exercise_10_7_unit_edge_weight e *
            Sym2.lift
              ⟨fun u v : Fin 5 ↦
                  ((2 : ℝ) - exercise_10_7_witness u v - exercise_10_7_witness v u) / 4,
                by
                  intro u v
                  ring⟩
              e) =
        Finset.sum (C₅).edgeFinset (fun _ ↦ (5 + Real.sqrt 5) / 8) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          obtain ⟨p, rfl⟩ := Sym2.mk_surjective e
          rcases p with ⟨u, v⟩
          -- Turn edge membership into adjacency, then apply the constant edge-term formula.
          have hadj : (C₅).Adj u v := by
            simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
          simpa [Sym2.lift_mk, exercise_10_7_unit_edge_weight_apply] using
            exercise_10_7_edgeTerm_of_adj hadj
    _ = (((C₅).edgeFinset).card : ℝ) * ((5 + Real.sqrt 5) / 8) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = 5 * (5 + Real.sqrt 5) / 8 := by
      rw [exercise_10_7_cycleEdgeFinsetCard]
      ring

/-- The explicit witness realizes the pentagon value as an attainable Goemans-Williamson
objective value for the five-cycle `C₅` with unit edge weights. -/
theorem exercise_10_7_witness_mem_goemans_williamson_objective_values :
    5 * (5 + Real.sqrt 5) / 8 ∈
      goemans_williamson_objective_values C₅ exercise_10_7_unit_edge_weight := by
  refine ⟨exercise_10_7_witness, exercise_10_7_witness_feasible, ?_⟩
  exact exercise_10_7_witness_objective

/-- Exercise 10.7. For the five-cycle with unit edge weights, the standard Max-Cut semidefinite
relaxation has value at least `5 (5 + √5) / 8`. -/
theorem exercise_10_7_lower_bound :
    5 * (5 + Real.sqrt 5) / 8 ≤
      goemans_williamson_value C₅ exercise_10_7_unit_edge_weight := by
  -- Pass from the explicit attained value to the supremum that defines the relaxation value.
  rw [goemans_williamson_value_eq_sSup]
  exact
    le_csSup
      (goemansWilliamsonObjectiveValues_bddAbove (G := C₅) exercise_10_7_unit_edge_weight)
      exercise_10_7_witness_mem_goemans_williamson_objective_values

end Exercise10_7
