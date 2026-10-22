/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_47
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.BondPercolationAPI
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_31
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_39
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Example_19_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_30
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe v w

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/- `source-facing`: this file owns the textbook recurrence statement for simple random walks on
subgraphs of the square lattice.
`core/canonical`: recurrence is expressed through `IsRecurrentMarkovChain`, the discrete kernel
owner `discreteMatrixKernel`, the graph-walk owner `IsSimpleRandomWalk`, the conductance owner
`conductanceTransitionMatrix`, and the existing lattice-graph owner `latticeGraph 2`.
`bridge/view`: the full square-lattice walk is used only through the canonical conductance
normalization of the unit edge weights `simpleGraphWeights (latticeGraph 2)` in order to feed the
Chapter 17 recurrence theorem into the Chapter 19 subgraph monotonicity theorem. -/

/-- Helper for Example 19.29: the ambient square-lattice transition matrix is the conductance
normalization of the unit nearest-neighbor weights. -/
private abbrev squareLatticeTransitionMatrix : LatticePoint 2 → LatticePoint 2 → ℝ≥0∞ :=
  conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))

-- Proof sketch: each square-lattice vertex has exactly four nearest neighbors, so the row sum is
-- `1`, and the conductance-normalized unit-edge walk is precisely the simple random walk on
-- `latticeGraph 2`.
/-- Helper for Example 19.29: in `ℤ²`, adjacency is exactly one step in one of the four coordinate
directions. -/
private theorem squareLattice_adj_iff (x y : LatticePoint 2) :
    (latticeGraph 2).Adj x y ↔
      y = x + Pi.single 0 (1 : ℤ) ∨
        y = x + Pi.single 0 (-1 : ℤ) ∨
          y = x + Pi.single 1 (1 : ℤ) ∨
            y = x + Pi.single 1 (-1 : ℤ) := by
  have hupdate :
      (latticeGraph 2).Adj x y ↔
        ∃ i : Fin 2, y = Function.update x i (x i + 1) ∨ y = Function.update x i (x i - 1) := by
    rw [latticeGraph_adj_iff]
    constructor
    · intro hxy
      rcases hxy with ⟨i, hi, hcoord⟩
      rcases Int.natAbs_eq_iff.mp hi with hdiff | hdiff
      · refine ⟨i, Or.inr ?_⟩
        funext j
        by_cases hj : j = i
        · subst hj
          simp
          omega
        · simp [Function.update, hj, hcoord j hj]
      · refine ⟨i, Or.inl ?_⟩
        funext j
        by_cases hj : j = i
        · subst hj
          simp
          omega
        · simp [Function.update, hj, hcoord j hj]
    · rintro ⟨i, rfl | rfl⟩
      · refine ⟨i, ?_, ?_⟩
        · simp
        · intro j hj
          simp [Function.update, hj]
      · refine ⟨i, ?_, ?_⟩
        · simp
        · intro j hj
          simp [Function.update, hj]
  constructor
  · intro hxy
    rcases hupdate.1 hxy with ⟨i, hy | hy⟩
    · fin_cases i
      · left
        -- Proof comment: coordinate `0` with increment `+1` is the positive first basis step.
        ext j
        fin_cases j <;> simp [hy]
      · right
        right
        left
        -- Proof comment: coordinate `1` with increment `+1` is the positive second basis step.
        ext j
        fin_cases j <;> simp [hy]
    · fin_cases i
      · right
        left
        -- Proof comment: coordinate `0` with increment `-1` is the negative first basis step.
        ext j
        fin_cases j <;> simp [hy, sub_eq_add_neg]
      · right
        right
        right
        -- Proof comment: coordinate `1` with increment `-1` is the negative second basis step.
        ext j
        fin_cases j <;> simp [hy, sub_eq_add_neg]
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨0, by simp, ?_⟩
      intro j hj
      fin_cases j
      · exact (hj rfl).elim
      · simp
    · refine ⟨0, by simp, ?_⟩
      intro j hj
      fin_cases j
      · exact (hj rfl).elim
      · simp
    · refine ⟨1, by simp, ?_⟩
      intro j hj
      fin_cases j
      · simp
      · exact (hj rfl).elim
    · refine ⟨1, by simp, ?_⟩
      intro j hj
      fin_cases j
      · simp
      · exact (hj rfl).elim

/-- Helper for Example 19.29: square-lattice adjacency depends only on the increment `y - x`. -/
private theorem squareLattice_adj_sub_iff (x y : LatticePoint 2) :
    (latticeGraph 2).Adj x y ↔ (latticeGraph 2).Adj 0 (y - x) := by
  rw [latticeGraph_adj_iff, latticeGraph_adj_iff]
  constructor
  · rintro ⟨i, hi, hsame⟩
    refine ⟨i, ?_, ?_⟩
    · -- Proof comment: the distinguished coordinate difference is unchanged by translating the
      -- edge to the origin.
      change Int.natAbs (0 - (y i - x i)) = 1
      have hdiff : (0 : ℤ) - (y i - x i) = x i - y i := by
        omega
      rw [hdiff]
      exact hi
    · intro j hj
      -- Proof comment: equal non-distinguished coordinates become zero increments after
      -- subtracting `x`.
      change (0 : ℤ) = y j - x j
      have hxy : x j = y j := hsame j hj
      have hzero : y j - x j = 0 := by
        omega
      simpa using hzero.symm
  · rintro ⟨i, hi, hsame⟩
    refine ⟨i, ?_, ?_⟩
    · -- Proof comment: translating the origin-based increment back to `x` recovers the original
      -- edge difference.
      change Int.natAbs (x i - y i) = 1
      have hdiff : x i - y i = (0 : ℤ) - (y i - x i) := by
        omega
      rw [hdiff]
      exact hi
    · intro j hj
      -- Proof comment: zero increment away from the distinguished coordinate means the original
      -- endpoints agree there.
      have hzero : (0 : ℤ) = y j - x j := by
        change (0 : ℤ) = (y - x) j
        simpa using hsame j hj
      omega

/-- Helper for Example 19.29: the square-lattice unit weights are translation invariant. -/
private theorem squareLatticeWeight_translationInvariant (x y : LatticePoint 2) :
    simpleGraphWeights (latticeGraph 2) x y =
      simpleGraphWeights (latticeGraph 2) 0 (y - x) := by
  -- Proof comment: unit edge weights are just adjacency indicators, and adjacency only depends on
  -- the increment `y - x`.
  simp [simpleGraphWeights, squareLattice_adj_sub_iff]

/-- Helper for Example 19.29: the origin has four unit-conductance neighbors in the square
lattice. -/
private theorem squareLatticeConductance_zero :
    conductance (simpleGraphWeights (latticeGraph 2)) 0 = 4 := by
  let dirs : Finset (LatticePoint 2) :=
    {Pi.single 0 (1 : ℤ), Pi.single 0 (-1 : ℤ), Pi.single 1 (1 : ℤ), Pi.single 1 (-1 : ℤ)}
  have hzero :
      ∀ y : LatticePoint 2, y ∉ dirs → simpleGraphWeights (latticeGraph 2) 0 y = 0 := by
    intro y hy
    have hNotAdj : ¬ (latticeGraph 2).Adj 0 y := by
      intro hadj
      rcases (squareLattice_adj_iff 0 y).1 hadj with hy' | hy' | hy' | hy'
      · exact hy (by simp [dirs, hy'])
      · exact hy (by simp [dirs, hy'])
      · exact hy (by simp [dirs, hy'])
      · exact hy (by simp [dirs, hy'])
    -- Proof comment: away from the four cardinal directions, the unit edge weight is zero.
    simp [simpleGraphWeights, hNotAdj]
  have hadjPos0 : (latticeGraph 2).Adj 0 (Pi.single 0 (1 : ℤ)) := by
    exact (squareLattice_adj_iff 0 _).2 (by left; simp)
  have hadjNeg0 : (latticeGraph 2).Adj 0 (Pi.single 0 (-1 : ℤ)) := by
    exact (squareLattice_adj_iff 0 _).2 (by right; left; simp)
  have hadjPos1 : (latticeGraph 2).Adj 0 (Pi.single 1 (1 : ℤ)) := by
    exact (squareLattice_adj_iff 0 _).2 (by right; right; left; simp)
  have hadjNeg1 : (latticeGraph 2).Adj 0 (Pi.single 1 (-1 : ℤ)) := by
    exact (squareLattice_adj_iff 0 _).2 (by right; right; right; simp)
  -- Proof comment: only the four cardinal neighbors contribute to the conductance at the origin,
  -- and each contributing weight is exactly `1`.
  rw [conductance, tsum_eq_sum (s := dirs) hzero]
  have hadjDir : ∀ z : LatticePoint 2, z ∈ dirs → (latticeGraph 2).Adj 0 z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hadjPos0
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hadjNeg0
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hadjPos1
    rcases Finset.mem_singleton.1 hz with rfl
    exact hadjNeg1
  have hdirs : dirs.card = 4 := by
    decide
  have hsumSimple :
      dirs.sum (fun b ↦ simpleGraphWeights (latticeGraph 2) 0 b) =
        dirs.sum (fun _ ↦ (1 : ℝ≥0∞)) := by
    refine Finset.sum_congr rfl ?_
    intro b hb
    simp [simpleGraphWeights, hadjDir b hb]
  have hsumCard : dirs.sum (fun _ ↦ (1 : ℝ≥0∞)) = dirs.card := by
    simp
  simpa using hsumSimple.trans <| hsumCard.trans <| by
    exact_mod_cast hdirs

/-- Helper for Example 19.29: every square-lattice row has total conductance `4` by translation
from the origin. -/
private theorem squareLatticeConductance_eq_four (x : LatticePoint 2) :
    conductance (simpleGraphWeights (latticeGraph 2)) x = 4 := by
  rw [conductance]
  have hshift :
      ∑' y : LatticePoint 2, simpleGraphWeights (latticeGraph 2) x y =
        ∑' y : LatticePoint 2, simpleGraphWeights (latticeGraph 2) x (y + x) := by
    simpa [Equiv.coe_addRight] using
      ((Equiv.addRight x).tsum_eq
        (f := fun y : LatticePoint 2 ↦ simpleGraphWeights (latticeGraph 2) x y)).symm
  rw [hshift]
  -- Proof comment: translating the whole row by `x` reduces it to the origin row.
  have hpoint :
      (fun y : LatticePoint 2 ↦ simpleGraphWeights (latticeGraph 2) x (y + x)) =
        fun y : LatticePoint 2 ↦ simpleGraphWeights (latticeGraph 2) 0 y := by
    funext y
    rw [squareLatticeWeight_translationInvariant]
    simp [sub_eq_add_neg, add_assoc, add_comm]
  rw [hpoint]
  exact squareLatticeConductance_zero
private theorem squareLatticeKernel_isSimpleRandomWalk :
    IsSimpleRandomWalk
      (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)))
      (latticeGraph 2) := by
  -- Proof comment: Example 19.10 turns the unit-conductance normalization into the simple random
  -- walk once symmetry, finiteness, and positivity of the conductance are available.
  refine conductanceTransitionMatrix_isRandomWalkWithWeights ?_ ?_ ?_
  · exact simpleGraphWeights_symmetric (latticeGraph 2)
  · intro x
    norm_num [squareLatticeConductance_eq_four x]
  · intro x
    norm_num [squareLatticeConductance_eq_four x]

-- Proof sketch: adjacency in `latticeGraph 2` depends only on the increment `y - x`, so the
-- normalized unit-edge walk does as well.
private theorem squareLatticeKernel_translationInvariant :
    IsTranslationInvariantStepMatrix
      (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))) := by
  intro x y
  -- Proof comment: the normalized transition entry depends only on the translated unit weight,
  -- and every row has the same conductance `4`.
  rw [conductanceTransitionMatrix_apply, conductanceTransitionMatrix_apply,
    squareLatticeConductance_eq_four x, squareLatticeConductance_eq_four 0,
    squareLatticeWeight_translationInvariant]

/-- Helper for Example 19.29: the ambient square-lattice transition matrix is stochastic. -/
private theorem squareLatticeKernel_isStochasticMatrix :
    IsStochasticMatrix squareLatticeTransitionMatrix := by
  -- Proof comment: Example 19.10 reduces stochasticity to finite positive row conductance, and
  -- each square-lattice row has conductance `4`.
  simpa [squareLatticeTransitionMatrix] using
    (conductanceTransitionMatrix_isStochastic
      (C := simpleGraphWeights (latticeGraph 2))
      (hC_finite := fun x ↦ by
        norm_num [squareLatticeConductance_eq_four x])
      (hC_pos := fun x ↦ by
        norm_num [squareLatticeConductance_eq_four x]))

/-- Helper for Example 19.29: the ambient square-lattice one-step matrix defines a Markov kernel
after passing to the canonical discrete kernel owner. -/
private instance squareLatticeDiscreteKernel_isMarkovKernel :
    IsMarkovKernel (discreteMatrixKernel squareLatticeTransitionMatrix) :=
  discreteMatrixKernel_isMarkovKernel _ squareLatticeKernel_isStochasticMatrix

/-- Helper for Example 19.29: the canonical one-step law on `ℤ²` chooses one coordinate and one
sign uniformly, so its support is exactly the four cardinal unit vectors. -/
private noncomputable def squareLatticeStepPMF : PMF (LatticePoint 2) :=
  (PMF.uniformOfFintype (Bool × Fin 2)).map
    (fun s ↦ if s.1 then Pi.single s.2 (1 : ℤ) else Pi.single s.2 (-1))

-- Proof sketch: from the origin, the four nearest-neighbor moves in the coordinate directions
-- each occur with probability `1 / 4`, matching `symmetricSimpleRandomWalkStepPMF 2`.
private theorem squareLatticeKernel_row_zero (y : LatticePoint 2) :
    conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)) 0 y =
      if (latticeGraph 2).Adj 0 y then 1 / 4 else 0 := by
  -- Proof comment: at the origin the conductance walk is the unit adjacency indicator normalized
  -- by the total conductance `4`.
  rw [conductanceTransitionMatrix_apply, squareLatticeConductance_eq_four 0]
  by_cases hy : (latticeGraph 2).Adj 0 y
  · simp [simpleGraphWeights, hy]
  · simp [simpleGraphWeights, hy]

/-- Helper for Example 19.29: the square-lattice origin row vanishes away from the four cardinal
neighbors. -/
private theorem squareLatticeKernel_row_zero_eq_zero_of_not_cardinal
    (y : LatticePoint 2)
    (hy :
      y ∉ ({Pi.single 0 (1 : ℤ), Pi.single 0 (-1 : ℤ), Pi.single 1 (1 : ℤ),
        Pi.single 1 (-1 : ℤ)} : Finset (LatticePoint 2))) :
    conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)) 0 y = 0 := by
  have hNotAdj : ¬ (latticeGraph 2).Adj 0 y := by
    intro hadj
    rcases (squareLattice_adj_iff 0 y).1 hadj with hy' | hy' | hy' | hy'
    · exact hy (by simp [hy'])
    · exact hy (by simp [hy'])
    · exact hy (by simp [hy'])
    · exact hy (by simp [hy'])
  -- Proof comment: the origin row is the adjacency indicator normalized by `4`, so it is zero
  -- outside the four nearest neighbors.
  rw [squareLatticeKernel_row_zero]
  simp [hNotAdj]

/-- Helper for Example 19.29: each of the four cardinal neighbors of the origin has transition
mass `1 / 4` for the square-lattice conductance walk. -/
private theorem squareLatticeKernel_row_zero_eq_quarter_of_cardinal
    (y : LatticePoint 2)
    (hy :
      y = Pi.single 0 (1 : ℤ) ∨
        y = Pi.single 0 (-1 : ℤ) ∨
          y = Pi.single 1 (1 : ℤ) ∨
            y = Pi.single 1 (-1 : ℤ)) :
    conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)) 0 y = 1 / 4 := by
  have hy' :
      y = 0 + Pi.single 0 (1 : ℤ) ∨
        y = 0 + Pi.single 0 (-1 : ℤ) ∨
          y = 0 + Pi.single 1 (1 : ℤ) ∨
            y = 0 + Pi.single 1 (-1 : ℤ) := by
    simpa [zero_add] using hy
  have hadj : (latticeGraph 2).Adj 0 y := (squareLattice_adj_iff 0 y).2 hy'
  -- Proof comment: the direct origin-row formula specializes to `1 / 4` on each cardinal step.
  rw [squareLatticeKernel_row_zero]
  simp [hadj]

/-- Helper for Example 19.29: a nonzero single-coordinate step cannot coincide with a step on a
different coordinate. -/
private theorem squareLattice_single_ne_single_of_ne
    {i j : Fin 2} (hij : i ≠ j) {m n : ℤ} (hm : m ≠ 0) :
    (Pi.single i m : LatticePoint 2) ≠ Pi.single j n := by
  intro hEq
  have hcoord : (Pi.single i m : LatticePoint 2) i = (Pi.single j n : LatticePoint 2) i :=
    congrArg (fun z : LatticePoint 2 ↦ z i) hEq
  simp [hij, hm] at hcoord

/-- Helper for Example 19.29: the explicit square-lattice step law assigns mass `1 / 4` to each
cardinal unit vector. -/
private theorem squareLatticeStepPMF_apply_cardinal
    (y : LatticePoint 2)
    (hy :
      y = Pi.single 0 (1 : ℤ) ∨
        y = Pi.single 0 (-1 : ℤ) ∨
          y = Pi.single 1 (1 : ℤ) ∨
            y = Pi.single 1 (-1 : ℤ)) :
    squareLatticeStepPMF y = 1 / 4 := by
  rcases hy with rfl | rfl | rfl | rfl
  · -- Proof comment: only the witness `(true, 0)` contributes to the positive first-coordinate
    -- step under the uniform `Bool × Fin 2` law.
    rw [squareLatticeStepPMF, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have hpos : (Pi.single 0 (1 : ℤ) : LatticePoint 2) ≠ Pi.single 1 (1 : ℤ) :=
      squareLattice_single_ne_single_of_ne (i := 0) (j := 1) (by decide) (m := 1) (n := 1)
        (by norm_num)
    have hneg : (Pi.single 0 (1 : ℤ) : LatticePoint 2) ≠ Pi.single 1 (-1 : ℤ) :=
      squareLattice_single_ne_single_of_ne (i := 0) (j := 1) (by decide) (m := 1) (n := -1)
        (by norm_num)
    simp [PMF.uniformOfFintype_apply, hpos, hneg]
  · -- Proof comment: only the witness `(false, 0)` contributes to the negative first-coordinate
    -- step.
    rw [squareLatticeStepPMF, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have hpos : (Pi.single 0 (-1 : ℤ) : LatticePoint 2) ≠ Pi.single 1 (1 : ℤ) :=
      squareLattice_single_ne_single_of_ne (i := 0) (j := 1) (by decide) (m := -1) (n := 1)
        (by norm_num)
    have hneg : (Pi.single 0 (-1 : ℤ) : LatticePoint 2) ≠ Pi.single 1 (-1 : ℤ) :=
      squareLattice_single_ne_single_of_ne (i := 0) (j := 1) (by decide) (m := -1) (n := -1)
        (by norm_num)
    simp [PMF.uniformOfFintype_apply, hpos, hneg]
  · -- Proof comment: only the witness `(true, 1)` contributes to the positive second-coordinate
    -- step.
    rw [squareLatticeStepPMF, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have hpos : (Pi.single 1 (1 : ℤ) : LatticePoint 2) ≠ Pi.single 0 (1 : ℤ) :=
      squareLattice_single_ne_single_of_ne (i := 1) (j := 0) (by decide) (m := 1) (n := 1)
        (by norm_num)
    have hneg : (Pi.single 1 (1 : ℤ) : LatticePoint 2) ≠ Pi.single 0 (-1 : ℤ) :=
      squareLattice_single_ne_single_of_ne (i := 1) (j := 0) (by decide) (m := 1) (n := -1)
        (by norm_num)
    simp [PMF.uniformOfFintype_apply, hpos, hneg]
  · -- Proof comment: only the witness `(false, 1)` contributes to the negative second-coordinate
    -- step.
    rw [squareLatticeStepPMF, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have hpos : (Pi.single 1 (-1 : ℤ) : LatticePoint 2) ≠ Pi.single 0 (1 : ℤ) :=
      squareLattice_single_ne_single_of_ne (i := 1) (j := 0) (by decide) (m := -1) (n := 1)
        (by norm_num)
    have hneg : (Pi.single 1 (-1 : ℤ) : LatticePoint 2) ≠ Pi.single 0 (-1 : ℤ) :=
      squareLattice_single_ne_single_of_ne (i := 1) (j := 0) (by decide) (m := -1) (n := -1)
        (by norm_num)
    simp [PMF.uniformOfFintype_apply, hpos, hneg]

/-- Helper for Example 19.29: the explicit square-lattice step law vanishes away from the four
cardinal unit vectors. -/
private theorem squareLatticeStepPMF_apply_zero_of_not_cardinal
    (y : LatticePoint 2)
    (hy :
      y ∉ ({Pi.single 0 (1 : ℤ), Pi.single 0 (-1 : ℤ), Pi.single 1 (1 : ℤ),
        Pi.single 1 (-1 : ℤ)} : Finset (LatticePoint 2))) :
    squareLatticeStepPMF y = 0 := by
  rw [squareLatticeStepPMF, PMF.map_apply]
  have hnone :
      ∀ a : Bool × Fin 2,
        y ≠ if a.1 then Pi.single a.2 (1 : ℤ) else Pi.single a.2 (-1) := by
    intro a
    rcases a with ⟨b, i⟩
    fin_cases i <;> cases b
    · intro hEq
      exact hy (by simp [hEq])
    · intro hEq
      exact hy (by simp [hEq])
    · intro hEq
      exact hy (by simp [hEq])
    · intro hEq
      exact hy (by simp [hEq])
  -- Proof comment: every summand in the pushforward formula is zero because no sample point lands
  -- at `y`.
  simp [hnone]

/-- Helper for Example 19.29: the origin row of the normalized square-lattice walk equals the
canonical nearest-neighbor step law, written locally to avoid depending on the missing Chapter 17
owner import surface. -/
private theorem squareLatticeKernel_originRow_eq_squareLatticeStepPMF
    (y : LatticePoint 2) :
    conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)) 0 y =
      squareLatticeStepPMF y := by
  by_cases hy :
      y = Pi.single 0 (1 : ℤ) ∨
        y = Pi.single 0 (-1 : ℤ) ∨
          y = Pi.single 1 (1 : ℤ) ∨
            y = Pi.single 1 (-1 : ℤ)
  · -- Proof comment: on the four cardinal unit vectors, both one-step laws assign mass `1 / 4`.
    rw [squareLatticeKernel_row_zero_eq_quarter_of_cardinal y hy,
      squareLatticeStepPMF_apply_cardinal y hy]
  · have hy_notmem :
        y ∉ ({Pi.single 0 (1 : ℤ), Pi.single 0 (-1 : ℤ), Pi.single 1 (1 : ℤ),
          Pi.single 1 (-1 : ℤ)} : Finset (LatticePoint 2)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hy
    -- Proof comment: away from the four allowed increments, both laws vanish.
    rw [squareLatticeKernel_row_zero_eq_zero_of_not_cardinal y hy_notmem,
      squareLatticeStepPMF_apply_zero_of_not_cardinal y hy_notmem]

/-- Helper for Example 19.29: the ambient square-lattice origin row matches the canonical
symmetric nearest-neighbor step law from Theorem 17.39. -/
private theorem squareLatticeKernel_originRow_eq_symmetricSimpleRandomWalkStepPMF
    (y : LatticePoint 2) :
    squareLatticeTransitionMatrix 0 y = symmetricSimpleRandomWalkStepPMF 2 y := by
  -- Proof comment: the local explicit step law was defined to be the same `Bool × Fin 2`
  -- pushforward as the Chapter 17 symmetric simple random-walk step law.
  simpa [squareLatticeTransitionMatrix, squareLatticeStepPMF, symmetricSimpleRandomWalkStepPMF]
    using squareLatticeKernel_originRow_eq_squareLatticeStepPMF y

/-- Helper for Example 19.29: the local square-lattice step law has zero drift in each
coordinate. -/
private theorem squareLatticeStepPMF_mean_zero (i : Fin 2) :
    ∑' x : LatticePoint 2, (x i : ℝ) * (squareLatticeStepPMF x).toReal = 0 := by
  let dirs : Finset (LatticePoint 2) :=
    {Pi.single 0 (1 : ℤ), Pi.single 0 (-1 : ℤ), Pi.single 1 (1 : ℤ), Pi.single 1 (-1 : ℤ)}
  have hzero :
      ∀ x : LatticePoint 2, x ∉ dirs → (x i : ℝ) * (squareLatticeStepPMF x).toReal = 0 := by
    intro x hx
    rw [squareLatticeStepPMF_apply_zero_of_not_cardinal x hx]
    simp
  have hpos0 : squareLatticeStepPMF (Pi.single 0 (1 : ℤ) : LatticePoint 2) = 1 / 4 := by
    exact squareLatticeStepPMF_apply_cardinal _ (by left; rfl)
  have hneg0 : squareLatticeStepPMF (Pi.single 0 (-1 : ℤ) : LatticePoint 2) = 1 / 4 := by
    exact squareLatticeStepPMF_apply_cardinal _ (by right; left; rfl)
  have hpos1 : squareLatticeStepPMF (Pi.single 1 (1 : ℤ) : LatticePoint 2) = 1 / 4 := by
    exact squareLatticeStepPMF_apply_cardinal _ (by right; right; left; rfl)
  have hneg1 : squareLatticeStepPMF (Pi.single 1 (-1 : ℤ) : LatticePoint 2) = 1 / 4 := by
    exact squareLatticeStepPMF_apply_cardinal _ (by right; right; right; rfl)
  rw [tsum_eq_sum (s := dirs) hzero]
  -- Proof comment: only the four cardinal increments contribute, and the positive/negative pair
  -- on each coordinate cancels exactly.
  dsimp [dirs]
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · fin_cases i
    · rw [hpos0, hneg0, hpos1, hneg1]
      norm_num [Pi.single_apply]
    · rw [hpos0, hneg0, hpos1, hneg1]
      norm_num [Pi.single_apply]
  · decide
  · decide
  · decide

/-- Helper for Example 19.29: the square-lattice step law has finite second moment because it is
supported on four unit steps. -/
private theorem squareLatticeStepPMF_secondMoment_lt_top :
    ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * squareLatticeStepPMF x <
      ⊤ := by
  let dirs : Finset (LatticePoint 2) :=
    {Pi.single 0 (1 : ℤ), Pi.single 0 (-1 : ℤ), Pi.single 1 (1 : ℤ), Pi.single 1 (-1 : ℤ)}
  have hzero :
      ∀ x : LatticePoint 2,
        x ∉ dirs →
          ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * squareLatticeStepPMF x = 0 := by
    intro x hx
    rw [squareLatticeStepPMF_apply_zero_of_not_cardinal x hx]
    simp
  rw [tsum_eq_sum (s := dirs) hzero, ENNReal.sum_lt_top]
  intro x hx
  have hx_cardinal :
      x = Pi.single 0 (1 : ℤ) ∨
        x = Pi.single 0 (-1 : ℤ) ∨
          x = Pi.single 1 (1 : ℤ) ∨
            x = Pi.single 1 (-1 : ℤ) := by
    simpa [dirs, Finset.mem_insert, Finset.mem_singleton] using hx
  rw [squareLatticeStepPMF_apply_cardinal x hx_cardinal]
  -- Proof comment: each support point contributes a finite ENNReal quantity, so the finite sum
  -- remains finite.
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by norm_num)

/-- Helper for Example 19.29: the origin row of the ambient square-lattice kernel has zero drift
in each coordinate. -/
private theorem squareLatticeKernel_originRow_mean_zero (i : Fin 2) :
    ∑' x : LatticePoint 2, (x i : ℝ) * (squareLatticeTransitionMatrix 0 x).toReal = 0 := by
  have hrow :
      (fun x : LatticePoint 2 ↦ (x i : ℝ) * (squareLatticeTransitionMatrix 0 x).toReal) =
        fun x : LatticePoint 2 ↦ (x i : ℝ) * (squareLatticeStepPMF x).toReal := by
    funext x
    -- Proof comment: the local row-identification lemma is consumed through the transition-matrix
    -- abbreviation before taking `toReal`.
    simpa [squareLatticeTransitionMatrix] using
      congrArg (fun t : ℝ≥0∞ ↦ (x i : ℝ) * t.toReal)
        (squareLatticeKernel_originRow_eq_squareLatticeStepPMF x)
  rw [hrow]
  exact squareLatticeStepPMF_mean_zero i

/-- Helper for Example 19.29: the origin row of the ambient square-lattice kernel has finite
second moment. -/
private theorem squareLatticeKernel_originRow_secondMoment_lt_top :
    ∑' x : LatticePoint 2,
        ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * squareLatticeTransitionMatrix 0 x < ⊤ := by
  have hrow :
      (fun x : LatticePoint 2 ↦
          ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * squareLatticeTransitionMatrix 0 x) =
        fun x : LatticePoint 2 ↦
          ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * squareLatticeStepPMF x := by
    funext x
    -- Proof comment: the second-moment row identity is the same origin-row comparison pushed
    -- through multiplication by the squared norm factor.
    simpa [squareLatticeTransitionMatrix] using
      congrArg
        (fun t : ℝ≥0∞ ↦ ‖latticeEmbedding x‖ₑ ^ 2 * t)
        (squareLatticeKernel_originRow_eq_squareLatticeStepPMF x)
  rw [hrow]
  exact squareLatticeStepPMF_secondMoment_lt_top

/-- Helper for Example 19.29: the terminal-state projection on a finite history is measurable. -/
private theorem squareLatticeTerminalState_measurable (n : ℕ) :
    Measurable
      (fun z : Π _ : Finset.Iic n, LatticePoint 2 ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩) := by
  fun_prop

/-- Helper for Example 19.29: the natural history σ-algebra of the canonical coordinate process
on `ℕ → LatticePoint 2` up to time `s` is exactly the sigma-algebra generated by the finite prefix
map `Preorder.frestrictLe s`. -/
private theorem generatedFiltrationSpace_eval_eq_frestrictLeComap
    (s : ℕ) :
    generatedFiltrationSpace (Function.eval : ℕ → (ℕ → LatticePoint 2) → LatticePoint 2) s =
      MeasurableSpace.comap (Preorder.frestrictLe s) inferInstance := by
  refine le_antisymm ?_ ?_
  · rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Finset.Iic s := ⟨t, Finset.mem_Iic.2 ht⟩
    have hCoord :
        Measurable[
          MeasurableSpace.comap (Preorder.frestrictLe s) inferInstance]
          (Function.eval t : (ℕ → LatticePoint 2) → LatticePoint 2) := by
      -- Proof comment: each history coordinate `eval t` with `t ≤ s` is recovered by reading the
      -- prefix map at the slot `⟨t, t ≤ s⟩`.
      simpa [Function.eval, Preorder.frestrictLe_apply, i] using
        (measurable_pi_apply i).comp (comap_measurable (Preorder.frestrictLe s))
    exact hCoord.comap_le
  · have hPrefix :
      Measurable[
        generatedFiltrationSpace
          (Function.eval : ℕ → (ℕ → LatticePoint 2) → LatticePoint 2) s]
        (Preorder.frestrictLe s : (ℕ → LatticePoint 2) → Finset.Iic s → LatticePoint 2) := by
      -- Proof comment: every coordinate of the prefix map is one of the generators `eval t`
      -- with `t ≤ s`.
      rw [@measurable_pi_iff]
      intro i
      refine Measurable.of_comap_le ?_
      exact le_iSup_of_le i.1 <| le_iSup_of_le (Finset.mem_Iic.1 i.2) le_rfl
    exact hPrefix.comap_le

/-- Helper for Example 19.29: the homogeneous history kernel reads the final state of a finite
history and applies the ambient square-lattice one-step kernel there. -/
private def squareLatticeHistoryKernel (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, LatticePoint 2) (LatticePoint 2) :=
  Kernel.comap (discreteMatrixKernel squareLatticeTransitionMatrix)
    (fun z : Π _ : Finset.Iic n, LatticePoint 2 ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
    (squareLatticeTerminalState_measurable n)

/-- Helper for Example 19.29: each finite-history kernel inherits the Markov property from the
ambient one-step square-lattice kernel. -/
private instance squareLatticeHistoryKernel_isMarkovKernel (n : ℕ) :
    IsMarkovKernel (squareLatticeHistoryKernel n) := by
  -- Proof comment: `Kernel.comap` preserves the Markov-kernel structure of the ambient one-step
  -- kernel.
  dsimp [squareLatticeHistoryKernel]
  infer_instance

/-- Helper for Example 19.29: the canonical path-space law of the ambient square-lattice walk
started from `x`. -/
private def squareLatticeCanonicalPathLaw (x : LatticePoint 2) :
    ProbabilityMeasure (ℕ → LatticePoint 2) :=
  ⟨Kernel.trajMeasure (X := fun _ : ℕ ↦ LatticePoint 2) (Measure.dirac x)
      squareLatticeHistoryKernel,
    inferInstance⟩

/-- Helper for Example 19.29: the canonical path-space law starts from the prescribed initial
state on coordinate `0`. -/
private theorem squareLatticeCanonicalPathLaw_map_eval_zero (x : LatticePoint 2) :
    (squareLatticeCanonicalPathLaw x : Measure (ℕ → LatticePoint 2)).map (Function.eval 0) =
      Measure.dirac x := by
  let μ : Measure (ℕ → LatticePoint 2) := squareLatticeCanonicalPathLaw x
  have hprefix :
      μ.map (Preorder.frestrictLe 0) = Measure.dirac (fun _ : Finset.Iic 0 ↦ x) := by
    -- Proof comment: the length-zero prefix of the canonical trajectory law is the deterministic
    -- initial state.
    simpa [μ, squareLatticeCanonicalPathLaw, squareLatticeHistoryKernel, Kernel.partialTraj_self]
      using
        (Kernel.trajMeasure_map_frestrictLe (X := fun _ : ℕ ↦ LatticePoint 2)
          (μ₀ := Measure.dirac x) (κ := squareLatticeHistoryKernel) 0)
  -- Proof comment: evaluate the zero prefix at its unique coordinate to recover the initial law.
  calc
    (squareLatticeCanonicalPathLaw x : Measure (ℕ → LatticePoint 2)).map (Function.eval 0) =
        (μ.map (Preorder.frestrictLe 0)).map
          (fun z : Finset.Iic 0 → LatticePoint 2 ↦ z ⟨0, Finset.mem_Iic.2 le_rfl⟩) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
    _ = Measure.dirac x := by
          rw [hprefix]
          simp

/-- Helper for Example 19.29: under the canonical ambient path law, conditioning the next
coordinate on the past gives the square-lattice one-step kernel evaluated at the current state. -/
private theorem squareLatticeCanonicalPathLaw_oneStepConditional
    (x : LatticePoint 2) ⦃A : Set (LatticePoint 2)⦄ (hA : MeasurableSet A) (s : ℕ) :
    (squareLatticeCanonicalPathLaw x)⟦Function.eval (s + 1) ⁻¹' A |
        generatedFiltrationSpace Function.eval s⟧ =ᵐ[
          (squareLatticeCanonicalPathLaw x : Measure (ℕ → LatticePoint 2))]
      (fun ξ ↦
        ((discreteMatrixKernel squareLatticeTransitionMatrix) (Function.eval s ξ)).real A) := by
  letI : StandardBorelSpace (LatticePoint 2) := inferInstance
  letI : StandardBorelSpace (Finset.Iic s → LatticePoint 2) := inferInstance
  let μ : Measure (ℕ → LatticePoint 2) := squareLatticeCanonicalPathLaw x
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, squareLatticeCanonicalPathLaw]
    infer_instance
  let H : (ℕ → LatticePoint 2) → Finset.Iic s → LatticePoint 2 := Preorder.frestrictLe s
  have hH_meas : Measurable H := Preorder.measurable_frestrictLe s
  have hnext_meas : Measurable (Function.eval (s + 1) : (ℕ → LatticePoint 2) → LatticePoint 2) :=
    measurable_pi_apply (s + 1)
  have hcond :
      condDistrib (Function.eval (s + 1)) H μ =ᵐ[μ.map H] squareLatticeHistoryKernel s := by
    -- Proof comment: `Kernel.condDistrib_trajMeasure` identifies the next-step conditional law
    -- of the canonical trajectory measure with the history kernel itself.
    simpa [μ, H, squareLatticeCanonicalPathLaw] using
      (Kernel.condDistrib_trajMeasure (X := fun _ : ℕ ↦ LatticePoint 2)
        (μ₀ := Measure.dirac x) (κ := squareLatticeHistoryKernel) (a := s))
  have hcondexp :
      μ⟦(Function.eval (s + 1)) ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
        fun ξ ↦ (condDistrib (Function.eval (s + 1)) H μ (H ξ)).real A := by
    -- Proof comment: rewrite the conditional probability event through the owner conditional
    -- distribution kernel.
    simpa using
      (condDistrib_ae_eq_condExp (μ := μ) (X := H) (Y := Function.eval (s + 1))
        hH_meas hnext_meas hA).symm
  have hcond_comp :
      (fun ξ ↦ (condDistrib (Function.eval (s + 1)) H μ (H ξ)).real A) =ᵐ[μ]
        fun ξ ↦ (squareLatticeHistoryKernel s (H ξ)).real A := by
    filter_upwards [ae_eq_comp hH_meas.aemeasurable hcond] with ξ hξ
    simpa [Function.comp] using congrArg (fun ν : Measure (LatticePoint 2) ↦ ν.real A) hξ
  rw [generatedFiltrationSpace_eval_eq_frestrictLeComap]
  exact hcondexp.trans <|
    hcond_comp.trans <|
      Filter.Eventually.of_forall fun ξ ↦ by
        simp [squareLatticeHistoryKernel, H, Preorder.frestrictLe_apply]

/-- Helper for Example 19.29: the canonical square-lattice path law realizes the semigroup of
powers of the ambient one-step matrix. -/
private theorem squareLatticeCanonicalPathLaw_isMarkovProcessRealization :
    IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel squareLatticeTransitionMatrix ^ n)
      squareLatticeCanonicalPathLaw Function.eval := by
  -- Proof comment: the canonical trajectory law satisfies the Chapter 18 start-law and one-step
  -- conditional API, so it realizes the powers of the square-lattice kernel.
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := discreteMatrixKernel squareLatticeTransitionMatrix)
    (P := squareLatticeCanonicalPathLaw)
    (X := Function.eval)
    (hmeas := fun n ↦ measurable_pi_apply n)
    (hstart := squareLatticeCanonicalPathLaw_map_eval_zero)
    (hstep := ?_)
  intro x A hA s
  exact squareLatticeCanonicalPathLaw_oneStepConditional x hA s

/-- Helper for Example 19.29: the canonical ambient square-lattice walk is recurrent because its
step matrix is the canonical symmetric nearest-neighbor walk on `ℤ²`. -/
private theorem squareLatticeCanonicalPathLaw_isRecurrent :
    IsRecurrentMarkovChain squareLatticeCanonicalPathLaw Function.eval := by
  letI :
      IsMarkovProcessRealization
        (fun n ↦ discreteMatrixKernel squareLatticeTransitionMatrix ^ n)
        squareLatticeCanonicalPathLaw Function.eval :=
    squareLatticeCanonicalPathLaw_isMarkovProcessRealization
  -- Proof comment: Theorem 17.39 applies directly once the ambient square-lattice row at the
  -- origin is identified with the canonical symmetric nearest-neighbor step law on `ℤ²`.
  exact
    (symmetricSimpleRandomWalk_lattice_recurrent_iff_dimension_le_two
      (D := 2)
      (P := squareLatticeCanonicalPathLaw)
      (X := Function.eval)
      (p := squareLatticeTransitionMatrix)
      squareLatticeKernel_translationInvariant
      squareLatticeKernel_originRow_eq_symmetricSimpleRandomWalkStepPMF).2 (by decide)

private theorem exists_recurrent_squareLattice_realization :
    ∃ (Ω : Type), ∃ _ : MeasurableSpace Ω,
        ∃ P : LatticePoint 2 → ProbabilityMeasure Ω,
          ∃ X : ℕ → Ω → LatticePoint 2,
            IsMarkovProcessRealization
              (fun n ↦
                discreteMatrixKernel
                  (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))) ^ n) P X ∧
            IsRecurrentMarkovChain P X := by
  -- Proof comment: the canonical path space `ℕ → ℤ²` already provides the required ambient
  -- realization and recurrence witness.
  refine
    ⟨ℕ → LatticePoint 2, inferInstance, squareLatticeCanonicalPathLaw, Function.eval, ?_, ?_⟩
  · simpa [squareLatticeTransitionMatrix] using
      squareLatticeCanonicalPathLaw_isMarkovProcessRealization
  · exact squareLatticeCanonicalPathLaw_isRecurrent

/-- Helper for Example 19.29: the unit edge weights of a square-lattice subgraph are bounded by
the unit edge weights of the induced ambient square lattice on the same vertex set. -/
private theorem simpleGraphWeights_le_of_squareLatticeSubgraph
    (H : (latticeGraph 2).Subgraph) :
    ∀ x y : H.verts,
      simpleGraphWeights H.coe x y ≤
        simpleGraphWeights (SimpleGraph.induce H.verts (latticeGraph 2)) x y := by
  have hsub : H.coe ≤ SimpleGraph.induce H.verts (latticeGraph 2) := by
    intro x y hxy
    change (latticeGraph 2).Adj x y
    exact H.coe_adj_sub x y hxy
  -- Proof comment: this is exactly the generic monotonicity of unit edge weights under subgraph
  -- inclusion, specialized to the square-lattice ambient graph.
  simpa using
    simpleGraphWeights_le_of_isSubgraph
      (SimpleGraph.induce H.verts (latticeGraph 2)) H.coe hsub

private theorem recurrent_of_squareLattice_subgraph
    {Ω : Type v} {Ω' : Type w} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (H : (latticeGraph 2).Subgraph)
    (p₀ : LatticePoint 2 → LatticePoint 2 → ℝ≥0∞)
    (p : H.verts → H.verts → ℝ≥0∞)
    (P₀ : LatticePoint 2 → ProbabilityMeasure Ω') (X₀ : ℕ → Ω' → LatticePoint 2)
    (P : H.verts → ProbabilityMeasure Ω) (X : ℕ → Ω → H.verts)
    [IsSimpleRandomWalk p₀ (latticeGraph 2)]
    [IsSimpleRandomWalk p H.coe]
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p₀ ^ n) P₀ X₀]
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (hrec₀ : IsRecurrentMarkovChain P₀ X₀) :
    IsRecurrentMarkovChain P X := by
  have hsub : H.coe ≤ SimpleGraph.induce H.verts (latticeGraph 2) := by
    intro x y hxy
    change (latticeGraph 2).Adj x y
    exact H.coe_adj_sub x y hxy
  -- Proof comment: Theorem 19.30 transfers recurrence from the ambient square-lattice walk to
  -- the simple random walk on the subgraph `H`.
  exact
    simpleRandomWalk_recurrent_of_subgraph
      (G := latticeGraph 2) (s := H.verts) (G' := H.coe)
      (p := p₀) (p' := p) (P := P₀) (X := X₀) (P' := P) (X' := X)
      hsub hrec₀

section

variable {Ω : Type v} [MeasurableSpace Ω]

-- Proof sketch: realize the full square-lattice walk once using the canonical conductance
-- normalization of `simpleGraphWeights (latticeGraph 2)`, apply the Chapter 17 recurrence theorem
-- in dimension `2`, and then pass to the subgraph `H` with Theorem 19.30.
/-- Example 19.29: every simple random walk on a subgraph `H` of the square lattice
`latticeGraph 2` is recurrent. This strengthens the textbook connected-subgraph statement,
since the recurrence transfer through Theorem 19.30 does not use connectedness. The textbook
proof uses Rayleigh's monotonicity principle to compare the effective resistance from `0` to `∞`
in `H` with the effective resistance in the full square lattice, which is infinite. -/
theorem simpleRandomWalk_on_subgraph_of_square_lattice_isRecurrent
    (H : (latticeGraph 2).Subgraph)
    (p : H.verts → H.verts → ℝ≥0∞)
    (P : H.verts → ProbabilityMeasure Ω) (X : ℕ → Ω → H.verts)
    [IsSimpleRandomWalk p H.coe]
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X] :
    IsRecurrentMarkovChain P X := by
  letI :
      IsSimpleRandomWalk
        (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2)))
        (latticeGraph 2) :=
    squareLatticeKernel_isSimpleRandomWalk
  rcases exists_recurrent_squareLattice_realization with ⟨Ω', mΩ', P', X', hreal', hrec'⟩
  letI : MeasurableSpace Ω' := mΩ'
  letI :
      IsMarkovProcessRealization
        (fun n ↦
          discreteMatrixKernel
            (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))) ^ n) P' X' :=
    hreal'
  exact
    recurrent_of_squareLattice_subgraph
      H (conductanceTransitionMatrix (simpleGraphWeights (latticeGraph 2))) p P' X' P X hrec'

end

end ProbabilityTheory
