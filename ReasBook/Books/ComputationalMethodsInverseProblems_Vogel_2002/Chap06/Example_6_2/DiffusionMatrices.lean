/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

namespace OneDimensionalDiffusion

/-- The discrete first-difference matrix with homogeneous Dirichlet boundary behavior on
`Fin (n + 1)` and interior-state columns indexed by `Fin n`. -/
def differenceMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  fun i j ↦
    if i = Fin.castSucc j then
      1
    else if i = j.succ then
      -1
    else
      0

/-- The entrywise bidiagonal formula for `differenceMatrix`. -/
theorem differenceMatrix_apply (n : ℕ) (i : Fin (n + 1)) (j : Fin n) :
    differenceMatrix n i j =
      if i = Fin.castSucc j then
        1
      else if i = j.succ then
        -1
      else
        0 := by
  -- This theorem just restates the defining bidiagonal formula.
  rfl

/-- The weighted one-dimensional diffusion stiffness matrix obtained from the conductivity
samples `κ` and the discrete first-difference operator. -/
def stiffnessMatrix (n : ℕ) (κ : Fin (n + 1) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (n + 1 : ℝ) •
    (Matrix.transpose (differenceMatrix n) * Matrix.diagonal κ * differenceMatrix n)

/-- The stiffness matrix is the weighted Gram operator of `differenceMatrix`. -/
theorem stiffnessMatrix_eqWeightedGram (n : ℕ) (κ : Fin (n + 1) → ℝ) :
    stiffnessMatrix n κ =
      (n + 1 : ℝ) •
        (Matrix.transpose (differenceMatrix n) * Matrix.diagonal κ * differenceMatrix n) := by
  -- This is the defining formula of `stiffnessMatrix`.
  rfl

/-- The adjacency relation on the finite path graph is decidable. -/
noncomputable instance instDecidableRelPathGraphAdj (n : ℕ) :
    DecidableRel (SimpleGraph.pathGraph (n + 1)).Adj := by
  classical
  infer_instance

/-- The discrete Neumann Laplacian on the conductivity grid, realized as the path-graph
Laplacian on `Fin (n + 1)`. -/
noncomputable def neumannLaplacian (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (SimpleGraph.pathGraph (n + 1)).lapMatrix ℝ

/-- The discrete Neumann Laplacian agrees with the path-graph Laplacian. -/
theorem neumannLaplacian_eqPathGraphLapMatrix (n : ℕ) :
    neumannLaplacian n = (SimpleGraph.pathGraph (n + 1)).lapMatrix ℝ := by
  -- This theorem just unfolds the definition of `neumannLaplacian`.
  rfl

/-- Helper for Example 6.2-extra-1: applying `differenceMatrixᵀ` computes the forward edge
differences of a grid function. -/
theorem differenceMatrixTranspose_mulVec_apply (n : ℕ) (x : Fin (n + 1) → ℝ) (j : Fin n) :
    Matrix.mulVec (Matrix.transpose (differenceMatrix n)) x j =
      x (Fin.castSucc j) - x j.succ := by
  -- Expand the transpose action and isolate the two nonzero entries of the bidiagonal column.
  rw [Matrix.mulVec_apply_eq_sum]
  have hcastSucc : Fin.castSucc j ≠ j.succ := by
    exact ne_of_lt Fin.castSucc_lt_succ
  let f : Fin (n + 1) → ℝ :=
    fun i ↦ if i = Fin.castSucc j then x i else if i = j.succ then -x i else 0
  have hzero :
      Finset.sum ((Finset.univ.erase j.succ).erase (Fin.castSucc j)) f = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rcases Finset.mem_erase.mp hi with ⟨hi_castSucc, hi⟩
    rcases Finset.mem_erase.mp hi with ⟨hi_succ, _⟩
    simp [hi_castSucc, hi_succ]
  have hsumRewrite :
      (∑ i : Fin (n + 1), (differenceMatrix n).transpose j i * x i) = ∑ i : Fin (n + 1), f i := by
    refine congrArg (fun g : Fin (n + 1) → ℝ => ∑ i, g i) ?_
    funext i
    simp [f, Matrix.transpose_apply, differenceMatrix]
  rw [hsumRewrite]
  rw [← Finset.univ.add_sum_erase f (Finset.mem_univ j.succ)]
  rw [← (Finset.univ.erase j.succ).add_sum_erase f
      (show Fin.castSucc j ∈ Finset.univ.erase j.succ by simp [hcastSucc])]
  have hsuccCast : j.succ ≠ j.castSucc := hcastSucc.symm
  simp [f, hsuccCast, hzero, sub_eq_add_neg, add_comm]

/-- Helper for Example 6.2-extra-1: the first row of `differenceMatrix` extracts the left
boundary value. -/
theorem differenceMatrix_mulVec_apply_zero (n : ℕ) (x : Fin (n + 1) → ℝ) :
    Matrix.mulVec (differenceMatrix (n + 1)) x 0 = x 0 := by
  -- Only the first column contributes to the top row of the bidiagonal matrix.
  rw [Matrix.mulVec_apply_eq_sum]
  have hzero : ∀ i : Fin (n + 1), i ≠ 0 → differenceMatrix (n + 1) 0 i * x i = 0 := by
    intro i hi
    grind [differenceMatrix]
  convert! Finset.sum_eq_single 0 (fun i _ hi ↦ hzero i hi) _ using 1 <;> simp [differenceMatrix]

/-- Helper for Example 6.2-extra-1: successive rows of `differenceMatrix` compute adjacent
backward differences. -/
theorem differenceMatrix_mulVec_apply_succ (n : ℕ) (x : Fin (n + 1) → ℝ) (j : Fin n) :
    Matrix.mulVec (differenceMatrix (n + 1)) x (Fin.castSucc j).succ = x j.succ - x j.castSucc := by
  -- The row indexed by `(Fin.castSucc j).succ` has exactly the entries `-1` at `j.castSucc`
  -- and `1` at `j.succ`.
  rw [Matrix.mulVec_apply_eq_sum]
  have hcastSucc : Fin.castSucc j ≠ j.succ := by
    exact ne_of_lt Fin.castSucc_lt_succ
  let f : Fin (n + 1) → ℝ :=
    fun i ↦ if i = Fin.castSucc j then -x i else if i = j.succ then x i else 0
  have hzero :
      Finset.sum ((Finset.univ.erase j.succ).erase (Fin.castSucc j)) f = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rcases Finset.mem_erase.mp hi with ⟨hi_castSucc, hi⟩
    rcases Finset.mem_erase.mp hi with ⟨hi_succ, _⟩
    simp [hi_castSucc, hi_succ]
  have hsumRewrite :
      (∑ i : Fin (n + 1), differenceMatrix (n + 1) (Fin.castSucc j).succ i * x i) =
        ∑ i : Fin (n + 1), f i := by
    refine congrArg (fun g : Fin (n + 1) → ℝ => ∑ i, g i) ?_
    funext i
    by_cases hiCast : i = Fin.castSucc j
    · grind [differenceMatrix]
    · by_cases hiSucc : i = j.succ
      · grind [differenceMatrix]
      · grind [differenceMatrix]
  rw [hsumRewrite]
  rw [← Finset.univ.add_sum_erase f (Finset.mem_univ j.succ)]
  rw [← (Finset.univ.erase j.succ).add_sum_erase f
      (show Fin.castSucc j ∈ Finset.univ.erase j.succ by simp [hcastSucc])]
  have hsuccCast : j.succ ≠ j.castSucc := hcastSucc.symm
  simp [f, hsuccCast, hzero, sub_eq_add_neg]

/-- Helper for Example 6.2-extra-1: the last row of `differenceMatrix` extracts the negated
right boundary difference. -/
theorem differenceMatrix_mulVec_apply_last (n : ℕ) (x : Fin (n + 1) → ℝ) :
    Matrix.mulVec (differenceMatrix (n + 1)) x (Fin.last (n + 1)) = -x (Fin.last n) := by
  -- Only the last column contributes to the terminal row of the bidiagonal matrix.
  rw [Matrix.mulVec_apply_eq_sum]
  let f : Fin (n + 1) → ℝ := fun i ↦ if i = Fin.last n then -x i else 0
  have hsumRewrite :
      (∑ i : Fin (n + 1), differenceMatrix (n + 1) (Fin.last (n + 1)) i * x i) =
        ∑ i : Fin (n + 1), f i := by
    refine congrArg (fun g : Fin (n + 1) → ℝ => ∑ i, g i) ?_
    funext i
    by_cases hi : i = Fin.last n
    · grind [differenceMatrix]
    · grind [differenceMatrix]
  rw [hsumRewrite]
  rw [← Finset.univ.add_sum_erase f (Finset.mem_univ (Fin.last n))]
  simp [f]

/-- Helper for Example 6.2-extra-1: the path-graph Laplacian at the left endpoint is the
expected one-sided second difference. -/
theorem pathGraphLapMatrix_mulVec_apply_zero (n : ℕ) (x : Fin (n + 2) → ℝ) :
    Matrix.mulVec ((SimpleGraph.pathGraph (n + 2)).lapMatrix ℝ) x 0 = x 0 - x 1 := by
  -- First identify the unique neighbor of `0`, then apply the graph-Laplacian action formula.
  have hneighborSet :
      (SimpleGraph.pathGraph (n + 2)).neighborSet 0 = ({1} : Set (Fin (n + 2))) := by
    ext u
    simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff, SimpleGraph.pathGraph_adj,
      Fin.ext_iff]
    constructor
    · intro hu
      rcases hu with hu | hu
      · simpa using hu.symm
      · exact (Nat.succ_ne_zero _ hu).elim
    · intro hu
      left
      simpa using hu.symm
  have hneighbor :
      (SimpleGraph.pathGraph (n + 2)).neighborFinset 0 = {1} := by
    ext u
    have hu : u ∈ (SimpleGraph.pathGraph (n + 2)).neighborSet 0 ↔ u ∈ ({1} : Set (Fin (n + 2))) := by
      rw [hneighborSet]
    simpa [SimpleGraph.mem_neighborSet] using hu
  have hdegree : (SimpleGraph.pathGraph (n + 2)).degree 0 = 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbor]
    simp
  -- With the endpoint degree and neighbor set fixed, the scalar formula is immediate.
  rw [SimpleGraph.lapMatrix_mulVec_apply, hdegree, hneighbor]
  simp

/-- Helper for Example 6.2-extra-1: the path-graph Laplacian at an interior vertex is the
standard centered second difference. -/
theorem pathGraphLapMatrix_mulVec_apply_succ (n : ℕ) (x : Fin (n + 2) → ℝ) (j : Fin n) :
    Matrix.mulVec ((SimpleGraph.pathGraph (n + 2)).lapMatrix ℝ) x ((Fin.castSucc j).succ) =
      2 * x ((Fin.castSucc j).succ) - x (Fin.castSucc (Fin.castSucc j)) - x j.succ.succ := by
  -- First normalize the two neighbors of the interior vertex as its predecessor and successor.
  have hneighbor :
      (SimpleGraph.pathGraph (n + 2)).neighborFinset ((Fin.castSucc j).succ) =
        {Fin.castSucc (Fin.castSucc j), j.succ.succ} := by
    have hneighborSet :
        (SimpleGraph.pathGraph (n + 2)).neighborSet ((Fin.castSucc j).succ) =
          ({Fin.castSucc (Fin.castSucc j), j.succ.succ} : Set (Fin (n + 2))) := by
      ext u
      simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
        SimpleGraph.pathGraph_adj, Fin.ext_iff]
      constructor
      · intro hu
        rcases hu with hu | hu
        · right
          simp [Fin.val_succ, Fin.val_castSucc] at hu ⊢
          omega
        · left
          simp [Fin.val_succ, Fin.val_castSucc] at hu ⊢
          omega
      · intro hu
        rcases hu with hu | hu
        · right
          simp [Fin.val_succ, Fin.val_castSucc] at hu ⊢
          omega
        · left
          simp [Fin.val_succ, Fin.val_castSucc] at hu ⊢
          omega
    ext u
    have hu :
        u ∈ (SimpleGraph.pathGraph (n + 2)).neighborSet ((Fin.castSucc j).succ) ↔
          u ∈ ({Fin.castSucc (Fin.castSucc j), j.succ.succ} : Set (Fin (n + 2))) := by
      rw [hneighborSet]
    simpa [SimpleGraph.mem_neighborSet] using hu
  have hne : Fin.castSucc (Fin.castSucc j) ≠ j.succ.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.val_succ, Fin.val_castSucc] at hval
    omega
  have hdegree : (SimpleGraph.pathGraph (n + 2)).degree ((Fin.castSucc j).succ) = 2 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbor]
    simp [hne]
  -- Once the graph side is in endpoint/interior normal form, the centered difference is explicit.
  rw [SimpleGraph.lapMatrix_mulVec_apply, hdegree, hneighbor]
  rw [Finset.sum_pair hne]
  ring

/-- Helper for Example 6.2-extra-1: the path-graph Laplacian at the right endpoint is the
expected one-sided second difference. -/
theorem pathGraphLapMatrix_mulVec_apply_last (n : ℕ) (x : Fin (n + 2) → ℝ) :
    Matrix.mulVec ((SimpleGraph.pathGraph (n + 2)).lapMatrix ℝ) x (Fin.last (n + 1)) =
      x (Fin.last (n + 1)) - x (Fin.castSucc (Fin.last n)) := by
  -- First identify the unique neighbor of the terminal vertex, then evaluate the Laplacian.
  have hneighborSet :
      (SimpleGraph.pathGraph (n + 2)).neighborSet (Fin.last (n + 1)) =
        ({Fin.castSucc (Fin.last n)} : Set (Fin (n + 2))) := by
    ext u
    simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff, SimpleGraph.pathGraph_adj,
      Fin.ext_iff]
    constructor
    · intro hu
      rcases hu with hu | hu
      · have : False := by
          have hu' : n + 2 = u.1 := by
            simp [Fin.val_last] at hu ⊢
            exact hu
          exact (Nat.ne_of_lt u.is_lt hu'.symm).elim
        exact this.elim
      · simp [Fin.val_last] at hu ⊢
        omega
    · intro hu
      right
      simp [Fin.val_last] at hu ⊢
      omega
  have hneighbor :
      (SimpleGraph.pathGraph (n + 2)).neighborFinset (Fin.last (n + 1)) =
        {Fin.castSucc (Fin.last n)} := by
    ext u
    have hu :
        u ∈ (SimpleGraph.pathGraph (n + 2)).neighborSet (Fin.last (n + 1)) ↔
          u ∈ ({Fin.castSucc (Fin.last n)} : Set (Fin (n + 2))) := by
      rw [hneighborSet]
    simpa [SimpleGraph.mem_neighborSet] using hu
  have hdegree : (SimpleGraph.pathGraph (n + 2)).degree (Fin.last (n + 1)) = 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbor]
    simp
  -- With the terminal degree and neighbor set fixed, the endpoint formula is immediate.
  rw [SimpleGraph.lapMatrix_mulVec_apply, hdegree, hneighbor]
  simp

/-- The discrete Neumann Laplacian is the unweighted Gram operator of `differenceMatrix`. -/
theorem neumannLaplacian_eqDifferenceMatrixMulTranspose (n : ℕ) :
    neumannLaplacian n =
      differenceMatrix n * Matrix.transpose (differenceMatrix n) := by
  cases n with
  | zero =>
      -- In the `1 × 1` base case, both matrices are visibly zero.
      ext i j
      fin_cases i
      fin_cases j
      simp [neumannLaplacian_eqPathGraphLapMatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix]
  | succ n =>
      -- Route correction: normalize the path-graph Laplacian row actions first, then compare
      -- them with the already-normalized Gram-side row formulas.
      rw [Matrix.ext_iff_mulVec]
      intro x
      funext i
      refine Fin.cases ?_ ?_ i
      · -- The left endpoint matches the top row of the discrete Gram operator.
        calc
          Matrix.mulVec (neumannLaplacian (n + 1)) x 0 = x 0 - x 1 := by
            rw [neumannLaplacian_eqPathGraphLapMatrix, pathGraphLapMatrix_mulVec_apply_zero]
          _ =
              Matrix.mulVec
                (differenceMatrix (n + 1) * Matrix.transpose (differenceMatrix (n + 1))) x 0 := by
            rw [← Matrix.mulVec_mulVec]
            simpa [differenceMatrixTranspose_mulVec_apply] using
              (differenceMatrix_mulVec_apply_zero n
                ((Matrix.transpose (differenceMatrix (n + 1))).mulVec x)).symm
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · -- The right endpoint matches the last row after expanding the terminal difference.
          calc
            Matrix.mulVec (neumannLaplacian (n + 1)) x (Fin.last n).succ =
                x (Fin.last (n + 1)) - x (Fin.castSucc (Fin.last n)) := by
              rw [neumannLaplacian_eqPathGraphLapMatrix]
              simpa using pathGraphLapMatrix_mulVec_apply_last n x
          _ =
                Matrix.mulVec
                  (differenceMatrix (n + 1) * Matrix.transpose (differenceMatrix (n + 1))) x
                  (Fin.last n).succ := by
              rw [← Matrix.mulVec_mulVec]
              simpa [differenceMatrixTranspose_mulVec_apply] using
                (differenceMatrix_mulVec_apply_last n
                  ((Matrix.transpose (differenceMatrix (n + 1))).mulVec x)).symm
        · intro j
          -- Every interior row becomes the centered second difference on both sides.
          have hGram :
              Matrix.mulVec
                  (differenceMatrix (n + 1) * Matrix.transpose (differenceMatrix (n + 1))) x
                  (Fin.castSucc j).succ =
                (x ((Fin.castSucc j).succ) - x j.succ.succ) -
                  (x (Fin.castSucc (Fin.castSucc j)) - x ((Fin.castSucc j).succ)) := by
            rw [← Matrix.mulVec_mulVec]
            simpa [differenceMatrixTranspose_mulVec_apply, ← Fin.castSucc_succ] using
              differenceMatrix_mulVec_apply_succ n
                ((Matrix.transpose (differenceMatrix (n + 1))).mulVec x) j
          calc
            Matrix.mulVec (neumannLaplacian (n + 1)) x (Fin.castSucc j).succ =
                2 * x ((Fin.castSucc j).succ) - x (Fin.castSucc (Fin.castSucc j)) -
                  x j.succ.succ := by
              rw [neumannLaplacian_eqPathGraphLapMatrix, pathGraphLapMatrix_mulVec_apply_succ]
            _ = (x ((Fin.castSucc j).succ) - x j.succ.succ) -
                  (x (Fin.castSucc (Fin.castSucc j)) - x ((Fin.castSucc j).succ)) := by
              ring
            _ =
                Matrix.mulVec
                  (differenceMatrix (n + 1) * Matrix.transpose (differenceMatrix (n + 1))) x
                  (Fin.castSucc j).succ := by
              exact hGram.symm

/-- The discrete Neumann Laplacian is positive semidefinite. -/
theorem neumannLaplacian_posSemidef (n : ℕ) :
    Matrix.PosSemidef (neumannLaplacian n) := by
  -- This is the standard positive-semidefiniteness theorem for graph Laplacians.
  simpa [neumannLaplacian_eqPathGraphLapMatrix n] using
    (SimpleGraph.posSemidef_lapMatrix ℝ (SimpleGraph.pathGraph (n + 1)))

/-- The constant-one vector belongs to the kernel of the discrete Neumann Laplacian. -/
theorem neumannLaplacian_mulVecOne_eqZero (n : ℕ) :
    Matrix.mulVec (neumannLaplacian n) (fun _ ↦ (1 : ℝ)) = 0 := by
  -- Constant vectors lie in the kernel of every graph Laplacian.
  simpa [neumannLaplacian_eqPathGraphLapMatrix n] using
    (SimpleGraph.lapMatrix_mulVec_const_eq_zero
      (R := ℝ) (G := SimpleGraph.pathGraph (n + 1)))

/-- Helper for Example 6.2-extra-1: the discrete first-difference matrix has trivial kernel, so
its `mulVec` action is injective. -/
theorem differenceMatrix_mulVec_injective (n : ℕ) :
    Function.Injective (differenceMatrix n).mulVec := by
  -- Recover the coordinates recursively from the boundary value and the adjacent differences.
  intro x y hxy
  cases n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n =>
      funext i
      induction i using Fin.induction with
      | zero =>
          have hrow := congrFun hxy 0
          simpa [differenceMatrix_mulVec_apply_zero] using hrow
      | succ j ih =>
          have hrow := congrFun hxy (Fin.castSucc j).succ
          have hstep : x j.succ - x j.castSucc = y j.succ - y j.castSucc := by
            simpa [differenceMatrix_mulVec_apply_succ] using hrow
          linarith

/-- Strict positivity of the conductivity samples yields a positive-definite stiffness matrix. -/
theorem stiffnessMatrix_posDefOfPos (n : ℕ) (κ : Fin (n + 1) → ℝ) (hκ : ∀ i, 0 < κ i) :
    Matrix.PosDef (stiffnessMatrix n κ) := by
  -- First make the weighted Gram core positive definite using diagonal positivity and injectivity.
  have hdiag : Matrix.PosDef (Matrix.diagonal κ) := by
    simpa using Matrix.PosDef.diagonal hκ
  have hcore :
      Matrix.PosDef
        (Matrix.transpose (differenceMatrix n) * Matrix.diagonal κ * differenceMatrix n) := by
    simpa using
      hdiag.conjTranspose_mul_mul_same (B := differenceMatrix n)
        (differenceMatrix_mulVec_injective n)
  -- Then scale by the positive mesh factor `(n + 1 : ℝ)`.
  have hscale : 0 < (n + 1 : ℝ) := add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one
  simpa [stiffnessMatrix_eqWeightedGram] using hcore.smul hscale

end OneDimensionalDiffusion
