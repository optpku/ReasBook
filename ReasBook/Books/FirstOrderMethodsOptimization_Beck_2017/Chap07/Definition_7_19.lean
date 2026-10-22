/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_9
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_18
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Proposition_7_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Function

noncomputable section

namespace Matrix

section

variable {m n : ℕ}

/- Definition 7.19 is `source-facing`: it strengthens the spectral-function owner from
Definition 7.18 by requiring the associated function on singular-value coordinates to be
absolutely permutation symmetric. The relevant existing owners are `Matrix.IsSpectralFunction`,
`singular_value_function`, and `Function.IsAbsolutelyPermutationSymmetric`. -/

/-- An absolutely permutation symmetric singular-value factorization of `g` consists of an
associated function on `ℝ^(min m n)` whose composition with `singular_value_function` recovers
`g`. -/
inductive HasAbsolutelyPermutationSymmetricSingularValueFactorization
    (g : Matrix (Fin m) (Fin n) ℝ → EReal) : Prop
  | mk
      (associatedFunction : (Fin (min m n) → ℝ) → EReal)
      (associatedFunction_isAbsolutelyPermutationSymmetric :
        Function.IsAbsolutelyPermutationSymmetric associatedFunction)
      (comp_eq : g = associatedFunction ∘ singular_value_function) :
      HasAbsolutelyPermutationSymmetricSingularValueFactorization g

/-- Helper for Definition 7.19: the Gram matrix of a rectangular diagonal matrix is the diagonal
matrix whose first `min m n` entries are the squared diagonal values and whose remaining entries
are zero. -/
theorem rectangularDiagonal_conjTranspose_mul_eq_squared_tail
    (x : Fin (min m n) → ℝ) :
    (rectangularDiagonal x)ᴴ * rectangularDiagonal x =
      Matrix.diagonal
        (fun j : Fin n ↦ if h : j.1 < min m n then x ⟨j.1, h⟩ ^ 2 else 0) := by
  classical
  -- Compute the Gram matrix entrywise by isolating the unique common diagonal term.
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.mul_apply]
    by_cases hi : i.1 < m
    · let ii : Fin m := ⟨i.1, hi⟩
      rw [Fintype.sum_eq_single ii]
      · -- On the diagonal, the surviving term is the square of the corresponding diagonal entry.
        have hmin : i.1 < min m n := Nat.lt_min.mpr ⟨hi, i.2⟩
        rw [Matrix.diagonal_apply, if_pos rfl]
        simpa [hmin, pow_two, rectangularDiagonal, ii]
      · intro k hk
        -- Away from the matching row index, the summand is zero.
        have hk' : k.1 ≠ i.1 := by
          intro hki
          apply hk
          ext
          exact hki
        simp [rectangularDiagonal, hk']
    · have hk' : ∀ k : Fin m, k.1 ≠ i.1 := by
        intro k hki
        exact hi (hki ▸ k.2)
      have hsum :
          (∑ k : Fin m, ((rectangularDiagonal x)ᴴ i k) * rectangularDiagonal x k i) = 0 := by
        -- If the row index lies past `m`, every entry in the `i`-th column is zero.
        apply Fintype.sum_eq_zero
        intro k
        simp [rectangularDiagonal, hk' k]
      have hmin : ¬ i.1 < min m n := by
        intro h
        exact hi (Nat.lt_of_lt_of_le h (Nat.min_le_left _ _))
      rw [Matrix.diagonal_apply, if_pos rfl]
      simpa [hmin] using hsum
  · rw [Matrix.diagonal_apply]
    have hmul : (((rectangularDiagonal x)ᴴ * rectangularDiagonal x) i j) = 0 := by
      rw [Matrix.mul_apply]
      by_cases hi : i.1 < m
      · let ii : Fin m := ⟨i.1, hi⟩
        rw [Fintype.sum_eq_single ii]
        · -- Off the diagonal, the surviving term vanishes because the column indices differ.
          have hij' : ii.1 ≠ j.1 := by
            intro h
            apply hij
            ext
            simpa [ii] using h
          simp [rectangularDiagonal, hij']
        · intro k hk
          have hk' : k.1 ≠ i.1 := by
            intro hki
            apply hk
            ext
            exact hki
          simp [rectangularDiagonal, hk']
      · have hk' : ∀ k : Fin m, k.1 ≠ i.1 := by
          intro k hki
          exact hi (hki ▸ k.2)
        have hsum :
            (∑ k : Fin m, ((rectangularDiagonal x)ᴴ i k) * rectangularDiagonal x k j) = 0 := by
          -- Again, if the would-be matching row is unavailable, every summand is zero.
          apply Fintype.sum_eq_zero
          intro k
          simp [rectangularDiagonal, hk' k]
        simpa using hsum
    rw [if_neg hij]
    exact hmul

/-- Helper for Definition 7.19: squaring a nonnegative antitone diagonal profile and appending
zeros preserves antitonicity. -/
theorem squared_tail_antitone (x : Fin (min m n) → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i) (hx_antitone : Antitone x) :
    Antitone (fun j : Fin n ↦ if h : j.1 < min m n then x ⟨j.1, h⟩ ^ 2 else 0) := by
  -- Compare either two genuine diagonal entries or a diagonal entry with the zero tail.
  intro i j hij
  by_cases hi : i.1 < min m n
  · by_cases hj : j.1 < min m n
    · have hxj : 0 ≤ x ⟨j.1, hj⟩ := hx_nonneg _
      have hle : x ⟨j.1, hj⟩ ≤ x ⟨i.1, hi⟩ := hx_antitone (by simpa using hij)
      have hsquare : x ⟨j.1, hj⟩ ^ 2 ≤ x ⟨i.1, hi⟩ ^ 2 := pow_le_pow_left₀ hxj hle 2
      simpa only [hi, hj] using hsquare
    · have hxi : 0 ≤ x ⟨i.1, hi⟩ := hx_nonneg _
      simpa only [hi, hj] using sq_nonneg (x ⟨i.1, hi⟩)
  · have hj : ¬ j.1 < min m n := by
      intro hj
      exact hi (lt_of_le_of_lt (show i.1 ≤ j.1 by simpa using hij) hj)
    simp [hi, hj]

/-- Helper for Definition 7.19: a real diagonal matrix with antitone diagonal entries has ordered
eigenvalue list equal to that diagonal. -/
theorem diagonal_eigenvalues_zero_indexed_eq (y : Fin n → ℝ) (hy : Antitone y) :
    let A : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal y
    let hA : A.IsHermitian := by simp [A]
    hA.eigenvalues₀ = fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j) := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal y
  let hA : A.IsHermitian := by
    simp [A]
  have hcast_anti :
      Antitone (fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j)) := by
    -- Transport antitonicity across the standard `Fin.cast` reindexing.
    simpa using hy.comp_monotone
      (show Monotone (fun j : Fin (Fintype.card (Fin n)) ↦ Fin.cast (by simp) j) by
        intro a b hab
        simpa using hab)
  have hroots :
      A.charpoly.roots =
        Multiset.map
          (RCLike.ofReal ∘ fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j))
          Finset.univ.val := by
    -- The characteristic polynomial of a diagonal matrix factors into the diagonal linear terms.
    rw [show A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (y i)) by
      simpa [A] using Matrix.charpoly_diagonal y]
    rw [Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort :
      (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) =
        List.ofFn (fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j)) := by
    -- Both sides are the decreasing sort of the same real root multiset.
    simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hcast_anti.sortedGE_ofFn
  exact List.ofFn_inj.1 (hA.sort_roots_charpoly_eq_eigenvalues₀.symm.trans hsort)

/-- Helper for Definition 7.19: a rectangular diagonal matrix with a nonnegative antitone diagonal
profile has that profile as its ordered singular-value vector. -/
theorem singular_value_function_rectangularDiagonal_eq_of_nonneg_antitone
    (x : Fin (min m n) → ℝ) (hx_nonneg : ∀ i, 0 ≤ x i) (hx_antitone : Antitone x) :
    singular_value_function (rectangularDiagonal x) = x := by
  let y : Fin n → ℝ := fun j ↦ if h : j.1 < min m n then x ⟨j.1, h⟩ ^ 2 else 0
  have hgram : (rectangularDiagonal x)ᴴ * rectangularDiagonal x = Matrix.diagonal y := by
    -- The Gram matrix is diagonal with squared diagonal entries and a zero tail.
    simpa [y] using rectangularDiagonal_conjTranspose_mul_eq_squared_tail (m := m) (n := n) x
  have hy_antitone : Antitone y := squared_tail_antitone x hx_nonneg hx_antitone
  have hy_hermitian : (Matrix.diagonal y).IsHermitian := by
    simp
  have hdiag_eigs :
      ((Matrix.isSymmetric_toEuclideanLin_iff).2 hy_hermitian).eigenvalues finrank_euclideanSpace =
        fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j) := by
    -- The ordered eigenvalues of the diagonal Gram matrix are exactly its diagonal entries.
    simpa [Matrix.IsHermitian.eigenvalues₀] using
      diagonal_eigenvalues_zero_indexed_eq (n := n) y hy_antitone
  ext i
  have hi_n : (i : ℕ) < n := lt_of_lt_of_le i.2 (Nat.min_le_right _ _)
  have hsquare : (singular_value_function (rectangularDiagonal x) i) ^ 2 = x i ^ 2 := by
    have hgram' : (rectangularDiagonal x)ᵀ * rectangularDiagonal x = Matrix.diagonal y := by
      simpa using hgram
    have hcomp :
        LinearMap.adjoint (Matrix.toEuclideanLin (rectangularDiagonal x)) ∘ₗ
            Matrix.toEuclideanLin (rectangularDiagonal x) =
          Matrix.toEuclideanLin (Matrix.diagonal y) := by
      -- Translate the Gram matrix identity from matrices to Euclidean linear maps.
      rw [show LinearMap.adjoint (Matrix.toEuclideanLin (rectangularDiagonal x)) =
          Matrix.toEuclideanLin ((rectangularDiagonal x)ᴴ) by
        simpa using
          (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := rectangularDiagonal x)).symm]
      ext v j
      simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, hgram'] using
        congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ (M *ᵥ v.ofLp) j) hgram'
    have hsq :
        (Matrix.toEuclideanLin (rectangularDiagonal x)).singularValues i ^ 2 =
          ((Matrix.isSymmetric_toEuclideanLin_iff).2 hy_hermitian).eigenvalues
            finrank_euclideanSpace ⟨i.1, by simpa using hi_n⟩ := by
      -- Singular values are the square roots of the ordered eigenvalues of the Gram operator.
      simpa [hcomp] using
        (LinearMap.sq_singularValues_of_lt
          (T := Matrix.toEuclideanLin (rectangularDiagonal x))
          (hn := finrank_euclideanSpace) (i := i.1) (by simpa using hi_n))
    rw [singular_value_function_apply]
    rw [hsq, hdiag_eigs]
    have hyi : y ⟨i.1, by simpa using hi_n⟩ = x i ^ 2 := by
      dsimp [y]
      rw [if_pos i.2]
    simpa [hyi]
  have hσ_nonneg : 0 ≤ singular_value_function (rectangularDiagonal x) i :=
    singular_value_function_nonneg (rectangularDiagonal x) i
  have hx_i_nonneg : 0 ≤ x i := hx_nonneg i
  -- Nonnegative numbers with the same square are equal.
  nlinarith

/-- Helper for Definition 7.19: every vector in `ℝ^(min m n)` can be realized as the ordered
singular-value vector of some matrix after passing to the decreasing rearrangement of its absolute
coordinates. -/
theorem exists_matrix_with_singular_value_function_eq_abs_descendingRearrangement
    (x : Fin (min m n) → ℝ) :
    ∃ X : Matrix (Fin m) (Fin n) ℝ,
      singular_value_function X = Function.descendingRearrangement (fun i ↦ |x i|) := by
  let y : Fin (min m n) → ℝ := Function.descendingRearrangement (fun i ↦ |x i|)
  have hy_nonneg : ∀ i, 0 ≤ y i := by
    intro i
    -- Every coordinate of the rearranged absolute-value profile is nonnegative.
    rw [show y i = Function.descendingRearrangement (fun j ↦ |x j|) i by rfl]
    rw [Function.descendingRearrangement_apply]
    let L := (List.ofFn fun j : Fin (min m n) ↦ |x j|).mergeSort (· ≥ ·)
    have hiL : i.1 < L.length := by
      simpa [L] using i.2
    rw [show L.getD i 0 = L.get ⟨i.1, hiL⟩ by
      simpa [L] using (List.getD_eq_get L 0 ⟨i.1, hiL⟩)]
    have hmem_sorted : L.get ⟨i.1, hiL⟩ ∈ L := List.get_mem L ⟨i.1, hiL⟩
    have hmem_original : L.get ⟨i.1, hiL⟩ ∈ List.ofFn (fun j : Fin (min m n) ↦ |x j|) := by
      exact (List.mem_mergeSort).1 hmem_sorted
    rcases (List.mem_ofFn).1 hmem_original with ⟨j, hj⟩
    simpa [L, hj] using abs_nonneg (x j)
  have hy_antitone : Antitone y := by
    let L := (List.ofFn fun j : Fin (min m n) ↦ |x j|).mergeSort (· ≥ ·)
    have hpair : L.Pairwise (fun a b : ℝ ↦ a ≥ b) := by
      simpa [L] using
        (List.pairwise_mergeSort' (r := fun a b : ℝ ↦ a ≥ b)
          (List.ofFn fun j : Fin (min m n) ↦ |x j|))
    have hanti_get : Antitone L.get := hpair.sortedGE.antitone_get
    -- The defining sorted list of the rearrangement is weakly decreasing.
    intro i j hij
    have hiL : i.1 < L.length := by
      simpa [L] using i.2
    have hjL : j.1 < L.length := by
      simpa [L] using j.2
    rw [show y i = L.get ⟨i.1, hiL⟩ by
      rw [show y i = Function.descendingRearrangement (fun k ↦ |x k|) i by rfl]
      rw [Function.descendingRearrangement_apply]
      simpa [L] using (List.getD_eq_get L 0 ⟨i.1, hiL⟩)]
    rw [show y j = L.get ⟨j.1, hjL⟩ by
      rw [show y j = Function.descendingRearrangement (fun k ↦ |x k|) j by rfl]
      rw [Function.descendingRearrangement_apply]
      simpa [L] using (List.getD_eq_get L 0 ⟨j.1, hjL⟩)]
    exact hanti_get (by simpa using hij)
  refine ⟨rectangularDiagonal y, ?_⟩
  -- Realize the canonical source-side representative by a rectangular diagonal matrix.
  exact singular_value_function_rectangularDiagonal_eq_of_nonneg_antitone y hy_nonneg hy_antitone

/-- Helper for Definition 7.19: the constant zero singular-value profile factors the constant zero
matrix-valued function through `singular_value_function`. -/
theorem matrix_const_zero_symmetric_factorization :
    (fun _ : Matrix (Fin m) (Fin n) ℝ ↦ (0 : EReal)) =
      (fun _ : (Fin (min m n) → ℝ) ↦ (0 : EReal)) ∘ singular_value_function := by
  -- Both sides evaluate to zero on every matrix.
  ext X
  simp [Function.comp_apply]

-- Proof sketch: unpack the factorization witness, transport the `ne_bot` and nonempty effective
-- domain fields for the associated function across the identity `g = associatedFunction ∘
-- singular_value_function`, and use the same singular-value vector as a witness for the effective
-- domain of `g`.
/-- An absolutely permutation symmetric singular-value factorization forces the matrix-valued
function to be proper. -/
theorem HasAbsolutelyPermutationSymmetricSingularValueFactorization.isProper
    {g : Matrix (Fin m) (Fin n) ℝ → EReal}
    (hg : HasAbsolutelyPermutationSymmetricSingularValueFactorization g) :
    IsProperExtendedRealFunction g := by
  rcases hg with ⟨f, hf_abs, hcomp⟩
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_ }
  · intro X
    -- The factorization reduces `g X` to the associated absolutely permutation symmetric profile.
    rw [hcomp]
    exact hf_abs.ne_bot (singular_value_function X)
  · rcases hf_abs.effective_domain_nonempty with ⟨x, hx_mem⟩
    have hx : f x < ⊤ := by
      simpa [mem_effective_domain] using hx_mem
    have hx_desc :
        f x = f (Function.descendingRearrangement (fun i ↦ |x i|)) :=
      hf_abs.map_eq_abs_descendingRearrangement x
    rcases
      exists_matrix_with_singular_value_function_eq_abs_descendingRearrangement (m := m) (n := n) x
        with ⟨X, hX⟩
    refine ⟨X, ?_⟩
    -- Realize the finite witness on singular-value coordinates by an actual matrix.
    simpa [mem_effective_domain, hcomp, hX, hx_desc] using hx

/-- Definition 7.19: a proper extended-real-valued function on `ℝ^(m × n)` is symmetric spectral
when it is the composition of the singular-value map with some absolutely permutation symmetric
proper function on `ℝ^(min m n)`. -/
class IsSymmetricSpectralFunction (g : Matrix (Fin m) (Fin n) ℝ → EReal) : Prop where
  has_absolutely_permutation_symmetric_singular_value_factorization :
    HasAbsolutelyPermutationSymmetricSingularValueFactorization g

/-- A symmetric spectral function is proper because its defining singular-value factorization uses
an absolutely permutation symmetric associated function. -/
instance (g : Matrix (Fin m) (Fin n) ℝ → EReal) [hg : IsSymmetricSpectralFunction g] :
    IsProperExtendedRealFunction g :=
  hg.has_absolutely_permutation_symmetric_singular_value_factorization.isProper

-- Proof sketch: if `g = f ∘ singular_value_function` with `f` absolutely permutation symmetric,
-- then the induced properness instance on `g` and the same associated function supply the
-- associated-function witness required by
-- `Matrix.IsSpectralFunction`.
/-- A symmetric spectral function is spectral. -/
instance {g : Matrix (Fin m) (Fin n) ℝ → EReal} [IsSymmetricSpectralFunction g] :
    IsSpectralFunction g := by
  let hg : IsSymmetricSpectralFunction g := inferInstance
  rcases hg.has_absolutely_permutation_symmetric_singular_value_factorization with
    ⟨f, hf_abs, hcomp⟩
  refine
    { toIsProperExtendedRealFunction := inferInstance
      associatedFunction_exists := ?_ }
  -- Reuse the same associated function; absolute permutation symmetry already contains properness.
  exact
    ⟨f,
      { ne_bot := hf_abs.ne_bot
        effective_domain_nonempty := hf_abs.effective_domain_nonempty },
      hcomp⟩

-- Proof sketch: one direction extracts the singular-value factorization witness from the class and
-- then uses the previous helper theorem to obtain properness of `g`; the converse packages a
-- properness proof together with the associated function into the factorization helper.
/-- A function on real `m × n` matrices is symmetric spectral exactly when it is proper and equals
an absolutely permutation symmetric associated function on singular-value coordinates composed with
`singular_value_function`. -/
theorem isSymmetricSpectralFunction_iff_exists_associatedFunction
    (g : Matrix (Fin m) (Fin n) ℝ → EReal) :
    IsSymmetricSpectralFunction g ↔
      IsProperExtendedRealFunction g ∧
        ∃ f : (Fin (min m n) → ℝ) → EReal,
          Function.IsAbsolutelyPermutationSymmetric f ∧
            g = f ∘ singular_value_function := by
  constructor
  · intro hg
    rcases hg.has_absolutely_permutation_symmetric_singular_value_factorization with
      ⟨f, hf_abs, hcomp⟩
    -- Unpack the class witness and read properness from the previous theorem.
    exact ⟨inferInstance, ⟨f, hf_abs, hcomp⟩⟩
  · rintro ⟨_, ⟨f, hf_abs, hcomp⟩⟩
    -- Repackage the given absolutely permutation symmetric factorization into the class.
    exact
      ⟨HasAbsolutelyPermutationSymmetricSingularValueFactorization.mk f hf_abs hcomp⟩

-- Proof sketch: choose the constant zero function on singular-value coordinates; Definition 7.9
-- already provides its absolute permutation symmetry, and its composition with
-- `singular_value_function` is again the constant zero function.
/-- The constant zero extended-real-valued function on real `m × n` matrices is symmetric
spectral. -/
instance : IsSymmetricSpectralFunction (fun _ : Matrix (Fin m) (Fin n) ℝ ↦ (0 : EReal)) := by
  refine ⟨?_⟩
  let habs :
      Function.IsAbsolutelyPermutationSymmetric
        (fun _ : (Fin (min m n) → ℝ) ↦ (0 : EReal)) := inferInstance
  -- Use the constant zero associated profile from Definition 7.9 and the factorization from
  -- Definition 7.18.
  exact
    HasAbsolutelyPermutationSymmetricSingularValueFactorization.mk
      (fun _ : (Fin (min m n) → ℝ) ↦ (0 : EReal))
      habs
      matrix_const_zero_symmetric_factorization

end

end Matrix
