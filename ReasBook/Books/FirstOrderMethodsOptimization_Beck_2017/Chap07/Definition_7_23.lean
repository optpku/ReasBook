/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_30
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_8

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

section

variable {n : ℕ}

local notation "𝕊" => symmetricMatrices n

/-- The ordered eigenvalue map on the symmetric matrix space `𝕊^n`, sending `X` to the decreasingly
ordered list of its real eigenvalues indexed by `Fin n`. -/
noncomputable def symmetricEigenvalues_7_23 (X : 𝕊) : Fin n → ℝ :=
  (X.property.isHermitian).eigenvalues

-- Proof sketch: unfold `symmetricEigenvalues`; it is defined to be the canonical Hermitian
-- eigenvalue list attached to the underlying symmetric matrix.
/-- Evaluating `symmetricEigenvalues X` at `i` gives the `i`-th entry of the canonical decreasing
eigenvalue list of the symmetric matrix `X`. -/
theorem symmetricEigenvalues_7_23_apply (X : 𝕊) (i : Fin n) :
    symmetricEigenvalues_7_23 X i = (X.property.isHermitian).eigenvalues i := by
  -- This is the defining evaluation rule for `symmetricEigenvalues`.
  rfl

/-- A proper permutation-symmetric eigenvalue factorization of `g` consists of an associated
function on `ℝ^n` whose composition with `symmetricEigenvalues` recovers `g`. -/
inductive HasPermutationSymmetricEigenvalueFactorization (g : 𝕊 → EReal) : Prop
  | mk
      (associatedFunction : (Fin n → ℝ) → EReal)
      (associatedFunction_isProper : IsProperExtendedRealFunction associatedFunction)
      (associatedFunction_isPermutationSymmetric :
        IsPermutationSymmetricFunction associatedFunction)
      (comp_eq : g = associatedFunction ∘ symmetricEigenvalues_7_23) :
      HasPermutationSymmetricEigenvalueFactorization g

private theorem diagonal_mem_symmetricMatrices (x : Fin n → ℝ) :
    Matrix.diagonal (x↓) ∈ symmetricMatrices n := by
  -- Membership in `𝕊^n` is symmetry of the underlying real matrix, and diagonal matrices are
  -- symmetric.
  rw [mem_symmetricMatrices_iff]
  simp

private noncomputable def descendingDiagonalMatrix (x : Fin n → ℝ) : 𝕊 :=
  ⟨Matrix.diagonal (x↓), diagonal_mem_symmetricMatrices x⟩

private theorem antitone_descendingRearrangement (x : Fin n → ℝ) : Antitone (x↓) := by
  -- The tuple `x ∘ Tuple.sort x` is monotone, and composing with `Fin.revPerm` reverses the order.
  simpa [Function.comp_def, descendingRearrangement] using
    (Tuple.monotone_sort x).comp_antitone Fin.rev_anti

private theorem diagonal_eigenvalues_zero_indexed (x : Fin n → ℝ) :
    let A : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (x↓)
    let hA : A.IsHermitian := by
      simp [A]
    hA.eigenvalues₀ = fun j : Fin (Fintype.card (Fin n)) ↦ x↓ (Fin.cast (by simp) j) := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (x↓)
  let hA : A.IsHermitian := by
    simp [A]
  have hcast_anti :
      Antitone (fun j : Fin (Fintype.card (Fin n)) ↦ x↓ (Fin.cast (by simp) j)) := by
    -- Transport the antitonicity of `x↓` across the order-preserving `Fin.cast`.
    simpa using (antitone_descendingRearrangement x).comp_monotone
      (show Monotone (fun j : Fin (Fintype.card (Fin n)) ↦ Fin.cast (by simp) j) by
        intro a b hab
        simpa using hab)
  have hroots :
      A.charpoly.roots =
        Multiset.map
          (RCLike.ofReal ∘ fun j : Fin (Fintype.card (Fin n)) ↦ x↓ (Fin.cast (by simp) j))
          Finset.univ.val := by
    -- The characteristic polynomial of a diagonal matrix factors into linear terms, so its roots
    -- are precisely the diagonal entries counted with multiplicity.
    rw [show A.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((x↓) i)) by
      simpa [A] using Matrix.charpoly_diagonal (x↓)]
    rw [Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort :
      (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) =
        List.ofFn (fun j : Fin (Fintype.card (Fin n)) ↦ x↓ (Fin.cast (by simp) j)) := by
    -- Both sides are the decreasing sort of the same multiset of real roots.
    simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hcast_anti.sortedGE_ofFn
  exact List.ofFn_inj.1 (hA.sort_roots_charpoly_eq_eigenvalues₀.symm.trans hsort)

private theorem symmetricEigenvalues_descendingDiagonalMatrix_eq_comp_perm (x : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), symmetricEigenvalues_7_23 (descendingDiagonalMatrix x) = x↓ ∘ σ := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (x↓)
  let hA : A.IsHermitian := by
    simp [A]
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (α := Fin (Fintype.card (Fin n))) (β := Fin n) (by simp)
  let c : Fin (Fintype.card (Fin n)) ≃ Fin n := finCongr (by simp)
  let σ : Equiv.Perm (Fin n) := e.symm.trans c
  refine ⟨σ, ?_⟩
  ext i
  -- Route correction: `Matrix.IsHermitian.eigenvalues` on `Fin n` is only a reindex of the
  -- canonical sorted spectrum, so the diagonal realization is exact only up to permutation.
  rw [symmetricEigenvalues_7_23_apply]
  change hA.eigenvalues₀ (e.symm i) = x↓ (σ i)
  rw [diagonal_eigenvalues_zero_indexed (n := n) x]
  simp [σ, c, e, finCongr_apply]

private theorem descendingRearrangement_idem (x : Fin n → ℝ) : (x↓)↓ = x↓ := by
  -- The first rearrangement already differs from `x` only by a permutation, so sorting again does
  -- nothing.
  simpa [descendingRearrangement, Function.comp_assoc, Equiv.Perm.coe_mul] using
    (descendingRearrangement_comp_perm x (Tuple.sort x * Fin.revPerm))

-- Proof sketch: unpack the factorization witness, transport the `ne_bot` and nonempty effective
-- domain fields for the associated function across the identity `g = associatedFunction ∘
-- symmetricEigenvalues`, and use the same eigenvalue vector as a witness for the effective domain
-- of `g`.
/-- A permutation-symmetric eigenvalue factorization forces the target function on `𝕊^n` to be
proper. -/
theorem HasPermutationSymmetricEigenvalueFactorization.isProper
    {g : 𝕊 → EReal} (hg : HasPermutationSymmetricEigenvalueFactorization g) :
    IsProperExtendedRealFunction g := by
  rcases hg with ⟨f, hf_proper, hf_perm, hcomp⟩
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_ }
  · intro X
    -- The factorization reduces `g X` to the proper associated function evaluated on eigenvalues.
    rw [hcomp]
    exact hf_proper.ne_bot (symmetricEigenvalues_7_23 X)
  · rcases hf_proper.effective_domain_nonempty with ⟨x, hxmem⟩
    have hx : f x < ⊤ := by
      simpa [mem_effective_domain] using hxmem
    have hx_desc : f x = f x↓ :=
      ((isPermutationSymmetricFunction_iff_forall_eq_descendingRearrangement f).1 hf_perm).2 x
    refine ⟨descendingDiagonalMatrix x, ?_⟩
    -- Realize the decreasing rearrangement `x↓` by a diagonal symmetric matrix and then use
    -- permutation symmetry to remove the harmless reindexing of `symmetricEigenvalues`.
    rw [mem_effective_domain]
    rw [hcomp]
    simp only [Function.comp_apply]
    rcases symmetricEigenvalues_descendingDiagonalMatrix_eq_comp_perm (n := n) x with ⟨σ, hσ⟩
    rw [hσ]
    have hσ_desc : f (x↓ ∘ σ) = f ((x↓ ∘ σ)↓) :=
      ((isPermutationSymmetricFunction_iff_forall_eq_descendingRearrangement f).1 hf_perm).2
        (x↓ ∘ σ)
    rw [hσ_desc, descendingRearrangement_comp_perm, descendingRearrangement_idem]
    simpa [hx_desc] using hx

/-- Definition 7.23: a proper extended-real-valued function on `𝕊^n` is a symmetric spectral
function when it is the composition of the ordered eigenvalue map with some proper permutation
symmetric function on `ℝ^n`. -/
class IsSymmetricSpectralFunction (g : 𝕊 → EReal) : Prop where
  has_permutation_symmetric_eigenvalue_factorization :
    HasPermutationSymmetricEigenvalueFactorization g

/-- A symmetric spectral function on `𝕊^n` is proper because its defining eigenvalue factorization
uses a proper associated function on `ℝ^n`. -/
instance (g : 𝕊 → EReal) [hg : IsSymmetricSpectralFunction g] :
    IsProperExtendedRealFunction g :=
  hg.has_permutation_symmetric_eigenvalue_factorization.isProper

-- Proof sketch: take the representing permutation-symmetric function on `ℝ^n` to be the constant
-- zero function; then `0 = 0 ∘ symmetricEigenvalues` and the helper instance supplies the source
-- properness and permutation symmetry.
/-- The constant zero extended-real-valued function on `𝕊^n` is a symmetric spectral function. -/
instance : IsSymmetricSpectralFunction (fun _ : 𝕊 ↦ (0 : EReal)) := by
  refine ⟨?_⟩
  let hperm : IsPermutationSymmetricFunction (fun _ : Fin n → ℝ ↦ (0 : EReal)) := inferInstance
  -- Use the constant zero profile on `ℝ^n`; its composition with `symmetricEigenvalues` is still
  -- the constant zero function on `𝕊^n`.
  refine
    HasPermutationSymmetricEigenvalueFactorization.mk
      (fun _ : Fin n → ℝ ↦ (0 : EReal))
      hperm.toIsProperExtendedRealFunction
      hperm
      ?_
  ext X
  simp

end
