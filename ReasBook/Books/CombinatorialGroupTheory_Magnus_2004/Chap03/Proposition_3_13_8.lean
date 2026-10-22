/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MatrixGroups

universe u

set_option autoImplicit false

/-!
Primary domain: Bass-Serre decompositions of matrix groups over polynomial rings.

Layer triage:
- `source-facing`: the two concrete subgroups of `GL(2, F[t])`, namely the constant-coefficient
  copy of `GL(2, F)` and the upper triangular subgroup `T(F[t])`, with common subgroup `T(F)`.
- `core/canonical`: `Subgroup.amalgamatedProduct` and
  `Subgroup.amalgamatedProductComparison` from Proposition `3-12-5`, built on top of mathlib's
  `Monoid.PushoutI`, together with `Matrix.BlockTriangular` for the upper triangular subgroup.
- `bridge/view`: the constant-coefficient embeddings into `GL(2, F[t])` and the coordinate-level
  characterization `g 1 0 = 0` of membership in the upper triangular subgroup.

Domain sampling:
1. Proposition `3-12-5` already exposes `Subgroup.amalgamatedProduct` and
   `Subgroup.amalgamatedProductComparison` as the chapter owner/bridge API for a two-factor
   amalgamated product over a subgroup intersection.
2. `Matrix.BlockTriangular`, `Matrix.blockTriangular_one`, `Matrix.BlockTriangular.mul`, and
   `Matrix.blockTriangular_inv_of_blockTriangular` are the canonical owner lemmas for upper
   triangularity of matrices.
3. `GL (Fin 2) R` is the canonical owner for invertible `2 × 2` matrices over `R`.
4. `Matrix.GeneralLinearGroup.map` is the canonical way to embed `GL(2, F)` into
   `GL(2, F[t])` along the coefficient homomorphism `Polynomial.C`.
5. `Subgroup.map`, `Subgroup.range`, and `Subgroup.inf` are the canonical subgroup-level APIs for
   the constant copy of `GL(2, F)`, the copy of `T(F)`, and the identified intersection.

Primitive vs. derived:
- primitive data: the two actual subgroups inside `GL(2, F[t])`, with the upper triangular one
  defined by the intrinsic `Matrix.BlockTriangular` predicate;
- derived data: the coordinate lemma `g 1 0 = 0` for that subgroup, the constant-coefficient
  image of `T(F)` inside `GL(2, F[t])`, the two-factor amalgamated product, and its canonical
  comparison map into the ambient matrix group.
-/

section

variable {R : Type u} [CommRing R]

/-- The subgroup `T(R)` of invertible upper triangular `2 × 2` matrices over `R`. -/
def upperTriangularSubgroup : Subgroup (GL (Fin 2) R) where
  carrier := {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R).BlockTriangular id}
  one_mem' := by
    simpa using
      (Matrix.blockTriangular_one : Matrix.BlockTriangular (1 : Matrix (Fin 2) (Fin 2) R) id)
  mul_mem' := by
    intro a b ha hb
    simpa using Matrix.BlockTriangular.mul ha hb
  inv_mem' := by
    intro g hg
    let _ := g.invertible
    simpa using
      (Matrix.blockTriangular_inv_of_blockTriangular hg :
        ((g : Matrix (Fin 2) (Fin 2) R)⁻¹).BlockTriangular id)

/-- For `2 × 2` matrices, upper triangularity is equivalent to vanishing lower-left entry. -/
@[simp] theorem mem_upperTriangularSubgroup_iff {g : GL (Fin 2) R} :
    g ∈ upperTriangularSubgroup ↔ g 1 0 = 0 := by
  constructor
  · intro hg
    exact hg (show (0 : Fin 2) < 1 by decide)
  · intro hg i j hij
    have hi : i = 1 := by
      apply Fin.ext
      have hi_lt : (i : ℕ) < 2 := i.2
      have hj_lt : (j : ℕ) < 2 := j.2
      have hji : (j : ℕ) < i := by
        simpa using hij
      omega
    subst hi
    have hj : j = 0 := by
      apply Fin.ext
      have hji : (j : ℕ) < 1 := by
        simpa using hij
      omega
    subst hj
    simpa using hg

end

section

variable (F : Type u) [Field F]

/-- The constant-coefficient copy of `GL(2, F)` inside `GL(2, F[t])`. -/
noncomputable def constantLinearSubgroup : Subgroup (GL (Fin 2) (Polynomial F)) :=
  (Matrix.GeneralLinearGroup.map (Polynomial.C : F →+* Polynomial F)).range

/-- The constant image of `T(F)` is the intersection of the constant copy of `GL(2, F)` with the
upper triangular subgroup of `GL(2, F[t])`. -/
-- Proof sketch: a constant matrix lies in the upper triangular subgroup of `GL(2, F[t])`
-- exactly when its lower-left entry is the zero polynomial, which is equivalent to the original
-- lower-left entry in `F` being zero.
theorem map_upperTriangularSubgroup_eq_inf :
    upperTriangularSubgroup.map
        (Matrix.GeneralLinearGroup.map (Polynomial.C : F →+* Polynomial F)) =
      constantLinearSubgroup F ⊓ upperTriangularSubgroup :=
  sorry

/-- Proposition 3-13-8: the canonical comparison map from the amalgamated free product of the
constant copy of `GL(2, F)` and the upper triangular subgroup `T(F[t])`, with the corresponding
subgroup `T(F)` identified, onto `GL(2, F[t])` is bijective. -/
-- Proof sketch: let `GL(2, F[t])` act on the Behr tree attached to the valuation at infinity on
-- `F(t)`. The quotient graph is an edge; its two vertex stabilizers are the constant copy of
-- `GL(2, F)` and `T(F[t])`, and the edge stabilizer is `T(F)`. Bass-Serre theory then identifies
-- the ambient group with the amalgamated free product of those two stabilizers; the bridge theorem
-- `map_upperTriangularSubgroup_eq_inf` identifies the constant image of the source-facing subgroup
-- `T(F)` with the intersection used by `Subgroup.amalgamatedProductComparison`.
theorem glPolynomial_amalgamatedProductComparison_bijective :
    Function.Bijective
      (Subgroup.amalgamatedProductComparison
        (constantLinearSubgroup F)
        (upperTriangularSubgroup : Subgroup (GL (Fin 2) (Polynomial F)))) := by
  sorry

end
