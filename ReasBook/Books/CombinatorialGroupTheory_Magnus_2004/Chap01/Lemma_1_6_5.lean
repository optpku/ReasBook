/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.LinearAlgebra.Matrix.Rank

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Layer triage:
-- `source-facing`: a matrix over a field whose associated diagonal `q`-linear column-sum form
-- vanishes on every `q`-tuple of rows, together with the resulting rank bound.
-- `core/canonical`: `Matrix (Fin n) (Fin m) K` and the owner invariant `Matrix.rank`.
-- `bridge/view`: the textbook tuple `(i₁, …, i_q)` is represented canonically by a function
-- `Fin q → Fin n`.
-- Domain sampling:
-- 1. `Matrix.rank` is mathlib's owner invariant for matrix-rank statements.
-- 2. `Matrix.rank_eq_finrank_span_row` is the direct owner bridge from matrix rank to the
--    dimension of the row space, which is the linear-algebra owner viewpoint used in the
--    textbook proof.
-- 3. `Matrix.rank_le_width` is the canonical ambient width bound for matrices
--    `Matrix (Fin n) (Fin m) K`.
-- 4. `MultilinearMap.mkPiRing` is the canonical owner declaration for the `q`-fold product map
--    on `K`, so the diagonal `q`-linear form belongs proof-side rather than as a separate public
--    wrapper around the matrix statement.
--
-- Best owner abstraction:
-- the public statement should live on the matrix owner itself, as a theorem in namespace
-- `Matrix`. The vanishing `q`-fold column-product condition is primitive source data, while the
-- diagonal multilinear form and row-space reformulation stay proof-side derived API.
--
-- Primitive vs. derived:
-- the primitive source data are the matrix `A`, the existence of an element `ω` with `ω^q = -1`,
-- and the vanishing of all `q`-fold column products. The diagonal multilinear form on rows and
-- the rank bound are derived owner-level constructions attached to `A`.
namespace Matrix

variable {K : Type*} [Field K] {q n m : ℕ}

/-- Lemma 1-6-5: let `q > 1`, let `A` be an `n × m` matrix over a field `K`, and suppose `K`
contains an element `ω` with `ω ^ q = -1`. If for every `q`-tuple of row indices the sum of the
corresponding `q`-fold column products is zero, then the rank of `A` is at most `m / 2`. -/
-- Proof sketch: encode each row of `A` as a vector in `K^m` and the given vanishing condition as
-- the statement that the associated diagonal `q`-linear form vanishes on the span of the rows.
-- Following the textbook induction on `m`, use the existence of `ω` with `ω^q = -1` to reduce to
-- a null subspace in dimension `m - 2`, and then identify the resulting row-space dimension with
-- `A.rank` through `Matrix.rank_eq_finrank_span_row`.
theorem rank_le_half_width_of_vanishing_qfold_column_products
    (A : Matrix (Fin n) (Fin m) K) (hq : 1 < q) (hω : ∃ ω : K, ω ^ q = -1)
    (hvanish : ∀ rows : Fin q → Fin n, ∑ j, ∏ t, A (rows t) j = 0) :
    A.rank ≤ m / 2 := sorry

end Matrix
