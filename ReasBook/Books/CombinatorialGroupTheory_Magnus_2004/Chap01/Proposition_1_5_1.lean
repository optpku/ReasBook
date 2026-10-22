/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Corollary_1_4_16
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_5_2

open MulAction Matrix.GeneralLinearGroup
open scoped commutatorElement

universe u v

noncomputable section

section

variable {F : Type v} [Group F]

open RankTwoFreeGroup

namespace FreeGroupBasis

-- Layer triage:
-- `source-facing`: a rank-two basis `basis : FreeGroupBasis (Fin 2) F` and the cyclic word
-- determined by the commutator of its two basis elements.
-- `core/canonical`: the basis-induced action `basis.cyclicWordMulAction` on `CyclicWord (Fin 2)`,
-- the owner subgroup `MulAction.stabilizer`, the bridge `basis.toGL : MulAut F →* GL (Fin 2) ℤ`,
-- and the determinant morphism on `GL (Fin 2) ℤ`.
-- `bridge/view`: `commutatorCyclicWord` is the standard rank-two commutator word, while the
-- textbook subgroup `SA(F)` is expressed directly by the determinant-one kernel
-- `(det.comp basis.toGL).ker`.
--
-- Domain sampling:
-- 1. `CyclicWord X` and the induced action from Proposition `1-5-2` are the chapter owner API for
--    cyclic words and their automorphic images.
-- 2. `MulAction.stabilizer` is mathlib's owner subgroup for automorphisms fixing a cyclic word.
-- 3. `FreeGroupBasis.toGL` from Corollary `1-4-16` is the canonical bridge from automorphisms of
--    a rank-two free group to `GL (Fin 2) ℤ`.
-- 4. `Matrix.GeneralLinearGroup.det` is the owner determinant morphism on `GL (Fin 2) ℤ`.
--
-- Primitive vs. derived:
-- the primitive source data are only the chosen rank-two basis; the commutator cyclic words come
-- from the source-facing owner declarations `RankTwoFreeGroup.commutatorCyclicWord` and
-- `RankTwoFreeGroup.inverseCommutatorCyclicWord` imported from Proposition `1-5-2`. The
-- stabilizer subgroup and the determinant-one kernel `(det.comp basis.toGL).ker` are derived
-- owner constructions built from those data.

/-- Proposition 1-5-1 (1): every automorphism of a rank-two free group carries the commutator
cyclic word to itself or to its inverse. -/
-- Proof sketch: it is enough to check the claim on elementary Nielsen automorphisms generating
-- `Aut(F)`. Direct calculations on the commutator show that proper generators fix the cyclic word
-- and improper generators send it to the inverse cyclic word.
theorem smul_commutatorCyclicWord_eq_or_eq_inverse
    (basis : FreeGroupBasis (Fin 2) F) (α : MulAut F) :
    letI := basis.cyclicWordMulAction
    α • commutatorCyclicWord = commutatorCyclicWord ∨
      α • commutatorCyclicWord = inverseCommutatorCyclicWord := sorry

/-- Proposition 1-5-1 (2): the stabilizer `A_w` of the commutator cyclic word is the subgroup
`SA(F)` of proper automorphisms. -/
-- Proof sketch: combine the previous dichotomy with the determinant description of proper
-- automorphisms through `basis.toGL`; determinant `1` is exactly the case where the commutator
-- cyclic word is fixed rather than inverted.
theorem commutatorCyclicWord_stabilizer_eq_det_comp_toGL_ker
    (basis : FreeGroupBasis (Fin 2) F) :
    letI := basis.cyclicWordMulAction
    stabilizer (MulAut F) commutatorCyclicWord = (det.comp basis.toGL).ker := sorry

/-- Proposition 1-5-1 (3): the subgroup `SA(F)` of proper automorphisms has index `2` in
`Aut(F)`. -/
-- Proof sketch: the determinant of `basis.toGL α` detects whether `α` is proper or improper, and
-- its image is exactly `{1, -1}`. Therefore the determinant-one kernel has index `2`.
theorem det_comp_toGL_ker_index_eq_two (basis : FreeGroupBasis (Fin 2) F) :
    ((det.comp basis.toGL).ker).index = 2 := sorry

end FreeGroupBasis

end
