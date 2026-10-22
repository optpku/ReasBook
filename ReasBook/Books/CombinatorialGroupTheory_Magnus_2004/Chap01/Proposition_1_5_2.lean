/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_5
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_25

universe u v

open MulAction QuotientGroup
open scoped commutatorElement

noncomputable section

section

variable {X : Type u}

namespace FreeGroupBasis

variable {F : Type v} [Group F]

/-- The basis-induced `Aut(F)`-action on cyclic words over the basis alphabet `X`. -/
@[reducible] noncomputable def cyclicWordMulAction (basis : FreeGroupBasis X F) :
    MulAction (MulAut F) (CyclicWord X) :=
  MulAction.compHom (CyclicWord X)
    (MulAut.congr basis.repr : MulAut F →* MulAut (FreeGroup X))

end FreeGroupBasis

namespace RankTwoFreeGroup

/-- The standard commutator `[x, y]` in the rank-two free group on `Fin 2`. -/
def commutator : FreeGroup (Fin 2) :=
  ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆

/-- The cyclic word determined by the rank-two commutator `[x, y]`. -/
def commutatorCyclicWord : CyclicWord (Fin 2) :=
  CyclicWord.conjClassesEquiv.symm <| ConjClasses.mk commutator

/-- The cyclic word determined by the inverse commutator `[x, y]⁻¹`. -/
def inverseCommutatorCyclicWord : CyclicWord (Fin 2) :=
  CyclicWord.conjClassesEquiv.symm <| ConjClasses.mk commutator⁻¹

end RankTwoFreeGroup

-- Layer triage:
-- `source-facing`: a cyclic word `w : CyclicWord X` in the free group on a basis `X`, together
-- with the exceptional rank-two commutator-power shape.
-- `core/canonical`: the action of `MulAut (FreeGroup X)` on `CyclicWord X`, the owner subgroup
-- `MulAction.stabilizer`, the inner automorphism owner subgroup
-- `MulAut.innerAutomorphismSubgroup (FreeGroup X)`, the subgroup image `Subgroup.map`, and the
-- owner index quantity `Subgroup.index`.
-- `bridge/view`: the textbook quotient `Aut(F) / JA(F)` is rendered as the quotient modulo the
-- canonical inner automorphism subgroup, and the exceptional source case is expressed by
-- transporting the standard commutator from `FreeGroup (Fin 2)` across a basis equivalence and
-- then passing to the conjugacy class of the resulting nonzero integral power.
-- Domain sampling:
-- 1. The `MulAction (MulAut (FreeGroup X)) (CyclicWord X)` instance from Definition `1-4-17`
--    is the chapter owner action of free-group automorphisms on cyclic words.
-- 2. `MulAction.stabilizer` is mathlib's owner subgroup for point stabilizers under a group
--    action.
-- 3. `MulAut.innerAutomorphismSubgroup` from Proposition `1-4-5` is the chapter owner subgroup
--    of inner automorphisms.
-- 4. `Subgroup.map` and `Subgroup.index` are the owner APIs for the image of a subgroup in a
--    quotient group and for finite-versus-infinite index.
-- Primitive vs. derived:
-- the primitive source data are only the cyclic word `w`, the nontriviality hypothesis that its
-- conjugacy class is nontrivial, and the free-basis rank condition `1 < Nat.card X`; the
-- stabilizer in `Aut(F(X))`, its image in the quotient by inner automorphisms, and the
-- index-zero reformulation of infinite index are all derived owner API.
/-- Proposition 1-5-2: let `w` be a nontrivial cyclic word in a free group of rank at least `2`.
If `w` is not the cyclic word of a nonzero power of a basic commutator in rank `2`, then the
image of its stabilizer in `Aut(F) / JA(F)` has infinite index. -/
-- Proof sketch: assume the image of the stabilizer has finite index in the `JA`-quotient. Then the
-- orbit of `w` under automorphisms has bounded cyclic length modulo `JA`, so repeated Nielsen
-- moves cannot create arbitrarily long cyclic representatives. Whitehead's length-growth argument
-- forces the cyclic word to alternate between two basis letters and hence to be a nonzero power
-- of the rank-two commutator.
theorem cyclicWord_stabilizer_image_in_JAQuotient_index_eq_zero_of_not_rankTwo_commutator_power
    (w : CyclicWord X) (hX : 1 < Nat.card X) (hw : w.toConjClasses ≠ ConjClasses.mk 1)
    (hcomm :
      ¬ ∃ e : X ≃ Fin 2, ∃ k : ℤ, k ≠ 0 ∧
        w.toConjClasses =
          ConjClasses.mk ((FreeGroup.freeGroupCongr e.symm RankTwoFreeGroup.commutator) ^ k)) :
    (Subgroup.map (mk' (JA(FreeGroup X)))
      (stabilizer (MulAut (FreeGroup X)) w)).index = 0 :=
  sorry
