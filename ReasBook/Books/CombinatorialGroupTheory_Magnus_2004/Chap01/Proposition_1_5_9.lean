/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_5_2

universe u v

open MulAction

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

private def cyclicWordFamilyFinset {m : ℕ} (U : Fin m → CyclicWord X) :
    Finset (CyclicWord X) := by
  classical
  exact (Finset.univ : Finset (Fin m)).image U

private theorem cyclicWordFamily_stabilizer_eq_fixingSubgroup
    (basis : FreeGroupBasis X F) {m : ℕ} (U : Fin m → CyclicWord X) :
    letI := basis.cyclicWordMulAction
    stabilizer (MulAut F) U =
      fixingSubgroup (MulAut F) (cyclicWordFamilyFinset U : Set (CyclicWord X)) := by
  classical
  letI := basis.cyclicWordMulAction
  ext α
  rw [MulAction.mem_stabilizer_iff, mem_fixingSubgroup_iff]
  constructor
  · intro hα w hw
    change w ∈ cyclicWordFamilyFinset U at hw
    rcases Finset.mem_image.mp hw with ⟨i, -, rfl⟩
    change (α • U) i = U i
    simpa using congrArg (fun V : Fin m → CyclicWord X ↦ V i) hα
  · intro hα
    ext i
    simpa using congrArg Subtype.val <| hα (U i) <| by
      change U i ∈ cyclicWordFamilyFinset U
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

-- Layer triage:
-- `source-facing`: a finite basis `basis : FreeGroupBasis X F`, a finite set
-- `S : Finset (CyclicWord X)`, and the subgroup of `Aut(F)` fixing each cyclic word in `S`.
-- `core/canonical`: `Group.IsFinitelyPresented` as mathlib's owner notion of admitting a finite
-- presentation, together with the basis-induced `Aut(F)`-action `basis.cyclicWordMulAction` and
-- the owner subgroup `MulAction.fixingSubgroup`.
-- `bridge/view`: a tuple `U : Fin m → CyclicWord X` presents the same finite collection as
-- `Finset.univ.image U`, and its Pi-action stabilizer is exactly the fixing subgroup of that
-- finite set.
-- Domain sampling:
-- 1. `FreeGroupBasis.cyclicWordMulAction` from Proposition `1-5-2` is the owner basis-induced
--    `Aut(F)`-action on cyclic words over `X`.
-- 2. `MulAction.stabilizer` and `mem_stabilizer_iff` are mathlib's owner API for point
--    stabilizers.
-- 3. `MulAction.fixingSubgroup` and `mem_fixingSubgroup_iff` are mathlib's owner API for
--    pointwise fixers of a set.
-- 4. `Group.IsFinitelyPresented` is the owner notion of finite presentability.
-- Primitive vs. derived:
-- the primitive source data are the basis and the finite set `S`; the fixing subgroup is derived
-- canonically from `basis.cyclicWordMulAction`, while the tuple presentation
-- `U : Fin m → CyclicWord X` is only a bridge.
-- Proof sketch: McCool's algorithm constructs a finite generating set and a finite relator set for
-- the subgroup of automorphisms fixing the finite collection pointwise; this is exactly the data
-- needed to prove the canonical owner property `Group.IsFinitelyPresented`.
variable [Finite X]

/-- Proposition 1-5-9: for a free group `F` with finite basis `X` and a finite set `S` of cyclic
words over `X`, the subgroup of automorphisms fixing every member of `S` admits a finite
presentation. -/
theorem cyclicWordFinsetFixingSubgroup_isFinitelyPresented
    (basis : FreeGroupBasis X F) (S : Finset (CyclicWord X)) :
    letI := basis.cyclicWordMulAction
    Group.IsFinitelyPresented (fixingSubgroup (MulAut F) (S : Set (CyclicWord X))) := sorry

/-- Bridge form of Proposition 1-5-9 for a tuple presentation of the same finite collection. -/
theorem cyclicWordFamilyStabilizer_isFinitelyPresented
    (basis : FreeGroupBasis X F) {m : ℕ} (U : Fin m → CyclicWord X) :
    letI := basis.cyclicWordMulAction
    Group.IsFinitelyPresented (stabilizer (MulAut F) U) := by
  letI := basis.cyclicWordMulAction
  rw [cyclicWordFamily_stabilizer_eq_fixingSubgroup basis U]
  exact
    cyclicWordFinsetFixingSubgroup_isFinitelyPresented basis
      (cyclicWordFamilyFinset U)

end
