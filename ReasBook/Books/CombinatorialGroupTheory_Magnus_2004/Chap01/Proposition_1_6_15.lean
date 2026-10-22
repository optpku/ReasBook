/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_6_14

universe u

open scoped RelatorSetIr

section

-- Layer triage:
-- `source-facing`: the regular/singular relator-set reduction relation between relator sets with
-- possibly different ambient generator types, together with the counted reduction-to-triviality
-- language attached to a relator set `W`.
-- `core/canonical`: the relator-set owner notation `Ir(W)`, the automorphism owner
-- `MulAut (FreeGroup ι)`, set image `α '' W`, the specialization map
-- `specializeWordSetAtGenerator`, and `Relation.ReflTransGen` as the canonical owner of finite
-- transformation sequences.
-- `bridge/view`: a regular transformation of relators is the canonical image of `W` under an
-- automorphism of the ambient free group, while a singular transformation is the canonical
-- specialization obtained by killing one generator. The sigma package of "ambient generator type
-- together with relator set" and the adjoining singular-step count are internal bookkeeping used
-- only to realize the public counted sequence predicate.
-- Domain sampling:
-- 1. `Ir(W)` from Proposition `1-6-13` is the chapter owner abstraction for irreducibility rank.
-- 2. `ir_image_eq` from Proposition `1-6-13` is the canonical invariance statement for
--    regular transformations coming from automorphisms of the ambient free group.
-- 3. `specializeWordSetAtGenerator` from Proposition `1-6-14` is the canonical relator-set
--    construction for setting a generator equal to `1`.
-- 4. `GroupPresentation.TietzeExpansion` from Proposition `2-2-1` is the project pattern for
--    binder-indexed relations between relator sets with varying generator types, and
--    `Relation.ReflTransGen` is the canonical owner for finite step sequences.
-- Primitive vs. derived:
-- the primitive source-facing data are the one-step regular and singular relator-set reductions.
-- The counted sequence predicate, reduction-to-triviality predicate, and minimum singular-step
-- invariant are derived from that owner relation by adjoining an internal singular-step count and
-- applying `Relation.ReflTransGen` and `sInf`.

/-- One relator-set reduction either applies a regular automorphic image or applies the singular
specialization obtained by setting one generator equal to `1`. -/
inductive RelatorSetReduction :
    {ι : Type u} → Set (FreeGroup ι) → {ι' : Type u} → Set (FreeGroup ι') → Prop
  | regular {ι : Type u} (W : Set (FreeGroup ι)) (α : MulAut (FreeGroup ι)) :
      RelatorSetReduction W (α '' W)
  | singular {ι : Type u} (W : Set (FreeGroup ι)) (i : ι) :
      RelatorSetReduction W (specializeWordSetAtGenerator i W)

private abbrev RelatorSetState :=
  Σ ι : Type u, Set (FreeGroup ι)

private abbrev relatorSetState {ι : Type u} (W : Set (FreeGroup ι)) : RelatorSetState :=
  ⟨ι, W⟩

/-- Internal counted lift of `RelatorSetReduction`: regular steps keep the singular count,
while singular steps increment it by `1`. -/
private inductive RelatorSetReductionCountedStep :
    (RelatorSetState × ℕ) → (RelatorSetState × ℕ) → Prop
  | regular {ι : Type u} (W : Set (FreeGroup ι)) (α : MulAut (FreeGroup ι)) (s : ℕ) :
      RelatorSetReductionCountedStep (relatorSetState W, s)
        (relatorSetState (α '' W), s)
  | singular {ι : Type u} (W : Set (FreeGroup ι)) (i : ι) (s : ℕ) :
      RelatorSetReductionCountedStep (relatorSetState W, s)
        (relatorSetState (specializeWordSetAtGenerator i W), s + 1)

/-- `RelatorSetReductionSequenceWithSingularCount W s W'` means that `W'` is obtained from `W` by
a finite relator-set reduction sequence with exactly `s` singular transformations. -/
def RelatorSetReductionSequenceWithSingularCount
    {ι : Type u} (W : Set (FreeGroup ι)) (s : ℕ) {ι' : Type u}
    (W' : Set (FreeGroup ι')) : Prop :=
  Relation.ReflTransGen RelatorSetReductionCountedStep (relatorSetState W, 0)
    (relatorSetState W', s)

/-- `reducesRelatorSetToTrivialityWithSingularCount W s` means that `W` can be reduced to a trivial
relator set by a finite sequence attached to `W` using exactly `s` singular transformations, where
regular transformations are images under free-group automorphisms and singular transformations are
specializations obtained by setting one generator equal to `1`. -/
def reducesRelatorSetToTrivialityWithSingularCount
    {ι : Type u} (W : Set (FreeGroup ι)) (s : ℕ) : Prop :=
  ∃ (ι' : Type u) (W' : Set (FreeGroup ι')),
    RelatorSetReductionSequenceWithSingularCount W s W' ∧ W' ⊆ {1}

variable {n : ℕ}

/-- The minimum number of singular transformations in a sequence attached to `W` and reducing `W`
to triviality. -/
noncomputable def minSingularReductionCount (W : Set (FreeGroup (Fin n))) : ℕ :=
  sInf {s : ℕ | reducesRelatorSetToTrivialityWithSingularCount W s}

/-- Proposition 1-6-15: `Ir(W)` equals the rank of the ambient free group minus the minimum number
of singular transformations in a sequence attached to `W` and reducing `W` to triviality. -/
-- Proof sketch: regular transformations preserve `Ir(W)` by Proposition `1-6-13`, while each
-- singular transformation can decrease `Ir(W)` by at most one by Proposition `1-6-14`. Reducing to
-- a trivial relator set leaves a free group on the surviving generators, whose irreducibility rank
-- is exactly that remaining rank. Therefore the optimal number of singular steps is precisely the
-- defect `n - Ir(W)`.
theorem ir_eq_rank_sub_minSingularReductionCount
    (W : Set (FreeGroup (Fin n))) :
    Ir(W) = n - minSingularReductionCount W := sorry

end
