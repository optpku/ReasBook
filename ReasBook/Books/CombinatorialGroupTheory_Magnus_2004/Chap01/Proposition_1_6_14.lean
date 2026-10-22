/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_6_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped RelatorSetIr

-- Layer triage:
-- `source-facing`: the specialized relator set obtained by setting one distinguished generator
-- equal to `1`, together with the induced monotonicity statement for the irreducibility rank
-- `Ir`.
-- `core/canonical`: the relator-set owner notation `Ir(W)`, the quotient owner
-- `PresentedGroup W`, `FreeGroup.lift`, `QuotientGroup.map`, and the surviving-generator subtype
-- `{j : ι // j ≠ i}`.
-- `bridge/view`: the set-level specialization is the image of the relators under the unique
-- free-group homomorphism that kills the generator `i` and sends every other generator to the
-- corresponding generator of the smaller free group.
-- Domain sampling:
-- 1. `Ir(W)` from Proposition `1-6-13` is the chapter owner abstraction for irreducibility rank.
-- 2. `PresentedGroup W` is the ambient owner object on which `Ir(W)` is built.
-- 3. `FreeGroup.lift` is the owner construction for a homomorphism defined by its values on
--    generators, so the primitive specialization data should be the homomorphism itself.
-- 4. `QuotientGroup.map` and `PresentedGroup.generated_by` give the quotient-level bridge from the
--    free-group specialization to the induced surjective map of presented groups.
-- Primitive vs. derived:
-- the primitive source data are only the distinguished generator `i`; the specialized relator set
-- and the induced map of presented groups are derived canonically from the specialization
-- homomorphism.

section

/-- Internal bridge: the free-group homomorphism that sets the generator `i` equal to `1` and
keeps every other generator. -/
private noncomputable def specializeAtGeneratorHom {ι : Type u} (i : ι) :
    FreeGroup ι →* FreeGroup {j : ι // j ≠ i} :=
  let _ : DecidableEq ι := Classical.decEq ι
  FreeGroup.lift fun j : ι ↦
    if h : j = i then 1 else FreeGroup.of ⟨j, h⟩

/-- The relator set obtained from `W` by setting the generator `i` equal to `1`. -/
def specializeWordSetAtGenerator {ι : Type u} (i : ι) (W : Set (FreeGroup ι)) :
    Set (FreeGroup {j : ι // j ≠ i}) :=
  specializeAtGeneratorHom i '' W

namespace PresentedGroup

/-- Internal bridge: the quotient map induced by setting the generator `i` equal to `1`. -/
private noncomputable def specializeAtGenerator {ι : Type u} (W : Set (FreeGroup ι)) (i : ι) :
    PresentedGroup W →* PresentedGroup (specializeWordSetAtGenerator i W) :=
  QuotientGroup.map (Subgroup.normalClosure W)
    (Subgroup.normalClosure (specializeWordSetAtGenerator i W))
    (specializeAtGeneratorHom i)
    (Subgroup.normalClosure_le_normal fun r hr ↦
      Subgroup.subset_normalClosure ⟨r, hr, rfl⟩)

@[simp] private theorem specializeAtGenerator_of_self {ι : Type u} (W : Set (FreeGroup ι)) (i : ι) :
    specializeAtGenerator W i (PresentedGroup.of i) = 1 := by
  change QuotientGroup.mk (specializeAtGeneratorHom i (FreeGroup.of i)) = 1
  simp [specializeAtGeneratorHom]
  rfl

@[simp] private theorem specializeAtGenerator_of_ne {ι : Type u} (W : Set (FreeGroup ι)) {i j : ι}
    (h : j ≠ i) :
    specializeAtGenerator W i (PresentedGroup.of j) = PresentedGroup.of ⟨j, h⟩ := by
  change QuotientGroup.mk (specializeAtGeneratorHom i (FreeGroup.of j)) =
    PresentedGroup.of ⟨j, h⟩
  simp [specializeAtGeneratorHom, h]
  rfl

/-- Internal bridge: setting one generator equal to `1` induces a surjection on the presented
groups. -/
private theorem specializeAtGenerator_surjective {ι : Type u} (W : Set (FreeGroup ι)) (i : ι) :
    Function.Surjective (specializeAtGenerator W i) := by
  classical
  rw [← MonoidHom.range_eq_top]
  ext x
  constructor
  · intro _
    simp
  · intro _
    exact PresentedGroup.generated_by _ _ (fun j ↦ by
      refine ⟨PresentedGroup.of j.1, ?_⟩
      simpa using specializeAtGenerator_of_ne W j.2) x

end PresentedGroup

private theorem groupIr_mono_of_surjective {G H : Type u} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Surjective φ) :
    groupIr H ≤ groupIr G := by
  unfold groupIr
  refine sSup_le ?_
  rintro _ ⟨m, ⟨ψ, hψ⟩, rfl⟩
  exact le_groupIr_of_surjective m (ψ.comp φ) (hψ.comp hφ)

variable {n : ℕ}

/-- Proposition 1-6-14: if `W` is a set of words in the free group on `Fin n`, and the specialized
set is obtained from `W` by setting the generator `i` equal to `1`, then `Ir(W) ≥ Ir(W°)`. -/
-- Proof sketch: the induced quotient map from the original presented group onto the specialized
-- one is surjective. Any free quotient of the specialized presentation therefore gives, by
-- composition, a free quotient of the original presentation of the same rank.
theorem ir_ge_specializeWordSetAtGenerator
    (W : Set (FreeGroup (Fin n))) (i : Fin n) :
    Ir(W) ≥ Ir(specializeWordSetAtGenerator i W) := by
  exact groupIr_mono_of_surjective (PresentedGroup.specializeAtGenerator W i)
    (PresentedGroup.specializeAtGenerator_surjective W i)

end
