/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open MulEquiv

section

variable {F : Type u} {G : Type v} [Group F] [Group G]

-- Layer triage:
-- `source-facing`: a binary word `w : FreeGroup (Fin 2)` together with its value set in the free
-- group `F` under all substitutions of the two generators.
-- `core/canonical`: `FreeGroup (Fin 2)` is the owner object of binary words, `FreeGroup.lift` is
-- the owner abstraction turning a substitution `Fin 2 → F` into the corresponding evaluation
-- homomorphism, and `Set.range` is the canonical owner of the resulting value set in `F`.
-- `bridge/view`: the equivalent homomorphism-level formulation
-- `∃ φ : FreeGroup (Fin 2) →* F, φ w = g`, and transport of the value set across `MulEquiv`s.
-- Domain sampling:
-- 1. `FreeGroup (Fin 2)` is the canonical owner of words in two generators.
-- 2. `FreeGroup.lift` is the canonical evaluation map determined by a substitution
--    `Fin 2 → F`.
-- 3. `Set.range` is the chapter/mathlib owner construction for a value set; compare
--    `ParametricWord.valueSet` in Proposition `1-8-3`.
-- 4. `FreeGroup.mk` is the canonical bridge from signed words to elements of a concrete free
--    group, and `ComputablePred` is the chapter owner for algorithmic membership on such coded
--    inputs.
-- Primitive vs. derived:
-- the primitive source data are only the word `w`, the ambient group `F`, and a substitution
-- `x : Fin 2 → F`; the homomorphism `FreeGroup.lift x`, the existential homomorphism
-- formulation `∃ φ, φ w = g`, and any later computability interface on coded free-group words are
-- derived API from the owner set below.

/-- The value set of a binary word is the set of all values it attains under substitutions of the
two free generators into the ambient group. -/
def binaryWordValueSet (w : FreeGroup (Fin 2)) : Set F :=
  Set.range fun x : Fin 2 → F ↦ FreeGroup.lift x w

/-- Membership in the binary-word value set is exactly solvability of the corresponding word
equation by a substitution of the two generators. -/
@[simp] theorem mem_binaryWordValueSet_iff (w : FreeGroup (Fin 2)) (g : F) :
    g ∈ binaryWordValueSet w ↔ ∃ x : Fin 2 → F, FreeGroup.lift x w = g := by
  rfl

/-- The substitution-based value-set condition is equivalent to the homomorphism-level
formulation. -/
theorem mem_binaryWordValueSet_iff_exists_hom (w : FreeGroup (Fin 2)) (g : F) :
    g ∈ binaryWordValueSet w ↔ ∃ φ : FreeGroup (Fin 2) →* F, φ w = g := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨FreeGroup.lift x, rfl⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨φ ∘ FreeGroup.of, ?_⟩
    have hlift : FreeGroup.lift (φ ∘ FreeGroup.of) w = φ w := by
      exact DFunLike.congr_fun (FreeGroup.lift.apply_symm_apply φ) w
    exact hlift.trans hφ

/-- Group isomorphisms transport the value set of a binary word. -/
theorem mem_binaryWordValueSet_iff_map (e : F ≃* G) (w : FreeGroup (Fin 2)) (g : F) :
    g ∈ binaryWordValueSet w ↔ e g ∈ binaryWordValueSet w := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨fun i ↦ e (x i), ?_⟩
    have hlift :
        FreeGroup.lift (fun i ↦ e (x i)) =
          monoidHomCongrRightEquiv e (FreeGroup.lift x) := by
      ext i
      simp [monoidHomCongrRightEquiv, MonoidHom.comp_apply]
    simpa [monoidHomCongrRightEquiv, MonoidHom.comp_apply] using
      congrArg (fun φ : FreeGroup (Fin 2) →* G ↦ φ w) hlift
  · rintro ⟨x, hx⟩
    refine ⟨fun i ↦ e.symm (x i), ?_⟩
    have hlift :
        FreeGroup.lift (fun i ↦ e.symm (x i)) =
          (monoidHomCongrRightEquiv e).symm (FreeGroup.lift x) := by
      ext i
      simp [monoidHomCongrRightEquiv, MonoidHom.comp_apply]
    calc
      FreeGroup.lift (fun i ↦ e.symm (x i)) w = e.symm (FreeGroup.lift x w) := by
        simpa [monoidHomCongrRightEquiv, MonoidHom.comp_apply] using
          congrArg (fun φ : FreeGroup (Fin 2) →* F ↦ φ w) hlift
      _ = g := by simpa using congrArg e.symm hx

section

variable {X : Type u} [Primcodable X]

/-- Proposition 1-8-5: for a fixed binary word `w`, there is an algorithm deciding whether a
signed word on `X` represents an element of the value set of `w` in the canonical free group
`FreeGroup X`. -/
-- Layer: `source-facing`.
-- `core/canonical`: `binaryWordValueSet`, `FreeGroup.mk`, and `ComputablePred`.
-- `bridge/view`: Section `8` reduces binary-word value-set membership to the one-variable
-- equation machinery summarized in Proposition `1-8-3`.
theorem computable_represents_element_of_binaryWordValueSet (w : FreeGroup (Fin 2)) :
    ComputablePred fun L : List (X × Bool) ↦
      FreeGroup.mk L ∈ binaryWordValueSet w := sorry

end

end
