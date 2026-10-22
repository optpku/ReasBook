/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open HNNExtension
open HNNExtension.NormalWord

section

variable {G : Type u} [Group G] (A B : Subgroup G)

/-!
Primary domain: HNN extensions and Britton-style reduced words.

Layer triage:
- `source-facing`: a sequence `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` with no pinch
  `t⁻¹, gᵢ, t` for `gᵢ ∈ A` and no pinch `t, gᵢ, t⁻¹` for `gᵢ ∈ B`.
- `core/canonical`: `HNNExtension.NormalWord.ReducedWord G A' B'` is mathlib's owner family for
  reduced HNN words, with the chain condition forbidding `t, gᵢ, t⁻¹` for `gᵢ ∈ A'` and
  `t⁻¹, gᵢ, t` for `gᵢ ∈ B'`.
- `bridge/view`: the source convention is the specialization with swapped subgroup roles,
  `HNNExtension.NormalWord.ReducedWord G B A`, encoded by `head := g₀` and
  `toList := [(ε₁, g₁), ..., (εₙ, gₙ)]`.

Domain sampling:
1. `HNNExtension.toSubgroup A' B' u` is the subgroup attached to the stable-letter sign `u`, with
   `toSubgroup A' B' 1 = A'` and `toSubgroup A' B' (-1) = B'`.
2. `HNNExtension.NormalWord.ReducedWord G A' B'` is the canonical reduced-word owner for an HNN
   extension.
3. `ReducedWord.chain` stores the no-pinch condition on consecutive syllables by forbidding
   `t^u, gᵢ, t^{-u}` whenever `gᵢ ∈ toSubgroup A' B' u`.
4. `HNNExtension.swapEquiv φ : HNNExtension G B A φ.symm ≃* HNNExtension G A B φ` is the
   canonical stable-letter inversion equivalence, sending `t` to `t⁻¹` and fixing the base group.
5. Specializing `(A', B') := (B, A)` makes the forbidden pinches exactly the source ones, and
   `ReducedWord.toHNNExtension` evaluates such a source word in the original HNN extension through
   `swapEquiv`.

Primitive vs. derived:
the primitive source data are the initial group element `g₀` and the list of syllables
`(εᵢ, gᵢ)`. The no-pinch condition is then the canonical chain field of
`HNNExtension.NormalWord.ReducedWord`. Because the source stable-letter convention attaches `B` to
`t` and `A` to `t⁻¹`, the source-facing recall is the canonical specialization
`HNNExtension.NormalWord.ReducedWord G B A`; evaluation in the original HNN extension is derived
through the stable-letter inversion bridge, with no parallel local wrapper or duplicate predicate.
-/

/- Definition 4-2-1: a reduced sequence in the source HNN-extension convention is mathlib's
canonical reduced-word object `HNNExtension.NormalWord.ReducedWord G B A`.

The textbook sequence `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` is represented by the initial base-group
term `head := g₀` together with the syllable list `toList := [(ε₁, g₁), ..., (εₙ, gₙ)]`. The
stored chain condition in this specialization is exactly the requirement that there be no
consecutive pinch `t⁻¹, gᵢ, t` with `gᵢ ∈ A` and no consecutive pinch `t, gᵢ, t⁻¹` with
`gᵢ ∈ B`, because `toSubgroup B A 1 = B` and `toSubgroup B A (-1) = A`. -/
#check (ReducedWord G B A)

namespace HNNExtension

section

variable {A B}
variable (φ : A ≃* B)

private noncomputable def swapHom : HNNExtension G B A φ.symm →* HNNExtension G A B φ :=
  HNNExtension.lift HNNExtension.of (HNNExtension.t⁻¹) HNNExtension.inv_t_mul_of

private theorem swapHom_symm_comp_swapHom :
    MonoidHom.comp (swapHom φ) (swapHom φ.symm) = MonoidHom.id (HNNExtension G A B φ) := by
  apply HNNExtension.hom_ext
  · ext g
    change
      HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
          (HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
            (HNNExtension.of g)) =
        HNNExtension.of g
    rw [HNNExtension.lift_of, HNNExtension.lift_of]
  · change swapHom φ (swapHom φ.symm HNNExtension.t) = HNNExtension.t
    rw [show swapHom φ.symm HNNExtension.t = HNNExtension.t⁻¹ by
      change
        HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
            HNNExtension.t =
          HNNExtension.t⁻¹
      rw [HNNExtension.lift_t]]
    change
      HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
          HNNExtension.t⁻¹ =
        HNNExtension.t
    rw [map_inv, HNNExtension.lift_t]
    simp

/-- The canonical stable-letter inversion equivalence between the two HNN-extension conventions.
It fixes the embedded base group and sends the stable letter to its inverse. -/
noncomputable def swapEquiv : HNNExtension G B A φ.symm ≃* HNNExtension G A B φ :=
  { toFun := swapHom φ
    invFun := swapHom φ.symm
    left_inv := fun x ↦
      congrArg (fun f : HNNExtension G B A φ.symm →* HNNExtension G B A φ.symm ↦ f x)
        (swapHom_symm_comp_swapHom φ.symm)
    right_inv := fun x ↦
      congrArg (fun f : HNNExtension G A B φ →* HNNExtension G A B φ ↦ f x)
        (swapHom_symm_comp_swapHom φ)
    map_mul' := fun x y ↦ map_mul (swapHom φ) x y }

@[simp] theorem swapEquiv_of (g : G) : swapEquiv φ (HNNExtension.of g) = HNNExtension.of g := by
  change
    HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
        (HNNExtension.of g) =
      HNNExtension.of g
  rw [HNNExtension.lift_of]

@[simp] theorem swapEquiv_t :
    swapEquiv φ (HNNExtension.t : HNNExtension G B A φ.symm) =
      (HNNExtension.t : HNNExtension G A B φ)⁻¹ := by
  change
    HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
        HNNExtension.t =
      HNNExtension.t⁻¹
  rw [HNNExtension.lift_t]

@[simp] theorem swapEquiv_symm_of (g : G) :
    (swapEquiv φ).symm (HNNExtension.of g) = HNNExtension.of g := by
  change
    HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
        (HNNExtension.of g) =
      HNNExtension.of g
  rw [HNNExtension.lift_of]

@[simp] theorem swapEquiv_symm_t :
    (swapEquiv φ).symm (HNNExtension.t : HNNExtension G A B φ) =
      (HNNExtension.t : HNNExtension G B A φ.symm)⁻¹ := by
  change
    HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
        HNNExtension.t =
      HNNExtension.t⁻¹
  rw [HNNExtension.lift_t]

end

end HNNExtension

namespace HNNExtension.NormalWord.ReducedWord

section

variable {A B}
variable (φ : A ≃* B)

/-- Evaluate a reduced word written in the source stable-letter convention in the original HNN
extension `HNNExtension G A B φ`. -/
noncomputable def toHNNExtension (w : ReducedWord G B A) : HNNExtension G A B φ :=
  HNNExtension.swapEquiv φ (w.prod φ.symm)

end

end HNNExtension.NormalWord.ReducedWord

end
