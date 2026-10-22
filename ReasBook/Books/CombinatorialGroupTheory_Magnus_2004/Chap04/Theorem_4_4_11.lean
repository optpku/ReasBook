/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap02.Theorem_2_2_5

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

namespace BaumslagSolitar23

/-!
Primary domain: one-relator groups and Hopfianity for the Baumslag-Solitar group `BS(2,3)`.

Layer triage:
- `source-facing`: the standard endomorphism of `BS(2,3)` written in the textbook letters `b`
  and `t`, with `t` fixed and `b` sent to `b^2`.
- `core/canonical`: the existing project owner `BaumslagSolitar23.Group` from Theorem `2-2-5`,
  mathlib's `PresentedGroup.toGroup`, and the chapter owner predicate `IsHopfian`.
- `bridge/view`: the textbook letters are recovered from the upstream owner by `b := y` and
  `t := x`.

Domain sampling:
1. Theorem `2-2-5` already packages `BS(2,3)` in the owner namespace `BaumslagSolitar23`,
   together with the canonical generator images `x` and `y`.
2. `PresentedGroup.toGroup` and `PresentedGroup.toGroup.of` are the owner APIs for defining an
   endomorphism from generator images and then evaluating it on those generators.
3. `PresentedGroup.one_of_mem` is the canonical relator-triviality lemma, so a separate local
   theorem saying the defining relator becomes `1` would duplicate owner API.
4. `IsHopfian` from Proposition `1-3-5` is the canonical owner predicate for the conclusion that
   `BS(2,3)` is non-Hopfian.

Primitive vs. derived:
the public primitive data are the existing owner group together with its canonical generators `x`
and `y`. The textbook letters `b` and `t` are only a local notation bridge, and the generator
assignment used to build the endomorphism plus its relator check are derived implementation
details, so they remain private. The named endomorphism and its image/surjectivity/noninjectivity
lemmas are the public companion surface; there is no separate existential wrapper API.
-/

/- Source-facing notation: the textbook letters `b` and `t` are just the upstream owner
generators `y` and `x`. They are kept local so the public API stays on the canonical owner
declarations from Theorem `2-2-5`. -/
local notation "b" => y
local notation "t" => x

private def squareEndomorphismImages : BaumslagSolitar23Generator → Group
  | .x => x
  | .y => y ^ (2 : ℕ)

private theorem squareEndomorphism_respects_relator
    (r : FreeGroup BaumslagSolitar23Generator) (hr : r ∈ relators) :
    FreeGroup.lift squareEndomorphismImages r = (1 : Group) := by
  sorry

/-- The standard endomorphism of `BS(2,3)` fixing `t` and sending `b` to `b^2`. -/
noncomputable def squareEndomorphism : Group →* Group :=
  PresentedGroup.toGroup squareEndomorphism_respects_relator

/-- The standard endomorphism of `BS(2,3)` sends `b` to `b^2`. -/
@[simp] theorem squareEndomorphism_of_b :
    squareEndomorphism b = b ^ (2 : ℕ) := by
  simpa [squareEndomorphismImages] using
    (show squareEndomorphism (PresentedGroup.of BaumslagSolitar23Generator.y) =
        squareEndomorphismImages BaumslagSolitar23Generator.y from
      PresentedGroup.toGroup.of squareEndomorphism_respects_relator)

/-- The standard endomorphism of `BS(2,3)` fixes the generator `t`. -/
@[simp] theorem squareEndomorphism_of_t :
    squareEndomorphism t = t := by
  simpa [squareEndomorphismImages] using
    (show squareEndomorphism (PresentedGroup.of BaumslagSolitar23Generator.x) =
        squareEndomorphismImages BaumslagSolitar23Generator.x from
      PresentedGroup.toGroup.of squareEndomorphism_respects_relator)

/-- The standard endomorphism of `BS(2,3)` is surjective. -/
-- Proof sketch: the image contains `t` by `squareEndomorphism_of_t`, and it also contains `b`
-- because the defining relation rewrites `t⁻¹ b^2 t = b^3`, so from the image element `b^2` one
-- recovers `b`. Since `b` and `t` generate the group, the endomorphism is surjective.
theorem squareEndomorphism_surjective :
    Function.Surjective squareEndomorphism := by
  sorry

/-- The standard endomorphism of `BS(2,3)` is not injective. -/
-- Proof sketch: the commutator `[t⁻¹ b t, b]` is nontrivial by Britton's lemma in the HNN
-- extension model of `BS(2,3)`, but its image under `squareEndomorphism` is
-- `[t⁻¹ b^2 t, b^2] = [b^3, b^2] = 1`.
theorem squareEndomorphism_not_injective :
    ¬ Function.Injective squareEndomorphism := by
  sorry

/-- Theorem 4-4-11: the group `⟨ b, t ; t⁻¹ b^2 t = b^3 ⟩` is non-Hopfian. -/
theorem not_isHopfian : ¬ IsHopfian Group := by
  intro hHopfian
  exact squareEndomorphism_not_injective <|
    MonoidHom.injective_of_surjective squareEndomorphism squareEndomorphism_surjective

end BaumslagSolitar23
