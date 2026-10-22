/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

/-- The canonical equivalence from the quotient `G ⧸ G_s` to a transitive `G`-set `S`. -/
noncomputable def quotientStabilizerEquivOfIsPretransitive [MulAction.IsPretransitive G S] (s : S) :
    G ⧸ MulAction.stabilizer G s ≃ S :=
  (MulAction.orbitEquivQuotientStabilizer G s).symm.trans
    ((Equiv.setCongr (MulAction.orbit_eq_univ G s)).trans (Equiv.Set.univ S))

@[simp] theorem quotientStabilizerEquivOfIsPretransitive_apply
    [MulAction.IsPretransitive G S] (s : S) (x : G ⧸ MulAction.stabilizer G s) :
    quotientStabilizerEquivOfIsPretransitive s x = MulAction.ofQuotientStabilizer G s x := by
  refine Quotient.inductionOn' x fun g ↦ ?_
  rfl

/-- Lemma 3.4.3: if the action of `G` on `S` is transitive, then the canonical equivariant map
`G ⧸ G_s → S`, sending `gG_s` to `g • s`, is bijective, so `S` is isomorphic to the `G`-set
`G ⧸ MulAction.stabilizer G s`. -/
theorem ofQuotientStabilizer_bijective_of_isPretransitive [MulAction.IsPretransitive G S] (s : S) :
    Function.Bijective (MulAction.ofQuotientStabilizer G s) := by
  simpa [quotientStabilizerEquivOfIsPretransitive_apply] using
    (quotientStabilizerEquivOfIsPretransitive s).bijective

/-- The quotient-stabilizer equivalence is `G`-equivariant. -/
theorem quotientStabilizerEquivOfIsPretransitive_equivariant
    [MulAction.IsPretransitive G S] (s : S) (g : G)
    (x : G ⧸ MulAction.stabilizer G s) :
    quotientStabilizerEquivOfIsPretransitive s (g • x) =
      g • quotientStabilizerEquivOfIsPretransitive s x := by
  simp [quotientStabilizerEquivOfIsPretransitive_apply, MulAction.ofQuotientStabilizer_smul]
