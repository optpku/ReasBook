/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_27

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open List

noncomputable section

section

variable {X : Type u}

local instance theorem_4_5_6_decidableEq : DecidableEq X := Classical.decEq X

local notation "basis" => FreeGroupBasis.ofFreeGroup X

private theorem not_basisLetterOccurs_mk_of_not_mem_map_fst
    {word : List (X × Bool)} {x : X} (hx : x ∉ word.map Prod.fst) :
    ¬ basisLetterOccurs basis x (FreeGroup.mk word) := by
  rw [basisLetterOccurs, reducedWordSupport, List.mem_toFinset]
  intro hx'
  have hxred : x ∈ (FreeGroup.reduce word).map Prod.fst := by
    simpa [FreeGroupBasis.ofFreeGroup, FreeGroup.toWord_mk] using hx'
  have hred : FreeGroup.Red word (FreeGroup.reduce word) := FreeGroup.reduce.red
  have hsub : (FreeGroup.reduce word).map Prod.fst <+ word.map Prod.fst := by
    simpa using (FreeGroup.Red.sublist hred).map Prod.fst
  exact hx <| hsub.subset hxred

-- Layer triage:
-- `source-facing`: a cyclically reduced relator word `relator`, a freely reduced word `w`, a
-- second word `v` omitting some generator occurring in `w`, and equality of the two words in the
-- one-relator torsion quotient with defining relator `(FreeGroup.mk relator) ^ n`.
-- `core/canonical`: Proposition `2-5-27` is the existing owner theorem for long overlaps in the
-- quotient `PresentedGroup ({s ^ n} : Set (FreeGroup X))`, using `List.IsInfix`,
-- `basisLetterOccurs basis`, `FreeGroup.IsCyclicallyReduced`, and `PresentedGroup.mk`.
-- `bridge/view`: this file keeps the stronger source-facing omission hypothesis on the displayed
-- list word `v` and specializes the owner theorem to the displayed reduced words.
--
-- Domain sampling:
-- 1. `exists_long_common_part_with_relator_of_eq_in_power_relator_quotient` from Proposition
--    `2-5-27` is the chapter's owner theorem for the long-overlap conclusion in a torsion
--    one-relator quotient.
-- 2. `basisLetterOccurs basis` from Proposition `1-7-4` is the existing occurrence predicate for
--    generators in the canonical reduced word of a free-group element.
-- 3. `List.IsInfix` from mathlib is the owner predicate for consecutive subwords of reduced
--    words.
-- 4. Mathlib's `FreeGroup.pow_mk`, `FreeGroup.toWord_mk`, and
--    `FreeGroup.IsCyclicallyReduced.flatten_replicate` are the canonical length API turning the
--    owner theorem's bound into the source-facing bound on `((FreeGroup.mk relator) ^ n).toWord`.
--
-- Primitive vs. derived:
-- the primitive public data are the displayed words `relator`, `w`, `v`, the exponent `n`, and
-- the quotient equality between `w` and `v`; the canonical occurrence and long-overlap predicates
-- are derived bridge API used only internally to express the proof through the upstream owner
-- theorem.

/-- Theorem 4-5-6: if `G = ⟨X ; r^n = 1⟩` with `r` cyclically reduced and `n > 1`, and a freely
reduced word `w` is equal in `G` to a word `v` omitting some generator that occurs in `w`, then
`w` contains a contiguous subword that is also a subword of the reduced word of `r^n` or `r⁻ⁿ`,
and whose length is greater than `(n - 1) / n` times the length of `r^n`. The fractional bound is
rendered as the equivalent natural-number inequality
`n * segment.length > (n - 1) * (((FreeGroup.mk relator : FreeGroup X) ^ n).toWord.length)`. -/
-- Proof sketch: this is the long-overlap theorem for one-relator torsion groups. One applies the
-- Magnus breakdown of the equality `w = v` in the quotient by `r^n`, reducing first to the case
-- where the omitted generator occurs in the defining relator. Induct on the length of the
-- cyclically reduced relator and use the HNN-extension/free-product normal-form analysis to force
-- a long overlap between `w` and one of the cyclic conjugates of `r^n` or `r⁻ⁿ`.
theorem exists_long_relatorPower_subword_of_eq_in_oneRelatorTorsion
    (relator w v : List (X × Bool)) (n : ℕ)
    (hr_cyclic : FreeGroup.IsCyclicallyReduced relator)
    (hw_reduced : FreeGroup.IsReduced w)
    (hn : 1 < n)
    (heq :
      PresentedGroup.mk (Set.singleton ((FreeGroup.mk relator : FreeGroup X) ^ n))
          (FreeGroup.mk w) =
        PresentedGroup.mk (Set.singleton ((FreeGroup.mk relator : FreeGroup X) ^ n))
          (FreeGroup.mk v))
    (homit : ∃ x : X, x ∈ w.map Prod.fst ∧ x ∉ v.map Prod.fst) :
    ∃ segment : List (X × Bool),
      segment <:+: w ∧
        (segment <:+: (FreeGroup.mk relator ^ n).toWord ∨
          segment <:+: ((FreeGroup.mk relator ^ n)⁻¹).toWord) ∧
        n * segment.length >
          (n - 1) * ((FreeGroup.mk relator ^ n).toWord.length) := by
  classical
  let s : FreeGroup X := FreeGroup.mk relator
  rcases homit with ⟨x, hxw, hxv⟩
  have hs_cyclic : FreeGroup.IsCyclicallyReduced s.toWord := by
    simpa [s, FreeGroup.toWord_mk, hr_cyclic.isReduced.reduce_eq] using hr_cyclic
  have hoccurs_w : basisLetterOccurs basis x (FreeGroup.mk w) := by
    have hoccurs_w_iff : basisLetterOccurs basis x (FreeGroup.mk w) ↔ x ∈ w.map Prod.fst := by
      rw [basisLetterOccurs, reducedWordSupport, List.mem_toFinset]
      simp [FreeGroupBasis.ofFreeGroup, FreeGroup.toWord_mk, hw_reduced.reduce_eq]
    exact hoccurs_w_iff.2 hxw
  have hnot_occurs_v : ¬ basisLetterOccurs basis x (FreeGroup.mk v) := by
    exact not_basisLetterOccurs_mk_of_not_mem_map_fst hxv
  obtain ⟨segment, hwpart, hrelpart, hlen⟩ :=
    exists_long_common_part_with_relator_of_eq_in_power_relator_quotient
      s n (FreeGroup.mk w) (FreeGroup.mk v)
      hn hs_cyclic (by simpa [s] using heq) hoccurs_w hnot_occurs_v
  have hs_norm : s.norm = relator.length := by
    simp [s, FreeGroup.norm, FreeGroup.toWord_mk, hr_cyclic.isReduced.reduce_eq]
  have hpow_len : (s ^ n).toWord.length = n * s.norm := by
    simp [s, hs_norm, FreeGroup.pow_mk, FreeGroup.toWord_mk,
      (hr_cyclic.flatten_replicate n).isReduced.reduce_eq]
  refine ⟨segment, ?_, ?_, ?_⟩
  · simpa [FreeGroup.toWord_mk, hw_reduced.reduce_eq] using hwpart
  · simpa [s] using hrelpart
  · have hn_pos : 0 < n := lt_trans Nat.zero_lt_one hn
    have hlen' : n * segment.length > n * ((n - 1) * s.norm) :=
      Nat.mul_lt_mul_of_pos_left hlen hn_pos
    have hpow_len' : ((FreeGroup.mk relator : FreeGroup X) ^ n).toWord.length = n * s.norm := by
      simpa [s] using hpow_len
    rw [gt_iff_lt, hpow_len']
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlen'

end
