/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_16
import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_17
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_19

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/-!
Primary domain: one-relator groups and torsion in one-relator quotients.

Layer triage:
- `source-facing`: a one-relator group on generators `X` with defining relator `r`, together
  with the two torsion alternatives from the textbook: the quotient is torsion free when `r` is
  not a proper power, and when `r = u ^ n` with `u` root-free, the image of `u` has exact order
  `n` and controls all finite-order elements up to conjugacy.
- `core/canonical`: `PresentedGroup ({r} : Set (FreeGroup X))` is the owner for the one-relator
  quotient, `PresentedGroup.mk` is the canonical image map, `IsMulTorsionFree`, `orderOf`,
  `IsOfFinOrder`, and `IsConj` are the owner predicates for torsion, exact order, finite order,
  and conjugacy, and `IsProperPower` is the project predicate for proper powers.
- `bridge/view`: the textbook generator list `⟨t, b, c, … ; r⟩` carries no extra owner-level data
  beyond the ambient free group on a type `X`, and the cyclically reduced hypothesis on `r` is
  redundant for the final torsion statements, so it is omitted from the public Lean API.

Domain sampling:
1. `PresentedGroup ({r} : Set (FreeGroup X))` is the established owner abstraction for a
   one-relator group in this project.
2. `isMulTorsionFree_presentedGroup_singleton_of_relator_not_properPower` already records the
   torsion-free clause at exactly that owner level.
3. `orderOf_root_image_eq_maximal_exponent` and
   `exists_isConj_zpow_root_image_of_isOfFinOrder` already give the exact-order and torsion
   conjugacy conclusions for a chosen maximal root of the relator.
4. The remaining bridge needed here is only the maximal-root consequence of the hypothesis that
   the chosen root `u` is itself not a proper power.

Primitive vs. derived:
the primitive public data are the relator `r` and, in the torsion case, a chosen root `u` with
`r = u ^ n` and `u` not a proper power. Torsion-freeness, exact order, and conjugacy of
finite-order elements are derived owner-level conclusions on the quotient.
-/

variable {X : Type u}

/- Theorem 4-5-2 (1): if the relator `r` of a one-relator group is not a proper power in the
ambient free group, then the quotient `PresentedGroup ({r} : Set (FreeGroup X))` is torsion free.
This is exactly Proposition `2-5-17`, so the file reuses that canonical theorem directly rather
than keeping a duplicate local wrapper. -/
#check isMulTorsionFree_presentedGroup_singleton_of_relator_not_properPower

section

variable (r u : FreeGroup X) (n : ℕ+)

local notation "rels" => (Set.singleton r : Set (FreeGroup X))
local notation "G" => PresentedGroup rels
local notation "q" => PresentedGroup.mk rels

/-- If `r = u ^ n` and `u` is root-free, then `n` is maximal among all positive root exponents
of `r`. This is the only local bridge needed to reuse Proposition `2-5-16`. -/
private theorem relator_root_exponent_le_of_not_properPower
    (hroot : r = u ^ (n : ℕ)) (hu : ¬ IsProperPower u) {t : FreeGroup X} {m : ℕ+}
    (ht : r = t ^ (m : ℕ)) :
    m ≤ n := by
  have hpow : u ^ (n : ℕ) = t ^ (m : ℕ) := by
    calc
      u ^ (n : ℕ) = r := hroot.symm
      _ = t ^ (m : ℕ) := ht
  have hu_ne_one : u ≠ 1 := by
    intro hu1
    apply hu
    refine ⟨1, 2, by decide, by simp [hu1]⟩
  have hcomm : Commute (u ^ ((n : ℕ) : ℤ)) (t ^ ((m : ℕ) : ℤ)) := by
    simp [zpow_natCast, hpow]
  rcases exists_common_zpowers_generator_of_commute_zpow u t ((n : ℕ) : ℤ) ((m : ℕ) : ℤ)
      (by exact_mod_cast n.ne_zero) (by exact_mod_cast m.ne_zero) hcomm with
    ⟨c, hu_mem, ht_mem⟩
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hu_mem
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp ht_mem
  have hc_ne_one : c ≠ 1 := by
    intro hc
    apply hu_ne_one
    rw [← ha, hc]
    simp
  have ha_abs_le_one : Int.natAbs a ≤ 1 := by
    by_contra hle
    have hgt : 1 < Int.natAbs a := lt_of_not_ge hle
    apply hu
    cases a with
    | ofNat k =>
        refine ⟨c, k, hgt, ?_⟩
        simpa [zpow_natCast] using ha
    | negSucc k =>
        refine ⟨c⁻¹, k.succ, hgt, ?_⟩
        simpa using ha
  have ha_ne_zero : a ≠ 0 := by
    intro ha0
    apply hu_ne_one
    rw [← ha, ha0]
    simp
  have ha_abs_pos : 0 < Int.natAbs a := Int.natAbs_pos.mpr ha_ne_zero
  have ha_abs_eq_one : Int.natAbs a = 1 := by omega
  have hc_not_fin : ¬ IsOfFinOrder c := not_isOfFinOrder_of_isMulTorsionFree hc_ne_one
  have hexp : a * ((n : ℕ) : ℤ) = b * ((m : ℕ) : ℤ) := by
    apply (injective_zpow_iff_not_isOfFinOrder.mpr hc_not_fin)
    calc
      c ^ (a * ((n : ℕ) : ℤ)) = (c ^ a) ^ (((n : ℕ) : ℤ)) := by rw [zpow_mul]
      _ = u ^ (((n : ℕ) : ℤ)) := by rw [ha]
      _ = t ^ (((m : ℕ) : ℤ)) := by rw [zpow_natCast, zpow_natCast, hpow]
      _ = (c ^ b) ^ (((m : ℕ) : ℤ)) := by rw [hb]
      _ = c ^ (b * ((m : ℕ) : ℤ)) := by rw [zpow_mul]
  have hnatAbs : Int.natAbs a * (n : ℕ) = Int.natAbs b * (m : ℕ) := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs hexp
  have hn_eq' : 1 * (n : ℕ) = Int.natAbs b * (m : ℕ) := by
    simpa [ha_abs_eq_one] using hnatAbs
  have hn_eq : (n : ℕ) = Int.natAbs b * (m : ℕ) := by
    simpa using hn_eq'
  have hb_abs_ne_zero : Int.natAbs b ≠ 0 := by
    intro hb0
    have hn_zero : (n : ℕ) = 0 := by
      simp [hn_eq, hb0]
    exact n.ne_zero hn_zero
  have hb_abs_pos : 1 ≤ Int.natAbs b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb_abs_ne_zero)
  calc
    (m : ℕ) ≤ Int.natAbs b * (m : ℕ) := by
      simpa using Nat.mul_le_mul_right (m : ℕ) hb_abs_pos
    _ = n := hn_eq.symm

/-- Theorem 4-5-2 (2): if `r = u ^ n` and `u` is not a proper power, then the image of `u` in the
one-relator quotient has exact order `n`. -/
-- Proof sketch: the private helper identifies `n` as the maximal positive root exponent of `r`.
-- Apply the existing maximal-root one-relator torsion theorem from Proposition `2-5-16`.
theorem orderOf_relator_root_image_eq_of_not_properPower
    (hroot : r = u ^ (n : ℕ)) (hu : ¬ IsProperPower u) :
    orderOf (q u) = n := by
  simpa using
    orderOf_root_image_eq_maximal_exponent r u n hroot
      (fun {_} {_} ht ↦ relator_root_exponent_le_of_not_properPower r u n hroot hu ht)

/-- Theorem 4-5-2 (3): if `r = u ^ n` and `u` is not a proper power, then every finite-order
element of the one-relator quotient is conjugate to an integral power of the image of `u`. -/
-- Proof sketch: reuse the same maximal-root bridge and then apply Proposition `2-5-16 (2)`.
theorem exists_isConj_zpow_relator_root_image_of_isOfFinOrder_of_not_properPower
    (hroot : r = u ^ (n : ℕ)) (hu : ¬ IsProperPower u)
    (g : G) (hg : IsOfFinOrder g) :
    ∃ k : ℤ, IsConj g ((q u) ^ k) := by
  simpa using
    exists_isConj_zpow_root_image_of_isOfFinOrder r u n hroot
      (fun {_} {_} ht ↦ relator_root_exponent_le_of_not_properPower r u n hroot hu ht) g hg

end

end
