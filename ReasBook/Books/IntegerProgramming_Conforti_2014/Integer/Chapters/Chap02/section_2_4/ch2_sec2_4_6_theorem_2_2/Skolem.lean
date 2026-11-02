module

public import Mathlib.Tactic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.ZMod.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_6_definition_2_26.SteinerTripleSystem
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_6_theorem_2_2.Transport

public section

namespace SteinerTripleSystem

/-- Helper for Theorem 2.2: the Skolem construction uses the even cyclic coordinate
`ZMod (2 * (k + 1))`. -/
abbrev SkolemCoord (k : ℕ) := ZMod (2 * (k + 1))

/-- Helper for Theorem 2.2: the finite Skolem points carry a cyclic coordinate and one of the
three colors. -/
abbrev SkolemPoint (k : ℕ) := SkolemCoord k × Fin 3

/-- Helper for Theorem 2.2: the Skolem modulus is always positive, so the standard `ZMod` value
lemmas are available without local instance plumbing. -/
instance skolemModulusNeZero (k : ℕ) : NeZero (2 * (k + 1)) := by
  exact ⟨Nat.ne_of_gt (by positivity)⟩

/-- Helper for Theorem 2.2: the first half of `ZMod (2 * (k + 1))` is represented by the values
strictly below `k + 1`. -/
abbrev skolemInFirstHalf (k : ℕ) (x : SkolemCoord k) : Prop :=
  x.val < k + 1

/-- Helper for Theorem 2.2: the half-turn on the even cycle adds `k + 1`, swapping the two
halves of the Skolem coordinate set. -/
def skolemHalfTurn (k : ℕ) (x : SkolemCoord k) : SkolemCoord k :=
  x + (k + 1)

/-- Helper for Theorem 2.2: Skolem's relabeling sends first-half symbols to even residues and
second-half symbols to odd residues. -/
def skolemEncode (k : ℕ) (x : SkolemCoord k) : SkolemCoord k :=
  if skolemInFirstHalf k x then (2 * x.val : ℕ) else (2 * (x.val - (k + 1)) + 1 : ℕ)

/-- Helper for Theorem 2.2: Skolem decodes an even residue by halving it and an odd residue by
halving after removing the parity bit. -/
def skolemDecode (k : ℕ) (z : SkolemCoord k) : SkolemCoord k :=
  if z.val % 2 = 0 then (z.val / 2 : ℕ) else (z.val / 2 + (k + 1) : ℕ)

/-- Helper for Theorem 2.2: the Skolem quasigroup law is obtained by decoding the ordinary cyclic
sum on `ZMod (2 * (k + 1))`. -/
def skolemProd (k : ℕ) (x y : SkolemCoord k) : SkolemCoord k :=
  skolemDecode k (x + y)

/-- Helper for Theorem 2.2: the Skolem right-solver inverts the decoded sum in the second
argument. -/
def skolemRightSolve (k : ℕ) (x z : SkolemCoord k) : SkolemCoord k :=
  skolemEncode k z - x

/-- Helper for Theorem 2.2: first-half elements have the obvious half-turn value after adding
`k + 1`. -/
lemma skolemHalfTurn_val_of_firstHalf (k : ℕ) {x : SkolemCoord k}
    (hx : skolemInFirstHalf k x) :
    (skolemHalfTurn k x).val = x.val + (k + 1) := by
  -- The half-turn does not wrap for first-half points because their values are below `k + 1`.
  have hk : (((k + 1 : ℕ) : SkolemCoord k)).val = k + 1 := by
    have hklt : k + 1 < 2 * (k + 1) := by omega
    exact ZMod.val_natCast_of_lt hklt
  have hlt : x.val + (((k + 1 : ℕ) : SkolemCoord k)).val < 2 * (k + 1) := by
    rw [hk]
    simpa [two_mul] using Nat.add_lt_add_right hx (k + 1)
  have hraw :
      (x + ((k + 1 : ℕ) : SkolemCoord k)).val =
        x.val + (((k + 1 : ℕ) : SkolemCoord k)).val :=
    ZMod.val_add_of_lt hlt
  rw [hk] at hraw
  simpa [skolemHalfTurn] using hraw

/-- Helper for Theorem 2.2: second-half elements wrap back to the first half after the Skolem
half-turn. -/
lemma skolemHalfTurn_val_of_not_firstHalf (k : ℕ) {x : SkolemCoord k}
    (hx : ¬ skolemInFirstHalf k x) :
    (skolemHalfTurn k x).val = x.val - (k + 1) := by
  -- Wrapping occurs exactly once because the value is already at least `k + 1`.
  have hk : (((k + 1 : ℕ) : SkolemCoord k)).val = k + 1 := by
    have hklt : k + 1 < 2 * (k + 1) := by omega
    exact ZMod.val_natCast_of_lt hklt
  have hx_ge : k + 1 ≤ x.val := Nat.not_lt.mp hx
  have hwrap : 2 * (k + 1) ≤ x.val + (((k + 1 : ℕ) : SkolemCoord k)).val := by
    rw [hk]
    omega
  have hval : (skolemHalfTurn k x).val = x.val + (k + 1) - 2 * (k + 1) := by
    have hraw :
        (x + ((k + 1 : ℕ) : SkolemCoord k)).val =
          x.val + (((k + 1 : ℕ) : SkolemCoord k)).val - 2 * (k + 1) :=
      ZMod.val_add_of_le hwrap
    rw [hk] at hraw
    simpa [skolemHalfTurn] using hraw
  omega

/-- Helper for Theorem 2.2: the Skolem encoding has the expected even value on the first half. -/
lemma skolemEncode_val_of_firstHalf (k : ℕ) {x : SkolemCoord k}
    (hx : skolemInFirstHalf k x) :
    (skolemEncode k x).val = 2 * x.val := by
  -- The even code stays below the modulus because first-half values are below `k + 1`.
  have hlt : 2 * x.val < 2 * (k + 1) := by
    exact Nat.mul_lt_mul_of_pos_left hx (by decide)
  simpa [skolemEncode, hx] using
    (ZMod.val_natCast_of_lt hlt : (((2 * x.val : ℕ) : SkolemCoord k)).val = 2 * x.val)

/-- Helper for Theorem 2.2: the Skolem encoding has the expected odd value on the second half. -/
lemma skolemEncode_val_of_not_firstHalf (k : ℕ) {x : SkolemCoord k}
    (hx : ¬ skolemInFirstHalf k x) :
    (skolemEncode k x).val = 2 * (x.val - (k + 1)) + 1 := by
  -- Subtracting `k + 1` moves a second-half value back into the first-half range.
  have hx_ge : k + 1 ≤ x.val := Nat.not_lt.mp hx
  have hlt : 2 * (x.val - (k + 1)) + 1 < 2 * (k + 1) := by
    have hxl : x.val < 2 * (k + 1) := ZMod.val_lt x
    omega
  simpa [skolemEncode, hx] using
    (ZMod.val_natCast_of_lt hlt :
      (((2 * (x.val - (k + 1)) + 1 : ℕ) : SkolemCoord k)).val = 2 * (x.val - (k + 1)) + 1)

/-- Helper for Theorem 2.2: decoding an even Skolem code halves its value. -/
lemma skolemDecode_val_of_even (k : ℕ) {z : SkolemCoord k} (hz : z.val % 2 = 0) :
    (skolemDecode k z).val = z.val / 2 := by
  -- The halved even code stays below the modulus because `z.val < 2 * (k + 1)`.
  rw [skolemDecode, if_pos hz]
  have hlt : z.val / 2 < 2 * (k + 1) := by
    have hzlt : z.val < 2 * (k + 1) := ZMod.val_lt z
    omega
  exact ZMod.val_natCast_of_lt hlt

/-- Helper for Theorem 2.2: decoding an odd Skolem code halves after removing the parity bit and
adds back the second-half offset. -/
lemma skolemDecode_val_of_odd (k : ℕ) {z : SkolemCoord k} (hz : z.val % 2 = 1) :
    (skolemDecode k z).val = z.val / 2 + (k + 1) := by
  -- The decoded odd value lies in the second half but still below the modulus.
  rw [skolemDecode, if_neg (by omega)]
  have hzlt : z.val < 2 * (k + 1) := ZMod.val_lt z
  have hlt : z.val / 2 + (k + 1) < 2 * (k + 1) := by
    omega
  exact ZMod.val_natCast_of_lt hlt

/-- Helper for Theorem 2.2: decoding an encoded Skolem symbol recovers the original point. -/
lemma skolemDecode_encode (k : ℕ) (x : SkolemCoord k) :
    skolemDecode k (skolemEncode k x) = x := by
  by_cases hx : skolemInFirstHalf k x
  · -- First-half symbols encode to even residues, so decoding simply halves them again.
    apply ZMod.val_injective (2 * (k + 1))
    have hdec :
        (skolemDecode k (skolemEncode k x)).val = (skolemEncode k x).val / 2 :=
      skolemDecode_val_of_even k (by
        rw [skolemEncode_val_of_firstHalf k hx]
        omega)
    rw [hdec, skolemEncode_val_of_firstHalf k hx]
    omega
  · -- Second-half symbols encode to odd residues, so decoding removes the parity bit and
    -- restores the offset by `k + 1`.
    apply ZMod.val_injective (2 * (k + 1))
    have hdec :
        (skolemDecode k (skolemEncode k x)).val =
          (skolemEncode k x).val / 2 + (k + 1) :=
      skolemDecode_val_of_odd k (by
        rw [skolemEncode_val_of_not_firstHalf k hx]
        omega)
    rw [hdec, skolemEncode_val_of_not_firstHalf k hx]
    omega

/-- Helper for Theorem 2.2: encoding the decoded sum recovers the original cyclic residue. -/
lemma skolemEncode_decode (k : ℕ) (z : SkolemCoord k) :
    skolemEncode k (skolemDecode k z) = z := by
  by_cases hz : z.val % 2 = 0
  · -- Even residues decode into the first half, and re-encoding doubles them back.
    apply ZMod.val_injective (2 * (k + 1))
    have hz_half : z.val / 2 < k + 1 := by
      have hzlt : z.val < 2 * (k + 1) := ZMod.val_lt z
      omega
    have hfirst : skolemInFirstHalf k (skolemDecode k z) := by
      rw [skolemInFirstHalf, skolemDecode_val_of_even k hz]
      exact hz_half
    rw [skolemEncode_val_of_firstHalf]
    · rw [skolemDecode_val_of_even k hz]
      omega
    · exact hfirst
  · -- Odd residues decode into the second half, and re-encoding removes the added offset.
    apply ZMod.val_injective (2 * (k + 1))
    have hz_mod : z.val % 2 = 1 := by
      omega
    have hnot : ¬ skolemInFirstHalf k (skolemDecode k z) := by
      rw [skolemInFirstHalf, skolemDecode_val_of_odd k hz_mod]
      omega
    rw [skolemEncode_val_of_not_firstHalf k hnot]
    rw [skolemDecode_val_of_odd k hz_mod]
    omega

/-- Helper for Theorem 2.2: the Skolem quasigroup solver is correct in the second argument. -/
lemma skolemProd_rightSolve (k : ℕ) (x z : SkolemCoord k) :
    skolemProd k x (skolemRightSolve k x z) = z := by
  -- The defining equation reduces to the inverse relation between the encoding and the decoding.
  calc
    skolemProd k x (skolemRightSolve k x z)
        = skolemDecode k (x + (skolemEncode k z - x)) := by
          rfl
    _ = skolemDecode k (skolemEncode k z) := by
          congr 1
          abel
    _ = z := skolemDecode_encode k z

/-- Helper for Theorem 2.2: the Skolem right-solver is unique because encoding turns the
quasigroup equation back into an ordinary linear equation. -/
lemma skolemRightSolve_unique (k : ℕ) {x y z : SkolemCoord k}
    (hy : skolemProd k x y = z) :
    y = skolemRightSolve k x z := by
  -- Re-encoding the decoded sum identifies the original residue and then solves linearly.
  have hsum : x + y = skolemEncode k z := by
    calc
      x + y = skolemEncode k (skolemDecode k (x + y)) := by
            symm
            exact skolemEncode_decode k (x + y)
      _ = skolemEncode k z := by
            simpa [skolemProd] using congrArg (skolemEncode k) hy
  calc
    y = (x + y) - x := by abel
    _ = skolemEncode k z - x := by rw [hsum]
    _ = skolemRightSolve k x z := rfl

/-- Helper for Theorem 2.2: first-half points are fixed by the Skolem diagonal product. -/
lemma skolemProd_self_of_firstHalf (k : ℕ) {x : SkolemCoord k}
    (hx : skolemInFirstHalf k x) :
    skolemProd k x x = x := by
  -- Doubling a first-half value stays even and below the modulus, so the decoder just halves it.
  apply ZMod.val_injective (2 * (k + 1))
  have hlt : x.val + x.val < 2 * (k + 1) := by
    simpa [two_mul] using Nat.add_lt_add hx hx
  have hadd : (x + x).val = x.val + x.val := ZMod.val_add_of_lt hlt
  have hdec : (skolemProd k x x).val = (x + x).val / 2 := by
    simpa [skolemProd] using
      (skolemDecode_val_of_even k (by rw [hadd]; omega))
  rw [hdec, hadd]
  omega

/-- Helper for Theorem 2.2: second-half points are sent to their half-turn mate by the Skolem
diagonal product. -/
lemma skolemProd_self_of_not_firstHalf (k : ℕ) {x : SkolemCoord k}
    (hx : ¬ skolemInFirstHalf k x) :
    skolemProd k x x = skolemHalfTurn k x := by
  -- On the second half, the doubled value wraps once and decoding returns the first-half mate.
  apply ZMod.val_injective (2 * (k + 1))
  have hx_ge : k + 1 ≤ x.val := Nat.not_lt.mp hx
  have hwrap : 2 * (k + 1) ≤ x.val + x.val := by
    omega
  have hadd : (x + x).val = x.val + x.val - 2 * (k + 1) := ZMod.val_add_of_le hwrap
  have hdec : (skolemProd k x x).val = (x + x).val / 2 := by
    simpa [skolemProd] using
      (skolemDecode_val_of_even k (by rw [hadd]; omega))
  rw [hdec, hadd, skolemHalfTurn_val_of_not_firstHalf k hx]
  omega

/-- Helper for Theorem 2.2: the Skolem vertical triples live on the first half of the cycle and
use all three colors. -/
def skolemVerticalBlock (k : ℕ) (x : SkolemCoord k) : Finset (Option (SkolemPoint k)) :=
  { some (x, 0), some (x, 1), some (x, 2) }

/-- Helper for Theorem 2.2: the Skolem infinity triples join `none` to a second-half point and
its first-half mate in the next color. -/
def skolemInfinityBlock (k : ℕ) (x : SkolemCoord k) (i : Fin 3) :
    Finset (Option (SkolemPoint k)) :=
  { none, some (skolemHalfTurn k x, i), some (x, i + 1) }

/-- Helper for Theorem 2.2: the Skolem slanted triples use two same-color points and the decoded
cyclic sum in the next color. -/
def skolemSlantedBlock (k : ℕ) (x y : SkolemCoord k) (i : Fin 3) :
    Finset (Option (SkolemPoint k)) :=
  { some (x, i), some (y, i), some (skolemProd k x y, i + 1) }

/-- Helper for Theorem 2.2: the Skolem block family consists of the first-half vertical triples,
the first-half infinity triples, and the slanted triples on distinct same-color endpoints. -/
def skolemBlocks (k : ℕ) : Set (Finset (Option (SkolemPoint k))) :=
  {s | (∃ x, skolemInFirstHalf k x ∧ s = skolemVerticalBlock k x) ∨
      (∃ x i, skolemInFirstHalf k x ∧ s = skolemInfinityBlock k x i) ∨
      ∃ x y i, x ≠ y ∧ s = skolemSlantedBlock k x y i}

/-- Helper for Theorem 2.2: every Skolem block lies in the universal ground set. -/
lemma skolemBlocks_subset_ground (k : ℕ) :
    ∀ s ∈ skolemBlocks k, s ⊆ (Finset.univ : Finset (Option (SkolemPoint k))) := by
  -- Every Skolem block lives on the ambient finite type `Option (SkolemPoint k)`.
  intro s hs a ha
  simp

/-- Helper for Theorem 2.2: a Skolem vertical block has cardinality `3`. -/
lemma skolemVerticalBlock_card (k : ℕ) (x : SkolemCoord k) :
    (skolemVerticalBlock k x).card = 3 := by
  -- The three color coordinates are visibly distinct.
  simp [skolemVerticalBlock]

/-- Helper for Theorem 2.2: a Skolem infinity block has cardinality `3`. -/
lemma skolemInfinityBlock_card (k : ℕ) (x : SkolemCoord k) (i : Fin 3) :
    (skolemInfinityBlock k x i).card = 3 := by
  -- `none` is distinct from every `some`, and the two finite points have different colors.
  refine Finset.card_eq_three.mpr ?_
  refine ⟨none, some (skolemHalfTurn k x, i), some (x, i + 1), ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro h
    have hcolor : i ≠ i + 1 := by
      fin_cases i <;> decide
    exact hcolor (congrArg Prod.snd (Option.some.inj h))
  · simp [skolemInfinityBlock]

/-- Helper for Theorem 2.2: a Skolem slanted block has cardinality `3` when the same-color
endpoints are distinct. -/
lemma skolemSlantedBlock_card (k : ℕ) {x y : SkolemCoord k} (hxy : x ≠ y) (i : Fin 3) :
    (skolemSlantedBlock k x y i).card = 3 := by
  -- The two same-color endpoints differ in the cyclic coordinate, while the third point differs
  -- by color.
  refine Finset.card_eq_three.mpr ?_
  refine ⟨some (x, i), some (y, i), some (skolemProd k x y, i + 1), ?_, ?_, ?_, ?_⟩
  · intro h
    exact hxy (congrArg Prod.fst (Option.some.inj h))
  · intro h
    have hcolor : i ≠ i + 1 := by
      fin_cases i <;> decide
    exact hcolor (congrArg Prod.snd (Option.some.inj h))
  · intro h
    have hcolor : i ≠ i + 1 := by
      fin_cases i <;> decide
    exact hcolor (congrArg Prod.snd (Option.some.inj h))
  · simp [skolemSlantedBlock]

/-- Helper for Theorem 2.2: every Skolem block has cardinality `3`. -/
lemma skolemBlocks_sized (k : ℕ) : (skolemBlocks k).Sized 3 := by
  -- Each Skolem block is one of the three concrete constructors, and each constructor already
  -- has a dedicated cardinality lemma.
  intro s hs
  rcases hs with (⟨x, hx, rfl⟩ | ⟨x, i, hx, rfl⟩ | ⟨x, y, i, hxy, rfl⟩)
  · exact skolemVerticalBlock_card k x
  · exact skolemInfinityBlock_card k x i
  · exact skolemSlantedBlock_card k hxy i

/-- Helper for Theorem 2.2: the next Skolem color is always different from the current one. -/
lemma skolemColor_ne_succ (i : Fin 3) : i ≠ i + 1 := by
  -- The three colors of `Fin 3` can be checked directly.
  fin_cases i <;> decide

/-- Helper for Theorem 2.2: the Skolem half-turn sends first-half coordinates to the second
half. -/
lemma skolemHalfTurn_not_firstHalf_of_firstHalf (k : ℕ) {x : SkolemCoord k}
    (hx : skolemInFirstHalf k x) :
    ¬ skolemInFirstHalf k (skolemHalfTurn k x) := by
  -- Adding `k + 1` to a first-half value moves it past the first-half cutoff.
  rw [skolemInFirstHalf, skolemHalfTurn_val_of_firstHalf k hx]
  omega

/-- Helper for Theorem 2.2: the Skolem half-turn sends second-half coordinates back into the
first half. -/
lemma skolemInFirstHalf_halfTurn_of_not_firstHalf (k : ℕ) {x : SkolemCoord k}
    (hx : ¬ skolemInFirstHalf k x) :
    skolemInFirstHalf k (skolemHalfTurn k x) := by
  -- Subtracting `k + 1` from a second-half value lands strictly below `k + 1`.
  rw [skolemInFirstHalf, skolemHalfTurn_val_of_not_firstHalf k hx]
  have hxlt : x.val < 2 * (k + 1) := ZMod.val_lt x
  omega

/-- Helper for Theorem 2.2: applying the Skolem half-turn twice returns to the original
coordinate. -/
lemma skolemHalfTurn_involutive (k : ℕ) (x : SkolemCoord k) :
    skolemHalfTurn k (skolemHalfTurn k x) = x := by
  -- The half-turn swaps the two halves of the cycle, so a second half-turn undoes the first.
  apply ZMod.val_injective (2 * (k + 1))
  by_cases hx : skolemInFirstHalf k x
  · rw [skolemHalfTurn_val_of_not_firstHalf k
        (skolemHalfTurn_not_firstHalf_of_firstHalf k hx)]
    rw [skolemHalfTurn_val_of_firstHalf k hx]
    omega
  · rw [skolemHalfTurn_val_of_firstHalf k
        (skolemInFirstHalf_halfTurn_of_not_firstHalf k hx)]
    rw [skolemHalfTurn_val_of_not_firstHalf k hx]
    omega

/-- Helper for Theorem 2.2: the decoded Skolem product is symmetric because it comes from cyclic
addition. -/
lemma skolemProd_comm (k : ℕ) (x y : SkolemCoord k) :
    skolemProd k x y = skolemProd k y x := by
  -- The defining cyclic sum is commutative before decoding.
  simp [skolemProd, add_comm]

/-- Helper for Theorem 2.2: swapping the same-color endpoints does not change a Skolem slanted
block. -/
lemma skolemSlantedBlock_swap (k : ℕ) (x y : SkolemCoord k) (i : Fin 3) :
    skolemSlantedBlock k x y i = skolemSlantedBlock k y x i := by
  -- A slanted block depends only on the unordered same-color endpoint pair.
  ext z
  simp [skolemSlantedBlock, skolemProd_comm, or_left_comm]

/-- Helper for Theorem 2.2: a literal pair consisting of `none` and one finite Skolem point is
covered by a unique infinity block. -/
lemma skolemCoverWithNone (k : ℕ) (u : SkolemPoint k) :
    ∃! s, s ∈ skolemBlocks k ∧ ({none, some u} : Finset (Option (SkolemPoint k))) ⊆ s := by
  rcases u with ⟨x, i⟩
  by_cases hx : skolemInFirstHalf k x
  · refine ⟨skolemInfinityBlock k x (i + 2), ?_, ?_⟩
    · constructor
      · -- The first-half point appears as the second finite vertex of the corresponding infinity
        -- block.
        exact Or.inr <| Or.inl ⟨x, i + 2, hx, rfl⟩
      · intro a ha
        have ha' : a = none ∨ a = some (x, i) := by
          simpa [Finset.mem_insert, Finset.mem_singleton, eq_comm, or_left_comm, or_assoc] using ha
        rcases ha' with rfl | rfl
        · simp [skolemInfinityBlock]
        · -- On `Fin 3`, adding two chooses the predecessor color.
          fin_cases i <;> simp [skolemInfinityBlock]
    · intro s hs
      rcases hs with ⟨hsB, hsub⟩
      have hnone : none ∈ s := hsub (by simp)
      have hu : some (x, i) ∈ s := hsub (by simp)
      rcases hsB with (⟨y, hy, rfl⟩ | ⟨y, j, hy, rfl⟩ | ⟨a, b, j, hab, rfl⟩)
      · -- Vertical blocks contain no `none`.
        simp [skolemVerticalBlock] at hnone
      · -- An infinity block is determined by the unique first-half point it contains.
        have huCases :
            (x = skolemHalfTurn k y ∧ i = j) ∨ (x = y ∧ i = j + 1) := by
          simpa [skolemInfinityBlock] using hu
        rcases huCases with ⟨hxy, hij⟩ | ⟨hxy, hij⟩
        · exfalso
          subst hxy
          exact skolemHalfTurn_not_firstHalf_of_firstHalf k hy hx
        · subst hxy
          fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · -- Slanted blocks also contain no `none`.
        simp [skolemSlantedBlock] at hnone
  · refine ⟨skolemInfinityBlock k (skolemHalfTurn k x) i, ?_, ?_⟩
    · constructor
      · -- A second-half point appears as the first finite vertex of the corresponding infinity
        -- block based at its half-turn mate.
        have hhalf : skolemInFirstHalf k (skolemHalfTurn k x) :=
          skolemInFirstHalf_halfTurn_of_not_firstHalf k hx
        exact Or.inr <| Or.inl ⟨skolemHalfTurn k x, i, hhalf, rfl⟩
      · intro a ha
        have ha' : a = none ∨ a = some (x, i) := by
          simpa [Finset.mem_insert, Finset.mem_singleton, eq_comm, or_left_comm, or_assoc] using ha
        rcases ha' with rfl | rfl
        · simp [skolemInfinityBlock]
        · simp [skolemInfinityBlock, skolemHalfTurn_involutive]
    · intro s hs
      rcases hs with ⟨hsB, hsub⟩
      have hnone : none ∈ s := hsub (by simp)
      have hu : some (x, i) ∈ s := hsub (by simp)
      rcases hsB with (⟨y, hy, rfl⟩ | ⟨y, j, hy, rfl⟩ | ⟨a, b, j, hab, rfl⟩)
      · -- Vertical blocks contain no `none`.
        simp [skolemVerticalBlock] at hnone
      · -- The first-half witness is uniquely recovered from the second-half point.
        have huCases :
            (x = skolemHalfTurn k y ∧ i = j) ∨ (x = y ∧ i = j + 1) := by
          simpa [skolemInfinityBlock] using hu
        rcases huCases with ⟨hxy, hij⟩ | ⟨hxy, hij⟩
        · have hyx : skolemHalfTurn k x = y := by
            simpa [skolemHalfTurn_involutive] using congrArg (skolemHalfTurn k) hxy
          cases hij
          cases hyx
          rfl
        · exfalso
          subst hxy
          exact hx hy
      · -- Slanted blocks also contain no `none`.
        simp [skolemSlantedBlock] at hnone

/-- Helper for Theorem 2.2: two distinct same-color Skolem points are covered by a unique
slanted block. -/
lemma skolemCoverOfSameColorPoints (k : ℕ) {x y : SkolemCoord k} (hxy : x ≠ y) (i : Fin 3) :
    ∃! s, s ∈ skolemBlocks k ∧
      ({some (x, i), some (y, i)} : Finset (Option (SkolemPoint k))) ⊆ s := by
  refine ⟨skolemSlantedBlock k x y i, ?_, ?_⟩
  · constructor
    · -- The witness is exactly the slanted block on the two same-color endpoints.
      exact Or.inr <| Or.inr ⟨x, y, i, hxy, rfl⟩
    · intro a ha
      have ha' : a = some (x, i) ∨ a = some (y, i) := by
        simpa [hxy] using ha
      rcases ha' with rfl | rfl <;> simp [skolemSlantedBlock, hxy]
  · intro s hs
    rcases hs with ⟨hsB, hsub⟩
    have huPair : some (x, i) ∈ ({some (x, i), some (y, i)} : Finset (Option (SkolemPoint k))) := by
      simp [hxy]
    have hvPair : some (y, i) ∈ ({some (x, i), some (y, i)} : Finset (Option (SkolemPoint k))) := by
      simp
    rcases hsB with (⟨a, ha, rfl⟩ | ⟨a, j, ha, rfl⟩ | ⟨a, b, j, hab, rfl⟩)
    · -- A vertical block cannot contain two distinct points of the same color.
      have huVert : some (x, i) ∈ skolemVerticalBlock k a := hsub huPair
      have hvVert : some (y, i) ∈ skolemVerticalBlock k a := hsub hvPair
      fin_cases i <;> simp [skolemVerticalBlock] at huVert hvVert
      all_goals exact (hxy (huVert.trans hvVert.symm)).elim
    · -- An infinity block has only one finite point of each color.
      have huInf :
          some (x, i) ∈ skolemInfinityBlock k a j := hsub huPair
      have hvInf :
          some (y, i) ∈ skolemInfinityBlock k a j := hsub hvPair
      have huCases :
          (x = skolemHalfTurn k a ∧ i = j) ∨ (x = a ∧ i = j + 1) := by
        simpa [skolemInfinityBlock] using huInf
      have hvCases :
          (y = skolemHalfTurn k a ∧ i = j) ∨ (y = a ∧ i = j + 1) := by
        simpa [skolemInfinityBlock] using hvInf
      rcases huCases with ⟨hx, hix⟩ | ⟨hx, hix⟩ <;>
        rcases hvCases with ⟨hy, hiy⟩ | ⟨hy, hiy⟩
      · exact (hxy (hx.trans hy.symm)).elim
      · exact (skolemColor_ne_succ j (hix.symm.trans hiy)).elim
      · exact (skolemColor_ne_succ j (hiy.symm.trans hix)).elim
      · exact (hxy (hx.trans hy.symm)).elim
    · -- Any slanted candidate covering the pair must use the same color and the same unordered
      -- endpoint pair.
      have huSlant :
          some (x, i) ∈ skolemSlantedBlock k a b j := hsub huPair
      have hvSlant :
          some (y, i) ∈ skolemSlantedBlock k a b j := hsub hvPair
      by_cases hj : j = i
      · subst j
        have huEnds : x = a ∨ x = b := by
          simpa [skolemSlantedBlock, hab, skolemColor_ne_succ i] using huSlant
        have hvEnds : y = a ∨ y = b := by
          simpa [skolemSlantedBlock, hab, skolemColor_ne_succ i] using hvSlant
        rcases huEnds with rfl | rfl
        · rcases hvEnds with hya | hyb
          · exact (hxy hya.symm).elim
          · subst hyb
            rfl
        · rcases hvEnds with hya | hyb
          · subst hya
            rw [skolemSlantedBlock_swap]
          · exact (hxy hyb.symm).elim
      · have huCases :
          (x = a ∧ i = j) ∨ (x = b ∧ i = j) ∨
            (x = skolemProd k a b ∧ i = j + 1) := by
          simpa [skolemSlantedBlock] using huSlant
        have hvCases :
          (y = a ∧ i = j) ∨ (y = b ∧ i = j) ∨
            (y = skolemProd k a b ∧ i = j + 1) := by
          simpa [skolemSlantedBlock] using hvSlant
        have hi_ne : i ≠ j := fun hij ↦ hj hij.symm
        have hxProd : x = skolemProd k a b := by
          rcases huCases with ⟨hx, hij⟩ | ⟨hx, hij⟩ | ⟨hx, hij⟩
          · exact (hi_ne hij).elim
          · exact (hi_ne hij).elim
          · exact hx
        have hyProd : y = skolemProd k a b := by
          rcases hvCases with ⟨hy, hij⟩ | ⟨hy, hij⟩ | ⟨hy, hij⟩
          · exact (hi_ne hij).elim
          · exact (hi_ne hij).elim
          · exact hy
        exact (hxy (hxProd.trans hyProd.symm)).elim

/-- Helper for Theorem 2.2: away from the diagonal case, the recovered right endpoint of the
Skolem quasigroup witness is genuinely different from the left endpoint. -/
lemma skolemRightSolve_ne_self_of_ne_diag (k : ℕ) {x z : SkolemCoord k}
    (hdiag : z ≠ skolemProd k x x) :
    skolemRightSolve k x z ≠ x := by
  -- If the recovered endpoint collapsed to `x`, the solver equation would put `z` back on the
  -- diagonal product.
  intro hsolve
  apply hdiag
  calc
    z = skolemProd k x (skolemRightSolve k x z) := by
      symm
      exact skolemProd_rightSolve k x z
    _ = skolemProd k x x := by rw [hsolve]

/-- Helper for Theorem 2.2: a first-half diagonal mixed-color pair is covered uniquely by the
vertical Skolem block through that coordinate. -/
lemma skolemMixedColorDiagonalFirstHalfUnique (k : ℕ) (x : SkolemCoord k) (i : Fin 3)
    (hx : skolemInFirstHalf k x) :
    ∃! s, s ∈ skolemBlocks k ∧
      ({some (x, i), some (skolemProd k x x, i + 1)} : Finset (Option (SkolemPoint k))) ⊆ s := by
  refine ⟨skolemVerticalBlock k x, ?_, ?_⟩
  · constructor
    · -- The first-half diagonal pair lies on the vertical block through `x`.
      exact Or.inl ⟨x, hx, rfl⟩
    · intro a ha
      have ha' :
          a = some (x, i) ∨ a = some (x, i + 1) := by
        simpa [skolemProd_self_of_firstHalf k hx, Finset.mem_insert, Finset.mem_singleton,
          eq_comm, or_left_comm, or_assoc] using ha
      rcases ha' with rfl | rfl
      · fin_cases i <;> simp [skolemVerticalBlock]
      · fin_cases i <;> simp [skolemVerticalBlock]
  · intro s hs
    rcases hs with ⟨hsB, hsub⟩
    have huPair :
        some (x, i) ∈
          ({some (x, i), some (skolemProd k x x, i + 1)} :
            Finset (Option (SkolemPoint k))) := by
      simp [skolemColor_ne_succ i]
    have hvPair :
        some (x, i + 1) ∈
          ({some (x, i), some (skolemProd k x x, i + 1)} :
            Finset (Option (SkolemPoint k))) := by
      simp [skolemProd_self_of_firstHalf k hx]
    rcases hsB with (⟨a, ha, rfl⟩ | ⟨a, j, ha, rfl⟩ | ⟨a, b, j, hab, rfl⟩)
    · -- A vertical candidate is fixed by the color-`i` point that it contains.
      have huVert : some (x, i) ∈ skolemVerticalBlock k a := hsub huPair
      have hax : x = a := by
        fin_cases i <;> simpa [skolemVerticalBlock] using huVert
      subst a
      rfl
    · -- Route correction: an infinity block has one first-half and one second-half finite point,
      -- so it cannot contain both colored copies of the same first-half coordinate.
      have huInf : some (x, i) ∈ skolemInfinityBlock k a j := hsub huPair
      have hvInf : some (x, i + 1) ∈ skolemInfinityBlock k a j := hsub hvPair
      have huCases :
          (x = skolemHalfTurn k a ∧ i = j) ∨ (x = a ∧ i = j + 1) := by
        simpa [skolemInfinityBlock] using huInf
      have hvCases :
          (x = skolemHalfTurn k a ∧ i + 1 = j) ∨ (x = a ∧ i + 1 = j + 1) := by
        simpa [skolemInfinityBlock] using hvInf
      rcases huCases with ⟨hxa, hij⟩ | ⟨hxa, hij⟩ <;>
        rcases hvCases with ⟨hxb, hji⟩ | ⟨hxb, hji⟩
      · exfalso
        fin_cases i <;> fin_cases j <;> simp at hij hji
      · have hnot : ¬ skolemInFirstHalf k x := by
          simpa [hxa] using skolemHalfTurn_not_firstHalf_of_firstHalf k ha
        exact (hnot hx).elim
      · have hnot : ¬ skolemInFirstHalf k x := by
          simpa [hxb] using skolemHalfTurn_not_firstHalf_of_firstHalf k ha
        exact (hnot hx).elim
      · exfalso
        fin_cases i <;> fin_cases j <;> simp at hij hji
    · -- A slanted candidate would force its second same-color endpoint to collapse back to `x`.
      have huSlant : some (x, i) ∈ skolemSlantedBlock k a b j := hsub huPair
      have hvSlant : some (x, i + 1) ∈ skolemSlantedBlock k a b j := hsub hvPair
      have hj : j = i := by
        fin_cases i <;> fin_cases j <;>
          simp [skolemSlantedBlock] at huSlant hvSlant ⊢
      subst j
      have huEnds : x = a ∨ x = b := by
        simpa [skolemSlantedBlock, hab, skolemColor_ne_succ i] using huSlant
      have hprod : x = skolemProd k a b := by
        simpa [skolemSlantedBlock, hab, skolemColor_ne_succ i] using hvSlant
      have hselfSolve : x = skolemRightSolve k x x :=
        skolemRightSolve_unique k
          (by simpa using skolemProd_self_of_firstHalf k hx)
      rcases huEnds with hax | hbx
      · have hbSolve : b = skolemRightSolve k x x :=
          skolemRightSolve_unique k
            (by simpa [hax] using hprod.symm)
        have habsurd : a = b := by
          calc
            a = x := hax.symm
            _ = skolemRightSolve k x x := hselfSolve
            _ = b := hbSolve.symm
        exact (hab habsurd).elim
      · have haSolve : a = skolemRightSolve k x x :=
          skolemRightSolve_unique k <| by
            calc
              skolemProd k x a = skolemProd k b a := by rw [hbx]
              _ = skolemProd k a b := skolemProd_comm k b a
              _ = x := hprod.symm
        have habsurd : a = b := by
          calc
            a = skolemRightSolve k x x := haSolve
            _ = x := hselfSolve.symm
            _ = b := hbx
        exact (hab habsurd).elim

/-- Helper for Theorem 2.2: a second-half diagonal mixed-color pair is covered uniquely by the
Skolem infinity block based at its first-half half-turn mate. -/
lemma skolemMixedColorDiagonalSecondHalfUnique (k : ℕ) (x : SkolemCoord k) (i : Fin 3)
    (hx : ¬ skolemInFirstHalf k x) :
    ∃! s, s ∈ skolemBlocks k ∧
      ({some (x, i), some (skolemProd k x x, i + 1)} : Finset (Option (SkolemPoint k))) ⊆ s := by
  let a : SkolemCoord k := skolemHalfTurn k x
  have ha : skolemInFirstHalf k a := skolemInFirstHalf_halfTurn_of_not_firstHalf k hx
  have hprod : skolemProd k x x = a := by
    simpa [a] using skolemProd_self_of_not_firstHalf k hx
  refine ⟨skolemInfinityBlock k a i, ?_, ?_⟩
  · constructor
    · -- The second-half diagonal pair is exactly the finite part of the matching infinity block.
      exact Or.inr <| Or.inl ⟨a, i, ha, rfl⟩
    · intro u hu
      have hu' :
          u = some (x, i) ∨ u = some (a, i + 1) := by
        simpa [a, hprod, Finset.mem_insert, Finset.mem_singleton, eq_comm, or_left_comm,
          or_assoc] using hu
      rcases hu' with rfl | rfl
      · simp [skolemInfinityBlock, a, skolemHalfTurn_involutive]
      · simp [skolemInfinityBlock, a]
  · intro s hs
    rcases hs with ⟨hsB, hsub⟩
    have huPair :
        some (x, i) ∈
          ({some (x, i), some (skolemProd k x x, i + 1)} :
            Finset (Option (SkolemPoint k))) := by
      simp [skolemColor_ne_succ i]
    have hvPair :
        some (a, i + 1) ∈
          ({some (x, i), some (skolemProd k x x, i + 1)} :
            Finset (Option (SkolemPoint k))) := by
      simp [a, hprod]
    rcases hsB with (⟨b, hb, rfl⟩ | ⟨b, j, hb, rfl⟩ | ⟨u, v, j, huv, rfl⟩)
    · -- A vertical candidate would make the second-half coordinate `x` lie in the first half.
      have huVert : some (x, i) ∈ skolemVerticalBlock k b := hsub huPair
      have hxb : x = b := by
        fin_cases i <;> simpa [skolemVerticalBlock] using huVert
      exact (hx (by simpa [hxb] using hb)).elim
    · -- The unique second-half finite point already determines the infinity block completely.
      have huInf : some (x, i) ∈ skolemInfinityBlock k b j := hsub huPair
      have huCases :
          (x = skolemHalfTurn k b ∧ i = j) ∨ (x = b ∧ i = j + 1) := by
        simpa [skolemInfinityBlock] using huInf
      rcases huCases with ⟨hxb, hij⟩ | ⟨hxb, hij⟩
      · have hba : b = a := by
          calc
            b = skolemHalfTurn k x := by
              symm
              simpa [skolemHalfTurn_involutive] using congrArg (skolemHalfTurn k) hxb
            _ = a := rfl
        subst hba
        subst hij
        rfl
      · exact (hx (by simpa [hxb] using hb)).elim
    · -- A slanted candidate would again force its second same-color endpoint to equal `x`.
      have huSlant : some (x, i) ∈ skolemSlantedBlock k u v j := hsub huPair
      have hvSlant : some (a, i + 1) ∈ skolemSlantedBlock k u v j := hsub hvPair
      have hj : j = i := by
        fin_cases i <;> fin_cases j <;>
          simp [skolemSlantedBlock] at huSlant hvSlant ⊢
      subst j
      have huEnds : x = u ∨ x = v := by
        simpa [skolemSlantedBlock, huv, skolemColor_ne_succ i] using huSlant
      have hvProd : a = skolemProd k u v := by
        simpa [skolemSlantedBlock, huv, skolemColor_ne_succ i] using hvSlant
      have hselfSolve : x = skolemRightSolve k x a :=
        skolemRightSolve_unique k (by simpa [a] using hprod)
      rcases huEnds with hxu | hxv
      · have hvSolve : v = skolemRightSolve k x a :=
          skolemRightSolve_unique k
            (by simpa [hxu] using hvProd.symm)
        have huvsurd : u = v := by
          calc
            u = x := hxu.symm
            _ = skolemRightSolve k x a := hselfSolve
            _ = v := hvSolve.symm
        exact (huv huvsurd).elim
      · have huSolve : u = skolemRightSolve k x a :=
          skolemRightSolve_unique k <| by
            calc
              skolemProd k x u = skolemProd k v u := by rw [hxv]
              _ = skolemProd k u v := skolemProd_comm k v u
              _ = a := hvProd.symm
        have huvsurd : u = v := by
          calc
            u = skolemRightSolve k x a := huSolve
            _ = x := hselfSolve.symm
            _ = v := hxv
        exact (huv huvsurd).elim

/-- Helper for Theorem 2.2: a non-diagonal oriented mixed-color pair is covered uniquely by the
Skolem slanted block recovered from the right-solver. -/
lemma skolemMixedColorGenericSlantedUnique (k : ℕ) (x z : SkolemCoord k) (i : Fin 3)
    (hdiag : z ≠ skolemProd k x x) :
    ∃! s, s ∈ skolemBlocks k ∧
      ({some (x, i), some (z, i + 1)} : Finset (Option (SkolemPoint k))) ⊆ s := by
  let y : SkolemCoord k := skolemRightSolve k x z
  have hyx : y ≠ x := by
    simpa [y] using skolemRightSolve_ne_self_of_ne_diag k hdiag
  have hxy : x ≠ y := fun h ↦ hyx h.symm
  have hprod : skolemProd k x y = z := by
    simpa [y] using skolemProd_rightSolve k x z
  refine ⟨skolemSlantedBlock k x y i, ?_, ?_⟩
  · constructor
    · -- The generic witness uses the solver-recovered same-color endpoint.
      exact Or.inr <| Or.inr ⟨x, y, i, hxy, rfl⟩
    · intro u hu
      have hu' :
          u = some (x, i) ∨ u = some (z, i + 1) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, eq_comm, or_left_comm, or_assoc] using hu
      rcases hu' with rfl | rfl
      · simp [skolemSlantedBlock, y, hxy]
      · simp [skolemSlantedBlock, y, hprod]
  · intro s hs
    rcases hs with ⟨hsB, hsub⟩
    have huPair :
        some (x, i) ∈
          ({some (x, i), some (z, i + 1)} : Finset (Option (SkolemPoint k))) := by
      simp [skolemColor_ne_succ i]
    have hvPair :
        some (z, i + 1) ∈
          ({some (x, i), some (z, i + 1)} : Finset (Option (SkolemPoint k))) := by
      simp
    rcases hsB with (⟨a, ha, rfl⟩ | ⟨a, j, ha, rfl⟩ | ⟨a, b, j, hab, rfl⟩)
    · -- A vertical candidate would force `z = x`, which puts the pair back on the diagonal.
      have huVert : some (x, i) ∈ skolemVerticalBlock k a := hsub huPair
      have hvVert : some (z, i + 1) ∈ skolemVerticalBlock k a := hsub hvPair
      have hxa : x = a := by
        fin_cases i <;> simpa [skolemVerticalBlock] using huVert
      have hza : z = a := by
        fin_cases i <;> simpa [skolemVerticalBlock] using hvVert
      have hzdiag : z = skolemProd k x x := by
        calc
          z = a := hza
          _ = x := hxa.symm
          _ = skolemProd k x x := (skolemProd_self_of_firstHalf k (by simpa [hxa] using ha)).symm
      exact (hdiag hzdiag).elim
    · -- An infinity candidate would also reconstruct the forbidden diagonal endpoint.
      have huInf : some (x, i) ∈ skolemInfinityBlock k a j := hsub huPair
      have hvInf : some (z, i + 1) ∈ skolemInfinityBlock k a j := hsub hvPair
      have huCases :
          (x = skolemHalfTurn k a ∧ i = j) ∨ (x = a ∧ i = j + 1) := by
        simpa [skolemInfinityBlock] using huInf
      have hvCases :
          (z = skolemHalfTurn k a ∧ i + 1 = j) ∨ (z = a ∧ i + 1 = j + 1) := by
        simpa [skolemInfinityBlock] using hvInf
      rcases huCases with ⟨hxa, hij⟩ | ⟨hxa, hij⟩ <;>
        rcases hvCases with ⟨hza, hji⟩ | ⟨hza, hji⟩
      · exact (skolemColor_ne_succ i (hij.trans hji.symm)).elim
      · have hxnot : ¬ skolemInFirstHalf k x := by
          simpa [hxa] using skolemHalfTurn_not_firstHalf_of_firstHalf k ha
        have hzdiag : z = skolemProd k x x := by
          have hprod' : skolemProd k x x = a := by
            calc
              skolemProd k x x = skolemHalfTurn k x := skolemProd_self_of_not_firstHalf k hxnot
              _ = a := by rw [hxa, skolemHalfTurn_involutive]
          calc
            z = a := hza
            _ = skolemProd k x x := hprod'.symm
        exact (hdiag hzdiag).elim
      · exfalso
        fin_cases i <;> fin_cases j <;> simp at hij hji
      · exact (skolemColor_ne_succ i (hij.trans hji.symm)).elim
    · -- Once the slanted color is fixed, endpoint recovery identifies the recovered solver
      -- endpoint uniquely.
      have huSlant : some (x, i) ∈ skolemSlantedBlock k a b j := hsub huPair
      have hvSlant : some (z, i + 1) ∈ skolemSlantedBlock k a b j := hsub hvPair
      have hj : j = i := by
        fin_cases i <;> fin_cases j <;>
          simp [skolemSlantedBlock] at huSlant hvSlant ⊢
      subst j
      have huEnds : x = a ∨ x = b := by
        simpa [skolemSlantedBlock, hab, skolemColor_ne_succ i] using huSlant
      have hzProd : z = skolemProd k a b := by
        simpa [skolemSlantedBlock, hab, skolemColor_ne_succ i] using hvSlant
      rcases huEnds with hax | hbx
      · have hbSolve : b = y := by
          calc
            b = skolemRightSolve k x z :=
              skolemRightSolve_unique k
                (by simpa [hax] using hzProd.symm)
            _ = y := rfl
        subst hax
        subst hbSolve
        rfl
      · have haSolve : a = y := by
          calc
            a = skolemRightSolve k x z := by
              apply skolemRightSolve_unique k
              calc
                skolemProd k x a = skolemProd k b a := by rw [hbx]
                _ = skolemProd k a b := skolemProd_comm k b a
                _ = z := hzProd.symm
            _ = y := rfl
        subst hbx
        subst haSolve
        rw [skolemSlantedBlock_swap]

/-- Helper for Theorem 2.2: an oriented mixed-color pair of Skolem points is covered by a unique
Skolem block. -/
lemma skolemCoverOfMixedColorsOriented (k : ℕ) (x z : SkolemCoord k) (i : Fin 3) :
    ∃! s, s ∈ skolemBlocks k ∧
      ({some (x, i), some (z, i + 1)} : Finset (Option (SkolemPoint k))) ⊆ s := by
  -- Route correction: the mixed-color proof now dispatches to the geometric Skolem branches
  -- instead of keeping all constructor contradictions inside one monolithic theorem.
  by_cases hdiag : z = skolemProd k x x
  · by_cases hx : skolemInFirstHalf k x
    · simpa [hdiag] using skolemMixedColorDiagonalFirstHalfUnique k x i hx
    · simpa [hdiag] using skolemMixedColorDiagonalSecondHalfUnique k x i hx
  · exact skolemMixedColorGenericSlantedUnique k x z i hdiag

/-- Helper for Theorem 2.2: two distinct colors in `Fin 3` differ by one cyclic step in one of
the two orientations. -/
lemma skolemFin3_eq_add_one_or_eq_add_one (i j : Fin 3) (hij : i ≠ j) :
    j = i + 1 ∨ i = j + 1 := by
  -- On `Fin 3`, checking the three colors directly isolates the only two cyclic orientations.
  fin_cases i <;> fin_cases j <;> simp at hij ⊢

/-- Helper for Theorem 2.2: a literal pair of distinct Skolem points is covered by a unique
Skolem block. -/
lemma skolemCoverOfTwoPoints (k : ℕ) {u v : Option (SkolemPoint k)} (huv : u ≠ v) :
    ∃! s, s ∈ skolemBlocks k ∧ ({u, v} : Finset (Option (SkolemPoint k))) ⊆ s := by
  rcases u with (_ | ⟨x, i⟩)
  · rcases v with (_ | v)
    · exact (huv rfl).elim
    · simpa using skolemCoverWithNone k v
  · rcases v with (_ | ⟨z, j⟩)
    · have hpair :
        ({some (x, i), none} : Finset (Option (SkolemPoint k))) =
          ({none, some (x, i)} : Finset (Option (SkolemPoint k))) := by
        ext a
        constructor <;> intro ha <;>
          simpa [Finset.mem_insert, Finset.mem_singleton, eq_comm, or_comm] using ha
      simpa [hpair] using skolemCoverWithNone k (x, i)
    · by_cases hij : i = j
      · subst hij
        have hxz : x ≠ z := by
          intro hxz
          exact huv (by cases hxz; rfl)
        simpa using skolemCoverOfSameColorPoints k hxz i
      · by_cases hxz : x = z
        · subst hxz
          rcases skolemFin3_eq_add_one_or_eq_add_one i j hij with hji | hij'
          · simpa [hji] using skolemCoverOfMixedColorsOriented k x x i
          · have hpair :
              ({some (x, j + 1), some (x, j)} : Finset (Option (SkolemPoint k))) =
                ({some (x, j), some (x, j + 1)} : Finset (Option (SkolemPoint k))) := by
              ext a
              constructor <;> intro ha <;>
                simpa [Finset.mem_insert, Finset.mem_singleton, eq_comm, or_comm] using ha
            simpa [hij', hpair] using skolemCoverOfMixedColorsOriented k x x j
        · rcases skolemFin3_eq_add_one_or_eq_add_one i j hij with hji | hij'
          · simpa [hji] using skolemCoverOfMixedColorsOriented k x z i
          · have hpair :
              ({some (x, j + 1), some (z, j)} : Finset (Option (SkolemPoint k))) =
                ({some (z, j), some (x, j + 1)} : Finset (Option (SkolemPoint k))) := by
              ext a
              constructor <;> intro ha <;>
                simpa [Finset.mem_insert, Finset.mem_singleton, eq_comm, or_comm] using ha
            simpa [hij', hpair] using
              (skolemCoverOfMixedColorsOriented k z x j)

/-- Helper for Theorem 2.2: every `2`-subset of the Skolem ground type should lie in a unique
Skolem block. -/
lemma skolemPairCover (k : ℕ) :
    ∀ p, p ∈ (Finset.univ : Finset (Option (SkolemPoint k))).powersetCard 2 →
      ∃! s, s ∈ skolemBlocks k ∧ p ⊆ s := by
  intro p hp
  -- Route correction: the `powersetCard` bookkeeping is now isolated, so the combinatorial work
  -- runs entirely on a literal distinct pair.
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hp).2
  exact skolemCoverOfTwoPoints k huv

/-- Helper for Theorem 2.2: the Skolem family should supply the nontrivial `6k + 1` orders,
realized on `Option (ZMod (2 * (k + 1)) × Fin 3)`. -/
theorem skolemExistsOnSucc (k : ℕ) :
    ∃ S : Set (Finset (Option (ZMod (2 * (k + 1)) × Fin 3))), IsOn Finset.univ S := by
  -- Final assembly now depends only on the isolated block-family API and the literal pair-cover
  -- interface.
  refine ⟨skolemBlocks k, IsOn.ofSubsetGroundSizedAndPairCover ?_ ?_ ?_⟩
  · exact skolemBlocks_subset_ground k
  · exact skolemBlocks_sized k
  · exact skolemPairCover k

end SteinerTripleSystem
