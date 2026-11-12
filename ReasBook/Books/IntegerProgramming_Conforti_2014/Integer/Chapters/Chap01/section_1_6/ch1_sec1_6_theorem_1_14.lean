/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Order.Minimal
public import Mathlib.Order.WellFoundedSet

open scoped BigOperators Matrix

public section

variable {m n : ℕ}

/-- A vector `x` is feasible for the boxed equality-form system determined by `A`, `b`, `l`, and
`u`. -/
def boxFeasible
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (l u x : Fin n → ℤ) : Prop :=
  A *ᵥ x = b ∧ l ≤ x ∧ x ≤ u

/-- The objective vector `c` strictly improves when moving from `y` to `x`. -/
def strictlyImproves
    (c x y : Fin n → ℤ) : Prop :=
  c ⬝ᵥ x < c ⬝ᵥ y

/-- An element of `Z` yields a positive feasible augmentation from `x₀` that strictly improves
the objective vector `c`. -/
def hasImprovingAugmentation
    (A : Matrix (Fin m) (Fin n) ℤ) (Z : Finset (Fin n → ℤ))
    (c : Fin n → ℤ) (b : Fin m → ℤ) (l u x₀ : Fin n → ℤ) : Prop :=
  ∃ z ∈ Z, ∃ step : ℕ,
    0 < step ∧
      boxFeasible A b l u (x₀ + step • z) ∧
        strictlyImproves c (x₀ + step • z) x₀

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: encode an integer by its
nonnegative and nonpositive parts. -/
def splitInt (z : ℤ) : ℕ × ℕ :=
  (Int.toNat (max z 0), Int.toNat (max (-z) 0))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: encode an integer vector by its
coordinatewise sign split. -/
def splitVector (z : Fin n → ℤ) : Fin n → ℕ × ℕ :=
  fun i ↦ splitInt (z i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: recover an integer from its
sign-split pair. -/
def decodeInt (p : ℕ × ℕ) : ℤ :=
  p.1 - p.2

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: decoding `splitInt` returns the
original integer. -/
lemma splitInt_decode (z : ℤ) : decodeInt (splitInt z) = z := by
  by_cases hz : 0 ≤ z
  · have hneg : -z ≤ 0 := by
      simpa using neg_nonpos.mpr hz
    -- In the nonnegative case only the positive part survives.
    simp [decodeInt, splitInt, hz, hneg]
  · have hz' : z ≤ 0 := le_of_not_ge hz
    -- In the nonpositive case only the negative part survives.
    simp [decodeInt, splitInt, hz']

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: the negative part of a
nonnegative integer vanishes in the sign-split encoding. -/
lemma splitInt_snd_eq_zero_of_nonneg {z : ℤ} (hz : 0 ≤ z) : (splitInt z).2 = 0 := by
  have hneg : -z ≤ 0 := by
    simpa using neg_nonpos.mpr hz
  simp [splitInt, hneg]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: the positive part of a
nonpositive integer vanishes in the sign-split encoding. -/
lemma splitInt_fst_eq_zero_of_nonpos {z : ℤ} (hz : z ≤ 0) : (splitInt z).1 = 0 := by
  simp [splitInt, hz]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: the sign-split encoding is
injective. -/
lemma splitVector_injective : Function.Injective (@splitVector n) := by
  intro x y hxy
  funext i
  have hcoord : splitInt (x i) = splitInt (y i) := congrFun hxy i
  calc
    x i = decodeInt (splitInt (x i)) := (splitInt_decode _).symm
    _ = decodeInt (splitInt (y i)) := congrArg decodeInt hcoord
    _ = y i := splitInt_decode _

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: a sign-split inequality forces
the smaller integer to lie between `0` and the larger one in the same orthant. -/
lemma int_bounds_of_splitInt_le {z d : ℤ} (h : splitInt z ≤ splitInt d) :
    (0 ≤ d → 0 ≤ z ∧ z ≤ d) ∧ (d ≤ 0 → d ≤ z ∧ z ≤ 0) := by
  constructor
  · intro hd
    have hdSnd : (splitInt d).2 = 0 := splitInt_snd_eq_zero_of_nonneg hd
    have hzSndLe : (splitInt z).2 ≤ 0 := by
      simpa [hdSnd] using h.2
    have hzSnd : (splitInt z).2 = 0 := Nat.le_zero.mp hzSndLe
    have hzEq : z = (splitInt z).1 := by
      simpa [decodeInt, hzSnd] using (splitInt_decode z).symm
    have hdEq : d = (splitInt d).1 := by
      simpa [decodeInt, hdSnd] using (splitInt_decode d).symm
    constructor
    · rw [hzEq]
      exact Int.natCast_nonneg _
    · rw [hzEq, hdEq]
      exact_mod_cast h.1
  · intro hd
    have hdFst : (splitInt d).1 = 0 := splitInt_fst_eq_zero_of_nonpos hd
    have hzFstLe : (splitInt z).1 ≤ 0 := by
      simpa [hdFst] using h.1
    have hzFst : (splitInt z).1 = 0 := Nat.le_zero.mp hzFstLe
    have hzEq : z = -((splitInt z).2 : ℤ) := by
      simpa [decodeInt, hzFst] using (splitInt_decode z).symm
    have hdEq : d = -((splitInt d).2 : ℤ) := by
      simpa [decodeInt, hdFst] using (splitInt_decode d).symm
    constructor
    · rw [hdEq, hzEq]
      have hsndCast : ((splitInt z).2 : ℤ) ≤ (splitInt d).2 := by
        exact_mod_cast h.2
      exact Int.neg_le_neg hsndCast
    · rw [hzEq]
      exact neg_nonpos.mpr (Int.natCast_nonneg _)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: subtracting a conformal
subvector keeps the remainder inside the same sign-split box. -/
lemma splitInt_sub_le_of_le {z d : ℤ} (h : splitInt z ≤ splitInt d) :
    splitInt (d - z) ≤ splitInt d := by
  rcases int_bounds_of_splitInt_le h with ⟨hpos, hneg⟩
  by_cases hd : 0 ≤ d
  · rcases hpos hd with ⟨hzNonneg, hzLe⟩
    have hdz : 0 ≤ d - z := sub_nonneg.mpr hzLe
    constructor
    · -- The positive part shrinks because `0 ≤ z`.
      simpa [splitInt, hd, hdz] using sub_le_self d hzNonneg
    · -- Both negative parts are zero in the nonnegative orthant.
      simpa [splitInt, hd] using hzLe
  · have hdNeg : d ≤ 0 := le_of_not_ge hd
    rcases hneg hdNeg with ⟨hdLeZ, hzNonpos⟩
    have hdz : d - z ≤ 0 := sub_nonpos.mpr hdLeZ
    have hnegd : 0 ≤ -d := by
      simpa using neg_nonneg.mpr hdNeg
    have hnegz : 0 ≤ -z := by
      simpa using neg_nonneg.mpr hzNonpos
    have hnegLe : -z ≤ -d := by
      exact Int.neg_le_neg hdLeZ
    have hnegSub : 0 ≤ (-d) - (-z) := sub_nonneg.mpr hnegLe
    have hrewrite : -(d - z) = (-d) - (-z) := by
      simp [sub_eq_add_neg, add_comm]
    constructor
    · -- Both positive parts are zero in the nonpositive orthant.
      simp [splitInt, hdNeg, hdz]
    · -- The negative part shrinks because `0 ≤ -z`.
      simpa [splitInt, hdNeg, hdz, hrewrite, hnegd, hnegSub] using
        sub_le_self (-d) hnegz

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: coordinatewise sign-split
domination yields coordinatewise interval bounds. -/
lemma coord_bounds_of_splitVector_le {z d : Fin n → ℤ} (h : splitVector z ≤ splitVector d)
    (i : Fin n) :
    (0 ≤ d i → 0 ≤ z i ∧ z i ≤ d i) ∧ (d i ≤ 0 → d i ≤ z i ∧ z i ≤ 0) :=
  int_bounds_of_splitInt_le (h i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: subtracting a conformal vector
from a vector leaves a remainder still dominated by the original one. -/
lemma splitVector_sub_le_of_le {z d : Fin n → ℤ} (h : splitVector z ≤ splitVector d) :
    splitVector (d - z) ≤ splitVector d := by
  intro i
  exact splitInt_sub_le_of_le (h i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: subtracting a nonzero conformal
vector strictly decreases the sign-split encoding. -/
lemma splitVector_sub_lt_of_nonzero {z d : Fin n → ℤ}
    (h : splitVector z ≤ splitVector d) (hz : z ≠ 0) :
    splitVector (d - z) < splitVector d := by
  refine lt_of_le_of_ne (splitVector_sub_le_of_le h) ?_
  intro hEq
  apply hz
  have hdiff : d - z = d := splitVector_injective hEq
  ext i
  exact sub_eq_self.mp (congrFun hdiff i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean: a conformal kernel substep of a
feasible improving difference stays inside the same box and preserves the equality constraints. -/
lemma boxFeasible_add_of_splitVector_le
    {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ} {l u x₀ d z : Fin n → ℤ}
    (hx₀ : boxFeasible A b l u x₀)
    (hxd : boxFeasible A b l u (x₀ + d))
    (hzle : splitVector z ≤ splitVector d)
    (hkernel : A *ᵥ z = 0) :
    boxFeasible A b l u (x₀ + z) := by
  rcases hx₀ with ⟨hx₀eq, hxl₀, hxu₀⟩
  rcases hxd with ⟨hxdeq, hxld, hxud⟩
  refine ⟨?_, ?_, ?_⟩
  · -- The selected step stays in the same equality fiber because it lies in the kernel of `A`.
    simp [Matrix.mulVec_add, hx₀eq, hkernel]
  · intro i
    rcases coord_bounds_of_splitVector_le hzle i with ⟨hpos, hneg⟩
    by_cases hd : 0 ≤ d i
    · rcases hpos hd with ⟨hzNonneg, hzLe⟩
      have hx₀Le : x₀ i ≤ x₀ i + z i := by
        simpa using add_le_add_right hzNonneg (x₀ i)
      exact le_trans (hxl₀ i) hx₀Le
    · have hdNeg : d i ≤ 0 := le_of_not_ge hd
      rcases hneg hdNeg with ⟨hdLeZ, _⟩
      have hxdLe : x₀ i + d i ≤ x₀ i + z i := add_le_add_right hdLeZ _
      exact le_trans (hxld i) hxdLe
  · intro i
    rcases coord_bounds_of_splitVector_le hzle i with ⟨hpos, hneg⟩
    by_cases hd : 0 ≤ d i
    · rcases hpos hd with ⟨_, hzLe⟩
      have hxLeD : x₀ i + z i ≤ x₀ i + d i := add_le_add_right hzLe _
      exact le_trans hxLeD (hxud i)
    · have hdNeg : d i ≤ 0 := le_of_not_ge hd
      rcases hneg hdNeg with ⟨_, hzNonpos⟩
      have hzLeX₀ : x₀ i + z i ≤ x₀ i := by
        simpa using add_le_add_right hzNonpos (x₀ i)
      exact le_trans hzLeX₀ (hxu₀ i)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_14.lean. See https://en.wikipedia.org/wiki/Graver_basis.

Theorem 1.14: for each integer matrix `A`, there exists a finite family of integer directions
depending only on `A` such that every feasible but nonoptimal point of the boxed equality-form
integer linear program admits a positive multiple of one of those directions that remains feasible
and strictly improves the objective value. -/
theorem existsFiniteAugmentingSet
    (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ Z : Finset (Fin n → ℤ),
      ∀ (c : Fin n → ℤ) (b : Fin m → ℤ) (l u x₀ : Fin n → ℤ),
        boxFeasible A b l u x₀ →
              (∃ x : Fin n → ℤ, boxFeasible A b l u x ∧ strictlyImproves c x x₀) →
                hasImprovingAugmentation A Z c b l u x₀ := by
  classical
  let Encoded : Set (Fin n → ℕ × ℕ) :=
    {e | ∃ z : Fin n → ℤ, z ≠ 0 ∧ A *ᵥ z = 0 ∧ splitVector z = e}
  have hpwo : Encoded.IsPWO := Set.isPWO_of_wellQuasiOrderedLE Encoded
  have hminimalFinite : {e | Minimal (· ∈ Encoded) e}.Finite :=
    (setOf_minimal_antichain (fun e ↦ e ∈ Encoded)).finite_of_partiallyWellOrderedOn
      (hpwo.mono (setOf_minimal_subset _))
  obtain ⟨t, a, _, haRange⟩ := hminimalFinite.fin_param
  have haEncoded : ∀ k, a k ∈ Encoded := by
    intro k
    have hkRange : a k ∈ Set.range a := ⟨k, rfl⟩
    have hkMinimal : Minimal (fun e ↦ e ∈ Encoded) (a k) := by
      rw [haRange] at hkRange
      exact hkRange
    exact hkMinimal.1
  choose v hvNonzero hvKernel hvEncode using haEncoded
  let Z : Finset (Fin n → ℤ) := Finset.univ.image v
  refine ⟨Z, ?_⟩
  intro c b l u x₀ hx₀ hbetter
  rcases hbetter with ⟨x, hx, hlt⟩
  let d : Fin n → ℤ := x - x₀
  have hxd : x₀ + d = x := by
    ext i
    simp [d]
  have hdKernel : A *ᵥ d = 0 := by
    rcases hx₀ with ⟨hx₀eq, _, _⟩
    rcases hx with ⟨hxeq, _, _⟩
    -- The feasible difference lies in the kernel of `A`.
    simp [d, Matrix.mulVec_sub, hxeq, hx₀eq]
  have hdObjective : c ⬝ᵥ d < 0 := by
    -- Strict improvement means the feasible difference has negative objective value.
    simpa [d, strictlyImproves, dotProduct_sub] using sub_lt_zero.mpr hlt
  have hdecompose :
      ∀ e : Fin n → ℕ × ℕ, ∀ d' : Fin n → ℤ,
        splitVector d' = e →
        A *ᵥ d' = 0 →
        ∃ L : List (Fin t),
          (∀ k ∈ L, splitVector (v k) ≤ e) ∧
          (L.map v).sum = d' := by
    intro e
    refine ((inferInstance : WellFoundedLT (Fin n → ℕ × ℕ)).wf).induction
      (C := fun e ↦ ∀ d' : Fin n → ℤ,
        splitVector d' = e →
        A *ᵥ d' = 0 →
        ∃ L : List (Fin t),
          (∀ k ∈ L, splitVector (v k) ≤ e) ∧
          (L.map v).sum = d') e ?_
    intro e ih d' hsplit hkernel
    by_cases hd'zero : d' = 0
    · refine ⟨[], ?_, ?_⟩
      · intro k hk
        cases hk
      · simp [hd'zero]
    · have hmem : e ∈ Encoded := ⟨d', hd'zero, hkernel, hsplit⟩
      obtain ⟨emin, hminLe, hmin⟩ := hpwo.exists_le_minimal hmem
      have hminRange : emin ∈ Set.range a := by
        rw [haRange]
        exact hmin
      rcases hminRange with ⟨k, rfl⟩
      let r : Fin n → ℤ := d' - v k
      have hkLeD : splitVector (v k) ≤ splitVector d' := by
        rw [hsplit]
        simpa [hvEncode] using hminLe
      have hrLeD : splitVector r ≤ splitVector d' := by
        simpa [r] using splitVector_sub_le_of_le hkLeD
      have hrKernel : A *ᵥ r = 0 := by
        -- Subtract the chosen kernel generator to stay in the kernel.
        simp [r, Matrix.mulVec_sub, hkernel, hvKernel k]
      have hrLt : splitVector r < e := by
        simpa [r, hsplit] using splitVector_sub_lt_of_nonzero hkLeD (hvNonzero k)
      rcases ih (splitVector r) hrLt r rfl hrKernel with ⟨L, hLle, hLsum⟩
      refine ⟨k :: L, ?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with hjHead | hjTail
        · simpa [hjHead, hvEncode] using hminLe
        · have hrLeE : splitVector r ≤ e := by
            simpa [hsplit] using hrLeD
          exact (hLle j hjTail).trans hrLeE
      · -- Reassemble the recursive remainder with the chosen minimal summand.
        simp [r, hLsum, sub_eq_add_neg, add_left_comm]
  have listSumObjective_nonneg :
      ∀ L : List (Fin t), (∀ k ∈ L, 0 ≤ c ⬝ᵥ v k) → 0 ≤ c ⬝ᵥ (L.map v).sum := by
    intro L
    induction L with
    | nil =>
        intro hL
        simp
    | cons k L ih =>
        intro hL
        have hk : 0 ≤ c ⬝ᵥ v k := hL k List.mem_cons_self
        have hTail : ∀ j ∈ L, 0 ≤ c ⬝ᵥ v j := by
          intro j hj
          exact hL j (List.mem_cons_of_mem _ hj)
        have hTailSum : 0 ≤ c ⬝ᵥ (L.map v).sum := ih hTail
        -- Dot products distribute over the list sum of augmentation directions.
        simpa [dotProduct_add, add_comm, add_left_comm, add_assoc] using add_nonneg hk hTailSum
  rcases hdecompose (splitVector d) d rfl hdKernel with ⟨L, hLle, hLsum⟩
  have hSumObjective : c ⬝ᵥ (L.map v).sum < 0 := by
    simpa [hLsum] using hdObjective
  have hNegative : ∃ k ∈ L, c ⬝ᵥ v k < 0 := by
    by_contra hnone
    have hNonneg : ∀ k ∈ L, 0 ≤ c ⬝ᵥ v k := by
      intro k hk
      exact le_of_not_gt (fun hlt' => hnone ⟨k, hk, hlt'⟩)
    exact (not_lt_of_ge (listSumObjective_nonneg L hNonneg)) hSumObjective
  rcases hNegative with ⟨k, hkL, hkNeg⟩
  have hkBox : boxFeasible A b l u (x₀ + v k) := by
    have hkLe : splitVector (v k) ≤ splitVector d := hLle k hkL
    have hxdBox : boxFeasible A b l u (x₀ + d) := by
      simpa [hxd] using hx
    exact boxFeasible_add_of_splitVector_le hx₀ hxdBox hkLe (hvKernel k)
  have hkImprove : strictlyImproves c (x₀ + v k) x₀ := by
    -- A negative summand strictly decreases the objective when added to `x₀`.
    rw [strictlyImproves]
    calc
      c ⬝ᵥ (x₀ + v k) = c ⬝ᵥ x₀ + c ⬝ᵥ v k := by
        simp [dotProduct_add]
      _ < c ⬝ᵥ x₀ := by
        simpa using Int.add_lt_add_left hkNeg (c ⬝ᵥ x₀)
  refine ⟨v k, ?_, 1, Nat.succ_pos 0, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · simpa using hkBox
  · simpa using hkImprove
