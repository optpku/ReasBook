module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_theorem_1_6.EuclideanProduct

@[expose] public section

open scoped Matrix

namespace Int

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_theorem_1_6.lean`: the defining Euclidean
remainder is the floor remainder. -/
private lemma euclideanStepRemainder_eq_fmod_self (a b : ℤ) :
    Int.euclideanStepRemainder a b = Int.fmod a b := by
  -- The two definitions differ only in the order of the integer product.
  rw [Int.euclideanStepRemainder, Int.fmod_def]
  rw [mul_comm b (Int.fdiv a b)]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_theorem_1_6.lean`: right multiplication by
one step matrix performs the Euclidean update on a row. -/
private lemma vecMul_euclideanStepMatrix_eq (a b : ℤ) :
    (![a, b] : Fin 2 → ℤ) ᵥ* Int.euclideanStepMatrix a b =
      ![b, Int.euclideanStepRemainder a b] := by
  -- Evaluate both coordinates of the explicit `2 × 2` multiplication.
  ext i
  fin_cases i
  · simp [Matrix.vecMul, dotProduct, Int.euclideanStepMatrix, Int.euclideanStepRemainder,
      Fin.sum_univ_two]
  · simp [Matrix.vecMul, dotProduct, Int.euclideanStepMatrix, Int.euclideanStepRemainder,
      Fin.sum_univ_two]
    ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_theorem_1_6.lean`: removing the first
state of a nontrivial Euclidean-step sequence leaves a Euclidean-step sequence. -/
private lemma euclideanStepSequenceTail
    (a b : ℤ)
    (n : ℕ)
    (ab : Fin (n + 2) → ℤ × ℤ)
    (hseq : Int.IsEuclideanStepSequence a b (n + 1) ab) :
    Int.IsEuclideanStepSequence b (Int.euclideanStepRemainder a b) n
      (fun i ↦ ab i.succ) := by
  -- Split the sequence specification into the four clauses inherited by the tail.
  rcases hseq with ⟨hstart, hnonzero, hstep, hterminal⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The first tail state is the first Euclidean update of `(a, b)`.
    simpa only [Fin.castSucc_zero, hstart] using hstep (0 : Fin (n + 1))
  · -- Every preterminal tail state was already a preterminal state of the original run.
    intro i
    simpa only using hnonzero i.succ
  · -- The transition law is unchanged after shifting all indices by one.
    intro i
    simpa only using hstep i.succ
  · -- Shifting the last tail index gives the last original index.
    simpa only [Fin.succ_last] using hterminal

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_theorem_1_6.lean`: one Euclidean
remainder step preserves the integer gcd. -/
private lemma euclideanStepRemainder_gcd (a b : ℤ) :
    Int.gcd b (Int.euclideanStepRemainder a b) = Int.gcd a b := by
  -- Compare the two gcds through their universal divisibility characterization.
  let d : ℤ := Int.gcd b (Int.euclideanStepRemainder a b)
  have hdNonneg : 0 ≤ d := by
    dsimp only [d]
    exact Int.natCast_nonneg (Int.gcd b (Int.euclideanStepRemainder a b))
  have hdDvdB : d ∣ b := by
    exact Int.gcd_dvd_left b (Int.euclideanStepRemainder a b)
  have hdDvdRemainder : d ∣ Int.euclideanStepRemainder a b := by
    exact Int.gcd_dvd_right b (Int.euclideanStepRemainder a b)
  have hdDvdA : d ∣ a := by
    have hdDvdProduct : d ∣ Int.fdiv a b * b := dvd_mul_of_dvd_right hdDvdB
    have hdDvdSum : d ∣ Int.euclideanStepRemainder a b + Int.fdiv a b * b :=
      Int.dvd_add hdDvdRemainder hdDvdProduct
    simpa only [Int.euclideanStepRemainder, sub_add_cancel] using hdDvdSum
  have hgreatest : ∀ e : ℤ, e ∣ a → e ∣ b → e ∣ d := by
    intro e heA heB
    have heProduct : e ∣ Int.fdiv a b * b := dvd_mul_of_dvd_right heB
    have heRemainder : e ∣ Int.euclideanStepRemainder a b := by
      simpa only [Int.euclideanStepRemainder] using Int.dvd_sub heA heProduct
    exact Int.dvd_coe_gcd heB heRemainder
  have hdEq : d = Int.gcd a b :=
    Int.gcd_greatest hdNonneg hdDvdA hdDvdB hgreatest
  -- Both sides of `hdEq` are natural numbers coerced to integers.
  dsimp only [d] at hdEq
  exact_mod_cast hdEq

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_theorem_1_6.lean`: a nonzero divisor
has floor remainder of strictly smaller absolute value. -/
private lemma euclideanStepRemainder_natAbs_lt (a b : ℤ) (hb : b ≠ 0) :
    Int.natAbs (Int.euclideanStepRemainder a b) < Int.natAbs b := by
  -- Move to the canonical floor remainder and compare the corresponding integer absolute values.
  rw [euclideanStepRemainder_eq_fmod_self]
  apply Int.ofNat_lt.mp
  simp only [Int.natCast_natAbs]
  rcases lt_or_gt_of_ne hb with hbNeg | hbPos
  · by_cases hdiv : b ∣ a
    · -- A divisible input has zero remainder, so strictness follows from `b ≠ 0`.
      have hem : a % b = 0 := Int.emod_eq_zero_of_dvd hdiv
      rw [Int.fmod_eq_emod]
      simp only [not_le.mpr hbNeg, false_or, hdiv, if_pos, add_zero, hem, abs_zero,
        abs_of_neg hbNeg]
      omega
    · -- Otherwise the floor remainder is `a % b + b`, lying strictly between `b` and `0`.
      have hemNonneg : 0 ≤ a % b := Int.emod_nonneg a hb
      have hemNe : a % b ≠ 0 := by
        intro hem
        exact hdiv (Int.dvd_iff_emod_eq_zero.mpr hem)
      have hemPos : 0 < a % b := lt_of_le_of_ne hemNonneg (Ne.symm hemNe)
      have hemLt : a % b < -b := by
        have hemBound := Int.emod_lt a hb
        simpa only [Int.natCast_natAbs, abs_of_neg hbNeg] using hemBound
      have hsumNonpos : a % b + b ≤ 0 := by
        omega
      rw [Int.fmod_eq_emod]
      simp only [not_le.mpr hbNeg, false_or, hdiv, if_false, abs_of_nonpos hsumNonpos,
        abs_of_neg hbNeg]
      omega
  · -- For a positive divisor, floor remainder agrees with nonnegative Euclidean remainder.
    rw [Int.fmod_eq_emod_of_nonneg a (le_of_lt hbPos),
      abs_of_nonneg (Int.emod_nonneg a hb), abs_of_pos hbPos]
    simpa only [Int.natCast_natAbs, abs_of_pos hbPos] using Int.emod_lt a hb

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_theorem_1_6.lean`: the ordered matrix
product sends the initial row to the last state of a Euclidean-step sequence. -/
private lemma euclideanStepSequence_vecMul_eq_last
    (a b : ℤ)
    (n : ℕ)
    (ab : Fin (n + 1) → ℤ × ℤ)
    (hseq : Int.IsEuclideanStepSequence a b n ab) :
    (![a, b] : Fin 2 → ℤ) ᵥ* Int.euclideanStepProduct n ab =
      ![(ab (Fin.last n)).1, (ab (Fin.last n)).2] := by
  induction n generalizing a b with
  | zero =>
      -- The empty product is the identity and the unique state is the initial state.
      simp only [Int.euclideanStepProduct_def, List.ofFn_zero, List.prod_nil,
        Matrix.vecMul_one, Fin.last_zero, hseq.1]
  | succ n ih =>
      let tail : Fin (n + 1) → ℤ × ℤ := fun i ↦ ab i.succ
      have htail : Int.IsEuclideanStepSequence b (Int.euclideanStepRemainder a b) n tail :=
        euclideanStepSequenceTail a b n ab hseq
      have htailAction := ih b (Int.euclideanStepRemainder a b) tail htail
      -- Split off the first matrix, execute one step, and invoke the tail induction hypothesis.
      rw [Int.euclideanStepProduct_def, List.ofFn_succ, List.prod_cons,
        ← Matrix.vecMul_vecMul, Fin.castSucc_zero, hseq.1,
        vecMul_euclideanStepMatrix_eq a b]
      simpa only [Int.euclideanStepProduct_def, tail, Fin.succ_last] using htailAction

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_theorem_1_6.lean`: every integer pair
starts a finite Euclidean-step sequence. -/
private theorem existsEuclideanStepSequence (a b : ℤ) :
    ∃ n : ℕ, ∃ ab : Fin (n + 1) → ℤ × ℤ,
      Int.IsEuclideanStepSequence a b n ab := by
  by_cases hb : b = 0
  · -- If the second component is zero, the one-state sequence is already terminal.
    refine ⟨0, fun _ ↦ (a, b), ?_⟩
    simp only [Int.IsEuclideanStepSequence, hb, ne_eq, not_true_eq_false,
      IsEmpty.forall_iff, and_self]
  · -- Recurse on the strictly smaller remainder and prepend the current state.
    obtain ⟨n, tail, htail⟩ :=
      existsEuclideanStepSequence b (Int.euclideanStepRemainder a b)
    let ab : Fin (n + 2) → ℤ × ℤ := Fin.cons (a, b) tail
    rcases htail with ⟨htStart, htNonzero, htStep, htTerminal⟩
    refine ⟨n + 1, ab, ?_, ?_, ?_, ?_⟩
    · -- The prepended sequence starts at `(a, b)`.
      simp only [ab, Fin.cons_zero]
    · -- The new first preterminal state uses `hb`; later states inherit tail nonzeroness.
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [ab, Fin.castSucc_zero, Fin.cons_zero] using hb
      · simpa only [ab, Fin.castSucc_succ, Fin.cons_succ] using htNonzero j
    · -- The first transition is by construction, and all later transitions come from the tail.
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [ab, Fin.succ_zero_eq_one, Fin.cons_one, Fin.castSucc_zero, Fin.cons_zero]
          using htStart
      · simpa only [ab, Fin.cons_succ, Fin.castSucc_succ]
          using htStep j
    · -- Prepending does not change the terminal tail state.
      simpa only [ab, Fin.cons_last] using htTerminal
termination_by Int.natAbs b
decreasing_by
  exact euclideanStepRemainder_natAbs_lt a b hb

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_theorem_1_6.lean`: every ordered
Euclidean-step matrix product has unit determinant. -/
private lemma euclideanStepProduct_isUnit_det
    (n : ℕ)
    (ab : Fin (n + 1) → ℤ × ℤ) :
    IsUnit (Int.euclideanStepProduct n ab).det := by
  induction n with
  | zero =>
      -- The determinant of the empty product is one.
      simp only [Int.euclideanStepProduct_def, List.ofFn_zero, List.prod_nil, Matrix.det_one,
        isUnit_one]
  | succ n ih =>
      have hneg : IsUnit (-1 : ℤ) := by
        exact isUnit_neg_one
      have htail := ih (fun i ↦ ab i.succ)
      -- Split off the first matrix and multiply its unit determinant by the tail determinant.
      simpa only [Int.euclideanStepProduct_def, List.ofFn_succ, List.prod_cons, Matrix.det_mul,
        Int.euclideanStepMatrix_det_eq_neg_one] using hneg.mul htail

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_theorem_1_6.lean.
Theorem 1.6 (1). For integers `a` and `b` with `a` and `b` not both zero, there is a finite
Euclidean-step sequence whose ordered step-matrix product sends `![a, b]` to the terminal row of
that run. -/
theorem exists_euclideanStepSequence_vecMul_eq_terminal_zero
    (a b : ℤ)
    (hnot : a ≠ 0 ∨ b ≠ 0) :
    ∃ n : ℕ, ∃ ab : Fin (n + 1) → ℤ × ℤ,
      Int.IsEuclideanStepSequence a b n ab ∧
        (![a, b] : Fin 2 → ℤ) ᵥ* Int.euclideanStepProduct n ab =
          ![(ab (Fin.last n)).1, 0] := by
  -- Choose a terminating run, then rewrite its matrix action to its terminal state.
  obtain ⟨n, ab, hseq⟩ := existsEuclideanStepSequence a b
  refine ⟨n, ab, hseq, ?_⟩
  rw [euclideanStepSequence_vecMul_eq_last a b n ab hseq, hseq.2.2.2]

/-- The terminal first component of a Euclidean-step sequence has absolute value `Int.gcd a b`. -/
theorem euclideanStepSequence_terminal_natAbs_eq_gcd
    (a b : ℤ)
    (n : ℕ)
    (ab : Fin (n + 1) → ℤ × ℤ)
    (hseq : Int.IsEuclideanStepSequence a b n ab) :
    Int.natAbs ((ab (Fin.last n)).1) = Int.gcd a b := by
  induction n generalizing a b with
  | zero =>
      -- At length zero, terminality forces `b = 0`, so the claim is `natAbs a = gcd a 0`.
      have hb : b = 0 := by
        simpa only [Fin.last_zero, hseq.1] using hseq.2.2.2
      simp only [Fin.last_zero, hseq.1, hb, Int.gcd_zero_right]
  | succ n ih =>
      have htail := euclideanStepSequenceTail a b n ab hseq
      have hterminal := ih b (Int.euclideanStepRemainder a b) (fun i ↦ ab i.succ) htail
      -- The tail has the same terminal state, and one Euclidean step preserves gcd.
      simpa only [Fin.succ_last, euclideanStepRemainder_gcd] using hterminal

/-- Theorem 1.6 (2). Along a finite Euclidean-step sequence for nonzero input `(a, b)`, every
step matrix has determinant `-1`. -/
theorem euclideanStepSequence_stepMatrices_det_eq_neg_one
    (a b : ℤ)
    (n : ℕ)
    (ab : Fin (n + 1) → ℤ × ℤ)
    (hnot : a ≠ 0 ∨ b ≠ 0)
    (hseq : Int.IsEuclideanStepSequence a b n ab) :
    ∀ i : Fin n,
      (Int.euclideanStepMatrix (ab i.castSucc).1 (ab i.castSucc).2).det = -1 := by
  -- Apply the determinant computation independently at each preterminal state.
  intro i
  exact Int.euclideanStepMatrix_det_eq_neg_one (ab i.castSucc).1 (ab i.castSucc).2

/-- Theorem 1.6 (3). The ordered Euclidean-step product attached to a nontrivial input `(a, b)`
has unit determinant. -/
theorem euclideanStepSequence_isUnit_det
    (a b : ℤ)
    (n : ℕ)
    (ab : Fin (n + 1) → ℤ × ℤ)
    (hnot : a ≠ 0 ∨ b ≠ 0)
    (hseq : Int.IsEuclideanStepSequence a b n ab) :
    IsUnit (Int.euclideanStepProduct n ab).det := by
  -- The general product lemma already supplies the unit determinant.
  exact euclideanStepProduct_isUnit_det n ab

/-- A Euclidean-step product for nonzero input `(a, b)` admits an integral two-sided inverse. -/
theorem euclideanStepSequence_int_inverse
    (a b : ℤ)
    (n : ℕ)
    (ab : Fin (n + 1) → ℤ × ℤ)
    (hnot : a ≠ 0 ∨ b ≠ 0)
    (hseq : Int.IsEuclideanStepSequence a b n ab) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℤ,
      Int.euclideanStepProduct n ab * S = 1 ∧
        S * Int.euclideanStepProduct n ab = 1 := by
  -- Use the nonsingular inverse associated to the unit determinant of the product.
  have hdet := euclideanStepSequence_isUnit_det a b n ab hnot hseq
  refine ⟨(Int.euclideanStepProduct n ab)⁻¹, ?_, ?_⟩
  · exact Matrix.mul_nonsing_inv (Int.euclideanStepProduct n ab) hdet
  · exact Matrix.nonsing_inv_mul (Int.euclideanStepProduct n ab) hdet

end Int

end
