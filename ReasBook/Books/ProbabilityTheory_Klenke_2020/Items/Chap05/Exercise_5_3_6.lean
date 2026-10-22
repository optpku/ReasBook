/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

/-- Helper for Exercise 5.3.6: a valid real logarithmic base is positive and different from `1`.
-/
structure LogBase where
  val : ℝ
  pos : 0 < val
  ne_one : val ≠ 1

instance : CoeOut LogBase ℝ := ⟨LogBase.val⟩

/-- Helper for Exercise 5.3.6: a prefix code assigns a codeword to each symbol so that no codeword
is a prefix of a different one. -/
structure PrefixCode (α : Type*) (E : Type*) where
  encode : E → List α
  prefix_free : Pairwise (fun e₁ e₂ ↦ ¬ (encode e₁ <+: encode e₂))

namespace PrefixCode

variable {α E : Type*} [Fintype E]

/-- Helper for Exercise 5.3.6: the expected code length is the `p`-weighted sum of the codeword
lengths. -/
noncomputable def expectedLength (C : PrefixCode α E) (p : PMF E) : ℝ :=
  ∑ e : E, (p e).toReal * (C.encode e).length

/-- Helper for Exercise 5.3.6: unfolding `expectedLength` gives the defining finite sum. -/
@[simp] theorem expectedLength_def (C : PrefixCode α E) (p : PMF E) :
    C.expectedLength p = ∑ e : E, (p e).toReal * (C.encode e).length := rfl

end PrefixCode

/-- Helper for Exercise 5.3.6: on a finite alphabet, the base-`b` entropy is the usual finite
Shannon sum in logarithmic base `b`, viewed in `EReal`. -/
noncomputable def entropyInBase {E : Type*} [Fintype E] (b : LogBase) (p : PMF E) : EReal :=
  ((-∑ e : E, (p e).toReal * Real.logb (b : ℝ) (p e).toReal : ℝ) : EReal)

/-- Helper for Exercise 5.3.6: `entropyInBase` evaluates to the corresponding finite real sum. -/
@[simp] theorem entropyInBase_toReal_eq_sum {E : Type*} [Fintype E] (b : LogBase) (p : PMF E) :
    (entropyInBase b p).toReal = -∑ e : E, (p e).toReal * Real.logb (b : ℝ) (p e).toReal := by
  simp [entropyInBase]

/-- Helper for Exercise 5.3.6: the real masses of a finite probability mass function sum to `1`.
-/
private theorem sumToRealPmf {E : Type*} [Fintype E] (p : PMF E) :
    ∑ e : E, (p e).toReal = 1 := by
  have htsum :
      (∑' e : E, p e).toReal = ∑' e : E, (p e).toReal :=
    ENNReal.tsum_toReal_eq fun e ↦ p.apply_ne_top e
  rw [p.tsum_coe, ENNReal.toReal_one, tsum_fintype] at htsum
  simpa using htsum.symm

/-- Helper for Exercise 5.3.6: Jensen's inequality for `x ↦ x * log x`, written in the form
`∑ p * log (p / w) ≥ 0`. -/
private theorem sumMulLogRatio_nonneg {E : Type*} [Fintype E]
    (p : PMF E) (w : E → ℝ) (hw_sum : ∑ e : E, w e = 1) (hw_pos : ∀ e, 0 < w e) :
    0 ≤ ∑ e : E, (p e).toReal * Real.log ((p e).toReal / w e) := by
  let φ : ℝ → ℝ := fun x ↦ x * Real.log x
  have hconv : ConvexOn ℝ (Set.Ici 0) φ := by
    simpa [φ] using Real.convexOn_mul_log
  have hmem : ∀ e : E, ((p e).toReal / w e) ∈ Set.Ici (0 : ℝ) := by
    intro e
    exact div_nonneg ENNReal.toReal_nonneg (le_of_lt (hw_pos e))
  have hnonneg : ∀ e : E, 0 ≤ w e := by
    intro e
    exact le_of_lt (hw_pos e)
  have hj :=
    ConvexOn.map_sum_le (t := Finset.univ) (w := w)
      (p := fun e ↦ (p e).toReal / w e) hconv (fun e _ ↦ hnonneg e) hw_sum
      (fun e _ ↦ hmem e)
  have hweighted : ∑ e : E, w e * ((p e).toReal / w e) = 1 := by
    calc
      ∑ e : E, w e * ((p e).toReal / w e) = ∑ e : E, (p e).toReal := by
        apply Finset.sum_congr rfl
        intro e he
        field_simp [ne_of_gt (hw_pos e)]
      _ = 1 := sumToRealPmf p
  have hkl :
      0 ≤ ∑ e : E, w e * (((p e).toReal / w e) * Real.log ((p e).toReal / w e)) := by
    have hj' :
        φ (∑ e : E, w e * ((p e).toReal / w e)) ≤
          ∑ e : E, w e * φ ((p e).toReal / w e) := by
      simpa [smul_eq_mul] using hj
    rw [hweighted] at hj'
    simpa [φ] using hj'
  have hrewrite :
      (∑ e : E, w e * (((p e).toReal / w e) * Real.log ((p e).toReal / w e))) =
        ∑ e : E, (p e).toReal * Real.log ((p e).toReal / w e) := by
    apply Finset.sum_congr rfl
    intro e he
    field_simp [ne_of_gt (hw_pos e)]
  rwa [hrewrite] at hkl

/-- Helper for Exercise 5.3.6: any strictly positive sub-probability `q` bounds the entropy by
the logarithmic sum `-∑ p(e) log_b q(e)`. -/
private theorem entropyInBase_le_logSum_of_subprobability {E : Type*} [Fintype E]
    (b : LogBase) (hb : 1 < (b : ℝ)) (p : PMF E) (q : E → ℝ) (hq_pos : ∀ e, 0 < q e)
    (hq_sum : ∑ e : E, q e ≤ 1) :
    (entropyInBase b p).toReal ≤ -∑ e : E, (p e).toReal * Real.logb (b : ℝ) (q e) := by
  classical
  let Q : ℝ := ∑ e : E, q e
  let w : E → ℝ := fun e ↦ q e / Q
  letI : Nonempty E := ⟨p.support_nonempty.some⟩
  have hQ_pos : 0 < Q := by
    let e₀ : E := Classical.choice inferInstance
    calc
      0 < q e₀ := hq_pos e₀
      _ ≤ ∑ e : E, q e := by
        simpa [Q] using
          Finset.single_le_sum (fun e _ ↦ le_of_lt (hq_pos e)) (Finset.mem_univ e₀)
  have hQ_le_one : Q ≤ 1 := by
    simpa [Q] using hq_sum
  have hw_sum : ∑ e : E, w e = 1 := by
    calc
      ∑ e : E, w e = (∑ e : E, q e) / Q := by
        simp [w, Q, Finset.sum_div]
      _ = 1 := by
        simp [Q, hQ_pos.ne']
  have hw_pos : ∀ e : E, 0 < w e := by
    intro e
    exact div_pos (hq_pos e) hQ_pos
  have hkl_nonneg :
      0 ≤ ∑ e : E, (p e).toReal * Real.log ((p e).toReal / w e) :=
    sumMulLogRatio_nonneg p w hw_sum hw_pos
  have hratio :
      (∑ e : E, (p e).toReal * Real.log ((p e).toReal / w e)) =
        ∑ e : E, (p e).toReal * Real.log (p e).toReal -
          ∑ e : E, (p e).toReal * Real.log (w e) := by
    calc
      ∑ e : E, (p e).toReal * Real.log ((p e).toReal / w e) =
          ∑ e : E,
            ((p e).toReal * Real.log (p e).toReal -
              (p e).toReal * Real.log (w e)) := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases hp : p e = 0
        · simp [hp]
        · rw [Real.log_div (ENNReal.toReal_pos hp (p.apply_ne_top e)).ne' (ne_of_gt (hw_pos e))]
          ring
      _ = _ := by
        rw [Finset.sum_sub_distrib]
  have hentropy_le_w :
      -∑ e : E, (p e).toReal * Real.log (p e).toReal ≤
        -∑ e : E, (p e).toReal * Real.log (w e) := by
    rw [hratio] at hkl_nonneg
    linarith
  have hw_eq :
      (-∑ e : E, (p e).toReal * Real.log (w e)) =
        (-∑ e : E, (p e).toReal * Real.log (q e)) + Real.log Q := by
    calc
      -∑ e : E, (p e).toReal * Real.log (w e) =
          -∑ e : E, ((p e).toReal * Real.log (q e) - (p e).toReal * Real.log Q) := by
        congr 1
        apply Finset.sum_congr rfl
        intro e he
        rw [show w e = q e / Q by rfl, Real.log_div (ne_of_gt (hq_pos e)) (ne_of_gt hQ_pos)]
        ring
      _ = -((∑ e : E, (p e).toReal * Real.log (q e)) -
            ∑ e : E, (p e).toReal * Real.log Q) := by
        rw [Finset.sum_sub_distrib]
      _ = (-∑ e : E, (p e).toReal * Real.log (q e)) +
            ∑ e : E, (p e).toReal * Real.log Q := by
        ring
      _ = (-∑ e : E, (p e).toReal * Real.log (q e)) +
            Real.log Q * ∑ e : E, (p e).toReal := by
        congr 1
        calc
          ∑ e : E, (p e).toReal * Real.log Q = ∑ e : E, Real.log Q * (p e).toReal := by
            apply Finset.sum_congr rfl
            intro e he
            ring
          _ = Real.log Q * ∑ e : E, (p e).toReal := by
            rw [Finset.mul_sum]
      _ = (-∑ e : E, (p e).toReal * Real.log (q e)) + Real.log Q := by
        rw [sumToRealPmf p]
        ring
  have hlogQ_nonpos : Real.log Q ≤ 0 := by
    exact Real.log_nonpos hQ_pos.le hQ_le_one
  have hnat :
      -∑ e : E, (p e).toReal * Real.log (p e).toReal ≤
        -∑ e : E, (p e).toReal * Real.log (q e) := by
    rw [hw_eq] at hentropy_le_w
    linarith
  have hcoeff_pos : 0 < (Real.log (b : ℝ))⁻¹ := by
    exact inv_pos.mpr (Real.log_pos hb)
  have hlogb :
      -∑ e : E, (p e).toReal * Real.logb (b : ℝ) (p e).toReal ≤
        -∑ e : E, (p e).toReal * Real.logb (b : ℝ) (q e) := by
    have hscaled := mul_le_mul_of_nonneg_left hnat (le_of_lt hcoeff_pos)
    simpa [Real.logb, div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      using hscaled
  simpa using hlogb

/-- Helper for Exercise 5.3.6: a natural base `b ≥ 2` determines a valid logarithmic base. -/
private theorem nat_base_one_lt (b : ℕ) (hb : 2 ≤ b) : (1 : ℝ) < b := by
  have h : (1 : ℕ) < b := lt_of_lt_of_le one_lt_two hb
  exact_mod_cast h

/-- Helper for Exercise 5.3.6: the logarithmic base attached to a natural number `b ≥ 2`. -/
def nat_base (b : ℕ) (hb : 2 ≤ b) : LogBase :=
  ⟨b, by positivity, ne_of_gt (nat_base_one_lt b hb)⟩

/-- The 26 letters of the Latin alphabet used in the Morse-code table of the exercise. -/
inductive MorseLetter
  | A | B | C | D | E | F | G | H | I | J | K | L | M
  | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
  deriving DecidableEq, Fintype

/-- The German letter frequencies from the Morse-code table in Exercise 5.3.6. -/
noncomputable def morseGermanWeight : MorseLetter → ENNReal
  | .A => 651 / 10000
  | .B => 189 / 10000
  | .C => 306 / 10000
  | .D => 508 / 10000
  | .E => 1740 / 10000
  | .F => 166 / 10000
  | .G => 301 / 10000
  | .H => 476 / 10000
  | .I => 755 / 10000
  | .J => 27 / 10000
  | .K => 121 / 10000
  | .L => 344 / 10000
  | .M => 253 / 10000
  | .N => 978 / 10000
  | .O => 251 / 10000
  | .P => 79 / 10000
  | .Q => 2 / 10000
  | .R => 7 / 100
  | .S => 727 / 10000
  | .T => 615 / 10000
  | .U => 435 / 10000
  | .V => 67 / 10000
  | .W => 189 / 10000
  | .X => 3 / 10000
  | .Y => 4 / 10000
  | .Z => 113 / 10000

/-- Helper for Exercise 5.3.6: the Morse alphabet as an explicit finset for closed finite
computations. -/
def morseLetterFinset : Finset MorseLetter :=
  { MorseLetter.A, MorseLetter.B, MorseLetter.C, MorseLetter.D, MorseLetter.E, MorseLetter.F,
    MorseLetter.G, MorseLetter.H, MorseLetter.I, MorseLetter.J, MorseLetter.K, MorseLetter.L,
    MorseLetter.M, MorseLetter.N, MorseLetter.O, MorseLetter.P, MorseLetter.Q, MorseLetter.R,
    MorseLetter.S, MorseLetter.T, MorseLetter.U, MorseLetter.V, MorseLetter.W, MorseLetter.X,
    MorseLetter.Y, MorseLetter.Z }

/-- Helper for Exercise 5.3.6: `Finset.univ` on `MorseLetter` is the explicit 26-letter alphabet. -/
theorem univ_eq_morseLetterFinset : (Finset.univ : Finset MorseLetter) = morseLetterFinset := by
  decide

-- Proof sketch: expand the finite sum over all 26 letters and check that the listed decimal
-- frequencies add up to `1`.
/-- The Morse-code frequency table defines a probability mass function on the alphabet. -/
theorem morseGermanWeight_sum : ∑ a : MorseLetter, morseGermanWeight a = 1 := by
  have hsum :
      (∑ a : MorseLetter, morseGermanWeight a).toReal = 1 := by
    rw [ENNReal.toReal_sum]
    · rw [univ_eq_morseLetterFinset]
      -- Expand the explicit 26-term real sum coming from the German frequency table.
      simp [morseLetterFinset, morseGermanWeight, Finset.sum_insert, Finset.mem_singleton]
      norm_num
    · intro a ha
      cases a <;>
        exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by norm_num)
  have hne : (∑ a : MorseLetter, morseGermanWeight a) ≠ ⊤ := by
    intro htop
    simp [htop] at hsum
  -- Compare after applying `toReal`, where the arithmetic becomes a closed rational identity.
  exact (ENNReal.toReal_eq_toReal_iff' hne ENNReal.one_ne_top).mp hsum

/-- The German letter-frequency law from Exercise 5.3.6 as a probability mass function. -/
noncomputable def morseGermanPMF : PMF MorseLetter :=
  PMF.ofFintype morseGermanWeight morseGermanWeight_sum

/-- Helper for Exercise 5.3.6: the PMF obtained from the German Morse weights evaluates to the
listed table entry at each letter. -/
@[simp] theorem morseGermanPMF_apply (a : MorseLetter) :
    morseGermanPMF a = morseGermanWeight a := by
  -- The finite PMF construction is definitionally the given weight function.
  simp [morseGermanPMF]

/-- The ternary Morse code from Exercise 5.3.6, with `0 = dot`, `1 = dash`, and `2` the
terminating pause symbol. -/
def morseCodeWord : MorseLetter → List (Fin 3)
  | .A => [0, 1, 2]
  | .B => [1, 0, 0, 0, 2]
  | .C => [1, 0, 1, 0, 2]
  | .D => [1, 0, 0, 2]
  | .E => [0, 2]
  | .F => [0, 0, 1, 0, 2]
  | .G => [1, 1, 0, 2]
  | .H => [0, 0, 0, 0, 2]
  | .I => [0, 0, 2]
  | .J => [0, 1, 1, 1, 2]
  | .K => [1, 0, 1, 2]
  | .L => [0, 1, 0, 0, 2]
  | .M => [1, 1, 2]
  | .N => [1, 0, 2]
  | .O => [1, 1, 1, 2]
  | .P => [0, 1, 1, 0, 2]
  | .Q => [1, 1, 0, 1, 2]
  | .R => [0, 1, 0, 2]
  | .S => [0, 0, 0, 2]
  | .T => [1, 2]
  | .U => [0, 0, 1, 2]
  | .V => [0, 0, 0, 1, 2]
  | .W => [0, 1, 1, 2]
  | .X => [1, 0, 0, 1, 2]
  | .Y => [1, 0, 1, 1, 2]
  | .Z => [1, 1, 0, 0, 2]

/-- The Morse code is prefix-free once the terminating pause symbol is included. -/
theorem morseCodeWord_prefix_free :
    Pairwise fun a b : MorseLetter ↦ ¬ (morseCodeWord a <+: morseCodeWord b) := by
  simpa [Pairwise] using
    (show ∀ a b : MorseLetter, a ≠ b → ¬ (morseCodeWord a <+: morseCodeWord b) by
      decide)

/-- The ternary Morse code as a prefix code over the digit alphabet `Fin 3`. -/
def morseCode : PrefixCode (Fin 3) MorseLetter where
  encode := morseCodeWord
  prefix_free := morseCodeWord_prefix_free

/-- Helper for Exercise 5.3.6: the ternary Kraft weight attached to a Morse codeword is
`3^{-length}`. -/
noncomputable def morseCodeWeight (a : MorseLetter) : ℝ :=
  ((1 / 3 : ℝ) ^ (morseCodeWord a).length)

/-- Helper for Exercise 5.3.6: the Morse code weights are strictly positive. -/
private theorem morseCodeWeight_pos (a : MorseLetter) : 0 < morseCodeWeight a := by
  simp [morseCodeWeight]

/-- Helper for Exercise 5.3.6: the explicit ternary Kraft sum of the Morse code is at most `1`. -/
private theorem morseCodeWeight_sum_le_one :
    (∑ a : MorseLetter, morseCodeWeight a) ≤ 1 := by
  rw [univ_eq_morseLetterFinset]
  simp [morseLetterFinset, morseCodeWeight, morseCodeWord, Finset.sum_insert,
    Finset.mem_singleton]
  norm_num

/-- Helper for Exercise 5.3.6: for a `b`-adic code, the logarithmic codeweight sum is the
expected code length. -/
private theorem natBaseExpectedLengthEqNegativeLogCodeweightSum {E : Type*} [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) (C : PrefixCode (Fin b) E) :
    C.expectedLength p =
      -∑ e : E, (p e).toReal *
        Real.logb (nat_base b hb : ℝ) ((1 / b : ℝ) ^ (C.encode e).length) := by
  rw [PrefixCode.expectedLength_def]
  have hself : Real.logb (nat_base b hb : ℝ) (b : ℝ) = 1 := by
    simpa using Real.logb_self_eq_one (nat_base_one_lt b hb)
  calc
    ∑ e : E, (p e).toReal * (C.encode e).length =
        ∑ e : E,
          -((p e).toReal *
            Real.logb (nat_base b hb : ℝ) ((1 / b : ℝ) ^ (C.encode e).length)) := by
      apply Finset.sum_congr rfl
      intro e he
      calc
        (p e).toReal * (C.encode e).length = -((p e).toReal * (-(C.encode e).length : ℝ)) := by
          ring
        _ = -((p e).toReal *
            Real.logb (nat_base b hb : ℝ) ((1 / b : ℝ) ^ (C.encode e).length)) := by
          rw [Real.logb_pow, one_div, Real.logb_inv, hself]
          ring
    _ = -∑ e : E, (p e).toReal *
          Real.logb (nat_base b hb : ℝ) ((1 / b : ℝ) ^ (C.encode e).length) := by
      rw [← Finset.sum_neg_distrib]

-- Proof sketch: unfold `PrefixCode.expectedLength`, substitute the 26 values from the table, and
-- evaluate the resulting rational sum.
/-- The average ternary Morse-code length for the German frequency table is `3.4429`. -/
theorem morseAverageCodeLength_eq :
    morseCode.expectedLength morseGermanPMF = (34429 : ℝ) / 10000 := by
  -- Expand the expected length into the finite weighted sum over all letters.
  rw [PrefixCode.expectedLength_def]
  rw [univ_eq_morseLetterFinset]
  -- Replace the PMF values and the codeword lengths by the explicit table entries.
  simp [morseLetterFinset, morseGermanPMF_apply, morseCode, morseCodeWord, morseGermanWeight,
    Finset.sum_insert, Finset.mem_singleton]
  -- The remaining goal is the closed rational identity from the exercise table.
  norm_num

-- Proof sketch: use `morseAverageCodeLength_eq` for the explicit average length, then compare it
-- with the base-`3` entropy sum for `morseGermanPMF`.
/-- Exercise 5.3.6: For the German letter frequencies, the Morse code has average ternary length
`3.4429`, and the ternary entropy `H₃` is bounded above by this average length. -/
theorem morse_code_average_length_and_entropy_comparison :
    morseCode.expectedLength morseGermanPMF = (34429 : ℝ) / 10000 ∧
      (entropyInBase (nat_base 3 (show 2 ≤ 3 by norm_num)) morseGermanPMF).toReal ≤
        morseCode.expectedLength
        morseGermanPMF := by
  refine ⟨morseAverageCodeLength_eq, ?_⟩
  let b : LogBase := nat_base 3 (show 2 ≤ 3 by norm_num)
  have hb : 1 < (b : ℝ) := nat_base_one_lt 3 (show 2 ≤ 3 by norm_num)
  have hentropy_le :
      (entropyInBase b morseGermanPMF).toReal ≤
        -∑ a : MorseLetter, (morseGermanPMF a).toReal * Real.logb (b : ℝ) (morseCodeWeight a) := by
    exact entropyInBase_le_logSum_of_subprobability b hb morseGermanPMF morseCodeWeight
      morseCodeWeight_pos morseCodeWeight_sum_le_one
  have hlength :
      -∑ a : MorseLetter, (morseGermanPMF a).toReal * Real.logb (b : ℝ) (morseCodeWeight a) =
        morseCode.expectedLength morseGermanPMF := by
    simpa [b, morseCodeWeight] using
      (natBaseExpectedLengthEqNegativeLogCodeweightSum 3 (show 2 ≤ 3 by norm_num)
        morseGermanPMF morseCode).symm
  simpa [b] using hentropy_le.trans_eq hlength
