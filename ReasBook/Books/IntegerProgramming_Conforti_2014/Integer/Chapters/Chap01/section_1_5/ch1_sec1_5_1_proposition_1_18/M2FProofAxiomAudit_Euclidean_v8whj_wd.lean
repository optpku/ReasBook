/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_2_definition_1_17.PolynomialBound

@[expose] public section

/-- A Euclidean-algorithm input consists of naturals `a` and `b` with `0 < a` and `b ≤ a`. -/
structure EuclideanInput where
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_le_a : b ≤ a

namespace EuclideanInput

/-- Construct a Euclidean-algorithm input from explicit inequalities `0 < a` and `b ≤ a`. -/
def ofLE (a b : ℕ) (a_pos : 0 < a) (b_le_a : b ≤ a) : EuclideanInput :=
  ⟨a, b, a_pos, b_le_a⟩

/-- The binary encoding size of `input` is the sum of the binary lengths of its two entries. -/
def encodingSize (input : EuclideanInput) : ℕ :=
  Nat.size input.a + Nat.size input.b

/-- The initial Euclidean-algorithm state attached to `input`. -/
def initialState (input : EuclideanInput) : ℕ × ℕ :=
  (input.a, input.b)

end EuclideanInput

/-- One Euclidean step sends `(x, y)` to `(y, x % y)`. -/
def euclideanStep : ℕ × ℕ → ℕ × ℕ
  | (x, y) => (y, x % y)

namespace EuclideanInput

/-- An explicit fuelled loop counter for the Euclidean iteration on natural-number states. -/
def iterationCountAux : ℕ → ℕ × ℕ → ℕ
  | 0, _ => 0
  | _ + 1, (_, 0) => 0
  | fuel + 1, state@(_, _ + 1) => 1 + iterationCountAux fuel (euclideanStep state)

/-- An explicit fuelled terminal-state evaluator for the Euclidean iteration on natural-number
states. -/
def terminalStateAux : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, state => state
  | _ + 1, state@(_, 0) => state
  | fuel + 1, state@(_, _ + 1) => terminalStateAux fuel (euclideanStep state)

/-- The number of Euclidean iterations performed on `input` before the second component becomes
`0`. -/
def iterationCount (input : EuclideanInput) : ℕ :=
  iterationCountAux input.b input.initialState

/-- The Euclidean-algorithm running time on `input`, measured as a fixed arithmetic-operation cost
per iteration together with one final output step. -/
def runningTime (input : EuclideanInput) : ℕ :=
  2 * input.iterationCount + 1

/-- The terminal Euclidean-algorithm state reached from `input`. -/
def terminalState (input : EuclideanInput) : ℕ × ℕ :=
  terminalStateAux input.b input.initialState

/-- Expanding `input.encodingSize` gives the sum `Nat.size input.a + Nat.size input.b`. -/
theorem encodingSize_eq (input : EuclideanInput) :
    input.encodingSize = Nat.size input.a + Nat.size input.b := by
  -- The stated size formula is exactly the defining equation of `encodingSize`.
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_18/Euclidean.lean`:
the fuelled terminal state is obtained by iterating the step the number of times counted by the
fuelled loop counter. -/
private theorem terminalStateAux_eq_iterate_iterationCountAux
    (fuel : ℕ) (state : ℕ × ℕ) :
    terminalStateAux fuel state = (euclideanStep^[iterationCountAux fuel state]) state := by
  -- Induction on fuel keeps the evaluator and counter synchronized through each active step.
  induction fuel generalizing state with
  | zero =>
      simp [terminalStateAux, iterationCountAux]
  | succ fuel ih =>
      rcases state with ⟨x, y⟩
      cases y with
      | zero =>
          simp [terminalStateAux, iterationCountAux]
      | succ y =>
          simp only [terminalStateAux, iterationCountAux]
          rw [Nat.add_comm 1, Function.iterate_succ_apply]
          exact ih (euclideanStep (x, y + 1))

/-- The terminal state is the result of iterating `euclideanStep` exactly `input.iterationCount`
times from `input.initialState`. -/
theorem terminalState_def (input : EuclideanInput) :
    input.terminalState =
      (euclideanStep^[input.iterationCount]) input.initialState := by
  -- Specialize the synchronized fuelled-loop interface to the input's initial state and fuel.
  exact terminalStateAux_eq_iterate_iterationCountAux input.b input.initialState

/-- Expanding `input.runningTime` gives the fixed-cost arithmetic-operation count
`2 * input.iterationCount + 1`. -/
theorem runningTime_def (input : EuclideanInput) :
    input.runningTime = 2 * input.iterationCount + 1 := by
  -- The displayed cost is the defining equation of `runningTime`.
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_18/Euclidean.lean`:
fuel dominating the second component suffices for the Euclidean evaluator to reach the gcd
terminal state. -/
private theorem terminalStateAux_eq_gcd_zero_of_le
    (x y fuel : ℕ) (hy : y ≤ fuel) :
    terminalStateAux fuel (x, y) = (Nat.gcd x y, 0) := by
  -- Strong induction follows the strictly decreasing remainder in each Euclidean step.
  induction y using Nat.strong_induction_on generalizing x fuel with
  | h y ih =>
      cases y with
      | zero =>
          cases fuel with
          | zero =>
              simp [terminalStateAux]
          | succ fuel =>
              simp [terminalStateAux]
      | succ y =>
          cases fuel with
          | zero =>
              cases hy
          | succ fuel =>
              have hfuel : y ≤ fuel := Nat.le_of_succ_le_succ hy
              have hmod_lt : x % (y + 1) < y + 1 := Nat.mod_lt _ (Nat.succ_pos _)
              have hmod_le : x % (y + 1) ≤ fuel :=
                (Nat.le_of_lt_succ hmod_lt).trans hfuel
              calc
                terminalStateAux (fuel + 1) (x, y + 1) =
                    terminalStateAux fuel (y + 1, x % (y + 1)) := by
                  rfl
                _ = (Nat.gcd (y + 1) (x % (y + 1)), 0) :=
                  ih (x % (y + 1)) hmod_lt (y + 1) fuel hmod_le
                _ = (Nat.gcd (x % (y + 1)) (y + 1), 0) := by
                  rw [Nat.gcd_comm]
                _ = (Nat.gcd (y + 1) x, 0) := by
                  rw [← Nat.gcd_rec]
                _ = (Nat.gcd x (y + 1), 0) := by
                  rw [Nat.gcd_comm]

/-- The Euclidean algorithm on `input` terminates at `(Nat.gcd input.a input.b, 0)`. -/
theorem terminalState_eq_gcd_zero (input : EuclideanInput) :
    input.terminalState = (Nat.gcd input.a input.b, 0) := by
  -- Initial fuel equals `input.b`, so the general fuel invariant applies directly.
  exact terminalStateAux_eq_gcd_zero_of_le input.a input.b input.b le_rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_18/Euclidean.lean`:
when `0 < y ≤ x`, the remainder of `x` by `y` is at most half of `x`. -/
private theorem mod_le_half_of_pos_of_le {x y : ℕ} (hy : 0 < y) (hyx : y ≤ x) :
    x % y ≤ x / 2 := by
  -- If `y` is already at most half of `x`, use the strict remainder bound directly.
  by_cases hhalf : y ≤ x / 2
  · exact (Nat.mod_lt x hy).le.trans hhalf
  · -- Otherwise `x` lies below `2 * y`, so one subtraction computes the remainder.
    have htwo_pos : 0 < 2 := by
      omega
    have hx_lt : x < y * 2 := by
      exact (Nat.div_lt_iff_lt_mul htwo_pos).mp (Nat.lt_of_not_ge hhalf)
    have hsub_lt : x - y < y := by
      omega
    rw [Nat.mod_eq_sub_mod hyx, Nat.mod_eq_of_lt hsub_lt]
    omega

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_18/Euclidean.lean`:
doubling domination gives a one-step decrease of the binary logarithmic rank. -/
private theorem log2_succ_le_of_two_mul_le {r x : ℕ} (hr : 0 < r) (hrx : 2 * r ≤ x) :
    Nat.log2 r + 1 ≤ Nat.log2 x := by
  -- Rewrite the successor rank as the logarithm of a doubled argument, then use monotonicity.
  calc
    Nat.log2 r + 1 = Nat.log 2 (r * 2) := by
      rw [Nat.log2_eq_log_two, Nat.log_mul_base Nat.one_lt_two (ne_of_gt hr)]
    _ = Nat.log 2 (2 * r) := by
      rw [Nat.mul_comm]
    _ ≤ Nat.log 2 x := Nat.log_mono_right hrx
    _ = Nat.log2 x := by
      rw [Nat.log2_eq_log_two]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_18/Euclidean.lean`:
the fuelled Euclidean loop has length at most twice the binary logarithmic rank plus one. -/
private theorem iterationCountAux_le_log2_of_le
    (x y fuel : ℕ) (hyx : y ≤ x) :
    iterationCountAux fuel (x, y) ≤ 1 + 2 * Nat.log2 x := by
  -- Strong induction controls two Euclidean steps by the halving remainder invariant.
  induction x using Nat.strong_induction_on generalizing y fuel with
  | h x ih =>
      cases fuel with
      | zero =>
          simp [iterationCountAux]
      | succ fuel =>
          cases y with
          | zero =>
              simp [iterationCountAux]
          | succ y =>
              cases fuel with
              | zero =>
                  simp [iterationCountAux]
              | succ fuel =>
                  by_cases hr : x % (y + 1) = 0
                  · simp [iterationCountAux, euclideanStep, hr]
                  · have hr_pos : 0 < x % (y + 1) := Nat.pos_of_ne_zero hr
                    have hr_lt : x % (y + 1) < x :=
                      (Nat.mod_lt x (Nat.succ_pos y)).trans_le hyx
                    have hnext_le : (y + 1) % (x % (y + 1)) ≤ x % (y + 1) :=
                      (Nat.mod_lt (y + 1) hr_pos).le
                    have hrecursive :=
                      ih (x % (y + 1)) hr_lt ((y + 1) % (x % (y + 1))) fuel hnext_le
                    have hhalf : x % (y + 1) ≤ x / 2 :=
                      mod_le_half_of_pos_of_le (Nat.succ_pos y) hyx
                    have hdouble : 2 * (x % (y + 1)) ≤ x := by
                      omega
                    have hlog : Nat.log2 (x % (y + 1)) + 1 ≤ Nat.log2 x :=
                      log2_succ_le_of_two_mul_le hr_pos hdouble
                    obtain ⟨r, hr_eq⟩ := Nat.exists_eq_succ_of_ne_zero hr
                    rw [hr_eq] at hrecursive hlog
                    simp only [iterationCountAux, euclideanStep]
                    rw [hr_eq]
                    simp only [iterationCountAux, euclideanStep]
                    simp only [Nat.succ_eq_add_one] at hrecursive hlog ⊢
                    omega

/-- The Euclidean algorithm on `input` performs at most `1 + 2 * Nat.log2 input.a` iterations. -/
theorem iterationCount_le_log2 (input : EuclideanInput) :
    input.iterationCount ≤ 1 + 2 * Nat.log2 input.a := by
  -- Apply the fuel-independent rank bound using the input invariant `b ≤ a`.
  exact iterationCountAux_le_log2_of_le input.a input.b input.b input.b_le_a

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_18/Euclidean.lean`:
the binary logarithmic rank of the first entry is bounded by the total encoding size. -/
private theorem log2_le_encodingSize (input : EuclideanInput) :
    Nat.log2 input.a ≤ input.encodingSize := by
  -- Binary length strictly dominates the logarithm because the first entry is positive.
  have hsize_pos : 0 < Nat.size input.a := Nat.size_pos.2 input.a_pos
  have hlog_size : Nat.log2 input.a < Nat.size input.a := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow' (ne_of_gt hsize_pos) (Nat.lt_size_self input.a)
  -- The first entry's size is one summand of the complete input encoding.
  rw [encodingSize_eq]
  omega

/-- The Euclidean-algorithm loop count is polynomially bounded by the binary encoding size of the
input. -/
theorem iterationCount_polynomiallyBounded :
    Function.PolynomiallyBoundedByNat iterationCount encodingSize := by
  -- The affine polynomial `1 + 2X` dominates the logarithmic iteration bound.
  apply Function.polynomiallyBoundedByNat_iff.2
  refine ⟨Polynomial.C 1 + Polynomial.C 2 * Polynomial.X, ?_⟩
  intro input
  -- Transport the logarithmic iteration estimate through the encoding-size bound.
  have hlog_encoding := log2_le_encodingSize input
  have hlog_bound : 1 + 2 * Nat.log2 input.a ≤ 1 + 2 * input.encodingSize := by
    omega
  have hbound : iterationCount input ≤ 1 + 2 * input.encodingSize := by
    exact (iterationCount_le_log2 input).trans hlog_bound
  simpa [Polynomial.eval_add, Polynomial.eval_mul] using hbound

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_18/Euclidean.lean`:
the fixed-cost running time is bounded by an affine function of the binary encoding size. -/
private theorem runningTime_le_affine_encodingSize (input : EuclideanInput) :
    input.runningTime ≤ 3 + 4 * input.encodingSize := by
  -- The logarithmic rank is bounded by the first summand of the encoding size.
  have hlog_encoding := log2_le_encodingSize input
  -- Substitute the iteration bound into the fixed arithmetic cost and normalize.
  have hiterations := iterationCount_le_log2 input
  rw [runningTime_def]
  omega

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_18/Euclidean.lean`:
the running-time bound is expressed by evaluation of the affine polynomial `3 + 4X`. -/
private theorem runningTime_le_eval_affinePolynomial (input : EuclideanInput) :
    input.runningTime ≤
      (Polynomial.C 3 + Polynomial.C 4 * Polynomial.X).eval input.encodingSize := by
  -- Normalize the polynomial evaluation to the established affine estimate.
  simpa [Polynomial.eval_add, Polynomial.eval_mul] using
    runningTime_le_affine_encodingSize input

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_18/Euclidean.lean
The Euclidean-algorithm running time is polynomially bounded by the binary encoding size of the
input. -/
theorem runningTime_polynomiallyBounded :
    Function.PolynomiallyBoundedByNat runningTime encodingSize := by
  -- Substituting the loop bound into the fixed-cost model gives the affine witness `3 + 4X`.
  apply Function.polynomiallyBoundedByNat_iff.2
  refine ⟨Polynomial.C 3 + Polynomial.C 4 * Polynomial.X, ?_⟩
  -- The bridge lemma packages the witness's pointwise evaluation in the required normal form.
  exact runningTime_le_eval_affinePolynomial

end EuclideanInput

#print axioms EuclideanInput.runningTime_polynomiallyBounded

end

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_0eed5fa37219800986c1"
#print axioms _root_.EuclideanInput.runningTime_polynomiallyBounded
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_0eed5fa37219800986c1"
