/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_proposition_1_18.Euclidean

public section

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_algorithm_1_5.lean:
if the remaining fuel dominates the second component, then
`EuclideanInput.terminalStateAux` reaches the gcd terminal state. -/
theorem EuclideanInput.terminalStateAux_eq_gcd_zero_of_le
    (x y fuel : ℕ) (hy : y ≤ fuel) :
    EuclideanInput.terminalStateAux fuel (x, y) = (Nat.gcd x y, 0) := by
  -- Strong induction on the second component follows the Euclidean descent.
  revert x fuel
  refine Nat.strong_induction_on y ?_
  intro y ih x fuel hy
  cases y with
  | zero =>
      cases fuel with
      | zero =>
          simp [EuclideanInput.terminalStateAux]
      | succ fuel =>
          simp [EuclideanInput.terminalStateAux]
  | succ y =>
      cases fuel with
      | zero =>
          cases hy
      | succ fuel =>
          have hfuel : y ≤ fuel := Nat.le_of_succ_le_succ hy
          have hmod_lt : x % (y + 1) < y + 1 := Nat.mod_lt _ (Nat.succ_pos _)
          have hmod_le : x % (y + 1) ≤ fuel := by
            exact (Nat.le_of_lt_succ hmod_lt).trans hfuel
          calc
            EuclideanInput.terminalStateAux (fuel + 1) (x, y + 1)
                = EuclideanInput.terminalStateAux fuel (y + 1, x % (y + 1)) := by
                    rfl
            _ = (Nat.gcd (y + 1) (x % (y + 1)), 0) :=
              ih (x % (y + 1)) hmod_lt (y + 1) fuel hmod_le
            _ = (Nat.gcd (x % (y + 1)) (y + 1), 0) := by
              rw [Nat.gcd_comm]
            _ = (Nat.gcd (y + 1) x, 0) := by
              rw [← Nat.gcd_rec]
            _ = (Nat.gcd x (y + 1), 0) := by
              rw [Nat.gcd_comm]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_algorithm_1_5.lean.
Algorithm 1.5: for `a ≥ b` with `0 < a`, the Euclidean algorithm returns `Nat.gcd a b` as its
output value. -/
theorem euclideanAlgorithm_returns_gcd
    (a b : ℕ) (ha : 0 < a) (hb : b ≤ a) :
    ((EuclideanInput.ofLE a b ha hb).terminalState).1 = Nat.gcd a b := by
  -- The Euclidean loop starts with fuel `b`, which is enough to drive the second component to `0`.
  simpa [EuclideanInput.ofLE, EuclideanInput.terminalState, EuclideanInput.initialState] using
    congrArg Prod.fst
      (EuclideanInput.terminalStateAux_eq_gcd_zero_of_le a b b le_rfl)

end

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_c65e35a7d0f9b4275a86"
#print axioms _root_.euclideanAlgorithm_returns_gcd
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_c65e35a7d0f9b4275a86"
