module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Canonical real lifts of angle sequences

This file defines the real lift of a sequence of quotient-valued angles obtained by
starting with the canonical representative and recursively adding canonical
representatives of consecutive differences.
-/

public section

noncomputable section

namespace Real.Angle

/-- The canonical recursively unwrapped real lift of an angle sequence. -/
def liftSequence (θ : ℕ → Real.Angle) : ℕ → ℝ
  | 0 => (θ 0).toReal
  | n + 1 => liftSequence θ n + (θ (n + 1) - θ n).toReal

/-- The canonical lift starts at the canonical real representative of the first angle. -/
@[simp]
theorem liftSequence_zero (θ : ℕ → Real.Angle) :
    liftSequence θ 0 = (θ 0).toReal := by
  rfl

/-- A successor value of the canonical lift adds the canonical representative of the
corresponding angle increment. -/
theorem liftSequence_succ (θ : ℕ → Real.Angle) (n : ℕ) :
    liftSequence θ (n + 1) =
      liftSequence θ n + (θ (n + 1) - θ n).toReal := by
  rfl

/-- Consecutive values of the canonical lift differ by the canonical representative of
the corresponding quotient-angle increment. -/
theorem liftSequence_succ_sub (θ : ℕ → Real.Angle) (n : ℕ) :
    liftSequence θ (n + 1) - liftSequence θ n =
      (θ (n + 1) - θ n).toReal := by
  rw [liftSequence_succ]
  abel

/-- Coercing a canonical real lift back to `Real.Angle` recovers the original sequence. -/
@[simp]
theorem coe_liftSequence (θ : ℕ → Real.Angle) (n : ℕ) :
    (liftSequence θ n : Real.Angle) = θ n := by
  induction n with
  | zero =>
      rw [liftSequence_zero]
      exact coe_toReal _
  | succ n ih =>
      rw [liftSequence_succ]
      change (liftSequence θ n : Real.Angle) +
        (((θ (n + 1) - θ n).toReal : ℝ) : Real.Angle) = θ (n + 1)
      rw [ih, coe_toReal]
      abel

/-- A real number in the principal interval represents a consecutive angle increment
exactly when it equals the corresponding increment of the canonical lift. -/
theorem coe_eq_liftSequence_succ_sub_iff (θ : ℕ → Real.Angle) (n : ℕ) (δ : ℝ)
    (hδ : δ ∈ Set.Ioc (-Real.pi) Real.pi) :
    (δ : Real.Angle) = θ (n + 1) - θ n ↔
      δ = liftSequence θ (n + 1) - liftSequence θ n := by
  rw [liftSequence_succ_sub]
  constructor
  · intro hcoe
    have hreal := congrArg Real.Angle.toReal hcoe
    have hδreal : (δ : Real.Angle).toReal = δ :=
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hδ
    rw [hδreal] at hreal
    exact hreal
  · intro hδeq
    rw [hδeq]
    exact coe_toReal _

/-- Two canonical angle lifts stay on the branch represented by their quotient-valued
difference when the initial branches agree and every recursively predicted difference
lies in the principal interval. -/
theorem liftSequence_sub_eq_toReal_sub_of_mem_Ioc
    (α β : ℕ → Real.Angle)
    (hzero : liftSequence α 0 - liftSequence β 0 = (α 0 - β 0).toReal)
    (hprincipal : ∀ n : ℕ,
      (α n - β n).toReal +
          (α (n + 1) - α n).toReal -
          (β (n + 1) - β n).toReal ∈ Set.Ioc (-Real.pi) Real.pi) :
    ∀ n : ℕ, liftSequence α n - liftSequence β n = (α n - β n).toReal := by
  intro n
  induction n with
  | zero =>
      exact hzero
  | succ n ih =>
      rw [liftSequence_succ, liftSequence_succ]
      have hrearrange :
          (liftSequence α n + (α (n + 1) - α n).toReal) -
              (liftSequence β n + (β (n + 1) - β n).toReal) =
            (liftSequence α n - liftSequence β n) +
              (α (n + 1) - α n).toReal -
              (β (n + 1) - β n).toReal := by
        abel
      rw [hrearrange, ih]
      have hcoe :
          (((α n - β n).toReal +
              (α (n + 1) - α n).toReal -
              (β (n + 1) - β n).toReal : ℝ) : Real.Angle) =
            α (n + 1) - β (n + 1) := by
        change (((α n - β n).toReal : ℝ) : Real.Angle) +
            (((α (n + 1) - α n).toReal : ℝ) : Real.Angle) -
            (((β (n + 1) - β n).toReal : ℝ) : Real.Angle) =
          α (n + 1) - β (n + 1)
        rw [coe_toReal, coe_toReal, coe_toReal]
        abel
      have hreal := congrArg Real.Angle.toReal hcoe
      have hprincipalReal :
          ((((α n - β n).toReal +
              (α (n + 1) - α n).toReal -
              (β (n + 1) - β n).toReal : ℝ) : Real.Angle).toReal) =
            (α n - β n).toReal +
              (α (n + 1) - α n).toReal -
              (β (n + 1) - β n).toReal :=
        Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr (hprincipal n)
      rw [hprincipalReal] at hreal
      exact hreal

/-- Along the even subsequence of a canonical angle lift, a quotient-valued relation
with an arbitrary real comparison sequence determines the corresponding real
representative.  The only branch hypothesis is that the representative predicted by
two angle increments and one comparison increment lies in the principal interval. -/
theorem liftSequence_even_sub_eq_toReal_of_coe_of_mem_Ioc
    (theta : ℕ → Real.Angle) (phi : ℕ → ℝ) (psi : ℕ → Real.Angle)
    (hzero : liftSequence theta 0 - phi 0 = (psi 0).toReal)
    (hcoe : ∀ j : ℕ,
      ((liftSequence theta (2 * j) - phi j : ℝ) : Real.Angle) = psi j)
    (hprincipal : ∀ j : ℕ,
      (psi j).toReal +
          (theta (2 * j + 1) - theta (2 * j)).toReal +
          (theta ((2 * j + 1) + 1) - theta (2 * j + 1)).toReal -
          (phi (j + 1) - phi j) ∈ Set.Ioc (-Real.pi) Real.pi) :
    ∀ j : ℕ, liftSequence theta (2 * j) - phi j = (psi j).toReal := by
  intro j
  induction j with
  | zero =>
      simpa using hzero
  | succ j ih =>
      have hindex : 2 * (j + 1) = (2 * j + 1) + 1 := by
        simp [Nat.mul_succ, Nat.add_assoc]
      have hrec :
          liftSequence theta (2 * (j + 1)) - phi (j + 1) =
            (liftSequence theta (2 * j) - phi j) +
              (theta (2 * j + 1) - theta (2 * j)).toReal +
              (theta ((2 * j + 1) + 1) - theta (2 * j + 1)).toReal -
              (phi (j + 1) - phi j) := by
        rw [hindex, liftSequence_succ, liftSequence_succ]
        abel
      let a := (psi j).toReal
      let b := (theta (2 * j + 1) - theta (2 * j)).toReal
      let c := (theta ((2 * j + 1) + 1) - theta (2 * j + 1)).toReal
      let d := phi (j + 1) - phi j
      have hprincipalReal :
          (((a + b + c - d : ℝ) : Real.Angle).toReal) = a + b + c - d :=
        Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr (by
          simpa only [a, b, c, d] using hprincipal j)
      have hreal := congrArg Real.Angle.toReal (hcoe (j + 1))
      rw [hrec, ih] at hreal
      change (((a + b + c - d : ℝ) : Real.Angle).toReal) = (psi (j + 1)).toReal at hreal
      rw [hprincipalReal] at hreal
      rw [hrec, ih]
      simpa only [a, b, c, d] using hreal

/-- An antitone real angle lift has positive winding number whenever the
remainder in a full-turn decomposition is smaller than the first traversed
gap.  This isolates the order argument from any particular orbit or scale
estimate. -/
theorem windingNumber_pos_of_antitone
    (lift : ℕ → ℝ) (hanti : Antitone lift) {k n : ℕ}
    (hkn : k < n) {m : ℤ} {remainder : ℝ}
    (hdecomp : lift k - lift n = 2 * Real.pi * (m : ℝ) + remainder)
    (hremainder : remainder < lift k - lift (k + 1)) :
    1 ≤ m := by
  have hsucc : k + 1 ≤ n := Nat.succ_le_iff.mpr hkn
  have hfirstGap : lift k - lift (k + 1) ≤ lift k - lift n := by
    linarith [hanti hsucc]
  by_contra hm
  have hmNonpos : m ≤ 0 := by
    apply Int.lt_add_one_iff.mp
    simpa only [zero_add] using (lt_of_not_ge hm)
  have hmReal : (m : ℝ) ≤ 0 := by
    exact_mod_cast hmNonpos
  have hturnNonpos : 2 * Real.pi * (m : ℝ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num) Real.pi_pos.le) hmReal
  rw [hdecomp] at hfirstGap
  linarith

end Real.Angle
