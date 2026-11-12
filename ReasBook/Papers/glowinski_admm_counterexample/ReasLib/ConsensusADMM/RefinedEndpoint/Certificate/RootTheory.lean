/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.RefinedEndpoint.Interval
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Period1024
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

open ADMM.RefinedEndpoint

/-- A proposed rational rectangle for a complex root. -/
structure RootBox where
  re : RatInterval
  im : RatInterval
  deriving DecidableEq

def RootBox.Contains (B : RootBox) (z : ℂ) : Prop :=
  B.re.Contains z.re ∧ B.im.Contains z.im

def RootBox.point (a b : ℚ) : RootBox := ⟨.point a, .point b⟩

/-- Exact interval image of multiplication; proposed rounded boxes are checked
against these rational endpoints. -/
def RootBox.mul (A B : RootBox) : RootBox :=
  ⟨(A.re.mul B.re).sub (A.im.mul B.im),
    (A.re.mul B.im).add (A.im.mul B.re)⟩

def RootBox.Encloses (A B : RootBox) : Prop :=
  A.re.lower ≤ B.re.lower ∧ B.re.upper ≤ A.re.upper ∧
  A.im.lower ≤ B.im.lower ∧ B.im.upper ≤ A.im.upper

instance (A B : RootBox) : Decidable (A.Encloses B) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem RootBox.Contains.weaken {A B : RootBox} {z : ℂ}
    (hz : B.Contains z) (h : A.Encloses B) : A.Contains z :=
  ⟨hz.1.weaken h.1 h.2.1, hz.2.weaken h.2.2.1 h.2.2.2⟩

theorem RootBox.Contains.mul {A B : RootBox} {z w : ℂ}
    (hz : A.Contains z) (hw : B.Contains w) : (A.mul B).Contains (z * w) := by
  constructor
  · simpa only [RootBox.mul, Complex.mul_re] using
      (hz.1.mul hw.1).sub (hz.2.mul hw.2)
  · simpa only [RootBox.mul, Complex.mul_im] using
      (hz.1.mul hw.2).add (hz.2.mul hw.1)

/-- Finite rational checks sufficient for an outward square-root enclosure. -/
def SqrtCheck (I J : RatInterval) : Prop :=
  0 ≤ J.lower ∧ 0 ≤ I.lower ∧ J.lower ^ 2 ≤ I.lower ∧
    0 ≤ J.upper ∧ I.upper ≤ J.upper ^ 2

instance (I J : RatInterval) : Decidable (SqrtCheck I J) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem sqrtCheck_sound {I J : RatInterval} {x : ℝ}
    (hx : I.Contains x) (h : SqrtCheck I J) : J.Contains (Real.sqrt x) :=
  RatInterval.contains_sqrt hx h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

def halfCosInput (B : RootBox) : RatInterval := ((RatInterval.point 1).add B.re).half
def halfSinInput (B : RootBox) : RatInterval := ((RatInterval.point 1).sub B.re).half

def HalfAngleCheck (A B : RootBox) : Prop :=
  SqrtCheck (halfCosInput A) B.re ∧ SqrtCheck (halfSinInput A) B.im

instance (A B : RootBox) : Decidable (HalfAngleCheck A B) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The positive half-angle branch is selected by the actual angle range. -/
theorem halfAngleCheck_sound {A B : RootBox} {t : ℝ}
    (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi)
    (ht : A.re.Contains (Real.cos t)) (h : HalfAngleCheck A B) :
    B.re.Contains (Real.cos (t / 2)) ∧ B.im.Contains (Real.sin (t / 2)) := by
  constructor
  · rw [Real.cos_half (by linarith [Real.pi_pos]) htπ]
    apply sqrtCheck_sound _ h.1
    simpa only [halfCosInput, Rat.cast_one] using ((RatInterval.contains_point 1).add ht).half
  · rw [Real.sin_half_eq_sqrt ht0 (by linarith [Real.pi_pos])]
    apply sqrtCheck_sound _ h.2
    simpa only [halfSinInput, Rat.cast_one] using ((RatInterval.contains_point 1).sub ht).half

/-- A common root of unity, independent of the Fourier mode index. -/
noncomputable def root (k : ℕ) : ℂ :=
  AddCircle.toCircle (ZMod.toAddCircle (k : Period1024.Phase))

@[simp] theorem root_zero : root 0 = 1 := by simp [root]

theorem root_succ (k : ℕ) : root (k + 1) = root 1 * root k := by
  simp only [root, Nat.cast_add, Nat.cast_one, map_add,
    AddCircle.toCircle_add, Circle.coe_mul]
  exact mul_comm _ _

theorem root_one_re : (root 1).re = Real.cos (Real.pi / 512) := by
  unfold root
  rw [ZMod.toAddCircle_natCast, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  simp only [ADMM.RefinedEndpoint.Data.period]
  rw [Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

theorem root_one_im : (root 1).im = Real.sin (Real.pi / 512) := by
  unfold root
  rw [ZMod.toAddCircle_natCast, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  simp only [ADMM.RefinedEndpoint.Data.period]
  rw [Complex.exp_ofReal_mul_I_im]
  congr 1
  ring

/-- The actual mode phases are entries of the common root table. -/
theorem phase_eq_root (h : Period1024.Coordinate) (k : ℕ) :
    Period1024.phase h (k : Period1024.Phase) = root ((Period1024.mode h * k) % 1024) := by
  have hcast : ((Period1024.mode h * k % 1024 : ℕ) : Period1024.Phase) =
      ((Period1024.mode h * k : ℕ) : Period1024.Phase) := by
    exact ZMod.natCast_mod _ _
  change (AddCircle.toCircle (ZMod.toAddCircle
    ((Period1024.mode h : Period1024.Phase) * (k : Period1024.Phase))) : ℂ) = _
  rw [← Nat.cast_mul, ← hcast]
  rfl

end ConsensusADMM.RefinedEndpoint.Certificate
