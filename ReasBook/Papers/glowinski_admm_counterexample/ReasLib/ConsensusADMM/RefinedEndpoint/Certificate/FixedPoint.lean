/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.RootTheory

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

open ADMM.RefinedEndpoint

/-- Integer endpoints on one common positive grid. -/
structure IntInterval where
  lower : ℤ
  upper : ℤ
  deriving DecidableEq

def IntInterval.toRat (A : IntInterval) (s : ℤ) : RatInterval :=
  ⟨(A.lower : ℚ) / s, (A.upper : ℚ) / s⟩

def IntInterval.mulLower (A B : IntInterval) : ℤ :=
  min (min (A.lower * B.lower) (A.lower * B.upper))
    (min (A.upper * B.lower) (A.upper * B.upper))

def IntInterval.mulUpper (A B : IntInterval) : ℤ :=
  max (max (A.lower * B.lower) (A.lower * B.upper))
    (max (A.upper * B.lower) (A.upper * B.upper))

theorem IntInterval.mul_lower {s : ℤ} (hs : 0 < s) (A B : IntInterval) :
    ((A.toRat s).mul (B.toRat s)).lower = (A.mulLower B : ℚ) / ((s : ℚ) * s) := by
  have hsq : 0 ≤ (s : ℚ) * s := mul_self_nonneg _
  simp only [toRat, RatInterval.mul, mulLower]
  simp_rw [div_mul_div_comm, min_div_div_right hsq]
  norm_cast

theorem IntInterval.mul_upper {s : ℤ} (hs : 0 < s) (A B : IntInterval) :
    ((A.toRat s).mul (B.toRat s)).upper = (A.mulUpper B : ℚ) / ((s : ℚ) * s) := by
  have hsq : 0 ≤ (s : ℚ) * s := mul_self_nonneg _
  simp only [toRat, RatInterval.mul, mulUpper]
  simp_rw [div_mul_div_comm, max_div_div_right hsq]
  norm_cast

structure IntRootBox where
  re : IntInterval
  im : IntInterval
  deriving DecidableEq

/-- Balanced lookup trees keep kernel certificate checks logarithmic in the
table length, without relying on native evaluation or unchecked array code. -/
inductive RootTree
  | leaf (value : IntRootBox)
  | node (split : ℕ) (left right : RootTree)

def RootTree.get : RootTree → ℕ → IntRootBox
  | .leaf value, _ => value
  | .node split left right, k =>
      if k < split then left.get k else right.get (k - split)

def RootTree.leafCount : RootTree → ℕ
  | .leaf _ => 1
  | .node _ left right => left.leafCount + right.leafCount

def IntRootBox.toRat (A : IntRootBox) (s : ℤ) : RootBox :=
  ⟨A.re.toRat s, A.im.toRat s⟩

def IntRootBox.mulReLower (A B : IntRootBox) : ℤ :=
  A.re.mulLower B.re - A.im.mulUpper B.im
def IntRootBox.mulReUpper (A B : IntRootBox) : ℤ :=
  A.re.mulUpper B.re - A.im.mulLower B.im
def IntRootBox.mulImLower (A B : IntRootBox) : ℤ :=
  A.re.mulLower B.im + A.im.mulLower B.re
def IntRootBox.mulImUpper (A B : IntRootBox) : ℤ :=
  A.re.mulUpper B.im + A.im.mulUpper B.re

def IntRootBox.MulCheck (A B C : IntRootBox) (s : ℤ) : Prop :=
  C.re.lower * s ≤ A.mulReLower B ∧ A.mulReUpper B ≤ C.re.upper * s ∧
  C.im.lower * s ≤ A.mulImLower B ∧ A.mulImUpper B ≤ C.im.upper * s

instance (A B C : IntRootBox) (s : ℤ) : Decidable (A.MulCheck B C s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem IntRootBox.mul_re_lower {s : ℤ} (hs : 0 < s) (A B : IntRootBox) :
    ((A.toRat s).mul (B.toRat s)).re.lower =
      (A.mulReLower B : ℚ) / ((s : ℚ) * s) := by
  simp only [toRat, RootBox.mul, RatInterval.sub, RatInterval.add, RatInterval.neg]
  rw [IntInterval.mul_lower hs, IntInterval.mul_upper hs]
  simp only [mulReLower, Int.cast_sub, Int.cast_add, Int.cast_neg,
    sub_eq_add_neg, add_div, neg_div]

theorem IntRootBox.mul_re_upper {s : ℤ} (hs : 0 < s) (A B : IntRootBox) :
    ((A.toRat s).mul (B.toRat s)).re.upper =
      (A.mulReUpper B : ℚ) / ((s : ℚ) * s) := by
  simp only [toRat, RootBox.mul, RatInterval.sub, RatInterval.add, RatInterval.neg]
  rw [IntInterval.mul_upper hs, IntInterval.mul_lower hs]
  simp only [mulReUpper, Int.cast_sub, Int.cast_add, Int.cast_neg,
    sub_eq_add_neg, add_div, neg_div]

theorem IntRootBox.mul_im_lower {s : ℤ} (hs : 0 < s) (A B : IntRootBox) :
    ((A.toRat s).mul (B.toRat s)).im.lower =
      (A.mulImLower B : ℚ) / ((s : ℚ) * s) := by
  simp only [toRat, RootBox.mul, RatInterval.add]
  rw [IntInterval.mul_lower hs, IntInterval.mul_lower hs]
  simp only [mulImLower, Int.cast_add, add_div]

theorem IntRootBox.mul_im_upper {s : ℤ} (hs : 0 < s) (A B : IntRootBox) :
    ((A.toRat s).mul (B.toRat s)).im.upper =
      (A.mulImUpper B : ℚ) / ((s : ℚ) * s) := by
  simp only [toRat, RootBox.mul, RatInterval.add]
  rw [IntInterval.mul_upper hs, IntInterval.mul_upper hs]
  simp only [mulImUpper, Int.cast_add, add_div]

private theorem divide_grid_lower {s a b : ℤ} (hs : 0 < s) (h : a * s ≤ b) :
    (a : ℚ) / s ≤ (b : ℚ) / ((s : ℚ) * s) := by
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  apply (div_le_div_iff₀ hs' (mul_pos hs' hs')).2
  have h' : (a : ℚ) * s ≤ b := by exact_mod_cast h
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h' hs'.le

private theorem divide_grid_upper {s a b : ℤ} (hs : 0 < s) (h : a ≤ b * s) :
    (a : ℚ) / ((s : ℚ) * s) ≤ (b : ℚ) / s := by
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  apply (div_le_div_iff₀ (mul_pos hs' hs') hs').2
  have h' : (a : ℚ) ≤ b * s := by exact_mod_cast h
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h' hs'.le

/-- Integer checks are transported to exact rational enclosure inequalities.
Only the computation representation changes; the real quantity being enclosed does not. -/
theorem IntRootBox.mulCheck_sound {s : ℤ} (hs : 0 < s) {A B C : IntRootBox}
    (h : A.MulCheck B C s) : (C.toRat s).Encloses ((A.toRat s).mul (B.toRat s)) := by
  unfold RootBox.Encloses
  rw [mul_re_lower hs, mul_re_upper hs, mul_im_lower hs, mul_im_upper hs]
  exact ⟨divide_grid_lower hs h.1, divide_grid_upper hs h.2.1,
    divide_grid_lower hs h.2.2.1, divide_grid_upper hs h.2.2.2⟩

end ConsensusADMM.RefinedEndpoint.Certificate
