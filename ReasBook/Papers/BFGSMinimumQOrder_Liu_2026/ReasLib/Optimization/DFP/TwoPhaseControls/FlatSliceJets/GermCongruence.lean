module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison

public section

noncomputable section

open Filter
open scoped Topology
open Asymptotics

namespace DFP.TwoLeg

/-- Two real germs agree through order `n - 1` at the origin. -/
def EqModPow (n : ℕ) (f g : ℝ → ℝ) : Prop :=
  (fun ε => f ε - g ε) =O[𝓝 0] (fun ε => ε ^ n)

/-- Expose the asymptotic characterization of a finite-order germ congruence. -/
theorem EqModPow.of_isBigO {n : ℕ} {f g : ℝ → ℝ}
    (h : (fun ε => f ε - g ε) =O[𝓝 0] (fun ε => ε ^ n)) :
    EqModPow n f g := by
  exact h

/-- Recover the asymptotic characterization of a finite-order germ congruence. -/
theorem EqModPow.to_isBigO {n : ℕ} {f g : ℝ → ℝ}
    (h : EqModPow n f g) :
    (fun ε => f ε - g ε) =O[𝓝 0] (fun ε => ε ^ n) := by
  exact h

namespace EqModPow

/-- Transport a germ congruence across pointwise equal representatives. -/
theorem congr {n : ℕ} {f g f' g' : ℝ → ℝ}
    (h : EqModPow n f g) (hf : ∀ ε, f' ε = f ε) (hg : ∀ ε, g' ε = g ε) :
    EqModPow n f' g' := by
  unfold EqModPow at h ⊢
  refine h.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  have hpoint : ∀ ε, f ε - g ε = f' ε - g' ε := by
    intro ε
    rw [hf ε, hg ε]
  exact Filter.Eventually.of_forall hpoint

theorem refl (n : ℕ) (f : ℝ → ℝ) : EqModPow n f f := by
  simpa [EqModPow] using
    (isBigO_zero (fun ε : ℝ => ε ^ n) (𝓝 0))

theorem symm {n : ℕ} {f g : ℝ → ℝ} (h : EqModPow n f g) :
    EqModPow n g f := by
  unfold EqModPow at h ⊢
  refine h.neg_left.congr' ?_ (Eventually.of_forall fun _ => rfl)
  have hneg : ∀ ε, -(f ε - g ε) = g ε - f ε := by
    intro ε
    ring
  exact Eventually.of_forall hneg

theorem trans {n : ℕ} {f g k : ℝ → ℝ}
    (hfg : EqModPow n f g) (hgk : EqModPow n g k) :
    EqModPow n f k := by
  unfold EqModPow at hfg hgk ⊢
  refine (hfg.add hgk).congr' ?_ (Eventually.of_forall fun _ => rfl)
  have htrans : ∀ ε, (f ε - g ε) + (g ε - k ε) = f ε - k ε := by
    intro ε
    ring
  exact Eventually.of_forall htrans

theorem neg {n : ℕ} {f g : ℝ → ℝ} (h : EqModPow n f g) :
    EqModPow n (fun ε => -f ε) (fun ε => -g ε) := by
  unfold EqModPow at h ⊢
  refine h.neg_left.congr' ?_ (Eventually.of_forall fun _ => rfl)
  have hneg : ∀ ε, -(f ε - g ε) = (-f ε) - (-g ε) := by
    intro ε
    ring
  exact Eventually.of_forall hneg

theorem add {n : ℕ} {f g k l : ℝ → ℝ}
    (hfg : EqModPow n f g) (hkl : EqModPow n k l) :
    EqModPow n (fun ε => f ε + k ε) (fun ε => g ε + l ε) := by
  unfold EqModPow at hfg hkl ⊢
  refine (hfg.add hkl).congr' ?_ (Eventually.of_forall fun _ => rfl)
  have hadd : ∀ ε, (f ε - g ε) + (k ε - l ε) = (f ε + k ε) - (g ε + l ε) := by
    intro ε
    ring
  exact Eventually.of_forall hadd

theorem sub {n : ℕ} {f g k l : ℝ → ℝ}
    (hfg : EqModPow n f g) (hkl : EqModPow n k l) :
    EqModPow n (fun ε => f ε - k ε) (fun ε => g ε - l ε) := by
  unfold EqModPow at hfg hkl ⊢
  refine (hfg.sub hkl).congr' ?_ (Eventually.of_forall fun _ => rfl)
  have hsub : ∀ ε, (f ε - g ε) - (k ε - l ε) = (f ε - k ε) - (g ε - l ε) := by
    intro ε
    ring
  exact Eventually.of_forall hsub

/-- Multiplication by the same power of the germ parameter raises the comparison order. -/
theorem mul_pow_left {n k : ℕ} {f g : ℝ → ℝ}
    (hfg : EqModPow n f g) :
    EqModPow (n + k) (fun ε => ε ^ k * f ε) (fun ε => ε ^ k * g ε) := by
  have hproduct :=
    (Asymptotics.isBigO_refl (fun ε : ℝ => ε ^ k) (𝓝 0)).mul
      (EqModPow.to_isBigO hfg)
  have hleft (ε : ℝ) :
      ε ^ k * (f ε - g ε) = ε ^ k * f ε - ε ^ k * g ε := by
    ring
  have hproduct' := hproduct.congr_left hleft
  apply EqModPow.of_isBigO
  simpa only [← pow_add, Nat.add_comm] using hproduct'

/-- Scalar multiplication preserves a finite-order germ comparison. -/
theorem const_mul_left {n : ℕ} {f g : ℝ → ℝ}
    (c : ℝ) (hfg : EqModPow n f g) :
    EqModPow n (fun ε => c * f ε) (fun ε => c * g ε) := by
  have hscaled := (EqModPow.to_isBigO hfg).const_mul_left c
  have hidentity (ε : ℝ) :
      c * (f ε - g ε) = c * f ε - c * g ε := by
    ring
  exact EqModPow.of_isBigO (hscaled.congr_left hidentity)

/-- A germ comparison at a higher order also holds at every lower order. -/
theorem mono {n m : ℕ} {f g : ℝ → ℝ}
    (hfg : EqModPow m f g) (hnm : n ≤ m) : EqModPow n f g := by
  obtain rfl | hlt := hnm.eq_or_lt
  · exact hfg
  · apply EqModPow.of_isBigO
    exact (EqModPow.to_isBigO hfg).trans
      (Asymptotics.isLittleO_pow_pow hlt).isBigO

/-- A positive-order germ comparison forces equality of the values at the origin. -/
theorem eq_at_zero_of_pos {n : ℕ} {f g : ℝ → ℝ}
    (hn : 0 < n) (hfg : EqModPow n f g) : f 0 = g 0 := by
  have hzeroRule := mem_of_mem_nhds (EqModPow.to_isBigO hfg).eq_zero_imp
  have hzeroPower : (0 : ℝ) ^ n = 0 := zero_pow (Nat.ne_of_gt hn)
  exact sub_eq_zero.mp (hzeroRule hzeroPower)

theorem of_factor {n : ℕ} {f g q : ℝ → ℝ}
    (hq : ContinuousAt q 0)
    (hfactor : ∀ ε, f ε - g ε = q ε * ε ^ n) :
    EqModPow n f g := by
  have hO : (fun ε : ℝ => q ε * ε ^ n) =O[𝓝 0] (fun ε => ε ^ n) := by
    simpa using hq.isBigO.mul (isBigO_refl (fun ε : ℝ => ε ^ n) (𝓝 0))
  unfold EqModPow
  exact hO.congr' (Eventually.of_forall fun ε => (hfactor ε).symm)
    (Eventually.of_forall fun _ => rfl)

theorem mul {n : ℕ} {f g k l : ℝ → ℝ}
    (hfg : EqModPow n f g) (hkl : EqModPow n k l)
    (hg : ContinuousAt g 0) (hk : ContinuousAt k 0) :
    EqModPow n (fun ε => f ε * k ε) (fun ε => g ε * l ε) := by
  unfold EqModPow at hfg hkl ⊢
  have hleft :
      (fun ε => (f ε - g ε) * k ε) =O[𝓝 0] (fun ε : ℝ => ε ^ n) := by
    simpa using hfg.mul hk.isBigO
  have hright :
      (fun ε => g ε * (k ε - l ε)) =O[𝓝 0] (fun ε : ℝ => ε ^ n) := by
    simpa using hg.isBigO.mul hkl
  refine (hleft.add hright).congr' ?_ (Eventually.of_forall fun _ => rfl)
  have hmul : ∀ ε, (f ε - g ε) * k ε + g ε * (k ε - l ε) = f ε * k ε - g ε * l ε := by
    intro ε
    ring
  exact Eventually.of_forall hmul

/-- Verify a proposed reciprocal by checking that its product is one modulo `ε^n`. -/
theorem inv_of_mul_eq_one {n : ℕ} {f g : ℝ → ℝ}
    (h : EqModPow n (fun ε => f ε * g ε) (fun _ => 1))
    (hf : ContinuousAt f 0) (hf0 : f 0 ≠ 0) :
    EqModPow n (fun ε => (f ε)⁻¹) g := by
  unfold EqModPow at h ⊢
  have hneg :
      (fun ε => 1 - f ε * g ε) =O[𝓝 0] (fun ε : ℝ => ε ^ n) := by
    refine h.neg_left.congr' ?_ (Eventually.of_forall fun _ => rfl)
    have hneg : ∀ ε, -(f ε * g ε - 1) = 1 - f ε * g ε := by
      intro ε
      ring
    exact Eventually.of_forall hneg
  have hO :
      (fun ε => (f ε)⁻¹ * (1 - f ε * g ε)) =O[𝓝 0]
        (fun ε : ℝ => ε ^ n) := by
    simpa using (hf.inv₀ hf0).isBigO.mul hneg
  refine hO.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hf.eventually_ne hf0] with ε hε
  field_simp [hε]

/-- Verify a proposed quotient by checking `numerator = denominator * candidate`
modulo `ε^n`. -/
theorem div_of_eq_mul {n : ℕ} {num den q : ℝ → ℝ}
    (h : EqModPow n num (fun ε => den ε * q ε))
    (hden : ContinuousAt den 0) (hden0 : den 0 ≠ 0) :
    EqModPow n (fun ε => num ε / den ε) q := by
  unfold EqModPow at h ⊢
  have hO :
      (fun ε => (den ε)⁻¹ * (num ε - den ε * q ε)) =O[𝓝 0]
        (fun ε : ℝ => ε ^ n) := by
    simpa using (hden.inv₀ hden0).isBigO.mul h
  refine hO.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hden.eventually_ne hden0] with ε hε
  field_simp [hε]


/-- Verify a proposed positive square root by squaring it modulo `ε^n`. -/
theorem sqrt_of_sq {n : ℕ} {f g : ℝ → ℝ}
    (h : EqModPow n f (fun ε => g ε ^ 2))
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (hf0 : 0 < f 0) (hg0 : 0 < g 0) :
    EqModPow n (fun ε => Real.sqrt (f ε)) g := by
  unfold EqModPow at h ⊢
  let d : ℝ → ℝ := fun ε => Real.sqrt (f ε) + g ε
  have hd : ContinuousAt d 0 := hf.sqrt.add hg
  have hd0 : d 0 ≠ 0 := by
    dsimp [d]
    positivity
  have hO :
      (fun ε => (f ε - g ε ^ 2) * (d ε)⁻¹) =O[𝓝 0]
        (fun ε : ℝ => ε ^ n) := by
    simpa using h.mul (hd.inv₀ hd0).isBigO
  refine hO.congr' ?_ (Eventually.of_forall fun _ => rfl)
  have hf_nonneg : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 ≤ f ε := by
    have hpos : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < f ε :=
      continuousAt_const.eventually_lt hf hf0
    exact hpos.mono (fun _ hε => hε.le)
  filter_upwards [hf_nonneg, hd.eventually_ne hd0] with ε hfε hdε
  have hsqrt : Real.sqrt (f ε) ^ 2 = f ε := Real.sq_sqrt hfε
  dsimp [d] at hdε ⊢
  field_simp [hdε]
  nlinarith

end EqModPow

end DFP.TwoLeg
