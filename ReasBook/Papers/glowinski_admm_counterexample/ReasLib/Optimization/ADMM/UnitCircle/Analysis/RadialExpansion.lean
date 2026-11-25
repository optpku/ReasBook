/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.ZeroFrequency

@[expose] public section

open scoped BigOperators

namespace ADMM.UnitCircle

/-- An exact radial divided difference, continuous jointly wherever `z ≠ 0`.
The witness is constructed algebraically below for the actual supply symbol;
continuity of an unspecified remainder is not assumed as a convergence input. -/
structure RadialExpansion (f : ℝ → ℂ → ℂ) where
  remainder : ℝ → ℂ → ℂ
  identity : ∀ α z, f α z = f 1 z + ((1 - α : ℝ) : ℂ) * remainder α z
  continuous_value : ∀ p : ℝ × ℂ, p.2 ≠ 0 →
    ContinuousAt (fun q : ℝ × ℂ ↦ f q.1 q.2) p
  continuous_remainder : ∀ p : ℝ × ℂ, p.2 ≠ 0 →
    ContinuousAt (fun q : ℝ × ℂ ↦ remainder q.1 q.2) p

namespace RadialExpansion

variable {f g : ℝ → ℂ → ℂ}

theorem continuous_base (F : RadialExpansion f) (p : ℝ × ℂ) (hp : p.2 ≠ 0) :
    ContinuousAt (fun q : ℝ × ℂ ↦ f 1 q.2) p :=
  (F.continuous_value (1, p.2) hp).comp (x := p)
    (f := fun q : ℝ × ℂ ↦ ((1 : ℝ), q.2))
    (continuousAt_const.prodMk continuousAt_snd)

noncomputable def constant (g : ℂ → ℂ)
    (hg : ∀ z : ℂ, z ≠ 0 → ContinuousAt g z) :
    RadialExpansion (fun _ z ↦ g z) where
  remainder _ _ := 0
  identity _ _ := by simp
  continuous_value p hp := (hg p.2 hp).comp
    (f := fun q : ℝ × ℂ ↦ q.2) (x := p) continuousAt_snd
  continuous_remainder _ _ := continuousAt_const

noncomputable def discount : RadialExpansion (fun α _ ↦ (α : ℂ)) where
  remainder _ _ := -1
  identity α _ := by push_cast; ring
  continuous_value p _ := Complex.continuous_ofReal.continuousAt.comp
    (f := fun q : ℝ × ℂ ↦ q.1) (x := p) continuousAt_fst
  continuous_remainder _ _ := continuousAt_const

noncomputable def add (F : RadialExpansion f) (G : RadialExpansion g) :
    RadialExpansion (fun α z ↦ f α z + g α z) where
  remainder α z := F.remainder α z + G.remainder α z
  identity α z := by rw [F.identity α z, G.identity α z]; ring
  continuous_value p hp := (F.continuous_value p hp).add (G.continuous_value p hp)
  continuous_remainder p hp := (F.continuous_remainder p hp).add (G.continuous_remainder p hp)

noncomputable def neg (F : RadialExpansion f) :
    RadialExpansion (fun α z ↦ -f α z) where
  remainder α z := -F.remainder α z
  identity α z := by rw [F.identity α z]; ring
  continuous_value p hp := (F.continuous_value p hp).neg
  continuous_remainder p hp := (F.continuous_remainder p hp).neg

noncomputable def sub (F : RadialExpansion f) (G : RadialExpansion g) :
    RadialExpansion (fun α z ↦ f α z - g α z) := by
  simpa only [sub_eq_add_neg] using F.add G.neg

noncomputable def mul (F : RadialExpansion f) (G : RadialExpansion g) :
    RadialExpansion (fun α z ↦ f α z * g α z) where
  remainder α z := F.remainder α z * g α z + f 1 z * G.remainder α z
  identity α z := by rw [F.identity α z, G.identity α z]; ring
  continuous_value p hp := (F.continuous_value p hp).mul (G.continuous_value p hp)
  continuous_remainder p hp := ((F.continuous_remainder p hp).mul
    (G.continuous_value p hp)).add
    ((F.continuous_base p hp).mul (G.continuous_remainder p hp))

noncomputable def star (F : RadialExpansion f) :
    RadialExpansion (fun α z ↦ star (f α z)) where
  remainder α z := Star.star (F.remainder α z)
  identity α z := by
    conv_lhs => rw [F.identity α z]
    simp
  continuous_value p hp := (F.continuous_value p hp).star
  continuous_remainder p hp := (F.continuous_remainder p hp).star

noncomputable def pow (F : RadialExpansion f) (n : ℕ) :
    RadialExpansion (fun α z ↦ f α z ^ n) := by
  induction n with
  | zero => simpa using constant (fun _ ↦ (1 : ℂ)) (fun _ _ ↦ continuousAt_const)
  | succ n ih => simpa only [pow_succ] using ih.mul F

theorem continuousAt_sum {ι : Type*} (s : Finset ι)
    (f : ι → (ℝ × ℂ) → ℂ) (p : ℝ × ℂ)
    (hf : ∀ i ∈ s, ContinuousAt (f i) p) :
    ContinuousAt (fun q ↦ ∑ i ∈ s, f i q) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ × ℂ ↦ (0 : ℂ)) p)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

noncomputable def sum {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ → ℂ)
    (F : ∀ i, RadialExpansion (f i)) :
    RadialExpansion (fun α z ↦ ∑ i, f i α z) where
  remainder α z := ∑ i, (F i).remainder α z
  identity α z := by
    simp_rw [(F _).identity α z]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  continuous_value p hp := continuousAt_sum Finset.univ _ p
    (fun i _ ↦ (F i).continuous_value p hp)
  continuous_remainder p hp := continuousAt_sum Finset.univ _ p
    (fun i _ ↦ (F i).continuous_remainder p hp)

end RadialExpansion

noncomputable def radialConstant (a : ℂ) :
    RadialExpansion (fun _ _ ↦ a) :=
  RadialExpansion.constant _ (fun _ _ ↦ continuousAt_const)

noncomputable def radialInverse : RadialExpansion (fun _ z ↦ z⁻¹) :=
  RadialExpansion.constant _ (fun _ hz ↦ continuousAt_inv₀ hz)

noncomputable def delaySymbol_radialExpansion :
    RadialExpansion delaySymbol := by
  exact (radialConstant 1).sub (RadialExpansion.discount.mul radialInverse)

noncomputable def multiplierSymbol_radialExpansion (γ : ℝ) :
    RadialExpansion (fun α z ↦ multiplierSymbol α γ z) := by
  exact (radialConstant 1).add
    (((radialConstant ((γ : ℂ) - 1)).mul RadialExpansion.discount).mul radialInverse)

noncomputable def pointRow_radialExpansion (b i : Fin 2) :
    RadialExpansion (fun α z ↦ pointRow α z b i) := by
  by_cases hi : i = 0
  · simpa only [pointRow, hi, if_true] using radialConstant 1
  · by_cases hb : b = 0
    · simpa only [pointRow, hi, hb, if_false, if_true] using delaySymbol_radialExpansion
    · simpa only [pointRow, hi, hb, if_false] using radialConstant 0

noncomputable def normalRow_radialExpansion (γ : ℝ) (b i : Fin 2) :
    RadialExpansion (fun α z ↦ normalRow α γ z b i) := by
  by_cases hb : b = 0
  · by_cases hi : i = 0
    · simpa only [normalRow, hi, hb, if_true] using delaySymbol_radialExpansion.neg
    · simpa only [normalRow, hi, hb, if_false, if_true] using
        (multiplierSymbol_radialExpansion γ).neg
  · by_cases hi : i = 0
    · simpa only [normalRow, hi, hb, if_false, if_true] using radialConstant 0
    · simpa only [normalRow, hi, hb, if_false] using multiplierSymbol_radialExpansion γ

noncomputable def lagMultiplier_radialExpansion {ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2) :
    RadialExpansion (fun α z ↦ lagMultiplier c α z b) := by
  let A := RadialExpansion.discount
  let Z := radialInverse
  let T (i : Fin ℓ) :=
    ((radialConstant (c.backward b i)).mul
      ((radialConstant 1).sub ((A.pow (i.val + 1)).mul (Z.pow (i.val + 1))))).add
    ((radialConstant (c.forward b i)).mul
      ((A.pow (2 * (i.val + 1))).sub
        ((A.pow (i.val + 1)).mul
          ((RadialExpansion.constant (fun z : ℂ ↦ z)
            (fun _ _ ↦ continuousAt_id)).pow (i.val + 1)))))
  exact (radialConstant c.omega).add (RadialExpansion.sum _ T)

noncomputable def rawSupplySymbol_radialExpansion {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ)
    (i j : Fin 2) : RadialExpansion (fun α z ↦ rawSupplySymbol c α γ z i j) := by
  exact RadialExpansion.sum _ (fun b : Fin 2 ↦
    (((normalRow_radialExpansion γ b i).star).mul
      (lagMultiplier_radialExpansion c b)).mul (pointRow_radialExpansion b j))

/-- The actual supply admits an exact jointly continuous radial remainder.
All polynomial operations are expanded constructively; no extra regularity
condition is inserted into the convergence theorem. -/
noncomputable def supplySymbol_radialExpansion {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ)
    (i j : Fin 2) : RadialExpansion (fun α z ↦ supplySymbol c α γ z i j) := by
  let A := rawSupplySymbol_radialExpansion c γ i j
  let B := rawSupplySymbol_radialExpansion c γ j i
  let D := delaySymbol_radialExpansion
  let H := ((radialConstant (1 / 2)).mul (A.add B.star)).neg
  let E := (((radialConstant c.epsilon).mul (D.star.mul D)).mul
    (radialConstant (residualCoordinateMatrix i j)))
  convert! H.sub E using 1
  ext α z
  simp [supplySymbol, hermitianPart, Matrix.conjTranspose_apply,
    Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  ring

end ADMM.UnitCircle
