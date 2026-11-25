/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.NumericGram
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.RootBounds
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramSemantics
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

open ADMM.RefinedEndpoint
open ADMM.RefinedEndpoint.Data
open Period1024
open scoped RealInnerProductSpace

def gramBaseDenominator : ℤ := 1024 * (denominator : ℤ) ^ 2

theorem gramBaseDenominator_pos : 0 < gramBaseDenominator := by
  norm_num [gramBaseDenominator, denominator]

noncomputable def gramValueTerm (a b : Bool) (d : ℕ) (f : FourierFactor) : ℝ :=
  (modeMultiplicity f : ℝ) *
    ((coefficientRe a b f : ℝ) * (root ((f.mode * d) % 1024)).re +
      (coefficientIm a b f : ℝ) * (root ((f.mode * d) % 1024)).im)

/-- Each integer interval term encloses its actual real root-of-unity expression. -/
theorem gramTerm_contains (a b : Bool) (d : ℕ) (f : FourierFactor) :
    ((gramTerm a b d f).toRat grid).Contains (gramValueTerm a b d f) := by
  have hr := rootBoxes_sound ((f.mode * d) % 1024) (Nat.mod_lt _ (by decide))
  exact IntInterval.contains_scale
    (IntInterval.contains_add
      (IntInterval.contains_scale hr.1 (coefficientRe a b f))
      (IntInterval.contains_scale hr.2 (coefficientIm a b f))) (modeMultiplicity f)

theorem sum_factor_lookup (f : FourierFactor → ℝ) :
    (fourierFactors.map f).sum = ∑ h : Coordinate, f (factor h) := by
  have h := congrArg List.sum (List.ofFn_getElem_eq_map fourierFactors f)
  have hs : (fourierFactors.map f).sum =
      ∑ i : Fin fourierFactors.length, f fourierFactors[i.val] := by
    simpa only [List.sum_ofFn] using h.symm
  refine hs.trans (Fintype.sum_equiv (finCongr fourierFactors_length) _ _ ?_)
  intro i
  simp [Period1024.factor]

noncomputable def blockCoefficient (a : Bool) (h : Coordinate) : ℂ :=
  if a then multiplierCoefficient h else etaCoefficient h

noncomputable def gramFamily (a : Bool) (i : Phase) : Ambient :=
  if a then scaledMultiplier i else eta i

/-- The normalized real Fourier product and the integer numerator have exactly
the same coefficients, including the sign of the cross sine term. -/
theorem gramValueTerm_factor (a b : Bool) (i : Phase) (h : Coordinate) :
    Period1024.multiplicity h / Data.period *
      (phase h i * (blockCoefficient b h * star (blockCoefficient a h))).re =
      gramValueTerm a b i.val (factor h) / gramBaseDenominator := by
  have hp : phase h i = root ((mode h * i.val) % 1024) := by
    simpa only [ZMod.natCast_zmod_val] using phase_eq_root h i.val
  have hm : mode h = (factor h).mode := rfl
  cases a <;> cases b <;> simp only [blockCoefficient, Bool.false_eq_true, ite_false, ite_true] <;>
    rw [gram_product_re] <;>
    simp only [etaCoefficient_re, etaCoefficient_im,
      multiplierCoefficient_re, multiplierCoefficient_im] <;>
    rw [hp, hm] <;>
    by_cases hh : (factor h).mode = 512 <;>
    simp [gramValueTerm, gramBaseDenominator, coefficientRe, coefficientIm,
      modeMultiplicity, Period1024.multiplicity, Period1024.mode,
      Data.period, hh] <;> push_cast <;> ring

theorem gramFamily_inner (a b : Bool) (i j : Phase) :
    inner ℝ (gramFamily a i) (gramFamily b j) =
      (fourierFactors.map (gramValueTerm a b (j - i).val)).sum / gramBaseDenominator := by
  have hinner : inner ℝ (gramFamily a i) (gramFamily b j) =
      ∑ h, Period1024.multiplicity h / Data.period *
        (phase h (j - i) * (blockCoefficient b h * star (blockCoefficient a h))).re := by
    cases a <;> cases b <;>
      exact normalized_fourier_inner _ _ i j
  rw [hinner, sum_factor_lookup, Finset.sum_div]
  exact Finset.sum_congr rfl (fun h _ ↦ gramValueTerm_factor a b (j - i) h)

/-- The finite integer Gram computation bounds the actual geometric inner product. -/
theorem gramNumerator_contains (a b : Bool) (i j : Phase) :
    ((gramNumerator a b (j - i).val).toRat gramDenominator).Contains
      (inner ℝ (gramFamily a i) (gramFamily b j)) := by
  have hsum := IntInterval.contains_sum_map fourierFactors (gramTerm a b (j - i).val)
    (gramValueTerm a b (j - i).val) grid (fun f _ ↦ gramTerm_contains a b (j - i).val f)
  have hdiv := IntInterval.contains_divisor hsum gramBaseDenominator gramBaseDenominator_pos
  rw [← gramFamily_inner a b i j] at hdiv
  exact hdiv

end ConsensusADMM.RefinedEndpoint.Certificate
