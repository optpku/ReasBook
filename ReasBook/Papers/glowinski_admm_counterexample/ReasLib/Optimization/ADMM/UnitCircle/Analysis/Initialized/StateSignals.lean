/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.WeightedSignals
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.LagOperatorBridge
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.Separation

@[expose] public section

namespace ADMM.UnitCircle.Initialized

open Supply Fourier

noncomputable section

/-- The real residual obtained by extending the actual state by zero before its first term. -/
def auxResidual {m : ℕ} (w : ℕ → Fin m → ℝ) : ℕ → Fin m → ℝ :=
  w - zeroDelay w 1

def auxPoint {m : ℕ} (η w : ℕ → Fin m → ℝ) (b : Fin 2) : ℕ → Fin m → ℝ :=
  if b = 0 then η + auxResidual w else η

def auxMultiplier {m : ℕ} (γ : ℝ) (w : ℕ → Fin m → ℝ) : ℕ → Fin m → ℝ :=
  w + (γ - 1) • zeroDelay w 1

def auxNormal {m : ℕ} (γ : ℝ) (η w : ℕ → Fin m → ℝ) (b : Fin 2) : ℕ → Fin m → ℝ :=
  if b = 0 then -(η - zeroDelay η 1) - auxMultiplier γ w else auxMultiplier γ w

theorem auxResidual_summable {m : ℕ} {α : ℝ} {w : ℕ → Fin m → ℝ}
    (hw : SquareSummable α w) : SquareSummable α (auxResidual w) :=
  hw.sub (hw.zeroDelay 1)

theorem auxPoint_summable {m : ℕ} {α : ℝ} {η w : ℕ → Fin m → ℝ}
    (hη : SquareSummable α η) (hw : SquareSummable α w) (b : Fin 2) :
    SquareSummable α (auxPoint η w b) := by
  by_cases hb : b = 0
  · simpa only [auxPoint, if_pos hb] using hη.add (auxResidual_summable hw)
  · simpa only [auxPoint, if_neg hb] using hη

theorem auxMultiplier_summable {m : ℕ} {α : ℝ} {w : ℕ → Fin m → ℝ}
    (hw : SquareSummable α w) (γ : ℝ) : SquareSummable α (auxMultiplier γ w) :=
  hw.add ((hw.zeroDelay 1).smul (γ - 1))

theorem auxNormal_summable {m : ℕ} {α : ℝ} {η w : ℕ → Fin m → ℝ}
    (hη : SquareSummable α η) (hw : SquareSummable α w) (γ : ℝ) (b : Fin 2) :
    SquareSummable α (auxNormal γ η w b) := by
  by_cases hb : b = 0
  · simpa only [auxNormal, if_pos hb] using
      (hη.sub (hη.zeroDelay 1)).neg.sub (auxMultiplier_summable hw γ)
  · simpa only [auxNormal, if_neg hb] using auxMultiplier_summable hw γ

theorem complexLp_neg {m : ℕ} (α : ℝ) (x : ℕ → Fin m → ℝ)
    (hx : SquareSummable α x) (a : Fin m) :
    complexLp α (-x) hx.neg a = -complexLp α x hx a := by
  have h := complexLp_smul α (-1) x hx a
  simpa only [neg_one_smul, Complex.ofReal_neg, Complex.ofReal_one] using h

theorem complexLp_auxMultiplier {m : ℕ} (α γ : ℝ) (w : ℕ → Fin m → ℝ)
    (hw : SquareSummable α w) (a : Fin m) :
    complexLp α (auxMultiplier γ w) (auxMultiplier_summable hw γ) a =
      multiplierNormal α γ (complexLp α w hw a) := by
  change complexLp α (w + (γ - 1) • zeroDelay w 1)
    (hw.add ((hw.zeroDelay 1).smul (γ - 1))) a = _
  rw [complexLp_add α w ((γ - 1) • zeroDelay w 1) hw ((hw.zeroDelay 1).smul (γ - 1)) a,
    complexLp_smul α (γ - 1) (zeroDelay w 1) (hw.zeroDelay 1) a,
    complexLp_zeroDelay α w hw 1 a]
  simp only [pow_one, smul_smul, multiplierNormal, Complex.ofReal_mul, Int.natCast_one]

def stateCoordinates {m : ℕ} (α : ℝ) (η w : ℕ → Fin m → ℝ)
    (hη : SquareSummable α η) (hw : SquareSummable α w) (a : Fin m) : Fin 2 → TimeSequence :=
  fun b ↦ if b = 0 then complexLp α η hη a else complexLp α w hw a

theorem complexLp_auxPoint {m : ℕ} (α : ℝ) (η w : ℕ → Fin m → ℝ)
    (hη : SquareSummable α η) (hw : SquareSummable α w) (b : Fin 2) (a : Fin m) :
    complexLp α (auxPoint η w b) (auxPoint_summable hη hw b) a =
      pointSignal α (stateCoordinates α η w hη hw a) b := by
  by_cases hb : b = 0
  · subst b
    change complexLp α (η + (w - zeroDelay w 1))
      (hη.add (hw.sub (hw.zeroDelay 1))) a = _
    rw [complexLp_add α η (w - zeroDelay w 1) hη (hw.sub (hw.zeroDelay 1)) a,
      complexLp_difference α w hw a]
    simp only [pointSignal, stateCoordinates, if_true, one_ne_zero, if_false]
  · simp only [auxPoint, if_neg hb, pointSignal, stateCoordinates, ite_true]

theorem complexLp_auxNormal {m : ℕ} (α γ : ℝ) (η w : ℕ → Fin m → ℝ)
    (hη : SquareSummable α η) (hw : SquareSummable α w) (b : Fin 2) (a : Fin m) :
    complexLp α (auxNormal γ η w b) (auxNormal_summable hη hw γ b) a =
      normalSignal α γ (stateCoordinates α η w hη hw a) b := by
  by_cases hb : b = 0
  · subst b
    change complexLp α (-(η - zeroDelay η 1) - auxMultiplier γ w)
      ((hη.sub (hη.zeroDelay 1)).neg.sub (auxMultiplier_summable hw γ)) a = _
    rw [complexLp_sub α (-(η - zeroDelay η 1)) (auxMultiplier γ w)
      (hη.sub (hη.zeroDelay 1)).neg (auxMultiplier_summable hw γ) a,
      complexLp_neg α (η - zeroDelay η 1) (hη.sub (hη.zeroDelay 1)) a,
      complexLp_difference α η hη a, complexLp_auxMultiplier α γ w hw a]
    simp only [normalSignal, stateCoordinates, if_true, one_ne_zero, if_false]
  · simp only [auxNormal, if_neg hb, normalSignal, stateCoordinates, one_ne_zero, if_false]
    exact complexLp_auxMultiplier α γ w hw a

end

end ADMM.UnitCircle.Initialized
