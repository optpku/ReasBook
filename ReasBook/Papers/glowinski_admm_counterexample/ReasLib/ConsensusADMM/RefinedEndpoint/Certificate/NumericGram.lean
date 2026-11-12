/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.RootData
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.IntegerArithmetic
public import glowinski_admm_counterexample.ReasLib.ADMM.RefinedEndpoint.DataChecks
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.RefinedConstants

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

open ADMM.RefinedEndpoint.Data

/-- Integer numerator of the cosine coefficient for one Gram entry.
`false` selects eta, `true` selects the scaled multiplier. -/
def coefficientRe (a b : Bool) (f : FourierFactor) : ℤ :=
  if a then
    if b then f.wRe ^ 2 + f.wIm ^ 2 else f.etaRe * f.wRe + f.etaIm * f.wIm
  else if b then f.etaRe * f.wRe + f.etaIm * f.wIm
  else f.etaRe ^ 2 + f.etaIm ^ 2

/-- Integer sine coefficient; swapping the two blocks conjugates it. -/
def coefficientIm (a b : Bool) (f : FourierFactor) : ℤ :=
  if a = b then 0
  else if a then -(f.etaIm * f.wRe - f.etaRe * f.wIm)
  else f.etaIm * f.wRe - f.etaRe * f.wIm

def modeMultiplicity (f : FourierFactor) : ℤ := if f.mode = 512 then 1 else 2

/-- One exact integer interval contribution on the shared denominator. -/
def gramTerm (a b : Bool) (d : ℕ) (f : FourierFactor) : IntInterval :=
  let R := rawRootBox ((f.mode * d) % 1024)
  IntInterval.scale (modeMultiplicity f)
    ((IntInterval.scale (coefficientRe a b f) R.re).add
      (IntInterval.scale (coefficientIm a b f) R.im))

/-- An entirely integer interpretation of a circulant Gram row. -/
def gramNumerator (a b : Bool) (d : ℕ) : IntInterval :=
  IntInterval.sum (fourierFactors.map (gramTerm a b d))

def gramDenominator : ℤ := 1024 * (denominator : ℤ) ^ 2 * grid

theorem gramDenominator_pos : 0 < gramDenominator := by
  norm_num [gramDenominator, denominator, grid]

/-- Vertex indices 0..1023 denote eta; 1024..2047 denote scaled multipliers. -/
def gramEntryNumerator (i j : ℕ) : IntInterval :=
  gramNumerator (decide (1024 ≤ i)) (decide (1024 ≤ j))
    ((j % 1024 + 1024 - i % 1024) % 1024)

abbrev SparseVector := List (ℕ × ℤ)

/-- Sparse bilinear pairing with the same positive Gram denominator. -/
def pairNumerator (A B : SparseVector) : IntInterval :=
  IntInterval.sum (A.map fun a ↦ IntInterval.sum (B.map fun b ↦
    IntInterval.scale (a.2 * b.2) (gramEntryNumerator a.1 b.1)))

def upperNumerator : ℤ := 47172066094067
def upperDenominator : ℤ := 25000000000000

theorem upperDenominator_pos : 0 < upperDenominator := by decide

theorem upper_quotient : ADMM.RefinedEndpoint.upper =
    (upperNumerator : ℝ) / (upperDenominator : ℝ) := by
  norm_num [ADMM.RefinedEndpoint.upper, upperNumerator, upperDenominator]

/-- The actual first normal at phase zero, multiplied by the positive test denominator. -/
def firstNormalNumerator : SparseVector :=
  [(1023, upperDenominator), (0, -upperDenominator),
    (1024, -upperDenominator), (2047, upperDenominator - upperNumerator)]

/-- The corresponding second normal, with the same scaling. -/
def secondNormalNumerator : SparseVector :=
  [(1024, upperDenominator), (2047, upperNumerator - upperDenominator)]

/-- Code zero is the origin comparison; all other codes are nonself phases. -/
def firstTarget (j : ℕ) : SparseVector :=
  if j = 0 then [(0, 1), (1024, 1), (2047, -1)]
  else [(0, 1), (1024, 1), (2047, -1),
    (j, -1), (1024 + j, -1), (1024 + (j - 1), 1)]

def secondTarget (j : ℕ) : SparseVector :=
  if j = 0 then [(0, 1)] else [(0, 1), (j, -1)]

def residualVector : SparseVector := [(1024, 1), (2047, -1)]

def firstSupportNumerator (j : ℕ) : IntInterval :=
  pairNumerator firstNormalNumerator (firstTarget j)

def secondSupportNumerator (j : ℕ) : IntInterval :=
  pairNumerator secondNormalNumerator (secondTarget j)

def residualNormNumerator : IntInterval := pairNumerator residualVector residualVector

end ConsensusADMM.RefinedEndpoint.Certificate
