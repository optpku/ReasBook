/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

public section

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace KernelMoment

/-- The Chapter 7 kernel moment integrand `u ↦ u^s / (1 + u^p)^j`. -/
@[expose]
def integrand (p : ℝ) (j : ℕ) (s u : ℝ) : ℝ :=
  u ^ s / (1 + u ^ p) ^ j

@[simp]
theorem integrand_def (p : ℝ) (j : ℕ) (s u : ℝ) :
    integrand p j s u = u ^ s / (1 + u ^ p) ^ j := rfl

/-- The finite positive-step quadrature sum `S_{p,j}^s(n,h)` from Proposition 7.19. -/
@[expose]
def quadratureSum (p : ℝ) (j : ℕ) (s : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  h * Finset.sum (Finset.Icc 1 n) (fun k ↦ integrand p j s ((k : ℝ) * h))

@[simp]
theorem quadratureSum_def (p : ℝ) (j : ℕ) (s : ℝ) (n : ℕ) (h : ℝ) :
    quadratureSum p j s n h =
      h * Finset.sum (Finset.Icc 1 n) (fun k ↦ integrand p j s ((k : ℝ) * h)) := rfl

/-- The infinite-step series `S_{p,j}^s(∞,h)` used in the proof of Proposition 7.19. -/
@[expose]
def quadratureSeries (p : ℝ) (j : ℕ) (s h : ℝ) : ℝ :=
  tsum (fun k : ℕ ↦ h * integrand p j s (((k + 1 : ℕ) : ℝ) * h))

@[simp]
theorem quadratureSeries_def (p : ℝ) (j : ℕ) (s h : ℝ) :
    quadratureSeries p j s h =
      tsum (fun k : ℕ ↦ h * integrand p j s (((k + 1 : ℕ) : ℝ) * h)) := rfl

/-- The improper kernel moment integral `I_{p,j}^s = ∫_0^∞ u^s / (1 + u^p)^j du`. -/
@[expose]
def integral (p : ℝ) (j : ℕ) (s : ℝ) : ℝ :=
  MeasureTheory.integral (Measure.restrict volume (Set.Ioi (0 : ℝ))) (fun u ↦ integrand p j s u)

@[simp]
theorem integral_def (p : ℝ) (j : ℕ) (s : ℝ) :
    integral p j s =
      MeasureTheory.integral (Measure.restrict volume (Set.Ioi (0 : ℝ)))
        (fun u ↦ integrand p j s u) := rfl

namespace Notation

/-- Scoped notation for the Chapter 7 quadrature sum `S_{p,j}^s(n,h)`. -/
scoped notation "S_{" p "," j "}^{" s "}(" n "," h ")" => quadratureSum p j s n h

/-- Scoped notation for the Chapter 7 infinite quadrature series `S_{p,j}^s(∞,h)`. -/
scoped notation "S_{" p "," j "}^{" s "}(∞," h ")" => quadratureSeries p j s h

/-- Scoped notation for the Chapter 7 kernel moment integral `I_{p,j}^s`. -/
scoped notation "I_{" p "," j "}^{" s "}" => integral p j s

end Notation

end KernelMoment
