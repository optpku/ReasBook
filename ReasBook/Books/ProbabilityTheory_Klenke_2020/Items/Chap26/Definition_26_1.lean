/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

/-- Continuous `ℝ^d`-valued paths on `[0, ∞)`, modeled as `ContinuousMap NNReal (Fin d → ℝ)`. -/
abbrev EuclideanPathSpace (d : ℕ) := ContinuousMap NNReal (Fin d → ℝ)

/-- The Borel measurable structure on the continuous `ℝ^d`-path space. -/
instance euclideanPathSpaceMeasurableSpace (d : ℕ) :
    MeasurableSpace (EuclideanPathSpace d) :=
  borel (EuclideanPathSpace d)

/-- The continuous `ℝ^d`-path space carries its Borel measurable structure. -/
instance euclideanPathSpaceBorelSpace (d : ℕ) : BorelSpace (EuclideanPathSpace d) :=
  ⟨rfl⟩

/-- A pathwise strong-solution operator sends an initial state and a driving path to a continuous
solution path, with the nonanticipative measurability from Definition 26.1. -/
structure StrongSolutionOperator (n m : ℕ) where
  toFun (x : Fin n → ℝ) (w : EuclideanPathSpace m) : EuclideanPathSpace n
  measurable_up_to (t : NNReal) :
    Measurable[
      MeasurableSpace.prod inferInstance
        (generatedFiltrationSpace (fun s (ω : EuclideanPathSpace m) ↦ ω s) t),
      generatedFiltrationSpace (fun s (ω : EuclideanPathSpace n) ↦ ω s) t] fun xw :
        (Fin n → ℝ) × EuclideanPathSpace m ↦
        toFun xw.1 xw.2

attribute [coe] StrongSolutionOperator.toFun

/-- A strong-solution operator can be used as a function of the initial value and the driving
path. -/
instance strongSolutionOperatorCoeFun (n m : ℕ) :
    CoeFun (StrongSolutionOperator n m)
      (fun _ ↦ (Fin n → ℝ) → EuclideanPathSpace m → EuclideanPathSpace n) :=
  ⟨StrongSolutionOperator.toFun⟩

/-- Realizing a strong-solution operator on an initial state and a continuous driving path yields
the corresponding continuous state-path random variable. -/
abbrev StrongSolutionOperator.realization (F : StrongSolutionOperator n m)
    {Ω : Type u} (ξ : Ω → Fin n → ℝ) (W : Ω → EuclideanPathSpace m) :
    Ω → EuclideanPathSpace n :=
  fun ω ↦ F (ξ ω) (W ω)

namespace CoordinateProcess

/-- View a coordinate-valued process as an `EuclideanSpace`-valued process through the canonical
equivalence `EuclideanSpace ℝ (Fin d) ≃ Fin d → ℝ`. -/
abbrev toEuclidean {Ω : Type u} {d : ℕ} (W : NNReal → Ω → Fin d → ℝ) :
    NNReal → Ω → EuclideanSpace ℝ (Fin d) :=
  fun t ω ↦ (EuclideanSpace.equiv (Fin d) ℝ).symm (W t ω)

/-- Evaluating `CoordinateProcess.toEuclidean W` applies the canonical inverse coordinate
equivalence to `W t ω`. -/
theorem toEuclidean_apply {Ω : Type u} {d : ℕ} (W : NNReal → Ω → Fin d → ℝ)
    (t : NNReal) (ω : Ω) :
    toEuclidean W t ω = (EuclideanSpace.equiv (Fin d) ℝ).symm (W t ω) :=
  rfl

end CoordinateProcess

/-- Definition 26.1: a strong solution of an `n`-dimensional SDE driven by an `m`-dimensional
continuous noise path consists of a pathwise solver map `F` such that, for every horizon `t`, the
map `(x, w) ↦ F (x, w)` is measurable from `B(ℝ^n) ⊗ 𝒢_t^m` to `𝒢_t^n`, and the realized process
`X = F (ξ, W)` satisfies the ambient SDE relation. -/
def StrongSolution {Ω : Type u} [MeasurableSpace Ω] (n m : ℕ)
    (SolvesSDE : (Ω → Fin n → ℝ) → (Ω → EuclideanPathSpace m) →
      (Ω → EuclideanPathSpace n) → Prop)
    (ξ : Ω → Fin n → ℝ) (W : Ω → EuclideanPathSpace m) (X : Ω → EuclideanPathSpace n) : Prop :=
  ∃ F : StrongSolutionOperator n m,
    (X = fun ω ↦ F (ξ ω) (W ω)) ∧
      SolvesSDE ξ W X

-- Proof sketch: unfold `StrongSolution`; the operator witness already packages the prefix
-- measurability, so the remaining data are exactly the realization identity `X = F(ξ, W)` and the
-- ambient SDE-solution statement.
/-- Definition 26.1, unfolded: `X` is a strong solution exactly when there is a pathwise
strong-solution operator `F` whose realization is `X` and for which `X` satisfies the ambient SDE
relation. -/
theorem strongSolution_iff_exists_solver
    {Ω : Type u} [MeasurableSpace Ω] {n m : ℕ}
    {SolvesSDE : (Ω → Fin n → ℝ) → (Ω → EuclideanPathSpace m) →
      (Ω → EuclideanPathSpace n) → Prop}
    {ξ : Ω → Fin n → ℝ} {W : Ω → EuclideanPathSpace m} {X : Ω → EuclideanPathSpace n} :
    StrongSolution n m SolvesSDE ξ W X ↔
      ∃ F : StrongSolutionOperator n m,
        (X = fun ω ↦ F (ξ ω) (W ω)) ∧
          SolvesSDE ξ W X :=
  Iff.rfl

end ProbabilityTheory

namespace Function

/-- Object-prefix bridge to `ProbabilityTheory.CoordinateProcess.toEuclidean`. -/
abbrev toEuclidean {Ω : Type u} {d : ℕ} (W : NNReal → Ω → Fin d → ℝ) :
    NNReal → Ω → EuclideanSpace ℝ (Fin d) :=
  ProbabilityTheory.CoordinateProcess.toEuclidean W

/-- Evaluating `W.toEuclidean` applies the canonical inverse coordinate equivalence to `W t ω`. -/
theorem toEuclidean_apply {Ω : Type u} {d : ℕ} (W : NNReal → Ω → Fin d → ℝ)
    (t : NNReal) (ω : Ω) :
    Function.toEuclidean W t ω = (EuclideanSpace.equiv (Fin d) ℝ).symm (W t ω) :=
  ProbabilityTheory.CoordinateProcess.toEuclidean_apply W t ω

end Function
