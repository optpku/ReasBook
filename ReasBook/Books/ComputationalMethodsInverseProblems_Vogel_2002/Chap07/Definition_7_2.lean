/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_1

public section

noncomputable section

universe u w

section GCVValue

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The fixed-influence-matrix generalized cross-validation value. -/
def gcvValue (A : Matrix n n ℝ) (d : EuclideanSpace ℝ n) : ℝ :=
  predictiveRisk (regularizedResidual A d) /
    ((Matrix.trace (1 - A) / (Fintype.card n : ℝ)) ^ 2)

/-- The defining formula for `gcvValue`. -/
@[simp] theorem gcvValue_def (A : Matrix n n ℝ) (d : EuclideanSpace ℝ n) :
    gcvValue A d =
      predictiveRisk (regularizedResidual A d) /
        ((Matrix.trace (1 - A) / (Fintype.card n : ℝ)) ^ 2) := by
  simp [gcvValue]

end GCVValue

section GCV

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {τ : Type w}

/-- Definition 7.2-extra-1 (1). The generalized cross-validation objective associated
to a family of influence matrices. -/
def gcv (Afamily : τ → Matrix n n ℝ) (d : EuclideanSpace ℝ n) : τ → ℝ :=
  fun a ↦ gcvValue (Afamily a) d

/-- The defining formula for `gcv` in terms of `gcvValue`. -/
@[simp] theorem gcv_eq_gcvValue (Afamily : τ → Matrix n n ℝ) (d : EuclideanSpace ℝ n)
    (a : τ) :
    gcv Afamily d a = gcvValue (Afamily a) d := by
  simp [gcv]

/-- Definition 7.2-extra-1 (2). A parameter is a generalized cross-validation
parameter when it minimizes `gcv` on `Set.univ`. -/
def IsGCVParameter (Afamily : τ → Matrix n n ℝ) (d : EuclideanSpace ℝ n)
    (a : τ) : Prop :=
  IsMinOn (gcv Afamily d) Set.univ a

/-- The defining characterization of `IsGCVParameter`. -/
@[simp] theorem IsGCVParameter_iff (Afamily : τ → Matrix n n ℝ) (d : EuclideanSpace ℝ n)
    (a : τ) :
    IsGCVParameter Afamily d a ↔ IsMinOn (gcv Afamily d) Set.univ a := Iff.rfl

end GCV

end
