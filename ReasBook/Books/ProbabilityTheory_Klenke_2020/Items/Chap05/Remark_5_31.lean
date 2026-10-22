/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_64
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28

open Filter MeasureTheory ProbabilityTheory

open scoped Topology

noncomputable section

/-- Remark 5.31: condition (5.14) is sharp in the sense that every increasing nonnegative
normalizing sequence with divergent logarithmically weighted inverse-square series admits a
pairwise independent, centered, square-integrable counterexample of unit variance whose normalized
partial sums have almost-sure `EReal` limsup `⊤`. -/
def rademacherMenshovSharpnessStatement : Prop :=
  ∀ a : ℕ → NNReal, Monotone a →
    ¬ Summable (fun n : ℕ ↦ ((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹)) →
      ∃ P : ProbabilityMeasure (ℕ → ℝ),
        Pairwise (fun i j ↦ IndepFun (coordinateProcess i) (coordinateProcess j) P.toMeasure) ∧
        (∀ n, MemLp (coordinateProcess n) 2 P.toMeasure) ∧
        (∀ n, P.toMeasure[coordinateProcess n] = 0) ∧
        (∀ n, Var[coordinateProcess n; P.toMeasure] = 1) ∧
        ∀ᵐ ω ∂P.toMeasure,
          limsup
            (fun n : ℕ ↦
              (((|partialSum coordinateProcess (n + 1) ω| / (a n : ℝ)) : ℝ) : EReal))
            atTop = ⊤
