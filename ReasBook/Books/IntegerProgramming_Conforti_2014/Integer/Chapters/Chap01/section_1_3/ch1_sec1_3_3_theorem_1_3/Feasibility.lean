/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_12
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.YesSet
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_22
import Mathlib.Data.Matrix.Mul

open scoped BigOperators Matrix

-- Rational nonnegative mixed-integer linear feasibility instances and their canonical decision
-- problem.
namespace MixedIntegerLinearFeasibility

/-- A rational nonnegative mixed-integer linear feasibility instance consists of rational matrices
`A`, `G`, and a rational right-hand side `b` describing the system `A x + G y ≤ b` with
`x ∈ ℤ_+^n` and `y ∈ ℝ_+^p`. -/
structure Instance where
  m : ℕ
  n : ℕ
  p : ℕ
  A : Matrix (Fin m) (Fin n) ℚ
  G : Matrix (Fin m) (Fin p) ℚ
  b : Fin m → ℚ

namespace Instance

/-- Build a mixed-integer linear feasibility instance from the rational system data `(A, G, b)`. -/
def ofSystem {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) : Instance where
  m := m
  n := n
  p := p
  A := A
  G := G
  b := b

/-- The encoding size of a mixed-integer linear feasibility instance is the sum of the encoding
sizes of the rows of `A`, the rows of `G`, and the entries of `b`. -/
def encodingSize (I : Instance) : ℕ :=
  (∑ i, EncodingSize.rationalVector (I.A i)) +
    (∑ i, EncodingSize.rationalVector (I.G i)) +
    EncodingSize.rationalVector I.b

/-- Expanding `I.encodingSize` gives the rowwise contributions of `A` and `G` together with the
right-hand side contribution from `b`. -/
theorem encodingSize_eq (I : Instance) :
    I.encodingSize =
      (∑ i, EncodingSize.rationalVector (I.A i)) +
        (∑ i, EncodingSize.rationalVector (I.G i)) +
        EncodingSize.rationalVector I.b :=
  rfl

/-- A mixed-integer linear feasibility instance is feasible when the corresponding Chapter 1
mixed-integer linear set is nonempty. -/
def hasFeasiblePoint (I : Instance) : Prop :=
  Set.Nonempty (rationalMixedIntegerLinearSet I.A I.G I.b)

/-- A mixed-integer linear feasibility instance is feasible exactly when its canonical Chapter 1
mixed-integer linear set is nonempty. -/
theorem hasFeasiblePoint_iff_nonempty_rationalMixedIntegerLinearSet (I : Instance) :
    I.hasFeasiblePoint ↔ Set.Nonempty (rationalMixedIntegerLinearSet I.A I.G I.b) :=
  Iff.rfl

/-- Expanding `I.hasFeasiblePoint` through `rationalMixedIntegerLinearSet` recovers the textbook
existential over a nonnegative integral vector `x` and a nonnegative real vector `y` satisfying
`A x + G y ≤ b`. -/
theorem hasFeasiblePoint_iff (I : Instance) :
    I.hasFeasiblePoint ↔
      ∃ x : Fin I.n → ℤ,
        ∃ y : Fin I.p → ℝ,
          0 ≤ x ∧
            0 ≤ y ∧
            (I.A.map (Rat.castHom ℝ)) *ᵥ (fun i ↦ (x i : ℝ)) + (I.G.map (Rat.castHom ℝ)) *ᵥ y ≤
              fun i ↦ (I.b i : ℝ) := by
  constructor
  · rintro ⟨xy, hxy⟩
    rw [mem_rationalMixedIntegerLinearSet_iff] at hxy
    rcases hxy with ⟨hineq, hx_nonneg, hy_nonneg, hx_integral⟩
    let x : Fin I.n → ℤ := fun i ↦ Classical.choose (hx_integral i)
    have hx_cast : xy.1 = fun i ↦ (x i : ℝ) := by
      funext i
      exact Classical.choose_spec (hx_integral i)
    -- Read the feasible mixed point as an integer witness `x` and a continuous witness `xy.2`.
    refine ⟨x, xy.2, ?_, hy_nonneg, ?_⟩
    · intro i
      have hxi : (0 : ℝ) ≤ (x i : ℝ) := by
        simpa [hx_cast] using hx_nonneg i
      exact_mod_cast hxi
    · simpa [hx_cast] using hineq
  · rintro ⟨x, y, hx_nonneg, hy_nonneg, hineq⟩
    -- Package the integral and continuous witnesses back into the canonical feasible point.
    refine ⟨((fun i ↦ (x i : ℝ)), y), ?_⟩
    rw [mem_rationalMixedIntegerLinearSet_iff]
    refine ⟨hineq, ?_, hy_nonneg, ?_⟩
    · intro i
      change (0 : ℝ) ≤ (x i : ℝ)
      exact_mod_cast hx_nonneg i
    · intro i
      exact ⟨x i, rfl⟩

end Instance

/-- The canonical decision problem asking whether a rational nonnegative mixed-integer linear
feasibility instance admits a feasible point. -/
noncomputable def decisionProblem : DecisionProblem :=
  DecisionProblem.ofYesSet Instance.encodingSize { I | I.hasFeasiblePoint }

/-- The Boolean answer of `decisionProblem` is true exactly when the underlying mixed-integer
system has a feasible point. -/
theorem decisionProblem_answer_eq_true_iff (I : Instance) :
    decisionProblem.answer I = true ↔ I.hasFeasiblePoint := by
  simp [decisionProblem]

end MixedIntegerLinearFeasibility
