/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_5.ch8_sec8_5_exercise_8_16.Equality

open scoped Matrix

-- This source-facing exercise records the equality-constrained Benders variant directly over the
-- Chapter 8 residual `b - A x`.

section Exercise816

variable {m n p : ℕ}
universe u v

variable {K : Type u} {J : Type v}

/-- The `x`-projection of the mixed system `A x + G y = b`, `y ≥ 0`, encoded as existence of an
equality-constrained Benders subproblem solution after fixing `x`. -/
abbrev benders_equality_projection_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  Benders.Equality.projectionSet (benders_residual A b) G

/-- The optimal value `z_LP(x)` of the equality-constrained Benders subproblem with right-hand
side `rhs`, recorded in `EReal` so unbounded-above subproblems have value `⊤ = +∞`. -/
noncomputable abbrev benders_equality_subproblem_value
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ)
    (rhs : Fin m → ℝ) : EReal :=
  Benders.Equality.subproblemValue G h rhs

/-- The source value `z_I` of the equality-constrained mixed problem obtained from (8.26),
namely the maximum of `c x + h y` over feasible pairs `(x, y)` satisfying `A x + G y = b`. -/
noncomputable abbrev benders_equality_original_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : Fin p → ℝ) : EReal :=
  Benders.Equality.originalValue (benders_residual A b) G X (fun x ↦ c ⬝ᵥ x) h

/-- Exercise 8.16. If the mixed problem (8.26) uses equality constraints `A x + G y = b`
instead of inequalities `A x + G y ≤ b`, then the Chapter 8 Benders reformulation is modified by
replacing the subproblem feasible set, the `x`-projection, and the original objective value by
their equality-constrained analogues. Under the corresponding equality-specific projection and
subproblem-value hypotheses, the same Benders master value formula remains valid, and the proof is
changed only by making those substitutions throughout Theorem 8.18. -/
theorem benders_equality_original_value_eq_master_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : Fin p → ℝ)
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (hproj :
      benders_equality_projection_set A G b =
        benders_feasibility_cut_set A b r)
    (hsubproblem :
      ∀ x : Fin n → ℝ,
        x ∈ benders_equality_projection_set A G b →
          benders_equality_subproblem_value G h (benders_residual A b x) =
            benders_optimality_cut_value A b u x) :
    benders_equality_original_value A G b X c h =
      benders_master_value A b X u r c := by
  -- Route correction: reuse the residual-based equality owner theorem instead of replaying its
  -- expensive `EReal.toReal` proof locally in the source-facing wrapper.
  -- Specialize the owner theorem to the Chapter 8 residual `x ↦ b - A x` and objective
  -- `x ↦ c ⬝ᵥ x`; the hypotheses already have exactly that residual-based shape.
  exact Benders.Equality.originalValue_eq_masterValue
    (α := Fin n → ℝ)
    (m := m)
    (p := p)
    (K := K)
    (J := J)
    (residual := benders_residual A b)
    G
    X
    (fun x ↦ c ⬝ᵥ x)
    h
    u
    r
    hproj
    hsubproblem

end Exercise816
