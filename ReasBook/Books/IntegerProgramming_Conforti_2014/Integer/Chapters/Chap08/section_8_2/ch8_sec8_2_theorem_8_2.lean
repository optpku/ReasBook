/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_theorem_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators IntegerVectorNotation Matrix

section Theorem82

variable {m p K H : ℕ}

/-- The point `sum_k lambda_k v^k + sum_h mu_h r^h` represented by Dantzig-Wolfe coefficients. -/
def dantzig_wolfe_point
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ)
    (lam : Fin K → ℝ)
    (mu : Fin H → ℝ) : Fin p → ℝ :=
  (∑ k, lam k • v k) + ∑ h, mu h • r h

/-- The Dantzig-Wolfe coefficient conditions: `lambda` is a convex combination and `mu` is
componentwise nonnegative. -/
def dantzig_wolfe_coefficients
    (lam : Fin K → ℝ)
    (mu : Fin H → ℝ) : Prop :=
  (∑ k, lam k) = 1 ∧
    (∀ k, 0 ≤ lam k) ∧
    ∀ h, 0 ≤ mu h

/-- `dantzig_wolfe_coefficients lam mu` means that `lambda` is a convex combination and `mu` is
componentwise nonnegative. -/
theorem dantzig_wolfe_coefficients_iff
    (lam : Fin K → ℝ)
    (mu : Fin H → ℝ) :
    dantzig_wolfe_coefficients lam mu ↔
      (∑ k, lam k) = 1 ∧
        (∀ k, 0 ≤ lam k) ∧
        ∀ h, 0 ≤ mu h :=
  Iff.rfl

/-- `HasDantzigWolfeDecomposition Q v r` means that every point of `convexHull ℝ Q` admits the
representation used in the Dantzig-Wolfe relaxation (8.13). -/
def HasDantzigWolfeDecomposition
    (Q : Set (Fin p → ℝ))
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ) : Prop :=
  ∀ x : Fin p → ℝ,
    x ∈ convexHull ℝ Q ↔
      ∃ lam : Fin K → ℝ,
        ∃ mu : Fin H → ℝ,
          x = dantzig_wolfe_point v r lam mu ∧
            dantzig_wolfe_coefficients lam mu

/-- `HasDantzigWolfeDecomposition Q v r` means that every point of `convexHull ℝ Q` is represented
by Dantzig-Wolfe coefficients and generators `v`, `r`. -/
theorem hasDantzigWolfeDecomposition_iff
    (Q : Set (Fin p → ℝ))
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ) :
    HasDantzigWolfeDecomposition Q v r ↔
      ∀ x : Fin p → ℝ,
        x ∈ convexHull ℝ Q ↔
          ∃ lam : Fin K → ℝ,
            ∃ mu : Fin H → ℝ,
              x = dantzig_wolfe_point v r lam mu ∧
                dantzig_wolfe_coefficients lam mu :=
  Iff.rfl

/-- The feasible coefficient pairs `(lambda, mu)` of the Dantzig-Wolfe relaxation (8.13). -/
def dantzig_wolfe_relaxation_feasible_set
    (A1 : Matrix (Fin m) (Fin p) ℝ)
    (b1 : Fin m → ℝ)
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ) : Set ((Fin K → ℝ) × (Fin H → ℝ)) :=
  {y : (Fin K → ℝ) × (Fin H → ℝ) |
    A1 *ᵥ dantzig_wolfe_point v r y.1 y.2 ≤ b1 ∧
      dantzig_wolfe_coefficients y.1 y.2}

/-- Membership in `dantzig_wolfe_relaxation_feasible_set A1 b1 v r` means satisfying the master
inequalities `A1 x ≤ b1` after substituting the Dantzig-Wolfe point together with the coefficient
constraints from `(8.13)`. -/
theorem mem_dantzig_wolfe_relaxation_feasible_set_iff
    (A1 : Matrix (Fin m) (Fin p) ℝ)
    (b1 : Fin m → ℝ)
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ)
    (y : (Fin K → ℝ) × (Fin H → ℝ)) :
    y ∈ dantzig_wolfe_relaxation_feasible_set A1 b1 v r ↔
      A1 *ᵥ dantzig_wolfe_point v r y.1 y.2 ≤ b1 ∧
        dantzig_wolfe_coefficients y.1 y.2 :=
  Iff.rfl

/-- The source-facing Dantzig-Wolfe relaxation value of `(8.13)`, recorded in `EReal` so the
Chapter 8 value conventions still distinguish infeasibility `⊥` from unbounded-above behavior
`⊤`. -/
noncomputable def dantzig_wolfe_relaxation_value
    (A1 : Matrix (Fin m) (Fin p) ℝ)
    (b1 : Fin m → ℝ)
    (c : Fin p → ℝ)
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ) : EReal :=
  sSup
    ((fun y : (Fin K → ℝ) × (Fin H → ℝ) ↦
        ((c ⬝ᵥ dantzig_wolfe_point v r y.1 y.2 : ℝ) : EReal)) ''
      dantzig_wolfe_relaxation_feasible_set A1 b1 v r)

/-- `dantzig_wolfe_relaxation_value A1 b1 c v r` is the supremum of the master objective over the
feasible coefficient pairs from `(8.13)`. -/
theorem dantzig_wolfe_relaxation_value_eq_sSup
    (A1 : Matrix (Fin m) (Fin p) ℝ)
    (b1 : Fin m → ℝ)
    (c : Fin p → ℝ)
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ) :
    dantzig_wolfe_relaxation_value A1 b1 c v r =
      sSup
        ((fun y : (Fin K → ℝ) × (Fin H → ℝ) ↦
            ((c ⬝ᵥ dantzig_wolfe_point v r y.1 y.2 : ℝ) : EReal)) ''
          dantzig_wolfe_relaxation_feasible_set A1 b1 v r) :=
  rfl

/-- Theorem 8.2 (1). If every point of `convexHull ℝ Q` admits the decomposition used in
formulation `(8.13)`, then the Dantzig-Wolfe relaxation has the same canonical Chapter 8 value as
the convexified integer program `integer_program_value A1 b1 c (convexHull ℝ Q)`. -/
theorem dantzig_wolfe_relaxation_value_eq_integer_program_value_on_convex_hull
    (A1 : Matrix (Fin m) (Fin p) ℝ)
    (b1 : Fin m → ℝ)
    (c : Fin p → ℝ)
    (Q : Set (Fin p → ℝ))
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ)
    (hdecomp : HasDantzigWolfeDecomposition Q v r) :
    dantzig_wolfe_relaxation_value A1 b1 c v r =
      integer_program_value A1 b1 c (convexHull ℝ Q) := by
  have hobjectiveImage :
      (fun y : (Fin K → ℝ) × (Fin H → ℝ) ↦
        ((c ⬝ᵥ dantzig_wolfe_point v r y.1 y.2 : ℝ) : EReal)) ''
          dantzig_wolfe_relaxation_feasible_set A1 b1 v r =
        (fun x : Fin p → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
          convex_hull_feasible_set A1 b1 Q := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨dantzig_wolfe_point v r y.1 y.2, ?_, rfl⟩
      rw [mem_convex_hull_feasible_set_iff]
      constructor
      · -- The decomposition witnesses place each master-feasible point in `convexHull ℝ Q`.
        exact (hdecomp (dantzig_wolfe_point v r y.1 y.2)).2 ⟨y.1, y.2, rfl, hy.2⟩
      · -- The master inequality is already one half of relaxation feasibility.
        exact hy.1
    · rintro ⟨x, hx, rfl⟩
      rw [mem_convex_hull_feasible_set_iff] at hx
      rcases (hdecomp x).1 hx.1 with ⟨lam, mu, rfl, hcoeff⟩
      refine ⟨(lam, mu), ?_, rfl⟩
      -- Repackage the convex-hull witness as a feasible Dantzig-Wolfe coefficient pair.
      rw [mem_dantzig_wolfe_relaxation_feasible_set_iff]
      exact ⟨hx.2, hcoeff⟩
  -- The two values are supremums of the same objective image set.
  rw [dantzig_wolfe_relaxation_value_eq_sSup, integer_program_value_eq_sSup]
  rw [hobjectiveImage]

/-- Theorem 8.2 (2). The Dantzig-Wolfe reformulation is obtained from (8.13) by adding the
integrality constraints (8.14), namely that `sum_k v_j^k lambda_k + sum_h r_j^h mu_h` is an
integer for every coordinate `j = 1, ..., p`. -/
def dantzig_wolfe_reformulation_feasible_set
    (A1 : Matrix (Fin m) (Fin p) ℝ)
    (b1 : Fin m → ℝ)
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ) : Set ((Fin K → ℝ) × (Fin H → ℝ)) :=
  dantzig_wolfe_relaxation_feasible_set A1 b1 v r ∩
    {y : (Fin K → ℝ) × (Fin H → ℝ) |
      dantzig_wolfe_point v r y.1 y.2 ∈ ℤ^p}

/-- Membership in `dantzig_wolfe_reformulation_feasible_set` means satisfying the Dantzig-Wolfe
relaxation constraints together with the coordinatewise integrality constraints (8.14). -/
theorem mem_dantzig_wolfe_reformulation_feasible_set_iff
    (A1 : Matrix (Fin m) (Fin p) ℝ)
    (b1 : Fin m → ℝ)
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ)
    (y : (Fin K → ℝ) × (Fin H → ℝ)) :
    y ∈ dantzig_wolfe_reformulation_feasible_set A1 b1 v r ↔
      A1 *ᵥ dantzig_wolfe_point v r y.1 y.2 ≤ b1 ∧
        dantzig_wolfe_coefficients y.1 y.2 ∧
        dantzig_wolfe_point v r y.1 y.2 ∈ ℤ^p := by
  constructor
  · intro hy
    exact ⟨hy.1.1, hy.1.2, hy.2⟩
  · rintro ⟨hineq, hcoeff, hint⟩
    exact ⟨⟨hineq, hcoeff⟩, hint⟩

/-- Bridge/view: membership in the Dantzig-Wolfe reformulation is membership in the continuous
master relaxation together with the integrality constraints `(8.14)`. -/
theorem mem_dantzig_wolfe_reformulation_feasible_set_iff_relaxation
    (A1 : Matrix (Fin m) (Fin p) ℝ)
    (b1 : Fin m → ℝ)
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ)
    (y : (Fin K → ℝ) × (Fin H → ℝ)) :
    y ∈ dantzig_wolfe_reformulation_feasible_set A1 b1 v r ↔
      y ∈ dantzig_wolfe_relaxation_feasible_set A1 b1 v r ∧
        dantzig_wolfe_point v r y.1 y.2 ∈ ℤ^p :=
  Iff.rfl

end Theorem82
