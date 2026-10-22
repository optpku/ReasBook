/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

variable {m : ℕ+} {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin (m : ℕ))
local notation "G" => Fin (m : ℕ) ⊕ Fin (m : ℕ)

/- Proposition 6.20 lies in the finite max-type / simplex-duality domain.

Sampled owner-style declarations:
- `Matrix.fromRows` and `Matrix.fromRows_mulVec`, the canonical signed row stack;
- `piecewiseLinearObjective` and `piecewiseLinearObjective_eq_simplexSup` in `Example_6_1_1`, the
  project owner for a finite maximum of affine functionals and its simplex representation;
- `StdSimplex`, the canonical simplex owner used by that representation theorem.

Best owner abstraction:
- source-facing: Proposition 6.20's absolute row-maximum written through a signed row family;
- core/canonical: `piecewiseLinearObjective` specialized to `Matrix.fromRows A (-A)`;
- bridge/view: the duplicated offset `Sum.elim b b` on the signed row index.

Primitive data:
- the row matrix `A`;
- the offset vector `b`;
- the evaluation point `x`.

Derived API:
- the signed row family `Matrix.fromRows A (-A)`;
- the signed offset `Sum.elim b b`;
- the simplex-supremum representation.

Source/core/bridge triage:
- source-facing: `max_abs_row_pairing_sub_offset_eq_sSup_signed_simplex`;
- core/canonical: `piecewiseLinearObjective_eq_simplexSup`;
- bridge/view: the signed-row specialization connecting the absolute-value formula to that owner.

The previous file introduced local wrapper names for the stacked matrix and its evaluation, even
though the owner-level row stack already exists canonically as `Matrix.fromRows`, and the simplex
representation already exists canonically as `piecewiseLinearObjective_eq_simplexSup`. This
refinement deletes that duplicate layer and states Proposition 6.20 directly on the canonical
signed-row/simplex surface.
-/

/-- Helper for Proposition 6.20: the signed affine row score on the stacked row index type. -/
def signed_row_score
    (A : Matrix (Fin (m : ℕ)) (Fin n) ℝ) (b : F) (x : E) : G → ℝ :=
  Sum.elim
    (fun j ↦ dotProduct (A j) x - b j)
    (fun j ↦ -dotProduct (A j) x - b j)

/-- Helper for Proposition 6.20: the absolute-value row objective is the finite maximum of the
corresponding signed row scores. -/
lemma sup_abs_row_pairing_sub_offset_eq_signed_row_sup
    (A : Matrix (Fin (m : ℕ)) (Fin n) ℝ) (b : F) (x : E) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (m : ℕ) ↦ |dotProduct (A j) x| - b j) =
      Finset.univ.sup' Finset.univ_nonempty (signed_row_score A b x) := by
  -- Each absolute-value term is the maximum of its positive and negative signed branches.
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro j hj
    rw [abs_eq_max_neg, ← max_sub_sub_right]
    have h_inl :
        dotProduct (A j) x - b j ≤
          Finset.univ.sup' Finset.univ_nonempty (signed_row_score A b x) := by
      exact
        Finset.le_sup'_of_le
          (f := signed_row_score A b x)
          (s := Finset.univ)
          (b := Sum.inl j)
          (by simp)
          (by simp [signed_row_score])
    have h_inr :
        -dotProduct (A j) x - b j ≤
          Finset.univ.sup' Finset.univ_nonempty (signed_row_score A b x) := by
      exact
        Finset.le_sup'_of_le
          (f := signed_row_score A b x)
          (s := Finset.univ)
          (b := Sum.inr j)
          (by simp)
          (by simp [signed_row_score])
    exact
      max_le_iff.mpr ⟨h_inl, h_inr⟩
  · rw [Finset.sup'_le_iff]
    intro k hk
    cases k with
    | inl j =>
        -- The positive branch is dominated by the absolute-value term for the same row.
        exact
          (sub_le_sub_right (le_abs_self (dotProduct (A j) x)) (b j)).trans <|
            (by
              exact
                Finset.le_sup'
                  (fun i : Fin (m : ℕ) ↦ |dotProduct (A i) x| - b i)
                  (Finset.mem_univ j))
    | inr j =>
        -- The negative branch is dominated by the same absolute-value term.
        exact
          (sub_le_sub_right (neg_le_abs (dotProduct (A j) x)) (b j)).trans <|
            (by
              exact
                Finset.le_sup'
                  (fun i : Fin (m : ℕ) ↦ |dotProduct (A i) x| - b i)
                  (Finset.mem_univ j))

/-- Helper for Proposition 6.20: a finite maximum equals the supremum of all simplex-weighted
averages of the same finite family. -/
lemma finset_sup'_eq_sSup_stdSimplex_weighted_sum
    {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty f =
      sSup (Set.range fun u : StdSimplex ℝ ι ↦ ∑ i, u.weights i * f i) := by
  classical
  let S : Set ℝ := Set.range fun u : StdSimplex ℝ ι ↦ ∑ i, u.weights i * f i
  have hS_nonempty : S.Nonempty := by
    let i0 : ι := Classical.choice ‹Nonempty ι›
    refine ⟨f i0, ?_⟩
    refine ⟨StdSimplex.single (R := ℝ) i0, ?_⟩
    simpa [dotProduct] using
      (single_dotProduct (v := f) (x := (1 : ℝ)) (i := i0))
  have hS_bdd : BddAbove S := by
    refine ⟨Finset.univ.sup' Finset.univ_nonempty f, ?_⟩
    rintro y ⟨u, rfl⟩
    have hpointwise :
        ∀ i : ι, u.weights i * f i ≤
          u.weights i * Finset.univ.sup' Finset.univ_nonempty f := by
      intro i
      exact
        mul_le_mul_of_nonneg_left
          (Finset.le_sup' f (Finset.mem_univ i))
          (u.nonneg i)
    calc
      ∑ i, u.weights i * f i ≤
          ∑ i, u.weights i * Finset.univ.sup' Finset.univ_nonempty f := by
            exact Finset.sum_le_sum fun i _ ↦ hpointwise i
      _ = (∑ i, u.weights i) * Finset.univ.sup' Finset.univ_nonempty f := by
            rw [Finset.sum_mul]
      _ = Finset.univ.sup' Finset.univ_nonempty f := by
            have htotal : ∑ i, u.weights i = 1 := by
              simpa [Finsupp.sum_fintype] using u.total
            simp [htotal]
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro i hi
    refine le_csSup hS_bdd ?_
    refine ⟨StdSimplex.single (R := ℝ) i, ?_⟩
    simpa [dotProduct] using
      (single_dotProduct (v := f) (x := (1 : ℝ)) (i := i))
  · refine csSup_le hS_nonempty ?_
    rintro y ⟨u, rfl⟩
    have hpointwise :
        ∀ i : ι, u.weights i * f i ≤
          u.weights i * Finset.univ.sup' Finset.univ_nonempty f := by
      intro i
      exact
        mul_le_mul_of_nonneg_left
          (Finset.le_sup' f (Finset.mem_univ i))
          (u.nonneg i)
    calc
      ∑ i, u.weights i * f i ≤
          ∑ i, u.weights i * Finset.univ.sup' Finset.univ_nonempty f := by
            exact Finset.sum_le_sum fun i _ ↦ hpointwise i
      _ = (∑ i, u.weights i) * Finset.univ.sup' Finset.univ_nonempty f := by
            rw [Finset.sum_mul]
      _ = Finset.univ.sup' Finset.univ_nonempty f := by
            have htotal : ∑ i, u.weights i = 1 := by
              simpa [Finsupp.sum_fintype] using u.total
            simp [htotal]

/-- Helper for Proposition 6.20: the simplex-weighted signed score is the dot-product expression
coming from the stacked matrix `Matrix.fromRows A (-A)` and duplicated offset `Sum.elim b b`. -/
lemma signed_row_weighted_sum_eq_matrix_dotProduct_sub
    (A : Matrix (Fin (m : ℕ)) (Fin n) ℝ) (b : F) (x : E) (u : StdSimplex ℝ G) :
    ∑ k, u.weights k * signed_row_score A b x k =
      dotProduct ((Matrix.fromRows A (-A)).mulVec x) u.weights -
        dotProduct (Sum.elim b b) u.weights := by
  have hscore :
      signed_row_score A b x =
        ((Matrix.fromRows A (-A)).mulVec x) - Sum.elim b b := by
    -- Expanding the stacked matrix action identifies each signed branch pointwise.
    funext k
    cases k with
    | inl j =>
        simp [signed_row_score, Matrix.fromRows_mulVec, Matrix.mulVec, dotProduct]
    | inr j =>
        simp [signed_row_score, Matrix.fromRows_mulVec, Matrix.mulVec, dotProduct]
  -- Commute the dot product once, then use the pointwise score identity.
  calc
    ∑ k, u.weights k * signed_row_score A b x k =
        dotProduct u.weights (signed_row_score A b x) := by
          simp [dotProduct]
    _ = dotProduct (signed_row_score A b x) u.weights := by
          rw [dotProduct_comm]
    _ = dotProduct (((Matrix.fromRows A (-A)).mulVec x) - Sum.elim b b) u.weights := by
          rw [hscore]
    _ = dotProduct ((Matrix.fromRows A (-A)).mulVec x) u.weights -
          dotProduct (Sum.elim b b) u.weights := by
          rw [sub_dotProduct]

/-- Proposition 6.20: stacking `A` and `-A` and duplicating `b` identifies
`max_j (|⟪a_j, x⟫| - b_j)` with the supremum of the corresponding affine functional over the
standard simplex on the signed row index set. -/
theorem max_abs_row_pairing_sub_offset_eq_sSup_signed_simplex
    (A : Matrix (Fin (m : ℕ)) (Fin n) ℝ) (b : F) (x : E) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (m : ℕ) ↦ |dotProduct (A j) x| - b j) =
      sSup (Set.range fun u : StdSimplex ℝ G ↦
        dotProduct ((Matrix.fromRows A (-A)).mulVec x) u.weights -
          dotProduct (Sum.elim b b) u.weights) := by
  -- Route correction: Proposition 6.20 uses the signed row stack `A / -A`, not the
  -- absolute-affine owner from Example 6.1.1.
  have hrange :
      Set.range (fun u : StdSimplex ℝ G ↦ ∑ k, u.weights k * signed_row_score A b x k) =
        Set.range fun u : StdSimplex ℝ G ↦
          dotProduct ((Matrix.fromRows A (-A)).mulVec x) u.weights -
            dotProduct (Sum.elim b b) u.weights := by
    -- The adapter lemma identifies the two parameterized value sets pointwise.
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, (signed_row_weighted_sum_eq_matrix_dotProduct_sub A b x u).symm⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, signed_row_weighted_sum_eq_matrix_dotProduct_sub A b x u⟩
  -- Rewrite the rowwise absolute maximum as a signed maximum, then pass to simplex averages.
  calc
    Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (m : ℕ) ↦ |dotProduct (A j) x| - b j) =
      Finset.univ.sup' Finset.univ_nonempty (signed_row_score A b x) := by
        simpa using sup_abs_row_pairing_sub_offset_eq_signed_row_sup A b x
    _ = sSup (Set.range fun u : StdSimplex ℝ G ↦
          ∑ k, u.weights k * signed_row_score A b x k) := by
        simpa using
          finset_sup'_eq_sSup_stdSimplex_weighted_sum (f := signed_row_score A b x)
    _ = sSup (Set.range fun u : StdSimplex ℝ G ↦
          dotProduct ((Matrix.fromRows A (-A)).mulVec x) u.weights -
            dotProduct (Sum.elim b b) u.weights) := by
        rw [hrange]

end
