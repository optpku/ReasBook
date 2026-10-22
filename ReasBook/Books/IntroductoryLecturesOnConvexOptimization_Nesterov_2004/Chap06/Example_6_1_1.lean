/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

variable {ι : Type v} [Fintype ι] [Nonempty ι]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Example 6.1.1 lies in the finite max-type / simplex-duality domain.

Sampled owner-style declarations:
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`;
- `StdSimplex` and its weight coordinates in the chapter's finite convex-combination layer;
- the chapter's Fenchel-duality bridge `fenchelDual` in `Chap03/Definition_3_1_2_1`.

Best owner abstraction:
- source-facing: the finite max-absolute affine objective attached to a family `(a_j, b_j)`;
- core/canonical: `maxTypeObjective` together with `StdSimplex`;
- bridge/view: the `ℓ₁`-ball and signed-simplex multiplier representations of the same function.

Primitive data:
- a finite family `a : ι → E`;
- offsets `b : ι → ℝ`.

Derived API:
- the source-facing owner `piecewiseLinearObjective a b`;
- its direct finite-maximum formula;
- the `ℓ₁`-ball representation;
- the signed-simplex representation from the end of the example.

This file keeps the public owner at the actual source-facing absolute-value function
`x ↦ max_j |⟪a_j, x⟫ - b_j|`, and records the multiplier representations as separate theorem
statements rather than replacing that function by a surrogate package. -/

/-- The max-absolute affine objective attached to the finite family
`x ↦ ⟪a_j, x⟫ - b_j`. -/
def piecewiseLinearObjective (a : ι → E) (b : ι → ℝ) : E → ℝ :=
  maxTypeObjective fun j x ↦ |inner ℝ (a j) x - b j|

/-- Helper for Example 6.1.1: every pairing with an `ℓ₁`-ball coefficient vector is bounded by
the maximum absolute coordinate score. -/
lemma l1_ball_pairing_le_finset_sup_abs
    (t : ι → ℝ) {u : ι → ℝ} (hu : ∑ j, |u j| ≤ 1) :
    ∑ j, u j * t j ≤ Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |t j|) := by
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |t j|)
  have hM_nonneg : 0 ≤ M := by
    let i0 : ι := Classical.choice ‹Nonempty ι›
    exact le_trans (abs_nonneg (t i0)) (Finset.le_sup' (fun j : ι ↦ |t j|) (Finset.mem_univ i0))
  have h_abs :
      |∑ j, u j * t j| ≤ M := by
    -- Bound the absolute pairing by the weighted sum of the coordinatewise maximum.
    calc
      |∑ j, u j * t j| ≤ ∑ j, |u j * t j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |u j| * |t j| := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [abs_mul]
      _ ≤ ∑ j, |u j| * M := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact
              mul_le_mul_of_nonneg_left
                (Finset.le_sup' (fun i : ι ↦ |t i|) (Finset.mem_univ j))
                (abs_nonneg (u j))
      _ = (∑ j, |u j|) * M := by
            rw [Finset.sum_mul]
      _ ≤ 1 * M := by
            exact mul_le_mul_of_nonneg_right hu hM_nonneg
      _ = M := by ring
  -- Drop the outer absolute value to recover the original pairing.
  exact (le_abs_self _).trans h_abs

/-- Helper for Example 6.1.1: a signed basis vector attains the maximum absolute coordinate score
inside the `ℓ₁` unit ball. -/
lemma exists_signed_basis_attaining_finset_sup_abs
    (t : ι → ℝ) :
    ∃ u : ι → ℝ,
      ∑ j, |u j| ≤ 1 ∧
        ∑ j, u j * t j = Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |t j|) := by
  classical
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : ι ↦ |t j|)
  by_cases ht0 : 0 ≤ t j0
  · -- Use the positive basis vector when the maximizing coordinate is nonnegative.
    let u : ι → ℝ := Pi.single j0 (1 : ℝ)
    refine ⟨u, ?_, ?_⟩
    · have hsingle_norm : ∑ j, |u j| = 1 := by
        rw [Finset.sum_eq_single j0]
        · simp [u]
        · intro j _ hj
          simp [u, hj]
        · simp
      exact hsingle_norm.le
    · have hsingle_value : ∑ j, u j * t j = t j0 := by
        rw [Finset.sum_eq_single j0]
        · simp [u]
        · intro j _ hj
          simp [u, hj]
        · simp
      calc
        ∑ j, u j * t j = t j0 := hsingle_value
        _ = |t j0| := by rw [abs_of_nonneg ht0]
        _ = Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |t j|) := hj0.symm
  · have htneg : t j0 < 0 := lt_of_not_ge ht0
    -- Use the negative basis vector when the maximizing coordinate is negative.
    let u : ι → ℝ := Pi.single j0 (-1 : ℝ)
    refine ⟨u, ?_, ?_⟩
    · have hsingle_norm : ∑ j, |u j| = 1 := by
        rw [Finset.sum_eq_single j0]
        · simp [u]
        · intro j _ hj
          simp [u, hj]
        · simp
      exact hsingle_norm.le
    · have hsingle_value : ∑ j, u j * t j = -t j0 := by
        rw [Finset.sum_eq_single j0]
        · simp [u]
        · intro j _ hj
          simp [u, hj]
        · simp
      calc
        ∑ j, u j * t j = -t j0 := hsingle_value
        _ = |t j0| := by rw [abs_of_neg htneg]
        _ = Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |t j|) := hj0.symm

/-- Helper for Example 6.1.1: the maximum absolute score equals the maximum over the positive and
negative branches indexed by `ι ⊕ ι`. -/
lemma sup_abs_affine_eq_signed_sup
    (t : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |t j|) =
      Finset.univ.sup' Finset.univ_nonempty
        (Sum.elim (fun j ↦ t j) (fun j ↦ -t j) : ι ⊕ ι → ℝ) := by
  let signed : ι ⊕ ι → ℝ := Sum.elim (fun j ↦ t j) (fun j ↦ -t j)
  -- Compare each absolute-value score with its signed branches, then reverse the comparison branchwise.
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro j hj
    rw [abs_eq_max_neg]
    refine max_le ?_ ?_
    · simpa [signed] using
        (Finset.le_sup' signed (Finset.mem_univ (Sum.inl j)))
    · simpa [signed] using
        (Finset.le_sup' signed (Finset.mem_univ (Sum.inr j)))
  · rw [Finset.sup'_le_iff]
    intro k hk
    cases k with
    | inl j =>
        exact
          (le_abs_self (t j)).trans <|
            Finset.le_sup' (fun i : ι ↦ |t i|) (Finset.mem_univ j)
    | inr j =>
        exact
          (neg_le_abs (t j)).trans <|
            Finset.le_sup' (fun i : ι ↦ |t i|) (Finset.mem_univ j)

/-- Helper for Example 6.1.1: a finite maximum equals the supremum of all simplex-weighted
averages of the same finite family. -/
lemma finset_sup'_eq_sSup_stdSimplex_weighted_sum
    {κ : Type*} [Fintype κ] [Nonempty κ] (f : κ → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty f =
      sSup (Set.range fun u : StdSimplex ℝ κ ↦ ∑ i, u.weights i * f i) := by
  classical
  let S : Set ℝ := Set.range fun u : StdSimplex ℝ κ ↦ ∑ i, u.weights i * f i
  have hS_nonempty : S.Nonempty := by
    let i0 : κ := Classical.choice ‹Nonempty κ›
    refine ⟨f i0, ?_⟩
    refine ⟨StdSimplex.single (R := ℝ) i0, ?_⟩
    simpa [dotProduct] using
      (single_dotProduct (v := f) (x := (1 : ℝ)) (i := i0))
  have hS_bdd : BddAbove S := by
    refine ⟨Finset.univ.sup' Finset.univ_nonempty f, ?_⟩
    rintro y ⟨u, rfl⟩
    have hpointwise :
        ∀ i : κ, u.weights i * f i ≤
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
  -- Realize the maximum by a simplex vertex and bound every simplex average by the same maximum.
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
        ∀ i : κ, u.weights i * f i ≤
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

/-- Helper for Example 6.1.1: the simplex-weighted signed score rewrites as the difference of the
positive and negative branch weights. -/
lemma signed_score_weighted_sum_eq_weight_difference_sum
    (t : ι → ℝ) (u : StdSimplex ℝ (ι ⊕ ι)) :
    ∑ k, u.weights k * (Sum.elim (fun j ↦ t j) (fun j ↦ -t j) k) =
      ∑ j, (u.weights (Sum.inl j) - u.weights (Sum.inr j)) * t j := by
  -- Split the signed index set into its positive and negative branches, then regroup each pair.
  calc
    ∑ k, u.weights k * (Sum.elim (fun j ↦ t j) (fun j ↦ -t j) k) =
        ∑ j, u.weights (Sum.inl j) * t j + ∑ j, u.weights (Sum.inr j) * (-t j) := by
          rw [Fintype.sum_sum_type]
          simp
    _ = ∑ j, (u.weights (Sum.inl j) - u.weights (Sum.inr j)) * t j := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring

-- Proof sketch: unfold `piecewiseLinearObjective` through the owner
-- `maxTypeObjective`.
/-- Evaluating the max-absolute affine objective gives the finite maximum of the absolute affine
pieces. -/
theorem piecewiseLinearObjective_apply (a : ι → E) (b : ι → ℝ) (x : E) :
    piecewiseLinearObjective a b x =
      Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) x - b j|) := by
  -- Unfold the source-facing owner to the canonical finite-maximum owner.
  simpa [piecewiseLinearObjective] using
    (maxTypeObjective_apply (fun j x ↦ |inner ℝ (a j) x - b j|) x)

-- Proof sketch: use the scalar identity
-- `|t| = sup {u * t | |u| ≤ 1}`, then combine the coordinate multipliers into a single point of
-- the `ℓ₁` ball in `ι → ℝ`.
/-- The max-absolute affine objective is the supremum of the corresponding linear functional over
the `ℓ₁` unit ball of coefficient vectors. -/
theorem piecewiseLinearObjective_eq_sSup_l1Ball
    (a : ι → E) (b : ι → ℝ) (x : E) :
    piecewiseLinearObjective a b x =
      sSup
        ((fun u : ι → ℝ ↦ ∑ j, u j * (inner ℝ (a j) x - b j)) ''
          {u : ι → ℝ | ∑ j, |u j| ≤ 1}) := by
  let t : ι → ℝ := fun j ↦ inner ℝ (a j) x - b j
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |t j|)
  let S : Set ℝ :=
    ((fun u : ι → ℝ ↦ ∑ j, u j * t j) '' {u : ι → ℝ | ∑ j, |u j| ≤ 1})
  have hobj : piecewiseLinearObjective a b x = M := by
    -- First normalize the objective to the finite maximum of the scalar scores `t j`.
    simpa [t, M] using piecewiseLinearObjective_apply a b x
  have hS_bdd : BddAbove S := by
    refine ⟨M, ?_⟩
    rintro y ⟨u, hu_ball, rfl⟩
    exact l1_ball_pairing_le_finset_sup_abs (t := t) hu_ball
  obtain ⟨u0, hu0_ball, hu0_value⟩ := exists_signed_basis_attaining_finset_sup_abs (t := t)
  have hS_nonempty : S.Nonempty := by
    refine ⟨M, ?_⟩
    refine ⟨u0, hu0_ball, ?_⟩
    simpa [M, S] using hu0_value
  have hsup : M = sSup S := by
    -- The upper bound comes from the `ℓ₁` estimate, and the lower bound comes from the signed basis witness.
    apply le_antisymm
    · refine le_csSup hS_bdd ?_
      refine ⟨u0, hu0_ball, ?_⟩
      simpa [M, S] using hu0_value
    · refine csSup_le hS_nonempty ?_
      rintro y ⟨u, hu_ball, rfl⟩
      exact l1_ball_pairing_le_finset_sup_abs (t := t) hu_ball
  calc
    piecewiseLinearObjective a b x = M := hobj
    _ = sSup S := hsup
    _ = sSup
          ((fun u : ι → ℝ ↦ ∑ j, u j * (inner ℝ (a j) x - b j)) ''
            {u : ι → ℝ | ∑ j, |u j| ≤ 1}) := by
          simp [S, t]

-- Proof sketch: split each signed coefficient `u j` as a difference of nonnegative parts
-- `u₁ j - u₂ j`, normalize them to total mass `1`, and identify those nonnegative parts with a
-- simplex point on the signed index set `ι ⊕ ι`.
/-- Example 6.1.1 [Chapter6_1.json:13]: the max-absolute affine objective admits the signed-simplex
representation
`f(x) = sup_{u ∈ Δ(ι ⊕ ι)} ∑_j (u(inl j) - u(inr j)) (⟪a_j, x⟫ - b_j)`. -/
theorem piecewiseLinearObjective_eq_simplexSup
    (a : ι → E) (b : ι → ℝ) (x : E) :
    piecewiseLinearObjective a b x =
      sSup
        (Set.range fun u : StdSimplex ℝ (ι ⊕ ι) ↦
          ∑ j, (u.weights (Sum.inl j) - u.weights (Sum.inr j)) *
            (inner ℝ (a j) x - b j)) := by
  let t : ι → ℝ := fun j ↦ inner ℝ (a j) x - b j
  let signed : ι ⊕ ι → ℝ := Sum.elim (fun j ↦ t j) (fun j ↦ -t j)
  have hrange :
      Set.range (fun u : StdSimplex ℝ (ι ⊕ ι) ↦ ∑ k, u.weights k * signed k) =
        Set.range fun u : StdSimplex ℝ (ι ⊕ ι) ↦
          ∑ j, (u.weights (Sum.inl j) - u.weights (Sum.inr j)) * t j := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨u, ?_⟩
      simpa [signed] using
        (signed_score_weighted_sum_eq_weight_difference_sum (t := t) u).symm
    · rintro ⟨u, rfl⟩
      refine ⟨u, ?_⟩
      simpa [signed] using signed_score_weighted_sum_eq_weight_difference_sum (t := t) u
  -- Rewrite the absolute maximum as a signed maximum, then pass from signed maxima to simplex averages.
  calc
    piecewiseLinearObjective a b x =
        Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |t j|) := by
          simpa [t] using piecewiseLinearObjective_apply a b x
    _ = Finset.univ.sup' Finset.univ_nonempty signed := by
          simpa [signed] using sup_abs_affine_eq_signed_sup (t := t)
    _ = sSup (Set.range fun u : StdSimplex ℝ (ι ⊕ ι) ↦ ∑ k, u.weights k * signed k) := by
          simpa [signed] using
            finset_sup'_eq_sSup_stdSimplex_weighted_sum (f := signed)
    _ = sSup
          (Set.range fun u : StdSimplex ℝ (ι ⊕ ι) ↦
            ∑ j, (u.weights (Sum.inl j) - u.weights (Sum.inr j)) * t j) := by
          rw [hrange]
    _ = sSup
          (Set.range fun u : StdSimplex ℝ (ι ⊕ ι) ↦
            ∑ j, (u.weights (Sum.inl j) - u.weights (Sum.inr j)) *
              (inner ℝ (a j) x - b j)) := by
          simp [t]

end
