/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part16

section Chap06
section Section30

-- Proof sketch: specialize Theorem 6.30.20 at `x* = 0` and rewrite the Fenchel conjugate at the
-- origin as the negative of the infimum of the weighted objective. The feasible-set description
-- is then the condition that the dual slice at `x* = 0` be strictly greater than `-∞`.
-- Finally, use the standard criterion that the infimum of a proper convex function is finite
-- exactly when `0` belongs to the Minkowski sum of the domains of the conjugates, encoded here by
-- explicit witnesses from those domains whose weighted sum is zero.
/-- Helper for Theorem 6.30.21: the finiteness condition `⊥ < sInf (range g)` is equivalent to
the Fenchel conjugate of `g` being finite at `0`. This is the algebraic bridge between the
infimum formulation of the dual objective and the effective-domain formulation via conjugates. -/
lemma helperForTheorem_6_30_21_bot_lt_sInf_range_iff_fenchelConjugate_zero_lt_top
    {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    (⊥ : EReal) < sInf (Set.range g) ↔ fenchelConjugate n g 0 < (⊤ : EReal) := by
  -- Rewrite the `sInf` of the range as the `iInf` over all points.
  have hsInf : sInf (Set.range g) = iInf fun x : Fin n → ℝ => g x := by
    simpa [sInf_range]
  -- Evaluate the conjugate at `0` using its closed-form formula.
  have hConj :
      fenchelConjugate n g 0 = - (iInf fun x : Fin n → ℝ => g x) := by
    simpa using (fenchelConjugate_zero_eq_neg_iInf (n := n) (f := g))
  -- Compare the strict bounds by applying order-reversal of negation.
  have hNeg :
      (⊥ : EReal) < (iInf fun x : Fin n → ℝ => g x) ↔
        - (iInf fun x : Fin n → ℝ => g x) < (⊤ : EReal) := by
    -- `-(iInf g) < -⊥` is the same inequality, and `-⊥ = ⊤`.
    have h :=
      (EReal.neg_lt_neg_iff (a := (iInf fun x : Fin n → ℝ => g x)) (b := (⊥ : EReal)))
    have h' :
        (- (iInf fun x : Fin n → ℝ => g x) < (⊤ : EReal)) ↔
          (⊥ : EReal) < (iInf fun x : Fin n → ℝ => g x) := by
      simpa using h
    exact h'.symm
  -- Assemble the equivalence with the two rewrites above.
  calc
    (⊥ : EReal) < sInf (Set.range g)
        ↔ (⊥ : EReal) < (iInf fun x : Fin n → ℝ => g x) := by
            simpa [hsInf]
    _ ↔ - (iInf fun x : Fin n → ℝ => g x) < (⊤ : EReal) := hNeg
    _ ↔ fenchelConjugate n g 0 < (⊤ : EReal) := by
          simpa [hConj]

/-- Helper for Theorem 6.30.21: the Fenchel conjugate at `0` records the negative infimum, so
it is `⊤` exactly when the objective is unbounded below (`sInf (range g) = ⊥`). -/
lemma helperForTheorem_6_30_21_fenchelConjugate_zero_eq_top_iff_sInf_range_eq_bot
    {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    fenchelConjugate n g 0 = (⊤ : EReal) ↔ sInf (Set.range g) = (⊥ : EReal) := by
  -- Rewrite both sides in terms of the pointwise infimum `iInf x, g x`.
  have hsInf : sInf (Set.range g) = iInf fun x : Fin n → ℝ => g x := by
    simpa [sInf_range]
  have hConj :
      fenchelConjugate n g 0 = - (iInf fun x : Fin n → ℝ => g x) := by
    simpa using (fenchelConjugate_zero_eq_neg_iInf (n := n) (f := g))
  constructor
  · intro hTop
    -- Negating the identity `f*(0) = ⊤` forces `iInf g = ⊥`, hence `sInf (range g) = ⊥`.
    have hiInf : (iInf fun x : Fin n → ℝ => g x) = (⊥ : EReal) := by
      have hNeg : - (iInf fun x : Fin n → ℝ => g x) = (⊤ : EReal) := by
        simpa [hConj] using hTop
      have := congrArg Neg.neg hNeg
      simpa using this
    simpa [hsInf, hiInf]
  · intro hBot
    -- Conversely, if the infimum is `⊥`, then `f*(0) = -⊥ = ⊤`.
    have hiInf : (iInf fun x : Fin n → ℝ => g x) = (⊥ : EReal) := by
      simpa [hsInf] using hBot
    calc
      fenchelConjugate n g 0 = - (iInf fun x : Fin n → ℝ => g x) := by
        simpa [hConj]
      _ = - (⊥ : EReal) := by
        simp [hiInf]
      _ = (⊤ : EReal) := by
        simp

/-- Helper for Theorem 6.30.21: a proper `EReal`-valued function has a Fenchel conjugate that is
never `⊥`. This avoids degenerate `-∞` cases when rearranging Fenchel–Young inequalities from the
definition `f*(x*) = sup_x (⟪x, x*⟫ - f x)`. -/
lemma helperForTheorem_6_30_21_fenchelConjugate_ne_bot_of_properERealFunction
    {n : ℕ} {f : (Fin n → ℝ) → EReal} (hf : ProperERealFunction f) (xStar : Fin n → ℝ) :
    fenchelConjugate n f xStar ≠ (⊥ : EReal) := by
  classical
  -- Choose a point where `f` is finite above to witness a non-`⊥` element in the range.
  rcases hf.2 with ⟨x0, hx0_ne_top⟩
  have hx0_ne_bot : f x0 ≠ (⊥ : EReal) := hf.1 x0
  set r0 : ℝ := (f x0).toReal
  have hfx0 : ((r0 : ℝ) : EReal) = f x0 := by
    simpa [r0] using (EReal.coe_toReal (x := f x0) hx0_ne_top hx0_ne_bot)
  have hterm_ne_bot : (((x0 ⬝ᵥ xStar : ℝ) : EReal) - f x0) ≠ (⊥ : EReal) := by
    -- Rewrite the term as a real coercion.
    have hterm : (((x0 ⬝ᵥ xStar : ℝ) : EReal) - f x0) =
        (((x0 ⬝ᵥ xStar : ℝ) - r0 : ℝ) : EReal) := by
      -- Replace `f x0` by a real and use `EReal.coe_sub`.
      calc
        (((x0 ⬝ᵥ xStar : ℝ) : EReal) - f x0)
            = (((x0 ⬝ᵥ xStar : ℝ) : EReal) - ((r0 : ℝ) : EReal)) := by
                simp [hfx0]
        _ = (((x0 ⬝ᵥ xStar : ℝ) - r0 : ℝ) : EReal) := by
              simpa using (EReal.coe_sub (x0 ⬝ᵥ xStar : ℝ) r0)
    -- A real coercion is never `⊥`.
    simpa [hterm] using (EReal.coe_ne_bot ((x0 ⬝ᵥ xStar : ℝ) - r0))
  -- The conjugate is the supremum of these terms, so it cannot be `⊥`.
  intro hbot
  have hle : (((x0 ⬝ᵥ xStar : ℝ) : EReal) - f x0) ≤ fenchelConjugate n f xStar := by
    unfold fenchelConjugate
    exact le_sSup ⟨x0, rfl⟩
  have hle_bot : (((x0 ⬝ᵥ xStar : ℝ) : EReal) - f x0) ≤ (⊥ : EReal) := by
    simpa [hbot] using hle
  have heq : (((x0 ⬝ᵥ xStar : ℝ) : EReal) - f x0) = (⊥ : EReal) :=
    le_antisymm hle_bot bot_le
  exact hterm_ne_bot heq

/-- Helper for Theorem 6.30.21: on the dual-feasible branch `uStar ≥ 0`, the witness condition
forces the weighted objective to be bounded below, so its infimum is not `⊥` (i.e. not `-∞`). -/
lemma helperForTheorem_6_30_21_bot_lt_sInf_range_weightedObjective_of_witness_of_nonneg
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexERealFunction (F := (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexERealFunction (F := (Fin n → ℝ)) (f i))
    {uStar : Fin m → ℝ} (hnonneg : ∀ i : Fin m, 0 ≤ uStar i)
    {y0 : Fin n → ℝ}
    (hy0 : y0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f0))
    {y : Fin m → Fin n → ℝ}
    (hy : ∀ i : Fin m,
      y i ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i)))
    (hSum : y0 + ∑ i : Fin m, (uStar i) • y i = 0) :
    (⊥ : EReal) <
        sInf (Set.range fun x : Fin n → ℝ =>
          ordinaryConvexProgramWeightedObjective f0 f uStar x) := by
  classical
  -- Let `g(x) = f0(x) + ∑ᵢ uᵢ* fᵢ(x)` be the weighted objective.
  let g : (Fin n → ℝ) → EReal := ordinaryConvexProgramWeightedObjective f0 f uStar

  -- Extract the finiteness information `f*(y) < ⊤` from `effectiveDomain`.
  have hy0_top : fenchelConjugate n f0 y0 ≠ (⊤ : EReal) := by
    have :
        y0 ∈ {x | x ∈ (Set.univ : Set (Fin n → ℝ)) ∧ fenchelConjugate n f0 x < (⊤ : EReal)} := by
      simpa [effectiveDomain_eq] using hy0
    exact (lt_top_iff_ne_top).1 this.2
  have hy_top : ∀ i : Fin m, fenchelConjugate n (f i) (y i) ≠ (⊤ : EReal) := by
    intro i
    have :
        y i ∈ {x | x ∈ (Set.univ : Set (Fin n → ℝ)) ∧ fenchelConjugate n (f i) x < (⊤ : EReal)} := by
      simpa [effectiveDomain_eq] using hy i
    exact (lt_top_iff_ne_top).1 this.2

  -- Properness gives `f*(y) ≠ ⊥`, needed for rearranging `EReal` subtractions.
  have hy0_bot : fenchelConjugate n f0 y0 ≠ (⊥ : EReal) := by
    exact
      helperForTheorem_6_30_21_fenchelConjugate_ne_bot_of_properERealFunction
        (hf := hf0.1) (xStar := y0)
  have hy_bot : ∀ i : Fin m, fenchelConjugate n (f i) (y i) ≠ (⊥ : EReal) := by
    intro i
    exact
      helperForTheorem_6_30_21_fenchelConjugate_ne_bot_of_properERealFunction
        (hf := (hf i).1) (xStar := y i)

  -- Convert the conjugate values to reals so we can use cancellation on the constant term.
  let r0 : ℝ := (fenchelConjugate n f0 y0).toReal
  have hconj0 : ((r0 : ℝ) : EReal) = fenchelConjugate n f0 y0 := by
    simpa [r0] using (EReal.coe_toReal (x := fenchelConjugate n f0 y0) hy0_top hy0_bot)
  let r : Fin m → ℝ := fun i : Fin m => (fenchelConjugate n (f i) (y i)).toReal
  have hconj : ∀ i : Fin m, ((r i : ℝ) : EReal) = fenchelConjugate n (f i) (y i) := by
    intro i
    simpa [r] using
      (EReal.coe_toReal (x := fenchelConjugate n (f i) (y i)) (hy_top i) (hy_bot i))
  let rK : ℝ := r0 + ∑ i : Fin m, uStar i * r i

  have hK :
      ((rK : ℝ) : EReal) =
        fenchelConjugate n f0 y0 +
          ∑ i : Fin m, ((uStar i : ℝ) : EReal) * fenchelConjugate n (f i) (y i) := by
    -- Rewrite every conjugate value as a real and use the `EReal` coercion lemmas.
    calc
      ((rK : ℝ) : EReal)
          = ((r0 : ℝ) : EReal) + ((∑ i : Fin m, uStar i * r i : ℝ) : EReal) := by
              simp [rK, EReal.coe_add]
      _ = fenchelConjugate n f0 y0 + ((∑ i : Fin m, uStar i * r i : ℝ) : EReal) := by
            simp [hconj0]
      _ =
          fenchelConjugate n f0 y0 +
            (∑ i : Fin m, ((uStar i : ℝ) : EReal) * ((r i : ℝ) : EReal)) := by
            -- Turn the coerced sum into a sum of coerced products, then add `fenchelConjugate n f0 y0`.
            have hSum :
                (∑ i : Fin m, ((uStar i : ℝ) : EReal) * ((r i : ℝ) : EReal)) =
                  ((∑ i : Fin m, uStar i * r i : ℝ) : EReal) := by
              simpa [EReal.coe_mul] using
                (helperForTheorem_6_30_20_coe_sum_mul_eq_sum_coe_mul (m := m)
                  (a := uStar) (b := r))
            simpa using congrArg (fun t => fenchelConjugate n f0 y0 + t) hSum.symm
      _ =
          fenchelConjugate n f0 y0 +
            (∑ i : Fin m, ((uStar i : ℝ) : EReal) * fenchelConjugate n (f i) (y i)) := by
            refine congrArg (fun t => fenchelConjugate n f0 y0 + t) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hconj i]

  -- Key pointwise estimate: the witnesses produce a global lower bound on `g`.
  have hLower : ∀ x : Fin n → ℝ, ((0 : EReal) - (rK : EReal)) ≤ g x := by
    intro x
    -- First derive the Fenchel–Young bounds `⟪x, y⟫ ≤ f(x) + f*(y)` for `f0` and each `f i`.
    have hFenchel0 : ((x ⬝ᵥ y0 : ℝ) : EReal) ≤ f0 x + fenchelConjugate n f0 y0 := by
      have hsub : ((x ⬝ᵥ y0 : ℝ) : EReal) - f0 x ≤ fenchelConjugate n f0 y0 := by
        unfold fenchelConjugate
        exact le_sSup ⟨x, rfl⟩
      have hx_ne_bot : f0 x ≠ (⊥ : EReal) := hf0.1.1 x
      have h1 : f0 x ≠ (⊥ : EReal) ∨ fenchelConjugate n f0 y0 ≠ ⊤ := Or.inl hx_ne_bot
      have h2 : f0 x ≠ ⊤ ∨ fenchelConjugate n f0 y0 ≠ (⊥ : EReal) := Or.inr hy0_bot
      have hle : ((x ⬝ᵥ y0 : ℝ) : EReal) ≤ fenchelConjugate n f0 y0 + f0 x :=
        (EReal.sub_le_iff_le_add h1 h2).1 hsub
      simpa [add_comm, add_left_comm, add_assoc] using hle
    have hFenchel :
        ∀ i : Fin m,
          ((x ⬝ᵥ y i : ℝ) : EReal) ≤ f i x + fenchelConjugate n (f i) (y i) := by
      intro i
      have hsub : ((x ⬝ᵥ y i : ℝ) : EReal) - f i x ≤ fenchelConjugate n (f i) (y i) := by
        unfold fenchelConjugate
        exact le_sSup ⟨x, rfl⟩
      have hx_ne_bot : f i x ≠ (⊥ : EReal) := (hf i).1.1 x
      have h1 : f i x ≠ (⊥ : EReal) ∨ fenchelConjugate n (f i) (y i) ≠ ⊤ := Or.inl hx_ne_bot
      have h2 : f i x ≠ ⊤ ∨ fenchelConjugate n (f i) (y i) ≠ (⊥ : EReal) := Or.inr (hy_bot i)
      have hle : ((x ⬝ᵥ y i : ℝ) : EReal) ≤ fenchelConjugate n (f i) (y i) + f i x :=
        (EReal.sub_le_iff_le_add h1 h2).1 hsub
      simpa [add_comm, add_left_comm, add_assoc] using hle

    -- Multiply by the nonnegative multipliers and sum.
    have hMul :
        ∀ i : Fin m,
          ((uStar i : ℝ) : EReal) * ((x ⬝ᵥ y i : ℝ) : EReal) ≤
            ((uStar i : ℝ) : EReal) * f i x +
              ((uStar i : ℝ) : EReal) * fenchelConjugate n (f i) (y i) := by
      intro i
      have ha : (0 : EReal) ≤ ((uStar i : ℝ) : EReal) := by
        exact_mod_cast (hnonneg i)
      have hne_top : ((uStar i : ℝ) : EReal) ≠ (⊤ : EReal) := by
        simp
      have hle :
          ((uStar i : ℝ) : EReal) * ((x ⬝ᵥ y i : ℝ) : EReal) ≤
            ((uStar i : ℝ) : EReal) * (f i x + fenchelConjugate n (f i) (y i)) := by
        exact mul_le_mul_of_nonneg_left (hFenchel i) ha
      calc
        ((uStar i : ℝ) : EReal) * ((x ⬝ᵥ y i : ℝ) : EReal)
            ≤
            ((uStar i : ℝ) : EReal) *
              (f i x + fenchelConjugate n (f i) (y i)) := hle
        _ =
            ((uStar i : ℝ) : EReal) * f i x +
              ((uStar i : ℝ) : EReal) * fenchelConjugate n (f i) (y i) := by
              -- Distribute multiplication by a nonnegative finite scalar.
              simpa using
                (EReal.left_distrib_of_nonneg_of_ne_top (x := ((uStar i : ℝ) : EReal))
                  ha hne_top (f i x) (fenchelConjugate n (f i) (y i)))

    have hSumMul :
        (∑ i : Fin m, ((uStar i : ℝ) : EReal) * ((x ⬝ᵥ y i : ℝ) : EReal)) ≤
          ∑ i : Fin m,
            (((uStar i : ℝ) : EReal) * f i x +
              ((uStar i : ℝ) : EReal) * fenchelConjugate n (f i) (y i)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hMul i

    -- Add the `f0` term.
    have hMainIneq :
        ((x ⬝ᵥ y0 : ℝ) : EReal) +
            (∑ i : Fin m, ((uStar i : ℝ) : EReal) * ((x ⬝ᵥ y i : ℝ) : EReal)) ≤
          (f0 x + fenchelConjugate n f0 y0) +
            (∑ i : Fin m,
              (((uStar i : ℝ) : EReal) * f i x +
                ((uStar i : ℝ) : EReal) * fenchelConjugate n (f i) (y i))) := by
      have := add_le_add hFenchel0 hSumMul
      -- Reassociate to match the displayed form.
      simpa [add_assoc] using this

    -- The left-hand side is `0` because `y0 + ∑ᵢ uᵢ* • y i = 0`.
    have hLeftZero :
        ((x ⬝ᵥ y0 : ℝ) : EReal) +
            (∑ i : Fin m, ((uStar i : ℝ) : EReal) * ((x ⬝ᵥ y i : ℝ) : EReal)) = 0 := by
      -- Rewrite the sum of products into a coerced real sum.
      have hSumProd :
          (∑ i : Fin m, ((uStar i : ℝ) : EReal) * ((x ⬝ᵥ y i : ℝ) : EReal)) =
            ((∑ i : Fin m, uStar i * (x ⬝ᵥ y i) : ℝ) : EReal) := by
        simpa using
          (helperForTheorem_6_30_20_coe_sum_mul_eq_sum_coe_mul (m := m)
            (a := uStar) (b := fun i : Fin m => (x ⬝ᵥ y i : ℝ)))
      -- Real dot-product identity coming from `hSum`.
      have hReal :
          (x ⬝ᵥ y0 : ℝ) + (∑ i : Fin m, uStar i * (x ⬝ᵥ y i) : ℝ) =
            x ⬝ᵥ (y0 + ∑ i : Fin m, uStar i • y i) := by
        have h :
            x ⬝ᵥ (y0 + ∑ i : Fin m, uStar i • y i) =
              (x ⬝ᵥ y0) + ∑ i : Fin m, uStar i * (x ⬝ᵥ y i) := by
          calc
            x ⬝ᵥ (y0 + ∑ i : Fin m, uStar i • y i)
                = (x ⬝ᵥ y0) + x ⬝ᵥ (∑ i : Fin m, uStar i • y i) := by
                    simp [dotProduct_add]
            _ = (x ⬝ᵥ y0) + ∑ i : Fin m, uStar i * (x ⬝ᵥ y i) := by
                  simp [dotProduct_sum, dotProduct_smul, smul_eq_mul]
        simpa using h.symm
      have hE :
          (((x ⬝ᵥ y0 : ℝ) + (∑ i : Fin m, uStar i * (x ⬝ᵥ y i) : ℝ)) : EReal) = 0 := by
        calc
          (((x ⬝ᵥ y0 : ℝ) + (∑ i : Fin m, uStar i * (x ⬝ᵥ y i) : ℝ)) : EReal) =
              ((x ⬝ᵥ (y0 + ∑ i : Fin m, uStar i • y i) : ℝ) : EReal) := by
                simpa using congrArg (fun r : ℝ => ((r : ℝ) : EReal)) hReal
          _ = ((x ⬝ᵥ (0 : Fin n → ℝ) : ℝ) : EReal) := by
                simp [hSum]
          _ = 0 := by
                simp
      calc
        ((x ⬝ᵥ y0 : ℝ) : EReal) +
            (∑ i : Fin m, ((uStar i : ℝ) : EReal) * ((x ⬝ᵥ y i : ℝ) : EReal)) =
            ((x ⬝ᵥ y0 : ℝ) : EReal) + ((∑ i : Fin m, uStar i * (x ⬝ᵥ y i) : ℝ) : EReal) := by
              simpa [hSumProd]
        _ =
            (((x ⬝ᵥ y0 : ℝ) + (∑ i : Fin m, uStar i * (x ⬝ᵥ y i) : ℝ)) : EReal) := by
              simp
        _ = 0 := hE

    -- Use `hLeftZero` to turn `hMainIneq` into `0 ≤ g x + rK`.
    have hNonneg :
        (0 : EReal) ≤
          (f0 x + fenchelConjugate n f0 y0) +
            (∑ i : Fin m,
              (((uStar i : ℝ) : EReal) * f i x +
                ((uStar i : ℝ) : EReal) * fenchelConjugate n (f i) (y i))) := by
      have := hMainIneq
      -- Replace the left-hand side by `0`.
      simpa [hLeftZero] using this

    -- Rewrite the right-hand side as `g x + (rK : EReal)`.
    have hRewrite :
        (f0 x + fenchelConjugate n f0 y0) +
            (∑ i : Fin m,
              (((uStar i : ℝ) : EReal) * f i x +
                ((uStar i : ℝ) : EReal) * fenchelConjugate n (f i) (y i))) =
          g x + (rK : EReal) := by
      -- First split the `Finset` sum.
      calc
        (f0 x + fenchelConjugate n f0 y0) +
            (∑ i : Fin m,
              (((uStar i : ℝ) : EReal) * f i x +
                ((uStar i : ℝ) : EReal) * fenchelConjugate n (f i) (y i))) =
            (f0 x + fenchelConjugate n f0 y0) +
              ((∑ i : Fin m, ((uStar i : ℝ) : EReal) * f i x) +
                (∑ i : Fin m, ((uStar i : ℝ) : EReal) * fenchelConjugate n (f i) (y i))) := by
              simp [Finset.sum_add_distrib, add_assoc]
        _ =
            (f0 x + ∑ i : Fin m, ((uStar i : ℝ) : EReal) * f i x) +
              (fenchelConjugate n f0 y0 +
                ∑ i : Fin m, ((uStar i : ℝ) : EReal) * fenchelConjugate n (f i) (y i)) := by
              -- Reassociate and commute.
              abel
        _ = g x + (rK : EReal) := by
              -- Unfold `g` and use `hK`.
              simp [g, ordinaryConvexProgramWeightedObjective, hK, add_assoc]

    -- Conclude `0 - rK ≤ g x` using the `EReal` subtraction lemma.
    have hNonneg' : (0 : EReal) ≤ g x + (rK : EReal) := by
      simpa [hRewrite] using hNonneg
    have hiff :=
      (EReal.sub_le_iff_le_add (a := (0 : EReal)) (b := (rK : EReal)) (c := g x)
        (Or.inl (EReal.coe_ne_bot rK)) (Or.inl (EReal.coe_ne_top rK)))
    exact hiff.2 hNonneg'

  -- With the global lower bound in hand, `sInf (range g)` is above `0 - rK`, hence above `⊥`.
  have hLowerBound : ((0 : EReal) - (rK : EReal)) ≤ sInf (Set.range g) := by
    refine le_sInf ?_
    rintro z ⟨x, rfl⟩
    exact hLower x
  have hbot_lt : (⊥ : EReal) < ((0 : EReal) - (rK : EReal)) := by
    -- `0 - rK = -↑rK = ↑(-rK)`, hence it lies strictly above `⊥`.
    have hsub : ((0 : EReal) - (rK : EReal)) = -((rK : ℝ) : EReal) := by
      simp [sub_eq_add_neg]
    have hneg : -((rK : ℝ) : EReal) = ((-rK : ℝ) : EReal) := by
      simpa using (EReal.coe_neg rK).symm
    rw [hsub, hneg]
    exact EReal.bot_lt_coe (-rK)
  -- Conclude the strict bound by transitivity.
  exact lt_of_lt_of_le hbot_lt hLowerBound

/-- Helper for Theorem 6.30.21: if `uStar ≥ 0` and the (book-style) witness condition holds, then
the weighted objective is bounded below, i.e. `⊥ < sInf (range (ordinaryConvexProgramWeightedObjective ...))`.
This is just the witness lemma with the witnesses packaged as an existential. -/
lemma helperForTheorem_6_30_21_bot_lt_sInf_range_weightedObjective_of_exists_witness_of_nonneg
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexERealFunction (F := (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexERealFunction (F := (Fin n → ℝ)) (f i))
    {uStar : Fin m → ℝ} (hnonneg : ∀ i : Fin m, 0 ≤ uStar i) :
    (∃ y0 : Fin n → ℝ,
        y0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f0) ∧
        ∃ y : Fin m → Fin n → ℝ,
          (∀ i : Fin m,
            y i ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))) ∧
          y0 + ∑ i : Fin m, (uStar i) • y i = 0) →
      (⊥ : EReal) <
          sInf (Set.range fun x : Fin n → ℝ =>
            ordinaryConvexProgramWeightedObjective f0 f uStar x) := by
  -- Unpack the witnesses and invoke the core witness lemma.
  rintro ⟨y0, hy0, y, hy, hSum⟩
  -- This is exactly `helperForTheorem_6_30_21_bot_lt_sInf_range_weightedObjective_of_witness_of_nonneg`.
  simpa using
    (helperForTheorem_6_30_21_bot_lt_sInf_range_weightedObjective_of_witness_of_nonneg
      (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (uStar := uStar) (hnonneg := hnonneg)
      (y0 := y0) hy0 (y := y) hy hSum)

/-- Helper for Theorem 6.30.21: on the dual-feasible branch `uStar ≥ 0`, the witness condition
implies that the Fenchel conjugate of the weighted objective is finite at `0`. -/
lemma helperForTheorem_6_30_21_fenchelConjugate_zero_lt_top_of_witness_of_nonneg
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexERealFunction (F := (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexERealFunction (F := (Fin n → ℝ)) (f i))
    {uStar : Fin m → ℝ} (hnonneg : ∀ i : Fin m, 0 ≤ uStar i)
    {y0 : Fin n → ℝ}
    (hy0 : y0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f0))
    {y : Fin m → Fin n → ℝ}
    (hy : ∀ i : Fin m,
      y i ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i)))
    (hSum : y0 + ∑ i : Fin m, (uStar i) • y i = 0) :
    fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) 0 < (⊤ : EReal) := by
  -- First obtain the strict lower bound `⊥ < sInf (range g)` from the witness lemma.
  have hbot_lt :
      (⊥ : EReal) <
          sInf (Set.range fun x : Fin n → ℝ =>
            ordinaryConvexProgramWeightedObjective f0 f uStar x) := by
    simpa using
      helperForTheorem_6_30_21_bot_lt_sInf_range_weightedObjective_of_witness_of_nonneg
        (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (uStar := uStar)
        (hnonneg := hnonneg) (y0 := y0) hy0 (y := y) hy hSum
  -- Then rewrite the finiteness of the infimum as finiteness of the conjugate at `0`.
  have hiff :
      (⊥ : EReal) <
          sInf (Set.range fun x : Fin n → ℝ =>
            ordinaryConvexProgramWeightedObjective f0 f uStar x) ↔
        fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) 0 < (⊤ : EReal) := by
    simpa using
      (helperForTheorem_6_30_21_bot_lt_sInf_range_iff_fenchelConjugate_zero_lt_top
        (g := ordinaryConvexProgramWeightedObjective f0 f uStar))
  exact hiff.mp hbot_lt

/-- Helper for Theorem 6.30.21: on the dual-feasible branch `uStar ≥ 0`, the existential witness
condition implies that the Fenchel conjugate of the weighted objective is finite at `0`. -/
lemma helperForTheorem_6_30_21_fenchelConjugate_zero_lt_top_of_exists_witness_of_nonneg
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexERealFunction (F := (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexERealFunction (F := (Fin n → ℝ)) (f i))
    {uStar : Fin m → ℝ} (hnonneg : ∀ i : Fin m, 0 ≤ uStar i) :
    (∃ y0 : Fin n → ℝ,
        y0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f0) ∧
        ∃ y : Fin m → Fin n → ℝ,
          (∀ i : Fin m,
            y i ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))) ∧
          y0 + ∑ i : Fin m, (uStar i) • y i = 0) →
      fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) 0 < (⊤ : EReal) := by
  -- Unpack the witnesses and apply the pointwise witness lemma.
  rintro ⟨y0, hy0, y, hy, hSum⟩
  exact
    helperForTheorem_6_30_21_fenchelConjugate_zero_lt_top_of_witness_of_nonneg
      (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (uStar := uStar) (hnonneg := hnonneg)
      (y0 := y0) hy0 (y := y) hy hSum

-- The remaining direction of the witness criterion (finite infimum ⇒ witnesses) is only valid on
-- the dual-feasible branch `uStar ≥ 0`. Since the main theorem quantifies over all multipliers
-- `uStar` (and is refuted by an explicit negative-multiplier counterexample later in this file),
-- we only record the basic scalar-multiplication facts that the intended `uStar ≥ 0` route uses.

/-- Helper for Theorem 6.30.21: multiplying an `EReal` by a positive real scalar preserves the
finiteness predicate `< ⊤`. This is used to identify `dom (λ f)` with `dom f` when `λ > 0`. -/
lemma helperForTheorem_6_30_21_mul_lt_top_iff_of_pos {lam : ℝ} (hlam : 0 < lam) (z : EReal) :
    (((lam : ℝ) : EReal) * z < (⊤ : EReal)) ↔ z < (⊤ : EReal) := by
  -- Split on whether `z` is `⊥`, a real number, or `⊤`.
  have hposE : (0 : EReal) < ((lam : ℝ) : EReal) := by
    exact_mod_cast hlam
  cases z using EReal.rec with
  | bot =>
      -- Positive scalars send `⊥` to `⊥`, so both sides reduce to `⊥ < ⊤`.
      simp [EReal.mul_bot_of_pos, hposE]
  | top =>
      -- Positive scalars send `⊤` to `⊤`, so both sides reduce to `⊤ < ⊤`.
      simp [EReal.mul_top_of_pos, hposE]
  | coe r =>
      -- Any real coercion is strictly below `⊤`, and products of reals stay real.
      constructor
      · intro _h
        exact EReal.coe_lt_top r
      · intro _h
        -- Rewrite the product of coercions as a coercion of the real product.
        simpa [EReal.coe_mul] using (EReal.coe_lt_top (lam * r))

/-- Helper for Theorem 6.30.21: for `λ > 0`, multiplying a function by `(λ : EReal)` does not
change its effective domain on `Set.univ`. -/
lemma helperForTheorem_6_30_21_effectiveDomain_mul_eq_of_pos
    {n : ℕ} (f : (Fin n → ℝ) → EReal) {lam : ℝ} (hlam : 0 < lam) :
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => ((lam : ℝ) : EReal) * f x) =
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
  -- Unfold `effectiveDomain` and use `mul_lt_top_iff_of_pos` pointwise.
  ext x
  simp [effectiveDomain_eq, helperForTheorem_6_30_21_mul_lt_top_iff_of_pos (lam := lam) hlam]

/-- Helper for Theorem 6.30.21: multiplying a proper convex `EReal`-valued function by a
nonnegative scalar preserves proper convexity on `Set.univ`. This packages the scaled terms in
the Section 16 sum theorem for the nonnegative branch `uStar ≥ 0`. -/
lemma helperForTheorem_6_30_21_properConvexFunctionOn_univ_mul_of_nonneg
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := Fin n → ℝ) f)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ((lam : ℝ) : EReal) * f x) := by
  by_cases hzero : lam = 0
  · subst hzero
    have hzero_mul :
        (fun x => ((0 : ℝ) : EReal) * f x) = fun _ : Fin n → ℝ => (0 : EReal) := by
      funext x
      simp
    -- The zero multiple is the constant-zero function, which is proper convex on `univ`.
    refine ⟨?_, ?_, ?_⟩
    · have hconvZero : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (fun _ : Fin n → ℝ => (0 : EReal)) := by
        have hnotbot : ∀ x : Fin n → ℝ, (fun _ : Fin n → ℝ => (0 : EReal)) x ≠ (⊥ : EReal) := by
          intro x
          simp
        refine
          (convexFunctionOn_iff_segment_inequality (C := Set.univ)
            (f := fun _ : Fin n → ℝ => (0 : EReal)) (hC := convex_univ) (hnotbot := ?_)).2 ?_
        · intro x hx
          exact hnotbot x
        · intro x hx y hy t ht0 ht1
          simp
      simpa [hzero_mul] using hconvZero
    · refine ⟨((0 : Fin n → ℝ), (0 : ℝ)), ?_⟩
      have hmem :
          ((0 : ℝ) : EReal) ≥ (fun _ : Fin n → ℝ => (0 : EReal)) (0 : Fin n → ℝ) := by
        simp
      simpa [hzero_mul] using
        (mem_epigraph_univ_iff (f := fun _ : Fin n → ℝ => (0 : EReal))).2 hmem
    · intro x hx
      have hne :
          ((fun x => ((0 : ℝ) : EReal) * f x) x) ≠ (⊥ : EReal) := by
        simp
      simpa [hzero_mul] using hne
  · have hpos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hzero)
    have hscaled : ProperConvexERealFunction (F := Fin n → ℝ)
        (fun x => ((lam : ℝ) : EReal) * f x) := by
      constructor
      · constructor
        intro x
        -- Positive finite scalars preserve the non-`⊥` condition.
        exact ereal_mul_ne_bot_of_pos hpos (hf.1.1 x)
        · rcases hf.1.2 with ⟨x0, hx0_ne_top⟩
          refine ⟨x0, ?_⟩
          have hltTop :
              (((lam : ℝ) : EReal) * f x0) < (⊤ : EReal) := by
            exact
              (helperForTheorem_6_30_21_mul_lt_top_iff_of_pos (lam := lam) hpos (f x0)).2
                  ((lt_top_iff_ne_top).2 hx0_ne_top)
          exact (lt_top_iff_ne_top).1 hltTop
      · intro x y a b ha hb hab
        -- Multiply the original Jensen inequality by the nonnegative scalar `lam`.
        have hconv : ConvexERealFunction f := hf.2
        have hineq := hconv (x := x) (y := y) (a := a) (b := b) ha hb hab
        have hlamE : (0 : EReal) ≤ ((lam : ℝ) : EReal) := by
          exact_mod_cast hlam
        have hlam_ne_top : ((lam : ℝ) : EReal) ≠ (⊤ : EReal) := by
          simp
        calc
          ((lam : ℝ) : EReal) * f (a • x + b • y)
              ≤ ((lam : ℝ) : EReal) *
                  (((a : ℝ) : EReal) * f x + ((b : ℝ) : EReal) * f y) := by
                    exact mul_le_mul_of_nonneg_left hineq hlamE
          _ =
              (((lam : ℝ) : EReal) * (((a : ℝ) : EReal) * f x)) +
                (((lam : ℝ) : EReal) * (((b : ℝ) : EReal) * f y)) := by
                  simpa using
                    (EReal.left_distrib_of_nonneg_of_ne_top
                      (x := ((lam : ℝ) : EReal)) hlamE hlam_ne_top
                      (((a : ℝ) : EReal) * f x) (((b : ℝ) : EReal) * f y))
          _ =
              ((a : ℝ) : EReal) * (((lam : ℝ) : EReal) * f x) +
                ((b : ℝ) : EReal) * (((lam : ℝ) : EReal) * f y) := by
                  simp [mul_assoc, mul_left_comm, mul_comm]
    -- Convert the scaled proper convex `EReal` function back to the `ProperConvexFunctionOn` API.
    exact
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := fun x => ((lam : ℝ) : EReal) * f x) hscaled

-- Route correction: the helper lemmas below were an unfinished attempt at the `uStar ≥ 0` route for
-- the third conjunct of Theorem 6.30.21. Since the main theorem statement is unprovable as written
-- (see the explicit negative-multiplier counterexample below), we disable them until the statement
-- is repaired upstream.

/-- Helper for Theorem 6.30.21: in the one-dimensional quadratic counterexample family, the
right-hand witness condition of the third conjunct is always satisfied by the zero witnesses,
independently of the scalar multiplier `c`. -/
lemma helperForTheorem_6_30_21_zeroWitness_rhs_for_scalarMultiplier :
    let f0 : (Fin 1 → ℝ) → EReal := fun _ => (0 : EReal)
    let f : Fin 1 → (Fin 1 → ℝ) → EReal := fun _ x => (((x 0) ^ 2 : ℝ) : EReal)
    ∀ c : ℝ,
      ∃ y0 : Fin 1 → ℝ,
        y0 ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 f0) ∧
        ∃ y : Fin 1 → Fin 1 → ℝ,
          (∀ i : Fin 1,
            y i ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 (f i))) ∧
          y0 + ∑ i : Fin 1, ((fun _ : Fin 1 => c) i) • y i = 0 := by
  classical
  -- Unfold the concrete functions so the Fenchel-domain checks become explicit.
  dsimp
  -- First place `0` in the effective domain of `f₀*`.
  have hy0_dom :
      (0 : Fin 1 → ℝ) ∈
        effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
          (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal))) := by
    rw [effectiveDomain_eq]
    refine ⟨?_, ?_⟩
    · simp
    have hle :
        fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)) 0 ≤ (0 : EReal) := by
      have hiff :=
        (fenchelConjugate_le_coe_iff_affine_le (n := 1)
          (f := fun _ : Fin 1 → ℝ => (0 : EReal)) (b := (0 : Fin 1 → ℝ)) (μ := (0 : ℝ)))
      refine hiff.2 ?_
      intro x
      simp
    have hltTop : (0 : EReal) < (⊤ : EReal) := by
      simp
    exact lt_of_le_of_lt hle hltTop
  -- The same argument puts `0` in the effective domain of each quadratic conjugate.
  have hy_dom : ∀ i : Fin 1,
      (0 : Fin 1 → ℝ) ∈
        effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
          (fenchelConjugate 1 (fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))) := by
    intro i
    rw [effectiveDomain_eq]
    refine ⟨?_, ?_⟩
    · simp
    have hle :
        fenchelConjugate 1 (fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal)) 0 ≤ (0 : EReal) := by
      have hiff :=
        (fenchelConjugate_le_coe_iff_affine_le (n := 1)
          (f := fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
          (b := (0 : Fin 1 → ℝ)) (μ := (0 : ℝ)))
      refine hiff.2 ?_
      intro x
      have hx : (0 : ℝ) ≤ (x 0) ^ 2 := by
        exact pow_two_nonneg (x 0)
      have hxE : ((0 : ℝ) : EReal) ≤ (((x 0) ^ 2 : ℝ) : EReal) :=
        (EReal.coe_le_coe_iff).2 hx
      simpa using hxE
    have hltTop : (0 : EReal) < (⊤ : EReal) := by
      simp
    exact lt_of_le_of_lt hle hltTop
  intro c
  -- The zero witnesses satisfy the affine balance for every scalar multiplier.
  refine ⟨0, hy0_dom, ?_⟩
  refine ⟨(fun _i => (0 : Fin 1 → ℝ)), ?_, ?_⟩
  · intro i
    simpa using hy_dom i
  · simp

/-- Helper for Theorem 6.30.21: the witness-style finiteness criterion in the third conjunct
cannot quantify over all multipliers `uStar`. A single negative multiplier can make the weighted
objective unbounded below (`sInf = ⊥`) even though the zero vector lies in the effective domains of
each Fenchel conjugate, so the right-hand witness condition holds. -/
lemma helperForTheorem_6_30_21_counterexample_negativeMultiplier :
    let f0 : (Fin 1 → ℝ) → EReal := fun _ => (0 : EReal)
    let f : Fin 1 → (Fin 1 → ℝ) → EReal := fun _ x => (((x 0) ^ 2 : ℝ) : EReal)
    let uStar : Fin 1 → ℝ := fun _ => (-1 : ℝ)
    ¬ ((⊥ : EReal) <
          sInf (Set.range fun x : Fin 1 → ℝ =>
            ordinaryConvexProgramWeightedObjective f0 f uStar x) ↔
        ∃ y0 : Fin 1 → ℝ,
          y0 ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 f0) ∧
          ∃ y : Fin 1 → Fin 1 → ℝ,
            (∀ i : Fin 1,
              y i ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 (f i))) ∧
            y0 + ∑ i : Fin 1, (uStar i) • y i = 0) := by
  classical
  -- Unfold the concrete data so the goal becomes an explicit `¬ (P ↔ Q)`.
  dsimp
  -- First show the RHS holds by invoking the dedicated zero-witness helper at `c = -1`.
  have hRhs :
      ∃ y0 : Fin 1 → ℝ,
        y0 ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal))) ∧
        ∃ y : Fin 1 → Fin 1 → ℝ,
          (∀ i : Fin 1,
            y i ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 (fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal)))) ∧
          (y0 + ∑ i : Fin 1, ((fun _ : Fin 1 => (-1 : ℝ)) i) • y i = 0) := by
    simpa using
      (helperForTheorem_6_30_21_zeroWitness_rhs_for_scalarMultiplier (c := (-1 : ℝ)))
  -- Next show the LHS is false: the weighted objective is `x ↦ -(x 0)^2`, so its infimum is `-∞`.
  have hsInf :
      sInf (Set.range fun x : Fin 1 → ℝ =>
        ordinaryConvexProgramWeightedObjective
          (fun _ : Fin 1 → ℝ => (0 : EReal))
          (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
          (fun _ : Fin 1 => (-1 : ℝ)) x) = (⊥ : EReal) := by
    -- Use the unbounded-below criterion for the infimum in a complete linear order.
    refine (sInf_eq_bot).2 ?_
    intro b hb
    cases b using EReal.rec with
    | bot =>
        -- `b = ⊥` contradicts the hypothesis `⊥ < b`.
        exact False.elim (lt_irrefl (⊥ : EReal) hb)
    | coe r =>
        -- For a real bound `r`, pick `x = (t)` with `-(t^2) < r`.
        let t : ℝ := r - 1
        refine ⟨
          ordinaryConvexProgramWeightedObjective
            (fun _ : Fin 1 → ℝ => (0 : EReal))
            (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
            (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => t), ?_, ?_⟩
        · refine ⟨(fun _ => t), rfl⟩
        · have hg :
              ordinaryConvexProgramWeightedObjective
                  (fun _ : Fin 1 → ℝ => (0 : EReal))
                  (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
                  (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => t) =
                (((-(t ^ 2) : ℝ) : EReal)) := by
            -- Expand the `Fin 1` sum and simplify.
            simp [ordinaryConvexProgramWeightedObjective, Fin.sum_univ_one, t, EReal.coe_mul]
          have ht : (-(t ^ 2) : ℝ) < r := by
            dsimp [t]
            nlinarith
          have htE : (((-(t ^ 2) : ℝ) : EReal)) < ((r : ℝ) : EReal) :=
            (EReal.coe_lt_coe_iff).2 ht
          -- Rewrite the objective value and close the goal with the lifted real inequality.
          rw [hg]
          exact htE
    | top =>
        -- For `b = ⊤`, any real value is strictly below.
        refine ⟨
          ordinaryConvexProgramWeightedObjective
            (fun _ : Fin 1 → ℝ => (0 : EReal))
            (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
            (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => (0 : ℝ)), ?_, ?_⟩
        · refine ⟨(fun _ => (0 : ℝ)), rfl⟩
        · have hg :
              ordinaryConvexProgramWeightedObjective
                  (fun _ : Fin 1 → ℝ => (0 : EReal))
                  (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
                  (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => (0 : ℝ)) =
                (((0 : ℝ) : EReal)) := by
            simp [ordinaryConvexProgramWeightedObjective, Fin.sum_univ_one, EReal.coe_mul]
          -- Rewrite to a real coercion and use the basic bound `↑0 < ⊤`.
          rw [hg]
          simpa using (EReal.coe_lt_top (0 : ℝ))
  have hLhs :
      ¬ ((⊥ : EReal) <
        sInf (Set.range fun x : Fin 1 → ℝ =>
          ordinaryConvexProgramWeightedObjective
            (fun _ : Fin 1 → ℝ => (0 : EReal))
            (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
            (fun _ : Fin 1 => (-1 : ℝ)) x)) := by
    -- If the infimum equals `⊥`, it cannot be strictly larger than `⊥`.
    intro h
    -- Rewrite the hypothesis using the computed infimum, reducing to `⊥ < ⊥`.
    have hTmp := h
    rw [hsInf] at hTmp
    exact (lt_irrefl (⊥ : EReal) hTmp)
  -- Combine `¬LHS` and `RHS` to refute the equivalence.
  intro hiff
  have : (⊥ : EReal) <
      sInf (Set.range fun x : Fin 1 → ℝ =>
        ordinaryConvexProgramWeightedObjective
          (fun _ : Fin 1 → ℝ => (0 : EReal))
          (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
          (fun _ : Fin 1 => (-1 : ℝ)) x) := by
    exact hiff.mpr hRhs
  exact hLhs this

/-- Helper for Theorem 6.30.21: in the one-constraint quadratic example (`f₀ ≡ 0`, `f₁(x)=x^2`),
every *negative* scalar multiplier makes the weighted objective unbounded below (so the infimum is
`⊥`), while the zero witnesses still satisfy the right-hand witness condition. Hence the
witness-style finiteness criterion cannot be quantified over all multipliers. -/
lemma helperForTheorem_6_30_21_counterexample_anyNegativeMultiplier :
    let f0 : (Fin 1 → ℝ) → EReal := fun _ => (0 : EReal)
    let f : Fin 1 → (Fin 1 → ℝ) → EReal := fun _ x => (((x 0) ^ 2 : ℝ) : EReal)
    ∀ c : ℝ, c < 0 →
      ¬ ((⊥ : EReal) <
            sInf (Set.range fun x : Fin 1 → ℝ =>
              ordinaryConvexProgramWeightedObjective f0 f (fun _ : Fin 1 => c) x) ↔
          ∃ y0 : Fin 1 → ℝ,
            y0 ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 f0) ∧
            ∃ y : Fin 1 → Fin 1 → ℝ,
              (∀ i : Fin 1,
                y i ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 (f i))) ∧
              y0 + ∑ i : Fin 1, ((fun _ : Fin 1 => c) i) • y i = 0) := by
  classical
  -- Unfold the concrete data so `f0` and `f` are explicit.
  dsimp
  intro c hcneg

  -- Step 1: invoke the zero-witness helper, which works for every scalar multiplier `c`.
  have hRhs :
      ∃ y0 : Fin 1 → ℝ,
        y0 ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal))) ∧
        ∃ y : Fin 1 → Fin 1 → ℝ,
          (∀ i : Fin 1,
            y i ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 (fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal)))) ∧
          (y0 + ∑ i : Fin 1, ((fun _ : Fin 1 => c) i) • y i = 0) := by
    simpa using (helperForTheorem_6_30_21_zeroWitness_rhs_for_scalarMultiplier (c := c))

  -- Step 2: the LHS is false for `c < 0` because the weighted objective is unbounded below.
  have hsInf :
      sInf (Set.range fun x : Fin 1 → ℝ =>
        ordinaryConvexProgramWeightedObjective
          (fun _ : Fin 1 → ℝ => (0 : EReal))
          (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
          (fun _ : Fin 1 => c) x) = (⊥ : EReal) := by
    -- Use the `sInf = ⊥` criterion: for every `b > ⊥` we can find a point with value `< b`.
    refine (sInf_eq_bot).2 ?_
    intro b hb
    cases b using EReal.rec with
    | bot =>
        -- `b = ⊥` contradicts `⊥ < b`.
        exact False.elim (lt_irrefl (⊥ : EReal) hb)
    | top =>
        -- For `b = ⊤`, any real value is strictly below.
        refine ⟨
          ordinaryConvexProgramWeightedObjective
            (fun _ : Fin 1 → ℝ => (0 : EReal))
            (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
            (fun _ : Fin 1 => c) (fun _ => (0 : ℝ)), ?_, ?_⟩
        · refine ⟨(fun _ => (0 : ℝ)), rfl⟩
        · have hg :
              ordinaryConvexProgramWeightedObjective
                  (fun _ : Fin 1 → ℝ => (0 : EReal))
                  (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
                  (fun _ : Fin 1 => c) (fun _ => (0 : ℝ)) =
                (((0 : ℝ) : EReal)) := by
            simp [ordinaryConvexProgramWeightedObjective, Fin.sum_univ_one, EReal.coe_mul]
          rw [hg]
          simpa using (EReal.coe_lt_top (0 : ℝ))
    | coe r =>
        -- For a real bound `r`, pick a coordinate `t` with `c * t^2 < r`.
        by_cases hr : 0 ≤ r
        · -- If `0 ≤ r`, the choice `t = 1` works since `c < 0 ≤ r`.
          let t : ℝ := 1
          refine ⟨
            ordinaryConvexProgramWeightedObjective
              (fun _ : Fin 1 → ℝ => (0 : EReal))
              (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
              (fun _ : Fin 1 => c) (fun _ => t), ?_, ?_⟩
          · refine ⟨(fun _ => t), rfl⟩
          · have hg :
                ordinaryConvexProgramWeightedObjective
                    (fun _ : Fin 1 → ℝ => (0 : EReal))
                    (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
                    (fun _ : Fin 1 => c) (fun _ => t) =
                  (((c * (t ^ 2) : ℝ) : EReal)) := by
              simp [ordinaryConvexProgramWeightedObjective, Fin.sum_univ_one, t, EReal.coe_mul]
            have ht : (c * (t ^ 2) : ℝ) < r := by
              -- Here `t^2 = 1`, so this is just `c < r`.
              have hc_lt_r : c < r := by
                linarith
              simpa [t] using hc_lt_r
            have htE : (((c * (t ^ 2) : ℝ) : EReal)) < ((r : ℝ) : EReal) :=
              (EReal.coe_lt_coe_iff).2 ht
            rw [hg]
            exact htE
        · -- If `r < 0`, take `t = (-r)/(-c) + 1` so `(-c) * t > -r`, hence `c * t^2 < r`.
          have hrneg : r < 0 := lt_of_not_ge hr
          have hcpos : 0 < (-c) := by linarith
          have hcne : (-c) ≠ 0 := ne_of_gt hcpos
          let t : ℝ := (-r) / (-c) + 1
          refine ⟨
            ordinaryConvexProgramWeightedObjective
              (fun _ : Fin 1 → ℝ => (0 : EReal))
              (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
              (fun _ : Fin 1 => c) (fun _ => t), ?_, ?_⟩
          · refine ⟨(fun _ => t), rfl⟩
          · have hg :
                ordinaryConvexProgramWeightedObjective
                    (fun _ : Fin 1 → ℝ => (0 : EReal))
                    (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
                    (fun _ : Fin 1 => c) (fun _ => t) =
                  (((c * (t ^ 2) : ℝ) : EReal)) := by
              simp [ordinaryConvexProgramWeightedObjective, Fin.sum_univ_one, t, EReal.coe_mul]
            have ht_ge_one : 1 ≤ t := by
              have hdiv_nonneg : 0 ≤ (-r) / (-c) := by
                exact div_nonneg (le_of_lt (neg_pos.mpr hrneg)) (le_of_lt hcpos)
              have : (1 : ℝ) ≤ (-r) / (-c) + 1 := by linarith
              simpa [t] using this
            have h01 : (0 : ℝ) ≤ (1 : ℝ) := by
              norm_num
            have ht_nonneg : 0 ≤ t := le_trans h01 ht_ge_one
            have ht_le_sq : t ≤ t ^ 2 := by
              have : t * 1 ≤ t * t := mul_le_mul_of_nonneg_left ht_ge_one ht_nonneg
              simpa [pow_two] using this
            have hmul_le : (-c) * t ≤ (-c) * (t ^ 2) := by
              have hnonneg : 0 ≤ (-c) := le_of_lt hcpos
              exact mul_le_mul_of_nonneg_left ht_le_sq hnonneg
            have hmul_lt : (-r : ℝ) < (-c) * t := by
              -- Compute `(-c) * t = (-r) + (-c)` and use `0 < (-c)`.
              have hmul' : (-c) * t = (-r) + (-c) := by
                calc
                  (-c) * t = (-c) * ((-r) / (-c) + 1) := by
                    simp [t]
                  _ = (-c) * ((-r) / (-c)) + (-c) * 1 := by
                    simp [mul_add, add_assoc]
                  _ = (-c) * (-r) / (-c) + (-c) := by
                    simpa using (mul_div_assoc (-c) (-r) (-c)).symm
                  _ = (-r) + (-c) := by
                    simpa [mul_assoc] using (mul_div_cancel_left₀ (b := (-r)) (a := (-c)) hcne)
              -- Now `(-r) < (-r) + (-c)`.
              have : (-r : ℝ) < (-r : ℝ) + (-c) := by
                simpa [add_comm, add_left_comm, add_assoc] using (lt_add_of_pos_right (-r) hcpos)
              simpa [hmul'] using this
            have hpos : (-r : ℝ) < (-c) * (t ^ 2) := lt_of_lt_of_le hmul_lt hmul_le
            have ht : (c * (t ^ 2) : ℝ) < r := by
              -- Negate `(-r) < (-c) * t^2` to get `c * t^2 < r`.
              have := neg_lt_neg hpos
              -- `-((-c) * t^2) = c * t^2` and `-(-r) = r`.
              simpa [neg_mul] using this
            have htE : (((c * (t ^ 2) : ℝ) : EReal)) < ((r : ℝ) : EReal) :=
              (EReal.coe_lt_coe_iff).2 ht
            rw [hg]
            exact htE

  have hLhs :
      ¬ ((⊥ : EReal) <
        sInf (Set.range fun x : Fin 1 → ℝ =>
          ordinaryConvexProgramWeightedObjective
            (fun _ : Fin 1 → ℝ => (0 : EReal))
            (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
            (fun _ : Fin 1 => c) x)) := by
    -- If the infimum equals `⊥`, it cannot be strictly larger than `⊥`.
    intro h
    have hTmp := h
    rw [hsInf] at hTmp
    exact (lt_irrefl (⊥ : EReal) hTmp)

  -- Since `RHS` is true and `LHS` is false, the equivalence `LHS ↔ RHS` is impossible.
  intro hiff
  have : (⊥ : EReal) <
      sInf (Set.range fun x : Fin 1 → ℝ =>
        ordinaryConvexProgramWeightedObjective
          (fun _ : Fin 1 → ℝ => (0 : EReal))
          (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
          (fun _ : Fin 1 => c) x) := by
    exact hiff.mpr hRhs
  exact hLhs this

end Section30
end Chap06
