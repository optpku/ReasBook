/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_29

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm SupportFunction

universe u v

section Family

variable {ι : Type u}

/- Proposition 7.12 lies in the chapter's symmetric-hull / support-function / finite
max-absolute-linear domain.

Sampled owner-style declarations:
- mathlib `absConvexHull` and `convexHull_union_neg_eq_absConvexHull`;
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`;
- `ξ[Q]` and `supportFunction_convexHull_eq` in `Chap03/Definition_3_9`.

Best owner abstraction:
- source-facing: the symmetric hull `conv {±aᵢ}` and the finite objective `x ↦ maxᵢ |⟪aᵢ, x⟫|`;
- core/canonical: `absConvexHull ℝ (Set.range a)`, `maxTypeObjective`, and the Chapter 3 support
  function `ξ[Q]`;
- bridge/view: the theorem identifying `conv {±aᵢ}` with `absConvexHull ℝ (Set.range a)` and the
  support-function identity relating the finite max to that canonical hull.

Primitive data:
- a family `a : ι → E`;
- a finite nonempty index type `[Fintype ι] [Nonempty ι]` for the finite max owner.

Derived API:
- the source-facing specialization of mathlib's canonical symmetric-hull bridge
  `convexHull ℝ (Set.range a ∪ Set.range (fun i ↦ -a i)) = absConvexHull ℝ (Set.range a)`;
- the canonical owner evaluation theorem `maxTypeObjective_apply`, specialized to
  `fun i x ↦ |⟪aᵢ, x⟫|`;
- the support-function bridge below.
-/

section Hull

variable {E : Type v} [AddCommGroup E] [Module ℝ E]

/-- The textbook symmetric hull `conv {±aᵢ}` of a family `a` is exactly the canonical absolutely
convex hull of its range. This is the `Set.range` specialization of mathlib's owner theorem
`convexHull_union_neg_eq_absConvexHull`. -/
theorem convexHull_range_union_neg_eq_absConvexHull_range (a : ι → E) :
    convexHull ℝ (Set.range a ∪ Set.range (fun i ↦ -a i)) =
      absConvexHull ℝ (Set.range a) := by
  simpa [Set.neg_range] using
    (convexHull_union_neg_eq_absConvexHull :
      convexHull ℝ (Set.range a ∪ -Set.range a) = absConvexHull ℝ (Set.range a))

end Hull

section Support

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section FiniteFamily

variable [Fintype ι] [Nonempty ι]

/-- Companion bridge: the Chapter 3 support function of the canonical absolutely convex hull
`absConvexHull ℝ (Set.range a)` is exactly the finite max of the absolute pairings. -/
theorem supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner
    (a : ι → E) (x : E) :
    (ξ[absConvexHull ℝ (Set.range a)] x).toReal =
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  classical
  -- Rewrite the absolutely convex hull through the textbook symmetric hull `conv {±aᵢ}`.
  rw [← convexHull_range_union_neg_eq_absConvexHull_range, supportFunction_convexHull_eq]
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ |inner ℝ (a i) x|)
  have hupper : ξ[Set.range a ∪ Set.range (fun i ↦ -a i)] x ≤ (M : EReal) := by
    -- Every generator `aᵢ` or `-aᵢ` contributes at most the finite max `M`.
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with hy | hy
    · rcases hy with ⟨i, rfl⟩
      have hi_le : |inner ℝ (a i) x| ≤ M := by
        exact Finset.le_sup' (fun j : ι ↦ |inner ℝ (a j) x|) (by simp)
      have hinner_le : inner ℝ (a i) x ≤ M := by
        exact le_trans (le_abs_self (inner ℝ (a i) x)) hi_le
      exact (show (((inner ℝ (a i) x : ℝ) : EReal) ≤ (M : EReal)) by
        exact_mod_cast hinner_le)
    · rcases hy with ⟨i, rfl⟩
      have hi_le : |inner ℝ (a i) x| ≤ M := by
        exact Finset.le_sup' (fun j : ι ↦ |inner ℝ (a j) x|) (by simp)
      have hneg_le : -inner ℝ (a i) x ≤ M := by
        exact le_trans (neg_le_abs (inner ℝ (a i) x)) hi_le
      simpa using (show (((-inner ℝ (a i) x : ℝ) : EReal) ≤ (M : EReal)) by
        exact_mod_cast hneg_le)
  have hlower : (M : EReal) ≤ ξ[Set.range a ∪ Set.range (fun i ↦ -a i)] x := by
    -- Choose an index attaining `M` and then pick the sign whose pairing is positive.
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) x|)
    by_cases hsign : 0 ≤ inner ℝ (a i) x
    · rw [supportFunction_apply]
      calc
        (M : EReal) = (((|inner ℝ (a i) x| : ℝ) : EReal)) := by
          exact_mod_cast hi
        _ = (((inner ℝ (a i) x : ℝ) : EReal)) := by
          exact_mod_cast (abs_of_nonneg hsign)
        _ ≤ sSup ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) ''
              (Set.range a ∪ Set.range (fun i ↦ -a i))) := by
          exact le_sSup ⟨a i, Or.inl (Set.mem_range_self i), rfl⟩
    · rw [supportFunction_apply]
      calc
        (M : EReal) = (((|inner ℝ (a i) x| : ℝ) : EReal)) := by
          exact_mod_cast hi
        _ = (((inner ℝ (-a i) x : ℝ) : EReal)) := by
          have habs :
              |inner ℝ (a i) x| = inner ℝ (-a i) x := by
            calc
              |inner ℝ (a i) x| = -inner ℝ (a i) x := by
                exact abs_of_nonpos (le_of_not_ge hsign)
              _ = inner ℝ (-a i) x := by simp
          exact_mod_cast habs
        _ ≤ sSup ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) ''
              (Set.range a ∪ Set.range (fun i ↦ -a i))) := by
          exact le_sSup ⟨-a i, Or.inr (Set.mem_range_self i), rfl⟩
  have hξ : ξ[Set.range a ∪ Set.range (fun i ↦ -a i)] x = (M : EReal) :=
    le_antisymm hupper hlower
  have hM : M = maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
    rw [maxTypeObjective_apply]
  calc
    (ξ[Set.range a ∪ Set.range (fun i ↦ -a i)] x).toReal = M := by
      simpa using congrArg EReal.toReal hξ
    _ = maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := hM

/-- Proposition 7.12 (2): the support function of the symmetric hull `conv {±aᵢ}` is exactly the
finite maximum of the absolute pairings `maxᵢ |⟪aᵢ, x⟫|`. -/
theorem supportFunction_convexHull_range_union_neg_toReal_eq_maxTypeObjective_absInner
    (a : ι → E) (x : E) :
    (ξ[convexHull ℝ (Set.range a ∪ Set.range fun i : ι ↦ -a i)] x).toReal =
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  simpa [convexHull_range_union_neg_eq_absConvexHull_range] using
    supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner a x

end FiniteFamily

end Support

end Family

section Ellipsoid

variable {m : ℕ+} {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Proposition 7.12: the inverse matrix cancels the original Euclidean linear action
of a positive-definite matrix. -/
private theorem nonsing_inv_toEuclideanLin_comp
    (G : Mat) (hG : G.PosDef) (x : E) :
    (G⁻¹).toEuclideanLin (G.toEuclideanLin x) = x := by
  -- Convert the Euclidean action back to `mulVec` and use the inverse identity.
  have hGdet : IsUnit G.det := isUnit_iff_ne_zero.mpr (ne_of_gt hG.det_pos)
  have hmul : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGdet
  ext i
  simp [Matrix.mulVec_mulVec, hmul]

/-- Helper for Proposition 7.12: the inner centered ellipsoid contains a point whose pairing
with `x` realizes the primal `G`-norm of `x`. -/
private theorem exists_inner_ellipsoid_point_attaining_positiveDefMatrixNorm
    {G : Mat} (hG : G.PosDef) (x : E) :
    ∃ y : E, y ∈ W[1](G) ∧ inner ℝ y x = ‖x‖[⟨G, hG⟩] := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    -- The origin belongs to every centered ellipsoid and realizes the zero norm.
    · rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hG]
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
      simp
    · simp [hx]
  · let G' : {G : Mat // G.PosDef} := ⟨G, hG⟩
    let p : ℝ := ‖x‖[G']
    let y : E := p⁻¹ • G.toEuclideanLin x
    have hp_pos : 0 < p := by
      dsimp [p]
      exact Seminorm.map_pos_of_ne_zero (positiveDefMatrixNorm G hG) hx
    have hquadratic_nonneg : 0 ≤ inner ℝ (G.toEuclideanLin x) x := by
      have hPosLin : G.toEuclideanLin.IsPositive :=
        Matrix.isPositive_toEuclideanLin_iff.mpr hG.posSemidef
      simpa [real_inner_comm] using hPosLin.inner_nonneg_right x
    have hp_sq : p ^ (2 : ℕ) = inner ℝ (G.toEuclideanLin x) x := by
      dsimp [p]
      rw [positiveDefMatrixNorm_def G' x, Real.sq_sqrt hquadratic_nonneg]
    have hy_inv : (G⁻¹).toEuclideanLin y = p⁻¹ • x := by
      -- The inverse action collapses the `G` factor in the explicit support witness.
      dsimp [y]
      rw [LinearMap.map_smul, nonsing_inv_toEuclideanLin_comp G hG x]
    refine ⟨y, ?_, ?_⟩
    · rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hG]
      have hunit :
          p⁻¹ * (p⁻¹ * inner ℝ (G.toEuclideanLin x) x) = 1 := by
        rw [← hp_sq, pow_two]
        field_simp [hp_pos.ne']
      have hy_dual : ‖y‖[G',*] = 1 := by
        rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
        calc
          Real.sqrt (inner ℝ y ((G⁻¹).toEuclideanLin y)) =
              Real.sqrt (p⁻¹ * (p⁻¹ * inner ℝ (G.toEuclideanLin x) x)) := by
                rw [hy_inv]
                dsimp [y]
                rw [real_inner_smul_left, real_inner_smul_right]
          _ = Real.sqrt 1 := by rw [hunit]
          _ = 1 := by simp
      simpa [G'] using hy_dual.le
    · -- The same normalization makes the pairing with `x` equal to the primal `G`-norm.
      calc
        inner ℝ y x = p⁻¹ * inner ℝ (G.toEuclideanLin x) x := by
          dsimp [y]
          rw [real_inner_smul_left]
        _ = p⁻¹ * p ^ (2 : ℕ) := by rw [hp_sq]
        _ = p := by
          rw [pow_two]
          field_simp [hp_pos.ne']
        _ = ‖x‖[G'] := by rfl

/-- Helper for Proposition 7.12: the support function of `absConvexHull ℝ (Set.range a)` is never
`⊥` because the absolutely convex hull always contains the origin. -/
private theorem supportFunction_absConvexHull_range_ne_bot
    (a : Fin (m : ℕ) → E) (x : E) :
    ξ[absConvexHull ℝ (Set.range a)] x ≠ ⊥ := by
  intro hbot
  have hzero_le : ((0 : ℝ) : EReal) ≤ ξ[absConvexHull ℝ (Set.range a)] x := by
    -- Insert the origin into the support supremum to rule out `⊥`.
    rw [supportFunction_apply]
    exact le_sSup ⟨0, zero_mem_absConvexHull, by simp⟩
  rw [hbot] at hzero_le
  exact (not_le_of_gt (EReal.bot_lt_coe 0)) hzero_le

/-- Helper for Proposition 7.12: the outer ellipsoid of a rounding controls the support value of
`absConvexHull ℝ (Set.range a)` by `γ √n ‖x‖_G`. -/
private theorem supportFunction_absConvexHull_range_ereal_upper_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G) :
    ξ[absConvexHull ℝ (Set.range a)] x ≤
      (γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] : EReal) := by
  let G' : {G : Mat // G.PosDef} := ⟨G, hrounding.posDef⟩
  have hnorm_nonneg : 0 ≤ ‖x‖[G'] := by
    positivity
  -- The outer ellipsoid controls every support point through the dual-pairing estimate.
  rw [supportFunction_apply]
  refine sSup_le ?_
  rintro _ ⟨y, hyC, rfl⟩
  have hy_outer : y ∈ W[(γ * Real.sqrt (n : ℝ))](G) :=
    hrounding.subset_outer_ellipsoid hyC
  have hy_dual : ‖y‖[G',*] ≤ γ * Real.sqrt (n : ℝ) := by
    rwa [mem_centeredMatrixEllipsoid_iff_dualNorm_le hrounding.posDef] at hy_outer
  calc
    ((inner ℝ y x : ℝ) : EReal) ≤ ((‖y‖[G',*] * ‖x‖[G'] : ℝ) : EReal) := by
      exact_mod_cast
        (Seminorm.inner_le_dualNorm_mul (positiveDefMatrixNorm G hrounding.posDef) x y)
    _ ≤ ((γ * Real.sqrt (n : ℝ) * ‖x‖[G'] : ℝ) : EReal) := by
      exact_mod_cast (mul_le_mul_of_nonneg_right hy_dual hnorm_nonneg)
    _ = (γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] : EReal) := by
      simp [G']

-- Proof sketch: Proposition 7.12 is the support-function sandwich induced by the centered
-- ellipsoidal-rounding owner, then rewritten through the symmetric-hull bridge
-- `convexHull_range_union_neg_eq_absConvexHull_range`.
/-- Companion bridge: the lower ellipsoidal bound written for the canonical absolutely convex hull
`absConvexHull ℝ (Set.range a)`. -/
theorem ellipsoidalNorm_le_maxTypeObjective_absInner_of_ellipsoidal_rounding_absConvexHull
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G) :
    ‖x‖[⟨G, hrounding.posDef⟩] ≤ maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  let G' : {G : Mat // G.PosDef} := ⟨G, hrounding.posDef⟩
  have hsupport_ereal_upper :
      ξ[absConvexHull ℝ (Set.range a)] x ≤
        (γ * Real.sqrt (n : ℝ) * ‖x‖[G'] : EReal) :=
    supportFunction_absConvexHull_range_ereal_upper_of_ellipsoidal_rounding a x hrounding
  have hsupport_ne_top : ξ[absConvexHull ℝ (Set.range a)] x ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hsupport_ereal_upper
  rcases exists_inner_ellipsoid_point_attaining_positiveDefMatrixNorm hrounding.posDef x with
    ⟨y, hy_unit, hy_inner⟩
  have hy_hull : y ∈ absConvexHull ℝ (Set.range a) := hrounding.unit_ellipsoid_subset hy_unit
  have hy_le : ((‖x‖[G'] : ℝ) : EReal) ≤ ξ[absConvexHull ℝ (Set.range a)] x := by
    -- The inner ellipsoid witness contributes the exact primal norm to the support supremum.
    rw [supportFunction_apply]
    simpa [hy_inner] using
      (le_sSup
        ⟨y, hy_hull, rfl⟩ :
          (((inner ℝ y x : ℝ) : EReal)) ≤
            sSup ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) ''
              absConvexHull ℝ (Set.range a)))
  have hmain :
      ‖x‖[G'] ≤ (ξ[absConvexHull ℝ (Set.range a)] x).toReal := by
    exact EReal.toReal_le_toReal hy_le (EReal.coe_ne_bot _) hsupport_ne_top
  rw [supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner] at hmain
  simpa [G'] using hmain

/-- Proposition 7.12 (1): if the symmetric hull `conv {±aᵢ}` admits a `γ √n`-ellipsoidal
rounding with shape matrix `G`, then `maxᵢ |⟪aᵢ, x⟫|` bounds the `G`-norm of `x` from below. -/
theorem ellipsoidalNorm_le_maxTypeObjective_absInner_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding :
      IsEllipsoidalRounding
        (convexHull ℝ (Set.range a ∪ Set.range fun i : Fin (m : ℕ) ↦ -a i)) γ G) :
    ‖x‖[⟨G, hrounding.posDef⟩] ≤ maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  have hrounding' : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G := by
    simpa [convexHull_range_union_neg_eq_absConvexHull_range] using hrounding
  simpa using
    ellipsoidalNorm_le_maxTypeObjective_absInner_of_ellipsoidal_rounding_absConvexHull a x
      hrounding'

/- Proposition 7.12 (2) is exactly
`supportFunction_convexHull_range_union_neg_toReal_eq_maxTypeObjective_absInner`. -/

-- Proof sketch: combine the support-function identity
-- `supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner` with the outer
-- inclusion from `hrounding`, then evaluate the support function of the centered ellipsoid
-- `W[(γ * √n)](G)` via the dual norm `‖·‖[⟨G, hrounding.posDef⟩]`.
/-- Companion bridge: the upper ellipsoidal bound written for the canonical absolutely convex hull
`absConvexHull ℝ (Set.range a)`. -/
theorem maxTypeObjective_absInner_le_of_ellipsoidal_rounding_absConvexHull
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x ≤
      γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] := by
  have hsupport_nonbot :
      ξ[absConvexHull ℝ (Set.range a)] x ≠ ⊥ :=
    supportFunction_absConvexHull_range_ne_bot a x
  have hsupport_ereal_upper :
      ξ[absConvexHull ℝ (Set.range a)] x ≤
        (γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] : EReal) :=
    supportFunction_absConvexHull_range_ereal_upper_of_ellipsoidal_rounding a x hrounding
  -- Convert the `EReal` upper bound back to a real inequality and rewrite the support value.
  have hmain :
      (ξ[absConvexHull ℝ (Set.range a)] x).toReal ≤
        γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] := by
    exact EReal.toReal_le_toReal hsupport_ereal_upper hsupport_nonbot (EReal.coe_ne_top _)
  rw [supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner] at hmain
  exact hmain

/-- Proposition 7.12 (3): if the symmetric hull `conv {±aᵢ}` admits a `γ √n`-ellipsoidal
rounding with shape matrix `G`, then `maxᵢ |⟪aᵢ, x⟫|` is bounded above by `γ √n ‖x‖_G`. -/
theorem maxTypeObjective_absInner_le_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding :
      IsEllipsoidalRounding
        (convexHull ℝ (Set.range a ∪ Set.range fun i : Fin (m : ℕ) ↦ -a i)) γ G) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x ≤
      γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] := by
  have hrounding' : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G := by
    simpa [convexHull_range_union_neg_eq_absConvexHull_range] using hrounding
  simpa using
    maxTypeObjective_absInner_le_of_ellipsoidal_rounding_absConvexHull a x hrounding'

/-- Companion bridge: the support function of `absConvexHull ℝ (Set.range a)` satisfies the same
upper bound because it is exactly the finite max of the absolute pairings in real form. -/
theorem supportFunction_absConvexHull_range_le_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G) :
    (ξ[absConvexHull ℝ (Set.range a)] x).toReal ≤
      γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] := by
  rw [supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner]
  exact maxTypeObjective_absInner_le_of_ellipsoidal_rounding_absConvexHull a x hrounding

-- Proof sketch: each generator `a_i` belongs to the symmetric hull `conv {±aᵢ}`, so the outer
-- inclusion from `hrounding` places `a_i` inside `W[(γ * √n)](G)`. Rewriting membership in this
-- centered ellipsoid by `mem_centeredMatrixEllipsoid_iff_dualNorm_le` gives the claimed
-- dual-norm bound.
/-- Each generator `a_i` lies in the outer centered ellipsoid coming from the rounding
hypothesis. Equivalently, its `G`-dual norm is at most `γ √n`. -/
theorem generator_ellipsoidalDualNorm_le_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (i : Fin (m : ℕ))
    (hrounding :
      IsEllipsoidalRounding
        (convexHull ℝ (Set.range a ∪ Set.range fun j : Fin (m : ℕ) ↦ -a j)) γ G) :
    ‖a i‖[⟨G, hrounding.posDef⟩,*] ≤ γ * Real.sqrt (n : ℝ) := by
  have hrounding' : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G := by
    simpa [convexHull_range_union_neg_eq_absConvexHull_range] using hrounding
  have hai_mem : a i ∈ absConvexHull ℝ (Set.range a) := by
    exact subset_absConvexHull (Set.mem_range_self i)
  have hai_outer : a i ∈ W[(γ * Real.sqrt (n : ℝ))](G) :=
    hrounding'.subset_outer_ellipsoid hai_mem
  -- Rewrite outer-ellipsoid membership as the dual-norm inequality.
  rwa [mem_centeredMatrixEllipsoid_iff_dualNorm_le hrounding'.posDef] at hai_outer

end Ellipsoid

end
