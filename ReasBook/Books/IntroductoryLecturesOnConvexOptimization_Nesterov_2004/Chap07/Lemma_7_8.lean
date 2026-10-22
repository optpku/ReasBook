/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_29
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_35
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm SupportFunction SymmetricBox

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 7.8 lies in Chapter 7's orthant-box / support-function / diagonal-ellipsoid domain.

Sampled owner-style declarations:
- `ξ[Q]` and `supportFunction_convexHull_eq` in `Chap03/Definition_3_9`, the chapter owner for
  support functions;
- `supportFunction_range_toReal_eq_sSup_inner` in `Chap07/Lemma_7_1`, the finite-range support
  function bridge already available upstream for families `a : Fin m → Eₙ`;
- `signSymmetricConvexHull` in `Chap07/Definition_7_35`, the source-facing Chapter 7 owner for
  the box hull `convexHull ℝ (⋃ i, B(a i))`;
- `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` in
  `Chap01/Definition_1_10_2`, the canonical orthant owner;
- `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, the centered-rounding owner packaging the
  unit and outer ellipsoid containments together with positive definiteness.

Best owner abstraction:
- source-facing: the box hull owner `signSymmetricConvexHull a`;
- core/canonical: `ξ[Q]`, `nonnegativeOrthant`, `IsEllipsoidalRounding`, and the
  positive-definite norm owner `‖x‖[G]`;
- bridge/view: the orthant-restricted identification of `ξ[signSymmetricConvexHull a]` with the
  finite-range support function `ξ[Set.range a]`.

Primitive data:
- a family `a : Fin m → Eₙ`.

Derived API:
- the orthant bridge from the source-facing box-hull owner to the canonical finite-range support
  function;
- the centered rounding datum `IsEllipsoidalRounding (signSymmetricConvexHull a) γ D`;
- the support-function sandwich theorem below, derived from that owner.

Source/core/bridge triage:
- source-facing: the two theorems below about `signSymmetricConvexHull a`;
- core/canonical: `IsEllipsoidalRounding`;
- bridge/view: passing from `hrounding : IsEllipsoidalRounding (signSymmetricConvexHull a) γ D`
  to the inner/outer containments with `hrounding.unit_ellipsoid_subset` and
  `hrounding.subset_outer_ellipsoid`.

This refinement deletes the raw-set duplication in the public theorem surface. The box hull is now
named by its Chapter 7 owner `signSymmetricConvexHull`, and the main sandwich theorem is stated
through the centered-rounding owner `IsEllipsoidalRounding` instead of keeping its fields as
parallel hypotheses.
-/

/-- On the nonnegative orthant, the support function of the symmetric box `B(a)` with nonnegative
generator `a` is the linear form `x ↦ ⟪a, x⟫`. -/
theorem supportFunction_symmetricBox_toReal_eq_inner_of_mem_nonnegativeOrthant
    {a x : Eₙ} (ha : a ∈ nonnegativeOrthant n) (hx : x ∈ nonnegativeOrthant n) :
    (ξ[(B(a))] x).toReal = inner ℝ a x := by
  -- Compare every point of the box with the top corner `a` coordinatewise on `ℝⁿ_+`.
  have hupper : ξ[B(a)] x ≤ (inner ℝ a x : EReal) := by
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨s, hs, rfl⟩
    have hs_le : ∀ i : Fin n, s i * x i ≤ a i * x i := by
      intro i
      exact mul_le_mul_of_nonneg_right (hs i).2 (by simpa using hx i)
    have hinner_le : inner ℝ s x ≤ inner ℝ a x := by
      rw [PiLp.inner_apply, PiLp.inner_apply]
      refine Finset.sum_le_sum ?_
      intro i hi
      calc
        x.ofLp i * s.ofLp i = s.ofLp i * x.ofLp i := by ring
        _ ≤ a.ofLp i * x.ofLp i := hs_le i
        _ = inner ℝ (a.ofLp i) (x.ofLp i) := by
          simpa using (RCLike.inner_apply' (x := a.ofLp i) (y := x.ofLp i)).symm
    change (((inner ℝ s x : ℝ) : EReal) ≤ (inner ℝ a x : EReal))
    exact_mod_cast hinner_le
  have ha_box : a ∈ B(a) := by
    -- The nonnegative generator `a` is itself the upper corner of its symmetric box.
    intro i
    constructor
    · have hai_nonneg : 0 ≤ a i := by
        simpa using ha i
      linarith
    · exact le_rfl
  have hlower : (inner ℝ a x : EReal) ≤ ξ[B(a)] x := by
    -- Insert the corner `a` into the support-function supremum.
    rw [supportFunction_apply]
    exact le_sSup ⟨a, ha_box, rfl⟩
  have hξ : ξ[B(a)] x = (inner ℝ a x : EReal) := le_antisymm hupper hlower
  -- Convert the extended-real identity back to the real-valued support formula.
  simpa using congrArg EReal.toReal hξ

/-- Helper for Lemma 7.8: each generator belongs to its Chapter 7 sign-symmetric box hull. -/
private theorem generator_mem_signSymmetricConvexHull
    (a : Fin m → Eₙ) (ha_nonneg : ∀ i : Fin m, a i ∈ nonnegativeOrthant n)
    (i : Fin m) :
    a i ∈ signSymmetricConvexHull a := by
  -- The generator lies in its own coordinate box, hence in the convex hull of their union.
  rw [signSymmetricConvexHull_def]
  refine subset_convexHull ℝ _ ?_
  refine Set.mem_iUnion.mpr ?_
  refine ⟨i, ?_⟩
  intro j
  constructor
  · have haij_nonneg : 0 ≤ a i j := by
      simpa using ha_nonneg i j
    linarith
  · exact le_rfl

/-- On the nonnegative orthant, the support function of the Chapter 7 box-hull owner
`signSymmetricConvexHull a` agrees with the canonical finite-range support function
`ξ[Set.range a]`. -/
theorem supportFunction_signSymmetricConvexHull_eq_range_on_nonnegativeOrthant
    (a : Fin m → Eₙ) (ha_nonneg : ∀ i : Fin m, a i ∈ nonnegativeOrthant n)
    {x : Eₙ} (hx : x ∈ nonnegativeOrthant n) :
    (ξ[signSymmetricConvexHull a] x).toReal = (ξ[Set.range a] x).toReal := by
  classical
  by_cases hm : Nonempty (Fin m)
  · let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m ↦ inner ℝ (a i) x)
    -- First identify the box-hull support value with the attained finite maximum `M`.
    have hupper : ξ[signSymmetricConvexHull a] x ≤ (M : EReal) := by
      rw [signSymmetricConvexHull_def, supportFunction_convexHull_eq, supportFunction_apply]
      refine sSup_le ?_
      rintro _ ⟨y, hy, rfl⟩
      rcases Set.mem_iUnion.mp hy with ⟨i, hyi⟩
      have hyi_le : inner ℝ y x ≤ inner ℝ (a i) x := by
        have hcoord_le : ∀ j : Fin n, y j * x j ≤ a i j * x j := by
          intro j
          exact mul_le_mul_of_nonneg_right (hyi j).2 (by simpa using hx j)
        rw [PiLp.inner_apply, PiLp.inner_apply]
        refine Finset.sum_le_sum ?_
        intro j hj
        calc
          x.ofLp j * y.ofLp j = y.ofLp j * x.ofLp j := by ring
          _ ≤ (a i).ofLp j * x.ofLp j := hcoord_le j
          _ = inner ℝ ((a i).ofLp j) (x.ofLp j) := by
            simpa using (RCLike.inner_apply' (x := (a i).ofLp j) (y := x.ofLp j)).symm
      calc
        ((inner ℝ y x : ℝ) : EReal) ≤ ((inner ℝ (a i) x : ℝ) : EReal) := by
          exact_mod_cast hyi_le
        _ ≤ (M : EReal) := by
          exact_mod_cast
            (Finset.le_sup'_of_le (fun j : Fin m ↦ inner ℝ (a j) x)
              (by simp : i ∈ Finset.univ) le_rfl)
    have hlower : (M : EReal) ≤ ξ[signSymmetricConvexHull a] x := by
      -- The maximizing generator contributes a point of the hull with support value `M`.
      obtain ⟨i, -, hi⟩ :=
        Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : Fin m ↦ inner ℝ (a j) x)
      rw [supportFunction_apply]
      have hai_le :
          (((inner ℝ (a i) x : ℝ) : EReal)) ≤
            sSup ((fun g : Eₙ ↦ ((inner ℝ g x : ℝ) : EReal)) '' signSymmetricConvexHull a) :=
        le_sSup ⟨a i, generator_mem_signSymmetricConvexHull a ha_nonneg i, rfl⟩
      have hM : (M : EReal) = (((inner ℝ (a i) x : ℝ) : EReal)) := by
        exact_mod_cast hi
      calc
        (M : EReal) = (((inner ℝ (a i) x : ℝ) : EReal)) := hM
        _ ≤ sSup ((fun g : Eₙ ↦ ((inner ℝ g x : ℝ) : EReal)) '' signSymmetricConvexHull a) :=
          hai_le
    have hξ : ξ[signSymmetricConvexHull a] x = (M : EReal) := le_antisymm hupper hlower
    have hM :
        M = sSup (Set.range fun i : Fin m ↦ inner ℝ (a i) x) := by
      simpa [M] using
        (Finset.sup'_eq_csSup_image Finset.univ Finset.univ_nonempty
          (fun i : Fin m ↦ inner ℝ (a i) x))
    -- Then rewrite the same finite maximum through the canonical range support function.
    calc
      (ξ[signSymmetricConvexHull a] x).toReal = M := by
        simpa using congrArg EReal.toReal hξ
      _ = sSup (Set.range fun i : Fin m ↦ inner ℝ (a i) x) := hM
      _ = (ξ[Set.range a] x).toReal := by
        symm
        simpa using supportFunction_range_toReal_eq_sSup_inner (a := a) (x := x)
  · let hEmpty : IsEmpty (Fin m) := not_nonempty_iff.mp hm
    have hunion : (⋃ i : Fin m, B((a i))) = (∅ : Set Eₙ) := by
      ext y
      constructor
      · intro hy
        rcases Set.mem_iUnion.mp hy with ⟨i, _⟩
        exact (hEmpty.false i).elim
      · simp
    have hrange :
        Set.range (fun i : Fin m ↦ inner ℝ (a i) x) = (∅ : Set ℝ) := by
      ext t
      constructor
      · rintro ⟨i, rfl⟩
        exact (hEmpty.false i).elim
      · simp
    -- In the empty-family case both support functions collapse to the empty supremum.
    rw [signSymmetricConvexHull_def, supportFunction_convexHull_eq, supportFunction_apply, hunion,
      supportFunction_range_toReal_eq_sSup_inner (a := a) (x := x), hrange]
    simp

/-- Helper for Lemma 7.8: the inverse matrix cancels the original Euclidean linear action. -/
private theorem nonsing_inv_toEuclideanLin_comp
    (D : Matₙ) (hD : D.PosDef) (x : Eₙ) :
    (D⁻¹).toEuclideanLin (D.toEuclideanLin x) = x := by
  -- Convert the Euclidean action back to `mulVec` and use the inverse identity.
  have hDdet : IsUnit D.det := isUnit_iff_ne_zero.mpr (ne_of_gt hD.det_pos)
  have hmul : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hDdet
  ext i
  simp [Matrix.mulVec_mulVec, hmul]

/-- Helper for Lemma 7.8: the inner unit ellipsoid contains a support point realizing the
`D`-primal norm of `x`. -/
private theorem exists_inner_ellipsoid_point_attaining_positiveDefMatrixNorm
    {D : Matₙ} (hD : D.PosDef) (x : Eₙ) :
    ∃ y : Eₙ, y ∈ W[1](D) ∧ inner ℝ y x = ‖x‖[⟨D, hD⟩] := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    -- The zero vector belongs to every centered ellipsoid and realizes the zero norm.
    · rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hD]
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
      simp
    · simp [hx]
  · let G : {G : Matₙ // G.PosDef} := ⟨D, hD⟩
    let p : ℝ := ‖x‖[G]
    let y : Eₙ := p⁻¹ • D.toEuclideanLin x
    have hp_pos : 0 < p := by
      dsimp [p]
      exact Seminorm.map_pos_of_ne_zero (positiveDefMatrixNorm D hD) hx
    have hquadratic_nonneg : 0 ≤ inner ℝ (D.toEuclideanLin x) x := by
      have hPosLin : D.toEuclideanLin.IsPositive :=
        Matrix.isPositive_toEuclideanLin_iff.mpr hD.posSemidef
      simpa [real_inner_comm] using hPosLin.inner_nonneg_right x
    have hp_sq : p ^ (2 : ℕ) = inner ℝ (D.toEuclideanLin x) x := by
      dsimp [p]
      rw [positiveDefMatrixNorm_def G x, Real.sq_sqrt hquadratic_nonneg]
    have hy_inv : (D⁻¹).toEuclideanLin y = p⁻¹ • x := by
      -- The inverse action collapses the `D` factor in the explicit support witness.
      dsimp [y]
      rw [LinearMap.map_smul, nonsing_inv_toEuclideanLin_comp D hD x]
    refine ⟨y, ?_, ?_⟩
    · rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hD]
      have hunit :
          p⁻¹ * (p⁻¹ * inner ℝ (D.toEuclideanLin x) x) = 1 := by
        rw [← hp_sq, pow_two]
        field_simp [hp_pos.ne']
      have hy_dual : ‖y‖[G,*] = 1 := by
        rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
        calc
          Real.sqrt (inner ℝ y ((D⁻¹).toEuclideanLin y))
              = Real.sqrt (p⁻¹ * (p⁻¹ * inner ℝ (D.toEuclideanLin x) x)) := by
                  rw [hy_inv]
                  dsimp [y]
                  rw [real_inner_smul_left, real_inner_smul_right]
          _ = Real.sqrt 1 := by rw [hunit]
          _ = 1 := by simp
      simpa [G] using hy_dual.le
    · -- The same normalization makes the pairing with `x` equal to the primal `D`-norm.
      calc
        inner ℝ y x = p⁻¹ * inner ℝ (D.toEuclideanLin x) x := by
          dsimp [y]
          rw [real_inner_smul_left]
        _ = p⁻¹ * p ^ (2 : ℕ) := by rw [hp_sq]
        _ = p := by
          rw [pow_two]
          field_simp [hp_pos.ne']
        _ = ‖x‖[G] := by rfl

-- Proof sketch: on the nonnegative orthant, the support function of each coordinate box
-- `coordinateBox (a i)` is `⟪a_i, x⟫` because `a_i` has nonnegative coordinates. Hence the support
-- function of `signSymmetricConvexHull a` agrees with the canonical finite-range owner
-- `ξ[Set.range a]`. Monotonicity of support functions under the inclusions
-- `W[1](D) ⊆ signSymmetricConvexHull a ⊆ W[γ √n](D)` supplied by
-- `hrounding : IsEllipsoidalRounding (signSymmetricConvexHull a) γ D` then give the lower and
-- upper bounds, and the support function of `W[ρ](D)` is `ρ * ‖x‖[⟨D, hrounding.posDef⟩]`.
/-- Lemma 7.8: if the convex hull of the boxes `B(a_i)` with nonnegative generators contains
`W₁(D)` and is contained in `W_{γ √n}(D)`, then on the nonnegative orthant the support function of
that box hull is sandwiched between `‖x‖_D` and `γ √n ‖x‖_D`. -/
theorem supportFunction_signSymmetricConvexHull_bounds_on_nonnegativeOrthant
    (a : Fin m → Eₙ) {D : Matₙ} {γ : ℝ}
    (ha_nonneg : ∀ i : Fin m, a i ∈ nonnegativeOrthant n)
    (hrounding : IsEllipsoidalRounding (signSymmetricConvexHull a) γ D)
    (x : Eₙ) (hx_nonneg : x ∈ nonnegativeOrthant n) :
    ‖x‖[⟨D, hrounding.posDef⟩] ≤
        (ξ[signSymmetricConvexHull a] x).toReal ∧
      (ξ[signSymmetricConvexHull a] x).toReal ≤
        γ * Real.sqrt (n : ℝ) * ‖x‖[⟨D, hrounding.posDef⟩] := by
  let G : {G : Matₙ // G.PosDef} := ⟨D, hrounding.posDef⟩
  have hnorm_nonneg : 0 ≤ ‖x‖[G] := by
    positivity
  have hzero_mem_unit : (0 : Eₙ) ∈ W[1](D) := by
    rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hrounding.posDef]
    rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
    simp
  have hzero_mem_hull : (0 : Eₙ) ∈ signSymmetricConvexHull a :=
    hrounding.unit_ellipsoid_subset hzero_mem_unit
  have hgamma_nonneg : 0 ≤ γ * Real.sqrt (n : ℝ) := by
    have hzero_outer : (0 : Eₙ) ∈ W[(γ * Real.sqrt (n : ℝ))](D) :=
      hrounding.subset_outer_ellipsoid hzero_mem_hull
    rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hrounding.posDef,
      positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv] at hzero_outer
    simpa using hzero_outer
  have hsupport_nonbot : ξ[signSymmetricConvexHull a] x ≠ ⊥ := by
    -- The unit ellipsoid contributes a point of the hull, so the support value is finite below.
    intro hbot
    have hzero_le : ((0 : ℝ) : EReal) ≤ ξ[signSymmetricConvexHull a] x := by
      rw [supportFunction_apply]
      exact le_sSup ⟨0, hzero_mem_hull, by simp⟩
    rw [hbot] at hzero_le
    exact (not_le_of_gt (EReal.bot_lt_coe 0)) hzero_le
  have hsupport_ereal_upper :
      ξ[signSymmetricConvexHull a] x ≤
        (γ * Real.sqrt (n : ℝ) * ‖x‖[G] : EReal) := by
    -- The outer ellipsoid controls every support point by the dual pairing estimate.
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨y, hyC, rfl⟩
    have hy_outer : y ∈ W[(γ * Real.sqrt (n : ℝ))](D) :=
      hrounding.subset_outer_ellipsoid hyC
    have hy_dual : ‖y‖[G,*] ≤ γ * Real.sqrt (n : ℝ) := by
      rwa [mem_centeredMatrixEllipsoid_iff_dualNorm_le hrounding.posDef] at hy_outer
    calc
      ((inner ℝ y x : ℝ) : EReal) ≤ ((‖y‖[G,*] * ‖x‖[G] : ℝ) : EReal) := by
        exact_mod_cast
          (Seminorm.inner_le_dualNorm_mul (positiveDefMatrixNorm D hrounding.posDef) x y)
      _ ≤ ((γ * Real.sqrt (n : ℝ) * ‖x‖[G] : ℝ) : EReal) := by
        exact_mod_cast (mul_le_mul_of_nonneg_right hy_dual hnorm_nonneg)
  have hsupport_ne_top : ξ[signSymmetricConvexHull a] x ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hsupport_ereal_upper
  constructor
  · rcases
      exists_inner_ellipsoid_point_attaining_positiveDefMatrixNorm hrounding.posDef x with
      ⟨y, hy_unit, hy_inner⟩
    have hy_hull : y ∈ signSymmetricConvexHull a := hrounding.unit_ellipsoid_subset hy_unit
    have hy_le : ((‖x‖[G] : ℝ) : EReal) ≤ ξ[signSymmetricConvexHull a] x := by
      -- The inner ellipsoid witness contributes the exact primal norm to the support supremum.
      rw [supportFunction_apply]
      simpa [hy_inner] using
        (le_sSup
          ⟨y, hy_hull, rfl⟩ :
            (((inner ℝ y x : ℝ) : EReal)) ≤
              sSup ((fun g : Eₙ ↦ ((inner ℝ g x : ℝ) : EReal)) '' signSymmetricConvexHull a))
    exact EReal.toReal_le_toReal hy_le (EReal.coe_ne_bot _) hsupport_ne_top
  · -- Rewrite through the finite generator support function, then bound each generator.
    calc
      (ξ[signSymmetricConvexHull a] x).toReal = (ξ[Set.range a] x).toReal :=
        supportFunction_signSymmetricConvexHull_eq_range_on_nonnegativeOrthant
          a ha_nonneg hx_nonneg
      _ = sSup (Set.range fun i : Fin m ↦ inner ℝ (a i) x) := by
        simpa using supportFunction_range_toReal_eq_sSup_inner (a := a) (x := x)
      _ ≤ γ * Real.sqrt (n : ℝ) * ‖x‖[G] := by
        refine Real.sSup_le ?_ (mul_nonneg hgamma_nonneg hnorm_nonneg)
        rintro _ ⟨i, rfl⟩
        have hai_mem : a i ∈ signSymmetricConvexHull a :=
          generator_mem_signSymmetricConvexHull a ha_nonneg i
        have hai_outer : a i ∈ W[(γ * Real.sqrt (n : ℝ))](D) :=
          hrounding.subset_outer_ellipsoid hai_mem
        have hai_dual : ‖a i‖[G,*] ≤ γ * Real.sqrt (n : ℝ) := by
          rwa [mem_centeredMatrixEllipsoid_iff_dualNorm_le hrounding.posDef] at hai_outer
        calc
          inner ℝ (a i) x ≤ ‖a i‖[G,*] * ‖x‖[G] :=
            Seminorm.inner_le_dualNorm_mul (positiveDefMatrixNorm D hrounding.posDef) x (a i)
          _ ≤ (γ * Real.sqrt (n : ℝ)) * ‖x‖[G] :=
            mul_le_mul_of_nonneg_right hai_dual hnorm_nonneg
          _ = γ * Real.sqrt (n : ℝ) * ‖x‖[G] := by ring

end
