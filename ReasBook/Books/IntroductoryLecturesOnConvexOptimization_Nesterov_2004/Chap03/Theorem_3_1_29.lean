/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_22
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.PointwiseSupremumOn

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u v

variable {X : Type u} {U : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommMonoid U] [Module ℝ U]

/- This item lies in the chapter's parametric minimax / saddle-value domain.

Sampled owner-style declarations:
- `pointwiseSupremumOn` in `Chap03/PointwiseSupremumOn`, the chapter owner for faithful upper
  envelopes of a kernel;
- `ClosedConvexOn` in `Chap03/Definition_3_1_1_5`, the chapter owner for primal slice geometry;
- `IsSaddlePointOn` in `Mathlib/Order/SaddlePoint`, the canonical owner for saddle inequalities;
- `exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer` in
  `Chap03/Lemma_3_22`, the nearby minimax owner theorem behind the present unique-minimizer
  consequence.

Best owner abstraction:
- source-facing: the minimax equality between the attained primal minimum and attained dual
  maximum;
- core/canonical: `IsSaddlePointOn`, `pointwiseSupremumOn`, `IsMinOn`, `IsMaxOn`, and `IsLeast`;
- bridge/view: the chosen minimizer family `x`, which realizes the diagonal values.

Primitive data:
- the feasible sets `P` and `S`;
- the kernel `Ψ`;
- the real-valued upper objective `f`, bridged to `pointwiseSupremumOn` on `P`;
- the closed-convexity of the primal slices and the concavity of the dual slices;
- the chosen slice minimizers `x u` on `P` and their uniqueness;
- an attained maximizer `uStar ∈ S` of the lower-value function
  `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`.

Derived API:
- the actual minimax equality for the primal and dual value sets;
- the canonical saddle predicate at `(x uStar, uStar)`;
- the primal-minimizer and value companions derived from that saddle relation.
-/

section

variable {P : Set X} {S : Set U} {Ψ : X → U → ℝ} {f : X → ℝ}
variable (x : U → X)
variable {uStar : U}

/-- Helper for Theorem 3.1.29: the chosen slice minimizer realizes the slice infimum. -/
-- Proof sketch: the `IsMinOn` witness says `x u` is a greatest lower bound witness for the slice
-- image, so the conditional infimum is its attained value.
lemma slice_value_eq_csInf_of_isMinOn
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    {u : U} (hu : u ∈ S) :
    sInf ((fun p ↦ Ψ p u) '' P) = Ψ (x u) u := by
  -- The attained slice minimum identifies the infimum with the minimizing slice value.
  exact ((hx_min hu).isGLB (hx_mem hu)).csInf_eq
    ⟨Ψ (x u) u, ⟨x u, hx_mem hu, rfl⟩⟩

/-- Helper for Theorem 3.1.29: every feasible slice value is bounded above by the represented
objective. -/
-- Proof sketch: `f x` is the pointwise supremum of the slice values over `S`, so each individual
-- feasible slice lies below that supremum.
lemma kernel_le_objective_of_mem
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    {xStar : X} (hxStar : xStar ∈ P) {u : U} (hu : u ∈ S) :
    Ψ xStar u ≤ f xStar := by
  -- The distinguished slice is one point in the defining supremum for `f xStar`.
  have hsSup :
      (Ψ xStar u : WithTop ℝ) ≤
        pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) xStar := by
    rw [pointwiseSupremumOn_apply]
    refine le_csSup ?_ ?_
    · exact ⟨⊤, fun _ _ ↦ le_top⟩
    · exact ⟨u, hu, rfl⟩
  have hsSup' : (Ψ xStar u : WithTop ℝ) ≤ (f xStar : WithTop ℝ) := by
    simpa [hf_eq hxStar] using hsSup
  exact_mod_cast hsSup'

/-- Helper for Theorem 3.1.29: at a saddle point, the upper envelope agrees with the
distinguished slice value. -/
-- Proof sketch: the saddle inequality makes the `uStar` slice a greatest element of the slice
-- image at `xStar`, so the supremum defining `f xStar` is exactly `Ψ xStar uStar`.
lemma objective_eq_slice_of_isSaddlePointOn
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    {xStar : X} (hxStar : xStar ∈ P) {uStar : U} (huStar : uStar ∈ S)
    (hsaddle : IsSaddlePointOn P S Ψ xStar uStar) :
    f xStar = Ψ xStar uStar := by
  have hgreatest :
      IsGreatest ((fun u ↦ (Ψ xStar u : WithTop ℝ)) '' S)
        (((Ψ xStar uStar : ℝ) : WithTop ℝ)) := by
    -- The saddle inequality makes the `uStar` slice dominate every other feasible slice.
    refine ⟨⟨uStar, huStar, rfl⟩, ?_⟩
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    change ((Ψ xStar u : ℝ) : WithTop ℝ) ≤ ((Ψ xStar uStar : ℝ) : WithTop ℝ)
    exact_mod_cast hsaddle xStar hxStar u hu
  have hsup :
      pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) xStar =
        (((Ψ xStar uStar : ℝ) : WithTop ℝ)) := by
    rw [pointwiseSupremumOn_apply]
    exact hgreatest.csSup_eq
  apply WithTop.coe_injective
  calc
    ((f xStar : ℝ) : WithTop ℝ)
        = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) xStar := hf_eq hxStar
    _ = (((Ψ xStar uStar : ℝ) : WithTop ℝ)) := hsup

/-- Helper for Theorem 3.1.29: a closed convex slice with an attained unique minimizer has bounded
constrained sublevel sets. -/
-- Proof sketch: if one constrained sublevel set were unbounded, its closed convexity would yield a
-- nonzero asymptotic-cone direction. The whole ray from the unique minimizer along that direction
-- would stay inside the same sublevel set. Convexity of the slice objective then forces every
-- point on that ray to attain the minimal slice value, producing a second minimizer and
-- contradicting uniqueness.
lemma bounded_constrainedSublevelSet_of_unique_slice_argmin
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun p ↦ (Ψ p u : WithTop ℝ)))
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    {u : U} (hu : u ∈ S) (α : ℝ) :
    Bornology.IsBounded
      (constrainedSublevelSet P (fun p ↦ (Ψ p u : WithTop ℝ)) α) := by
  let A := constrainedSublevelSet P (fun p ↦ (Ψ p u : WithTop ℝ)) α
  let x0 := x u
  have hx0P : x0 ∈ P := hx_mem hu
  have hx0min : IsMinOn (fun p ↦ Ψ p u) P x0 := hx_min hu
  have hA_closed : IsClosed A := by
    -- The slice sublevel set is closed by the closed-convex slice owner.
    simpa [A] using (hΨ_closedConvex hu).isClosed_constrainedSublevelSet α
  have hA_convex : Convex ℝ A := by
    -- The same slice owner makes each constrained sublevel set convex.
    simpa [A] using (hΨ_closedConvex hu).convex_constrainedSublevelSet α
  by_cases hα : Ψ x0 u ≤ α
  · have hx0A : x0 ∈ A := by
      -- The minimizing point belongs to the current sublevel set once its value is below `α`.
      exact mem_constrainedSublevelSet_iff.2 ⟨hx0P, by exact_mod_cast hα⟩
    by_contra hA_unbounded
    obtain ⟨d, hd_ne, hd_cone⟩ :=
      (not_bounded_iff_exists_ne_zero_mem_asymptoticCone (s := A)).mp hA_unbounded
    have hray_mem : ∀ c : ℝ, 0 ≤ c → c • d + x0 ∈ A := by
      -- A nonzero asymptotic-cone direction keeps the whole forward ray inside the closed convex
      -- sublevel set.
      intro c hc
      simpa [A, x0] using
        hA_convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hA_closed hc hd_cone hx0A
    have hd_shiftP : d + x0 ∈ P := by
      -- The unit step along the asymptotic direction is still feasible.
      simpa [one_smul] using
        (mem_constrainedSublevelSet_iff.mp (hray_mem 1 (by positivity))).1
    have hconv_slice : ConvexOn ℝ P (fun p ↦ Ψ p u) := by
      -- Closed convexity of the lifted slice recovers ordinary real convexity.
      simpa [withTopRealPart] using (hΨ_closedConvex hu).convexOn_withTopRealPart
    have hd_shift_le : Ψ (d + x0) u ≤ Ψ x0 u := by
      -- Compare `x0 + d` with points farther out on the asymptotic ray and let the weight tend to
      -- zero; the entire ray stays in the same `α`-sublevel set.
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt ((α - Ψ x0 u) / ε)
      let c : ℝ := N + 1
      have hc_pos : 0 < c := by
        positivity
      have hc_ne : c ≠ 0 := ne_of_gt hc_pos
      have hc_inv_nonneg : 0 ≤ c⁻¹ := inv_nonneg.mpr hc_pos.le
      have hc_ge_one : 1 ≤ c := by
        dsimp [c]
        have hN_nonneg : (0 : ℝ) ≤ N := by
          exact_mod_cast Nat.zero_le N
        linarith
      have hc_inv_le_one : c⁻¹ ≤ (1 : ℝ) := by
        simpa [one_div] using (one_div_le_one_div_of_le zero_lt_one hc_ge_one)
      have hc_coeff_nonneg : 0 ≤ 1 - c⁻¹ := by
        linarith
      have hc_sum : (1 - c⁻¹) + c⁻¹ = 1 := by
        ring
      have hcxA : c • d + x0 ∈ A := hray_mem c hc_pos.le
      have hcxP : c • d + x0 ∈ P := (mem_constrainedSublevelSet_iff.mp hcxA).1
      have hcx_le : Ψ (c • d + x0) u ≤ α := by
        exact_mod_cast (mem_constrainedSublevelSet_iff.mp hcxA).2
      have hcomb :
          (1 - c⁻¹) • x0 + c⁻¹ • (c • d + x0) = d + x0 := by
        -- This is the one-dimensional convex combination placing `x0 + d` between `x0` and the
        -- farther ray point `x0 + c d`.
        calc
          (1 - c⁻¹) • x0 + c⁻¹ • (c • d + x0)
              = c⁻¹ • ((c • d + x0) - x0) + x0 := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  (Convex.combo_eq_smul_sub_add (x := x0) (y := c • d + x0) hc_sum)
          _ = c⁻¹ • (c • d) + x0 := by simp
          _ = d + x0 := by
            rw [smul_smul, inv_mul_cancel₀ hc_ne, one_smul]
      have hconv :=
        hconv_slice.2 hx0P hcxP hc_coeff_nonneg hc_inv_nonneg hc_sum
      rw [hcomb] at hconv
      have hfrac_lt : c⁻¹ * (α - Ψ x0 u) < ε := by
        have hdiv_lt : (α - Ψ x0 u) / ε < c := by
          dsimp [c]
          linarith [hN]
        have hmul_lt : α - Ψ x0 u < c * ε := (div_lt_iff₀ hε).1 hdiv_lt
        have hscaled :
            c⁻¹ * (α - Ψ x0 u) < c⁻¹ * (c * ε) :=
          mul_lt_mul_of_pos_left hmul_lt (inv_pos.mpr hc_pos)
        calc
          c⁻¹ * (α - Ψ x0 u) < c⁻¹ * (c * ε) := hscaled
          _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hc_ne, one_mul]
      calc
        Ψ (d + x0) u
            ≤ (1 - c⁻¹) * Ψ x0 u + c⁻¹ * Ψ (c • d + x0) u := hconv
        _ ≤ (1 - c⁻¹) * Ψ x0 u + c⁻¹ * α := by
          gcongr
        _ = Ψ x0 u + c⁻¹ * (α - Ψ x0 u) := by
          ring
        _ ≤ Ψ x0 u + ε := by
          linarith [hfrac_lt]
    have hd_shift_eq : Ψ (d + x0) u = Ψ x0 u := by
      -- Minimality gives the reverse inequality, so the shifted point is another slice minimizer.
      exact le_antisymm hd_shift_le (hx0min hd_shiftP)
    have hd_shift_min : IsMinOn (fun p ↦ Ψ p u) P (d + x0) := by
      -- Equality with the minimal slice value upgrades the shifted point to a full minimizer.
      intro p hp
      calc
        Ψ (d + x0) u = Ψ x0 u := hd_shift_eq
        _ ≤ Ψ p u := hx0min hp
    have hsame : d + x0 = x0 := hx_unique hu (d + x0) hd_shift_min
    have hsame' : d + x0 = 0 + x0 := by
      simpa using hsame
    exact hd_ne (add_right_cancel hsame')
  · -- If the minimizing slice value already exceeds `α`, then the constrained sublevel set is empty.
    have hA_empty : A = ∅ := by
      ext p
      constructor
      · intro hp
        have hpP : p ∈ P := (mem_constrainedSublevelSet_iff.mp hp).1
        have hpα : Ψ p u ≤ α := by
          exact_mod_cast (mem_constrainedSublevelSet_iff.mp hp).2
        have hx0_le : Ψ x0 u ≤ Ψ p u := hx0min hpP
        exact False.elim (hα (hx0_le.trans hpα))
      · intro hp
        simp at hp
    change Bornology.IsBounded A
    simpa [hA_empty] using (Bornology.isBounded_empty : Bornology.IsBounded (∅ : Set X))

/-- Helper for Theorem 3.1.29: the two-slice maximum attains its minimum, and that minimum is the
`uStar` slice value. -/
-- Proof sketch: the unique-slice-minimizer hypothesis supplies bounded sublevel sets for each
-- slice. Minimize the two-slice maximum using the compact-sublevel existence theorem, linearize
-- that maximum with the chapter minimax-parameter owner, compare the linearized slice to the
-- concave `uLam` slice, and then use the maximizing property of `uStar` to identify the attained
-- minimum value.
lemma exists_isMinOn_two_slice_max_eq_uStar_value_of_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun p ↦ (Ψ p u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun p ↦ Ψ p u) '' P)) S uStar)
    {u : U} (hu : u ∈ S) :
    ∃ xBar ∈ P,
      IsMinOn (fun p ↦ max (Ψ p u) (Ψ p uStar)) P xBar ∧
        max (Ψ xBar u) (Ψ xBar uStar) = sInf ((fun p ↦ Ψ p uStar) '' P) := by
  let F : X → ℝ := fun p ↦ max (Ψ p u) (Ψ p uStar)
  have hP_nonempty : P.Nonempty := ⟨x uStar, hx_mem huStar⟩
  have hvalue_uStar_eq :
      sInf ((fun p ↦ Ψ p uStar) '' P) = Ψ (x uStar) uStar :=
    slice_value_eq_csInf_of_isMinOn x hx_mem hx_min huStar
  have hF_closedConvex :
      ClosedConvexOn P (fun p ↦ (F p : WithTop ℝ)) :=
    by
      -- The pointwise maximum inherits closed convexity from the two slice owners.
      change ClosedConvexOn P
        (((fun p ↦ (Ψ p u : WithTop ℝ)) ⊔ fun p ↦ (Ψ p uStar : WithTop ℝ)))
      simpa [Set.inter_self] using
        (ClosedConvexOn.max_inter
          (hΨ_closedConvex hu)
          (hΨ_closedConvex huStar))
  have hlevel_bounded :
      ∀ ⦃w : U⦄, w ∈ S → ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet P (fun p ↦ (Ψ p w : WithTop ℝ)) α) := by
    intro w hw α
    exact
      bounded_constrainedSublevelSet_of_unique_slice_argmin
        x hΨ_closedConvex hx_mem hx_min hx_unique hw α
  have hF_bounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet P (fun p ↦ (F p : WithTop ℝ)) α) := by
    intro α
    refine (hlevel_bounded huStar α).subset ?_
    intro p hp
    rcases mem_constrainedSublevelSet_iff.mp hp with ⟨hpP, hpα⟩
    have hpα' : max (Ψ p u) (Ψ p uStar) ≤ α := by
      exact_mod_cast hpα
    refine mem_constrainedSublevelSet_iff.2 ⟨hpP, ?_⟩
    exact_mod_cast (le_trans (le_max_right (Ψ p u) (Ψ p uStar)) hpα')
  obtain ⟨xBar, hxBar_mem, hxBar_min⟩ :=
    exists_isMinOn_of_closedConvexOn_bounded_sublevels hP_nonempty hF_closedConvex hF_bounded
  obtain ⟨lam, hlam⟩ :=
    exists_minimax_parameter_of_bounded_constrainedSublevelSets
      (hΨ_closedConvex hu)
      (hΨ_closedConvex huStar)
      hF_bounded
  let uLam : U := (1 - (lam : ℝ)) • uStar + (lam : ℝ) • u
  let line : X → ℝ := fun p ↦ (1 - (lam : ℝ)) * Ψ p uStar + (lam : ℝ) * Ψ p u
  have hS_convex : Convex ℝ S := (hΨ_concave (hx_mem huStar)).1
  have huLam_mem : uLam ∈ S := by
    -- Concavity already records convexity of `S`, so the affine combination remains feasible.
    simpa [uLam] using
      hS_convex huStar hu (sub_nonneg.mpr lam.2.2) lam.2.1 (by nlinarith)
  have hvalue_uLam_eq :
      sInf ((fun p ↦ Ψ p uLam) '' P) = Ψ (x uLam) uLam :=
    slice_value_eq_csInf_of_isMinOn x hx_mem hx_min huLam_mem
  have hline_le_uLam : ∀ p ∈ P, line p ≤ Ψ p uLam := by
    -- Concavity of the dual slice compares the weighted line with the slice at `uLam`.
    intro p hp
    have hineq :=
      (hΨ_concave hp).2 huStar hu (sub_nonneg.mpr lam.2.2) lam.2.1 (by nlinarith)
    simpa [line, uLam, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using hineq
  have hline_le_F : ∀ p : X, line p ≤ F p := by
    -- Any convex combination of two scalars is bounded above by their maximum.
    intro p
    have hleft :
        (1 - (lam : ℝ)) * Ψ p uStar ≤ (1 - (lam : ℝ)) * F p := by
      exact mul_le_mul_of_nonneg_left (le_max_right (Ψ p u) (Ψ p uStar))
        (sub_nonneg.mpr lam.2.2)
    have hright :
        (lam : ℝ) * Ψ p u ≤ (lam : ℝ) * F p := by
      exact mul_le_mul_of_nonneg_left (le_max_left (Ψ p u) (Ψ p uStar)) lam.2.1
    change (1 - (lam : ℝ)) * Ψ p uStar + (lam : ℝ) * Ψ p u ≤ F p
    nlinarith
  have hminimax :
      sInf (Set.range fun p : P ↦ ((F p : ℝ) : EReal)) =
        sInf (Set.range fun p : P ↦ ((line p : ℝ) : EReal)) := by
    -- The two-function minimax owner rewrites the max-objective infimum as the line infimum.
    simpa [F, line, max_def, AffineMap.lineMap_apply_ring, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using
      (isMinimaxLinearizationParameter_iff
        (fun p : P ↦ Ψ p u) (fun p : P ↦ Ψ p uStar) lam).mp hlam
  have hsInf_line_le_value :
      sInf (Set.range fun p : P ↦ ((line p : ℝ) : EReal)) ≤
        (((sInf ((fun p ↦ Ψ p uStar) '' P) : ℝ)) : EReal) := by
    -- Evaluate the line at the minimizing point of the `uLam` slice, then use maximality of `uStar`.
    have hline_mem :
        (((line (x uLam) : ℝ) : EReal)) ∈ Set.range fun p : P ↦ ((line p : ℝ) : EReal) :=
      ⟨⟨x uLam, hx_mem huLam_mem⟩, rfl⟩
    calc
      sInf (Set.range fun p : P ↦ ((line p : ℝ) : EReal)) ≤ ((line (x uLam) : ℝ) : EReal) :=
        sInf_le hline_mem
      _ ≤ ((Ψ (x uLam) uLam : ℝ) : EReal) := by
        exact_mod_cast hline_le_uLam (x uLam) (hx_mem huLam_mem)
      _ = (((sInf ((fun p ↦ Ψ p uLam) '' P) : ℝ)) : EReal) := by
        exact_mod_cast hvalue_uLam_eq.symm
      _ ≤ (((sInf ((fun p ↦ Ψ p uStar) '' P) : ℝ)) : EReal) := by
        exact_mod_cast huStar_max huLam_mem
  have hvalue_le_hsInf_F :
      (((sInf ((fun p ↦ Ψ p uStar) '' P) : ℝ)) : EReal) ≤
        sInf (Set.range fun p : P ↦ ((F p : ℝ) : EReal)) := by
    -- The `uStar` lower value is a lower bound for every value of the two-slice maximum.
    refine le_sInf ?_
    intro b hb
    rcases hb with ⟨p, rfl⟩
    have hvalue_le_slice :
        sInf ((fun q ↦ Ψ q uStar) '' P) ≤ Ψ p uStar := by
      calc
        sInf ((fun q ↦ Ψ q uStar) '' P) = Ψ (x uStar) uStar := hvalue_uStar_eq
        _ ≤ Ψ p uStar := hx_min huStar p.property
    have hvalue_le_F_real :
        sInf ((fun q ↦ Ψ q uStar) '' P) ≤ F p := by
      exact hvalue_le_slice.trans (le_max_right (Ψ p u) (Ψ p uStar))
    change (((sInf ((fun q ↦ Ψ q uStar) '' P) : ℝ)) : EReal) ≤ ((F p : ℝ) : EReal)
    exact_mod_cast hvalue_le_F_real
  have hsInf_F_eq :
      sInf (Set.range fun p : P ↦ ((F p : ℝ) : EReal)) =
        (((sInf ((fun p ↦ Ψ p uStar) '' P) : ℝ)) : EReal) := by
    refine le_antisymm ?_ hvalue_le_hsInf_F
    rw [hminimax]
    exact hsInf_line_le_value
  have hxBar_le_hsInf_F :
      ((F xBar : ℝ) : EReal) ≤ sInf (Set.range fun p : P ↦ ((F p : ℝ) : EReal)) := by
    -- The minimizer is itself a lower bound for the feasible subtype image.
    refine le_sInf ?_
    intro b hb
    rcases hb with ⟨p, rfl⟩
    change ((F xBar : ℝ) : EReal) ≤ ((F p : ℝ) : EReal)
    exact_mod_cast (hxBar_min p.property)
  have hsInf_F_le_xBar :
      sInf (Set.range fun p : P ↦ ((F p : ℝ) : EReal)) ≤ ((F xBar : ℝ) : EReal) :=
    sInf_le ⟨⟨xBar, hxBar_mem⟩, rfl⟩
  have hxBar_value :
      ((F xBar : ℝ) : EReal) = (((sInf ((fun p ↦ Ψ p uStar) '' P) : ℝ)) : EReal) := by
    refine le_antisymm ?_ ?_
    · exact hxBar_le_hsInf_F.trans hsInf_F_eq.le
    · exact hsInf_F_eq.symm.le.trans hsInf_F_le_xBar
  refine ⟨xBar, hxBar_mem, ?_, ?_⟩
  · simpa [F] using hxBar_min
  · exact_mod_cast hxBar_value

/-- Helper for Theorem 3.1.29: the distinguished pair is a saddle point once the two-slice
attainment route and uniqueness collapse the auxiliary minimizers back to `x uStar`. -/
-- Proof sketch: for each feasible `u`, minimize `x ↦ max (Ψ x u) (Ψ x uStar)`. The attained value
-- equals the `uStar` slice infimum, so the minimizer is also a `uStar` slice minimizer. Uniqueness
-- forces that minimizer to be `x uStar`, which gives the left-hand saddle inequality. The right-
-- hand saddle inequality is just the minimizing property of the `uStar` slice.
lemma saddle_point_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    IsSaddlePointOn P S Ψ (x uStar) uStar := by
  intro p hp u hu
  obtain ⟨xBar, hxBar_mem, hxBar_min, hxBar_value⟩ :=
    exists_isMinOn_two_slice_max_eq_uStar_value_of_attained_dual_max
      x hΨ_closedConvex hΨ_concave hx_mem hx_min hx_unique huStar huStar_max hu
  have huStar_slice_eq :
      sInf ((fun q ↦ Ψ q uStar) '' P) = Ψ (x uStar) uStar :=
    slice_value_eq_csInf_of_isMinOn x hx_mem hx_min huStar
  have hxBar_uStar_eq :
      Ψ xBar uStar = sInf ((fun q ↦ Ψ q uStar) '' P) := by
    -- The two-slice maximum equals the `uStar` slice value, so the `uStar` coordinate itself
    -- already attains the slice infimum at `xBar`.
    have hlower :
        sInf ((fun q ↦ Ψ q uStar) '' P) ≤ Ψ xBar uStar := by
      calc
        sInf ((fun q ↦ Ψ q uStar) '' P) = Ψ (x uStar) uStar := huStar_slice_eq
        _ ≤ Ψ xBar uStar := hx_min huStar hxBar_mem
    have hupper :
        Ψ xBar uStar ≤ sInf ((fun q ↦ Ψ q uStar) '' P) := by
      calc
        Ψ xBar uStar ≤ max (Ψ xBar u) (Ψ xBar uStar) := le_max_right _ _
        _ = sInf ((fun q ↦ Ψ q uStar) '' P) := hxBar_value
    exact le_antisymm hupper hlower
  have hxBar_uStar_min : IsMinOn (fun q ↦ Ψ q uStar) P xBar := by
    -- Equality with the distinguished slice infimum upgrades `xBar` to a full `uStar` minimizer.
    intro q hq
    calc
      Ψ xBar uStar = sInf ((fun p ↦ Ψ p uStar) '' P) := hxBar_uStar_eq
      _ = Ψ (x uStar) uStar := huStar_slice_eq
      _ ≤ Ψ q uStar := hx_min huStar hq
  have hxBar_eq : xBar = x uStar := hx_unique huStar xBar hxBar_uStar_min
  have hleft :
      Ψ (x uStar) u ≤ Ψ (x uStar) uStar := by
    -- Once `xBar = x uStar`, the two-slice maximum identity forces the `u` slice to stay below
    -- the `uStar` slice at that common point.
    have hmax_eq :
        max (Ψ (x uStar) u) (Ψ (x uStar) uStar) =
          Ψ (x uStar) uStar := by
      calc
        max (Ψ (x uStar) u) (Ψ (x uStar) uStar)
            = max (Ψ xBar u) (Ψ xBar uStar) := by rw [hxBar_eq]
        _ = sInf ((fun q ↦ Ψ q uStar) '' P) := hxBar_value
        _ = Ψ (x uStar) uStar := huStar_slice_eq
    calc
      Ψ (x uStar) u ≤ max (Ψ (x uStar) u) (Ψ (x uStar) uStar) := le_max_left _ _
      _ = Ψ (x uStar) uStar := hmax_eq
  exact hleft.trans (hx_min huStar hp)

/-- Theorem 3.1.29: if every primal slice `x ↦ Ψ x u` with `u ∈ S` attains the unique minimizer
`x u` on `P`, and if the lower-value function `u ↦ sInf ((fun x ↦ Ψ x u) '' P)` attains its
maximum on `S`, then the primal minimum of `f` on `P` equals the dual maximum of that lower-value
function on `S`. -/
-- Proof sketch: first use the unique-minimizer hypothesis together with Theorem 3.1.4 and
-- Lemma 3.1.22 to show that `(x uStar, uStar)` is a saddle point of `Ψ` on `P × S`. The saddle
-- inequalities imply that `x uStar` minimizes `f` on `P` and that
-- `f (x uStar) = sInf ((fun x ↦ Ψ x uStar) '' P)`. Finally combine that identity with the
-- maximizing property `huStar_max` to identify the primal infimum `sInf (f '' P)` with the dual
-- supremum `sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S)`.
theorem minimax_eq_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    sInf (f '' P) = sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := by
  have hsaddle :
      IsSaddlePointOn P S Ψ (x uStar) uStar :=
    saddle_point_of_unique_slice_argmin_and_attained_dual_max
      x hΨ_closedConvex hΨ_concave hx_mem hx_min hx_unique huStar huStar_max
  have hslice_eq :
      f (x uStar) = Ψ (x uStar) uStar :=
    objective_eq_slice_of_isSaddlePointOn hf_eq (hx_mem huStar) huStar hsaddle
  have hvalue_eq :
      f (x uStar) = sInf ((fun p ↦ Ψ p uStar) '' P) := by
    calc
      f (x uStar) = Ψ (x uStar) uStar := hslice_eq
      _ = sInf ((fun p ↦ Ψ p uStar) '' P) := by
        symm
        exact slice_value_eq_csInf_of_isMinOn x hx_mem hx_min huStar
  have hleast :
      IsLeast (f '' P) (f (x uStar)) := by
    -- The saddle inequalities and the upper-envelope bridge make `f (x uStar)` the least primal
    -- value and show that it is attained at `x uStar`.
    refine ⟨⟨x uStar, hx_mem huStar, rfl⟩, ?_⟩
    rintro _ ⟨p, hpP, rfl⟩
    calc
      f (x uStar) = Ψ (x uStar) uStar := hslice_eq
      _ ≤ Ψ p uStar := hsaddle p hpP uStar huStar
      _ ≤ f p := kernel_le_objective_of_mem hf_eq hpP huStar
  have hgreatest :
      IsGreatest ((fun u ↦ sInf ((fun p ↦ Ψ p u) '' P)) '' S)
        (sInf ((fun p ↦ Ψ p uStar) '' P)) := by
    -- The maximizing parameter contributes the greatest element in the dual value image.
    refine ⟨⟨uStar, huStar, rfl⟩, ?_⟩
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    exact huStar_max hu
  calc
    sInf (f '' P) = f (x uStar) := hleast.csInf_eq
    _ = sInf ((fun p ↦ Ψ p uStar) '' P) := hvalue_eq
    _ = sSup ((fun u ↦ sInf ((fun p ↦ Ψ p u) '' P)) '' S) := hgreatest.csSup_eq.symm

/-- The distinguished pair `(x uStar, uStar)` is a saddle point of `Ψ` on `P × S` under the
unique-slice-minimizer and dual-maximizer hypotheses. -/
-- Proof sketch: apply Theorem 3.1.4 to each closed-convex slice `x ↦ Ψ x u` to recover bounded
-- sublevel sets from uniqueness of `x u`. Then Lemma 3.1.22 applied at `uStar` forces the two
-- inequalities `Ψ (x uStar) u ≤ Ψ (x uStar) uStar ≤ Ψ x uStar` for all `u ∈ S` and `x ∈ P`,
-- which is exactly the saddle relation.
theorem isSaddlePointOn_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    IsSaddlePointOn P S Ψ (x uStar) uStar := by
  exact
    saddle_point_of_unique_slice_argmin_and_attained_dual_max
      x hΨ_closedConvex hΨ_concave hx_mem hx_min hx_unique huStar huStar_max

/-- Companion consequence of Theorem 3.1.29: the distinguished primal point `x uStar` minimizes
the real-valued upper objective `f` on `P`. -/
-- Proof sketch: combine the saddle inequalities at `(x uStar, uStar)` with the bridge
-- `hf_eq` identifying `f` on `P` with the faithful upper envelope `pointwiseSupremumOn S Ψ`.
-- This gives `f (x uStar) ≤ f x` for every feasible `x`.
theorem isMinOn_objective_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    IsMinOn f P (x uStar) := by
  have hsaddle :
      IsSaddlePointOn P S Ψ (x uStar) uStar :=
    isSaddlePointOn_of_unique_slice_argmin_and_attained_dual_max
      x hΨ_closedConvex hΨ_concave hf_eq hx_mem hx_min hx_unique huStar huStar_max
  have hvalue_eq :
      f (x uStar) = Ψ (x uStar) uStar :=
    objective_eq_slice_of_isSaddlePointOn hf_eq (hx_mem huStar) huStar hsaddle
  intro p hp
  calc
    f (x uStar) = Ψ (x uStar) uStar := hvalue_eq
    _ ≤ Ψ p uStar := hsaddle p hp uStar huStar
    _ ≤ f p := kernel_le_objective_of_mem hf_eq hp huStar

/-- Companion value identity from Theorem 3.1.29. -/
-- Proof sketch: once `x uStar` is known to minimize `f` on `P`, the right-hand saddle inequality
-- identifies its objective value with the slice minimum
-- `sInf ((fun x ↦ Ψ x uStar) '' P)`.
theorem objective_eq_valueFunction_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    f (x uStar) = sInf ((fun x ↦ Ψ x uStar) '' P) := by
  have hsaddle :
      IsSaddlePointOn P S Ψ (x uStar) uStar :=
    isSaddlePointOn_of_unique_slice_argmin_and_attained_dual_max
      x hΨ_closedConvex hΨ_concave hf_eq hx_mem hx_min hx_unique huStar huStar_max
  calc
    f (x uStar) = Ψ (x uStar) uStar := by
      exact objective_eq_slice_of_isSaddlePointOn hf_eq (hx_mem huStar) huStar hsaddle
    _ = sInf ((fun p ↦ Ψ p uStar) '' P) := by
      symm
      exact slice_value_eq_csInf_of_isMinOn x hx_mem hx_min huStar

/-- Order-theoretic companion of Theorem 3.1.29: the upper-envelope value attained at `x uStar`
is the least element of the feasible value image. -/
-- Proof sketch: reformulate `isMinOn_objective_of_unique_slice_argmin_and_attained_dual_max`
-- as the statement that `f (x uStar)` is a lower bound on `f '' P`, and use `hx_mem huStar` to
-- record that the bound is itself attained in the image.
theorem primal_min_isLeast_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    IsLeast (f '' P) (f (x uStar)) := by
  refine ⟨⟨x uStar, hx_mem huStar, rfl⟩, ?_⟩
  rintro _ ⟨p, hpP, rfl⟩
  have hmin : IsMinOn f P (x uStar) :=
    isMinOn_objective_of_unique_slice_argmin_and_attained_dual_max
      x hΨ_closedConvex hΨ_concave hf_eq hx_mem hx_min hx_unique huStar huStar_max
  exact hmin hpP

end

end
