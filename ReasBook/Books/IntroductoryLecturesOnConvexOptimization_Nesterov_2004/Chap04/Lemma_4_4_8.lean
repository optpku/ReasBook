/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open Set
open scoped ConvexAnalysis
open scoped BInducedNorm
open scoped ModifiedGaussNewtonLocalModelNotation

universe u v

/- Lemma 4.4.8 lies in the weighted modified Gauss--Newton optimal-value domain.

Sampled owner-style declarations:
* `PrimalSpace` in `Definition_4_2_9`, the chapter owner for the intrinsic `B`-weighted carrier;
* `modifiedGaussNewtonLocalModel` in `Definition_4_4_11`, the chapter owner for the affine
  residual model;
* `modifiedGaussNewtonOptimalValueAt` and `modifiedGaussNewtonOptimalValue` in
  `Proposition_4_4_6`, the chapter owners for whole-space modified Gauss--Newton optimal values.

Source/core/bridge triage:
* source-facing: the weighted textbook formulas written with `‖·‖[B₁]` and `‖·‖[B₂]`;
* core/canonical: `modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x` and
  `modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x` on `PrimalSpace B₁` and `PrimalSpace B₂`;
* bridge/view: the step-variable `sInf` expansion, the `‖·‖[B]` rewrites, and the final
  positive-`τ` infimum formula.

This file therefore keeps only thin weighted bridge lemmas. The duplicate local owners for the
auxiliary objective and its optimal value are deleted in favor of direct reuse of the Chapter 4
canonical owner. -/

section AuxiliaryValue

variable {E₁ : Type u} {E₂ : Type v}
variable [AddCommGroup E₁] [Module ℝ E₁]
variable [AddCommGroup E₂] [Module ℝ E₂]
variable (B₁ : BilinForm ℝ E₁) [Fact B₁.toQuadraticMap.PosDef]
variable (B₂ : BilinForm ℝ E₂) [Fact B₂.toQuadraticMap.PosDef]
variable (F : PrimalSpace B₁ → PrimalSpace B₂)
variable (J : PrimalSpace B₁ → PrimalSpace B₁ →L[ℝ] PrimalSpace B₂)
variable (x : PrimalSpace B₁)

/- The weighted auxiliary value in Lemma 4.4.8 is the existing Chapter 4 optimal-value owner
specialized to the local model `ψ[F; norm; J]` on the intrinsic weighted carriers. -/
set_option linter.hashCommand false in
#check (modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x : ℝ → EReal)

set_option linter.hashCommand false in
#check (modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x : NNRealˣ → ℝ)

/-- Unfolding the canonical weighted optimal-value owner gives the step-variable infimum over the
intrinsic weighted carrier `PrimalSpace B₁`. -/
theorem modifiedGaussNewtonOptimalValueAt_weighted_eq_sInf_range
    (M : ℝ) :
    modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x M =
      sInf (range fun h : PrimalSpace B₁ ↦
        (‖F x + J x h‖ + (M / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) : EReal)) := by
  -- Rewrite the whole-space owner to the step variable `h = y - x`.
  rw [modifiedGaussNewtonOptimalValueAt_eq_sInf_range]
  congr 1
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y - x, ?_⟩
    simp only [quadraticallyRegularizedObjective_apply, modifiedGaussNewtonLocalModel_apply]
    exact_mod_cast
      (show ‖F x + (J x) (y - x)‖ + (M / 2) * ‖y - x‖ ^ (2 : ℕ) =
          ‖F x + (J x) (y - x)‖ + (M / 2) * ‖y - x‖ ^ (2 : ℕ) by
        rfl)
  · rintro ⟨h, rfl⟩
    refine ⟨h + x, ?_⟩
    simp only [quadraticallyRegularizedObjective_apply, modifiedGaussNewtonLocalModel_apply]
    have hshift :
        ‖F x + (J x) (h + x - x)‖ + (M / 2) * ‖h + x - x‖ ^ (2 : ℕ) =
          ‖F x + (J x) h‖ + (M / 2) * ‖h‖ ^ (2 : ℕ) := by
      simp
    exact_mod_cast hshift

/-- Rewriting the intrinsic ambient norms back into the explicit textbook `B`-induced norms
recovers the weighted formula stated in the source text. -/
theorem modifiedGaussNewtonOptimalValueAt_weighted_eq_sInf_range_bInducedNorm
    (M : ℝ) :
    modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x M =
      sInf (range fun h : PrimalSpace B₁ ↦
        (‖F x + J x h‖[B₂] + (M / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ) : EReal)) := by
  simpa only [LinearMap.BilinForm.primalSpace_norm_eq_bInducedNorm] using
    modifiedGaussNewtonOptimalValueAt_weighted_eq_sInf_range B₁ B₂ F J x M

-- In the positive-regularization regime, the source-facing weighted auxiliary value is still the
-- existing Chapter 4 positive owner `modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x`.
/-- Helper for Lemma 4.4.8: coercing the infimum of a nonempty bounded-below real range into
`EReal` agrees with taking the infimum after coercion. -/
lemma ereal_sInf_coe_range_eq
    {α : Type*} (f : α → ℝ)
    (hnonempty : (range f).Nonempty)
    (hbddBelow : BddBelow (range f)) :
    sInf (range fun a ↦ (f a : EReal)) = ((sInf (range f) : ℝ) : EReal) := by
  -- Transport the real greatest-lower-bound characterization across the coercion `ℝ → EReal`.
  have hglb : IsGLB (range f) (sInf (range f)) :=
    Real.isGLB_sInf hnonempty hbddBelow
  have hglb' :
      IsGLB (Real.toEReal '' range f) (((sInf (range f) : ℝ) : EReal)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact_mod_cast hglb.1 hy
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          rintro rfl
          rcases hnonempty with ⟨y, hy⟩
          have : (⊤ : EReal) ≤ (y : EReal) := hz ⟨y, hy, rfl⟩
          simp at this
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with r
        have hr : ∀ y ∈ range f, r ≤ y := by
          intro y hy
          exact_mod_cast (hz ⟨y, hy, rfl⟩)
        exact_mod_cast hglb.2 hr
  calc
    sInf (range fun a ↦ (f a : EReal)) = sInf (Real.toEReal '' range f) := by
      congr 1
      ext z
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨f a, ⟨a, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
    _ = ((sInf (range f) : ℝ) : EReal) := by
      exact hglb'.csInf_eq (by
    rcases hnonempty with ⟨y, hy⟩
    exact ⟨(y : EReal), ⟨y, hy, rfl⟩⟩)

/-- In the positive-regularization regime, the source-facing weighted auxiliary value is the real
infimum of the weighted step-variable objective. -/
theorem modifiedGaussNewtonOptimalValue_weighted_eq_sInf_range_bInducedNorm
    (M : NNRealˣ) :
    modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x M =
      sInf (range fun h : PrimalSpace B₁ ↦
        ‖F x + J x h‖[B₂] + (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ))) := by
  let objective : PrimalSpace B₁ → ℝ := fun h ↦
    ‖F x + J x h‖[B₂] + (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ))
  have hobjective_nonempty : (range objective).Nonempty := by
    refine ⟨objective 0, ⟨0, rfl⟩⟩
  have hobjective_bddBelow : BddBelow (range objective) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨h, rfl⟩
    have hnorm_nonneg : 0 ≤ ‖F x + J x h‖[B₂] := by
      positivity
    have hquad_nonneg : 0 ≤ (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ)) := by
      positivity
    exact add_nonneg hnorm_nonneg hquad_nonneg
  have hvalue :
      modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x (M : ℝ) =
        ((sInf (range objective) : ℝ) : EReal) := by
    -- Rewrite the `EReal` owner as the coercion of the corresponding real infimum.
    rw [modifiedGaussNewtonOptimalValueAt_weighted_eq_sInf_range_bInducedNorm]
    simpa [objective] using
      ereal_sInf_coe_range_eq (f := objective) hobjective_nonempty hobjective_bddBelow
  have hdom : (M : ℝ) ∈ dom (modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x) := by
    -- The coerced real infimum is finite, so the positive-regime owner lies in its
    -- effective domain.
    refine (mem_extendedRealEffectiveDomain_iff).2 ?_
    constructor
    · intro htop
      have : ((sInf (range objective) : ℝ) : EReal) = ⊤ := by
        rw [← hvalue]
        exact htop
      simp at this
    · intro hbot
      have : ((sInf (range objective) : ℝ) : EReal) = ⊥ := by
        rw [← hvalue]
        exact hbot
      simp at this
  have hcoe :
      ((modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x M : ℝ) : EReal) =
        ((sInf (range objective) : ℝ) : EReal) := by
    -- Coercing the positive-regime real part back to `EReal` recovers the finite owner value.
    rw [modifiedGaussNewtonOptimalValue, coe_extendedRealRealPart hdom, hvalue]
  exact EReal.coe_eq_coe_iff.mp hcoe

/-- Helper for Lemma 4.4.8: every positive-`τ` quadratic majorant dominates the weighted norm. -/
lemma bInducedNorm_le_positive_tau_quadratic
    (u : PrimalSpace B₂) (τ : NNRealˣ) :
    ‖u‖[B₂] ≤
      ((τ : ℝ) / 2 : ℝ) + (1 / (2 * (τ : ℝ)) : ℝ) * ‖u‖[B₂] ^ (2 : ℕ) := by
  -- Rewrite the gap as a positive square divided by the positive denominator `2τ`.
  have hτ_pos : 0 < (τ : ℝ) := by
    have hτ_pos_nn : (0 : NNReal) < (τ : NNReal) := by
      exact pos_iff_ne_zero.mpr (Units.ne_zero τ)
    exact_mod_cast hτ_pos_nn
  have hgap_nonneg : 0 ≤ ((τ : ℝ) - ‖u‖[B₂]) ^ (2 : ℕ) / (2 * (τ : ℝ)) := by
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hgap_identity :
      ((τ : ℝ) / 2 : ℝ) + (1 / (2 * (τ : ℝ)) : ℝ) * ‖u‖[B₂] ^ (2 : ℕ) - ‖u‖[B₂] =
        ((τ : ℝ) - ‖u‖[B₂]) ^ (2 : ℕ) / (2 * (τ : ℝ)) := by
    field_simp [hτ_pos.ne']
    ring
  have hmajorant_nonneg :
      0 ≤
        ((τ : ℝ) / 2 : ℝ) + (1 / (2 * (τ : ℝ)) : ℝ) * ‖u‖[B₂] ^ (2 : ℕ) - ‖u‖[B₂] := by
    rw [hgap_identity]
    exact hgap_nonneg
  linarith

/-- Helper for Lemma 4.4.8: translating a nonempty bounded-below real range by a constant
translates its infimum by the same constant. -/
lemma sInf_range_add_const
    {α : Type*} (f : α → ℝ) (c : ℝ)
    (hnonempty : (range f).Nonempty)
    (hbddBelow : BddBelow (range f)) :
    sInf (range fun a ↦ f a + c) = sInf (range f) + c := by
  -- Compare the greatest lower bounds before and after the common translation.
  have hglb : IsGLB (range f) (sInf (range f)) :=
    Real.isGLB_sInf hnonempty hbddBelow
  have hglb' : IsGLB (range fun a ↦ f a + c) (sInf (range f) + c) := by
    constructor
    · rintro _ ⟨a, rfl⟩
      have hle : sInf (range f) ≤ f a := hglb.1 ⟨a, rfl⟩
      linarith
    · intro z hz
      have hz' : z - c ≤ sInf (range f) := by
        refine le_csInf hnonempty ?_
        rintro _ ⟨a, rfl⟩
        have hzfa : z ≤ f a + c := hz ⟨a, rfl⟩
        linarith
      linarith
  exact hglb'.csInf_eq (by
    rcases hnonempty with ⟨y, hy⟩
    rcases hy with ⟨a, rfl⟩
    exact ⟨f a + c, ⟨a, rfl⟩⟩)

/-- Helper for Lemma 4.4.8: the weighted norm is the infimum of its positive-`τ` quadratic
majorants. -/
lemma bInducedNorm_eq_sInf_positive_tau_quadratic
    (u : PrimalSpace B₂) :
    ‖u‖[B₂] = sInf (range fun τ : NNRealˣ ↦
      ((τ : ℝ) / 2 : ℝ) + (1 / (2 * (τ : ℝ)) : ℝ) * ‖u‖[B₂] ^ (2 : ℕ)) := by
  let objective : NNRealˣ → ℝ := fun τ ↦
    ((τ : ℝ) / 2 : ℝ) + (1 / (2 * (τ : ℝ)) : ℝ) * ‖u‖[B₂] ^ (2 : ℕ)
  have hobjective_nonempty : (range objective).Nonempty := by
    refine ⟨objective 1, ⟨1, rfl⟩⟩
  have hobjective_bddBelow : BddBelow (range objective) := by
    refine ⟨‖u‖[B₂], ?_⟩
    rintro _ ⟨τ, rfl⟩
    exact bInducedNorm_le_positive_tau_quadratic (B₂ := B₂) u τ
  refine le_antisymm ?_ ?_
  · -- The norm is a lower bound for every positive-`τ` quadratic slice.
    refine le_csInf hobjective_nonempty ?_
    rintro _ ⟨τ, rfl⟩
    exact bInducedNorm_le_positive_tau_quadratic (B₂ := B₂) u τ
  · by_cases hu : ‖u‖[B₂] = 0
    · -- When the residual norm vanishes, arbitrarily small positive `τ` make the slice
      -- arbitrarily small.
      by_contra hsInf_pos
      have hsInf_pos' : 0 < sInf (range objective) := by
        have : ¬ sInf (range objective) ≤ 0 := by
          simpa [objective, hu] using hsInf_pos
        exact lt_of_not_ge this
      let τ : NNRealˣ :=
        Units.mk0 (Real.toNNReal (sInf (range objective)))
          (ne_of_gt (by rwa [Real.toNNReal_pos]))
      have hsInf_le_tau : sInf (range objective) ≤ objective τ := by
        exact csInf_le hobjective_bddBelow ⟨τ, rfl⟩
      have hτ_eq : (τ : ℝ) = sInf (range objective) := by
        simp [τ, Real.toNNReal_of_nonneg hsInf_pos'.le]
      have hτ_value : objective τ = sInf (range objective) / 2 := by
        simp [objective, hτ_eq, hu]
      linarith
    · -- Otherwise the exact witness `τ = ‖u‖[B₂]` attains equality.
      have hu_pos : 0 < ‖u‖[B₂] := by
        refine lt_of_le_of_ne ?_ (by simpa [eq_comm] using hu)
        positivity
      let τ : NNRealˣ :=
        Units.mk0 (Real.toNNReal ‖u‖[B₂]) (ne_of_gt (by rwa [Real.toNNReal_pos]))
      have hsInf_le_tau : sInf (range objective) ≤ objective τ := by
        exact csInf_le hobjective_bddBelow ⟨τ, rfl⟩
      have hτ_eq : (τ : ℝ) = ‖u‖[B₂] := by
        simp [τ]
      have hτ_value : objective τ = ‖u‖[B₂] := by
        simp [objective, hτ_eq]
        field_simp [hu_pos.ne']
        ring
      exact hsInf_le_tau.trans_eq hτ_value

-- Proof sketch: use `√a = inf_{τ > 0} ((τ / 2) + a / (2τ))` with
-- `a = ‖F x + J x h‖[B₂]^2`, then exchange the two infima on the intrinsic weighted carrier.
/-- Lemma 4.4.8: for positive regularization, the canonical weighted optimal-value owner equals
the infimum of the reduced positive-`τ` objective written in the explicit `B`-induced norms. -/
theorem modifiedGaussNewtonWeightedAuxiliaryValue_eq_sInf_weightedTauObjective
    (M : NNRealˣ) :
    modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x M =
      sInf (range fun τ : NNRealˣ ↦
        ((τ : ℝ) / 2 : ℝ) +
          sInf (range fun h : PrimalSpace B₁ ↦
            (1 / (2 * (τ : ℝ)) : ℝ) * ‖F x + J x h‖[B₂] ^ (2 : ℕ) +
              (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ)))) := by
  let objective : PrimalSpace B₁ → ℝ := fun h ↦
    ‖F x + J x h‖[B₂] + (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ))
  let tauObjective : NNRealˣ → PrimalSpace B₁ → ℝ := fun τ h ↦
    ((τ : ℝ) / 2 : ℝ) + (1 / (2 * (τ : ℝ)) : ℝ) * ‖F x + J x h‖[B₂] ^ (2 : ℕ) +
      (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ))
  let reducedObjective : NNRealˣ → ℝ := fun τ ↦
    ((τ : ℝ) / 2 : ℝ) + sInf (range fun h : PrimalSpace B₁ ↦
      (1 / (2 * (τ : ℝ)) : ℝ) * ‖F x + J x h‖[B₂] ^ (2 : ℕ) +
        (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ)))
  have hobjective_nonempty : (range objective).Nonempty := by
    refine ⟨objective 0, ⟨0, rfl⟩⟩
  have hobjective_bddBelow : BddBelow (range objective) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨h, rfl⟩
    have hnorm_nonneg : 0 ≤ ‖F x + J x h‖[B₂] := by
      positivity
    have hquad_nonneg : 0 ≤ (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ)) := by
      positivity
    exact add_nonneg hnorm_nonneg hquad_nonneg
  have htau_slice_nonempty :
      ∀ τ : NNRealˣ, (range fun h : PrimalSpace B₁ ↦ tauObjective τ h).Nonempty := by
    intro τ
    refine ⟨tauObjective τ 0, ⟨0, rfl⟩⟩
  have htau_slice_bddBelow :
      ∀ τ : NNRealˣ, BddBelow (range fun h : PrimalSpace B₁ ↦ tauObjective τ h) := by
    intro τ
    refine ⟨0, ?_⟩
    rintro _ ⟨h, rfl⟩
    have htau_nonneg : 0 ≤ ((τ : ℝ) / 2 : ℝ) := by positivity
    have hresidual_nonneg :
        0 ≤ (1 / (2 * (τ : ℝ)) : ℝ) * ‖F x + J x h‖[B₂] ^ (2 : ℕ) := by
      positivity
    have hquad_nonneg : 0 ≤ (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ)) := by
      positivity
    simpa [tauObjective, add_assoc, add_left_comm, add_comm] using
      add_nonneg (add_nonneg htau_nonneg hresidual_nonneg) hquad_nonneg
  have hobjective_eq_tauInf :
      ∀ h : PrimalSpace B₁,
        objective h = sInf (range fun τ : NNRealˣ ↦ tauObjective τ h) := by
    intro h
    let residualObjective : NNRealˣ → ℝ := fun τ ↦
      ((τ : ℝ) / 2 : ℝ) + (1 / (2 * (τ : ℝ)) : ℝ) * ‖F x + J x h‖[B₂] ^ (2 : ℕ)
    let quadraticPenalty : ℝ := (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ))
    have hresidual_nonempty : (range residualObjective).Nonempty := by
      refine ⟨residualObjective 1, ⟨1, rfl⟩⟩
    have hresidual_bddBelow : BddBelow (range residualObjective) := by
      refine ⟨‖F x + J x h‖[B₂], ?_⟩
      rintro _ ⟨τ, rfl⟩
      exact bInducedNorm_le_positive_tau_quadratic (B₂ := B₂) (u := F x + J x h) τ
    -- First rewrite the residual norm by the scalar positive-`τ` infimum, then
    -- translate by the fixed quadratic penalty.
    calc
      objective h = ‖F x + J x h‖[B₂] + quadraticPenalty := by
        simp [objective, quadraticPenalty]
      _ = sInf (range residualObjective) + quadraticPenalty := by
        rw [bInducedNorm_eq_sInf_positive_tau_quadratic (B₂ := B₂) (u := F x + J x h)]
      _ = sInf (range fun τ : NNRealˣ ↦ residualObjective τ + quadraticPenalty) := by
        rw [← sInf_range_add_const residualObjective quadraticPenalty
          hresidual_nonempty hresidual_bddBelow]
      _ = sInf (range fun τ : NNRealˣ ↦ tauObjective τ h) := by
        simp [residualObjective, tauObjective, quadraticPenalty, add_left_comm, add_comm]
  have hreduced_eq_slice :
      ∀ τ : NNRealˣ,
        reducedObjective τ = sInf (range fun h : PrimalSpace B₁ ↦ tauObjective τ h) := by
    intro τ
    let sliceObjective : PrimalSpace B₁ → ℝ := fun h ↦
      (1 / (2 * (τ : ℝ)) : ℝ) * ‖F x + J x h‖[B₂] ^ (2 : ℕ) +
        (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ))
    have hslice_nonempty : (range sliceObjective).Nonempty := by
      refine ⟨sliceObjective 0, ⟨0, rfl⟩⟩
    have hslice_bddBelow : BddBelow (range sliceObjective) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨h, rfl⟩
      have hresidual_nonneg :
          0 ≤ (1 / (2 * (τ : ℝ)) : ℝ) * ‖F x + J x h‖[B₂] ^ (2 : ℕ) := by
        positivity
      have hquad_nonneg : 0 ≤ (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ)) := by
        positivity
      simpa [sliceObjective] using add_nonneg hresidual_nonneg hquad_nonneg
    -- Move the step-independent `τ / 2` term through the inner infimum.
    calc
      reducedObjective τ = ((τ : ℝ) / 2 : ℝ) + sInf (range sliceObjective) := by
        simp [reducedObjective, sliceObjective]
      _ = sInf (range sliceObjective) + ((τ : ℝ) / 2 : ℝ) := by ring
      _ = sInf (range fun h : PrimalSpace B₁ ↦ sliceObjective h + ((τ : ℝ) / 2 : ℝ)) := by
        rw [← sInf_range_add_const sliceObjective (((τ : ℝ) / 2 : ℝ))
          hslice_nonempty hslice_bddBelow]
      _ = sInf (range fun h : PrimalSpace B₁ ↦ ((τ : ℝ) / 2 : ℝ) + sliceObjective h) := by
        simp [add_comm]
      _ = sInf (range fun h : PrimalSpace B₁ ↦ tauObjective τ h) := by
        simp [sliceObjective, tauObjective, add_left_comm, add_comm]
  have hobjective_le_reduced :
      ∀ τ : NNRealˣ, sInf (range objective) ≤ reducedObjective τ := by
    intro τ
    rw [hreduced_eq_slice τ]
    -- Every pointwise `τ`-slice dominates the original objective.
    refine le_csInf (htau_slice_nonempty τ) ?_
    rintro _ ⟨h, rfl⟩
    have hsInf_le_objective : sInf (range objective) ≤ objective h := by
      exact csInf_le hobjective_bddBelow ⟨h, rfl⟩
    have hobjective_le_tau : objective h ≤ tauObjective τ h := by
      -- Add the fixed quadratic penalty to the scalar norm majorant.
      calc
        objective h =
            ‖F x + J x h‖[B₂] + (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ)) := by
          simp [objective]
        _ ≤
            (((τ : ℝ) / 2 : ℝ) +
                (1 / (2 * (τ : ℝ)) : ℝ) * ‖F x + J x h‖[B₂] ^ (2 : ℕ)) +
              (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ)) := by
          have hmajorant :=
            bInducedNorm_le_positive_tau_quadratic (B₂ := B₂) (u := F x + J x h) τ
          linarith
        _ = tauObjective τ h := by
          rfl
    exact hsInf_le_objective.trans hobjective_le_tau
  have hmain_lower :
      sInf (range objective) ≤ sInf (range reducedObjective) := by
    -- Every reduced `τ`-slice dominates the original objective, so the original
    -- infimum is a lower bound.
    refine le_csInf ?_ ?_
    · exact ⟨reducedObjective 1, ⟨1, rfl⟩⟩
    · rintro _ ⟨τ, rfl⟩
      exact hobjective_le_reduced τ
  have hreduced_bddBelow : BddBelow (range reducedObjective) := by
    refine ⟨sInf (range objective), ?_⟩
    rintro _ ⟨τ, rfl⟩
    exact hobjective_le_reduced τ
  have hmain_upper :
      sInf (range reducedObjective) ≤ sInf (range objective) := by
    -- Conversely, the reduced infimum is below every original slice because each
    -- original slice is the infimum of its own positive-`τ` majorants.
    refine le_csInf hobjective_nonempty ?_
    rintro _ ⟨h, rfl⟩
    have hslice_lower :
        sInf (range reducedObjective) ≤ sInf (range fun τ : NNRealˣ ↦ tauObjective τ h) := by
      refine le_csInf ?_ ?_
      · exact ⟨tauObjective 1 h, ⟨1, rfl⟩⟩
      · rintro _ ⟨τ, rfl⟩
        have hsInf_le_reduced : sInf (range reducedObjective) ≤ reducedObjective τ := by
          exact csInf_le hreduced_bddBelow ⟨τ, rfl⟩
        have hreduced_le_tau : reducedObjective τ ≤ tauObjective τ h := by
          rw [hreduced_eq_slice τ]
          exact csInf_le (htau_slice_bddBelow τ) ⟨h, rfl⟩
        exact hsInf_le_reduced.trans hreduced_le_tau
    simpa [hobjective_eq_tauInf h] using hslice_lower
  -- Combine the positive-regime bridge with the two infimum inequalities.
  calc
    modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x M = sInf (range objective) := by
      simpa [objective] using
        modifiedGaussNewtonOptimalValue_weighted_eq_sInf_range_bInducedNorm B₁ B₂ F J x M
    _ = sInf (range reducedObjective) := le_antisymm hmain_lower hmain_upper
    _ = sInf (range fun τ : NNRealˣ ↦
          ((τ : ℝ) / 2 : ℝ) +
            sInf (range fun h : PrimalSpace B₁ ↦
              (1 / (2 * (τ : ℝ)) : ℝ) * ‖F x + J x h‖[B₂] ^ (2 : ℕ) +
                (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ)))) := by
      simp [reducedObjective]

end AuxiliaryValue

end
