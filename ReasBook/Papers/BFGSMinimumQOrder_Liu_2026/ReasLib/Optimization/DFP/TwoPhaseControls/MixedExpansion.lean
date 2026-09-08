module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformAt
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondJetConcrete
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RecoveryAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RecoveryDerivative
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RecoveryConcrete
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RecoveryJetAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RawStepAdapters
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RawSignInvariance
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm

public section

namespace DFP.TwoLeg.Mixed

/- The source estimates retain only coefficients below the displayed remainder order.
   This local interface records exactly that truncated information and leaves the top
   Taylor coefficient to the compact coefficient-bound argument below. -/

open scoped BigOperators

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale), a
truncated independent-radius germ records regularity and only the coefficients below
its remainder order. -/
structure IndependentRadiusTruncatedGerm
    (f : (ℝ × ℝ × ℝ) → ℝ → ℝ) (K : Set (ℝ × ℝ × ℝ)) (m : ℕ)
    (coeff : Fin m → (ℝ × ℝ × ℝ) → ℝ) : Prop where
  regularity : ∀ θ, θ ∈ K →
    ContDiffAt ℝ m (Function.uncurry f) (θ, 0)
  coefficient_eq : ∀ (n : Fin m) (θ : ℝ × ℝ × ℝ), θ ∈ K →
    (FiniteTaylorJet.ofFunction ℝ m (f θ) 0).scalarCoeff n.castSucc = coeff n θ

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale),
the full scalar Taylor sum splits into its lower coefficients and the top coefficient. -/
lemma truncatedTaylor_sum_decomposition
    (m : ℕ) (a : Fin (m + 1) → ℝ) (r : ℝ) :
    (∑ n : Fin (m + 1), a n * r ^ (n : ℕ)) =
      (∑ n : Fin m, a n.castSucc * r ^ (n : ℕ)) +
        a (Fin.last m) * r ^ m := by
  rw [Fin.sum_univ_castSucc]
  rfl

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale),
a truncated coefficient germ yields some positive compact-uniform remainder constant. -/
theorem uniformRemainderOn_of_independentRadiusTruncatedGerm
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)} {m : ℕ}
    {coeff : Fin m → (ℝ × ℝ × ℝ) → ℝ}
    (_hm : 0 < m) (hK : IsCompact K)
    (hGerm : IndependentRadiusTruncatedGerm f K m coeff) :
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ f θ r - ∑ n : Fin m, coeff n θ * r ^ (n : ℕ))
      K C (m : ℝ) := by
  -- The full order-m Taylor remainder is uniformly bounded with coefficient one.
  have hJet := FiniteTaylorJet.uniformRemainderOn_of_contDiffAt m f 0 K hK
    (fun θ hθ ↦ hGerm.regularity θ hθ) 1 one_pos
  obtain ⟨δ, hδ, hbound⟩ := FiniteTaylorJet.IsUniformRemainderOn.bound hJet
  -- Compactness also bounds the unprescribed degree-m coefficient.
  obtain ⟨B, hB, hcoeff⟩ := FiniteTaylorJet.uniformCoeffBounds_of_contDiffAt m f 0 K hK
    (fun θ hθ ↦ hGerm.regularity θ hθ) ⟨m, Nat.lt_succ_self m⟩
  have hC : 0 < 1 + B := by linarith
  refine ⟨1 + B, hC, ?_⟩
  refine Asymptotics.IsUniformRemainderOn.of_bound hδ ?_
  intro θ hθ r hr
  let J := FiniteTaylorJet.ofFunction ℝ m (f θ) 0
  let top : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  have htopnorm : ‖J.scalarCoeff top‖ ≤ B := by
    rw [FiniteTaylorJet.scalarCoeff_apply]
    calc
      ‖J.coeff top (fun _ ↦ 1)‖ ≤ ‖J.coeff top‖ * ∏ _ : Fin (m : ℕ), ‖(1 : ℝ)‖ :=
        (J.coeff top).le_opNorm _
      _ = ‖J.coeff top‖ := by simp
      _ ≤ B := by simpa only [J, top] using hcoeff θ hθ
  have hfull := hbound θ hθ r hr
  have htopbound : ‖J.scalarCoeff top * r ^ m‖ ≤ B * |r| ^ (m : ℝ) := by
    calc
      ‖J.scalarCoeff top * r ^ m‖ = ‖J.scalarCoeff top‖ * |r| ^ m := by
        simp only [norm_mul, Real.norm_eq_abs, abs_pow]
      _ ≤ B * |r| ^ m := by
        exact mul_le_mul_of_nonneg_right htopnorm (by positivity)
      _ = B * |r| ^ (m : ℝ) := by
        rw [Real.rpow_natCast]
  have hdecomp := truncatedTaylor_sum_decomposition m
    (fun n ↦ J.scalarCoeff n) r
  have hcoefflow : ∀ n : Fin m, J.scalarCoeff n.castSucc = coeff n θ := by
    intro n
    simpa only [J] using hGerm.coefficient_eq n θ hθ
  have hresidual_eq :
      f θ r - ∑ n : Fin m, coeff n θ * r ^ (n : ℕ) =
        J.remainder (f θ) 0 r + J.scalarCoeff top * r ^ m := by
    rw [FiniteTaylorJet.remainder_def, FiniteTaylorJet.eval_eq_sum_smul_scalarCoeff,
      zero_add]
    simp only [smul_eq_mul]
    have hdecomp' :
        (∑ n : Fin (m + 1), r ^ (n : ℕ) * J.scalarCoeff n) =
          (∑ n : Fin m, r ^ (n : ℕ) * J.scalarCoeff n.castSucc) +
            r ^ m * J.scalarCoeff top := by
      calc
        (∑ n : Fin (m + 1), r ^ (n : ℕ) * J.scalarCoeff n) =
            ∑ n : Fin (m + 1), J.scalarCoeff n * r ^ (n : ℕ) := by
              apply Finset.sum_congr rfl
              intro n hn
              ring
        _ = (∑ n : Fin m, J.scalarCoeff n.castSucc * r ^ (n : ℕ)) +
            J.scalarCoeff top * r ^ m := hdecomp
        _ = (∑ n : Fin m, r ^ (n : ℕ) * J.scalarCoeff n.castSucc) +
            r ^ m * J.scalarCoeff top := by
              apply congrArg₂ (· + ·)
              · apply Finset.sum_congr rfl
                intro n hn
                ring
              · ring
    rw [hdecomp']
    rw [show (∑ n : Fin m, r ^ (n : ℕ) * J.scalarCoeff n.castSucc) =
        ∑ n : Fin m, coeff n θ * r ^ (n : ℕ) by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hcoefflow n]
          ring]
    ring
  have hrembound : ‖J.remainder (f θ) 0 r‖ ≤ 1 * |r| ^ (m : ℝ) := by
    simpa only [J, Real.norm_eq_abs, Real.rpow_natCast] using hfull
  rw [hresidual_eq]
  calc
    ‖J.remainder (f θ) 0 r + J.scalarCoeff top * r ^ m‖ ≤
        ‖J.remainder (f θ) 0 r‖ + ‖J.scalarCoeff top * r ^ m‖ := norm_add_le _ _
    _ ≤ 1 * |r| ^ (m : ℝ) + B * |r| ^ (m : ℝ) :=
      add_le_add hrembound htopbound
    _ = (1 + B) * |r| ^ (m : ℝ) := by ring

/-- The mixed input at zero radius is the canonical base state for Appendix Lemma A.5
    (Mixed-variable expansion of radius, shape, and scale). -/
lemma mixedInput_zero (θ : ℝ × ℝ × ℝ) :
    input θ 0 = (0, 2, 1) := by
  rw [input_apply]
  norm_num

/-- The mixed map evaluated on its zero-radius input is the canonical base output for
    Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale). -/
lemma mixedMap_input_zero (θ : ℝ × ℝ × ℝ) :
    map θ.1 (input θ 0) = (0, 2, 1) := by
  rw [mixedInput_zero, map_zero]

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale), the
constant Taylor coefficient of the mixed radius output is zero. -/
lemma mixedRadius_constantCoeff (θ : ℝ × ℝ × ℝ) :
    (FiniteTaylorJet.ofFunction ℝ 3
      (fun r : ℝ ↦ (map θ.1 (input θ r)).1) 0).scalarCoeff
        ⟨0, by norm_num⟩ = 0 := by
  rw [FiniteTaylorJet.scalarCoeff_ofFunction]
  simp only [iteratedDeriv_zero]
  rw [mixedMap_input_zero]
  norm_num

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale), the
constant Taylor coefficient of the mixed shape output is two. -/
lemma mixedShape_constantCoeff (θ : ℝ × ℝ × ℝ) :
    (FiniteTaylorJet.ofFunction ℝ 2
      (fun r : ℝ ↦ (map θ.1 (input θ r)).2.1) 0).scalarCoeff
        ⟨0, by norm_num⟩ = 2 := by
  rw [FiniteTaylorJet.scalarCoeff_ofFunction]
  simp only [iteratedDeriv_zero]
  rw [mixedMap_input_zero]
  norm_num

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale), the
constant Taylor coefficient of the mixed high-scale output is one. -/
lemma mixedScale_constantCoeff (θ : ℝ × ℝ × ℝ) :
    (FiniteTaylorJet.ofFunction ℝ 2
      (fun r : ℝ ↦ (map θ.1 (input θ r)).2.2) 0).scalarCoeff
        ⟨0, by norm_num⟩ = 1 := by
  rw [FiniteTaylorJet.scalarCoeff_ofFunction]
  simp only [iteratedDeriv_zero]
  rw [mixedMap_input_zero]
  norm_num

/- The compact parameter region supplies the signed-control bound needed by the
   missing independent-radius factorization.  Keep this extraction separate so
   the eventual normal-form proof can consume it without reopening membership. -/

/-- Membership in `parameterSet β B` bounds the signed control coordinate by `1 / 4`. -/
lemma parameterSetControlAbsLt (β B : ℝ) (hβ_small : β < 1 / 4)
    {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ parameterSet β B) :
    |θ.1| < (1 / 4 : ℝ) := by
  have hinterval := (mem_parameterSet θ β B).mp hθ |>.1
  have habs : |θ.1| ≤ β := by
    exact abs_le.mpr hinterval
  linarith

/- The canonical input itself is polynomial in the independent radius.  This
   isolates the regularity available before the canceled two-leg map is used. -/

/-- The canonical input map is `C^m` at every independent-radius base point for
    Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale). -/
lemma input_uncurry_contDiffAt (m : ℕ) (θ : ℝ × ℝ × ℝ) :
    ContDiffAt ℝ m (Function.uncurry input) (θ, 0) := by
  have hpoly : ContDiffAt ℝ m
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (z.2, 2 + z.1.2.1 * z.1.1 * z.2, 1 + z.1.2.2 * z.1.1 * z.2)) (θ, 0) := by
    fun_prop
  have hinput : Function.uncurry input =
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (z.2, 2 + z.1.2.1 * z.1.1 * z.2, 1 + z.1.2.2 * z.1.1 * z.2)) := by
    funext z
    exact input_apply z.1.1 z.1.2.1 z.1.2.2 z.2
  rw [hinput]
  exact hpoly

/- Exact equality of two scalar families transports a truncated independent-radius
   germ without reopening either its regularity or coefficient obligations. -/

/-- Exact pointwise equality preserves an independent-radius truncated germ. -/
lemma independentRadiusTruncatedGerm_congr
    {f g : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)}
    {m : ℕ} {coeff : Fin m → (ℝ × ℝ × ℝ) → ℝ}
    (hfg : ∀ θ r, f θ r = g θ r)
    (hGerm : IndependentRadiusTruncatedGerm g K m coeff) :
    IndependentRadiusTruncatedGerm f K m coeff := by
  refine ⟨?_, ?_⟩
  · intro θ hθ
    have huncurry : Function.uncurry f = Function.uncurry g := by
      funext z
      exact hfg z.1 z.2
    rw [huncurry]
    exact hGerm.regularity θ hθ
  · intro n θ hθ
    have hscalar : f θ = g θ := by
      funext r
      exact hfg θ r
    rw [hscalar]
    exact hGerm.coefficient_eq n θ hθ

/- Eventual equality is the transport interface needed when a rational normal form
   agrees with the removable map only on a neighborhood of the base radius. -/

/-- An eventual equality of scalar families preserves an independent-radius truncated germ. -/
lemma independentRadiusTruncatedGerm_of_eventuallyEq
    {f g : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)}
    {m : ℕ} {coeff : Fin m → (ℝ × ℝ × ℝ) → ℝ}
    (hregular : ∀ θ, θ ∈ K →
      Function.uncurry f =ᶠ[nhds (θ, 0)] Function.uncurry g)
    (hscalar : ∀ θ, θ ∈ K → f θ =ᶠ[nhds 0] g θ)
    (hGerm : IndependentRadiusTruncatedGerm g K m coeff) :
    IndependentRadiusTruncatedGerm f K m coeff := by
  refine ⟨?_, ?_⟩
  · intro θ hθ
    exact (hGerm.regularity θ hθ).congr_of_eventuallyEq (hregular θ hθ)
  · intro n θ hθ
    have hcoeff := hGerm.coefficient_eq n θ hθ
    rw [FiniteTaylorJet.scalarCoeff_ofFunction]
    rw [← hcoeff]
    rw [FiniteTaylorJet.scalarCoeff_ofFunction]
    congr 1
    exact (hscalar θ hθ).iteratedDeriv_eq n

/-- The raw evaluator agrees with the public map on the independent-radius input away
    from the removable radius-zero branch. -/
lemma independentMapRaw_input_eq_map (θ : ℝ × ℝ × ℝ) (r : ℝ) (hr : r ≠ 0) :
    independentMapRaw θ.1 r (input θ r).2.1 (input θ r).2.2 =
      map θ.1 (input θ r) := by
  rw [input_apply]
  exact independentMapRaw_eq_map θ.1 r
    (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) hr

/- The normal-form regularity is already supplied by the analytic recovery interface.
   These projection lemmas keep the final transport proof at the scalar level. -/

/-- The radius projection of the independent-radius normal form is finitely smooth at
    every zero-radius base point. -/
lemma independentRadiusNormalForm_radius_contDiffAt (m : ℕ) (θ : ℝ × ℝ × ℝ) :
    ContDiffAt ℝ m
      (Function.uncurry (fun θ r ↦ (independentRadiusNormalForm θ r).1)) (θ, 0) := by
  exact (independentRadiusNormalForm_contDiffAt_of_secondFactors m θ).fst

/-- The shape projection of the independent-radius normal form is finitely smooth at
    every zero-radius base point. -/
lemma independentRadiusNormalForm_shape_contDiffAt (m : ℕ) (θ : ℝ × ℝ × ℝ) :
    ContDiffAt ℝ m
      (Function.uncurry (fun θ r ↦ (independentRadiusNormalForm θ r).2.1)) (θ, 0) := by
  exact (independentRadiusNormalForm_contDiffAt_of_secondFactors m θ).snd.fst

/-- The high-scale projection of the independent-radius normal form is finitely smooth at
    every zero-radius base point. -/
lemma independentRadiusNormalForm_scale_contDiffAt (m : ℕ) (θ : ℝ × ℝ × ℝ) :
    ContDiffAt ℝ m
      (Function.uncurry (fun θ r ↦ (independentRadiusNormalForm θ r).2.2)) (θ, 0) := by
  exact (independentRadiusNormalForm_contDiffAt_of_secondFactors m θ).snd.snd

/- The zero-radius values and the first radius coefficient are independent of the
   unresolved two-leg transport calculation. -/

/-- The normal-form radius has zero constant Taylor coefficient. -/
lemma independentRadiusNormalForm_radius_constantCoeff (θ : ℝ × ℝ × ℝ) :
    (FiniteTaylorJet.ofFunction ℝ 3
      (fun r : ℝ ↦ (independentRadiusNormalForm θ r).1) 0).scalarCoeff
        ⟨0, by norm_num⟩ = 0 := by
  rw [FiniteTaylorJet.scalarCoeff_ofFunction]
  simp only [iteratedDeriv_zero]
  rw [independentRadiusNormalForm_zero]
  norm_num

/-- The normal-form radius has unit linear Taylor coefficient. -/
lemma independentRadiusNormalForm_radius_linearCoeff (θ : ℝ × ℝ × ℝ) :
    (FiniteTaylorJet.ofFunction ℝ 3
      (fun r : ℝ ↦ (independentRadiusNormalForm θ r).1) 0).scalarCoeff
        ⟨1, by norm_num⟩ = 1 := by
  rw [FiniteTaylorJet.scalarCoeff_ofFunction]
  simp only [Nat.factorial, Nat.cast_one, inv_one, one_smul]
  rw [iteratedDeriv_one]
  have hfun : (fun r : ℝ ↦ (independentRadiusNormalForm θ r).1) =
      (fun r : ℝ ↦ r * (independentRadiusRecoveryFactors (θ, r)).1) := by
    funext r
    exact congrArg Prod.fst (independentRadiusNormalForm_eq_recoveryFactors θ r)
  -- Differentiate the explicit radius product; only the factor value at zero is needed.
  rw [hfun]
  have hpath : DifferentiableAt ℝ (fun r : ℝ ↦ (θ, r)) 0 := by
    fun_prop
  have hpair : DifferentiableAt ℝ
      (fun r : ℝ ↦ independentRadiusRecoveryFactors (θ, r)) 0 :=
    (independentRadiusRecoveryFactors_analyticAt_of_secondFactors θ).differentiableAt.comp
      0 hpath
  have hfactor : DifferentiableAt ℝ
      (fun r : ℝ ↦ (independentRadiusRecoveryFactors (θ, r)).1) 0 := by
    exact differentiableAt_fst.comp 0 hpair
  have hderiv := deriv_mul (x := (0 : ℝ))
    (c := fun r : ℝ ↦ r)
    (d := fun r : ℝ ↦ (independentRadiusRecoveryFactors (θ, r)).1)
    differentiableAt_id hfactor
  have hmul : (fun r : ℝ ↦ r) *
      (fun r : ℝ ↦ (independentRadiusRecoveryFactors (θ, r)).1) =
      (fun r : ℝ ↦ r * (independentRadiusRecoveryFactors (θ, r)).1) := by
    funext r
    rfl
  rw [← hmul, hderiv]
  simp only [deriv_id', one_mul, zero_mul, add_zero]
  rw [independentRadiusRecoveryFactors_zero]
  norm_num

/-- The normal-form shape has constant Taylor coefficient two. -/
lemma independentRadiusNormalForm_shape_constantCoeff (θ : ℝ × ℝ × ℝ) :
    (FiniteTaylorJet.ofFunction ℝ 2
      (fun r : ℝ ↦ (independentRadiusNormalForm θ r).2.1) 0).scalarCoeff
        ⟨0, by norm_num⟩ = 2 := by
  rw [FiniteTaylorJet.scalarCoeff_ofFunction]
  simp only [iteratedDeriv_zero]
  rw [independentRadiusNormalForm_zero]
  norm_num

/-- The normal-form high-scale factor has constant Taylor coefficient one. -/
lemma independentRadiusNormalForm_scale_constantCoeff (θ : ℝ × ℝ × ℝ) :
    (FiniteTaylorJet.ofFunction ℝ 2
      (fun r : ℝ ↦ (independentRadiusNormalForm θ r).2.2) 0).scalarCoeff
        ⟨0, by norm_num⟩ = 1 := by
  rw [FiniteTaylorJet.scalarCoeff_ofFunction]
  simp only [iteratedDeriv_zero]
  rw [independentRadiusNormalForm_zero]
  norm_num

/-
/-- The first normalized spectral and gradient factors have their explicit first jets. -/
lemma independentRadiusFirstFactorJets (θ : ℝ × ℝ × ℝ) :
    HasDerivAt (fun r ↦ independentRadiusFirstSpectral (θ, r))
        (θ.1 * (2 * θ.2.2 + θ.2.1 + 4), -2 * θ.1) 0 ∧
      HasDerivAt (fun r ↦ independentRadiusFirstGradient (θ, r))
        (-2 * θ.1, θ.1 * (θ.2.1 - 6) / 3) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let b : ℝ → ℝ := fun _ ↦ θ.1
  let P : ℝ → ℝ := fun _ ↦ θ.2.1
  let J : ℝ → ℝ := fun _ ↦ θ.2.2
  let one : ℝ → ℝ := fun _ ↦ 1
  let two : ℝ → ℝ := fun _ ↦ 2
  let three : ℝ → ℝ := fun _ ↦ 3
  let p : ℝ → ℝ := (P * b) * X + two
  let h : ℝ → ℝ := one + (J * b) * X
  let B : ℝ → ℝ := one + ((fun r ↦ 2 * (b * X) r) + X ^ 2)
  let C : ℝ → ℝ := (one + b * X) ^ 2 + p * (X ^ 2) * (b + X) ^ 2
  let a : ℝ → ℝ := h * p - h * (p ^ 2) * (X ^ 2) * (b + X) ^ 2 / C + one / B
  let c : ℝ → ℝ := one / B - h * p * X * (b + X) * (one + b * X) / C
  let d : ℝ → ℝ := h - h * (one + b * X) ^ 2 / C + one / B
  let q : ℝ → ℝ := one - (fun r ↦ 2 * ((p + one) * X * (b + X)) r) / (three * B)
  let u : ℝ → ℝ := p - (fun r ↦ 2 * ((p + one) * (one + b * X)) r) / (three * B)
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hb : HasDerivAt b 0 0 := hasDerivAt_const 0 θ.1
  have hP : HasDerivAt P 0 0 := hasDerivAt_const 0 θ.2.1
  have hJ : HasDerivAt J 0 0 := hasDerivAt_const 0 θ.2.2
  have hp : HasDerivAt p (θ.1 * θ.2.1) 0 := by
    exact ((hP.mul hb).mul hX).add (hasDerivAt_const 0 (2 : ℝ)) |>.congr_deriv
      (g' := θ.1 * θ.2.1) (by simp [p, X, b, P, two]; ring)
  have hh : HasDerivAt h (θ.1 * θ.2.2) 0 := by
    exact (hasDerivAt_const 0 (1 : ℝ)).add ((hJ.mul hb).mul hX) |>.congr_deriv
      (g' := θ.1 * θ.2.2) (by simp [h, X, b, J, one]; ring)
  have hB : HasDerivAt B (2 * θ.1) 0 := by
    exact (hasDerivAt_const 0 (1 : ℝ)).add
      (((hb.mul hX).const_mul 2).add (hX.pow 2)) |>.congr_deriv
      (g' := 2 * θ.1) (by simp [B, X, b, one])
  have hC : HasDerivAt C (2 * θ.1) 0 := by
    exact ((hasDerivAt_const 0 (1 : ℝ)).add (hb.mul hX)).pow 2 |>.add
      ((hp.mul (hX.pow 2)).mul ((hb.add hX).pow 2)) |>.congr_deriv
      (g' := 2 * θ.1) (by simp [C, X, b, p, P, one, two])
  have hB0 : B 0 ≠ 0 := by norm_num [B, X, b]
  have hC0 : C 0 ≠ 0 := by norm_num [C, X, b, p, P]
  have ha : HasDerivAt a (θ.1 * (2 * θ.2.2 + θ.2.1 - 2)) 0 := by
    exact (hh.mul hp).sub
      ((((hh.mul (hp.pow 2)).mul (hX.pow 2)).mul ((hb.add hX).pow 2)).div hC hC0) |>.add
      ((hasDerivAt_const 0 (1 : ℝ)).div hB hB0) |>.congr_deriv
      (g' := θ.1 * (2 * θ.2.2 + θ.2.1 - 2))
      (by simp [a, X, b, P, J, p, h, B, C, one, two]; ring)
  have hc : HasDerivAt c (-4 * θ.1) 0 := by
    have hterm := ((((hh.mul hp).mul hX).mul (hb.add hX)).mul
      ((hb.mul hX).const_add 1)).div hC hC0
    have h' := ((hasDerivAt_const 0 (1 : ℝ)).div hB hB0).sub hterm
    apply h'.congr_deriv (g' := -4 * θ.1)
    simp [c, X, b, P, J, p, h, B, C, one, two]
    ring
  have hd : HasDerivAt d (-2 * θ.1) 0 := by
    have hterm := (hh.mul (((hb.mul hX).const_add 1).pow 2)).div hC hC0
    exact (hh.sub hterm).add ((hasDerivAt_const 0 (1 : ℝ)).div hB hB0) |>.congr_deriv
      (g' := -2 * θ.1) (by simp [d, X, b, P, J, p, h, B, C, one, two]; ring)
  have hq : HasDerivAt q (-2 * θ.1) 0 := by
    have hden := (hasDerivAt_const 0 (3 : ℝ)).mul hB
    have hden0 : ((fun _ : ℝ ↦ (3 : ℝ)) * B) 0 ≠ 0 := by
      norm_num [B, X, b]
    have hnum := (((hp.add (hasDerivAt_const 0 (1 : ℝ))).mul hX).mul (hb.add hX)).const_mul 2
    have h' := (hasDerivAt_const 0 (1 : ℝ)).sub (hnum.div hden hden0)
    exact h'.congr_deriv (g' := -2 * θ.1) (by simp [q, X, b, P, p, B, one, two, three]; ring)
  have hu : HasDerivAt u (θ.1 * (θ.2.1 - 6) / 3) 0 := by
    have hden := (hasDerivAt_const 0 (3 : ℝ)).mul hB
    have hden0 : ((fun _ : ℝ ↦ (3 : ℝ)) * B) 0 ≠ 0 := by
      norm_num [B, X, b]
    have hnum := ((hp.add (hasDerivAt_const 0 (1 : ℝ))).mul
      ((hb.mul hX).const_add 1)).const_mul 2
    have h' := hp.sub (hnum.div hden hden0)
    exact h'.congr_deriv (g' := θ.1 * (θ.2.1 - 6) / 3)
      (by simp [u, X, b, P, p, B, one, two, three]; ring)
  let mA : ℝ → ℝ := X ^ 2 * a
  let mC : ℝ → ℝ := X * c
  let mD : ℝ → ℝ := d
  have hmA0 : mA 0 = 0 := by simp [mA, X]
  have hmC0 : mC 0 = 0 := by simp [mC, X]
  have hmD0 : mD 0 = 1 := by simp [mD, d, X, b, P, J, p, h, B, C]
  have hmA : HasDerivAt mA 0 0 := by
    exact ((hX.pow 2).mul ha).congr_deriv (g' := 0) (by simp [mA, X]; ring)
  have hmC : HasDerivAt mC 1 0 := by
    have hc0 : c 0 = 1 := by simp [c, X, b, P, J, p, h, B, C]
    exact (hX.mul hc).congr_deriv (g' := 1) (by simp [mC, X, hc0]; ring)
  have hmD : HasDerivAt mD (-2 * θ.1) 0 := hd
  let rad : ℝ → ℝ := fun r ↦ (mA r - mD r) ^ 2 + 4 * (mC r) ^ 2
  have hrad : HasDerivAt rad (-4 * θ.1) 0 := by
    exact ((hmA.sub hmD).pow 2).add ((hmC.pow 2).const_mul 4) |>.congr_deriv
      (g' := -4 * θ.1) (by simp [rad, hmA0, hmC0, hmD0]; ring)
  have hrad0 : rad 0 ≠ 0 := by simp [rad, hmA0, hmC0, hmD0]
  have hrad0val : rad 0 = 1 := by simp [rad, hmA0, hmC0, hmD0]
  let gap : ℝ → ℝ := fun r ↦ Real.sqrt (rad r)
  have hgap : HasDerivAt gap (-2 * θ.1) 0 := by
    exact (hrad.sqrt hrad0).congr_deriv (g' := -2 * θ.1)
      (by simp [gap, hrad0val])
  let high : ℝ → ℝ := fun r ↦ (mA r + mD r + gap r) / 2
  let low : ℝ → ℝ := fun r ↦ (mA r + mD r - gap r) / 2
  have hhigh : HasDerivAt high (-2 * θ.1) 0 := by
    exact ((hmA.add hmD).add hgap).div (hasDerivAt_const 0 (2 : ℝ)) (by norm_num) |>.congr_deriv
      (g' := -2 * θ.1) (by simp [high]; ring)
  have hlow : HasDerivAt low 0 0 := by
    exact ((hmA.add hmD).sub hgap).div (hasDerivAt_const 0 (2 : ℝ)) (by norm_num) |>.congr_deriv
      (g' := 0) (by simp [low]; ring)
  let denomRad : ℝ → ℝ := fun r ↦ (mD r - low r) ^ 2 + (mC r) ^ 2
  have hdenomRad : HasDerivAt denomRad (-4 * θ.1) 0 := by
    exact ((hmD.sub hlow).pow 2).add (hmC.pow 2) |>.congr_deriv
      (g' := -4 * θ.1) (by simp [denomRad, mD, low, mC, X]; ring)
  have hdenomRad0 : denomRad 0 ≠ 0 := by simp [denomRad, mD, low, mC, X, hmC0, hmD0, hrad0val]
  have hdenomRad0val : denomRad 0 = 1 := by simp [denomRad, mD, low, mC, X, hmC0, hmD0, hrad0val]
  let denom : ℝ → ℝ := fun r ↦ Real.sqrt (denomRad r)
  have hdenom : HasDerivAt denom (-2 * θ.1) 0 := by
    exact (hdenomRad.sqrt hdenomRad0).congr_deriv (g' := -2 * θ.1)
      (by simp [denom, hdenomRad0val])
  have hhigh0 : high 0 ≠ 0 := by norm_num [high, mA, mD, gap, rad, X, a, d]
  have hdenom0 : denom 0 ≠ 0 := by norm_num [denom, denomRad, mD, low, mC, X, a, d]
  let spectralLow : ℝ → ℝ := fun r ↦ (a r * d r - c r ^ 2) / high r
  let gradientLow : ℝ → ℝ := fun r ↦
    ((d r - low r) * q r - X r ^ 2 * c r * u r) / denom r
  let gradientHigh : ℝ → ℝ := fun r ↦
    (c r * q r + (d r - low r) * u r) / denom r
  have hSL : HasDerivAt spectralLow (θ.1 * (2 * θ.2.2 + θ.2.1 + 4)) 0 := by
    exact ((ha.mul hd).sub (hc.pow 2)).div hhigh hhigh0 |>.congr_deriv
      (g' := θ.1 * (2 * θ.2.2 + θ.2.1 + 4))
      (by simp [spectralLow, high, mA, mC, mD, gap, rad, denom, X, a, c, d]; ring)
  have hGL : HasDerivAt gradientLow (-2 * θ.1) 0 := by
    exact ((((hmD.sub hlow).mul hq).sub (((hX.pow 2).mul hc).mul hu)).div hdenom hdenom0)
      |>.congr_deriv (g' := -2 * θ.1)
      (by simp [gradientLow, denom, denomRad, low, high, gap, rad, mA, mC, mD,
        X, a, c, d, q, u]; ring)
  have hGH : HasDerivAt gradientHigh (θ.1 * (θ.2.1 - 6) / 3) 0 := by
    exact ((hc.mul hq).add ((hmD.sub hlow).mul hu)).div hdenom hdenom0 |>.congr_deriv
      (g' := θ.1 * (θ.2.1 - 6) / 3)
      (by simp [gradientHigh, denom, denomRad, low, high, gap, rad, mA, mC, mD,
        X, a, c, d, q, u]; ring)
  constructor
  · apply (hSL.prodMk hhigh).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun r ↦ by
      simp [independentRadiusFirstSpectral, independentRadiusFirstResiduals,
        independentRadiusFirstMetricTriple, independentFirstResiduals,
        spectralLow, high, mA, mC, mD, gap, rad, X, a, c, d]; ring)
  · apply (hGL.prodMk hGH).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun r ↦ by
      simp [independentRadiusFirstGradient, independentRadiusFirstResiduals,
        independentRadiusFirstGradientResiduals, independentFirstResiduals,
        independentFirstGradientResiduals, independentRadiusFirstMetricTriple,
        gradientLow, gradientHigh, denom, denomRad, low, high, gap, rad,
        mA, mC, mD, X, a, c, d, q, u]; ring)

-/

/-
The second-leg residuals are rational expressions in the first-leg factors. Keeping
this derivative calculation separate makes the later spectral and gradient jets use
only named numerator/denominator interfaces.
 /-- The normalized second-leg residual triple has its explicit first derivative at zero. -/
lemma independentRadiusSecondResiduals_hasDerivAt (θ : ℝ × ℝ × ℝ) :
    HasDerivAt
      (fun r ↦ independentSecondResiduals θ.1 r
        (independentRadiusFirstSpectral (θ, r)).1
        (independentRadiusFirstSpectral (θ, r)).2
        (independentRadiusFirstGradient (θ, r)).1
        (independentRadiusFirstGradient (θ, r)).2)
      (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3,
        (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3, 8 * θ.1)) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let L : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).1
  let H : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).2
  let Q : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).1
  let U : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).2
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hfirst := independentRadiusFirstFactorJets θ
  have hL := hfirst.1.hasFDerivAt.fst.hasDerivAt
  have hH := hfirst.1.hasFDerivAt.snd.hasDerivAt
  have hQ := hfirst.2.hasFDerivAt.fst.hasDerivAt
  have hU := hfirst.2.hasFDerivAt.snd.hasDerivAt
  have hL0 : L 0 = 2 := by
    simpa [L] using congrArg Prod.fst (independentRadiusFirstSpectral_zero θ)
  have hH0 : H 0 = 1 := by
    simpa [H] using congrArg Prod.snd (independentRadiusFirstSpectral_zero θ)
  have hQ0 : Q 0 = 1 := by
    simpa [Q] using congrArg Prod.fst (independentRadiusFirstGradient_zero θ)
  have hU0 : U 0 = 1 := by
    simpa [U] using congrArg Prod.snd (independentRadiusFirstGradient_zero θ)
  let w₁ : ℝ → ℝ := fun r ↦ r * L r * Q r - 2 * θ.1 * H r * U r
  let w₂ : ℝ → ℝ := fun r ↦ H r * U r - 2 * θ.1 * r * L r * Q r
  have hw₁ : HasDerivAt w₁
      (2 + 2 * θ.1 ^ 2 * (12 - θ.2.1) / 3) 0 := by
    have h := ((hX.mul hL).mul hQ).sub
      ((hH.mul hU).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [w₁, X, L, H, Q, U, hL0, hH0, hQ0, hU0]
    ring
  have hw₂ : HasDerivAt w₂
      (θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (hH.mul hU).sub
      (((hX.mul hL).mul hQ).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [w₂, X, L, H, Q, U, hL0, hH0, hQ0]
    ring
  let β : ℝ → ℝ := fun r ↦
    r * L r * Q r * w₁ r + H r * U r * w₂ r
  let γ : ℝ → ℝ := fun r ↦
    r ^ 2 * L r * (w₁ r) ^ 2 + H r * (w₂ r) ^ 2
  have hβ : HasDerivAt β (2 * θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (((hX.mul hL).mul hQ).mul hw₁).add ((hH.mul hU).mul hw₂)
    apply h.congr_deriv
    simp [β, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hγ : HasDerivAt γ (2 * θ.1 * (θ.2.1 - 27) / 3) 0 := by
    have h := (((hX.pow 2).mul hL).mul (hw₁.pow 2)).add
      (hH.mul (hw₂.pow 2))
    apply h.congr_deriv
    simp [γ, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hβ0 : β 0 ≠ 0 := by
    simp [β, w₁, w₂, hL0, hH0, hQ0, hU0]
  have hγ0 : γ 0 ≠ 0 := by
    simp [γ, w₁, w₂, hL0, hH0, hQ0, hU0]
  let a : ℝ → ℝ := fun r ↦
    L r - r ^ 2 * L r ^ 2 * (w₁ r) ^ 2 / γ r + L r ^ 2 * Q r ^ 2 / β r
  let c : ℝ → ℝ := fun r ↦
    -r * L r * H r * w₁ r * w₂ r / γ r + L r * Q r * H r * U r / β r
  let d : ℝ → ℝ := fun r ↦
    H r - H r ^ 2 * (w₂ r) ^ 2 / γ r + H r ^ 2 * U r ^ 2 / β r
  have ha : HasDerivAt a
      (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3) 0 := by
    have h := hL.sub
      (((((hX.pow 2).mul (hL.pow 2)).mul (hw₁.pow 2)).div hγ hγ0)).add
      (((hL.pow 2).mul (hQ.pow 2)).div hβ hβ0)
    apply h.congr_deriv
    simp [a, β, γ, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hc : HasDerivAt c
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) 0 := by
    have h :=
      (((((hX.mul hL).mul hH).mul hw₁).mul hw₂).div hγ hγ0).neg.add
        (((hL.mul hQ).mul hH).mul hU |>.div hβ hβ0)
    apply h.congr_deriv
    simp [c, β, γ, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hd : HasDerivAt d (8 * θ.1) 0 := by
    have h := hH.sub
      ((((hH.pow 2).mul (hw₂.pow 2)).div hγ hγ0)).add
      (((hH.pow 2).mul (hU.pow 2)).div hβ hβ0)
    apply h.congr_deriv
    simp [d, β, γ, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have htriple := ha.prodMk (hc.prodMk hd)
  apply htriple.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun r ↦ by
    simp [independentSecondResiduals, a, c, d, β, γ, w₁, w₂, X, L, H, Q, U]
    rfl)

/-- The normalized second-leg spectral pair has derivative
    `(b (2 J + P - 12), 8 b)` at zero radius. -/
lemma independentRadiusSecondSpectral_hasDerivAt (θ : ℝ × ℝ × ℝ) :
    HasDerivAt
      (fun r ↦ independentRadiusSecondSpectral (θ, r))
      (θ.1 * (2 * θ.2.2 + θ.2.1 - 12), 8 * θ.1) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let A : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).1
  let C : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2.1
  let D : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2.2
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hres := independentRadiusSecondResiduals_hasDerivAt θ
  have hA := hres.hasFDerivAt.fst.hasDerivAt
  have hC := hres.hasFDerivAt.snd.hasFDerivAt.fst.hasDerivAt
  have hD := hres.hasFDerivAt.snd.hasFDerivAt.snd.hasDerivAt
  have hA0 : A 0 = 6 := by
    simpa [A] using congrArg Prod.fst (independentRadiusSecondResiduals_zero θ)
  have hC0 : C 0 = 2 := by
    simpa [C] using congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.1)
      (independentRadiusSecondResiduals_zero θ)
  have hD0 : D 0 = 1 := by
    simpa [D] using congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.2)
      (independentRadiusSecondResiduals_zero θ)
  let mA : ℝ → ℝ := fun r ↦ X r ^ 2 * A r
  let mC : ℝ → ℝ := fun r ↦ X r * C r
  let mD : ℝ → ℝ := D
  have hmA : HasDerivAt mA 0 0 := by
    exact (hX.pow 2).mul hA |>.congr_deriv (g' := 0) (by simp [mA, X])
  have hmC : HasDerivAt mC 2 0 := by
    exact hX.mul hC |>.congr_deriv (g' := 2) (by simp [mC, X, hC0])
  have hmD : HasDerivAt mD (8 * θ.1) 0 := hD
  let rad : ℝ → ℝ := fun r ↦ (mA r - mD r) ^ 2 + 4 * (mC r) ^ 2
  have hrad : HasDerivAt rad (16 * θ.1) 0 := by
    exact ((hmA.sub hmD).pow 2).add ((hmC.pow 2).const_mul 4) |>.congr_deriv
      (g' := 16 * θ.1) (by simp [rad, mA, mC, mD, X, hA0, hC0, hD0]; ring)
  have hrad0 : rad 0 ≠ 0 := by
    simp [rad, mA, mC, mD, X, hA0, hC0, hD0]
  let gap : ℝ → ℝ := fun r ↦ Real.sqrt (rad r)
  have hgap : HasDerivAt gap (8 * θ.1) 0 := by
    exact (hrad.sqrt hrad0).congr_deriv (g' := 8 * θ.1)
      (by simp [gap, rad, mA, mC, mD, X, hA0, hC0, hD0])
  let high : ℝ → ℝ := fun r ↦ (mA r + mD r + gap r) / 2
  let low : ℝ → ℝ := fun r ↦ (mA r + mD r - gap r) / 2
  have hhigh : HasDerivAt high (8 * θ.1) 0 := by
    exact ((hmA.add hmD).add hgap).div (hasDerivAt_const 0 (2 : ℝ)) (by norm_num)
      |>.congr_deriv (g' := 8 * θ.1) (by simp [high]; ring)
  have hlow : HasDerivAt low 0 0 := by
    exact ((hmA.add hmD).sub hgap).div (hasDerivAt_const 0 (2 : ℝ)) (by norm_num)
      |>.congr_deriv (g' := 0) (by simp [low]; ring)
  have hhigh0 : high 0 ≠ 0 := by
    simp [high, mA, mC, mD, gap, rad, X, hA0, hC0, hD0]
  let spectralLow : ℝ → ℝ := fun r ↦ (A r * D r - C r ^ 2) / high r
  have hSL : HasDerivAt spectralLow
      (θ.1 * (2 * θ.2.2 + θ.2.1 - 12)) 0 := by
    exact ((hA.mul hD).sub (hC.pow 2)).div hhigh hhigh0 |>.congr_deriv
      (g' := θ.1 * (2 * θ.2.2 + θ.2.1 - 12))
      (by simp [spectralLow, high, mA, mC, mD, gap, rad, X, hA0, hC0, hD0]; ring)
  have hpair := hSL.prodMk hhigh
  apply hpair.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun r ↦ by
    simp [independentRadiusSecondSpectral, independentSecondSpectralFactors,
      spectralLow, high, low, gap, rad, mA, mC, mD, X, A, C, D]
    rfl)

/-- The normalized second-leg gradient pair has derivative
    `(0, 4 b (3 J + P + 12) / 9)` at zero radius. -/
lemma independentRadiusSecondGradient_hasDerivAt (θ : ℝ × ℝ × ℝ) :
    HasDerivAt
      (fun r ↦ independentRadiusSecondGradient (θ, r))
      (0, 4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let L : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).1
  let H : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).2
  let Q : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).1
  let U : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).2
  let A : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).1
  let C : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).2.1
  let D : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).2.2
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hfirst := independentRadiusFirstFactorJets θ
  have hL := hfirst.1.hasFDerivAt.fst.hasDerivAt
  have hH := hfirst.1.hasFDerivAt.snd.hasDerivAt
  have hQ := hfirst.2.hasFDerivAt.fst.hasDerivAt
  have hU := hfirst.2.hasFDerivAt.snd.hasDerivAt
  have hL0 : L 0 = 2 := by
    simpa [L] using congrArg Prod.fst (independentRadiusFirstSpectral_zero θ)
  have hH0 : H 0 = 1 := by
    simpa [H] using congrArg Prod.snd (independentRadiusFirstSpectral_zero θ)
  have hQ0 : Q 0 = 1 := by
    simpa [Q] using congrArg Prod.fst (independentRadiusFirstGradient_zero θ)
  have hU0 : U 0 = 1 := by
    simpa [U] using congrArg Prod.snd (independentRadiusFirstGradient_zero θ)
  have hres := independentRadiusSecondResiduals_hasDerivAt θ
  have hA := hres.hasFDerivAt.fst.hasDerivAt
  have hC := hres.hasFDerivAt.snd.hasFDerivAt.fst.hasDerivAt
  have hD := hres.hasFDerivAt.snd.hasFDerivAt.snd.hasDerivAt
  have hA0 : A 0 = 6 := by
    simpa [A, L, H, Q, U] using congrArg Prod.fst (independentRadiusSecondResiduals_zero θ)
  have hC0 : C 0 = 2 := by
    simpa [C, L, H, Q, U] using congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.1)
      (independentRadiusSecondResiduals_zero θ)
  have hD0 : D 0 = 1 := by
    simpa [D, L, H, Q, U] using congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.2)
      (independentRadiusSecondResiduals_zero θ)
  let w₁ : ℝ → ℝ := fun r ↦ r * L r * Q r - 2 * θ.1 * H r * U r
  let w₂ : ℝ → ℝ := fun r ↦ H r * U r - 2 * θ.1 * r * L r * Q r
  let β : ℝ → ℝ := fun r ↦ r * L r * Q r * w₁ r + H r * U r * w₂ r
  let δ : ℝ → ℝ := fun r ↦ L r * Q r ^ 2 + H r * U r ^ 2
  have hw₁ : HasDerivAt w₁
      (2 + 2 * θ.1 ^ 2 * (12 - θ.2.1) / 3) 0 := by
    have h := ((hX.mul hL).mul hQ).sub
      ((hH.mul hU).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [X, L, H, Q, U, hL0, hH0, hQ0, hU0]
    ring
  have hw₂ : HasDerivAt w₂
      (θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (hH.mul hU).sub
      (((hX.mul hL).mul hQ).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [w₂, X, L, H, Q, U, hL0, hH0, hQ0]
    ring
  have hβ : HasDerivAt β (2 * θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (((hX.mul hL).mul hQ).mul hw₁).add ((hH.mul hU).mul hw₂)
    apply h.congr_deriv
    simp [β, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hβ0 : β 0 ≠ 0 := by
    simp [β, w₁, w₂, hL0, hH0, hQ0, hU0]
  have hδ : HasDerivAt δ
      (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 30) / 3) 0 := by
    have h := (hL.mul (hQ.pow 2)).add (hH.mul (hU.pow 2))
    apply h.congr_deriv
    simp [δ, L, H, Q, U, hL0, hH0, hQ0, hU0]
    ring
  have hδ0 : δ 0 = 3 := by
    simp [δ, hL0, hH0, hQ0, hU0]
  let threeβ : ℝ → ℝ := fun r ↦ 3 * β r
  have hthreeβ : HasDerivAt threeβ (2 * θ.1 * (θ.2.1 - 24)) 0 := by
    exact hβ.const_mul 3 |>.congr_deriv (g' := 2 * θ.1 * (θ.2.1 - 24))
      (by simp [threeβ]; ring)
  have hthreeβ0 : threeβ 0 ≠ 0 := by
    simp [threeβ, hβ0]
  let q : ℝ → ℝ := fun r ↦ Q r - X r * δ r * w₁ r / threeβ r
  let u : ℝ → ℝ := fun r ↦ U r - δ r * w₂ r / threeβ r
  have hq : HasDerivAt q 0 0 := by
    have h := hQ.sub (((hX.mul hδ).mul hw₁).div hthreeβ hthreeβ0)
    apply h.congr_deriv
    simp [q, threeβ, X, L, H, Q, U, δ, w₁, w₂, β, hL0, hH0, hQ0, hU0,
      hδ0]
    ring
  have hu : HasDerivAt u
      (θ.1 * (θ.2.1 - 6 * θ.2.2 - 60) / 9) 0 := by
    have h := hU.sub ((hδ.mul hw₂).div hthreeβ hthreeβ0)
    apply h.congr_deriv
    simp [u, threeβ, X, L, H, Q, U, δ, w₁, w₂, β, hL0, hH0, hQ0, hU0,
      hδ0]
    ring
  let mA : ℝ → ℝ := fun r ↦ X r ^ 2 * A r
  let mC : ℝ → ℝ := fun r ↦ X r * C r
  let mD : ℝ → ℝ := D
  have hmA : HasDerivAt mA 0 0 := by
    exact (hX.pow 2).mul hA |>.congr_deriv (g' := 0) (by simp [mA, X])
  have hmC : HasDerivAt mC 2 0 := by
    exact hX.mul hC |>.congr_deriv (g' := 2) (by simp [mC, X, hC0])
  have hmD : HasDerivAt mD (8 * θ.1) 0 := hD
  let rad : ℝ → ℝ := fun r ↦ (mA r - mD r) ^ 2 + 4 * (mC r) ^ 2
  have hrad : HasDerivAt rad (16 * θ.1) 0 := by
    exact ((hmA.sub hmD).pow 2).add ((hmC.pow 2).const_mul 4) |>.congr_deriv
      (g' := 16 * θ.1) (by simp [rad, mA, mC, mD, X, hA0, hC0, hD0]; ring)
  have hrad0 : rad 0 ≠ 0 := by
    simp [rad, mA, mC, mD, X, hA0, hC0, hD0]
  let gap : ℝ → ℝ := fun r ↦ Real.sqrt (rad r)
  have hgap : HasDerivAt gap (8 * θ.1) 0 := by
    exact (hrad.sqrt hrad0).congr_deriv (g' := 8 * θ.1)
      (by simp [gap, rad, mA, mC, mD, X, hA0, hC0, hD0])
  let low : ℝ → ℝ := fun r ↦ (mA r + mD r - gap r) / 2
  have hlow : HasDerivAt low 0 0 := by
    exact ((hmA.add hmD).sub hgap).div (hasDerivAt_const 0 (2 : ℝ)) (by norm_num)
      |>.congr_deriv (g' := 0) (by simp [low]; ring)
  let denomRad : ℝ → ℝ := fun r ↦ (mD r - low r) ^ 2 + (mC r) ^ 2
  have hdenomRad : HasDerivAt denomRad (16 * θ.1) 0 := by
    exact ((hmD.sub hlow).pow 2).add (hmC.pow 2) |>.congr_deriv
      (g' := 16 * θ.1) (by simp [denomRad, mD, low, mC, X, hA0, hC0, hD0]; ring)
  have hdenomRad0 : denomRad 0 ≠ 0 := by
    simp [denomRad, mD, low, mC, X, hA0, hC0, hD0, gap, rad]
  let denom : ℝ → ℝ := fun r ↦ Real.sqrt (denomRad r)
  have hdenom : HasDerivAt denom (8 * θ.1) 0 := by
    exact (hdenomRad.sqrt hdenomRad0).congr_deriv (g' := 8 * θ.1)
      (by simp [denom, denomRad, mD, low, mC, X, hA0, hC0, hD0, gap, rad])
  have hdenom0 : denom 0 ≠ 0 := by
    simp [denom, denomRad, mD, low, mC, X, hA0, hC0, hD0, gap, rad]
  let gradientLow : ℝ → ℝ := fun r ↦
    ((mD r - low r) * q r - X r ^ 2 * C r * u r) / denom r
  let gradientHigh : ℝ → ℝ := fun r ↦
    (C r * q r + (mD r - low r) * u r) / denom r
  have hGL : HasDerivAt gradientLow 0 0 := by
    exact ((((hmD.sub hlow).mul hq).sub (((hX.pow 2).mul hC).mul hu)).div hdenom hdenom0)
      |>.congr_deriv (g' := 0)
      (by simp [gradientLow, denom, denomRad, low, gap, rad, mA, mC, mD, X,
        A, C, D, q, u, hA0, hC0, hD0]; ring)
  have hGH : HasDerivAt gradientHigh
      (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) 0 := by
    exact ((hC.mul hq).add ((hmD.sub hlow).mul hu)).div hdenom hdenom0
      |>.congr_deriv (g' := 4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9)
      (by simp [gradientHigh, denom, denomRad, low, gap, rad, mA, mC, mD, X,
        A, C, D, q, u, hA0, hC0, hD0]; ring)
  have hpair := hGL.prodMk hGH
  apply hpair.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun r ↦ by
    simp [independentRadiusSecondGradient, independentSecondGradientFactors,
      independentSecondGradientResiduals, gradientLow, gradientHigh, denom,
      denomRad, low, gap, rad, mA, mC, mD, X, A, C, D, q, u, δ, β, w₁, w₂,
      threeβ]
    rfl)

-/

/-- The normalized second-leg spectral pair has the corrected first derivative at zero. -/
lemma independentRadiusSecondSpectral_hasDerivAt (θ : ℝ × ℝ × ℝ) :
    HasDerivAt
      (fun r ↦ independentRadiusSecondSpectral (θ, r))
      (θ.1 * (2 * θ.2.2 + θ.2.1 - 12), 8 * θ.1) 0 := by
  -- Reuse the denominator-normalized spectral calculation from the concrete jet interface.
  exact independentRadiusSecondSpectralJet θ

/-- The normalized second-leg gradient pair has the corrected first derivative at zero. -/
lemma independentRadiusSecondGradient_hasDerivAt (θ : ℝ × ℝ × ℝ) :
    HasDerivAt
      (fun r ↦ independentRadiusSecondGradient (θ, r))
      (0, 4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let L : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).1
  let H : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).2
  let Q : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).1
  let U : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).2
  let A : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).1
  let C : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).2.1
  let D : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).2.2
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hX0 : X 0 = 0 := by
    simp [X]
  -- Reuse the established first-factor and residual jets coordinatewise.
  have hfirst := independentRadiusFirstFactorJets θ
  have hL : HasDerivAt L (θ.1 * (2 * θ.2.2 + θ.2.1 + 4)) 0 := by
    simpa only [L] using hasDerivAt_fst_of_prod hfirst.1
  have hH : HasDerivAt H (-2 * θ.1) 0 := by
    simpa only [H] using hasDerivAt_snd_of_prod hfirst.1
  have hQ : HasDerivAt Q (-2 * θ.1) 0 := by
    simpa only [Q] using hasDerivAt_fst_of_prod hfirst.2
  have hU : HasDerivAt U (θ.1 * (θ.2.1 - 6) / 3) 0 := by
    simpa only [U] using hasDerivAt_snd_of_prod hfirst.2
  have hL0 : L 0 = 2 := by
    simpa only [L] using congrArg Prod.fst (independentRadiusFirstSpectral_zero θ)
  have hH0 : H 0 = 1 := by
    simpa only [H] using congrArg Prod.snd (independentRadiusFirstSpectral_zero θ)
  have hQ0 : Q 0 = 1 := by
    simpa only [Q] using congrArg Prod.fst (independentRadiusFirstGradient_zero θ)
  have hU0 : U 0 = 1 := by
    simpa only [U] using congrArg Prod.snd (independentRadiusFirstGradient_zero θ)
  have hres := independentRadiusSecondResiduals_hasDerivAt θ
  have hA : HasDerivAt A
      (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3) 0 := by
    simpa only [A, L, H, Q, U] using hasDerivAt_fst_of_prod hres
  have hC : HasDerivAt C
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) 0 := by
    have hsecond := hasDerivAt_snd_of_prod hres
    simpa only [C, L, H, Q, U] using hasDerivAt_fst_of_prod hsecond
  have hD : HasDerivAt D (8 * θ.1) 0 := by
    have hsecond := hasDerivAt_snd_of_prod hres
    simpa only [D, L, H, Q, U] using hasDerivAt_snd_of_prod hsecond
  have hA0 : A 0 = 6 := by
    simp only [A, L, H, Q, U, independentRadiusFirstSpectral_zero θ,
      independentRadiusFirstGradient_zero θ]
    exact congrArg Prod.fst (independentRadiusSecondResiduals_zero θ)
  have hC0 : C 0 = 2 := by
    simp only [C, L, H, Q, U, independentRadiusFirstSpectral_zero θ,
      independentRadiusFirstGradient_zero θ]
    exact congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.1)
      (independentRadiusSecondResiduals_zero θ)
  have hD0 : D 0 = 1 := by
    simp only [D, L, H, Q, U, independentRadiusFirstSpectral_zero θ,
      independentRadiusFirstGradient_zero θ]
    exact congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.2)
      (independentRadiusSecondResiduals_zero θ)
  let w₁ : ℝ → ℝ := X * L * Q - fun r ↦ 2 * θ.1 * (H * U) r
  let w₂ : ℝ → ℝ := H * U - fun r ↦ 2 * θ.1 * (X * L * Q) r
  let β : ℝ → ℝ := X * L * Q * w₁ + H * U * w₂
  let δ : ℝ → ℝ := L * Q ^ 2 + H * U ^ 2
  have hw₁ : HasDerivAt w₁
      (2 + 2 * θ.1 ^ 2 * (12 - θ.2.1) / 3) 0 := by
    have h := ((hX.mul hL).mul hQ).sub ((hH.mul hU).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [X, L, H, Q, U, hL0, hH0, hQ0, hU0]
    ring
  have hw₂ : HasDerivAt w₂ (θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (hH.mul hU).sub (((hX.mul hL).mul hQ).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [w₂, X, L, H, Q, U, hL0, hH0, hQ0, hU0, hX0]
    ring
  have hβ : HasDerivAt β (2 * θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (((hX.mul hL).mul hQ).mul hw₁).add ((hH.mul hU).mul hw₂)
    apply h.congr_deriv
    simp [β, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hβ0 : β 0 ≠ 0 := by
    simp [β, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0, hX0]
  have hδ : HasDerivAt δ
      (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 30) / 3) 0 := by
    have h := (hL.mul (hQ.pow 2)).add (hH.mul (hU.pow 2))
    apply h.congr_deriv
    simp [δ, L, H, Q, U, hL0, hH0, hQ0, hU0]
    ring
  have hδ0 : δ 0 = 3 := by
    norm_num [δ, hL0, hH0, hQ0, hU0]
  let threeβ : ℝ → ℝ := fun r ↦ 3 * β r
  have hthreeβ : HasDerivAt threeβ (2 * θ.1 * (θ.2.1 - 24)) 0 := by
    have hcoefficient : 3 * (2 * θ.1 * (θ.2.1 - 24) / 3) =
        2 * θ.1 * (θ.2.1 - 24) := by
      ring
    exact hβ.const_mul 3 |>.congr_deriv hcoefficient
  have hthreeβ0 : threeβ 0 ≠ 0 := by
    simp [threeβ, hβ0]
  let q : ℝ → ℝ := Q - X * δ * w₁ / threeβ
  let u : ℝ → ℝ := U - δ * w₂ / threeβ
  have hq : HasDerivAt q 0 0 := by
    have h := hQ.sub (((hX.mul hδ).mul hw₁).div hthreeβ hthreeβ0)
    apply h.congr_deriv
    simp [q, threeβ, X, L, H, Q, U, δ, w₁, w₂, β,
      hL0, hH0, hQ0, hU0, hδ0]
    ring
  have hq0 : q 0 = 1 := by
    norm_num [q, threeβ, X, δ, w₁, β, hX0, hL0, hH0, hQ0, hU0, hδ0]
  have hu0 : u 0 = 0 := by
    norm_num [u, threeβ, X, δ, w₂, β, hX0, hL0, hH0, hQ0, hU0, hδ0]
  have hu : HasDerivAt u
      (θ.1 * (θ.2.1 - 6 * θ.2.2 - 60) / 9) 0 := by
    have h := hU.sub ((hδ.mul hw₂).div hthreeβ hthreeβ0)
    apply h.congr_deriv
    simp [u, threeβ, X, L, H, Q, U, δ, w₁, w₂, β,
      hL0, hH0, hQ0, hU0, hδ0]
    ring
  let mA : ℝ → ℝ := fun r ↦ X r ^ 2 * A r
  let mC : ℝ → ℝ := fun r ↦ X r * C r
  let mD : ℝ → ℝ := D
  have hmA : HasDerivAt mA 0 0 := by
    have hcoefficient :
        2 * X 0 ^ (2 - 1) * 1 * A 0 + X 0 ^ 2 *
            (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3) = 0 := by
      simp [X]
    exact (hX.pow 2).mul hA |>.congr_deriv hcoefficient
  have hmC : HasDerivAt mC 2 0 := by
    have hcoefficient : 1 * C 0 + X 0 *
        (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) = 2 := by
      simp [X, hC0]
    exact hX.mul hC |>.congr_deriv hcoefficient
  have hmD : HasDerivAt mD (8 * θ.1) 0 := hD
  have hmA0 : mA 0 = 0 := by
    simp [mA, X]
  have hmC0 : mC 0 = 0 := by
    simp [mC, X]
  have hmD0 : mD 0 = 1 := hD0
  let rad : ℝ → ℝ := fun r ↦ (mA r - mD r) ^ 2 + 4 * (mC r) ^ 2
  have hrad : HasDerivAt rad (16 * θ.1) 0 := by
    have hcoefficient :
        2 * (mA - mD) 0 ^ (2 - 1) * (0 - 8 * θ.1) +
            4 * (2 * mC 0 ^ (2 - 1) * 2) = 16 * θ.1 := by
      simp [rad, mA, mC, mD, X, hA0, hC0, hD0]
      ring
    exact ((hmA.sub hmD).pow 2).add ((hmC.pow 2).const_mul 4) |>.congr_deriv
      hcoefficient
  have hrad0 : rad 0 ≠ 0 := by
    simp [rad, mA, mC, mD, X, hA0, hC0, hD0]
  let gap : ℝ → ℝ := fun r ↦ Real.sqrt (rad r)
  have hgap : HasDerivAt gap (8 * θ.1) 0 := by
    have hcoefficient : 16 * θ.1 / (2 * Real.sqrt (rad 0)) = 8 * θ.1 := by
      simp [gap, rad, mA, mC, mD, X, hA0, hC0, hD0]
      ring_nf
    exact (hrad.sqrt hrad0).congr_deriv hcoefficient
  have hgap0 : gap 0 = 1 := by
    norm_num [gap, rad, hmA0, hmC0, hmD0]
  let low : ℝ → ℝ := fun r ↦ (mA r + mD r - gap r) / 2
  have hlow : HasDerivAt low 0 0 := by
    exact ((hmA.add hmD).sub hgap).div (hasDerivAt_const 0 (2 : ℝ)) (by norm_num)
      |>.congr_deriv (by simp [low])
  have hlow0 : low 0 = 0 := by
    norm_num [low, hmA0, hmD0, hgap0]
  let denomRad : ℝ → ℝ := fun r ↦ (mD r - low r) ^ 2 + (mC r) ^ 2
  have hdenomRad : HasDerivAt denomRad (16 * θ.1) 0 := by
    have hcoefficient :
        2 * (mD - low) 0 ^ (2 - 1) * (8 * θ.1 - 0) +
            2 * mC 0 ^ (2 - 1) * 2 = 16 * θ.1 := by
      simp [denomRad, hmD0, hlow0, hmC0]
      ring
    exact ((hmD.sub hlow).pow 2).add (hmC.pow 2) |>.congr_deriv hcoefficient
  have hdenomRadValue : denomRad 0 = 1 := by
    norm_num [denomRad, hmD0, hlow0, hmC0]
  have hdenomRad0 : denomRad 0 ≠ 0 := by
    rw [hdenomRadValue]
    norm_num
  let denom : ℝ → ℝ := fun r ↦ Real.sqrt (denomRad r)
  have hdenom : HasDerivAt denom (8 * θ.1) 0 := by
    have hcoefficient : 16 * θ.1 / (2 * Real.sqrt (denomRad 0)) = 8 * θ.1 := by
      rw [hdenomRadValue]
      norm_num
      ring
    exact (hdenomRad.sqrt hdenomRad0).congr_deriv hcoefficient
  have hdenomValue : denom 0 = 1 := by
    norm_num [denom, hdenomRadValue]
  have hdenom0 : denom 0 ≠ 0 := by
    rw [hdenomValue]
    norm_num
  let gradientLow : ℝ → ℝ := ((mD - low) * q - X ^ 2 * C * u) / denom
  let gradientHigh : ℝ → ℝ := (C * q + (mD - low) * u) / denom
  have hGL : HasDerivAt gradientLow 0 0 := by
    have hcoefficient :
        (((8 * θ.1 - 0) * q 0 + (mD - low) 0 * 0 -
            ((2 * X 0 ^ (2 - 1) * 1 * C 0 + X 0 ^ 2 *
                (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3)) * u 0 +
              (X ^ 2 * C) 0 * (θ.1 * (θ.2.1 - 6 * θ.2.2 - 60) / 9))) *
          denom 0 - ((mD - low) * q - X ^ 2 * C * u) 0 * (8 * θ.1)) /
          denom 0 ^ 2 = 0 := by
      simp [gradientLow, hmD0, hlow0, hq0, hX0, hC0, hu0, hdenomValue]
    exact ((((hmD.sub hlow).mul hq).sub (((hX.pow 2).mul hC).mul hu)).div
      hdenom hdenom0).congr_deriv hcoefficient
  have hGH : HasDerivAt gradientHigh
      (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) 0 := by
    have hcoefficient :
        (((θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) * q 0 + C 0 * 0 +
            ((8 * θ.1 - 0) * u 0 + (mD - low) 0 *
              (θ.1 * (θ.2.1 - 6 * θ.2.2 - 60) / 9))) * denom 0 -
          (C * q + (mD - low) * u) 0 * (8 * θ.1)) / denom 0 ^ 2 =
          4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9 := by
      simp [gradientHigh, hC0, hq0, hmD0, hlow0, hu0, hdenomValue]
      ring
    exact ((hC.mul hq).add ((hmD.sub hlow).mul hu)).div hdenom hdenom0
      |>.congr_deriv hcoefficient
  -- Identify the scalar square-root model with the fixed low-eigenvector chart.
  have hgapEq : ∀ r : ℝ,
      gap r = RealSymmetric2.gap (mA r) (mC r) (mD r) := by
    intro r
    simp only [gap, RealSymmetric2.gap_apply]
    congr 1
    ring
  have hlowEq : ∀ r : ℝ,
      low r = RealSymmetric2.low (mA r) (mC r) (mD r) := by
    intro r
    dsimp [low]
    rw [RealSymmetric2.low_apply, hgapEq r]
  have hdenomEq : ∀ r : ℝ,
      denom r = RealSymmetric2.lowDenom (mA r) (mC r) (mD r) := by
    intro r
    simp [denom, denomRad, RealSymmetric2.lowDenom_apply, hlowEq r]
  have hlowEqConcrete : ∀ r : ℝ,
      low r = RealSymmetric2.low (r ^ 2 * A r) (r * C r) (D r) := by
    intro r
    simpa [mA, mC, mD, X] using hlowEq r
  have hdenomEqConcrete : ∀ r : ℝ,
      denom r = RealSymmetric2.lowDenom (r ^ 2 * A r) (r * C r) (D r) := by
    intro r
    simpa [mA, mC, mD, X] using hdenomEq r
  have hqEq : ∀ r : ℝ,
      q r = (independentSecondGradientResiduals θ.1 r
        (L r) (H r) (Q r) (U r)).1 := by
    intro r
    simp [q, independentSecondGradientResiduals, threeβ, δ, β, w₁, w₂, X]
    ring
  have huEq : ∀ r : ℝ,
      u r = (independentSecondGradientResiduals θ.1 r
        (L r) (H r) (Q r) (U r)).2 := by
    intro r
    simp [u, independentSecondGradientResiduals, threeβ, δ, β, w₁, w₂, X]
    ring
  have hpair := hGL.prodMk hGH
  have hpairEq : ∀ r : ℝ,
      (gradientLow r, gradientHigh r) = independentRadiusSecondGradient (θ, r) := by
    intro r
    unfold independentRadiusSecondGradient independentSecondGradientFactors
    apply Prod.ext
    · dsimp [gradientLow, A, C, D, L, H, Q, U, X]
      rw [hlowEqConcrete r, hdenomEqConcrete r, hqEq r, huEq r]
    · dsimp [gradientHigh, A, C, D, L, H, Q, U, X]
      rw [hlowEqConcrete r, hdenomEqConcrete r, hqEq r, huEq r]
  exact hpair.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun r ↦ (hpairEq r).symm))

/-- The independent-radius second-leg spectral and gradient factors have the displayed
    first derivative at the canonical zero-radius base. -/
lemma independentRadiusRecoveryFactors_hasDerivAt (θ : ℝ × ℝ × ℝ) :
    HasDerivAt (fun r ↦ independentRadiusRecoveryFactors (θ, r))
      (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18,
        (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9, 8 * θ.1)) 0 :=
  by
  -- The corrected component jets feed the recovery quotient adapter directly.
  have hS := independentRadiusSecondSpectral_hasDerivAt θ
  have hG := independentRadiusSecondGradient_hasDerivAt θ
  have hrec := independentRadiusRecoveryFactors_hasDerivAt_corrected θ
    (θ.1 * (2 * θ.2.2 + θ.2.1 - 12)) (8 * θ.1) 0
    (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) hS hG
  convert hrec using 1
  ring

/-- The independent-radius normal form has the displayed scalar coefficient germs. -/
lemma independentRadiusNormalForm_truncatedGerms :
    IndependentRadiusTruncatedGerm
        (fun θ r ↦ (independentRadiusNormalForm θ r).1)
          {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)} 3
        (fun n θ ↦ (![0, 1,
          θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (independentRadiusNormalForm θ r).2.1)
          {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)} 2
        (fun n θ ↦ (![2,
          θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9] : Fin 2 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (independentRadiusNormalForm θ r).2.2)
          {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)} 2
        (fun n θ ↦ (![1, 8 * θ.1] : Fin 2 → ℝ) n) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro θ hθ
      exact independentRadiusNormalForm_radius_contDiffAt 3 θ
    · intro n θ hθ
      fin_cases n
      · exact independentRadiusNormalForm_radius_constantCoeff θ
      · exact independentRadiusNormalForm_radius_linearCoeff θ
      · rw [FiniteTaylorJet.scalarCoeff_ofFunction]
        norm_num [Nat.factorial]
        have hfun : (fun r : ℝ ↦ (independentRadiusNormalForm θ r).1) =
            (fun r : ℝ ↦ r * (independentRadiusRecoveryFactors (θ, r)).1) := by
          funext r
          exact congrArg Prod.fst (independentRadiusNormalForm_eq_recoveryFactors θ r)
        rw [hfun]
        have hpath : ContDiffAt ℝ 2 (fun r : ℝ ↦ (θ, r)) 0 := by
          fun_prop
        have hrec : ContDiffAt ℝ 2
            (fun r : ℝ ↦ independentRadiusRecoveryFactors (θ, r)) 0 :=
          (independentRadiusRecoveryFactors_analyticAt_of_secondFactors θ).contDiffAt.comp
            0 hpath
        have hρ : ContDiffAt ℝ 2
            (fun r : ℝ ↦ (independentRadiusRecoveryFactors (θ, r)).1) 0 :=
          contDiffAt_fst.comp 0 hrec
        have hmul := iteratedDeriv_mul
          (x := (0 : ℝ))
          (show ContDiffAt ℝ 2 (fun r : ℝ ↦ r) 0 by fun_prop) hρ
        have hjet := independentRadiusRecoveryFactors_hasDerivAt θ
        have hρone : iteratedDeriv 1
            (fun r : ℝ ↦ (independentRadiusRecoveryFactors (θ, r)).1) 0 =
            θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18 := by
          have hρderiv := hjet.hasFDerivAt.fst.hasDerivAt.deriv
          simpa [ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.toSpanSingleton_apply] using hρderiv
        have hprod : (fun r : ℝ ↦ r) *
              (fun r : ℝ ↦ (independentRadiusRecoveryFactors (θ, r)).1) =
            (fun r : ℝ ↦ r * (independentRadiusRecoveryFactors (θ, r)).1) := by
          funext r
          rfl
        rw [← hprod]
        rw [hmul]
        norm_num [Finset.sum_range_succ, iteratedDeriv_fun_id_zero, hρone] <;>
          ring
  · constructor
    · intro θ hθ
      exact independentRadiusNormalForm_shape_contDiffAt 2 θ
    · intro n θ hθ
      fin_cases n
      · exact independentRadiusNormalForm_shape_constantCoeff θ
      · rw [FiniteTaylorJet.scalarCoeff_ofFunction]
        norm_num [Nat.factorial]
        have hfun : (fun r : ℝ ↦ (independentRadiusNormalForm θ r).2.1) =
            (fun r : ℝ ↦ (independentRadiusRecoveryFactors (θ, r)).2.1) := by
          funext r
          simpa only using congrArg (fun q : ℝ × ℝ × ℝ ↦ q.2.1)
            (independentRadiusNormalForm_eq_recoveryFactors θ r)
        rw [hfun]
        have hjet := independentRadiusRecoveryFactors_hasDerivAt θ
        simpa [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply] using
          hjet.hasFDerivAt.snd.fst.hasDerivAt.deriv
  · constructor
    · intro θ hθ
      exact independentRadiusNormalForm_scale_contDiffAt 2 θ
    · intro n θ hθ
      fin_cases n
      · exact independentRadiusNormalForm_scale_constantCoeff θ
      · rw [FiniteTaylorJet.scalarCoeff_ofFunction]
        norm_num [Nat.factorial]
        have hfun : (fun r : ℝ ↦ (independentRadiusNormalForm θ r).2.2) =
            (fun r : ℝ ↦ (independentRadiusRecoveryFactors (θ, r)).2.2) := by
          funext r
          simpa only using congrArg (fun q : ℝ × ℝ × ℝ ↦ q.2.2)
            (independentRadiusNormalForm_eq_recoveryFactors θ r)
        rw [hfun]
        have hjet := independentRadiusRecoveryFactors_hasDerivAt θ
        simpa [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply] using
          hjet.hasFDerivAt.snd.snd.hasDerivAt.deriv

/-- Both planar control matrices are positive definite on the signed-control strip. -/
lemma independentRadiusControlMatricesPosDef (b : ℝ) (hb : |b| < (1 / 4 : ℝ)) :
    (TwoPhaseControls.first b).matrix.PosDef ∧
      (TwoPhaseControls.second b).matrix.PosDef := by
  -- The strip bound controls the cross term in either quadratic form.
  have hleft : -(1 / 4 : ℝ) < b := (abs_lt.mp hb).1
  have hright : b < (1 / 4 : ℝ) := (abs_lt.mp hb).2
  have hnormSqPos (x : Fin 2 → ℝ) (hx : x ≠ 0) :
      0 < x 0 ^ 2 + x 1 ^ 2 := by
    have hcoord : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hzero
      apply hx
      funext i
      fin_cases i
      · exact not_ne_iff.mp (not_or.mp hzero).1
      · exact not_ne_iff.mp (not_or.mp hzero).2
    rcases hcoord with hzero | hone
    · nlinarith [sq_pos_of_ne_zero hzero]
    · nlinarith [sq_pos_of_ne_zero hone]
  constructor
  · rw [TwoPhaseControls.first_matrix]
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · intro x hx
      have hs := hnormSqPos x hx
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]
  · rw [TwoPhaseControls.second_matrix]
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · intro x hx
      have hs := hnormSqPos x hx
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]

/-- Negating the defining vector negates both columns of its positively oriented planar frame. -/
lemma euclideanPlane_frame_neg (e : EuclideanSpace ℝ (Fin 2)) :
    EuclideanPlane.frame (-e) = -EuclideanPlane.frame e := by
  -- The perpendicular map is linear, so both the vector and perpendicular columns change sign.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [EuclideanPlane.frame, EuclideanPlane.perp_apply]

/-- A gradient-oriented eigenframe is the fixed low-eigenvector frame up to one global sign. -/
lemma orientedEigenframe_eq_fixed_or_neg (a b d : ℝ)
    (g : EuclideanSpace ℝ (Fin 2)) :
    OrientedEigenframe.frame a b d g =
        EuclideanPlane.frame (RealSymmetric2.lowVector a b d) ∨
      OrientedEigenframe.frame a b d g =
        -EuclideanPlane.frame (RealSymmetric2.lowVector a b d) := by
  -- Split the orientation test; its negative branch negates the entire planar frame.
  unfold OrientedEigenframe.frame OrientedEigenframe.lowVector
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (euclideanPlane_frame_neg _)

/-- The transpose of the fixed low-eigenvector frame gives the two explicit normalized
gradient coordinates of a planar vector. -/
lemma lowFrame_transpose_mulVec (a b d q u : ℝ) :
    (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec ![q, u] =
      ![((d - RealSymmetric2.low a b d) * q - b * u) /
          RealSymmetric2.lowDenom a b d,
        (b * q + (d - RealSymmetric2.low a b d) * u) /
          RealSymmetric2.lowDenom a b d] := by
  -- Expand the two frame columns and read off their dot products with the vector.
  ext i
  fin_cases i <;>
    simp [EuclideanPlane.frame, EuclideanPlane.perp_apply,
      RealSymmetric2.lowVector, RealSymmetric2.lowRaw, Matrix.mulVec,
      Matrix.transpose_apply, dotProduct, Fin.sum_univ_two] <;>
    ring

/-- The physical low eigenvalue of a radius-scaled symmetric matrix is the squared radius
times its determinant factor whenever the high eigenvalue is nonzero. -/
lemma low_eq_radiusSq_mul_detFactor (r A C D : ℝ)
    (hhigh : RealSymmetric2.high (r ^ 2 * A) (r * C) D ≠ 0) :
    RealSymmetric2.low (r ^ 2 * A) (r * C) D =
      r ^ 2 * ((A * D - C ^ 2) /
        RealSymmetric2.high (r ^ 2 * A) (r * C) D) := by
  -- Use the determinant-over-high identity and factor out the common squared radius.
  rw [RealSymmetric2.low_eq_det_div_high_of_ne _ _ _ hhigh]
  field_simp [hhigh]

/-- A valid raw DFP step preserves positive definiteness of its metric component. -/
lemma independentRawStep_metric_posDef
    (M : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) (hM : M.PosDef) (hcontrol : control.matrix.PosDef)
    (htau : 0 < control.tau) (hg : g ≠ 0) :
    (independentRawStep M g control).1.PosDef := by
  -- Package the hypotheses as an abstract secant step, whose update theorem is canonical.
  let z := DFP.AbstractSecantStep.ofMatrices M g control.matrix control.tau
    hM hcontrol htau hg
  have hraw : independentRawStep M g control =
      (z.nextInverseHessian, z.nextGradient) := by
    simp only [independentRawStep, z, AbstractSecantStep.ofMatrices,
      AbstractSecantStep.nextInverseHessian, AbstractSecantStep.nextGradient,
      AbstractSecantStep.gradientChange, AbstractSecantStep.displacement,
      AbstractSecantStep.stepLength, AbstractSecantStep.preconditionedGradient]
  rw [hraw]
  exact z.nextInverseHessian_posDef

/-- The upper eigenvalue of a positive-definite real symmetric planar matrix is positive. -/
lemma realSymmetric2_high_pos_of_posDef (a b d : ℝ)
    (hM : (RealSymmetric2.matrix a b d).PosDef) :
    0 < RealSymmetric2.high a b d := by
  -- Test the quadratic form on the second coordinate vector to obtain `d > 0`.
  have hunit : (![(0 : ℝ), 1] : Fin 2 → ℝ) ≠ 0 := by
    intro hzero
    have hone := congrArg (fun v : Fin 2 → ℝ ↦ v 1) hzero
    norm_num at hone
  have hd : 0 < d := by
    have hquadratic := hM.dotProduct_mulVec_pos hunit
    simpa [RealSymmetric2.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hquadratic
  -- The square root in the quadratic formula dominates `d - a`.
  have hsq : (d - a) ^ 2 ≤ (d - a) ^ 2 + 4 * b ^ 2 := by
    nlinarith [sq_nonneg b]
  have hroot : d - a ≤ Real.sqrt ((d - a) ^ 2 + 4 * b ^ 2) := by
    calc
      d - a ≤ |d - a| := le_abs_self (d - a)
      _ = Real.sqrt ((d - a) ^ 2) := (Real.sqrt_sq_eq_abs (d - a)).symm
      _ ≤ Real.sqrt ((d - a) ^ 2 + 4 * b ^ 2) := Real.sqrt_le_sqrt hsq
  unfold RealSymmetric2.high RealSymmetric2.gap
  linarith

/-- Recovery from an oriented planar eigenframe agrees with the normalized radius-factor
formulas when the physical low eigenvalue and second gradient coordinate carry radius factors. -/
lemma orientedRecovery_eq_normalizedFactors
    (a b d r spectralLow spectralHigh gradientLow gradientHigh : ℝ)
    (v : Fin 2 → ℝ) (hr : r ≠ 0)
    (hlow : RealSymmetric2.low a b d = r ^ 2 * spectralLow)
    (hhigh : RealSymmetric2.high a b d = spectralHigh)
    (hcoords :
      (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
        ![gradientLow, r * gradientHigh]) :
    let F := OrientedEigenframe.frame a b d (WithLp.toLp 2 v)
    let w := F.transpose.mulVec v
    (CycleBoundaryState.recoveryRadius (RealSymmetric2.low a b d)
        (RealSymmetric2.high a b d) (w 0) (w 1),
      CycleBoundaryState.recoveryShape (RealSymmetric2.low a b d)
        (RealSymmetric2.high a b d) (w 0) (w 1),
      RealSymmetric2.high a b d) =
      (r * (spectralLow * gradientLow / (spectralHigh * gradientHigh)),
        spectralHigh * gradientHigh ^ 2 / (spectralLow * gradientLow ^ 2),
        spectralHigh) := by
  -- First prove the quotient calculation in the fixed frame, cancelling only the known radius.
  have hfixed :
      (CycleBoundaryState.recoveryRadius (RealSymmetric2.low a b d)
          (RealSymmetric2.high a b d) gradientLow (r * gradientHigh),
        CycleBoundaryState.recoveryShape (RealSymmetric2.low a b d)
          (RealSymmetric2.high a b d) gradientLow (r * gradientHigh),
        RealSymmetric2.high a b d) =
        (r * (spectralLow * gradientLow / (spectralHigh * gradientHigh)),
          spectralHigh * gradientHigh ^ 2 / (spectralLow * gradientLow ^ 2),
          spectralHigh) := by
    rw [hlow, hhigh]
    unfold CycleBoundaryState.recoveryRadius CycleBoundaryState.recoveryShape
    apply Prod.ext
    · simp only [Prod.fst]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      field_simp [hr]
    · apply Prod.ext
      · simp only [Prod.snd, Prod.fst]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        field_simp [hr]
      · rfl
  -- The oriented frame is fixed or globally negated; simultaneous coordinate negation
  -- leaves both recovery quotients unchanged.
  dsimp only
  rcases orientedEigenframe_eq_fixed_or_neg a b d (WithLp.toLp 2 v) with hframe | hframe
  · rw [hframe, hcoords]
    exact hfixed
  · rw [hframe]
    have hnegcoords :
        (-EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
          -![gradientLow, r * gradientHigh] := by
      rw [Matrix.transpose_neg, Matrix.neg_mulVec, hcoords]
    rw [hnegcoords]
    have hinvariant := recoveryTriple_neg_neg (RealSymmetric2.low a b d)
      (RealSymmetric2.high a b d) gradientLow (r * gradientHigh)
    simpa using hinvariant.trans hfixed

/-- The recovered triple produced by one raw step from a concrete metric and gradient. -/
noncomputable def independentRecoveredTriple
    (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) : ℝ × ℝ × ℝ :=
  let firstFrame := OrientedEigenframe.frame
    (H 0 0) (H 0 1) (H 1 1) (WithLp.toLp 2 g)
  let H₁ := firstFrame.transpose * H * firstFrame
  let g₁ := firstFrame.transpose.mulVec g
  let secondStep := independentRawStep H₁ g₁ control
  let secondFrame := OrientedEigenframe.frame
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
    (WithLp.toLp 2 secondStep.2)
  let g₂ := secondFrame.transpose.mulVec secondStep.2
  let lambdaMinus := RealSymmetric2.low
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
  let lambdaPlus := RealSymmetric2.high
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
  (CycleBoundaryState.recoveryRadius lambdaMinus lambdaPlus (g₂ 0) (g₂ 1),
    CycleBoundaryState.recoveryShape lambdaMinus lambdaPlus (g₂ 0) (g₂ 1),
    lambdaPlus)

/-- The raw mixed evaluator factors through the recovered-triple interface after its first
step has been identified. -/
lemma independentMapRaw_eq_independentRecoveredTriple
    (b r p h : ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (hfirst : independentRawStep (Matrix.diagonal ![h * p * r ^ 2, h])
        ![(1 : ℝ), p * r] (TwoPhaseControls.first b) = (H, g)) :
    independentMapRaw b r p h =
      independentRecoveredTriple H g (TwoPhaseControls.second b) := by
  unfold independentMapRaw independentRecoveredTriple
  dsimp only
  rw [hfirst]

/-- At nonzero radius, the normalized evaluator agrees with the raw two-leg representation
under the pointwise positivity conditions required by the two secant steps. -/
lemma independentRadiusNormalForm_eq_independentMapRaw_of_ne_zero
    (θ : ℝ × ℝ × ℝ) (r : ℝ) (hθ : |θ.1| < (1 / 4 : ℝ)) (hr : r ≠ 0)
    (hp : 0 < (input θ r).2.1) (hh : 0 < (input θ r).2.2)
    (hL : 0 < (independentRadiusFirstSpectral (θ, r)).1)
    (hH : 0 < (independentRadiusFirstSpectral (θ, r)).2)
    (hQ : (independentRadiusFirstGradient (θ, r)).1 ≠ 0) :
    independentRadiusNormalForm θ r =
      independentMapRaw θ.1 r (input θ r).2.1 (input θ r).2.2 := by
  let p : ℝ := (input θ r).2.1
  let h : ℝ := (input θ r).2.2
  have hrSq : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hinitial : (Matrix.diagonal ![h * p * r ^ 2, h] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (mul_pos hh hp) hrSq
    · exact hh
  have hcontrols := independentRadiusControlMatricesPosDef θ.1 hθ
  have htauFirst : 0 < (TwoPhaseControls.first θ.1).tau :=
    TwoPhaseControls.tau_pos θ.1 0
  have hgradientFirst : (![(1 : ℝ), p * r] : Fin 2 → ℝ) ≠ 0 := by
    intro hzero
    have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
    norm_num at hzeroFirst
  have hfirstRaw := independentRawStep_first_eq θ.1 r p h hinitial hcontrols.1
    htauFirst hgradientFirst hr
  let t₁ := independentFirstResiduals θ.1 r p h
  let M₁ := independentFirstMetric θ.1 r p h
  let v₁ := independentFirstGradient θ.1 r p
  let F₁ := EuclideanPlane.frame
    (RealSymmetric2.lowVector (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)
  let L := (independentRadiusFirstSpectral (θ, r)).1
  let H := (independentRadiusFirstSpectral (θ, r)).2
  let Q := (independentRadiusFirstGradient (θ, r)).1
  let U := (independentRadiusFirstGradient (θ, r)).2
  have hspectralFirst : independentRadiusFirstSpectral (θ, r) =
      independentFirstSpectralFactors θ.1 r p h := by
    rfl
  have hgradientFactorsFirst : independentRadiusFirstGradient (θ, r) =
      independentFirstGradientFactors θ.1 r p h := by
    rfl
  have hdenomFirst : RealSymmetric2.lowDenom
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    intro hzero
    apply hQ
    rw [hgradientFactorsFirst]
    unfold independentFirstGradientFactors
    dsimp only
    rw [hzero]
    simp
  have hhighFirst : RealSymmetric2.high
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    have hpositive : 0 < RealSymmetric2.high
        (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 := by
      simpa [H, hspectralFirst, independentFirstSpectralFactors, t₁] using hH
    exact ne_of_gt hpositive
  have hlowFirst : RealSymmetric2.low
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 = r ^ 2 * L := by
    rw [low_eq_radiusSq_mul_detFactor r t₁.1 t₁.2.1 t₁.2.2 hhighFirst]
    simp [L, hspectralFirst, independentFirstSpectralFactors, t₁]
  have hdiagFixedFirst : F₁.transpose * M₁ * F₁ =
      Matrix.diagonal ![r ^ 2 * L, H] := by
    have hmetricFirst : M₁ = RealSymmetric2.matrix
        (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        rfl
    have hdiag := RealSymmetric2.frame_diagonalizes_of_lowDenom_ne_zero
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 hdenomFirst
    rw [hmetricFirst, hdiag]
    simp [L, H, hspectralFirst, independentFirstSpectralFactors, t₁, hlowFirst]
  have hgradFixedFirst : F₁.transpose.mulVec v₁ = ![Q, r * U] := by
    have hcoords := lowFrame_transpose_mulVec
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2
      (independentFirstGradientResiduals θ.1 r p).1
      (r * (independentFirstGradientResiduals θ.1 r p).2)
    rw [show F₁.transpose.mulVec v₁ =
        (EuclideanPlane.frame (RealSymmetric2.lowVector
          (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)).transpose.mulVec
          ![(independentFirstGradientResiduals θ.1 r p).1,
            r * (independentFirstGradientResiduals θ.1 r p).2] by
      rfl]
    rw [hcoords]
    ext i
    fin_cases i <;>
      simp [Q, U, hgradientFactorsFirst, independentFirstGradientFactors, t₁] <;>
      ring
  have hframeFirst :
      OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1) (WithLp.toLp 2 v₁) = F₁ ∨
        OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1) (WithLp.toLp 2 v₁) = -F₁ := by
    rcases orientedEigenframe_eq_fixed_or_neg (M₁ 0 0) (M₁ 0 1) (M₁ 1 1)
      (WithLp.toLp 2 v₁) with hframe | hframe
    · left
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
    · right
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
  let t₂ := independentSecondResiduals θ.1 r L H Q U
  let M₂ := independentSecondMetric θ.1 r L H Q U
  let v₂ := independentSecondGradient θ.1 r L H Q U
  let S := (independentRadiusSecondSpectral (θ, r)).1
  let T := (independentRadiusSecondSpectral (θ, r)).2
  let Glo := (independentRadiusSecondGradient (θ, r)).1
  let Ghi := (independentRadiusSecondGradient (θ, r)).2
  have hdiagSecond : (Matrix.diagonal ![r ^ 2 * L, H] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (sq_pos_of_ne_zero hr) hL
    · exact hH
  have hgradientSecond : (![(1 : ℝ) • Q, (1 : ℝ) • (r * U)] : Fin 2 → ℝ) ≠ 0 := by
    intro hzero
    have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
    apply hQ
    simpa [Q] using hzeroFirst
  have hsecondRawPos := independentRawStep_second_eq θ.1 r L H Q U 1
    hdiagSecond hcontrols.2 (TwoPhaseControls.tau_pos θ.1 1)
    (by simpa using hgradientSecond) hr
  have hM₂pos : M₂.PosDef := by
    have hrawPos := independentRawStep_metric_posDef
      (Matrix.diagonal ![r ^ 2 * L, H]) (![Q, r * U] : Fin 2 → ℝ)
      (TwoPhaseControls.second θ.1) hdiagSecond hcontrols.2
      (TwoPhaseControls.tau_pos θ.1 1) (by simpa using hgradientSecond)
    have hmetricRaw :
        (independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
          (![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1)).1 =
          independentSecondMetric θ.1 r L H Q U :=
      by
        simpa using congrArg Prod.fst hsecondRawPos
    dsimp only [M₂]
    rw [← hmetricRaw]
    exact hrawPos
  have hhighSecondPos : 0 < RealSymmetric2.high
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 := by
    have hmatrixSecond : M₂ = RealSymmetric2.matrix
        (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        rfl
    apply realSymmetric2_high_pos_of_posDef
    rw [← hmatrixSecond]
    simpa [M₂, independentSecondMetric, t₂]
  have hhighSecond : RealSymmetric2.high
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 ≠ 0 :=
    ne_of_gt hhighSecondPos
  have hspectralSecond : independentRadiusSecondSpectral (θ, r) =
      independentSecondSpectralFactors θ.1 r L H Q U := by
    rfl
  have hlowSecond : RealSymmetric2.low
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 = r ^ 2 * S := by
    rw [low_eq_radiusSq_mul_detFactor r t₂.1 t₂.2.1 t₂.2.2 hhighSecond]
    simp [S, hspectralSecond, independentSecondSpectralFactors, t₂]
  have hgradientFactorsSecond : independentRadiusSecondGradient (θ, r) =
      independentSecondGradientFactors θ.1 r L H Q U := by
    rfl
  have hgradFixedSecond :
      (EuclideanPlane.frame (RealSymmetric2.lowVector
        (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)).transpose.mulVec v₂ =
          ![Glo, r * Ghi] := by
    have hcoords := lowFrame_transpose_mulVec
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2
      (independentSecondGradientResiduals θ.1 r L H Q U).1
      (r * (independentSecondGradientResiduals θ.1 r L H Q U).2)
    rw [show (EuclideanPlane.frame (RealSymmetric2.lowVector
        (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)).transpose.mulVec v₂ =
        (EuclideanPlane.frame (RealSymmetric2.lowVector
          (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)).transpose.mulVec
          ![(independentSecondGradientResiduals θ.1 r L H Q U).1,
            r * (independentSecondGradientResiduals θ.1 r L H Q U).2] by
      rfl]
    rw [hcoords]
    ext i
    fin_cases i <;>
      simp [Glo, Ghi, hgradientFactorsSecond, independentSecondGradientFactors, t₂] <;>
      ring
  change independentRadiusNormalForm θ r = independentMapRaw θ.1 r p h
  have hmapRaw := independentMapRaw_eq_independentRecoveredTriple θ.1 r p h
    M₁ v₁ hfirstRaw
  rw [hmapRaw]
  have hsecondRawCanonical :
      independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
          ![Q, r * U] (TwoPhaseControls.second θ.1) = (M₂, v₂) := by
    simpa [M₂, v₂] using hsecondRawPos
  rcases hframeFirst with hframeFirst | hframeFirst
  · -- The positively oriented first frame gives the canonical diagonal second input.
    unfold independentRecoveredTriple
    dsimp only
    rw [hframeFirst, hdiagFixedFirst, hgradFixedFirst, hsecondRawCanonical]
    have hhighSecondEq : RealSymmetric2.high
        (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 = T := by
      simp [T, hspectralSecond, independentSecondSpectralFactors, t₂]
    have hrecover := orientedRecovery_eq_normalizedFactors
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 r S T Glo Ghi v₂ hr
      hlowSecond hhighSecondEq hgradFixedSecond
    have hnormal :
        independentRadiusNormalForm θ r =
          (r * (S * Glo / (T * Ghi)), T * Ghi ^ 2 / (S * Glo ^ 2), T) := by
      rfl
    rw [hnormal]
    exact hrecover.symm
  · -- A negative first-frame choice negates the incoming gradient but leaves its metric
    -- diagonalization unchanged.
    have hdiagNeg :
        (-F₁).transpose * M₁ * (-F₁) = Matrix.diagonal ![r ^ 2 * L, H] := by
      simpa only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
        hdiagFixedFirst
    have hgradNeg : (-F₁).transpose.mulVec v₁ = -![Q, r * U] := by
      rw [Matrix.transpose_neg, Matrix.neg_mulVec, hgradFixedFirst]
    have hgradientSecondNeg :
        ((-1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ) ≠ 0 := by
      intro hzero
      have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
      apply hQ
      simpa [Q] using hzeroFirst
    have hsecondRawNeg := independentRawStep_second_eq θ.1 r L H Q U (-1)
      hdiagSecond hcontrols.2 (TwoPhaseControls.tau_pos θ.1 1)
      hgradientSecondNeg hr
    unfold independentRecoveredTriple
    dsimp only
    rw [hframeFirst, hdiagNeg, hgradNeg]
    have hsecondRawNeg' :
        independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
            (-![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1) =
          (M₂, -v₂) := by
      simpa [M₂, v₂] using hsecondRawNeg
    rw [hsecondRawNeg']
    have hgradFixedSecondNeg :
        (EuclideanPlane.frame (RealSymmetric2.lowVector
          (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)).transpose.mulVec (-v₂) =
            ![-Glo, r * (-Ghi)] := by
      rw [Matrix.mulVec_neg, hgradFixedSecond]
      ext i
      fin_cases i <;> simp <;> ring
    have hhighSecondEq : RealSymmetric2.high
        (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 = T := by
      simp [T, hspectralSecond, independentSecondSpectralFactors, t₂]
    have hrecoverNeg := orientedRecovery_eq_normalizedFactors
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 r S T (-Glo) (-Ghi) (-v₂) hr
      hlowSecond hhighSecondEq hgradFixedSecondNeg
    have hnormal :
        independentRadiusNormalForm θ r =
          (r * (S * Glo / (T * Ghi)), T * Ghi ^ 2 / (S * Glo ^ 2), T) := by
      rfl
    have hsign :
        (r * (S * (-Glo) / (T * (-Ghi))),
          T * (-Ghi) ^ 2 / (S * (-Glo) ^ 2), T) =
        (r * (S * Glo / (T * Ghi)), T * Ghi ^ 2 / (S * Glo ^ 2), T) := by
      apply Prod.ext
      · simp [neg_div_neg_eq]
      · apply Prod.ext
        · simp [neg_div_neg_eq]
        · rfl
    exact (hnormal.trans hsign.symm).trans hrecoverNeg.symm

/- At nonzero radius, the normalized independent evaluator agrees with the public map
   on the signed-control strip. -/
/-- At nonzero radius, the normalized independent evaluator agrees with the public map
    on the signed-control strip. -/
lemma independentRadiusNormalForm_eq_map_of_ne_zero
    (θ : ℝ × ℝ × ℝ) (r : ℝ) (hθ : |θ.1| < (1 / 4 : ℝ)) (hr : r ≠ 0)
    (hp : 0 < (input θ r).2.1) (hh : 0 < (input θ r).2.2)
    (hL : 0 < (independentRadiusFirstSpectral (θ, r)).1)
    (hH : 0 < (independentRadiusFirstSpectral (θ, r)).2)
    (hQ : (independentRadiusFirstGradient (θ, r)).1 ≠ 0) :
    independentRadiusNormalForm θ r = map θ.1 (input θ r) := by
  -- The raw evaluator is the only remaining representation bridge; the public map
  -- equality then follows by the stable nonzero-radius adapter.
  have hraw := independentRadiusNormalForm_eq_independentMapRaw_of_ne_zero θ r hθ hr
    hp hh hL hH hQ
  exact independentRadiusNormalForm_eq_map_of_raw_transport θ r hr hraw

/-- Near each strip point, the analytic independent-radius normal form agrees with the
    removable public mixed map. -/
lemma independentRadiusNormalForm_eventuallyEq_map
    (θ : ℝ × ℝ × ℝ) (hθ : |θ.1| < (1 / 4 : ℝ)) :
    Function.uncurry independentRadiusNormalForm =ᶠ[nhds (θ, 0)]
      (fun z ↦ map z.1.1 (input z.1 z.2)) := by
  have hstrip : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in nhds (θ, (0 : ℝ)),
      |z.1.1| < (1 / 4 : ℝ) := by
    have hc : ContinuousAt
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ |z.1.1|) (θ, 0) := by
      fun_prop
    exact hc.eventually (Iio_mem_nhds hθ)
  have hinput : ContinuousAt
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ input z.1 z.2) (θ, 0) :=
      (input_uncurry_contDiffAt 0 θ).continuousAt
  have hpcont : ContinuousAt
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.1) (θ, 0) :=
    continuousAt_fst.comp (continuousAt_snd.comp hinput)
  have hhcont : ContinuousAt
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.2) (θ, 0) :=
    continuousAt_snd.comp (continuousAt_snd.comp hinput)
  have hP : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in nhds (θ, 0),
      0 < (input z.1 z.2).2.1 := by
    apply hpcont.eventually
    have hbase :
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.1) (θ, 0) = 2 := by
      change (input θ 0).2.1 = 2
      rw [mixedInput_zero]
    rw [hbase]
    exact Ioi_mem_nhds (show (0 : ℝ) < 2 by norm_num)
  have hHinput : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in nhds (θ, 0),
      0 < (input z.1 z.2).2.2 := by
    apply hhcont.eventually
    have hbase :
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.2) (θ, 0) = 1 := by
      change (input θ 0).2.2 = 1
      rw [mixedInput_zero]
    rw [hbase]
    exact Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)
  have hScont := (independentRadiusFirstSpectral_analyticAt θ).continuousAt
  have hLcont : ContinuousAt
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusFirstSpectral z).1) (θ, 0) :=
    continuousAt_fst.comp hScont
  have hHcont : ContinuousAt
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusFirstSpectral z).2) (θ, 0) :=
    continuousAt_snd.comp hScont
  have hGcont := (independentRadiusFirstGradient_analyticAt θ).continuousAt
  have hQcont : ContinuousAt
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusFirstGradient z).1) (θ, 0) :=
    continuousAt_fst.comp hGcont
  have hLpos : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in nhds (θ, 0),
      0 < (independentRadiusFirstSpectral z).1 := by
    apply hLcont.eventually
    have hbase :
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstSpectral z).1) (θ, 0) = 2 := by
      exact congrArg Prod.fst (independentRadiusFirstSpectral_zero θ)
    rw [hbase]
    exact Ioi_mem_nhds (show (0 : ℝ) < 2 by norm_num)
  have hHpos : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in nhds (θ, 0),
      0 < (independentRadiusFirstSpectral z).2 := by
    apply hHcont.eventually
    have hbase :
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstSpectral z).2) (θ, 0) = 1 := by
      exact congrArg Prod.snd (independentRadiusFirstSpectral_zero θ)
    rw [hbase]
    exact Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)
  have hQne : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in nhds (θ, 0),
      (independentRadiusFirstGradient z).1 ≠ 0 := by
    have hbase :
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstGradient z).1) (θ, 0) = 1 := by
      simpa only [independentRadiusFirstGradient_zero]
    have hnear : ∀ᶠ y : ℝ in nhds
        ((fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstGradient z).1) (θ, 0)), y ≠ 0 := by
      simpa only [hbase] using
        (eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num))
    exact hQcont.eventually hnear
  filter_upwards [hstrip, hP, hHinput, hLpos, hHpos, hQne]
    with z hzstrip hpz hhz hLz hHz hQz
  by_cases hz0 : z.2 = 0
  · change independentRadiusNormalForm z.1 z.2 = map z.1.1 (input z.1 z.2)
    rw [hz0, independentRadiusNormalForm_zero, mixedInput_zero, map_zero]
  · exact independentRadiusNormalForm_eq_map_of_ne_zero z.1 z.2 hzstrip hz0
      hpz hhz hLz hHz hQz

-- Local declaration justification: the gradient calculation requires transparent normal-form
-- components above, while leaving the assembled normal form reducible makes the subsequent
-- germ transports exhaust their elaboration budget through irrelevant projection unfolding.
attribute [local irreducible] independentRadiusNormalForm map input parameterSet

/- The independent-radius remainder API reduces each paper-facing estimate to a
   coefficient germ.  The raw two-leg analytic calculation needed to populate
   those germs is not exposed by the current `MixedMap` interfaces. -/

/- The three public germs share one independent-radius cancellation calculation.  Keeping
   that calculation behind a joint interface prevents each projection from reopening the
   same removable branch and coefficient transport obligations. -/

/-- The bounded-control independent-radius cancellation supplies the three local germs on
    the strip `|b| < 1 / 4` for Appendix Lemma A.5 (Mixed-variable expansion of radius,
    shape, and scale). -/
-- TODO: transport the completed independent-radius normal form to `map` on a punctured
-- neighborhood, then assemble its first-order recovered-factor jet into these germs.
-- Route correction: the residual, spectral, recovery, and `ContDiffAt` interfaces now
-- compile in `RecoveryAdapter`; the remaining blocker is the oriented-frame sign bridge
-- and its denominator-free first-order jet, not regularity of the normal form itself.
lemma mixedIndependentRadiusCancellation :
    IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).1)
          {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)} 3
        (fun n θ ↦ (![0, 1,
          θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).2.1)
          {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)} 2
        (fun n θ ↦ (![2,
          θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9] : Fin 2 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).2.2)
          {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)} 2
        (fun n θ ↦ (![1, 8 * θ.1] : Fin 2 → ℝ) n) := by
  -- First construct the three normal-form germs; their regularity and zero-radius
  -- coefficients are independent of the public removable branch.
  have hnormal := independentRadiusNormalForm_truncatedGerms
  have htransport_radius :
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).1)
          {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)} 3
        (fun n θ ↦ (![0, 1,
          θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18] : Fin 3 → ℝ) n) := by
    refine independentRadiusTruncatedGerm_of_eventuallyEq
      (f := fun θ r ↦ (map θ.1 (input θ r)).1)
      (g := fun θ r ↦ (independentRadiusNormalForm θ r).1)
      (K := {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)})
      (m := 3)
      (coeff := fun n θ ↦ (![0, 1,
        θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18] : Fin 3 → ℝ) n)
      ?_ ?_ hnormal.1
    · intro θ hθ
      have hEq := independentRadiusNormalForm_eventuallyEq_map θ hθ
      have hEq' := hEq.symm.fun_comp (fun y : ℝ × ℝ × ℝ ↦ y.1)
      filter_upwards [hEq'] with z hz
      exact hz
    · intro θ hθ
      have hEq := independentRadiusNormalForm_eventuallyEq_map θ hθ
      have hpath : Filter.Tendsto (fun r : ℝ ↦ (θ, r)) (nhds 0) (nhds (θ, 0)) :=
        continuousAt_const.prodMk continuousAt_id
      have hEq' := hEq.symm.comp_tendsto hpath
      have hEq'' := hEq'.fun_comp (fun y : ℝ × ℝ × ℝ ↦ y.1)
      filter_upwards [hEq''] with r hr
      exact hr
  have htransport_shape :
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).2.1)
          {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)} 2
        (fun n θ ↦ (![2,
          θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9] : Fin 2 → ℝ) n) := by
    refine independentRadiusTruncatedGerm_of_eventuallyEq
      (f := fun θ r ↦ (map θ.1 (input θ r)).2.1)
      (g := fun θ r ↦ (independentRadiusNormalForm θ r).2.1)
      (K := {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)})
      (m := 2)
      (coeff := fun n θ ↦ (![2,
        θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9] : Fin 2 → ℝ) n)
      ?_ ?_ hnormal.2.1
    · intro θ hθ
      have hEq := independentRadiusNormalForm_eventuallyEq_map θ hθ
      have hEq' := hEq.symm.fun_comp (fun y : ℝ × ℝ × ℝ ↦ y.2.1)
      filter_upwards [hEq'] with z hz
      exact hz
    · intro θ hθ
      have hEq := independentRadiusNormalForm_eventuallyEq_map θ hθ
      have hpath : Filter.Tendsto (fun r : ℝ ↦ (θ, r)) (nhds 0) (nhds (θ, 0)) :=
        continuousAt_const.prodMk continuousAt_id
      have hEq' := hEq.symm.comp_tendsto hpath
      have hEq'' := hEq'.fun_comp (fun y : ℝ × ℝ × ℝ ↦ y.2.1)
      filter_upwards [hEq''] with r hr
      exact hr
  have htransport_scale :
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).2.2)
          {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)} 2
        (fun n θ ↦ (![1, 8 * θ.1] : Fin 2 → ℝ) n) := by
    refine independentRadiusTruncatedGerm_of_eventuallyEq
      (f := fun θ r ↦ (map θ.1 (input θ r)).2.2)
      (g := fun θ r ↦ (independentRadiusNormalForm θ r).2.2)
      (K := {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)})
      (m := 2)
      (coeff := fun n θ ↦ (![1, 8 * θ.1] : Fin 2 → ℝ) n)
      ?_ ?_ hnormal.2.2
    · intro θ hθ
      have hEq := independentRadiusNormalForm_eventuallyEq_map θ hθ
      have hEq' := hEq.symm.fun_comp (fun y : ℝ × ℝ × ℝ ↦ y.2.2)
      filter_upwards [hEq'] with z hz
      exact hz
    · intro θ hθ
      have hEq := independentRadiusNormalForm_eventuallyEq_map θ hθ
      have hpath : Filter.Tendsto (fun r : ℝ ↦ (θ, r)) (nhds 0) (nhds (θ, 0)) :=
        continuousAt_const.prodMk continuousAt_id
      have hEq' := hEq.symm.comp_tendsto hpath
      have hEq'' := hEq'.fun_comp (fun y : ℝ × ℝ × ℝ ↦ y.2.2)
      filter_upwards [hEq''] with r hr
      exact hr
  exact ⟨htransport_radius, htransport_shape, htransport_scale⟩

/-- The independent-radius two-leg map has the radius, shape, and scale coefficient germs
    required by Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale). -/
lemma mixedIndependentRadiusCoefficientGerms (β B : ℝ) (_hβ : 0 < β)
    (hβ_small : β < 1 / 4) (_hB : 0 ≤ B) :
    IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).1) (parameterSet β B) 3
        (fun n θ ↦ (![0, 1,
          θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).2.1) (parameterSet β B) 2
        (fun n θ ↦ (![2,
          θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9] : Fin 2 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).2.2) (parameterSet β B) 2
        (fun n θ ↦ (![1, 8 * θ.1] : Fin 2 → ℝ) n) := by
  -- Restrict the compact parameter set to the canonical strip and consume the
  -- independent-radius cancellation interface once for all three projections.
  have hcancel := mixedIndependentRadiusCancellation
  have hstrip : parameterSet β B ⊆
      {θ : ℝ × ℝ × ℝ | |θ.1| < (1 / 4 : ℝ)} := by
    intro θ hθ
    exact parameterSetControlAbsLt β B hβ_small hθ
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro θ hθ
      exact hcancel.1.regularity θ (hstrip hθ)
    · intro n θ hθ
      fin_cases n
      · have h := mixedRadius_constantCoeff θ
        convert h using 1 <;> norm_num
      · exact hcancel.1.coefficient_eq ⟨1, by norm_num⟩ θ (hstrip hθ)
      · exact hcancel.1.coefficient_eq ⟨2, by norm_num⟩ θ (hstrip hθ)
  · constructor
    · intro θ hθ
      exact hcancel.2.1.regularity θ (hstrip hθ)
    · intro n θ hθ
      fin_cases n
      · have h := mixedShape_constantCoeff θ
        convert h using 1 <;> norm_num
      · exact hcancel.2.1.coefficient_eq ⟨1, by norm_num⟩ θ (hstrip hθ)
  · constructor
    · intro θ hθ
      exact hcancel.2.2.regularity θ (hstrip hθ)
    · intro n θ hθ
      fin_cases n
      · have h := mixedScale_constantCoeff θ
        convert h using 1 <;> norm_num
      · exact hcancel.2.2.coefficient_eq ⟨1, by norm_num⟩ θ (hstrip hθ)

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale), the
radius output has the stated factorial-normalized coefficients through order three. -/
lemma mixedRadiusCoefficientGerm (β B : ℝ) (hβ : 0 < β) (hβ_small : β < 1 / 4)
    (hB : 0 ≤ B) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ (map θ.1 (input θ r)).1) (parameterSet β B) 3
      (fun n θ ↦ (![0, 1,
        θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18] : Fin 3 → ℝ) n) :=
  -- Route correction: the old full-jet interface incorrectly forced the cubic
  -- coefficient to vanish; the source only determines coefficients below order three.
  (mixedIndependentRadiusCoefficientGerms β B hβ hβ_small hB).1

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale), the
recovered shape has the stated factorial-normalized coefficients through order two. -/
lemma mixedShapeCoefficientGerm (β B : ℝ) (hβ : 0 < β) (hβ_small : β < 1 / 4)
    (hB : 0 ≤ B) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ (map θ.1 (input θ r)).2.1) (parameterSet β B) 2
      (fun n θ ↦ (![2,
        θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9] : Fin 2 → ℝ) n) :=
  -- The quadratic coefficient is likewise part of the order-two remainder, not a
  -- coefficient that the source asserts is zero.
  (mixedIndependentRadiusCoefficientGerms β B hβ hβ_small hB).2.1

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale), the
recovered high scale has the stated factorial-normalized coefficients through order two. -/
lemma mixedScaleCoefficientGerm (β B : ℝ) (hβ : 0 < β) (hβ_small : β < 1 / 4)
    (hB : 0 ≤ B) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ (map θ.1 (input θ r)).2.2) (parameterSet β B) 2
      (fun n θ ↦ (![1, 8 * θ.1] : Fin 2 → ℝ) n) :=
  -- The high-scale quadratic term is absorbed by the order-two remainder estimate.
  (mixedIndependentRadiusCoefficientGerms β B hβ hβ_small hB).2.2

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale), a
direct radius coefficient germ gives the corresponding paper-facing remainder. -/
lemma radiusRemainderOn_of_directGerm
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hGerm : IndependentRadiusTruncatedGerm
      (fun θ r ↦ (map θ.1 (input θ r)).1) K 3
      (fun n θ ↦ (![0, 1,
        θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18] : Fin 3 → ℝ) n))
    : ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ (map θ.1 (input θ r)).1 - r -
        (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) * r ^ 2)
      K C 3 := by
  -- Convert the truncated coefficient sum to the displayed radius polynomial.
  obtain ⟨C, hC, hraw⟩ := uniformRemainderOn_of_independentRadiusTruncatedGerm
    (by norm_num) hK hGerm
  refine ⟨C, hC, ?_⟩
  convert hraw using 1
  · funext θ r
    simp [Fin.sum_univ_succ]
    ring
  · norm_num

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale), a
direct shape coefficient germ gives the corresponding paper-facing remainder. -/
lemma shapeRemainderOn_of_directGerm
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hGerm : IndependentRadiusTruncatedGerm
      (fun θ r ↦ (map θ.1 (input θ r)).2.1) K 2
      (fun n θ ↦ (![2,
        θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9] : Fin 2 → ℝ) n))
    : ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ (map θ.1 (input θ r)).2.1 - 2 -
        (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9) * r)
      K C 2 := by
  -- The generic bound is normalized with the explicit shape coefficient polynomial.
  obtain ⟨C, hC, hraw⟩ := uniformRemainderOn_of_independentRadiusTruncatedGerm
    (by norm_num) hK hGerm
  refine ⟨C, hC, ?_⟩
  convert hraw using 1
  · funext θ r
    simp [Fin.sum_univ_succ]
    ring
  · norm_num

/-- For Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale), a
direct scale coefficient germ gives the corresponding paper-facing remainder. -/
lemma scaleRemainderOn_of_directGerm
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hGerm : IndependentRadiusTruncatedGerm
      (fun θ r ↦ (map θ.1 (input θ r)).2.2) K 2
      (fun n θ ↦ (![1, 8 * θ.1] : Fin 2 → ℝ) n))
    : ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ (map θ.1 (input θ r)).2.2 - 1 - 8 * θ.1 * r)
      K C 2 := by
  -- Normalize the generic Taylor estimate with the explicit scale polynomial.
  obtain ⟨C, hC, hraw⟩ := uniformRemainderOn_of_independentRadiusTruncatedGerm
    (by norm_num) hK hGerm
  refine ⟨C, hC, ?_⟩
  convert hraw using 1
  · funext θ r
    simp [Fin.sum_univ_succ]
    ring
  · norm_num

/-- Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale) (1):
uniformly for bounded `(b, P, J)`, the independent-radius update has the stated
quadratic term and an order-three remainder. -/
theorem radiusExpansion (β B : ℝ) (hβ : 0 < β) (hβ_small : β < 1 / 4)
    (hB : 0 ≤ B) :
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦
        let y := map θ.1 (input θ r)
        y.1 - r - (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) * r ^ 2)
      (parameterSet β B) C 3 := by
  -- First package the compact parameter region and the independent-radius germ.
  have hK : IsCompact (parameterSet β B) := parameterSet_isCompact β B
  have hGerm := mixedRadiusCoefficientGerm β B hβ hβ_small hB
  -- The corrected truncated-germ bridge supplies the required positive constant.
  exact radiusRemainderOn_of_directGerm hK hGerm

/-- Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale) (2):
uniformly for bounded `(b, P, J)`, the recovered shape has the stated linear term
and an order-two remainder. -/
theorem shapeExpansion (β B : ℝ) (hβ : 0 < β) (hβ_small : β < 1 / 4)
    (hB : 0 ≤ B) :
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦
        let y := map θ.1 (input θ r)
        y.2.1 - 2 - (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9) * r)
      (parameterSet β B) C 2 := by
  -- The shape estimate follows from the compact independent-radius coefficient germ.
  have hK : IsCompact (parameterSet β B) := parameterSet_isCompact β B
  have hGerm := mixedShapeCoefficientGerm β B hβ hβ_small hB
  exact shapeRemainderOn_of_directGerm hK hGerm

/-- Appendix Lemma A.5 (Mixed-variable expansion of radius, shape, and scale) (3):
uniformly for bounded `(b, P, J)`, the recovered high scale has linear term
`8 * b * r` and an order-two remainder. -/
theorem scaleExpansion (β B : ℝ) (hβ : 0 < β) (hβ_small : β < 1 / 4)
    (hB : 0 ≤ B) :
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦
        let y := map θ.1 (input θ r)
        y.2.2 - 1 - 8 * θ.1 * r)
      (parameterSet β B) C 2 := by
  -- The high-scale estimate uses the same compactness and germ-to-remainder bridge.
  have hK : IsCompact (parameterSet β B) := parameterSet_isCompact β B
  have hGerm := mixedScaleCoefficientGerm β B hβ hβ_small hB
  exact scaleRemainderOn_of_directGerm hK hGerm

end DFP.TwoLeg.Mixed
