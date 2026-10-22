/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import SmoothMinimization_Nesterov_2004.section01
import SmoothMinimization_Nesterov_2004.section02

/-- Points on the segment between `x` and `y` stay in a convex set. -/
lemma smooth_convex_upper_bound_gamma_mem {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {Q : Set E} (hQ_convex : Convex ℝ Q) {x y : E}
    (hx : x ∈ Q) (hy : y ∈ Q) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (y - x) ∈ Q := by
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have h1t : 0 ≤ 1 - t := by linarith [ht.2]
  have hsum : (1 - t) + t = 1 := by linarith
  have hconv := hQ_convex hx hy h1t ht0 hsum
  have hgamma : x + t • (y - x) = (1 - t) • x + t • y := by
    calc
      x + t • (y - x) = x + (t • y - t • x) := by
        simp [smul_sub]
      _ = t • y + (x - t • x) := by
        abel
      _ = (1 - t) • x + t • y := by
        have hx' : x - t • x = (1 - t) • x := by
          simp [sub_smul, one_smul]
        simp [hx', add_comm]
  simpa [hgamma] using hconv

/-- Segment parametrization difference from the left endpoint. -/
lemma smooth_convex_upper_bound_gamma_sub {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (x y : E) (t : ℝ) :
    x + t • (y - x) - x = t • (y - x) := by
  simp

/-- Difference of two points on the same segment. -/
lemma smooth_convex_upper_bound_gamma_sub_sub {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (x y : E) (s t : ℝ) :
    (x + s • (y - x)) - (x + t • (y - x)) = (s - t) • (y - x) := by
  calc
    (x + s • (y - x)) - (x + t • (y - x)) = (s • (y - x)) - (t • (y - x)) := by
      simp [add_sub_add_left_eq_sub]
    _ = (s - t) • (y - x) := by
      simp [sub_smul]

/-- Proposition 1.3.1.
Let `Q` be a closed convex subset of a finite-dimensional real normed space and let `f : Q → Real`
be convex and differentiable. If the gradient is Lipschitz with constant `L > 0` in the dual norm
(equation (grad_lipschitz)), then for any `x, y in Q`,
`f y <= f x + pairing (grad f x) (y - x) + (L / 2) (norm (y - x))^2`
(inequality (3.1)). -/
theorem smooth_convex_upper_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Q : Set E} (hQ_convex : Convex ℝ Q)
    {f : E → ℝ} (hf_diff : ∀ x ∈ Q, DifferentiableAt ℝ f x) {L : ℝ} (hL : 0 < L)
    (hgrad_lipschitz :
      forall x, x ∈ Q -> forall y, y ∈ Q ->
        DualNormDef ((fderiv ℝ f x).toLinearMap - (fderiv ℝ f y).toLinearMap) <=
          L * norm (x - y)) :
    forall x, x ∈ Q -> forall y, y ∈ Q ->
      f y <= f x + DualPairing ((fderiv Real f x).toLinearMap) (y - x) +
        (L / 2) * norm (y - x) ^ 2 := by
  intro x hx y hy
  classical
  set v : E := y - x
  let γ : ℝ → E := fun t => x + t • v
  let φ : ℝ → ℝ := fun t => f (γ t)
  let ψ : ℝ → ℝ := fun t => DualPairing ((fderiv ℝ f (γ t)).toLinearMap) v
  have hγ_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Q := by
    intro t ht
    simpa [γ, v] using
      (smooth_convex_upper_bound_gamma_mem (hQ_convex := hQ_convex) hx hy t ht)
  have hγ_maps : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    exact hγ_mem t ht
  have hγ_cont : Continuous γ := by
    have hsmul : Continuous fun t : ℝ => t • v := by
      simpa using (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • v)
    simpa [γ] using (continuous_const.add hsmul)
  have hf_cont : ContinuousOn f Q := by
    intro z hz
    exact (hf_diff z hz).continuousAt.continuousWithinAt
  have hφ_cont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    exact hf_cont.comp hγ_cont.continuousOn hγ_maps
  have hγ_deriv : ∀ t, HasDerivAt γ v t := by
    intro t
    have hsmul : HasDerivAt (fun t : ℝ => t • v) v t := by
      simpa using (hasDerivAt_id (x := t)).smul_const v
    simpa [γ] using hsmul.const_add x
  have hφ_deriv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt φ (DualPairing ((fderiv ℝ f (γ t)).toLinearMap) v) t := by
    intro t ht
    have hγt : γ t ∈ Q := hγ_mem t (Set.mem_Icc_of_Ioo ht)
    have houter : HasFDerivAt f (fderiv ℝ f (γ t)) (γ t) :=
      (hf_diff (γ t) hγt).hasFDerivAt
    have hinner : HasDerivAt γ v t := hγ_deriv t
    have hcomp : HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) v) t := by
      simpa [Function.comp] using (houter.comp_hasDerivAt (f := γ) (x := t) hinner)
    simpa [φ, ψ, DualPairing, Function.comp] using hcomp
  have hψ_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        DualPairing (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f x).toLinearMap) v ≤
          L * t * ‖v‖ ^ 2 := by
    intro t ht
    have hγt : γ t ∈ Q := hγ_mem t ht
    have hpair :
        DualPairing (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f x).toLinearMap) v ≤
          DualNormDef (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f x).toLinearMap) * ‖v‖ := by
      simpa using
        (dualPairing_le_dualNormDef_mul_norm_section02
          (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f x).toLinearMap) v)
    have hgrad :
        DualNormDef (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f x).toLinearMap) ≤
          L * ‖γ t - x‖ := by
      exact hgrad_lipschitz (γ t) hγt x hx
    have hnorm : ‖γ t - x‖ = t * ‖v‖ := by
      have ht0 : 0 ≤ t := ht.1
      calc
        ‖γ t - x‖ = ‖t • v‖ := by
          simp [γ, v]
        _ = |t| * ‖v‖ := by
          simpa [Real.norm_eq_abs] using (norm_smul t v)
        _ = t * ‖v‖ := by
          simp [abs_of_nonneg ht0]
    calc
      DualPairing (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f x).toLinearMap) v
          ≤
        DualNormDef (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f x).toLinearMap) * ‖v‖ := by
          exact hpair
      _ ≤ (L * ‖γ t - x‖) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right hgrad (norm_nonneg v)
      _ = L * t * ‖v‖ ^ 2 := by
        simp [hnorm, pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hψ_lip :
      LipschitzOnWith (Real.toNNReal (L * ‖v‖ ^ 2)) ψ (Set.Icc (0 : ℝ) 1) := by
    have hK : 0 ≤ L * ‖v‖ ^ 2 := by
      have hL0 : 0 ≤ L := le_of_lt hL
      have hv0 : 0 ≤ ‖v‖ ^ 2 := by
        exact pow_two_nonneg _
      nlinarith
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro s hs t ht
    have hs_mem : γ s ∈ Q := hγ_mem s hs
    have ht_mem : γ t ∈ Q := hγ_mem t ht
    have hpair1 :
        ψ s - ψ t ≤ L * ‖γ s - γ t‖ * ‖v‖ := by
      have hpair :
          DualPairing (((fderiv ℝ f (γ s)).toLinearMap) - (fderiv ℝ f (γ t)).toLinearMap) v ≤
            DualNormDef
              (((fderiv ℝ f (γ s)).toLinearMap) - (fderiv ℝ f (γ t)).toLinearMap) * ‖v‖ := by
        simpa using
          (dualPairing_le_dualNormDef_mul_norm_section02
            (((fderiv ℝ f (γ s)).toLinearMap) - (fderiv ℝ f (γ t)).toLinearMap) v)
      have hgrad :
          DualNormDef (((fderiv ℝ f (γ s)).toLinearMap) - (fderiv ℝ f (γ t)).toLinearMap) ≤
            L * ‖γ s - γ t‖ := by
        exact hgrad_lipschitz (γ s) hs_mem (γ t) ht_mem
      have hdiff :
          ψ s - ψ t =
            DualPairing (((fderiv ℝ f (γ s)).toLinearMap) - (fderiv ℝ f (γ t)).toLinearMap) v := by
        simp [ψ, DualPairing]
      calc
        ψ s - ψ t =
            DualPairing
              (((fderiv ℝ f (γ s)).toLinearMap) - (fderiv ℝ f (γ t)).toLinearMap) v := by
          exact hdiff
        _ ≤
            DualNormDef
              (((fderiv ℝ f (γ s)).toLinearMap) - (fderiv ℝ f (γ t)).toLinearMap) * ‖v‖ :=
          hpair
        _ ≤ (L * ‖γ s - γ t‖) * ‖v‖ := by
          exact mul_le_mul_of_nonneg_right hgrad (norm_nonneg v)
        _ = L * ‖γ s - γ t‖ * ‖v‖ := by
          ring
    have hpair2 :
        ψ t - ψ s ≤ L * ‖γ s - γ t‖ * ‖v‖ := by
      have hpair :
          DualPairing (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f (γ s)).toLinearMap) v ≤
            DualNormDef
              (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f (γ s)).toLinearMap) * ‖v‖ := by
        simpa using
          (dualPairing_le_dualNormDef_mul_norm_section02
            (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f (γ s)).toLinearMap) v)
      have hgrad :
          DualNormDef (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f (γ s)).toLinearMap) ≤
            L * ‖γ t - γ s‖ := by
        exact hgrad_lipschitz (γ t) ht_mem (γ s) hs_mem
      have hdiff :
          ψ t - ψ s =
            DualPairing (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f (γ s)).toLinearMap) v := by
        simp [ψ, DualPairing]
      calc
        ψ t - ψ s =
            DualPairing
              (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f (γ s)).toLinearMap) v := by
          exact hdiff
        _ ≤
            DualNormDef
              (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f (γ s)).toLinearMap) * ‖v‖ :=
          hpair
        _ ≤ (L * ‖γ t - γ s‖) * ‖v‖ := by
          exact mul_le_mul_of_nonneg_right hgrad (norm_nonneg v)
        _ = L * ‖γ s - γ t‖ * ‖v‖ := by
          simp [norm_sub_rev, mul_comm, mul_left_comm]
    have habs :
        |ψ s - ψ t| ≤ L * ‖γ s - γ t‖ * ‖v‖ := by
      refine abs_le.mpr ?_
      constructor
      · have : ψ t - ψ s ≤ L * ‖γ s - γ t‖ * ‖v‖ := hpair2
        linarith
      · exact hpair1
    have hγst : ‖γ s - γ t‖ = |s - t| * ‖v‖ := by
      calc
        ‖γ s - γ t‖ = ‖(s - t) • v‖ := by
          simpa [γ, v] using congrArg norm (smooth_convex_upper_bound_gamma_sub_sub x y s t)
        _ = |s - t| * ‖v‖ := by
          simpa [Real.norm_eq_abs] using (norm_smul (s - t) v)
    have hK' : (Real.toNNReal (L * ‖v‖ ^ 2) : ℝ) = L * ‖v‖ ^ 2 := by
      simp [Real.toNNReal_of_nonneg hK]
    calc
      dist (ψ s) (ψ t) = |ψ s - ψ t| := by
        simp [Real.dist_eq]
      _ ≤ L * ‖γ s - γ t‖ * ‖v‖ := habs
      _ = L * |s - t| * ‖v‖ ^ 2 := by
        simp [hγst, pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = (Real.toNNReal (L * ‖v‖ ^ 2) : ℝ) * dist s t := by
        simp [hK', Real.dist_eq, mul_comm, mul_left_comm, mul_assoc]
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    exact hψ_lip.continuousOn
  have hψ_int : IntervalIntegrable ψ MeasureTheory.volume 0 1 := by
    exact (hψ_cont.intervalIntegrable_of_Icc (by linarith))
  have hftc :
      ∫ t in (0 : ℝ)..1, ψ t = φ 1 - φ 0 := by
    have hderiv' : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt φ (ψ t) t := by
      intro t ht
      simpa [ψ] using (hφ_deriv t ht)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ)) (b := 1)
      (by linarith) hφ_cont hderiv' hψ_int
  have hftc' : f y - f x = ∫ t in (0 : ℝ)..1, ψ t := by
    simpa [φ, γ, v] using hftc.symm
  have hdiff :
      f y - f x - DualPairing ((fderiv ℝ f x).toLinearMap) v =
        ∫ t in (0 : ℝ)..1,
          DualPairing (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f x).toLinearMap) v := by
    have hconst :
        ∫ t in (0 : ℝ)..1, (DualPairing ((fderiv ℝ f x).toLinearMap) v) =
          DualPairing ((fderiv ℝ f x).toLinearMap) v := by
      simp
    calc
      f y - f x - DualPairing ((fderiv ℝ f x).toLinearMap) v =
          (∫ t in (0 : ℝ)..1, ψ t) -
            DualPairing ((fderiv ℝ f x).toLinearMap) v := by
        simp [hftc']
      _ = (∫ t in (0 : ℝ)..1, ψ t) -
            ∫ t in (0 : ℝ)..1, DualPairing ((fderiv ℝ f x).toLinearMap) v := by
        simp [hconst]
      _ = ∫ t in (0 : ℝ)..1,
            (ψ t - DualPairing ((fderiv ℝ f x).toLinearMap) v) := by
        symm
        exact intervalIntegral.integral_sub hψ_int (intervalIntegral.intervalIntegrable_const)
      _ = ∫ t in (0 : ℝ)..1,
            DualPairing (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f x).toLinearMap) v := by
        refine intervalIntegral.integral_congr ?_
        intro t ht
        simp [ψ, DualPairing]
  have hψ_int' :
      IntervalIntegrable
        (fun t =>
          DualPairing (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f x).toLinearMap) v)
        MeasureTheory.volume 0 1 := by
    simpa [ψ, DualPairing] using
      (IntervalIntegrable.sub hψ_int intervalIntegral.intervalIntegrable_const)
  have hcont_bound : Continuous fun t : ℝ => L * t * ‖v‖ ^ 2 := by
    simpa [mul_assoc] using
      (continuous_const.mul (continuous_id.mul continuous_const))
  have hbound_int :
      ∫ t in (0 : ℝ)..1,
        DualPairing (((fderiv ℝ f (γ t)).toLinearMap) - (fderiv ℝ f x).toLinearMap) v ≤
        ∫ t in (0 : ℝ)..1, L * t * ‖v‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by linarith)
      hψ_int' (hcont_bound.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1))
      ?_
    · intro t ht
      exact hψ_bound t ht
  have hfinal :
      f y - f x - DualPairing ((fderiv ℝ f x).toLinearMap) v ≤
        (L / 2) * ‖v‖ ^ 2 := by
    have hcalc : ∫ t in (0 : ℝ)..1, L * t * ‖v‖ ^ 2 = (L / 2) * ‖v‖ ^ 2 := by
      calc
        ∫ t in (0 : ℝ)..1, L * t * ‖v‖ ^ 2 =
            L * ∫ t in (0 : ℝ)..1, t * ‖v‖ ^ 2 := by
          simp [mul_assoc, intervalIntegral.integral_const_mul]
        _ = L * (∫ t in (0 : ℝ)..1, t) * ‖v‖ ^ 2 := by
          simp [mul_assoc, intervalIntegral.integral_mul_const]
        _ = L * (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
          have hInt : ∫ t in (0 : ℝ)..1, t = (1 / 2 : ℝ) := by
            simp [integral_id]
          simp [hInt]
        _ = (L / 2) * ‖v‖ ^ 2 := by
          ring
    have hbound' :
        f y - f x - DualPairing ((fderiv ℝ f x).toLinearMap) v ≤
          ∫ t in (0 : ℝ)..1, L * t * ‖v‖ ^ 2 := by
      simpa [hdiff] using hbound_int
    simpa [hcalc] using hbound'
  have hfin' :
      f y ≤ f x + DualPairing ((fderiv ℝ f x).toLinearMap) (y - x) +
        (L / 2) * ‖y - x‖ ^ 2 := by
    have : f y - f x - DualPairing ((fderiv ℝ f x).toLinearMap) v ≤ (L / 2) * ‖v‖ ^ 2 :=
      hfinal
    linarith [this]
  simpa [v] using hfin'

/-- Definition 1.3.1.
Let `f` satisfy the assumptions of Proposition 1.3.1. For `x ∈ Q`, define `T_Q(x) ∈ Q` to be any
minimizer of `y ↦ ⟪∇ f(x), y - x⟫ + (L / 2) ‖y - x‖^2` over `y ∈ Q`
(equation (3.2)). If the norm is not strictly convex, the minimizer may be non-unique, and
`T_Q(x)` denotes an arbitrary choice. -/
noncomputable def T_Q {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (f : E → ℝ) (L : ℝ) (x : Q) : Q := by
  classical
  let g : E → ℝ := fun y =>
    DualPairing ((fderiv ℝ f x).toLinearMap) (y - x) + (L / 2) * ‖y - x‖ ^ 2
  by_cases h : ∃ y : Q, IsMinOn g Q (y : E)
  · exact Classical.choose h
  · exact x

/-- A pointwise minimizer yields an `IsLeast` on the image. -/
lemma isMinOn_image_isLeast {α β : Type*} [Preorder β] (f : α → β) (s : Set α) (a : α)
    (ha : a ∈ s) (hmin : IsMinOn f s a) : IsLeast (f '' s) (f a) := by
  refine ⟨⟨a, ha, rfl⟩, ?_⟩
  intro b hb
  rcases hb with ⟨x, hx, rfl⟩
  exact (isMinOn_iff.mp hmin) x hx

/-- Existence of a minimizer for the quadratic model on a closed set. -/
lemma smooth_convex_TQ_exists_isMinOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} (hQ_closed : IsClosed Q) {f : E → ℝ} {L : ℝ}
    (hL : 0 < L) (x : Q) :
    ∃ y : Q,
      IsMinOn
        (fun y : E =>
          DualPairing ((fderiv ℝ f x).toLinearMap) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
        Q (y : E) := by
  classical
  let g : E → ℝ := fun y =>
    DualPairing ((fderiv ℝ f x).toLinearMap) (y - x) + (L / 2) * ‖y - x‖ ^ 2
  let s : Module.Dual ℝ E := (fderiv ℝ f x).toLinearMap
  let M : ℝ := DualNormDef (-s)
  let R : ℝ := max 0 (2 * M / L)
  let K : Set E := Metric.closedBall (x : E) R ∩ Q
  have hR_nonneg : 0 ≤ R := by
    exact le_max_left _ _
  have hxK : (x : E) ∈ K := by
    refine ⟨?_, x.property⟩
    simpa using (Metric.mem_closedBall_self (x := (x : E)) hR_nonneg)
  have hK_nonempty : K.Nonempty := ⟨x, hxK⟩
  have hK_compact : IsCompact K := by
    have hball : IsCompact (Metric.closedBall (x : E) R) :=
      isCompact_closedBall (x := (x : E)) (r := R)
    simpa [K, Set.inter_comm] using (hball.inter_right hQ_closed)
  have hcont_g : Continuous g := by
    have hcont_s : Continuous fun y : E => s y := by
      simpa using (s.continuous_of_finiteDimensional)
    have hcont_lin : Continuous fun y : E => DualPairing s (y - x) := by
      have hcont_sy : Continuous fun y : E => s y := hcont_s
      have hcont_sub : Continuous fun y : E => s y - s x := hcont_sy.sub continuous_const
      simpa [DualPairing, map_sub] using hcont_sub
    have hnorm : Continuous fun y : E => ‖y - x‖ := by
      simpa using (continuous_id.sub continuous_const).norm
    have hpow : Continuous fun y : E => ‖y - x‖ ^ 2 := by
      simpa using hnorm.pow 2
    have hquad : Continuous fun y : E => (L / 2) * ‖y - x‖ ^ 2 :=
      continuous_const.mul hpow
    simpa [g] using hcont_lin.add hquad
  have hcont_g_on : ContinuousOn g K := hcont_g.continuousOn
  obtain ⟨y, hyK, hyminK⟩ := hK_compact.exists_isMinOn hK_nonempty hcont_g_on
  have hyQ : y ∈ Q := hyK.2
  have hxg : g x = 0 := by
    simp [g, DualPairing]
  have hy0 : g y ≤ 0 := by
    have hxy : g y ≤ g x := (isMinOn_iff.mp hyminK) x hxK
    simpa [hxg] using hxy
  have houtside :
      ∀ z ∈ Q, R ≤ ‖z - x‖ → 0 ≤ g z := by
    intro z hzQ hzR
    have hR' : 2 * M / L ≤ ‖z - x‖ := by
      exact le_trans (le_max_right _ _) hzR
    have hR'' : 2 * M ≤ ‖z - x‖ * L := by
      have h := (div_le_iff₀ hL).1 hR'
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hlin : DualPairing s (z - x) ≥ -M * ‖z - x‖ := by
      have h :=
        dualPairing_le_dualNormDef_mul_norm_section02 (s := -s) (x := z - x)
      have h' : -DualPairing s (z - x) ≤ M * ‖z - x‖ := by
        simpa [DualPairing, M, s] using h
      linarith
    have hlin' : -M * ‖z - x‖ ≤ DualPairing s (z - x) := by
      linarith [hlin]
    have hbound : -M * ‖z - x‖ + (L / 2) * ‖z - x‖ ^ 2 ≤ g z := by
      have hsum := add_le_add_right hlin' ((L / 2) * ‖z - x‖ ^ 2)
      simpa [g, add_comm, add_left_comm, add_assoc] using hsum
    have hquad : 0 ≤ -M * ‖z - x‖ + (L / 2) * ‖z - x‖ ^ 2 := by
      have hr : 0 ≤ ‖z - x‖ := norm_nonneg _
      nlinarith [hR'', hr, hL]
    exact le_trans hquad hbound
  have hyminQ : IsMinOn g Q y := by
    intro z hzQ
    by_cases hzR : ‖z - x‖ ≤ R
    · have hzball : z ∈ Metric.closedBall (x : E) R := by
        have : dist z x ≤ R := by
          simpa [dist_eq_norm] using hzR
        exact (Metric.mem_closedBall).2 this
      have hzK : z ∈ K := ⟨hzball, hzQ⟩
      exact (isMinOn_iff.mp hyminK) z hzK
    · have hzR' : R ≤ ‖z - x‖ := le_of_not_ge hzR
      have hgz : 0 ≤ g z := houtside z hzQ hzR'
      exact le_trans hy0 hgz
  refine ⟨⟨y, hyQ⟩, ?_⟩
  simpa [g] using hyminQ

/-- If a minimizer exists, `T_Q` is a minimizer of the quadratic model. -/
lemma T_Q_isMinOn_of_exists {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f : E → ℝ} {L : ℝ} (x : Q)
    (h :
      ∃ y : Q,
        IsMinOn
          (fun y : E =>
            DualPairing ((fderiv ℝ f x).toLinearMap) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
          Q (y : E)) :
    IsMinOn
      (fun y : E =>
        DualPairing ((fderiv ℝ f x).toLinearMap) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
      Q (T_Q Q f L x : E) := by
  classical
  simpa [T_Q, h] using (Classical.choose_spec h)

/-- The quadratic model at `T_Q` equals the infimum over `Q`. -/
lemma smooth_convex_TQ_value_eq_sInf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} (hQ_closed : IsClosed Q) {f : E → ℝ} {L : ℝ}
    (hL : 0 < L) (x : Q) :
    sInf
        ((fun y : E =>
          DualPairing ((fderiv ℝ f x).toLinearMap) (y - x) +
            (L / 2) * ‖y - x‖ ^ 2) '' Q) =
      (fun y : E =>
        DualPairing ((fderiv ℝ f x).toLinearMap) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
        (T_Q Q f L x : E) := by
  classical
  let g : E → ℝ := fun y =>
    DualPairing ((fderiv ℝ f x).toLinearMap) (y - x) + (L / 2) * ‖y - x‖ ^ 2
  have hmin_exists : ∃ y : Q, IsMinOn g Q (y : E) :=
    smooth_convex_TQ_exists_isMinOn (hQ_closed := hQ_closed) (hL := hL) x
  have hmin_TQ : IsMinOn g Q (T_Q Q f L x : E) :=
    T_Q_isMinOn_of_exists (Q := Q) (f := f) (L := L) x hmin_exists
  have hleast :
      IsLeast (g '' Q) (g (T_Q Q f L x : E)) :=
    isMinOn_image_isLeast g Q (T_Q Q f L x : E) (T_Q Q f L x).property hmin_TQ
  simpa [g] using hleast.csInf_eq

/-- Proposition 1.3.2.
Under the assumptions of Proposition 1.3.1, for any `x ∈ Q` we have
`f(T_Q(x)) ≤ f(x) + min_{y ∈ Q} { ⟪∇ f(x), y - x⟫ + (L / 2) ‖y - x‖^2 }`
(equation (3.3)). -/
theorem smooth_convex_TQ_min_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] {Q : Set E} (hQ_closed : IsClosed Q)
    (hQ_convex : Convex Real Q) {f : E → Real}
    (hf_diff : ∀ x ∈ Q, DifferentiableAt Real f x) {L : Real} (hL : 0 < L)
    (hgrad_lipschitz :
      forall x, x ∈ Q -> forall y, y ∈ Q ->
        DualNormDef ((fderiv Real f x).toLinearMap - (fderiv Real f y).toLinearMap) <=
          L * norm (x - y)) :
    forall x : Q,
      f (T_Q Q f L x) <= f x + sInf
        ((fun y =>
          DualPairing ((fderiv Real f x).toLinearMap) (y - x) +
            (L / 2) * norm (y - x) ^ 2) '' Q) := by
  intro x
  have hx : (x : E) ∈ Q := x.property
  have hy : (T_Q Q f L x : E) ∈ Q := (T_Q Q f L x).property
  have hupper :=
    smooth_convex_upper_bound (hQ_convex := hQ_convex) (f := f) (hf_diff := hf_diff)
      (hL := hL) (hgrad_lipschitz := hgrad_lipschitz) x hx (T_Q Q f L x) hy
  let g : E → ℝ := fun y =>
    DualPairing ((fderiv ℝ f x).toLinearMap) (y - x) + (L / 2) * ‖y - x‖ ^ 2
  have hval :
      sInf (g '' Q) = g (T_Q Q f L x : E) := by
    simpa [g] using
      smooth_convex_TQ_value_eq_sInf (hQ_closed := hQ_closed) (hL := hL) x
  have hupper' : f (T_Q Q f L x) ≤ f x + g (T_Q Q f L x : E) := by
    simpa [g, add_assoc] using hupper
  simpa [g, hval] using hupper'

/-- Definition 1.3.2.
Let `Q ⊆ E` be closed and convex. A function `d : E → ℝ` is a prox-function for `Q` if it is
continuous and `σ`-strongly convex on `Q` for some `σ > 0`. -/
def ProxFunction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) (d : E → ℝ) : Prop :=
  IsProxFunction Q d

/-- Definition 1.3.2.
Define the prox-center `x0 ∈ Q` by `x0 ∈ argmin_{x ∈ Q} d x` (equation (prox_center_3)) and
assume the normalization `d x0 = 0`. -/
def IsNormalizedProxCenter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) (d : E → ℝ) (x0 : E) : Prop :=
  IsProxCenter Q d x0 ∧ d x0 = 0

/-- Proposition 1.3.3.
Assume `d` is `σ`-strongly convex on `Q` and `x0 ∈ argmin_{x ∈ Q} d x` with `d x0 = 0`. Then for
all `x ∈ Q`, `d x ≥ (σ / 2) ‖x - x0‖^2` (equation (3.4)). -/
theorem prox_center_lower_bound_section03 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E}
    (hconv : StrongConvexOn Q σ d) (hx0 : IsNormalizedProxCenter Q d x0) :
    ∀ x ∈ Q, d x ≥ (1 / 2 : ℝ) * σ * ‖x - x0‖ ^ (2 : ℕ) := by
  rcases hx0 with ⟨hx0min, hx0zero⟩
  intro x hx
  exact
    prox_center_lower_bound (Q2 := Q) (d2 := d) (σ2 := σ) (u0 := x0)
      hconv hx0min hx0zero x hx

/-- Definition 1.3.3.
Consider the smooth convex minimization problem `min_{x ∈ Q} f x` (equation (3.5)), where
`Q ⊆ E` is closed and convex, and `f` is convex and differentiable on `Q` with `L`-Lipschitz
continuous gradient as in (grad_lipschitz). -/
def SmoothConvexMinimizationProblem {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Q : Set E) (f : E → ℝ) (L : ℝ) : Prop :=
  IsClosed Q ∧ Convex ℝ Q ∧ ConvexOn ℝ Q f ∧ DifferentiableOn ℝ f Q ∧ 0 < L ∧
    ∀ x ∈ Q, ∀ y ∈ Q,
      DualNormDef ((fderiv ℝ f x).toLinearMap - (fderiv ℝ f y).toLinearMap) ≤
        L * ‖x - y‖

/-- Definition 1.3.4.
Let `{α_i}_{i ≥ 0}` be positive step-size parameters and define
`A_k = ∑_{i=0}^k α_i` (equation (Ak_def)). -/
def A_k (α : ℕ → ℝ) (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) (fun i => α i)

/-- Definition 1.3.4.
Given points `x_0, …, x_k ∈ Q`, define
`ψ_k = min_{x ∈ Q} { (L/σ) d x + ∑_{i=0}^k α_i [ f(x_i) + ⟪∇ f(x_i), x - x_i⟫ ] }`
(equation (psi_k_def)). -/
noncomputable def psi_k {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (f d : E → ℝ) (L σ : ℝ) (α : ℕ → ℝ)
    (xSeq : ℕ → Q) (k : ℕ) : ℝ :=
  sInf ((fun z : E =>
    (L / σ) * d z +
      Finset.sum (Finset.range (k + 1)) (fun i =>
        let xi : E := xSeq i
        α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) (z - xi)))) '' Q)

/-- Definition 1.3.4.
Given a sequence `{y_k} ⊆ Q`, define the relation
`(R_k): A_k f(y_k) ≤ ψ_k` (equation (Rk)). -/
def R_k {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (f d : E → ℝ) (L σ : ℝ) (α : ℕ → ℝ)
    (xSeq : ℕ → Q) (ySeq : ℕ → Q) (k : ℕ) : Prop :=
  A_k α k * f (ySeq k) ≤ psi_k Q f d L σ α xSeq k

/-- The quadratic model at `T_Q` is minimal on `Q`. -/
lemma R0_TQ_model_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} (hQ_closed : IsClosed Q) {f : E → ℝ} {L : ℝ}
    (hL : 0 < L) (x0 : Q) :
    ∀ z ∈ Q,
      DualPairing ((fderiv ℝ f x0).toLinearMap) ((T_Q Q f L x0 : E) - x0) +
          (L / 2) * ‖(T_Q Q f L x0 : E) - x0‖ ^ 2
        ≤
      DualPairing ((fderiv ℝ f x0).toLinearMap) (z - x0) + (L / 2) * ‖z - x0‖ ^ 2 := by
  classical
  let g : E → ℝ := fun y =>
    DualPairing ((fderiv ℝ f x0).toLinearMap) (y - x0) + (L / 2) * ‖y - x0‖ ^ 2
  have hmin_exists : ∃ y : Q, IsMinOn g Q (y : E) :=
    smooth_convex_TQ_exists_isMinOn (hQ_closed := hQ_closed) (hL := hL) x0
  have hmin_TQ : IsMinOn g Q (T_Q Q f L x0 : E) :=
    T_Q_isMinOn_of_exists (Q := Q) (f := f) (L := L) x0 hmin_exists
  intro z hz
  have hle : g (T_Q Q f L x0 : E) ≤ g z := (isMinOn_iff.mp hmin_TQ) z hz
  simpa [g] using hle

/-- Scale the prox-center lower bound to compare with the quadratic model. -/
lemma R0_scaled_quadratic_le_prox {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {d : E → ℝ} {σ L : ℝ} (α : ℕ → ℝ) {x0 : E}
    (hconv : StrongConvexOn Q σ d) (hx0 : IsNormalizedProxCenter Q d x0)
    (hσ : 0 < σ) (hL : 0 < L) (hα0 : α 0 ∈ Set.Ioc (0 : ℝ) 1) :
    ∀ z ∈ Q,
      (α 0) * ((L / 2) * ‖z - x0‖ ^ 2) ≤ (L / σ) * d z := by
  intro z hz
  have hprox : (1 / 2 : ℝ) * σ * ‖z - x0‖ ^ 2 ≤ d z := by
    simpa [ge_iff_le] using
      (prox_center_lower_bound_section03 (hconv := hconv) (hx0 := hx0) z hz)
  have hLσ_nonneg : 0 ≤ L / σ := by
    exact div_nonneg (le_of_lt hL) (le_of_lt hσ)
  have hscaled :
      (L / σ) * ((1 / 2 : ℝ) * σ * ‖z - x0‖ ^ 2) ≤ (L / σ) * d z := by
    exact mul_le_mul_of_nonneg_left hprox hLσ_nonneg
  have hscaled' : (L / 2) * ‖z - x0‖ ^ 2 ≤ (L / σ) * d z := by
    have hσ_ne : (σ : ℝ) ≠ 0 := ne_of_gt hσ
    have hcalc :
        (L / σ) * ((1 / 2 : ℝ) * σ * ‖z - x0‖ ^ 2) = (L / 2) * ‖z - x0‖ ^ 2 := by
      field_simp [hσ_ne, mul_comm, mul_left_comm, mul_assoc]
    calc
      (L / 2) * ‖z - x0‖ ^ 2 =
          (L / σ) * ((1 / 2 : ℝ) * σ * ‖z - x0‖ ^ 2) := by
        symm
        exact hcalc
      _ ≤ (L / σ) * d z := hscaled
  have ht_nonneg : 0 ≤ (L / 2) * ‖z - x0‖ ^ 2 := by
    have hL2 : 0 ≤ L / 2 := by nlinarith [hL]
    exact mul_nonneg hL2 (pow_two_nonneg ‖z - x0‖)
  have hα_le1 : α 0 ≤ 1 := hα0.2
  calc
    (α 0) * ((L / 2) * ‖z - x0‖ ^ 2) ≤ 1 * ((L / 2) * ‖z - x0‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_right hα_le1 ht_nonneg
    _ = (L / 2) * ‖z - x0‖ ^ 2 := by ring
    _ ≤ (L / σ) * d z := hscaled'

/-- Pointwise lower bound for the `psi_0` comparison. -/
lemma R0_pointwise_bound_for_csInf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (hf_diff : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hL : 0 < L)
    (hgrad_lipschitz :
      ∀ x ∈ Q, ∀ y ∈ Q,
        DualNormDef ((fderiv ℝ f x).toLinearMap - (fderiv ℝ f y).toLinearMap) ≤
          L * ‖x - y‖)
    (hconv : StrongConvexOn Q σ d) (hσ : 0 < σ) (x0 : Q)
    (hx0 : IsNormalizedProxCenter Q d x0) (hα0 : α 0 ∈ Set.Ioc (0 : ℝ) 1) :
    ∀ z ∈ Q,
      (α 0) * f (T_Q Q f L x0) ≤
        (L / σ) * d z +
          (α 0) * (f x0 + DualPairing ((fderiv ℝ f x0).toLinearMap) (z - x0)) := by
  intro z hz
  have hx0' : (x0 : E) ∈ Q := x0.property
  have hy0' : (T_Q Q f L x0 : E) ∈ Q := (T_Q Q f L x0).property
  have hupper :=
    smooth_convex_upper_bound (hQ_convex := hQ_convex) (f := f) (hf_diff := hf_diff)
      (hL := hL) (hgrad_lipschitz := hgrad_lipschitz) x0 hx0' (T_Q Q f L x0) hy0'
  let g : E → ℝ := fun y =>
    DualPairing ((fderiv ℝ f x0).toLinearMap) (y - x0) + (L / 2) * ‖y - x0‖ ^ 2
  have hupper' : f (T_Q Q f L x0) ≤ f x0 + g (T_Q Q f L x0 : E) := by
    simpa [g, add_assoc] using hupper
  have hmodel_le : g (T_Q Q f L x0 : E) ≤ g z := by
    have h :=
      R0_TQ_model_le (hQ_closed := hQ_closed) (hL := hL) (f := f) (x0 := x0) z hz
    simpa [g] using h
  have hupper_z : f (T_Q Q f L x0) ≤ f x0 + g z := by
    have hmodel_le' : f x0 + g (T_Q Q f L x0 : E) ≤ f x0 + g z := by
      simpa [add_comm] using (add_le_add_right hmodel_le (f x0))
    exact le_trans hupper' hmodel_le'
  have hα0_nonneg : 0 ≤ α 0 := by
    exact le_of_lt hα0.1
  have hmul :
      (α 0) * f (T_Q Q f L x0) ≤ (α 0) * (f x0 + g z) := by
    exact mul_le_mul_of_nonneg_left hupper_z hα0_nonneg
  have hmul' :
      (α 0) * f (T_Q Q f L x0) ≤
        (α 0) * f x0 + (α 0) * DualPairing ((fderiv ℝ f x0).toLinearMap) (z - x0) +
          (α 0) * ((L / 2) * ‖z - x0‖ ^ 2) := by
    simpa [g, mul_add, add_assoc, add_left_comm, add_comm] using hmul
  have hscaled :
      (α 0) * ((L / 2) * ‖z - x0‖ ^ 2) ≤ (L / σ) * d z :=
    R0_scaled_quadratic_le_prox (α := α) (hconv := hconv) (hx0 := hx0)
      (hσ := hσ) (hL := hL) (hα0 := hα0) z hz
  have hsum :
      (α 0) * f x0 + (α 0) * DualPairing ((fderiv ℝ f x0).toLinearMap) (z - x0) +
          (α 0) * ((L / 2) * ‖z - x0‖ ^ 2)
        ≤
      (α 0) * f x0 + (α 0) * DualPairing ((fderiv ℝ f x0).toLinearMap) (z - x0) +
          (L / σ) * d z := by
    have h :=
      add_le_add_left hscaled
        ((α 0) * f x0 + (α 0) * DualPairing ((fderiv ℝ f x0).toLinearMap) (z - x0))
    simpa [add_assoc, add_left_comm, add_comm] using h
  have hfinal := le_trans hmul' hsum
  simpa [mul_add, add_assoc, add_left_comm, add_comm] using hfinal

/-- Proposition 1.3.4.
Assume `α_0 ∈ (0,1]`. Let `x0` be the prox-center of `Q` from Definition 3.4, and set
`y0 = T_Q(x0)` (equation (y0_def)). Then the relation `(R_0)` in (Rk) holds. -/
theorem R0_relation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (hf_diff : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hL : 0 < L)
    (hgrad_lipschitz :
      ∀ x ∈ Q, ∀ y ∈ Q,
        DualNormDef ((fderiv ℝ f x).toLinearMap - (fderiv ℝ f y).toLinearMap) ≤
          L * ‖x - y‖)
    (hconv : StrongConvexOn Q σ d) (hσ : 0 < σ)
    (xSeq ySeq : ℕ → Q) (x0 : Q) (hx0 : IsNormalizedProxCenter Q d x0)
    (hα0 : α 0 ∈ Set.Ioc (0 : ℝ) 1)
    (hxSeq0 : xSeq 0 = x0) (hySeq0 : ySeq 0 = T_Q Q f L x0) :
    R_k Q f d L σ α xSeq ySeq 0 := by
  classical
  have hgoal :
      α 0 * f ↑(T_Q Q f L x0) ≤
        sInf ((fun a ↦ L / σ * d a + α 0 * (f ↑x0 + DualPairing (↑(fderiv ℝ f ↑x0)) (a - ↑x0))) '' Q) := by
      refine le_csInf ?_ ?_
      · refine ⟨(L / σ) * d (x0 : E) +
          (α 0) * (f x0 + DualPairing ((fderiv ℝ f x0).toLinearMap) ((x0 : E) - x0)), ?_⟩
        exact ⟨(x0 : E), x0.property, rfl⟩
      · intro b hb
        rcases hb with ⟨z, hz, rfl⟩
        exact
          R0_pointwise_bound_for_csInf (α := α) (hQ_closed := hQ_closed)
            (hQ_convex := hQ_convex) (hf_diff := hf_diff) (hL := hL)
            (hgrad_lipschitz := hgrad_lipschitz) (hconv := hconv) (hσ := hσ) (x0 := x0)
            (hx0 := hx0) (hα0 := hα0) z hz
  simpa [R_k, A_k, psi_k, hxSeq0, hySeq0] using hgoal

/-- Definition 1.3.5.
For `k ≥ 0`, define `z_k ∈ Q` to be any minimizer achieving `ψ_k` in (psi_k_def), namely
`z_k ∈ argmin_{x ∈ Q} { (L/σ) d x + ∑_{i=0}^k α_i [ f(x_i) + ⟪∇ f(x_i), x - x_i⟫ ] }`
(equation (zk_def)). -/
noncomputable def z_k_objective {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (f d : E → ℝ) (L σ : ℝ) (α : ℕ → ℝ)
    (xSeq : ℕ → Q) (k : ℕ) : E → ℝ :=
  fun z =>
    (L / σ) * d z +
      Finset.sum (Finset.range (k + 1)) (fun i =>
        let xi : E := xSeq i
        α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) (z - xi)))

/-- Definition 1.3.5.
Under the prox assumptions used later, `z_k` is certified by `z_k_isMinOn` to minimize the
auxiliary objective `z_k_objective`. -/
noncomputable def z_k {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (f d : E → ℝ) (L σ : ℝ) (α : ℕ → ℝ)
    (xSeq : ℕ → Q) (k : ℕ) : Q := by
  classical
  let g : E → ℝ := z_k_objective Q f d L σ α xSeq k
  by_cases h : ∃ z : Q, IsMinOn g Q (z : E)
  · exact Classical.choose h
  · exact xSeq k

/-- Internal implementation bridge: if a minimizer of `z_k_objective` exists, `z_k` is chosen to
be one. This is intentionally kept private; the paper-facing interface is `z_k_isMinOn`. -/
private lemma z_k_isMinOn_of_exists_internal {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} {α : ℕ → ℝ}
    {xSeq : ℕ → Q} {k : ℕ}
    (h :
      ∃ z : Q,
        IsMinOn (z_k_objective Q f d L σ α xSeq k) Q (z : E)) :
    IsMinOn (z_k_objective Q f d L σ α xSeq k) Q (z_k Q f d L σ α xSeq k : E) := by
  classical
  simpa [z_k, h] using (Classical.choose_spec h)

/-- Internal existence theorem for the auxiliary objective defining `z_k`. This is kept private so
downstream files use `z_k_isMinOn` instead of the intermediate existence packaging. -/
private lemma z_k_exists_isMinOn_internal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} {α : ℕ → ℝ}
    {xSeq : ℕ → Q} {k : ℕ} (hQ_closed : IsClosed Q) (hd_cont : ContinuousOn d Q)
    (hL : 0 < L) (hconv : StrongConvexOn Q σ d) (hσ : 0 < σ) (x0 : Q)
    (hx0 : IsNormalizedProxCenter Q d x0) :
    ∃ z : Q,
      IsMinOn (z_k_objective Q f d L σ α xSeq k) Q (z : E) := by
  classical
  let g : E → ℝ := z_k_objective Q f d L σ α xSeq k
  let s : Module.Dual ℝ E :=
    Finset.sum (Finset.range (k + 1)) (fun i =>
      α i • (fderiv ℝ f (xSeq i)).toLinearMap)
  let c : ℝ :=
    Finset.sum (Finset.range (k + 1)) (fun i =>
      let xi : E := xSeq i
      α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) ((x0 : E) - xi)))
  let M : ℝ := DualNormDef (-s)
  let R : ℝ := max 0 (2 * M / L)
  let K : Set E := Metric.closedBall (x0 : E) R ∩ Q
  have hg_eq :
      g =
        fun z : E =>
          (L / σ) * d z + c + DualPairing s (z - (x0 : E)) := by
    funext z
    have hs_apply :
        DualPairing s (z - (x0 : E)) =
          Finset.sum (Finset.range (k + 1)) (fun i =>
            α i * DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (z - (x0 : E))) := by
      simp [s, DualPairing]
    calc
      g z =
          (L / σ) * d z +
            Finset.sum (Finset.range (k + 1)) (fun i =>
              let xi : E := xSeq i
              α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) (z - xi))) := rfl
      _ =
          (L / σ) * d z +
            Finset.sum (Finset.range (k + 1)) (fun i =>
              let xi : E := xSeq i
              α i * (f xi +
                (DualPairing ((fderiv ℝ f xi).toLinearMap) (z - (x0 : E)) +
                  DualPairing ((fderiv ℝ f xi).toLinearMap) ((x0 : E) - xi)))) := by
            refine congrArg (fun t : ℝ => (L / σ) * d z + t) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hsplit :
                z - (xSeq i : E) =
                  (z - (x0 : E)) + ((x0 : E) - (xSeq i : E)) := by
              abel
            calc
              ((let xi : E := xSeq i;
                α i * (f xi + DualPairing ((fderiv ℝ f xi).toLinearMap) (z - xi)))) =
                  α i *
                    (f (xSeq i) +
                      DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (z - (xSeq i : E))) := by
                  rfl
              _ =
                  α i *
                    (f (xSeq i) +
                      DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap)
                        ((z - (x0 : E)) + ((x0 : E) - (xSeq i : E)))) := by
                  rw [hsplit]
              _ =
                  α i *
                    (f (xSeq i) +
                      (DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (z - (x0 : E)) +
                        DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap)
                          ((x0 : E) - (xSeq i : E)))) := by
                  simp [DualPairing]
              _ =
                  ((let xi : E := xSeq i;
                    α i * (f xi +
                      (DualPairing ((fderiv ℝ f xi).toLinearMap) (z - (x0 : E)) +
                        DualPairing ((fderiv ℝ f xi).toLinearMap) ((x0 : E) - xi))))) := by
                  rfl
      _ =
          (L / σ) * d z + c +
            Finset.sum (Finset.range (k + 1)) (fun i =>
              α i * DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (z - (x0 : E))) := by
            simp [c, Finset.sum_add_distrib, mul_add, add_left_comm, add_comm]
      _ = (L / σ) * d z + c + DualPairing s (z - (x0 : E)) := by
            rw [hs_apply]
  have hR_nonneg : 0 ≤ R := by
    exact le_max_left _ _
  have hx0K : (x0 : E) ∈ K := by
    refine ⟨?_, x0.property⟩
    simpa using (Metric.mem_closedBall_self (x := (x0 : E)) hR_nonneg)
  have hK_nonempty : K.Nonempty := ⟨x0, hx0K⟩
  have hK_compact : IsCompact K := by
    have hball : IsCompact (Metric.closedBall (x0 : E) R) :=
      isCompact_closedBall (x := (x0 : E)) (r := R)
    simpa [K, Set.inter_comm] using (hball.inter_right hQ_closed)
  have hd_cont_K : ContinuousOn d K := by
    exact hd_cont.mono (by intro z hz; exact hz.2)
  have hcont_s : Continuous fun z : E => s z := by
    simpa using (s.continuous_of_finiteDimensional)
  have hcont_lin : Continuous fun z : E => DualPairing s (z - (x0 : E)) := by
    have hcont_sub : Continuous fun z : E => s z - s x0 := hcont_s.sub continuous_const
    simpa [DualPairing, map_sub] using hcont_sub
  have hcont_g' :
      ContinuousOn
        (fun z : E => (L / σ) * d z + c + DualPairing s (z - (x0 : E))) K := by
    have hscaled : ContinuousOn (fun z : E => (L / σ) * d z) K :=
      continuousOn_const.mul hd_cont_K
    exact (hscaled.add continuousOn_const).add hcont_lin.continuousOn
  have hcont_g_on : ContinuousOn g K := by
    simpa [hg_eq] using hcont_g'
  obtain ⟨y, hyK, hyminK⟩ := hK_compact.exists_isMinOn hK_nonempty hcont_g_on
  have hyQ : y ∈ Q := hyK.2
  have hx0g : g (x0 : E) = c := by
    simp [hg_eq, hx0.2, DualPairing]
  have hyc : g y ≤ c := by
    have hxy : g y ≤ g x0 := (isMinOn_iff.mp hyminK) x0 hx0K
    simpa [hx0g] using hxy
  have houtside :
      ∀ z ∈ Q, R ≤ ‖z - (x0 : E)‖ → c ≤ g z := by
    intro z hzQ hzR
    have hR' : 2 * M / L ≤ ‖z - (x0 : E)‖ := by
      exact le_trans (le_max_right _ _) hzR
    have hR'' : 2 * M ≤ ‖z - (x0 : E)‖ * L := by
      have h := (div_le_iff₀ hL).1 hR'
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hlin : DualPairing s (z - (x0 : E)) ≥ -M * ‖z - (x0 : E)‖ := by
      have h :=
        dualPairing_le_dualNormDef_mul_norm_section02 (s := -s) (x := z - (x0 : E))
      have h' : -DualPairing s (z - (x0 : E)) ≤ M * ‖z - (x0 : E)‖ := by
        simpa [DualPairing, M] using h
      linarith
    have hprox : (1 / 2 : ℝ) * σ * ‖z - (x0 : E)‖ ^ 2 ≤ d z := by
      simpa [ge_iff_le] using
        (prox_center_lower_bound_section03 (hconv := hconv) (hx0 := hx0) z hzQ)
    have hLσ_nonneg : 0 ≤ L / σ := by
      exact div_nonneg (le_of_lt hL) (le_of_lt hσ)
    have hscaled :
        (L / σ) * ((1 / 2 : ℝ) * σ * ‖z - (x0 : E)‖ ^ 2) ≤ (L / σ) * d z := by
      exact mul_le_mul_of_nonneg_left hprox hLσ_nonneg
    have hscaled' : (L / 2) * ‖z - (x0 : E)‖ ^ 2 ≤ (L / σ) * d z := by
      have hσ_ne : (σ : ℝ) ≠ 0 := ne_of_gt hσ
      have hcalc :
          (L / σ) * ((1 / 2 : ℝ) * σ * ‖z - (x0 : E)‖ ^ 2) =
            (L / 2) * ‖z - (x0 : E)‖ ^ 2 := by
        field_simp [hσ_ne, mul_comm, mul_left_comm, mul_assoc]
      calc
        (L / 2) * ‖z - (x0 : E)‖ ^ 2 =
            (L / σ) * ((1 / 2 : ℝ) * σ * ‖z - (x0 : E)‖ ^ 2) := by
          symm
          exact hcalc
        _ ≤ (L / σ) * d z := hscaled
    have hsum :
        -M * ‖z - (x0 : E)‖ + (L / 2) * ‖z - (x0 : E)‖ ^ 2 ≤
          DualPairing s (z - (x0 : E)) + (L / σ) * d z := by
      linarith
    have hbound :
        c + (-M * ‖z - (x0 : E)‖ + (L / 2) * ‖z - (x0 : E)‖ ^ 2) ≤ g z := by
      have h := add_le_add_left hsum c
      simpa [hg_eq, add_assoc, add_left_comm, add_comm] using h
    have hquad : 0 ≤ -M * ‖z - (x0 : E)‖ + (L / 2) * ‖z - (x0 : E)‖ ^ 2 := by
      have hr : 0 ≤ ‖z - (x0 : E)‖ := norm_nonneg _
      nlinarith [hR'', hr, hL]
    have hbase : c ≤ c + (-M * ‖z - (x0 : E)‖ + (L / 2) * ‖z - (x0 : E)‖ ^ 2) := by
      linarith
    exact le_trans hbase hbound
  have hyminQ : IsMinOn g Q y := by
    intro z hzQ
    by_cases hzR : ‖z - (x0 : E)‖ ≤ R
    · have hzball : z ∈ Metric.closedBall (x0 : E) R := by
        exact (Metric.mem_closedBall).2 (by simpa [dist_eq_norm] using hzR)
      exact (isMinOn_iff.mp hyminK) z ⟨hzball, hzQ⟩
    · have hzR' : R ≤ ‖z - (x0 : E)‖ := le_of_not_ge hzR
      have hgz : c ≤ g z := houtside z hzQ hzR'
      exact le_trans hyc hgz
  refine ⟨⟨y, hyQ⟩, ?_⟩
  simpa [g] using hyminQ

/-- Paper-facing minimizer theorem for `z_k`: under the standard prox assumptions, the chosen
point `z_k` minimizes the canonical objective `z_k_objective`. -/
lemma z_k_isMinOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} {α : ℕ → ℝ}
    {xSeq : ℕ → Q} {k : ℕ} (hQ_closed : IsClosed Q) (hd_cont : ContinuousOn d Q)
    (hL : 0 < L) (hconv : StrongConvexOn Q σ d) (hσ : 0 < σ) (x0 : Q)
    (hx0 : IsNormalizedProxCenter Q d x0) :
    IsMinOn (z_k_objective Q f d L σ α xSeq k) Q (z_k Q f d L σ α xSeq k : E) := by
  exact z_k_isMinOn_of_exists_internal
    (z_k_exists_isMinOn_internal (Q := Q) (f := f) (d := d) (L := L) (σ := σ) (α := α)
      (xSeq := xSeq) (k := k) hQ_closed hd_cont hL hconv hσ x0 hx0)

/-- Supporting hyperplane inequality for a differentiable convex function on a convex set. -/
lemma section03_convex_support_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f : E → ℝ} (hQ_convex : Convex ℝ Q)
    (hf_convex : ConvexOn ℝ Q f) {u v : E} (hu : u ∈ Q) (hv : v ∈ Q)
    (hv_diff : DifferentiableAt ℝ f v) :
    f u ≥ f v + DualPairing ((fderiv ℝ f v).toLinearMap) (u - v) := by
  classical
  -- Reduce to a one-dimensional convex function on `[0,1]` and compare the derivative at `0`
  -- with the secant slope to `1`.
  let gAff : ℝ →ᵃ[ℝ] E := AffineMap.lineMap v u
  have hseg : Set.Icc (0 : ℝ) 1 ⊆ (fun t => gAff t) ⁻¹' Q := by
    intro t ht
    simpa [gAff] using hQ_convex.lineMap_mem hv hu ht
  have hgPre : ConvexOn ℝ ((fun t => gAff t) ⁻¹' Q) (fun t => f (gAff t)) := by
    simpa [Function.comp, gAff] using (hf_convex.comp_affineMap gAff)
  have hg : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => f (gAff t)) := by
    refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
    intro x hx y hy a b ha hb hab
    exact hgPre.2 (hseg hx) (hseg hy) ha hb hab
  have hInner : HasDerivAt (fun t : ℝ => gAff t) (u - v) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => v + t • (u - v)) (u - v) 0 := by
      simpa using
        (HasDerivAt.const_add v ((hasDerivAt_id (0 : ℝ)).smul_const (u - v)))
    simpa [gAff, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm, add_left_comm,
      add_assoc] using h0
  have hDeriv : HasDerivAt (fun t : ℝ => f (gAff t)) ((fderiv ℝ f v) (u - v)) 0 := by
    have hAff0 : gAff 0 = v := by
      simp [gAff, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    have hF : HasFDerivAt f (fderiv ℝ f v) (gAff 0) := by
      simpa [hAff0] using hv_diff.hasFDerivAt
    simpa [Function.comp] using
      (HasFDerivAt.comp_hasDerivAt (x := 0) (f := fun t : ℝ => gAff t) (l := f) hF hInner)
  have hle : ((fderiv ℝ f v) (u - v)) ≤ slope (fun t : ℝ => f (gAff t)) 0 1 := by
    have hx0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    have hy1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    simpa using hg.le_slope_of_hasDerivAt hx0 hy1 (by norm_num) hDeriv
  have hslope :
      slope (fun t : ℝ => f (gAff t)) 0 1 = f (gAff 1) - f (gAff 0) := by
    simp [slope_def_field]
  have hfinal : f (gAff 0) + ((fderiv ℝ f v) (u - v)) ≤ f (gAff 1) := by
    linarith [hle, hslope]
  have hAff0 : gAff 0 = v := by
    simp [gAff, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hAff1 : gAff 1 = u := by
    simp [gAff, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  -- Rewrite back in terms of `u, v`.
  simpa [DualPairing, hAff0, hAff1, add_comm, add_left_comm, add_assoc] using hfinal

/-- Basic properties of `τ_k = α_{k+1} / A_{k+1}` under (3.6). -/
lemma section03_tau_props (α : ℕ → ℝ) (k : ℕ) (hα_pos : ∀ k, 0 < α k)
    (hα_sq : ∀ k, (α (k + 1)) ^ 2 ≤ A_k α (k + 1)) :
    let A := A_k α (k + 1)
    let τ := α (k + 1) / A
    0 < A ∧ 0 ≤ τ ∧ τ ≤ 1 ∧ τ ^ 2 ≤ 1 / A := by
  classical
  let A := A_k α (k + 1)
  let τ := α (k + 1) / A
  have hsum : A = A_k α k + α (k + 1) := by
    simp [A, A_k, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
  have hsum_nonneg : 0 ≤ A_k α k := by
    unfold A_k
    exact Finset.sum_nonneg (fun i _ => le_of_lt (hα_pos i))
  have hA_ge : α (k + 1) ≤ A := by
    have : α (k + 1) ≤ A_k α k + α (k + 1) := by
      nlinarith [hsum_nonneg]
    simpa [hsum] using this
  have hA_pos : 0 < A := lt_of_lt_of_le (hα_pos (k + 1)) hA_ge
  have hτ_nonneg : 0 ≤ τ := by
    exact div_nonneg (le_of_lt (hα_pos (k + 1))) (le_of_lt hA_pos)
  have hτ_le : τ ≤ 1 := by
    have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
    have hτ_le' : α (k + 1) / A ≤ 1 := by
      exact div_le_one_of_le₀ hA_ge hA_nonneg
    simpa [τ] using hτ_le'
  have hA_ne : A ≠ 0 := ne_of_gt hA_pos
  have hτ_sq : τ ^ 2 ≤ 1 / A := by
    have hA2_pos : 0 < A ^ 2 := by
      exact pow_pos hA_pos 2
    have hineq : (α (k + 1)) ^ 2 ≤ (1 / A) * A ^ 2 := by
      have hcalc : (1 / A) * A ^ 2 = A := by
        field_simp [hA_ne]
      have hα_sq' : (α (k + 1)) ^ 2 ≤ A := by
        simpa [A] using hα_sq k
      calc
        (α (k + 1)) ^ 2 ≤ A := hα_sq'
        _ = (1 / A) * A ^ 2 := by
          symm
          exact hcalc
    have hdiv : (α (k + 1)) ^ 2 / A ^ 2 ≤ 1 / A := by
      exact (div_le_iff₀ hA2_pos).2 hineq
    simpa [τ, div_pow] using hdiv
  refine ⟨hA_pos, hτ_nonneg, hτ_le, hτ_sq⟩

/-- Change-of-variables identity for `y = τ_k x + (1-τ_k) y_k`. -/
lemma section03_change_of_variables_y {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} (hQ_convex : Convex ℝ Q) {f d : E → ℝ} {L σ : ℝ}
    (α : ℕ → ℝ) (xSeq ySeq : ℕ → Q) (k : ℕ) {x : E} (hx : x ∈ Q)
    (hτ_nonneg : 0 ≤ α (k + 1) / A_k α (k + 1))
    (hτ_le : α (k + 1) / A_k α (k + 1) ≤ 1)
    (hx_update :
      (xSeq (k + 1) : E) =
        (α (k + 1) / A_k α (k + 1)) • (z_k Q f d L σ α xSeq k : E) +
          (1 - α (k + 1) / A_k α (k + 1)) • (ySeq k : E)) :
    let τ := α (k + 1) / A_k α (k + 1)
    let y : E := τ • x + (1 - τ) • (ySeq k : E)
    y ∈ Q ∧ y - (xSeq (k + 1) : E) = τ • (x - (z_k Q f d L σ α xSeq k : E)) := by
  classical
  let τ := α (k + 1) / A_k α (k + 1)
  let y : E := τ • x + (1 - τ) • (ySeq k : E)
  have hy_mem : y ∈ Q := by
    have hyk : (ySeq k : E) ∈ Q := (ySeq k).property
    have h1τ_nonneg : 0 ≤ 1 - τ := by linarith [hτ_le]
    have hsum : τ + (1 - τ) = 1 := by ring
    simpa [y] using hQ_convex hx hyk hτ_nonneg h1τ_nonneg hsum
  have hdiff :
      y - (xSeq (k + 1) : E) = τ • (x - (z_k Q f d L σ α xSeq k : E)) := by
    have hx_update' : (xSeq (k + 1) : E) =
        τ • (z_k Q f d L σ α xSeq k : E) + (1 - τ) • (ySeq k : E) := by
      simpa [τ] using hx_update
    calc
      y - (xSeq (k + 1) : E) =
          (τ • x + (1 - τ) • (ySeq k : E)) -
            (τ • (z_k Q f d L σ α xSeq k : E) + (1 - τ) • (ySeq k : E)) := by
        simp [y, hx_update']
      _ = τ • (x - (z_k Q f d L σ α xSeq k : E)) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add]
  exact ⟨hy_mem, hdiff⟩

/-- Combine the gradient pairing terms using the update for `x_{k+1}`. -/
lemma section03_dualpairing_combine_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (xSeq ySeq : ℕ → Q) (k : ℕ) (hA_pos : 0 < A_k α (k + 1))
    (hx_update :
      (xSeq (k + 1) : E) =
        (α (k + 1) / A_k α (k + 1)) • (z_k Q f d L σ α xSeq k : E) +
          (1 - α (k + 1) / A_k α (k + 1)) • (ySeq k : E))
    (g : Module.Dual ℝ E) (x : E) :
    A_k α k * DualPairing g ((ySeq k : E) - (xSeq (k + 1) : E)) +
        α (k + 1) * DualPairing g (x - (xSeq (k + 1) : E)) =
      α (k + 1) * DualPairing g (x - (z_k Q f d L σ α xSeq k : E)) := by
  classical
  let A := A_k α (k + 1)
  let τ := α (k + 1) / A
  have hA : A = A_k α k + α (k + 1) := by
    simp [A, A_k, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
  have hx_update' :
      (xSeq (k + 1) : E) =
        τ • (z_k Q f d L σ α xSeq k : E) + (1 - τ) • (ySeq k : E) := by
    simpa [A, τ] using hx_update
  have hA_ne : (A : ℝ) ≠ 0 := ne_of_gt hA_pos
  have hcoeff : A_k α k * τ = α (k + 1) * (1 - τ) := by
    have hA' : A_k α k = A - α (k + 1) := by
      linarith [hA]
    calc
      A_k α k * τ = (A - α (k + 1)) * (α (k + 1) / A) := by
        simp [hA', τ]
      _ = α (k + 1) * (1 - α (k + 1) / A) := by
        field_simp [hA_ne, mul_comm, mul_left_comm, mul_assoc]
      _ = α (k + 1) * (1 - τ) := by simp [τ]
  have hyk :
      DualPairing g ((ySeq k : E) - (xSeq (k + 1) : E)) =
        τ * DualPairing g ((ySeq k : E) - (z_k Q f d L σ α xSeq k : E)) := by
    simp [DualPairing, hx_update', map_add, map_smul, sub_eq_add_neg, mul_add]
    ring
  have hxk :
      DualPairing g (x - (xSeq (k + 1) : E)) =
        DualPairing g (x - (z_k Q f d L σ α xSeq k : E)) -
          (1 - τ) * DualPairing g ((ySeq k : E) - (z_k Q f d L σ α xSeq k : E)) := by
    simp [DualPairing, hx_update', map_add, map_smul, sub_eq_add_neg, mul_add]
    ring
  calc
    A_k α k * DualPairing g ((ySeq k : E) - (xSeq (k + 1) : E)) +
        α (k + 1) * DualPairing g (x - (xSeq (k + 1) : E)) =
      A_k α k * (τ * DualPairing g ((ySeq k : E) - (z_k Q f d L σ α xSeq k : E))) +
        α (k + 1) *
          (DualPairing g (x - (z_k Q f d L σ α xSeq k : E)) -
            (1 - τ) * DualPairing g ((ySeq k : E) - (z_k Q f d L σ α xSeq k : E))) := by
      simp [hyk, hxk]
    _ =
        α (k + 1) * DualPairing g (x - (z_k Q f d L σ α xSeq k : E)) +
          (A_k α k * τ - α (k + 1) * (1 - τ)) *
            DualPairing g ((ySeq k : E) - (z_k Q f d L σ α xSeq k : E)) := by
      ring
    _ = α (k + 1) * DualPairing g (x - (z_k Q f d L σ α xSeq k : E)) := by
      simp [hcoeff]

/-- Compare quadratic coefficients using the bound `τ^2 ≤ 1 / A`. -/
lemma section03_quad_coeff_compare {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L A τ : ℝ} (hL : 0 ≤ L) (hA : 0 < A) (hτ : τ ^ 2 ≤ 1 / A) (v : E) :
    (L / (2 * A)) * ‖v‖ ^ 2 ≥ (L / 2) * τ ^ 2 * ‖v‖ ^ 2 := by
  have hnonneg : 0 ≤ (L / 2) * ‖v‖ ^ 2 := by
    have hL2 : 0 ≤ L / 2 := by nlinarith
    exact mul_nonneg hL2 (pow_two_nonneg ‖v‖)
  have hτ_le :
      (L / 2) * τ ^ 2 * ‖v‖ ^ 2 ≤ (L / 2) * (1 / A) * ‖v‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hτ hnonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hA_ne : (A : ℝ) ≠ 0 := ne_of_gt hA
  calc
    (L / (2 * A)) * ‖v‖ ^ 2 = (L / 2) * (1 / A) * ‖v‖ ^ 2 := by
      field_simp [hA_ne, mul_comm, mul_left_comm, mul_assoc]
    _ ≥ (L / 2) * τ ^ 2 * ‖v‖ ^ 2 := by
      simpa [ge_iff_le] using hτ_le

/-- Quadratic-model identity after a change of variables. -/
lemma section03_change_of_variables_model {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (xSeq : ℕ → Q) (k : ℕ) {x y : E} {τ : ℝ}
    (hy_shift :
      y - (xSeq (k + 1) : E) =
        τ • (x - (z_k Q f d L σ α xSeq k : E))) (g : Module.Dual ℝ E) :
    (L / 2) * τ ^ 2 * ‖x - (z_k Q f d L σ α xSeq k : E)‖ ^ 2 +
        τ * DualPairing g (x - (z_k Q f d L σ α xSeq k : E)) =
      (L / 2) * ‖y - (xSeq (k + 1) : E)‖ ^ 2 + DualPairing g (y - (xSeq (k + 1) : E)) := by
  have hnorm :
      ‖τ • (x - (z_k Q f d L σ α xSeq k : E))‖ ^ 2 =
        τ ^ 2 * ‖x - (z_k Q f d L σ α xSeq k : E)‖ ^ 2 := by
    calc
      ‖τ • (x - (z_k Q f d L σ α xSeq k : E))‖ ^ 2 =
          (|τ| * ‖x - (z_k Q f d L σ α xSeq k : E)‖) ^ 2 := by
        simp [norm_smul]
      _ = |τ| ^ 2 * ‖x - (z_k Q f d L σ α xSeq k : E)‖ ^ 2 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_pow |τ| ‖x - (z_k Q f d L σ α xSeq k : E)‖ 2)
      _ = τ ^ 2 * ‖x - (z_k Q f d L σ α xSeq k : E)‖ ^ 2 := by
        simp [pow_two]
  have hlin :
      DualPairing g (τ • (x - (z_k Q f d L σ α xSeq k : E))) =
        τ * DualPairing g (x - (z_k Q f d L σ α xSeq k : E)) := by
    simp [DualPairing, map_smul]
  calc
    (L / 2) * τ ^ 2 * ‖x - (z_k Q f d L σ α xSeq k : E)‖ ^ 2 +
        τ * DualPairing g (x - (z_k Q f d L σ α xSeq k : E)) =
      (L / 2) * ‖τ • (x - (z_k Q f d L σ α xSeq k : E))‖ ^ 2 +
        DualPairing g (τ • (x - (z_k Q f d L σ α xSeq k : E))) := by
      simp [hnorm, hlin, mul_comm, mul_left_comm, mul_assoc]
    _ = (L / 2) * ‖y - (xSeq (k + 1) : E)‖ ^ 2 + DualPairing g (y - (xSeq (k + 1) : E)) := by
      simp [hy_shift]

/-- The quadratic model at `T_Q` dominates the function decrease. -/
lemma section03_model_at_TQ_ge_fdiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} (hQ_convex : Convex ℝ Q) {f : E → ℝ}
    (hf_diff : ∀ x ∈ Q, DifferentiableAt ℝ f x) {L : ℝ} (hL : 0 < L)
    (hgrad_lipschitz :
      ∀ x ∈ Q, ∀ y ∈ Q,
        DualNormDef ((fderiv ℝ f x).toLinearMap - (fderiv ℝ f y).toLinearMap) ≤
          L * ‖x - y‖)
    (x0 : Q) :
    DualPairing ((fderiv ℝ f x0).toLinearMap) ((T_Q Q f L x0 : E) - x0) +
        (L / 2) * ‖(T_Q Q f L x0 : E) - x0‖ ^ 2 ≥
      f (T_Q Q f L x0) - f x0 := by
  have hx0 : (x0 : E) ∈ Q := x0.property
  have hy0 : (T_Q Q f L x0 : E) ∈ Q := (T_Q Q f L x0).property
  have hupper :=
    smooth_convex_upper_bound (hQ_convex := hQ_convex) (f := f) (hf_diff := hf_diff)
      (hL := hL) (hgrad_lipschitz := hgrad_lipschitz) x0 hx0 (T_Q Q f L x0) hy0
  linarith

/-- Affine function `x ↦ ⟪s, x - x0⟫` is convex on a convex set. -/
lemma section03_convex_dualpairing_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} (hQ_convex : Convex ℝ Q) (s : Module.Dual ℝ E) (x0 : E) :
    ConvexOn ℝ Q (fun x => DualPairing s (x - x0)) := by
  have hlin : ConvexOn ℝ Q (fun x : E => DualPairing s x) := (LinearMap.convexOn s hQ_convex)
  have h := hlin.add_const (-DualPairing s x0)
  simpa [DualPairing, map_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
