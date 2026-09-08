module

public import ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.Construction
public import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump.DisjointInterpolation
public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumSummable
public import ReasLib.Analysis.Convex.HessianPerturbation.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Topology.Algebra.Support
public import ReasLib.Analysis.Hessian
public import ReasLib.Analysis.StandardQuadratic
public import ReasLib.Topology.MetricSpace.PairwiseSeparation

public section

open Filter Set Topology
open scoped ContDiff EuclideanSpace Matrix.Norms.L2Operator

namespace PlanarGradient

/-- Radially decreasing points with quarter-scale decay have pairwise disjoint
quarter-norm closed balls. -/
private theorem quarterNormBallsPairwiseDisjoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) (hx : ∀ k, x k ≠ 0)
    (hanti : StrictAnti (fun k ↦ ‖x k‖))
    (hratio : ∀ k, ‖x (k + 1)‖ / ‖x k‖ ≤ (1 : ℝ) / 4) :
    Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.closedBall (x k) (‖x k‖ / 4)) := by
  -- It is enough to compare the two radii with the reverse-triangle lower bound.
  apply Metric.pairwiseDisjoint_closedBall_of_radius_add_lt_dist
  intro i j hij
  have hforward : ∀ {p q : ℕ}, p < q →
      ‖x p‖ / 4 + ‖x q‖ / 4 < dist (x p) (x q) := by
    intro p q hpq
    have hpPos : 0 < ‖x p‖ := norm_pos_iff.mpr (hx p)
    have hqLeSucc : ‖x q‖ ≤ ‖x (p + 1)‖ := by
      exact hanti.antitone (Nat.succ_le_iff.mpr hpq)
    have hSuccLe : ‖x (p + 1)‖ ≤ ‖x p‖ / 4 := by
      have hmul := (div_le_iff₀ hpPos).mp (hratio p)
      nlinarith
    have hqLeQuarter : ‖x q‖ ≤ ‖x p‖ / 4 := hqLeSucc.trans hSuccLe
    have hqLt : ‖x q‖ < ‖x p‖ := hanti hpq
    have hRadius : ‖x p‖ / 4 + ‖x q‖ / 4 < ‖x p‖ - ‖x q‖ := by
      nlinarith
    calc
      ‖x p‖ / 4 + ‖x q‖ / 4 < ‖x p‖ - ‖x q‖ := hRadius
      _ ≤ ‖x p - x q‖ := norm_sub_norm_le _ _
      _ = dist (x p) (x q) := by rw [dist_eq_norm]
  rcases Nat.lt_or_gt_of_ne hij with hijOrder | hjiOrder
  · exact hforward hijOrder
  · rw [add_comm, dist_comm]
    exact hforward hjiOrder

/-- The iterated derivatives of an affine linear functional obey a scale-covariant
norm bound on a closed ball. -/
private theorem norm_iteratedFDeriv_inner_sub_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) (x a z : E) (ρ : ℝ) (hρ : 0 < ρ) (hz : ‖z - x‖ ≤ ρ) :
    ‖iteratedFDeriv ℝ m (fun y ↦ inner ℝ a (y - x)) z‖ ≤
      ‖a‖ * ρ * (ρ⁻¹) ^ m := by
  have hderiv : fderiv ℝ (fun y : E ↦ inner ℝ a (y - x)) = fun _ ↦ innerSL ℝ a := by
    funext y
    have hsub : HasFDerivAt (fun w : E ↦ w - x)
        (ContinuousLinearMap.id ℝ E) y := by
      simpa only [id_eq] using (hasFDerivAt_id y).sub_const x
    have hinner := (innerSL ℝ a).hasFDerivAt.comp y hsub
    change fderiv ℝ ((innerSL ℝ a) ∘ fun w : E ↦ w - x) y = innerSL ℝ a
    simpa only [ContinuousLinearMap.comp_id] using hinner.fderiv
  cases m with
  | zero =>
      -- The zeroth derivative is bounded by Cauchy--Schwarz on the support ball.
      rw [norm_iteratedFDeriv_zero, pow_zero, mul_one]
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left hz (norm_nonneg a))
  | succ m =>
      cases m with
      | zero =>
          -- The first derivative is the Riesz functional associated to `a`.
          rw [norm_iteratedFDeriv_one, congrFun hderiv z, innerSL_apply_norm,
            pow_one]
          field_simp [hρ.ne']
          rfl
      | succ m =>
          -- Every derivative of order at least two of an affine map vanishes.
          have hzero : iteratedFDeriv ℝ (m + 2)
              (fun y : E ↦ inner ℝ a (y - x)) z = 0 := by
            rw [show m + 2 = (m + 1) + 1 by omega,
              iteratedFDeriv_succ_eq_comp_right, hderiv]
            rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m)]
            ext v
            simp only [Function.comp_apply, Pi.zero_apply]
            rw [continuousMultilinearCurryRightEquiv_symm_apply']
            rfl
          rw [show m + 1 + 1 = m + 2 by omega, hzero, norm_zero]
          positivity

/-- Every order of a scaled linear bump has a uniform scale-covariant derivative
bound, with a constant depending only on the cutoff and the order. -/
private theorem exists_scaledLinearBump_iteratedFDeriv_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hχsupport : tsupport χ ⊆ Metric.ball 0 1) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : E) (ρ : ℝ) (a z : E), 0 < ρ →
      ‖iteratedFDeriv ℝ m (AffineBump.scaledLinearBump χ x ρ a) z‖ ≤
        K * ‖a‖ * ρ * (ρ⁻¹) ^ m := by
  classical
  let boundExists : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ y,
      ‖iteratedFDeriv ℝ i χ y‖ ≤ B := fun i ↦
    hχcompact.exists_norm_iteratedFDeriv_le (hχ.of_le (mod_cast le_top))
  let B : ℕ → ℝ := fun i ↦ Classical.choose (boundExists i)
  have hBnonneg (i : ℕ) : 0 ≤ B i := (Classical.choose_spec (boundExists i)).1
  have hBbound (i : ℕ) (y : E) : ‖iteratedFDeriv ℝ i χ y‖ ≤ B i :=
    (Classical.choose_spec (boundExists i)).2 y
  let K : ℝ := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B i
  have hKnonneg : 0 ≤ K := by
    dsimp only [K]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (Nat.cast_nonneg _) (hBnonneg i)
  refine ⟨K, hKnonneg, ?_⟩
  intro x ρ a z hρ
  by_cases hz : z ∈ tsupport (AffineBump.scaledLinearBump χ x ρ a)
  · have hzBall : z ∈ Metric.closedBall x ρ :=
      AffineBump.tsupport_scaledLinearBump_subset_closedBall
        χ hχsupport x ρ a hρ hz
    have hzNorm : ‖z - x‖ ≤ ρ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hzBall
    have hcutoffSmooth : ContDiff ℝ ∞ (fun y : E ↦ χ (ρ⁻¹ • (y - x))) := by
      fun_prop
    have hlinearSmooth : ContDiff ℝ ∞ (fun y : E ↦ inner ℝ a (y - x)) := by
      have hsub : ContDiff ℝ ∞ (fun y : E ↦ y - x) := contDiff_id.sub contDiff_const
      change ContDiff ℝ ∞ ((innerSL ℝ a) ∘ fun y : E ↦ y - x)
      exact (innerSL ℝ a).contDiff.comp hsub
    have hcutoffBound (i : ℕ) (y : E) :
        ‖iteratedFDeriv ℝ i (fun w : E ↦ χ (ρ⁻¹ • (w - x))) y‖ ≤
          B i * (ρ⁻¹) ^ i := by
      let A : E →L[ℝ] E := ρ⁻¹ • ContinuousLinearMap.id ℝ E
      have hA : ‖A‖ ≤ ρ⁻¹ := by
        calc
          ‖A‖ ≤ ‖ρ⁻¹‖ * ‖ContinuousLinearMap.id ℝ E‖ := by
            simpa only [A] using
              norm_smul_le (ρ⁻¹) (ContinuousLinearMap.id ℝ E)
          _ ≤ ρ⁻¹ * 1 := by
            rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
            exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
              (le_of_lt (inv_pos.mpr hρ))
          _ = ρ⁻¹ := mul_one _
      have hcomp := norm_iteratedFDeriv_comp_affine_le i χ A (-ρ⁻¹ • x)
        (hχ.of_le (mod_cast le_top)) y
      have hAffine : (fun w : E ↦ χ (ρ⁻¹ • (w - x))) =
          fun w : E ↦ χ (A w + -ρ⁻¹ • x) := by
        funext w
        congr 1
        calc
          ρ⁻¹ • (w - x) = ρ⁻¹ • w - ρ⁻¹ • x := smul_sub _ _ _
          _ = A w + -ρ⁻¹ • x := by
            simp only [A, smul_apply, ContinuousLinearMap.id_apply, sub_eq_add_neg,
              neg_smul]
      have hArgument : A y + -ρ⁻¹ • x = ρ⁻¹ • (y - x) := by
        calc
          A y + -ρ⁻¹ • x = ρ⁻¹ • y - ρ⁻¹ • x := by
            simp only [A, smul_apply, ContinuousLinearMap.id_apply, sub_eq_add_neg,
              neg_smul]
          _ = ρ⁻¹ • (y - x) := (smul_sub _ _ _).symm
      have hcomp' :
          ‖iteratedFDeriv ℝ i (fun w : E ↦ χ (ρ⁻¹ • (w - x))) y‖ ≤
            ‖iteratedFDeriv ℝ i χ (ρ⁻¹ • (y - x))‖ * ‖A‖ ^ i := by
        rw [hAffine]
        rw [hArgument] at hcomp
        exact hcomp
      calc
        ‖iteratedFDeriv ℝ i (fun w : E ↦ χ (ρ⁻¹ • (w - x))) y‖ ≤
            ‖iteratedFDeriv ℝ i χ (ρ⁻¹ • (y - x))‖ * ‖A‖ ^ i := hcomp'
        _ ≤ B i * (ρ⁻¹) ^ i := by
          exact mul_le_mul (hBbound i _) (pow_le_pow_left₀ (norm_nonneg A) hA i)
            (pow_nonneg (norm_nonneg A) i) (hBnonneg i)
    have hproduct := norm_iteratedFDeriv_mul_le hcutoffSmooth hlinearSmooth z
      (show m ≤ (∞ : ℕ∞ω) by exact_mod_cast le_top)
    have hbumpEq : AffineBump.scaledLinearBump χ x ρ a =
        fun y ↦ χ (ρ⁻¹ • (y - x)) * inner ℝ a (y - x) := by
      funext y
      exact AffineBump.scaledLinearBump_apply χ x ρ a y
    rw [hbumpEq]
    calc
      ‖iteratedFDeriv ℝ m
          (fun y ↦ χ (ρ⁻¹ • (y - x)) * inner ℝ a (y - x)) z‖ ≤
          ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y ↦ χ (ρ⁻¹ • (y - x))) z‖ *
            ‖iteratedFDeriv ℝ (m - i) (fun y ↦ inner ℝ a (y - x)) z‖ := hproduct
      _ ≤ ∑ i ∈ Finset.range (m + 1),
          ((m.choose i : ℝ) * B i) * (‖a‖ * ρ * (ρ⁻¹) ^ m) := by
        apply Finset.sum_le_sum
        intro i hi
        have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hchoose : 0 ≤ (m.choose i : ℝ) := by positivity
        have hcut := hcutoffBound i z
        have hlin := norm_iteratedFDeriv_inner_sub_le (m - i) x a z ρ hρ hzNorm
        have hfirst : (m.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y ↦ χ (ρ⁻¹ • (y - x))) z‖ ≤
              (m.choose i : ℝ) * (B i * (ρ⁻¹) ^ i) :=
          mul_le_mul_of_nonneg_left hcut hchoose
        have hfirstNonneg : 0 ≤ (m.choose i : ℝ) * (B i * (ρ⁻¹) ^ i) := by
          exact mul_nonneg hchoose
            (mul_nonneg (hBnonneg i) (pow_nonneg (le_of_lt (inv_pos.mpr hρ)) i))
        calc
          (m.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (fun y ↦ χ (ρ⁻¹ • (y - x))) z‖ *
              ‖iteratedFDeriv ℝ (m - i) (fun y ↦ inner ℝ a (y - x)) z‖ ≤
              (m.choose i : ℝ) * (B i * (ρ⁻¹) ^ i) *
                (‖a‖ * ρ * (ρ⁻¹) ^ (m - i)) := by
            exact mul_le_mul hfirst hlin (norm_nonneg _) hfirstNonneg
          _ = ((m.choose i : ℝ) * B i) * (‖a‖ * ρ * (ρ⁻¹) ^ m) := by
            calc
              (m.choose i : ℝ) * (B i * (ρ⁻¹) ^ i) *
                  (‖a‖ * ρ * (ρ⁻¹) ^ (m - i)) =
                  ((m.choose i : ℝ) * B i) * (‖a‖ * ρ) *
                    ((ρ⁻¹) ^ i * (ρ⁻¹) ^ (m - i)) := by ring
              _ = ((m.choose i : ℝ) * B i) * (‖a‖ * ρ * (ρ⁻¹) ^ m) := by
                rw [← pow_add, Nat.add_sub_of_le him]
                ring
      _ = K * ‖a‖ * ρ * (ρ⁻¹) ^ m := by
        rw [← Finset.sum_mul]
        simp only [K]
        ring
  · rw [iteratedFDeriv_eq_zero_of_notMem_tsupport _ m hz, norm_zero]
    positivity

/-- All-order flat coefficients and quarter-geometric radii give summable
scaled-bump derivative weights. -/
private theorem summableScaledWeightsOfFlatGeometricDecay
    (r : ℕ → ℝ) (d : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hratio : ∀ k, r (k + 1) / r k ≤ (1 : ℝ) / 4)
    (hflat : ∀ m : ℕ, (fun k ↦ |d k|) =o[atTop] (fun k ↦ r k ^ m))
    (K : ℝ) (m : ℕ) :
    Summable (fun k ↦ K * |d k| * (r k / 4) * ((r k / 4)⁻¹) ^ m) := by
  -- Geometric decay controls the radii, while flatness absorbs every inverse scale.
  have hrSummable : Summable r := by
    apply summable_of_ratio_norm_eventually_le
      (show (1 : ℝ) / 4 < 1 by norm_num)
    filter_upwards [] with k
    simpa only [Real.norm_eq_abs, abs_of_pos (hr (k + 1)), abs_of_pos (hr k)] using
      (div_le_iff₀ (hr k)).mp (hratio k)
  have hflatEventually : ∀ᶠ k in atTop, |d k| ≤ r k ^ m := by
    have hbound := (hflat m).bound zero_lt_one
    filter_upwards [hbound] with k hk
    simpa only [Real.norm_eq_abs, abs_abs, one_mul,
      abs_of_pos (pow_pos (hr k) m)] using hk
  refine ((hrSummable.mul_left (|K| * (4 : ℝ) ^ m))).of_norm_bounded_eventually_nat ?_
  filter_upwards [hflatEventually] with k hk
  have hrk : r k ≠ 0 := (hr k).ne'
  have hscale :
      r k ^ m * (r k / 4) * ((r k / 4)⁻¹) ^ m ≤ (4 : ℝ) ^ m * r k := by
    have hidentity :
        r k ^ m * (r k / 4) * ((r k / 4)⁻¹) ^ m =
          ((4 : ℝ) ^ m * r k) / 4 := by
      field_simp [hrk]
      rw [← mul_pow]
      field_simp [hrk]
    rw [hidentity]
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 4 by norm_num) m, (hr k).le]
  have hρpos : 0 < r k / 4 := div_pos (hr k) (by norm_num)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_abs,
    abs_of_pos hρpos, abs_pow, abs_of_pos (inv_pos.mpr hρpos)]
  calc
    |K| * |d k| * (r k / 4) * ((r k / 4)⁻¹) ^ m ≤
        |K| * (r k ^ m * (r k / 4) * ((r k / 4)⁻¹) ^ m) := by
      have hρnonneg : 0 ≤ r k / 4 := hρpos.le
      have hinvPowNonneg : 0 ≤ ((r k / 4)⁻¹) ^ m :=
        pow_nonneg (inv_nonneg.mpr hρnonneg) m
      calc
        |K| * |d k| * (r k / 4) * ((r k / 4)⁻¹) ^ m ≤
            |K| * (r k ^ m) * (r k / 4) * ((r k / 4)⁻¹) ^ m := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hk (abs_nonneg K)) hρnonneg)
            hinvPowNonneg
        _ = |K| * (r k ^ m * (r k / 4) * ((r k / 4)⁻¹) ^ m) := by ring
    _ ≤ |K| * ((4 : ℝ) ^ m * r k) :=
      mul_le_mul_of_nonneg_left hscale (abs_nonneg K)
    _ = |K| * (4 : ℝ) ^ m * r k := by ring

/-- The matrix Hessian deviation of a quadratic perturbation has the same norm as
the perturbation's second iterated Fréchet derivative. -/
private theorem convexHessianQuadraticPerturbationNorm
    {n : ℕ} (Ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hΨ : ContDiff ℝ 2 Ψ) (z : EuclideanSpace ℝ (Fin n)) :
    ‖ConvexAnalysis.hessian
        (fun x ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2 + Ψ x) z - 1‖ =
      ‖iteratedFDeriv ℝ 2 Ψ z‖ := by
  -- Transport the matrix difference to the canonical operator-valued Hessian.
  rw [Matrix.cstar_norm_def, map_sub, map_one,
    ConvexAnalysis.toEuclideanCLM_hessian]
  have hformula :
      fderiv ℝ (gradient (fun x ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2 + Ψ x)) z =
        1 + fderiv ℝ (gradient Ψ) z := by
    simpa only [sub_zero] using
      HessianPerturbation.fderiv_gradient_halfNormSq_sub_add 0 Ψ z hΨ
  rw [hformula, add_sub_cancel_left]
  exact norm_fderiv_gradient_eq_norm_iteratedFDeriv_two Ψ z

/-- PlanarGradient.exists_compactlySupportedInterpolation (Lemma 4.1,
compactly supported interpolation). For every ambient dimension at least two,
there is a positive dimension-dependent
constant such that every embedded alternating-scale sequence is interpolated by the
gradient of a smooth function with a compactly supported quadratic tail and a uniform
operator-norm Hessian bound. -/
theorem exists_compactlySupportedInterpolation (n : ℕ) (h_n : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ι : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
        (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
        (g : ℕ → EuclideanSpace ℝ (Fin 2)) (δ : ℕ → ℝ) (a b : ℝ),
        IsAlternatingScale σ g δ a b →
          ∃ H : EuclideanSpace ℝ (Fin n) → ℝ,
            ContDiff ℝ ∞ H ∧
            ContDiff ℝ ∞
              (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ∧
            HasCompactSupport
              (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ∧
            tsupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ⊆
              Metric.closedBall 0 (5 * ‖g 0‖ / 4) ∧
            (∀ k : ℕ,
              gradient H (ι (g k)) =
                ι (candidate EuclideanPlane.orientation (g k) (δ k))) ∧
            gradient H 0 = 0 ∧
            ConvexAnalysis.hessian H 0 = 1 ∧
            ∀ z : EuclideanSpace ℝ (Fin n),
              ‖ConvexAnalysis.hessian H z - 1‖ ≤
                C * sSup (Set.range (fun k : ℕ ↦ |δ k| / ‖g k‖)) := by
  classical
  -- Fix the cutoff and its analytic interface before constructing the bump series.
  let hInner : (0 : ℝ) < 1 / 3 := by norm_num
  let hOuter : (1 / 3 : ℝ) < 1 / 2 := by norm_num
  let χ : EuclideanSpace ℝ (Fin n) → ℝ :=
    SmoothCutoff.centeredBump 0 (1 / 3) (1 / 2) hInner hOuter
  have hχSmooth : ContDiff ℝ ∞ χ := by
    exact SmoothCutoff.contDiff_centeredBump 0 (1 / 3) (1 / 2) hInner hOuter
  have hχCompact : HasCompactSupport χ := by
    exact SmoothCutoff.hasCompactSupport_centeredBump 0 (1 / 3) (1 / 2) hInner hOuter
  have hχTsupport : tsupport χ = Metric.closedBall 0 (1 / 2) := by
    exact SmoothCutoff.tsupport_centeredBump 0 (1 / 3) (1 / 2) hInner hOuter
  have hHalfLtOne : (1 / 2 : ℝ) < 1 := by
    norm_num
  have hχSupport : tsupport χ ⊆ Metric.ball 0 1 := by
    rw [hχTsupport]
    exact Metric.closedBall_subset_ball hHalfLtOne
  have hχZero : χ 0 = 1 := by
    apply SmoothCutoff.centeredBump_eq_one_of_mem_closedBall
    simp only [Metric.mem_closedBall, dist_self]
    norm_num
  let jetBoundExists : ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
        (a z : EuclideanSpace ℝ (Fin n)), 0 < ρ →
          ‖iteratedFDeriv ℝ m (AffineBump.scaledLinearBump χ x ρ a) z‖ ≤
            K * ‖a‖ * ρ * (ρ⁻¹) ^ m := fun m ↦
    exists_scaledLinearBump_iteratedFDeriv_bound χ hχSmooth hχCompact hχSupport m
  let jetBound : ℕ → ℝ := fun m ↦ Classical.choose (jetBoundExists m)
  have hJetBoundNonneg (m : ℕ) : 0 ≤ jetBound m :=
    (Classical.choose_spec (jetBoundExists m)).1
  have hJetBound (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
      (a z : EuclideanSpace ℝ (Fin n)) (hρ : 0 < ρ) :
      ‖iteratedFDeriv ℝ m (AffineBump.scaledLinearBump χ x ρ a) z‖ ≤
        jetBound m * ‖a‖ * ρ * (ρ⁻¹) ^ m :=
    (Classical.choose_spec (jetBoundExists m)).2 x ρ a z hρ
  let C : ℝ := 4 * (jetBound 2 + 1)
  have hFourPos : (0 : ℝ) < 4 := by
    norm_num
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos hFourPos (add_pos_of_nonneg_of_pos (hJetBoundNonneg 2) zero_lt_one)
  refine ⟨C, hC, ?_⟩
  intro ι σ hσ g δ a b h
  -- Embed the alternating sequence and attach one quarter-scale bump to each center.
  let r : ℕ → ℝ := fun k ↦ ‖g k‖
  let x : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ ι (g k)
  let ρ : ℕ → ℝ := fun k ↦ r k / 4
  let d : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦
    ι (perturbation EuclideanPlane.orientation (g k) (δ k))
  let ψ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k ↦
    AffineBump.scaledLinearBump χ (x k) (ρ k) (d k)
  let correction : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦ ∑' k, ψ k z
  let H : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦
    (1 / 2 : ℝ) * ‖z‖ ^ 2 + correction z
  have hrPos (k : ℕ) : 0 < r k := by
    exact norm_pos_iff.mpr (h.nonzero k)
  have hρPos (k : ℕ) : 0 < ρ k := by
    dsimp only [ρ]
    exact div_pos (hrPos k) hFourPos
  have hxNorm (k : ℕ) : ‖x k‖ = r k := by
    exact ι.norm_map (g k)
  have hxNonzero (k : ℕ) : x k ≠ 0 := by
    intro hk
    apply h.nonzero k
    have hmap : ι (g k) = ι 0 := by
      simpa only [x, map_zero] using hk
    exact ι.injective hmap
  have hxAnti : StrictAnti (fun k ↦ ‖x k‖) := by
    simpa only [hxNorm] using h.radiusStrictAnti
  have hrRatio (k : ℕ) : r (k + 1) / r k ≤ (1 : ℝ) / 4 := by
    exact h.ratioLeQuarter k
  have hxRatio (k : ℕ) : ‖x (k + 1)‖ / ‖x k‖ ≤ (1 : ℝ) / 4 := by
    simpa only [hxNorm, r] using h.ratioLeQuarter k
  have hBalls : Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.closedBall (x k) (ρ k)) := by
    simpa only [ρ, hxNorm, r] using
      quarterNormBallsPairwiseDisjoint x hxNonzero hxAnti hxRatio
  have hψSupport (k : ℕ) : tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k) := by
    exact AffineBump.tsupport_scaledLinearBump_subset_closedBall
      χ hχSupport (x k) (ρ k) (d k) (hρPos k)
  have hψPairwise : Set.univ.PairwiseDisjoint (fun k ↦ tsupport (ψ k)) :=
    hBalls.mono hψSupport
  have hψSmooth (k : ℕ) : ContDiff ℝ ∞ (ψ k) := by
    exact AffineBump.contDiff_scaledLinearBump χ hχSmooth (x k) (ρ k) (d k)
  have hdNorm (k : ℕ) : ‖d k‖ = |δ k| := by
    dsimp only [d]
    rw [ι.norm_map]
    exact norm_perturbation EuclideanPlane.orientation (δ k) (h.nonzero k)
  have hFlatRadius (q : ℕ) :
      (fun k ↦ |δ k|) =o[atTop] (fun k ↦ r k ^ q) := by
    simpa only [r] using h.flat q
  have hWeightSummable (m : ℕ) :
      Summable (fun k ↦ jetBound m * |δ k| * (r k / 4) *
        ((r k / 4)⁻¹) ^ m) := by
    exact summableScaledWeightsOfFlatGeometricDecay r δ hrPos hrRatio
      hFlatRadius (jetBound m) m
  have hψBound (m k : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
      ‖iteratedFDeriv ℝ m (ψ k) z‖ ≤
        jetBound m * |δ k| * (r k / 4) * ((r k / 4)⁻¹) ^ m := by
    simpa only [ψ, ρ, hdNorm] using
      hJetBound m (x k) (ρ k) (d k) z (hρPos k)
  -- Summable bounds at every derivative order justify differentiating the series.
  have hCorrectionSmooth : ContDiff ℝ ∞ correction := by
    exact contDiff_tsum hψSmooth (fun m _ ↦ hWeightSummable m)
      (fun m k z _ ↦ hψBound m k z)
  have hTsumEqFinsum : correction = fun z ↦ ∑ᶠ k, ψ k z := by
    funext z
    dsimp only [correction]
    exact tsum_eq_finsum
      (DisjointFinsum.support_apply_subsingleton_of_pairwiseDisjoint_tsupport
        ψ hψPairwise z).finite
  have hGlobalBall (k : ℕ) : Metric.closedBall (x k) (ρ k) ⊆
      Metric.closedBall 0 (5 * ‖g 0‖ / 4) := by
    intro z hz
    have hzDist : ‖z - x k‖ ≤ ρ k := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hrLe : r k ≤ r 0 := h.radiusStrictAnti.antitone (Nat.zero_le k)
    have hzNorm : ‖z‖ ≤ 5 * r 0 / 4 := by
      calc
        ‖z‖ = ‖(z - x k) + x k‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - x k‖ + ‖x k‖ := norm_add_le _ _
        _ ≤ ρ k + r k := add_le_add hzDist (le_of_eq (hxNorm k))
        _ ≤ r k / 4 + r k := by rfl
        _ ≤ 5 * r 0 / 4 := by
          linarith
    simpa only [Metric.mem_closedBall, dist_zero_right] using hzNorm
  have hCorrectionSupport : tsupport correction ⊆
      Metric.closedBall 0 (5 * ‖g 0‖ / 4) := by
    apply closure_minimal
    · intro z hz
      have hactive : ∃ k, ψ k z ≠ 0 := by
        by_contra hnone
        have hnone' : ∀ k, ψ k z = 0 := by
          simpa only [not_exists, not_not] using hnone
        apply hz
        dsimp only [correction]
        exact DisjointFinsum.tsum_eq_zero_of_forall_eq_zero _ hnone'
      obtain ⟨k, hk⟩ := hactive
      exact hGlobalBall k (hψSupport k (subset_tsupport (ψ k) hk))
    · exact Metric.isClosed_closedBall
  have hCorrectionCompact : HasCompactSupport correction := by
    apply HasCompactSupport.intro (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin n)) (5 * ‖g 0‖ / 4))
    intro z hz
    have hzOutside : z ∉ tsupport correction := by
      intro hzSupport
      exact hz (hCorrectionSupport hzSupport)
    exact image_eq_zero_of_notMem_tsupport hzOutside
  -- Pairwise disjointness makes the correction gradient select exactly one bump.
  have hGradientCorrection (k : ℕ) : gradient correction (x k) = d k := by
    rw [hTsumEqFinsum]
    exact AffineBump.gradient_finsum_scaledLinearBump_center
      χ hχSmooth hχZero hχSupport x ρ d hρPos hBalls k
  have hZeroOutside (k : ℕ) : 0 ∉ tsupport (ψ k) := by
    intro hk
    have hkBall := hψSupport k hk
    have hkNorm : ‖x k‖ ≤ ρ k := by
      simpa only [Metric.mem_closedBall, dist_zero_left] using hkBall
    rw [hxNorm] at hkNorm
    dsimp only [ρ] at hkNorm
    nlinarith [hrPos k]
  have hOrderLeTop (m : ℕ) : (m : ℕ∞) ≤ ⊤ := le_top
  have hCorrectionJetZero (m : ℕ) :
      iteratedFDeriv ℝ m correction 0 = 0 := by
    calc
      iteratedFDeriv ℝ m correction 0 =
          ∑' k, iteratedFDeriv ℝ m (ψ k) 0 := by
        exact iteratedFDeriv_tsum_apply hψSmooth
          (fun q _ ↦ hWeightSummable q) (fun q k z _ ↦ hψBound q k z)
          (hOrderLeTop m) 0
      _ = ∑' _k : ℕ, 0 := by
        apply tsum_congr
        intro k
        exact iteratedFDeriv_eq_zero_of_notMem_tsupport (ψ k) m (hZeroOutside k)
      _ = 0 := tsum_zero
  have hCorrectionGradientZero : gradient correction 0 = 0 := by
    unfold gradient
    have hnorm : ‖fderiv ℝ correction 0‖ = 0 := by
      rw [← norm_iteratedFDeriv_one correction, hCorrectionJetZero 1, norm_zero]
    rw [norm_eq_zero.mp hnorm, map_zero]
  have hQuadraticSmooth : ContDiff ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) ↦ (1 / 2 : ℝ) * ‖z‖ ^ 2) := by
    simpa only [id_eq, smul_eq_mul] using
      ((contDiff_id.norm_sq ℝ).const_smul (1 / 2 : ℝ))
  have hHSmooth : ContDiff ℝ ∞ H := hQuadraticSmooth.add hCorrectionSmooth
  have hSmoothOrderNonzero : (∞ : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hCorrectionDifferentiable : Differentiable ℝ correction := by
    exact hCorrectionSmooth.differentiable hSmoothOrderNonzero
  have hTail : H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) =
      correction := by
    funext z
    simp only [Pi.sub_apply, H, standardQuadratic_apply, add_sub_cancel_left]
  have hWBounded : BddAbove (Set.range (fun k : ℕ ↦ |δ k| / ‖g k‖)) := by
    refine ⟨σ, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact h.perturbationRatioLe k
  let W := sSup (Set.range (fun k : ℕ ↦ |δ k| / ‖g k‖))
  have hRatioLeW (k : ℕ) : |δ k| / ‖g k‖ ≤ W := by
    exact le_csSup hWBounded (Set.mem_range_self k)
  have hWNonneg : 0 ≤ W := by
    have hratioNonneg : 0 ≤ |δ 0| / ‖g 0‖ :=
      div_nonneg (abs_nonneg _) (norm_nonneg _)
    exact hratioNonneg.trans (hRatioLeW 0)
  -- Normalize the second-derivative scale and dominate it by the global ratio supremum.
  have hPointwiseSecondBound (k : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
      ‖iteratedFDeriv ℝ 2 (ψ k) z‖ ≤ C * W := by
    have hraw := hψBound 2 k z
    have hrk : r k ≠ 0 := (hrPos k).ne'
    have hnormalize : jetBound 2 * |δ k| * (r k / 4) * ((r k / 4)⁻¹) ^ 2 =
        (4 * jetBound 2) * (|δ k| / r k) := by
      field_simp [hrk]
    rw [hnormalize] at hraw
    have hcoefficient : 0 ≤ 4 * jetBound 2 :=
      mul_nonneg hFourPos.le (hJetBoundNonneg 2)
    have hcoefficientLe : 4 * jetBound 2 ≤ C := by
      dsimp only [C]
      linarith
    have hratioNonneg : 0 ≤ |δ k| / r k :=
      div_nonneg (abs_nonneg _) (hrPos k).le
    have hratioLe : |δ k| / r k ≤ W := by
      simpa only [r, W] using hRatioLeW k
    calc
      ‖iteratedFDeriv ℝ 2 (ψ k) z‖ ≤
          (4 * jetBound 2) * (|δ k| / r k) := hraw
      _ ≤ C * W := by
        exact mul_le_mul hcoefficientLe hratioLe hratioNonneg hC.le
  have hCorrectionSecondBound (z : EuclideanSpace ℝ (Fin n)) :
      ‖iteratedFDeriv ℝ 2 correction z‖ ≤ C * W := by
    have hseries : iteratedFDeriv ℝ 2 correction z =
        ∑' k, iteratedFDeriv ℝ 2 (ψ k) z := by
      exact iteratedFDeriv_tsum_apply hψSmooth
        (fun q _ ↦ hWeightSummable q) (fun q k y _ ↦ hψBound q k y)
        (hOrderLeTop 2) z
    have hDerivativePairwise : Set.univ.PairwiseDisjoint
        (fun k ↦ tsupport (iteratedFDeriv ℝ 2 (ψ k))) :=
      hψPairwise.mono (fun k ↦ tsupport_iteratedFDeriv_subset 2)
    have hActiveDerivative :
        (Function.support (fun k ↦ iteratedFDeriv ℝ 2 (ψ k) z)).Subsingleton :=
      DisjointFinsum.support_apply_subsingleton_of_pairwiseDisjoint_tsupport
        (fun k ↦ iteratedFDeriv ℝ 2 (ψ k)) hDerivativePairwise z
    rw [hseries]
    by_cases hactive : ∃ k, iteratedFDeriv ℝ 2 (ψ k) z ≠ 0
    · obtain ⟨k, hk⟩ := hactive
      rw [DisjointFinsum.tsum_eq_single_of_support_subsingleton _ k hk hActiveDerivative]
      exact hPointwiseSecondBound k z
    · have hactive' : ∀ k, iteratedFDeriv ℝ 2 (ψ k) z = 0 := by
        simpa only [not_exists, not_not] using hactive
      rw [DisjointFinsum.tsum_eq_zero_of_forall_eq_zero _ hactive', norm_zero]
      exact mul_nonneg hC.le hWNonneg
  have hTwoNat : (2 : ℕ∞) ≤ ⊤ := le_top
  have hTwoLeTop : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr hTwoNat
  have hCorrectionTwice : ContDiff ℝ 2 correction := by
    exact hCorrectionSmooth.of_le hTwoLeTop
  -- Add the quadratic back and discharge each advertised interpolation property.
  refine ⟨H, hHSmooth, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTail]
    exact hCorrectionSmooth
  · rw [hTail]
    exact hCorrectionCompact
  · rw [hTail]
    exact hCorrectionSupport
  · intro k
    have hformula := HessianPerturbation.gradient_halfNormSq_sub_add
      0 correction (x k) hCorrectionDifferentiable.differentiableAt
    calc
      gradient H (ι (g k)) = x k + gradient correction (x k) := by
        simpa only [H, x, sub_zero] using hformula
      _ = x k + d k := by rw [hGradientCorrection k]
      _ = ι (candidate EuclideanPlane.orientation (g k) (δ k)) := by
        simp only [x, d, candidate_apply, map_add]
  · have hformula := HessianPerturbation.gradient_halfNormSq_sub_add
      0 correction 0 hCorrectionDifferentiable.differentiableAt
    simpa only [H, sub_zero, zero_add, hCorrectionGradientZero] using hformula
  · apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [convexHessianQuadraticPerturbationNorm correction
      hCorrectionTwice 0,
      hCorrectionJetZero 2, norm_zero]
  · intro z
    rw [convexHessianQuadraticPerturbationNorm correction
      hCorrectionTwice z]
    simpa only [C, W] using hCorrectionSecondBound z

end PlanarGradient
