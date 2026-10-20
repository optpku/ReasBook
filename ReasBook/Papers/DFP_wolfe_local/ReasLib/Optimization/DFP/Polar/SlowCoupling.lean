module

public import ReasLib.Optimization.DFP.Polar.FastRemainder
public import ReasLib.Optimization.DFP.Polar.TubeBounds
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder

/-!
# Cubic slow coupling for the actual polar map

The source's leading map preserves the first diagonal coordinate for every
fast input. Taylor expansion in scale, together with state control of the
third scale derivative, gives the product `|t| ^ 3 * fixedNorm u`.
-/

public section

noncomputable section

open Filter
open scoped Topology ContDiff

namespace DFP.Polar.SlowCoupling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): joint fourth
regularity on a compact zero-scale fiber gives a common scale tube with a
uniform fourth derivative bound. -/
theorem compactFourthDerivativeBound (f : ℝ × E → ℝ) (𝒦 : Set E)
    (h𝒦 : IsCompact 𝒦) (hf : ∀ x ∈ 𝒦, ContDiffAt ℝ 4 f (0, x)) :
    ∃ B > 0, ∃ δ > 0, ∀ x ∈ 𝒦, ∀ t : ℝ, ‖t‖ < δ →
      ContDiffAt ℝ 4 f (t, x) ∧ ‖iteratedFDeriv ℝ 4 f (t, x)‖ ≤ B := by
  have hbase : ContinuousOn (fun x ↦ iteratedFDeriv ℝ 4 f (0, x)) 𝒦 := by
    intro x hx
    have hcontinuous := (hf x hx).continuousAt_iteratedFDeriv le_rfl
    have hinput : ContinuousAt (fun y : E ↦ ((0 : ℝ), y)) x :=
      continuousAt_const.prodMk continuousAt_id
    exact (hcontinuous.comp_of_eq hinput rfl).continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := h𝒦.exists_bound_of_continuousOn hbase
  have hB : 0 < |B₀| + 1 := by positivity
  have hfinite : (4 : ℕ∞ω) ≠ ∞ := by simp
  have hlocal : ∀ x ∈ 𝒦, ∀ᶠ p : ℝ × E in 𝓝 (0, x),
      ContDiffAt ℝ 4 f p ∧ ‖iteratedFDeriv ℝ 4 f p‖ ≤ |B₀| + 1 := by
    intro x hx
    have hbound : ‖iteratedFDeriv ℝ 4 f (0, x)‖ < |B₀| + 1 := by
      linarith [hB₀ x hx, le_abs_self B₀]
    have hnorm := ((hf x hx).continuousAt_iteratedFDeriv le_rfl).norm
    filter_upwards [(hf x hx).eventually hfinite,
      hnorm.eventually (Iio_mem_nhds hbound)] with p hp hpnorm
    exact ⟨hp, hpnorm.le⟩
  obtain ⟨δ, hδ, hbound⟩ := FiniteTaylorJet.compactFiberNormRadius (X := ℝ)
    (P := fun t x ↦ ContDiffAt ℝ 4 f (t, x) ∧
      ‖iteratedFDeriv ℝ 4 f (t, x)‖ ≤ |B₀| + 1) h𝒦 hlocal
  exact ⟨|B₀| + 1, hB, δ, hδ, hbound⟩

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): restricting a
joint iterated derivative to the state variable differentiates through the
canonical state inclusion. -/
theorem stateIteratedDerivative_hasFDerivAt (n : ℕ) (f : ℝ × E → ℝ) (t : ℝ) (x : E)
    (hf : ContDiffAt ℝ (n + 1) f (t, x)) :
    HasFDerivAt (fun y ↦ iteratedFDeriv ℝ n f (t, y))
      ((fderiv ℝ (iteratedFDeriv ℝ n f) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  have hdegree : (n : ℕ∞ω) < (n + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self n
  have hd := hf.differentiableAt_iteratedFDeriv hdegree
  simpa only [Function.comp_def] using
    hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the state
derivative of a joint iterated derivative is bounded by the next joint
derivative norm. -/
theorem norm_stateIteratedDerivative_le (n : ℕ) (f : ℝ × E → ℝ) (t : ℝ) (x : E)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ‖iteratedFDeriv ℝ (n + 1) f (t, x)‖ ≤ B) :
    ‖(fderiv ℝ (iteratedFDeriv ℝ n f) (t, x)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  calc
    ‖(fderiv ℝ (iteratedFDeriv ℝ n f) (t, x)) (0, v)‖ ≤
        ‖fderiv ℝ (iteratedFDeriv ℝ n f) (t, x)‖ * ‖((0, v) : ℝ × E)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ B * ‖v‖ := by
      rw [norm_fderiv_iteratedFDeriv, Prod.norm_mk, norm_zero,
        max_eq_right (norm_nonneg v)]
      exact mul_le_mul_of_nonneg_right hbound (norm_nonneg v)

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): a fourth
derivative bound controls state variation of the third joint derivative on
a fixed convex state set. -/
theorem thirdJointDerivative_state_lipschitz (f : ℝ × E → ℝ) (𝒦 : Set E)
    (h𝒦 : Convex ℝ 𝒦) (t B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ x ∈ 𝒦, ContDiffAt ℝ 4 f (t, x))
    (hbound : ∀ x ∈ 𝒦, ‖iteratedFDeriv ℝ 4 f (t, x)‖ ≤ B)
    (x y : E) (hx : x ∈ 𝒦) (hy : y ∈ 𝒦) :
    ‖iteratedFDeriv ℝ 3 f (t, y) - iteratedFDeriv ℝ 3 f (t, x)‖ ≤ B * ‖y - x‖ := by
  have hd : ∀ z ∈ 𝒦,
      HasFDerivWithinAt (fun w ↦ iteratedFDeriv ℝ 3 f (t, w))
        ((fderiv ℝ (iteratedFDeriv ℝ 3 f) (t, z)).comp
          (ContinuousLinearMap.inr ℝ ℝ E)) 𝒦 z := by
    intro z hz
    exact (stateIteratedDerivative_hasFDerivAt 3 f t z (hf z hz)).hasFDerivWithinAt
  have hnorm : ∀ z ∈ 𝒦,
      ‖(fderiv ℝ (iteratedFDeriv ℝ 3 f) (t, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ E)‖ ≤ B := by
    intro z hz
    exact norm_stateIteratedDerivative_le 3 f t z B hB (hbound z hz)
  exact h𝒦.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hnorm hx hy

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): rescaling the
scalar argument multiplies its zero-based scale jet by the corresponding
power of the rescaling. -/
theorem iteratedDeriv_rescale_zero (n : ℕ) (f : ℝ → ℝ) (c : ℝ)
    (hf : ContDiffAt ℝ n f 0) :
    iteratedDeriv n (fun s : ℝ ↦ f (s * c)) 0 = c ^ n * iteratedDeriv n f 0 := by
  have hreg : ContDiffAt ℝ n f ((0 : ℝ) + (0 : ℝ) • c) := by simpa using hf
  have h := FiniteTaylorJet.iteratedDeriv_comp_add_smul (x := (0 : ℝ))
    (h := c) (t := (0 : ℝ)) hreg
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h
  simpa only [zero_smul, add_zero, zero_add, zero_mul, smul_eq_mul, Finset.prod_const,
    Finset.card_fin] using h

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the difference
of joint scale-line derivatives is bounded by the corresponding joint
derivative difference times the scale direction's norm. -/
theorem norm_iteratedDeriv_scaleDifference_le (n : ℕ) (f : ℝ × E → ℝ)
    (t s B : ℝ) (x y : E)
    (hx : ContDiffAt ℝ n f (s * t, x)) (hy : ContDiffAt ℝ n f (s * t, y))
    (hbound : ‖iteratedFDeriv ℝ n f (s * t, y) -
      iteratedFDeriv ℝ n f (s * t, x)‖ ≤ B) :
    ‖iteratedDeriv n (fun v : ℝ ↦ f (v * t, y) - f (v * t, x)) s‖ ≤ B * ‖t‖ ^ n := by
  have hinputx : ContDiffAt ℝ n (fun v : ℝ ↦ (v * t, x)) s := by fun_prop
  have hinputy : ContDiffAt ℝ n (fun v : ℝ ↦ (v * t, y)) s := by fun_prop
  have hpathx : ContDiffAt ℝ n (fun v : ℝ ↦ f (v * t, x)) s := hx.comp s hinputx
  have hpathy : ContDiffAt ℝ n (fun v : ℝ ↦ f (v * t, y)) s := hy.comp s hinputy
  have hx' : ContDiffAt ℝ n f (((0 : ℝ), x) + s • ((t, 0) : ℝ × E)) := by
    simpa only [Prod.smul_mk, smul_zero, smul_eq_mul, Prod.mk_add_mk,
      zero_add, add_zero] using hx
  have hy' : ContDiffAt ℝ n f (((0 : ℝ), y) + s • ((t, 0) : ℝ × E)) := by
    simpa only [Prod.smul_mk, smul_zero, smul_eq_mul, Prod.mk_add_mk,
      zero_add, add_zero] using hy
  have hdx := FiniteTaylorJet.iteratedDeriv_comp_add_smul
    (x := ((0 : ℝ), x)) (h := ((t, 0) : ℝ × E)) (t := s) hx'
  have hdy := FiniteTaylorJet.iteratedDeriv_comp_add_smul
    (x := ((0 : ℝ), y)) (h := ((t, 0) : ℝ × E)) (t := s) hy'
  simp only [Prod.smul_mk, smul_zero, smul_eq_mul, Prod.mk_add_mk,
    zero_add, add_zero] at hdx hdy
  rw [iteratedDeriv_fun_sub hpathy hpathx, hdy, hdx, ← sub_apply]
  calc
    ‖(iteratedFDeriv ℝ n f (s * t, y) - iteratedFDeriv ℝ n f (s * t, x))
        (fun _ ↦ (t, 0))‖ ≤
      ‖iteratedFDeriv ℝ n f (s * t, y) - iteratedFDeriv ℝ n f (s * t, x)‖ *
        ∏ _ : Fin n, ‖((t, 0) : ℝ × E)‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ B * ∏ _ : Fin n, ‖((t, 0) : ℝ × E)‖ :=
      mul_le_mul_of_nonneg_right hbound (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    _ = B * ‖t‖ ^ n := by
      simp only [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg t),
        Finset.prod_const, Finset.card_fin]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): cancellation of
the first two scale coefficients gives a uniform cubic Lipschitz bound for
scale increments on a fixed compact convex state set. -/
theorem uniformCubicStateDifference (f : ℝ × E → ℝ) (𝒦 : Set E)
    (hcompact : IsCompact 𝒦) (hconvex : Convex ℝ 𝒦)
    (hf : ∀ x ∈ 𝒦, ContDiffAt ℝ 4 f (0, x))
    (hzero : ∀ x ∈ 𝒦, ∀ n : Fin 3, (n : ℕ) ≠ 0 →
      iteratedDeriv (n : ℕ) (fun t : ℝ ↦ f (t, x)) 0 = 0) :
    ∃ C > 0, ∃ δ > 0, ∀ x ∈ 𝒦, ∀ y ∈ 𝒦, ∀ t : ℝ, ‖t‖ < δ →
      ‖(f (t, y) - f (0, y)) - (f (t, x) - f (0, x))‖ ≤
        C * ‖t‖ ^ 3 * ‖y - x‖ := by
  obtain ⟨B, hB, δ, hδ, hbound⟩ := compactFourthDerivativeBound f 𝒦 hcompact hf
  refine ⟨B, hB, δ, hδ, ?_⟩
  intro x hx y hy t ht
  let g : ℝ → ℝ := fun s ↦ f (s * t, y) - f (s * t, x)
  have hdegree : (3 : ℕ∞ω) ≤ 4 := by norm_num
  have hscale : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖s * t‖ < δ := by
    intro s hs
    have hsNorm : ‖s‖ = s := by rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    rw [norm_mul, hsNorm]
    exact (mul_le_of_le_one_left (norm_nonneg t) hs.2).trans_lt ht
  have hpath : ∀ z ∈ 𝒦, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ContDiffAt ℝ 3 (fun v : ℝ ↦ f (v * t, z)) s := by
    intro z hz s hs
    have hreg := ((hbound z hz (s * t) (hscale s hs)).1).of_le hdegree
    have hinput : ContDiffAt ℝ 3 (fun v : ℝ ↦ (v * t, z)) s := by fun_prop
    exact hreg.comp s hinput
  have hg : ∀ s ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 g s := by
    intro s hs
    exact (hpath y hy s hs).sub (hpath x hx s hs)
  have hzeroInterval : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hslice : ∀ z ∈ 𝒦, ContDiffAt ℝ 3 (fun v : ℝ ↦ f (v, z)) 0 := by
    intro z hz
    have hinput : ContDiffAt ℝ 3 (fun v : ℝ ↦ (v, z)) 0 := by fun_prop
    exact ((hf z hz).of_le hdegree).comp 0 hinput
  have hzeroG : ∀ n : Fin 3, (n : ℕ) ≠ 0 → iteratedDeriv (n : ℕ) g 0 = 0 := by
    intro n hn
    have hnNat : (n : ℕ) ≤ 3 := by omega
    have hnDegree : ((n : ℕ) : ℕ∞ω) ≤ 3 := by exact_mod_cast hnNat
    dsimp only [g]
    rw [iteratedDeriv_fun_sub ((hpath y hy 0 hzeroInterval).of_le hnDegree)
      ((hpath x hx 0 hzeroInterval).of_le hnDegree)]
    rw [iteratedDeriv_rescale_zero (n : ℕ) (fun v ↦ f (v, y)) t
      ((hslice y hy).of_le hnDegree),
      iteratedDeriv_rescale_zero (n : ℕ) (fun v ↦ f (v, x)) t
      ((hslice x hx).of_le hnDegree), hzero y hy n hn, hzero x hx n hn]
    ring
  have hthird : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedDeriv 3 g s‖ ≤ B * ‖y - x‖ * ‖t‖ ^ 3 := by
    intro s hs
    have hreg : ∀ z ∈ 𝒦, ContDiffAt ℝ 4 f (s * t, z) := by
      intro z hz
      exact (hbound z hz (s * t) (hscale s hs)).1
    have htop : ∀ z ∈ 𝒦, ‖iteratedFDeriv ℝ 4 f (s * t, z)‖ ≤ B := by
      intro z hz
      exact (hbound z hz (s * t) (hscale s hs)).2
    have hvariation := thirdJointDerivative_state_lipschitz f 𝒦 hconvex
      (s * t) B hB.le hreg htop x y hx hy
    exact norm_iteratedDeriv_scaleDifference_le 3 f t s (B * ‖y - x‖) x y
      ((hreg x hx).of_le hdegree) ((hreg y hy).of_le hdegree) hvariation
  have hgOn : ContDiffOn ℝ 3 g (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    exact (hg s hs).contDiffWithinAt
  have hthirdWithin : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 3 g (Set.Icc (0 : ℝ) 1) s‖ ≤
        B * ‖y - x‖ * ‖t‖ ^ 3 := by
    intro s hs
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) (hg s hs) hs]
    exact hthird s hs
  have htaylor := taylor_mean_remainder_bound (f := g) (n := 2)
    (a := 0) (b := 1) (x := 1) zero_le_one hgOn
    (Set.right_mem_Icc.mpr zero_le_one) hthirdWithin
  have hTaylorValue : taylorWithinEval g 2 (Set.Icc (0 : ℝ) 1) 0 1 = g 0 := by
    rw [taylor_within_apply]
    have hterms : ∀ k ∈ Finset.range 3, k ≠ 0 →
        iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      intro k hk hkzero
      have hklt : k < 3 := Finset.mem_range.mp hk
      have hkDegree : (k : ℕ∞ω) ≤ 3 := by exact_mod_cast Nat.le_of_lt hklt
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
        ((hg 0 hzeroInterval).of_le hkDegree) hzeroInterval]
      exact hzeroG ⟨k, hklt⟩ hkzero
    rw [Finset.sum_eq_single 0]
    · simp only [pow_zero, sub_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
        one_mul, one_smul, iteratedDerivWithin_zero]
    · intro k hk hkzero
      rw [hterms k hk hkzero]
      exact smul_zero _
    · intro hnot
      have hmem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
      exact (hnot hmem).elim
  rw [hTaylorValue] at htaylor
  have hnonnegative : 0 ≤ B * ‖y - x‖ * ‖t‖ ^ 3 := by positivity
  have hTaylorBound : ‖g 1 - g 0‖ ≤ B * ‖t‖ ^ 3 * ‖y - x‖ := by
    norm_num only [sub_zero, one_pow, mul_one, Nat.factorial_succ,
      Nat.factorial_zero, Nat.reduceMul, Nat.cast_ofNat] at htaylor
    nlinarith
  have hidentity :
      g 1 - g 0 = (f (t, y) - f (0, y)) - (f (t, x) - f (0, x)) := by
    dsimp only [g]
    rw [one_mul, zero_mul]
    ring
  rwa [hidentity] at hTaylorBound

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the first
coordinate of the actual normalized map as a joint function of scale and state. -/
def slowMap (L κ : ℝ) (p : ℝ × (ℝ × ℝ × ℝ)) : ℝ :=
  (Normalized.map L κ p.1 p.2).1

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the actual map's
first-coordinate formula in the scale-state product. -/
theorem slowMap_apply (L κ t : ℝ) (x : ℝ × ℝ × ℝ) :
    slowMap L κ (t, x) = (Normalized.map L κ t x).1 := by
  rfl

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the actual slow
map is jointly analytic at every zero-scale regular positive state. -/
theorem slowMap_analyticAt_zero (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hA : 0 < x.1) (hC : 0 < x.2.1)
    (hCNext : 0 < (Normalized.leadingStage (Normalized.limitAngle 0) x).2.1) :
    AnalyticAt ℝ (slowMap L κ) (0, x) := by
  have hmap := Normalized.map_analyticAt_zero L κ x hA hC hCNext
  have hfirst := analyticAt_fst.comp hmap
  have hfun :
      (fun p : ℝ × (ℝ × ℝ × ℝ) ↦
        (Function.uncurry (Normalized.map L κ) p).1) = slowMap L κ := by
    funext p
    rfl
  simpa only [Function.comp_def, hfun] using hfirst

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the first two
positive scale coefficients of the actual slow map vanish for every regular
fast input, as inherited from the full normalized map. -/
theorem slowMap_positiveIteratedDeriv_eq_zero (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hA : 0 < x.1) (hC : 0 < x.2.1)
    (hCNext : 0 < (Normalized.leadingStage (Normalized.limitAngle 0) x).2.1)
    (n : Fin 3) (hn : (n : ℕ) ≠ 0) :
    iteratedDeriv (n : ℕ) (fun t : ℝ ↦ slowMap L κ (t, x)) 0 = 0 := by
  let P : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  have hf : ContDiffAt ℝ (n : ℕ) (fun t : ℝ ↦ Normalized.map L κ t x) 0 :=
    (FastRemainder.map_scale_analyticAt L κ x hA hC hCNext).contDiffAt
  have hcomp := P.iteratedFDeriv_comp_left (i := (n : ℕ)) hf le_rfl
  have hzero := FastRemainder.map_positiveIteratedFDeriv_eq_zero L κ x hA hC hCNext n hn
  have hfun : (fun t : ℝ ↦ slowMap L κ (t, x)) =
      P ∘ (fun t : ℝ ↦ Normalized.map L κ t x) := by
    funext t
    rw [slowMap_apply]
    rfl
  rw [hfun, iteratedDeriv_eq_iteratedFDeriv, hcomp, hzero]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, zero_apply, map_zero]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): on a compact
convex regular state set, the actual slow increments have a uniform cubic
state Lipschitz bound. -/
theorem map_slowIncrement_uniformCubicStateDifference (L κ : ℝ)
    (𝒦 : Set (ℝ × ℝ × ℝ)) (hcompact : IsCompact 𝒦) (hconvex : Convex ℝ 𝒦)
    (hA : ∀ x ∈ 𝒦, 0 < x.1) (hC : ∀ x ∈ 𝒦, 0 < x.2.1)
    (hCNext : ∀ x ∈ 𝒦, 0 < (Normalized.leadingStage (Normalized.limitAngle 0) x).2.1) :
    ∃ C > 0, ∃ δ > 0, ∀ x ∈ 𝒦, ∀ y ∈ 𝒦, ∀ t : ℝ, |t| < δ →
      |((Normalized.map L κ t y).1 - y.1) -
        ((Normalized.map L κ t x).1 - x.1)| ≤ C * |t| ^ 3 * ‖y - x‖ := by
  have hf : ∀ x ∈ 𝒦, ContDiffAt ℝ 4 (slowMap L κ) (0, x) := by
    intro x hx
    exact (slowMap_analyticAt_zero L κ x (hA x hx) (hC x hx) (hCNext x hx)).contDiffAt
  have hzero : ∀ x ∈ 𝒦, ∀ n : Fin 3, (n : ℕ) ≠ 0 →
      iteratedDeriv (n : ℕ) (fun t : ℝ ↦ slowMap L κ (t, x)) 0 = 0 := by
    intro x hx n hn
    exact slowMap_positiveIteratedDeriv_eq_zero L κ x (hA x hx) (hC x hx) (hCNext x hx) n hn
  obtain ⟨C, hCpositive, δ, hδ, hbound⟩ := uniformCubicStateDifference
    (slowMap L κ) 𝒦 hcompact hconvex hf hzero
  refine ⟨C, hCpositive, δ, hδ, ?_⟩
  intro x hx y hy t ht
  have hsmall : ‖t‖ < δ := by simpa only [Real.norm_eq_abs] using ht
  simpa only [slowMap_apply, FastContraction.map_zero_fst, Real.norm_eq_abs] using
    hbound x hx y hy t hsmall

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): perturbing only
the fast coordinates preserves the input first diagonal coordinate. -/
theorem perturbedState_fst (A : ℝ) (u : Fin 2 → ℝ) :
    (FastRemainder.perturbedState A u).1 = A := by
  rw [FastRemainder.perturbedState_apply]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the difference
from the actual even curve has exactly the two prescribed fast coordinates. -/
theorem perturbedState_sub_evenState (A : ℝ) (u : Fin 2 → ℝ) :
    FastRemainder.perturbedState A u - TwoCycle.evenState A =
      ((0, u 0, u 1) : ℝ × ℝ × ℝ) := by
  rw [FastRemainder.perturbedState_apply]
  apply Prod.ext
  · simp only [Prod.fst_sub, TwoCycle.evenState_firstDiagonal, sub_self]
  · apply Prod.ext
    · simp only [Prod.snd_sub, Prod.fst_sub, FastContraction.fastCoordinates_apply,
        Pi.add_apply, Matrix.cons_val_zero, add_sub_cancel_left]
    · simp only [Prod.snd_sub, FastContraction.fastCoordinates_apply,
        Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_sub_cancel_left]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): a positive fixed
basis constant controls the ordinary norm of each fast displacement. -/
private theorem norm_le_positiveBasisBound (u : Fin 2 → ℝ) :
    ‖u‖ ≤ (‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1) *
      FastContraction.fixedNorm u := by
  have hbound := FastContraction.norm_le_basisOperator_mul_fixedNorm u
  nlinarith [FastContraction.fixedNorm_nonneg u]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): displacement
from the source's even curve has ordinary norm controlled by the fixed fast
norm with the original fixed change-of-basis matrix. -/
theorem norm_perturbedState_sub_evenState_le (A : ℝ) (u : Fin 2 → ℝ) :
    ‖FastRemainder.perturbedState A u - TwoCycle.evenState A‖ ≤
      (‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1) *
        FastContraction.fixedNorm u := by
  have hnorm : ‖((0, u 0, u 1) : ℝ × ℝ × ℝ)‖ ≤ ‖u‖ := by
    simp only [Prod.norm_mk, norm_zero]
    exact max_le (norm_nonneg u) (max_le (norm_le_pi_norm u 0) (norm_le_pi_norm u 1))
  rw [perturbedState_sub_evenState]
  exact hnorm.trans (norm_le_positiveBasisBound u)

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): one regular
compact state ball and source slow/fast radii can be fixed before the feedback
parameters `L` and `κ`. -/
theorem existsFixedSourceNeighborhood :
    ∃ r > 0, ∃ d > 0, ∃ R > 0,
      (∀ x ∈ Metric.closedBall TwoCycle.evenReference R,
        0 < x.1 ∧ 0 < x.2.1 ∧
          0 < (Normalized.leadingStage (Normalized.limitAngle 0) x).2.1) ∧
      ∀ A : ℝ, |A - TwoCycle.kZero| < d →
        A ∈ TwoCycle.normalizationSet ∧
        TwoCycle.evenState A ∈ Metric.closedBall TwoCycle.evenReference R ∧
        ∀ u : Fin 2 → ℝ, FastContraction.fixedNorm u < r →
          FastRemainder.perturbedState A u ∈ Metric.closedBall TwoCycle.evenReference R := by
  obtain ⟨R, hR, hregular⟩ := FastRemainder.exists_regular_closedBall
  have hcompact : Metric.closedBall TwoCycle.evenReference R ∈
      𝓝 (FastRemainder.perturbedState TwoCycle.kZero 0) := by
    rw [FastRemainder.perturbedState_zero, TwoCycle.evenState_kZero]
    exact Metric.closedBall_mem_nhds _ hR
  obtain ⟨η, hη, hinput⟩ := Metric.eventually_nhds_iff.mp
    (FastRemainder.continuousAt_perturbedState.eventually hcompact)
  obtain ⟨a, ha, hnormalization⟩ := Metric.mem_nhds_iff.mp TwoCycle.normalizationSet_mem_nhds
  let B := ‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hr : 0 < η / (2 * B) := div_pos hη (mul_pos zero_lt_two hB)
  refine ⟨η / (2 * B), hr, min (η / 2) a, lt_min (half_pos hη) ha, R, hR, hregular, ?_⟩
  intro A hA
  have hslow : |A - TwoCycle.kZero| < η :=
    (hA.trans_le (min_le_left _ _)).trans (half_lt_self hη)
  have hnormal : A ∈ TwoCycle.normalizationSet := by
    apply hnormalization
    rw [Metric.mem_ball, Real.dist_eq]
    exact hA.trans_le (min_le_right _ _)
  have hperturbed : ∀ u : Fin 2 → ℝ, FastContraction.fixedNorm u < η / (2 * B) →
      FastRemainder.perturbedState A u ∈ Metric.closedBall TwoCycle.evenReference R := by
    intro u hu
    have hfast : ‖u‖ < η := by
      calc
        ‖u‖ ≤ B * FastContraction.fixedNorm u :=
          norm_le_positiveBasisBound u
        _ < B * (η / (2 * B)) := mul_lt_mul_of_pos_left hu hB
        _ = η / 2 := by field_simp [hB.ne']
        _ < η := half_lt_self hη
    have hnear : dist (A, u) (TwoCycle.kZero, (0 : Fin 2 → ℝ)) < η := by
      rw [Prod.dist_eq, Real.dist_eq, dist_zero_right]
      exact max_lt hslow hfast
    exact Metric.mem_closedBall.mpr (hinput hnear)
  have hzero : FastContraction.fixedNorm (0 : Fin 2 → ℝ) = 0 :=
    (FastContraction.fixedNorm_eq_zero 0).mpr rfl
  have heven := hperturbed 0
  rw [hzero] at heven
  refine ⟨hnormal, ?_, hperturbed⟩
  simpa only [FastRemainder.perturbedState_zero] using heven hr

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): select fixed
source slow and fast radii before arbitrary feedback parameters. The actual
slow map then satisfies the required uniform cubic off-curve estimate. -/
theorem uniformSlowCouplingFixedNeighborhood :
    ∃ r > 0, ∃ d > 0, ∀ L κ : ℝ, ∃ Ccross > 0, ∃ δ > 0,
      ∀ A : ℝ, |A - TwoCycle.kZero| < d →
        A ∈ TwoCycle.normalizationSet ∧
        ∀ u : Fin 2 → ℝ, FastContraction.fixedNorm u < r →
          ∀ t : ℝ, |t| < δ →
            |(Normalized.map L κ t (FastRemainder.perturbedState A u)).1 -
              (Normalized.map L κ t (TwoCycle.evenState A)).1| ≤
                Ccross * |t| ^ 3 * FastContraction.fixedNorm u := by
  obtain ⟨r, hr, d, hd, R, hR, hregular, hsource⟩ := existsFixedSourceNeighborhood
  let B := ‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨r, hr, d, hd, ?_⟩
  intro L κ
  obtain ⟨C, hC, δ, hδ, hbound⟩ := map_slowIncrement_uniformCubicStateDifference L κ
    (Metric.closedBall TwoCycle.evenReference R) (isCompact_closedBall _ _)
    (convex_closedBall _ _)
    (fun x hx ↦ (hregular x hx).1) (fun x hx ↦ (hregular x hx).2.1)
    (fun x hx ↦ (hregular x hx).2.2)
  refine ⟨C * B, mul_pos hC hB, δ, hδ, ?_⟩
  intro A hA
  have hstates := hsource A hA
  refine ⟨hstates.1, ?_⟩
  intro u hu t ht
  have hraw := hbound (TwoCycle.evenState A) hstates.2.1
    (FastRemainder.perturbedState A u) (hstates.2.2 u hu) t ht
  have hidentity :
      ((Normalized.map L κ t (FastRemainder.perturbedState A u)).1 -
        (FastRemainder.perturbedState A u).1) -
      ((Normalized.map L κ t (TwoCycle.evenState A)).1 - (TwoCycle.evenState A).1) =
      (Normalized.map L κ t (FastRemainder.perturbedState A u)).1 -
        (Normalized.map L κ t (TwoCycle.evenState A)).1 := by
    rw [perturbedState_fst, TwoCycle.evenState_firstDiagonal]
    ring
  rw [hidentity] at hraw
  calc
    |(Normalized.map L κ t (FastRemainder.perturbedState A u)).1 -
        (Normalized.map L κ t (TwoCycle.evenState A)).1| ≤
      C * |t| ^ 3 * ‖FastRemainder.perturbedState A u - TwoCycle.evenState A‖ := hraw
    _ ≤ C * |t| ^ 3 * (B * FastContraction.fixedNorm u) :=
      mul_le_mul_of_nonneg_left (norm_perturbedState_sub_evenState_le A u)
        (mul_nonneg hC.le (pow_nonneg (abs_nonneg t) 3))
    _ = (C * B) * |t| ^ 3 * FastContraction.fixedNorm u := by ring

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): centering the
actual slow output at `K` gives exactly the scalar-step residual used by the
source tube barriers. -/
theorem slowStepError_eq (G : ℝ → ℝ) (K A Aplus t : ℝ) :
    (Aplus - K) - TubeBounds.scalarStep G K t (A - K) =
      Aplus - (A + t ^ 3 * G A) := by
  have hcenter : K + (A - K) = A := by ring
  rw [TubeBounds.scalarStep_apply, hcenter]
  ring

/-- eq:polar-fast-bound (lem:polar-continuation): the actual normalized map
has slow error bounded by `Ccross * t ^ 3 * fixedNorm u + Cslow * t ^ 4`
on a fixed neighborhood of the source cycle normalization. The fast radius
and parameter neighborhood precede the feedback selection, and all constants
precede the initial cycle index. -/
theorem polarSlowBound :
    ∃ r > 0, ∃ rate > (1 / 3 : ℝ), ∃ η > 0,
      ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
        νStar ∈ TwoCycle.parameterSet ∧
        ∃ s > 0, ∃ Ccross > 0, ∃ Cslow > 0, ∃ ε > 0,
          TwoCycle.restoringDrift νStar (cycleK νStar) = 0 ∧
          ∀ A ∈ Set.Icc (cycleK νStar - s) (cycleK νStar + s),
            ContDiffAt ℝ ω TwoCycle.inverseParameter A ∧
              A ∈ TwoCycle.normalizationSet ∧ 0 < A ∧
              deriv (TwoCycle.restoringDrift νStar) A ≤ -rate ∧
              ∀ u : Fin 2 → ℝ, FastContraction.fixedNorm u < r →
                ∀ t : ℝ, 0 ≤ t → t < ε →
                  |(Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar) t
                    (FastRemainder.perturbedState A u)).1 -
                      (A + t ^ 3 * TwoCycle.restoringDrift νStar A)| ≤
                        Ccross * t ^ 3 * FastContraction.fixedNorm u + Cslow * t ^ 4 := by
  obtain ⟨r, hr, d, hd, hcoupling⟩ := uniformSlowCouplingFixedNeighborhood
  obtain ⟨rate, hrate, δG, hδG, hrestoring⟩ := TwoCycle.restoringSlowDrift
  have htendsto : Tendsto cycleK (𝓝 baseAngle) (𝓝 TwoCycle.kZero) := by
    simpa only [ContinuousAt, TwoCycle.kZero_def] using
      TwoCycle.hasDerivAt_cycleK_baseAngle.continuousAt
  have hcenterEventually : ∀ᶠ ν : ℝ in 𝓝 baseAngle,
      |cycleK ν - TwoCycle.kZero| < d / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      htendsto.eventually (Metric.ball_mem_nhds TwoCycle.kZero (half_pos hd))
  obtain ⟨η, hη, hcenter⟩ := Metric.eventually_nhds_iff.mp hcenterEventually
  refine ⟨r, hr, rate, hrate, min η δG, lt_min hη hδG, ?_⟩
  intro νStar hνStar
  have hνSource : νStar ∈ Set.Ioo baseAngle (baseAngle + δG) := by
    refine ⟨hνStar.1, ?_⟩
    exact hνStar.2.trans_le (add_le_add le_rfl (min_le_right η δG))
  have hνNear : dist νStar baseAngle < η := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hνStar.1)]
    have hupper := hνStar.2
    linarith [min_le_left η δG]
  have hKnear : |cycleK νStar - TwoCycle.kZero| < d / 2 := hcenter hνNear
  obtain ⟨hparameter, rG, hrG, Cslow, hCslow, δSlow, hδSlow, heq, hbranch⟩ :=
    hrestoring νStar hνSource
  obtain ⟨Ccross, hCcross, δCross, hδCross, hcross⟩ :=
    hcoupling (4 * baseAngle / (9 * νStar)) (cycleK νStar)
  let s := min rG (d / 4)
  have hs : 0 < s := lt_min hrG (div_pos hd zero_lt_four)
  refine ⟨hparameter, s, hs, Ccross, hCcross, Cslow, hCslow,
    min δCross δSlow, lt_min hδCross hδSlow, heq, ?_⟩
  intro A hA
  have hsG : s ≤ rG := min_le_left _ _
  have hsD : s ≤ d / 4 := min_le_right _ _
  have hAG : A ∈ Set.Icc (cycleK νStar - rG) (cycleK νStar + rG) := by
    constructor
    · linarith [hA.1]
    · linarith [hA.2]
  have hAcenter : |A - cycleK νStar| ≤ s := by
    apply abs_le.mpr
    constructor
    · linarith [hA.1]
    · linarith [hA.2]
  have hAnear : |A - TwoCycle.kZero| < d := by
    have htriangle := abs_sub_le A (cycleK νStar) TwoCycle.kZero
    linarith
  have hproperties := hbranch A hAG
  refine ⟨hproperties.1, hproperties.2.1, hproperties.2.2.1,
    hproperties.2.2.2.1, ?_⟩
  intro u hu t ht htε
  have htCross : |t| < δCross := by
    rw [abs_of_nonneg ht]
    exact htε.trans_le (min_le_left _ _)
  have htSlow : |t| < δSlow := by
    rw [abs_of_nonneg ht]
    exact htε.trans_le (min_le_right _ _)
  have hcrossBound := (hcross A hAnear).2 u hu t htCross
  have hslowBound := hproperties.2.2.2.2 t htSlow
  rw [abs_of_nonneg ht] at hcrossBound hslowBound
  have htriangle := abs_sub_le
    (Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar) t
      (FastRemainder.perturbedState A u)).1
    (Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar) t
      (TwoCycle.evenState A)).1
    (A + t ^ 3 * TwoCycle.restoringDrift νStar A)
  exact htriangle.trans (add_le_add hcrossBound hslowBound)

end DFP.Polar.SlowCoupling
