module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import ReasLib.Analysis.Calculus.FiniteTaylorJet
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

public section

open Filter
open scoped Topology

universe u v w

namespace FiniteTaylorJet

/-- Pointwise product-neighborhood control over a compact second factor becomes
uniform control in the first factor. -/
lemma compactFiberEventually {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {K : Set Y}
    (hK : IsCompact K) {P : X → Y → Prop}
    (hP : ∀ y ∈ K, ∀ᶠ z : X × Y in 𝓝 (x, y), P z.1 z.2) :
    ∀ᶠ x' in 𝓝 x, ∀ y ∈ K, P x' y := by
  -- Compactness turns the pointwise product neighborhoods into one first-factor neighborhood.
  exact hK.eventually_forall_of_forall_eventually hP

/-- Product-neighborhood control over a compact parameter set holds on one
positive norm ball in the increment variable. -/
lemma compactFiberNormRadius {X : Type u} {Y : Type v}
    [SeminormedAddCommGroup X] [TopologicalSpace Y] {K : Set Y}
    (hK : IsCompact K) {P : X → Y → Prop}
    (hP : ∀ y ∈ K, ∀ᶠ z : X × Y in 𝓝 (0, y), P z.1 z.2) :
    ∃ δ > 0, ∀ y ∈ K, ∀ h : X, ‖h‖ < δ → P h y := by
  -- First uniformize the neighborhood, then choose one metric ball inside it.
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (compactFiberEventually hK hP)
  refine ⟨δ, hδ, ?_⟩
  intro y hy h hh
  exact hball (by simpa only [dist_zero_right] using hh) y hy

variable {Y : Type u} {X : Type v} {Z : Type w}
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The order-zero derivative jet evaluates to the base value at every increment. -/
lemma eval_ofFunction_zero (f : X → Z) (x h : X) :
    (ofFunction ℝ 0 f x).eval h = f x := by
  -- The unique degree is zero, whose iterated derivative is the original value.
  rw [eval_eq_sum, Fin.sum_univ_succ]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [coeff_ofFunction_apply]
  simp only [Fin.val_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  exact iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := f) (x := x) (fun _ ↦ h)

/-- Pointwise finite-order differentiability along a compact fiber holds on
one common tube around that fiber. -/
lemma compactContDiffAtTube {m : ℕ} {g : Y × X → Z} {x : X} {K : Set Y}
    (hK : IsCompact K) (hg : ∀ y ∈ K, ContDiffAt ℝ m g (y, x)) :
    ∃ δ > 0, ∀ y ∈ K, ∀ h : X, ‖h‖ < δ → ContDiffAt ℝ m g (y, x + h) := by
  -- Pull each local differentiability neighborhood back along `(h,y) ↦ (y,x+h)`.
  apply compactFiberNormRadius hK
  intro y hy
  let φ : X × Y → Y × X := fun z ↦ (z.2, x + z.1)
  have hφ : Continuous φ :=
    continuous_snd.prodMk (continuous_const.add continuous_fst)
  have hφy : Tendsto φ (𝓝 (0, y)) (𝓝 (y, x)) :=
    hφ.tendsto' (0, y) (y, x) (by simp only [φ, add_zero])
  have hnear := (hg y hy).eventually (by simp)
  simpa only [φ] using hφy.eventually hnear

omit [NormedSpace ℝ Y] [NormedSpace ℝ X] [NormedSpace ℝ Z] in
/-- A function continuous along a compact fiber varies uniformly little in
the second coordinate on one common norm ball. -/
lemma compactValueOscillation {g : Y × X → Z} {x : X} {K : Set Y}
    (hK : IsCompact K) (hg : ∀ y ∈ K, ContinuousAt g (y, x))
    {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ y ∈ K, ∀ h : X, ‖h‖ < δ → ‖g (y, x + h) - g (y, x)‖ < c := by
  -- The difference of the shifted and base evaluations tends to zero at each fiber point.
  apply compactFiberNormRadius hK
  intro y hy
  let φ : X × Y → Y × X := fun z ↦ (z.2, x + z.1)
  let ψ : X × Y → Y × X := fun z ↦ (z.2, x)
  have hφ : Continuous φ :=
    continuous_snd.prodMk (continuous_const.add continuous_fst)
  have hψ : Continuous ψ := continuous_snd.prodMk continuous_const
  have hφy : Tendsto φ (𝓝 (0, y)) (𝓝 (y, x)) :=
    hφ.tendsto' (0, y) (y, x) (by simp only [φ, add_zero])
  have hψy : Tendsto ψ (𝓝 (0, y)) (𝓝 (y, x)) :=
    hψ.tendsto' (0, y) (y, x) (by simp only [ψ])
  have hshift : Tendsto (g ∘ φ) (𝓝 (0, y)) (𝓝 (g (y, x))) :=
    Filter.Tendsto.comp (hg y hy) hφy
  have hbase : Tendsto (g ∘ ψ) (𝓝 (0, y)) (𝓝 (g (y, x))) :=
    Filter.Tendsto.comp (hg y hy) hψy
  have hzero : Tendsto
      (fun z : X × Y ↦ ‖g (z.2, x + z.1) - g (z.2, x)‖)
      (𝓝 (0, y)) (𝓝 0) := by
    simpa only [φ, ψ, Function.comp_apply, sub_self, norm_zero] using
      (hshift.sub hbase).norm
  exact hzero.eventually (Iio_mem_nhds hc)

/-- On a compact fiber, the top iterated derivative has one common radius on
which its variation in the second coordinate is uniformly small. -/
lemma compactIteratedFDerivOscillation {m : ℕ} {g : Y × X → Z} {x : X}
    {K : Set Y} (hK : IsCompact K)
    (hg : ∀ y ∈ K, ContDiffAt ℝ m g (y, x)) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ y ∈ K, ∀ h : X, ‖h‖ < δ →
      ‖iteratedFDeriv ℝ m g (y, x + h) - iteratedFDeriv ℝ m g (y, x)‖ < c := by
  -- Uniformize continuity of the derivative difference, which vanishes at zero increment.
  apply compactFiberNormRadius hK
  intro y hy
  let φ : X × Y → Y × X := fun z ↦ (z.2, x + z.1)
  let ψ : X × Y → Y × X := fun z ↦ (z.2, x)
  have hφ : Continuous φ :=
    continuous_snd.prodMk (continuous_const.add continuous_fst)
  have hψ : Continuous ψ := continuous_snd.prodMk continuous_const
  have hφy : Tendsto φ (𝓝 (0, y)) (𝓝 (y, x)) :=
    hφ.tendsto' (0, y) (y, x) (by simp only [φ, add_zero])
  have hψy : Tendsto ψ (𝓝 (0, y)) (𝓝 (y, x)) :=
    hψ.tendsto' (0, y) (y, x) (by simp only [ψ])
  have hderiv := (hg y hy).continuousAt_iteratedFDeriv le_rfl
  have hshift : Tendsto (iteratedFDeriv ℝ m g ∘ φ)
      (𝓝 (0, y)) (𝓝 (iteratedFDeriv ℝ m g (y, x))) := by
    exact Filter.Tendsto.comp hderiv hφy
  have hbase : Tendsto (iteratedFDeriv ℝ m g ∘ ψ)
      (𝓝 (0, y)) (𝓝 (iteratedFDeriv ℝ m g (y, x))) := by
    exact Filter.Tendsto.comp hderiv hψy
  have hzero :
      Tendsto
        (fun z : X × Y ↦
          ‖iteratedFDeriv ℝ m g (z.2, x + z.1) -
            iteratedFDeriv ℝ m g (z.2, x)‖)
        (𝓝 (0, y)) (𝓝 0) := by
    simpa only [φ, ψ, Function.comp_apply, sub_self, norm_zero] using
      (hshift.sub hbase).norm
  exact hzero.eventually (Iio_mem_nhds hc)

/-- Differentiating a function along an affine line applies its Fréchet
derivative to the line direction. -/
lemma deriv_comp_add_smul_of_differentiableAt {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : V → W} {x h : V} {t : ℝ} (hf : DifferentiableAt ℝ f (x + t • h)) :
    deriv (fun s : ℝ ↦ f (x + s • h)) t = fderiv ℝ f (x + t • h) h := by
  -- Apply the Fréchet chain rule to the affine line and identify its derivative with `h`.
  have hline : Differentiable ℝ (fun s : ℝ ↦ x + s • h) := by fun_prop
  convert fderiv_comp_deriv t hf hline.differentiableAt
  · simp only [Function.comp_apply]
  · simpa using (deriv_smul_const (x := t) differentiableAt_id h).symm

/-- The derivative of a diagonal evaluation of an iterated Fréchet derivative
along a line is the next diagonal iterated derivative. -/
lemma deriv_iteratedFDeriv_comp_add_smul {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : V → W} {x h : V} {t : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ (n + 1) f (x + t • h)) :
    deriv (fun s : ℝ ↦ iteratedFDeriv ℝ n f (x + s • h) (fun _ ↦ h)) t =
      iteratedFDeriv ℝ (n + 1) f (x + t • h) (fun _ ↦ h) := by
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) (x + t • h) := by
    -- One further derivative exists because `f` is `C^(n+1)` at this point.
    apply hf.differentiableAt_iteratedFDeriv
    norm_cast
    exact Nat.lt_succ_self n
  -- First evaluate the multilinear-map-valued derivative on the fixed diagonal.
  convert deriv_comp_add_smul_of_differentiableAt
    (hdiff.continuousMultilinear_apply_const (fun _ ↦ h))
  -- The derivative of the `n`-th iterated derivative is its `(n+1)`-st derivative.
  exact hdiff.iteratedFDeriv_succ_apply_left'

/-- Iterated derivatives of an affine-line restriction are diagonal evaluations
of the corresponding iterated Fréchet derivatives. -/
lemma iteratedDeriv_comp_add_smul {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : V → W} {x h : V} {t : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n f (x + t • h)) :
    iteratedDeriv n (fun s : ℝ ↦ f (x + s • h)) t =
      iteratedFDeriv ℝ n f (x + t • h) (fun _ ↦ h) := by
  induction n generalizing t with
  | zero =>
      -- Both zeroth derivatives are the original function value.
      simp only [iteratedDeriv_zero]
      exact iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := f) (x := x + t • h) (fun _ ↦ h)
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heventually :
          iteratedDeriv n (fun s : ℝ ↦ f (x + s • h)) =ᶠ[𝓝 t]
            fun s ↦ iteratedFDeriv ℝ n f (x + s • h) (fun _ ↦ h) := by
        have hline : Continuous (fun s : ℝ ↦ x + s • h) := by fun_prop
        filter_upwards [hline.continuousAt.eventually (hf.eventually (by simp))] with s hs
        exact ih (hs.of_le (by norm_num))
      rw [heventually.deriv_eq]
      exact deriv_iteratedFDeriv_comp_add_smul hf

/-- The top iterated derivative of a factorial-normalized vector monomial is
the constant vector coefficient. -/
lemma iteratedDeriv_factorialInv_pow_smul (m : ℕ) (a : Z) (t : ℝ) :
    iteratedDeriv m (fun s : ℝ ↦ ((m.factorial : ℝ)⁻¹ * s ^ m) • a) t = a := by
  -- Differentiate the scalar monomial, then cancel its factorial normalization.
  rw [iteratedDeriv_smul_const (by fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow,
    Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), one_smul]

/-- Every derivative below the degree of a factorial-normalized vector
monomial vanishes at zero. -/
lemma iteratedDeriv_factorialInv_pow_smul_zero {m k : ℕ} (hk : k < m) (a : Z) :
    iteratedDeriv k (fun s : ℝ ↦ ((m.factorial : ℝ)⁻¹ * s ^ m) • a) 0 = 0 := by
  -- The remaining positive power of zero kills each lower derivative.
  rw [iteratedDeriv_smul_const (by fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  simp only [zero_pow (Nat.sub_pos_of_lt hk).ne', mul_zero, zero_smul]

/-- An operator-norm oscillation bound for a joint iterated derivative bounds
the corresponding scalar radial derivative difference. -/
lemma norm_iteratedDeriv_radial_sub_le (m : ℕ) (g : Y × X → Z)
    (y : Y) (x h : X) (t c : ℝ)
    (ht : ContDiffAt ℝ m g (y, x + t • h))
    (hzero : ContDiffAt ℝ m g (y, x))
    (hosc : ‖iteratedFDeriv ℝ m g (y, x + t • h) -
      iteratedFDeriv ℝ m g (y, x)‖ ≤ c) :
    ‖iteratedDeriv m (fun s : ℝ ↦ g (y, x + s • h)) t -
      iteratedDeriv m (fun s : ℝ ↦ g (y, x + s • h)) 0‖ ≤
        c * ‖h‖ ^ m := by
  have ht' : ContDiffAt ℝ m g ((y, x) + t • ((0, h) : Y × X)) := by
    simpa only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero] using ht
  have hzero' : ContDiffAt ℝ m g ((y, x) + (0 : ℝ) • ((0, h) : Y × X)) := by
    simpa only [zero_smul, add_zero] using hzero
  have htderiv := iteratedDeriv_comp_add_smul
    (f := g) (x := (y, x)) (h := ((0, h) : Y × X)) (t := t) ht'
  have hzeroderiv := iteratedDeriv_comp_add_smul
    (f := g) (x := (y, x)) (h := ((0, h) : Y × X)) (t := 0) hzero'
  simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_smul] at htderiv hzeroderiv
  rw [htderiv, hzeroderiv]
  calc
    ‖iteratedFDeriv ℝ m g (y, x + t • h) (fun _ ↦ (0, h)) -
        iteratedFDeriv ℝ m g (y, x) (fun _ ↦ (0, h))‖ =
        ‖(iteratedFDeriv ℝ m g (y, x + t • h) -
          iteratedFDeriv ℝ m g (y, x)) (fun _ ↦ (0, h))‖ := by
            rw [sub_apply]
    _ ≤ ‖iteratedFDeriv ℝ m g (y, x + t • h) -
          iteratedFDeriv ℝ m g (y, x)‖ * ∏ _i : Fin m, ‖((0, h) : Y × X)‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ c * ∏ _i : Fin m, ‖((0, h) : Y × X)‖ :=
      mul_le_mul_of_nonneg_right hosc (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    _ = c * ‖h‖ ^ m := by
      simp only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg h), Finset.prod_const,
        Finset.card_fin]

/-- Oscillation of the top joint derivative along a radial segment controls
the successor-order Taylor-jet remainder of the corresponding slice. -/
lemma norm_taylorRemainder_le_of_iteratedFDerivOscillation (n : ℕ)
    (g : Y × X → Z) (y : Y) (x h : X) (c : ℝ)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContDiffAt ℝ (n + 1) g (y, x + t • h))
    (hosc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n + 1) g (y, x + t • h) -
        iteratedFDeriv ℝ (n + 1) g (y, x)‖ ≤ c) :
    ‖(ofFunction ℝ (n + 1) (fun z ↦ g (y, z)) x).remainder
        (fun z ↦ g (y, z)) x h‖ ≤
      c / n.factorial * ‖h‖ ^ ((n + 1 : ℕ) : ℝ) := by
  -- Route correction: reduce the multivariable remainder to the scalar radial residual;
  -- the earlier direct multivariable induction had no executable mean-value step.
  let radial : ℝ → Z := fun t ↦ g (y, x + t • h)
  let top : Z := iteratedDeriv (n + 1) radial 0
  let monomial : ℝ → Z := fun t ↦
    ((((n + 1).factorial : ℝ)⁻¹ * t ^ (n + 1)) • top)
  let residual : ℝ → Z := fun t ↦ radial t - monomial t
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hslice (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ContDiffAt ℝ (n + 1) (fun z ↦ g (y, z)) (x + t • h) := by
    -- Restrict the joint function to the fixed-parameter affine slice.
    simpa only [Function.comp_def] using
      (hreg t ht).comp (x + t • h) (contDiffAt_const.prodMk contDiffAt_id)
  have hradial (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ContDiffAt ℝ (n + 1) radial t := by
    -- Compose the slice with the radial line through `x` in direction `h`.
    have hline : ContDiffAt ℝ (n + 1) (fun s : ℝ ↦ x + s • h) t := by
      fun_prop
    simpa only [radial, Function.comp_def] using (hslice t ht).comp t hline
  have hmonomial : ContDiff ℝ (n + 1) monomial := by
    -- The subtracted top-degree monomial is smooth.
    dsimp only [monomial]
    fun_prop
  have hresidual : ContDiffOn ℝ (n + 1) residual (Set.Icc (0 : ℝ) 1) := by
    -- Both summands are continuously differentiable throughout the segment.
    intro t ht
    exact ((hradial t ht).sub hmonomial.contDiffAt).contDiffWithinAt
  have hderivBound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin (n + 1) residual (Set.Icc (0 : ℝ) 1) t‖ ≤
        c * ‖h‖ ^ (n + 1) := by
    -- The normalized monomial removes the derivative at the segment base.
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc zero_lt_one)
      ((hradial t ht).sub hmonomial.contDiffAt) ht]
    rw [iteratedDeriv_fun_sub (hradial t ht) hmonomial.contDiffAt]
    rw [iteratedDeriv_factorialInv_pow_smul]
    have hregZero : ContDiffAt ℝ (n + 1) g (y, x) := by
      simpa only [zero_smul, add_zero] using hreg 0 hzero
    exact norm_iteratedDeriv_radial_sub_le (n + 1) g y x h t c
      (hreg t ht) hregZero (hosc t ht)
  have htaylor := taylor_mean_remainder_bound (E := Z) (n := n)
    (a := 0) (b := 1) (C := c * ‖h‖ ^ (n + 1)) (x := 1)
    zero_le_one hresidual ⟨zero_le_one, le_rfl⟩ hderivBound
  have htaylorResidual :
      taylorWithinEval residual n (Set.Icc (0 : ℝ) 1) 0 1 =
        taylorWithinEval radial n (Set.Icc (0 : ℝ) 1) 0 1 := by
    -- Every derivative below the subtracted monomial's degree vanishes at zero.
    rw [taylor_within_apply, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk_lt : k < n + 1 := Nat.lt_succ_of_le hk_le
    have hradialZero : ContDiffAt ℝ k radial 0 :=
      (hradial 0 hzero).of_le (by exact_mod_cast hk_le.trans (Nat.le_succ n))
    have hmonomialZero : ContDiffAt ℝ k monomial 0 :=
      hmonomial.contDiffAt.of_le (by exact_mod_cast hk_le.trans (Nat.le_succ n))
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (hradialZero.sub hmonomialZero) hzero]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      hradialZero hzero]
    rw [iteratedDeriv_fun_sub hradialZero hmonomialZero]
    rw [iteratedDeriv_factorialInv_pow_smul_zero hk_lt]
    simp only [sub_zero]
  have hjetTaylor :
      (ofFunction ℝ (n + 1) (fun z ↦ g (y, z)) x).eval h =
        taylorWithinEval radial (n + 1) (Set.Icc (0 : ℝ) 1) 0 1 := by
    -- Diagonal Fréchet coefficients are precisely the scalar radial derivatives.
    rw [eval_eq_sum, taylor_within_apply, ← Fin.sum_univ_eq_sum_range]
    congr with k
    rw [coeff_ofFunction_apply]
    have hk_le : (k : ℕ) ≤ n + 1 := Nat.le_of_lt_succ k.isLt
    have hradialZero : ContDiffAt ℝ (k : ℕ) radial 0 :=
      (hradial 0 hzero).of_le (by exact_mod_cast hk_le)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      hradialZero hzero]
    have hradialDeriv :
        iteratedDeriv (k : ℕ) radial 0 =
          iteratedFDeriv ℝ (k : ℕ) (fun z ↦ g (y, z)) x (fun _ ↦ h) := by
      simpa only [radial, zero_smul, add_zero] using
        (iteratedDeriv_comp_add_smul (x := x) (h := h) (t := 0)
          ((hslice 0 hzero).of_le (by exact_mod_cast hk_le)))
    rw [hradialDeriv]
    simp only [sub_zero, one_pow, mul_one]
  have htopWithin :
      iteratedDerivWithin (n + 1) radial (Set.Icc (0 : ℝ) 1) 0 = top := by
    -- On the nondegenerate interval, the within derivative is the ordinary derivative.
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (hradial 0 hzero) hzero
  have hremainder :
      (ofFunction ℝ (n + 1) (fun z ↦ g (y, z)) x).remainder
          (fun z ↦ g (y, z)) x h =
        residual 1 - taylorWithinEval residual n (Set.Icc (0 : ℝ) 1) 0 1 := by
    -- Reinsert the removed top Taylor term and identify the full jet polynomial.
    rw [remainder_def, hjetTaylor, htaylorResidual, taylorWithinEval_succ, htopWithin]
    have htopTerm :
        ((((n + 1 : ℝ) * n.factorial)⁻¹ * (1 - 0) ^ (n + 1)) • top) =
          monomial 1 := by
      simp only [monomial, one_pow, sub_zero, mul_one, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [htopTerm]
    simp only [residual, radial, one_smul]
    abel
  rw [hremainder]
  calc
    ‖residual 1 - taylorWithinEval residual n (Set.Icc (0 : ℝ) 1) 0 1‖
        ≤ (c * ‖h‖ ^ (n + 1)) * (1 - 0) ^ (n + 1) / n.factorial := htaylor
    _ = c / n.factorial * ‖h‖ ^ ((n + 1 : ℕ) : ℝ) := by
      rw [sub_zero, one_pow, mul_one, Real.rpow_natCast]
      ring

variable {Θ : Type u} {E : Type v} {F : Type w}
variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A family of finite jets has a uniform remainder bound on `K` when one
positive radius works for all parameters in `K`. -/
def IsUniformRemainderOn {m : ℕ} (f : Θ → E → F)
    (J : Θ → FiniteTaylorJet ℝ E F m) (x : E) (K : Set Θ) (C q : ℝ) : Prop :=
  ∃ δ > 0, ∀ θ ∈ K, ∀ h : E, ‖h‖ < δ →
    ‖(J θ).remainder (f θ) x h‖ ≤ C * ‖h‖ ^ q

namespace IsUniformRemainderOn

omit [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] in
/-- The defining common-radius characterization of a uniform jet remainder. -/
theorem spec {m : ℕ} (f : Θ → E → F) (J : Θ → FiniteTaylorJet ℝ E F m)
    (x : E) (K : Set Θ) (C q : ℝ) :
    FiniteTaylorJet.IsUniformRemainderOn f J x K C q ↔
      ∃ δ > 0, ∀ θ ∈ K, ∀ h : E, ‖h‖ < δ →
        ‖(J θ).remainder (f θ) x h‖ ≤ C * ‖h‖ ^ q := by
  -- Unfolding exposes the common positive radius and its uniform estimate.
  rfl

omit [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] in
/-- A uniform jet remainder supplies an explicit common positive radius and its
associated bound. -/
theorem bound {m : ℕ} {f : Θ → E → F} {J : Θ → FiniteTaylorJet ℝ E F m}
    {x : E} {K : Set Θ} {C q : ℝ}
    (hJ : FiniteTaylorJet.IsUniformRemainderOn f J x K C q) :
    ∃ δ > 0, ∀ θ ∈ K, ∀ h : E, ‖h‖ < δ →
      ‖(J θ).remainder (f θ) x h‖ ≤ C * ‖h‖ ^ q := by
  -- Project the common radius and pointwise estimate from the predicate.
  exact hJ

omit [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] in
/-- Restrict a multivariable uniform jet remainder along uniformly bounded
scalar directions to obtain the scalar-path remainder predicate. -/
theorem along {m : ℕ} {f : Θ → E → F} {J : Θ → FiniteTaylorJet ℝ E F m}
    {x : E} {K : Set Θ} {C q : ℝ}
    (hJ : FiniteTaylorJet.IsUniformRemainderOn f J x K C q)
    (v : Θ → E) (hv : ∀ θ ∈ K, ‖v θ‖ ≤ 1) (hC : 0 ≤ C) (hq : 0 ≤ q) :
    Asymptotics.IsUniformRemainderOn
      (fun θ ε ↦ (J θ).remainder (f θ) x (ε • v θ)) K C q := by
  -- Reuse the vector estimate's common radius for every scalar path.
  obtain ⟨δ, hδ, hbound⟩ := bound hJ
  -- Route correction: the imported scalar predicate is opaque, so cross its public big-O bridge.
  refine (Asymptotics.IsUniformRemainderOn.isBigOWith_iff
    (fun θ ε ↦ (J θ).remainder (f θ) x (ε • v θ)) K C q).mp ?_
  rw [Asymptotics.isBigOWith_iff]
  refine Metric.eventually_prod_nhds_iff.mpr
    ⟨fun θ ↦ θ ∈ K, Filter.eventually_principal.mpr (fun θ hθ ↦ hθ), δ, hδ, ?_⟩
  intro θ hθ ε hε
  have habs : |ε| < δ := by
    simpa only [Real.dist_0_eq_abs] using hε
  have hnorm : ‖ε • v θ‖ ≤ |ε| := by
    -- A direction of norm at most one cannot enlarge the scalar increment.
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg ε) (hv θ hθ)
  have hadmissible : ‖ε • v θ‖ < δ := hnorm.trans_lt habs
  have hscalar : ‖(J θ).remainder (f θ) x (ε • v θ)‖ ≤ C * |ε| ^ q := by
    calc
      ‖(J θ).remainder (f θ) x (ε • v θ)‖
          ≤ C * ‖ε • v θ‖ ^ q := hbound θ hθ (ε • v θ) hadmissible
      _ ≤ C * |ε| ^ q := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hnorm hq) hC
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg ε) q)] using hscalar

end IsUniformRemainderOn

/-- Joint finite-order differentiability restricts to finite-order differentiability
of every fixed-parameter slice. -/
private lemma contDiffAt_slice {m : ℕ} {f : Θ → E → F} {θ : Θ} {x : E}
    (hf : ContDiffAt ℝ m (Function.uncurry f) (θ, x)) :
    ContDiffAt ℝ m (f θ) x := by
  -- Compose the joint map with the affine inclusion `z ↦ (θ, z)`.
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using
    hf.comp x (contDiffAt_const.prodMk contDiffAt_id)

/-- If a family is jointly `C^m` at every point of a compact parameter fiber,
its factorial-normalized order-`m` Taylor jets have a uniform Peano remainder
bound there. -/
theorem uniformRemainderOn_of_contDiffAt (m : ℕ) (f : Θ → E → F) (x : E)
    (K : Set Θ) (hK : IsCompact K)
    (hf : ∀ θ ∈ K, ContDiffAt ℝ m (Function.uncurry f) (θ, x))
    (C : ℝ) (hC : 0 < C) :
    IsUniformRemainderOn f (fun θ ↦ ofFunction ℝ m (f θ) x) x K C (m : ℝ) := by
  cases m with
  | zero =>
      -- At order zero, compact-uniform continuity directly controls the value remainder.
      obtain ⟨δ, hδ, hvalue⟩ := compactValueOscillation hK
        (fun θ hθ ↦ (hf θ hθ).continuousAt) hC
      refine (IsUniformRemainderOn.spec f
        (fun θ ↦ ofFunction ℝ 0 (f θ) x) x K C _).mpr
        ⟨δ, hδ, ?_⟩
      intro θ hθ h hh
      have hsmall := (hvalue θ hθ h hh).le
      rw [remainder_def, eval_ofFunction_zero]
      simpa only [Function.uncurry_apply_pair, Nat.cast_zero, Real.rpow_zero, mul_one] using hsmall
  | succ n =>
      have hfactorialPos : 0 < (n.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos n
      have htolerance : 0 < C * (n.factorial : ℝ) := mul_pos hC hfactorialPos
      -- Choose common radii for segment regularity and top-derivative oscillation.
      obtain ⟨δreg, hδreg, hreg⟩ := compactContDiffAtTube hK hf
      obtain ⟨δosc, hδosc, hosc⟩ :=
        compactIteratedFDerivOscillation hK hf htolerance
      refine (IsUniformRemainderOn.spec f
        (fun θ ↦ ofFunction ℝ (n + 1) (f θ) x) x K C _).mpr
        ⟨min δreg δosc, lt_min hδreg hδosc, ?_⟩
      intro θ hθ h hh
      have hhreg : ‖h‖ < δreg := hh.trans_le (min_le_left _ _)
      have hhosc : ‖h‖ < δosc := hh.trans_le (min_le_right _ _)
      have hsegmentNorm (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖t • h‖ ≤ ‖h‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (norm_nonneg h)
      have hsegmentReg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ContDiffAt ℝ (n + 1) (Function.uncurry f) (θ, x + t • h) := by
        intro t ht
        exact hreg θ hθ (t • h) ((hsegmentNorm t ht).trans_lt hhreg)
      have hsegmentOsc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedFDeriv ℝ (n + 1) (Function.uncurry f) (θ, x + t • h) -
            iteratedFDeriv ℝ (n + 1) (Function.uncurry f) (θ, x)‖ ≤
              C * (n.factorial : ℝ) := by
        intro t ht
        exact (hosc θ hθ (t • h) ((hsegmentNorm t ht).trans_lt hhosc)).le
      have hradial := norm_taylorRemainder_le_of_iteratedFDerivOscillation n
        (Function.uncurry f) θ x h (C * (n.factorial : ℝ)) hsegmentReg hsegmentOsc
      have hfactorialNe : (n.factorial : ℝ) ≠ 0 := ne_of_gt hfactorialPos
      -- Cancel the chosen factorial tolerance to recover the prescribed coefficient `C`.
      simpa only [Function.uncurry_apply_pair, mul_div_cancel_right₀ C hfactorialNe] using hradial

/-- A jointly `C^m` family has factorial-normalized order-`m` Taylor jets whose
Peano remainders satisfy every positive order-`m` coefficient bound uniformly on a
compact parameter set. -/
theorem uniformRemainderOn_of_contDiff (m : ℕ) (f : Θ → E → F) (x : E)
    (K : Set Θ) (hK : IsCompact K)
    (hf : ContDiff ℝ m (Function.uncurry f)) (C : ℝ) (hC : 0 < C) :
    IsUniformRemainderOn f (fun θ ↦ ofFunction ℝ m (f θ) x) x K C (m : ℝ) := by
  -- Global differentiability supplies the pointwise hypotheses on the compact fiber.
  exact uniformRemainderOn_of_contDiffAt m f x K hK
    (fun θ _ ↦ hf.contDiffAt) C hC

/-- If a family is jointly analytic at every point of a compact parameter
fiber, its factorial-normalized finite Taylor jets have a uniform Peano
remainder bound there. -/
theorem uniformRemainderOn_of_analyticAt [CompleteSpace F]
    (m : ℕ) (f : Θ → E → F) (x : E) (K : Set Θ) (hK : IsCompact K)
    (hf : ∀ θ ∈ K, AnalyticAt ℝ (Function.uncurry f) (θ, x))
    (C : ℝ) (hC : 0 < C) :
    IsUniformRemainderOn f (fun θ ↦ ofFunction ℝ m (f θ) x) x K C (m : ℝ) := by
  -- Analyticity gives differentiability of every finite order at each fiber point.
  exact uniformRemainderOn_of_contDiffAt m f x K hK
    (fun θ hθ ↦ (hf θ hθ).contDiffAt) C hC

/-- A jointly analytic family has factorial-normalized order-`m` Taylor jets
whose Peano remainders satisfy every positive order-`m` coefficient bound uniformly on
a compact parameter set. -/
theorem uniformRemainderOn_of_analyticOnNhd (m : ℕ) (f : Θ → E → F) (x : E)
    (K : Set Θ) (hK : IsCompact K)
    (hf : AnalyticOnNhd ℝ (Function.uncurry f) Set.univ)
    (C : ℝ) (hC : 0 < C) :
    IsUniformRemainderOn f (fun θ ↦ ofFunction ℝ m (f θ) x) x K C (m : ℝ) := by
  -- On the whole domain, analyticity yields the required finite-order regularity.
  exact uniformRemainderOn_of_contDiffAt m f x K hK
    (fun θ _ ↦ (hf.contDiffOn uniqueDiffOn_univ).contDiffAt
      Filter.univ_mem) C hC

end FiniteTaylorJet
