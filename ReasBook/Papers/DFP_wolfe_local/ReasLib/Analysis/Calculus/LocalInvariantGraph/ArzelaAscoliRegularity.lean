module

public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.MeanValue

public section

open Set Filter
open scoped Topology BoundedContinuousFunction NNReal

namespace LocalInvariantGraph

/-- Helper for cm-center-proposition: a uniformly bounded family with a common
Lipschitz constant on a compact domain has a uniformly convergent subsequence.
This is the compactness step of the source Arzelà–Ascoli argument. -/
theorem uniformlyBoundedLipschitzSubsequence
    {K E : Type*} [PseudoMetricSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [ProperSpace E]
    (f : ℕ → K → E) (L : ℝ≥0) (B : ℝ)
    (hlip : ∀ n, LipschitzWith L (f n)) (hbound : ∀ n x, ‖f n x‖ ≤ B) :
    ∃ g : K →ᵇ E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun n ↦ f (φ n)) g atTop := by
  let F : ℕ → (K →ᵇ E) := fun n ↦
    BoundedContinuousFunction.mkOfCompact ⟨f n, (hlip n).continuous⟩
  have hequi : Equicontinuous (fun g : range F ↦ (g.1 : K → E)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ ↦ L * t)
    · simpa only [Pi.mul_def, mul_zero] using
        (continuous_const.mul continuous_id : Continuous (fun t : ℝ ↦ (L : ℝ) * t)).tendsto 0
    · intro x y g
      obtain ⟨n, hn⟩ := g.property
      rw [← hn]
      exact (hlip n).dist_le_mul x y
  have hrange : ∀ (g : K →ᵇ E) (x : K), g ∈ range F →
      g x ∈ Metric.closedBall (0 : E) B := by
    intro g x hg
    obtain ⟨n, rfl⟩ := hg
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbound n x
  have hcompact := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : E) B) (isCompact_closedBall 0 B)
    (range F) hrange hequi
  obtain ⟨g, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun n ↦ subset_closure (mem_range_self n))
  exact ⟨g, φ, hφ, BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim⟩

/-- Helper for cm-center-proposition: a continuous chain of consecutive derivatives
on an open interval determines the finite smoothness of its first component. -/
theorem contDiffOn_of_derivativeChain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} (hs : IsOpen s) (m : ℕ) (g : ℕ → ℝ → E)
    (hcont : ∀ r, r ≤ m → ContinuousOn (g r) s)
    (hderiv : ∀ r, r < m → ∀ x ∈ s, HasDerivAt (g r) (g (r + 1) x) x) :
    ContDiffOn ℝ m (g 0) s := by
  induction m generalizing g with
  | zero =>
      exact contDiffOn_zero.mpr (hcont 0 le_rfl)
  | succ m ih =>
      have hnext : ContDiffOn ℝ m (g 1) s := by
        apply ih (fun r ↦ g (r + 1))
        · intro r hr
          exact hcont (r + 1) (Nat.succ_le_succ hr)
        · intro r hr x hx
          exact hderiv (r + 1) (Nat.succ_lt_succ hr) x hx
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen hs]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        exact (hderiv 0 (Nat.zero_lt_succ m) x hx).differentiableAt.differentiableWithinAt
      · simp
      · apply hnext.congr
        intro x hx
        exact (hderiv 0 (Nat.zero_lt_succ m) x hx).deriv

/-- Helper for cm-center-proposition: uniform limits of coherent derivative jets
on an open domain form the derivative chain of a finite-smooth limit. -/
theorem contDiffOn_of_uniformDerivativeLimits
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {s : Set ℝ} (hs : IsOpen s) (m : ℕ)
    (f : ℕ → ℕ → ℝ → E) (g : ℕ → ℝ → E)
    (hcont : ∀ n r, r ≤ m → ContinuousOn (f n r) s)
    (hderiv : ∀ n r, r < m → ∀ x ∈ s,
      HasDerivAt (f n r) (f n (r + 1) x) x)
    (hlim : ∀ r, r ≤ m → TendstoUniformlyOn (fun n ↦ f n r) (g r) atTop s) :
    ContDiffOn ℝ m (g 0) s := by
  apply contDiffOn_of_derivativeChain hs m g
  · intro r hr
    apply (hlim r hr).continuousOn
    exact (Eventually.of_forall (fun n ↦ hcont n r hr)).frequently
  · intro r hr x hx
    apply hasDerivAt_of_tendstoUniformlyOn hs (hlim (r + 1) (Nat.succ_le_of_lt hr))
    · exact Eventually.of_forall (fun n ↦ hderiv n r hr)
    · intro y hy
      exact (hlim r (Nat.le_of_lt hr)).tendsto_at hy
    · exact hx


/-- Helper for cm-center-proposition: a bound on the next derivative gives a
common Lipschitz constant for a derivative restricted to a closed interval. -/
theorem iteratedDerivBoundLipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {m r : ℕ} (hf : ContDiff ℝ (m + 1 : ℕ) f)
    (hr : r ≤ m) (a b : ℝ) (B : ℝ≥0)
    (hbound : ∀ x ∈ Icc a b, ‖iteratedDeriv (r + 1) f x‖ ≤ B) :
    LipschitzOnWith B (iteratedDeriv r f) (Icc a b) := by
  have horder : (r : WithTop ℕ∞) < (m + 1 : ℕ) := by
    exact_mod_cast Nat.lt_succ_of_le hr
  have hd := hf.differentiable_iteratedDeriv r horder
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun x _ ↦ hd x)
  · intro x hx
    rw [← iteratedDeriv_succ]
    exact_mod_cast hbound x hx
  · exact convex_Icc a b

/-- Helper for cm-center-proposition: uniformly bounded derivatives through order
`m+1` on a closed interval and pointwise convergence imply a Cᵐ limit on its
interior. The proof takes a simultaneous Arzelà–Ascoli subsequence of all jets
through order `m`, then identifies their consecutive derivatives by uniform limits. -/
theorem contDiffOn_of_uniformDerivativeBounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (m : ℕ) (a b : ℝ) (f : ℕ → ℝ → E) (g : ℝ → E) (B : ℝ≥0)
    (hf : ∀ n, ContDiff ℝ (m + 1 : ℕ) (f n))
    (hbound : ∀ n r, r ≤ m + 1 → ∀ x ∈ Icc a b,
      ‖iteratedDeriv r (f n) x‖ ≤ B)
    (hpoint : ∀ x ∈ Icc a b, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    ContDiffOn ℝ m g (Ioo a b) := by
  classical
  let J : ℕ → Icc a b → Fin (m + 1) → E :=
    fun n x i ↦ iteratedDeriv i (f n) x
  have hjetLip : ∀ n, LipschitzWith B (J n) := by
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    apply (dist_pi_le_iff (mul_nonneg B.coe_nonneg dist_nonneg)).2
    intro i
    have hi : (i : ℕ) ≤ m := Nat.le_of_lt_succ i.isLt
    have hderivative := iteratedDerivBoundLipschitz (hf n) hi a b B
      (hbound n (i + 1) (Nat.succ_le_succ hi))
    exact hderivative.dist_le_mul x x.property y y.property
  have hjetBound : ∀ n x, ‖J n x‖ ≤ (B : ℝ) := by
    intro n x
    apply (pi_norm_le_iff_of_nonneg B.coe_nonneg).2
    intro i
    exact hbound n i (Nat.le_trans (Nat.le_of_lt_succ i.isLt) (Nat.le_succ m))
      x x.property
  obtain ⟨v, φ, hφ, hlim⟩ := uniformlyBoundedLipschitzSubsequence J B B hjetLip hjetBound
  let G : ℕ → ℝ → E := fun r x ↦
    if hr : r ≤ m then
      if hx : x ∈ Icc a b then v ⟨x, hx⟩ ⟨r, Nat.lt_succ_of_le hr⟩ else 0
    else 0
  have hjetLimit : ∀ r, r ≤ m →
      TendstoUniformlyOn (fun n ↦ iteratedDeriv r (f (φ n))) (G r) atTop (Ioo a b) := by
    intro r hr
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hlim ε hε] with n hn
    intro x hx
    have hclosed : x ∈ Icc a b := Ioo_subset_Icc_self hx
    have hcoordinate := (dist_le_pi_dist (v ⟨x, hclosed⟩) (J (φ n) ⟨x, hclosed⟩)
      ⟨r, Nat.lt_succ_of_le hr⟩).trans_lt (hn ⟨x, hclosed⟩)
    simpa only [G, dif_pos hr, dif_pos hclosed, J] using hcoordinate
  have hregular : ContDiffOn ℝ m (G 0) (Ioo a b) := by
    apply contDiffOn_of_uniformDerivativeLimits isOpen_Ioo m
      (fun n r ↦ iteratedDeriv r (f (φ n))) G
    · intro n r hr
      have horder : (r : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by
        exact_mod_cast Nat.le_trans hr (Nat.le_succ m)
      exact ((hf (φ n)).continuous_iteratedDeriv r horder).continuousOn
    · intro n r hr x _
      have horder : (r : WithTop ℕ∞) < (m + 1 : ℕ) := by
        exact_mod_cast Nat.lt_succ_of_le (Nat.le_of_lt hr)
      simpa only [← iteratedDeriv_succ] using
        ((hf (φ n)).differentiable_iteratedDeriv r horder x).hasDerivAt
    · exact hjetLimit
  apply hregular.congr
  intro x hx
  have hsource := (hpoint x (Ioo_subset_Icc_self hx)).comp hφ.tendsto_atTop
  have hjet := (hjetLimit 0 (Nat.zero_le m)).tendsto_at hx
  simpa only [iteratedDeriv_zero] using tendsto_nhds_unique hsource hjet

end LocalInvariantGraph
