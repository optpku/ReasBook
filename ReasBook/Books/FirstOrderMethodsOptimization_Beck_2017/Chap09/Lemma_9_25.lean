/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_4
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_6
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_4
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Theorem_9_12
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Filter
open scoped BigOperators Topology
open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g ω : E → EReal} {XStar : Set E} {FOpt σ : ℝ}
variable {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}

/- Domain sampling for Lemma 9.25.
- Primary domain: composite mirror descent in Bregman geometry.
- Inspected owner declarations:
  `IsCompositeConvexMinimizationProblem f g XStar FOpt` and
  `IsCompositeMirrorDescentProblem f g XStar FOpt Lf` from Definition 9.4,
  `IsBregmanPotentialOn ω (effective_domain g) σ` from Definitions 9.2 and 9.5,
  `is_mirror_c_trajectory f g ω x s t` from Definition 9.6,
  `best_achieved_function_value` from Definition 8.8, and
  the equation-(9.33) bridge from Text 9.10.

Lemma 9.25 is `source-facing`: it states the weighted running-best Mirror-C objective-gap estimate
for a concrete trajectory with nonincreasing stepsizes. The best owner abstraction for the
iterative side is therefore `is_mirror_c_trajectory`, while the composite-objective assumptions
should use the smaller chapter owner `IsCompositeConvexMinimizationProblem`; the stronger
`IsCompositeMirrorDescentProblem` is only the `Lf`-augmented extension used by later rate theorems.
The primitive data are the composite convex problem package, the Bregman owner `B[ω]`, the
nonnegativity of `g` on `dom(g)`, and the concrete trajectory/stepsize hypotheses. -/

-- Proof sketch: isolate the one-step shifted Mirror-C estimate, then prove the rest of the
-- textbook bookkeeping directly in Lean. Once the one-step estimate is available, the remaining
-- work is summation, a shifted-penalty comparison using antitonicity of `t`, and the standard
-- running-best division argument.
/-- Helper for Lemma 9.25: every optimal point of the composite problem lies in
`effective_domain g`. -/
lemma mirrorCOptimalPoint_memEffectiveDomain
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
  -- Compare the optimal point against a finite point of `g` to rule out `g xStar = ⊤`.
  have hxStar_min : IsMinOn (fun y ↦ f y + g y) Set.univ xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  obtain ⟨z, hz_dom⟩ := h_problem.g_proper.effective_domain_nonempty
  have hz_f : z ∈ effective_domain f := by
    exact interior_subset
      (h_problem.g_effective_domain_subset_interior_f_effective_domain hz_dom)
  have hz_sum_lt_top : f z + g z < ⊤ := by
    exact EReal.add_lt_top (mem_effective_domain.mp hz_f).ne (mem_effective_domain.mp hz_dom).ne
  have hxStar_le_z : f xStar + g xStar ≤ f z + g z := by
    exact (isMinOn_iff.mp hxStar_min) z (by simp)
  have hxStar_sum_lt_top : f xStar + g xStar < ⊤ := by
    exact lt_of_le_of_lt hxStar_le_z hz_sum_lt_top
  have hg_ne_top : g xStar ≠ ⊤ := by
    intro hg_top
    have hf_ne_bot : f xStar ≠ ⊥ := h_problem.toIsProperExtendedRealFunction.ne_bot xStar
    have hsum_top : f xStar + g xStar = ⊤ := by
      simp [hg_top, hf_ne_bot]
    exact (ne_of_lt hxStar_sum_lt_top) hsum_top
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_ne_top)

/-- Helper for Lemma 9.25: an optimal point attains the recorded optimal value in real form. -/
lemma compositeOptimalPoint_toReal_eq_FOpt
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    (f xStar + g xStar).toReal = FOpt := by
  -- The optimizer-induced GLB agrees with the stored optimal value.
  have hxStar_min : IsMinOn (fun y ↦ f y + g y) Set.univ xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hvalue :
      f xStar + g xStar = (FOpt : EReal) := by
    exact IsGLB.unique
      (by simpa [Set.mem_range] using hxStar_min.isGLB (by simp))
      h_problem.optimal_value_isGLB
  rw [hvalue]
  exact EReal.toReal_coe FOpt

/-- Helper for Lemma 9.25: the Chapter 9 three-point identity can be written directly in add form
for the Mirror-C trajectory. -/
lemma mirrorCThreePointAddForm
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (n : ℕ) (u : E) :
    inner ℝ
        ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
        (u - x (n + 1)) +
      B[ω] u (x n) =
    B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) := by
  -- Expand the three Bregman terms once and collect the gradient pairings.
  rw [bregmanDistance_def, bregmanDistance_def, bregmanDistance_def]
  have hsplit : u - x n = (u - x (n + 1)) + (x (n + 1) - x n) := by
    abel
  rw [hsplit, inner_add_right, inner_sub_left]
  ring

/-- Helper for Lemma 9.25: the one-step perturbation fed into the Chapter 9 second-prox theorem. -/
def mirrorCLinearPenalty (g : E → EReal) (sn : StrongDual ℝ E) (step : ℝ) : E → EReal :=
  fun u ↦ (((step * sn u : ℝ) : EReal) + (step : EReal) * g u)

/-- Helper for Lemma 9.25: Text 9.10 rewrites the stored Mirror-C update minimizer into the
equation `(9.33)` Bregman-form objective. -/
lemma mirrorCStepBregmanForm_isMinOn
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (n : ℕ) :
    IsMinOn (secondProxObjective (mirrorCLinearPenalty g (s n) (t n)) ω (x n))
      Set.univ (x (n + 1)) := by
  have hxnext_finite : x (n + 1) ∈ finite_domain ω := by
    exact mem_finite_domain.mpr
      ⟨hω.subset_effective_domain (h_traj.mem_effective_domain (n + 1)), hω.ne_bot _⟩
  have horig :
      IsMinOn (mirror_c_update_objective g ω (x n) (s n) (t n))
        (finite_domain ω) (x (n + 1)) := by
    rw [isMinOn_iff]
    intro y hy
    exact (isMinOn_iff.mp (h_traj.isMinOn n)) y (Set.mem_univ y)
  have hbregman :=
    (isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_form
      g ω (x n) (x (n + 1)) (s n) (t n) hxnext_finite).mp horig
  rw [isMinOn_univ_iff]
  intro y
  by_cases hy_finite : y ∈ finite_domain ω
  · simpa [SecondProxObjective.apply, mirrorCLinearPenalty, add_assoc] using
      (isMinOn_iff.mp hbregman y hy_finite)
  · have hy_not_g : y ∉ effective_domain g := by
      intro hyg
      exact hy_finite (mem_finite_domain.mpr ⟨hω.subset_effective_domain hyg, hω.ne_bot _⟩)
    have hgy_top : g y = ⊤ := by
      exact top_unique (le_of_not_gt (by simpa [mem_effective_domain] using hy_not_g))
    have hscaled_top : ((t n : ℝ) : EReal) * g y = ⊤ := by
      rw [hgy_top]
      exact EReal.coe_mul_top_of_pos (h_traj.stepsize_pos n)
    have hright_top :
        secondProxObjective (mirrorCLinearPenalty g (s n) (t n)) ω (x n) y = ⊤ := by
      rw [SecondProxObjective.apply, mirrorCLinearPenalty, hscaled_top]
      rw [EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
      exact EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
    rw [hright_top]
    exact le_top

/-- Helper for Lemma 9.25: along a Mirror-C trajectory, each finite composite objective value
splits into the sum of the finite real parts of `f` and `g`. -/
lemma mirrorCObjectiveValue_toReal_eq_add
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (n : ℕ) :
    (f (x n) + g (x n)).toReal = (f (x n)).toReal + (g (x n)).toReal := by
  -- The trajectory stays in `dom(g)`, and the standing problem assumptions place `dom(g)` inside
  -- the finite-valued interior of `f`.
  have hxg : x n ∈ effective_domain g := h_traj.mem_effective_domain n
  have hxf : x n ∈ effective_domain f := by
    exact interior_subset (h_problem.g_effective_domain_subset_interior_f_effective_domain hxg)
  have hf_top : f (x n) ≠ ⊤ := (mem_effective_domain.mp hxf).ne
  have hf_bot : f (x n) ≠ ⊥ := h_problem.toIsProperExtendedRealFunction.ne_bot (x n)
  have hg_top : g (x n) ≠ ⊤ := (mem_effective_domain.mp hxg).ne
  have hg_bot : g (x n) ≠ ⊥ := h_problem.g_proper.ne_bot (x n)
  -- `EReal.toReal_add` converts the finite extended-real sum to the displayed real sum.
  rw [EReal.toReal_add hf_top hf_bot hg_top hg_bot]

/-- Helper for Lemma 9.25: positive stepsizes preserve the effective domain when passing from `g`
to the linear-plus-penalty perturbation. -/
lemma mirrorCLinearPenalty_effectiveDomain_eq
    (g : E → EReal) (sn : StrongDual ℝ E) {step : ℝ} (hstep : 0 < step) :
    effective_domain (mirrorCLinearPenalty g sn step) = effective_domain g := by
  ext u
  constructor
  · -- Route correction: recover `u ∈ dom(g)` by ruling out `g u = ⊤` inside the finite sum.
    intro hu
    rw [mem_effective_domain] at hu ⊢
    by_contra hgu_top
    have hgu_eq_top : g u = ⊤ := by
      exact top_unique (le_of_not_gt hgu_top)
    have hscaled_top : (step : EReal) * g u = ⊤ := by
      rw [hgu_eq_top]
      exact EReal.coe_mul_top_of_pos hstep
    have hsum_top : mirrorCLinearPenalty g sn step u = ⊤ := by
      simpa [mirrorCLinearPenalty, hscaled_top] using
        EReal.add_top_of_ne_bot (show (((step * sn u : ℝ) : EReal)) ≠ ⊥ by
          exact EReal.coe_ne_bot _)
    exact (ne_of_lt hu) hsum_top
  · -- The linear term is always finite, so positivity of `step` transfers finiteness of `g u`.
    intro hu
    rw [mem_effective_domain] at hu ⊢
    refine EReal.add_lt_top ?_ ?_
    · exact EReal.coe_ne_top _
    · have hstep_nonneg : (0 : EReal) ≤ (step : ℝ) := by
        exact_mod_cast hstep.le
      exact
        (EReal.mul_ne_top _ _).2
          ⟨Or.inl (EReal.coe_ne_bot _), Or.inl hstep_nonneg,
            Or.inl (EReal.coe_ne_top _), Or.inr hu.ne⟩

/-- Helper for Lemma 9.25: on `dom(g)`, the second-prox perturbation has the expected real value. -/
lemma mirrorCLinearPenalty_toReal_eq
    (hg_proper : IsProperExtendedRealFunction g) (sn : StrongDual ℝ E)
    {step : ℝ} (hstep : 0 < step) {u : E} (hu : u ∈ effective_domain g) :
    (mirrorCLinearPenalty g sn step u).toReal =
      step * sn u + step * (g u).toReal := by
  have hstep_nonneg : (0 : EReal) ≤ (step : ℝ) := by
    exact_mod_cast hstep.le
  have hscaled_top : (step : EReal) * g u ≠ ⊤ := by
    exact
      (EReal.mul_ne_top _ _).2
        ⟨Or.inl (EReal.coe_ne_bot _), Or.inl hstep_nonneg,
          Or.inl (EReal.coe_ne_top _), Or.inr (mem_effective_domain.mp hu).ne⟩
  have hscaled_bot : (step : EReal) * g u ≠ ⊥ := by
    exact
      (EReal.mul_ne_bot _ _).2
        ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (hg_proper.ne_bot u),
          Or.inl (EReal.coe_ne_top _), Or.inl hstep_nonneg⟩
  -- Expand the finite extended-real sum and convert each summand through `toReal`.
  rw [mirrorCLinearPenalty, EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
    hscaled_top hscaled_bot]
  simp [EReal.toReal_mul]

/-- Helper for Lemma 9.25: the second-prox perturbation is proper and convex for positive
stepsizes. -/
lemma mirrorCLinearPenaltyData
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    (sn : StrongDual ℝ E) {step : ℝ} (hstep : 0 < step) :
    IsProperExtendedRealFunction (mirrorCLinearPenalty g sn step) ∧
      is_convex_function (mirrorCLinearPenalty g sn step) := by
  have hstep_nonneg : 0 ≤ step := le_of_lt hstep
  have hlinearConvex :
      ConvexOn ℝ Set.univ (fun u : E ↦ step * sn u) := by
    -- The real-valued linear functional is affine, hence convex on all of `E`.
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    refine le_of_eq ?_
    simp [smul_eq_mul, mul_add, add_mul, mul_assoc, mul_left_comm, hab]
  have hlinearConvexEReal :
      is_convex_function (fun u : E ↦ (((step * sn u : ℝ) : EReal))) :=
    Function.toEReal_isConvexFunction hlinearConvex
  have hlinear_ne_bot :
      ∀ u : E, (((step * sn u : ℝ) : EReal)) ≠ ⊥ := by
    intro u
    exact EReal.coe_ne_bot _
  have hscaledConvex :
      is_convex_function (fun u : E ↦ (step : EReal) * g u) := by
    let α : Unit → NNReal := fun _ ↦ ⟨step, hstep_nonneg⟩
    simpa [α] using
      (is_convex_function_fintype_nonneg_weighted_sum
        (f := fun _ : Unit => g)
        (hf := fun _ ↦ h_problem.g_convex)
        (h_ne_bot := fun _ u ↦ h_problem.g_proper.ne_bot u)
        α)
  have hscaled_ne_bot :
      ∀ u : E, (step : EReal) * g u ≠ ⊥ := by
    intro u
    have hstepE_nonneg : (0 : EReal) ≤ (step : ℝ) := by
      exact_mod_cast hstep_nonneg
    exact
      (EReal.mul_ne_bot _ _).2
        ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (h_problem.g_proper.ne_bot u),
          Or.inl (EReal.coe_ne_top _), Or.inl hstepE_nonneg⟩
  constructor
  · -- Properness comes from non-bot pointwise values and the unchanged effective domain.
    refine ⟨?_, ?_⟩
    · intro u
      exact EReal.add_ne_bot_iff.mpr ⟨hlinear_ne_bot u, hscaled_ne_bot u⟩
    · rcases h_problem.g_proper.effective_domain_nonempty with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      simpa [mirrorCLinearPenalty_effectiveDomain_eq (g := g) (sn := sn) hstep] using hu
  · -- Convexity is the pointwise sum of the lifted linear term and the scaled convex penalty.
    simpa [mirrorCLinearPenalty, Pi.add_apply] using
      is_convex_function_pointwise_add
      hlinearConvexEReal hscaledConvex hlinear_ne_bot hscaled_ne_bot

/-- First-order comparison for a second-prox minimizer when membership in `dom(∂ω)` is already
known.  This directional proof avoids the relative-interior sum-rule qualification needed only
to *derive* that membership in Theorem 9.12. -/
lemma secondProxOptimality_real_of_differentiableAt
    {ψ : E → EReal} {a b u : E}
    (hψ_proper : IsProperExtendedRealFunction ψ)
    (hψ_convex : is_convex_function ψ)
    (hmin : IsMinOn (secondProxObjective ψ ω b) Set.univ a)
    (ha : a ∈ effective_domain ψ) (hu : u ∈ effective_domain ψ)
    (hω_diff : DifferentiableAt ℝ (fun z ↦ (ω z).toReal) a) :
    inner ℝ
        ((∇ (fun z ↦ (ω z).toReal) b) - (∇ (fun z ↦ (ω z).toReal) a))
        (u - a) ≤
      (ψ u).toReal - (ψ a).toReal := by
  let line : ℝ → E := fun r ↦ (1 - r) • a + r • u
  have hconv : ConvexOn ℝ (effective_domain ψ) (fun z ↦ (ψ z).toReal) :=
    convexOn_toReal_of_is_convex_function_of_proper ψ hψ_convex
  have hBderiv : HasFDerivAt (fun z ↦ B[ω] z b)
      (InnerProductSpace.toDual ℝ E
        ((∇ (fun z ↦ (ω z).toReal) a) - (∇ (fun z ↦ (ω z).toReal) b))) a := by
    have hpot := hω_diff.hasGradientAt.hasFDerivAt
    have hlin : HasFDerivAt
        (fun z : E ↦ inner ℝ (∇ (fun w ↦ (ω w).toReal) b) z)
        (InnerProductSpace.toDual ℝ E (∇ (fun w ↦ (ω w).toReal) b)) a :=
      (InnerProductSpace.toDual ℝ E (∇ (fun w ↦ (ω w).toReal) b)).hasFDerivAt
    have hdisp : HasFDerivAt
        (fun z : E ↦ inner ℝ (∇ (fun w ↦ (ω w).toReal) b) (z - b))
        (InnerProductSpace.toDual ℝ E (∇ (fun w ↦ (ω w).toReal) b)) a := by
      simpa [inner_sub_right] using
        hlin.sub_const (inner ℝ (∇ (fun w ↦ (ω w).toReal) b) b)
    simpa [bregmanDistance_def, map_sub] using
      (hpot.sub_const ((ω b).toReal)).sub hdisp
  have hlineDeriv : HasLineDerivAt ℝ (fun z ↦ B[ω] z b)
      (inner ℝ
        ((∇ (fun z ↦ (ω z).toReal) a) - (∇ (fun z ↦ (ω z).toReal) b))
        (u - a)) a (u - a) := by
    simpa [InnerProductSpace.toDual_apply_apply, inner_sub_left] using
      hBderiv.hasLineDerivAt (u - a)
  have hslope :
      Tendsto (fun r : ℝ ↦ (B[ω] (line r) b - B[ω] a b) / r)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) a) - (∇ (fun z ↦ (ω z).toReal) b))
          (u - a))) := by
    simpa [line, sub_eq_add_neg, add_smul, smul_sub, add_comm, add_left_comm, add_assoc,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hlineDeriv.tendsto_slope_zero_right
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := by
    simpa [Set.mem_Ioi] using
      (eventually_mem_nhdsWithin : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r ∈ Set.Ioi (0 : ℝ))
  have hlt1 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < 1 := by
    simpa [Set.mem_Iio] using
      (show Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) from
        nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  have hpointwise :
      ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
        -((B[ω] (line r) b - B[ω] a b) / r) ≤
          (ψ u).toReal - (ψ a).toReal := by
    filter_upwards [hpos, hlt1] with r hr hr1
    have hr0 : 0 ≤ 1 - r := by linarith
    have hz : line r ∈ effective_domain ψ := by
      exact hconv.1 ha hu hr0 hr.le (by linarith)
    have hconvex_value :
        (ψ (line r)).toReal ≤ (1 - r) * (ψ a).toReal + r * (ψ u).toReal := by
      simpa [line, smul_eq_mul] using hconv.2 ha hu hr0 hr.le (by linarith)
    have hminE := (isMinOn_iff.mp hmin) (line r) (by simp)
    have ha_eq : ψ a = (((ψ a).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp ha).ne (hψ_proper.ne_bot a)).symm
    have hz_eq : ψ (line r) = (((ψ (line r)).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hz).ne (hψ_proper.ne_bot (line r))).symm
    have hminR :
        (ψ a).toReal + B[ω] a b ≤ (ψ (line r)).toReal + B[ω] (line r) b := by
      rw [SecondProxObjective.apply, SecondProxObjective.apply, ha_eq, hz_eq] at hminE
      simpa [EReal.coe_add] using EReal.coe_le_coe_iff.mp hminE
    rw [show -((B[ω] (line r) b - B[ω] a b) / r) =
      (-(B[ω] (line r) b - B[ω] a b)) / r by ring]
    apply (div_le_iff₀ hr).2
    nlinarith
  have hnegSlope :
      Tendsto (fun r : ℝ ↦ -((B[ω] (line r) b - B[ω] a b) / r))
        (𝓝[>] (0 : ℝ))
        (𝓝 (-inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) a) - (∇ (fun z ↦ (ω z).toReal) b))
          (u - a))) := hslope.neg
  have hlimit := le_of_tendsto_of_tendsto hnegSlope tendsto_const_nhds hpointwise
  simpa [inner_sub_left] using hlimit

/-- Helper for Lemma 9.25: each Mirror-C step satisfies the textbook pairing-plus-penalty
inequality. -/
lemma mirrorCStepPairingPenalty_le
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (n : ℕ) {u : E} (hu : u ∈ effective_domain g) :
    t n * s n (x n - u) + t n * ((g (x (n + 1))).toReal - (g u).toReal) ≤
      B[ω] u (x n) - B[ω] u (x (n + 1)) - B[ω] (x (n + 1)) (x n) +
        t n * s n (x n - x (n + 1)) := by
  -- Route correction: package the step objective as a second-prox datum, apply Theorem 9.12 in
  -- add form, and rewrite the resulting pairing with the three-point Bregman identity.
  let ψ : E → EReal := mirrorCLinearPenalty g (s n) (t n)
  have ht_pos : 0 < t n := h_traj.stepsize_pos n
  have hψ_dom : effective_domain ψ = effective_domain g := by
    simpa [ψ] using
      mirrorCLinearPenalty_effectiveDomain_eq (g := g) (sn := s n) ht_pos
  have hψ_data :
      IsProperExtendedRealFunction ψ ∧ is_convex_function ψ := by
    simpa [ψ] using
      mirrorCLinearPenaltyData
        (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
        h_problem (s n) ht_pos
  have hωψ : IsBregmanPotentialOn ω (effective_domain ψ) σ := by
    simpa [hψ_dom] using hω
  have huψ : u ∈ effective_domain ψ := by
    simpa [hψ_dom] using hu
  have hxnextψ : x (n + 1) ∈ effective_domain ψ := by
    simpa [hψ_dom] using h_traj.mem_effective_domain (n + 1)
  have hmin :
      IsMinOn (secondProxObjective ψ ω (x n)) Set.univ (x (n + 1)) := by
    simpa [ψ] using mirrorCStepBregmanForm_isMinOn hω h_traj n
  have hopt_real_base :
      inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) ≤
        (ψ u).toReal - (ψ (x (n + 1))).toReal := by
    exact secondProxOptimality_real_of_differentiableAt
      (hψ_proper := hψ_data.1) (hψ_convex := hψ_data.2) (hmin := hmin)
      (ha := hxnextψ) (hu := huψ)
      (hω_diff _ (h_traj.mem_subdifferential_domain (n + 1)))
  have hψxnext_top : ψ (x (n + 1)) ≠ ⊤ := (mem_effective_domain.mp hxnextψ).ne
  have hψxnext_bot : ψ (x (n + 1)) ≠ ⊥ := hψ_data.1.ne_bot (x (n + 1))
  have hleft_bot :
      ((inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) : EReal) +
        ψ (x (n + 1))) ≠ ⊥ := by
    exact EReal.add_ne_bot_iff.mpr ⟨by simp, hψxnext_bot⟩
  have hreal_raw :
      ((inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
      (u - x (n + 1)) : EReal) +
        ψ (x (n + 1))).toReal ≤
      (ψ u).toReal := by
    rw [EReal.toReal_add (by simp) (by simp) hψxnext_top hψxnext_bot]
    simp only [EReal.toReal_coe]
    linarith
  have hψxnext_toReal :
      (ψ (x (n + 1))).toReal =
        t n * s n (x (n + 1)) + t n * (g (x (n + 1))).toReal := by
    simpa [ψ] using
      mirrorCLinearPenalty_toReal_eq
        (g := g) h_problem.g_proper (s n) ht_pos (h_traj.mem_effective_domain (n + 1))
  have hψu_toReal :
      (ψ u).toReal = t n * s n u + t n * (g u).toReal := by
    simpa [ψ] using
      mirrorCLinearPenalty_toReal_eq
        (g := g) h_problem.g_proper (s n) ht_pos hu
  have hreal :
      inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) +
        (t n * s n (x (n + 1)) + t n * (g (x (n + 1))).toReal) ≤
      t n * s n u + t n * (g u).toReal := by
    rw [EReal.toReal_add (by simp) (by simp) hψxnext_top hψxnext_bot,
      hψxnext_toReal, hψu_toReal] at hreal_raw
    simpa using hreal_raw
  have hinner :
      inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) ≤
        t n * s n (u - x (n + 1)) +
          t n * ((g u).toReal - (g (x (n + 1))).toReal) := by
    have hs_apply : s n (u - x (n + 1)) = s n u - s n (x (n + 1)) := by
      rw [map_sub]
    nlinarith [hreal, hs_apply]
  have hthree :
      inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) +
        B[ω] u (x n) =
      B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) := by
    exact mirrorCThreePointAddForm
      (f := f) (g := g) (ω := ω) (x := x) (s := s) (t := t) h_traj n u
  have hthree_le :
      B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) - B[ω] u (x n) ≤
        t n * s n (u - x (n + 1)) +
          t n * ((g u).toReal - (g (x (n + 1))).toReal) := by
    nlinarith [hinner, hthree]
  have hs_shift :
      s n (u - x (n + 1)) = s n (x n - x (n + 1)) - s n (x n - u) := by
    repeat rw [map_sub]
    ring
  -- Collect the pairing identity and the second-prox comparison into the textbook one-step form.
  nlinarith [hthree_le, hs_shift]

/-- Helper for Lemma 9.25: the optimality of `xStar` rewrites the shifted composite objective gap
into the current subgradient pairing plus the shifted penalty difference. -/
lemma mirrorCSubgradientShiftedGap_le
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    (f (x n)).toReal + (g (x (n + 1))).toReal - FOpt ≤
      s n (x n - xStar) + ((g (x (n + 1))).toReal - (g xStar).toReal) := by
  have hxStar_g : xStar ∈ effective_domain g :=
    mirrorCOptimalPoint_memEffectiveDomain h_problem hxStar
  have hxStar_f : xStar ∈ effective_domain f := by
    exact interior_subset
      (h_problem.g_effective_domain_subset_interior_f_effective_domain hxStar_g)
  have hxn_f : x n ∈ effective_domain f := by
    exact interior_subset
      (h_problem.g_effective_domain_subset_interior_f_effective_domain
        (h_traj.mem_effective_domain n))
  have hsub_real :
      s n (xStar - x n) ≤ (f xStar).toReal - (f (x n)).toReal := by
    exact subgradient_eval_le_toReal_sub
      f (x n) xStar
      (fun z _ ↦ h_problem.toIsProperExtendedRealFunction.ne_bot z)
      hxn_f hxStar_f (by simpa [mem_strongDualSubdifferential] using h_traj.subgradient_mem n)
  have hreverse : s n (xStar - x n) = -s n (x n - xStar) := by
    rw [show xStar - x n = -(x n - xStar) by abel, map_neg]
  have hpairing :
      (f (x n)).toReal - (f xStar).toReal ≤ s n (x n - xStar) := by
    nlinarith [hsub_real, hreverse]
  have hxStar_top : f xStar ≠ ⊤ := (mem_effective_domain.mp hxStar_f).ne
  have hxStar_bot : f xStar ≠ ⊥ := h_problem.toIsProperExtendedRealFunction.ne_bot xStar
  have hgxStar_top : g xStar ≠ ⊤ := (mem_effective_domain.mp hxStar_g).ne
  have hgxStar_bot : g xStar ≠ ⊥ := h_problem.g_proper.ne_bot xStar
  have hFOpt_split : (f xStar).toReal + (g xStar).toReal = FOpt := by
    rw [← compositeOptimalPoint_toReal_eq_FOpt h_problem hxStar]
    exact (EReal.toReal_add hxStar_top hxStar_bot hgxStar_top hgxStar_bot).symm
  -- Replace `FOpt` by the optimizer value and keep only the subgradient pairing on the right.
  nlinarith [hpairing, hFOpt_split]

/-- Helper for Lemma 9.25: the mixed linear/Bregman term is controlled by the usual Young
inequality and the lower quadratic bound for the Bregman distance. -/
lemma mirrorCStepMixedTerm_le
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (n : ℕ) :
    t n * s n (x n - x (n + 1)) - B[ω] (x (n + 1)) (x n) ≤
      ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ) := by
  -- Bound the linear term by the operator norm, absorb it with Young, and then use the quadratic
  -- Bregman lower bound to cancel the remaining norm square.
  let diff := x n - x (n + 1)
  have hquadratic :
      (σ / 2) * ‖diff‖ ^ (2 : ℕ) ≤ B[ω] (x (n + 1)) (x n) := by
    simpa [diff, norm_sub_rev] using
      bregmanDistance_lower_quadratic_bound
        hω (x (n + 1)) (x n)
        (h_traj.mem_effective_domain (n + 1))
        (h_traj.mem_effective_domain n)
        (h_traj.mem_subdifferential_domain n)
        (hω_diff _ (h_traj.mem_subdifferential_domain n))
  have happly_norm :
      |s n diff| ≤ ‖s n‖ * ‖diff‖ := by
    simpa [diff, Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm (s n) diff
  have happly_le :
      t n * s n diff ≤ t n * (‖s n‖ * ‖diff‖) := by
    have hs_le : s n diff ≤ ‖s n‖ * ‖diff‖ := le_trans (le_abs_self _) happly_norm
    exact mul_le_mul_of_nonneg_left hs_le (le_of_lt (h_traj.stepsize_pos n))
  have hyoung_aux :
      2 * ‖diff‖ * (t n * ‖s n‖) ≤
        σ * ‖diff‖ ^ (2 : ℕ) + σ⁻¹ * (t n * ‖s n‖) ^ (2 : ℕ) := by
    simpa [diff, mul_comm, mul_left_comm, mul_assoc] using
      two_mul_le_add_mul_sq (a := ‖diff‖) (b := t n * ‖s n‖) hω.sigma_pos
  have hyoung :
      t n * (‖s n‖ * ‖diff‖) ≤
        ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ) +
          (σ / 2) * ‖diff‖ ^ (2 : ℕ) := by
    have hdouble :
        2 * (t n * (‖s n‖ * ‖diff‖)) ≤
          2 *
            ((((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) +
              (σ / 2) * ‖diff‖ ^ (2 : ℕ)) := by
      calc
        2 * (t n * (‖s n‖ * ‖diff‖)) = 2 * ‖diff‖ * (t n * ‖s n‖) := by
          ring
        _ ≤ σ * ‖diff‖ ^ (2 : ℕ) + σ⁻¹ * (t n * ‖s n‖) ^ (2 : ℕ) := hyoung_aux
        _ =
          2 *
            ((((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) +
              (σ / 2) * ‖diff‖ ^ (2 : ℕ)) := by
            field_simp [pow_two, hω.sigma_pos.ne']
            ring
    nlinarith
  -- The quadratic term from Young is exactly dominated by the Bregman lower bound.
  nlinarith [happly_le, hyoung, hquadratic]

/-- Helper for Lemma 9.25: the one-step shifted Mirror-C estimate. -/
lemma mirrorCStepShiftedObjectiveGap_le
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt) ≤
      B[ω] xStar (x n) - B[ω] xStar (x (n + 1)) +
        ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ) := by
  have hxStar_g : xStar ∈ effective_domain g :=
    mirrorCOptimalPoint_memEffectiveDomain h_problem hxStar
  have hgap :
      (f (x n)).toReal + (g (x (n + 1))).toReal - FOpt ≤
        s n (x n - xStar) + ((g (x (n + 1))).toReal - (g xStar).toReal) :=
    mirrorCSubgradientShiftedGap_le
      (f := f) (g := g) (ω := ω) (XStar := XStar) (FOpt := FOpt)
      (x := x) (s := s) (t := t) h_problem h_traj hxStar n
  have hgap_scaled :
      t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt) ≤
        t n *
          (s n (x n - xStar) + ((g (x (n + 1))).toReal - (g xStar).toReal)) := by
    exact mul_le_mul_of_nonneg_left hgap (le_of_lt (h_traj.stepsize_pos n))
  have hpair :
      t n * s n (x n - xStar) + t n * ((g (x (n + 1))).toReal - (g xStar).toReal) ≤
        B[ω] xStar (x n) - B[ω] xStar (x (n + 1)) - B[ω] (x (n + 1)) (x n) +
          t n * s n (x n - x (n + 1)) :=
    mirrorCStepPairingPenalty_le
      (f := f) (g := g) (ω := ω) (XStar := XStar) (FOpt := FOpt) (σ := σ)
      (x := x) (s := s) (t := t) h_problem hω hω_diff h_traj n hxStar_g
  have hmixed :
      t n * s n (x n - x (n + 1)) - B[ω] (x (n + 1)) (x n) ≤
        ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ) :=
    mirrorCStepMixedTerm_le
      (f := f) (g := g) (ω := ω) (x := x) (s := s) (t := t) hω hω_diff h_traj n
  -- Assemble the subgradient rewrite, the prox inequality, and the mixed-term estimate.
  nlinarith [hgap_scaled, hpair, hmixed]

/-- Helper for Lemma 9.25: summing the one-step shifted Mirror-C estimate gives the shifted prefix
gap bound. -/
lemma mirrorCShiftedGapPrefixSum_le
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1))
      (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) ≤
      B[ω] xStar (x 0) +
        (1 / (2 * σ)) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
  -- Sum the one-step estimate, telescope the Bregman terms, and drop the terminal nonnegative
  -- Bregman distance.
  have hsum_le :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) ≤
        Finset.sum (Finset.range (k + 1))
          (fun n ↦
            (B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) +
              ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) := by
    exact Finset.sum_le_sum fun n _ ↦
      mirrorCStepShiftedObjectiveGap_le
        (f := f) (g := g) (ω := ω) (XStar := XStar) (FOpt := FOpt) (σ := σ)
        (x := x) (s := s) (t := t) h_problem hω hω_diff h_traj hxStar n
  have htelescope :
      ∀ m : ℕ,
        Finset.sum (Finset.range (m + 1))
          (fun n ↦ B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) =
        B[ω] xStar (x 0) - B[ω] xStar (x (m + 1)) := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hquadraticSum :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) =
        (1 / (2 * σ)) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
    calc
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) =
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) * (1 / (2 * σ))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
      _ =
        (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) *
          (1 / (2 * σ)) := by
            rw [Finset.sum_mul]
      _ =
        (1 / (2 * σ)) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
            ring
  have hxStar_dom : xStar ∈ effective_domain g :=
    mirrorCOptimalPoint_memEffectiveDomain h_problem hxStar
  have hterminal_nonneg : 0 ≤ B[ω] xStar (x (k + 1)) := by
    exact bregmanDistance_nonneg_of_mem_subdifferential_domain
      hω xStar (x (k + 1)) hxStar_dom
      (h_traj.mem_effective_domain (k + 1))
      (h_traj.mem_subdifferential_domain (k + 1))
      (hω_diff _ (h_traj.mem_subdifferential_domain (k + 1)))
  calc
    Finset.sum (Finset.range (k + 1))
        (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) ≤
      Finset.sum (Finset.range (k + 1))
        (fun n ↦
          (B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) +
            ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) := hsum_le
    _ =
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) +
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) := by
            rw [Finset.sum_add_distrib]
    _ =
      (B[ω] xStar (x 0) - B[ω] xStar (x (k + 1))) +
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) := by
            rw [htelescope k]
    _ ≤
      B[ω] xStar (x 0) +
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) := by
            nlinarith
    _ =
      B[ω] xStar (x 0) +
        (1 / (2 * σ)) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
            rw [hquadraticSum]

/-- Helper for Lemma 9.25: the weighted prefix sum of penalty values is bounded by the initial
penalty term plus the shifted weighted prefix sum. -/
lemma mirrorCPenaltyPrefix_le_shiftedPenaltyPrefix
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (h_stepsize_antitone : Antitone t)
    (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (g (x n)).toReal) ≤
      (t 0) * (g (x 0)).toReal +
        Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (g (x (n + 1))).toReal) := by
  -- Rewrite the prefix sum by isolating the initial term, then compare the remaining weights
  -- pointwise using antitonicity of `t` and add the final nonnegative shifted term.
  have hg_nonneg : ∀ n : ℕ, 0 ≤ (g (x n)).toReal := by
    intro n
    exact EReal.toReal_nonneg (h_nonneg (x n) (h_traj.mem_effective_domain n))
  have hcore :
      Finset.sum (Finset.range k) (fun n ↦ t (n + 1) * (g (x (n + 1))).toReal) ≤
        Finset.sum (Finset.range k) (fun n ↦ t n * (g (x (n + 1))).toReal) := by
    exact Finset.sum_le_sum fun n _ ↦
      mul_le_mul_of_nonneg_right (h_stepsize_antitone (Nat.le_succ n)) (hg_nonneg (n + 1))
  have htail_nonneg : 0 ≤ t k * (g (x (k + 1))).toReal := by
    exact mul_nonneg (le_of_lt (h_traj.stepsize_pos k)) (hg_nonneg (k + 1))
  have htail_le :
      Finset.sum (Finset.range k) (fun n ↦ t n * (g (x (n + 1))).toReal) ≤
        Finset.sum (Finset.range k) (fun n ↦ t n * (g (x (n + 1))).toReal) +
          t k * (g (x (k + 1))).toReal := by
    exact le_add_of_nonneg_right htail_nonneg
  calc
    Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (g (x n)).toReal) =
      (t 0) * (g (x 0)).toReal +
        Finset.sum (Finset.range k) (fun n ↦ t (n + 1) * (g (x (n + 1))).toReal) := by
          rw [Finset.sum_range_succ']
          ring
    _ ≤
      (t 0) * (g (x 0)).toReal +
        Finset.sum (Finset.range k) (fun n ↦ t n * (g (x (n + 1))).toReal) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left hcore ((t 0) * (g (x 0)).toReal)
    _ ≤
      (t 0) * (g (x 0)).toReal +
        (Finset.sum (Finset.range k) (fun n ↦ t n * (g (x (n + 1))).toReal) +
          t k * (g (x (k + 1))).toReal) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left
                htail_le
                ((t 0) * (g (x 0)).toReal)
    _ =
      (t 0) * (g (x 0)).toReal +
        Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (g (x (n + 1))).toReal) := by
          rw [Finset.sum_range_succ]

/-- Helper for Lemma 9.25: the shifted penalty bookkeeping dominates the weighted prefix sum of
composite objective gaps. -/
lemma shiftedMirrorCGapSumDominatesObjectiveGap
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (h_stepsize_antitone : Antitone t)
    (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) ≤
      (t 0) * (g (x 0)).toReal +
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) := by
  -- Split both weighted sums into the same base `f`-part plus a penalty prefix comparison.
  let baseSum :=
    Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f (x n)).toReal - FOpt))
  let penaltySum :=
    Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (g (x n)).toReal)
  let shiftedPenaltySum :=
    Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (g (x (n + 1))).toReal)
  have hleft :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) =
        baseSum + penaltySum := by
    -- Rewrite each composite objective into its `f`- and `g`-parts.
    dsimp [baseSum, penaltySum]
    calc
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) =
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n)).toReal - FOpt) + t n * (g (x n)).toReal) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [mirrorCObjectiveValue_toReal_eq_add h_problem h_traj n]
            ring
      _ = baseSum + penaltySum := by
            rw [Finset.sum_add_distrib]
  have hright :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) =
        baseSum + shiftedPenaltySum := by
    -- The shifted sum has the same base term, with only the penalty index translated by one step.
    dsimp [baseSum, shiftedPenaltySum]
    calc
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) =
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n)).toReal - FOpt) + t n * (g (x (n + 1))).toReal) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
      _ = baseSum + shiftedPenaltySum := by
            rw [Finset.sum_add_distrib]
  have hpenalty :=
    mirrorCPenaltyPrefix_le_shiftedPenaltyPrefix
      (f := f) (g := g) (ω := ω) (x := x) (s := s) (t := t)
      h_nonneg h_traj h_stepsize_antitone k
  rw [hleft, hright]
  nlinarith

/-- Companion to Lemma 9.25: under the composite convex minimization assumptions of Definition 9.4,
together with the mirror-map assumptions of Definition 9.5 and the Mirror-C trajectory data of
Definition 9.6, if `g` is nonnegative on `dom(g)` and the Mirror-C stepsizes are nonincreasing,
then for every optimal point `xStar ∈ XStar = X^*` and every iteration index `k`, the weighted
prefix sum of composite objective gaps is bounded by
`t₀ g(x⁰) + B_ω(xStar, x⁰) + (1 / (2σ)) * ∑_{n=0}^k t_n^2 ‖f'(x^n)‖^2`. -/
theorem mirror_c_weighted_objective_gap_sum_le
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (h_stepsize_antitone : Antitone t)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1))
      (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) ≤
      (t 0) * (g (x 0)).toReal +
        B[ω] xStar (x 0) +
        (1 / (2 * σ)) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
  -- First compare the unshifted weighted objective sum with the shifted one, then apply the
  -- shifted prefix estimate.
  have hshifted :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) ≤
        (t 0) * (g (x 0)).toReal +
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) := by
    exact shiftedMirrorCGapSumDominatesObjectiveGap
      (f := f) (g := g) (ω := ω) (XStar := XStar) (FOpt := FOpt)
      (x := x) (s := s) (t := t) h_problem h_nonneg h_traj h_stepsize_antitone k
  have hprefix :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) ≤
        B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
    exact mirrorCShiftedGapPrefixSum_le
      (f := f) (g := g) (ω := ω) (XStar := XStar) (FOpt := FOpt) (σ := σ)
      (x := x) (s := s) (t := t) h_problem hω hω_diff h_traj hxStar k
  calc
    Finset.sum (Finset.range (k + 1))
        (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) ≤
      (t 0) * (g (x 0)).toReal +
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) := hshifted
    _ ≤
      (t 0) * (g (x 0)).toReal +
        (B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left hprefix ((t 0) * (g (x 0)).toReal)
    _ =
      (t 0) * (g (x 0)).toReal +
        B[ω] xStar (x 0) +
        (1 / (2 * σ)) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
            ring

-- Proof sketch: apply `mirror_c_weighted_objective_gap_sum_le`, use the prefix-minimality of
-- `best_achieved_function_value` to bound each composite objective gap below by the running-best
-- gap, and divide by the positive prefix sum supplied by `h_traj.stepsize_pos`.
/-- Lemma 9.25: under the composite convex minimization assumptions extracted from Definition 9.4,
together with the mirror-map assumptions of Definition 9.5 and the Mirror-C trajectory data of
Definition 9.6, if `g` is nonnegative on `dom(g)` and the Mirror-C stepsizes are nonincreasing,
then for every optimal point `xStar ∈ XStar = X^*` and every iteration index `k`, the
running-best composite objective gap up to time `k` is bounded by the weighted ratio
`(t₀ g(x⁰) + B_ω(xStar, x⁰) + (1 / (2σ)) * ∑_{n=0}^k t_n^2 ‖f'(x^n)‖^2) / ∑_{n=0}^k t_n`. -/
theorem mirror_c_best_value_gap_le
    (h_problem : IsCompositeConvexMinimizationProblem f g XStar FOpt)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (h_stepsize_antitone : Antitone t)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    best_achieved_function_value (fun y ↦ (f y + g y).toReal) x k - FOpt ≤
      ((t 0) * (g (x 0)).toReal +
        B[ω] xStar (x 0) +
        (1 / (2 * σ)) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))) /
        Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := by
  let bestGap := best_achieved_function_value (fun y ↦ (f y + g y).toReal) x k - FOpt
  let prefixSum := Finset.sum (Finset.range (k + 1)) (fun n ↦ t n)
  let numerator :=
    (t 0) * (g (x 0)).toReal +
      B[ω] xStar (x 0) +
      (1 / (2 * σ)) *
        Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))
  -- The initial positive stepsize already appears in every prefix sum.
  have h0_mem : 0 ∈ Finset.range (k + 1) := by
    simp
  have hprefix_ge : t 0 ≤ prefixSum := by
    dsimp [prefixSum]
    simpa using
      (Finset.single_le_sum (fun n _ ↦ le_of_lt (h_traj.stepsize_pos n)) h0_mem)
  have hprefix_pos : 0 < prefixSum := by
    exact lt_of_lt_of_le (h_traj.stepsize_pos 0) hprefix_ge
  have hpointwise :
      ∀ n ∈ Finset.range (k + 1),
        t n * bestGap ≤ t n * ((f (x n) + g (x n)).toReal - FOpt) := by
    intro n hn
    have hbest_le :
        best_achieved_function_value (fun y ↦ (f y + g y).toReal) x k ≤
          (f (x n) + g (x n)).toReal := by
      exact best_achieved_function_value_le_objective_value
        (fun y ↦ (f y + g y).toReal) x k n hn
    have hgap_le : bestGap ≤ (f (x n) + g (x n)).toReal - FOpt := by
      dsimp [bestGap]
      linarith
    exact mul_le_mul_of_nonneg_left hgap_le (le_of_lt (h_traj.stepsize_pos n))
  have hsum_best :
      Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * bestGap) ≤
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) := by
    exact Finset.sum_le_sum hpointwise
  have hsum_best_eq :
      Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * bestGap) = prefixSum * bestGap := by
    dsimp [prefixSum]
    rw [Finset.sum_mul]
  have hweighted :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) ≤
        numerator := by
    exact mirror_c_weighted_objective_gap_sum_le
      (f := f) (g := g) (ω := ω) (XStar := XStar) (FOpt := FOpt) (σ := σ)
      (x := x) (s := s) (t := t) h_problem hω hω_diff h_nonneg h_traj
      h_stepsize_antitone hxStar k
  have hscaled : prefixSum * bestGap ≤ numerator := by
    calc
      prefixSum * bestGap =
        Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * bestGap) := by
          symm
          exact hsum_best_eq
      _ ≤
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) := hsum_best
      _ ≤ numerator := hweighted
  have hscaled' : bestGap * prefixSum ≤ numerator := by
    simpa [mul_comm] using hscaled
  have hscaled'' :
      (best_achieved_function_value (fun y ↦ (f y + g y).toReal) x k - FOpt) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) ≤
        ((t 0) * (g (x 0)).toReal +
          B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))) := by
    simpa [bestGap, prefixSum, numerator, mul_comm, mul_left_comm, mul_assoc] using hscaled'
  exact (le_div_iff₀ hprefix_pos).2 hscaled''

end
