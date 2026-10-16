module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.SmoothCycle
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

open Set Filter
open scoped Topology RealInnerProductSpace

namespace ConsensusADMM.SmoothRealization

variable {N : ℕ} [NeZero N] {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth realization certificate for a finite strictly supported family. -/
structure Interpolates (p n : ZMod N → E) (f : E → ℝ) where
  modulus : ℝ
  level : ℝ
  constant : NNReal
  modulus_pos : 0 < modulus
  level_pos : 0 < level
  stronglyConvex : StrongConvexOn univ modulus f
  contDiff : ContDiff ℝ 1 f
  lipschitz : LipschitzWith constant (fderiv ℝ f)
  zero : f 0 = 0
  derivative_zero : HasFDerivAt f (0 : E →L[ℝ] ℝ) 0
  lower : ∀ x, modulus / 2 * ‖x‖ ^ 2 ≤ f x
  values : ∀ i, f (p i) = level
  supports : ∀ i x, f (p i) + ⟪n i, x - p i⟫ ≤ f x

/-- Taking half the minimum self-product gives a common positive interpolation
level without assuming any cyclic orthogonal symmetry. -/
theorem exists_interpolates (p n : ZMod N → E)
    (supports : ProjectionCycle.StrictNonselfSupports p n) :
    ∃ f : E → ℝ, Nonempty (Interpolates p n f) := by
  classical
  obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun i : ZMod N ↦ ⟪n i, p i⟫) Finset.univ_nonempty
  let a : ℝ := ⟪n i₀, p i₀⟫ / 2
  have ha : 0 < a := half_pos (supports i₀).1
  have hab (i : ZMod N) : a < ⟪n i, p i⟫ :=
    (half_lt_self (supports i₀).1).trans_le (hmin i (Finset.mem_univ i))
  let z : Option (ZMod N) → E := Option.elim' 0 p
  let q : Option (ZMod N) → E := Option.elim' 0 n
  let φ : Option (ZMod N) → ℝ := Option.elim' 0 (fun _ ↦ a)
  have hstrict (i j : Option (ZMod N)) (hij : i ≠ j) :
      0 < φ i - φ j - ⟪q j, z i - z j⟫ := by
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        simp only [φ, q, z, Option.elim', zero_sub, inner_neg_right]
        linarith [hab j]
    | some i =>
      cases j with
      | none =>
        simpa only [φ, q, z, Option.elim', sub_zero, inner_zero_left] using ha
      | some j =>
        have hs := (supports j).2 i (fun h ↦ hij (congrArg some h))
        simp only [φ, q, z, Option.elim', sub_self, zero_sub, inner_sub_right]
        simp only [inner_sub_right] at hs
        linarith
  obtain ⟨f, μ, L, hf⟩ := SmoothInterpolation.exists_strongInterpolation z q φ none
    rfl rfl rfl hstrict
  exact ⟨f, ⟨⟨μ, a, L, hf.positive, ha, hf.stronglyConvex, hf.contDiff,
    hf.lipschitz, hf.zero, hf.origin_derivative, hf.lower,
    fun i ↦ hf.values (some i), fun i x ↦ hf.supports (some i) x⟩⟩⟩

/-- Every quadratic augmented objective has a unique real minimizer. The
quadratic coercivity certificate controls arbitrary centers and multipliers. -/
theorem exists_unique_augmented (f : E → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hc : Continuous f) (hs : StrongConvexOn univ μ f) (h0 : f 0 = 0)
    (hl : ∀ x, μ / 2 * ‖x‖ ^ 2 ≤ f x) (center dual : E) :
    ∃! p, ∀ z,
      f p + (⟪dual, p - center⟫ + ‖p - center‖ ^ 2 / 2) ≤
        f z + (⟪dual, z - center⟫ + ‖z - center‖ ^ 2 / 2) := by
  let H : E → ℝ := fun x ↦ f x + ‖x‖ ^ 2 / 2
  have hH : SmoothInterpolation.QuadraticCore H (μ + 1) := by
    refine ⟨by positivity, hc.add ((continuous_norm.pow 2).div_const 2), ?_, ?_, ?_⟩
    · rw [strongConvexOn_iff_convex] at hs ⊢
      convert hs using 1
      ext x
      dsimp [H]
      ring
    · simp [H, h0]
    · intro x
      dsimp [H]
      linarith [hl x]
  obtain ⟨p, hp⟩ := hH.exists_minimizer (center - dual)
  have identity (x : E) :
      f x + (⟪dual, x - center⟫ + ‖x - center‖ ^ 2 / 2) =
        H x - ⟪center - dual, x⟫ + (‖center‖ ^ 2 / 2 - ⟪dual, center⟫) := by
    dsimp [H]
    rw [inner_sub_right, inner_sub_left, norm_sub_sq_real, real_inner_comm x center]
    ring
  refine ⟨p, ?_, ?_⟩
  · intro z
    simpa only [identity, add_le_add_iff_right] using hp z
  · intro z hz
    have hzp : H z - ⟪center - dual, z⟫ ≤ H p - ⟪center - dual, p⟫ := by
      simpa only [identity, add_le_add_iff_right] using hz p
    have bound := SmoothInterpolation.strong_minimum_bound
      (hH.tilt_stronglyConvex (center - dual)) hp z
    have hn : ‖z - p‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖z - p‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

/-- The real augmented minimizer is finite and uniquely minimizes its extended
real lift, including among all ambient-space inputs. -/
theorem exists_unique_augmented_ofReal (f : E → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hc : Continuous f) (hs : StrongConvexOn univ μ f) (h0 : f 0 = 0)
    (hl : ∀ x, μ / 2 * ‖x‖ ^ 2 ≤ f x) (center dual : E) :
    ∃! p, ofReal f p ≠ ⊤ ∧ ofReal f p ≠ ⊥ ∧ ∀ z,
      ofReal f p + ((⟪dual, p - center⟫ + ‖p - center‖ ^ 2 / 2 : ℝ) : EReal) ≤
        ofReal f z + ((⟪dual, z - center⟫ + ‖z - center‖ ^ 2 / 2 : ℝ) : EReal) := by
  obtain ⟨p, hp, hu⟩ := exists_unique_augmented f μ hμ hc hs h0 hl center dual
  refine ⟨p, ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _, ?_⟩, ?_⟩
  · intro z
    simpa only [ofReal_apply, ← EReal.coe_add, EReal.coe_le_coe_iff] using hp z
  · intro z hz
    apply hu z
    simpa only [ofReal_apply, ← EReal.coe_add, EReal.coe_le_coe_iff] using hz.2.2

/-- At a differentiable stationary origin, the only global supporting normal
is zero. This identifies the multiplier as well as the primal KKT point. -/
theorem supporting_normal_at_origin_eq_zero {f : E → ℝ} {q : E}
    (hf : HasFDerivAt f (0 : E →L[ℝ] ℝ) 0)
    (hs : ∀ z, f 0 + ⟪q, z⟫ ≤ f z) : q = 0 := by
  have hmin : IsLocalMin (fun z ↦ f z - ⟪q, z⟫) 0 := by
    apply Filter.Eventually.of_forall
    intro z
    simp only [inner_zero_right, sub_zero]
    linarith [hs z]
  have hd : HasFDerivAt (fun z ↦ f z - ⟪q, z⟫)
      (-(innerSL ℝ q)) 0 := by
    convert hf.sub ((innerSL ℝ q).hasFDerivAt) using 1 <;>
      first | rfl | simp only [zero_sub]
  have hzero := hmin.hasFDerivAt_eq_zero hd
  have hq := DFunLike.congr_fun hzero q
  have hnorm : ‖q‖ ^ 2 = 0 := by
    simpa only [ContinuousLinearMap.neg_apply, innerSL_apply_apply,
      ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq, neg_eq_zero] using hq
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

end ConsensusADMM.SmoothRealization
