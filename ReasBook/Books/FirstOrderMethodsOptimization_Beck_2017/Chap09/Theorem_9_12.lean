/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Theorem_9_12.Objective
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Theorem_9_12.Linearized
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_18
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

noncomputable section

open Filter
open InnerProductSpace (toDualMap)
open scoped Pointwise Topology Gradient

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ψ ω : E → EReal} {σ : ℝ} {a b : E}
variable (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
variable (hω_diff : ∀ x ∈ subdifferential_domain ω,
  DifferentiableAt ℝ (fun z ↦ (ω z).toReal) x)
variable (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_convex : is_convex_function ψ)
variable (hb : b ∈ subdifferential_domain ω)
variable (ha : IsMinOn (secondProxObjective ψ ω b) Set.univ a)

include hω hω_diff hψ_proper hb ha
include hψ_convex

/- Theorem 9.12 is `source-facing`. Its second-prox objective is the item-owned core construction
`secondProxObjective`, while `IsBregmanPotentialOn ω (effective_domain ψ) σ` supplies the
standing Bregman-potential assumptions. The source's ambient differentiability requirement is
kept separately as `hω_diff`, since differentiability within `dom(∂ω)` does not imply
`DifferentiableAt` there. Its two conclusions have independent companions for downstream use and
a combined `..._spec` theorem matching the source statement. Closedness of `ψ` is not needed for
this optimality conclusion. The theorem needs the relative-interior
qualification used by Lemma 9.7 after the affine perturbation of `ψ`; the bare Bregman-potential
assumptions do not control subdifferentiability at boundary minimizers. -/

namespace SecondProxObjective

omit hω hω_diff hψ_convex hb ha in
/-- Helper for Theorem 9.12 default GPT-5.4 high proof-only after final statement repair: the
affine-perturbed penalty `x ↦ ψ x - ⟪∇ω(b), x⟫` is convex whenever `ψ` is convex. -/
private theorem affinePerturbedPenalty_isConvex
    (hψConvex : is_convex_function ψ) :
    is_convex_function (affinePerturbedPenalty ψ ω b) := by
  let aω : StrongDual ℝ E := InnerProductSpace.toDual ℝ E (-∇ (fun z ↦ (ω z).toReal) b)
  have hlinearConvex : ConvexOn ℝ Set.univ (fun x : E ↦ aω x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ α β hα hβ hαβ
    refine le_of_eq ?_
    simp [smul_eq_mul, map_add]
  have hlinearConvexEReal :
      is_convex_function (fun x : E ↦ ((aω x : ℝ) : EReal)) :=
    Function.toEReal_isConvexFunction hlinearConvex
  have hlinearNeBot : ∀ x : E, ((aω x : ℝ) : EReal) ≠ ⊥ := by
    intro x
    simp
  have hsumConvex :=
    is_convex_function_pointwise_add
      hψConvex hlinearConvexEReal hψ_proper.ne_bot hlinearNeBot
  -- Rewrite the generic affine perturbation back to the item-owned owner notation.
  simpa [affinePerturbedPenalty, aω, Pi.add_apply,
    InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hsumConvex

omit hω_diff hb in
/-- Domain companion for Theorem 9.12: a second-prox minimizer lies in both `dom(ψ)` and
`dom(∂ω)`. This domain conclusion does not require differentiability of `ω.toReal` or the
base-point hypothesis. The relative-interior qualification is the exact-sum-rule condition that
excludes unsupported boundary minimizers. -/
theorem minimizer_mem_domains
    (hqual : (intrinsicInterior ℝ (effective_domain ψ) ∩
      intrinsicInterior ℝ (effective_domain ω)).Nonempty) :
    a ∈ effective_domain ψ ∩ subdifferential_domain ω := by
  have hlin :
      IsMinOn (linearizedSecondProxObjective ψ ω b) Set.univ a :=
    SecondProxObjective.isMinOn_linearized ψ ω b a ha
  have hωAff :
      IsBregmanPotentialOn ω (effective_domain (affinePerturbedPenalty ψ ω b)) σ := by
    simpa [AffinePerturbedPenalty.effectiveDomain ψ ω b] using hω
  have hqualAff :
      (intrinsicInterior ℝ (effective_domain (affinePerturbedPenalty ψ ω b)) ∩
          intrinsicInterior ℝ (effective_domain ω)).Nonempty := by
    simpa [AffinePerturbedPenalty.effectiveDomain ψ ω b] using hqual
  have hcomp :
      IsMinOn (fun x ↦ affinePerturbedPenalty ψ ω b x + ω x) Set.univ a := by
    -- Normalize the second-prox objective to the affine-perturbed composite owner from Lemma 9.7.
    simpa [LinearizedSecondProxObjective.eq_affinePerturbed_add ψ ω b hω] using hlin
  have hdomains :
      a ∈ effective_domain (affinePerturbedPenalty ψ ω b) ∩ subdifferential_domain ω :=
    composite_minimizer_mem_domains hωAff
      (AffinePerturbedPenalty.proper ψ ω b hψ_proper)
      (affinePerturbedPenalty_isConvex
        (ψ := ψ) (ω := ω) (b := b) hψ_proper hψ_convex) hqualAff hcomp
  -- Undo the affine-perturbation domain normalization.
  simpa [AffinePerturbedPenalty.effectiveDomain ψ ω b] using hdomains

omit hω_diff hb in
/-- Helper for Theorem 9.12 default GPT-5.4 high proof-only after final statement repair: a
minimizer of the normalized affine-perturbed composite objective yields explicit split
subgradients whose sum is zero. -/
private theorem existsZeroSplitSubgradientOfAffinePerturbedCompositeMinimizer
    (hqual : (intrinsicInterior ℝ (effective_domain ψ) ∩
      intrinsicInterior ℝ (effective_domain ω)).Nonempty) :
    ∃ ηψ ηω : Module.Dual ℝ E,
      ηψ ∈ ∂ (affinePerturbedPenalty ψ ω b)(a) ∧
      ηω ∈ ∂ω(a) ∧
      ηψ + ηω = (0 : Module.Dual ℝ E) := by
  let hψAff := AffinePerturbedPenalty.proper ψ ω b hψ_proper
  have hlin :
      IsMinOn (linearizedSecondProxObjective ψ ω b) Set.univ a :=
    SecondProxObjective.isMinOn_linearized ψ ω b a ha
  have hωAff :
      IsBregmanPotentialOn ω (effective_domain (affinePerturbedPenalty ψ ω b)) σ := by
    simpa [AffinePerturbedPenalty.effectiveDomain ψ ω b] using hω
  have hqualAff :
      (intrinsicInterior ℝ (effective_domain (affinePerturbedPenalty ψ ω b)) ∩
          intrinsicInterior ℝ (effective_domain ω)).Nonempty := by
    simpa [AffinePerturbedPenalty.effectiveDomain ψ ω b] using hqual
  have hcomp :
      IsMinOn (fun x ↦ affinePerturbedPenalty ψ ω b x + ω x) Set.univ a := by
    -- Normalize the second-prox objective to the affine-perturbed composite owner.
    simpa [LinearizedSecondProxObjective.eq_affinePerturbed_add ψ ω b hω] using hlin
  have hcompDom :
      (effective_domain (fun x ↦ affinePerturbedPenalty ψ ω b x + ω x)).Nonempty := by
    rcases hψAff.effective_domain_nonempty with ⟨x, hxAff⟩
    have hxω : x ∈ effective_domain ω := hωAff.subset_effective_domain hxAff
    refine ⟨x, ?_⟩
    exact mem_effective_domain.mpr <|
      EReal.add_lt_top (ne_of_lt (mem_effective_domain.mp hxAff))
        (ne_of_lt (mem_effective_domain.mp hxω))
  have hzero :
      (0 : Module.Dual ℝ E) ∈
        ∂ (fun x ↦ affinePerturbedPenalty ψ ω b x + ω x)(a) := by
    -- Fermat converts global minimality of the normalized objective into a zero subgradient.
    exact
      (isMinOn_univ_iff_zero_mem_subdifferential
        (f := fun x ↦ affinePerturbedPenalty ψ ω b x + ω x) hcompDom).mp hcomp
  let F : Fin 2 → E → EReal := fun i =>
    match i with
    | 0 => affinePerturbedPenalty ψ ω b
    | 1 => ω
  have hneBot : ∀ i : Fin 2, ∀ y : E, F i y ≠ ⊥ := by
    intro i y
    fin_cases i
    · simpa [F] using hψAff.ne_bot y
    · simpa [F] using hω.ne_bot y
  have hconvF : ∀ i : Fin 2, is_convex_function (F i) := by
    intro i
    fin_cases i
    · simpa [F] using
        affinePerturbedPenalty_isConvex
          (ψ := ψ) (ω := ω) (b := b) hψ_proper hψ_convex
    · simpa [F] using hω.convex
  have hqualF :
      (⋂ i : Fin 2, intrinsicInterior ℝ (effective_domain (F i))).Nonempty := by
    rcases hqualAff with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    -- Repackage the binary qualification in the finite-family surface used by the exact sum rule.
    simp only [Set.mem_iInter]
    intro i
    fin_cases i
    · simpa [F] using hx.1
    · simpa [F] using hx.2
  have hsumBase :
      subdifferential (fun y ↦ ∑ i : Fin 2, F i y) a =
        ∑ i : Fin 2, ∂ (F i)(a) :=
    subdifferential_finset_sum_eq_sum_subdifferential_of_nonempty_iInter_relativeInterior
      (E := E) (ι := Fin 2) (f := F) (x := a) hneBot hconvF hqualF
  have hsumLeft :
      (fun y ↦ ∑ i : Fin 2, F i y) =
        (fun y ↦ affinePerturbedPenalty ψ ω b y + ω y) := by
    funext y
    simp [F, Fin.sum_univ_two]
  have hsumRight :
      (∑ i : Fin 2, ∂ (F i)(a)) =
        ∂ (affinePerturbedPenalty ψ ω b)(a) + ∂ω(a) := by
    simp [F, Fin.sum_univ_two]
  have hzeroSplit :
      (0 : Module.Dual ℝ E) ∈
        ∂ (affinePerturbedPenalty ψ ω b)(a) + ∂ω(a) := by
    have hzeroFamily :
        (0 : Module.Dual ℝ E) ∈ subdifferential (fun y ↦ ∑ i : Fin 2, F i y) a := by
      simpa [hsumLeft] using hzero
    -- Rewrite the normalized composite subdifferential through the qualified binary exact sum rule.
    rw [← hsumRight, ← hsumBase]
    exact hzeroFamily
  rw [Set.mem_add] at hzeroSplit
  rcases hzeroSplit with ⟨ηψ, hηψ, ηω, hηω, hsum⟩
  exact ⟨ηψ, ηω, hηψ, hηω, hsum⟩

omit hω hω_diff hψ_proper hψ_convex hb ha in
/-- Helper for Theorem 9.12 default GPT-5.4 high proof-only after final statement repair: a
subgradient of the affine-perturbed penalty transports to a `ψ`-subgradient after restoring the
fixed linear term based at `b`. -/
private theorem memSubdifferential_of_memAffinePerturbedPenaltySubdifferential
    {η : Module.Dual ℝ E}
    (hη : η ∈ ∂(affinePerturbedPenalty ψ ω b)(a)) :
    η + (toDualMap ℝ E (∇ (fun z ↦ (ω z).toReal) b) : Module.Dual ℝ E) ∈ ∂ ψ(a) := by
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hη ⊢
  refine ⟨?_, ?_⟩
  · -- The affine perturbation leaves the penalty effective domain unchanged.
    simpa [AffinePerturbedPenalty.effectiveDomain ψ ω b] using hη.1
  · intro u hu
    let ξ : Module.Dual ℝ E := toDualMap ℝ E (∇ (fun z ↦ (ω z).toReal) b)
    have huAff : u ∈ effective_domain (affinePerturbedPenalty ψ ω b) := by
      simpa [AffinePerturbedPenalty.effectiveDomain ψ ω b] using hu
    have hbase :
        affinePerturbedPenalty ψ ω b a + (η (u - a) : EReal) ≤
          affinePerturbedPenalty ψ ω b u := by
      simpa [ge_iff_le] using hη.2 u huAff
    have hshift :
        affinePerturbedPenalty ψ ω b a + (η (u - a) : EReal) +
            (((toDualMap ℝ E (∇ (fun z ↦ (ω z).toReal) b) u : ℝ)) : EReal) ≤
          affinePerturbedPenalty ψ ω b u +
            (((toDualMap ℝ E (∇ (fun z ↦ (ω z).toReal) b) u : ℝ)) : EReal) := by
      exact (EReal.addLECancellable_coe
        ((toDualMap ℝ E (∇ (fun z ↦ (ω z).toReal) b)) u)).add_le_add_iff_right.mpr hbase
    have hpair :
        ((η + ξ) (u - a) : ℝ) = η (u - a) + ξ u - ξ a := by
      have hξsub : ξ (u - a) = ξ u - ξ a := map_sub ξ u a
      simpa [map_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        congrArg (fun t : ℝ ↦ η u - η a + t) hξsub
    have hrestored :
        ψ a + (((η + ξ) (u - a) : ℝ) : EReal) ≤
          ψ u := by
      calc
        ψ a + (((η + ξ) (u - a) : ℝ) : EReal)
            = ψ a + (((η (u - a) + ξ u - ξ a : ℝ)) : EReal) := by rw [hpair]
        _ = affinePerturbedPenalty ψ ω b a + (η (u - a) : EReal) + ((ξ u : ℝ) : EReal) := by
          simp [affinePerturbedPenalty, ξ, EReal.coe_add, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm]
        _ ≤ affinePerturbedPenalty ψ ω b u + ((ξ u : ℝ) : EReal) := hshift
        _ = ψ u + (((-ξ u : ℝ)) : EReal) + ((ξ u : ℝ) : EReal) := by
          simp [affinePerturbedPenalty, ξ, add_left_comm, add_comm]
        _ = ψ u + 0 := by
          have hcancel : (((-ξ u : ℝ)) : EReal) + ((ξ u : ℝ) : EReal) = 0 := by
            rw [← EReal.coe_add]
            norm_num
          rw [add_assoc]
          rw [hcancel]
        _ = ψ u := by simp
    simpa [ge_iff_le, ξ, InnerProductSpace.toDualMap_apply_apply, map_sub] using hrestored

omit hψ_proper hψ_convex hb ha in
/-- Helper for Theorem 9.12 default GPT-5.4 high proof-only after final statement repair: any
`ω`-subgradient at `a` is bounded above by the differentiable gradient pairing on feasible
displacements `u - a`. -/
private theorem omegaSubgradientPairing_le_gradientPairing_onEffectiveDomain
    {ηω : Module.Dual ℝ E}
    (haω : a ∈ subdifferential_domain ω)
    (hηω : ηω ∈ ∂ω(a)) (u : E) (hu : u ∈ effective_domain ψ) :
    ηω (u - a) ≤ inner ℝ (∇ (fun z ↦ (ω z).toReal) a) (u - a) := by
  let line : ℝ → E := fun t ↦ (1 - t) • a + t • u
  have haEff : a ∈ effective_domain ω :=
    subdifferential_domain_subset_effective_domain haω
  have huω : u ∈ effective_domain ω := hω.subset_effective_domain hu
  have hlineDeriv :
      HasLineDerivAt ℝ (fun z ↦ (ω z).toReal)
        (inner ℝ (∇ (fun z ↦ (ω z).toReal) a) (u - a)) a (u - a) := by
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
      (hω_diff a haω).hasGradientAt.hasFDerivAt.hasLineDerivAt (u - a)
  have hquotTendsto :
      Tendsto (fun t : ℝ ↦ ((ω (line t)).toReal - (ω a).toReal) / t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (∇ (fun z ↦ (ω z).toReal) a) (u - a))) := by
    simpa [line, sub_eq_add_neg, add_smul, smul_sub, add_comm, add_left_comm, add_assoc,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hlineDeriv.tendsto_slope_zero_right
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := by
    simpa [Set.mem_Ioi] using
      (eventually_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Set.Ioi (0 : ℝ))
  have hlt1 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 := by
    simpa [Set.mem_Iio] using
      (show Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) from
        nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  have hpointwise :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ηω (u - a) ≤ ((ω (line t)).toReal - (ω a).toReal) / t := by
    filter_upwards [hpos, hlt1] with t htpos ht1
    have hlineω : line t ∈ effective_domain ω := by
      have hseg :
          t • u + (1 - t) • a ∈ effective_domain ω :=
        combo_mem_effective_domain_of_is_convex_function hω.convex huω haEff
          ⟨htpos.le, ht1.le⟩
      simpa [line, add_comm, add_left_comm, add_assoc] using hseg
    have hsub_t :
        ηω (line t - a) ≤ (ω (line t)).toReal - (ω a).toReal :=
      subgradient_eval_le_toReal_sub ω a (line t)
        (fun z _ ↦ hω.ne_bot z) haEff hlineω hηω
    have hline_sub : line t - a = t • (u - a) := by
      dsimp [line]
      calc
        ((1 - t) • a + t • u) - a
            = ((1 - t) • a + t • u) + (-1 : ℝ) • a := by
                simp [sub_eq_add_neg]
        _ = t • (u - a) := by
                simp [sub_eq_add_neg, smul_add, add_smul, add_left_comm, add_comm]
                abel_nf
    rw [hline_sub, map_smul, smul_eq_mul] at hsub_t
    exact (le_div_iff₀ htpos).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsub_t)
  -- Pass the one-sided subgradient bound to the right-limit and identify the derivative.
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hquotTendsto hpointwise

/-- First-order companion to Theorem 9.12: under the intrinsic-interior qualification, for convex
`ψ`, once the minimizer is known to lie in `dom(∂ω)`, every `u ∈ dom(ψ)` satisfies (9.16). -/
theorem optimality_ineq
    (hqual : (intrinsicInterior ℝ (effective_domain ψ) ∩
      intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    (haω : a ∈ subdifferential_domain ω) (u : E) (hu : u ∈ effective_domain ψ) :
    inner ℝ
      (∇ (fun x ↦ (ω x).toReal) b - ∇ (fun x ↦ (ω x).toReal) a) (u - a) ≤
      ψ u - ψ a := by
  let gb : Module.Dual ℝ E :=
    toDualMap ℝ E (∇ (fun z ↦ (ω z).toReal) b)
  have haψ : a ∈ effective_domain ψ :=
    (minimizer_mem_domains hω hψ_proper hψ_convex ha hqual).1
  obtain ⟨ηψ, ηω, hηψ, hηω, hsum⟩ :=
    existsZeroSplitSubgradientOfAffinePerturbedCompositeMinimizer
      (hω := hω) (hψ_proper := hψ_proper) (hψ_convex := hψ_convex) (ha := ha) hqual
  have hψSub :
      ηψ + gb ∈ ∂ ψ(a) :=
    memSubdifferential_of_memAffinePerturbedPenaltySubdifferential
      (ψ := ψ) (ω := ω) (b := b) hηψ
  have hsumEval : ηψ (u - a) + ηω (u - a) = 0 := by
    simpa [Pi.add_apply] using congrArg (fun ξ : Module.Dual ℝ E ↦ ξ (u - a)) hsum
  have hpsi_real :
      inner ℝ (∇ (fun z ↦ (ω z).toReal) b) (u - a) - ηω (u - a) ≤
        (ψ u).toReal - (ψ a).toReal := by
    have hsub :=
      subgradient_eval_le_toReal_sub ψ a u
        (fun z _ ↦ hψ_proper.ne_bot z) haψ hu hψSub
    have hsub' :
        ηψ (u - a) + inner ℝ (∇ (fun z ↦ (ω z).toReal) b) (u - a) ≤
          (ψ u).toReal - (ψ a).toReal := by
      simpa [gb, Pi.add_apply, InnerProductSpace.toDualMap_apply_apply] using hsub
    have hsumEval' : ηψ (u - a) = -ηω (u - a) := by
      linarith
    rw [hsumEval'] at hsub'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub'
  have hωpair :
      ηω (u - a) ≤
        inner ℝ (∇ (fun z ↦ (ω z).toReal) a) (u - a) :=
    omegaSubgradientPairing_le_gradientPairing_onEffectiveDomain
      (hω := hω) (hω_diff := hω_diff) haω hηω u hu
  have hfinal_real :
      inner ℝ (∇ (fun x ↦ (ω x).toReal) b) (u - a) -
          inner ℝ (∇ (fun x ↦ (ω x).toReal) a) (u - a) ≤
        (ψ u).toReal - (ψ a).toReal := by
    linarith
  have hfinal_real' :
      inner ℝ
        (∇ (fun x ↦ (ω x).toReal) b - ∇ (fun x ↦ (ω x).toReal) a) (u - a) ≤
        (ψ u).toReal - (ψ a).toReal := by
    simpa [inner_sub_left] using hfinal_real
  have hu_top : ψ u ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hu)
  have ha_top : ψ a ≠ ⊤ := ne_of_lt (mem_effective_domain.mp haψ)
  have hu_eq : ψ u = (((ψ u).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hu_top (hψ_proper.ne_bot u)).symm
  have ha_eq : ψ a = (((ψ a).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal ha_top (hψ_proper.ne_bot a)).symm
  have hfinal_ereal :
      (((inner ℝ
          (∇ (fun x ↦ (ω x).toReal) b - ∇ (fun x ↦ (ω x).toReal) a) (u - a)) : ℝ) :
          EReal) ≤
        (((ψ u).toReal : ℝ) : EReal) - (((ψ a).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_sub] using (EReal.coe_le_coe hfinal_real')
  rw [hu_eq, ha_eq]
  exact hfinal_ereal

omit hω_diff hb in
/-- Companion for Theorem 9.12: a second-prox minimizer lies in the subdifferential domain of the
Bregman potential. -/
theorem minimizer_mem_subdifferential_domain
    (hqual : (intrinsicInterior ℝ (effective_domain ψ) ∩
      intrinsicInterior ℝ (effective_domain ω)).Nonempty) :
    a ∈ subdifferential_domain ω :=
  (minimizer_mem_domains hω hψ_proper hψ_convex ha hqual).2

/-- Theorem 9.12: under the intrinsic-interior qualification, a minimizer of
`secondProxObjective ψ ω b` lies in `dom(∂ω)` and satisfies the variational inequality (9.16) at
every point of `dom(ψ)`. -/
theorem minimizer_spec
    (hqual : (intrinsicInterior ℝ (effective_domain ψ) ∩
      intrinsicInterior ℝ (effective_domain ω)).Nonempty) :
    a ∈ subdifferential_domain ω ∧
      ∀ u ∈ effective_domain ψ,
        inner ℝ
          (∇ (fun x ↦ (ω x).toReal) b - ∇ (fun x ↦ (ω x).toReal) a) (u - a) ≤
          ψ u - ψ a := by
  have haω :=
    minimizer_mem_subdifferential_domain hω hψ_proper hψ_convex ha hqual
  constructor
  · exact haω
  · intro u hu
    exact optimality_ineq hω hω_diff hψ_proper hψ_convex hb ha hqual haω u hu

/-- Companion for Theorem 9.12: under the intrinsic-interior qualification, for convex `ψ`, the
cancellation-safe add form of the second-prox variational inequality. -/
theorem optimality_add
    (hqual : (intrinsicInterior ℝ (effective_domain ψ) ∩
      intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    (haω : a ∈ subdifferential_domain ω) (u : E) (hu : u ∈ effective_domain ψ) :
    inner ℝ
      (∇ (fun x ↦ (ω x).toReal) b - ∇ (fun x ↦ (ω x).toReal) a) (u - a) +
      ψ a ≤ ψ u := by
  apply (EReal.le_sub_iff_add_le
    (.inl (hψ_proper.ne_bot a))
    (.inl (mem_effective_domain.mp
      (minimizer_mem_effective_domain hψ_proper ha)).ne)).1
  exact optimality_ineq hω hω_diff hψ_proper hψ_convex hb ha hqual haω u hu

/-- Canonical companion for Theorem 9.12: under the intrinsic-interior qualification, for convex
`ψ`, a minimizer of `secondProxObjective ψ ω b` has the subgradient certificate induced by
`∇ω(b) - ∇ω(a)`. -/
theorem gradient_mem_subdifferential
    (hqual : (intrinsicInterior ℝ (effective_domain ψ) ∩
      intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    (haω : a ∈ subdifferential_domain ω) :
    (toDualMap ℝ E
      (∇ (fun x ↦ (ω x).toReal) b - ∇ (fun x ↦ (ω x).toReal) a) : Module.Dual ℝ E) ∈
      ∂ ψ(a) := by
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨minimizer_mem_effective_domain hψ_proper ha, ?_⟩
  intro u hu
  simpa [ge_iff_le, add_comm, inner_sub_left, EReal.coe_sub] using
    optimality_add hω hω_diff hψ_proper hψ_convex hb ha hqual haω u hu

end SecondProxObjective

end

#print SecondProxObjective.optimality_ineq
#print SecondProxObjective.optimality_add
#print SecondProxObjective.minimizer_spec
