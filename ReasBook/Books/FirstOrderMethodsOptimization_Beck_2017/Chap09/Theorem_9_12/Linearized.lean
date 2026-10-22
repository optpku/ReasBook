/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Theorem_9_12.Objective
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import Mathlib.Analysis.Convex.Deriv

noncomputable section

open scoped Gradient

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ψ ω : E → EReal} {a b : E}

/-- The linearized second-prox objective obtained from `x ↦ ψ x + B[ω] x b` by removing the
`x`-independent constant term. -/
def linearizedSecondProxObjective (ψ ω : E → EReal) (b : E) : E → EReal :=
  fun x ↦
    ψ x +
      ((ω x).toReal - inner ℝ (∇ (fun z ↦ (ω z).toReal) b) x : ℝ)

/-- The affine perturbation of `ψ` by the linear functional `x ↦ -⟪∇ω(b), x⟫`. -/
def affinePerturbedPenalty (ψ ω : E → EReal) (b : E) : E → EReal :=
  fun x ↦ ψ x + (((-inner ℝ (∇ (fun z ↦ (ω z).toReal) b) x : ℝ)) : EReal)

namespace SecondProxObjective

/-- The second-prox objective is the linearized objective plus an `x`-independent constant. -/
lemma eq_linearized_add_const
    (ψ ω : E → EReal) (b x : E) :
    secondProxObjective ψ ω b x =
      linearizedSecondProxObjective ψ ω b x +
        (((inner ℝ (∇ (fun z ↦ (ω z).toReal) b) b - (ω b).toReal : ℝ)) : EReal) := by
  -- Expand the Bregman term and collect the `x`-dependent part into the linearized objective.
  rw [SecondProxObjective.apply, bregmanDistance_def, linearizedSecondProxObjective]
  have hreal :
      (ω x).toReal - (ω b).toReal - inner ℝ (∇ (fun z ↦ (ω z).toReal) b) (x - b) =
        ((ω x).toReal - inner ℝ (∇ (fun z ↦ (ω z).toReal) b) x) +
          (inner ℝ (∇ (fun z ↦ (ω z).toReal) b) b - (ω b).toReal) := by
    rw [inner_sub_right]
    ring
  rw [hreal, EReal.coe_add]
  simp [add_left_comm, add_comm]

/-- A minimizer of the second-prox objective is also a minimizer of the linearized objective. -/
lemma isMinOn_linearized
    (ψ ω : E → EReal) (b a : E)
    (ha : IsMinOn (secondProxObjective ψ ω b) Set.univ a) :
    IsMinOn (linearizedSecondProxObjective ψ ω b) Set.univ a := by
  rw [isMinOn_univ_iff] at ha ⊢
  intro x
  have hax := ha x
  rw [eq_linearized_add_const, eq_linearized_add_const] at hax
  -- Cancel the common additive constant from the minimizer inequality.
  exact ((EReal.addLECancellable_coe _).add_le_add_iff_right).mp hax

end SecondProxObjective

namespace AffinePerturbedPenalty

/-- Adding the finite affine perturbation does not change the effective domain of `ψ`. -/
lemma effectiveDomain
    (ψ ω : E → EReal) (b : E) :
    effective_domain (affinePerturbedPenalty ψ ω b) = effective_domain ψ := by
  ext x
  constructor
  · intro hx
    rw [mem_effective_domain] at hx ⊢
    by_contra hψx
    have hψx_top : ψ x = ⊤ := le_antisymm le_top (not_lt.mp hψx)
    have hsum_top : affinePerturbedPenalty ψ ω b x = ⊤ := by
      rw [affinePerturbedPenalty, hψx_top]
      exact EReal.top_add_of_ne_bot
        (EReal.coe_ne_bot (-inner ℝ (∇ (fun z ↦ (ω z).toReal) b) x))
    exact (ne_of_lt hx) hsum_top
  · intro hx
    rw [mem_effective_domain] at hx ⊢
    -- The affine perturbation is finite everywhere, so finiteness is inherited from `ψ`.
    simpa [affinePerturbedPenalty] using
      EReal.add_lt_top (ne_of_lt hx) (EReal.coe_ne_top _)

/-- The affine-perturbed penalty remains proper whenever `ψ` is proper. -/
lemma proper
    (ψ ω : E → EReal) (b : E)
    (hψ_proper : IsProperExtendedRealFunction ψ) :
    IsProperExtendedRealFunction (affinePerturbedPenalty ψ ω b) := by
  constructor
  · intro x
    -- The finite affine term cannot create a `⊥` value.
    exact EReal.add_ne_bot_iff.mpr
      ⟨hψ_proper.ne_bot x, EReal.coe_ne_bot _⟩
  · rcases hψ_proper.effective_domain_nonempty with ⟨x, hx⟩
    -- Properness keeps the same effective domain witness after the affine perturbation.
    refine ⟨x, ?_⟩
    simpa [effectiveDomain ψ ω b] using hx

end AffinePerturbedPenalty

namespace LinearizedSecondProxObjective

/-- The linearized second-prox objective is the affine-perturbed penalty plus the finite potential
term `x ↦ (ω x).toReal`. -/
lemma eq_affinePerturbed_add_toReal
    (ψ ω : E → EReal) (b x : E) :
    linearizedSecondProxObjective ψ ω b x =
      affinePerturbedPenalty ψ ω b x + (ω x).toReal := by
  -- Separate the finite `ω(x)` contribution from the affine perturbation of `ψ`.
  rw [linearizedSecondProxObjective, affinePerturbedPenalty]
  have hreal :
      (ω x).toReal - inner ℝ (∇ (fun z ↦ (ω z).toReal) b) x =
        (-inner ℝ (∇ (fun z ↦ (ω z).toReal) b) x) + (ω x).toReal := by
    ring
  rw [hreal, EReal.coe_add]
  simp [add_left_comm, add_comm]

/-- Adding the finite potential term `x ↦ (ω x).toReal` does not change the effective domain of
the linearized objective. -/
lemma effectiveDomain
    (ψ ω : E → EReal) (b : E) :
    effective_domain (linearizedSecondProxObjective ψ ω b) = effective_domain ψ := by
  ext x
  constructor
  · intro hx
    rw [mem_effective_domain] at hx ⊢
    by_contra hψx
    have hψx_top : ψ x = ⊤ := le_antisymm le_top (not_lt.mp hψx)
    have hlin_top : linearizedSecondProxObjective ψ ω b x = ⊤ := by
      rw [linearizedSecondProxObjective, hψx_top]
      simpa using
        EReal.top_add_of_ne_bot
          (EReal.coe_ne_bot
            ((ω x).toReal - inner ℝ (∇ (fun z ↦ (ω z).toReal) b) x))
    exact (ne_of_lt hx) hlin_top
  · intro hx
    rw [mem_effective_domain] at hx ⊢
    -- The extra linearized term is a finite real scalar, so it preserves the effective domain.
    simpa [linearizedSecondProxObjective] using
      EReal.add_lt_top (ne_of_lt hx) (EReal.coe_ne_top _)

/-- If `ω` is a Bregman potential on `dom(ψ)`, the linearized objective is the sum of the
affine-perturbed penalty and `ω`. -/
lemma eq_affinePerturbed_add
    (ψ ω : E → EReal) (b : E) {σ : ℝ}
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ) :
    linearizedSecondProxObjective ψ ω b =
      fun x ↦ affinePerturbedPenalty ψ ω b x + ω x := by
  funext x
  by_cases hx : x ∈ effective_domain ψ
  · have hxω : x ∈ effective_domain ω := hω.subset_effective_domain hx
    have hω_value : ((((ω x).toReal : ℝ) : EReal)) = ω x :=
      EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hxω)) (hω.ne_bot x)
    rw [eq_affinePerturbed_add_toReal, hω_value]
  · have hlin_top : linearizedSecondProxObjective ψ ω b x = ⊤ := by
      have hxlin : x ∉ effective_domain (linearizedSecondProxObjective ψ ω b) := by
        simpa [effectiveDomain ψ ω b] using hx
      exact le_antisymm le_top (not_lt.mp hxlin)
    have haff_top : affinePerturbedPenalty ψ ω b x = ⊤ := by
      have hxa : x ∉ effective_domain (affinePerturbedPenalty ψ ω b) := by
        simpa [AffinePerturbedPenalty.effectiveDomain ψ ω b] using hx
      exact le_antisymm le_top (not_lt.mp hxa)
    rw [hlin_top, haff_top]
    simpa [add_comm] using (EReal.top_add_of_ne_bot (hω.ne_bot x)).symm

end LinearizedSecondProxObjective

end
