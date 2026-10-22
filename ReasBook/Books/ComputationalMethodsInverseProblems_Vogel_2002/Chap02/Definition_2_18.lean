/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A3.Comparison
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

public section

open Filter
open scoped Topology

namespace FilterRegularization

universe u v w x

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w} {ι : Type x}

section Convergence

variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]

/-- Definition 2.18 (1). A regularization family `R` converges to `Rstar` along `K.range`
if each `R α` is continuous and every sequence `gSeq` converging in `H₂` to `g : K.range`
admits a parameter sequence `αSeq` with `R (αSeq n) (gSeq n) → Rstar g`. -/
structure ConvergesTo (K : H₁ →L[𝕜] H₂) (R : ι → H₂ → H₁) (Rstar : K.range → H₁) : Prop where
  /-- Each regularization operator `R α` is continuous. -/
  continuous (α : ι) : Continuous (R α)
  /-- Every data sequence converging to `g : K.range` admits a parameter choice along which the
  regularized reconstructions converge to `Rstar g`. -/
  seq (g : K.range) (gSeq : ℕ → H₂) (hgSeq : Tendsto gSeq atTop (𝓝 (g : H₂))) :
      ∃ αSeq : ℕ → ι,
        Tendsto (fun n ↦ R (αSeq n) (gSeq n)) atTop (𝓝 (Rstar g))

set_option linter.defProp false in
/-- Build `ConvergesTo` from the continuity and sequence-convergence clauses. -/
def ConvergesTo.ofContinuousAndSeq
    (K : H₁ →L[𝕜] H₂) (R : ι → H₂ → H₁) (Rstar : K.range → H₁)
    (hcont : ∀ α : ι, Continuous (R α))
    (hseq : ∀ g : K.range, ∀ gSeq : ℕ → H₂,
      Tendsto gSeq atTop (𝓝 (g : H₂)) →
        ∃ αSeq : ℕ → ι,
          Tendsto (fun n ↦ R (αSeq n) (gSeq n)) atTop (𝓝 (Rstar g))) :
    ConvergesTo K R Rstar :=
  { continuous := hcont
    seq := hseq }

/-- Specification theorem for `ConvergesTo`. -/
theorem convergesTo_iff
    (K : H₁ →L[𝕜] H₂) (R : ι → H₂ → H₁) (Rstar : K.range → H₁) :
    ConvergesTo K R Rstar ↔
      (∀ α : ι, Continuous (R α)) ∧
        ∀ g : K.range, ∀ gSeq : ℕ → H₂,
          Tendsto gSeq atTop (𝓝 (g : H₂)) →
            ∃ αSeq : ℕ → ι,
              Tendsto (fun n ↦ R (αSeq n) (gSeq n)) atTop (𝓝 (Rstar g)) := by
  constructor
  · intro h
    exact ⟨h.continuous, h.seq⟩
  · rintro ⟨hcont, hseq⟩
    exact ⟨hcont, hseq⟩

end Convergence

section Linearity

/-- Definition 2.18 (2). A regularization family `R` is linear if each `R α` is a bounded
linear operator. -/
def IsLinear (𝕜 : Type u) [RCLike 𝕜]
    [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]
    (R : ι → H₂ → H₁) : Prop :=
  ∀ α : ι, IsBoundedLinearMap 𝕜 (R α)

variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]

/-- Specification theorem for `IsLinear`. -/
theorem isLinear_iff (R : ι → H₂ → H₁) :
    IsLinear 𝕜 R ↔ ∀ α : ι, IsBoundedLinearMap 𝕜 (R α) :=
  Iff.rfl

namespace IsLinear

/-- A linear regularization scheme canonically determines a family of continuous linear maps. -/
def toContinuousLinearMapFamily {R : ι → H₂ → H₁} (hR : IsLinear 𝕜 R) :
    ι → H₂ →L[𝕜] H₁ :=
  fun α ↦ (hR α).toContinuousLinearMap

/-- A family of continuous linear maps defines a linear regularization scheme. -/
theorem ofContinuousLinearMapFamily (S : ι → H₂ →L[𝕜] H₁) :
    IsLinear 𝕜 (fun α x ↦ S α x) :=
  fun α ↦ (S α).isBoundedLinearMap

/-- The bundled family associated to `hR` evaluates to the original regularization operators. -/
@[simp] theorem toContinuousLinearMapFamily_apply {R : ι → H₂ → H₁} (hR : IsLinear 𝕜 R)
    (α : ι) (x : H₂) :
    IsLinear.toContinuousLinearMapFamily hR α x = R α x := by
  simp [IsLinear.toContinuousLinearMapFamily]

end IsLinear

/-- A linear regularization scheme is equivalently realized by a family of continuous linear
maps. -/
theorem isLinear_iff_existsFamily (R : ι → H₂ → H₁) :
    IsLinear 𝕜 R ↔
      ∃ S : ι → H₂ →L[𝕜] H₁, ∀ α : ι, R α = S α := by
  constructor
  · intro hR
    refine ⟨IsLinear.toContinuousLinearMapFamily hR, ?_⟩
    intro α
    funext x
    exact IsLinear.toContinuousLinearMapFamily_apply hR α x
  · rintro ⟨S, hS⟩ α
    rw [hS α]
    exact (S α).isBoundedLinearMap

/-- Every operator in a linear regularization scheme is continuous. -/
theorem IsLinear.continuous {R : ι → H₂ → H₁} (hR : IsLinear 𝕜 R) (α : ι) :
    Continuous (R α : H₂ → H₁) :=
  (IsLinear.toContinuousLinearMapFamily hR α).continuous

end Linearity

end FilterRegularization
