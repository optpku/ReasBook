/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ψ ω : E → EReal} {a b : E}

/-- The second-prox objective in the minimization identity (9.15), for a penalty `ψ`, Bregman
potential `ω`, and base point `b`. -/
def secondProxObjective (ψ ω : E → EReal) (b : E) : E → EReal :=
  fun x ↦ ψ x + B[ω] x b

namespace SecondProxObjective

/-- Evaluating the objective in (9.15) gives `ψ(x) + B[ω] x b`. -/
@[simp] theorem apply (ψ ω : E → EReal) (b x : E) :
    secondProxObjective ψ ω b x = ψ x + B[ω] x b :=
  rfl

/-- The finite Bregman term does not change the effective domain of the penalty. -/
@[simp] theorem effectiveDomain (ψ ω : E → EReal) (b : E) :
    effective_domain (secondProxObjective ψ ω b) = effective_domain ψ := by
  ext x
  rw [mem_effective_domain, mem_effective_domain, apply]
  constructor
  · intro hx
    rw [lt_top_iff_ne_top] at hx ⊢
    intro hψx
    apply hx
    rw [hψx]
    exact EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
  · intro hx
    exact EReal.add_lt_top hx.ne (EReal.coe_ne_top _)

/-- A global minimizer of the second-prox objective for a proper penalty lies in the penalty's
effective domain. -/
theorem minimizer_mem_effective_domain
    (hψ : IsProperExtendedRealFunction ψ)
    (ha : IsMinOn (secondProxObjective ψ ω b) Set.univ a) :
    a ∈ effective_domain ψ := by
  rcases hψ.effective_domain_nonempty with ⟨x, hx⟩
  rw [← effectiveDomain ψ ω b] at hx ⊢
  exact lt_of_le_of_lt (isMinOn_univ_iff.mp ha x) hx

end SecondProxObjective

end
