/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.StrictProjectionCycle
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

open scoped RealInnerProductSpace
open Filter

namespace ConsensusADMM.ProjectionCycle

universe u v
variable {N : ℕ} {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable section

/-- Orthogonally append an auxiliary vector at a common scale. -/
def scaledPair (ε : ℝ) (x : E) (y : F) : WithLp 2 (E × F) :=
  WithLp.toLp 2 (x, ε • y)

omit [InnerProductSpace ℝ E] in
@[simp] theorem scaledPair_add (ε : ℝ) (x₁ x₂ : E) (y₁ y₂ : F) :
    scaledPair ε (x₁ + x₂) (y₁ + y₂) = scaledPair ε x₁ y₁ + scaledPair ε x₂ y₂ := by
  apply WithLp.ofLp_injective; apply Prod.ext <;> simp [scaledPair, smul_add]

omit [InnerProductSpace ℝ E] in
@[simp] theorem scaledPair_sub (ε : ℝ) (x₁ x₂ : E) (y₁ y₂ : F) :
    scaledPair ε (x₁ - x₂) (y₁ - y₂) = scaledPair ε x₁ y₁ - scaledPair ε x₂ y₂ := by
  apply WithLp.ofLp_injective; apply Prod.ext <;> simp [scaledPair, smul_sub]

@[simp] theorem scaledPair_smul (ε c : ℝ) (x : E) (y : F) :
    scaledPair ε (c • x) (c • y) = c • scaledPair ε x y := by
  apply WithLp.ofLp_injective; apply Prod.ext <;> simp [scaledPair, smul_smul, mul_comm]

/-- Orthogonality makes every support the sum of its original margin and the
squared scale times its auxiliary margin. -/
theorem scaledPair_inner (ε : ℝ) (x₁ x₂ : E) (y₁ y₂ : F) :
    inner ℝ (scaledPair ε x₁ y₁) (scaledPair ε x₂ y₂) =
      inner ℝ x₁ x₂ + ε ^ 2 * inner ℝ y₁ y₂ := by
  simp [scaledPair, WithLp.prod_inner_apply, inner_smul_left, inner_smul_right, pow_two,
    mul_assoc]

/-- At every nonzero scale, strict auxiliary supports improve weak original supports. -/
theorem strictSupports_scaledPair {p n : ZMod N → E} {q m : ZMod N → F}
    (hweak : NonselfSupports p n) (hstrict : StrictNonselfSupports q m)
    {ε : ℝ} (hε : ε ≠ 0) :
    StrictNonselfSupports (fun i ↦ scaledPair ε (p i) (q i))
      (fun i ↦ scaledPair ε (n i) (m i)) := by
  intro i
  constructor
  · rw [scaledPair_inner]
    exact add_pos_of_nonneg_of_pos (hweak i).1
      (mul_pos (sq_pos_of_ne_zero hε) (hstrict i).1)
  · intro j hji
    rw [← scaledPair_sub, scaledPair_inner]
    exact add_pos_of_nonneg_of_pos ((hweak i).2 j hji)
      (mul_pos (sq_pos_of_ne_zero hε) ((hstrict i).2 j hji))

/-- Small orthogonal perturbations preserve all finitely many strict margins. -/
theorem strictSupports_scaledPair_eventually [NeZero N]
    {p n : ZMod N → E} (q m : ZMod N → F)
    (hstrict : StrictNonselfSupports p n) :
    ∀ᶠ ε in nhds (0 : ℝ),
      StrictNonselfSupports (fun i ↦ scaledPair ε (p i) (q i))
        (fun i ↦ scaledPair ε (n i) (m i)) := by
  apply Filter.eventually_all.mpr
  intro i
  have hzero : ∀ᶠ ε in nhds (0 : ℝ),
      0 < inner ℝ (scaledPair ε (n i) (m i)) (scaledPair ε (p i) (q i)) := by
    simp only [scaledPair_inner]
    exact (continuousAt_const.add ((continuousAt_id.pow 2).mul continuousAt_const)).eventually
      (by simpa using lt_mem_nhds (hstrict i).1)
  have hpairs : ∀ᶠ ε in nhds (0 : ℝ), ∀ j, j ≠ i →
      0 < inner ℝ (scaledPair ε (n i) (m i))
        (scaledPair ε (p i) (q i) - scaledPair ε (p j) (q j)) := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall fun _ h ↦ (h hji).elim
    · simp only [← scaledPair_sub, scaledPair_inner]
      have he : ∀ᶠ ε in nhds (0 : ℝ),
          0 < inner ℝ (n i) (p i - p j) + ε ^ 2 * inner ℝ (m i) (q i - q j) :=
        (continuousAt_const.add ((continuousAt_id.pow 2).mul continuousAt_const)).eventually
          (by simpa using lt_mem_nhds ((hstrict i).2 j hji))
      exact he.mono fun _ h _ ↦ h
  exact hzero.and hpairs

/-- Orthogonal pairing commutes with the four linear cycle recurrences. -/
theorem cycleVectors_scaledPair (γ ε : ℝ) (η ν : ZMod N → E) (η₁ ν₁ : ZMod N → F)
    (i : ZMod N) :
    residual γ (fun j ↦ scaledPair ε (ν j) (ν₁ j)) i =
        scaledPair ε (residual γ ν i) (residual γ ν₁ i) ∧
    xVertex γ (fun j ↦ scaledPair ε (η j) (η₁ j)) (fun j ↦ scaledPair ε (ν j) (ν₁ j)) i =
        scaledPair ε (xVertex γ η ν i) (xVertex γ η₁ ν₁ i) ∧
    firstNormal γ (fun j ↦ scaledPair ε (η j) (η₁ j))
        (fun j ↦ scaledPair ε (ν j) (ν₁ j)) i =
        scaledPair ε (firstNormal γ η ν i) (firstNormal γ η₁ ν₁ i) ∧
    secondNormal γ (fun j ↦ scaledPair ε (ν j) (ν₁ j)) i =
        scaledPair ε (secondNormal γ ν i) (secondNormal γ ν₁ i) := by
  simp only [residual, xVertex, firstNormal, secondNormal, ← scaledPair_add,
    ← scaledPair_sub, ← scaledPair_smul, and_self]

/-- An original nonzero residual remains nonzero after orthogonal pairing. -/
theorem residual_scaledPair_nonzero (γ ε : ℝ) (ν : ZMod N → E) (ν₁ : ZMod N → F)
    (hnonzero : ∃ i, residual γ ν i ≠ 0) :
    ∃ i, residual γ (fun j ↦ scaledPair ε (ν j) (ν₁ j)) i ≠ 0 := by
  obtain ⟨i, hi⟩ := hnonzero
  refine ⟨i, fun hz ↦ hi ?_⟩
  have hf := congrArg (fun z : WithLp 2 (E × F) ↦ (WithLp.ofLp z).1) hz
  simpa [residual, scaledPair] using hf

/-- Direct sum of the two phase maps preserves orthogonal cyclic symmetry. -/
theorem symmetry_scaledPair (ε : ℝ) {η ν : ZMod N → E} {η₁ ν₁ : ZMod N → F}
    (h : HasOrthogonalCyclicSymmetry η ν) (h₁ : HasOrthogonalCyclicSymmetry η₁ ν₁) :
    HasOrthogonalCyclicSymmetry (fun i ↦ scaledPair ε (η i) (η₁ i))
      (fun i ↦ scaledPair ε (ν i) (ν₁ i)) := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨V, hV⟩ := h₁
  refine ⟨U.withLpProdCongr 2 V, fun i ↦ ⟨?_, ?_⟩⟩
  · apply WithLp.ofLp_injective; apply Prod.ext <;> simp [scaledPair, (hU i).1, (hV i).1]
  · apply WithLp.ofLp_injective; apply Prod.ext <;> simp [scaledPair, (hU i).2, (hV i).2]

end
end ConsensusADMM.ProjectionCycle
