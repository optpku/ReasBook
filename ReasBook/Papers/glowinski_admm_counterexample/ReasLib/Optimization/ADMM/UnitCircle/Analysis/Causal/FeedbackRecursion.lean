/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.FeedbackOperator

@[expose] public section

namespace ADMM.UnitCircle.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The strictly triangular within-step evaluation: first compute the `F`
input/output, then the `J` input/output, then update the causal memory. -/
def homotopyState (D : ℕ → Fin 2 → E → E) (α γ τ : ℝ)
    (e : ℕ → Fin 2 → E) : ℕ → E × E
  | 0 => (0, 0)
  | k + 1 =>
      let s := homotopyState D α γ τ e k
      let vF := e k 0 + α • s.2 + (-γ) • s.1
      let q := τ • D k 0 vF
      let vJ := e k 1 + q + γ • s.1
      let η := τ • D k 1 vJ
      (α • (q - η + s.1), η)

/-- The causal input sequence exists for every forcing, even before its
square summability has been established. -/
def homotopyInput (D : ℕ → Fin 2 → E → E) (α γ τ : ℝ)
    (e : ℕ → Fin 2 → E) (k : ℕ) : Fin 2 → E :=
  let s := homotopyState D α γ τ e k
  let vF := e k 0 + α • s.2 + (-γ) • s.1
  fun b ↦ if b = 0 then vF else e k 1 + τ • D k 0 vF + γ • s.1

def homotopyOutput (D : ℕ → Fin 2 → E → E) (α γ τ : ℝ)
    (e : ℕ → Fin 2 → E) (k : ℕ) (b : Fin 2) : E :=
  τ • D k b (homotopyInput D α γ τ e k b)

@[simp] theorem homotopyState_initial (D : ℕ → Fin 2 → E → E) (α γ τ : ℝ)
    (e : ℕ → Fin 2 → E) : homotopyState D α γ τ e 0 = (0, 0) := rfl

theorem homotopyState_update (D : ℕ → Fin 2 → E → E) (α γ τ : ℝ)
    (e : ℕ → Fin 2 → E) (k : ℕ) :
    homotopyState D α γ τ e (k + 1) =
      (α • (homotopyOutput D α γ τ e k 0 - homotopyOutput D α γ τ e k 1 +
          (homotopyState D α γ τ e k).1), homotopyOutput D α γ τ e k 1) := by
  simp [homotopyState, homotopyOutput, homotopyInput]

/-- The finite-state memory is exactly the manuscript's causal resolvent. -/
theorem homotopyState_resolvent (D : ℕ → Fin 2 → E → E) (α γ τ : ℝ)
    (e : ℕ → Fin 2 → E) (k : ℕ) :
    (homotopyState D α γ τ e k).1 = causalResolvent α
      (fun j ↦ homotopyOutput D α γ τ e j 0 - homotopyOutput D α γ τ e j 1) k := by
  induction k with
  | zero => simp
  | succ k ih => rw [homotopyState_update, causalResolvent_succ]; simpa using congrArg (fun t ↦
      α • (homotopyOutput D α γ τ e k 0 - homotopyOutput D α γ τ e k 1 + t)) ih

theorem homotopyState_previous_output (D : ℕ → Fin 2 → E → E) (α γ τ : ℝ)
    (e : ℕ → Fin 2 → E) (k : ℕ) :
    (homotopyState D α γ τ e k).2 = delay (fun j ↦ homotopyOutput D α γ τ e j 1) k := by
  cases k with
  | zero => simp
  | succ k => rw [homotopyState_update]; rfl

/-- The constructed sequence solves the exact nonlinear feedback relation. -/
theorem homotopyInput_feedback (D : ℕ → Fin 2 → E → E) (α γ τ : ℝ)
    (e : ℕ → Fin 2 → E) :
    homotopyInput D α γ τ e = e + feedbackOperator α γ (homotopyOutput D α γ τ e) := by
  funext k b
  fin_cases b
  · change homotopyInput D α γ τ e k 0 = e k 0 +
      feedbackOperator α γ (homotopyOutput D α γ τ e) k 0
    rw [feedbackOperator_first]
    change e k 0 + α • (homotopyState D α γ τ e k).2 +
      (-γ) • (homotopyState D α γ τ e k).1 = _
    rw [homotopyState_previous_output, homotopyState_resolvent]
    module
  · change homotopyInput D α γ τ e k 1 = e k 1 +
      feedbackOperator α γ (homotopyOutput D α γ τ e) k 1
    rw [feedbackOperator_second]
    rw [show homotopyInput D α γ τ e k 1 = e k 1 +
      homotopyOutput D α γ τ e k 0 + γ • (homotopyState D α γ τ e k).1 by rfl]
    rw [homotopyState_resolvent]
    module

/-- The homotopy parameter may be factored outside the linear feedback. -/
theorem homotopyInput_equation (D : ℕ → Fin 2 → E → E) (α γ τ : ℝ)
    (e : ℕ → Fin 2 → E) (k : ℕ) :
    homotopyInput D α γ τ e k = e k +
      τ • feedbackOperator α γ (fun j b ↦ D j b (homotopyInput D α γ τ e j b)) k := by
  have heq : homotopyOutput D α γ τ e =
      τ • (fun j b ↦ D j b (homotopyInput D α γ τ e j b)) := rfl
  have h := congrFun (homotopyInput_feedback D α γ τ e) k
  rw [heq, feedbackOperator_smul] at h
  exact h

/-- Causality and the within-step triangular order give uniqueness on every
finite prefix. No fixed-point theorem on infinite sequences is used. -/
theorem feedback_prefix_unique (D : ℕ → Fin 2 → E → E) (α γ τ : ℝ)
    (e : ℕ → Fin 2 → E) (T : ℕ) (v w : ℕ → Fin 2 → E)
    (hv : ∀ k < T, v k = e k + τ • feedbackOperator α γ (fun j b ↦ D j b (v j b)) k)
    (hw : ∀ k < T, w k = e k + τ • feedbackOperator α γ (fun j b ↦ D j b (w j b)) k) :
    ∀ k < T, v k = w k := by
  have hprove : ∀ k, k < T → v k = w k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hK : causalResolvent α (fun j ↦ D j 0 (v j 0) - D j 1 (v j 1)) k =
          causalResolvent α (fun j ↦ D j 0 (w j 0) - D j 1 (w j 1)) k := by
        apply causalResolvent_prefix_congr
        intro j hj
        rw [ih j hj (lt_trans hj hk)]
      have hdelay : delay (fun j ↦ D j 1 (v j 1)) k =
          delay (fun j ↦ D j 1 (w j 1)) k := by
        cases k with
        | zero => simp
        | succ k =>
          simp only [delay_succ]
          rw [ih k (Nat.lt_succ_self k) (lt_trans (Nat.lt_succ_self k) hk)]
      have h0 : v k 0 = w k 0 := by
        have hv0 := congrFun (hv k hk) 0
        have hw0 := congrFun (hw k hk) 0
        simp only [Pi.add_apply, Pi.smul_apply, feedbackOperator_first] at hv0 hw0
        rw [hdelay, hK] at hv0
        exact hv0.trans hw0.symm
      have h1 : v k 1 = w k 1 := by
        have hv1 := congrFun (hv k hk) 1
        have hw1 := congrFun (hw k hk) 1
        simp only [Pi.add_apply, Pi.smul_apply, feedbackOperator_second] at hv1 hw1
        rw [h0, hK] at hv1
        exact hv1.trans hw1.symm
      funext b
      fin_cases b
      · exact h0
      · exact h1
  exact hprove

end ADMM.UnitCircle.Causal
