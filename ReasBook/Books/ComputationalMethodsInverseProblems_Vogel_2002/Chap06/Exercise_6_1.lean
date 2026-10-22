/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

import Mathlib.Tactic.Ring

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

public section

/-!
Exercise 6.1.

The source item is an identifiability claim: when `c = 0` and the forcing is
the known constant `f(t) = f0`, observations of the displacement trajectory
`x(t)` should determine both parameters `k` and `m` in equation `(6.1)`.

The current repository snapshot still does not expose a checked Chapter 6 owner
for equation `(6.1)` or for the observation semantics. This file therefore
states the exercise directly on an explicit observation set `s`, using a
source-facing predicate that records both the needed `C²` regularity and the
specialized equation `m * iteratedDeriv 2 x t + k * x t = f0`. Under those
regularity hypotheses, `iteratedDeriv 2 x t` is the genuine observed second
derivative of the trajectory.
-/

/-- `SolvesUndampedConstantForcingOn s x f0 k m` means that the observed
displacement trajectory `x` is twice continuously differentiable at each
observation time in `s` and satisfies the undamped constant-forcing
specialization of equation `(6.1)` with parameters `(k, m)` there. -/
def SolvesUndampedConstantForcingOn
    (s : Set ℝ) (x : ℝ → ℝ) (f0 k m : ℝ) : Prop :=
  (∀ t ∈ s, ContDiffAt ℝ 2 x t) ∧
    Set.EqOn (fun t ↦ m * iteratedDeriv 2 x t + k * x t) (fun _ ↦ f0) s

namespace SolvesUndampedConstantForcingOn

theorem contDiffAt
    {s : Set ℝ} {x : ℝ → ℝ} {f0 k m : ℝ}
    (hsolve : SolvesUndampedConstantForcingOn s x f0 k m) {t : ℝ} (ht : t ∈ s) :
    ContDiffAt ℝ 2 x t :=
  hsolve.1 t ht

theorem eq
    {s : Set ℝ} {x : ℝ → ℝ} {f0 k m : ℝ}
    (hsolve : SolvesUndampedConstantForcingOn s x f0 k m) {t : ℝ} (ht : t ∈ s) :
    m * iteratedDeriv 2 x t + k * x t = f0 :=
  hsolve.2 ht

end SolvesUndampedConstantForcingOn

/-- Exercise 6.1. If the same observed displacement `x` on an observation set `s`
satisfies the undamped constant-forcing specialization of equation `(6.1)` for
both parameter pairs `(k₁, m₁)` and `(k₂, m₂)`, and if the observations detect
that `x` and its genuine second derivative are not proportional on `s`, then
the two parameter pairs are equal. -/
theorem parametersUniqueOfObservedDisplacement
    (s : Set ℝ) (x : ℝ → ℝ) (f0 k₁ m₁ k₂ m₂ : ℝ)
    (hsolve₁ : SolvesUndampedConstantForcingOn s x f0 k₁ m₁)
    (hsolve₂ : SolvesUndampedConstantForcingOn s x f0 k₂ m₂)
    (h_nondegenerate : ∃ t₁ ∈ s, ∃ t₂ ∈ s,
      x t₁ * iteratedDeriv 2 x t₂ ≠ x t₂ * iteratedDeriv 2 x t₁) :
    (k₁, m₁) = (k₂, m₂) := by
  rcases h_nondegenerate with ⟨t₁, ht₁, t₂, ht₂, hdet⟩
  let d : ℝ → ℝ := iteratedDeriv 2 x
  have hEq₁ : m₁ * d t₁ + k₁ * x t₁ = m₂ * d t₁ + k₂ * x t₁ := by
    rw [show m₁ * d t₁ + k₁ * x t₁ = f0 from hsolve₁.eq ht₁]
    rw [show m₂ * d t₁ + k₂ * x t₁ = f0 from hsolve₂.eq ht₁]
  have hEq₂ : m₁ * d t₂ + k₁ * x t₂ = m₂ * d t₂ + k₂ * x t₂ := by
    rw [show m₁ * d t₂ + k₁ * x t₂ = f0 from hsolve₁.eq ht₂]
    rw [show m₂ * d t₂ + k₂ * x t₂ = f0 from hsolve₂.eq ht₂]
  have hsub₁ : (m₁ - m₂) * d t₁ + (k₁ - k₂) * x t₁ = 0 := by
    calc
      (m₁ - m₂) * d t₁ + (k₁ - k₂) * x t₁
          = (m₁ * d t₁ + k₁ * x t₁) - (m₂ * d t₁ + k₂ * x t₁) := by ring
      _ = 0 := sub_eq_zero.mpr hEq₁
  have hsub₂ : (m₁ - m₂) * d t₂ + (k₁ - k₂) * x t₂ = 0 := by
    calc
      (m₁ - m₂) * d t₂ + (k₁ - k₂) * x t₂
          = (m₁ * d t₂ + k₁ * x t₂) - (m₂ * d t₂ + k₂ * x t₂) := by ring
      _ = 0 := sub_eq_zero.mpr hEq₂
  have hk_mul : (k₁ - k₂) * (x t₁ * d t₂ - x t₂ * d t₁) = 0 := by
    calc
      (k₁ - k₂) * (x t₁ * d t₂ - x t₂ * d t₁)
          = ((m₁ - m₂) * d t₁ + (k₁ - k₂) * x t₁) * d t₂
              - ((m₁ - m₂) * d t₂ + (k₁ - k₂) * x t₂) * d t₁ := by ring_nf
      _ = 0 := by rw [hsub₁, hsub₂]; ring
  have hm_mul : (m₁ - m₂) * (d t₁ * x t₂ - d t₂ * x t₁) = 0 := by
    calc
      (m₁ - m₂) * (d t₁ * x t₂ - d t₂ * x t₁)
          = ((m₁ - m₂) * d t₁ + (k₁ - k₂) * x t₁) * x t₂
              - ((m₁ - m₂) * d t₂ + (k₁ - k₂) * x t₂) * x t₁ := by ring_nf
      _ = 0 := by rw [hsub₁, hsub₂]; ring
  have hk_zero : k₁ - k₂ = 0 := by
    apply (mul_eq_zero.mp hk_mul).resolve_right
    exact sub_ne_zero.mpr hdet
  have hm_zero : m₁ - m₂ = 0 := by
    apply (mul_eq_zero.mp hm_mul).resolve_right
    exact sub_ne_zero.mpr (by simpa [mul_comm] using hdet.symm)
  ext
  · exact sub_eq_zero.mp hk_zero
  · exact sub_eq_zero.mp hm_zero
