/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_42

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type u}

/-- The one-step multiplicative factor in the Cox--Ross--Rubinstein model, driven by a
`{-1,1}`-valued innovation. The textbook cases `Dₙ = 1` and `Dₙ = -1` give the factors `1 + b`
and `1 + a`, respectively. -/
def coxRossRubinsteinFactor (a b : ℝ) (d : {x : ℝ // x = -1 ∨ x = 1}) : ℝ :=
  1 + (a + b) / 2 + ((b - a) / 2) * d.1

private def coxRossRubinsteinPriceProcessAux {T : ℕ} (x0 a b : ℝ)
    (D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}) : ℕ → Ω → ℝ
  | 0 => fun _ ↦ x0
  | n + 1 => fun ω ↦
      (if h : n < T then coxRossRubinsteinFactor a b (D ⟨n, h⟩ ω) else 1) *
        coxRossRubinsteinPriceProcessAux x0 a b D n ω

/-- Definition 9.44: for a fixed horizon `T`, initial value `x0`, and `{-1,1}`-valued driving
sequence `D₁, …, D_T`, the Cox--Ross--Rubinstein price process on times `0, …, T` is the
recursively defined family with `X₀ = x0` and
`X_{n+1} = ρ(D_{n+1}) X_n`, where `ρ(1) = 1 + b` and `ρ(-1) = 1 + a`. In Lean's `0`-based
indexing, `D i` represents the textbook increment `D_{i+1}`. -/
def coxRossRubinsteinPriceProcess {T : ℕ} (x0 a b : ℝ)
    (D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}) : Fin (T + 1) → Ω → ℝ :=
  fun n ↦ coxRossRubinsteinPriceProcessAux x0 a b D n.1

-- Proof sketch: for `d = 1`, the affine formula becomes `1 + b`.
@[simp] theorem coxRossRubinsteinFactor_pos (a b : ℝ) :
    coxRossRubinsteinFactor a b ⟨1, Or.inr rfl⟩ = 1 + b := by
  calc
    coxRossRubinsteinFactor a b ⟨1, Or.inr rfl⟩
      = 1 + (a + b) / 2 + (b - a) / 2 := by
          simp [coxRossRubinsteinFactor]
    _ = 1 + b := by ring

-- Proof sketch: for `d = -1`, the affine formula becomes `1 + a`.
@[simp] theorem coxRossRubinsteinFactor_neg (a b : ℝ) :
    coxRossRubinsteinFactor a b ⟨-1, Or.inl rfl⟩ = 1 + a := by
  calc
    coxRossRubinsteinFactor a b ⟨-1, Or.inl rfl⟩
      = 1 + (a + b) / 2 + -((b - a) / 2) := by
          simp [coxRossRubinsteinFactor]
    _ = 1 + a := by ring

-- Proof sketch: `d.1` is measurable on the subtype and affine real combinations preserve
-- measurability.
theorem measurable_coxRossRubinsteinFactor (a b : ℝ) :
    Measurable (coxRossRubinsteinFactor a b) := by
  let c : {x : ℝ // x = -1 ∨ x = 1} → ℝ := fun _ ↦ 1 + (a + b) / 2
  let l : {x : ℝ // x = -1 ∨ x = 1} → ℝ := fun d ↦ ((b - a) / 2) * d.1
  have hc : Measurable c := measurable_const
  have hl : Measurable l := measurable_const.mul measurable_subtype_coe
  simpa [c, l, coxRossRubinsteinFactor] using hc.add hl

private theorem coxRossRubinsteinPriceProcessAux_eq_prod {T : ℕ} (x0 a b : ℝ)
    (D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}) :
    ∀ n ω (hn : n ≤ T),
      coxRossRubinsteinPriceProcessAux x0 a b D n ω =
        x0 * ∏ i : Fin n, coxRossRubinsteinFactor a b (D (i.castLE hn) ω)
  | 0, ω, _ => by simp [coxRossRubinsteinPriceProcessAux]
  | n + 1, ω, hn => by
      have h : n < T := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have hlast : (Fin.last n).castLE hn = ⟨n, h⟩ := by
        ext
        rfl
      simp [coxRossRubinsteinPriceProcessAux, h]
      rw [coxRossRubinsteinPriceProcessAux_eq_prod x0 a b D n ω (Nat.le_of_lt h)]
      rw [show
        ∏ i : Fin (n + 1), coxRossRubinsteinFactor a b (D (i.castLE hn) ω) =
          (∏ i : Fin n, coxRossRubinsteinFactor a b (D (i.castLE (Nat.le_of_lt h)) ω)) *
            coxRossRubinsteinFactor a b (D ⟨n, h⟩ ω) by
          rw [Fin.prod_univ_castSucc]
          simp [hlast]]
      ring

private theorem measurable_coxRossRubinsteinPriceProcessAux {T : ℕ} (x0 a b : ℝ)
    [MeasurableSpace Ω] (D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1})
    (hD : ∀ n, Measurable (D n)) :
    ∀ n, Measurable (coxRossRubinsteinPriceProcessAux x0 a b D n)
  | 0 => by simp [coxRossRubinsteinPriceProcessAux]
  | n + 1 => by
      by_cases h : n < T
      · simpa [coxRossRubinsteinPriceProcessAux, h] using
          ((measurable_coxRossRubinsteinFactor a b).comp (hD ⟨n, h⟩)).mul
            (measurable_coxRossRubinsteinPriceProcessAux x0 a b D hD n)
      · simpa [coxRossRubinsteinPriceProcessAux, h] using
          measurable_coxRossRubinsteinPriceProcessAux x0 a b D hD n

-- Proof sketch: expand the recursive definition and induct on `n`; this recovers the closed-form
-- finite product representation used in the previous version of the file.
/-- The recursively defined Cox--Ross--Rubinstein process agrees with the textbook finite-product
formula. -/
theorem coxRossRubinsteinPriceProcess_eq_prod {T : ℕ} (x0 a b : ℝ)
    (D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}) (n : Fin (T + 1)) (ω : Ω) :
    coxRossRubinsteinPriceProcess x0 a b D n ω =
      x0 * ∏ i : Fin n.1, coxRossRubinsteinFactor a b (D (i.castLE (Nat.lt_succ_iff.mp n.2)) ω) := by
  simpa [coxRossRubinsteinPriceProcess] using
    coxRossRubinsteinPriceProcessAux_eq_prod x0 a b D n.1 ω (Nat.lt_succ_iff.mp n.2)

-- Proof sketch: split the final product into the first `n` factors and the new factor at `n + 1`.
/-- The Cox--Ross--Rubinstein process satisfies the one-step recursion
`X_{n+1} = ρ(D_{n+1}) X_n`, where `ρ(1) = 1 + b` and `ρ(-1) = 1 + a`. -/
theorem coxRossRubinsteinPriceProcess_succ {T : ℕ} (x0 a b : ℝ)
    (D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}) (n : Fin T) (ω : Ω) :
    coxRossRubinsteinPriceProcess x0 a b D n.succ ω =
      coxRossRubinsteinFactor a b (D n ω) *
        coxRossRubinsteinPriceProcess x0 a b D n.castSucc ω := by
  simp [coxRossRubinsteinPriceProcess, coxRossRubinsteinPriceProcessAux, n.2]

-- Proof sketch: the empty product is `1`.
/-- The initial value of the Cox--Ross--Rubinstein process is `x0`. -/
@[simp] theorem coxRossRubinsteinPriceProcess_zero {T : ℕ} (x0 a b : ℝ)
    (D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}) (ω : Ω) :
    coxRossRubinsteinPriceProcess x0 a b D 0 ω = x0 := by
  simp [coxRossRubinsteinPriceProcess, coxRossRubinsteinPriceProcessAux]

section BinaryModelBridge

variable [MeasurableSpace Ω]

-- Proof sketch: every factor is measurable, and finite products of measurable real-valued
-- functions are measurable.
theorem isStochasticProcess_coxRossRubinsteinPriceProcess {T : ℕ} (x0 a b : ℝ)
    (D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}) (hD : ∀ n, Measurable (D n)) :
    IsStochasticProcess (coxRossRubinsteinPriceProcess x0 a b D) := by
  intro n
  simpa [coxRossRubinsteinPriceProcess] using
    measurable_coxRossRubinsteinPriceProcessAux x0 a b D hD n.1

-- Proof sketch: the CRR process is a binary model in the sense of Definition 9.42: the
-- innovations are exactly the given `{-1,1}`-valued drivers, and the next-step map depends only
-- on the latest price together with the current sign.
/-- The finite-horizon Cox--Ross--Rubinstein price process is a binary model in the sense of
Definition 9.42. This is the owner-abstraction bridge for Definition 9.44. -/
theorem coxRossRubinsteinPriceProcess_isBinaryModel {T : ℕ} (x0 a b : ℝ)
    (D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}) (hD : ∀ n, Measurable (D n)) :
    IsBinaryModel (coxRossRubinsteinPriceProcess x0 a b D) := by
  refine ⟨isStochasticProcess_coxRossRubinsteinPriceProcess x0 a b D hD, x0, ?_, D, hD, ?_⟩
  · funext ω
    simp
  · refine ⟨fun
      | ⟨0, _⟩, _history, d => coxRossRubinsteinFactor a b d * x0
      | ⟨m + 1, _⟩, history, d =>
          coxRossRubinsteinFactor a b d * history ⟨m, Nat.lt_succ_self m⟩, ?_⟩
    intro n
    cases' n with n hn
    cases n with
    | zero =>
        funext ω
        simpa using
          coxRossRubinsteinPriceProcess_succ x0 a b D ⟨0, hn⟩ ω
    | succ m =>
        funext ω
        simpa [binaryModelHistory] using
          coxRossRubinsteinPriceProcess_succ x0 a b D ⟨m + 1, hn⟩ ω

end BinaryModelBridge

end ProbabilityTheory
