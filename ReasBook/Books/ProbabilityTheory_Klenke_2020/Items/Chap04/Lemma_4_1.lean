/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory
open scoped BigOperators

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: rewrite the normal representation as the canonical finite sum of restricted
-- constant simple functions, then evaluate the lower integral of that finite sum by additivity and
-- `SimpleFunc.restrict_const_lintegral`.
/-- Lemma 4.1: a normal representation of a nonnegative simple function computes its lower
integral as the corresponding weighted measure sum. -/
theorem lintegral_eq_weighted_measure_sum_of_normal_representation
    (μ : Measure Ω) (f : SimpleFunc Ω ENNReal)
    {n : ℕ} (A : Fin n → Set Ω) (α : Fin n → ENNReal)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (_hA_disj : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hfA : (f : Ω → ENNReal) = fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ α i) ω) :
    f.lintegral μ = ∑ i, α i * μ (A i) := by
  classical
  let g : SimpleFunc Ω ENNReal := ∑ i, (SimpleFunc.const Ω (α i)).restrict (A i)
  have hg_apply (ω : Ω) : g ω = ∑ i, ((SimpleFunc.const Ω (α i)).restrict (A i)) ω := by
    let s : Finset (Fin n) := Finset.univ
    change (s.sum fun i ↦ (SimpleFunc.const Ω (α i)).restrict (A i)) ω =
      s.sum fun i ↦ ((SimpleFunc.const Ω (α i)).restrict (A i)) ω
    induction s using Finset.induction_on with
    | empty =>
        simp
    | insert i s hi hs =>
        simp [hi, hs, SimpleFunc.coe_add, Pi.add_apply]
  have hfg : f = g := by
    ext ω
    rw [hfA]
    calc
      ∑ i, (A i).indicator (fun _ ↦ α i) ω
          = ∑ i, ((SimpleFunc.const Ω (α i)).restrict (A i)) ω := by
              refine Finset.sum_congr rfl (fun i _ ↦ ?_)
              rw [SimpleFunc.restrict_apply _ (hA_meas i)]
              rfl
      _ = g ω := by
        simpa using (hg_apply ω).symm
  rw [hfg]
  have hs :
      ∀ s : Finset (Fin n),
        (∑ i ∈ s, (SimpleFunc.const Ω (α i)).restrict (A i)).lintegral μ =
          ∑ i ∈ s, α i * μ (A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp
    | insert i s hi hs =>
        simp [hi, hs, hA_meas i, SimpleFunc.add_lintegral, SimpleFunc.restrict_const_lintegral]
  simpa [g] using hs Finset.univ

/-- Textbook two-representation form of Lemma 4.1: two normal representations of the same
nonnegative simple function have the same weighted measure sum. -/
theorem weighted_measure_sum_eq_of_normal_representations
    (μ : Measure Ω) (f : SimpleFunc Ω ENNReal)
    {m n : ℕ} (A : Fin m → Set Ω) (B : Fin n → Set Ω)
    (α : Fin m → ENNReal) (β : Fin n → ENNReal)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hB_meas : ∀ j, MeasurableSet (B j))
    (hA_disj : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hB_disj : Pairwise (fun i j ↦ Disjoint (B i) (B j)))
    (hfA : (f : Ω → ENNReal) = fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ α i) ω)
    (hfB : (f : Ω → ENNReal) = fun ω ↦ ∑ j, (B j).indicator (fun _ ↦ β j) ω) :
    ∑ i, α i * μ (A i) = ∑ j, β j * μ (B j) := by
  rw [← lintegral_eq_weighted_measure_sum_of_normal_representation μ f A α hA_meas hA_disj hfA,
    lintegral_eq_weighted_measure_sum_of_normal_representation μ f B β hB_meas hB_disj hfB]
