/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.LagData
public import Mathlib.Data.List.Sort

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Division

open ADMM.RefinedEndpoint.Data

def rawBlock (b : Fin 2) : List LagWeight :=
  lagWeights.filter (fun e ↦ decide (e.block = Concrete.blockOfIndex b))

def collectedLag (b : Fin 2) : Laurent :=
  (0, omega + ((rawBlock b).map LagWeight.coefficient).sum) ::
    (rawBlock b).map (fun e ↦ (e.lag, -e.coefficient))

/-- Exposed structural sorting code, so every normalization is kernel executable. -/
def exponentInsert (e : ℤ × ℚ) : Laurent → Laurent
  | [] => [e]
  | f :: p => if e.1 ≤ f.1 then e :: f :: p else f :: exponentInsert e p

def exponentSort : Laurent → Laurent
  | [] => []
  | e :: p => exponentInsert e (exponentSort p)

theorem exponentInsert_eq (e : ℤ × ℚ) (p : Laurent) :
    exponentInsert e p = p.orderedInsert (fun e f ↦ e.1 ≤ f.1) e := by
  induction p with
  | nil => simp only [exponentInsert, List.orderedInsert_nil]
  | cons f p ih => simp only [exponentInsert, List.orderedInsert_cons, ih]

theorem exponentSort_eq (p : Laurent) :
    exponentSort p = p.insertionSort (fun e f ↦ e.1 ≤ f.1) := by
  induction p with
  | nil => simp only [exponentSort, List.insertionSort_nil]
  | cons e p ih => rw [exponentSort, ih, exponentInsert_eq, List.insertionSort_cons]

def normalizedFromRaw (b : Fin 2) : Laurent := exponentSort (collectedLag b)

theorem evaluateLaurent_perm {p q : Laurent} (h : p.Perm q) (z : ℂ) :
    evaluateLaurent p z = evaluateLaurent q z :=
  (h.map (fun e : ℤ × ℚ ↦ (e.2 : ℂ) * z ^ e.1)).sum_eq

/-- Sorting a finite Laurent expression preserves its exact evaluation. -/
theorem evaluateLaurent_insertionSort (p : Laurent) (z : ℂ) :
    evaluateLaurent (p.insertionSort (fun e f ↦ e.1 ≤ f.1)) z =
      evaluateLaurent p z :=
  evaluateLaurent_perm (List.perm_insertionSort (fun e f : ℤ × ℚ ↦ e.1 ≤ f.1) p) z

lemma evaluate_collected (xs : List LagWeight) (c : ℚ) (z : ℂ) :
    evaluateLaurent ((0, c + (xs.map LagWeight.coefficient).sum) ::
      xs.map (fun e ↦ (e.lag, -e.coefficient))) z =
      (c : ℂ) + (xs.map (fun e ↦ (e.coefficient : ℂ) * (1 - z ^ e.lag))).sum := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    simp only [List.map_cons, List.sum_cons, evaluateLaurent_cons, zpow_zero, mul_one,
      Rat.cast_add, Rat.cast_neg] at ih ⊢
    linear_combination ih

/-- The sorted multiplier is derived from the original JSON terms by one
collection of the constant term and one permutation, rather than hundreds of
independent scans of the full expanded source. -/
theorem evaluate_normalizedFromRaw (b : Fin 2) (z : ℂ) :
    evaluateLaurent (normalizedFromRaw b) z = evaluateLaurent (lagLaurent b) z := by
  rw [normalizedFromRaw, exponentSort_eq, evaluateLaurent_insertionSort, collectedLag, evaluate_collected,
    evaluate_lagLaurent, paper_lagMultiplier_one]
  rfl

set_option maxRecDepth 8192 in
-- Check the complete sorted rational normalization once per block.
theorem normalizedLag0_correct : normalizedLag0 = normalizedFromRaw 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
-- The same whole-list check for the second raw-input block.
theorem normalizedLag1_correct : normalizedLag1 = normalizedFromRaw 1 := by
  decide +kernel

/-- The normalized data evaluate to the actual multiplier in both blocks. -/
theorem evaluate_normalizedLag (b : Fin 2) (z : ℂ) :
    evaluateLaurent (normalizedLag b) z = lagMultiplier paperWeights 1 z b := by
  unfold normalizedLag
  split_ifs with hb
  · subst b
    rw [normalizedLag0_correct, evaluate_normalizedFromRaw, evaluate_lagLaurent]
  · have hb1 : b = 1 := by
      apply Fin.ext
      have hh := b.isLt
      have hne : b.val ≠ 0 := by intro h; apply hb; exact Fin.ext h
      omega
    subst b
    rw [normalizedLag1_correct, evaluate_normalizedFromRaw, evaluate_lagLaurent]

end ADMM.UnitCircle.LowerCertificate.Division
