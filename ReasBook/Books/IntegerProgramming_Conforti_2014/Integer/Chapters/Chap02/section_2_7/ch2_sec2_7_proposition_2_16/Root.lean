/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Fin.Basic

public section

/-- The textbook distinguished vertex `1`, represented in `Fin n` coordinates by `0`. -/
def textbook_root {n : ℕ} (hpos : 0 < n) : Fin n :=
  ⟨0, hpos⟩
