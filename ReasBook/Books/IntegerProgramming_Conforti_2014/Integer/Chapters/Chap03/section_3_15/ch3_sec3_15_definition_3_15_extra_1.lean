/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

variable {α β : Type*}

/- Definition 3.15-extra-1. The `x`-projection of a subset of a product is the canonical set image
`Prod.fst '' S`. -/
section

variable (S : Set (α × β))

#check (Prod.fst '' S : Set α)

end

/-- A point lies in `Prod.fst '' S` exactly when it is the first coordinate of some point of `S`. -/
theorem mem_image_fst_iff
    {S : Set (α × β)}
    {x : α} :
    x ∈ Prod.fst '' S ↔ ∃ y : β, (x, y) ∈ S := by
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    exact ⟨xy.2, hxy⟩
  · rintro ⟨y, hxy⟩
    exact ⟨(x, y), hxy, rfl⟩
