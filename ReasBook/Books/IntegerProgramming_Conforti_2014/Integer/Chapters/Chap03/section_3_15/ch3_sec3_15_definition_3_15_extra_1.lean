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
