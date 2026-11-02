module

public import Mathlib.Data.Fin.Basic

public section

/-- The textbook distinguished vertex `1`, represented in `Fin n` coordinates by `0`. -/
def textbook_root {n : ℕ} (hpos : 0 < n) : Fin n :=
  ⟨0, hpos⟩
