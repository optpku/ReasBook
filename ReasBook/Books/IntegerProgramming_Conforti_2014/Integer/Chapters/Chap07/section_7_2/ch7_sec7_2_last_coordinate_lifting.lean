import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Archimedean
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1

open scoped BigOperators Matrix

section LastCoordinateLifting

variable {n : ℕ}

/-- The slice cut out by fixing the last coordinate to `r`. -/
def last_coordinate_eq_set (n : ℕ) (r : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {x | x (Fin.last n) = r}

/-- Membership in `last_coordinate_eq_set n r` means that the last coordinate equals `r`. -/
theorem mem_last_coordinate_eq_set_iff {r : ℝ} {x : Fin (n + 1) → ℝ} :
    x ∈ last_coordinate_eq_set n r ↔ x (Fin.last n) = r :=
  Iff.rfl

/-- The partial left-hand side `∑_{i < n} αᵢ xᵢ` obtained by omitting the last coordinate. -/
def partial_lifting_value (α : Fin n → ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin n, α i * x i.castSucc

/-- Expanding `partial_lifting_value α x` recovers the sum over the non-last coordinates. -/
theorem partial_lifting_value_eq_sum
    (α : Fin n → ℝ) (x : Fin (n + 1) → ℝ) :
    partial_lifting_value α x = ∑ i : Fin n, α i * x i.castSucc :=
  rfl

/-- The objective values `∑_{i < n} αᵢ xᵢ` attained on the slice `S ∩ {x_last = r}`. -/
def last_coordinate_slice_values
    (S : Set (Fin (n + 1) → ℝ))
    (α : Fin n → ℝ)
    (r : ℝ) : Set ℝ :=
  partial_lifting_value α '' (S ∩ last_coordinate_eq_set n r)

/-- Membership in `last_coordinate_slice_values S α r` means that the value is attained by some
point of `S` with last coordinate `r`. -/
theorem mem_last_coordinate_slice_values_iff
    {S : Set (Fin (n + 1) → ℝ)}
    {α : Fin n → ℝ}
    {r t : ℝ} :
    t ∈ last_coordinate_slice_values S α r ↔
      ∃ x : Fin (n + 1) → ℝ, x ∈ S ∧ x (Fin.last n) = r ∧ partial_lifting_value α x = t := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, mem_last_coordinate_eq_set_iff.mp hx.2, rfl⟩
  · rintro ⟨x, hxS, hxlast, rfl⟩
    exact ⟨x, ⟨hxS, mem_last_coordinate_eq_set_iff.mpr hxlast⟩, rfl⟩

/-- The canonical lifted coefficient vector `Fin.snoc α αn` evaluates against `x` as the source
inequality `∑_{i < n} αᵢ xᵢ + αn x_last`. -/
theorem dotProduct_last_coordinate_lifting_coeffs
    (α : Fin n → ℝ)
    (αn : ℝ)
    (x : Fin (n + 1) → ℝ) :
    Fin.snoc α αn ⬝ᵥ x =
      partial_lifting_value α x + αn * x (Fin.last n) := by
  simp [partial_lifting_value, dotProduct, Fin.sum_univ_castSucc, add_comm]

/-- The coefficient obtained from the maximum objective value on the `x_last = 1` slice. -/
noncomputable def last_coordinate_lifting_coefficient
    (S : Set (Fin (n + 1) → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ) : ℝ :=
  β - sSup (last_coordinate_slice_values S α 1)

/-- Expanding `last_coordinate_lifting_coefficient S α β` recovers the formula
`β - sup {∑_{i < n} αᵢ xᵢ | x ∈ S, x_last = 1}`. -/
theorem last_coordinate_lifting_coefficient_eq
    (S : Set (Fin (n + 1) → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ) :
    last_coordinate_lifting_coefficient S α β =
      β - sSup (last_coordinate_slice_values S α 1) :=
  rfl

/-- The last-coordinate coefficients that keep the lifted inequality valid on `S`. -/
def valid_last_coordinate_lifting_coefficients
    (S : Set (Fin (n + 1) → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ) : Set ℝ :=
  {αn | is_valid_inequality S (Fin.snoc α αn) β}

/-- Membership in `valid_last_coordinate_lifting_coefficients S α β` is exactly validity of the
corresponding lifted inequality. -/
theorem mem_valid_last_coordinate_lifting_coefficients_iff
    {S : Set (Fin (n + 1) → ℝ)}
    {α : Fin n → ℝ}
    {β αn : ℝ} :
    αn ∈ valid_last_coordinate_lifting_coefficients S α β ↔
      is_valid_inequality S (Fin.snoc α αn) β :=
  Iff.rfl

end LastCoordinateLifting
