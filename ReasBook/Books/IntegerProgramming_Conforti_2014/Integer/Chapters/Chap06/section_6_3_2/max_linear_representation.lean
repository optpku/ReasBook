import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open scoped Matrix

section MaxLinearRepresentation

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ

/-- `IsMaxLinearRepresentation ψ normals` means that the finite family `normals` realizes `ψ` as
the pointwise maximum of the corresponding linear functionals on `ℝ^q`. -/
def IsMaxLinearRepresentation {t : ℕ} [NeZero t]
    (ψ : Rq → ℝ) (normals : Fin t → Rq) : Prop :=
  ∀ r : Rq,
    ψ r = Finset.univ.sup' Finset.univ_nonempty (fun i : Fin t ↦ normals i ⬝ᵥ r)

/-- Unfolding `IsMaxLinearRepresentation ψ normals` recovers the pointwise `sup'` formula. -/
theorem isMaxLinearRepresentation_iff
    {t : ℕ} [NeZero t] {ψ : Rq → ℝ} {normals : Fin t → Rq} :
    IsMaxLinearRepresentation ψ normals ↔
      ∀ r : Rq,
        ψ r = Finset.univ.sup' Finset.univ_nonempty (fun i : Fin t ↦ normals i ⬝ᵥ r) :=
  Iff.rfl

namespace IsMaxLinearRepresentation

/-- A max-linear representation evaluates `ψ` by the displayed `sup'` formula at each point. -/
theorem apply_eq_sup
    {t : ℕ} [NeZero t] {ψ : Rq → ℝ} {normals : Fin t → Rq}
    (h : IsMaxLinearRepresentation ψ normals) (r : Rq) :
    ψ r = Finset.univ.sup' Finset.univ_nonempty (fun i : Fin t ↦ normals i ⬝ᵥ r) :=
  h r

end IsMaxLinearRepresentation

/-- `HasMaxLinearRepresentation ψ` means that `ψ` is realized by the maximum of finitely many
linear functionals on `ℝ^q`. -/
def HasMaxLinearRepresentation (ψ : Rq → ℝ) : Prop :=
  ∃ t : ℕ, ∃ _ : NeZero t, ∃ normals : Fin t → Rq, IsMaxLinearRepresentation ψ normals

/-- Unfolding `HasMaxLinearRepresentation ψ` exposes the representing finite family of normals. -/
theorem hasMaxLinearRepresentation_iff
    {ψ : Rq → ℝ} :
    HasMaxLinearRepresentation ψ ↔
      ∃ t : ℕ, ∃ _ : NeZero t, ∃ normals : Fin t → Rq, IsMaxLinearRepresentation ψ normals :=
  Iff.rfl

namespace HasMaxLinearRepresentation

/-- A fixed max-linear representation yields the existential owner `HasMaxLinearRepresentation`. -/
theorem of_isMaxLinearRepresentation
    {t : ℕ} [NeZero t] {ψ : Rq → ℝ} {normals : Fin t → Rq}
    (h : IsMaxLinearRepresentation ψ normals) :
    HasMaxLinearRepresentation ψ :=
  ⟨t, inferInstance, normals, h⟩

end HasMaxLinearRepresentation

/-- `HasMaxLinearRepresentationOfSizeLE bound ψ` means that `ψ` admits a max-linear
representation using at most `bound` linear functionals. -/
def HasMaxLinearRepresentationOfSizeLE (bound : ℕ) (ψ : Rq → ℝ) : Prop :=
  ∃ t : ℕ, t ≤ bound ∧ ∃ _ : NeZero t, ∃ normals : Fin t → Rq, IsMaxLinearRepresentation ψ normals

/-- Unfolding `HasMaxLinearRepresentationOfSizeLE bound ψ` exposes the size bound and the
representing finite family of normals. -/
theorem hasMaxLinearRepresentationOfSizeLE_iff
    {bound : ℕ} {ψ : Rq → ℝ} :
    HasMaxLinearRepresentationOfSizeLE bound ψ ↔
      ∃ t : ℕ, t ≤ bound ∧ ∃ _ : NeZero t, ∃ normals : Fin t → Rq,
        IsMaxLinearRepresentation ψ normals :=
  Iff.rfl

namespace HasMaxLinearRepresentationOfSizeLE

/-- A fixed max-linear representation with `t ≤ bound` yields the bounded owner
`HasMaxLinearRepresentationOfSizeLE bound ψ`. -/
theorem of_isMaxLinearRepresentation
    {bound t : ℕ} [NeZero t] {ψ : Rq → ℝ} {normals : Fin t → Rq}
    (ht : t ≤ bound) (h : IsMaxLinearRepresentation ψ normals) :
    HasMaxLinearRepresentationOfSizeLE bound ψ :=
  ⟨t, ht, inferInstance, normals, h⟩

/-- A bounded max-linear representation is, in particular, a max-linear representation. -/
theorem hasMaxLinearRepresentation
    {bound : ℕ} {ψ : Rq → ℝ}
    (h : HasMaxLinearRepresentationOfSizeLE bound ψ) :
    HasMaxLinearRepresentation ψ := by
  rcases h with ⟨t, _, _, normals, hnormals⟩
  exact ⟨t, inferInstance, normals, hnormals⟩

/-- A max-linear representation bounded by `bound` is also bounded by any larger `bound'`. -/
theorem mono
    {bound bound' : ℕ} {ψ : Rq → ℝ}
    (h : HasMaxLinearRepresentationOfSizeLE bound ψ)
    (hbound : bound ≤ bound') :
    HasMaxLinearRepresentationOfSizeLE bound' ψ := by
  rcases h with ⟨t, ht, _, normals, hnormals⟩
  exact ⟨t, ht.trans hbound, inferInstance, normals, hnormals⟩

end HasMaxLinearRepresentationOfSizeLE

end MaxLinearRepresentation
