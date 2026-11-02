import Mathlib

section Exercise_4_37

variable {R : Type*} [Semiring R]
variable {E F : Type*} [AddCommMonoid E] [Module R E] [AddCommMonoid F] [Module R F]

/-- Exercise 4.37. If a linear equivalence maps `P` onto `Q`, then the inverse linear equivalence
maps `Q` onto `P`; in particular, linear isomorphism of polytopes is symmetric. -/
theorem polytope_linearly_isomorphic_comm
    {P : Set E} {Q : Set F} :
    (∃ e : E ≃ₗ[R] F, e '' P = Q) ↔
      ∃ e : F ≃ₗ[R] E, e '' Q = P := by
  constructor
  · rintro ⟨e, hPQ⟩
    exact ⟨e.symm, (e.toEquiv.eq_image_iff_symm_image_eq P Q).1 hPQ.symm⟩
  · rintro ⟨e, hQP⟩
    exact ⟨e.symm, (e.toEquiv.eq_image_iff_symm_image_eq Q P).1 hQP.symm⟩

end Exercise_4_37
