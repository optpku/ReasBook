module

public import Book.Lemma_3_1
public import ReasLib.Optimization.BFGS.PlanarGradient.SeparationBounds

public section

noncomputable section

open scoped BigOperators

universe u

section OrientedPlane

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/- Derivation 3.1 (1): positive initial angular separation remains positive along a
nonzero planar gradient recurrence. -/
#check (PlanarGradient.angularSeparation_pos_of_recurrence (E := E) :
  ∀ (o : Orientation ℝ E (Fin 2)) (g : ℕ → E) (δ : ℕ → ℝ)
    (hNonzero : ∀ k, g k ≠ 0)
    (hDistinct : ∀ k, 0 < k → g k ≠ g (k - 1))
    (hPre : ∀ k, 0 < k →
      inner ℝ (g k - g (k - 1)) (g k) =
        inner ℝ (g k) (PlanarGradient.perturbation o (g (k - 1)) (δ (k - 1))))
    (hScale : ∀ k, 0 < k →
      PlanarGradient.scale o (g (k - 1)) (g k) (δ k) ≠ 0)
    (hNext : ∀ k, 0 < k →
      g (k + 1) = PlanarGradient.next o (g (k - 1)) (g k) (δ k))
    (hInitial : 0 < PlanarGradient.angularSeparation o (g 0) (g 1)),
    ∀ k, 0 < k →
      0 < PlanarGradient.angularSeparation o (g (k - 1)) (g k))

/- Derivation 3.1 (2): the exact normalized-vector recurrence for angular separation. -/
#check (PlanarGradient.angularSeparation_next_eq_div_norm (E := E) :
  ∀ (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δPrev δ : ℝ)
    (hPrev : gPrev ≠ 0) (hg : g ≠ 0) (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g =
      inner ℝ g (PlanarGradient.perturbation o gPrev δPrev))
    (hScale : PlanarGradient.scale o gPrev g δ ≠ 0),
    PlanarGradient.angularSeparation o g (PlanarGradient.next o gPrev g δ) =
      PlanarGradient.angularSeparation o gPrev g /
        ‖NormedSpace.normalize gPrev -
          (‖g‖ / ‖gPrev‖) • NormedSpace.normalize g‖)

/- Derivation 3.1 (3): one recurrence step decreases angular separation by at most the
factor `1 + ‖g‖ / ‖gPrev‖`. -/
#check (PlanarGradient.angularSeparation_next_lower_bound (E := E) :
  ∀ (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δPrev δ : ℝ)
    (hPrev : gPrev ≠ 0) (hg : g ≠ 0) (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g =
      inner ℝ g (PlanarGradient.perturbation o gPrev δPrev))
    (hScale : PlanarGradient.scale o gPrev g δ ≠ 0),
    PlanarGradient.angularSeparation o gPrev g / (1 + ‖g‖ / ‖gPrev‖) ≤
      PlanarGradient.angularSeparation o g (PlanarGradient.next o gPrev g δ))

/- Derivation 3.1 (4): iteration of the one-step estimate gives the finite-product
lower bound for angular separation. -/
#check (PlanarGradient.angularSeparation_prod_lower_bound (E := E) :
  ∀ (o : Orientation ℝ E (Fin 2)) (g : ℕ → E) (δ : ℕ → ℝ)
    (hNonzero : ∀ k, g k ≠ 0)
    (hDistinct : ∀ k, 0 < k → g k ≠ g (k - 1))
    (hPre : ∀ k, 0 < k →
      inner ℝ (g k - g (k - 1)) (g k) =
        inner ℝ (g k) (PlanarGradient.perturbation o (g (k - 1)) (δ (k - 1))))
    (hScale : ∀ k, 0 < k →
      PlanarGradient.scale o (g (k - 1)) (g k) (δ k) ≠ 0)
    (hNext : ∀ k, 0 < k →
      g (k + 1) = PlanarGradient.next o (g (k - 1)) (g k) (δ k))
    (hInitial : 0 < PlanarGradient.angularSeparation o (g 0) (g 1)) (k : ℕ),
    PlanarGradient.angularSeparation o (g 0) (g 1) *
        ∏ i ∈ Finset.range k, (1 + ‖g (i + 1)‖ / ‖g i‖)⁻¹ ≤
      PlanarGradient.angularSeparation o (g k) (g (k + 1)))

/- The explicit uniform lower-bound datum. -/
#check (PlanarGradient.angleLowerBound (E := E) :
  Orientation ℝ E (Fin 2) → (ℕ → E) → ℝ)

/- The defining formula for the explicit uniform lower bound. -/
#check (PlanarGradient.angleLowerBound_apply (E := E) :
  ∀ (o : Orientation ℝ E (Fin 2)) (g : ℕ → E),
    PlanarGradient.angleLowerBound o g =
      PlanarGradient.angularSeparation o (g 0) (g 1) *
        Real.exp (-(∑' i : ℕ, ‖g (i + 1)‖ / ‖g i‖)))

/- Derivation 3.1 (5): the explicit angular lower bound is positive when the norm-ratio
series is summable and the initial separation is positive. -/
#check (PlanarGradient.angleLowerBound_pos (E := E) :
  ∀ (o : Orientation ℝ E (Fin 2)) (g : ℕ → E)
    (hNonzero : ∀ k, g k ≠ 0)
    (hSummable : Summable (fun i : ℕ ↦ ‖g (i + 1)‖ / ‖g i‖))
    (hInitial : 0 < PlanarGradient.angularSeparation o (g 0) (g 1)),
    0 < PlanarGradient.angleLowerBound o g)

/- Derivation 3.1 (6): the explicit positive constant uniformly bounds every angular
separation in the recurrence from below. -/
#check (PlanarGradient.angleLowerBound_le_angularSeparation (E := E) :
  ∀ (o : Orientation ℝ E (Fin 2)) (g : ℕ → E) (δ : ℕ → ℝ)
    (hNonzero : ∀ k, g k ≠ 0)
    (hDistinct : ∀ k, 0 < k → g k ≠ g (k - 1))
    (hPre : ∀ k, 0 < k →
      inner ℝ (g k - g (k - 1)) (g k) =
        inner ℝ (g k) (PlanarGradient.perturbation o (g (k - 1)) (δ (k - 1))))
    (hScale : ∀ k, 0 < k →
      PlanarGradient.scale o (g (k - 1)) (g k) (δ k) ≠ 0)
    (hNext : ∀ k, 0 < k →
      g (k + 1) = PlanarGradient.next o (g (k - 1)) (g k) (δ k))
    (hInitial : 0 < PlanarGradient.angularSeparation o (g 0) (g 1))
    (hSummable : Summable (fun i : ℕ ↦ ‖g (i + 1)‖ / ‖g i‖)),
    ∀ k, 0 < k → PlanarGradient.angleLowerBound o g ≤
      PlanarGradient.angularSeparation o (g (k - 1)) (g k))

/- Derivation 3.1 (7): the same explicit positive constant uniformly bounds the
absolute tangent coefficients in the recurrence from below. -/
#check (PlanarGradient.angleLowerBound_le_abs_tangentCoefficient (E := E) :
  ∀ (o : Orientation ℝ E (Fin 2)) (g : ℕ → E) (δ : ℕ → ℝ)
    (hNonzero : ∀ k, g k ≠ 0)
    (hDistinct : ∀ k, 0 < k → g k ≠ g (k - 1))
    (hPre : ∀ k, 0 < k →
      inner ℝ (g k - g (k - 1)) (g k) =
        inner ℝ (g k) (PlanarGradient.perturbation o (g (k - 1)) (δ (k - 1))))
    (hScale : ∀ k, 0 < k →
      PlanarGradient.scale o (g (k - 1)) (g k) (δ k) ≠ 0)
    (hNext : ∀ k, 0 < k →
      g (k + 1) = PlanarGradient.next o (g (k - 1)) (g k) (δ k))
    (hInitial : 0 < PlanarGradient.angularSeparation o (g 0) (g 1))
    (hSummable : Summable (fun i : ℕ ↦ ‖g (i + 1)‖ / ‖g i‖)),
    ∀ k, 0 < k → PlanarGradient.angleLowerBound o g ≤
      |PlanarGradient.tangentCoefficient o (g (k - 1)) (g k)|)

end OrientedPlane
